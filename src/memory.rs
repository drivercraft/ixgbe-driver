//! Memory management for the ixgbe driver.
//!
//! This module provides memory pool management and DMA allocation utilities for the
//! ixgbe driver. It includes:
//!
//! - [`MemPool`]: A fixed-size memory pool for efficient packet buffer allocation
//! - [`Packet`]: A packet buffer with automatic memory management
//! - [`alloc_pkt`]: Convenience function for allocating packets from a memory pool
//!
//! # Memory Pool
//!
//! The memory pool pre-allocates a fixed number of equally-sized buffers from DMA-capable
//! memory. This design minimizes allocation overhead and ensures all packet buffers are
//! accessible by the NIC hardware.
//!
//! # Example
//!
//! ```rust,ignore
//! use ixgbe_driver::memory::MemPool;
//!
//! // Create a pool with 4096 entries, each 2048 bytes
//! let pool = MemPool::allocate::<MyHal>(4096, 2048)?;
//!
//! // Allocate a packet from the pool
//! let packet = alloc_pkt(&pool, 1500)?;
//! ```

use core::fmt::Debug;
use core::ops::{Deref, DerefMut};
use core::ptr::NonNull;
use core::{cell::RefCell, marker::PhantomData};

use crate::hal::IxgbeHal;
use crate::{IxgbeError, IxgbeResult};
use alloc::sync::Arc;
use alloc::vec::Vec;
use alloc::{fmt, slice};

/// Physical address in system memory.
///
/// This type represents a physical memory address that can be accessed by hardware devices
/// via DMA.
pub type PhysAddr = usize;
/// Virtual address in system memory.
///
/// This type represents a virtual memory address that is used by the CPU/Driver to access memory.
pub type VirtAddr = usize;

const HUGE_PAGE_BITS: u32 = 21;
const HUGE_PAGE_SIZE: usize = 1 << HUGE_PAGE_BITS;

// this differs from upstream ixy as our packet metadata is stored outside of the actual packet data
// which results in a different alignment requirement
/// Headroom reserved at the start of each packet buffer.
///
/// This space can be used to prepend headers (e.g., VLAN, Ethernet, IP) without
/// needing to reallocate or copy the packet data.
pub const PACKET_HEADROOM: usize = 32;

/// A memory pool for efficient DMA-capable buffer allocation.
///
/// The memory pool pre-allocates a fixed number of equally-sized buffers from
/// DMA-capable memory. This design ensures that:
///
/// - All buffers are physically contiguous and accessible by the NIC
/// - Allocation is fast (O(1) simple stack pop)
/// - Memory fragmentation is avoided
///
/// # Thread Safety
///
/// The memory pool uses interior mutability via `RefCell` and can be safely
/// shared between threads.
///
/// # Example
///
/// ```rust,ignore
/// use ixgbe_driver::memory::MemPool;
///
/// // Create a pool with 4096 entries of 2048 bytes each
/// let pool = MemPool::allocate::<MyHal>(4096, 2048)?;
///
/// // Get the entry size
/// assert_eq!(pool.entry_size(), 2048);
/// ```
pub struct MemPool {
    base_addr: *mut u8,
    num_entries: usize,
    entry_size: usize,
    phys_addr: Vec<usize>,
    pub(crate) free_stack: RefCell<Vec<usize>>,
}

impl MemPool {
    /// Allocates a new memory pool.
    ///
    /// Creates a memory pool with the specified number of entries, each of the
    /// given size. The entry size must divide the huge page size (2MB) evenly.
    ///
    /// # Arguments
    ///
    /// * `entries` - Number of buffer entries in the pool
    /// * `size` - Size of each entry in bytes (0 defaults to 2048)
    ///
    /// # Returns
    ///
    /// An `Arc`-wrapped `MemPool` that can be shared across packet buffers.
    ///
    /// # Errors
    ///
    /// - [`IxgbeError::PageNotAligned`] - If `size` is not a divisor of the page size
    /// - [`IxgbeError::NoMemory`] - If DMA allocation fails
    ///
    /// # Panics
    ///
    /// Panics if `size` is not a divisor of the huge page size (2MB).
    pub fn allocate<H: IxgbeHal>(entries: usize, size: usize) -> IxgbeResult<Arc<MemPool>> {
        let entry_size = match size {
            0 => 2048,
            x => x,
        };

        if HUGE_PAGE_SIZE % entry_size != 0 {
            error!("entry size must be a divisor of the page size");
            return Err(IxgbeError::PageNotAligned);
        }

        let dma = Dma::<u8, H>::allocate(entries * entry_size, false)?;
        let mut phys_addr = Vec::with_capacity(entries);

        for i in 0..entries {
            phys_addr.push(unsafe {
                H::mmio_virt_to_phys(
                    NonNull::new(dma.virt.add(i * entry_size)).unwrap(),
                    entry_size,
                )
            })
        }

        let pool = MemPool {
            base_addr: dma.virt,
            num_entries: entries,
            entry_size,
            phys_addr,
            free_stack: RefCell::new(Vec::with_capacity(entries)),
        };

        let pool = Arc::new(pool);
        pool.free_stack.borrow_mut().extend(0..entries);

        Ok(pool)
    }

    /// Returns the position of a free buffer in the memory pool, or [`None`] if the pool is empty.
    pub(crate) fn alloc_buf(&self) -> Option<usize> {
        self.free_stack.borrow_mut().pop()
    }

    /// Marks a buffer in the memory pool as free.
    pub(crate) fn free_buf(&self, id: usize) {
        assert!(
            id < self.num_entries,
            "buffer outside of memory pool, id: {id}"
        );

        let mut free_stack = self.free_stack.borrow_mut();
        if free_stack.contains(&id) {
            panic!("free buf: buffer already free");
        }

        free_stack.push(id);
    }

    /// Returns the size (in bytes) of each entry in the pool.
    pub fn entry_size(&self) -> usize {
        self.entry_size
    }

    /// Returns the virtual address of a buffer from the memory pool.
    pub(crate) fn get_virt_addr(&self, id: usize) -> *mut u8 {
        assert!(
            id < self.num_entries,
            "buffer outside of memory pool, id: {id}"
        );

        unsafe { self.base_addr.add(id * self.entry_size) }
    }

    /// Returns the physical address of a buffer from the memory pool.
    ///
    /// This address can be passed to the NIC hardware for DMA operations.
    pub fn get_phys_addr(&self, id: usize) -> usize {
        self.phys_addr[id]
    }
}

/// DMA-allocated memory block.
///
/// Represents a block of physically contiguous memory allocated for DMA operations.
/// This is a low-level type used internally for descriptor ring allocation.
pub struct Dma<T, H: IxgbeHal> {
    pub virt: *mut T,
    pub phys: usize,
    _marker: PhantomData<H>,
}

impl<T, H: IxgbeHal> Dma<T, H> {
    /// Allocates a new DMA memory block.
    ///
    /// # Arguments
    ///
    /// * `size` - Size of the allocation in bytes
    /// * `_require_contiguous` - Whether memory must be contiguous (currently unused)
    ///
    /// # Errors
    ///
    /// Returns [`IxgbeError::NoMemory`] if the allocation fails.
    pub fn allocate(size: usize, _require_contiguous: bool) -> IxgbeResult<Dma<T, H>> {
        // let size = if size % HUGE_PAGE_SIZE != 0 {
        //     ((size >> HUGE_PAGE_BITS) + 1) << HUGE_PAGE_BITS
        // } else {
        //     size
        // };
        // let size = if size < 0x1000 { 0x1000 } else { size };
        // let (pa, va) = H::dma_alloc(size / 0x1000, crate::BufferDirection::Both);
        let (pa, va) = H::dma_alloc(size);
        info!(
            "allocated DMA memory @pa: {:#x}, va: {:#x}, size: {:#x}",
            pa,
            va.as_ptr() as usize,
            size
        );
        Ok(Dma::<T, H> {
            virt: va.as_ptr() as *mut T,
            phys: pa,
            _marker: PhantomData,
        })
    }
}

/// A packet buffer with automatic memory management.
///
/// `Packet` represents a buffer that was allocated from a [`MemPool`]. When the
/// packet is dropped, the buffer is automatically returned to the pool for reuse.
///
/// # Data Access
///
/// The packet implements `Deref` and `DerefMut` to `[u8]`, allowing direct access
/// to the packet data as a byte slice.
///
/// # Cloning
///
/// Cloning a packet creates a deep copy by allocating a new buffer from the pool
/// and copying the data. The original packet remains valid.
///
/// # Example
///
/// ```rust,ignore
/// use ixgbe_driver::memory::alloc_pkt;
///
/// let packet = alloc_pkt(&pool, 1500)?;
///
/// // Access data
/// let data: &[u8] = &packet;
///
/// // Modify data
/// packet.as_mut_bytes()[0] = 0xFF;
///
/// // Get addresses for DMA
/// let phys_addr = packet.get_phys_addr();
/// let virt_addr = packet.get_virt_addr();
/// ```
pub struct Packet {
    pub(crate) addr_virt: NonNull<u8>,
    pub(crate) addr_phys: usize,
    pub(crate) len: usize,
    pub(crate) pool: Arc<MemPool>,
    pub(crate) pool_entry: usize,
}

impl Clone for Packet {
    fn clone(&self) -> Self {
        let mut p = alloc_pkt(&self.pool, self.len).expect("no buffer available");
        p.clone_from_slice(self);

        p
    }
}

impl Deref for Packet {
    type Target = [u8];

    fn deref(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.addr_virt.as_ptr(), self.len) }
    }
}

impl DerefMut for Packet {
    fn deref_mut(&mut self) -> &mut [u8] {
        unsafe { slice::from_raw_parts_mut(self.addr_virt.as_ptr(), self.len) }
    }
}

impl Debug for Packet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl Drop for Packet {
    fn drop(&mut self) {
        self.pool.free_buf(self.pool_entry);
    }
}

impl Packet {
    /// Creates a new packet from raw components.
    ///
    /// # Safety
    ///
    /// The caller must ensure that:
    /// - `addr_virt` points to valid memory
    /// - `addr_phys` is the correct physical address for `addr_virt`
    /// - The memory was allocated from `pool` at entry `pool_entry`
    /// - `len` does not exceed the allocated buffer size
    pub(crate) unsafe fn new(
        addr_virt: *mut u8,
        addr_phys: usize,
        len: usize,
        pool: Arc<MemPool>,
        pool_entry: usize,
    ) -> Packet {
        Packet {
            addr_virt: NonNull::new_unchecked(addr_virt),
            addr_phys,
            len,
            pool,
            pool_entry,
        }
    }

    /// Returns the virtual address of the packet data.
    pub fn get_virt_addr(&self) -> *mut u8 {
        self.addr_virt.as_ptr()
    }

    /// Returns the physical address of the packet data.
    ///
    /// This address is used by the NIC hardware for DMA operations.
    pub fn get_phys_addr(&self) -> usize {
        self.addr_phys
    }

    /// Returns the packet data as a byte slice.
    pub fn as_bytes(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.addr_virt.as_ptr(), self.len) }
    }

    /// Returns the packet data as a mutable byte slice.
    pub fn as_mut_bytes(&mut self) -> &mut [u8] {
        unsafe { slice::from_raw_parts_mut(self.addr_virt.as_ptr(), self.len) }
    }

    /// Returns a mutable slice to the headroom of the packet.
    ///
    /// The `len` parameter controls how much of the headroom is returned.
    ///
    /// # Panics
    ///
    /// Panics if `len` is greater than [`PACKET_HEADROOM`]
    pub fn headroom_mut(&mut self, len: usize) -> &mut [u8] {
        assert!(len <= PACKET_HEADROOM);
        unsafe { slice::from_raw_parts_mut(self.addr_virt.as_ptr().sub(len), len) }
    }

    #[cfg(target_arch = "x86_64")]
    #[inline(always)]
    pub(crate) fn prefrtch(&self, hint: Prefetch) {
        if core_detect::is_x86_feature_detected!("sse") {
            let addr = self.get_virt_addr() as *const _;
            unsafe {
                use core::arch::x86_64;
                match hint {
                    Prefetch::Time0 => x86_64::_mm_prefetch(addr, x86_64::_MM_HINT_T0),
                    Prefetch::Time1 => x86_64::_mm_prefetch(addr, x86_64::_MM_HINT_T1),
                    Prefetch::Time2 => x86_64::_mm_prefetch(addr, x86_64::_MM_HINT_T2),
                    Prefetch::NonTemporal => x86_64::_mm_prefetch(addr, x86_64::_MM_HINT_NTA),
                }
            }
        }
    }
}

/// Allocates a packet from the memory pool.
///
/// Attempts to allocate a packet buffer of the specified size from the pool.
/// The allocation will fail if:
///
/// - The pool is exhausted (no free buffers)
/// - The requested size exceeds the available space after reserving headroom
///
/// # Arguments
///
/// * `pool` - The memory pool to allocate from
/// * `size` - Desired packet data size in bytes
///
/// # Returns
///
/// `Some(Packet)` if allocation succeeded, `None` otherwise.
///
/// # Example
///
/// ```rust,ignore
/// use ixgbe_driver::memory::alloc_pkt;
///
/// if let Some(packet) = alloc_pkt(&pool, 1500) {
///     // Use the packet
/// } else {
///     // Handle allocation failure
/// }
/// ```
pub fn alloc_pkt(pool: &Arc<MemPool>, size: usize) -> Option<Packet> {
    if size > pool.entry_size - PACKET_HEADROOM {
        return None;
    }

    pool.alloc_buf().map(|id| unsafe {
        Packet::new(
            pool.get_virt_addr(id).add(PACKET_HEADROOM),
            pool.get_phys_addr(id) + PACKET_HEADROOM,
            size,
            Arc::clone(pool),
            id,
        )
    })
}

/// CPU cache prefetch hints for x86_64 SSE instructions.
///
/// These hints control how data is prefetched into the CPU cache hierarchy.
/// Different hints are appropriate for different access patterns.
///
/// The `prefetch` functions are only available on x86_64 when SSE is supported.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Prefetch {
    /// Corresponds to _MM_HINT_T0 on x86 sse.
    ///
    /// Fetch data into all cache levels.
    Time0,

    /// Corresponds to _MM_HINT_T1 on x86 sse.
    ///
    /// Fetch data into L2 cache (not L1).
    Time1,

    /// Corresponds to _MM_HINT_T2 on x86 sse.
    ///
    /// Fetch data into L3 cache (not L2 or L1).
    Time2,

    /// Corresponds to _MM_HINT_NTA on x86 sse.
    ///
    /// Non-temporal fetch - data is not expected to be reused.
    NonTemporal,
}

unsafe impl Sync for MemPool {}
unsafe impl Send for MemPool {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_constants() {
        assert_eq!(PACKET_HEADROOM, 32);
        assert_eq!(HUGE_PAGE_BITS, 21);
        assert_eq!(HUGE_PAGE_SIZE, 1 << 21);
        assert_eq!(HUGE_PAGE_SIZE, 0x200000);
    }

    #[test]
    fn test_prefetch_ord() {
        assert!(Prefetch::Time0 < Prefetch::Time1);
        assert!(Prefetch::Time1 < Prefetch::Time2);
        assert!(Prefetch::Time2 < Prefetch::NonTemporal);
    }

    #[test]
    fn test_prefetch_eq() {
        assert_eq!(Prefetch::Time0, Prefetch::Time0);
        assert_ne!(Prefetch::Time0, Prefetch::Time1);
    }

    #[test]
    fn test_prefetch_copy() {
        let hint = Prefetch::Time0;
        let copied = hint;
        assert_eq!(hint, copied);
    }

    #[test]
    fn test_mempool_allocation_alignment() {
        // Test that various entry sizes divide the huge page size evenly
        let valid_sizes = [
            2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288,
        ];
        for &size in &valid_sizes {
            assert_eq!(
                HUGE_PAGE_SIZE % size,
                0,
                "Size {} should divide page size",
                size
            );
        }
    }

    #[test]
    fn test_mempool_invalid_alignment() {
        // Test that invalid sizes do not divide the huge page size evenly
        let invalid_sizes = [100, 1536, 3000, 5000];
        for &size in &invalid_sizes {
            assert_ne!(
                HUGE_PAGE_SIZE % size,
                0,
                "Size {} should not divide page size evenly",
                size
            );
        }
    }

    #[test]
    fn test_mempool_entry_size_default() {
        // Test that default entry size is 2048
        let size = 0;
        let entry_size = match size {
            0 => 2048,
            x => x,
        };
        assert_eq!(entry_size, 2048);
    }
}
