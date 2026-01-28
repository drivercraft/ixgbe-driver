//! Functional tests - Memory pool management
//!
//! These tests verify memory pool functionality in simulated environments, including:
//! - Memory allocation and deallocation
//! - Boundary condition handling
//! - Error scenario handling

use ixgbe_driver::{alloc_pkt, IxgbeError, IxgbeHal, MemPool, PACKET_HEADROOM};

// Mock HAL implementation for testing
struct MockHal;

unsafe impl IxgbeHal for MockHal {
    fn dma_alloc(size: usize) -> (usize, core::ptr::NonNull<u8>) {
        // Use standard library for allocation in test environment
        let layout = std::alloc::Layout::from_size_align(size, 4096).unwrap();
        let ptr = unsafe { std::alloc::alloc(layout) };
        if ptr.is_null() {
            panic!("Memory allocation failed");
        }
        let phys_addr = ptr as usize; // Simulate physical address
        (phys_addr, core::ptr::NonNull::new(ptr).unwrap())
    }

    unsafe fn dma_dealloc(paddr: usize, vaddr: core::ptr::NonNull<u8>, size: usize) -> i32 {
        // Use standard library for deallocation
        let layout = std::alloc::Layout::from_size_align(size, 4096).unwrap();
        std::alloc::dealloc(vaddr.as_ptr(), layout);
        0
    }

    unsafe fn mmio_phys_to_virt(paddr: usize, size: usize) -> core::ptr::NonNull<u8> {
        // Simulate MMIO mapping
        core::ptr::NonNull::new(paddr as *mut u8).unwrap()
    }

    unsafe fn mmio_virt_to_phys(vaddr: core::ptr::NonNull<u8>, size: usize) -> usize {
        // Simulate address translation
        vaddr.as_ptr() as usize
    }

    fn wait_until(duration: core::time::Duration) -> Result<(), &'static str> {
        // Simulate waiting
        Ok(())
    }
}

#[test]
fn test_memory_pool_allocation() {
    // Test normal memory pool allocation
    let pool = MemPool::allocate::<MockHal>(4096, 2048).expect("Failed to allocate memory pool");
    assert_eq!(pool.entry_size(), 2048);
}

#[test]
fn test_memory_pool_invalid_size() {
    // Test invalid entry size (not divisible by page size)
    let result = MemPool::allocate::<MockHal>(4096, 100);
    assert!(matches!(result, Err(IxgbeError::PageNotAligned)));
}

#[test]
fn test_packet_allocation_and_deallocation() {
    // Test packet allocation and automatic deallocation
    let pool = MemPool::allocate::<MockHal>(4096, 2048).unwrap();

    // Allocate packet
    let packet = alloc_pkt(&pool, 1500).expect("Failed to allocate packet");
    assert_eq!(packet.len(), 1500);

    // Verify packet is accessible
    let data = packet.as_bytes();
    assert_eq!(data.len(), 1500);

    // Packet should be automatically freed back to memory pool when out of scope
    drop(packet);

    // Should be able to allocate again
    let packet2 = alloc_pkt(&pool, 1500).expect("Failed to allocate second packet");
    assert_eq!(packet2.len(), 1500);
}

#[test]
fn test_packet_allocation_too_large() {
    // Test allocating packet larger than entry size
    let pool = MemPool::allocate::<MockHal>(4096, 2048).unwrap();

    // Try to allocate packet exceeding available space (considering headroom)
    let result = alloc_pkt(&pool, 2048 - PACKET_HEADROOM + 1);
    assert!(result.is_none());
}

#[test]
fn test_packet_data_access() {
    // Test read/write access to packet data
    let pool = MemPool::allocate::<MockHal>(4096, 2048).unwrap();
    let mut packet = alloc_pkt(&pool, 1500).unwrap();

    // Write data
    {
        let data = packet.as_mut_bytes();
        data[0] = 0xFF;
        data[1] = 0x00;
        data[1499] = 0xAA;
    }

    // Read data
    {
        let data = packet.as_bytes();
        assert_eq!(data[0], 0xFF);
        assert_eq!(data[1], 0x00);
        assert_eq!(data[1499], 0xAA);
    }
}

#[test]
fn test_packet_clone() {
    // Test packet cloning functionality
    let pool = MemPool::allocate::<MockHal>(4096, 2048).unwrap();
    let mut original = alloc_pkt(&pool, 100).unwrap();

    // Modify original packet
    original.as_mut_bytes()[0] = 0x42;

    // Clone packet
    let cloned = original.clone();

    // Verify cloned packet has same content
    assert_eq!(cloned.len(), original.len());
    assert_eq!(cloned.as_bytes()[0], 0x42);

    // Verify they are independent copies
    original.as_mut_bytes()[0] = 0x24;
    assert_eq!(original.as_bytes()[0], 0x24);
    assert_eq!(cloned.as_bytes()[0], 0x42); // Cloned should remain unchanged
}

#[test]
fn test_memory_pool_exhaustion() {
    // Test memory pool exhaustion scenario
    let pool = MemPool::allocate::<MockHal>(2, 2048).unwrap(); // Only 2 entries

    // Allocate all available entries
    let packet1 = alloc_pkt(&pool, 1500).unwrap();
    let packet2 = alloc_pkt(&pool, 1500).unwrap();

    // Pool should be exhausted
    let packet3 = alloc_pkt(&pool, 1500);
    assert!(packet3.is_none());

    // Should be able to allocate again after releasing an entry
    drop(packet1);
    let packet4 = alloc_pkt(&pool, 1500).unwrap();
    assert_eq!(packet4.len(), 1500);
}

#[test]
fn test_packet_headroom_access() {
    // Test packet headroom access
    let pool = MemPool::allocate::<MockHal>(4096, 2048).unwrap();
    let mut packet = alloc_pkt(&pool, 1500).unwrap();

    // Access headroom
    {
        let headroom = packet.headroom_mut(10);
        assert_eq!(headroom.len(), 10);
        headroom[0] = 0xDE;
        headroom[9] = 0xAD;
    }

    // Verify headroom is independent of data space
    assert_eq!(packet.as_bytes()[0], 0); // First byte of data space should be 0
}

#[test]
#[should_panic]
fn test_packet_headroom_too_large() {
    // Test accessing oversized headroom (should panic)
    let pool = MemPool::allocate::<MockHal>(4096, 2048).unwrap();
    let mut packet = alloc_pkt(&pool, 1500).unwrap();

    // This should panic because requested headroom exceeds PACKET_HEADROOM
    let _ = packet.headroom_mut(PACKET_HEADROOM + 1);
}
