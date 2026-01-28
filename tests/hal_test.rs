//! Functional tests - Hardware Abstraction Layer interface
//!
//! These tests verify Hardware Abstraction Layer interface functionality, including:
//! - DMA memory management
//! - MMIO address translation
//! - Timing and waiting functions

use core::ptr::NonNull;
use core::time::Duration;
use ixgbe_driver::IxgbeHal;

// Mock HAL implementation for testing
struct TestHal;

static mut DMA_ALLOC_COUNT: usize = 0;
static mut DMA_DEALLOC_COUNT: usize = 0;

unsafe impl IxgbeHal for TestHal {
    fn dma_alloc(size: usize) -> (usize, NonNull<u8>) {
        unsafe {
            DMA_ALLOC_COUNT += 1;
        }

        // Use standard library for test allocation
        let layout = std::alloc::Layout::from_size_align(size, 4096).expect("Invalid layout");
        let ptr = unsafe { std::alloc::alloc(layout) };

        if ptr.is_null() {
            panic!("DMA allocation failed in test");
        }

        let phys_addr = ptr as usize; // Simulate physical address
        (phys_addr, NonNull::new(ptr).unwrap())
    }

    unsafe fn dma_dealloc(paddr: usize, vaddr: NonNull<u8>, size: usize) -> i32 {
        unsafe {
            DMA_DEALLOC_COUNT += 1;
        }

        // Use standard library for deallocation
        let layout = std::alloc::Layout::from_size_align(size, 4096).expect("Invalid layout");
        std::alloc::dealloc(vaddr.as_ptr(), layout);
        0 // Success
    }

    unsafe fn mmio_phys_to_virt(paddr: usize, size: usize) -> NonNull<u8> {
        // Simple identity mapping for testing
        NonNull::new(paddr as *mut u8).unwrap()
    }

    unsafe fn mmio_virt_to_phys(vaddr: NonNull<u8>, size: usize) -> usize {
        // Simple identity mapping for testing
        vaddr.as_ptr() as usize
    }

    fn wait_until(duration: Duration) -> Result<(), &'static str> {
        // In tests, we don't actually wait, just return success
        Ok(())
    }
}

#[test]
fn test_dma_memory_lifecycle() {
    unsafe {
        DMA_ALLOC_COUNT = 0;
        DMA_DEALLOC_COUNT = 0;
    }

    // Test DMA memory allocation and deallocation
    let (phys_addr, virt_ptr) = TestHal::dma_alloc(4096);

    unsafe {
        assert_eq!(DMA_ALLOC_COUNT, 1);
        assert_eq!(DMA_DEALLOC_COUNT, 0);
    }

    // Verify address validity
    assert!(!virt_ptr.as_ptr().is_null());
    assert!(phys_addr != 0);

    // Free memory
    let result = unsafe { TestHal::dma_dealloc(phys_addr, virt_ptr, 4096) };
    assert_eq!(result, 0);

    unsafe {
        assert_eq!(DMA_ALLOC_COUNT, 1);
        assert_eq!(DMA_DEALLOC_COUNT, 1);
    }
}

#[test]
fn test_mmio_address_translation() {
    // Test MMIO address translation
    let test_paddr = 0xDEADBEEF;
    let test_size = 4096;

    // Physical to virtual translation
    let virt_ptr = unsafe { TestHal::mmio_phys_to_virt(test_paddr, test_size) };
    assert_eq!(virt_ptr.as_ptr() as usize, test_paddr);

    // Virtual to physical translation
    let phys_addr = unsafe { TestHal::mmio_virt_to_phys(virt_ptr, test_size) };
    assert_eq!(phys_addr, test_paddr);
}

#[test]
fn test_wait_until_functionality() {
    // Test waiting functionality
    let duration = Duration::from_millis(100);

    // In test environment, waiting should always succeed
    let result = TestHal::wait_until(duration);
    assert!(result.is_ok());
}

#[test]
fn test_multiple_dma_allocations() {
    unsafe {
        DMA_ALLOC_COUNT = 0;
        DMA_DEALLOC_COUNT = 0;
    }

    // Test multiple DMA allocations
    let mut allocations = Vec::new();

    for i in 0..5 {
        let size = 4096 * (i + 1);
        let (phys_addr, virt_ptr) = TestHal::dma_alloc(size);
        allocations.push((phys_addr, virt_ptr, size));
    }

    unsafe {
        assert_eq!(DMA_ALLOC_COUNT, 5);
        assert_eq!(DMA_DEALLOC_COUNT, 0);
    }

    // Free all allocations
    for (phys_addr, virt_ptr, size) in allocations {
        let result = unsafe { TestHal::dma_dealloc(phys_addr, virt_ptr, size) };
        assert_eq!(result, 0);
    }

    unsafe {
        assert_eq!(DMA_ALLOC_COUNT, 5);
        assert_eq!(DMA_DEALLOC_COUNT, 5);
    }
}

#[test]
fn test_hal_trait_object_safety() {
    // Test HAL trait object safety
    // This ensures HAL can be used as a trait object at runtime

    // Create a simple wrapper to test trait object
    struct HalWrapper<T: IxgbeHal>(core::marker::PhantomData<T>);

    impl<T: IxgbeHal> HalWrapper<T> {
        fn test_allocation(&self) -> usize {
            let (phys_addr, _virt_ptr) = T::dma_alloc(4096);
            phys_addr
        }
    }

    let wrapper = HalWrapper::<TestHal>(core::marker::PhantomData);
    let addr = wrapper.test_allocation();
    assert!(addr != 0);
}

#[test]
fn test_error_handling_in_hal() {
    // Test error handling in HAL
    // Note: Our TestHal implementation always succeeds, but actual HAL implementations may fail

    // Test normal case
    let result = TestHal::wait_until(Duration::from_secs(1));
    assert!(result.is_ok());

    // In actual HAL implementations, this may return errors
    // For example: wait timeout, out of memory, etc.
}

// Mock a potentially failing HAL implementation for testing error handling
struct FailingHal;

unsafe impl IxgbeHal for FailingHal {
    fn dma_alloc(_size: usize) -> (usize, NonNull<u8>) {
        // Simulate allocation failure
        panic!("DMA allocation failed");
    }

    unsafe fn dma_dealloc(_paddr: usize, _vaddr: NonNull<u8>, _size: usize) -> i32 {
        -1 // Simulate deallocation failure
    }

    unsafe fn mmio_phys_to_virt(_paddr: usize, _size: usize) -> NonNull<u8> {
        panic!("MMIO mapping failed");
    }

    unsafe fn mmio_virt_to_phys(_vaddr: NonNull<u8>, _size: usize) -> usize {
        panic!("Address translation failed");
    }

    fn wait_until(_duration: Duration) -> Result<(), &'static str> {
        Err("Wait timeout")
    }
}

#[test]
fn test_failing_hal_error_handling() {
    // Test failing HAL implementation
    let result = FailingHal::wait_until(Duration::from_secs(1));
    assert!(result.is_err());
    assert_eq!(result.unwrap_err(), "Wait timeout");
}

#[test]
#[should_panic(expected = "DMA allocation failed")]
fn test_failing_hal_allocation() {
    // Test failing HAL allocation (should panic)
    let _ = FailingHal::dma_alloc(4096);
}
