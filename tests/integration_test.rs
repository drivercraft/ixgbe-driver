//! System-level integration tests
//!
//! These tests verify integration between components and system-level functionality,
//! focusing on end-to-end testing using public APIs.

use ixgbe_driver::{alloc_pkt, IxgbeError, IxgbeHal, MemPool};
use std::ptr::NonNull;
use std::time::Duration;

// Mock HAL implementation for integration testing
struct IntegrationTestHal;

unsafe impl IxgbeHal for IntegrationTestHal {
    fn dma_alloc(size: usize) -> (usize, NonNull<u8>) {
        let layout = std::alloc::Layout::from_size_align(size, 4096).unwrap();
        let ptr = unsafe { std::alloc::alloc(layout) };
        if ptr.is_null() {
            panic!("Memory allocation failed");
        }
        (ptr as usize, NonNull::new(ptr).unwrap())
    }

    unsafe fn dma_dealloc(_paddr: usize, vaddr: NonNull<u8>, size: usize) -> i32 {
        let layout = std::alloc::Layout::from_size_align(size, 4096).unwrap();
        std::alloc::dealloc(vaddr.as_ptr(), layout);
        0
    }

    unsafe fn mmio_phys_to_virt(_paddr: usize, _size: usize) -> NonNull<u8> {
        NonNull::new(0x1000 as *mut u8).unwrap()
    }

    unsafe fn mmio_virt_to_phys(_vaddr: NonNull<u8>, _size: usize) -> usize {
        0x1000
    }

    fn wait_until(_duration: Duration) -> Result<(), &'static str> {
        Ok(())
    }
}

#[test]
fn test_memory_pool_packet_integration() {
    // Test system-level integration of memory pool and packet allocation

    let pool =
        MemPool::allocate::<IntegrationTestHal>(1024, 2048).expect("Failed to create memory pool");

    // Verify basic pool properties
    assert_eq!(pool.entry_size(), 2048);

    // Test packet allocation and deallocation
    let packet1 = alloc_pkt(&pool, 1500).expect("Failed to allocate packet");
    let packet2 = alloc_pkt(&pool, 1500).expect("Failed to allocate packet");

    // Verify basic packet properties
    assert_eq!(packet1.len(), 1500);
    assert_eq!(packet2.len(), 1500);

    // Packets are automatically freed (via Drop trait)
}

#[test]
fn test_error_propagation() {
    // Test error propagation in the system

    // Test memory pool allocation failure
    let result = MemPool::allocate::<IntegrationTestHal>(4096, 100); // Invalid size
    assert!(matches!(result, Err(IxgbeError::PageNotAligned)));
}

#[test]
fn test_resource_management() {
    // Test resource management - allocate many packets then release

    let pool =
        MemPool::allocate::<IntegrationTestHal>(10, 2048).expect("Failed to create memory pool");

    // Allocate all available packets
    let mut packets = Vec::new();
    for _ in 0..10 {
        let packet = alloc_pkt(&pool, 1500).expect("Failed to allocate packet");
        packets.push(packet);
    }

    // Attempting to allocate more should fail
    assert!(alloc_pkt(&pool, 1500).is_none());

    // Release some packets
    packets.clear();

    // Should be able to allocate again
    let packet = alloc_pkt(&pool, 1500).expect("Failed to allocate packet after release");
    assert_eq!(packet.len(), 1500);
}

#[test]
fn test_performance_baseline() {
    // Performance baseline test - verify basic operation performance characteristics

    let pool =
        MemPool::allocate::<IntegrationTestHal>(1000, 2048).expect("Failed to create memory pool");

    // Measure allocation performance
    let start = std::time::Instant::now();
    for _ in 0..100 {
        let _packet = alloc_pkt(&pool, 1500).expect("Failed to allocate packet");
    }
    let duration = start.elapsed();

    // Verify completion within reasonable time (this test is mainly to establish a baseline)
    assert!(duration.as_millis() < 1000); // Should complete within 1 second
}
