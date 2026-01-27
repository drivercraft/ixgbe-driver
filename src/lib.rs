//! # ixgbe-driver
//!
//! A `no_std` driver implementation for Intel 82599+ 10 Gigabit Ethernet NICs.
//!
//! This crate provides a safe, low-level driver for the Intel 82599 (ixgbe) family of
//! network interface cards. It is designed to be used in embedded and bare-metal environments
//! where the standard library is not available.
//!
//! ## Features
//!
//! - `no_std` compatible - works without the standard library
//! - Multi-queue support for both RX and TX
//! - MSI/MSI-X interrupt support (with `irq` feature)
//! - Memory pool management for efficient packet buffer allocation
//! - Zero-copy packet handling
//!
//! ## Basic Usage
//!
//! ```rust,ignore
//! use ixgbe_driver::{IxgbeDevice, IxgbeHal, MemPool, NicDevice};
//!
//! // First, implement the IxgbeHal trait for your platform
//! struct MyHal;
//!
//! unsafe impl IxgbeHal for MyHal {
//!     // Implement required methods...
//! }
//!
//! // Initialize the device
//! let pool = MemPool::allocate::<MyHal>(4096, 2048)?;
//! let device = IxgbeDevice::<MyHal, 512>::init(
//!     pci_bar_addr,
//!     pci_bar_size,
//!     num_rx_queues,
//!     num_tx_queues,
//!     &pool,
//! )?;
//!
//! // Send and receive packets
//! let tx_buf = IxgbeNetBuf::alloc(&pool, packet_size)?;
//! device.send(queue_id, tx_buf)?;
//!
//! device.receive_packets(queue_id, num_packets, |rx_buf| {
//!     // Handle received packet
//! })?;
//! ```
//!
//! ## Hardware Abstraction Layer (HAL)
//!
//! This driver requires the user to implement the [`IxgbeHal`] trait, which provides
//! platform-specific operations such as:
//! - DMA memory allocation/deallocation
//! - MMIO address translation
//! - Timing/waiting operations
//!
//! ## Platform Support
//!
//! The ixgbe driver supports Intel 82599 and compatible 10GbE controllers including:
//! - Intel 82599ES
//! - Intel X540
//! - Intel X550/X552
//!
//! ## Interrupt Modes
//!
//! The driver supports three operation modes:
//! - **Polling mode** (default): No interrupts, the driver continuously polls for packets
//! - **MSI mode**: Message Signaled Interrupts (with `irq` feature)
//! - **MSI-X mode**: Extended MSI with multiple vectors (with `irq` feature)

#![no_std]
#![deny(warnings)]
#![deny(missing_docs)]
#![allow(dead_code)]

mod constants;
mod descriptor;
mod hal;
mod interrupts;
mod ixgbe;
mod memory;

extern crate alloc;
#[macro_use]
extern crate log;

pub use hal::IxgbeHal;
pub use ixgbe::{IxgbeDevice, IxgbeNetBuf};

pub use memory::{alloc_pkt, MemPool, PhysAddr};

/// Vendor ID for Intel.
pub const INTEL_VEND: u16 = 0x8086;

/// Device ID for the 82599ES, used to identify the device from the PCI space.
pub const INTEL_82599: u16 = 0x10FB;

/// Error type for ixgbe driver operations.
///
/// This enum represents the various error conditions that can occur when
/// interacting with the ixgbe device.
#[derive(Debug)]
pub enum IxgbeError {
    /// The queue size is not aligned (not a power of 2).
    ///
    /// Hardware descriptor rings require sizes that are powers of 2.
    QueueNotAligned,
    /// There are not enough descriptors available in the queue.
    ///
    /// The transmit or receive queue is full. The caller should retry later
    /// after processing pending packets.
    QueueFull,
    /// No memory available.
    ///
    /// The memory pool is exhausted or DMA allocation failed.
    NoMemory,
    /// The allocated page is not properly aligned.
    ///
    /// DMA memory must be aligned to page boundaries.
    PageNotAligned,
    /// The device is not ready for the requested operation.
    ///
    /// This typically means a packet receive operation was attempted when
    /// no packets are available.
    NotReady,
    /// Invalid queue ID.
    ///
    /// The specified `queue_id` does not exist on this device.
    InvalidQueue,
}

/// Result type for ixgbe driver functions.
///
/// A type alias for `Result` with [`IxgbeError`] as the error type.
pub type IxgbeResult<T = ()> = Result<T, IxgbeError>;

/// Generic network device interface.
///
/// This trait provides a common interface for network device drivers, allowing
/// protocol stacks to be implemented independently of the specific NIC hardware.
/// It is inspired by the ixy driver approach and provides methods for:
///
/// - Device identification and configuration
/// - Packet transmission and reception
/// - Queue management
/// - Statistics tracking
///
/// # Example
///
/// ```rust,ignore
/// use ixgbe_driver::{IxgbeDevice, NicDevice};
///
/// let mut device = IxgbeDevice::<MyHal, 512>::init(...)?;
///
/// // Check device info
/// println!("Driver: {}", device.get_driver_name());
/// println!("MAC: {:02x?}", device.get_mac_addr());
/// println!("Speed: {} Mbit/s", device.get_link_speed());
///
/// // Send and receive
/// while device.can_receive(0)? {
///     device.receive_packets(0, 32, |packet| {
///         // Process packet
///     })?;
/// }
/// ```
pub trait NicDevice<H: IxgbeHal> {
    /// Returns the driver's name.
    ///
    /// This is a simple string identifier such as "ixgbe" or "virtio".
    fn get_driver_name(&self) -> &str;

    /// Returns the MAC (Ethernet) address of this device.
    ///
    /// Returns a 6-byte array representing the layer 2 address.
    fn get_mac_addr(&self) -> [u8; 6];

    /// Resets the network card's statistics registers.
    ///
    /// Clears all packet and byte counters maintained by the hardware.
    /// This affects the values returned by subsequent statistics reads.
    fn reset_stats(&mut self);

    /// Returns the link speed of the network card.
    ///
    /// Returns the current link speed in Mbit/s (e.g., 10000 for 10GbE).
    /// Returns 0 if the link is down.
    fn get_link_speed(&self) -> u16;

    /// Polls the transmit queue for completed packets and frees their buffers.
    ///
    /// This method reclaims transmit descriptors that have been completed by
    /// the hardware and returns their packet buffers to the memory pool.
    ///
    /// # Arguments
    ///
    /// * `queue_id` - The transmit queue ID to clean
    ///
    /// # Errors
    ///
    /// Returns [`IxgbeError::InvalidQueue`] if `queue_id` is out of range.
    fn recycle_tx_buffers(&mut self, queue_id: u16) -> IxgbeResult;

    /// Receives up to `packet_nums` packets from the network.
    ///
    /// This method receives packets from the specified queue and invokes the
    /// closure `f` for each received packet. Using a closure avoids dynamic
    /// memory allocation and allows the caller to handle packets efficiently.
    ///
    /// # Arguments
    ///
    /// * `queue_id` - The receive queue ID to read from
    /// * `packet_nums` - Maximum number of packets to receive
    /// * `f` - Closure called for each received packet with the [`IxgbeNetBuf`]
    ///
    /// # Returns
    ///
    /// Returns the number of packets actually received.
    ///
    /// # Errors
    ///
    /// - [`IxgbeError::NotReady`] - No packets are currently available
    /// - [`IxgbeError::InvalidQueue`] - `queue_id` is out of range
    ///
    /// # Example
    ///
    /// ```rust,ignore
    /// let count = device.receive_packets(0, 32, |packet| {
    ///     let data = packet.packet();
    ///     // Handle packet data
    /// })?;
    /// println!("Received {} packets", count);
    /// ```
    fn receive_packets<F>(&mut self, queue_id: u16, packet_nums: usize, f: F) -> IxgbeResult<usize>
    where
        F: FnMut(IxgbeNetBuf);

    /// Sends a packet to the network.
    ///
    /// Queues the packet for transmission on the specified queue. The actual
    /// transmission happens asynchronously in the hardware.
    ///
    /// # Arguments
    ///
    /// * `queue_id` - The transmit queue ID to send on
    /// * `tx_buf` - The packet buffer to send
    ///
    /// # Errors
    ///
    /// - [`IxgbeError::QueueFull`] - The transmit queue has no available descriptors
    /// - [`IxgbeError::InvalidQueue`] - `queue_id` is out of range
    fn send(&mut self, queue_id: u16, tx_buf: IxgbeNetBuf) -> IxgbeResult;

    /// Checks whether a packet can be received from the specified queue.
    ///
    /// Returns `true` if at least one packet is available in the receive queue.
    ///
    /// # Errors
    ///
    /// Returns [`IxgbeError::InvalidQueue`] if `queue_id` is out of range.
    fn can_receive(&self, queue_id: u16) -> IxgbeResult<bool>;

    /// Checks whether a packet can be sent on the specified queue.
    ///
    /// Returns `true` if the transmit queue has at least one free descriptor.
    ///
    /// # Errors
    ///
    /// Returns [`IxgbeError::InvalidQueue`] if `queue_id` is out of range.
    fn can_send(&self, queue_id: u16) -> IxgbeResult<bool>;
}

/// Network device statistics.
///
/// Holds counters for sent and received packets and bytes.
/// These values can be read from the hardware's statistic registers.
#[derive(Default, Copy, Clone)]
pub struct DeviceStats {
    /// Number of received packets.
    pub rx_pkts: u64,
    /// Number of transmitted packets.
    pub tx_pkts: u64,
    /// Number of received bytes.
    pub rx_bytes: u64,
    /// Number of transmitted bytes.
    pub tx_bytes: u64,
}

impl core::fmt::Display for DeviceStats {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "rx_pkts: {}, tx_pkts: {}, rx_bytes: {}, tx_bytes: {}",
            self.rx_pkts, self.tx_pkts, self.rx_bytes, self.tx_bytes
        )
    }
}
