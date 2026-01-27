//! Interrupt management for the ixgbe driver.
//!
//! This module provides structures and configuration for managing MSI and MSI-X
//! interrupts on Intel 82599 NICs. Interrupt support is optional and requires the
//! `irq` feature to be enabled.
//!
//! # Interrupt Types
//!
//! The Intel 82599 supports two interrupt mechanisms:
//!
//! - **MSI (Message Signaled Interrupts)**: Single interrupt vector
//! - **MSI-X (Extended MSI)**: Multiple interrupt vectors for per-queue interrupts
//!
//! # Interrupt Throttling
//!
//! Interrupt throttling (rate limiting) is controlled by the `itr_rate` field and
//! is expressed in units of 2μs. Common values:
//!
//! | Value | Time  | Interrupts/sec |
//! |-------|-------|----------------|
//! | 0x008 | 2μs   | ~488,200       |
//! | 0x028 | 10μs  | ~97,600        |
//! | 0xC8  | 50μs  | ~20,000        |
//! | 0x7D0 | 500μs | ~2,000         |

use alloc::vec::Vec;

/// The number of msi-x vectors this device can have.
/// It can be set from PCI space, but we took the value from the data sheet.
pub const IXGBE_MAX_MSIX_VECTORS: usize = 64;

/// Interrupt configuration for the ixgbe device.
///
/// This structure contains global interrupt settings for the device including
/// throttle rate, timeout, and per-queue configuration.
#[derive(Default)]
pub struct Interrupts {
    /// Whether interrupts are enabled for this device.
    pub interrupts_enabled: bool,
    /// Interrupt Throttling Rate (ITR) - controls the maximum interrupt rate.
    pub itr_rate: u32,
    /// The interrupt type (MSI or MSIX).
    pub interrupt_type: u64,
    /// Interrupt timeout in milliseconds (-1 to disable timeout).
    pub timeout_ms: i16,
    /// Interrupt settings per queue.
    pub queues: Vec<InterruptsQueue>,
}

/// Per-queue interrupt configuration.
///
/// Controls whether interrupts are enabled for a specific transmit or receive queue.
pub struct InterruptsQueue {
    /// Whether the interrupt is enabled for this queue.
    pub interrupt_enabled: bool,
}

/// The type of interrupt mechanism to use.
///
/// - `Msi`: Message Signaled Interrupts (single vector)
/// - `Msix`: Extended MSI (multiple vectors)
pub enum InterruptType {
    Msi,
    Msix,
}
