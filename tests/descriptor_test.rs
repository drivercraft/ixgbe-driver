//! Functional tests - Descriptor operations
//!
//! These tests verify descriptor functionality in simulated environments, including:
//! - Descriptor initialization
//! - Descriptor state read/write
//! - Descriptor command configuration

use bit_field::BitField;
use ixgbe_driver::descriptor::*;
use volatile::Volatile;

#[test]
fn test_rx_descriptor_initialization() {
    // Test RX descriptor initialization
    let mut desc = AdvancedRxDescriptor {
        packet_buffer_address: Volatile::new(0),
        header_buffer_address: Volatile::new(0),
    };

    desc.init();

    assert_eq!(desc.packet_buffer_address.read(), 0);
    assert_eq!(desc.header_buffer_address.read(), 0);
}

#[test]
fn test_rx_descriptor_address_setting() {
    // Test RX descriptor address configuration
    let mut desc = AdvancedRxDescriptor {
        packet_buffer_address: Volatile::new(0),
        header_buffer_address: Volatile::new(0),
    };

    let test_addr = 0xDEADBEEF as u64;
    desc.set_packet_address(test_addr);

    assert_eq!(desc.packet_buffer_address.read(), test_addr);
}

#[test]
fn test_rx_descriptor_status_reset() {
    // Test RX descriptor status reset
    let mut desc = AdvancedRxDescriptor {
        packet_buffer_address: Volatile::new(0xFFFF_FFFF_FFFF_FFFF),
        header_buffer_address: Volatile::new(0xFFFF_FFFF_FFFF_FFFF),
    };

    desc.reset_status();

    assert_eq!(desc.header_buffer_address.read(), 0);
    // packet_buffer_address should remain unchanged
    assert_eq!(desc.packet_buffer_address.read(), 0xFFFF_FFFF_FFFF_FFFF);
}

#[test]
fn test_rx_descriptor_status_flags() {
    // Test RX descriptor status flag bits
    let mut desc = AdvancedRxDescriptor {
        packet_buffer_address: Volatile::new(0),
        header_buffer_address: Volatile::new(0),
    };

    // Initial state: DD bit not set
    assert!(!desc.descriptor_done());
    assert!(!desc.end_of_packet());

    // Set DD bit (descriptor done)
    desc.header_buffer_address.write(RX_STATUS_DD as u64);
    assert!(desc.descriptor_done());
    assert!(!desc.end_of_packet());

    // Set EOP bit (end of packet)
    desc.header_buffer_address
        .write((RX_STATUS_DD | RX_STATUS_EOP) as u64);
    assert!(desc.descriptor_done());
    assert!(desc.end_of_packet());
}

#[test]
fn test_rx_descriptor_packet_info() {
    // Test RX descriptor packet info reading
    let mut desc = AdvancedRxDescriptor {
        packet_buffer_address: Volatile::new(0),
        header_buffer_address: Volatile::new(0),
    };

    // Set packet length
    let packet_len = 1500u64;
    desc.header_buffer_address.write(packet_len << 32);

    assert_eq!(desc.length(), packet_len);
    assert_eq!(desc.get_pkt_len(), packet_len);
}

#[test]
fn test_rx_descriptor_rss_info() {
    // Test RX descriptor RSS info
    let mut desc = AdvancedRxDescriptor {
        packet_buffer_address: Volatile::new(0),
        header_buffer_address: Volatile::new(0),
    };

    // Set RSS type
    let rss_type = 0b101u64;
    desc.packet_buffer_address.write(rss_type);

    assert_eq!(desc.get_rss_type(), rss_type);
}

#[test]
fn test_rx_descriptor_packet_type() {
    // Test RX descriptor packet type
    let mut desc = AdvancedRxDescriptor {
        packet_buffer_address: Volatile::new(0),
        header_buffer_address: Volatile::new(0),
    };

    // Set packet type (12 bits)
    let packet_type = 0x234u64; // 12-bit value
    desc.packet_buffer_address.write(packet_type << 4);

    let written_value = desc.packet_buffer_address.read();
    let retrieved_type = desc.get_packet_type();
    println!(
        "packet_type: 0x{:x}, written: 0x{:x}, retrieved: 0x{:x}",
        packet_type, written_value, retrieved_type
    );

    assert_eq!(desc.get_packet_type(), packet_type);
}

#[test]
fn test_tx_descriptor_initialization() {
    // Test TX descriptor initialization
    let mut desc = AdvancedTxDescriptor {
        packet_buffer_address: Volatile::new(0),
        data_len: Volatile::new(0),
        dtyp_mac_rsv: Volatile::new(0),
        dcmd: Volatile::new(0),
        paylen_popts_cc_idx_sta: Volatile::new(0),
    };

    desc.init();

    assert_eq!(desc.packet_buffer_address.read(), 0);
    assert_eq!(desc.data_len.read(), 0);
    assert_eq!(desc.dtyp_mac_rsv.read(), 0);
    assert_eq!(desc.dcmd.read(), 0);
    assert_eq!(desc.paylen_popts_cc_idx_sta.read(), 0);
}

#[test]
fn test_tx_descriptor_send_setup() {
    // Test TX descriptor send configuration
    let mut desc = AdvancedTxDescriptor {
        packet_buffer_address: Volatile::new(0),
        data_len: Volatile::new(0),
        dtyp_mac_rsv: Volatile::new(0),
        dcmd: Volatile::new(0),
        paylen_popts_cc_idx_sta: Volatile::new(0),
    };

    let buffer_addr = 0xDEADBEEF as u64;
    let buffer_len = 1500u16;

    desc.send(buffer_addr, buffer_len);

    assert_eq!(desc.packet_buffer_address.read(), buffer_addr);
    assert_eq!(desc.data_len.read(), buffer_len);
    assert_eq!(desc.dtyp_mac_rsv.read(), TX_DTYP_ADV);
    assert_eq!(
        desc.paylen_popts_cc_idx_sta.read(),
        (buffer_len as u32) << TX_PAYLEN_SHIFT
    );
    assert_eq!(
        desc.dcmd.read(),
        TX_CMD_DEXT | TX_CMD_RS | TX_CMD_IFCS | TX_CMD_EOP
    );
}

#[test]
fn test_tx_descriptor_command_flags() {
    // Test TX descriptor command flag bits
    let mut desc = AdvancedTxDescriptor {
        packet_buffer_address: Volatile::new(0),
        data_len: Volatile::new(0),
        dtyp_mac_rsv: Volatile::new(0),
        dcmd: Volatile::new(0),
        paylen_popts_cc_idx_sta: Volatile::new(0),
    };

    // Set various command flags
    let mut cmd = 0u8;
    cmd |= TX_CMD_EOP;
    cmd |= TX_CMD_IFCS;
    cmd |= TX_CMD_RS;
    cmd |= TX_CMD_DEXT;

    desc.dcmd.write(cmd);

    // Verify flag bits are set correctly
    assert_eq!(desc.dcmd.read() & TX_CMD_EOP, TX_CMD_EOP);
    assert_eq!(desc.dcmd.read() & TX_CMD_IFCS, TX_CMD_IFCS);
    assert_eq!(desc.dcmd.read() & TX_CMD_RS, TX_CMD_RS);
    assert_eq!(desc.dcmd.read() & TX_CMD_DEXT, TX_CMD_DEXT);
}

#[test]
fn test_descriptor_constants_consistency() {
    // Test descriptor constant consistency
    assert_eq!(TX_PAYLEN_SHIFT, 46 - 32);
    assert_eq!(TX_DTYP_ADV, 0x3 << 4);

    // Verify status constants don't conflict
    assert_ne!(RX_STATUS_DD, RX_STATUS_EOP);
    assert_ne!(TX_STATUS_DD, 0); // TX_STATUS_DD should be non-zero
}

#[test]
fn test_descriptor_bit_field_operations() {
    // Test bit field operation correctness
    let mut value: u64 = 0;

    // Test setting and clearing bits
    value = value | (0b101 << 4); // Set value at bits 4-6
    assert_eq!(value.get_bits(4..7), 0b101);

    value = value & !(0b111 << 4); // Clear bits 4-6
    assert_eq!(value.get_bits(4..7), 0);

    // Test boundary cases
    value = u64::MAX;
    assert_eq!(value.get_bits(0..1), 1);
    assert_eq!(value.get_bits(63..64), 1);
}
