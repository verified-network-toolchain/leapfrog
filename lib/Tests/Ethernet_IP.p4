/* -*- P4_16 -*- */
#include "core.p4"
#include "v1model.p4"
// From https://github.com/p4lang/tutorials/blob/master/exercises/basic_tunnel/solution/basic_tunnel.p4 
const bit<16> TYPE_IPV4 = 0x800;

/*************************************************************************
*********************** H E A D E R S  ***********************************
*************************************************************************/

typedef bit<9>  egressSpec_t;
typedef bit<48> macAddr_t;
typedef bit<32> ip4Addr_t;

header ethernet_t {
    macAddr_t dstAddr;
    macAddr_t srcAddr;
    bit<16>   etherType;
}

header ethernet2_t {
    bit<24> dstAddr1;
    bit<24> dstAddr2;
    bit<24> srcAddr1;
    bit<24> srcAddr2;
    bit<8>   etherType1;
    bit<8>   etherType2;
}

header ipv4_t {
    bit<4>    version;
    bit<4>    ihl;
    bit<8>    diffserv;
    bit<16>   totalLen;
    bit<16>   identification;
    bit<3>    flags;
    bit<13>   fragOffset;
    bit<8>    ttl;
    bit<8>    protocol;
    bit<16>   hdrChecksum;
    ip4Addr_t srcAddr;
    ip4Addr_t dstAddr;
}

struct metadata {
    /* empty */
}

struct headers {
    ethernet_t   ethernet;
    ethernet2_t  ethernet2;
    ipv4_t       ipv4;
}

/*************************************************************************
*********************** P A R S E R  ***********************************
*************************************************************************/
const bit<4>  PARSER_NUM = 0x0;
parser extract_only(packet_in p, out headers hdr) {
    state start {
        p.extract(hdr.ethernet);
        p.extract(hdr.ipv4);
        transition accept;
    }
}

parser advance(packet_in p, out headers hdr) {
    state start {
        p.advance(96);
        transition select (p.lookahead<bit<16>>()) {
            0x0800: adv;
            _ : reject;
        }
    }    

    state adv {
        p.advance(16);
        p.extract(hdr.ipv4);
        transition accept;
    }
}

parser ethernetV2(packet_in p, out headers hdr) {
    state start {
        p.extract(hdr.ethernet2);
        transition select(hdr.ethernet2.etherType2) {
            0x00: check_etherType1;
            _ : reject;
        }
    }

    state check_etherType1 {
        transition select(hdr.ethernet2.etherType1) {
            0x80: accept;
            _ : reject;
        }
    }
}


parser MyParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {
    
    extract_only() parser_extract;
    advance() parser_advance;
    ethernetV2() parser_ethernet2;

    state start {
        transition select (PARSER_NUM) {
            0x0: parse_ethernet;
            0x1: parse_extract;
            0x2: parse_advance;
            0x3: parse_ethernet2; // transition select on partial bits of 0x0800
            default: reject;
        }
    }

    state parse_ethernet2 {
        parser_ethernet2.apply(packet, hdr);
        transition accept;
    }

    state parse_extract {
        parser_extract.apply(packet, hdr);
        transition accept;
    }

    state parse_advance {
        parser_advance.apply(packet, hdr);
        transition accept;
    }

    state parse_ethernet {
        packet.extract(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
            TYPE_IPV4: parse_ipv4;
            default: accept;
        }
    }

    state parse_ipv4 {
        packet.extract(hdr.ipv4);
        transition accept;
    }

}

/*************************************************************************
************   C H E C K S U M    V E R I F I C A T I O N   *************
*************************************************************************/

control MyVerifyChecksum(inout headers hdr, inout metadata meta) {   
    apply {  }
}


/*************************************************************************
**************  I N G R E S S   P R O C E S S I N G   *******************
*************************************************************************/

control MyIngress(inout headers hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {
    action drop() {
        mark_to_drop(standard_metadata);
    }
    
    action ipv4_forward(macAddr_t dstAddr, egressSpec_t port) {
        standard_metadata.egress_spec = port;
        hdr.ethernet.srcAddr = hdr.ethernet.dstAddr;
        hdr.ethernet.dstAddr = dstAddr;
        hdr.ipv4.ttl = hdr.ipv4.ttl - 1;
    }
    
    table ipv4_lpm {
        key = {
            hdr.ipv4.dstAddr: lpm;
        }
        actions = {
            ipv4_forward;
            drop;
            NoAction;
        }
        size = 1024;
        default_action = drop();
    }

    apply {
        if (hdr.ipv4.isValid()) {
            // Process only non-tunneled IPv4 packets
            ipv4_lpm.apply();
        }
    }
}

/*************************************************************************
****************  E G R E S S   P R O C E S S I N G   *******************
*************************************************************************/

control MyEgress(inout headers hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
    apply {  }
}

/*************************************************************************
*************   C H E C K S U M    C O M P U T A T I O N   **************
*************************************************************************/

control MyComputeChecksum(inout headers  hdr, inout metadata meta) {
     apply {
	update_checksum(
	    hdr.ipv4.isValid(),
            { hdr.ipv4.version,
	      hdr.ipv4.ihl,
              hdr.ipv4.diffserv,
              hdr.ipv4.totalLen,
              hdr.ipv4.identification,
              hdr.ipv4.flags,
              hdr.ipv4.fragOffset,
              hdr.ipv4.ttl,
              hdr.ipv4.protocol,
              hdr.ipv4.srcAddr,
              hdr.ipv4.dstAddr },
            hdr.ipv4.hdrChecksum,
            HashAlgorithm.csum16);
    }
}

/*************************************************************************
***********************  D E P A R S E R  *******************************
*************************************************************************/

control MyDeparser(packet_out packet, in headers hdr) {
    apply {
        packet.emit(hdr.ethernet);
        packet.emit(hdr.ipv4);
    }
}

/*************************************************************************
***********************  S W I T C H  *******************************
*************************************************************************/

V1Switch(
MyParser(),
MyVerifyChecksum(),
MyIngress(),
MyEgress(),
MyComputeChecksum(),
MyDeparser()
) main;