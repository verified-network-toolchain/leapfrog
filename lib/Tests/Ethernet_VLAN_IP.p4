/* -*- P4_16 -*- */
#include "core.p4"
#include "v1model.p4"

const bit<16> TYPE_IPV4 = 0x800;
const bit<16> TYPE_VLAN = 0x8100;

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

header vlan_t {
    bit<16>   TPID;
    bit<16>   TCI;
    bit<16>    etherType;
}

header buf_t {
    bit<16> buffer;
}

struct metadata {
    /* empty */
}

struct headers {
    ethernet_t   ethernet;
    ipv4_t       ipv4;
    vlan_t       vlan;
    buf_t        buf;
}

/*************************************************************************
*********************** P A R S E R  ***********************************
*************************************************************************/
const bit<4>  PARSER_NUM = 0x0;

parser advance (packet_in packet, out headers hdr) {
    state start {
        packet.advance(64);
        transition peeker;
    }
    
    state peeker {
        packet.advance(16);
        transition select (packet.lookahead<bit<16>>()) {
            TYPE_IPV4: accept;
            TYPE_VLAN: parse_vlan;
            default : peeker;
        }
    }

    state parse_vlan {
        packet.extract(hdr.vlan);
        transition select(hdr.vlan.etherType) {
            TYPE_IPV4: accept;
            default: reject;
        }
    }
} 

parser loopLookahead(packet_in packet, out headers hdr) {
    state start {
        transition parse_ethernet;
    }

    state parse_ethernet {
        packet.extract(hdr.buf.buffer);
        transition select(hdr.buf.buffer) {
            TYPE_IPV4: accept;
            TYPE_VLAN: parse_vlan;
            default: parse_ethernet;
        }
    }

    state parse_vlan {
        packet.extract(hdr.vlan);
        transition select(hdr.vlan.etherType) {
            TYPE_IPV4: accept;
            default: reject;
        }
    }
} 

parser sepIPV4(packet_in packet, out headers hdr) {
    state start {
        transition parse_ethernet;
    }

    state parse_ethernet {
        packet.extract(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
            TYPE_IPV4: parse_ipv4;
            TYPE_VLAN: parse_vlan;
            default: reject;
        }
    }

    state parse_vlan {
        packet.extract(hdr.vlan);
        transition select(hdr.vlan.etherType) {
            TYPE_IPV4: parse_ipv4_2;
            default: reject;
        }
    }

    state parse_ipv4 {
        packet.extract(hdr.ipv4);
        transition accept;
    }
    
    state parse_ipv4_2 {
        packet.extract(hdr.ipv4);
        transition accept;
    }
} 

parser MyParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {
    sepIPV4() parser_separateIPV4;
    loopLookahead() parser_loopLookahead;
    advance() parser_advance;

    state start {
        transition select (PARSER_NUM) {
            0x0: parse_ethernet;
            0x1: parse_separateIPV4;
            0x2: parse_loopLookahead; 
            0x3: parse_advance;
            default: reject;
        }
    }

    state parse_advance {
        parser_advance.apply(packet, hdr);
        transition parse_ipv4;
    }

    state parse_separateIPV4 {
        parser_separateIPV4.apply(packet, hdr);
        transition accept;
    }

    state parse_loopLookahead {
        parser_loopLookahead.apply(packet, hdr);
        transition parse_ipv4;
    }

    state parse_ethernet {
        packet.extract(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
            TYPE_IPV4: parse_ipv4;
            TYPE_VLAN: parse_vlan;
            default: reject;
        }
    }

    state parse_vlan {
        packet.extract(hdr.vlan);
        transition select(hdr.vlan.etherType) {
            TYPE_IPV4: parse_ipv4;
            default: reject;
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