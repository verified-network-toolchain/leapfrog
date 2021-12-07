# Benchmarks overview

This file is meant to house descriptions of the different benchmarks that we maintain in `lib/P4automata/Benchmarks`. In particular, it keeps track of two considerations:
* _utility_ --- i.e., the benchmark's practical purpose for network parser verification
* _novelty_ --- i.e., how this benchmark demonstrates something that is different from the other benchmarks

## BabyIP
This benchmark compares two parsers for a "baby" version of IP+TCP/UDP. A `BabyIP` header looks like this:
```
+------------+------------+--------------+
| src (8bit) | dst (8bit) | proto (4bit) |
+------------+------------+--------------+
```
If `type` is `0x01`, then the next bits should be a `BabyUDP` header, which looks like this:
```
+--------------+--------------+--------------+
| sport (8bit) | dport (8bit) | flags (4bit) |
+--------------+--------------+--------------+
```
On the other hand, if `type` is `0x00`, then the next bits should be a `BabyTCP` header, which looks like this:
```
+--------------+--------------+--------------+------------+
| sport (8bit) | dport (8bit) | flags (4bit) | seq (8bit) |
+--------------+--------------+--------------+------------+
```

### BabyIP1
The first parser, called `BabyIP1`, handles this format in a straightforward fashion. It has three headers, `ip` (20 bits), `udp` (20 bits) and `tcp` (28 bits). It first parses the `BabyIP` header into `ip`, and then looks at the `proto` field to find out whether it should parse a `BabyUDP` or `BabyTCP` header next, like this:
```
+-------------+                         +--------------+
| Start       |                         | ParseUDP     |     +--------+
|~~~~~~~~~~~~~|--( ip[19:16] = 0x01 )-->|~~~~~~~~~~~~~~|---->| accept |
| extract(ip) |                         | extract(udp) |     +--------+   
+-------------+                         +--------------+         ^
       |                                                         |
       |                                +--------------+         |
       |                                | ParseTCP     |         |
       \---------( ip[19:16] = 0x00 )-->|~~~~~~~~~~~~~~|---------/
                                        | extract(tcp) |
                                        +--------------+
```

### BabyIP2
The second parser, called `BabyIP2`, is slightly different. It exploits the fact that the `BabyUDP` and `BabyTCP` headers have a common prefix. This means that we can parse `BabyIP` plus this prefix in one go, and then look at the `proto` field to see if we need to extract more bits (in the case of `BabyTCP`. To accomplish this, we use two headers: `combi` (40 bits) and `seq` (8 bits). The parser works as follows:
```
+----------------+
| Start          |                            +--------+
|~~~~~~~~~~~~~~~~|--( combi[19:16] = 0x01 )-->| accept |
| extract(combi) |                            +--------+   
+----------------+                                ^
       |                                          |
       |                                +--------------+
       |                                | ParseSeq     |
       \----( combi[19:16] = 0x00 )---->|~~~~~~~~~~~~~~|
                                        | extract(seq) |
                                        +--------------+
```

### Utility
Protocol parsers maintain the best data throughput when they consume as many bits as possible in one go --- i.e., with as few as possible pauses between those bursts. Some hardware targets even set minimum requirements for bit extraction. This benchmark shows one way of optimizing for this constraint, by merging a common prefix among expected data.

Note that while the protocol used here is a toy, something similar is also possible for real TCP and UDP, since they share a common prefix of source and destination port (16 bits).

### Novelty
The one thing that is showcased best by this benchmark is that we can compare parsers that have `extract` calls of different sizes. In other words, there is no need for the number of bits extracted by states to align perfectly, and we can compare a configuration where bits are still being buffered to a configuration that is about to execute a transition.

Note that almost all other benchmarks exhibit this feature in some way. However, this benchmark is still nice because it focuses on this feature alone, so there is no noise from other things.

### Other remarks
Note that the `proto` field can also have values different from `0x00` or `0x01`. In that case, the packet is rejected. What's somewhat interesting is that, in `BabyIP1`, such a packet is _explicitly_ rejected by the transition to `reject` from `Start` (not drawn). For `BabyIP2`, it may also happen `proto` is neither `0x00` nor `0x01`, and fewer than 20 bits follow (in which case the packet is rejected _implicitly_ for lack of bits), or at least 20 bits follow (in which case the packet is rejected _explicitly_ by the transition from `Start` to `reject`).

## Simple versus Sloppy
This benchmark compares two (arguably real, but rather rough) parsers for Ethernet+IPv4/IPv6. An Ethernet header looks like this:
```
+---------------+---------------+---------------------+
| src (48 bits) | dst (48 bits) | ethertype (16 bits) |
+---------------+---------------+---------------------+
```
In this scenario, an Ethernet frame is followed by either an IPv4 header (if `ethertype` is `0x8600`) or an IPv6 header (if `ethertype` is `0x86DD`). 

Both parsers that follow use the same header structure, with three fields named `ethernet` (112 bits), `ipv4` (128 bits) and `ipv6` (288 bits). Note that to keep this example simple, we treat each header as a datablob; one can imagine splitting them up in different fields as well.

### Sloppy
The `Sloppy` parser reads in the Ethernet header. If `ethertype` is `0x86DD`, it parses an IPv6 header. Otherwise, it assumes that what follows is an IPv4 header, and acts accordingly.
```
+-------------------+                                    +---------------+
| ParseEthernet     |                                    | ParseIPv6     |    +--------+
|~~~~~~~~~~~~~~~~~~~|---( ethernet[111:96] = 0x86dd )--->|~~~~~~~~~~~~~~~|--->| accept |
| extract(ethernet) |                                    | extract(ipv6) |    +--------+
+-------------------+                                    +---------------+        ^
         |                                                                        |
         |                                               +---------------+        |
         |                                               | ParseIPv4     |        |
         \-----------------------( default )------------>|~~~~~~~~~~~~~~~|--------/
                                                         | extract(ipv4) |
                                                         +---------------+
```

### Strict
The `Strict` parser acts very similarly to the `Sloppy` parser, except that it also checks whether `ethertype` is `0x8600` before parsing an IPv4 header, and rejects otherwise, like this:
```
+-------------------+                                    +---------------+
| ParseEthernet     |                                    | ParseIPv6     |    +--------+
|~~~~~~~~~~~~~~~~~~~|---( ethernet[111:96] = 0x86dd )--->|~~~~~~~~~~~~~~~|--->| accept |
| extract(ethernet) |                                    | extract(ipv6) |    +--------+
+-------------------+                                    +---------------+        ^
         |                                                                        |
         |                                               +---------------+        |
         |                                               | ParseIPv4     |        |
         \--------------( ethernet[111:96] = 0x8600 )--->|~~~~~~~~~~~~~~~|--------/
                                                         | extract(ipv4) |
                                                         +---------------+
```

### Utility
Every check that a parser needs to do before consuming bits slows down throughput slightly. The `Sloppy` parser slightly optimizes for this by _assuming_ that anything that is not an IPv6 packet must be an IPv4 packet. 

Clearly, the `Sloppy` parser accepts more packets than the `Strict` parser. In particular, packets that (1) do not have an ethertype of `0x8600` or `0x86DD` and (2) have exactly 128 bits following the ethernet header are accepted by `Sloppy` but not by `Strict`. In practice, this discrepancy is resolved by the control logic, which checks the `ethertype` post-hoc (i.e., after acceptance) and drops anything that is unexpected.

### Novelty
We perform two benchmarks that involve these parsers.

*  The first benchmark is unique in that it does not simply assert that states must be equally accepting. Instead, it compares packets accepted by `Sloppy` where `ethertype` is one of `0x8600` or `0x86DD` to packets accepted by `Strict`. This additional constraint models the post-hoc filtering that should be performed by the control logic when the `Sloppy` parser is used.

* The second benchmark is unique in that it is not concerned with the languages of the parsers, but rather the stores that they produce. It asserts that, if both parsers accept, then they have equivalent stores, meaning that (1) they have the same `ethernet` header, and (2) if `ethertype` is `0x8600` (respectively `0x86DD`), then they have the same `ipv4` (respectively `ipv6`) header.

### Other remarks
One can also imagine a generalized version where $n$ ethertypes are considered, and anything not matching the first $n-1$ ethertypes is assumed to be of the $n$th etertype.

Even though both parsers use the same header format, the second proof could also be phrased for headers that are wildly different in structure; the main challenge is coming up with the relation that you want to establish. This can be somewhat tricky, as not all fields will be populated by all packets, which requires the conditions on `ethertype`.
