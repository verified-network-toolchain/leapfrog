# Copyright 2019-present Cornell University
#
# Licensed under the Apache License, Version 2.0 (the "License"); you may not
# use this file except in compliance with the License. You may obtain a copy
# of the License at
#
#   http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
# WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
# License for the specific language governing permissions and limitations
# under the License.

.PHONY: all build install clean

all: build

build: _CoqProject
	dune build -p leapfrog

install: _CoqProject
	dune install -p leapfrog

clean:
	rm _CoqProject
	dune clean -p leapfrog

min-imports:
	find lib/ -name "*.v" | sed "s#^./##" | xargs -i coq-min-imports {} -cmi-verbose -cmi-replace $(shell cat _CoqProject)

benchmarks-small: ethernet selfcomparison mpls sloppystrict ipfilter

benchmarks-large: ipoptions3 edgeself edgetrans datacenterself serviceproviderself enterpriseself

ipfilter: build
	xargs coqc lib/Benchmarks/IPFilterProof.v < _CoqProject | grep "Tactic call"

mpls: build
	xargs coqc lib/Benchmarks/MPLSVectorizedProof.v < _CoqProject | grep "Tactic call"

selfcomparison: build
	xargs coqc lib/Benchmarks/SelfComparisonProof.v < _CoqProject | grep "Tactic call"

ethernet: build
	xargs coqc lib/Benchmarks/EthernetProof.v < _CoqProject | grep "Tactic call"

sloppystrict: build
	xargs coqc lib/Benchmarks/SloppyStrictProof.v < _CoqProject | grep "Tactic call"

ipoptions3: build
	nohup /usr/bin/time -v xargs coqc lib/Benchmarks/IPOptions3Proof.v < _CoqProject > ipoptions_timing.out 2>&1 &

edgeself:
	nohup /usr/bin/time -v xargs coqc lib/Benchmarks/EdgeSelfProof.v < _CoqProject > edge_self_timing.out 2>&1 &

edgetrans:
	nohup /usr/bin/time -v xargs coqc lib/Benchmarks/EdgeTransProof.v < _CoqProject > edge_trans_timing.out 2>&1 &

datacenterself:
	nohup /usr/bin/time -v xargs coqc lib/Benchmarks/DatacenterSelfProof.v < _CoqProject > datacenter_self_timing.out 2>&1 &

enterpriseself:
	nohup /usr/bin/time -v xargs coqc lib/Benchmarks/EnterpriseSelfProof.v < _CoqProject > enterprise_self_timing.out 2>&1 &

serviceproviderself:
	nohup /usr/bin/time -v xargs coqc lib/Benchmarks/ServiceproviderSelfProof.v < _CoqProject > serviceprovider_self_timing.out 2>&1 &

_CoqProject: _CoqProject.noplugins
	cp _CoqProject.noplugins _CoqProject
	echo >> _CoqProject
	echo "-I $(OPAM_SWITCH_PREFIX)/lib/mirrorsolve" >> _CoqProject
