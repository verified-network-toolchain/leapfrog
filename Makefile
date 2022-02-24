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

benchmarks-large: ipoptions3 edgeself edgetrans datacenter serviceprovider enterprise

ipfilter: build
	xargs coqc lib/Benchmarks/IPFilterProof.v < _CoqProject

mpls: build
	xargs coqc lib/Benchmarks/MPLSVectorizedProof.v < _CoqProject

selfcomparison: build
	xargs coqc lib/Benchmarks/SelfComparisonProof.v < _CoqProject

ethernet: build
	xargs coqc lib/Benchmarks/EthernetProof.v < _CoqProject

sloppystrict: build
	xargs coqc lib/Benchmarks/SloppyStrictProof.v < _CoqProject

ipoptions3: build
	xargs coqc lib/Benchmarks/IPOptions3Proof.v < _CoqProject

edgeself:
	xargs coqc lib/Benchmarks/EdgeSelfProof.v < _CoqProject

edgetrans:
	xargs coqc lib/Benchmarks/EdgeTransProof.v < _CoqProject

datacenterself:
	xargs coqc lib/Benchmarks/DatacenterSelfProof.v < _CoqProject

enterpriseself:
	xargs coqc lib/Benchmarks/EnterpriseSelfProof.v < _CoqProject

serviceproviderself:
	xargs coqc lib/Benchmarks/ServiceproviderSelfProof.v < _CoqProject

_CoqProject: _CoqProject.noplugins
	cp _CoqProject.noplugins _CoqProject
	echo >> _CoqProject
	echo "-I $(OPAM_SWITCH_PREFIX)/lib/mirrorsolve" >> _CoqProject
	echo "-I $(OPAM_SWITCH_PREFIX)/lib/coq-memprof" >> _CoqProject
