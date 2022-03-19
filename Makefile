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

AECINSTRUCTIONS=Instructions.pdf

.PHONY: all build install clean

all: build

build: _CoqProject
	dune build -p leapfrog

install: _CoqProject
	dune install -p leapfrog

clean:
	rm _CoqProject
	dune clean -p leapfrog
	rm -f $(AECINSTRUCTIONS)

min-imports:
	find lib/ -name "*.v" | sed "s#^./##" | xargs -i coq-min-imports {} -cmi-verbose -cmi-replace $(shell cat _CoqProject)

benchmarks-small: pipenv build
	cd benchmarking && pipenv run ./runner.py --size small

benchmarks-large: pipenv build
	cd benchmarking && pipenv run ./runner.py --size large

ipfilter: build
	xargs coqc lib/Benchmarks/IPFilterProof.v < _CoqProject

memorytall: build
	xargs coqc lib/Benchmarks/MemoryTallProof.v < _CoqProject | grep "Tactic call"

memorywide: build
	xargs coqc lib/Benchmarks/MemoryWideProof.v < _CoqProject | grep "Tactic call"

mpls: build
	xargs coqc lib/Benchmarks/MPLSVectorizedProof.v < _CoqProject

selfcomparison: build
	xargs coqc lib/Benchmarks/SelfComparisonProof.v < _CoqProject

ethernet: build
	xargs coqc lib/Benchmarks/EthernetProof.v < _CoqProject

sloppystrictstores: build
	xargs coqc lib/Benchmarks/SloppyStrictStores.v < _CoqProject

sloppystrictfilter: build
	xargs coqc lib/Benchmarks/SloppyStrictFilter.v < _CoqProject

ipoptions3: build
	xargs coqc lib/Benchmarks/IPOptions3Proof.v < _CoqProject
ipoptions2: build
	xargs coqc lib/Benchmarks/IPOptions2Proof.v < _CoqProject
ipoptions1: build
	xargs coqc lib/Benchmarks/IPOptions1Proof.v < _CoqProject

edgeself: build
	xargs coqc lib/Benchmarks/EdgeSelfProof.v < _CoqProject

edgetrans: build
	xargs coqc lib/Benchmarks/EdgeTransProof.v < _CoqProject

datacenterself: build
	xargs coqc lib/Benchmarks/DatacenterSelfProof.v < _CoqProject

enterpriseself: build
	xargs coqc lib/Benchmarks/EnterpriseSelfProof.v < _CoqProject

serviceproviderself: build
	xargs coqc lib/Benchmarks/ServiceproviderSelfProof.v < _CoqProject

pipenv: 
	cd benchmarking && pipenv install

_CoqProject: _CoqProject.noplugins
	cp _CoqProject.noplugins _CoqProject
	echo >> _CoqProject
	echo "-I $(OPAM_SWITCH_PREFIX)/lib/mirrorsolve" >> _CoqProject
	echo "-I $(OPAM_SWITCH_PREFIX)/lib/coq-memprof" >> _CoqProject

container: Dockerfile
	docker build . -t hackedy/leapfrog

shell: container
	docker run -it hackedy/leapfrog

shell-gui: container
	docker run -u root -v /tmp/.X11-unix:/tmp/.X11-unix -e DISPLAY=$(DISPLAY) -h $(shell cat /etc/hostname) -v $(HOME)/.Xauthority:/home/opam/.Xauthority -it hackedy/leapfrog

$(AECINSTRUCTIONS): README.md
	pandoc -V geometry:margin=1in README.md -o $(AECINSTRUCTIONS)

aec-instructions: $(AECINSTRUCTIONS)
