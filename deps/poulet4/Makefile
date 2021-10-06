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

build:
	dune build -p poulet4

install:
	dune install -p poulet4

clean:
	dune clean -p poulet4

benchmarks: smallfilter babyip

smallfilter:
	xargs coqc lib/P4automata/Benchmarks/SmallFilterProof.v < _CoqProject | grep "Tactic call"

babyip:
	xargs coqc lib/P4automata/Benchmarks/BabyIPProof.v < _CoqProject | grep "Tactic call"
