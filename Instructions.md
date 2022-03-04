# Prequisites
Leapfrog does not have special requirements for interactive use and for some of the evaluation claims on smaller benchmarks.
However, some of the larger benchmarks require a significant amount of memory (we conducted our evaluation with 500GB of RAM).

# Instructions: kick the tires (30 minutes)
## (Optional, Recommended) Loading the Docker image
We have provided a Docker image with the necessary prerequisites. 
To use this image, first load the image using:  
`docker -i leapfrog.tar`

In addition, the experiments can take a long time, so we recommend mounting a persistent volume for the image.
WARNING: If you don't do this, the output of leapfrog within the image will not be saved between docker sessions.
So we strongly recommend that you mount a persistent volume (one of the authors recently skipped this step in artifact evaluation and had to redo a bunch of experiments).

To make a persistent volume, make a new directory and make sure it is globally accessible: `mkdir logs && chmod o+rwx logs`.
Then, run the image and mount the directory by the following: 
```docker run -v `realpath logs`:/home/reviewer/logs -it leapfrog bash```
## Compiling (5-10 minutes)
Verify that Leapfrog compiles from scratch by running
`make clean`
and then
`make`
from the root directory. This should take several minutes (at most 5). Warning messages are normal, for example, here is our output:
```
john@Johns-MacBook-Pro leapfrog % gtime -v make
cp _CoqProject.noplugins _CoqProject
echo >> _CoqProject
echo "-I /Users/john/.opam/default/lib/mirrorsolve" >> _CoqProject
echo "-I /Users/john/.opam/default/lib/coq-memprof" >> _CoqProject
dune build -p leapfrog
      coqdep lib/BisimChecker.v.d
*** Warning: in file BisimChecker.v, declared ML module mirrorsolve has not been found!
        coqc lib/Benchmarks/.DataCenter.aux,lib/Benchmarks/DataCenter.{glob,vo}
File "./lib/Benchmarks/DataCenter.v", line 83, characters 0-4461:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/DataCenter.v", line 83, characters 0-4461:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/DataCenter.v", line 83, characters 0-4461:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/DataCenter.v", line 83, characters 0-4461:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/DataCenter.v", line 83, characters 0-4461:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/DataCenter.v", line 83, characters 0-4461:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/DataCenter.v", line 83, characters 0-4461:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/DataCenter.v", line 83, characters 0-4461:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/DataCenter.v", line 83, characters 0-4461:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/DataCenter.v", line 83, characters 0-4461:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/DataCenter.v", line 83, characters 0-4461:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/DataCenter.v", line 83, characters 0-4461:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/DataCenter.v", line 83, characters 0-4461:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/DataCenter.v", line 83, characters 0-4461:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/DataCenter.v", line 83, characters 0-4461:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/DataCenter.v", line 83, characters 0-4461:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/DataCenter.v", line 83, characters 0-4461:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/DataCenter.v", line 83, characters 0-4461:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
        coqc lib/Benchmarks/.Enterprise.aux,lib/Benchmarks/Enterprise.{glob,vo}
File "./lib/Benchmarks/Enterprise.v", line 82, characters 2-3745:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/Enterprise.v", line 82, characters 2-3745:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/Enterprise.v", line 82, characters 2-3745:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/Enterprise.v", line 82, characters 2-3745:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/Enterprise.v", line 82, characters 2-3745:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/Enterprise.v", line 82, characters 2-3745:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/Enterprise.v", line 82, characters 2-3745:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/Enterprise.v", line 82, characters 2-3745:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/Enterprise.v", line 82, characters 2-3745:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/Enterprise.v", line 82, characters 2-3745:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/Enterprise.v", line 82, characters 2-3745:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/Enterprise.v", line 82, characters 2-3745:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/Enterprise.v", line 82, characters 2-3745:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/Enterprise.v", line 82, characters 2-3745:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
        coqc lib/Benchmarks/.SloppyStrict.aux,lib/Benchmarks/SloppyStrict.{glob,vo}
File "./lib/Benchmarks/SloppyStrict.v", line 53, characters 2-553:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/SloppyStrict.v", line 112, characters 2-584:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
File "./lib/Benchmarks/SloppyStrict.v", line 112, characters 2-584:
Warning: To avoid stack overflow, large numbers in nat are interpreted as
applications of Nat.of_num_uint. [abstract-large-number,numbers]
```
## Running one benchmark (30 seconds)
Verify that a single benchmark runs by running `make ethernet`. 
This should take a few seconds to a minute at most (it took us 5 seconds on a laptop and 10 seconds on a server).
There will be a lot of debugging output, this is normal.
Here is our output for comparison:

```
john@Johns-MacBook-Pro leapfrog % gtime -v make ethernet
dune build -p leapfrog
xargs coqc lib/Benchmarks/EthernetProof.v < _CoqProject
Tactic call init prebisim ran for 0.533 secs (0.525u,0.007s) (success)
Tactic call init phase ran for 0.533 secs (0.526u,0.007s) (success)
Tactic call setting in rem_iff ran for 0. secs (0.u,0.s) (success)
Tactic call proving name <-> term ran for 0.001 secs (0.001u,0.s) (success)
Tactic call clearbody ran for 0.003 secs (0.003u,0.s) (success)
Tactic call remembering iff ran for 0.005 secs (0.005u,0.s) (success)
Tactic call Horig ran for 0.015 secs (0.015u,0.s) (success)
Tactic call compilation correct ran for 0.05 secs (0.049u,0.s) (success)
Tactic call antecedents ran for 0.033 secs (0.033u,0.s) (success)
Tactic call compile fm ran for 0.087 secs (0.087u,0.s) (success)
Debug:
put smt query in /var/folders/zy/nsq34jws3tl13j5rf6h61y6r0000gn/T/vcfbbf75.smt2
Tactic call smt check neg ran for 0.009 secs (0.004u,0.s) (success)
UNSAT
Tactic call asserting neg ran for 0.059 secs (0.059u,0.s) (success)
Tactic call clearing Horig ran for 0. secs (0.u,0.s) (success)
Tactic call apply extend ran for 0.006 secs (0.006u,0.s) (success)
Tactic call wp compute ran for 0.025 secs (0.024u,0.s) (success)
Tactic call set R' ran for 0.008 secs (0.008u,0.s) (success)
Tactic call simplify append ran for 0. secs (0.u,0.s) (success)
Tactic call extending ran for 0.046 secs (0.045u,0.s) (success)
Tactic call clearing all ran for 0. secs (0.u,0.s) (success)
Tactic call setting in rem_iff ran for 0. secs (0.u,0.s) (success)
Tactic call proving name <-> term ran for 0.002 secs (0.002u,0.s) (success)
Tactic call clearbody ran for 0.003 secs (0.003u,0.s) (success)
Tactic call remembering iff ran for 0.006 secs (0.006u,0.s) (success)
Tactic call Horig ran for 0.039 secs (0.039u,0.s) (success)
Tactic call compilation correct ran for 0.134 secs (0.133u,0.s) (success)
Tactic call antecedents ran for 0.095 secs (0.094u,0.s) (success)
Tactic call compile fm ran for 0.245 secs (0.244u,0.001s) (success)
Debug:
put smt query in /var/folders/zy/nsq34jws3tl13j5rf6h61y6r0000gn/T/vc2791d5.smt2
Tactic call smt check neg ran for 0.033 secs (0.027u,0.001s) (failure)
Debug:
put smt query in /var/folders/zy/nsq34jws3tl13j5rf6h61y6r0000gn/T/vcdcec18.smt2
Tactic call smt check pos ran for 0.022 secs (0.017u,0.s) (success)
SAT
Tactic call asserting pos ran for 0.236 secs (0.234u,0.001s) (success)
Tactic call clearing Horig ran for 0. secs (0.u,0.s) (success)
Tactic call apply skip ran for 0.007 secs (0.007u,0.s) (success)
Tactic call skipping ran for 0.008 secs (0.008u,0.s) (success)
Tactic call clearing all ran for 0. secs (0.u,0.s) (success)
Tactic call setting in rem_iff ran for 0. secs (0.u,0.s) (success)
Tactic call proving name <-> term ran for 0.001 secs (0.001u,0.s) (success)
Tactic call clearbody ran for 0.011 secs (0.01u,0.s) (success)
Tactic call remembering iff ran for 0.013 secs (0.012u,0.s) (success)
Tactic call Horig ran for 0.016 secs (0.016u,0.s) (success)
Tactic call compilation correct ran for 0.047 secs (0.047u,0.s) (success)
Tactic call antecedents ran for 0.036 secs (0.036u,0.s) (success)
Tactic call compile fm ran for 0.088 secs (0.087u,0.s) (success)
Debug:
put smt query in /var/folders/zy/nsq34jws3tl13j5rf6h61y6r0000gn/T/vc9230d8.smt2
Tactic call smt check neg ran for 0.012 secs (0.007u,0.001s) (success)
UNSAT
Tactic call asserting neg ran for 0.043 secs (0.043u,0.s) (success)
Tactic call clearing Horig ran for 0. secs (0.u,0.s) (success)
Tactic call apply extend ran for 0.006 secs (0.006u,0.s) (success)
Tactic call wp compute ran for 0.023 secs (0.023u,0.s) (success)
Tactic call set R' ran for 0.015 secs (0.015u,0.s) (success)
Tactic call simplify append ran for 0. secs (0.u,0.s) (success)
Tactic call extending ran for 0.052 secs (0.052u,0.s) (success)
Tactic call clearing all ran for 0. secs (0.u,0.s) (success)
Tactic call setting in rem_iff ran for 0. secs (0.u,0.s) (success)
Tactic call proving name <-> term ran for 0.002 secs (0.002u,0.s) (success)
Tactic call clearbody ran for 0.003 secs (0.003u,0.s) (success)
Tactic call remembering iff ran for 0.006 secs (0.006u,0.s) (success)
Tactic call Horig ran for 0.021 secs (0.021u,0.s) (success)
Tactic call compilation correct ran for 0.07 secs (0.07u,0.s) (success)
Tactic call antecedents ran for 0.058 secs (0.057u,0.s) (success)
Tactic call compile fm ran for 0.145 secs (0.143u,0.001s) (success)
Debug:
put smt query in /var/folders/zy/nsq34jws3tl13j5rf6h61y6r0000gn/T/vc5d7017.smt2
Tactic call smt check neg ran for 0.026 secs (0.021u,0.s) (failure)
Debug:
put smt query in /var/folders/zy/nsq34jws3tl13j5rf6h61y6r0000gn/T/vc52b6ea.smt2
Tactic call smt check pos ran for 0.025 secs (0.021u,0.001s) (success)
SAT
Tactic call asserting pos ran for 0.225 secs (0.223u,0.001s) (success)
Tactic call clearing Horig ran for 0. secs (0.u,0.s) (success)
Tactic call apply skip ran for 0.007 secs (0.007u,0.s) (success)
Tactic call skipping ran for 0.008 secs (0.008u,0.s) (success)
Tactic call clearing all ran for 0. secs (0.u,0.s) (success)
Tactic call build phase ran for 1.507 secs (1.467u,0.016s) (success)
Debug:
put smt query in /var/folders/zy/nsq34jws3tl13j5rf6h61y6r0000gn/T/vc675e90.smt2
Tactic call smt check pos ran for 0.008 secs (0.004u,0.s) (success)
Tactic call close phase ran for 0.155 secs (0.15u,0.001s) (success)
Finished transaction in 1.024 secs (1.019u,0.005s) (successful)
	Command being timed: "make ethernet"
	User time (seconds): 4.81
	System time (seconds): 0.17
	Percent of CPU this job got: 99%
	Elapsed (wall clock) time (h:mm:ss or m:ss): 0:05.00
```

## Running the benchmarking tools (15 minutes)
Verify that the benchmarking tools work correctly by running a set of smaller benchmarks.
The benchmarking tools are in `benchmarking/`, so first 
* change directory to benchmarking: `pushd benchmarking`,
* make sure that the pipenv environment is initialized: `pipenv install`, 
* and then run the benchmarking script on small benchmarks: `pipenv run ./runner.py --size small`. 

This should take roughly 15 minutes.

# Instructions: Evaluate the claims (variable time, 2 hours - a week of server time)
Our paper makes the following claims:
1. A tool exists for reasoning about P4A parsers. This is witnessed by our implementation in general.
2. Our implementation mechanizes a variety of language-equivalence results about P4A parsers. 
  This is witnessed by compiling leapfrog (which compiles and checks our Coq proofs of language-equivalence metatheory).
3. We prove language equivalence for a variety of benchmarks (Table 2). On small benchmarks, the proof is interactive, while large benchmarks take longer and require a lot of memory.
4. We validate the optimized output of the parser-gen tool for a single benchmark, namely edge (Figure 7).

Claims 1 and 2 are verified by the implementation compiling. 
For a detailed mapping of paper results to the implementation, please see TODO.
We discuss how to verify claims 3 and 4 in more detail.

## Language equivalence (Claim 3)
There are two sets of benchmarks, small and large (grouped by total state size less than 10 states), that together compose the contents of Table 2. 
Because the small benchmarks are interactive while the large benchmarks are not, 
we provide a runner script `benchmarking/runner.py` for running these groups of benchmarks separately. 
To access the runner script, do the following:
* change directory to benchmarking: `pushd benchmarking`,
* make sure that the pipenv environment is initialized: `pipenv install`.
Now the runner script can be run with `pipenv run ./runner.py <args>`.

We also provide a data extraction script which measures the runtime and memory usage of the benchmarks in `benchmarking/plotter.py`.
This script requires the same pipenv environment as `runner.py` and should be called with the output directory specified by the output of `runner.py`. (If that's a bit confusing, don't worry, we will explain in detail how to use `runner.py` and `plotter.py`.)

### Small benchmarks (30 minutes)
These benchmarks comprise all of the Utility benchmarks except for Variable length parsing: State Rearrangement, Header initialization, Speculative Loop, Relational verification, and External filtering.
If you are using the provided image, run the benchmarking script with the persistent `logs/` directory as an option: 
`pipenv run ./runner.py --size small --log-dir /opt/reviewer/logs`.
If you run the runner script without a `--log-dir` option it will default to `benchmarking/logs`, e.g. by 
`pipenv run ./runner.py --size small`.

This command will indicate where the logging info is saved (it uses the git hash and current time to mangle the output directory): 
```
pipenv run ./runner.py --size small
running small benchmarks
building leapfrog...
dune build -p leapfrog
done!
starting benchmarking with output directory: /Users/john/leapfrog/benchmarking/logs/609bf43/03-03-2022.17:01:50
...
more output 
...
```

To check the runtimes, run the plotting script with this output directory as an argument, e.g.
```
pipenv run ./plotter.py /Users/john/leapfrog/benchmarking/logs/609bf43/03-03-2022.17:01:50

sloppystrict,609bf43,2022-03-03 17:01:50,00:01:40.430000,2275424
mpls,609bf43,2022-03-03 17:01:50,00:02:06.650000,3526288
ethernet,609bf43,2022-03-03 17:01:50,00:00:04.710000,677920
selfcomparison,609bf43,2022-03-03 17:01:50,00:09:49.710000,4625728
ipfilter,609bf43,2022-03-03 17:01:50,00:00:25.930000,1154928
```

The output format is benchmark name, hash, timestamp, runtime in hh:mm:ss, and memory use in KB.
So in this case, mpls (the overview example) took 2 minutes and 6.65 seconds while using roughly 3.3 GB memory. 

Verify that all of the small benchmarks succeeded and in particular, that the plotting script produces rows for sloppystrict, mpls, ethernet, selfcomparison, and ipfilter.

### Large benchmarks (a long time, should be done asynchronously)
The larger benchmarks are the Applicability benchmarks and the variable-length parsing benchmark (ipoptions3).
Warning: these benchmarks take a long time and a lot of memory. 
For reference, the Edge applicability benchmark took 9 hours and 250 GB on our server.
So we recommend using nohup to run them remotely if possible.
They use the same runner script as above, but with the `--size` option set to `large`: 
```
pipenv run ./runner.py --size large --log-dir /opt/reviewer/logs
```

To run them with nohup in the background, you can use the following command: 
```
nohup pipenv run ./runner.py --size large --log-dir /opt/reviewer/logs > leapfrog_output.out 2>&1 &
```

Similar to before, use the plotting script to view the runtime and memory usage. The output directory for the logs will be at the beginning
of the `leapfrog_output.out` file if run using the nohup command.

## Translation validation (Claim 4)
The translation validation experiment is found in `lib/Benchmarks/Edge.v` and `lib/Benchmarks/EdgeTransProof.v`. 
Our version of the Edge parser is the Plain automata in `Edge.v`, while the output of the parser-gen is the Optimized automata in `Edge.v`.
To build this automata, we implemented a python script for converting TCAM tables into P4A parsers; this script is found in `lib/Benchmarks/mk_bench.py`.
The parser-gen TCAM output is in a string in `mk_bench.py` (the definition of edge on line 532), 
and the script prints out a P4A automata when run. 
Similar to before, the script requires a pipenv environment, so you will need to run `pipenv install` first, 
and then run the following command from `lib/Benchmarks`: 
```
pipenv run ./mk_bench.py > EdgeOptimizedOriginal.v
```

There is now a P4A automata definition in EdgeOptimizedOriginal.v that should compile: 
compare it with the Optimized automata in Edge.v.

Our conversion script is naive and the output needs a few more manual edits.
In particular, we made the following edits:
* Removed unused header branches. The output automata converts a TCAM mask expression (such as 0x0F) into a bit-by-bit comparison. 
  Many of these comparisons are unnecessary, e.g. in State_0, the first 16 matched bits are never used, so we completely remove them from the select statement. 
* Condensed contiguous select slices: for example, in State_0, we condensed the 16 slices of `buf_112[111 -- 111], buf_112[110 -- 110] ...` to a single slice `buf_112[[111 -- 96]`.
* Remove early accepts. The parser-gen tool assumed that malformed packets that are too short should be accepted (and later rejected by other mechanisms). These manifest as spurious branches that slice an entire packet but do not match the contents, and then transition to accept. 
In our implementation we assumed that such packets should be rejected. We removed these branches by hand (e.g. the second-to-last transition of State_0).
* Repair miscompiled branches. The parser-gen tool is very clever and in State_4, the output TCAM transitions into the middle of a different
parse state. Our script doesn't fully handle this behavior (it only handles transitions to the start of a parse state) and so reports an error in the comments. This comment contains info about the destination state, as well as the amount that actually should have been parsed.
For example, the comment for the first transition is: 
```(* overflow, transition to inl State_1 extracting only 48 *)```;
the transition should actually go to State_1 and only consume 48 bits. 
We manually repaired these transitions by jumping to the proper suffix of the destination state;
in this case, by still extracting 64 bits but transitioning to State_1_suff_0 (as State_1 always parses 16 bits).

# Adding a new benchmark
If you would like to make a new benchmark, the fastest way is to copy and tweak one of the existing files (for example `lib/Benchmarks/Ethernet.v`).
To add a state, add a constructor to the state inductive; 
to add a variable, add a constructor to the header inductive and specify its size as a nat in the definition of `sz`. 
The statement grammar includes assignment, sequencing, and extraction; for example, the statement
`extract(V1) ;; V2 <- V1[2 -- 1]` extracts into a header variable V1 and assigns two bits from V1 to the variable V2. 

For a new proof of language equivalence, again, it is best to use an existing proof as a template. However the proofs are push-button so it should be easy to do. 

Here are the contents of an existing proof `lib/Benchmarks/EthernetProof.v`: 
```
Require Import Leapfrog.Benchmarks.ProofHeader.
Require Import Leapfrog.Benchmarks.Ethernet.

Declare ML Module "mirrorsolve".
SetSMTSolver "cvc4".

Lemma ethernet_equiv:
  lang_equiv_state
    (P4A.interp Reference.aut)
    (P4A.interp Combined.aut)
    Reference.SPref
    Combined.Parse.
Proof.
  solve_lang_equiv_state_axiom Reference.state_eqdec Combined.state_eqdec false.
Time Qed.
```

If you were to tweak this, the parts to edit would be: 
1. The import path on line 2 to match your new benchmark;
2. The automata names (Reference.aut and Combined.aut) in the lemma definition;
3. The starting states for equivalence (Reference.SPref and Combined.Parse, which are members of the Reference.state and Combined.Parse inductives respectively);
4. The state decidable equality instances in the tactic (Reference.state_eqdec and Combined.state_eqdec). These should be generated automatically in your benchmark file with a `Scheme Equality for state.` vernacular command. You will need to change these functions to match your new state inductives.