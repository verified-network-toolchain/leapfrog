# Leapfrog

This is the artifact accompanying the paper "Leapfrog: Certified Equivalence for
Protocol Parsers", to appear at [PLDI 2022](https://pldi22.sigplan.org/).

## Hardware requirements

You should be able to build Leapfrog and run most of its evaluation on any
modern laptop. To run the larger benchmarks you will need a more powerful
computer, as Leapfrog ends up using a lot of memory. For reference, we conducted
our evaluation on a server with 500GB of RAM.

## Installation instructions

You can either install Leapfrog using a Docker image or build it from source. We
recommend using the Docker image.

### Option 1: Installation inside Docker

The easiest way to run Leapfrog is to run it inside the provided Docker
container. To do this, you will need Docker version 20.10.12 or newer, which
should be available through your system's package manager.

If you are running Docker on Linux, we recommend running in [root-less
mode](https://docs.docker.com/engine/security/rootless/). Alternatively, you may
add your user to the `docker` group in order to get access to the Docker daemon,
but please be aware of the following:

1. Adding yourself to the `docker` group exposes you to certain security
   risks---i.e., anyone in the `docker` group is essentially a password-less
   `root` user.
2. The container will mount the local directory. Since the user inside of the
   container is `root`, this may create `root`-owned files in your local
   directory as well.

There are a few ways to get the Docker image. This container is a few GB in
size, so this can take a while depending on the speed of your internet
connection. The third option has to build Coq and other dependencies, so it will
take a while depending on the speed of your computer.
1. Download it from Zenodo to a local file `leapfrog-docker-image.tar.xz` and then
   run `docker load -i leapfrog-docker-image.tar.xz`.
2. Download a public version from the Docker repos with `docker pull
   hackedy/leapfrog:latest`
3. Build a copy locally from the Zenodo source archive `leapfrog.zip`:
```
unzip leapfrog.zip
cd leapfrog
make container
```

The Leapfrog experiments can take a long time, so we suggest mounting a
persistent volume for the image to store logs and other output. If you don't do
this, the output of Leapfrog within the image will not be saved between
invocations of `docker run`, and you will almost certainly lose data. One of the
authors recently skipped this step in artifact evaluation and had to redo a
bunch of experiments :)

To make a persistent volume, create a new directory and make sure it is globally
accessible:
```
mkdir logs
chmod o+rwx logs
```
Then, run the image and mount the directory with the following Docker command:
```
docker run --platform 'linux/amd64' -v `realpath logs`:/home/opam/leapfrog/benchmarking/logs -it hackedy/leapfrog bash
```

Either way, once you have the Leapfrog docker image installed, you can start it
up and run a shell with
```
docker run --platform 'linux/amd64' -it hackedy/leapfrog
```
This will drop you into a Bash shell in a copy of the Leapfrog source with all
the Coq built. Inside the container, the MirrorSolve plugin is located in
`~/mirrorsolve`.

### Option 2: Manual installation

For this option, we will assume Ubuntu 21.10 as a base operating system.
Instructions for other systems may differ slightly.

Leapfrog relies on the following packages:

* GNU Make, version 4.3 or later
* GNU MP Bignum, version 6.2 or later
* GNU Time, version 1.9 or later
* CVC4, version 1.8 or later
* Z3, version 4.8.14 or later
* Dune, version 2.9.3 or later.
* OCaml, version 4.11.1 or later
* OPAM, version 2.0.8 or later.
* Coq, version 8.13.2
* Equations (Coq plugin), version 1.3~beta1+8.13
* [MirrorSolve](https://github.com/jsarracino/mirrorsolve) (Coq plugin), tag
  `pldi22-artifact`
* Python, version 3.9 or later
* Pipenv, version 11.9 or later

#### System-level software packages

To install Make, CVC4, Z3, OPAM, and GNU MP Bignum on Ubuntu, run the following:

```
sudo apt update
sudo apt install build-essential cvc4 z3 opam libgmp-dev python3 pipenv time
```

#### Packages installed through OPAM

First, initialize OPAM. If you are running inside a container, you may also
want to add the `--disable-sandboxing` flag.

```
opam init
eval $(opam env)
```

Next create a new switch---possibly substituting your version of the OCaml
compiler:

```
opam switch create leapfrog ocaml-base-compiler.4.11.1
eval $(opam env)
```

Then, add the Coq OPAM repository:

```
opam repo add coq-released https://coq.inria.fr/opam/released
```

Finally, update the OPAM state, and install the required versions of Coq and
Equations:

```
opam update
opam install coq=8.13.2 coq-equations=1.3~beta1+8.13 dune=2.9.3
```

#### Installing MirrorSolve

The MirrorSolve source code can be obtained using Git, as follows:

```
git clone https://github.com/jsarracino/mirrorsolve -b pldi22-artifact
```

To build and install the plugin, run the following inside the `mirrorsolve`
directory:

```
dune build
dune install
```

#### Building Leapfrog

Finally, you can build Leapfrog by running `make` inside the main source
directory. Warnings about missing the mirrorsolve module are normal here.

## Benchmarks

Leapfrog comes with several benchmarks, divided into "small" and "large" based
on the resources required to run them (see "Hardware Requirements" above). They
are all located under `lib/Benchmarks`. Each of these is divided into a file
containing the declaration of the P4 automata (e.g., `SmallFilter.v`) and a file
invoking the Leapfrog equivalence checking scripts (e.g., `SmallFilterProof.v`).

### Files for each benchmark

The mapping between the benchmarks in the paper (Table 2) and the development is
as follows.

| Paper name              | Automaton definition                                | Proof file                                             |
|-------------------------|-----------------------------------------------------|--------------------------------------------------------|
| State Rearrangement     | `Ethernet.v`                                        | `EthernetProof.v`                                      |
| Header initialization   | `SelfComparison.v`                                  | `SelfComparisonProof.v`                                |
| Speculative loop        | `MPLSVectorized.v`                                  | `MPLSVectorizedProof.v`                                |
| Relational verification | `SloppyStrict.v`                                    | `SloppyStrictProof.v` (`prebisim_sloppystrict_stores`) |
| External filtering      | `SloppyStrict.v`                                    | `SloppySTrictProof.v` (`prebisim_sloppystrict`)        |
| Variable-length parsing | `IPOptions.v` (`IPOptionsRef63`,`TimeStampSpec3`)   | `IPOptions{1,2,3}Proof.v`                              |
| Edge                    | `Edge.v`                                            | `EdgeSelfProof.v`                                      |
| Service Provider        | `ServiceProvider.v`                                 | `ServiceProviderTransProof.v`                          |
| Datacenter              | `DataCenter.v`                                      | `DataCenterSelfProof.v`                                |
| Enterprise              | `Enterprise.v`                                      | `EnterpriseSelfProof.v`                                |
| Translation Validation  | `Edge.v`                                            | `EdgeTransProof.v`                                     |

Of these, the first half ("State Rearrangement" through "External Filtering")
are classified as "small" benchmarks, while the rest are "large".

### Use of `admit`

Our language equivalence checking scripts come in two flavors. One version,
which is described in the paper, uses `admit` to discharge proof obligations
that have been cleared by our plugin. This means that we have to close the
proof using `Admitted`. Another version of the script uses two (unsound) axioms
to discharge these proof goals instead, which means that the proof can be
closed with Qed.

For the small benchmarks, we have used the latter version --- although the one
with `admit` also still works. The larger benchmarks do not complete on our
hardware with the axiom-based scripts, because Coq's proof checker runs out of
memory at QED-time. These benchmarks therefore use the `admit`-based scripts
described in the paper.

To verify that only smt queries are admitted in benchmarks, run Print
Assumptions <term> after one of the small benchmarks. You should see a few
axioms that are equivalent to Axiom K, and also two axioms for smt positive and
negative. Our admit script has the same structure as the axiom script but it
uses admit instead of applying the axioms. To see that the axioms are being used
safely, you can also inspect the script in `BisimChecker.v`.

### Running one benchmark (30 seconds)
From the root of the Leapfrog repo, run
```
make ethernet
```
This should run the `Ethernet.v` benchmark, which is a simple equivalence
check. It should take a few seconds to a minute at most (it took us 5 seconds on
a laptop and 10 seconds on a server).  There will be a lot of debugging output,
this is normal.

If this works, you are ready to move on to using the benchmarking script.

### Running the benchmark script (5 to 15 minutes)

Verify that the benchmarking tools work correctly by running on one benchmark. 

The benchmarking tools are in `benchmarking/`. To bootstrap the
environment, enter the Leapfrog directory and run
```
make pipenv
```
Next change directory to `benchmarking/`:
```
cd benchmarking
```

The benchmarking script is `runner.py` and it takes one required option, `--size`, as well as several optional options.
Run the benchmarking script on the ethernet benchmark by the following command: 
```
pipenv run ./runner.py --size one -f ethernet
```
This should take 30 seconds at most.
The runner outputs the logs of the benchmarks, including performance statistics,
into `benchmarking/logs`. If you are using Docker and have a persistent volume
set up, check that the logs are also showing up outside the Docker image.

### Optional: run the benchmark script on the small benchmarks (15 minutes)

If you have the time, verify that the small benchmarks finish by running the following command: 

```
pipenv run ./runner.py --size small
```
This should take about 15 minutes.

### Running the benchmarks interactively

If you've built everything locally, you should be able to open the benchmark
files in `lib/Benchmarks` in your favorite Coq editor, and step through the
proofs.

If you've built the Docker image, you may need to set up your editor inside of
the container first. The user `opam` is a password-less sudoer, so you should be
able to invoke `apt` and install what you need. For your convenience, the Docker
image also provides a pre-installed version of Coqide. If your host OS is Linux,
you should be able to run the following:

```
docker run --platform 'linux/amd64' -u root -v /tmp/.X11-unix:/tmp/.X11-unix -e DISPLAY=$DISPLAY -h $(shell cat /etc/hostname) -v ~/.Xauthority:/home/opam/.Xauthority -it hackedy/leapfrog
# inside the container shell
eval $(opam env)
make -B _CoqProject
coqide
```

Note that the `docker` command starts a root prompt inside the container, which
is necessary for it to have access to your local `.Xauthority` file.

On Mac OS X, coqide can run from inside the container using a combination of
XQuartz and `socat`, as described
[here](https://gist.github.com/stonehippo/2c2b0972b7d199c78fb94fa9b1be1f5d).

## Instructions: Evaluate the claims (variable, 2 hours to a week)
Our paper makes the following claims:
1. A tool exists for reasoning about P4A parsers. This is witnessed by our
   implementation in general.
2. Our implementation mechanizes a variety of language-equivalence results about
   P4A parsers. This is witnessed by compiling leapfrog (which compiles and
   checks our Coq proofs of language-equivalence metatheory).
3. We prove language equivalence for a variety of benchmarks (Table 2). On small
   benchmarks, the proof is interactive, while large benchmarks take longer and
   require a lot of memory.
4. We validate the optimized output of the parser-gen tool for a single
   benchmark, namely edge (Figure 7).

Claims 1 and 2 are verified by the implementation compiling. For a detailed
mapping of concepts from the paper to their equivalents in the implementation,
please see the "Code overview" section below. We now discuss how to verify
claims 3 and 4 in more detail.

### Language equivalence (Claim 3)
There are two sets of benchmarks, small and large (grouped by total state size
less than 10 states), that together compose the contents of Table 2. Because the
small benchmarks are reasonably fast while the large benchmarks are not, we
provide a runner script `benchmarking/runner.py` for running these groups of
benchmarks separately.

We also provide a data extraction script which measures the runtime and memory
usage of the benchmarks in `benchmarking/plotter.py`. Like `runner.py`, it needs
to be run using `pipenv`.

#### Small benchmarks (30 minutes)
If you haven't already run them, go back to the "Running the benchmark script"
section above and run them.

The output of the runner indicates where the logs are saved. Here is some
example output, showing how the runner uses the git hash and current time to
create a new directory.

```
pipenv run ./runner.py --size small
running small benchmarks
building leapfrog...
dune build -p leapfrog
done!
starting benchmarking with output directory: 
/Users/john/leapfrog/benchmarking/logs/609bf43/03-03-2022.17:01:50
...
more output 
...
```

To check the runtimes, run the plotting script with this output directory as an
argument. For example:
```
pipenv run ./plotter.py /Users/john/leapfrog/benchmarking/logs/609bf43/03-03-2022.17:01:50

sloppystrict,609bf43,2022-03-03 17:01:50,00:01:40.430000,2275424
mpls,609bf43,2022-03-03 17:01:50,00:02:06.650000,3526288
ethernet,609bf43,2022-03-03 17:01:50,00:00:04.710000,677920
selfcomparison,609bf43,2022-03-03 17:01:50,00:09:49.710000,4625728
ipfilter,609bf43,2022-03-03 17:01:50,00:00:25.930000,1154928
```

This produces a CSV on standard output. The columns are benchmark name, hash,
timestamp, runtime in hh:mm:ss, and maximum memory use in KB. So in this output,
mpls (the overview example) took 2 minutes and 6.65 seconds while using roughly
3.3 GB memory.

Verify that all of the small benchmarks succeeded and in particular, that the
plotting script produces rows for `sloppystrict`, `mpls`, `ethernet`,
`selfcomparison`, and `ipfilter`.

#### Large benchmarks (a **long** time, should be done asynchronously)
These benchmarks take a long time and more memory than any ordinary laptop has
available. For reference, the Edge applicability benchmark took 9 hours and
occupied 250 GB of memory on our server. So we recommend using `nohup` to run
them remotely if possible. They use the same runner script as above, but with
the `--size` option set to `large`:
```
pipenv run ./runner.py --size large
```

To run them with nohup in the background, you can use the following command:
```
nohup pipenv run ./runner.py --size large > leapfrog_output.out 2>&1 &
```

As for the small benchmarks, you can use the plotting script to view the runtime
and memory usage for all the benchmarks.  The output directory for the logs will
be at the beginning of the `leapfrog_output.out` file if run using the nohup
command.

Note: One claim that is *not* validated by the artifact is the variable-length parser.
The specific sentence in the paper is 

> Our parser handles up to three generic options, with data-dependent lengths that ranges from 0 bytes to 6 bytes.

The artifact benchmark is for two generic options (notice that the ipoptions benchmark is in fact ipoptions2). 

This is due to a modification to our proof search algorithm. Since the submission, 
in part due to reviewer feedback, 
we refactored and reimplemented part of our Ltac tactics to support axioms.
While we have spent some time optimizing the new search algorithm,
it is still not as performant as our previous algorithm, 
and so the ipoptions3 benchmark does not finish on our hardware.

We are in contact with our paper shepherd about this and we do not expect that the artifact supports the claim in the paper.

### Translation validation (Claim 4)
The translation validation experiment is found in `lib/Benchmarks/Edge.v` and
`lib/Benchmarks/EdgeTransProof.v`. Our version of the Edge parser is the Plain
automata in `Edge.v`, while the output of the parser-gen is the Optimized
automata in `Edge.v`. To build this automata, we implemented a python script for
converting TCAM tables into P4A parsers; this script is found in
`lib/Benchmarks/mk_bench.py`. The parser-gen TCAM output is in a string in
`mk_bench.py` (the definition of edge on line 532), and the script prints out a
P4A automata when run. Similar to before, the script requires a pipenv
environment, so you will need to run `pipenv install` first, and then run the
following command from `lib/Benchmarks`:

```
pipenv run ./mk_bench.py > EdgeOptimizedOriginal.v
```

There is now a P4A automata definition in EdgeOptimizedOriginal.v that should
compile: compare it with the Optimized automata in Edge.v.

Our conversion script is naive and the output needs a few more manual edits. In
particular, we made the following edits:

* Removed unused header branches. The output automata converts a TCAM mask
  expression (such as 0x0F) into a bit-by-bit comparison. Many of these
  comparisons are unnecessary, e.g. in State_0, the first 16 matched bits are
  never used, so we completely remove them from the select statement. 

* Condensed contiguous select slices: for example, in State_0, we condensed the
  16 slices of `buf_112[111 -- 111], buf_112[110 -- 110] ...` to a single slice
  `buf_112[111 -- 96]`.

* Remove early accepts. The parser-gen tool assumed that malformed packets that
  are too short should be accepted (and later rejected by other mechanisms).
  These manifest as spurious branches that slice an entire packet but do not
  match the contents, and then transition to accept. 
  
  In our implementation we assumed that such packets should be rejected. We
  removed these branches by hand (e.g. the second-to-last transition of State_0). 

* Repair miscompiled branches. The parser-gen tool is very clever and in
  State_4, the output TCAM transitions into the middle of a different parse
  state. Our script doesn't fully handle this behavior (it only handles
  transitions to the start of a parse state) and so reports an error in the
  comments. This comment contains info about the destination state, as well as
  the amount that actually should have been parsed.

  For example, the comment for the first transition is: 
  ```
  (* overflow, transition to inl State_1 extracting only 48 *)
  ```
  The transition should actually go to State_1 and only consume 48 bits. We
  manually repaired these transitions by jumping to the proper suffix of the
  destination state; in this case, by still extracting 64 bits but transitioning
  to State_1_suff_0 (as State_1 always parses 16 bits).

## Adding a new benchmark
If you would like to make a new benchmark, the fastest way is to copy and tweak
one of the existing files (for example `lib/Benchmarks/Ethernet.v`). To add a
state, add a constructor to the state inductive; to add a variable, add a
constructor to the header inductive and specify its size as a nat in the
definition of `sz`. The statement grammar includes assignment, sequencing, and
extraction; for example, the statement `extract(V1) ;; V2 <- V1[2 -- 1]`
extracts into a header variable V1 and assigns two bits from V1 to the variable
V2.

For a new proof of language equivalence, again, it is best to use an existing
proof as a template. However the proofs are push-button so it should be easy to
do, provided the automata are in fact equivalent.

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
3. The starting states for equivalence (Reference.SPref and Combined.Parse,
   which are members of the Reference.state and Combined.Parse inductives
   respectively);
4. The state decidable equality instances in the tactic (Reference.state_eqdec
   and Combined.state_eqdec). These should be generated automatically in your
   benchmark file with a `Scheme Equality for state.` vernacular command. You
   will need to change these functions to match your new state inductives.

## Code overview

The code of Leapfrog itself lives under `lib/`. What folows is an extensive but
perhaps not exhaustive overview of the development in relation to the concepts
from the paper.

### Syntax and semantics

Concepts from the parser language syntax and semantics described in Section 3
map to Coq definitions as follows:

| Concept                           | Coq definition              | Filename        |
|-----------------------------------|-----------------------------|-----------------|
| Expression syntax (Fig. 2)        | `expr`                      | `Syntax.v`      |
| Operation syntax (Fig. 2)         | `op`                        | `Syntax.v`      |
| Pattern syntax (Fig. 2)           | `pat`                       | `Syntax.v`      |
| Transition syntax (Fig. 2)        | `transition`                | `Syntax.v`      |
| State syntax (Fig. 2)             | `state`                     | `Syntax.v`      |
| P4 automata syntax (Fig. 2)       | `t`                         | `Syntax.v`      |
| Expression semantics (Def. 3.1)   | `eval_expr`                 | `Syntax.v`      |
| Operation size (Def. 3.2)         | `op_size`                   | `Syntax.v`      |
| Operation semantics (Def. 3.2)    | `eval_op`                   | `Syntax.v`      |
| Pattern semantics (Def. 3.3)      | `match_pat`                 | `Syntax.v`      |
| Transition semantics (Def. 3.3)   | `eval_trans` and `eval_sel` | `Syntax.v`      |
| Configurations (Def. 3.4)         | `configuration`             | `P4automaton.v` |
| Configuration dynamics (Def. 3.5) | `step`                      | `P4automaton.v` |
| Multi-step dynamics (Def. 3.6)    | `follow`                    | `P4automaton.v` |
| Language (Def. 3.6)               | `accepted`                  | `P4automaton.v` |

### Symbolic relations and weakest preconditions

These are the formalizations of the symbolic relations on configurations, and
the weakest precondition calculations on them.

Some concepts, for the sake of brevity:
* A "template-guarded formula" (TGF) is a formula of the form defined in
  Def. 4.7;
* A "template-guarded clause" (TGC) is understood to be a conjunction of TGFs
  (denoted `/\ R` in the paper);
* A "template-guarded entailment" (TPE) is an entailment between a TGC and a TGF
  (denoted `/\ R |= phi`)
* A "template-guarded co-entailment" (TPCE) is an entailment between a TGF and a
  TGC (denoted `phi |= /\ R`)

All of these are instantiations of the more general syntax for formulas in
Figure 3, and derive their semantics as in the general semantics of this syntax.

| Concept                                 | Coq definition       | Filename     |
|-----------------------------------------|----------------------|--------------|
| Bitvector expr. syntax (Figure 3)       | `bit_expr`           | `ConfRel.v`  |
| Bitvector expr. semantics (Def. 4.3)    | `interp_bit_expr`    | `ConfRel.v`  |
| Template syntax (Definition 4.7)        | `state_template`     | `ConfRel.v`  |
| Pure formula syntax (Def. 4.7, Fig. 3)  | `store_rel`          | `ConfRel.v`  |
| Pure formula semantics (Def. 4.3)       | `interp_store_rel`   | `ConfRel.v`  |
| TGF syntax (Def 4.7)                    | `conf_rel`           | `ConfRel.v`  |
| TGF semantics (Def 4.3)                 | `interp_conf_rel`    | `ConfRel.v`  |
| TGC syntax                              | `crel`               | `ConfRel.v`  |
| TGC semantics (Def 4.3)                 | `interp_crel`        | `ConfRel.v`  |
| TG(C)E syntax                           | `entailment`         | `ConfRel.v`  |
| TGE semantics (Def 4.3)                 | `interp_entailment`  | `ConfRel.v`  |
| TGCE semantics (Def 4.3)                | `interp_entailment'` | `ConfRel.v`  |
| WP^{<,>} definition (Sec. 4.3)          | `wp_lpred`           | `WP.v`       |
| WP^{<,>} soundness (Lem. 4.8)           | `wp_lpred_pair_safe` | `WPProofs.v` |
| WP definition (Lem. 4.9)                | `wp`                 | `WP.v`       |
| WP soundness (Lem. 4.9)                 | `wp_safe`            | `WPProofs.v` |

Note that our verified statements about the WP operator pertain to its
_soundness_, i.e., whether the returned condition truly is a precondition, not
its _completeness_, i.e., whether it gives the weakest precondition --- see also
Section 6.4 of the paper.

### Formula compilation pipeline

Our algorithm lowers the symbolic relations represented using `conf_rel`:
* First, a compilation to "simplified TGE/TGCE", also called SGTE/STCGE;
* Then, a compilation to a first-order logic over stores, called FOL(Conf);
* Next, an optimization pass removing concatenation of empty bitvectors,
  returning to FOL(Conf);
* Finally, a compilation to a first-order logic over bitvectors, called FOL(BV).

For an overview of the pipeline, we refer to Figure 5.

What follows are the pointers to the definitions of the three logics mentioned
above, the compilation steps between them, and their soundness theorems. Note
that the generic definition of first-order logic is located in the MirrorSolve
repo, not in the Leapfrog repo. Leapfrog instantiates it with particular
theories.

| Concept                          | Coq definition                           | Filename                               |
|----------------------------------|------------------------------------------|----------------------------------------|
| Simplified TG(C)E syntax         | `simplified_entailment`                  | `ConfRel.v`                            |
| Simplified TGE semantics         | `interp_simplified_entailment`           | `ConfRel.v`                            |
| Simplified TGCE semantics        | `interp_simplified_entailment'`          | `ConfRel.v`                            |
| Compilation of TG(C)E to STG(C)E | `simplify_entailment`                    | `ConfRel.v`                            |
| Correctness of TGE -> STGE       | `simplify_entailment_correct`            | `ConfRel.v`                            |
| Corr. of TGCE -> STGCE           | `simplify_entailment_correct'`           | `ConfRel.v`                            |
| FOL(-) syntax                    | `fm`                                     | `mirrorsolve/src/theories/FirstOrder.v`|
| FOL(-) semantics                 | `interp_fm`                              | `mirrorsolve/src/theories/FirstOrder.v`|
| FOL(Conf) instantiation          | `fm_model`                               | `FirstOrderConfRelSimplified.v`        |
| Comp. STGE to FOL(Conf)          | `compile_simplified_entailment`          | `CompileConfRelSimplified.v`           | 
| Corr. STGE -> FOL(Conf)          | `compile_simplified_entailment_correct`  | `CompileConfRelSimplified.v`           |
| Comp. STCGE to FOL(Conf)         | `compile_simplified_entailment'`         | `CompileConfRelSimplified.v`           | 
| Corr. STCGE -> FOL(Conf)         | `compile_simplified_entailment_correct'` | `CompileConfRelSimplified.v`           |
| Remove zero-concatenation        | `simplify_concat_zero_fm`                | `FirstOrderConfRelSimplified.v`        |
| Corr. zero-concatenation removal | `simplify_concat_zero_fm_corr`           | `FirstOrderConfRelSimplified.v`        |
| FOL(BV) instantiation            | `fm_model`                               | `FirstOrderBitVec.v`                   |
| Comp. FOL(Conf) -> FOL(BV)       | `compile_fm`                             | `CompileFirstOrderConfRelSimplified.v` |
| Corr. FOL(Conf) -> FOL(BV)       | `compile_simplified_fm_bv_correct`       | `CompileFirstOrderConfRelSimplified.v` |

### Equivalence checking

The optimized implementation of the algorithm (in LTac) and the elements of its
correctness break down as follows.

| Concept                                  | Coq definition                       | Filename                        |
|------------------------------------------|--------------------------------------|---------------------------------|
| Bisimulation (Sec. 4.1)                  | `bisimulation`                       | `Bisimulations/Semantic.v`      |
| Bisimilarity vs. lang. equiv. (Lem. 4.5) | `bisimilar_iff_lang_equiv`           | `Bisimulations/Semantic.v`      |
| Bisimilarity with leaps (Def. 5.4)       | `bisimilar_with_leaps`               | `Bisimulations/Leaps.v`         |
| Correctness of leaps (Lem. 5.6)          | `bisimilar_iff_bisimilar_with_leaps` | `Bisimulations/LeapsProofs.v`   |
| Executions of Algorithm 1                | `pre_bisimulation`                   | `Bisimulations/WPLeaps.v`       |
| Pre-bisimulations yield bisimulations    | `wp_leaps_implies_bisim_leaps`       | `Bisimulations/WPLeapsProofs.v` |
| Soundness of Algorithm 1                 | `lang_equiv_to_pre_bisim`            | `LangEquivToPreBisim.v`         |
| Calculation of I (Thm. 5.2)              | `init_bisim`                         | `BisimChecker.v`                |
| Main algorithm loop (Alg. 1, line 2-6)   | `run_bisim_*`                        | `BisimChecker.v`                |
| Final check (Alg. 1, line 7)             | `close_bisim_*`                      | `BisimChecker.v`                |
| Algorithm 1, optimized                   | `solve_lang_equiv_state_*`           | `BisimChecker.v`                |
