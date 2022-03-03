# Leapfrog
This is the artifact accompanying the paper "Leapfrog: Certified Equivalence for Protocol Parsers", to appear at [PLDI 2022](https://pldi22.sigplan.org/).

## Hardware requirements

To build Leapfrog and run the benchmarks in the "small" collection, 8GB of RAM is sufficient. The larger benchmarks may require up to 250GB of RAM. **--- TODO: John, could you check this please?**

## Installation instructions

### Option 1: Installation inside Docker

The easiest way to run Leapfrog is to run it inside the provided Docker container. To do this, you will need Docker version 20.10.12 or newer, which should be available through your system's package manager.

If you are running Docker on Linux, we recommend running in [root-less mode](https://docs.docker.com/engine/security/rootless/). Alternatively, you may add your user to the `docker` group in order to get access to the Docker daemon, but please be aware of the following:
1. Adding yourself to the `docker` group exposes you to certain security risks --- i.e., anyone in the `docker` group is essentially a password-less `root` user.
2. The container will mount the local directory. Since the user inside of the container is `root`, this may create `root`-owned files in your local directory as well.

Once you have Docker set up, type `make container`. When the container is built, you should be able to run `make shell` to start a shell inside the container, where you can run `make` to build Leapfrog.

### Option 2: Manual installation
Leapfrog relies on the following packages:

* CVC4, version 1.8 or later
* Z3, version 4.8.14 or later
* Dune, version 2.2 or later.
* OCaml, version 4.11.1 or later
* OPAM, version 2.0.8 or later.
* Coq, version 8.13.2
* Equations (Coq plugin), version 1.3~beta1+8.13
* [MirrorSolve](https://github.com/jsarracino/mirrorsolve) (Coq plugin), tag `pldi22-artifact` 

#### System-level software packages
To install CVC4, Z3, Dune and OPAM on Ubuntu, run the following:
```
sudo apt install cvc4 z3 dune opam ocaml
```
#### Packages installed through OPAM
To install Coq and Equations through OPAM, first create a new switch --- possibly substituting your version of the OCaml compiler:
```
opam switch create leapfrog ocaml-system.4.11.1
```
Next, add the Coq OPAM repository:
```
opam repo add coq-released https://coq.inria.fr/opam/released
```
Finally, update the OPAM state, and install the required versions of Coq and Equations:
```
opam update
opam install coq=8.13.2 coq-equations=1.3~beta1+8.13
```

#### Installing MirrorSolve
The MirrorSolve source code can be obtained using Git, as follows:
```
git clone https://github.com/jsarracino/mirrorsolve -b pldi22-artifact
```
To build and install the plugin, run the following inside the `mirrorsolve` directory:
```
opam install .
```

#### Building Leapfrog

Finally, you can build Leapfrog by running `make` inside the main source directory.

## Benchmarks

## Code overview

### Syntax and semantics

Concepts from the parser language syntax and semantics described in Section 3 map to Coq definitions as follows:

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

These are the formalizations of the symbolic relations on configurations, and the weakest precondition calculations on them. 

Some concepts, for the sake of brevity:
* A "template-guarded formula" (TGF) is a formula of the form defined in Def. 4.7;
* A "template-guarded clause" (TGC) is understood to be a conjunction of TGFs (denoted `/\ R` in the paper);
* A "template-guarded entailment" (TPE) is an entailment between a TGC and a TGF (denoted `/\ R |= phi`)
* A "template-guarded co-entailment" (TPCE) is an entailment between a TGF and a TGC (denoted `phi |= /\ R`)

All of these are instantiations of the more general syntax for formulas in Figure 3, and derive their semantics as in the general semantics of this syntax.

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
| TGE syntax                              | `entailment`         | `ConfRel.v`  |
| TGE semantics (Def 4.3)                 | `interp_entailment`  | `ConfRel.v`  |
| TGCE syntax                             | `entailment'`        | `ConfRel.v`  |
| TGCE semantics (Def 4.3)                | `interp_entailment'` | `ConfRel.v`  |
| WP^{<,>} definition (Sec. 4.3)          | `wp_lpred`           | `WP.v`       |
| WP^{<,>} soundness (Lem. 4.8)           | `wp_lpred_pair_safe` | `WPProofs.v` |
| WP definition (Lem. 4.9)                | `wp`                 | `WP.v`       |
| WP soundness (Lem. 4.9)                 | `wp_safe`            | `WPProofs.v` |

Note that our verified statements about the WP operator pertain to its _soundness_, i.e., whether the returned condition truly is a precondition, not its _completeness_, i.e., whether it gives the weakest precondition --- see also Section 6.4 of the paper.

### Formula compilation pipeline

Our algorithm lowers the symbolic relations represented using `conf_rel`:
* First, a compilation to "simplified TGE/TGCE", also called SGTE/STCGE;
* Then, a compilation to a first-order logic over stores, called FOL(Conf);
* Next, an optimization pass removing concatenation of empty bitvectors, returning to FOL(Conf);
* Finally, a compilation to a first-order logic over bitvectors, called FOL(BV).

For an overview of the pipeline, we refer to Figure 5. The generic first-order logic is provided by MirrorSolve, and can be found in `src/theories/FirstOrder.v`; an instantiation also automatically provides a semantics. 

What follows are the pointers to the definitions of the three logics mentioned above, the compilation steps between them, and their soundness theorems.

| Concept                          | Coq definition                           | Filename                               |
|----------------------------------|------------------------------------------|----------------------------------------|
| Simplified TGE                   | `simplified_entailment`                  | `ConfRel.v`                            |
| Compilation of TGE to STGE       | `simplify_entailment`                    | `ConfRel.v`                            |
| Correctness of TGE -> STGE       | `simplify_entailment_correct`            | `ConfRel.v`                            |
| Simplified TGCE                  | `simplified_entailment'`                 | `ConfRel.v`                            |
| Comp. of TGCE to STGCE           | `simplify_entailment'`                   | `ConfRel.v`                            |
| Corr. of TGCE -> STGCE           | `simplify_entailment_correct'`           | `ConfRel.v`                            |
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

The optimized implementation of the algorithm (in LTac) and the elements of its correctness break down as follows.

| Concept                                  | Coq definition                       | Filename                        |
|------------------------------------------|--------------------------------------|---------------------------------|
| Bisimulation (Sec. 4.1)                  | `bisimulation`                       | `Bisimulations/Semantic.v`      |
| Bisimilarity vs. lang. equiv. (Lem. 4.5) | `bisimilar_iff_lang_equiv`           | `Bisimulations/Semantic.v`      |
| Bisimilarity with leaps (Def. 5.4)       | `bisimilar_with_leaps`               | `Bisimulations/Leaps.v`         |
| Correctness of leaps (Lem. 5.6)          | `bisimilar_iff_bisimilar_with_leaps` | `Bisimulations/LeapsProofs.v`   |
| Executions of Algorithm 1                | `pre_bisimulation`                   | `Bisimulations/WPLeaps.v`       |
| Soundness of Algorithm 1                 | `wp_leaps_implies_bisim_leaps`       | `Bisimulations/WPLeapsProofs.v` |
| Calculation of I (Thm. 5.2)              | `init_bisim`                         | `BisimChecker.v`                |
| Main algorithm loop (Alg. 1, line 2-6)   | `run_bisim`                          | `BisimChecker.v`                |
| Final check (Alg. 1, line 7)             | `close_bisim`                        | `BisimChecker.v`                |
| Algorithm 1, optimized                   | `solve_lang_equiv_state_*`           | `BisimChecker.v`                |
