## Abstract

This artifact contains the Coq formulation of IM and FIM calculi. This document 
explains how to run the Coq formulations and Coq files briefly. It could be built 
from the scratch.


# 1) Build from Scratch 

This section explains how to build the artifact from scratch

### Prerequisites

1. Install Coq 8.10.2.
   The recommended way to install Coq is via `OPAM`. Refer to
   [here](https://coq.inria.fr/opam/www/using.html) for detailed steps. Or one could
   download the pre-built packages for Windows and MacOS via
   [here](https://github.com/coq/coq/releases/tag/V8.10.2). Choose a suitable installer
   according to your platform.

2. Make sure `Coq` is installed (type `coqc` in the terminal, if you see "command
   not found" this means you have not properly installed Coq), then install `Metalib`:
   1. Open terminal
   2. `git clone https://github.com/plclub/metalib`
   3. `cd metalib/Metalib`
   4. Make sure the version is correct by `git checkout 597fd7d`
   5. `make install`


### Build and Compile the Proofs

1. Enter  `IM /coq` or `FIM /coq`  directory.

2. Please make sure to run the command `eval \$(opam env)` before running make if 
   you installed the Coq via opam. 

3. Type `make` in the terminal to build and compile the proofs.

4. For `IM /coq`, you should see something like the following:
```
coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module' -f _CoqProject -o CoqSrc.mk
COQC LibTactics.v
COQC syntax_ott.v
COQC rules_inf.v
COQC Infrastructure.v
COQC Wellformedness.v
COQC SubtypingInversion.v
COQC Disjointness.v
COQC Value.v
COQC KeyProperties.v
COQC Deterministic.v
COQC IsomorphicSubtyping.v
COQC TypeSafety.v
```
execution time about: 1m4.800s

For `FIM /coq`, you should see something like the following:
```
coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module' -f _CoqProject -o CoqSrc.mk
COQDEP VFILES
COQC LibTactics.v
COQC syntax_ott.v
COQC rules_inf.v
COQC Infrastructure.v
COQC Wellformedness.v
COQC Value.v
COQC SubtypingInversion.v
COQC Disjointness.v
COQC KeyProperties.v
COQC Deterministic.v
COQC IsomorphicSubtyping.v
COQC TypeSafety.v
```
execution time: 9m23.006s



## Proof Structure

- `IM` directory contains the definition and proofs of \IM 
- `FIM` directory contains the definition and proofs of \FIM
- `syntax_ott.v` contains the locally nameless definitions of the calculus.
- `rules_inf.v` contains the `lngen` generated code.
- `Infrastructure.v` contains the type systems of the calculi and some lemmas.
- `Deterministic.v` contains the proofs of the determinism property.
- `Typing.v` contains the proofs of some typing lemmas.
- `Type_Safety.v` contains the proofs of the type preservation and progress properties.
- `Subtyping_inversion.v` contains some properties of the subtyping relation and consistent subtyping.
  
<!-- ## Correspondence


We show some important figures, Lemmas and theorems correspondence with the coq formalization. The following table shows the correspondence between lemmas discussed in paper and their source coq codes. For example, one can find the `Theorem 3.1` in file `IM/coq/Type\_Safety.v` and the definition name in file is `progress`.

| Theorems/Definitions | Description           | Files              | Name in Coq                 |
|----------------------|-----------------------|-----------------|------------|
| Fig. 8   | Syntax                | IM/coq/syntax\_ott.v  |          |
| Fig. 9   | Typing               | IM/coq/syntax\_ott.v  | Typing   |
| Fig. 10   | Reduction             | IM/coq/syntax\_ott.v  | step     |
| Fig. 10   | Reduction            | IM/coq/syntax\_ott.v  | nstep    |
| Theorem 3.1   | Progress         | IM/coq/Type\_Safety.v | progress |
| Theorem 3.2   | Preservation     | IM/coq/Type\_Safety.v | Preservation  |
| Theorem 3.3   | Annotation       | IM/coq/Type\_Safety.v | erase_step    |
| Fig. 11     | Syntax             | FIM/coq/syntax\_ott.v |      |
| Fig. 12     | subtyping          | FIM/coq/syntax\_ott.v | algo\_sub |
| Lemma 4.1   | reflexivity        | FIM/coq/SubtypingInversion.v   | sub\_reflexivity |
| Lemma 4.2   | transtivity        | FIM/coq/SubtypingInversion.v   | sub\_transtivity |
| Fig. 12     | disjoint           | FIM/coq/syntax\_ott.v   | disjoint |
| Fig. 13     | Wellformed         | FIM/coq/syntax\_ott.v   | WFTyp |
| Fig. 14     | Typing             | FIM/coq/syntax\_ott.v   | Typing |
| Lemma 4.3   | Well-formedness    | FIM/coq/Deterministic.v    | Typing\_regular\_0 |
| Lemma 4.4   | uniqeness          | FIM/coq/Type\_Safety.v     | inference\_unique |
| Lemma 4.5   | subsumption        | FIM/coq/Type\_Safety.v     | Typing\_chk\_sub |
| Fig. 15     |  Isomorphic Subtyping | FIM/coq/syntax\_ott.v   | subsub |
| Lemma 4.7   | Isomorphic Subtyping  | FIM/coq/Isomorphic\_Subtyping.v| subsub2sub |
| Fig. 16     |  Casting              | FIM/coq/syntax\_ott.v   | Cast |
| Fig. 17     |  Reduction            | FIM/coq/syntax\_ott.v   | step |
| Theorem 4.8      | determinism      | FIM/coq/Deterministic.v |  step\_unique  |
| Theorem 4.9      | Progress         | FIM/coq/Type\_Safety.v  | progress  |
| Theorem 4.10     | Preservation     | FIM/coq/Type\_Safety.v  | Preservation\_subsub  |
| Corollary 4.11   |Preservation      | FIM/coq/Type\_Safety.v  |  Preservation\_subsub | -->