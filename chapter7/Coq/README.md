# Merging Gradual Typing (artifact)

## Abstract

This artifact contains the Coq formulation of M, MD and GTFL calculus . This document 
explains how to run the Coq formulations and Coq files briefly. It could be built 
from the scratch.


# 1) Build from Scratch #

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

1. Enter  `M /coq` or `MD /coq`  directory.

2. Please make sure to run the command `eval \$(opam env)` before running make if 
   you installed the Coq via opam. 

3. Type `make` in the terminal to build and compile the proofs.

4. For `M /coq`, you should see something like the following:
```
coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module' -f _CoqProject -o CoqSrc.mk
COQDEP VFILES
COQC LibTactics.v
COQC syntax_ott.v
COQC rules_inf.v
COQC Infrastructure.v
COQC Typing.v
COQC Subtyping_inversion.v
COQC Key_Properties.v
COQC Deterministic.v
COQC Type_Safety.v
```
execution time about : 2m10.050s

For `MD /coq`, you should see something like the following:
```
coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module' -f _CoqProject -o CoqSrc.mk
COQDEP VFILES
COQC LibTactics.v
COQC syntax_ott.v
COQC rules_inf.v
COQC Infrastructure.v
COQC Typing.v
COQC Subtyping_inversion.v
COQC Key_Properties.v
COQC Deterministic.v
COQC Static.v
COQC Type_Safety.v
COQC agt.v
COQC criteria.v
```
execution time : 2m58.395s



## Proof Structure

- `M` directory contains the definition and proofs of \M 
- `MD` directory contains the definition and proofs of \MD and GTFL 
- `syntax_ott.v` contains the locally nameless definitions of the calculus.
- `rules_inf.v` contains the `lngen` generated code.
- `Infrastructure.v` contains the type systems of the calculi and some lemmas.
- `Deterministic.v` contains the proofs of the determinism property.
- `Typing.v` contains the proofs of some typing lemmas.
- `criteria.v` contains the proofs of gradual guarantee theorem.
- `Type_Safety.v` contains the proofs of the type preservation and progress properties.
- `agt.v` contains the proofs of the soundness theorem with respect to GTFL.
- `Static.v` contains the proofs of gradual typing superset.
- `Key_properties.v` constains some necessary lemmas about casting.
- `Subtyping_inversion.v` contains some properties of the subtyping relation and consistent subtyping.
  
## Correspondence


We show some important figures, Lemmas and theorems correspondence with the coq formalization. The following table shows the correspondence between lemmas discussed in paper and their source coq codes. For example, one can find the `Definition 3.1` in file `M/coq/syntax\_ott.v` and the definition name in file is `disjointSpec`.

| Theorems/Definitions | Description           | Files                         | Name in Coq                 |
|----------------------|-----------------------|-------------------------------|-----------------------------|
| Fig. 2               | Syntax                | M/coq/syntax\_ott.v           |                             |
| Fig. 3               | Typing                | M/coq/syntax\_ott.v           | Typing                      |
| Fig. 4               | Subtype               | M/coq/syntax\_ott.v           | sub                         |
| Fig. 4               | COST                  | M/coq/syntax\_ott.v           | co                          |
| Definition 3.1       | Disjointness          | M/coq/syntax\_ott.v           | disjointSpec                |
| Fig. 5         | Casting               | M/coq/syntax\_ott.v           | Cast                          |
| Fig. 5         | Reduction             | M/coq/syntax\_ott.v           | step                          |
| Lemma 3.3      | Determinism(casting)  | M/coq/Deterministic.v         | Cast\_unique                  |
| Lemma 3.4      | Preservation(casting) | M/coq/Type\_Safety.v          | Cast\_preservation            |
| Lemma 3.5      | Progress(casting)     | M/coq/Type\_Safety.v         | Cast\_progress                |
| Lemma 3.6      | Dynamic types         | M/coq/Typing.v                | principal\_inf                |
| Theorem 3.7   | Determinism           | M/coq/Deterministic.v         | step\_unique                  |
| Theorem 3.8   | Preservation          | M/coq/Type\_Safety.v          | preservation                  |
| Theorem 3.9   | Progress              | M/coq/Type\_Safety.v          | progress                      |
| Fig. 7         | Syntax                | MD/coq/syntax\_ott.v          |                               |
| Fig. 7         | Consistency           | MD/coq/syntax\_ott.v          | sim                           |
| Fig. 7         | Subtyping             | MD/coq/syntax\_ott.v          | sub                           |
| Fig. 7         | Consistent Subtyping  | MD/coq/syntax\_ott.v          | csub                          |
| Fig. 7         | Precision             | MD/coq/syntax\_ott.v          | tpre                          |
| Lemma 4.1      | Consistent Subtype    | MD/coq/Subtyping\_inversion.v | consub\_prop                  |
| Lemma 4.1      | Consistent Subtype    | MD/coq/Subtyping\_inversion.v | consub\_propr            |
| Definition 4.2 | Disjointness          | MD/coq/syntax\_ott.v          | DisjointSpec                 |
| Fig. 8         | Casting               | MD/coq/syntax\_ott.v           | Cast                         |
| Fig. 9         | Reduction             | MD/coq/syntax\_ott.v           | step                          |
| Theorem 4.3    | Determinism           | MD/coq/Deterministic.v        | step\_unique                  |
| Theorem 4.4    | Preservation          | MD/coq/Type\_Safety.v         | preservation                  |
| Theorem 4.5    | Progress              | MD/coq/Type\_Safety.v         | progress                      |
| Fig. 10        | Precision             | MD/coq/syntax\_ott.v          | precise                       |
| Theorem 5.1    | Equivalence(static)   | MD/coq/Static.v               | static\_dtyping\_dyn          |
| Theorem 5.1    | Equivalence(static)   | MD/coq/Static.v               | static\_Typing\_dyn           |
| Theorem 5.2    | Equivalence(dynamic)  | MD/coq/Static.v               | static\_ddstep\_dyn\_chk      |
| Theorem 5.2    | Equivalence(dynamic)  | MD/coq/Static.v               | static\_stepd\_dyn\_chk       |
| Theorem 5.3    | SGG                   | MD/coq/criteria.v             | SGG\_both                     |
| Theorem 5.4    | AGT          | MD/coq/agt.v               | AGT\_Soundness|
| Definition D.1 | Translation  | MD/coq/agt.v               | transt        |
| Definition D.2 | Translation  | MD/coq/agt.v               | transg        |
| Fig. 13        | GTFL         | MD/coq/agt.v               |               |
| Fig. 13               | Well-formedness       | M/coq/syntax\_ott.v           | well                        |
| Fig. 13               | Projection            | M/coq/syntax\_ott.v           | get\_ty                     |
| Fig. 13         | Wellformed             | MD/coq/syntax\_ott.v          | well                         |
| Fig. 13         | Projection             | MD/coq/syntax\_ott.v          | get\_ty                      |
| Fig. 13               | Label presence        | M/coq/syntax\_ott.v           | ityp                        |
| Fig. 14               | CBN             | MD/coq/syntax\_ott.v                | cbn                         |

