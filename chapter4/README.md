# Type-Directed Operational Semantics for Gradual Typing (artifact)

## Abstract

This artifact contains the Coq formulation of \B, \Bg, \Bgl and \E calculus associated with 
the paper "Type-Directed Operational Semantics for Gradual Typing". This document 
explains how to run the Coq formulations and Coq files briefly. 


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
   4.  Make sure the version is correct by `git checkout 597fd7d`
   5. `make install`


### Build and Compile the Proofs

1. Enter  `Bg/coq`, `Bgl/coq` or ``E/coq``  directory.

2. Please make sure to run the command `eval \$(opam env)` before running make if 
   you installed the Coq via opam. 

3. Type `make` in the terminal to build and compile the proofs.



## Correspondence

There are three folders and we show some important definitions and theorems correspondence with the coq formalization. The following three tables show the correspondence between lemmas discussed in paper and their source coq code. For example, one can find the `Lemma 3.5 (Preservation)` in file `Bg/coq/Type_Safety.v` and the lemma name in file is `Cast_preservation`.

| Theorems/Definitions | Description           | Files                             | Name in Coq                |
|----------------------|-----------------------|-----------------------------------|----------------------------|
| Fig. 1               | Syntax                | Bgl/coq/syntaxb\_ott.v            |                            |
| Fig. 2               | Syntax                | Bg/coq/syntax\_ott.v              |                            |
| Fig. 2               | Value                 | Bg/coq/syntax\_ott.v              | value                      |
| Fig. 2               | Ground                | Bg/coq/syntaxb\_ott.v             | Ground                     |
| Definition 3.1       | dynamic type          | Bg/coq/syntax\_ott.v              | dynamic\_type              |
| Fig. 3               | Typing                | Bg/coq/syntax\_ott.v              | Typing                     |
| Lemma 3.1            | Dynamic type          | Bg/coq/Typing.v                   | principle\_inf             |
| Lemma 3.2            | Inference             | Bg/coq/Typing.v                   | Typing\_Chk                |
| Lemma 3.3            | Typing unique         | Bg/coq/Typing.v                   | inference\_unique          |
| Fig.4                | Casting               | Bg/coq/syntax\_ott.v              | Cast                       |
| Lemma 3.4            | Casting value         | Bg/coq/Type\_Safety.v             | Cast\_value                |
| Lemma 3.5            | Preservation(casting) | Bg/coq/Type\_Safety.v             | Cast\_preservation         |
| Lemma 3.6            | Progress(casting)     | Bg/coq/Type\_Safety.v             | Cast\_progress             |
| Lemma 3.7            | Determinism(casting)  | Bg/coq/Deterministic.v            | Cast\_unique               |
| Lemma 3.8            | Consistency(casting)  | Bg/coq/Type\_Safety.v             | Cast\_sim                  |
| Fig.5                | Reduction             | Bg/coq/syntax\_ott.v              | step                       |
| Theorem 3.1          | Determinism           | Bg/coq/Deterministic.v            | step\_unique               |
| Theorem 3.2          | Preservation          | Bg/coq/Type\_Safety.v             | preservation               |
| Theorem 3.3          | Progress              | Bg/coq/Type\_Safety.v             | progress                   |
| Theorem 4.1          | Relation(labels)      | Bg/coq/Label.v                    | bgl\_to\_bg                |
| Theorem 4.1          | Relation(labels)      | Bg/coq/Label.v                    | bgl\_to\_bg\_typing        |
| Theorem 4.4          | Embedding             | Bgl/coq/embed.v                    | dynamic\_typing            |
| Theorem 4.5          | Equivalence           | Bgl/coq/embed.v                    | static\_Typing\_dyn        |
| Theorem 4.5          | Equivalence           | Bgl/coq/embed.v                    | static\_dtyping\_dyn       |
| Fig. 6               | Syntax                | Bgl/coq/syntax\_ott.v             |                            |
| Fig. 6               | value                 | Bgl/coq/syntax\_ott.v             | value                      |
| Fig. 6               | Ground type           | Bgl/coq/syntaxb\_ott.v            | Ground                     |
| Fig. 6               | Typing                | Bgl/coq/syntax\_ott.v             | Typing                     |
| Fig. 7               | Cast                  | Bgl/coq/syntax\_ott.v             | Cast                       |
| Fig. 8               | Reduction             | Bgl/coq/syntax\_ott.v             | sstep                      |
| Fig. 9               | Reduction             | Bgl/coq/syntax\_ott.v             | step                       |
| Fig. 11              | Elaboration           | Bgl/coq/syntax\_ott.v             | typing                     |
| Fig. 11              | Elaboration           | Bgl/coq/syntax\_ott.v             | btyping                    |
| Theorem 4.2          | Elaboration           | Bgl/coq/ttyping.v                 | elaboration\_soundness     |
| Theorem 4.2          | Elaboration           | Bgl/coq/ttyping.v                 | btyping\_typing            |
| Lemma 4.1            | Soundness(cast)       | Bgl/coq/soundness\_completeness.v | Casting\_soundness         |
| Lemma 4.2            | Soundness(cast)       | Bgl/coq/sound\_complete\_blame.v  | Cast\_soundness\_blame     |
| Lemma 4.3            | Completeness(cast)    | Bgl/coq/soundness\_completeness.v | Cast\_completeness         |
| Lemma 4.4            | Completeness(cast)    | Bgl/coq/sound\_complete\_blame.v  | Cast\_completeness\_blame  |
| Theorem 4.3          | Sound,complete        | Bgl/coq/soundness\_completeness.v | soundness                  |
| Theorem 4.3          | Sound,complete        | Bgl/coq/soundness\_completeness.v | soundness\_blame           |
| Theorem 4.3          | Sound,complete        | Bgl/coq/sound\_complete\_blame.v  | divergesl                  |
| Theorem 4.3          | Sound,complete        | Bgl/coq/soundness\_completeness.v | completeness               |
| Theorem 4.3          | Sound,complete        | Bgl/coq/sound\_complete\_blame.v  | completeness\_blame        |
| Theorem 4.3          | Sound,complete        | Bgl/coq/sound\_complete\_blame.v  | divergesr                  |
| Fig.12               | Type precision        | Bgl/coq/syntax\_ott.v             | tpre                       |
| Fig.12               | Expression precision  | Bgl/coq/syntax\_ott.v             | epre                       |
| Theorem 4.6          | SGG                   | Bgl/coq/criteria.v                | SGG\_both                  |
| Lemma 4.5            | DGG(casting)          | Bgl/coq/criteria.v                | Cast\_dgg                  |
| Theorem 4.7          | DGG1                  | Bgl/coq/criteria.v                | dynamic\_guarantee\_dir    |
| Theorem 4.8          | DGG2                  | Bgl/coq/criteria.v                | dynamic\_guarantee\_less   |
| Theorem 4.8          | DGG2                  | Bgl/coq/criteria.v                | dynamic\_guarantee\_blame |
| Theorem 4.9          | DGG                   | Bgl/coq/criteria.v                | dynamic\_guarantees        |
| Theorem 4.9          | DGG                   | Bgl/coq/criteria.v                | diverge\_case              |
| Theorem 4.9          | DGG                   | Bgl/coq/criteria.v                | dynamic\_guarantees\_less  |
| Theorem 4.9          | DGG                   | Bgl/coq/criteria.v                | dynamic\_guarantees\_blame |
| Fig.13               | Subtyping             | Bgl/coq/syntax\_ott.v             | sub                        |
| Fig.13               | Positive              | Bgl/coq/syntax\_ott.v             | suba                       |
| Fig.13               | Negative              | Bgl/coq/syntax\_ott.v             | subb                       |
| Fig.13               | Safe expression       | Bgl/coq/syntax\_ott.v             | Safe                       |
| Lemma 4.6            | Fractoring(subtype)   | Bgl/coq/safe\_theorem.v           | sub\_factoring\_right     |
| Lemma 4.6            | Fractoring(subtype)   | Bgl/coq/safe\_theorem.v           | sub\_factoring            |
| Lemma 4.7            | Fractoring(precision) | Bgl/coq/safe\_theorem.v           | tpre\_factoring           |
| Lemma 4.7            | Fractoring(precision) | Bgl/coq/safe\_theorem.v           | tpre\_factoring\_right    |
| Lemma 4.8            | Preservation(safe)    | Bgl/coq/safe\_theorem.v           | safe\_preservation         |
| Lemma 4.9            | Progress(safe)        | Bgl/coq/safe\_theorem.v           | safe\_progress             |
| Fig. 14              | Syntax                | E/coq/syntax\_ott.v               |                            |
| Fig. 15              | Typing                | E/coq/syntax\_ott.v               | Typing                     |
| Fig. 15              | Type precision        | E/coq/syntax\_ott.v               | tpre                       |
| Definition 5.1       | Dynamic type          | E/coq/syntax\_ott.v               | dynamic\_type            |
| Lemma 5.1            | Dynamic type          | E/coq/Typing.v                    | principle\_inf              |
| Lemma 5.2            | Dynamic type          | E/coq/Typing.v                    | principle\_inf2            |
| Lemma 5.3            | Inference unique      | E/coq/Typing.v                    | inference\_unique          |
| Fig. 16              | Casting               | E/coq/ syntax\_ott.v              | Cast                       |
| Fig. 17              | Reduction             | E/coq/ syntax\_ott.v              | step                       |
| Fig. 17              | Meet                  | E/coq/ syntax\_ott.v              | meet                       |
| Lemma 5.4            | Preservation(casting) | E/coq/Type\_safety.v              | Cast\_preservation         |
| Lemma 5.5            | Progress(casting)     | E/coq/Type\_safety.v              | Cast\_progress             |
| Lemma 5.6            | Determinism(casting)  | E/coq/Deterministic.v             | Cast\_unique               |
| Theorem 5.1          | Determinism           | E/coq/Deterministic.v             | step\_unique               |
| Theorem 5.2          | Preservation          | E/coq/Type\_Safety.v              | preservation               |
| Theorem 5.3          | Progress              | E/coq/Type\_Safety.v              | Progress                   |
| Fig. 18              | Term precision        | E/coq/syntax\_ott.v               | epre                       |
| Theorem 5.4          | Embedding             | E/coq/embed.v                    | dynamic\_typing            |
| Theorem 5.5          | SGG                   | E/coq/criteria.v                  | SGG\_both                  |
| Lemma 5.7            | DGG(casting)          | E/coq/criteria.v                  | Cast\_dgg                  |
| Theorem 5.6          | DGG                   | E/coq/criteria.v                  | dynamic\_guaranteel\_dir   |
| Theorem 5.7          | DGG                   | E/coq/criteria.v                  | DGGL                       |
| Theorem 5.7          | DGG                   | E/coq/criteria.v                  | DGGR                       |
| Theorem 5.7          | DGG                   | E/coq/criteria.v                  | Diverge                    |


## Proof Structure

- `Bg/coq` directory contains the definition and proofs of \B and \Bg
- `Bgl/coq` directory contains the definition and proofs of \B with blame labels and \Bg with blame labels  
- `E/coq` directory contains the definition and proofs of \e
- `Bg/coq/syntax_ott.v` contains the locally nameless definitions of \Bg.
- `Bg/coq/syntaxb_ott.v` contains the locally nameless definitions of \B.
- `Bgl/coq/syntax_ott.v` contains the locally nameless definitions of \Bg with blame labels.
- `Bgl/coq/syntaxb_ott.v` contains the locally nameless definitions of \B with blame labels.
- `E/coq/syntax_ott.v` contains the locally nameless definitions of \Bg.
- `rules_inf.v` and `rulesb_inf.v` contains the `lngen` generated code.
- `Infrastructure.v` contains the type systems of the calculi and some lemmas.
- `Infrastructure_b.v` contains the type systems of the blame calculi and some lemmas.
- `Deterministic.v` contains the proofs of the determinism property.
- `Typing.v` contains the proofs of some typing lemmas.
- `Typing_b.v` contains the proofs of some blame calculus typing lemmas.
- `ttyping.v` contains the proofs of some elaboration typing lemmas.
- `criteria.v` contains the proofs of gradual guarantee theorem.
- `Type_Safety.v` contains the proofs of the type preservation and progress properties.
- `Bgl/coq/soundness_completeness.v` contains the proofs of the soundness and completeness theorems with respect to blame calculus with  blame   label.
- `Bgl/coq/sound_complete_blame.v` contains the proofs of the soundness and completeness theorems with respect to blame calculus with blame label.
- `Bgl/coq/safe_theorem.v` contains the proofs of blame theorems.
