#  [Artifact] Pragmatic Gradual Polymorphism with References

## Abstract

This artifact contains the Coq formulation of static and gradual calculus associated with the paper "Pragmatic Gradual Polymorphism with References". 
If you want to learn more about Coq, please refer to [here](https://coq.inria.fr/documentation).
This document explains how to run the Coq formulations and Coq files briefly. Artifact can either be compiled in the pre-built docker image with all the dependencies installed or it could be built from the scratch.

## 1) Tested platforms #

The artifact has been tested using Coq 8.10.2.


## 2) Our CPU #

MacBook Pro2019: 1.4 GHz quad-core Intel Core i5

## 3) Storage Requirement #

3-6 GB


# 4) Docker Image #

This section explains how to pull the docker image of artifact from docker repo and use it. Run the following commands one by one in the terminal:

1. `$ docker pull wenjiaye/esop2023:v1` 
2. `$ docker run -it wenjiaye/esop2023:v1`
3. `$ eval $(opam env)`

An alternative approach is to load the docker image [here](https://connecthkuhk-my.sharepoint.com/:u:/g/personal/yewenjia_connect_hku_hk/EVVvyN20KoRJh1k-WCOVOuEBWE_6wX_NAyN7jNkHBUIMDg?e=IfafQs):

1. `$ docker load -i esop2023.tar` 
2. `$ docker run -it esop2023:v1`
3. `$ eval $(opam env)`



The artifact is located in /home/coq/artifact15/ directory.

There are two folders in the artifact, with make file in each:

1. **Static/coq** → contains static calculus formulation
2. **Gradual/coq** → contains gradual calculus formulation


Go to each folder and run make:

#### Static

1. `$ cd /home/coq/artifact15/Static/coq`
2. `$ make`
3. You should see something like the following:
```
coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module' -f _CoqProject -o CoqSrc.mk
make[1]: Entering directory '/home/coq/artifact15/Static/coq'
COQC LibTactics.v
COQC Definitions.v
COQC Infrastructure.v
COQC Lemmas.v
COQC Soundness.v
COQC Determinism.v
make[1]: Leaving directory '/home/coq/artifact15/Static/coq'
```
4. Execution time: 43.162s



#### Gradual

1. `$ cd /home/coq/artifact15/Gradual/coq`
2. `$ make`
3. You should see something like the following:
```
coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module' -f _CoqProject -o CoqSrc.mk
make[1]: Entering directory '/home/coq/artifact15/Gradual/coq'
COQC LibTactics.v
COQC Definitions.v
COQC Infrastructure.v
COQC Lemmas.v
COQC Soundness.v
COQC Determinism.v
COQC Static.v
COQC Criteria.v
make[1]: Leaving directory '/home/coq/artifact15/Gradual/coq'
```
4. Execution time: 2m53.827s



# 5) Build from Scratch #

This section explains how to build the artifact from scratch. 
Note that we also provide a dockerfile (refer to [here](https://github.com/YeWenjia/Pragmatic-Gradual-Polymorphism-with-References/tree/main/docker)). 

#### Prerequisites

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


#### Build and Compile the Proofs

1. Enter  `Static/coq` or `Gradual/coq`  directory.

2. Please make sure to run the command `eval $(opam env)` before running make if 
   you installed the Coq via opam. 

3. Type `make` in the terminal to build and compile the proofs.

4. For `Static/coq`, you should see something like the following:
```
coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module' -f _CoqProject -o CoqSrc.mk
COQC LibTactics.v
COQC Definitions.v
COQC Infrastructure.v
COQC Lemmas.v
COQC Soundness.v
COQC Determinism.v
```
execution time : 33.101s

For `Gradual/coq`, you should see something like the following:
```
coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module' -f _CoqProject -o CoqSrc.mk
COQDEP VFILES
COQC LibTactics.v
COQC Definitions.v
COQC Infrastructure.v
COQC Lemmas.v
COQC Soundness.v
COQC Determinism.v
COQC Static.v
COQC Criteria.v
```
execution time : 2m20.870s


## 6) Dockerfile #

We also provide a dockerfile (refer to [here](https://github.com/YeWenjia/Pragmatic-Gradual-Polymorphism-with-References/tree/main/docker)) and can be built by the following command:

`docker build -t esop23:v1 . `


## Proof Structure

- `Static` directory contains the definition and proofs of static system
- `Gradual` directory contains the definition and proofs of gradual system
- `Definitions` contains the locally nameless definitions of calculus.
- `Infrastructure.v` contains the type systems of the calculi and some lemmas.
- `Determinism.v` contains the proofs of the determinism property.
- `Typing.v` contains the proofs of some typing lemmas.
- `Lemmas.v` contains the proofs of some soundness auxiliary lemmas.
- `Static.v` contains the proofs of the relation between static and gradual system.
- `Soundness.v` contains the proof of type safety.
- `Criteria.v` contains the proofs of gradual guarantee theorem.

## Correspondence


We show some important Lemmas and theorems correspondence with the coq formalization. The following table shows the correspondence between lemmas discussed in paper and their source coq codes. For example, one can find the `Theorem 1 Determinism` in file `Static/coq/Deterministic.v` and the lemma name in file is `step_unique `.


| Theorems   | Description          | Files                       | Name in Coq             |
|------------|----------------------|-----------------------------|-------------------------|
| Theorem 1  | Determinism          | Static/coq/Determinism.v  | step\_unique            |
| Theorem 2  | Preservation         | Static/coq/Soundness.v      | preservation            |
| Theorem 3  | Progress             | Static/coq/Soundness.v      | progress                |
| Lemma 1    | Typing equivalence   | Static/coq/Lemmas.v         | typing\_atyping         |
| Lemma 1    | Typing equivalence   | Static/coq/Lemmas.v         | atyping\_typing         |
| Lemma 2    | Dynamic types        | Gradual/coq/Soundness.v     | ptype\_inf              |
| Lemma 3    | Synthesis            | Gradual/coq/Determinism.v   | typing\_chk2            |
| Theorem 4  | Determinism          | Gradual/coq/Determinism.v   | step\_unique            |
| Theorem 5  | Preservation         | Gradual/coq/Soundness.v     | preservation            |
| Theorem 6  | Progress             | Gradual/coq/Soundness.v     | progress                |
| Theorem 7  | Equivalence(static)  | Gradual/coq/Static.v        | typing\_styping         |
| Theorem 7  | Equivalence(static)  | Gradual/coq/Static.v        | styping\_typing         |
| Theorem 8  | SGG                  | Gradual/coq/Criteria.v      | SGG\_both               |
| Theorem 9  | Equivalence(dynamic) | Gradual/coq/Soundness.v     | static\_stepd\_dyn\_chk |
| Theorem 9  | Equivalence(dynamic) | Gradual/coq/Soundness.v     | static\_stepd\_dyn\_chk |
| Theorem 10 | DGG                  | Gradual/coq/Criteria.v      | dynamic\_guarantee\_dir |

