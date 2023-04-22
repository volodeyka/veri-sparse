# vefi-sparse

We have verified implementations of Sparse Matrix-Vector Multiplication (SpMV), Sparse Matrix-Sparse Vector Multiplication (SpMSpV), and Doubly Compressed Sparse Matrix-Sparse Vector Mutliplication (DSpMSpV) using Dafny and Coq.

## Requirements

To run the programs in this repository, you will need to have VS Code installed with the Dafny plug-in. Ensure that the plug-in is using Dafny 4.0.0 or higher.

To run Coq proofs you will need to install opam, and run the following

```
opam switch create verisparse ocaml-base-compiler.4.11.1
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.16.1 coq-equations coq-mathcomp-ssreflect coq-mathcomp-zify coq-fcsl-pcm coq-mathcomp-algebra
```

## Cloning the Repository

To clone this repository to your local machine, you can use the following command in your terminal:

`git clone https://github.com/volodeyka/vefi-sparse.git`

Enter the repo:

`cd vefi-sparse`

## Verifying Dafny Programs

Open the vefi-sparse/dafny folder in VS Code. The following files, once opened, should verify automatically.

SpMV: `spmv.dfy`

SpMSpV: `spmspv.dfy`

DSpMSpV: `dspmspv.dfy`

## Compiling and Running Coq Proof

Each Coq file is independent. To compile the Coq proof for each algorithm, run the following commands:

SpMV:
`coqc coq/spmv.v`

SpMSpV:
`coqc coq/spmspv.v`

DSpMSpV:
`coqc coq/dspmspv.v`
