# vefi-sparse

We have verified implementations of Sparse Matrix-Vector Multiplication (SpMV), Sparse Matrix-Sparse Vector Multiplication (SpMSpV), and Doubly Compressed Sparse Matrix-Sparse Vector Mutliplication (DSpMSpV) using Dafny and Coq.

## Requirements

To run the programs in this repository, you will need to have the following installed:

- Coq version 8.12 or higher
- Dafny version 4.0.0 or higher

## Cloning the Repository

To clone this repository to your local machine, you can use the following command in your terminal:

`git clone https://github.com/volodeyka/vefi-sparse.git`

Enter the repo:

`cd vefi-sparse`

## Verifying Dafny Programs

For each of the algorithms, running the Dafny program with the command below will output `Dafny program verifier finished`, stating that the program verifies successfully.

SpMV:
`dafny dafny/spmv.dfy`

SpMSpV:
`dafny dafny/spmspv.dfy`

DSpMSpV:
`dafny dafny/dspmspv.dfy`

## Compiling and Running Coq Proof

To compile the Coq proof for each algorithm, run the following commands:

SpMV:
`coqc coq/spmv.v`

SpMSpV:
`coqc coq/spmspv.v`

DSpMSpV:
`coqc coq/dspmspv.v`

This will generate a new file for each proof - for SpMV, it will create `spmv.vo`, for SpMSpV, `spmspv.vo`, and for DSpMSpV, `dspmspv.vo`.

To run these programs, you will need to start the Coq interpreter by running the `coqtop` command in your terminal.
