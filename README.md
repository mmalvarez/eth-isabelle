# If you are an artifact evaluator for ITP 2019

Please read [the artifact README](./ITP2019-artifact-README.md) first.

# Formalization of Ethereum Virtual Machine in Lem

This repository contains

* (EI) an EVM implementation in Lem `lem/evm.lem`
* (EI) a Keccak-256 implementation in Lem `lem/keccak.lem`
* (EI) a form of functional correctness defined in Lem `lem/evmNonExec.lem`
* (EI) a relational semantics that captures the environment's nondeterministic behavior `RelationalSem.thy`
* (EI) some example verified contracts in `example`
* (EI) a parser that parses hex code and emits an Isabelle/HOL expression representing the program `parser/hexparser.rb`
* Elle, a work-in-progress verified compiler from a structured language to EVM in `elle`

Items marked (EI) are part of the original [eth-isabelle](https://github.com/pirapira/eth-isabelle) distribution.

When you see `\<Rightarrow>` in the source, try using the [Isabelle2017](https://isabelle.in.tum.de/index.html) interface.  There you see `⇒` instead.

## Elle

This fork of eth-isabelle contains Elle, a compiler targeting EVM implemented in Isabelle that aims to be foundationally verified somewhat along the lines of [CompCert](http://compcert.inria.fr/)

## Building the LLLLC Standalone Executable

To build Elle's LLL compiler (llllc), only OCaml is needed (tested on version 4.02.3).

`cd elle/generated`

`make`

This should produce an executable, `llllc`.

To check the proofs of Elle and regenerate the file `elle/generated/FourL.ml`, which serves
as the source file used to build the OCaml standalone version of Elle, run

`make cleanGenerated`

and then check the file `elle/FourLExtract.thy` using the Isabelle IDE. If you don't
have Isabelle and Lem installed, you won't be able to regenerate `elle/generated/FourL.ml`, so be careful.

(adding support for a command-line build of `elle/generated/FourL.ml` is a TODO)

For more info on how to do this (which requires installing Lem and Isabelle),
see [the Eth-Isabelle README](./README_EthIsabelle.md).

## Testing the Elle Standalone Executable

Elle's llllc aims to be compatible in terms of inputs and outputs with the lll compiler
included in [Solidity](https://github.com/ethereum/solidity). To test out the compiler,
once you have built the `llllc` executable:

`cd elle/tests`

`../generated/llllc echo.lll`

(or any other lll file in the directory)

Currently the major limitations of Elle are the following (resolving both are TODOs):

- Only supports a single payload returned by `returnlll`; furthermore, it will ignore all
constructor code that takes place after the first `returnlll`.

- Does not yet support lll's `lit` construct for embedding literals in a program.

- Core compiler verification proofs are incomplete; this should be considered an unverified
version of Elle.

### Elle Syntax

`elle/ElleSyntax.thy`

### Elle Semantics

`elle/ElleSemantics.thy`

### Elle Compiler

`elle/ElleCompiler.thy`

### Compiler Correctness

### Roadmap

### Warning

Though it aims for ironclad correctness stemming from foundational guarantees, Elle's correctness proofs are
not yet complete, and it has not been thoroughly tested. Therefore it should not be considered production-quality
at this time.

That said, if you're interested in learning more about the compiler and being part of the testing or development process, please [contact Mario on Gitter](https://gitter.im/mmalvarez).

### Acknowledgement

The development of the Elle project is generously funded by ConsenSys.

### Legacy Version

A previous version of the compiler exists in `examples/LLLL.thy`. It contains a number of lemmas that have ended up
being unnecessary so far but may prove useful or educational.

Yoichi Hirai's original readme for Eth-Isabelle, describing the framework on which Elle is built,
can be found [here](./README_EthIsabelle.md)
