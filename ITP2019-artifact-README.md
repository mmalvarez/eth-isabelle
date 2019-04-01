# Artifact README

## Dependencies

Ocaml (tested with v 4.05.0)

Isabelle2018

## Installing

Run `git submodule init` to pull in the Lem submodule (located at lem-installation). We have tested with the Lem version having
the hash `0927743c1bd31d7bba20a54260ba4c4dd3ce49e9`

Build lem by navigating to `lem-installation` and running `make`

Add the generated `lem` executable to your PATH (it will be located at `lem-installation/bin/lem`)

run `export LEMLIB=$pwd/lem-installation/library` in order to make sure
that Lem loads the correct set of library files (otherwise it may attempt
to generate code that is incompatible with Isabelle2018)

Navigate back to the root of this repository ("eth-isabelle") and run `make lem-thy` to create the `.thy` files that Elle depends on

## Inspecting The Proofs

Run Isabelle-Jedit, with the `HOL` session (in order to be able to
step through the proofs contained in the `ElleCorrect` session,
it's better not to run that session)

`isabelle jedit -d ./lem -l HOL`

The most interesting proofs are in `elle/ElleCorrect`. The final
correctness theorems for the compiler are `elle_alt_correct*`
in `elle/ElleCorrect/ElleAltSemantics.thy`

## Recreating FourL.ml

Run Isabelle-Jedit, with the `ElleCorrect` session:
`isabelle jedit -d ../lem -d . -l ElleCorrect`

Then, open the file `elle/FourLExtract.thy`. If processed to the end,
this file should result in a new version of `elle/generated/FourL.ml` being
created.

## Building llllc (FourL Compiler)

navigate to `generated`, then run `make` to build
the compiler from its ML source using OCaml
(or `make llllc_opt` to
build a version of the compiler using Ocamlopt)

## Running llllc (FourL Compiler)

there are a number of `.lll` files in the `elle/tests` directory that
`llllc` should be able to run on all files in this directory, except
for `ENS.lll` and `erc20.lll` (it should be able to run on the modified
versions, `ENSmod.lll` and `erc20mod.lll`)
