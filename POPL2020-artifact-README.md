# Artifact README


Note that this development is a fork of the original
[eth-isabelle](https://github.com/pirapira/eth-isabelle) project.
Everything in the `elle` directory is the work of the author of this popl submission.

I have tested these build steps under a Lubuntu virtual machine. My primary
installation is Ubuntu installed on Windows 10 WSL.

## Dependencies

Machine with 16Gb of RAM for building the proofs
(you may be able to get away with less; 16Gb is the least I've successfully tested it with)

Ocaml (tested with v 4.05.0)

Ocamlbuild

Ocaml Zarith (including Zarith development libraries)

(i.e. `apt-get install ocaml ocamlbuild libzarith-ocaml libzarith-ocaml-dev`
on an Ubuntu-like system)

Isabelle2018
(download from https://isabelle.in.tum.de/)

## Installing

Run `git submodule init` and then `git submodule update lem-installation` to pull in the Lem submodule (located at lem-installation). We have tested with the Lem version having
the hash `0927743c1bd31d7bba20a54260ba4c4dd3ce49e9`

Build lem by navigating to `lem-installation` and running `make`

Add the generated `lem` executable to your PATH (it will be located at `lem-installation/bin/lem`)
i.e., something like `export PATH=$PWD/lem-installation/bin:$PATH`

run `export LEMLIB=$PWD/lem-installation/library` in order to make sure
that Lem loads the correct set of library files (otherwise it may attempt
to generate code that is incompatible with Isabelle2018)

Navigate back to the root of this repository ("eth-isabelle") and run `make lem-thy` to create the `.thy` files that Elle depends on

## Inspecting The Proofs

Run Isabelle-Jedit, with the `HOL` session (in order to be able to
step through the proofs contained in the `ElleCorrect` session,
it's better not to run the `ElleCorrect` session)

`isabelle jedit -d ./lem -l HOL`

For some proofs (particularly the more complex ones in `elle/ElleCorrect`)
you will need to increase the editor's limit on the number of allowed tracing
messages (or else the proofs will pause and appear to get stuck). To do this,
navigate through the Isabelle/JEdit menus as follows

`Plugins > Plugin Options > Isabelle > General > Editor Tracing Messages`

Increase this value to 30000.

The most interesting proofs are in `elle/ElleCorrect`. The final
correctness theorems for the compiler are `elle_alt_correct*`
in `elle/ElleCorrect/ElleAltSemantics.thy`

## Recreating FourL.ml

Run Isabelle-Jedit, with the `ElleCorrect` session:
`isabelle jedit -d ./lem -d ./elle -l ElleCorrect`

Then, open the file `elle/FourLExtract.thy`. If processed to the end,
this file should result in a new version of `elle/generated/FourL.ml` being
created.

## Building llllc (FourL Compiler)

Navigate to `generated`, then run `make` to build
the compiler from its ML source using OCaml
(or `make llllc_opt` to
build a version of the compiler using Ocamlopt)

## Running llllc (FourL Compiler)

There are a number of `.lll` files in the `elle/tests` directory that
`llllc` should be able to run on all files in this directory, except
for `ENS.lll` and `erc20.lll` (it should be able to run on the modified
versions, `ENSmod.lll` and `erc20mod.lll`)

If you want to inspect the output of the compiler, you can use
the parser that comes with `Eth-Isabelle` (i.e., is
due to Yoichi Hirai).
Just run (from the
repository root) `parser/hexparser.rb` on a file containing the
bytecode you want to parse (or pipe the output from `llllc` directly
into it). You'll need an installation of Ruby
(tested with 2.5.1p57)
to use this tool.
