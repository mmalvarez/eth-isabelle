*************
Installation
*************

Elle's installation is quite straightforward if
all you want to do is use the FourL frontend as described in
:doc:`usage`, and somewhat more involved if you want to
be able to generate, build, check, or modify
the implementation and proofs of Elle.

Getting Elle
=============

In the rest of this file, let ``>`` stand for a bash-compatible shell
prompt (that is, lines starting with ``>`` are to be understood as input)

Clone Elle from the `Github repo <https://github.com/mmalvarez/eth-isabelle>`_
as follows:

::
   
   > git clone https://github.com/mmalvarez/eth-isabelle

Later in this file, we assume that Elle is checked out into
a directory called ``eth-isabelle``. (This repository has this name because
it is a fork of `Yoichi Hirai's eth-isabelle <https://github.com/pirapira/eth-isabelle>`
project specifying EVM in the Isabelle proof assistant.)

Since Elle is no longer under active development, the ``master`` branch should
be stable enough to build reliably. For a version of Elle that is more guaranteed
to build successfully, try the ``ITP2019`` branch, which contains an artifact
submission for the 2019 edition of the Interactive Theorem Proving conference:

::
   
   > cd eth-isabelle
   > git checkout ITP2019   

.. _end-user-installation:
   
Installation as an End-User of Elle
=========================================

The following dependencies are required to build ``llllc``, the
FourL command-line interface to the FourL compiler frontend that makes
use of Elle's verified compiler.

- Ocaml (tested with v4.05.0)
- OcamlBuild
- OCaml Zarith

On an Ubuntu-like system, these can be installed as follows:

::
   
   > apt-get install ocaml ocamlbuild libzarith-ocaml libzarith-ocaml-dev

Once these dependencies are installed, navigate to ``eth-isabelle/elle/generated``
and run ``make``. This should succeed and generate a file called ``llllc``.
When run on an lll file, it will print (to standard output) a hexadecimal
representation of the bytecode produced by the compiler for that smart contract
(similar to Solidity LLL's command-line tool, but with fewer options and error
messages). Files to run ``llllc`` on can be found in the ``eth-isabelle/elle/tests``
directory.

For example:

::
   
   > cd eth-isabelle/elle/generated
   # output snipped
   > make
   # output snipped
   > ./llllc ../tests/if.lll
   6001600a576003600d565b60025b

Usage of ``llllc`` is described further in :doc:`usage`

To help inspect the output of ``llllc``, you may find it useful to use the
EVM bytecode parser contained in eth-isabelle:
`eth-isabelle/parser/hexparser.rb <https://github.com/mmalvarez/eth-isabelle/blob/master/parser/hexparser.rb>`

You'll need an installation of Ruby (tested with 2.5.1p57) to use this tool. It takes hex bytecodes like those
output by ``llllc`` (or other compilers for Ethereum, such as Solidity LLL) on standard input and outputs
(on standard output)
a series of mnemonics describing the opcodes in the input.
   
Installation for Modifying and Examining Elle
==============================================

The Elle git repository includes the file
`eth-isabelle/elle/generated/FourL.ml <https://github.com/mmalvarez/eth-isabelle/blob/master/elle/generated/FourL.ml>`.
This file is generated from the formal Isabelle model contained in the rest of the Elle repository, and is all that
is needed to build a working executable version of Elle/FourL as described in end-user-installation_.

In order to work with the formal model directly, Isabelle itself is needed as a dependency. Elle requires
Isabelle 2018, which can be downloaded `here<https://isabelle.in.tum.de/website-Isabelle2018/index.html>`
(binaries for Linux, MacOS, and Windows are provided).

Once Isabelle is installed, the user will need to set up Lem, a framework used to generate the some of the
Isabelle specifications used by Elle. In order to do this, first run the following, to update the
Lem submodule contained in Elle's git repository:


::
   
   > cd eth-isabelle
   > git submodule init
   # output snipped
   > git submodule update lem-installation
   # output snipped

we have tested with the version of Lem having the Git hash of ``0927743c1bd31d7bba20a54260ba4c4dd3ce49e9``.
Newer versions should also work. Older versions may not support generating code compatible with Isabelle2018.

In order to build Lem, run the following:

::
   
   > cd lem-installation
   > make
   # output snipped

If this succeeds, it will generate an executable called ``lem``. Add it to your path, and ensure the
it will look for its libraries in the correct place, by running the following:

::
   
   > `export PATH=$PWD/lem-installation/bin:$PATH`
   > `export LEMLIB=$PWD/lem-installation/library`

Finally, navigate back to the root of the repository (``eth-isabelle``), and run the following to
build the ``.thy`` files that Elle depends on of from their Lem sources:

::
   
   > make lem-thy

Examining Elle Sources
----------------------

Isabelle allows ``.thy`` files representing formal models and
proofs to be grouped together into *sessions*. Sessions make it easier
to automate the process of compiling Isabelle developments, as well
as allowing for caching the results of compilation and proof-checking
so that work does not need to be repeated each time Isabelle is
re-opened. Elle contains a session called ``ElleCorrect``, which
packs together all the files containing Elle's correctness proofs into
a single session file.

However, in order to be able to
step through the proofs contained in the ``ElleCorrect`` session,
it's better not to run the ``ElleCorrect`` session, since. Therefore,
to examine Elle's proofs,
run Isabelle-Jedit, with the ``HOL`` session 

::
   
   isabelle jedit -d ./lem -l HOL

For some proofs (particularly the more complex ones in ``elle/ElleCorrect``)
you will need to increase the editor's limit on the number of allowed tracing
messages (or else the proofs will pause and appear to get stuck). To do this,
navigate through the Isabelle/JEdit menus as follows

::
   
   Plugins > Plugin Options > Isabelle > General > Editor Tracing Messages

Increase this value to 30000.

The most interesting proofs are in ``eth-isabelle/elle/ElleCorrect``. The final
correctness theorems for the compiler are ``elle_alt_correct*``
in ``eth-isabelle/elle/ElleCorrect/ElleAltSemantics.thy``

For more details on the structure of Elle, see :doc:`implementation`.


Recreating FourL.ml
--------------------

The command-line binary version of the Elle-based FourL compiler depends on
``FourL.ml``, an Ocaml file that is produced from a formal Isabelle model
via Isabelle's built-in extraction mechanism. As such, FourL.ml can be regenerated
from Elle's sources, provided Isabelle is installed. This can be done as follows:

::
   
   > isabelle jedit -d ./lem -d ./elle -l ElleCorrect
   
This will open the ``ElleCorrect`` session (building this session for the first time
can take some time - as much as a couple of hours on a 16Gb machine). Once this session
is done being processed, open the file ``eth-isabelle/elle/ElleCorrect/FourLExtract.thy``.
If that file is processed to the end (which can be forced by moving the cursor to the end of the file)
it will create a new version of ``eth-isabelle/elle/generated/FourL.ml``, which can then be built as
described in end-user-installation_.
   
