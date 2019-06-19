***************************
Usage of the LLL Frontend
***************************

.. contents::

In order to provide an convenient interface for programmers to work with
Elle's verified compilation system, Elle provides a frontend called *FourL*
that allows users to translate programs written in `LLL <https://lll-docs.readthedocs.io>`_
to EVM bytecode. Unlike other implementations of LLL, FourL uses Elle's verified
translation algorithm as a core layer, ensuring that address resolution and
label scoping are handled properly. (For more details about what exactly Elle handles,
see :doc:`implementation` and :doc:`correctness`).

.. _basic-usage:

============
Basic Usage
============
After building the ``llllc`` frontend as described in :ref:`end-user-installation`,


::
   
   > cd eth-isabelle/elle/generated
   > ./llllc ../tests/if.lll
   6001600a576003600d565b60025b

This hex-code is output in the same format as Solidity LLL, and can be used with
other existing tooling for deployment, testing, and static analysis.
(For instance, `ganache <https://nethereum.readthedocs.io/en/latest/ethereum-and-clients/ganache-cli/>`_
and `web3.js <https://web3js.readthedocs.io/en/1.0/>`_ have been used for testing
``eth-isabelle/elle/tests/echo.lll``)
   
========================
Supported LLL Constructs
========================

.. role:: raw-html(raw)
	  :format: html

FourL supports a large subset of LLL, but does not support the
entire language. The supported constructs are listed below. For more
information about the meaning these and other LLL commands, see the
`lll documentation <https://lll-docs.readthedocs.io/en/latest/>`_

.. csv-table:: FourL supported commands
	       :header: "Command", "Notes/Caveats"
			
			"``seq``",       "Unlike Solidity LLL, sequencing does not clean up the stack after push instructions"
			"``if``",        "Expands to Elle control-flow"
	     		"``when``",      "Expands to Elle control-flow"
			"``unless``",    "Expands to Elle control-flow"
			"``for``",      "Expands to Elle control-flow"
			"``returnlll``", "Supported only in a special case: when a single returnlll instruction occurs at the :raw-html:`<br />` end of the constructor to return the code for the contract body"
		        "``lit``",         "Implemented using push rather than codecopy. :raw-html:`<br />` As such, only supports up to 32-bit constants."
			"``+/add``",
			"``-``",
			"``*``",
			"``div``",
			"``exp``",
			"``/``",
			"``%``"
			"``sha3``"
			"``keccak256``"
			"``&``"
			"``|``"
			"``^``"
			"``~``"
			"``shr``"
			"``&&``"
			"``||``"
			"``!``"
			"``=``"
			"``!=``"
			"``>``"
			"``<``"
			"``<=``"
			"``>=``"
			"``mstore``"
			"``mload``"
			"``return``"
			"``stop``"
			"``calldataload``"
			"``calldatacopy``"
			"``calldatasize``"
			"``callvalue``"
			"``caller``"
			"``sstore``"
			"``sload``"
			"``log0-log4``"
			"``event0-event4``"
			"``revert``"


Support for new constructs can be added by modifying the
list of FourL macros (``default_lll_funs``) in
`eth-isabelle/elle/FourL.thy <https://github.com/mmalvarez/eth-isabelle/blob/master/elle/FourL.thy>`_.
This will require regenerating ``FourL.ml`` as described in :ref:`elle-isabelle-installation`.

============================
Debugging Failed Compilation
============================

Unfortunately, the current version of Elle lacks detailed error reporting.
Compilation either succeeds, in which case bytecode is output, or it fails,
in which case a failure cause is not reported. This is one aspect of Elle
that needs to be corrected in its next incarnation, a generalized compiler
called `Gazelle <https://github.com/mmalvarez/gazelle>`_.

One option is simply to try to try to identify minimal error cases by writing
smaller lll programs and trying to understand the cause of the failure.

Another, more advanced option for understanding failures in the Elle/FourL
compiler involves running the compiler inside of the Isabelle proof assistant
as described in :ref:`running-compiler-in-isabelle`. In this way, one can
run different phases of the compiler separately to identify where
exactly the error is happening.
This requires setting
up Isabelle and Lem as described in :ref:`elle-isabelle-installation`.
   
===================
Inspecting Bytecode
===================
   
To help inspect the output of ``llllc``, you may find it useful to use the
EVM bytecode parser contained in eth-isabelle:
`eth-isabelle/parser/hexparser.rb <https://github.com/mmalvarez/eth-isabelle/blob/master/parser/hexparser.rb>`_

You'll need an installation of Ruby (tested with 2.5.1p57) to use this tool. It takes hex bytecodes like those
output by ``llllc`` (or other compilers for Ethereum, such as Solidity LLL) on standard input and outputs
(on standard output)
a series of mnemonics describing the opcodes in the input.
 
