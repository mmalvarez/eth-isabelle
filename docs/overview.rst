.. _overview:

*********
Overview
*********

Elle is a compiler focused on generating code for the
`Ethereum Virutal Machine (EVM) <https://jellopaper.org/evm/>`_.
What sets is apart from other Ethereum compiler technologies is that
it is *foundationally verified*: that is, it is implemented inside of
`Isabelle <https://isabelle.in.tum.de/>`_, a *proof assistant* that enables programmers to state
and prove *mathematical theorems* about their code. In the case of
Elle, a theorem exists stating that the behavior of the code output by the
Elle compiler matches the behavior of its input (see :doc:`Correctness`).

Assuming we trust the model
of Elle's source language (an LLL/Yul/WASM-like structured programming
layer on top of EVM) and the semantics of EVM (drawn from the `Eth-Isabelle <https://github.com/pirapira/eth-isabelle>`_ project,
we can have complete confidence that Elle generates EVM programs that match the
programmer's intent: that is, that behave the same way that input programs are supposed
to behave.

In the rest of this documentation, we'll cover
`:ref:how to install Elle <installation>`,
`how to use Elle's FourL frontend <usage_>` as
an end user to compile smart contracts written in the LLL language into EVM
bytecode. Next, we'll dive into the details of Elle's source-level representation,
covering its `syntax <syntax_>` and its `formal semantics <semantics_>`. Next, we'll talk about
`the internals of the implementation <implementation_>` of the Elle compiler
(along with the FourL frontend) as well
as its `correctness proof <correctness_>`.

Elle is intended to be supplanted by `Gazelle <https://github.com/mmalvarez/gazelle>`_, a .
As such, Elle itself is unlikely to see significant changes at this point. Nonetheless, Elle as it exists is a useful
system: it can be used to compile real-world LLL smart contracts; namely Dan Ellison's
`Echo <https://media.consensys.net/deploying-your-first-lll-contract-part-2-910d9eff497e>`_ smart contract,
Ben Edgington's `LLL-ERC20 <https://github.com/benjaminion/LLL_erc20/blob/master/erc20.lll>`_
token contract,
and the LLL implementation of the `ENS registry <https://github.com/ensdomains/ens/blob/master/contracts/ENS.lll>`_.
For these examples, see the `tests <https://github.com/mmalvarez/eth-isabelle/tree/master/elle/tests>`_ directory.
