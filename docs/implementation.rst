**************
Implementation
**************

This page describes some salient aspects of how the Elle compiler
is implemented. Details about the implementation of the correctess
proof are deferred until :doc:`correctness`.

.. Here is some more detail on the specific syntaxes/IRs used by Elle

In :doc:`syntax`, we described the syntax of the Elle language from the user's
perspective. However, internally, Elle uses a series of annotations to
describe Elle programs at various stages of compilation. These can be found
in ``elle/ElleSyntax.thy``. This more elaborated representation takes the form
of `general datatype <https://github.com/mmalvarez/eth-isabelle/blob/ITP2019/elle/ElleSyntax.thy#L68>`_
with extension points (type parameters) into which we can insert annotations later,
along with the `specific syntax extensions <https://github.com/mmalvarez/eth-isabelle/blob/ITP2019/elle/ElleSyntax.thy#L130>`_
used at various stages of the compiler.

The Elle compiler proceeds in several phases, outlined in the remainder of this document. Note that links in this
file are to the (frozen) ``ITP2019`` branch of the repository, to ensure consistency of line numbers as master evolves.
Though the line numbers may change, the general ideas should not.

=====================================
Phase 1 - Generating Size Annotations
=====================================

As a first step, the Elle compiler generates a pair of integer
annotations for each node in the syntax tree given to the compiler
as input. These annotations correspond to the range of bytes
taken up
by the code that will be generated from the syntax tree in the program
buffer. These are calculated as one would expect: instructions are simply
the length of the encoding of the instruction as bytecode, labels
correspond to the lengths of EVM JUMPDEST instructions, and sequence
nodes have lengths equal to the sum of the lengths of all their children.

The implementation of this compiler phase can be found
`here <https://github.com/mmalvarez/eth-isabelle/blob/ITP2019/elle/ElleCompiler.thy#L22>`__, in ``elle/ElleCompiler.thy``.

After this phase (and throughout the Elle compiler thereafter), syntax
trees will be proven to conform to the following predicates
``ll_valid_q`` and ``ll_validl_q`` (on
elaborated Elle syntax trees and lists of elaborated
Elle syntax trees, respectively)
(the size-annotations are referred to as "quantitative annotations",
and abbreviated by "q" or "(x, x')", throughout). These predicates
can be found `here <https://github.com/mmalvarez/eth-isabelle/blob/ITP2019/elle/ElleCorrect/Qvalid.thy#L27>`__, in
``elle/ElleCorrect/Qvalid.thy``.

Note that, other than for the ``s`` annotations on JUMP and JUMPI,
none of the syntax tree node annotations have any impact on the size of the
generated code corresponding to a node (thus, no effect on the inference rules
for ``ll_validl_q``). This makes sense, as they correspond purely to compile-time
artifacts that are not present in the generated code.

=============================
Phase 2 - Finding Labels
=============================


In the second phase of compilation, we enforce the invariant that
*each Seq node has exactly 0 or 1 descended labels*, as defined
according to the ``ll3'_descend`` predicate, which can be found in
``elle/ElleCorrect/Valid3.thy``, `here <https://github.com/mmalvarez/eth-isabelle/blob/ITP2019/elle/ElleCorrect/Valid3.thy#L13>`__.

For this phase of the compiler, we traverse the Elle syntax tree.
At each ``Seq`` node, we scan the sub-tree for all descended ``Lab``
nodes with an index "pointing back up" at the ``Seq`` node we are
currently considering. If we find no such nodes, we mark the
``Seq`` node with an annotation indicating there is no label
(an empty list). Otherwise, we take the first ``Lab`` node we
find (in a preorder traversal),
annotate it as having been "consumed" by a ``Seq`` node,
and store the path to that label at the ``Seq`` node. In order to
guard against multiple labels "pointing up" at the same ``Seq``
scope, this compiler pass fails if it ever encounters a ``Lab`` node
that has not been consumed in its top-level traversal of the tree
(since such a node corresponds either to a nonexistent scope,
or to a scope which already has a label corresponding to it).

The compiler pass is implemented in the function ``ll3_assign_label`` in
``elle/ElleCorrect/ElleCompiler.thy``, `here <https://github.com/mmalvarez/eth-isabelle/blob/ITP2019/elle/ElleCompiler.thy#L137>`__

For reasoning about this phase and subsequent phases,
we use the aforementioned``ll_descend`` predicate, which relates
two Elle syntax trees and one list of natural numbers. This
predicate captures situations in which the syntax tree
``l2`` can be found as a descendant of ``l1`` by treating
``k`` as a path through the tree, selecting which child-node
to choose at each step.

.. _valid3:

After the second phase of compilation (if successful),
syntax trees will be proven to conform to the
inductive predicate ``ll_valid3'``, which can be found
`here <https://github.com/mmalvarez/eth-isabelle/blob/ITP2019/elle/ElleCorrect/Valid3.thy#L131>`__, also in
``elle/ElleCorrect/Valid3.thy``. This predicate essentially corresponds to the
intuition that each Sequence node has exactly
zero or one labels referencing it, and that the locations
of these labels are annotated on the sequence nodes.

==========================
Phase 3 - Resolving Jumps
==========================

Once we have located the unique corresponding label (or determined the nonexistence of such
a label) for each sequence node in the second phase, we need to calculate target addresses
for each jump node based on the locations of those labels.

This process involves, essentially, a fixed-point calculation over the Elle syntax tree,
in order to ensure that sufficient space has been allocated to store the needed address
at each ``Jump`` and ``JumpI`` node.
This process is captured by the function
``process_jumps_loop``, which can be found in ``elle/ElleCorrect/ElleCompiler.thy``,
`here <https://github.com/mmalvarez/eth-isabelle/blob/ITP2019/elle/ElleCompiler.thy#L323>`__.

``process_jumps_loop`` makes use of two auxiliary functions. The first is
``process_jumps``, which captures one iteration of the size checks involved in
the jump-resolution process. ``process_jumps`` returns one of three cases of
result: either ``Success`` if all jumps have sufficient size to store their corresponding
addresses, ``Fail`` if there is an un-recoverable error (such as invalid input)
and ``Bump`` if a node in the tree has a jump-target size that needs to be incremented.

At each ``Seq`` node, ``process_jumps`` checks the node's annotation to see if there
is a corresponding label. If there isn't one, ``process_jumps`` scans all descended
``Jump`` nodes to make sure there are no descended jumps that point to that ``Seq`` node
(as such jumps would have no target), failing if it finds any.
If there is a label according to the annotation,
``process_jumps`` looks up that label to find its address
(failing if there isn't one to be found), and then
runs on that sequence node's descendants (doing an in-order traversal)
to find all jumps that point to the scope corresponding
to this sequence node. If any are found, ``process_jumps`` checks the space allocated to that jump
node against the space required to encode the address from the label that was looked up previously
for the ``Seq`` node.

If there is enough space, ``process_jumps`` continues scanning the
tree for other jumps corresponding to the same ``Seq`` node and performing the same check,
ultimately returning ``Success`` if all of them have enough space. Otherwise, it returns
the absolute location (as a ``childpath``)
of the first ``Jump`` node without enough space in the form of a
``Bump`` result.

(For ``Seq`` nodes descended from the root, ``process_jumps`` first performs these checks for
jumps pointing up to the outer ``Seq`` node, then recursively performs the same checks on the
descended ``Seq`` node.)

The second auxiliary function used by ``process_jumps_loop`` is ``inc_jump``, which takes
a path (corresponding to a ``Jump`` node) returned by ``process_jumps`` and increments its size,
adjusting the size annotations of the rest of the tree in the process as appropriate.

To avoid a complicated termination argument for 
``process_jumps_loop`` (functions in Isabelle need to be proven to terminate
or they become very inconvenient to reason about),
the execution of
this function is "fuelled" (termination is justified by a decreasing natural-number argument,
which is decremented once each time the loop is run - thus, once per time a ``Jump`` node's
size needs to be incremented).
If this fuel parameter is ``0``, ``process_jumps_loop`` returns a failure (``None``)
Otherwise, runs ``process_jumps`` on the root
of the Elle syntax tree given as an argument. If ``process_jumps`` returns
``Success``, ``process_jumps_loop`` returns the input syntax tree as nothing
needs to be done. If ``process_jumps`` returns ``Failure``,
``process_jumps_loop``
also fails (returns ``None``). Otherwise, if ``process_jumps`` returns ``Bump``,
``process_jumps_loop`` calls ``inc_jump`` on the child-path returned by
``process_jumps``, and then calls ``process_jumps_loop`` on the same arguments
(with fuel parameter decremented).

The correctness of ``process_jumps_loop`` is established by a series of
validation passes that happen after it runs. However, ``process_jumps_loop``
is proven directly to produce ``valid_q`` results from ``valid_q`` inputs.
Additionally, we define a function, ``get_process_jumps_fuel``, which
calculates a sufficient amount of fuel to ensure that ``process_jumps_loop``
terminates on its input (although this is not formally established with a proof).

By the end of running ``process_jumps_loop``, we have a syntax tree that should obey
the predicate ``ll4_validate_jump_targets``. This predicate essentially makes sure that
the indices of jump nodes (which point to the sequence node corresponding to the jump; i.e.,
to the scope the jump's target is in) correspond to a scope whose label has an address
matching the address stored at the jump node (which is the address that will ultimately be
written out to bytecode).

The definition of ``ll4_validate_jump_targets`` can be found in
``elle/ElleCorrect/Valid4.thy``, `here <https://github.com/mmalvarez/eth-isabelle/blob/ITP2019/elle/ElleCorrect/Valid4.thy#L1289>`__.

.. we also show validate_jump_targets_spec'

=====================
The Big Picture
=====================

At this point, we have produced a syntax tree that is valid as an
``ll4`` syntax tree, yet meets all of the predicates described above.
In its final form, ``ll4`` contains all the information needed to generate
concrete EVM machine code, including concrete addresses. At this point,
``codegen'`` is used to emit a list of bytes corresponding to the
output bytecode. (``codegen`` can be found in ``elle/ElleCompiler.thy``,
`here <https://github.com/mmalvarez/eth-isabelle/blob/ITP2019/elle/ElleCompiler.thy#L419>`__)

An additional validation
step is used after this point to ensure that all jumps are encodable
in EVM (that is, their addresses are at least 1 byte and not more than 32
bytes). Code for these extra validators can be found
in ``elle/ElleCorrect/ElleAltSemantics.thy``, `here <https://github.com/mmalvarez/eth-isabelle/blob/master/elle/ElleCorrect/ElleAltSemantics.thy#L842>`__.
Examples of how all these pieces may be put together into a single verified
compilation pipeline can be found in ``elle/ElleCompilerVerified.thy`` (`here <https://github.com/mmalvarez/eth-isabelle/blob/ITP2019/elle/ElleCompilerVerified.thy>`__)

In the next section, :doc:`correctness`, we will sketch the process by which
the generated EVM instructions are proven correct with respect to the
input program, making use of the information contained in these intermediate
predicates.
