***********
Elle Syntax
***********

.. contents::

(Note: this documentation page is adapted from
`an entry in the Elle Github wiki <https://github.com/mmalvarez/eth-isabelle/wiki/Elle-Core-Syntax>`_)

=======================================
Goal: Compiling Structured Code to EVM
=======================================

The Elle source language, also known as *Elle-Core*, captures *structured programming* abstractions
and enables their translation to Ethereum EVM bytecode through a verified compiler (whose details are
described in :doc:`implementation`).

What exactly is meant by structured programming? It corresponds to some features of languages that we usually take for granted: the ability to perform sequencing, if-statements, and loops in a predictable way that enables us to reason about different sub-components of a program separately, and then combine the results together soundly.

More concretely, suppose we have the following rather contrived program **P1**, that pushes two values onto the stack (the following is pseudocode for EVM bytecode):

::

   ; program P1
   push 0x00
   JUMPDEST
   pop
   push 0x01


If run from the beginning, this code is innocuous: the JUMPDEST instruction will have no effect, the first PUSHed value will be POP'd back off, and we will end up with 0x01 at the top of the stack. However, if execution starts from the JUMPDEST, we have a problem: if the stack is empty beforehand, running just the latter 3 lines of P1 will cause a stack underflow and halt execution. This can happen, for instance, if P1 resides at (code-buffer address) 0xA0, and we have a possible path through the program that  goes through the following code-snippet, sub-program P2:

::

   ; program P2
   push 0xA1 ; address of JUMPDEST of p1
   jump

We might want to prove that P1 will never cause a stack underflow. However, if P2 begins running with an empty stack, it will call into P1 in an unintended way that will cause the machine to crash. The fundamental problem here is that **jumps in EVM are always based on absolute addresses**, meaning there is no way to protect your code from another part of the program that happens to know the address of an internal JUMPDEST to which jumping would violate your code's invariants.

Instead, we can enforce a *structured* programming discipline - eschewing explicit jumps (i.e.,
`"considering goto harmful" <https://homepages.cwi.nl/~storm/teaching/reader/Dijkstra68.pdf>`_)
and instead using conditionals and loops to describe branching control flow. By denying users of the source-language (*Elle-Core*) the ability to do arbitrary jumps, we are able to compose
sub-programs in predictable ways.

=============================================
De Bruijn Indices and Structured Programming
=============================================

Elle-Core provides a very general kind of structured programming, able to express the usual structured constructs such as *if* and *while*, but also more intricate control-flow structures, while maintaining the guarantee that “internal” labels within a sub-program cannot be improperly accessed through a notion of scope.

Elle's approach to representing scope is inspired by a practice from the programming-languages community called `*de Bruijn indices* <https://en.wikipedia.org/wiki/De_Bruijn_indices>`_ that provide a convenient way to
describe scoped variables (it is also similar to the approach taken by `WebAssembly <https://ewasm.readthedocs.io/en/mkdocs/>`_).
For an example of how this looks in a traditional context, consider a function that takes two parameters, discards the first, and returns the second. In the `lambda calculus <https://en.wikipedia.org/wiki/Lambda_calculus>`_, we write this as

::
   
   (\ x . (\ y . y))


However, we have chosen arbitrary variable names, which brings inconveniences. Nothing stops us from writing

::
   
   (\ y . (\ x . x))

which expresses the same function. Perhaps more concerning, we could have equally written

::
   
   (\ x . (\ x . x))


which also corresponds to the same function, because of the scoping convention of the lambda calculus: *if we bind a variable name twice, the innermost binding takes precedence*.

De Bruijn indices provide a clever trick to eliminate this ambiguity of naming and get a more canonical representation of functions that does not depend on specific variable names. The idea is that, because inner bindings take precedence, we can always describe variables in relative terms: each variable is uniquely distinguished by *how many levels up in the syntax tree that variable was bound*. So our example above becomes

::
   
   (\ . (\ . #0))


``#0`` returns the second (innermost) parameter (we are zero-indexing). Had we wanted to return the first parameter instead, we would have written

::
   
   (\ . (\ . #1))

With Elle, we do something similar, applying this same notion of scoping discipline to our labels. Each sequencing node (sequencing together Elle subprograms) creates a new context in which a new jump-target (label) can be described. Specifically, sequence nodes in Elle can have exactly zero or one label node poiting up to them, which corresponds (if there is one) to the JUMPDEST instruction that will be the target of this scope's jump. Jumps work similarly, specifying their targets based on which scope they will jump to (“jump n” means “jump to the label bound in the scope n levels up in the syntax tree”) .

For instance, here is Elle pseudocode for an IF statement:

::

   seq [
     seq [
       push 0x01
       jumpI #0
       push 0x02
       jump #1
       label #0
       push 0x03
       label #1
       ]]


Note that this approach provides the locality that we need: two disjoint Seq nodes will have no way of referencing each other's corresponding bound label.


====================
Elle-Core Syntax
====================

**TODO: present Elle Core syntax in a comprehensible diagram**

To cut to the chase, here is the syntax definition for the Elle-Core language, as implemented in Isabelle:

::
   
   type_synonym idx = nat
   datatype ll1 =
     L "inst"
     (* de-Bruijn style approach to local binders *)
     | LLab "idx"
     | LJmp "idx"
     | LJmpI "idx"
     (* sequencing nodes also serve as local binders *)
     | LSeq "ll1 list"




## Label Resolution in Elle-Core

Hopefully I've convinced you that de Bruijn indices are a convenient way to represent the binding structures Elle needs to handle. Next I'm going to describe how we translate this code (that is, syntax trees of type ll1) into EVM bytecode.

Our first step is to calculate *locations* (referred to in the codebase as *quantitative annotations*, or *qan*) for each instruction in our program. The idea is as follows. EVM instructions take up a certain number of bytes as specified in the EVM specification. *Seq* constructs do not take up any space other than the space taken up by their members. *Label* constructs take up one byte (the size of a JUMPDEST instruction). *Jump* instructions take a variable number of bytes, depending on the length of the address to jump to - this number of bytes starts at 2 (one for the JUMP itself, one for the PUSH instruction that puts its address onto the stack) but increases to accommodate the size of the address (the PUSH payload) that  is actually calculated.

Once we have locations computed for all of our syntax-tree nodes, we begin examining the binding structure. For each sequence node, we examine all LLab nodes descended from it. If an LLab node is descended from an LSeq node at a distance of **n**, and that LLab's parameter (a natural number representing the index) is equal to n-1 (remember that we are using zero-indexing), the LLab's location within the tree rooted at that LSeq node is recorded.

If more than one such LLab is found for any one LSeq node, the compiler fails, as the user has given an invalid program. After all, it would not do to have the following (this is real Elle code this time, not pseudocode):

::
   
   LSeq [
   LJmp 0,
   LSeq [
    LLab 1,
    L (PUSH_N [0])
   ],
   LLab 0
   ]

The root LSeq node in this example has two labels “pointing upward” to the same sequence node. This creates an unacceptable ambiguity: to which label should the jump dispatch control flow? Depending on which we pick, we would have have added either 1 or 0 elements to the stack, so clearly they have different behavior. Elle will fail to compile code if it detects this condition.

===========================
Resolving Jump Addresses
===========================

Of course, we're not quite done: we still have to compute the addresses that each of our LJmp nodes will jump to (i.e., what value will be pushed onto the stack before the jump). At this point things get tricky. To save space, we want to minimize the number of bytes we push for each jump. Thus, we begin with the optimistic assumption that each jump target's address will be represented with one byte. With this assumption, we begin looking up the addresses of the labels corresponding to each jump and attempting to fit them into the number of bytes we have allocated.

If we ever fail to fit an address in the space we have allotted, we increase the number of bytes allocated to that jump by 1. Then we recalculate the addresses of all the Elle syntax nodes that must now be shifted, forget all the addresses of jumps we have so far resolved, and then begin the process again. Forgetting the previously resolved jumps is necessary, as their targets' addresses may have changed as a result of the 1-byte adjustment we just made.

Once we have resolved all jump addresses successfully, we have reached a form where we can quite easily write out our program as a sequence of EVM instructions. This forms the bytecode output by the Elle-Core compiler.

===========
Conclusion
===========

In this post, I have described the syntax of Elle-Core, the intermediate representation of the Elle system enabling structured programming, and its translation to EVM. The goal of the Elle project is to formally verify this translation - but that will have to wait for a future post (very briefly, we will write an interpreter for Elle and use induction to prove that the compiled EVM code will always behave the same way as the interpreted Elle code, where the EVM code's behavior is described by the model given in the Eth-Isabelle project).

TODO
In the previous article (:doc:`usage`) we talked about how to use the FourL frontend to write LLL code.
As covered in :doc:`implementation`, 
