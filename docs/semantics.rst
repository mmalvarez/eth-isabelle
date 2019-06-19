***************
Elle Semantics
***************

.. contents::

(Note: this documentation page is adapted from
`an entry in the Elle Github wiki <https://github.com/mmalvarez/eth-isabelle/wiki/Elle-Core-Semantics:-The-Meaning-of-Elle>`_

========================================
Goal: A Formal Meaning for Elle Programs
========================================

This document is intended to describe the semantics of the Elle-Core intermediate representation, the code that is translated to EVM via the Elle system using a verified procedure. What it means for this procedure to be “verified” is precisely that the behaviors of the source programs according to their semantics (described here) match the behaviors of the compiled EVM code, according to the EVM semantics described in Eth-Isabelle.

Before continuing, it is worth noting that this semantics uses the original EVM semantics to describe the behavior of individual instructions. However, all higher-level control flow is described by the Elle semantics, capturing the key abstraction Elle is intended to provide (structured control flow).

In the formal Isabelle development implementing Elle, this is actually described as a `*big-step operational semantics* <https://en.wikipedia.org/wiki/Operational_semantics#Big-step_semantics>`_. For clarity of exposition here (i.e., to make the presentation more comprehensible for people not already familiar with inductive semantics) I will describe it here as a "non-deterministic" interpreter. The big-step version of the semantics
is given later in (TODO)

Elle's semantics is nondeterministic
"in theory" but not “in practice”. What I mean by this is that while
source programs can describe nondeterministic behaviors, the Elle compiler will refuse to compile them into EVM programs (this is important, as the EVM is by necessity a deterministic virtual machine). Additionally, it is relatively straightforward to characterize which Elle programs are deterministic (a predicate called "valid3" captures precisely this condition).

TODO link in valid3?

Elle's interpreter uses a *logical program counter* which consists of an index into a syntax tree. In particular, this is expressed as a list of natural numbers, describing the path taken through the tree at each syntax node (that is, "[0,1,2]" means "the root's first child's second child's third child"; these paths are zero-indexed). In the codebase these lists are referred to as *childpaths* or *cp* for short. Most of the correctness proof revolves around showing that this logical program counter advances in such a way that the Elle program's behavior matches that of the EVM program with its standard (integer) program counter.

In the code below, "@" is list concatenation.

=================================
Informal Description of Semantics
=================================

-------------
Instructions
-------------

* Instruction nodes carry an EVM instruction that is guaranteed not to be a JUMP (i.e. no arbitrary modifications of the original program counter)
* If an instruction node is at the end of the tree (there is no next node), we return the result of running that instruction in the EVM semantics
* If the instruction is not at the end, we run the EVM instruction to get a new state, advance the logical program counter to the next instruction, and continue executing the Elle semantics from there

-------
Labels
-------

* Elle labels have the same semantics as an EVM JUMPDEST instruction

------
Jumps
------

* Jump nodes in Elle carry a "depth" parameter, pointing to a particular Sequence node a certain number of levels "up" in the tree.
* Label nodes in Elle also carry a "depth" parameter, which also points "up" the tree a certain number of levels to a Sequence node for which that label is a corresponding jump target
* For an Elle program to be valid, each Sequence node must have exactly one (or zero) label nodes "pointing up" to it
  
    * For valid Elle programs, the semantics of a jump involves moving the logical program counter to the location of the single label corresponding to the target of the jump
      
* Elle's semantics also describes execution of invalid programs, with more than one jump target
  
    * In these cases, Elle's execution *nondeterministically splits*, creating "parallel" executions that separately move the program counter to *each* of the jump targets, and continue executing from there.
    * This behavior cannot be realized by the EVM, and is prevented by checks in Elle's compilation process that assure that programs with multiple labels will not compile successfully to EVM

------------------
Conditional Jumps
------------------

* If the head of the EVM stack in the current state is zero (i.e. the conditional jump will not execute in EVM) and there is no next node in the tree, we are done and can return the current state (after subtracting gas for the jump
  instruction)
* If the head of the EVM stack is zero and there is a next node, we run the unsuccessful jump (subtracting the gas), increment the logical program counter to point to the next node in the tree, and then continue executing
* If the head of the EVM stack is nonzero (the conditional jump will execute) the semantics are the same as that of a jump (other than the different gas cost) - see above.

----------
Sequences
----------

* If a sequence is empty (has no sub-nodes), and there is no next node *after* the current sequence node, we are already done executing and can return the current state
* If a sequence is empty and there is a next node, we advance the logical program counter to that node and continue executing
* If a sequence is non-empty, we begin executing from that sequence's first child



========================
Interpreter (Pseudo)Code
========================

::

   Function get (root, cp) {
     if (cp == []) return root;
       else {
         if (node_type(root) != Seq) return null;
         else {
           if(nth (root, head(cp)) = null) return null;
           else return get(nth (root, head(cp)), tail(cp));
         }
     }
   }

   Function getnext (root, cp) {
      if (cp == []) return null;
      cp' = butlast (cp);
      cpl = last (cp);
      if (getnext (root, (cp'@(cpl+1))) = null) {
        return getnext (root, cp');
      }
      else {
          return (cp'@(cpl + 1));
      }
   }

   // Function get_label_cp(root)
   // returns locations of all labels pointing up to root

   Function ellesem (root, cp, state) {
     switch (get (root, cp)) {
       case null: return emptyset;
       
       // instructions carry which EVM instruction to execute
       case Inst(i):
         if(getnext (root, cp) = null) return evm_sem i state;
         else return ellesem (root, getnext (root, cp), evm_sem i state);
	 
       // labels are jumpdests
       case Label(d):
         if(getnext (root, cp) = null) return evm_sem JUMPDEST state;
         else return ellesem (root, getnext(root, cp), evm_sem JUMPDEST state);
	 
       // jumps carry a depth - how many scopes up to jump to
       case Jump(d):
         ctxpath = take((length cp - d), cp); //take all but last d elements
         context = get(root, ctxpath);
         s = get_label_cp context;
         return set{cp' | ellesem(root, cps, state)};
	 
       case JumpI(d):
         // if we should jump
         if(hd (evm_stack (st)) != 0) {
           ctxpath = take((length cp - d), cp); //take all but last d elements
	   context = get(root, ctxpath);
	   s = get_label_cp context;
	   return set{cp' | ellesem(root, cps, state)};
         }
         else {
           if(getnext (root, cp) = null) return state;
           else return ellesem(root, getnext(root, cp), state);
         }
	 
       // sequences carry a list of sub-nodes
       // we jump to all labels pointing to the Seq node "d" levels up
       case Seq(l):
         if(l == []) {
           if(getnext (root, cp) = null) return state;
           else return (ellesem(root, getnext(root, cp), state));
          }
          // if the list has children, run its first child nexts
          else return ellesem(root, cp@[0], state);
     }
    
   }

    
---------------------
Notes on Interpreter
---------------------

The "jump" and "jumpI" cases in the above code explicitly return sets of states, which captures the nondeterminism of the semantics. All other (deterministic) cases can be considered to be implicitly returning singleton sets containing the single next state (for clarity I have left these implicit).


=============================
Inductive Semantics for Elle
=============================

(While this presentation of Elle's semantics may appear different from the
interpreter, it should be possible to prove their equivalence. Indeed, this
is a goal of the Gazelle project's semantics framework.)


TODO: have the formal semantics (e.g. copy diagram from paper) in addition to interpreter

TODOS

Have a practical example of what the semantics do with a concrete program

Say more about what the proof does? (Or at least link to :doc:`correctness`)
