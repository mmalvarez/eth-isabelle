theory ElleAltSemantics
  imports Main "Valid4"
begin

(*
Alternate, inductive Elle semantics
Idea is that jumps nondeterministically go to _all_ applicable labels
*)

(* first we need a way to get the next childpath *)
(* this function assumes that this one is a genuine
childpath, it tries to find the next one.
*)


(* is this actually the behavior we want? *)
(* yes, if we implement "falling through" Seq nodes in the inductive
semantics *)
fun cp_next :: "('a, 'b, 'c, 'd, 'e, 'f, 'g) ll \<Rightarrow> childpath \<Rightarrow> childpath option" where
 "cp_next t p =
   (case (rev p) of
    [] \<Rightarrow> None
    | final#rrest \<Rightarrow> 
      (case (ll_get_node t (rev ((final+1)#rrest))) of
        Some _ \<Rightarrow> Some (rev ((final + 1)#rrest))
        | None \<Rightarrow> cp_next t (rev rrest) 
))
 "  

value "cp_next ((0,0), LSeq () [((0,0), L () (Arith ADD)), 
                                ((0,0), L () (Arith ADD)),
                                ((0,0), L () (Arith ADD)),
                                ((0,0), LSeq () [
                                       ((0,0), L () (Arith ADD)),
                                       ((0,0), L () (Arith SUB))
                                  ]),
                                ((0,0), L () (Arith ADD))
                               ]) [4,0]"

value "cp_next ((0,0), LSeq () [((0,0), L () (Arith ADD)), 
                                ((0,0), L () (Arith ADD)),
                                ((0,0), L () (Arith ADD)),
                                ((0,0), LSeq () [
                                       ((0,0), L () (Arith ADD)),
                                       ((0,0), L () (Arith SUB))
                                  ]),
                                ((0,0), L () (Arith ADD))
                               ]) []"

(* need more parameters *)
(* is initial childpath [] or [0]? *)
(* if it's a Seq, go to first child
if it's a jump, go to all targeted jump nodes
if it's any other node, interpret the node
and then go to cp_next *)
(*
have a constructor where if cp_next = None, then we are at the end of the tree
and so we just return (?)
we need to refactor this somehow, the naive approach is too verbose

one idea: what if we just have a separate function that checks if the
resultant cp_next is none?
*)

(* another way to simplify this: force us to enclose the entire thing in a Seq [...]
that doesn't have a label (e.g. only allows jumps in descendents) *)


(* make this not use type parameters? *)
(* here is the old version that has type parameters *)

inductive elle_alt_sem :: "('a, 'b, 'c, 'd, 'e, 'f, 'g) ll \<Rightarrow> 'x llinterp \<Rightarrow> childpath \<Rightarrow> 'x \<Rightarrow> 'x \<Rightarrow> bool" where
(* last node is an instruction *)
"\<And> t cp x e i instD jmpD jmpiD labD st st'.
    ll_get_node t cp = Some (x, L e i) \<Longrightarrow>
    cp_next t cp = None \<Longrightarrow>
    instD i st = st' \<Longrightarrow>
    elle_alt_sem t (instD, jmpD, jmpiD, labD) cp st st'"
(* instruction in the middle *)
| "\<And> t cp x e i cp' instD jmpD jmpiD labD st st' st''.
    ll_get_node t cp = Some (x, L e i) \<Longrightarrow>
    cp_next t cp = Some cp' \<Longrightarrow>
    instD i st = st' \<Longrightarrow>
    elle_alt_sem t (instD, jmpD, jmpiD, labD) cp' st' st'' \<Longrightarrow>
    elle_alt_sem t (instD, jmpD, jmpiD, labD) cp st st''"
(* last node is a label label *)
| "\<And> t cp x e d instD jmpD jmpiD labD st st'.
    ll_get_node t cp = Some (x, LLab e d) \<Longrightarrow>
    cp_next t cp = None \<Longrightarrow>
    labD st = st' \<Longrightarrow>
    elle_alt_sem t (instD, jmpD, jmpiD, labD) cp st st'"
(* label in the middle *)
| "\<And> t cp x e d cp' instD jmpD jmpiD labD st st'.
    ll_get_node t cp = Some (x, LLab e d) \<Longrightarrow>
    cp_next t cp = Some cp' \<Longrightarrow>
    labD st = st' \<Longrightarrow>
    elle_alt_sem t (instD, jmpD, jmpiD, labD) cp' st' st'' \<Longrightarrow>
    elle_alt_sem t (instD, jmpD, jmpiD, labD) cp st st''"
(* jump - TODO *)
(* note that this and jmpI cases do not allow us to resolve jumps at the
root. this limitation doesn't really matter in practice as we can just
wrap in a Seq [] *)
| "\<And> t cpre cj xj ej dj nj cl instD jmpD jmpiD labD st st' st''.
    ll_get_node t (cpre@cj) = Some (xj, LJmp ej dj nj) \<Longrightarrow>
    dj + 1 = length cj \<Longrightarrow>
    ll_get_node t (cpre@cl) = Some (xl, LLab el dl) \<Longrightarrow>
    dl + 1 = length cl \<Longrightarrow>
    jmpD st = st' \<Longrightarrow>
    elle_alt_sem t (instD, jmpD, jmpiD, labD) (cpre@cl) st' st'' \<Longrightarrow>
    elle_alt_sem t (instD, jmpD, jmpiD, labD) cp st st''"
(* jmpI, jump taken - TODO *)
| "\<And> t cpre cj xj ej dj nj cl  instD jmpD jmpiD labD st st' st''.
    ll_get_node t (cpre@cj) = Some (xj, LJmpI ej dj nj) \<Longrightarrow>
    dj + 1 = length cj \<Longrightarrow>
    ll_get_node t (cpre@cl) = Some (xl, LLab el dl) \<Longrightarrow>
    dl + 1 = length cl \<Longrightarrow>
    jmpiD st = (True, st') \<Longrightarrow>
    elle_alt_sem t (instD, jmpD, jmpiD, labD) cp' st' st'' \<Longrightarrow>
    elle_alt_sem t (instD, jmpD, jmpiD, labD) cp st st''"
(* jmpI, jump not taken, at end *)
| "\<And> t cp x e d n instD jmpD jmpiD labD st st'.
    ll_get_node t cp = Some (x, LJmpI e d n) \<Longrightarrow>
    cp_next t cp = None \<Longrightarrow>
    jmpiD st = (False, st') \<Longrightarrow>
    elle_alt_sem t (instD, jmpD, jmpiD, labD) cp st st'"
(* jmpI, jump not taken, in middle *)
| "\<And> t cp x e d n cp' instD jmpD jmpiD labD st st'.
    ll_get_node t cp = Some (x, LJmpI e d n) \<Longrightarrow>
    cp_next t cp = Some cp' \<Longrightarrow>
    jmpiD st = (False, st') \<Longrightarrow>
    elle_alt_sem t (instD, jmpD, jmpiD, labD) cp st' st'' \<Longrightarrow>
    elle_alt_sem t (instD, jmpD, jmpiD, labD) cp st st''"
(* empty sequence, end *)
| "\<And> t cp x e i z.
    ll_get_node t cp = Some (x, LSeq e []) \<Longrightarrow>
    cp_next t cp = None \<Longrightarrow> 
    elle_alt_sem t i cp z z"
(* empty sequence, in the middle *)
| "\<And> t cp x e i cp' z z'. 
    ll_get_node t cp = Some (x, LSeq e []) \<Longrightarrow>
    cp_next t cp = Some cp' \<Longrightarrow>
    elle_alt_sem t i cp' z z' \<Longrightarrow>
    elle_alt_sem t i cp z z'"
(* nonempty sequence *)
| "\<And> t cp x e h rest z z' .
    ll_get_node t cp = Some (x, LSeq e (h#rest)) \<Longrightarrow>
    elle_alt_sem t i (cp@[0]) z z' \<Longrightarrow>
    elle_alt_sem t i cp z z'"
(*
look up childpath (minus last element) at root
if this is 
*)


lemma elle_alt_sem_test :
"elle_alt_sem t i cp st st' \<Longrightarrow>
  True"
proof(induction rule:elle_alt_sem.induct)
case (1 t cp x e i instD jmpD jmpiD labD st st')
  then show ?case by auto
next
  case (2 t cp x e i cp' instD jmpD jmpiD labD st st' st'')
  then show ?case by auto
next
  case (3 t cp x e d instD jmpD jmpiD labD st st')
  then show ?case by auto
next
  case (4 st'' t cp x e d cp' instD jmpD jmpiD labD st st')
  then show ?case by auto
next
  case (5 xl el dl cp t cpre cj xj ej dj nj cl instD jmpD jmpiD labD st st' st'')
  then show ?case by auto
next
  case (6 xl el dl cp' cp t cpre cj xj ej dj nj cl instD jmpD jmpiD labD st st' st'')
  then show ?case by auto
next
  case (7 t cp x e d n instD jmpD jmpiD labD st st')
  then show ?case by auto
next
  case (8 st'' t cp x e d n cp' instD jmpD jmpiD labD st st')
  then show ?case by auto
next
  case (9 t cp x e i z)
  then show ?case by auto
next
  case (10 t cp x e i cp' z z')
  then show ?case by auto
next
  case (11 i t cp x e h rest z z')
  then show ?case sorry
qed

(*
fun cp_next :: "('a, 'b, 'c, 'd, 'e, 'f) ll \<Rightarrow> childpath \<Rightarrow> childpath option" where
"cp_next (x, LSeq e ls) [i] =
  

inductive cp_next :: "('a, 'b, 'c, 'd, 'e, 'f) ll \<Rightarrow> childpath \<Rightarrow> childpath \<Rightarrow> bool" where
"\<And> x c . 
*)
end