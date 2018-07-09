theory ElleAltSemantics
  imports Main "Valid4" "../../EvmFacts" "../../example/termination/ProgramList"
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

fun clearprog_cctx :: "constant_ctx \<Rightarrow> constant_ctx" where
"clearprog_cctx e =
  (e \<lparr> cctx_program := empty_program \<rparr>)"

(* TODO: be able to load at an arbitrary position (not just 0)? *)
(* this one seems to have problems with reduction, so I'm not using it *)
fun ll4_load_cctx :: "constant_ctx \<Rightarrow> ll4 \<Rightarrow> constant_ctx" where
"ll4_load_cctx cc t =
  (cc \<lparr> cctx_program := 
        Evm.program_of_lst (codegen' t) ProgramInAvl.program_content_of_lst
      \<rparr>)"

(* based on ProgramList.program_list_of_lst *)
fun  program_list_of_lst_validate  :: "inst list \<Rightarrow> inst list option"  where 
 " program_list_of_lst_validate [] = Some []"
|" program_list_of_lst_validate (Stack (PUSH_N bytes) # rest) =
    (if length bytes \<le> 0 then None
     else (if length bytes > 32 then None
           else (case program_list_of_lst_validate rest of
                        None \<Rightarrow> None
                      | Some rest' \<Rightarrow> 
                          Some ([Stack (PUSH_N bytes)] @
                            map(\<lambda>x. Unknown x) bytes @ rest'))))"
|" program_list_of_lst_validate (i # rest) = 
    (case program_list_of_lst_validate rest of None \<Rightarrow> None | Some rest' \<Rightarrow> Some (i#rest'))"


(* seeing if the list version is easier to work with *)
(* this one doesn't seem to quite be what we want *)
fun ll4_load_lst_map_cctx :: "constant_ctx \<Rightarrow> ll4 \<Rightarrow> constant_ctx" where
"ll4_load_lst_map_cctx cc t =
  (cc \<lparr> cctx_program := Evm.program_of_lst (codegen' t) (\<lambda> il i . program_map_of_lst 0 il (nat i)) \<rparr>)"

fun ll4_load_lst_cctx :: "constant_ctx \<Rightarrow> ll4 \<Rightarrow> constant_ctx" where
"ll4_load_lst_cctx cc t =
  (cc \<lparr> cctx_program := 
      Evm.program.make (\<lambda> i . index (program_list_of_lst (codegen' t)) (nat i))
                       (length (program_list_of_lst (codegen' t)))\<rparr>)"

fun ll4_load_lst_validate :: "constant_ctx \<Rightarrow> ll4 \<Rightarrow> constant_ctx option" where
"ll4_load_lst_validate cc t =
  (case codegen'_check t of None \<Rightarrow> None
        | Some tc \<Rightarrow>
          (case program_list_of_lst_validate tc of None \<Rightarrow> None
            | Some l \<Rightarrow> Some (cc \<lparr> cctx_program := 
                                    Evm.program.make (\<lambda> i . index l (nat i))
                                    (length l) \<rparr>)))"

lemma program_list_of_lst_validate_split [rule_format] :
"(! b c . program_list_of_lst_validate (a @ b) = Some c \<longrightarrow>
 (? a' . program_list_of_lst_validate a = Some a' \<and>
  (? b' . program_list_of_lst_validate b = Some b' \<and>
      c = a' @ b')))"
proof(induction a)
case Nil
  then show ?case 
    apply(auto)
    done
next
  case (Cons a b)
  then show ?case 
    apply(auto)
    apply(case_tac a, auto)
                apply(simp split:Option.option.split_asm Option.option.split, auto)
               apply(simp split:Option.option.split_asm Option.option.split, auto)
              apply(simp split:Option.option.split_asm Option.option.split, auto)
             apply(simp split:Option.option.split_asm Option.option.split, auto)
            apply(simp split:Option.option.split_asm Option.option.split, auto)
           apply(simp split:Option.option.split_asm Option.option.split, auto)
          apply(simp split:Option.option.split_asm Option.option.split, auto)
         apply(simp split:Option.option.split_asm Option.option.split, auto)
        apply(simp split:Option.option.split_asm Option.option.split, auto)
    apply(case_tac x10, auto)
          apply(simp split:Option.option.split_asm Option.option.split, auto)

         apply(case_tac x2, auto)
        apply(simp split:Option.option.split_asm Option.option.split, auto)
       apply(simp split:Option.option.split_asm Option.option.split, auto)
      apply(simp split:Option.option.split_asm Option.option.split, auto)
     apply(simp split:Option.option.split_asm Option.option.split, auto)
    apply(simp split:Option.option.split_asm Option.option.split, auto)
    done
qed

fun setpc_ir :: "instruction_result \<Rightarrow> nat \<Rightarrow> instruction_result" where
"setpc_ir ir n =
  irmap (\<lambda> v . v \<lparr> vctx_pc := (int n) \<rparr>) ir"

(* this is the basic idea of the theorem statement
the only thing we need to do is specify the precise
relationship between states - i.e. relationship between the cp that the
semantics is starting from and the pc that the program starts from *)
(*
additional assumption - we need to be valid3', and our first element of the
qvalidity has to be 0
*)
(* program_sem_t appears to be way too slow to execute - perhaps better
to switch back... *)
(* prove this holds for any non-continuing final state
(problem - will we need to make this hold inductively for non-final states?)
(will we have a problem with the hardcoded zero start? maybe we need to
subtract it from the final pc)
 *)
(*
lemma elle_alt_correct :
"elle_alt_sem ((0, sz), (t :: ll4t)) elle_interp cp (ir, cc, net) (ir', cc', net') \<Longrightarrow>
 ((0, sz), t) \<in> ll_valid3' \<Longrightarrow>
 ll4_validate_jump_targets [] ((0,sz),t) \<Longrightarrow>
 program_sem_t (ll4_load_cctx cc ((0,sz),t)) net ir = ir2' \<Longrightarrow>
 setpc_ir ir' 0 = setpc_ir ir2' 0
"
*)
(* Should we use "erreq", which throws away the details of the error *)
(* perhaps the issue is that we are sort of implicitly destructing on
the three-tuple in this inductive statement *)
(* est should probably be a record
  fst \<rightarrow> instruction result
  fst . snd \<rightarrow> cctx
  snd . snd \<rightarrow> net
*)

(* need new predicates: isi2e and iscont *)

fun isi2e :: "instruction_result \<Rightarrow> bool" where
"isi2e (InstructionToEnvironment _ _ _) = True"
| "isi2e _ = False"

definition iscont :: "instruction_result \<Rightarrow> bool" where
"iscont i = (\<not> (isi2e i) )"

(* from examples/termination/RunList *)
(*
theorem program_content_first [simp] :
  "program_map_of_lst 0 (a # lst) 0 = Some a"
apply(cases a)
apply(auto)
apply(subst program_list_content_eq4)
apply(cases "get_stack a")
apply(auto)
done
*)

(* need a couple lemmas about program_map_of_lst *)

(* will it suffice to only consider computations that end in a successful result? 
this seems sketchy, but I guess the idea is "computation suffixes"
*)

lemma qvalid_less' :
"(((a, (t :: ('a, 'b, 'c, 'd, 'e, 'f, 'g) llt)) \<in> ll_valid_q) \<longrightarrow> fst a \<le> snd a) \<and>
 ((((a1, a2), (l:: ('a, 'b, 'c, 'd, 'e, 'f, 'g) ll list)) \<in> ll_validl_q \<longrightarrow> a1 \<le> a2))
"
  apply(induction rule: ll_valid_q_ll_validl_q.induct, auto)
  done

lemma qvalid_less1 :
"((a, (t :: ('a, 'b, 'c, 'd, 'e, 'f, 'g) llt)) \<in> ll_valid_q) \<Longrightarrow> fst a \<le> snd a"
  apply(insert qvalid_less') apply(fastforce)
  done

lemma qvalid_less2 :
"(x, (l :: ('a, 'b, 'c, 'd, 'e, 'f, 'g) ll list)) \<in> ll_validl_q \<Longrightarrow> fst x \<le> snd x"
  apply(insert qvalid_less') apply(case_tac x)
  apply(fastforce)
  done

(* we need to rule out invalid (too long/ too short)
stack instructions *)
(* need additional premise about validity of
jump annotations *)
lemma qvalid_codegen'_check' :
  "(((a, (t :: ll4t)) \<in> ll_valid_q) \<longrightarrow> 
      (! il1 . codegen'_check (a, t) = Some il1 \<longrightarrow>
      (! il2 . program_list_of_lst_validate il1 = Some il2 \<longrightarrow>
      snd a \<ge> fst a \<and> length (il2) = snd a - fst a))) \<and>
 (((a1, a2), (l::  ll4 list)) \<in> ll_validl_q \<longrightarrow> 
      (! ils . List.those (map codegen'_check l) = Some ils \<longrightarrow>
      (! il . program_list_of_lst_validate (List.concat ils) = Some il  \<longrightarrow>
        a2 \<ge> a1 \<and> length il = a2 - a1)))"
proof(induction rule:ll_valid_q_ll_validl_q.induct)
case (1 i x e)
  then show ?case 
    apply(auto)
    apply(case_tac i, auto)
    apply(case_tac x10, auto)
    apply(simp split: if_split_asm)
    done
next
  case (2 x d e)
  then show ?case by auto
next
  case (3 x d e s)
  then show ?case 
    apply(auto)
    done
next
  case (4 x d e s)
  then show ?case
    apply(auto)
    done
next
  case (5 n l n' e)
  then show ?case 
    apply(auto)
     apply(case_tac "those (map codegen'_check l)", auto)
apply(case_tac "those (map codegen'_check l)", auto)
    done
next
  case (6 n)
  then show ?case
    apply(auto)
    done
next
  case (7 n h n' t n'')
  then show ?case 
    apply(auto)
    apply(case_tac "codegen'_check ((n,n'), h)", auto)
     apply(drule_tac program_list_of_lst_validate_split) apply(auto)
    apply(case_tac "codegen'_check ((n, n'), h)", auto)
    apply(drule_tac program_list_of_lst_validate_split) apply(auto)
    done
qed

lemma qvalid_codegen'_check1 [rule_format]:
  "(((a, (t :: ll4t)) \<in> ll_valid_q) \<longrightarrow> 
      (! il1 . codegen'_check (a, t) = Some il1 \<longrightarrow>
      (! il2 . program_list_of_lst_validate il1 = Some il2 \<longrightarrow>
      snd a \<ge> fst a \<and> length (il2) = snd a - fst a)))"
  apply(insert qvalid_codegen'_check')
  apply(fastforce)
  done

(* TODO: use descend here? *)

lemma qvalid_desc_bounded' :
"((a, (t :: ('a, 'b, 'c, 'd, 'e, 'f, 'g) llt)) \<in> ll_valid_q \<longrightarrow>
 (! cp nd nd' desc . ll_get_node (a, t) cp = Some ((nd, nd'), desc) \<longrightarrow>
    nd \<ge> fst a \<and> nd' \<le> snd a)) \<and>
  (((al, al'), (l :: ('a, 'b, 'c, 'd, 'e, 'f, 'g) ll list)) \<in> ll_validl_q \<longrightarrow>
    (! n  ac ac' tc. n < length l \<longrightarrow> l ! n = ((ac, ac'), tc) \<longrightarrow>
   (! cp nd nd' desc . 
    ll_get_node ((ac, ac'), tc) cp = Some ((nd, nd'), desc) \<longrightarrow>
    nd \<ge> al \<and> nd' \<le> al')))" 
proof(induction rule:ll_valid_q_ll_validl_q.induct)
case (1 i x e)
  then show ?case apply(auto)
     apply(case_tac cp, auto)
    apply(case_tac cp, auto)
    done
next
  case (2 x d e)
  then show ?case 
    apply(auto)
         apply(case_tac cp, auto)
    apply(case_tac cp, auto)
    done
next
  case (3 x d e s)
  then show ?case
apply(auto)
         apply(case_tac cp, auto)
    apply(case_tac cp, auto)
    done
next
  case (4 x d e s)
  then show ?case
apply(auto)
         apply(case_tac cp, auto)
    apply(case_tac cp, auto)
    done
next
  case (5 n l n' e)
  then show ?case apply(auto)
     apply(case_tac cp, auto)
     apply(frule_tac ll_get_node_len) apply(drule_tac x = a in spec) apply(auto)
     apply(case_tac "index l a", auto)
     apply(frule_tac "ll_get_node_child") apply(auto)
    apply(case_tac cp, auto)
    apply(frule_tac ll_get_node_len)
    apply(drule_tac x = a in spec) apply(auto)
    apply(case_tac "index l a", auto)
    apply(frule_tac "ll_get_node_child", auto)
    done
next
  case (6 n)
  then show ?case by auto
next
  case (7 n h n' t n'')
  then show ?case 
    apply(clarify)
    apply(case_tac na, auto)
      apply(drule_tac x = cp in spec) apply(auto)
      apply(drule_tac qvalid_less2, auto)

     apply(drule_tac x = nat in spec) apply(auto)
     apply(rotate_tac -1)
     apply(drule_tac x = cp in spec, rotate_tac -1)
     apply(auto)
     apply(drule_tac qvalid_less1, auto)

     apply(drule_tac x = nat in spec) apply(auto)
     apply(rotate_tac -1)
     apply(drule_tac x = cp in spec, rotate_tac -1)
     apply(auto)

done
qed

lemma valid3'_qvalid :
"((x,t )  :: ('a, 'b, 'c, 'd, 'e) ll3') \<in> ll_valid3' \<Longrightarrow>
  ((x, t) :: ('a, 'b, 'c, 'd, 'e) ll3') \<in> ll_valid_q"
  apply(induction rule:ll_valid3'.induct)
  apply(auto simp add:ll_valid_q_ll_validl_q.intros)
  done

(*
idea: don't use program_map_of_lst?
maybe just use program_list_of_lst with index?
it would be nice to be able to use the "bang" notation,
but maybe LemExtraDefs.index is the way to go?
*)
lemma elle_alt_correct :
"elle_alt_sem ((t :: ll4)) intp cp est est' (* (ir, cc, net) (ir', cc', net') *) \<Longrightarrow>
 (t \<in> ll_valid3' \<longrightarrow>
  (! tend ttree . t = ((0, tend), ttree) \<longrightarrow>
 ll4_validate_jump_targets [] t \<longrightarrow>
 intp = elle_interp \<longrightarrow>
 (! targstart targend tdesc . ll_get_node t cp = Some ((targstart, targend), tdesc) \<longrightarrow>
   (! vi . fst est = InstructionContinue vi \<longrightarrow>
   (! act vc venv fuel stopper . program_sem stopper
               (ll4_load_lst_cctx (fst (snd est)) t) 
               fuel (snd (snd est)) 
(* is this arithmetic around fst (fst t) right? *)
(* perhaps we need a secondary proof that validity implies
that targstart will be greater than or equal to fst (fst t) *)
               (setpc_ir (fst est) (targstart  (*- fst (fst t) *))) = 
                   (* fuel can be arbitrary, but we require to compute to a final result *)
                   InstructionToEnvironment act vc venv \<longrightarrow>
                  (* the issue may have to do with distinguishing between errors? *)
                  setpc_ir (fst est') 0 = setpc_ir (InstructionToEnvironment act vc venv) 0)))))"
proof(induction rule:elle_alt_sem.induct)
case (1 t cp x e i instD jmpD jmpiD labD st st')
  then show ?case 
    apply(clarify)
    apply(subgoal_tac "(x, llt.L e i) = ((targstart, targend), tdesc)") apply(auto)

    apply(case_tac fuel, auto)
     apply(split Option.option.split_asm) apply(auto)
      apply(split Option.option.split_asm) apply(auto)
     apply(split Option.option.split_asm) apply(auto)
     apply(simp split:if_split_asm) apply(auto)
         apply(simp_all add:program.defs)


(*
another phrasing of the lemmas we need
0 (DONE) valid3' implies q validity
1. (DONE) length of (program_list_of_lst) of a valid tree is equal to its ending annotation
2 (DONE). if we are descended from a valid root then our start \<ge> root's start and our end \<le> root's end
*)
(*
lemma:
- if we are valid
- and we have a descendent at a certain location
- then we will find 
- 
*)

         apply(case_tac elle_interp) 
         apply(simp add:elle_interp_def, clarify)
    apply(clarsimp)
 (* ok, we should do a proof sketch:
1. map_of_lst t addr = get_by_addr t (addr - startloc t)
2. need to say something else about program sem (but what?) *)
(* use Hoare? *)
    apply(case_tac "rev cp")
          apply( auto)
          apply(simp add:elle_interp_def, clarify)

          apply(case_tac st, clarsimp)


    apply(subst)
    (* show a correspondence between elle_instD an program_sem? *)
          (*
(* old proof follows *)
          apply(case_tac fuel, auto)
     apply(split Option.option.split_asm)
      apply(split Option.option.split_asm) apply(auto)
     apply(split Option.option.split_asm) apply(auto)
      (* this case should be easy because the map lookup will always succeed
          *)
    apply(simp add:Evm.program.defs)
      apply(case_tac i, auto) apply(case_tac x10, auto)


     apply(simp split:if_split_asm) apply(auto)
    apply(simp split: Option.option.split_asm)

          apply(case_tac i, auto) apply(case_tac x10, auto)
      (*   apply(case_tac i, auto) apply(case_tac x10, auto)
        apply(case_tac i, auto) apply(case_tac x10, auto)
       apply(case_tac i, auto) apply(case_tac x10, auto)
      apply(case_tac i, auto) apply(case_tac x10, auto)
     apply(split if_split_asm) apply(clarsimp)                                                                                                                                                                                                                  
apply(case_tac i, clarsimp) (* is this the right place to split on i? *)
    apply(case_tac x1)
    apply(simp_all add: elle_interp_def)
      apply(clarsimp) apply(case_tac st, simp) apply(hypsubst)
(* manageable-ish up to here. case tac on i next? *)

                  apply(simp split: if_split_asm)
(* here we could derive a contradiction from the fact
that Unknown is not a valid instruction - but I think
we can also do a proof that mirrors how the valid cases
will look (e.g. stop) *)
(* mostly manageable up to here *)
                     apply(simp_all add:check_resources_def)
    apply(clarsimp)
    apply(case_tac x2a, clarsimp)
                     apply(case_tac "vctx_stack vi", clarsimp)
                      apply(case_tac st) apply(clarsimp)
    apply(subgoal_tac "True")
                 apply(case_tac i, clarsimp)
                        apply(split if_split_asm) apply(clarsimp)
    apply(simp)
    apply(simp split: Option.option.split_asm)
*)
(*
                        apply(case_tac st, clarsimp)

                        apply(simp split: if_split_asm) 
                        apply(simp_all)
                        apply (simp_all add:check_resources_def)
                        apply(case_tac x10, clarsimp) apply(hypsubst)
                        apply(fastforce)
                        apply(fastforce)
                        apply(clarsimp)
                        apply(case_tac x2a, clarsimp)
                        apply(case_tac i, clarsimp) apply(hypsubst)
                        apply(case_tac x2, clarsimp) apply(case_tac st, simp, hypsubst)
    apply(simp split:if_split_asm) 
                        apply(fastforce)

    apply(subst check_resources_def)
    apply(simp add:lookup.simps)
    
next
  case (2 t cp x e i cp' instD jmpD jmpiD labD st st' st'')
  then show ?case sorry
next
  case (3 t cp x e d instD jmpD jmpiD labD st st')
  then show ?case sorry
next
  case (4 st'' t cp x e d cp' instD jmpD jmpiD labD st st')
  then show ?case sorry
next
  case (5 xl el dl cp t cpre cj xj ej dj nj cl instD jmpD jmpiD labD st st' st'')
  then show ?case sorry
next
  case (6 xl el dl cp' cp t cpre cj xj ej dj nj cl instD jmpD jmpiD labD st st' st'')
  then show ?case sorry
next
  case (7 t cp x e d n instD jmpD jmpiD labD st st')
  then show ?case sorry
next
  case (8 st'' t cp x e d n cp' instD jmpD jmpiD labD st st')
  then show ?case sorry
next
  case (9 t cp x e i z)
  then show ?case sorry
next
  case (10 t cp x e i cp' z z')
  then show ?case sorry
next
  case (11 i t cp x e h rest z z')
  then show ?case
    apply(clarsimp)
    sorry
qed

(*
fun cp_next :: "('a, 'b, 'c, 'd, 'e, 'f) ll \<Rightarrow> childpath \<Rightarrow> childpath option" where
"cp_next (x, LSeq e ls) [i] =
  

inductive cp_next :: "('a, 'b, 'c, 'd, 'e, 'f) ll \<Rightarrow> childpath \<Rightarrow> childpath \<Rightarrow> bool" where
"\<And> x c . 
*)
end