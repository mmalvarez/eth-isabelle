theory LLLL2
  
  imports Main "../ContractSem" "../RelationalSem" "../ProgramInAvl" "../Hoare/Hoare" "../lem/Evm"
  
begin
  
  (* LLLL, mark 2 *)

(* don't mix up de Bruijn indices with sizes *)

datatype swag =
  S "int"
  | Seq "swagl"
and swagl =
 SN 
|  SC "swag" "swagl"

    
    
  
(* we need to rule out invalid, PC, and misc instrs *)
(* stack manipulation should be OK *)
fun inst_valid :: "inst => bool" where
  "inst_valid (Unknown _) = False"
| "inst_valid (Pc _) = False"
| "inst_valid (Misc _) = False"
| "inst_valid _ = True"
  
type_synonym idx = nat
  
datatype ll1 =
  L "inst"
  (* de-Bruijn style approach to local binders *)
  | LLab "idx"
  | LJmp "idx"
  | LJmpI "idx"
  (* sequencing nodes also serve as local binders *)
  | LSeq "ll1 list"

(* extra parameter tracks idx depth *)
(* here we also ensure there is only 1 site per binder *)
(* Q: is this the right place to do that? *)
fun ll1_valid :: "ll1 \<Rightarrow> bool" where
  "ll1_valid (L i) = inst_valid i"
  | "ll1_valid (LSeq is) = list_all ll1_valid is"
  | "ll1_valid _ = True"
  
    
(*    
datatype ll2 =
  L "int * inst * int"
  | LLab "int * idx * int"
  | LJmp "int * idx * int"
  | LJmpI "int * idx * int"
  | LSeq "int * (int * ll2 * int) list * int"
*)
(* ll2 contains a field for us to decorate label locations and jumps with paths *)    
datatype ll2 =
  L "nat * inst * nat"
  | LLab "nat * idx * path2 option * nat"
  | LJmp "nat * idx * path2 option * nat"
  | LJmpI "nat * idx * path2 option * nat"
  | LSeq "nat * (nat * ll2 * nat) list * nat"
and path2 =
  Top "nat * nat" (* needs an int argument ? two? *)
  | Node "nat * (nat * ll2 * nat) list * nat * path2 * (nat * ll2 * nat) list * nat"

definition jump_size :: "nat" where
  "jump_size = nat (inst_size (Pc JUMP))"
  
declare jump_size_def [simp]

definition jumpi_size :: "nat" where
  "jumpi_size = nat (inst_size (Pc JUMPI))"  

declare jumpi_size_def [simp]
  
(* we need a size-validity predicate for ll2 *)
(* we take an int indicating where we start from *)
fun ll2_valid_sz :: "ll2 \<Rightarrow> nat \<Rightarrow> (nat * bool)" and
    ll2_valid_sz_seq :: "nat \<Rightarrow> (nat * ll2 * nat) list \<Rightarrow> nat \<Rightarrow> bool" where
  "ll2_valid_sz (L (i', c, i'')) i =
   (i'',
   (inst_valid c \<and> (i' = i) \<and> (i'' = i' + nat (inst_size c))))"
| "ll2_valid_sz (LLab (i', _, _, i'')) i =
   (i'',
   (i' = i \<and> i'' = i'))"
| "ll2_valid_sz (LJmp (i', _, _, i'')) i =
   (i'',
   (i = i' \<and> i'' = i' + jump_size))"
| "ll2_valid_sz (LJmpI (i', _, _, i'')) i =
   (i'',
   (i = i' \<and> i'' = i + jumpi_size))"
| "ll2_valid_sz (LSeq (i', ls, i'')) i =
   (i'',
   (i = i') \<and> ll2_valid_sz_seq i' ls i'')"
| "ll2_valid_sz_seq i [] i' =
   (i = i')"
| "ll2_valid_sz_seq i ((i', h, i'') # t) ifin =
   ((i = i') \<and>
   (ll2_valid_sz h i' = (i'', True)) \<and>
   (ll2_valid_sz_seq i'' t ifin))"
   
      
type_synonym loc2 = "ll2 * path2"
  
(* first pass, storing sizes *)
fun ll_phase1 :: "ll1 \<Rightarrow> nat \<Rightarrow> (ll2 * nat)" and
    ll_phase1_seq :: "ll1 list \<Rightarrow> nat \<Rightarrow> ((nat * ll2 * nat) list * nat)"
  where
  "ll_phase1 (ll1.L inst) i = (ll2.L (i, inst, i + nat (inst_size inst)), i + nat (inst_size inst))"
| "ll_phase1 (ll1.LLab idx) i = (ll2.LLab (i, idx, None, i), i)" (* labels take no room *)
| "ll_phase1 (ll1.LJmp idx) i = (ll2.LJmp (i, idx, None, i + 1), i + 1)" (* jumps take at least 4 bytes *)
| "ll_phase1 (ll1.LJmpI idx) i = (ll2.LJmpI (i, idx, None, i + 1), i + 1)"
| "ll_phase1 (ll1.LSeq ls) i =
   (let (ls', i') = ll_phase1_seq ls i in
   (ll2.LSeq (i, ls', i'), i'))"
| "ll_phase1_seq [] i = ([], i)"
| "ll_phase1_seq (h # t) i =
   (let (h', i') = ll_phase1 h i in
    (let (t', i'') = ll_phase1_seq t i' in
      ( (i, h', i') # t', i'')))"
  
definition ll_pass1 :: "ll1 \<Rightarrow> ll2" where
  "ll_pass1 l = fst (ll_phase1 l 0)"

lemma ll_phase1_ll_phase1_seq :
  "(ll_phase1_seq ls i = (ls', i')) \<longleftrightarrow> (ll_phase1 (ll1.LSeq ls) i) = (ll2.LSeq (i, ls', i'), i')"
  apply(induction ls, auto)
   apply(case_tac "ll_phase1 a i")
   apply(case_tac "ll_phase1_seq ls i'")
   apply(auto)
   apply (case_tac "ll_phase1_seq ls b")
   apply(auto)
  apply(case_tac "ll_phase1 a i")
  apply(case_tac "ll_phase1_seq ls i'")
  apply(auto)
  apply(case_tac "ll_phase1_seq ls b")
    apply(auto)
  done
    
lemma ll_phase1_ll_phase1_seq' :
  "(ll_phase1 (ll1.LSeq ls) i) = (ll2.LSeq (i, ls', i'), i') \<Longrightarrow> (ll_phase1_seq ls i = (ls', i'))"
  apply(simp add: ll_phase1_ll_phase1_seq)
  done 
    
 lemma ll_phase1_ll_phase1_seq'' :
  "(ll_phase1_seq ls i = (ls', i')) \<Longrightarrow> (ll_phase1 (ll1.LSeq ls) i) = (ll2.LSeq (i, ls', i'), i')"
  apply(simp add: ll_phase1_ll_phase1_seq)
   done 
     
lemma ll_phase1_ll_phase1_seqX :
  "(ll_phase1 x i) = (ll2.LSeq (i, ls', i'), i') \<Longrightarrow> (\<exists> y . x = ll1.LSeq y)"
  apply(induction x, auto)
  done 

    
lemma ll1_another :
  "(ll_phase1 x i) = (ll2.LSeq (i, ls', i'), i') \<Longrightarrow> (\<exists> y . x = ll1.LSeq y)"
  apply(induction x, auto)
  done 
    
(* prove ll_phase1_seq_correct first? *)
(* need to somehow capture the variation in position ? *)    
lemma ll_phase1_correct :
  "(ll1_valid x \<Longrightarrow> !i. ? x' . ? i'. ((ll_phase1 x i = (x', i')) \<and> (ll2_valid_sz x' i = (i', True))))"
  
  apply(induction "x", auto)
  apply(case_tac "ll_phase1_seq x i")
  apply(simp)
  apply(case_tac "x", auto)
  apply(case_tac "ll_phase1 aa i")
  apply(auto)
  apply(case_tac "ll_phase1_seq list ba")
  apply(clarsimp)
  apply(subgoal_tac "ll2_valid_sz ab i = (ba, True)", auto)
  apply(auto)
  apply(drule conjE)
    
  
    (*
    apply(clarify)
   apply(rule exE)
   apply(rule exE)
  apply(rule exE, auto)
  apply(rule exI)
  apply(rule exI)
    apply(auto)
  apply (case_tac "(ll_phase1_seq x ?i12 x)")  apply(simp)
    
  apply(case_tac "a", auto)
  apply(case_tac "x", auto)
    
  apply(case_tac "ll_phase1 a i")
  apply(case_tac "ll_phase1_seq list ba")
     apply(simp)
    
  apply(case_tac "x", auto)
    apply(case_tac "ll_phase1 a i")
    apply(simp)
  apply(case_tac "ll_phase1_seq lista bb")
     apply(simp)
  apply(auto)
  apply()
    
  apply(case_tac "list", auto)
    apply(clarsimp)

    
  apply(case_tac "ac", auto)
  
  apply (frule "ll_phase1_ll_phase1_seq''")
  
  apply (subgoal_tac "ll1_valid (ll1.LSeq x)")
   apply(auto)
   apply (case_tac "(ll_phase1_seq x i)")
  apply(auto simp add:list_all_def)
    
  apply(case_tac "(ll_phase1_seq x i)")
  apply(auto)
  apply(insert "ll_phase1_ll_phase1_seq''")
  apply(erule subst)
  apply(erule ssubst)
  apply(auto)
  apply(subst "ll_phase1_ll_phase1_seq")
  apply(case_tac "x", auto)
  apply(case_tac "ll_phase1 aa i")
  apply(auto)
  apply(case_tac "ll_phase1_seq list b")
  apply(clarsimp, auto)
    
  
   
  apply(auto)
  apply(simp add:ll_phase1_ll_phase1_seqX)
  apply(subgoal_tac "? x . 
  
  apply(rule ll_phase1_ll_phase1_seqX)
    
  apply(case_tac "ll_phase1 
  
  apply(case_tac "ll_phase1_seq x i")
  apply(auto)
      
    
  
  apply(auto simp add:ll_phase1_ll_phase1_seq)
  apply (case_tac "ll_phase1_seq x i")
  apply(auto)
  case_tac(
  
    
  apply (case_tac "a", auto)
  apply (simp add:ll_phase1_ll_phase1_seq)
  apply (case_tac "ll_phase1_seq x i", auto)
    
  apply(auto simp add:ll_phase1_ll_phase1_se)
  apply(case_tac "ll_phase1_seq x i")
  apply(auto) 
  case_tac("ll_phase1
  apply(auto simp add:ll_phase1_ll_phase1_seq)
  apply(case_tac "ll_phase1_seq x i")
    apply(auto)

  apply(simp add:ll_phase1.simps(5))
  
   apply(auto)
    apply(auto)
   
    
  apply(simp add: list_all_def)
  apply(case_tac "x", auto)
  apply (case_tac "ll_phase1 aa i")
  apply(auto)
  apply (case_tac "ll_phase1_seq list b")
  apply(case_tac "ab")
  apply(auto)
  apply(case_tac "ab")
  apply(case_tac "(ab, b)")
  apply(auto) 
   
   
   apply (case_tac "(ll_phase1_seq x i)")
  apply(simp add: list_all_def)
    apply(auto)
    apply (simp )
  
  
value "ll_pass1 (ll1.LSeq [ll1.LLab 0, ll1.L (Arith ADD)])"
  
value "(inst_size (Arith ADD))"
  
(* before going further with paths, we need some path utilities
   (inspired by Huet's Zippers paper)
 *)
  
(* navigation primitives *)
fun go_left :: "loc2 \<Rightarrow> loc2" where
  "go_left (t, (Top i j)) = undefined"
  "go_left (t, (Node (i, l#left, 