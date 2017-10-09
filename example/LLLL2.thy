theory LLLL2
  
  imports Main "../ContractSem" "../RelationalSem" "../ProgramInAvl" "../Hoare/Hoare" "../lem/Evm"
  
begin
  
  (* LLLL, mark 2 *)

(* we need to rule out invalid, PC, and misc instrs *)
(* stack manipulation should be OK *)
fun inst_valid :: "inst => bool" where
  "inst_valid (Unknown _) = False"
| "inst_valid (Pc _) = False"
| "inst_valid (Misc _) = False"
| "inst_valid _ = True"

(* don't mix up de Bruijn indices with sizes *)  
type_synonym idx = nat
  
datatype ll1 =
  L "inst"
  (* de-Bruijn style approach to local binders *)
  | LLab "idx"
  | LJmp "idx"
  | LJmpI "idx"
  (* sequencing nodes also serve as local binders *)
  | LSeq "ll1 list"

lemma old_ll1_induct:
  assumes Ln: "(\<And> i. P1 (L i))"
  and La: "(\<And> idx . P1 (LLab idx))"
  and Lj: "(\<And>idx . P1 (LJmp idx))"
  and Lji : "(\<And>idx . P1 (LJmpI idx))"
  and Ljs : "(\<And>l . P2 l \<Longrightarrow> P1 (LSeq l))"
  and Lln : "P2 []"
  and Llc : "\<And>t l . P1 t \<Longrightarrow> P2 l \<Longrightarrow> P2 (t # l)"
  shows "P1 t \<and> P2 l"
proof-
  {fix t
    have "P1 t \<and> (\<forall> l . t = LSeq l \<longrightarrow> P2 l)"
    proof (induction)
      case (L) thus ?case using Ln by auto next
      case (LLab) thus ?case using La by auto next
      case (LJmp) thus ?case using Lj by auto next
      case (LJmpI) thus ?case using Lji by auto next
      case (LSeq l) thus ?case
        apply (induct l) using Ljs Lln Llc by auto blast+
    qed}
  
  thus ?thesis by auto
qed
          

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
  
fun ll1_size :: "ll1 \<Rightarrow> nat" and
    ll1_size_seq :: "ll1 list \<Rightarrow> nat" where
    "ll1_size (ll1.L inst) = nat (inst_size inst)"
  | "ll1_size (ll1.LLab idx) = 0"
  | "ll1_size (ll1.LJmp idx) = 1"
  | "ll1_size (ll1.LJmpI idx) = 1"
  | "ll1_size (ll1.LSeq ls) = ll1_size_seq ls"
  | "ll1_size_seq [] = 0"
  | "ll1_size_seq (h # t) = ll1_size h + ll1_size_seq t"
  
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

lemma ll_phase1_size_correct :
  fixes "x" "xs"
  shows "(! i . ? x2 . (ll_phase1 x i = (x2, ll1_size x + i))) \<and>
         (! j . ? xs2 . (ll_phase1_seq xs j = (xs2, ll1_size_seq xs + j)))"
proof (induction rule: old_ll1_induct)
  case (1 inst) thus ?case by auto next
  case (2 idx) thus ?case by auto next
  case (3 idx) thus ?case by auto next
  case (4 idx) thus ?case by auto next
  case (5 l) thus ?case
    apply(clarsimp)
    apply(drule_tac x = "i" in spec)
    apply(case_tac "ll_phase1_seq l i", clarsimp)
    done next
  case 6 thus ?case by auto next
  case (7 h t) thus ?case
    apply(clarsimp)
    apply(case_tac "ll_phase1 h j", clarsimp)
    apply(case_tac "ll_phase1_seq t b", clarsimp)
    apply(drule_tac x = "j" in spec)
    apply(drule_tac x = "b" in spec)
    apply(auto)
    done next
qed
  
lemma ll_phase1_correct:
  shows  "(ll1_valid x \<longrightarrow> (! i . ? x2 . ? i' . ll_phase1 x i = (x2, i') \<and> ll2_valid_sz x2 i = (i', True))) \<and>
          (list_all ll1_valid xs \<longrightarrow>
            (! j . ? xs2 . ? j' .
              ll_phase1_seq xs j = (xs2, j') \<and>
              ll2_valid_sz_seq j xs2 j' = True))"
proof (induction rule:old_ll1_induct)
  case (1 i) thus ?case by auto next
  case (2 idx) thus ?case by auto next
  case (3 idx) thus ?case by auto next
  case (4 idx) thus ?case by auto next
  case (5 l) thus ?case
    apply(clarsimp)
    apply(case_tac "ll_phase1_seq l i", clarsimp)
    apply(drule_tac x = "i" in spec)
    apply(auto)
    done next
  case 6 thus ?case by auto next
  case (7 h t) thus ?case
    apply(clarsimp)
    apply(case_tac "ll_phase1 h j", clarsimp)
    apply(case_tac "ll_phase1_seq t b", clarsimp)
    apply(drule_tac x = "j" in spec)
    apply(drule_tac x = "b" in spec)
    apply(auto)
    done
qed
  
value "ll_pass1 (ll1.LSeq [ll1.LLab 0, ll1.L (Arith ADD)])"
  
value "(inst_size (Arith ADD))"
  
(* before going further with paths, we need some path utilities
   (inspired by Huet's Zippers paper)
 *)
  
(* navigation primitives *)
fun go_left :: "loc2 \<Rightarrow> loc2" where
  "go_left (t, (Top i j)) = undefined"
  "go_left (t, (Node (i, l#left, 