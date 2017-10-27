theory LLLL2_grow
  
  imports Main "../ContractSem" "../RelationalSem" "../ProgramInAvl" "../Hoare/Hoare" "../lem/Evm"
  
begin
  
  (* LLLL, mark 2, with "trees that grow" *)

(* we need to rule out invalid, PC, and misc instrs *)
(* stack manipulation should be OK *)
fun inst_valid :: "inst => bool" where
  "inst_valid (Unknown _) = False"
| "inst_valid (Pc _) = False"
| "inst_valid (Misc _) = False"
| "inst_valid _ = True"

(* don't mix up de Bruijn indices with sizes *)  
type_synonym idx = nat
  
(* we need 1 more parameter, for metadata that applies to all nodes *)
(* latter 2 are "pass through" for path datatype *)
  (* we need 1 more parameter, for metadata that applies to all nodes *)
(* latter 2 are "pass through" for path datatype *)
datatype ('ix, 'lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) llt =
  L "'lix" "inst"
  (* de-Bruijn style approach to local binders *)
  | LLab "'llx" "idx"
  | LJmp "'ljx" "idx"
  | LJmpI "'ljix" "idx"
  (* sequencing nodes also serve as local binders *)
  (* do we put an "'ix" in here? *)
  | LSeq "'lsx" "'ix" "('ix * ('ix, 'lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx )llt )list"

type_synonym ('ix, 'lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll =
  "('ix * ('ix, 'lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) llt)"
    
datatype ('ix, 'lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) llpath =
  Top "'ptx" 
  | Node "'pnx" "'lsx" "'ix" "('ix, 'lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll list"
               "('ix, 'lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) llpath"
               "'lsx" "'ix" "('ix, 'lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll list"

type_synonym ('ix, 'lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) llp =
  "('ix * ('ix, 'lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) llpath)"                              

                          
  
(* size decorations *)
  (*
    
(* now we record label target locations, for seq nodes *)
type_synonym ll3 = "((nat * nat), (nat * nat), (nat * nat), (nat * nat), (nat * nat * (nat option))) ll"
  
(* now we record jump target locations *)
type_synonym ll4 = "((nat * nat), (nat * nat), (nat * nat * nat), (nat * nat * nat), (nat * nat * (nat option))) ll"
  *)
  (*
lemma my_ll_induct:
  assumes Ln: "(\<And> i e x . P1 (x, L e i))"
  and La: "(\<And> idx e x . P1 (x, LLab e idx))"
  and Lj: "(\<And>idx e x. P1 (x, LJmp e idx))"
  and Lji : "(\<And>idx e x. P1 (x, LJmpI e idx))"
  and Ljs : "(\<And>e l x . P2 l \<Longrightarrow> P1 (x, LSeq e l))"
  and Lln : "P2 []"
  and Llc : "\<And>l h. P1 h \<Longrightarrow> P2 l \<Longrightarrow> P2 (h # l)"
  shows "P1 (x, t) \<and> P2 l"
*)
  (* do we need a neutral? yesyes *)
  (* what if P3 is a predicate over a list of 'ix data? *)
  (* we need to put this in a locale, make sure x is a monoid *)

locale llll
  
lemma my_ll_induct:
  assumes Ln: "(\<And> i e x . P1 (x, L e i))"
  and La: "(\<And> idx e x . P1 (x, LLab e idx))"
  and Lj: "(\<And>idx e x. P1 (x, LJmp e idx))"
  and Lji : "(\<And>idx e x. P1 (x, LJmpI e idx))"
  and Lls : "(\<And>e l x . P2 x l \<Longrightarrow> P1 (x, LSeq x e l))"
  and Lln : "\<And> n . P2 n []"
  and Llc : "\<And>l x y t z. P1 (x, t) \<Longrightarrow> P2 y l \<Longrightarrow> P3 x y z \<Longrightarrow> P2 z ((x,t) # l)"
  and Hneut : "(\<And> x . P3 x neut x)"
  and Hneut2 : "\<And> x . P3 neut x x"
  and HP2 : "\<And> y x z l . P2 y l \<Longrightarrow> P2 z ((x,t)#l) \<Longrightarrow> P3 x y z"
shows "P1 (x, t) \<and> P2 x l"
proof-
  {fix t
    have "P1 (x, t) \<and> (\<forall> l e . (t = LSeq x e l \<longrightarrow> P2 x l))"
    proof (induction t)
      case (L) thus ?case using Ln by auto next
      case (LLab) thus ?case using La by auto next
      case (LJmp) thus ?case using Lj by auto next
      case (LJmpI) thus ?case using Lji by auto next
      case (LSeq) thus ?case 
      proof(induction l rule:list.induct)
        case Nil 
        thus ?case using Lls[OF Lln] Lln Hneut
          apply(auto)
          apply(subgoal_tac "P2 x []")
            apply(clarsimp)
           apply(auto)
            
            
          
          by auto next
        case (Cons x1 x2) thus ?case using Ljs Lln Llc
          apply(clarsimp)
          apply(case_tac "x1", clarsimp)
          apply(subgoal_tac "P1 (x, b)", auto)
           apply(subgoal_tac "P2 x2", clarsimp)
            
            apply(auto)
            apply(clarsimp)
            apply(auto)
          done next
      qed
    qed}
  thus ?thesis by auto
qed

(* undecorated surface syntax
   TODO define "smart constructors" that plug in unit automatically *)    
type_synonym ll1 = "(unit, unit, unit, unit, unit, unit, unit) ll"

locale l1 begin
  
abbreviation L where "L == ll.L ()"
abbreviation LLab where "LLab == ll.LLab ()"
abbreviation LJmp where "LJmp == ll.LJmp ()"
abbreviation LJmpI where "LJmpI == ll.LJmpI ()"
abbreviation LSeq where "LSeq == ll.LSeq ()"  
end
  
fun ll1_valid :: "ll1 \<Rightarrow> bool" where
  "ll1_valid (l1.L i) = inst_valid i"
| "ll1_valid (l1.LSeq is) = list_all ll1_valid is"
| "ll1_valid _ = True"
    
(* ll2 contains a field for us to decorate label locations and jumps with paths *)
type_synonym ll2 = "((nat * nat), (nat * nat), (nat * nat), (nat * nat),
                     (nat * nat), (nat * nat), (nat * nat)) ll"
type_synonym llp2 = "((nat * nat), (nat * nat), (nat * nat), (nat * nat),
                     (nat * nat), (nat * nat), (nat * nat)) llp"
type_synonym loc2 = "ll2 * llp2"
    
value "(L (0, Arith ADD, 0))"
  
definition jump_size :: "nat" where
  "jump_size = nat (inst_size (Pc JUMP))"
  
declare jump_size_def [simp]

definition jumpi_size :: "nat" where
  "jumpi_size = nat (inst_size (Pc JUMPI))"  

declare jumpi_size_def [simp]
  
(* validity of ll2 terms that have just been translated from ll1 *)
inductive_set
  ll2_valid :: "(nat * ll2 * nat) set" and
  ll2_validl :: "(nat * (ll2 list) * nat) set" 
  where
    "\<And> i n . inst_valid i \<Longrightarrow> (n, 
                               (L (n, n + nat (inst_size i)) i), 
                               n + nat (inst_size i)) \<in> ll2_valid"
  | "\<And> n d . (n, (LLab (n, n) d), n) \<in> ll2_valid"
  | "\<And> n d . (n, (LJmp (n, n+1) d), n+1) \<in> ll2_valid"
  | "\<And> n d . (n, (LJmpI (n, n+1) d), n + 1) \<in> ll2_valid"
  | "\<And> n l n' . (n, l, n') \<in> ll2_validl \<Longrightarrow> (n, (LSeq (n, n') l), n') \<in> ll2_valid  "
  | "\<And> n . (n, [], n) \<in> ll2_validl"  
  | "\<And> n h n' t n'' .
     (n, h, n') \<in> ll2_valid \<Longrightarrow>
     (n', t, n'') \<in> ll2_validl \<Longrightarrow>
     (n, (h # t), n'') \<in> ll2_validl"
 
  
(* we need a size-validity predicate for ll2 *)
(* we take an int indicating where we start from *)
fun ll2_valid_sz :: "ll2 \<Rightarrow> nat \<Rightarrow> (nat * bool)" and
    ll2_valid_sz_seq :: "ll2 list \<Rightarrow> nat \<Rightarrow> (nat * bool)" where
  "ll2_valid_sz (L (i', i'') c) i =
   (i'',
   (inst_valid c \<and> (i' = i) \<and> (i'' = i' + nat (inst_size c))))"
| "ll2_valid_sz (LLab (i', i'') _) i =
   (i'',
   (i' = i \<and> i'' = i'))"
| "ll2_valid_sz (LJmp (i', i'') _) i =
   (i'',
   (i = i' \<and> i'' = i + jump_size))"
| "ll2_valid_sz (LJmpI (i', i'') _) i =
   (i'',
   (i = i' \<and> i'' = i + jumpi_size))"
| "ll2_valid_sz (LSeq (i', i'') ls) i =
   (i'',
   (i = i') \<and> ll2_valid_sz_seq ls i' = (i'', True))"
| "ll2_valid_sz_seq [] i =
   (i, True)"
| "ll2_valid_sz_seq (h # t) i =
   (let (i', b) = ll2_valid_sz h i in
    let (ifin, b') = ll2_valid_sz_seq t i' in 
   (ifin,
    (b = True) \<and> b' = True))"
     
value "ll2_valid_sz (LJmp (n, n + 4) 0) 0"
  
  
lemma ll2_valid_test :
  shows "((n, t, n') \<in> ll2_valid \<longrightarrow> ll2_valid_sz t n = (n', True)) \<and>
         ((m, l, m') \<in> ll2_validl \<longrightarrow> ll2_valid_sz_seq l m = (m', True))"
proof(induction rule: ll2_valid_ll2_validl.induct, auto)
qed  
  
fun ll1_size :: "ll1 \<Rightarrow> nat" and
    ll1_size_seq :: "ll1 list \<Rightarrow> nat" where
    "ll1_size (l1.L inst) = nat (inst_size inst)"
  | "ll1_size (l1.LLab idx) = 0"
  | "ll1_size (l1.LJmp idx) = 1"
  | "ll1_size (l1.LJmpI idx) = 1"
  | "ll1_size (l1.LSeq ls) = ll1_size_seq ls"
  | "ll1_size_seq [] = 0"
  | "ll1_size_seq (h # t) = ll1_size h + ll1_size_seq t"
  
(* first pass, storing sizes *)
fun ll_phase1 :: "ll1 \<Rightarrow> nat \<Rightarrow> (ll2 * nat)" and
    ll_phase1_seq :: "ll1 list \<Rightarrow> nat \<Rightarrow> (ll2 list * nat)"
  where
  "ll_phase1 (l1.L inst) i = (L (i, i + nat (inst_size inst)) inst,
                              i + nat (inst_size inst))"
| "ll_phase1 (l1.LLab idx) i = (LLab (i, i) idx, i)" (* labels take no room *)
| "ll_phase1 (l1.LJmp idx) i = (LJmp (i, 1 + i) idx, 1+i)" (* jumps take at least 1 byte *)
| "ll_phase1 (l1.LJmpI idx) i = (LJmpI (i, 1 + i) idx, 1+i)"
| "ll_phase1 (l1.LSeq ls) i =
   (let (ls', i') = ll_phase1_seq ls i in
   (LSeq (i, i') ls', i'))"
| "ll_phase1_seq [] i = ([], i)"
| "ll_phase1_seq (h # t) i =
   (let (h', i') = ll_phase1 h i in
    (let (t', i'') = ll_phase1_seq t i' in
      ( h' # t', i'')))"
  
definition ll_pass1 :: "ll1 \<Rightarrow> ll2" where
  "ll_pass1 l = fst (ll_phase1 l 0)"

lemma ll_phase1_size_correct :
  fixes "x" "xs"
  shows "(! i . ? x2 . (ll_phase1 x i = (x2, ll1_size x + i))) \<and>
         (! j . ? xs2 . (ll_phase1_seq xs j = (xs2, ll1_size_seq xs + j)))"
proof (induction rule: my_ll_induct)
  case (1 inst e) thus ?case by auto next
  case (2 idx e) thus ?case by auto next
  case (3 idx e) thus ?case by auto next
  case (4 idx e) thus ?case by auto next
  case (5 e l) thus ?case
    apply(clarsimp)
    apply(drule_tac x = "i" in spec)
    apply(case_tac "ll_phase1_seq l i", clarsimp)
    done next
  case 6 thus ?case by auto next
  case (7 h t) thus ?case
    apply(clarsimp)
    apply(case_tac "ll_phase1 t j", clarsimp)
    apply(case_tac "ll_phase1_seq h b", clarsimp)
    apply(drule_tac x = "j" in spec)
    apply(drule_tac x = "b" in spec)
    apply(auto)
    done next
qed
  
lemma ll_phase1_correct:
  shows  "(ll1_valid x \<longrightarrow> 
          (! i . ? x2 . ? i' . ll_phase1 x i = (x2, i') \<and> ll2_valid_sz x2 i = (i', True))) \<and>
          (list_all ll1_valid xs \<longrightarrow>
            (! j . ? xs2 . ? j' .
              ll_phase1_seq xs j = (xs2, j') \<and>
              ll2_valid_sz_seq xs2 j  = (j', True)))"
proof (induction rule:my_ll_induct)
  case (1 i) thus ?case by auto next
  case (2 idx) thus ?case by auto next
  case (3 idx) thus ?case by auto next
  case (4 idx) thus ?case by auto next
  case (5 e l) thus ?case
    apply(clarsimp)
    apply(case_tac "ll_phase1_seq l i", clarsimp)
    apply(drule_tac x = "i" in spec)
    apply(auto)
    done next
  case 6 thus ?case by auto next
  case (7 l t) thus ?case
    apply(clarsimp)
    apply(case_tac "ll_phase1 t j", clarsimp)
    apply(case_tac "ll_phase1_seq l b", clarsimp)
    apply(drule_tac x = "j" in spec)
    apply(drule_tac x = "b" in spec)
    apply(auto)
    done
qed
  
lemma ll_phase1_correct' :
  "(ll1_valid x \<longrightarrow> (! i . ? x2 . ? i' . ll_phase1 x i = (x2, i') \<and> (i, x2, i') \<in> ll2_valid)) \<and>
   (list_all ll1_valid xs \<longrightarrow>
    (! j . ? xs2 . ? j' . ll_phase1_seq xs j = (xs2, j') \<and> (j, xs2, j') \<in> ll2_validl))"
proof(induction rule:my_ll_induct)
  case (1 i) thus ?case by (auto simp add:ll2_valid.simps) next
  case (2 idx) thus ?case by (auto simp add:ll2_valid.simps) next
  case (3 idx) thus ?case by (auto simp add:ll2_valid.simps) next
  case (4 idx) thus ?case by (auto simp add:ll2_valid.simps) next
  case (5 e l) thus ?case
    apply(clarsimp)
    apply(case_tac "ll_phase1_seq l i", clarsimp)
    apply(drule_tac x = "i" in spec)
    apply (auto simp add:ll2_valid.simps)
    done  next
  case (6) thus ?case 
    apply(insert "ll2_valid_ll2_validl.intros")
    apply(auto)
    done next
  case(7 l t) thus ?case
    apply(clarsimp)
    apply(case_tac "ll_phase1 t j", clarsimp)
    apply(case_tac "ll_phase1_seq l b", clarsimp)
    apply(drule_tac x = "j" in spec)
    apply(drule_tac x = "b" in spec)
    apply(auto)
    apply(insert "ll2_valid_ll2_validl.intros")
    apply(auto)
    done
qed
  
value "ll_pass1 (l1.LSeq [l1.LLab 0, l1.L (Arith ADD)])"
  
value "(inst_size (Arith ADD))"
  
type_abbreviation ll2
  
inductive_set ll2_descend :: "(ll2 * ll2 * nat) set"
  where
    "\<And> n n' ls t .
       (n, LSeq (n, n') ls, n') \<in> ll2_valid \<Longrightarrow>
       (t) \<in> set ls \<Longrightarrow>
       (LSeq (n, n') ls, t, 1) \<in> ll2_descend"
  | "\<And> t t' n t'' n' .
       (t, t', n) \<in> ll2_descend \<Longrightarrow>
       (t', t'', n') \<in> ll2_descend \<Longrightarrow>
       (t, t'', n + n') \<in> ll2_descend"
  
(* validity of ll2 terms with labels resolved*)
(* Q: how do we detect label clashes? *)
inductive_set
  ll2_valid2 :: "(nat * ll2 * nat) set" and
  ll2_validl2 :: "(nat * ((nat * ll2 * nat) list) * nat) set"
  where
    "\<And> i n . inst_valid i \<Longrightarrow> (n, (L (n, i, n + nat (inst_size i))), n + nat (inst_size i)) \<in> ll2_valid2"
  | "\<And> n d . (n, (LLab (n, d, None, n)), n) \<in> ll2_valid2"
  | "\<And> n d . (n, (LJmp (n, d, None, 1+n)), 1+n) \<in> ll2_valid2"
  | "\<And> n d . (n, (LJmpI (n, d, None, 1+n)), 1+n) \<in> ll2_valid2"
  | "\<And> n l n' . (n, l, n') \<in> ll2_validl2 \<Longrightarrow>
                 (\<not> (\<exists> k . (LSeq (n, l, n'), LLab (_, k, _, _), k) \<in> ll2_descend)) \<Longrightarrow>
                 (n, (LSeq (n, l, n')), n') \<in> ll2_valid2"
  | "\<And> n l n'. (n, l, n') \<in> ll2_validl2 \<Longrightarrow>
                (\<exists>! k . (LSeq (n, l, n'), LLab (_, k, _, _), k) \<in> ll2_descend) \<Longrightarrow>
                (n, LSeq (n, l, n'), n') \<in> ll2_valid2"
  | "\<And> n . (n, [], n) \<in> ll2_validl2"  
  | "\<And> n h n' t n'' .
     (n, h, n') \<in> ll2_valid2 \<Longrightarrow>
     (n', t, n'') \<in> ll2_validl2 \<Longrightarrow>
     (n, ((n, h, n') # t), n'') \<in> ll2_validl2"

(* idea: how do we calculate label-correctness? *)
fun ll2_add_labels :: "ll2 \<Rightarrow> ll2" where
  "ll2_add_labels (L (n, i, n')) = L (n, i, n')"
   
  
(* before going further with paths, we need some path utilities
   (inspired by Huet's Zippers paper)
 *)
  
  
(* assumes our first notion of validity *)
(* TODO make this parametric w/r/t our syntax ? *)

inductive_set ll2_validl_rev :: "(nat * ((nat * ll2 * nat) list) * nat) set" where
    "\<And> n . (n, [], n) \<in> ll2_validl_rev"
  | "\<And> n l n' h n''.
    (n', h, n'') \<in> ll2_valid \<Longrightarrow>
    (n, l, n') \<in> ll2_validl_rev \<Longrightarrow>
    (n, (n',h,n'')#l, n'') \<in> ll2_validl_rev"
 
(* need an induction lemma for valid_rev *)    

lemma ll2_validl_rev_correct' [rule_format] : 
    "(k, l1, k') \<in> ll2_validl_rev \<Longrightarrow> (\<forall> l2 . (k', l2, k'') \<in> ll2_validl \<longrightarrow> (k, rev l1 @ l2, k'') \<in> ll2_validl)"
proof(induction "k" "l1" "k'"  rule: ll2_validl_rev.induct)
  case (1 n)
  thus ?case by auto 
  case (2 n l n' h n'')
  thus ?case
    apply(auto)
    apply(subgoal_tac "(n', (n', h, n'')#l2, k'') \<in> ll2_validl")
     apply(auto)
    apply(rule ll2_valid_ll2_validl.intros(7))
     apply(auto)
    done
qed

lemma ll2_validl_rev_correct :
  "(k, r, k') \<in> ll2_validl_rev \<Longrightarrow> (k, rev r, k') \<in> ll2_validl"
proof-
  assume H1: "(k, r, k') \<in> ll2_validl_rev"
  have H2: "(k', [], k') \<in> ll2_validl"
    apply(rule ll2_valid_ll2_validl.intros)
  done
  from ll2_validl_rev_correct'[OF H1 H2] have ?thesis
    apply(auto)
    done
  thus ?thesis by auto
qed

lemma ll2_validl_induct' [rule_format]:
  assumes Ll: "(n, t, n') \<in> ll2_validl"
  and Ln: "\<And> n . P n [] n"
  and Lind: "\<And> n h n' l n'' . (n, h, n') \<in> ll2_valid \<Longrightarrow> (n', l, n'') \<in> ll2_validl \<Longrightarrow> P n' l n'' \<Longrightarrow> P n ((n, h, n')#l) n''"
shows "P n t n'"
proof-
  {fix h l n n' m m'
    have "((n, h, n') \<in> ll2_valid \<longrightarrow> (n, h, n') \<in> ll2_valid) \<and>
          ((n, l, n') \<in> ll2_validl \<longrightarrow> P n l n')"
    proof (induction  rule:ll2_valid_ll2_validl.induct)
      case(1 i n) thus ?case by (rule ll2_valid_ll2_validl.intros) next
      case(2 n d) thus ?case by (rule ll2_valid_ll2_validl.intros) next
      case(3 n d) thus ?case by (rule ll2_valid_ll2_validl.intros) next
      case(4 n d) thus ?case by (rule ll2_valid_ll2_validl.intros) next
      case(5 n l n') 
        assume Hlv: "(n, l, n') \<in> ll2_validl"
        thus ?case using ll2_valid_ll2_validl.intros(5)[OF Hlv] 
          apply(auto)
            done next
      case(6 n) thus ?case using Ln by auto next
      case(7 n h n' l n'') 
        assume Hlv: "(n, h, n') \<in> ll2_valid"
         and Hllv : "(n', l, n'') \<in> ll2_validl"
         and Hp : "P n' l n''"
        thus ?case using Lind[OF Hlv]
          apply(auto)
          done
      qed}
    thus ?thesis using Ll by auto
qed

lemma ll2_validl_rev_correct_conv' [rule_format]:
  assumes H1: "(k', l1, k'') \<in> ll2_validl" 
  shows "(\<forall> l2 . (k, l2, k') \<in> ll2_validl_rev \<longrightarrow> (k, (rev l1) @ l2, k'') \<in> ll2_validl_rev)"
proof(induction "k'" "l1" "k''" rule: ll2_validl_induct')
  case (1) thus ?case using H1 by auto
  case (2 n) thus ?case by auto
  case (3 n h n' l n'') thus ?case
    apply(auto)
    apply(subgoal_tac "(k, (n, h, n') # l2, n') \<in> ll2_validl_rev")
     apply(auto)
    apply(rule ll2_validl_rev.intros)
     apply(auto)
    done
qed

lemma ll2_validl_rev_correct_conv :
  "(k, r, k') \<in> ll2_validl \<Longrightarrow> (k, rev r, k') \<in> ll2_validl_rev"
proof-
  assume H1 : "(k, r, k') \<in> ll2_validl"
  have H2 : "(k, [], k) \<in> ll2_validl_rev"
    apply(rule ll2_validl_rev.intros)
    done
  from ll2_validl_rev_correct_conv'[OF H1 H2] have ?thesis by auto
  thus ?thesis by auto
qed
    
    
  (* NOT DONE *)
  (* Q: should path correctness just be indexed to where root is in buffer? *)
  (* Q: better to have a few mut.ind. sets? *)
  (* we are using the first notion of validity *)
  (* Q: make this inductive def better? Can't prove go_left correct *)
inductive_set path2_valid :: "(nat * loc2 * nat) set" where
  "\<And> n n'.
   (n, t, n') \<in> ll2_valid \<Longrightarrow>
   (n, (t, Top (n, n')), n') \<in> path2_valid"
(*|"\<And> .
  (n, t, n') \<in> ll2_valid \<Longrightarrow>
  (n, (t, up), n') \<in> path2_valid \<Longrightarrow>
  ()
"*)
(* Q: move rev into premise to free up form of conclusion? *)
|"\<And> n l n' t n'' r n''' k up k'.
   (n', t, n'') \<in> ll2_valid \<Longrightarrow>
   (n, l, n') \<in> ll2_validl_rev  \<Longrightarrow>
   (n'', r, n''') \<in> ll2_validl \<Longrightarrow>
   (k, (LSeq (n, rev l @ ((n', t, n'')#r), n'''), up), k') \<in> path2_valid \<Longrightarrow> 
   (k, (t, Node(n, l, n', up, n'', r, n''')), k') \<in> path2_valid"


  
fun go_left :: "loc2 \<Rightarrow> loc2" where
  "go_left (t, path2.Node(n, (m,l,m')#ls, n', up, n'', rs, n''')) = 
           (l, path2.Node(n, ls, m, up, m', (n', t, n'')#rs, n'''))"
| "go_left loc = loc" (* bogus *)

(* Q: should these nav functions signal error *)
  
lemma go_left_correct :
  shows "(n, (t, l), n') \<in> path2_valid \<Longrightarrow> (n, go_left (t, l), n') \<in> path2_valid"
proof(induction rule: path2_valid.induct)
  case(1 t n n') thus ?case
    apply(simp)
    apply(rule path2_valid.intros, auto)
    done next
  case(2 n l n' t n'' r n''' k up k')
    thus ?case using ll2_valid_ll2_validl.intros(7)[OF `(n', t, n'')
       \<in> ll2_valid` `(n'', r, n''') \<in> ll2_validl`]
      apply(case_tac l)
       apply(auto)
       apply(erule path2_valid.intros, auto)
        apply(frule ll2_validl_rev.cases, auto)
      apply(rule path2_valid.intros, auto)
      done
qed

  (* go_right *)
fun go_right :: "loc2 \<Rightarrow> loc2" where
  "go_right (t, path2.Node(n, ls, n', up, n'', (m,r,m')#rs, n''')) = 
            (r, path2.Node(n, (n', t, n'')#ls, m, up, m', rs, n'''))"
| "go_right loc = loc" (*bogus*)
  
  (* go_up *)
fun go_up :: "loc2 \<Rightarrow> loc2" where
  "go_up (t, path2.Node(n, ls, n', up, n'', rs, n''')) =
         (LSeq (n, (rev ls)@((n',t,n'')#rs), n'''), up)"
| "go_up loc = loc" (*bogus*)
  
  (* go_down *)
fun go_down :: "loc2 \<Rightarrow> loc2" where
  "go_down (LSeq (n, (m,t,m')#ts, n'), p) =
           (t, path2.Node(n, [], m, p, m', ts, n'))"  
| "go_down loc = loc"

fun assign_label_up :: "loc2 \<Rightarrow> loc2"

fun assign_labels_down :: "loc2 \<Rightarrow> loc2"
and 
  
  (* then we can start talking about recursion *)
  
function sweep :: "loc2 \<Rightarrow> loc2" where
   "sweep (t, path2.Node(n, ls, n', up, n'', (m,r,m')#rs, n''')) =
    sweep (go_right (t, path2.Node(n, ls, n', up, n'', (m,r,m')#rs, n''')))" 
 | "sweep loc = loc"
  
     apply(auto)
     apply(auto)
      
    apply(simp)
   

