theory LLLL
  
  imports Main Nat "../ContractSem" "../RelationalSem" "../ProgramInAvl" "../Hoare/Hoare" "../lem/Evm" 
begin

value "CHR''0'' :: char"
(* convenience routines for reading/printing hex as string *)
value "List.hd (''abcd'' :: char list)"

definition hexread1_dom :: "char \<Rightarrow> bool" where
"hexread1_dom c = (c = CHR ''0'' \<or> c = CHR ''1'' \<or> c = CHR ''2'' \<or>
                   c = CHR ''3'' \<or> c = CHR ''4'' \<or> c = CHR ''5'' \<or>
                   c = CHR ''6'' \<or> c = CHR ''7'' \<or> c = CHR ''8'' \<or>
                   c = CHR ''9'' \<or> c = CHR ''A'' \<or> c = CHR ''B'' \<or>
                   c = CHR ''D'' \<or> c = CHR ''E'' \<or> c = CHR ''F'')"

definition hexread1 :: "char \<Rightarrow> nat" where
"hexread1 c = (if c = (CHR ''0'') then 0 else
               if c = (CHR ''1'') then 1 else
               if c = (CHR ''2'') then 2 else
               if c = (CHR ''3'') then 3 else
               if c = (CHR ''4'') then 4 else
               if c = (CHR ''5'') then 5 else
               if c = (CHR ''6'') then 6 else
               if c = (CHR ''7'') then 7 else
               if c = (CHR ''8'') then 8 else
               if c = (CHR ''9'') then 9 else
               if c = (CHR ''A'') then 10 else
               if c = (CHR ''B'') then 11 else
               if c = (CHR ''C'') then 12 else
               if c = (CHR ''D'') then 13 else
               if c = (CHR ''E'') then 14 else
               if c = (CHR ''F'') then 15 else
               undefined)"

definition hexwrite1_dom :: "nat \<Rightarrow> bool" where
"hexwrite1_dom n = (n < 16)"

definition hexwrite1 :: "nat \<Rightarrow> char" where
"hexwrite1 c = (if c = 0 then CHR ''0'' else
                if c = 1 then CHR ''1'' else
                if c = 2 then CHR ''2'' else
                if c = 3 then CHR ''3'' else
                if c = 4 then CHR ''4'' else
                if c = 5 then CHR ''5'' else
                if c = 6 then CHR ''6'' else
                if c = 7 then CHR ''7'' else
                if c = 8 then CHR ''8'' else
                if c = 9 then CHR ''9'' else
                if c = 10 then CHR ''A'' else
                if c = 11 then CHR ''B'' else
                if c = 12 then CHR ''C'' else
                if c = 13 then CHR ''D'' else
                if c = 14 then CHR ''E'' else
                if c = 15 then CHR ''F'' else undefined)"

value "(1 < (0::nat))"

lemma hexread1_hexwrite1 : "hexread1_dom c \<Longrightarrow> hexwrite1 (hexread1 c) = c"
  apply (auto simp add:hexread1_dom_def hexread1_def hexwrite1_def)
  done

lemma hexwrite1_help :
"n < 16 \<Longrightarrow>
    n \<noteq> 15 \<Longrightarrow>
    n \<noteq> 14 \<Longrightarrow>
    n \<noteq> 13 \<Longrightarrow>
    n \<noteq> 12 \<Longrightarrow>
    n \<noteq> 11 \<Longrightarrow>
    n \<noteq> 10 \<Longrightarrow>
    n \<noteq> 9 \<Longrightarrow>
    n \<noteq> 8 \<Longrightarrow>
    n \<noteq> 7 \<Longrightarrow>
    n \<noteq> 6 \<Longrightarrow>
    n \<noteq> 5 \<Longrightarrow>
    n \<noteq> 4 \<Longrightarrow>
    n \<noteq> 3 \<Longrightarrow>
    n \<noteq> 2 \<Longrightarrow>
    n \<noteq> Suc 0 \<Longrightarrow>
    0 < n \<Longrightarrow> False"
proof(induction n, auto)
qed 

lemma hexwrite1_hexread1 : "hexwrite1_dom n \<Longrightarrow> hexread1 (hexwrite1 n) = n"
  apply(auto simp add:hexwrite1_dom_def hexwrite1_def)
                  apply(auto simp add:hexread1_def)
                  apply(insert hexwrite1_help, auto)
  done


definition hexread2 :: "char \<Rightarrow> char \<Rightarrow> nat" where
"hexread2 c1 c2 = (16 * (hexread1 c1) + hexread1 c2)"

(* we need to reverse the input list? *)
(* TODO: later handle zero padding for odd numbers of bytes *)
fun hexread' :: "char list \<Rightarrow> nat \<Rightarrow> nat" where
"hexread' [] n = n"
| "hexread' [_] _ = undefined"
| "hexread' (n1#n2#t) a = hexread' t (hexread2 n1 n2 + 256 * a)"

definition hexread :: "char list \<Rightarrow> nat" where
"hexread ls = hexread' ls 0"

fun hexwrite2 :: "8 word \<Rightarrow> (char * char)" where
"hexwrite2 w = 
  (case Divides.divmod_nat (Word.unat w) 16 of
       (d,m) \<Rightarrow> (hexwrite1 d, hexwrite1 m))"

(* TODO: make sure we aren't supposed to do the reverse of this *)
fun hexwrite :: "8 word list \<Rightarrow> char list" where
"hexwrite [] = []"
| "hexwrite (h#t) = (case hexwrite2 h of
                     (c1, c2) \<Rightarrow> c1#c2#(hexwrite t))"

value "(hexwrite [1,2])"

(* *)

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

lemma my_ll1_induct:
  assumes Ln: "(\<And> i. P1 (L i))"
  and La: "(\<And> idx . P1 (LLab idx))"
  and Lj: "(\<And>idx . P1 (LJmp idx))"
  and Lji : "(\<And>idx . P1 (LJmpI idx))"
  and Lls : "(\<And>l . P2 l \<Longrightarrow> P1 (LSeq l))"
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
        apply (induct l) using Lls Lln Llc by auto blast+
    qed}
  
  thus ?thesis by auto
qed
          
fun ll1_valid :: "ll1 \<Rightarrow> bool" where
  "ll1_valid (L i) = inst_valid i"
  | "ll1_valid (LSeq is) = list_all ll1_valid is"
  | "ll1_valid _ = True"
  
    
(* "quantitative annotations" *)
type_synonym qan = "nat * nat"
  
datatype ('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) punit =
  PU

(* let's try the uniform version with pairs first *)
(* Q: can we fix the cases for valid_q by adding a 'dummy' optional argument of each data type? - doesn't seem to work *)
datatype ('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) llt =
  L "'lix" "inst"
  (* de-Bruijn style approach to local binders *)
  | LLab "'llx" "idx"
  (* idx stores which label it is
     nat stores how many bytes *)
  | LJmp "'ljx" "idx" "nat"
  | LJmpI "'ljix" "idx" "nat"
  (* sequencing nodes also serve as local binders *)
  (* do we put an "'ix" in here? *)
  | LSeq "'lsx" "(qan * ('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx )llt )list"
    
type_synonym ('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll =
  "(qan * ('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) llt)"

(* Q: should P2 also take a qan expressing entire list? *)
lemma my_ll_induct:
  assumes Ln: "(\<And> q e i. P1 (q, L e i))"
  and La: "(\<And> q e idx . P1 (q, LLab e idx))"
  and Lj: "(\<And> q e idx n . P1 (q, LJmp e idx n))"
  and Lji : "(\<And> q e idx n . P1 (q, LJmpI e idx n))"
  and Lls : "(\<And> q e l . P2 l \<Longrightarrow> P1 (q, LSeq e l))"
  and Lln : "P2 []" (* should this only be identical q? *)
  and Llc : "\<And> h l. P1 h \<Longrightarrow> P2 l \<Longrightarrow> P2 (h # l)"
  shows "P1 t \<and> P2 l"
proof-
  {fix t 
    have "(\<forall> q . P1 (q, t)) \<and> (\<forall> l e . t = LSeq e l \<longrightarrow> P2 l)"
    proof (induction)
      case (L) thus ?case using Ln by auto next
      case (LLab) thus ?case using La by auto next
      case (LJmp) thus ?case using Lj by auto next
      case (LJmpI) thus ?case using Lji by auto next
      case (LSeq e l) thus ?case 
      proof(induct l)
        case Nil thus ?case using Lln Lls by auto next
        case (Cons a l)
        thus ?case using Llc Lls
          apply(clarsimp) 
          apply(case_tac a)
          apply(subgoal_tac "P1 a") apply(clarsimp)
           apply(subgoal_tac "P2 l") apply(clarsimp)
           apply(auto, blast)
          apply(metis)
          done
      qed
    qed} 
  thus ?thesis
    apply(case_tac t)
    apply(auto, blast )
  done qed

(*Q: do we need more qan's in the path *)
datatype ('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) llpath =
  Top "'ptx" 
  | Node "'pnx" "'lsx" "('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll list"
               "('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) llpath"
               "('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll list" 

(* undecorated syntax with qan *)  
(* TODO: change these from units to any type *)
type_synonym ll2 =
  "(unit, unit, unit, unit, unit, unit, unit) ll"

type_synonym ll2p = 
  "(unit, unit, unit, unit, unit, unit, unit) llpath"

(* location = path + node *)  
type_synonym ll2l = "(ll2 * ll2p)"  

(* decorate Seq nodes with label resolution *)  
(* Q: just store which number child? list of nats representing path?*)
type_synonym ll3t =
  "(unit, bool, unit, unit, nat list, unit, unit) llt"  

type_synonym ('lix, 'ljx, 'ljix, 'ptx, 'pnx) ll3t' =
  "('lix, bool, 'ljx, 'ljix, nat list, 'ptx, 'pnx) llt"
  
type_synonym ll3 =
  "(unit, bool, unit, unit, nat list, unit, unit) ll"  


type_synonym ('lix, 'ljx, 'ljix, 'ptx, 'pnx) ll3' =
  "('lix, bool, 'ljx, 'ljix, nat list, 'ptx, 'pnx) ll"
  
type_synonym ll3p = 
  "(unit, bool, unit, unit, nat list, unit, unit) llpath"
  
type_synonym ll3l = "ll3 * ll3p"
  
type_synonym ll4t =
  "(unit, bool, nat, nat, nat list, unit, unit) llt"  
  
type_synonym ll4 =
  "(unit, bool, nat, nat, nat list, unit, unit) ll"  
  
type_synonym ll4p = 
  "(unit, bool, nat, nat, nat list, unit, unit) llpath"
  
type_synonym ll4l = "ll4 * ll4p"


  
    
definition jump_size :: "nat" where
  "jump_size = nat (inst_size (Pc JUMP))"
  
declare jump_size_def [simp]

definition jumpi_size :: "nat" where
  "jumpi_size = nat (inst_size (Pc JUMPI))"  

declare jumpi_size_def [simp]
  
(* validity of ll2 terms that have just been translated from ll1 *)
(* TODO: we need to break this up into separate pieces for each constructor,
   this way we can reuse them later without type variable ambiguities *)

definition ll_valid_qi :: "(qan * inst) set" where
  "ll_valid_qi = {((n,n'),i) . inst_valid i \<and> n' = n + nat (inst_size i)}"

declare ll_valid_qi_def [simp]  
  
definition ll_valid_ql :: "(qan * idx) set" where
  "ll_valid_ql = {((n,n'),i) . n' = n+1}"
  
declare ll_valid_ql_def [simp]  

(* +2 to account for the push instruction and the jump instruction *)
definition ll_valid_qj :: "(qan * idx * nat) set" where
  "ll_valid_qj = {((n,n'),d,s) . n' = n + 2 + s}"

declare ll_valid_qj_def [simp]  
  
definition ll_valid_qji :: "(qan * idx * nat) set" where
  "ll_valid_qji = {((n,n'),d,s) . n' = n + 2 + s}"

declare ll_valid_qji_def [simp]
  
inductive_set
  ll_valid_q :: "('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll set" and
  ll_validl_q :: "(qan * (('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll list)) set " 
  where
    "\<And> i x e . (x, i) \<in> ll_valid_qi \<Longrightarrow> (x, L e i) \<in> ll_valid_q"
  | "\<And> x d e . (x, d) \<in> ll_valid_ql \<Longrightarrow> (x, LLab e d) \<in> ll_valid_q"
  | "\<And> x d e s . (x, d, s) \<in> ll_valid_qj \<Longrightarrow> (x, LJmp e d s) \<in> ll_valid_q"
  | "\<And> x d e s . (x, d, s) \<in> ll_valid_qji \<Longrightarrow> (x, LJmpI e d s) \<in> ll_valid_q"
  | "\<And> n l n' e . ((n, n'), l) \<in> ll_validl_q \<Longrightarrow> ((n, n'), (LSeq e l)) \<in> ll_valid_q"
  | "\<And> n . ((n,n), []) \<in> ll_validl_q"  
  | "\<And> n h n' t n'' .
     ((n,n'), h) \<in> ll_valid_q \<Longrightarrow>
     ((n',n''), t) \<in> ll_validl_q \<Longrightarrow>
     ((n,n''), ((n,n'), h) # t) \<in> ll_validl_q"

(* TODO: define "bump" to move the given ll to the "right" in the buffer by X bytes
   in order for this to be useful, we will need to make our annotations
   parametric in the size (? - maybe we don't use this until the
   very end so it will work out)
*)
(* this should operate on a (qan * (ll list))?
   otherwise there is and repacking we have to do... *)    
fun ll_bump :: "nat \<Rightarrow> ('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll \<Rightarrow>
                       ('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll" where
    "ll_bump b ((n,n'), l) = ((n+b,n'+b), (case l of
                                           LSeq e ls \<Rightarrow> LSeq e (map (ll_bump b) ls)
                                           | _ \<Rightarrow>  l))"
    
(* this is also suffering from the same problem as the validity predicate itself had.
   we need a case for each constructor. *)
(* to fix this we should have a better induction rule for validity that breaks out cases,
   maybe defining all of them as a mutually inductive set will work... *)
(* I am unsure if this is actually necessary though as both rules work individually *)
    
lemma ll_bump_valid [rule_format]:
  "((x, (t :: ('lix, 'llx, 'ljx, 'ljix, 'llx, 'ptx, 'pnx) llt)) \<in> ll_valid_q \<longrightarrow> (! b . ((ll_bump b (x,t))) \<in> ll_valid_q)) \<and>
   (((m,m'), (l :: ('lix, 'llx, 'ljx, 'ljix, 'llx, 'ptx, 'pnx) ll list)) \<in> ll_validl_q \<longrightarrow> (! b' .((m+b', m'+b'), map (ll_bump b') l) \<in> ll_validl_q))"
proof(induction rule: ll_valid_q_ll_validl_q.induct) 
  case 1 thus ?case by (auto simp add: ll_valid_q_ll_validl_q.intros) next
  case 2 thus ?case by (auto simp add: ll_valid_q_ll_validl_q.intros) next
  case 3 thus ?case by (auto simp add: ll_valid_q_ll_validl_q.intros) next
  case 4 thus ?case by (auto simp add: ll_valid_q_ll_validl_q.intros) next
  case (5 n l n' e) thus ?case by (auto simp add:ll_valid_q_ll_validl_q.intros) next
  case 6 thus ?case by (auto simp add:ll_valid_q_ll_validl_q.intros) next
  case (7 n h n' t n'') thus ?case
    apply(clarsimp)
    apply(drule_tac x = "b'" in spec)
    apply(drule_tac x = "b'" in spec)
    apply(rule ll_valid_q_ll_validl_q.intros(7), auto)
    done qed

  
fun ll1_size :: "ll1 \<Rightarrow> nat" and
    ll1_size_seq :: "ll1 list \<Rightarrow> nat" where
    "ll1_size (ll1.L inst) = nat (inst_size inst)"
  | "ll1_size (ll1.LLab idx) = 1"
  | "ll1_size (ll1.LJmp idx) = 2"
  | "ll1_size (ll1.LJmpI idx) = 2"
  | "ll1_size (ll1.LSeq ls) = ll1_size_seq ls"
  | "ll1_size_seq [] = 0"
  | "ll1_size_seq (h # t) = ll1_size h + ll1_size_seq t"
  
(* first pass, storing sizes *)
fun ll_phase1 :: "ll1 \<Rightarrow> nat \<Rightarrow> (ll2 * nat)" and
    ll_phase1_seq :: "ll1 list \<Rightarrow> nat \<Rightarrow> (ll2 list * nat)"
  where
  "ll_phase1 (ll1.L inst) i = (((i, i + nat (inst_size inst)), L () inst ), i + nat (inst_size inst))"
| "ll_phase1 (ll1.LLab idx) i = (((i, i+1), LLab () idx ), 1+i)" (* labels take 1 byte *)
| "ll_phase1 (ll1.LJmp idx) i = (((i, 2 + i), LJmp () idx 0), 2 + i)" (* jumps take at least 2 bytes (jump plus push) *)
| "ll_phase1 (ll1.LJmpI idx) i = (((i, 2 + i), LJmpI () idx 0), 2 + i)"
| "ll_phase1 (ll1.LSeq ls) i =
   (let (ls', i') = ll_phase1_seq ls i in
   (((i, i'), LSeq () ls'), i'))"
| "ll_phase1_seq [] i = ([], i)"
| "ll_phase1_seq (h # t) i =
   (let (h', i') = ll_phase1 h i in
    (let (t', i'') = ll_phase1_seq t i' in
      (h' # t', i'')))"
  
definition ll_pass1 :: "ll1 \<Rightarrow> ll2" where
  "ll_pass1 l = fst (ll_phase1 l 0)"

lemma ll_phase1_correct :
  "(ll1_valid x \<longrightarrow> (! i . ? x2 . ? i' . ll_phase1 x i = (((i, i'), x2), i') \<and> ((i, i'), x2) \<in> ll_valid_q)) \<and>
   (list_all ll1_valid xs \<longrightarrow>
    (! j . ? xs2 . ? j' . ll_phase1_seq xs j = (xs2, j') \<and> ((j,j'),xs2) \<in> ll_validl_q))"
proof(induction rule:my_ll1_induct)
  case (1 i) thus ?case by (auto simp add:ll_valid_q.simps) next
  case (2 idx) thus ?case by (auto simp add:ll_valid_q.simps) next
  case (3 idx) thus ?case 
    by (auto simp add:ll_valid_q.simps) next
  case (4 idx) thus ?case by (auto simp add:ll_valid_q.simps) next
  case (5 l) thus ?case
    apply(clarsimp)
    apply(case_tac "ll_phase1_seq l i", clarsimp)
    apply(drule_tac x = "i" in spec)
    apply (auto simp add:ll_valid_q.simps)
    done  next
  case (6) thus ?case using ll_valid_q_ll_validl_q.intros(6) by auto next
  case(7 t l) thus ?case 
    apply(clarsimp)
    apply(case_tac "ll_phase1 t j", clarsimp)
    apply(rename_tac "b'")
    apply(case_tac "ll_phase1_seq l b'", clarsimp)
    apply(drule_tac x = "j" in spec)
    apply(clarsimp)
    apply(drule_tac x = "b" in spec)
    apply(clarsimp)
    apply(rule ll_valid_q_ll_validl_q.intros(7), auto)
    done
qed
  
value "ll_pass1 (ll1.LSeq [ll1.LLab 0, ll1.L (Arith ADD)])"
  
value "(inst_size (Arith ADD))"


(* this one uses set instead of get. hopefully this isn't a problem. *)
(* ll3'_descend is the one I am using right now &*)
inductive_set ll_descend :: "(('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll * ('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll * nat) set"
  where
    "\<And> n n' e ls t .
       ((n, n'), LSeq e ls) \<in> ll_valid_q \<Longrightarrow>
       t \<in> set ls \<Longrightarrow>
       (((n,n'), LSeq e ls), t, 1) \<in> ll_descend"    
  | "\<And> t t' n t'' n' .
       (t, t', n) \<in> ll_descend \<Longrightarrow>
       (t', t'', n') \<in> ll_descend \<Longrightarrow>
       (t, t'', n + n') \<in> ll_descend"

type_synonym childpath = "nat list"

(* TODO: need a validity premise? for step case? *)
(* TODO: should we reverse the list *)
inductive_set ll3'_descend :: "(('lix, 'ljx, 'ljix, 'ptx, 'pnx) ll3' * ('lix, 'ljx, 'ljix, 'ptx, 'pnx) ll3' * childpath) set"
  where
    "\<And> q e ls t .
       c < length ls \<Longrightarrow>
       List.nth ls c = t \<Longrightarrow>
       ((q, LSeq e ls), t, [c]) \<in> ll3'_descend"    
  | "\<And> t t' n t'' n' .
       (t, t', n) \<in> ll3'_descend \<Longrightarrow>
       (t', t'', n') \<in> ll3'_descend \<Longrightarrow>
       (t, t'', n @ n') \<in> ll3'_descend"
    
definition ll_valid_q3 :: "ll3 set" where
  "ll_valid_q3 = ll_valid_q"
  
definition ll_validl_q3 :: "(qan * ll3 list) set" where
  "ll_validl_q3 = ll_validl_q"
  
(*definition ll_valid_q3' :: "('lix, 'llx, 'ljx, 'ljix, nat list, 'ptx, 'pnx) ll set" where
  "ll_valid_q3' = ll_valid_q"*)
definition ll_valid_q3' :: "('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll set" where
  "ll_valid_q3' = {}"
  
definition ll_validl_q3' :: "(qan * (('lix, 'llx, 'ljx, 'ljix, nat list, 'ptx, 'pnx) ll list)) set" where
  "ll_validl_q3' = ll_validl_q"

definition ll_descend3' :: "(('lix, 'llx, 'ljx, 'ljix, nat list, 'ptx, 'pnx) ll * ('lix, 'llx, 'ljx, 'ljix, nat list, 'ptx, 'pnx) ll * nat) set" where
  "ll_descend3' = ll_descend"

(* Q: do we need to winnow this down to an ll3' set?
   might make this easier to work with, since then we can rely on additional data
   from the other annotations
 *)

(* NB this is the notion of validity for ll3 
that I am using right now*)
inductive_set ll_valid3' :: "('lix, 'ljx, 'ljix, 'ptx, 'pnx) ll3' set" where
"\<And> i e x. (x, i) \<in> ll_valid_qi \<Longrightarrow>
               (x, L e i) \<in> ll_valid3'"
 | "\<And> x d. (x, d) \<in> ll_valid_ql \<Longrightarrow>
             (x, LLab True d) \<in> ll_valid3'"
  | "\<And> e x d s. (x, d, s) \<in> ll_valid_qj \<Longrightarrow>
                (x, (LJmp e d s)) \<in> ll_valid3'"
  | "\<And> e x d s. (x, d, s) \<in> ll_valid_qji \<Longrightarrow>
               (x, (LJmpI e d s)) \<in> ll_valid3'"


  | "\<And> x l e  . (x, l) \<in> ll_validl_q \<Longrightarrow>
                 (z \<in> set l \<Longrightarrow> z \<in> ll_valid3') \<Longrightarrow>
                 (\<not> (\<exists> k y e' . ((x, LSeq e l), (y, LLab e' (List.length k - 1)), k) \<in> ll3'_descend)) \<Longrightarrow>
                 (x, (LSeq [] l)) \<in> ll_valid3'"

(* old version that assumed labels were true
*)
(*
  | "\<And> x l e  z k y. (x, l) \<in> ll_validl_q \<Longrightarrow>
                (z \<in> set l \<Longrightarrow> z \<in> ll_valid3') \<Longrightarrow>
                (((x, LSeq e l), (y, LLab True (List.length k - 1)), k) \<in> ll3'_descend) \<Longrightarrow>
                (\<And> k' y' . (((x, LSeq e l), (y, LLab True (List.length k' - 1)), k') \<in> ll3'_descend) \<Longrightarrow> k = e \<and> k = k' \<and> y = y') \<Longrightarrow>
                (x, LSeq k l) \<in> ll_valid3'"
*)
  | "\<And> x l e  z k y. (x, l) \<in> ll_validl_q \<Longrightarrow>
                (z \<in> set l \<Longrightarrow> z \<in> ll_valid3') \<Longrightarrow>
                (((x, LSeq e l), (y, LLab True (List.length k - 1)), k) \<in> ll3'_descend) \<Longrightarrow>
                (\<And> k' y' b . (((x, LSeq e l), (y, LLab b (List.length k' - 1)), k') \<in> ll3'_descend) \<Longrightarrow> b = true \<and> k = e \<and> k = k' \<and> y = y') \<Longrightarrow>
                (x, LSeq k l) \<in> ll_valid3'"
(* old version of ll3 validity, may have bugs *)
(*
inductive_set ll_valid3 :: "('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll set"
  where
    "\<And> i e x. (x, i) \<in> ll_valid_qi \<Longrightarrow>
               (x, L e i) \<in> ll_valid3"
  | "\<And> e x d. (x, d) \<in> ll_valid_ql \<Longrightarrow>
             (x, LLab e d) \<in> ll_valid3" 
  | "\<And> e x d s. (x, d, s) \<in> ll_valid_qj \<Longrightarrow>
                (x, (LJmp e d s)) \<in> ll_valid3"
  | "\<And> e x d s. (x, d, s) \<in> ll_valid_qji \<Longrightarrow>
               (x, (LJmpI e d s)) \<in> ll_valid3"
  | "\<And> x l e e' . (x, l) \<in> ll_validl_q \<Longrightarrow>
                 (z \<in> set l \<Longrightarrow> z \<in> ll_valid3) \<Longrightarrow>
                 (\<not> (\<exists> k y . ((x, LSeq e l), (y, LLab e' k), k) \<in> ll_descend)) \<Longrightarrow>
                 (x, (LSeq e l)) \<in> ll_valid3"
  | "\<And> x l e e' z. (x, l) \<in> ll_validl_q \<Longrightarrow>
                (z \<in> set l \<Longrightarrow> z \<in> ll_valid3) \<Longrightarrow>
                (\<exists>! k . \<exists>! y . (((x, LSeq e l), (y, LLab e' k), k) \<in> ll_descend)) \<Longrightarrow>
                (x, LSeq e l) \<in> ll_valid3"
    *)


(* dump an l2 to l3, marking all labels as unconsumed *)
fun ll3_init :: "ll2 \<Rightarrow> ll3" where
  "ll3_init (x, L e i) = (x, L e i)"
| "ll3_init (x, LLab e idx) = (x, LLab False idx)"
| "ll3_init (x, LJmp e idx s) = (x, LJmp e idx s)"
| "ll3_init (x, LJmpI e idx s) = (x, LJmpI e idx s)"
| "ll3_init (x, LSeq e ls) = 
   (x, LSeq [] (map ll3_init ls))"
(*
\<and>
 
*)


lemma ll3_init_noquant :
"(fst (ll3_init l) = fst l) \<and>
 (List.map (\<lambda> t . fst (ll3_init t)) ls = List.map fst ls)"
  apply(induction rule:my_ll_induct, auto)
  done

(* step one: prove that ll3_init does not touch qan's
   maaybe this could be done using parametricity? *)

lemma ll3_init_pres :
"((q, l2) \<in> ll_valid_q \<longrightarrow> (ll3_init (q, l2)) \<in> ll_valid_q)\<and>
 (((x,y), ls) \<in> ll_validl_q \<longrightarrow> ((x,y), (map ll3_init ls)) \<in> ll_validl_q)"
proof(induction rule: ll_valid_q_ll_validl_q.induct)
  case 1 thus ?case by (auto simp add:ll_valid_q_ll_validl_q.intros) next
  case 2 thus ?case by (auto simp add:ll_valid_q_ll_validl_q.intros) next
  case 3 thus ?case by (auto simp add:ll_valid_q_ll_validl_q.intros) next
  case 4 thus ?case by (auto simp add:ll_valid_q_ll_validl_q.intros) next
  case 5 thus ?case by (auto simp add:ll_valid_q_ll_validl_q.intros) next
  case 6 thus ?case by (auto simp add:ll_valid_q_ll_validl_q.intros) next
  case (7 n h n' t n'') thus ?case using ll3_init_noquant[of "((n,n'),h)" "[]"]
    apply(auto)
    apply(case_tac "ll3_init ((n,n'),h)", clarsimp)
    apply(rule ll_valid_q_ll_validl_q.intros(7), auto)
    done
qed

value "ll3_init (ll_pass1 (ll1.LSeq [ll1.LLab 0])) :: ll3"

(*
datatype consume_label_result =
  CFound "ll3 list" "childpath"
  | CNone "ll3 list"
  | CFail
*)

(* All of these predicates might not be needed. *)
(* this one is not the one we are using for consumes *)
(* it is worth a shot though, directly encoding the reverse as an inductive seems hard *)
inductive cp_less :: "childpath \<Rightarrow> childpath \<Rightarrow> bool" where
"\<And> n t . cp_less [] (n#t)"
| "\<And> n n' t t' . n < n' \<Longrightarrow> cp_less (n#t) (n'#t')"
| "\<And> n t t' . cp_less t t' \<Longrightarrow> cp_less (n#t) (n#t')"


(* i'm worried this is not correctly capturing preorder traversal
   it seems like it might be DFS instead...*)
inductive cp_rev_less' :: "childpath \<Rightarrow> childpath \<Rightarrow> bool" where
"\<And> n t . cp_rev_less' [] (n#t)"
| "\<And> n n' t . n < n' \<Longrightarrow> cp_rev_less' (n#t) (n'#t)"
| "\<And> t t' n n' . cp_rev_less' t t' \<Longrightarrow> cp_rev_less' (n#t) (n'#t')"

(* i think this is what we want 
   this isn't really inductive though *)
(*
inductive cp_rev_less :: "childpath \<Rightarrow> childpath \<Rightarrow> bool" where
"\<And> (n::nat) (t::childpath) . cp_rev_less [] (n#t)"
| "\<And> n n' p p' t . n < n' \<Longrightarrow> cp_rev_less (p@(n#t)) (p'@(n'#t))"
*)

inductive cp_rev_less :: "childpath \<Rightarrow> childpath \<Rightarrow> bool" where
"\<And> (n::nat) (t::childpath) . cp_rev_less [] (t@[n])"
| "\<And> n n' t t' . n < n' \<Longrightarrow> cp_rev_less (t@[n]) (t'@[n'])"
| "\<And> (t :: childpath) (t' :: childpath) l. cp_rev_less t t' \<Longrightarrow> cp_rev_less (t@l) (t'@l)"


(* we need to capture incrementing a childpath *)
fun cp_next :: "childpath \<Rightarrow> childpath" where
"cp_next [] = []"
| "cp_next (h#t) = (Suc h)#t"



(* this should be "plus anything"? *)
lemma cp_rev_less'_suc1 :
"cp_rev_less' k p \<Longrightarrow>
  (! n t . k = Suc n # t \<longrightarrow>
   cp_rev_less' (n#t) p)"
  apply(induction rule: cp_rev_less'.induct)
    apply(auto simp add:cp_rev_less'.intros)
  done

lemma cp_rev_less_sing' :
"n < n' \<Longrightarrow> cp_rev_less ([]@[n]) ([]@[n'])"
  apply(rule_tac cp_rev_less.intros) apply(auto)
  done

lemma cp_rev_less_sing :
"n < n' \<Longrightarrow> cp_rev_less [n] [n']"
  apply(insert cp_rev_less_sing') apply(auto)
  done

lemma cp_rev_less_least :
"cp_rev_less p k \<Longrightarrow> k \<noteq> []"
  apply(induction rule:cp_rev_less.induct)
    apply(auto)
  done
(* lots of aborted proofs about these definitions follow.
i'm abandoning them for now *)
(*
lemma cp_rev_less_least2 :
"cp_rev_less "
*)
(*
lemma cp_rev_less_last :
"cp_rev_less p1 p2 \<Longrightarrow>
  (! pre1 x1 . p1 = pre1@[x1] \<longrightarrow>
   (! pre2 x2 . p2 = pre2@[x2] \<longrightarrow>
      x1 \<le> x2))"
  apply(induction rule: cp_rev_less.induct) apply(auto)
  apply(case_tac l, auto)
*)
(*
lemma cp_rev_less_chip :
"(! p2 . cp_rev_less p1 p2 \<longrightarrow>
  (! h . cp_rev_less (h#p1) p2))"
  apply(induction p1, auto)
  apply(case_tac p2, auto)
       apply(drule_tac [1] cp_rev_less_least, auto)
    apply(rule_tac [1] cp_rev_less.intros)
  apply(drule_tac [1] cp_rev_less.cases) apply(auto)
  apply(drule_tac [1] cp_rev_less.cases) apply(auto)
    apply(rule_tac [1] cp_rev_less.intros) apply(auto)
*)  

lemma cp_less_least :
"cp_less p k \<Longrightarrow> k \<noteq> []"
  apply(induction rule:cp_less.induct)
    apply(auto)
  done
type_synonym consume_label_result = "(ll3 list * childpath) option"


(* TODO - proof plan
   first, we need to prove that the outputs of consume_label and then assign_label are qan-valid
   then, we need to have a "strong induction" theorem describing the results of consume_label
   under the conditions where we actually run it (if we haven't found a descendent yet for
   lesser paths  
   then we should have the additional facts we need to prove full ll3 validity for assign_labels
*)

(* this prevents multiple locations for the same label name
   because it will only "consume" one label per name
   and then it will fail later on the other one *)
(* modify this to pass around root?
   modify this to take a node instead of a node list? *)
(* subroutine for assign_label, marks label as consumed *)
fun ll3_consume_label :: "childpath \<Rightarrow> nat  \<Rightarrow> ll3 list \<Rightarrow> consume_label_result" where
 "ll3_consume_label p n [] = Some ([], [])"
(* Actually consume the label, but it must not be consumed yet *)
| "ll3_consume_label p n ((x, LLab b idx) # ls) = 
   (if idx = length p then (if b = False then Some ((x, LLab True idx)#ls, n#p) else None)
   else case (ll3_consume_label p (n+1) ls) of
    Some (ls', p') \<Rightarrow> Some ((x, LLab b idx)#ls', p')
   | None \<Rightarrow> None)"

| "ll3_consume_label p n ((x, LSeq e lsdec) # ls) =
   (case ll3_consume_label (n#p) 0 lsdec of
    Some (lsdec', []) \<Rightarrow> (case ll3_consume_label p (n+1) ls of
      Some (ls', p') \<Rightarrow> Some (((x, LSeq e lsdec') # ls'), p')
      | None \<Rightarrow> None)
    | Some (lsdec', p') \<Rightarrow> Some (((x, LSeq e lsdec') # ls), p')
    | None \<Rightarrow> None)"
  
| "ll3_consume_label p n (T#ls) =
   (case ll3_consume_label p (n+1) ls of
    Some (ls', p') \<Rightarrow> Some ((T#ls'), p')
    | None \<Rightarrow> None)"

(* we need to make this work with ll_induct, though *)
(*lemma ll3_consume_label_correct :
""*)

fun numnodes :: "('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll \<Rightarrow> nat" and
    numnodes_l :: "('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll list \<Rightarrow> nat" where
"numnodes (_, LSeq _ xs) = 1 + numnodes_l xs"
| "numnodes _ = 1"
| "numnodes_l [] = 1"
| "numnodes_l (h#t) = numnodes h + numnodes_l t"


(* should we shove the quantifiers into the Some case? *)
(* Another option, return a bool representing failure ? *)
(* no, i think we can just add a thing to the first case about
   how the numnodes of the result is less than original *)
(* we need another side for l, regarding what happens if l's head is an lseq *)
lemma ll3_consume_label_numnodes [rule_format] :
"
  (! e l l' p p' n q . t = (q, LSeq e l) \<longrightarrow> ll3_consume_label p n l = Some (l',p') \<longrightarrow> numnodes t \<ge> numnodes_l l' + 1) \<and>
  (! l' p p' n . ll3_consume_label p n l = Some (l', p') \<longrightarrow> numnodes_l l \<ge> numnodes_l l')"

proof(induction rule:my_ll_induct)
  case 1 thus ?case by auto next
  case 2 thus ?case by auto next
  case 3 thus ?case by auto next
  case 4 thus ?case by auto next
  case (5 q e l) thus ?case by auto next
  case 6 thus ?case by auto next
  case (7 h l) thus ?case
    apply(case_tac h)
    apply(clarsimp)
    apply(case_tac ba, clarsimp)
         apply(case_tac[1] "ll3_consume_label p (Suc n) l", clarsimp, auto)
         apply(blast)
        apply(case_tac[1] "x22 = length p", clarsimp)
         apply(case_tac[1] "x21", clarsimp, auto)
    apply(case_tac[1] "ll3_consume_label p (Suc n) l", clarsimp, auto, blast)
    apply(case_tac[1] "ll3_consume_label p (Suc n) l", clarsimp, auto, blast)
      apply(case_tac[1] "ll3_consume_label p (Suc n) l", clarsimp, auto, blast)
     apply(case_tac[1] "ll3_consume_label (n#p) 0 x52", clarsimp, auto)
     apply(case_tac[1] "ba", clarsimp, auto)
      apply(case_tac[1] "ll3_consume_label p (Suc n) l", clarsimp, auto)
    apply(drule_tac [1] x = aa in spec) 
    apply(drule_tac [1] x = ab in spec)
    
    apply(auto)
    done
qed

lemma ll3_consume_label_numnodes1 : "ll3_consume_label p n l = Some (l', p') \<Longrightarrow> numnodes_l l \<ge> numnodes_l l'"
  apply(insert ll3_consume_label_numnodes)
  apply(blast)
  done

(* finish this lemma statement, we may need a "strong" hypothesis
   about failing to run on previous steps, and re-stitching results *)


lemma ll3_consume_label_qvalid' :
"((q, t) \<in> ll_valid_q \<longrightarrow> (! ls e . t = (LSeq e ls) \<longrightarrow> (! p p' n ls' . ll3_consume_label p n ls = Some (ls', p') \<longrightarrow> (q, LSeq e ls') \<in> ll_valid_q)))
\<and> (((x,x'), ls) \<in> ll_validl_q \<longrightarrow> (! p p' n ls' . ll3_consume_label p n ls = Some (ls', p') \<longrightarrow> ((x,x'), ls') \<in> ll_validl_q ))"
  apply(induction rule:ll_valid_q_ll_validl_q.induct, auto simp add:ll_valid_q_ll_validl_q.intros)
  apply(case_tac h, auto)
      apply(case_tac[1] "ll3_consume_label p (Suc na) t", auto simp add:ll_valid_q_ll_validl_q.intros)
     apply(case_tac [1] "x22 = length p", clarsimp)
      apply(case_tac [1] "\<not>x21", clarsimp, auto)
      apply(rule_tac [1] "ll_valid_q_ll_validl_q.intros", auto)
      apply(erule_tac [1] "ll_valid_q.cases", auto simp add:ll_valid_q_ll_validl_q.intros)
     apply(case_tac [1] "ll3_consume_label p (Suc na) t", auto)
     apply(rule_tac [1] "ll_valid_q_ll_validl_q.intros", auto)
    apply(case_tac [1] "ll3_consume_label p (Suc na) t", auto simp add:ll_valid_q_ll_validl_q.intros)
   apply(case_tac [1] "ll3_consume_label p (Suc na) t", auto simp add:ll_valid_q_ll_validl_q.intros)
  apply(case_tac "ll3_consume_label (na # p) 0 x52", auto)
  apply(case_tac b, auto)
   apply(case_tac [1] "ll3_consume_label p (Suc na) t", auto simp add:ll_valid_q_ll_validl_q.intros)
  done

lemma ll3_consume_label_qvalid :
"(q,ls) \<in> ll_validl_q \<Longrightarrow> ll3_consume_label p n ls = Some (ls', p') \<Longrightarrow> (q, ls') \<in> ll_validl_q"
  apply(insert ll3_consume_label_qvalid')
  apply(case_tac q)
  apply(auto)
  done

lemma ll3_consume_label_hdq' :
  "(! e q qh h ts. t = (q, LSeq e ((qh,h)#ts)) \<longrightarrow>
      (! p n l' p'. ll3_consume_label p n ((qh,h)#ts) = Some (l',p') \<longrightarrow> 
     (? qh' h' ts' . l' = ((qh',h' )#ts') \<and> qh = qh'))) 
\<and>
  (! qh h ts . l = ((qh,h)#ts) \<longrightarrow>
    (! p n l' p' . ll3_consume_label p n l = Some (l', p') \<longrightarrow> 
    (? qh' h' ts' . l' = ((qh',h' )#ts') \<and> qh = qh')))"

  apply(induction rule:my_ll_induct)
        apply(auto)
  apply(case_tac[1] h, auto)
          apply(case_tac[1] "ll3_consume_label p (Suc n) ts", auto)
         apply(case_tac [1] "x22 = length p", auto)
          apply(case_tac [1] "\<not>x21", auto)
          apply(case_tac[1] "ll3_consume_label p (Suc n) ts", auto)
         apply(case_tac[1] "ll3_consume_label p (Suc n) ts", auto)
          apply(case_tac[1] "ll3_consume_label p (Suc n) ts", auto)
       apply(case_tac [1] "ll3_consume_label (n # p) 0 x52", auto)
    apply(rename_tac [1] boo)
      apply(case_tac [1] boo, auto)
       apply(case_tac[1] "ll3_consume_label p (Suc n) ts", auto)

  apply(case_tac[1] h, auto)
          apply(case_tac[1] "ll3_consume_label p (Suc n) ts", auto)
         apply(case_tac [1] "x22 = length p", auto)
          apply(case_tac [1] "\<not>x21", auto)
          apply(case_tac[1] "ll3_consume_label p (Suc n) ts", auto)
         apply(case_tac[1] "ll3_consume_label p (Suc n) ts", auto)
          apply(case_tac[1] "ll3_consume_label p (Suc n) ts", auto)
       apply(case_tac [1] "ll3_consume_label (n # p) 0 x52", auto)
    apply(rename_tac [1] boo)
      apply(case_tac [1] boo, auto)
      apply(case_tac[1] "ll3_consume_label p (Suc n) ts", auto)

  apply(case_tac[1] h, auto)
          apply(case_tac[1] "ll3_consume_label p (Suc n) ts", auto)
         apply(case_tac [1] "x22 = length p", auto)
          apply(case_tac [1] "\<not>x21", auto)
          apply(case_tac[1] "ll3_consume_label p (Suc n) ts", auto)
         apply(case_tac[1] "ll3_consume_label p (Suc n) ts", auto)
          apply(case_tac[1] "ll3_consume_label p (Suc n) ts", auto)
       apply(case_tac [1] "ll3_consume_label (n # p) 0 x52", auto)
    apply(rename_tac [1] boo)
      apply(case_tac [1] boo, auto)
     apply(case_tac[1] "ll3_consume_label p (Suc n) ts", auto)

  apply(case_tac[1] h, auto)
          apply(case_tac[1] "ll3_consume_label p (Suc n) ts", auto)
         apply(case_tac [1] "x22 = length p", auto)
          apply(case_tac [1] "\<not>x21", auto)
          apply(case_tac[1] "ll3_consume_label p (Suc n) ts", auto)
         apply(case_tac[1] "ll3_consume_label p (Suc n) ts", auto)
          apply(case_tac[1] "ll3_consume_label p (Suc n) ts", auto)
       apply(case_tac [1] "ll3_consume_label (n # p) 0 x52", auto)
    apply(rename_tac [1] boo)
      apply(case_tac [1] boo, auto)
    apply(case_tac[1] "ll3_consume_label p (Suc n) ts", auto)

  apply(case_tac[1] h, auto)
          apply(case_tac[1] "ll3_consume_label p (Suc n) ts", auto)
         apply(case_tac [1] "x22 = length p", auto)
          apply(case_tac [1] "\<not>x21", auto)
          apply(case_tac[1] "ll3_consume_label p (Suc n) ts", auto)
         apply(case_tac[1] "ll3_consume_label p (Suc n) ts", auto)
          apply(case_tac[1] "ll3_consume_label p (Suc n) ts", auto)
       apply(case_tac [1] "ll3_consume_label (n # p) 0 x52", auto)
    apply(rename_tac [1] boo)
      apply(case_tac [1] boo, auto)
   apply(case_tac[1] "ll3_consume_label p (Suc n) ts", auto)

    apply(case_tac[1] h, auto)
      apply(case_tac[1] "ll3_consume_label p (Suc n) l", auto)
         apply(case_tac [1] "x22 = length p", auto)
          apply(case_tac [1] "\<not>x21", auto)
          apply(case_tac[1] "ll3_consume_label p (Suc n) l", auto)
         apply(case_tac[1] "ll3_consume_label p (Suc n) l", auto)
          apply(case_tac[1] "ll3_consume_label p (Suc n) l", auto)
  apply(case_tac [1] "ll3_consume_label (n # p) 0 x52", auto)
  apply(case_tac [1] b, auto)
          apply(case_tac[1] "ll3_consume_label p (Suc n) l", auto)
  done

lemma ll3_consume_label_hdq :
  "ll3_consume_label p n ((qh,h)#ts') = Some (l', p') \<Longrightarrow>
    (? qh' h' ts' . l' = ((qh',h' )#ts') \<and> qh = qh')"
  apply(insert ll3_consume_label_hdq'[of bunk "((qh, h) # ts')"])
  apply(auto)
  apply(drule_tac x = p in spec)
  apply(drule_tac x = p in spec)
  apply(drule_tac x = n in spec)
  apply(drule_tac x = n in spec)
  apply(auto)
  done

(* new idea: we need to take into account arbitrary number of consumes (?) *)
(* idea: we need to take into account the other premises *)
(* crucially we need to properly track where in the list the change happened as a childpath *)
(* this means we need to track only the suffix.
*)
(*
inductive_set ll3_consumes :: "(ll3 list * childpath set * ll3 list) set" where
"\<And> l . (l,{},l) \<in> ll3_consumes"
| "\<And> p n l l' . ll3_consume_label p n l = Some (l', []) \<Longrightarrow> (l,{},l') \<in> ll3_consumes"
| "\<And> p n l l' ph pt . ll3_consume_label p n l = Some (l', ph#pt) \<Longrightarrow> (l,{(ph#pt)}, l') \<in> ll3_consumes"
| "\<And> l s l' s' l'' . (l,s,l') \<in> ll3_consumes \<Longrightarrow> (l',s', l'') \<in> ll3_consumes \<Longrightarrow> (s \<inter> s' = {})  
     \<Longrightarrow> (l,s \<union> s',l'') \<in> ll3_consumes"
*)
(* we need to fix this so it appropriately adjusts for values of n and path *)
(*
inductive_set ll3_consumes :: "(ll3 list * childpath set * ll3 list) set" where
"\<And> l . (l,{},l) \<in> ll3_consumes"
| "\<And> p n l l' . ll3_consume_label p n l = Some (l', []) \<Longrightarrow> (l,{},l') \<in> ll3_consumes"
| "\<And> p n l l' k pp . ll3_consume_label p n l = Some (l', pp@(k#p)) \<Longrightarrow> (l,{pp@[k - n]}, l') \<in> ll3_consumes"
| "\<And> l s l' s' l'' . (l,s,l') \<in> ll3_consumes \<Longrightarrow> (l',s', l'') \<in> ll3_consumes \<Longrightarrow> (s \<inter> s' = {})  
     \<Longrightarrow> (l,s \<union> s',l'') \<in> ll3_consumes"
*)
(* Q: add "k \<ge> n" hypothesis or no? *)
(* this is the second most recent one *)
(*
inductive_set ll3_consumes :: "(ll3 list * childpath set * ll3 list) set" where
"\<And> l . (l,{},l) \<in> ll3_consumes"
| "\<And> p n l l' . ll3_consume_label p n l = Some (l', []) \<Longrightarrow> (l,{},l') \<in> ll3_consumes"
| "\<And> p n l l' k pp . ll3_consume_label p n l = Some (l', pp@(k#p))  \<Longrightarrow> (l,{pp@[k - n]}, l') \<in> ll3_consumes"
| "\<And> l s l' s' l'' . (l,s,l') \<in> ll3_consumes \<Longrightarrow>
      (l',s', l'') \<in> ll3_consumes \<Longrightarrow> 
      (l,s \<union> s',l'') \<in> ll3_consumes"
*)
(*
inductive_set ll3_consumes :: "(ll3 list * childpath set * ll3 list) set" where
"\<And> l . (l,{},l) \<in> ll3_consumes"
| "\<And> p n l l' . ll3_consume_label p n l = Some (l', []) \<Longrightarrow> (l,{},l') \<in> ll3_consumes"
| "\<And> p n l l' k pp . ll3_consume_label p n l = Some (l', pp@(k#p))  \<Longrightarrow> (l,{pp@(k - n)#p}, l') \<in> ll3_consumes"
| "\<And> l s l' s' l'' . (l,s,l') \<in> ll3_consumes \<Longrightarrow>
      (l',s', l'') \<in> ll3_consumes \<Longrightarrow> 
      (l,s \<union> s',l'') \<in> ll3_consumes"
*)

(* Q: should we still conflate different consumes on parent paths?  *)
(* Another option: store lists rather than sets, but make assertions about sets of childpath * nat *)
inductive_set ll3_consumes :: "(ll3 list * (childpath * nat) list * ll3 list) set" where
"\<And> l . (l,[],l) \<in> ll3_consumes"
| "\<And> p n l l' . ll3_consume_label p n l = Some (l', []) \<Longrightarrow> (l,[],l') \<in> ll3_consumes"
| "\<And> p n l l' k pp . ll3_consume_label p n l = Some (l', pp@(k#p))  \<Longrightarrow> (l,[(pp@[k - n], length p)], l') \<in> ll3_consumes"
| "\<And> l s l' s' l'' . (l,s,l') \<in> ll3_consumes \<Longrightarrow>
      (l',s', l'') \<in> ll3_consumes \<Longrightarrow> 
      (l,s @ s',l'') \<in> ll3_consumes"

lemma haslast' :
"l = [] \<or> (? fi la . l = fi@[la])"
proof(induction l)
  case Nil thus ?case by auto
  case (Cons h t) thus ?case
    apply(auto) 
    done qed


(* new idea: a version of consumes that uses a sorted list of childpath * nat *)
lemma ll3_consume_label_unch' :
"(! e l l' p n q. (t :: ll3) = (q, LSeq e l) \<longrightarrow> (ll3_consume_label p n l = Some(l', []) \<longrightarrow> l = l'))
\<and> (! p n ls' . ll3_consume_label p n ls = Some (ls', []) \<longrightarrow> ls = ls')"
  
  apply(induction rule:my_ll_induct)
        apply(auto)
  apply(case_tac ba, auto)
      apply(case_tac [1] "ll3_consume_label p (Suc n) l", auto)
     apply(case_tac [1] "x22 = length p", auto)
      apply(case_tac [1] "\<not>x21", auto)
     apply(case_tac [1] "ll3_consume_label p (Suc n) l", auto)
    apply(case_tac [1] "ll3_consume_label p (Suc n) l", auto)
   apply(case_tac [1] "ll3_consume_label p (Suc n) l", auto)
  apply(case_tac "ll3_consume_label (n#p) 0 x52", auto)
  apply(case_tac ba, auto)
  apply(case_tac "ll3_consume_label p (Suc n) l", auto)
  done

lemma ll3_consume_label_unch :
"\<And> p n ls ls' . ll3_consume_label p n ls = Some (ls', []) \<Longrightarrow> ls = ls'"
  apply(insert ll3_consume_label_unch')
  apply(blast)
  done

(*
New idea: either p' is nil, or
the path we return has p plus a prefix
this prefix will be greater than or equal
to [n] (that is, p is not less than [n]))
*)
(* new idea: rather than using "cp_rev_less", just say
"p' = nil
or p' = l@(n#p)
 "
*)
(*
lemma ll3_consume_label_char' [rule_format] :
"
  (! e l q . (t :: ll3) = (q, LSeq e l) \<longrightarrow> 
  (! l' p n p' . ll3_consume_label p n l = Some (l',p') \<longrightarrow> 
  (p' = [] \<or>
   p' = n#p \<or>
   (? pp . p' = pp@p \<and>
    cp_rev_less [n] pp))))
\<and>
  (! p n l' p' . ll3_consume_label p n (l :: ll3 list) = Some (l', p') \<longrightarrow>
  (p' = [] \<or>
   p' = n#p \<or>
   (? pp . p' = pp@p \<and>
    cp_rev_less [n] pp)))
"
*)
lemma ll3_consume_label_char' [rule_format] :
"
  (! e l q . (t :: ll3) = (q, LSeq e l) \<longrightarrow> 
  (! l' p n p' . ll3_consume_label p n l = Some (l',p') \<longrightarrow> 
  (p' = [] \<or>
   (? pp m .  p' = pp@(m#p) \<and> m \<ge> n))))
\<and>
  (! l' p n p' . ll3_consume_label p n (l :: ll3 list) = Some (l',p') \<longrightarrow> 
  (p' = [] \<or>
   (? pp m .  p' = pp@(m#p) \<and> m \<ge> n)))
"
proof(induction rule:my_ll_induct)
  case 1 thus ?case by auto next
  case 2 thus ?case by auto next
  case 3 thus ?case by auto next
  case 4 thus ?case by auto next
  case (5 q e l) thus ?case 
    apply(auto) done next
  case 6 thus ?case by auto next
  case (7 h l) thus ?case
    apply(case_tac h)
    apply(auto)
     apply(case_tac [1] ba, auto)
        apply(case_tac[1] "ll3_consume_label p (Suc n) l", auto) 
    apply(drule_tac[1] x = "aa" in spec) 
    apply(rotate_tac[1] 2)
          apply(drule_tac[1] x = p in spec)
        apply(drule_tac[1] x = "Suc n" in spec)
         apply(auto)

     apply(case_tac [1] "x22 = length p", auto)
      apply(case_tac [1] "\<not>x21", auto)
       apply(case_tac [1] "ll3_consume_label p (Suc n) l", auto)
    apply(drule_tac[1] x = "aa" in spec) 
    apply(rotate_tac[1] 2)
          apply(drule_tac[1] x = p in spec)
        apply(drule_tac[1] x = "Suc n" in spec)
       apply(auto)

       apply(case_tac [1] "ll3_consume_label p (Suc n) l", auto)
    apply(drule_tac[1] x = "aa" in spec) 
    apply(rotate_tac[1] 2)
          apply(drule_tac[1] x = p in spec)
        apply(drule_tac[1] x = "Suc n" in spec)
         apply(auto)

     apply(case_tac [1] "ll3_consume_label p (Suc n) l", auto)
    apply(drule_tac[1] x = "aa" in spec) 
    apply(rotate_tac[1] 2)
          apply(drule_tac[1] x = p in spec)
        apply(drule_tac[1] x = "Suc n" in spec)
         apply(auto)

    apply(case_tac "ll3_consume_label (n # p) 0
              x52") apply(auto)
    apply(case_tac ba, auto)
      apply(case_tac "ll3_consume_label p (Suc n) l", auto)
    apply(drule_tac ll3_consume_label_unch, auto)
    apply(thin_tac [1] " \<forall>l' p n p'.
          ll3_consume_label p n aa = Some (l', p') \<longrightarrow>
          p' = [] \<or> (\<exists>pp m. p' = pp @ m # p \<and> n \<le> m)")

     apply(drule_tac [1] x = ab in spec)
    apply(rotate_tac[1] 2)
          apply(drule_tac[1] x = p in spec)
        apply(drule_tac[1] x = "Suc n" in spec)
         apply(auto)

    apply(thin_tac [1] " \<forall>l' p n p'.
          ll3_consume_label p n l = Some (l', p') \<longrightarrow>
          p' = [] \<or> (\<exists>pp m. p' = pp @ m # p \<and> n \<le> m)")

     apply(drule_tac [1] x = "aa" in spec) 
    apply(rotate_tac [1] 2)
     apply(drule_tac [1] x = "n#p" in spec) 
     apply(drule_tac [1] x = 0 in spec) apply(auto)
    done
  
qed


lemma ll3_consume_label_char :
" ll3_consume_label p n (l :: ll3 list) = Some (l', p') \<Longrightarrow>
  (p' = [] \<or> (? pp m .  p' = pp@(m#p) \<and> m \<ge> n))"
  apply(insert ll3_consume_label_char') apply(blast)
  done


function (sequential) ll3_assign_label :: "ll3 \<Rightarrow> ll3 option" and
    ll3_assign_label_list :: "ll3 list \<Rightarrow> ll3 list option" where
  "ll3_assign_label (x, LSeq e ls) =
   (case (ll3_consume_label [] 0 ls) of
    Some (ls', p) \<Rightarrow> (case ll3_assign_label_list ls' of
      Some ls'' \<Rightarrow> Some (x, LSeq (rev p) ls'')
      | None \<Rightarrow> None)
   | None \<Rightarrow> None)"
(* unconsumed labels are an error *)
| "ll3_assign_label (x, LLab False idx) = None"
| "ll3_assign_label T = Some T"

| "ll3_assign_label_list [] = Some []"
| "ll3_assign_label_list (h#t) = 
   (case ll3_assign_label h of
    Some h' \<Rightarrow> (case ll3_assign_label_list t of
                Some t' \<Rightarrow> Some (h'#t')
                | None \<Rightarrow> None)
   | None \<Rightarrow> None)"
  by pat_completeness auto

termination 
  apply(relation "measure (\<lambda> x . case x of Inl t \<Rightarrow> numnodes t | Inr l \<Rightarrow> numnodes_l l)")
     apply(clarsimp)
    apply(auto)
    apply(induct_tac [2] "t", auto)
  apply(subgoal_tac "numnodes_l a \<le> numnodes_l ls", auto)
   apply(rule ll3_consume_label_numnodes1, auto)
  apply(case_tac ba, auto)
  done



(* lemma: "unch" for assign_label*)
lemma ll3_assign_label_unch' :
"(! q' t' . ll3_assign_label t = Some (q', t') \<longrightarrow> fst t = q') \<and>
 (! l' . ll3_assign_label_list l = Some l' \<longrightarrow> map fst l = map fst l')"
  apply(induction rule:my_ll_induct, auto)
      apply(case_tac [1] e, auto)
     apply(case_tac [1] e, auto)
    apply(case_tac[1] "ll3_consume_label [] 0 l", auto)
  apply(rename_tac abo) (* W  T F *)
    apply(case_tac[1] "ll3_assign_label_list ab", clarsimp)
  apply(auto)
   apply(case_tac [1] "ll3_consume_label [] 0 l", auto)
   apply(rename_tac abco)
   apply(case_tac "ll3_assign_label_list ab", auto)
  apply(case_tac "ll3_assign_label ((a,b), ba)", auto)
  apply(case_tac "ll3_assign_label_list l", auto)
  done

lemma ll3_assign_label_unch1 :
"ll3_assign_label (q,t) = Some (q', t') \<Longrightarrow> q = q'"
  apply(case_tac q, auto)
  apply(case_tac q', auto)
   apply(insert ll3_assign_label_unch')
   apply(auto)
   apply(blast)
  apply(blast)
  done

lemma ll3_assign_label_unch2 :
"ll3_assign_label_list ls = Some ls' \<Longrightarrow> map fst ls = map fst ls'"
  apply(insert ll3_assign_label_unch')
  apply(auto)
  done

(*
lemma ll3_consume_label_nofiddle :
"
("(! e l l' p n q. (t :: ll3) = (q, LSeq e l) \<longrightarrow> (ll3_consume_label p n l = Some(l', []) \<longrightarrow> l = l'))
\<and> (! p n ls' . ll3_consume_label p n ls = Some (ls', []) \<longrightarrow> ls = ls')")
\<and>
()
"
*)

(* my the inductive hypothesis is not right, maybe it needs to be strengthened
   in the list case. also I'm skeptical about this OR... *)
(* we need to revise the second clause along these lines *)
(* restate: if EITHER assigning the label immediately works yielding q''
   OR consuming the label and then assigning it works yielding q''
   THEN ll_valid_q holds on the result *)
(* I need to add in label consumption to the chain of the second case, it's not there now *)

(* We can state this more succinctly, because we are doing rule induction on premise. *)
(* Q: do we need to generalize over possible annotation changes? *)
(* TODO: this is still not quite right... we need to
   we need a "rest of ll3 assign label" as things stand we are basically trying to apply
   assign_label twice.
*)
(* our list case is subtly wrong,
   we need to be handling all recursive calls on sub cases.
   in practice what this means is that we need to 
   - handle the case where the head of the list is a Seq node?
*)

(* we need 2 lemmas here:
  1: if consuming and then assigning a label is q-valid, assigning the label must
     be valid under the same qan
  2: if assigning a label is valid, and consuming the label on the original list
     is also valid, then assigning the consumed label is valid under the same qan *)

(* Idea: doing consume_label can't make assign_labels at the root true
   and it can't make assign_labels at the root false *)
(*aeaeae
lemma ll3_assign_label_consume_label2' :
"((q, (t :: ll3t)) \<in> ll_valid_q \<longrightarrow>
  (! e l . t = LSeq e l \<longrightarrow> (! p n l' p' . ll3_consume_label p n l = Some (l', p') \<longrightarrow>
  
)
\<and>
()
"
*)

(*
lemma ll3_consume_label_prefix :
"(! q e l . (t::ll3) = (q, LSeq e l) \<longrightarrow> 
   (! p n l' p'. (ll3_consume_label p n l = Some (l', p')) \<longrightarrow> 
    (p' = [] \<or> (? pp . p' = pp @ p))))
\<and>
((! p n l' p'. (ll3_consume_label p n (l :: ll3 list) = Some (l', p')) \<longrightarrow>
    (p' = [] \<or> (? pp . p' = pp @ p))))
"
  apply(induction rule:my_ll_induct, auto)
  apply(case_tac ba, auto)
      apply(case_tac " ll3_consume_label p (Suc n) l", auto) apply(blast)
     apply(case_tac "x22 = length p", auto)
      apply(case_tac "\<not> x21", auto)  apply(drule_tac[1] x = 
      apply(case_tac " ll3_consume_label p (Suc n) l", auto) apply(blast)
      apply(case_tac " ll3_consume_label p (Suc n) l", auto) apply(blast)
      apply(case_tac " ll3_consume_label p (Suc n) l", auto) apply(blast)
  apply(case_tac "ll3_consume_label (n # p) 0 x52", auto)
  apply(case_tac ba, auto)
      apply(case_tac " ll3_consume_label p (Suc n) l", auto) apply(blast)
  apply(case_tac x52, auto)
  apply(case_tac ba, auto)
      apply(case_tac " ll3_consume_label (n # p) (Suc 0) lista", auto) 
*)
(*
lemma ll3_consume_label_diff :

"
(! e l . (t :: ll3) = (q, LSeq e l) \<longrightarrow> 
   ( ! p n l' ph pt. ll3_consume_label p n l = Some(l', (ph#pt)) \<longrightarrow> 
    (! p' n' l'' . ll3_consume_label p' n' l' = Some (l'', (ph'#pt')) \<longrightarrow>
        
     l'))
\<and> (! p n ls' . ll3_consume_label p n ls = Some (ls', (ph#pt)) \<longrightarrow> ls = ls')
"
*)

lemma ll3_consume_label_length :
"(! q e l . (t::ll3) = (q, LSeq e l) \<longrightarrow> 
   (! p n l' p'. (ll3_consume_label p n l = Some (l', p')) \<longrightarrow> length l = length l'))
\<and>
((! p n l' p'. (ll3_consume_label p n (l :: ll3 list) = Some (l', p')) \<longrightarrow> length l = length l'))
"
proof(induction rule:my_ll_induct)
  case 1 thus ?case by auto next
  case 2 thus ?case by auto next
  case 3 thus ?case by auto next
  case 4 thus ?case by auto next
  case (5 q e l) thus ?case by auto next
  case 6 thus ?case 
    apply(auto)
    done
  case (7 h l) thus ?case 
    apply(auto)
     apply(case_tac h, auto)
    apply(case_tac [1] ba, auto)
         apply(case_tac [1] "ll3_consume_label p (Suc n) l", auto) apply(blast)
       apply(case_tac [1] "x22 = length p", auto)

        apply(case_tac [1] "\<not>x21", auto)

       apply(case_tac [1] "ll3_consume_label p (Suc n) l", auto) apply(blast)
    apply(case_tac [1] "ll3_consume_label p (Suc n) l", auto) apply(blast)
    apply(case_tac [1] "ll3_consume_label p (Suc n) l", auto) apply(blast)

     apply(case_tac [1] "ll3_consume_label (n # p) 0 x52", auto)
    apply(case_tac [1] ba, auto)
    apply(case_tac [1] "ll3_consume_label p (Suc n) l", auto) apply(blast)
    done
qed

lemma ll3_consumes_length :
"(l1, s, l2) \<in> ll3_consumes \<Longrightarrow> length l1 = length l2"
  apply(induction rule:ll3_consumes.induct, auto)
   apply(insert  ll3_consume_label_length, blast+)
  done

lemma set_diff_fact :
"s \<inter> s' = {} \<Longrightarrow> (s \<union> s') - (s \<union> t) = s' - t"
  apply(blast+)
  done

lemma set_diff_fact2 :
"s \<inter> s' = {} \<Longrightarrow> (s \<union> s') - (t \<union> s') = s - t"
  apply(blast+)
  done

lemma set_diff_fact3 :
"s \<inter> s' = {} \<Longrightarrow> sa \<subseteq> s \<Longrightarrow> s'a \<subseteq> s' ==> (s \<union> s') - (sa \<union> s'a) = (s - sa) \<union> (s' - s'a)"
  apply(auto)
  done

lemma set_diff_dist1 :
"(s1 - ss1) \<union> (s2 - ss2) \<subseteq>
(s1 \<union> s2) "
  apply(blast)
  done

lemma set_diff_dist2:
"? sk . (s1 - ss1) \<union> (s2 - ss2) = ((s1 \<union> s2) - sk)"
  apply(insert set_diff_dist1)
  apply(blast)
  done

lemma quick_opt_split :
"\<And> opt r f r'. (case opt of
  None \<Rightarrow> None
  | Some r \<Rightarrow> Some (f r)) = Some r' \<Longrightarrow> (? r . opt = Some r \<and> r' = f r)"
  apply(case_tac opt, auto)
  done

(* this approach is extremely inefficient *)
fun setmap :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a set) \<Rightarrow> ('b set)" where
"setmap f s = {x . ? y . y \<in> s \<and> x = f y}"


fun consumes_deepen :: "(childpath * nat) list \<Rightarrow> (childpath * nat) list" where
"consumes_deepen [] = []"
|"consumes_deepen ((p,0)#t) = (*(p,0)#*)consumes_deepen t" (* what should behavior be in this case *)
|"consumes_deepen ((p, Suc n)#t) = (p@[0], n)#consumes_deepen t"

fun incrlast :: "childpath \<Rightarrow> childpath" where
"incrlast [] = []"
| "incrlast (h#[]) = (h+1)#[]"
| "incrlast (h#(h'#t)) = h#(incrlast (h'#t))"

fun consumes_incr :: "(childpath * nat) list \<Rightarrow> (childpath * nat) list" where
"consumes_incr [] = []"
| "consumes_incr ((p,n)#t) = (incrlast p, n)#(consumes_incr t)"


fun consumes_deepen' :: "(childpath * nat) set \<Rightarrow> (childpath * nat) set" where
"consumes_deepen' s = {x . ? y ln . ln > 0 \<and> (y,ln) \<in> s \<and> x = (y@[0], ln-1)}"

fun consumes_incr' :: "(childpath * nat) set \<Rightarrow> (childpath * nat) set" where
"consumes_incr' s = { x . ? y n ln. (y@[n],ln) \<in> s \<and> x = (y@[n+1], ln)}"

lemma ll3_consume_label_sane1' :
"(! q e l . (t::ll3) = (q, LSeq e l) \<longrightarrow> 
   (! p n l' p' . ll3_consume_label p n l = Some (l', p') \<longrightarrow> p' \<noteq> [] \<longrightarrow>
     (? pp k . p' = pp@(k#p) \<and> k \<ge> n)))
\<and>
(! p n l' p' . ll3_consume_label p n l = Some (l', p') \<longrightarrow> p' \<noteq> [] \<longrightarrow>
     (? pp k . p' = pp@(k#p) \<and> k \<ge> n))
"
  apply(induction rule:my_ll_induct) apply(auto)
  apply(case_tac ba, auto)
      apply(case_tac[1] "ll3_consume_label p (Suc n) l", auto 2 1) 
      apply(drule_tac [1] x = "p" in spec)
      apply(drule_tac [1] x = "Suc n" in spec) apply(auto)
         apply(case_tac [1] "x22 = length p", auto)
          apply(case_tac [1] "\<not>x21", auto) 
     apply(case_tac[1] "ll3_consume_label p (Suc n) l", auto 2 1)
      apply(drule_tac [1] x = "p" in spec)
      apply(drule_tac [1] x = "Suc n" in spec) apply(auto)

    apply(case_tac[1] "ll3_consume_label p (Suc n) l", auto 2 1)
      apply(drule_tac [1] x = "p" in spec)
      apply(drule_tac [1] x = "Suc n" in spec) apply(auto)
     apply(case_tac[1] "ll3_consume_label p (Suc n) l", auto 2 1)
      apply(drule_tac [1] x = "p" in spec)
      apply(drule_tac [1] x = "Suc n" in spec) apply(auto)

   apply(case_tac [1] "ll3_consume_label (n # p) 0 x52", auto 2 1)
    apply(rename_tac [1] boo)
      apply(case_tac [1] boo, auto 2 1)
   apply(case_tac[1] "ll3_consume_label p (Suc n) l", auto 2 1)
   apply(drule_tac [1] ll3_consume_label_unch, auto)
  apply(thin_tac [1] " \<forall>p n l' p'.
          ll3_consume_label p n aa = Some (l', p') \<longrightarrow>
          p' \<noteq> [] \<longrightarrow> (\<exists>pp k. p' = pp @ k # p \<and> n \<le> k)")
  
      apply(drule_tac [1] x = "p" in spec)
   apply(drule_tac [1] x = "Suc n" in spec) apply(auto)
  apply(thin_tac[1] "\<forall>p n l' p'.
          ll3_consume_label p n l = Some (l', p') \<longrightarrow>
          p' \<noteq> [] \<longrightarrow> (\<exists>pp k. p' = pp @ k # p \<and> n \<le> k)")
      apply(drule_tac [1] x = "n#p" in spec)
  apply(drule_tac [1] x = "0" in spec) apply(auto)
  done
  
lemma ll3_consume_label_sane1 :
" ll3_consume_label p n l = Some (l', p') \<Longrightarrow> p' \<noteq> [] \<Longrightarrow>
     (? pp k . p' = pp@(k#p) \<and> k \<ge> n)
"
  apply(insert ll3_consume_label_sane1')
  apply(blast)
  done

lemma consumes_incr_emp : "consumes_incr [] = []"
  apply(auto)
  done  

lemma consumes_incr_app [rule_format]: "! t' . consumes_incr (t@t') = consumes_incr t @ consumes_incr t'"
proof(induction t)
  case Nil thus ?case by auto next
  case (Cons h t) thus ?case
    apply(auto)
    apply(case_tac h, auto)
    done qed

lemma consumes_deepen_app [rule_format]: "! t' . consumes_deepen (t@t') = consumes_deepen t @ consumes_deepen t'"
proof(induction t)
  case Nil thus ?case by auto next
  case (Cons h t) thus ?case
    apply(auto)
    apply(case_tac h, auto)
    apply(case_tac b, auto)
    done
qed
  

(* do we need an analogous consumes_decr? *)
(* Q: how to deal with current node's location? Just use zero? *)
(* NB: there may be an off by one here on the LLab case *)
(* I think they need to be restated, instead of != nil *)
(* our llab case here is wrong, only a prefix of p needs to be accounted for
, depending on the initial path argument passed in 
do we need @[0]?*)
(* TODO: restate this lemma for new "consumes" predicate and see
if we can get it to go through *)
(* we used to require p != nil in the lab case *)
(* How does Deepen work? Maybe we should reverse role of s'' and deepen (s'') *)
(* maybe we should use disjoint union? *)
(* I think the issue might be that llab uselessly quantifies over p? *)
(*
lemma ll3_consumes_split :
"(l1, s, l2) \<in> ll3_consumes \<Longrightarrow> 
(! q1 h1 t1 q2 h2 t2 . l1 = (q1, h1) # t1 \<longrightarrow> l2 = (q2, h2) # t2 \<longrightarrow> 
  (q1 = q2 \<and> (? s' . consumes_incr s' \<subseteq> s \<and> (t1, s', t2) \<in> ll3_consumes \<and>
           ((h1 = h2 \<and> s = consumes_incr s') \<or> 
              (? p n . h1 = LLab False ((length p) + n) \<and> h2 = LLab True ((length p) + n) \<and> ({(p@[0], n)} \<subseteq> s \<and> consumes_incr s' = s - {(p@[0], n)})) \<or> 
              (? e  ls1 ls2 . h1 = LSeq e ls1 \<and> h2 = LSeq e ls2 \<and> 
               (? s''.  (ls1, s'', ls2) \<in> ll3_consumes \<and>
                        (consumes_deepen s'' \<subseteq> s \<and> consumes_incr s' = s - (consumes_deepen s'')  )))))))"
*)

lemma incrlast_comp :
"incrlast (a@[b]) = a@[b+1]"
proof(induction a)
  case Nil thus ?case by auto next
  case (Cons h t) thus ?case 
    apply(auto) 
    apply(case_tac "t@[b]", auto)
    done qed


lemma incrlast_comp2 :
"a@[b+1] = incrlast (a@[b])"
  apply(insert incrlast_comp) apply(auto)
  done

(* Q: use sorted lists rather than sets for efficiency? *)
(* use a functional version of cp_rev_less for lesser metric,
   and implement "less" typeclass? *)
(* should we add a hypothesis about how either s'' is {} or else consumes_deepen isn't *)
(*
lemma ll3_consumes_split :
"(l1, s, l2) \<in> ll3_consumes \<Longrightarrow> 
(! q1 h1 t1 q2 h2 t2 . l1 = (q1, h1) # t1 \<longrightarrow> l2 = (q2, h2) # t2 \<longrightarrow> 
  (q1 = q2 \<and> (? s' . (t1, s', t2) \<in> ll3_consumes \<and>
           ((h1 = h2 \<and> s = consumes_incr s') \<or> 
              (? n . h1 = LLab False n \<and> h2 = LLab True n \<and> (s = ([0],n)#(consumes_incr s'))) \<or> 
              (? e  ls1 ls2 . h1 = LSeq e ls1 \<and> h2 = LSeq e ls2 \<and> 
               (? s''.  (ls1, s'', ls2) \<in> ll3_consumes \<and>
                        (s = (consumes_deepen s'')@(consumes_incr s')   )))))))"
*)
(* "hybrid approach" *)
lemma ll3_consumes_split :
"(l1, s, l2) \<in> ll3_consumes \<Longrightarrow> 
(! q1 h1 t1 q2 h2 t2 . l1 = (q1, h1) # t1 \<longrightarrow> l2 = (q2, h2) # t2 \<longrightarrow> 
  (q1 = q2 \<and> (? s' . (t1, s', t2) \<in> ll3_consumes \<and>
           ((h1 = h2 \<and> s = consumes_incr s') \<or> 
              (? n . h1 = LLab False n \<and> h2 = LLab True n \<and> (set s = set (([0],n)#(consumes_incr s')))) \<or> 
              (? e  ls1 ls2 . h1 = LSeq e ls1 \<and> h2 = LSeq e ls2 \<and> 
               (? s''.  (ls1, s'', ls2) \<in> ll3_consumes \<and>
                        (set s = set((consumes_deepen s'')@(consumes_incr s'))   )))))))"

proof(induction rule:ll3_consumes.induct)
  case (1 l) thus ?case
    apply(auto  simp add:ll3_consumes.intros)  
    apply(rule_tac x = "[]" in exI) 
    apply(auto  simp add:ll3_consumes.intros) 

    done next
  case (2 p n l l')
  then show ?case
    apply(auto 2 1)
      apply(case_tac h1, auto 2 1)
          apply(case_tac[1] "ll3_consume_label p (Suc n) t1", auto 2 1)
         apply(case_tac [1] "x22 = length p", auto 2 1)
          apply(case_tac [1] "\<not>x21", auto 2 1)
          apply(case_tac[1] "ll3_consume_label p (Suc n) t1", auto 2 1)
         apply(case_tac[1] "ll3_consume_label p (Suc n) t1", auto 2 1)
          apply(case_tac[1] "ll3_consume_label p (Suc n) t1", auto 2 1)
       apply(case_tac [1] "ll3_consume_label (n # p) 0 x52", auto 2 1)
    apply(rename_tac [1] boo)
      apply(case_tac [1] boo, auto 2 1)
       apply(case_tac[1] "ll3_consume_label p (Suc n) t1", auto 2 1)

      apply(case_tac h1, auto 2 1)
          apply(case_tac[1] "ll3_consume_label p (Suc n) t1", auto 2 1)
         apply(case_tac [1] "x22 = length p", auto 2 1)
          apply(case_tac [1] "\<not>x21", auto 2 1)
          apply(case_tac[1] "ll3_consume_label p (Suc n) t1", auto 2 1)
         apply(case_tac[1] "ll3_consume_label p (Suc n) t1", auto 2 1)
          apply(case_tac[1] "ll3_consume_label p (Suc n) t1", auto 2 1)
       apply(case_tac [1] "ll3_consume_label (n # p) 0 x52", auto 2 1)
    apply(rename_tac [1] boo)
      apply(case_tac [1] boo, auto 2 1)
      apply(case_tac[1] "ll3_consume_label p (Suc n) t1", auto 2 1)

    apply(frule_tac[1] ll3_consume_label_unch, auto 2 1)
    apply(rule_tac [1] x = "[]" in exI) apply(auto simp add:ll3_consumes.intros)

    done next

  case (3 p n l l' ph pt) thus ?case
    apply(clarify)
    apply(simp)

    apply(rule conjI)
     apply(drule_tac ll3_consume_label_hdq) apply(simp)

    apply(rule conjI)
     apply(drule_tac ll3_consume_label_hdq) apply(simp)

    (* problem already: what if n = ph? *)
    apply(frule_tac ll3_consume_label_sane1) apply(simp)
    apply(auto 2 1)

    apply(case_tac[1] h1, simp)
        apply(case_tac[1] "ll3_consume_label p (Suc n) t1") apply(simp)
        apply(auto 2 1)
    apply(frule_tac[1] ll3_consume_label_sane1)
         apply( auto 3 1)

        apply(drule_tac [1] "ll3_consumes.intros")
        apply(rule_tac [1] x = "[(pt @ [ph - Suc n], length p)]" in exI)
        apply(auto simp add:ll3_consumes.intros)
        apply(auto simp add: incrlast_comp)

               apply(case_tac [1] "x22 = length p", auto 2 1)
          apply(case_tac [1] "\<not>x21", auto 2 1)
          apply(rule_tac [1] x = "[]" in exI)
    apply(auto 2 1)
        apply(rule_tac [1] "ll3_consumes.intros")
       apply(case_tac[1] "ll3_consume_label p (Suc n) t1") apply(auto 2 1)
       apply(frule_tac ll3_consume_label_sane1, auto 3 1)
    apply(drule_tac [1] ll3_consumes.intros)

    apply(rule_tac [1] x = "[(pt@[ph - Suc n], length p)]" in exI)
       apply(auto 2 1 simp add:incrlast_comp)

        apply(case_tac[1] "ll3_consume_label p (Suc n) t1") apply(simp)
      apply(auto 2 1)
      apply(frule_tac ll3_consume_label_sane1)
      apply(auto 2 1)

       apply(drule_tac [1] "ll3_consumes.intros") 
      apply(rule_tac [1] x = "[(pt@[ph - Suc n], length p)]" in exI)
        apply(auto 2 1 simp add:incrlast_comp)

       apply(case_tac[1] "ll3_consume_label p (Suc n) t1") apply(auto 2 1)
       apply(frule_tac ll3_consume_label_sane1, auto 3 1)
       apply(rule_tac [1] x = "[(pt@[ph - Suc n], length p)]" in exI) apply(auto 2 1 simp add:ll3_consumes.intros incrlast_comp)
        

        apply(case_tac [1] "ll3_consume_label
              (n # p) 0 x52", auto 2 1)
    apply(rename_tac [1] "boo")
apply(case_tac [1] "boo", auto 2 1)

     apply(case_tac[1] "ll3_consume_label p (Suc n) t1") apply(auto 2 0)
     apply(drule_tac [1] "ll3_consume_label_unch", auto 2 0)
            apply(frule_tac ll3_consume_label_sane1, auto 3 1)
     apply(drule_tac [1] "ll3_consumes.intros")
     apply(rule_tac [1] x = "[(pt@[ph - Suc n], length p)]" in exI) apply(auto 2 1 simp add: incrlast_comp)

            apply(frule_tac ll3_consume_label_sane1, auto 3 1)
     apply(drule_tac [1] "ll3_consumes.intros")
    apply(rule_tac [1] x = "[]" in exI) apply (auto 2 1)
    apply(rule_tac[1] ll3_consumes.intros)
    apply(rule_tac [1] x = "[((pp @ [k], Suc (length p)))]" in exI) apply (auto 2 1)

    done next

  case (4 l s l' s' l'') thus ?case
    apply(clarify)
    apply(simp) apply(auto)
    

    apply(case_tac l', auto 2 0)
      apply(drule_tac[1] ll3_consumes_length, simp)

      
    apply(case_tac l', auto 2 0)
     apply(drule_tac[1] ll3_consumes_length, simp)

    apply(case_tac l', auto)

           apply(drule_tac[1] ll3_consumes_length, auto)
  
               apply(rule_tac [1] x = "s'a @ s'aa" in exI)
         apply(auto 2 1 simp add:ll3_consumes.intros consumes_incr_app)

               apply(rule_tac [1] x = "s'a @ s'aa" in exI)
        apply(auto 2 1 simp add:ll3_consumes.intros consumes_incr_app)
               apply(rule_tac [1] x = "s'a @ s'aa" in exI)
        apply(auto 2 1 simp add:ll3_consumes.intros consumes_incr_app)
               apply(rule_tac [1] x = "s'a @ s'aa" in exI)
        apply(auto 2 1 simp add:ll3_consumes.intros consumes_incr_app)
               apply(rule_tac [1] x = "s'a @ s'aa" in exI)
        apply(auto 2 1 simp add:ll3_consumes.intros consumes_incr_app)
               apply(rule_tac [1] x = "s'a @ s'aa" in exI)
        apply(auto 2 1 simp add:ll3_consumes.intros consumes_incr_app)
    apply(drule_tac[1] x = "s'' @ s''a" in spec) apply(auto simp add:ll3_consumes.intros consumes_incr_app consumes_deepen_app) 
    apply(drule_tac[1] x = "s'' @ s''a" in spec) apply(auto simp add:ll3_consumes.intros consumes_incr_app consumes_deepen_app) 
    done qed

(*
lemma ll3_consumes_char' :
"(! q e h l . (t::ll3) = (q, LSeq e (h#l)) \<longrightarrow> 
   (! p n h' l' p'. (ll3_consume_label p n (h#l) = Some (h'#l', p')) \<longrightarrow> (fst h = fst h')length l = length l'))
\<and>
((! p n l' p'. (ll3_consume_label p n (l :: ll3 list) = Some (l', p')) \<longrightarrow> length l = length l'))
"
*)
lemma ll3_assign_label_qvalid' :
"((q,t) \<in> ll_valid_q \<longrightarrow> ((! q' t' . ll3_assign_label (q,t) = Some (q',t') \<longrightarrow> q = q' \<and> (q',t') \<in> ll_valid_q) \<and>
    ((! e l . t = LSeq e l \<longrightarrow> (!p n  s l' . (l,s,l') \<in> ll3_consumes \<longrightarrow>
                     (! l'' . ll3_assign_label_list l' = Some l'' \<longrightarrow> (q,l'') \<in> ll_validl_q))))))
\<and> (((x,x'), ls) \<in> ll_validl_q \<longrightarrow> 
    ((! ls' . ll3_assign_label_list ls = Some ls' \<longrightarrow> ((x,x'), ls') \<in> ll_validl_q ))
     \<and> (!p n  s ls' . (ls,s,ls') \<in> ll3_consumes \<longrightarrow>
                     (! ls'' . ll3_assign_label_list ls' = Some ls'' \<longrightarrow> ((x,x'),ls'') \<in> ll_validl_q)))"
  apply(induction rule:ll_valid_q_ll_validl_q.induct, auto simp add:ll_valid_q_ll_validl_q.intros)
    apply(case_tac e, auto simp add:ll_valid_q_ll_validl_q.intros)
    apply(case_tac e, auto simp add:ll_valid_q_ll_validl_q.intros)
    apply(case_tac e, auto simp add:ll_valid_q_ll_validl_q.intros)

  apply(case_tac "ll3_consume_label [] 0 l", auto)
   apply(case_tac "ll3_assign_label_list aa", auto)
  
  apply(case_tac "ll3_consume_label [] 0 l", auto)
    apply(case_tac "ll3_assign_label_list aa", auto)

  apply(case_tac "ll3_consume_label [] 0 l", auto)
     apply(case_tac "ll3_assign_label_list aa", auto)
     apply(rule_tac [1] ll_valid_q_ll_validl_q.intros)
     apply(case_tac ba, auto)
      apply(drule_tac "ll3_consume_label_unch", auto)

     apply(subgoal_tac [1] "(l,[([]@(ac#list),length [])], aa) \<in> ll3_consumes")
      apply(blast)

  apply(frule_tac[1] ll3_consume_label_sane1) apply(auto)
  apply(drule_tac[1] ll3_consumes.intros(3)) apply(auto)

    apply(drule_tac [1] ll3_consumes_length, auto simp add:ll_valid_q_ll_validl_q.intros)

   apply(case_tac [1] "ll3_assign_label ((n, n'), h)", auto)
 apply(case_tac [1] "ll3_assign_label_list t", auto)
   apply(auto simp add:ll_valid_q_ll_validl_q.intros)

  apply(case_tac [1] ls', auto)
   apply(drule_tac[1] ll3_consumes_length, auto)

  apply(rename_tac  boo)
   apply(case_tac [1] "ll3_assign_label ((a, b), ba)", auto)
  apply(case_tac [1] "ll3_assign_label_list boo", auto)
  apply(frule_tac[1] ll3_consumes_split) apply(auto)
    apply(auto simp add:ll_valid_q_ll_validl_q.intros)
  apply(drule_tac [1] ll_valid_q.cases, auto)
    apply(auto simp add:ll_valid_q_ll_validl_q.intros)

  apply(case_tac[1] "ll3_consume_label [] 0 ls2", auto)
  apply(rename_tac  var2)
  apply(case_tac [1] "ll3_assign_label_list ac", auto)
  apply(drule_tac [1] ll_valid_q.cases, auto)

    apply(rule_tac[1] ll_valid_q_ll_validl_q.intros) apply(auto)
  apply(rule_tac[1] ll_valid_q_ll_validl_q.intros) 

    (* combine asssumes fact *)

  
    apply(case_tac var2) apply(auto)
  apply(drule_tac [1] ll3_consume_label_unch, auto)
  
  apply(subgoal_tac "? list' last . a#list = list'@[last]") apply(auto)
  
 apply(subgoal_tac [1] "(l,(s'')@[(a#list,0)], ac) \<in> ll3_consumes")

   apply(auto)
  apply(rule_tac ll3_consumes.intros(4)) apply(auto)
   apply(drule_tac ll3_consumes.intros(3)) apply(auto)


  apply(subgoal_tac [1] "a # list = [] \<or> (? fi la . a#list = fi @ [la])")
  apply(rule_tac[2] haslast')
  apply(auto)
  done

lemma ll3_assign_label_qvalid1 :
"((q,t) \<in> ll_valid_q \<Longrightarrow> ll3_assign_label (q,t) = Some (q',t') \<Longrightarrow> (q',t') \<in> ll_valid_q)"
  apply(insert ll3_assign_label_qvalid'[of q t])
  apply(auto)
  done

lemma ll3_assign_label_qvalid2 :
"((q,ls) \<in> ll_validl_q \<Longrightarrow> ll3_assign_label_list ls = Some ls' \<Longrightarrow> (q,ls') \<in> ll_validl_q)"
  apply(insert ll3_assign_label_qvalid'[of _ _ "(fst q)" "(snd q)" ls])
  apply(auto)
  done
(* idea: if assign labels succeeds, we have a ll_valid3
  we need some kind of strengthened hypothesis?
  do we need an equivalent of "consumes" for "assigns"?
 *)

(* we also need a lemma about consume label and descendents relation:
" if we consumed a label, and result is nil, then there are NO labels at that depth"
" if we consumed a label and the result is non nil, there is at least one"
later we'll have to prove there can't be more than one (?)

here's the second part to prove there isn't more than one:
if there is more than one in a list (at that depth), assign label has to
return false
*)

(* TODO: this is currently about consume label, we need an analogous one for assign label *)
(* idea: nodes are either the same, or we added a childpath to a seq node *)
(* how to characterize the childpath we add? *)
(* should we just say that getting the childpath works?
   or that it stands in the descendents relation? *)
(* yes, we want to talk about how there must be a descendent
   along that path *)
(* we also need a case for if t is a label, since consumes may switch it
   (better: just use consumes inside the seq case, assign label never directly
   modifies labels) *)
(*
lemma ll3_assign_label_sane1' :
"(! q' t' . ll3_assign_label t = Some (q', t') \<longrightarrow> 
    (((t = (q', t')) \<or>  
       (? e e' xs xs'. t = (q', LSeq e xs) \<and> ll3_assign_label_list xs = Some xs' \<and> t' = LSeq e' xs')))) \<and>
 (! l' . ll3_assign_label_list l = Some l' \<longrightarrow> map fst l = map fst l')"
*)

(* used to retrieve most recent consume *)
(* problem: what if there was nothing consumed this time?
   we may need another case in valid3' for that, but let's think on it
 *)
fun cplast :: "(childpath * nat) list \<Rightarrow> childpath" where
"cplast [] = []"
| "cplast (ph#[]) = fst ph"
| "cplast (ph#(ph'#pt)) = cplast (ph'#pt)"

(* we need to establish links between consume_labels and descendents. *)

(* Fact 1: if we return [], there are NO descendents at that depth.
Fact 2: if we return non nil, the returned path is the descendent path
Another note: if we use consumes instead, we get nicer formatting of paths (?)
*)

(* q: relationship between lengths of inputs and outputs?
let's look at consumes relation *)
(* to finish this up: the list case should talk about Seqs the list is part of *)

(* Another option: if the descendent exists,
then consume_label will find it.
make this general over inputs for consume_label
*)

(* maybe we need to characterize what consume_label does find?
do we need our cp_less predicate after all? *)
(*
fun cp_rev_less :: "childpath \<Rightarrow> childpath \<Rightarrow> bool" where
"cp_rev_less [] (h#t) = True"
*)


(* here we want to prove that when we consume_label on the parent,
the corresponding calls to consume_label on the child also returned nil

the question is whether we want to do induction on the list or
the index of the child. the index of the child sounds promising
i think all we need is a case analysis on ls (?)
*)

(* we need my_ll_induct *)
lemma ll3_consume_nil_gen' :
"(! q p n e l l' . (t::ll3) = (q, LSeq e l) \<longrightarrow> ll3_consume_label p n l = Some (l', []) \<longrightarrow>
  (! p' n' . length p = length p' \<longrightarrow> ll3_consume_label p' n' l = Some (l, [])))
\<and> (! p n ls' . ll3_consume_label p n ls = Some (ls', []) \<longrightarrow>
  (! p' n' . length p = length p' \<longrightarrow> ll3_consume_label p' n' ls = Some (ls, [])))"
  apply(induction rule:my_ll_induct, auto)
  apply(case_tac ba, auto)
       apply(case_tac [1] "ll3_consume_label p (Suc n) l", auto)
apply(case_tac [1] "ll3_consume_label p' (Suc n') l", auto)
         apply(drule_tac [1] x = p in spec) apply(auto)

         apply(drule_tac [1] x = p in spec) apply(auto)
         apply(drule_tac [1] x = p in spec) apply(auto)

       apply(case_tac [1] "ll3_consume_label p (Suc n) l", auto)
apply(case_tac [1] "ll3_consume_label p' (Suc n') l", auto)
      apply(drule_tac [1] x = p in spec) apply(auto)
       apply(drule_tac [1] x = p in spec) apply(auto)
      apply(drule_tac [1] x = p in spec) apply(auto)

       apply(case_tac [1] "ll3_consume_label p (Suc n) l", auto)
apply(case_tac [1] "ll3_consume_label p' (Suc n') l", auto)
      apply(drule_tac [1] x = p in spec) apply(auto)
      apply(drule_tac [1] x = p in spec) apply(auto)
      apply(drule_tac [1] x = p in spec) apply(auto)

       apply(case_tac [1] "ll3_consume_label p (Suc n) l", auto)
apply(case_tac [1] "ll3_consume_label p' (Suc n') l", auto)
       apply(drule_tac [1] x = p in spec) apply(auto)
      apply(drule_tac [1] x = p in spec) apply(auto)
      apply(drule_tac [1] x = p in spec) apply(auto)

       apply(case_tac [1] "ll3_consume_label p (Suc n) l", auto)
apply(case_tac [1] "ll3_consume_label p' (Suc n') l", auto)
       apply(drule_tac [1] x = p in spec) apply(auto)
    apply(drule_tac [1] x = p in spec) apply(auto)
    apply(drule_tac [1] x = p in spec) apply(auto)


    apply(case_tac [1] "ll3_consume_label
              (n # p) 0 x52", auto)
apply(case_tac [1] "ba", auto)
apply(case_tac [1] "ll3_consume_label p (Suc n) l", auto)
  apply(case_tac [1] "ll3_consume_label
              (n' # p') 0 x52", auto)
   apply(drule_tac [1] x = "(n # p)" in spec) apply(auto)

apply(case_tac [1] "ba", auto)
apply(case_tac [1] "ll3_consume_label p' (Suc n') l", auto)

      apply(drule_tac [1] x = p' in spec) (* bogus *)
      apply(drule_tac [1] x = p in spec)  apply(auto)
     apply(drule_tac [1] ll3_consume_label_unch)  (*bogus*)
     apply(drule_tac [1] ll3_consume_label_unch)
     apply(drule_tac [1] ll3_consume_label_unch) apply(simp)

  apply(drule_tac [1] x = "p" in spec) (* bogus *)
  apply(drule_tac [1] x = "p" in spec)
    apply(auto)

    apply(drule_tac [1] x = "p" in spec) (* bogus *)
  apply(drule_tac [1] x = "p" in spec)
   apply(auto)

  apply(drule_tac [1] x = "n#p" in spec) apply(auto)
  done

lemma ll3_consume_nil_gen :
"ll3_consume_label p n ls = Some (ls', []) \<Longrightarrow>
  length p = length p' \<Longrightarrow> ll3_consume_label p' n' ls = Some (ls, [])"
  apply(insert ll3_consume_nil_gen')
  apply(blast+)
  done

(* we need a generalized version of this for deeper descendents *)
lemma ll3_consume_label_child' [rule_format] :
"
(! c aa bb e2 l2l . length ls > c \<longrightarrow> ls ! c = ((aa, bb), llt.LSeq e2 l2l) \<longrightarrow>
 (! p n ls' . ll3_consume_label p n ls = Some (ls', []) \<longrightarrow>
  (? nx . (ll3_consume_label (c#p) nx l2l = Some (l2l, [])))
))"
  apply(induction ls)
   apply(auto)
  apply(case_tac ba, auto) 
      apply(case_tac [1] "ll3_consume_label p (Suc n) ls", auto)
      apply(case_tac c, auto)
      apply(drule_tac [1] x=nat in spec) apply(auto)
      apply(drule_tac [1] x = p in spec) apply(auto)
      (* need a lemma about how if output is [], it is []
         for any equal length path *)
      apply(thin_tac [1] "ll3_consume_label p (Suc n) ls = Some (ab, [])")
      apply(drule_tac [1] ll3_consume_nil_gen) apply(auto)

     apply(case_tac [1] "x22 = length p") apply(auto)
      apply(case_tac[1]"\<not> x21", auto)
     apply(case_tac  [1] "ll3_consume_label p (Suc n) ls") apply(auto)

  apply(case_tac [1] c, auto)
      apply(drule_tac [1] x=nat in spec) apply(auto)
     apply(drule_tac [1] x = p in spec) apply(auto)
      apply(thin_tac [1] "ll3_consume_label p (Suc n) ls = Some (ab, [])")
  apply(drule_tac [1] "ll3_consume_nil_gen") apply(auto)

     apply(case_tac  [1] "ll3_consume_label p (Suc n) ls") apply(auto)
    apply(case_tac [1] c, auto)
    
    apply(drule_tac [1] x = "nat" in spec) apply(auto)
    apply(drule_tac [1] x = "p" in spec) apply(auto)
      apply(thin_tac [1] "ll3_consume_label p (Suc n) ls = Some (ab, [])")
  apply(drule_tac [1] "ll3_consume_nil_gen") apply(auto)
  
     apply(case_tac  [1] "ll3_consume_label p (Suc n) ls") apply(auto)
    apply(case_tac [1] c, auto)
    apply(drule_tac [1] x = "nat" in spec) apply(auto)
   apply(drule_tac [1] x = "p" in spec) apply(auto)
      apply(thin_tac [1] "ll3_consume_label p (Suc n) ls = Some (ab, [])")
  apply(drule_tac [1] "ll3_consume_nil_gen") apply(auto)

  apply(case_tac [1] "ll3_consume_label (n # p)
              0 x52", auto)
  apply(case_tac [1] ba, auto)
  apply(case_tac [1] "ll3_consume_label p
              (Suc n) ls", auto)
  apply(case_tac [1] c, auto)
  apply(thin_tac [1] "ll3_consume_label p (Suc n) ls = Some (ac, [])")
  apply(drule_tac [1] ll3_consume_nil_gen) apply(auto)

    apply(drule_tac [1] x = "nat" in spec) apply(auto)
  apply(drule_tac [1] x = "p" in spec) apply(auto)
  apply(thin_tac [1] "ll3_consume_label p (Suc n) ls = Some (ac, [])")
  apply(thin_tac [1] "ll3_consume_label (n # p) 0 x52 = Some (ab, [])")
  apply(drule_tac [1] ll3_consume_nil_gen, auto)
  done

lemma ll3_consume_label_child :
"(ls ! c = ((aa, bb), llt.LSeq e2 l2l) \<Longrightarrow>
  c < length ls \<Longrightarrow>
 (ll3_consume_label p n ls = Some (ls', []) \<Longrightarrow>
  ((ll3_consume_label (c#p) nx l2l = Some (l2l, [])))))"
  apply(drule_tac ll3_consume_label_child') apply(auto)
  apply(thin_tac [1] "ll3_consume_label p n ls =
       Some (ls', [])")
  apply(drule_tac ll3_consume_nil_gen) apply(auto)
  done

(* this needs to become a version of the same fact
but for when immediate child is a label *)
(* need a constraint on length p*)
 lemma ll3_consume_label_child2' [rule_format] :
"
(! c aa bb e2 d . length ls > c \<longrightarrow> ls ! c = ((aa, bb), llt.LLab e2 d) \<longrightarrow>
 (! p n ls' . d = length p \<longrightarrow> ll3_consume_label p n ls \<noteq> Some (ls', [])
))
"
  apply(induction ls)
    apply(auto)

   apply(case_tac ba, auto) 
       apply(case_tac [1] "ll3_consume_label p (Suc n) ls", auto)
       apply(case_tac[1] c, auto)
      apply(case_tac [1] "x22 = length p", auto)
       apply(case_tac[1] "\<not> x21", auto)

       apply(case_tac [1] "ll3_consume_label p (Suc n) ls", auto)
      apply(case_tac[1] c, auto)

       apply(case_tac [1] "ll3_consume_label p (Suc n) ls", auto)
     apply(case_tac[1] c, auto)

       apply(case_tac [1] "ll3_consume_label p (Suc n) ls", auto)
    apply(case_tac[1] c, auto)

       apply(case_tac[1] "ll3_consume_label (n # p) 0 x52", auto)
   apply(case_tac[1] ba, auto)
       apply(case_tac [1] "ll3_consume_label p (Suc n) ls", auto)
   apply(case_tac[1] c, auto)

   done

lemma ll3_consume_label_child2 :
"ls ! c = ((aa, bb), llt.LLab e2 d) \<Longrightarrow>
  c < length ls \<Longrightarrow>
  d = length p \<Longrightarrow>
 ll3_consume_label p n ls \<noteq> Some (ls', [])"
  apply(drule_tac ll3_consume_label_child2') apply(auto)
  done

(* Is there some kind of directionality issue here?
e.g. are we consing onto the front somewhere
where we should be snocing on the backl

did  we switch p vs k

this could also be an issue of whether descend
accumulates paths in reverse order
*)
(*
lemma ll3_consume_label_none_descend :
"(l1, l2, k) \<in> ll3'_descend \<Longrightarrow>
 (! x1 e1 l1l . l1 = (x1, LSeq e1 l1l) \<longrightarrow>
 (! x2 e2 l2l . l2 = (x2, LSeq e2 l2l) \<longrightarrow>
 (! p n l1l' . ll3_consume_label p n l1l = Some (l1l', []) \<longrightarrow>
 (? n l2l' . ll3_consume_label (p@k) n l2l = Some (l2l', [])))))
"
*)

(* lemma: if we are not a seq, we cannot have descendents*)
lemma ll3_hasdesc :
"(t, t', k) \<in> ll3'_descend  \<Longrightarrow>
  (? q e ls . t = (q, LSeq e ls))
"
  apply(induction rule:ll3'_descend.induct)
   apply(auto)
  done

lemma ll3_hasdesc2 :
"(t, t', k) \<in> ll3'_descend  \<Longrightarrow>
  (? q e hd tl . t = (q, LSeq e (hd#tl)))
"
  apply(induction rule:ll3'_descend.induct)
   apply(auto)
  apply(case_tac ls) apply(auto)
  done


lemma ll3_consume_label_none_descend :
"(l1, l2, k) \<in> ll3'_descend \<Longrightarrow>
 (! x1 e1 l1l . l1 = (x1, LSeq e1 l1l) \<longrightarrow>
 (! x2 e2 l2l . l2 = (x2, LSeq e2 l2l) \<longrightarrow>
 (! p n l1l' . ll3_consume_label p n l1l = Some (l1l', []) \<longrightarrow>
 (? n l2l' . ll3_consume_label ((rev k)@p) n l2l = Some (l2l', [])))))
"
  apply(induction rule:ll3'_descend.induct)
   apply(auto)
  apply(case_tac "p@[c]", auto)
  apply(drule_tac ll3_consume_label_child) apply(auto)

  apply(case_tac bc, auto)
  apply(drule_tac[1] ll3_hasdesc) apply(auto)
    apply(drule_tac[1] ll3_hasdesc) apply(auto)
  apply(drule_tac[1] ll3_hasdesc) apply(auto)
  apply(drule_tac[1] ll3_hasdesc) apply(auto)
  apply(drule_tac[1] ll3_hasdesc) apply(auto)
  apply(drule_tac[1] ll3_hasdesc) apply(auto)
  apply(drule_tac[1] ll3_hasdesc) apply(auto)
  apply(drule_tac[1] ll3_hasdesc) apply(auto)
  apply(drule_tac[1] ll3_hasdesc) apply(auto)

  apply(drule_tac[1] x = p in spec) apply(auto)
  apply(drule_tac[1] x = "(rev n)@p" in spec) apply(auto)
  done

lemma ll3_consume_label_find :
"(l1, l2, k) \<in> ll3'_descend \<Longrightarrow>
 (! x1 e1 l1l . l1 = (x1, LSeq e1 l1l) \<longrightarrow>
 (! x2 e2 d . l2 = (x2, LLab e2 d) \<longrightarrow>
 (! p n l1l' . ll3_consume_label p n l1l = Some (l1l', []) \<longrightarrow>
 d + 1 \<noteq> length k + length p)))
"
  apply(induction rule:ll3'_descend.induct)
   apply(auto)
   apply(drule_tac [1] ll3_consume_label_child2) apply(auto)

  
  apply(case_tac bc, auto)

  apply(drule_tac[1] ll3_hasdesc) apply(auto)
    apply(drule_tac[1] ll3_hasdesc) apply(auto)
  apply(drule_tac[1] ll3_hasdesc) apply(auto)
  apply(drule_tac[1] ll3_hasdesc) apply(auto)
  apply(drule_tac[1] ll3_hasdesc) apply(auto)
  apply(drule_tac[1] ll3_hasdesc) apply(auto)
  apply(drule_tac[1] ll3_hasdesc) apply(auto)
  apply(drule_tac[1] ll3_hasdesc) apply(auto)
  apply(drule_tac[1] ll3_consume_label_none_descend) apply(auto)
  apply(rotate_tac [1] 2)
  apply(drule_tac [1] x =  p in spec) apply(auto)
  apply(drule_tac [1] x =  "rev n @ p" in spec) apply(auto)
  done

(*
lemma ll3_consume_label_find2 :
"(l1, l2, k) \<in> ll3'_descend \<Longrightarrow>
 (! x1 e1 l1l . l1 = (x1, LSeq e1 l1l) \<longrightarrow>
 (! x2 e2 d . l2 = (x2, LLab e2 d) \<longrightarrow>
 (! p n l1l' . ll3_consume_label p n l1l = Some (l1l', []) \<longrightarrow>
     (! l1l'' . ll3_assign_labels_list l1l = Some l1l'') \<longrightarrow>
 d + 1 \<noteq> length k + length p)))
"
*)

(* second attempt - we are going to talk about children of l now *)
(* we need to re look at the last line probably *)
(* new idea: instead of "\<in> set", use descendents as premise too for second part? first part too?  *)
(* induction on descendents relation ?
it really seems like we need descendents as a premise also
this one is closer to the answer
 *)
(*
lemma ll3_consume_label_nodesc :
"
  (! e l l' p n . t = (x, LSeq e l) \<longrightarrow> 
  ll3_consume_label p n l = Some (l',[]) \<longrightarrow> 
    (\<not> (\<exists> k y e' . 
        ((x, LSeq e l), (y, LLab e' ((List.length k) + (List.length p))), k) \<in> ll3'_descend))) \<and>
  (! l' p  n . ll3_consume_label p n l = Some (l', []) \<longrightarrow> 
      (! n . n < length l \<longrightarrow> (! x l2 e . l!n = (x,LSeq e l2) \<longrightarrow>
      (\<not> (\<exists> k y e' .
        (l!n, (y, LLab e' ((List.length k) + (List.length p) + 1)), k) \<in> ll3'_descend)))))"
(*
lemma ll3_consume_label_nodesc :
"
  (! e l l' p p' n q . t = (x, LSeq e l) \<longrightarrow> 
  ll3_consume_label p n l = Some (l',[]) \<longrightarrow> 
    (\<not> (\<exists> k y e' . 
        ((x, LSeq e l), (y, LLab e' ((List.length k) + (List.length p))), k) \<in> ll3'_descend))) \<and>
  (! l' p p' n . ll3_consume_label p n l = Some (l', []) \<longrightarrow> 
      (! x t e . t = (x,LSeq e l) \<longrightarrow>
      (\<not> (\<exists> k y e' .
        (t, (y, LLab e' ((List.length k) + (List.length p))), k) \<in> ll3'_descend))))"
*)
  apply(induction rule:my_ll_induct)
  apply(auto)
     apply(drule_tac [1] x = l' in spec)
     apply(drule_tac [1] x = p in spec) apply(auto)
    apply(frule_tac [1] ll3'_descend.cases) apply(auto)

(* we need more uses of spec, this might go through as is *)
      apply(drule_tac [1] x = ac in spec)
      apply(drule_tac [1] x = bc in spec)
      apply(drule_tac [1] x =  "snd (ls!c)" in spec)
      apply(auto)
sorry
*)
    (* is it set vs l' ? *)

lemma ll3_assign_label_length [rule_format]:
" (! ls' . ll3_assign_label_list ls = Some ls' \<longrightarrow> length ls = length ls')
"
proof (induction ls)
  case Nil thus ?case by auto next
  case (Cons h t) thus ?case
    apply(auto)
    apply(case_tac "ll3_assign_label h", auto)
    apply(case_tac "ll3_assign_label_list t", auto)
    done qed

(* this one's more complicated? do we need to talk about consumes? 
or do we just need to say that the output of running on l2l will be
equal to the output of running assign_label on that node ?
this means we probably need the full power of my_ll_induct
*)
(*
hmm, this one does not quite say the right thing 
*)
(*
lemma ll3_assign_label_preserve_child1' [rule_format] :
"
(! c aa bb e2 l2l . length ls > c \<longrightarrow> ls ! c = ((aa, bb), llt.LSeq e2 l2l) \<longrightarrow>
 (! ls' . ll3_assign_label_list ls = Some (ls') \<longrightarrow>
  (? ls0 p . ll3_consume_label [] 0 ls0 = Some (ls, p) \<and>
    ( ? e3 l2l'. ls' ! c = ((aa, bb), llt.LSeq e2 l2l')
))))"

proof(induction ls)
  case Nil thus ?case by auto
  case (Cons h t) thus ?case
  apply(auto)
    apply(case_tac "ll3_assign_label h", auto)
apply(case_tac "ll3_assign_label_list t", auto)
    apply(case_tac c, auto)

      apply(case_tac [1] "ll3_consume_label [] 0 l2l", auto) 
    apply(rename_tac boo)
      apply(case_tac [1] "ll3_assign_label_list ac", auto)

      apply(case_tac [1] "ll3_consume_label [0] 0 l2l", auto) 
    apply(rename_tac boo)
    apply(case_tac [1] "ll3_assign_label_list ac", auto)

      apply(case_tac [1] "ll3_consume_label [] 0 l2l", auto) 
    apply(rename_tac boo)
    apply(case_tac [1] "ll3_assign_label_list ac", auto)

      apply(case_tac [1] e2, auto)
     apply(case_tac [1] e2, auto)
    apply(case_tac [1] e2, auto)
    done qed
*)

(* This works, but is it quite what we need? *)
(* It looks like we might need the converse *)
lemma ll3_assign_label_preserve' [rule_format] :
"(! n' . ll3_assign_label n = Some n' \<longrightarrow>
   (n = n' \<and>
    (! q e d . n = (q, LLab e d) \<longrightarrow> e = True))  \<or> 
(? q  e e' ls ls'' .
      n = (q, LSeq e ls) \<and>
      n' = (q, LSeq e' ls'') \<and>
      (? ls' . ll3_consume_label [] 0 ls = Some (ls', rev e') \<and>
      ll3_assign_label_list ls' = Some ls''
      ))
) \<and>
(! ls' . ll3_assign_label_list ls = Some ls' \<longrightarrow>
  (! h t . ls = h#t \<longrightarrow> 
    (? h' t' . ls' = h' # t' \<longrightarrow>
  (ll3_assign_label_list t = Some t' \<and>
  (( h = h' \<and>
    ( ? q e d . h = (q, LLab e d) \<longrightarrow> e = True)) \<or> 
  (? q  e e' lsdec lsdec'' .
    h = (q, LSeq e lsdec) \<and>
    h' = (q, LSeq e' lsdec'') \<and>
    (? lsdec' . ll3_consume_label [] 0 lsdec = Some (lsdec', rev e') \<and>
    ll3_assign_label_list lsdec' = Some lsdec'')
)))))) 
"
  apply(induction rule:my_ll_induct)
        apply(auto)
            apply(drule_tac [1] ll3_assign_label_unch1) apply(auto)
apply(drule_tac [1] ll3_assign_label_unch1) apply(auto)
          apply(case_tac [1] e, auto)
         apply(case_tac [1] e, auto)

        apply(case_tac [1] "ll3_consume_label [] 0 l", auto)
        apply(rename_tac [1] boo)
     apply(case_tac [1] "ll3_assign_label_list ab", auto)

    apply(case_tac [1] "ll3_consume_label [] 0 l", auto)
        apply(rename_tac [1] boo)
    apply(case_tac [1] "ll3_assign_label_list ab", auto)

        apply(case_tac [1] "ll3_consume_label [] 0 l", auto)
        apply(rename_tac [1] boo)
         apply(case_tac [1] "ll3_assign_label_list ab", auto) 

      apply(case_tac [1] "ll3_consume_label [] 0 l", auto)
        apply(rename_tac [1] boo)
        apply(case_tac [1] "ll3_assign_label_list ab", auto) 

      apply(case_tac [1] "ll3_consume_label [] 0 l", auto)
        apply(rename_tac [1] boo)
       apply(case_tac [1] "ll3_assign_label_list ab", auto) 

      apply(case_tac [1] "ll3_consume_label [] 0 l", auto)
        apply(rename_tac [1] boo)
      apply(case_tac [1] "ll3_assign_label_list ab", auto) 

      apply(case_tac [1] "ll3_consume_label [] 0 l", auto)
        apply(rename_tac [1] boo)
   apply(case_tac [1] "ll3_assign_label_list ab", auto) 

    apply(case_tac [1] "ll3_consume_label [] 0 l", auto)
        apply(rename_tac [1] boo)
   apply(case_tac [1] "ll3_assign_label_list ab", auto) 

    apply(case_tac [1] "ll3_consume_label [] 0 l", auto)
        apply(rename_tac [1] boo)
   apply(case_tac [1] "ll3_assign_label_list ab", auto) 


  apply(case_tac [1] "ll3_assign_label ((a, b), ba)", auto)
   apply(case_tac[1] "ll3_assign_label_list l", auto)
  apply(case_tac[2] "ll3_assign_label_list l", auto)

  apply(case_tac [1] l, auto)
    apply(case_tac [1] "ll3_assign_label ((ab, b), ba)", auto)
  apply(case_tac [1] "ll3_assign_label ((ac, bd), be)", auto)
  done

(* i need to state this one correctly, it's not there yet *)
lemma ll3_assign_label_preserve_new' [rule_format] :
"(! n' . ll3_assign_label n = Some n' \<longrightarrow>
   (n = n' \<and>
    (! q e d . n = (q, LLab e d) \<longrightarrow> e = True))  \<or> 
(? q  e e' ls ls'' .
      n = (q, LSeq e ls) \<and>
      n' = (q, LSeq e' ls'') \<and>
      (? ls' . ll3_consume_label [] 0 ls = Some (ls', rev e') \<and>
      ll3_assign_label_list ls' = Some ls''
      ))
) \<and>
(! ls' . ll3_assign_label_list ls = Some ls' \<longrightarrow>
  ((ls = [] \<and> ls' = []) \<or>
  (? h t . ls = h#t \<and>
    (? h' t' . ls' = h' # t' \<and>
  (ll3_assign_label_list t = Some t' \<and>
  (( h = h' \<and>
    ( ? q e d . h = (q, LLab e d) \<longrightarrow> e = True)) \<or> 
  (? q  e e' lsdec lsdec'' .
    h = (q, LSeq e lsdec) \<and>
    h' = (q, LSeq e' lsdec'') \<and>
    (? lsdec' . ll3_consume_label [] 0 lsdec = Some (lsdec', rev e') \<and>
    ll3_assign_label_list lsdec' = Some lsdec'')
)))))))
"
  apply(induction rule:my_ll_induct)
  apply(auto)
            apply(drule_tac [1] ll3_assign_label_unch1) apply(auto)
              apply(drule_tac [1] ll3_assign_label_unch1) apply(auto)
             apply(case_tac[1] e, auto)
            apply(case_tac[1] e, auto)

      apply(case_tac [1] "ll3_consume_label [] 0 l", auto)
        apply(rename_tac [1] boo)
     apply(case_tac [1] "ll3_assign_label_list ab", auto)

    apply(case_tac [1] "ll3_consume_label [] 0 l", auto)
        apply(rename_tac [1] boo)
    apply(case_tac [1] "ll3_assign_label_list ab", auto)

        apply(case_tac [1] "ll3_consume_label [] 0 l", auto)
        apply(rename_tac [1] boo)
         apply(case_tac [1] "ll3_assign_label_list ab", auto) 

      apply(case_tac [1] "ll3_consume_label [] 0 l", auto)
        apply(rename_tac [1] boo)
        apply(case_tac [1] "ll3_assign_label_list ab", auto) 

      apply(case_tac [1] "ll3_consume_label [] 0 l", auto)
        apply(rename_tac [1] boo)
       apply(case_tac [1] "ll3_assign_label_list ab", auto) 

      apply(case_tac [1] "ll3_consume_label [] 0 l", auto)
        apply(rename_tac [1] boo)
      apply(case_tac [1] "ll3_assign_label_list ab", auto) 

     apply(case_tac [1] "ll3_consume_label [] 0 l", auto)
        apply(rename_tac [1] boo)
     apply(case_tac [1] "ll3_assign_label_list ab", auto) 

  apply(case_tac [1] "ll3_consume_label [] 0 l", auto)
        apply(rename_tac [1] boo)
      apply(case_tac [1] "ll3_assign_label_list ab", auto) 

  apply(case_tac [1] "ll3_consume_label [] 0 l", auto)
        apply(rename_tac [1] boo)
      apply(case_tac [1] "ll3_assign_label_list ab", auto) 


  apply(case_tac [1] "ll3_assign_label ((a, b), ba)", auto)
   apply(case_tac[1] "ll3_assign_label_list l", auto)
     apply(case_tac [1] bc, auto)

   apply(case_tac[1] "ll3_assign_label_list l", auto)
  done

lemma ll3_assign_label_preserve1 :
"ll3_assign_label n = Some n' \<Longrightarrow>
   (n = n' \<and>
    (! q e d . n = (q, LLab e d) \<longrightarrow> e = True))  \<or> 
(? q  e e' ls ls'' .
      n = (q, LSeq e ls) \<and>
      n' = (q, LSeq e' ls'') \<and>
      (? ls' . ll3_consume_label [] 0 ls = Some (ls', rev e') \<and>
      ll3_assign_label_list ls' = Some ls''
      ))
"
  apply(insert ll3_assign_label_preserve')
  apply(blast+)
  done

lemma ll3_assign_label_preserve2 :
"ll3_assign_label_list ls = Some ls' \<Longrightarrow>
  (! h t . ls = h#t \<longrightarrow> 
    (? h' t' . ls' = h' # t' \<longrightarrow>
  (ll3_assign_label_list t = Some t' \<and>
  (( h = h' \<and>
    ( ? q e d . h = (q, LLab e d) \<longrightarrow> e = True)) \<or> 
  (? q e e' lsdec lsdec'' .
    h = (q, LSeq e lsdec) \<and>
    h' = (q, LSeq e' lsdec'') \<and>
    (? lsdec' . ll3_consume_label [] 0 lsdec = Some (lsdec', rev e') \<and>
    ll3_assign_label_list lsdec' = Some lsdec'')
)))))
"
  apply(insert ll3_assign_label_preserve')
  apply(blast+)
  done

lemma ll3_assign_label_preserve_new1 :
"ll3_assign_label n = Some n' \<Longrightarrow>
   (n = n' \<and>
    (! q e d . n = (q, LLab e d) \<longrightarrow> e = True))  \<or> 
(? q  e e' ls ls'' .
      n = (q, LSeq e ls) \<and>
      n' = (q, LSeq e' ls'') \<and>
      (? ls' . ll3_consume_label [] 0 ls = Some (ls', rev e') \<and>
      ll3_assign_label_list ls' = Some ls''
      ))
"
  apply(insert ll3_assign_label_preserve_new')
  apply(blast+)
  done

lemma ll3_assign_label_preserve_new2 :
"ll3_assign_label_list ls = Some ls' \<Longrightarrow>
  ((ls = [] \<and> ls' = []) \<or>
  (? h t . ls = h#t \<and>
    (? h' t' . ls' = h' # t' \<and>
  (ll3_assign_label_list t = Some t' \<and>
  (( h = h' \<and>
    ( ? q e d . h = (q, LLab e d) \<longrightarrow> e = True)) \<or> 
  (? q  e e' lsdec lsdec'' .
    h = (q, LSeq e lsdec) \<and>
    h' = (q, LSeq e' lsdec'') \<and>
    (? lsdec' . ll3_consume_label [] 0 lsdec = Some (lsdec', rev e') \<and>
    ll3_assign_label_list lsdec' = Some lsdec'')
))))))"
  apply(insert ll3_assign_label_preserve_new')
  apply(blast+)
  done
  

(* we need versions of this that work backwards (?) *)
lemma ll3_assign_label_preserve2_gen' :
"(! c h  . length ls > c \<longrightarrow> ls ! c = h \<longrightarrow>
 (! ls' . ll3_assign_label_list ls = Some (ls') \<longrightarrow>
  (? h' . ls' ! c = h' \<and> 
    (( h = h' \<and>
    ( ? q e d . h = (q, LLab e d) \<longrightarrow> e = True)) \<or> 
  (? q e e' lsdec lsdec'' .
    h = (q, LSeq e lsdec) \<and>
    h' = (q, LSeq e' lsdec'') \<and>
    (? lsdec' . ll3_consume_label [] 0 lsdec = Some (lsdec', rev e') \<and>
    ll3_assign_label_list lsdec' = Some lsdec'')
)))))
"
  apply(induction ls)
   apply(auto)

  apply(case_tac "ll3_assign_label ((a, b), ba)", auto)
  apply(case_tac "ll3_assign_label_list ls", auto)

  apply(case_tac c, auto)
    apply(case_tac [1] ba, auto)

     apply(drule_tac ll3_assign_label_preserve1, auto)

    apply(case_tac [1] "ll3_consume_label [] 0 x52", auto)
        apply(rename_tac [1] boo)
    apply(case_tac [1] "ll3_assign_label_list ac", auto)

         apply(drule_tac ll3_assign_label_preserve1, auto)

  apply(case_tac ba, auto)
   apply(drule_tac ll3_assign_label_preserve1) apply(auto)

    apply(case_tac [1] "ll3_consume_label [] 0 x52", auto)
        apply(rename_tac [1] boo)
  apply(case_tac [1] "ll3_assign_label_list ac", auto)
  done

lemma ll3_assign_label_preserve2_gen :
"ll3_assign_label_list ls = Some (ls') \<Longrightarrow>
(! c h  . length ls > c \<longrightarrow> ls ! c = h \<longrightarrow>
  (? h' . ls' ! c = h' \<and> 
    (( h = h' \<and>
    ( ? q e d . h = (q, LLab e d) \<longrightarrow> e = True)) \<or> 
  (? q e e' lsdec lsdec'' .
    h = (q, LSeq e lsdec) \<and>
    h' = (q, LSeq e' lsdec'') \<and>
    (? lsdec' . ll3_consume_label [] 0 lsdec = Some (lsdec', rev e') \<and>
    ll3_assign_label_list lsdec' = Some lsdec'')
))))
"
  apply(insert ll3_assign_label_preserve2_gen')
  apply(blast+)
  done

lemma ll3_assign_label_preserve_new2_gen' :
"(! ls' . ll3_assign_label_list ls = Some (ls') \<longrightarrow>
  (! c  . length ls > c \<longrightarrow> 
  (? h . ls ! c = h \<and>
  (? h' . ls' ! c = h' \<and> 
    (( h = h' \<and>
    ( ? q e d . h = (q, LLab e d) \<longrightarrow> e = True)) \<or> 
  (? q e e' lsdec lsdec'' .
    h = (q, LSeq e lsdec) \<and>
    h' = (q, LSeq e' lsdec'') \<and>
    (? lsdec' . ll3_consume_label [] 0 lsdec = Some (lsdec', rev e') \<and>
    ll3_assign_label_list lsdec' = Some lsdec'')
))))))
"
  apply(induction ls)
  apply(auto)
 apply(case_tac "ll3_assign_label ((a, b), ba)", auto)
  apply(case_tac "ll3_assign_label_list ls", auto)

  apply(case_tac c, auto)
    apply(case_tac [1] ba, auto)

     apply(drule_tac ll3_assign_label_preserve1, auto)

    apply(case_tac [1] "ll3_consume_label [] 0 x52", auto)
        apply(rename_tac [1] boo)
    apply(case_tac [1] "ll3_assign_label_list ac", auto)

         apply(drule_tac ll3_assign_label_preserve1, auto)

  apply(case_tac ba, auto)
   apply(drule_tac ll3_assign_label_preserve1) apply(auto)

    apply(case_tac [1] "ll3_consume_label [] 0 x52", auto)
        apply(rename_tac [1] boo)
  apply(case_tac [1] "ll3_assign_label_list ac", auto)
  done

lemma ll3_assign_label_preserve_new2_gen :
" ll3_assign_label_list ls = Some (ls') \<Longrightarrow>
  (! c  . length ls > c \<longrightarrow> 
  (? h . ls ! c = h \<and>
  (? h' . ls' ! c = h' \<and> 
    (( h = h' \<and>
    ( ? q e d . h = (q, LLab e d) \<longrightarrow> e = True)) \<or> 
  (? q e e' lsdec lsdec'' .
    h = (q, LSeq e lsdec) \<and>
    h' = (q, LSeq e' lsdec'') \<and>
    (? lsdec' . ll3_consume_label [] 0 lsdec = Some (lsdec', rev e') \<and>
    ll3_assign_label_list lsdec' = Some lsdec'')
)))))
"
  apply(insert ll3_assign_label_preserve_new2_gen')
  apply(blast+)
  done

(* this is probably obviated by previous lemma *)
lemma ll3_assign_label_preserve_child2' [rule_format] :
"
(! c aa bb e2  . length ls > c \<longrightarrow> ls ! c = ((aa, bb), llt.LLab e2 0) \<longrightarrow>
 (! p n ls' . ll3_assign_label_list ls = Some (ls') \<longrightarrow>
  ls' ! c = ((aa, bb), llt.LLab e2 0)
))"
proof(induction ls)
  case Nil thus ?case by auto
  case (Cons h t) thus ?case
    apply(auto)
    apply(case_tac "ll3_assign_label h", auto)
apply(case_tac "ll3_assign_label_list t", auto)
    apply(case_tac c, auto)
      apply(case_tac [1] e2, auto)
     apply(case_tac [1] e2, auto)
    apply(case_tac [1] e2, auto)
    done qed

lemma ll3_assign_label_preserve_child2 :
"ll3_assign_label_list ls = Some (ls') \<Longrightarrow>
 length ls > c \<Longrightarrow> ls ! c = ((aa, bb), llt.LLab e2 0) \<Longrightarrow>
 ls' ! c = ((aa, bb), llt.LLab e2 0)"
  apply(drule_tac ll3_assign_label_preserve_child2')
    apply(auto)
  done


lemma ll3'_descend_relabel [rule_format] :
" (x, y, k) \<in> ll3'_descend \<Longrightarrow>
(! q e ls . x = (q, LSeq e ls) \<longrightarrow>
(! e' . ((q, LSeq e' ls), y, k) \<in> ll3'_descend))"
  apply(induction rule:ll3'_descend.induct)
   apply(auto simp add: ll3'_descend.intros)
  apply(case_tac bc, auto)
  apply(drule_tac[1] ll3_hasdesc)  apply(auto)
  apply(drule_tac[1] ll3_hasdesc)  apply(auto)
  apply(drule_tac[1] ll3_hasdesc)  apply(auto)
   apply(drule_tac[1] ll3_hasdesc)  apply(auto)
  apply(rule_tac [1] ll3'_descend.intros) apply(auto)
  done

lemma ll3'_descend_relabelq [rule_format] :
"(x, y, k) \<in> ll3'_descend \<Longrightarrow>
  (! q t . x = (q, t) \<longrightarrow>
    (! q' . ((q', t), y, k) \<in> ll3'_descend))"
  apply(induction rule:ll3'_descend.induct)
   apply(auto simp add:ll3'_descend.intros)
  apply(rule_tac ll3'_descend.intros) apply(auto)
  done

(* we need a seq \<rightarrow> seq version of this lemma** *)
(* do we need to take consume into account here also? *)
(* we need a lemma for the base case about behavior in the
case where a child is a label, kind of like for consume *)
(* do we need to talk about consume label? *)
(* does enew still mean the right thing?
it should be "eold" now *)
(* generalize to all incerceding Seq nodes? 
no - but seq \<rightarrow> seq version should be*)

(* rough sketch of seq \<rightarrow> seq version *)
(* do we need to comibne this and the next lemma? *)
(* look at consume_labels_child* lemmas,
try to do that.
children before descendents.
(Problem: how to characterize seq nodes?)
 *)
(* need "assign_labels_split"? *)
(* First off: need version for _immediate_ child Seq \<rightarrow> Seq
Then we can use that to prove this, or may we we can just
prove the general version after *)

(* need a version for arbitrary LSeq \<rightarrow> X descendents,
where the descendent relation being inducted on is in the tree
after label assignment *)

(* possibly we need my_ll_induct here*)
(* use immediate child for last link *)
(*
lemma ll3_assign_label_preserve_seq' :
" (x, y, k) \<in> ll3'_descend \<Longrightarrow>
(! q e ls' . x = (q, LSeq e ls') \<longrightarrow>
(! q' e' lsdec' . y = (q', LSeq e' lsdec') \<longrightarrow>
(! k' e'' q'' . (y, (q'', LLab e'' (length k + length k' - 1)), k') \<in> ll3'_descend \<longrightarrow>
(! ls eold . ll3_assign_label_list ls = Some ls' \<longrightarrow>
       ((q, LSeq eold ls), (q'', LLab e'' (length k + length k' - 1)), k@k') \<in> ll3'_descend))))
"
  apply(induction rule: ll3'_descend.induct)
   apply(auto)
(*
   apply(case_tac lsa, auto)
  apply(case_tac [1] "ll3_assign_label
              ((aa, ba), bb)", auto)
  apply(case_tac [1] "ll3_assign_label_list
              list", auto)
  apply(case_tac [1] c, auto)
*)
  apply(frule_tac [1] ll3_assign_label_length)
   apply(drule_tac [1] ll3_assign_label_preserve_new2_gen) apply(auto)
  apply(drule_tac [1] x = c in spec) apply(auto)
   apply(subgoal_tac [1]
  "(((a, b), llt.LSeq eold lsa),
        ((ac, bd),
         llt.LLab e'' (length k')),
        [c] @ k')
       \<in> ll3'_descend")
    apply(rule_tac [2] ll3'_descend.intros) apply(auto)
     apply(rule_tac [1] ll3'_descend.intros) apply(auto)

   apply(subgoal_tac [1]
  "(((a, b), llt.LSeq eold lsa (*ls*)),
        ((ac, bd),
         llt.LLab e'' (length k')),
        [c] @ k')
       \<in> ll3'_descend")
     apply(rule_tac [2] ll3'_descend.intros) apply(auto)

apply(rule_tac [1] ll3'_descend_relabel)
    apply(rule_tac[1] ll3'_descend.intros) apply(auto)


 apply(subgoal_tac [1]
  "(((a, b), llt.LSeq eold lsa (*ls*)),
        ((ac, bd),
         llt.LLab e'' (length k')),
        [c] @ k')
       \<in> ll3'_descend")
    apply(rule_tac [2] ll3'_descend.intros) apply(auto)
  (* either our subgoal is wrong or this isn't true *)
apply(rule_tac [1] ll3'_descend_relabel)

    apply(rule_tac[1] ll3'_descend.intros) apply(auto)




(* is this right? i think it is  *)
   apply(subgoal_tac [1]
  "(((a, b), llt.LSeq eold lsa),
        ((ac, bd),
         llt.LLab e'' (length k')),
        [c] @ k')
       \<in> ll3'_descend")
    apply(rule_tac [2] ll3'_descend.intros) apply(auto)

    (* relabel? *)
    (* maybe we need a drule to convert the child into a descendent *)
(*  apply(rule_tac [1] ll3'_descend_relabel) apply(auto) *)
    apply(rule_tac[1] ll3'_descend.intros) apply(auto)

    apply(drule_tac [1] ll3_assign_label_length) apply(auto)
  *)


(* necessary sublemma for valid3' (?) *)
(*
lemma ll3_assign_label_preserve_labels' :
"
  (! e l l' p n . t = (x, LSeq e l) \<longrightarrow> 
   
  ll3_consume_label p n l = Some (l',[]) \<longrightarrow> 
    (\<not> (\<exists> k y e' . 
        ((x, LSeq e l), (y, LLab e' ((List.length k) + (List.length p))), k) \<in> ll3'_descend))) \<and>
  (! l' p  n . ll3_consume_label p n l = Some (l', []) \<longrightarrow> 
      (! n . n < length l \<longrightarrow> (! x l2 e . l!n = (x,LSeq e l2) \<longrightarrow>
      (\<not> (\<exists> k y e' .
        (l!n, (y, LLab e' ((List.length k) + (List.length p) + 1)), k) \<in> ll3'_descend)))))"
*)

(* lemma about how
assign_labels cannot affect the result of a consumes
(does it have to be 0-length?)
i actually don't think it does!
*)

lemma ll3_descend_nonnil :
"(t, t', k) \<in> ll3'_descend \<Longrightarrow>
(? hd tl . k = hd # tl)"
proof(induction rule:ll3'_descend.induct)
  case 1 thus ?case
    apply(auto)
    done next
  case 2 thus ?case
    apply(auto)
    done qed

(* our course of action is still the following:
make a lemma saying that assign_label_list doesn't create
new descendents of the length of a descendece relationship
from any Seq node using that list 

in this one we need to include cases for all possibilities of c: either
- c is unchanged (c = c')
- or c was a label at the appropriate depth that got changed
- or c is a seq node computed from c' by a "consumes" and then an assign_labels*)



lemma haslast2 : 
"l = h # t \<Longrightarrow> ? ch ct . l = ch @ [ct]"
  apply(insert haslast'[of "h#t"])
  apply(auto)
  done

(* a sublemma needed for consume_label_found
note that as written it's not quite right,
we need last/butlast or something
i think what we really need is to generalize to
l1 @ l2, where head # tail is a special case
*)

(*
idea:
- if Seq l1, t1, k1 \in ll3'_descend and
- Seq l2, t2, k2 \in ll3'_descend and
- k2 = h2 # t2 then
- Seq (l1 @ l2), t1, k1 \in ll3'_descend and
- Seq (l1 @ l2), t2, ((h2 + length l1)#t2) \in ll3'_descend
*)

lemma ll3'_descend_cons :
"(t1, t2, k) \<in> ll3'_descend \<Longrightarrow>
 (? q e l . t1 = (q, LSeq e l) \<and> (? kh kt . k = kh # kt \<and>
  (! q' e' h . ((q', LSeq e' (h#l)), t2, (kh+1)#kt) \<in> ll3'_descend)))
"
proof(induction rule:ll3'_descend.induct)
  case (1 c q e ls t)
  then show ?case
    apply(auto simp add:ll3'_descend.intros) done
next
  case (2 t t' n t'' n')
  then show ?case 
    apply(auto)
    apply(subgoal_tac " (((ab, bb), llt.LSeq e' (((ac, bc), bd) # l)),
        t'', (Suc kh # kt) @ (kha # kta))
       \<in> ll3'_descend"
)
    apply(rule_tac[2] ll3'_descend.intros(2)) apply(auto)
done qed

(* should we be talking about ls or ls' here? *)
(* i think in the context of the lemma we are trying to prove,
we want to be talking about ls' *)

(*
Q: should we be talking about the absence of "finds"
in previous children? i imagine we need this at some point,
but maybe it should be a different lemma
*)
(* TODO: do we also need to characterize all the other children? that might be a good thing to add to this theorem
*)
lemma ll3_consume_label_found':
"
(! q e ls .  (t :: ll3) =  (q, LSeq e ls) \<longrightarrow>
(! ls' p p' n . ll3_consume_label p n ls = Some (ls', p' ) \<longrightarrow> p' \<noteq> [] \<longrightarrow>
  ( ? pp k . p' = pp @ k # p \<and> k \<ge> n \<and>
  (? q' . ! e' . ((q, LSeq e' ls), (q', LLab False (length p' - 1)), (k - n)#(rev pp)) \<in> ll3'_descend \<and>
             ((q, LSeq e' ls'), (q', LLab True (length p' - 1)), (k - n)#(rev pp)) \<in> ll3'_descend)
)))
\<and>
(! p n ls' p'  . ll3_consume_label p n ls = Some (ls', p') \<longrightarrow> p' \<noteq> [] \<longrightarrow>
  ( ? pp k . p' = pp @ k # p \<and>
  (? q' . ! q e  . ((q, LSeq e ls), (q', LLab False (length p' - 1)), (k - n)#(rev pp)) \<in> ll3'_descend \<and>
               ((q, LSeq e ls'), (q', LLab True (length p' - 1)), (k - n)#(rev pp)) \<in> ll3'_descend)))
"
proof(induction rule:my_ll_induct)
  case 1 thus ?case by auto next
  case 2 thus ?case by auto next
  case 3 thus ?case by auto next
  case 4 thus ?case by auto next
  case (5 q e l) thus ?case
    apply(auto)  
    apply(drule_tac x = p in spec)
apply(drule_tac x = n in spec)
    apply(frule_tac ll3_consume_label_sane1, auto)
     apply(case_tac q) apply(auto)
    apply(drule_tac x = a in spec) apply(drule_tac x = aa in spec)
     apply(drule_tac x = b in spec) apply(auto) 
  
    apply(case_tac q) apply(auto)
    apply(drule_tac x = a in spec) apply(drule_tac x = aa in spec)
     apply(drule_tac x = b in spec) apply(auto) 
 
    done next
  
  case 6
  then show ?case by auto next
  case (7 h l)
  thus ?case
    apply(auto)
    apply(case_tac h, auto)
    apply(case_tac ba, auto)


        (* L case *)
        apply(case_tac[1] "ll3_consume_label p (Suc n) l", auto)
        apply(frule_tac[1] ll3_consume_label_sane1) apply(simp) apply(auto)

         apply(drule_tac[1] x = p in spec)
    apply(rotate_tac[1] 4)
         apply(drule_tac [1] x = "Suc n" in spec) apply(drule_tac[1] x = aa in spec) apply(drule_tac[1] x = "pp@ k # p" in spec) apply(auto)
         apply(drule_tac [1] x = ab in spec) apply(rotate_tac [1] 4)
         apply(drule_tac [1] x = ba in spec) apply(auto)
    apply(drule_tac [1] x = ac in spec)
          apply(drule_tac [1] x = bb in spec) apply(drule_tac x = e in spec) apply(auto)
    apply(thin_tac[1] "(((ac, bb), llt.LSeq e aa),
        ((ab, ba),
         llt.LLab True (length pp + length p)),
        (k - Suc n) # rev pp)
       \<in> ll3'_descend")
        apply(drule_tac [1] ll3'_descend_cons) apply(auto)
    apply(subgoal_tac "k - n = Suc (k - Suc n)") apply(auto)
         apply(drule_tac[1] x = "ac" in spec)
    apply(drule_tac[1] x = "bb" in spec)
         apply(drule_tac[1] x = "e" in spec) apply(auto)
         apply(thin_tac[1] "
(((ac, bb), llt.LSeq e l),
        ((ab, ba),
         llt.LLab False (length pp + length p)),
        (k - Suc n) # rev pp) \<in> ll3'_descend
")
        apply(drule_tac [1] ll3'_descend_cons) apply(auto)
    apply(drule_tac[1] x = "ac" in spec)
         apply(drule_tac[1] x = "bb" in spec)
         apply(drule_tac[1] x = "e" in spec)
    apply(drule_tac[1] x = "a" in spec)
         apply(drule_tac[1] x = "b" in spec)
         apply(drule_tac[1] x = "llt.L () x12" in spec)
         apply(subgoal_tac [1] "Suc (k - Suc n) = (k) - n")
           apply(auto)

   apply(drule_tac[1] x = p in spec)
    apply(rotate_tac[1] 4)
         apply(drule_tac [1] x = "Suc n" in spec) apply(drule_tac[1] x = aa in spec) apply(drule_tac[1] x = "pp@ k # p" in spec) apply(auto)
         apply(drule_tac [1] x = ab in spec) apply(rotate_tac [1] 4)
         apply(drule_tac [1] x = ba in spec) apply(auto)
    apply(drule_tac [1] x = ac in spec)
          apply(drule_tac [1] x = bb in spec) apply(drule_tac x = e in spec) apply(auto)
    apply(thin_tac[1] "(((ac, bb), llt.LSeq e aa),
        ((ab, ba),
         llt.LLab True (length pp + length p)),
        (k - Suc n) # rev pp)
       \<in> ll3'_descend")
        apply(drule_tac [1] ll3'_descend_cons) apply(auto)
    apply(subgoal_tac "k - n = Suc (k - Suc n)") apply(auto)
         apply(drule_tac[1] x = "ac" in spec)
    apply(drule_tac[1] x = "bb" in spec)
         apply(drule_tac[1] x = "e" in spec) apply(auto)
         apply(thin_tac[1] "
(((ac, bb), llt.LSeq e l),
        ((ab, ba),
         llt.LLab False (length pp + length p)),
        (k - Suc n) # rev pp) \<in> ll3'_descend
")
        apply(drule_tac [1] ll3'_descend_cons) apply(auto)
    apply(drule_tac[1] x = "ac" in spec)
         apply(drule_tac[1] x = "bb" in spec)
         apply(drule_tac[1] x = "e" in spec)
    apply(drule_tac[1] x = "a" in spec)
         apply(drule_tac[1] x = "b" in spec)
         apply(drule_tac[1] x = "llt.L () x12" in spec)
         apply(subgoal_tac [1] "Suc (k - Suc n) = (k) - n")
           apply(auto)

       (* Lab case*)
       apply(case_tac [1] "x22 = length p") apply(auto)
        apply(case_tac [1] "\<not>x21", auto)
    apply(rule_tac[1] x = a in exI) apply(rule_tac [1] x = b in exI) apply(auto simp add:ll3'_descend.intros)

       apply(case_tac [1] "ll3_consume_label p (Suc n) l", auto)
       apply(drule_tac[1] x = p in spec) apply(drule_tac[1] x = "Suc n" in spec) apply(auto)
    apply(drule_tac[1] x = ab in spec) apply(rotate_tac [1] 4) apply(drule_tac x = ba in spec) apply(auto)
         apply(drule_tac[1] x = ac in spec) apply(drule_tac [1] x = bb in spec)
    apply(drule_tac[1] x = e in spec) apply(auto)
        apply(frule_tac[1] ll3_consume_label_sane1) apply(simp) apply(auto)
         apply(drule_tac[1] ll3'_descend_cons) apply(auto)
         apply(drule_tac[1] x = ac in spec) apply(drule_tac [1] x = bb in spec) apply(drule_tac[1] x = e in spec)
    apply(subgoal_tac "k - n = Suc (k - Suc n)")
         apply(auto)
        apply(drule_tac[1] x = ac in spec)
        apply(drule_tac[1] x = bb in spec) apply(drule_tac[1] x = e in spec) apply(auto)
    apply(thin_tac [1]
"(((ac, bb), llt.LSeq e l),
        ((ab, ba), llt.LLab False (length pp + length p)),
        (k - Suc n) # rev pp)
       \<in> ll3'_descend
") apply(frule_tac ll3_consume_label_sane1) apply(simp) apply(auto)
         apply(drule_tac[1] ll3'_descend_cons) apply(auto)
         apply(drule_tac[1] x = ac in spec) apply(drule_tac [1] x = bb in spec) apply(drule_tac[1] x = e in spec)
    apply(subgoal_tac "k - n = Suc (k - Suc n)")
         apply(auto)

       apply(frule_tac[1] ll3_consume_label_sane1) apply(simp)
       apply(drule_tac[1] x = ab in spec) apply(rotate_tac[1] 4) apply(drule_tac[1] x = ba in spec) 
    apply(clarsimp)
        apply(drule_tac[1] x = ac in spec) apply(drule_tac[1] x = bb in spec) apply(drule_tac[1] x = e in spec)
        apply(auto)
    apply(drule_tac[1] ll3'_descend_cons) apply(auto)
        apply(drule_tac [1] x = ac in spec) apply(drule_tac[1] x = bb in spec) apply(drule_tac[1] x = e in spec)
        apply(subgoal_tac "k - n = Suc (k - Suc n)") apply(auto)
    apply(thin_tac [1] "
       (((ac, bb), llt.LSeq e l),
        ((ab, ba), llt.LLab False (length pp + length p)),
        (k - Suc n) # rev pp)
       \<in> ll3'_descend")
        apply(drule_tac[1] ll3'_descend_cons) apply(auto)
        apply(drule_tac [1] x = ac in spec) apply(drule_tac[1] x = bb in spec) apply(drule_tac[1] x = e in spec)
       apply(subgoal_tac "k - n = Suc (k - Suc n)") apply(auto)

      (* Jmp case*)
      apply(case_tac[1] "ll3_consume_label p (Suc n) l", auto)
    apply(frule_tac[1] ll3_consume_label_sane1, auto)
       apply(drule_tac[1] x = p in spec) apply(rotate_tac[1] 4)
       apply(drule_tac[1] x = "Suc n" in spec) apply(auto)
       apply(drule_tac[1] x = ab in spec) apply(rotate_tac[1] 4)
       apply(drule_tac[1] x = ba in spec)
       apply(clarsimp)
       apply(drule_tac x = ac in spec) apply(drule_tac x = bb in spec) apply(drule_tac x = e in spec) apply(auto)
        apply(drule_tac[1] ll3'_descend_cons) apply(auto)
        apply(drule_tac[1] x = ac in spec) apply(drule_tac x = bb in spec) apply(drule_tac x = e in spec) 
        apply(drule_tac [1] x = a in spec) apply(drule_tac x = b in spec) apply(drule_tac x =  "llt.LJmp () x32 x33" in spec)
        apply(subgoal_tac "k - n = Suc (k - Suc n)", auto)
    apply(thin_tac "
 (((ac, bb), llt.LSeq e l),
        ((ab, ba), llt.LLab False (length pp + length p)),
        (k - Suc n) # rev pp) \<in> ll3'_descend
")
       apply(drule_tac[1] ll3'_descend_cons) apply(auto)
       apply(drule_tac [1] x = ac in spec) apply(drule_tac x = bb in spec)
       apply(drule_tac x = e in spec)
       apply(drule_tac[1] x = a in spec) apply(drule_tac x = b in spec)
       apply(drule_tac x =  "llt.LJmp () x32 x33" in spec)
       apply(subgoal_tac "k - n = Suc (k - Suc n)") apply(auto)

      apply(drule_tac x = p in spec) apply(rotate_tac[1] 4) apply(drule_tac x = "Suc n" in spec) apply(clarsimp)
      apply(drule_tac x = ab in spec) apply(rotate_tac[1] 4) apply(drule_tac x = ba in spec) apply(clarsimp)
      apply(drule_tac x = ac in spec) apply(drule_tac x = bb in spec) apply(drule_tac x = e in spec) apply(auto)
       apply(drule_tac [1] ll3'_descend_cons) apply(auto)
    apply(drule_tac x = ac in spec) apply(drule_tac x = bb in spec) apply(drule_tac x = e in spec)
       apply(drule_tac[1] x = a in spec) apply(drule_tac x = b in spec) apply(drule_tac x = "llt.LJmp () x32 x33" in spec)
       apply(subgoal_tac[1] "k - n = Suc (k - Suc n)") apply(auto)
    apply(thin_tac[1] " (((ac, bb), llt.LSeq e l),
        ((ab, ba),
         llt.LLab False (length pp + length p)),
        (k - Suc n) # rev pp)
       \<in> ll3'_descend") apply(drule_tac[1] ll3'_descend_cons) apply(clarsimp)
    apply(drule_tac x = ac in spec) apply(drule_tac x = bb in spec) apply(drule_tac x = e in spec)
       apply(drule_tac[1] x = a in spec) apply(drule_tac x = b in spec) apply(drule_tac x = "llt.LJmp () x32 x33" in spec)
      apply(subgoal_tac[1] "k - n = Suc (k - Suc n)") apply(auto)

(* JmpI case *)
      apply(case_tac[1] "ll3_consume_label p (Suc n) l", auto)
    apply(frule_tac[1] ll3_consume_label_sane1, clarsimp)
       apply(drule_tac[1] x = p in spec) apply(rotate_tac[1] 4)
       apply(drule_tac[1] x = "Suc n" in spec) apply(clarsimp)
       apply(drule_tac[1] x = ab in spec) apply(rotate_tac[1] 4)
       apply(drule_tac[1] x = ba in spec)
     apply(clarsimp) apply(auto)
      apply(drule_tac x = ac in spec) apply(drule_tac x = bb in spec) apply(drule_tac x = e in spec) apply(auto)
    apply(drule_tac ll3'_descend_cons) apply(clarsimp)
       apply(drule_tac x = ac in spec) apply(drule_tac x = bb in spec) apply(drule_tac x = e in spec) 
        apply(drule_tac [1] x = a in spec) apply(drule_tac x = b in spec) apply(drule_tac x =  "llt.LJmpI () x42 x43" in spec)
        apply(subgoal_tac "ka - n = Suc (ka - Suc n)", auto)
     apply(drule_tac x = ac in spec) apply(drule_tac x = bb in spec) apply(drule_tac x = e in spec) apply(auto)
    apply(thin_tac[1] "(((ac, bb), llt.LSeq e l),
        ((ab, ba),
         llt.LLab False (length ppa + length p)),
        (ka - Suc n) # rev ppa)
       \<in> ll3'_descend")
    apply(drule_tac ll3'_descend_cons) apply(clarsimp)
       apply(drule_tac x = ac in spec) apply(drule_tac x = bb in spec) apply(drule_tac x = e in spec) 
        apply(drule_tac [1] x = a in spec) apply(drule_tac x = b in spec) apply(drule_tac x =  "llt.LJmpI () x42 x43" in spec)
        apply(subgoal_tac "ka - n = Suc (ka - Suc n)", auto)

(* Seq case *)
    apply(case_tac[1] "ll3_consume_label (n # p) 0 x52", auto)
    apply(case_tac[1] ba, auto)

     apply(case_tac[1] " ll3_consume_label p (Suc n) l", auto)
    apply(thin_tac[1] "\<forall>ls' p p' n.
          ll3_consume_label p n x52 = Some (ls', p') \<longrightarrow>
          p' \<noteq> [] \<longrightarrow>
          (\<exists>pp k.
              p' = pp @ k # p \<and>
              n \<le> k \<and>
              (\<exists>aa ba.
                  \<forall>e'. (((a, b), llt.LSeq e' x52),
                        ((aa, ba), llt.LLab False (length p' - Suc 0)),
                        (k - n) # rev pp)
                       \<in> ll3'_descend \<and>
                       (((a, b), llt.LSeq e' ls'),
                        ((aa, ba), llt.LLab True (length p' - Suc 0)),
                        (k - n) # rev pp)
                       \<in> ll3'_descend))")
     apply(drule_tac[1] x = p in spec)
     apply(drule_tac[1] x = "Suc n" in spec) apply(clarsimp)
    apply(drule_tac[1] x = ac in spec) apply(rotate_tac[1] 4) apply(drule_tac[1] x = ba in spec) apply(clarsimp)
     apply(drule_tac[1] x = ad in spec) apply(drule_tac x = bb in spec) apply(drule_tac x = e in spec) apply(clarsimp)
     apply(drule_tac[1] ll3'_descend_cons) apply(clarsimp)
     apply(drule_tac[1] ll3'_descend_cons) apply(clarsimp)
    apply(thin_tac[1] "ll3_consume_label (n # p) 0 x52 = Some (aa, [])")
    apply(drule_tac[1] ll3_consume_label_sane1) apply(clarsimp)
     apply(drule_tac[1] x = ad in spec) apply(drule_tac x = ad in spec)
     apply(drule_tac[1] x = bb in spec) apply(drule_tac x = bb in spec)
     apply(drule_tac[1] x = e in spec) apply(drule_tac[1] x = e in spec)
     apply(drule_tac[1] x = a in spec) apply(drule_tac[1] x = a in spec)
     apply(drule_tac[1] x = b in spec) apply(drule_tac[1] x = b in spec)
     apply(drule_tac[1] x = "LSeq x51 x52" in spec)
     apply(clarsimp)
     apply(subgoal_tac[1] "k - n = Suc (k - Suc n)", auto)

    apply(thin_tac[1] "
 \<forall>p n ls' p'.
          ll3_consume_label p n l = Some (ls', p') \<longrightarrow>
          p' \<noteq> [] \<longrightarrow>
          (\<exists>pp k.
              p' = pp @ k # p \<and>
              (\<exists>a b. \<forall>aa ba e.
                        (((aa, ba), llt.LSeq e l),
                         ((a, b), llt.LLab False (length p' - Suc 0)),
                         (k - n) # rev pp)
                        \<in> ll3'_descend \<and>
                        (((aa, ba), llt.LSeq e ls'),
                         ((a, b), llt.LLab True (length p' - Suc 0)),
                         (k - n) # rev pp)
                        \<in> ll3'_descend))")
    apply(drule_tac[1] x = aa in spec)
    apply(drule_tac[1] x = "n#p" in spec)
    apply(frule_tac[1] ll3_consume_label_sane1, clarsimp)
    apply(drule_tac[1] x = "ab#list" in spec)
    apply(drule_tac[1] x = 0 in spec) apply(clarsimp)
    apply(drule_tac[1] x = x51 in spec) apply(clarsimp)
    apply(rule_tac[1] x = ac in exI) apply(rule_tac[1] x = ba in exI) apply(auto)
    apply(subgoal_tac[1]
"(((ad, bb), llt.LSeq e (((a, b), llt.LSeq x51 x52) # l)),
        ((ac, ba), llt.LLab False (length list)), [0] @ (k # rev pp))
       \<in> ll3'_descend")
    apply(simp)
     apply(rule_tac[1] ll3'_descend.intros(2))
    apply(rule_tac[1] ll3'_descend.intros(1)) apply(auto)
    apply(subgoal_tac[1] "(((ad, bb), llt.LSeq e (((a, b), llt.LSeq x51 aa) # l)),
        ((ac, ba), llt.LLab True (length list)), [0] @ (k # rev pp))
       \<in> ll3'_descend") apply(simp)
     apply(rule_tac[1] ll3'_descend.intros(2))
     apply(rule_tac[1] ll3'_descend.intros(1)) apply(auto)
    done qed

lemma ll3_consume_label_found:
"
(ll3_consume_label p n ls = Some (ls', p') \<Longrightarrow> p' \<noteq> [] \<Longrightarrow>
  (? pp k . p' = pp @ k # p \<and>
  (? q' . ! q e  . ((q, LSeq e ls), (q', LLab False (length p' - 1)), (k - n)#(rev pp)) \<in> ll3'_descend \<and>
               ((q, LSeq e ls'), (q', LLab True (length p' - 1)), (k - n)#(rev pp)) \<in> ll3'_descend)))
"
  apply(insert ll3_consume_label_found') apply(clarsimp)
  done


(* add something about uniqueness of k? *)
(* or at least somehow describe the fact that we didn't see this label in previous children *)
lemma ll3_assign_labels_backwards_fact :
" (x, y, k) \<in> ll3'_descend \<Longrightarrow>
(! q e ls' . x = (q, LSeq e ls') \<longrightarrow>
(! q' c' . y = (q', c') \<longrightarrow>
(* ll3_consumes premise here? *)
(! ls enew . ll3_assign_label_list ls = Some ls' \<longrightarrow>
   (? c . ((q, LSeq enew ls), (q', c), k) \<in> ll3'_descend \<and>
(* returned thing should only have true labels *)
      (c = c' \<or>
        (* Q: does this case only work for True? do we want/need this case? *)
(*       (? n . c = LLab True n \<and> c' = LLab True n \<and> n + 1 \<ge> length k) \<or> *)
(* i am skeptical about this case too, it probably needs revision *)
       (? n . c = LLab False n \<and> c' = LLab True n \<and> n + 1 < length k) \<or>
       (* idea here: 
          1. do some consumes on lsdec to get lsdec2
          2. do consume_label normal call on lsdec2 to get lsdec3
          3. do assign_label on lsdec3 to get lsdec4
       *)
       (? edec edec' lsdec lsdec2 lsdec3 lsdec4 cs . 
          c = LSeq edec lsdec \<and> c' = LSeq edec' lsdec4 \<and>

(* Q: do we need to talk about the max depth of these consumes? *)
          (lsdec, cs, lsdec2) \<in> ll3_consumes \<and>
          ll3_consume_label [] 0 lsdec2 = Some (lsdec3, rev edec') \<and>
          ll3_assign_label_list lsdec3 = Some lsdec4)
      )
))))
"
proof(induction rule:ll3'_descend.induct)
  case (1 c q e ls t)
  then show ?case
    apply(auto) 
    apply(frule_tac[1] ll3_assign_label_preserve_new2_gen)
     apply(drule_tac[1] ll3_assign_label_length) apply(auto)
    apply(drule_tac[1] x = c in spec)
    apply(auto)
        apply(drule_tac[1] x = "c'" in spec) apply(auto)
    apply(subgoal_tac[1] "((q, llt.LSeq enew lsa), ((a, b), c'), [c])
       \<in> ll3'_descend") apply(rule_tac[2] ll3'_descend.intros(1)) apply(auto)

        apply(drule_tac[1] x = "c'" in spec) apply(auto)
    apply(subgoal_tac[1] "((q, llt.LSeq enew lsa), ((a, b), c'), [c])
       \<in> ll3'_descend") apply(rule_tac[2] ll3'_descend.intros(1)) apply(auto)

        apply(drule_tac[1] x = "c'" in spec) apply(auto)
    apply(subgoal_tac[1] "((q, llt.LSeq enew lsa), ((a, b), c'), [c])
       \<in> ll3'_descend") apply(rule_tac[2] ll3'_descend.intros(1)) apply(auto)

     apply(rule_tac[1] x = "c'" in exI) apply(auto)
     apply(rule_tac[1] ll3'_descend.intros(1)) apply(auto)

         apply(rule_tac[1] x = "llt.LSeq e lsdec" in exI) apply(auto)
     apply(rule_tac[1] ll3'_descend.intros(1)) apply(auto)
     apply(drule_tac[1] x = lsdec in spec) apply(auto)
      apply(subgoal_tac[1] "(lsdec, [], lsdec) \<in> ll3_consumes")
      apply(rule_tac[2] ll3_consumes.intros) apply(auto)

    apply(drule_tac[1] x = lsdec in spec) apply(auto)
      apply(subgoal_tac[1] "(lsdec, [], lsdec) \<in> ll3_consumes")
     apply(rule_tac[2] ll3_consumes.intros) apply(auto)
    done next

   
  case (2 t t' n t'' n')
  then show ?case
    apply(auto)
    apply(case_tac t', auto) apply(case_tac bba, auto)
        apply(drule_tac[1] ll3_hasdesc2)
        apply(drule_tac[1] ll3_hasdesc2, auto)
       apply(drule_tac[1] ll3_hasdesc2)
       apply(drule_tac[1] ll3_hasdesc2, auto)
       apply(drule_tac[1] ll3_hasdesc2)
      apply(drule_tac[1] ll3_hasdesc2, auto)
       apply(drule_tac[1] ll3_hasdesc2)
     apply(drule_tac[1] ll3_hasdesc2, auto)

    apply(case_tac[1] c', auto)
    apply(rotate_tac [1] 2)
        apply(drule_tac[1] x = ls in spec) apply(auto)
        apply(drule_tac[1] x = enew in spec) apply(auto)
         apply(auto simp add:ll3'_descend.intros)
        apply(drule_tac[1] x = lsdec3 in spec) apply(auto)
      (* the issue now becomes dispatching this consumes fact
         this seems to suggest we might need a bound on consumes depth after all
         or can we otherwise characterize the consumes list
*)  (* case split on x51 (returned path of last consumes call? *)
        apply(case_tac x51) apply(auto)
    apply(frule_tac[1] ll3_consume_label_unch) apply(clarsimp)
    apply(rotate_tac[1] 6)
         apply(rule_tac[1] ll3'_descend.intros) apply(simp)
        apply(auto simp add:ll3'_descend.intros)

        apply(drule_tac x = ls in spec) apply(auto)
         apply(drule_tac x = enew in spec) apply(auto)
    apply(auto simp add:ll3'_descend.intros)

    apply(case_tac ls, auto)
    apply(drule_tac[1] x = 
    sorry
qed
   (* This lemma seems like a key point right now *)
(* Is the issue that we should be characterizing
all LLab descendents, not just some? *)

lemma ll3_assign_label_preserve_labels' :
" (x, y, k) \<in> ll3'_descend \<Longrightarrow>
(! q e ls' . x = (q, LSeq e ls') \<longrightarrow>
(! q' e' . y = (q', LLab e' (length k - 1)) \<longrightarrow>
(! ls enew . ll3_assign_label_list ls = Some ls' \<longrightarrow>
       ((q, LSeq enew ls), (q', LLab e' (length k - 1)), k) \<in> ll3'_descend)))
"


(* TODO: this lemma is needed by the valid3' proof but we don't
have the necessary sublemmas to prove it yet *)
(* also i wonder if this will need to interact with consumes in some way? 
maybe that is where the bound on consumes comes in.*)
lemma ll3_assign_label_preserve_labels' :
" (x, y, k) \<in> ll3'_descend \<Longrightarrow>
(! q e ls' . x = (q, LSeq e ls') \<longrightarrow>
(! q' e' . y = (q', LLab e' (length k - 1)) \<longrightarrow>
(! ls enew . ll3_assign_label_list ls = Some ls' \<longrightarrow>
       ((q, LSeq enew ls), (q', LLab e' (length k - 1)), k) \<in> ll3'_descend)))
"
proof(induction rule:ll3'_descend.induct)
  case (1 c q e ls t)
  then show ?case
    apply(auto  simp add:ll3'_descend.intros)
  apply(rule_tac[1] ll3'_descend.intros) 
     apply(frule_tac [1] ll3_assign_label_length) apply(auto)
apply(frule_tac [1] ll3_assign_label_length)
    apply(drule_tac[1] ll3_assign_label_preserve_new2_gen) apply(auto)
    done
next
  case (2 t t' n t'' n')
  then show ?case 
    apply(auto)
    apply(case_tac t', auto)

    apply(case_tac bba, auto)
      apply(drule_tac[1] ll3_hasdesc) 
          apply(drule_tac[1] ll3_hasdesc) apply(auto)
apply(drule_tac[1] ll3_hasdesc) 
         apply(drule_tac[1] ll3_hasdesc) apply(auto)
apply(drule_tac[1] ll3_hasdesc) 
        apply(drule_tac[1] ll3_hasdesc) apply(auto)
apply(drule_tac[1] ll3_hasdesc) 
       apply(drule_tac[1] ll3_hasdesc) apply(auto)
apply(drule_tac[1] ll3_hasdesc) 
      apply(drule_tac[1] ll3_hasdesc) apply(auto)



          (*apply(case_tac ls, auto)*)

           apply(drule_tac[1] ll3_hasdesc2) apply(auto)

    apply(case_tac [1] "ll3_assign_label ((ac, bc), bd)", auto)
    apply(case_tac[1] "ll3_assign_label_list list", auto)
  apply(drule_tac[1] ll3_hasdesc)  apply(auto)
  apply(drule_tac[1] ll3_hasdesc)  
         apply(drule_tac[1] ll3_hasdesc)  apply(auto)
  apply(drule_tac[1] ll3_hasdesc) 
  apply(drule_tac[1] ll3_hasdesc)  apply(auto)
  apply(drule_tac[1] ll3_hasdesc)  
  apply(drule_tac[1] ll3_hasdesc)  apply(auto)
  apply(drule_tac[1] ll3_hasdesc) 
      apply(drule_tac[1] ll3_hasdesc)  apply(auto)
 
     
     apply(rule_tac[1] ll3'_descend.intros) apply(auto)
    
    apply(drule_tac[1] ll3'_descend_relabelq) apply(simp)
    apply(drule_tac[1] ll3'_descend_relabel) apply(auto)
  (* idea ? - this is transitivity
     we should combine the two descends facts,
and then use a lemma about descends (?) 
no, that is just the same theorem again *)


    
    sorry
qed
  apply(induction rule:ll3'_descend.induct)
   apply(auto  simp add:ll3'_descend.intros)
  apply(rule_tac[1] ll3'_descend.intros) 
    apply(frule_tac [1] ll3_assign_label_length) apply(auto)
   apply(frule_tac[1] ll3_assign_label_length)

    apply(drule_tac[1] ll3_assign_label_preserve_new2_gen) apply(auto)


  apply(case_tac [1] bc, auto)
  apply(drule_tac[1] ll3_hasdesc) 
  apply(drule_tac[1] ll3_hasdesc)  apply(auto)
  apply(drule_tac[1] ll3_hasdesc)  
  apply(drule_tac[1] ll3_hasdesc)  apply(auto)
  apply(drule_tac[1] ll3_hasdesc)  
  apply(drule_tac[1] ll3_hasdesc)  apply(auto)
  apply(drule_tac[1] ll3_hasdesc)  
  apply(drule_tac[1] ll3_hasdesc)  apply(auto)
  apply(drule_tac[1] ll3_hasdesc)  
    apply(drule_tac[1] ll3_hasdesc)  apply(auto)

(*
    apply(drule_tac[1] ll3_assign_label_preserve_new2_gen) apply(auto)
*)

  apply(frule_tac [1] ll3_assign_label_preserve_new2) apply(auto)

    apply(drule_tac[1] ll3_hasdesc2) apply(auto)

       apply(case_tac[1] "ll3_assign_label ((ab, bc), bd)", auto)
(* speculative *)
  apply(case_tac [1] n, auto) apply(case_tac a, auto)
  apply(case_tac [1] "ll3_assign_label_list list", auto)

  apply(rule_tac [1] ll3'_descend.intros)
   apply(auto)

    (* we need a version of preserve_child2 that goes "backwards"
       i.e. if a particular label existed after it existed before *)
    (* what we are calling child3, maybe child4 *)

  apply(case_tac[1] "bc", auto)
        apply(drule_tac[1] ll3_hasdesc) apply(drule_tac[1] ll3_hasdesc) apply(auto)
       apply(drule_tac[1] ll3_hasdesc) apply(drule_tac[1] ll3_hasdesc) apply(auto)
      apply(drule_tac[1] ll3_hasdesc) apply(drule_tac[1] ll3_hasdesc) apply(auto)
     apply(drule_tac[1] ll3_hasdesc) apply(drule_tac[1] ll3_hasdesc) apply(auto)
    apply(drule_tac[1] ll3_hasdesc) apply(drule_tac[1] ll3_hasdesc) apply(auto)

    (* we need a lemma about descendents of ll3_assign_label_list *)
      apply(drule_tac[1] ll3_assign_label_preserve_new2_gen) apply(auto)


    (* we need reverse *)
   apply(drule_tac [1] ll3'_descend_relabel) apply(auto)

    apply(drule_tac[1] ll3_assign_label_preserve_new2_gen) apply(auto)


  apply(case_tac [1] lsa, auto)
  (* it looks like we need some proof about preservation
   of the descendent relation, after all *)
  apply(auto simp add: ll3'_descend.intros)

   apply(drule_tac [1] ll3_assign_label_preserve_child3_0) apply(auto)


   apply(drule_tac [1] ll3_assign_label_preserve_child2) apply(auto)
  (* is this part true? *)
   apply(rule_tac [1] ll3'_descend.intros) apply(auto)

  apply(case_tac bc, auto)
  apply(drule_tac[1] ll3_hasdesc) apply(drule_tac[1] ll3_hasdesc) apply(auto)
  apply(drule_tac[1] ll3_hasdesc) apply(drule_tac[1] ll3_hasdesc) apply(auto)
  apply(drule_tac[1] ll3_hasdesc) apply(drule_tac[1] ll3_hasdesc) apply(auto)
  apply(drule_tac[1] ll3_hasdesc) apply(drule_tac[1] ll3_hasdesc) apply(auto)
    apply(drule_tac[1] ll3_hasdesc) apply(drule_tac[1] ll3_hasdesc) apply(auto)

  (* we need a lemma for seq \<rightarrow> seq paths (like for consumes) *)

   apply(subgoal_tac [1] "(((ac, bf), llt.LSeq enew ls), ((aa, bb), llt.LSeq x51 x52), n) \<in> ll3'_descend")
    apply(rule_tac [2] ll3'_descend_relabel) apply(auto)
  apply(rule_tac [1] ll3'_descend.intros) apply(auto)
  apply(rotate_tac [1] 1)
  (* we need a "relabeling" lemma for ll3'_descend, saying that we can
     change the annotation on the root Seq node *)
  apply(drule_tac [1] 
 "ll3'_descend_relabel"[of x]) apply(auto)  


    apply(rule_tac [2] ll3'_descend.intros)

    apply(case_tac [1] "ll3_assign_label ((a, b), ba)", auto)
  apply(case_tac [1] "ll3_assign_label_list list", auto)

   apply(case_tac [1] enew, auto)
  apply(case_tac [1] "ll3_assign_label
              ((aa, ba), bb)", auto)
  apply(case_tac [1] "ll3_assign_label_list
              list", auto)
    apply(case_tac [1] c, auto)
    
   apply(auto  simp add:ll3'_descend.intros)


(* do we need to use descend instead of set? *)
(* maybe not, but maaybe we can use "!" operator *)
(* s'@p' ?*)
(* is our use of "consumes" here reasonable? *)
(* do we need to bound the consumes depth here? *)
lemma ll3_assign_label_valid3' :
"((q,t::ll3t) \<in> ll_valid_q \<longrightarrow> 
    ((! q' t' . ll3_assign_label (q,t) = Some (q',t') \<longrightarrow> q = q' \<and> (q',t') \<in> ll_valid3')
\<and>  ((! e l . t = LSeq e l \<longrightarrow> (! s l' . (l,s,l') \<in> ll3_consumes \<longrightarrow>
                     (! p'' l'' . ll3_consume_label [] 0 l' = Some (l'', p'') \<longrightarrow>
                     (! l''' . ll3_assign_label_list l'' = Some l''' \<longrightarrow> 
                          (q, LSeq p'' l''') \<in> ll_valid3')))))))
\<and> (((x,x'), (ls:: ll3 list)) \<in> ll_validl_q \<longrightarrow> 
     (!p n  s ls' . (ls,s,ls') \<in> ll3_consumes \<longrightarrow>
                     (! ls'' . ll3_assign_label_list ls' = Some ls'' \<longrightarrow> 
                        (! k . k \<in> (set ls'') \<longrightarrow>  (k \<in> ll_valid3')))))"

proof(induction rule:ll_valid_q_ll_validl_q.induct)
case (1 i x e)
  then show ?case
    apply(auto simp add:ll_valid3'.intros) done
next
  case (2 x d e)
  then show ?case
    apply(auto simp add:ll_valid3'.intros)
    apply(drule_tac [1] ll3_assign_label_unch1, auto)
     apply(drule_tac [1] ll3_assign_label_unch1, auto)
    apply(case_tac e, auto)
    apply(auto simp add:ll_valid3'.intros)
    done
next
  case (3 x d e s)
  then show ?case 
        apply(auto simp add:ll_valid3'.intros)
    done
next
  case (4 x d e s)
  then show ?case
    apply(auto simp add:ll_valid3'.intros)
    done
next
  case (5 n l n' e)
  then show ?case 
    apply(auto simp add:ll_valid3'.intros)
       apply(case_tac "ll3_consume_label [] 0 l", auto)
       apply(case_tac "ll3_assign_label_list aa", auto)
       apply(case_tac "ll3_consume_label [] 0 l", auto)
      apply(case_tac "ll3_assign_label_list aa", auto)
       apply(case_tac "ll3_consume_label [] 0 l", auto)
     apply(case_tac "ll3_assign_label_list aa", auto)
 
     apply(case_tac ba, auto)
    apply(drule_tac [1] x = "[]" in spec)
      apply(drule_tac [1] x = "aa" in spec) apply(auto)
       apply(drule_tac [1] ll3_consumes.intros) apply(auto)

    apply(frule_tac [1] ll3_consume_label_unch, auto)

    apply(rule_tac[1] ll_valid3'.intros(5)[of _ _ _ "[]"])
    apply(auto)
       apply(drule_tac [1] ll3_assign_label_qvalid2, auto)

      apply(frule_tac[1] ll3'_descend.cases) apply(auto)
       apply(frule_tac[1] ll3_consume_label_find, auto)
    apply(drule_tac[1] x = "[]" in spec) apply(auto)

       apply(drule_tac [1] x = ac in spec) apply(drule_tac x = bb in spec)
       apply(drule_tac[1] x = "llt.LLab e' 0" in spec)
    apply(frule_tac[1] List.nth_mem) apply(auto)
    apply(subgoal_tac[1] "((ac, bb), llt.LLab e' 0) \<in> set ls") apply(auto)
      apply(frule_tac[1] ll3_descend_nonnil, auto)

      apply(drule_tac[1] x = "[]" in spec) apply(clarsimp)

      apply(frule_tac[1] ll3_assign_labels_backwards_fact) apply(auto)
      apply(drule_tac[1] x = l in spec) apply(auto)
(* preserve_labels' works but we can't prove it yet
is there something more general that would work here? *)
      apply(frule_tac [1] ll3_assign_label_preserve_labels')
      apply(auto)
      apply(drule_tac [1] x = l in spec) apply(auto)
      apply(drule_tac [1] x = "[]" in spec)
    apply(thin_tac[1] "(((n, n'), llt.LSeq [] ab),
        ((a, b), llt.LLab e' (length k - Suc 0)), k)
       \<in> ll3'_descend")

      apply(frule_tac [1] ll3_consume_label_find)
      apply(auto)
      apply(drule_tac [1] x = "[]" in spec) apply(auto)
      apply(frule_tac [1] ll3_descend_nonnil) apply(auto)
(* we finished this part! *)
(* now on to more fun *)
    (* we need consume_label_found here. however, first it's probably
worth it to expose the induction hypothesis as we need that too *)
  
    apply(frule_tac [1] ll3_consume_label_found, simp)
     apply(auto)
     apply(rule_tac[1] ll_valid3'.intros(6)) apply(clarsimp)
    (* need q validity here *)

    apply(drule_tac [1] x = "[(ch @ [ct], 0)]" in spec)
    apply(drule_tac [1] x = "aa" in spec) apply(

(* ok, we just changed
valid3' so that it doesn't assume labels are true in the non nil case
we probably need some kind of "uniqueness" lemma for ll3_assign_labels
showing that other labels at that depth get weeded out in the form of a nil result
(unless this happens automatically somehow)
*)

    (* we need a consume_label_found fact, characterizing the existence
       of the consumed node, when non nil returned
something modeled after
(*
lemma ll3_consume_label_find :
"(l1, l2, k) \<in> ll3'_descend \<Longrightarrow>
 (! x1 e1 l1l . l1 = (x1, LSeq e1 l1l) \<longrightarrow>
 (! x2 e2 d . l2 = (x2, LLab e2 d) \<longrightarrow>
 (! p n l1l' . ll3_consume_label p n l1l = Some (l1l', []) \<longrightarrow>
 d + 1 \<noteq> length k + length p)))
"
*)
    *)
    (* we also have to prove that if assign_label_list returned Some,
       there are no other nodes at that depth *)
    apply(frule_tac[1] ll3_consume_label_find)

     apply(rule_tac[1] ll_valid3'.intros(6)[of _ _ _ "rev list @[a]"])
        apply(case_tac [1] "(n,n')", simp)


    (* another possible option here?
     we know each child of our Seq node is valid
*)

(* speculative work *)
      apply(rule_tac[2] ll_valid3'.intros(6)[of _ _ _ []]) 

    apply(frule_tac [1] ll3_assign_label_preserve_new2)




(* speculative work on subsequent goals *)
      apply(rule_tac [2] ll_valid3'.intros)
    apply(case_tac [2]
  (* another idea for what we might need here
     descendents of the result of calling assign_label_list
     that are labels
     the _same exact_ label node
     will be a descendent of the original

    then we need to use consume_label_find (or something like it)
    to derive a contradiction
*)

(* we need a "assign_label_list_sane" lemma about how
 the only changes possible in calling assign label list are adding
labels to seq nodes, and changing labels of things with sufficiently small
path specs (?)*)
    sorry
next
  case (6 n)
  then show ?case sorry
next
  case (7 n h n' t n'')
  then show ?case sorry
qed


fun ll3_unwrap :: "(ll3 list \<Rightarrow> 'a option) \<Rightarrow> ll3  \<Rightarrow> 'a option" where
  "ll3_unwrap f (_, LSeq _ ls) = f ls"
  | "ll3_unwrap _ (_, _) = None"
 
value "(ll3_init (ll_pass1 (ll1.LSeq [ll1.LLab 0])))"
value "ll3_assign_label (ll3_init (ll_pass1 (ll1.LSeq [ll1.LLab 0])))"
value "ll3_assign_label (ll3_init (ll_pass1 (ll1.LSeq [ll1.LSeq [ll1.LLab 0], ll1.LSeq [], ll1.LSeq [ll1.LLab 1]])))"

(* get the label at the provided childpath, if it exists *)
(* TODO: should we check to make sure this label is the right one? *)
(* TODO: we can generalize this, not just make ll3 specific *)
(* TODO apply this to a node, not a list (?) *)
(*
fun ll3_get_label :: "ll3 list \<Rightarrow> childpath \<Rightarrow> nat option" where
    "ll3_get_label (((x,_),LLab _ _)#_) (0#_) = Some x"
  | "ll3_get_label ((_, LSeq _ lsdec)#ls) (0#p) = 
     ll3_get_label lsdec p"
  | "ll3_get_label (_#ls) (0#_) = None"
  | "ll3_get_label (_#ls) (n#p) = 
     ll3_get_label (ls) ((n-1)#p)"
  | "ll3_get_label _ _ = None"
*)

fun ll_get_label :: "('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll list \<Rightarrow> childpath \<Rightarrow> nat option" where
    "ll_get_label (((x,_),LLab _ _)#_) (0#_) = Some x"
  | "ll_get_label ((_, LSeq _ lsdec)#ls) (0#p) = 
     ll_get_label lsdec p"
  | "ll_get_label (_#ls) (0#_) = None"
  | "ll_get_label (_#ls) (n#p) = 
     ll_get_label (ls) ((n-1)#p)"
  | "ll_get_label _ _ = None"

definition prog1 where
  "prog1 = ll3_assign_label (ll3_init (ll_pass1 (ll1.LSeq [ll1.LLab 0])))"

value prog1
  
definition prog2 where
  "prog2 = ll3_assign_label (ll3_init (ll_pass1 (ll1.LSeq [ll1.L (Arith ADD), ll1.LLab 0])))"  
  
value "(case prog2 of
        Some (_, LSeq _ lsdec) \<Rightarrow> ll3_get_label lsdec [1]
        | _ \<Rightarrow> None)"

definition src3 where
"src3 = ll1.LSeq [ll1.LSeq [ll1.LLab 0], ll1.LSeq [ll1.LJmp 1], ll1.LSeq [ll1.LLab 1]]"

definition prog3 where
"prog3 = ll3_assign_label (ll3_init (ll_pass1 (
ll1.LSeq [ll1.LSeq [ll1.LLab 0], ll1.LSeq [ll1.LJmp 1], ll1.LSeq [ll1.LLab 1]])))"
 
value prog3

(* now we go to ll4, we are getting ready to put in jump targets *)
fun ll4_init :: "ll3 \<Rightarrow> ll4" where
 "ll4_init (x, L e i) = (x, L e i)"
| "ll4_init (x, LLab e idx) = (x, LLab e idx)"
| "ll4_init (x, LJmp e idx s) = (x, LJmp 0 idx s)"
| "ll4_init (x, LJmpI e idx s) = (x, LJmpI 0 idx s)"
| "ll4_init (x, LSeq e ls) = (x, LSeq e (map ll4_init ls))"

(* resolve_jump routine, for once we know the label location *)
(* Idea: for any jump we find, we check if it is big enough to store what we want
   If it is not, then we need to rebuild the entire tree and try again *)
(* idea: we once again build a childpath as we go, so that if we must bail out,
   we know where to enlarge the node *)
(* the nat this takes as input will be read out of the label node.
   label resolution should have already taken place for this to work. *)

datatype jump_resolve_result =
  JSuccess
  | JFail "childpath"
  | JBump "childpath"
  
(* need a function to get number of bytes needed to encode a
   location *)
value "(Evm.log256floor 2048) + 1"

definition encode_size :: "nat \<Rightarrow> nat" where
  "encode_size n = (nat (Evm.log256floor (Int.int n)) + 1)"

(* declaring this makes the termination prover blow up *)  
(*declare encode_size_def [simp]  *)

(* this should take an ll4 *)
(*  TODO everything from here onward should take ll4 *)
(* make this mutually recursive with a "consume" function?  *)
(* the first nat argument is a location in buffer,
   the second is the current child index 
   the first nat should be optional, that is, None if there is
   no label at that node
*)
(* NB the childpath output by this function ought to be reversed *)
(* NB LJmpI also needs to be handled *)
(* TODO: add another argument that is the "previously resolved" childpath? *)
(* should we do a "jump"/"jumps" split again? seems like a good idea *)
fun ll3_resolve_jump :: "ll3 list \<Rightarrow> nat option \<Rightarrow> nat \<Rightarrow> childpath \<Rightarrow> childpath \<Rightarrow> jump_resolve_result" where
  (* TODO: does this handle returning the childpath correctly? should it be n#c?*)
  "ll3_resolve_jump ((_, LJmp e idx s)#ls) None n rel absol = 
   (if idx + 1 = length rel then JFail (n#absol)
    else ll3_resolve_jump ls None (n+1) rel absol)"

| "ll3_resolve_jump ((_, LJmp e idx s)#ls) (Some addr) n rel absol =
     (if idx (*+ 1*) = length rel then
        (if s < encode_size addr then JBump (n#absol) else
         if s = encode_size addr then ll3_resolve_jump ls (Some addr) (n + 1) rel absol
        else JFail (n#absol))
        else ll3_resolve_jump ls (Some addr) (n+1) rel absol)"

|  "ll3_resolve_jump ((_, LJmpI e idx s)#ls) None n rel absol = 
   (if idx + 1 = length rel then JFail (n#absol)
    else ll3_resolve_jump ls None (n+1) rel absol)"

| "ll3_resolve_jump ((_, LJmpI e idx s)#ls) (Some addr) n rel absol =
     (if idx (*+ 1*) = length rel then
        (if s < encode_size addr then JBump (n#absol) else
         if s = encode_size addr then ll3_resolve_jump ls (Some addr) (n + 1) rel absol
        else JFail (n#absol))
        else ll3_resolve_jump ls (Some addr) (n+1) rel absol)"

 | "ll3_resolve_jump ((_, LSeq [] lsdec)#ls') oaddr n rel absol =
     (* first we resolve the descendents' labels relative to where we were *)
     (case ll3_resolve_jump lsdec oaddr 0 (n#rel) (n#absol) of
     JSuccess \<Rightarrow> (* now we resolve the descendents' relative labels *)
                 (* for this we need to obtain label target, but there may not be one
                    if there isn't one we still need to check for failing jumps, but i think this does that*)
      (case ll3_resolve_jump lsdec None 0 [] (n#absol) of
       JSuccess \<Rightarrow> (* now we resolve neighbors *) ll3_resolve_jump ls' oaddr (n+1) rel absol
       | JFail c \<Rightarrow> JFail c
       | JBump c \<Rightarrow> JBump c)
     | JFail c \<Rightarrow> JFail c
     | JBump c \<Rightarrow> JBump c)"

| "ll3_resolve_jump ((_, LSeq e lsdec)#ls') oaddr n rel absol =
   (case ll3_resolve_jump lsdec oaddr 0 (n#rel) (n#absol) of
    JSuccess \<Rightarrow> 
    (case ll_get_label lsdec e of
        Some newaddr \<Rightarrow> (case ll3_resolve_jump lsdec (Some newaddr) 0 [] (n#absol) of
                      JSuccess \<Rightarrow> ll3_resolve_jump ls' oaddr (n+1) rel absol
                      | JFail c \<Rightarrow> JFail c
                      | JBump c \<Rightarrow> JBump c)
       | None \<Rightarrow> JFail absol)
    | JFail c \<Rightarrow> JFail c
    | JBump c \<Rightarrow> JBump c)"

  | "ll3_resolve_jump (h#ls) oaddr n rel absol =
     ll3_resolve_jump ls oaddr (n + 1) rel absol"
  | "ll3_resolve_jump [] _ _ _ _ = JSuccess"
(*
fun ll3_resolve_jump :: "ll3 list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> childpath \<Rightarrow> jump_resolve_result" where
  (* TODO: does this handle returning the childpath correctly? should it be n#c?*)
  "ll3_resolve_jump ((_, LJmp e idx s)#ls) addr n c =
     (if idx + 1 = length c then
        (if s < encode_size addr then JBump c else
         if s = encode_size addr then ll3_resolve_jump ls addr (n + 1) c
        else JFail c)
        else ll3_resolve_jump ls addr (n+1) c)"
   
| "ll3_resolve_jump ((_, LSeq e lsdec)#ls') addr n c =
     (case ll3_resolve_jump lsdec addr 0 (n#c) of
     JSuccess \<Rightarrow> ll3_resolve_jump ls' addr (n+1) c
     | JFail c \<Rightarrow> JFail c
     | JBump c \<Rightarrow> JBump c)"

  | "ll3_resolve_jump (h#ls) addr n c =
     ll3_resolve_jump ls addr (n + 1) c"
  | "ll3_resolve_jump [] _ _ _ = JSuccess"
*)
(* TODO: later replace this bump routine with a general bump *)    

(* this will call get label target *)
fun ll3_resolve_jump_wrap :: "ll3 \<Rightarrow> jump_resolve_result" where
"ll3_resolve_jump_wrap (x, LSeq e lsdec) =
   (case e of [] \<Rightarrow> ll3_resolve_jump lsdec None 0 [] []
    | e \<Rightarrow> (case ll_get_label lsdec e of
             Some a \<Rightarrow> ll3_resolve_jump lsdec (Some a) 0 [] []
           | None \<Rightarrow> JFail []))"
| "ll3_resolve_jump_wrap _ = JFail []"

value prog3

value "(case prog3 of
        Some l \<Rightarrow> ll3_resolve_jump_wrap l
        | _ \<Rightarrow> JFail [666])"

fun ll3_bump :: "nat \<Rightarrow> ll3 list \<Rightarrow> ll3 list" where
    "ll3_bump n (((x,x'), LSeq e lsdec)#ls') = ((x+n,x'+n),LSeq e (ll3_bump n lsdec))#(ll3_bump n ls')"
  | "ll3_bump n (((x,x'), t)#ls') = ((x+n, x'+n),t)#(ll3_bump n ls')"
  | "ll3_bump n [] = []"
    
(* once we find the offending jump, increment it *)
(* we need to return a qan defining new size things for the overall list *)
(* do we take a qan? or at least a bool showing whether we grew in that sublist *)    
fun ll3_inc_jump :: "ll3 list \<Rightarrow> nat \<Rightarrow> childpath \<Rightarrow> ll3 list * bool" where 
    (* TODO: select jump based on childpath *)
    "ll3_inc_jump (((x,x'), LJmp e idx s)#ls) n [c] = 
     (if n = c then
     (((x,x'+1), LJmp e idx (s+1))#(ll3_bump 1 ls), True)
       else (case ll3_inc_jump ls (n+1) [c] of
                  (ls', b) \<Rightarrow> (((x,x'), LJmp e idx s)#(ls'), b)))"
  | "ll3_inc_jump (((x,x'), LJmpI e idx s)#ls) n [c] = 
     (if n = c then
     (((x,x'+1), LJmpI e idx (s+1))#(ll3_bump 1 ls), True)
       else (case ll3_inc_jump ls (n+1) [c] of
                  (ls', b) \<Rightarrow> (((x,x'), LJmpI e idx s)#(ls'), b)))"
  (* TODO: should we use computed lsdec' or old lsdec in failure to find case *)
  | "ll3_inc_jump (((x,x'), LSeq e lsdec)#ls) n (c#cs) =
     (if n = c then case ll3_inc_jump lsdec 0 cs of
       (lsdec', True) \<Rightarrow> (((x,x'+1), LSeq e lsdec')#(ll3_bump 1 ls), True)
       | (lsdec', False) \<Rightarrow> (case ll3_inc_jump ls n (c#cs) of
                             (ls', b) \<Rightarrow> ((((x,x'), LSeq e lsdec')#ls'), b))
      else case ll3_inc_jump ls (n+1) (c#cs) of
       (ls', b) \<Rightarrow> (((x,x'), LSeq e lsdec)#ls', b))"
  | "ll3_inc_jump (h#ls) n c = (case (ll3_inc_jump ls (n + 1) c) of
                                  (ls', b) \<Rightarrow> (h#ls', b))"
  | "ll3_inc_jump [] _ _ = ([], False)"

fun ll3_inc_jump_wrap :: "ll3 \<Rightarrow> childpath \<Rightarrow> ll3" where
 "ll3_inc_jump_wrap ((x,x'), LSeq e lsdec) c =
  (case ll3_inc_jump lsdec 0 c of
   (lsdec', True) \<Rightarrow> ((x,x'+1), LSeq e lsdec')
  |(lsdec', False) \<Rightarrow> ((x,x'), LSeq e lsdec))
  "
|"ll3_inc_jump_wrap T _ = T"
    
value "(case prog3 of
        Some (_, LSeq e lsdec) \<Rightarrow> ll3_get_label lsdec e
        | _ \<Rightarrow> None)"
  
value "(case prog3 of
        Some (_, LSeq _ lsdec) \<Rightarrow> Some (ll3_inc_jump lsdec 0 [1,0])
        | _ \<Rightarrow> None)"

value "Word.word_rsplit ((Word256.word256FromNat 0) :: 256 word) :: 8 word list" 

fun process_jumps_loop :: "nat \<Rightarrow> ll3 \<Rightarrow> ll3 option" where
  "process_jumps_loop 0 _ = None"
| "process_jumps_loop n ls = 
   (case ll3_resolve_jump_wrap ls of
    JSuccess \<Rightarrow> Some ls
  | JFail _ \<Rightarrow> None
  | JBump c \<Rightarrow> process_jumps_loop (n - 1) (ll3_inc_jump_wrap ls (rev c)))"

value "(case prog3 of
        Some l \<Rightarrow> process_jumps_loop 40 l
        | _ \<Rightarrow> None)"

value "(case prog3 of
        Some l \<Rightarrow> (case (process_jumps_loop 40 l) of
                       Some l \<Rightarrow> Some (ll4_init l)
                       | _ \<Rightarrow> None)
        | _ \<Rightarrow> None)"


(* have a ll3_resolve_jumps_list *)
(* combine ll3_resolve_jump with ll3_inc_jump *)
(* we also need to use get_label to get the label location *)
(* take a nat and a childpath? we need to track where we
   are among descendents in the tree so we can reconstruct
   the "bump" command *)
(* first nat is fuel *)
(*
fun ll3_resolve_jumps :: "nat \<Rightarrow> ll3 \<Rightarrow> ll3 option" and
    ll3_resolve_jumps_list :: "nat \<Rightarrow> ll3 list \<Rightarrow> ll3 list option" where
  "ll3_resolve_jumps 0 _ = None"
| "ll3_resolve_jumps n (x, LSeq p []) = Some (x, LSeq p [])"
| "ll3_resolve_jumps n (x, LSeq p (h#ls)) =
   ((case ll3_get_label (h#ls) p of
     Some n \<Rightarrow> case ll3_resolve_jump (h#ls) n 0 [] of
      JSuccess \<Rightarrow> Some (n, LSeq) (* jsuccess means we need to add to childpath and process sublist, resolving sub jumps
                                    if any of them bump, we need to restart *)
      (* jbump means bump and restart *)
    | None \<Rightarrow> None))"  

| "ll3_resolve_jumps n ("
*)
(* finally, we resolve all jumps. for now, this will be fuelled, later we'll prove
   termination *)
(* do we need an ll4 init?
   maybe we don't, we can just use a childpath-stack to track which label is which address *)
(* should this return an ll4? yes *)
(* idea: putting the parts together.
   we require that labels have been assigned
   steps (should be separate functions?)
   1: call resolve_jump
      - bump if we need to, try to resolve again (fuelled)
      - pass result onto next stage
   1a: ll4 init?
   2: call write_jump_targets
      - if success, we get the thing

*)

fun mynth :: "'a option list \<Rightarrow> nat \<Rightarrow> 'a option" where
    "mynth [] _ = None"
  | "mynth (h#t) 0 = h"
  | "mynth (h#t) n = mynth t (n-1)"

fun mypeel :: "'a option list \<Rightarrow> 'a list option" where
"mypeel [] = Some []"
| "mypeel (None#_) = None"
| "mypeel ((Some h)#t) = (case mypeel t of
                          Some t' \<Rightarrow> Some (h#t')
                         | None \<Rightarrow> None)"

(* here we have a list of addresses, accumulated by labels as we go *)
fun write_jump_targets :: "nat option list \<Rightarrow> ll4 \<Rightarrow> ll4 option" where
"write_jump_targets ns ((x, x'), LSeq [] lsdec) = 
  (case (mypeel (map (write_jump_targets (None#ns)) lsdec)) of
   Some lsdec' \<Rightarrow> Some ((x,x'), LSeq [] lsdec')
  | None \<Rightarrow> None)"
| "write_jump_targets ns ((x,x'), LSeq loc lsdec) =
  (case ll_get_label lsdec loc of
    Some addr \<Rightarrow> (case (mypeel (map (write_jump_targets ((Some addr)#ns)) lsdec)) of
                  Some lsdec' \<Rightarrow> Some ((x,x'), LSeq loc lsdec')
                 | None \<Rightarrow> None)
    | None \<Rightarrow> None)"
| "write_jump_targets ns ((x,x'), LJmp _ idx sz) = 
  (case mynth ns idx of
   Some a \<Rightarrow> Some ((x,x'), LJmp a idx sz)
  | None \<Rightarrow> None)"
| "write_jump_targets ns ((x,x'), LJmpI _ idx sz) = 
  (case mynth ns idx of
   Some a \<Rightarrow> Some ((x,x'), LJmpI a idx sz)
  | None \<Rightarrow> None)"
| "write_jump_targets _ T = Some T"

value "(case prog3 of
        Some l \<Rightarrow> (case (process_jumps_loop 40 l) of
                       Some l \<Rightarrow> write_jump_targets [] (ll4_init l)
                       | _ \<Rightarrow> None)
        | _ \<Rightarrow> None)"
(* ll3_resolve_jumps :: "ll3 list \<Rightarrow> ll4 list"*)

value "Word.word_of_int 1 :: 1 word"
value "Evm.byteFromNat 255"

value "Divides.divmod_nat 255 256"

(* TODO ensure these are coming out in the right order *)
(* TODO this terminates because divmod decreases number *)
function output_address :: "nat \<Rightarrow> 8 word list" where
    "output_address n = (case Divides.divmod_nat n 256 of
                         (0, mo) \<Rightarrow> [Evm.byteFromNat mo]
                        |(Suc n, mo) \<Rightarrow> (Evm.byteFromNat mo)#(output_address (Suc n)))"
  by auto
termination sorry

(* use word256FromNat to get w256
   then use word_rsplit245 *)
definition bytes_of_nat :: "nat \<Rightarrow> 8 word list" where
  "bytes_of_nat n = Word.word_rsplit (Word256.word256FromNat n)"

fun codegen' :: "ll4 \<Rightarrow> inst list" where
    "codegen' (_, (L _ i)) = [i]"
  | "codegen' (_, (LLab _ _)) = [Pc JUMPDEST]"
  | "codegen' (_, (LJmp a _ s)) =
     (Evm.inst.Stack (PUSH_N (output_address a))) #[Pc JUMP]"
  | "codegen' (_, (LJmpI a _ _)) =
     (Evm.inst.Stack (PUSH_N (output_address a))) #[Pc JUMPI]"
  | "codegen' (_, (LSeq _ ls)) = List.concat (map codegen' ls)"
     
definition codegen :: "ll4 \<Rightarrow> 8 word list" where
"codegen ls = List.concat (map Evm.inst_code (codegen' ls))"

definition pipeline' :: "ll1 \<Rightarrow> nat \<Rightarrow> ll4 option" where
"pipeline' l n = 
 (case (ll3_assign_label (ll3_init (ll_pass1 l))) of
  Some l' \<Rightarrow> (case process_jumps_loop n l' of
              Some l'' \<Rightarrow> (case write_jump_targets [] (ll4_init l'') of
                           Some l''' \<Rightarrow> Some (l''')
                          | None \<Rightarrow> None)
             | None \<Rightarrow> None)
  | None \<Rightarrow> None)"

(* nat argument is fuel to give to jump resolver *)
definition pipeline :: "ll1 \<Rightarrow> nat \<Rightarrow> 8 word list option" where
"pipeline l n = 
 (case pipeline' l n of
  Some l' \<Rightarrow> Some (codegen l')
  | None \<Rightarrow> None)"

value "pipeline' src3 20"


value "pipeline src3 20"

definition progif :: ll1 where
"progif =
ll1.LSeq [
ll1.LSeq [
ll1.L ( Stack (PUSH_N [0])),
ll1.LJmpI 0,
ll1.L (Stack (PUSH_N [1])),
ll1.LJmp 1,
ll1.LLab 0,
ll1.L (Stack (PUSH_N [2])),
ll1.LLab 1
]]
"

value "pipeline' progif 30"
value "pipeline progif 30"
(* idea: *)
(* for final codegen pass, use stack_inst.PUSH_N
   *)
(* before going further with paths, we need some path utilities
   (inspired by Huet's Zippers paper)
 *)
  
   

