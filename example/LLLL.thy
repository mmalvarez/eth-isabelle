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

type_synonym ll2t =
  "(unit, unit, unit, unit, unit, unit, unit) llt"

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



(* get the label at the provided childpath, if it exists *)
type_synonym childpath = "nat list"

(* Q: better to return None or Some in nil case?
   (i.e., return None and then make the base case part of get list) *)
fun ll_get_node :: "('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll \<Rightarrow> childpath \<Rightarrow> ('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll option" and
    ll_get_node_list :: "('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll list \<Rightarrow> childpath \<Rightarrow> ('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll option" where
    "ll_get_node T [] = Some T"
  | "ll_get_node (q, LSeq e ls) p = 
     ll_get_node_list ls p"
  | "ll_get_node _ _ = None"

| "ll_get_node_list _ [] = None" (* this should never happen *)
| "ll_get_node_list [] _ = None" (* this case will happen when *)
  | "ll_get_node_list (h#ls) (0#p) = ll_get_node h p"
  | "ll_get_node_list (_#ls) (n#p) = 
     ll_get_node_list (ls) ((n-1)#p)"

(* TODO: maybe have a function for "reifying" a ll \<Rightarrow> childpath \<Rightarrow> ll function
back into an ll? I guess we just need to pass it nil. *)

value "ll_get_node ((0,0), ((llt.LSeq () [((0,0),llt.LLab () 0), ((0,0),llt.LLab () 1)]))::ll2t) [1]"

(* alternate definition of descend, good in certain situations *)
inductive_set ll_descend_alt  :: "(('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll * ('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll * childpath) set" where
"\<And> t t' kh kt . ll_get_node t (kh#kt) = Some t' \<Longrightarrow>
(t, t', kh#kt) \<in> ll_descend_alt"

inductive_set ll3'_descend_alt  :: "(('lix, 'ljx, 'ljix, 'ptx, 'pnx) ll3' * ('lix, 'ljx, 'ljix, 'ptx, 'pnx) ll3' * childpath) set"
where
"\<And> t t' kh kt . ll_get_node t (kh#kt) = Some t' \<Longrightarrow>
(t, t', kh#kt) \<in> ll3'_descend_alt"


(* TODO: later generalize this to all lls, for now we are avoiding type annoyances by not *)
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

lemma ll_get_node_len [rule_format] :
"(! kh kt t' . ll_get_node_list ts (kh#kt) = Some t' \<longrightarrow> kh < length ts)"
proof(induction ts)
case Nil
then show ?case by auto
next
  case (Cons a ts)
  then show ?case 
    apply(auto)
    apply(case_tac kh) apply(auto) 
    apply(drule_tac[1] x = nat in spec) apply(auto)
    done
qed

lemma ll_get_node_nth [rule_format] :
"(! kh t' . ll_get_node_list ts [kh] = Some t' \<longrightarrow>
    ts ! kh = t')"
proof(induction ts)
case Nil
then show ?case by auto
next
  case (Cons a ts)
  then show ?case apply(auto)
    apply(case_tac kh) apply(auto)
    done
qed

lemma ll_get_node_nth2 [rule_format] :
"(! kh . kh < length ts \<longrightarrow> 
 (! t' . ts ! kh = t' \<longrightarrow>
  ll_get_node_list ts [kh] = Some t'))"
proof(induction ts)
  case Nil
  then show ?case by auto
next
  case (Cons a ts)
  then show ?case 
    apply(auto)
    apply(case_tac kh) apply(auto)
    done
qed

(* version of this for last child? *)
lemma ll_get_node_child [rule_format] :
"(! kh kt t' . ll_get_node_list ts (kh#kt) = Some t' \<longrightarrow>
   (kh < length ts \<and>
   ll_get_node (ts ! kh) kt = Some t'))"
proof(induction ts)
case Nil
  then show ?case by auto
next
  case (Cons a ts)
  then show ?case
    apply(auto) apply(case_tac kh, auto)
    apply(case_tac kh, auto) 
    done
qed

(* need converse of previous lemma, to prove last-child lemma *)
lemma ll_get_node_child2 [rule_format] :
"(! t kh kt t' . ll_get_node t kt = Some t' \<longrightarrow>
    kh < length ts \<longrightarrow>
    ts ! kh = t \<longrightarrow>
    ll_get_node_list ts (kh#kt) = Some t'
)"
proof(induction ts)
case Nil
then show ?case by auto
next
  case (Cons a ts)
  then show ?case
    apply(auto)
    apply(case_tac kh, auto)
    done
qed

lemma ll_get_node_last [rule_format] :
"(! t kl t'' . ll_get_node t (k@[kl]) = Some t'' \<longrightarrow>
    (? t' . ll_get_node t k = Some t' \<and>
           ll_get_node t' [kl] = Some t''))
"
proof(induction k)
case Nil
then show ?case by auto
next
  case (Cons a k)
  then show ?case
    apply(auto)
    apply(case_tac ba, auto)
    apply(frule_tac[1] ll_get_node_child)
    apply(case_tac "x52 ! a", auto)
    apply (drule_tac x = ab in spec) apply(drule_tac x = b in spec) apply(drule_tac[1] x = ba in spec)
    apply(drule_tac x = kl in spec)
    apply(auto)
    apply(rule_tac x = aba in exI) apply(rule_tac x = bd in exI) apply(rule_tac x = be in exI)
    apply(auto)
    apply(case_tac k, auto) apply(rule_tac[1] ll_get_node_nth2) apply(auto)
    apply(thin_tac "ll_get_node ((ab, b), ba) (ac # list @ [kl]) =
       Some ((aa, bb), bc)")
    apply(drule_tac ll_get_node_child2) apply(auto)
    done
qed

lemma ll_get_node_last2 [rule_format] :
"((! t t' . ll_get_node t k = Some t' \<longrightarrow>
    (! t'' kl . ll_get_node t' [kl] = Some t'' \<longrightarrow>
    ll_get_node t (k@[kl]) = Some t'')))
"
proof(induction k)
case Nil
  then show ?case by auto
next
  case (Cons a k)
  then show ?case
    apply(auto)
    apply(case_tac ba, auto)
    apply(frule_tac ll_get_node_child, auto)
    apply(case_tac "x52 ! a", auto)
    apply(drule_tac x = ac in spec) apply(drule_tac x = b in spec) apply(drule_tac x = ba in spec)
    apply(auto)
    apply(drule_tac x = ab in spec) apply(drule_tac x = bd in spec) apply(drule_tac x = be in spec) apply(drule_tac x = kl in spec)
    apply(clarsimp)
    apply(thin_tac "ll_get_node ((ac, b), ba) k =
       Some ((aa, bb), bc)")
    apply(thin_tac "ll_get_node ((aa, bb), bc) [kl] =
       Some ((ab, bd), be)")
    apply(frule_tac ll_get_node_child2) apply(auto)
    done qed


lemma ll_descend_eq_l2r [rule_format] :
"(! t kh t' . ll_get_node t (kh#kt) = Some t' \<longrightarrow>
(t, t', kh#kt) \<in> ll3'_descend)"
proof(induction kt)
  case Nil
  then show ?case
    apply(auto)
    apply(case_tac ba, auto)
    apply(rule_tac[1] ll3'_descend.intros(1))
     apply(auto simp add:ll_get_node_len)
    apply(auto simp add:ll_get_node_nth)
    done
next
  case (Cons a kt)
  then show ?case
    apply(auto)
    apply(case_tac ba) apply(auto)
    apply(frule_tac[1] ll_get_node_len)

    apply(subgoal_tac[1] 
      " (((aa, b), llt.LSeq x51 x52),
        ((aaa, bb), bc), [kh] @ (a # kt))
       \<in> ll3'_descend")
     apply(rule_tac[2] ll3'_descend.intros(2)) apply(auto)
    apply(rule_tac[1] ll3'_descend.intros) apply(auto)
    apply(case_tac x52, auto) 
    apply(drule_tac[1] ll_get_node_child)
    apply(case_tac[1] "(((ab, b), ba) # list) ! kh", auto)
    done
qed

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

lemma ll_get_node_comp [rule_format] :
"(! t' t'' . ll_get_node t' p' = Some t'' \<longrightarrow>
  (! t p . ll_get_node t p = Some t' \<longrightarrow>
   ll_get_node t (p@p') = Some t''))
"     
proof(induction p')
  case Nil
  then show ?case by auto
next
  case (Cons a p)
  then show ?case
    apply(auto)
    apply(case_tac ba, auto)
    apply(frule_tac[1] ll_get_node_child)
    apply(case_tac[1] "x52 ! a") apply(auto)
    apply(drule_tac x = ac in spec) apply(drule_tac x = ba in spec) apply(drule_tac[1] x = baa in spec)
    apply(auto)
    apply(drule_tac x = ab in spec) apply(drule_tac x = bd in spec) apply(drule_tac x = be in spec)
    apply(drule_tac x = "pa @ [a]" in spec) apply(clarsimp)
    apply(thin_tac[1] "ll_get_node ((ac, ba), baa) p =
       Some ((aaa, bb), bc)")
    apply(drule_tac[1] ll_get_node_last2) apply(auto)
    apply(rule_tac ll_get_node_nth2) apply(auto)
    done qed



lemma ll_descend_eq_r2l :
"((q, t), (q', t'), k) \<in> ll3'_descend \<Longrightarrow>
ll_get_node (q, t) k = Some (q', t')"
proof(induction rule:ll3'_descend.induct)
  case (1 c q e ls t)
  then show ?case
    apply(auto)
    apply(frule_tac[1] ll_get_node_nth2, auto)
    done
next
  case (2 t t' n t'' n')
  then show ?case 
    apply(frule_tac[1] ll3_descend_nonnil)
    apply(auto) apply(rotate_tac[1] 1)
    apply(frule_tac[1] ll3_descend_nonnil) apply(auto)

    apply(subgoal_tac " ll_get_node t ((hd # tl) @ (hda # tla)) =
       Some t''")

     apply(rule_tac[2] ll_get_node_comp) apply(auto)
    done qed

lemma ll_descend_eq_l2r2 :
"x \<in> ll3'_descend_alt \<Longrightarrow> x \<in> ll3'_descend"
  apply(case_tac x) apply(auto)
  apply(drule_tac[1] ll3'_descend_alt.cases) apply(auto)
  apply(drule_tac ll_descend_eq_l2r) apply(auto)
  done

lemma ll_descend_eq_r2l2 :
"x \<in> ll3'_descend \<Longrightarrow> x \<in> ll3'_descend_alt"
  apply(case_tac x) apply(auto)
  apply(frule_tac ll3_descend_nonnil)
  apply(drule_tac ll_descend_eq_r2l) apply(auto)
  apply(rule_tac ll3'_descend_alt.intros) apply(auto)
  done

lemma ll_descend_eq :
"ll3'_descend = ll3'_descend_alt"
  apply(insert ll_descend_eq_l2r2)
  apply(insert ll_descend_eq_r2l2)
  apply(blast)
  done
 

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
                 (! z . z \<in> set l \<longrightarrow> z \<in> ll_valid3') \<Longrightarrow>
                 (\<not> (\<exists> k y e' . ((x, LSeq e l), (y, LLab e' (List.length k - 1)), k) \<in> ll3'_descend)) \<Longrightarrow>
                 (x, (LSeq [] l)) \<in> ll_valid3'"

  | "\<And> x l e  k y. (x, l) \<in> ll_validl_q \<Longrightarrow>
                (! z . z \<in> set l \<longrightarrow> z \<in> ll_valid3') \<Longrightarrow>
                (((x, LSeq e l), (y, LLab True (List.length k - 1)), k) \<in> ll3'_descend) \<Longrightarrow>
                (! k' y' b . (((x, LSeq e l), (y', LLab b (List.length k' - 1)), k') \<in> ll3'_descend) \<longrightarrow> k = k') \<Longrightarrow>
                (x, LSeq k l) \<in> ll_valid3'"


(* dump an l2 to l3, marking all labels as unconsumed *)
fun ll3_init :: "ll2 \<Rightarrow> ll3" where
  "ll3_init (x, L e i) = (x, L e i)"
| "ll3_init (x, LLab e idx) = (x, LLab False idx)"
| "ll3_init (x, LJmp e idx s) = (x, LJmp e idx s)"
| "ll3_init (x, LJmpI e idx s) = (x, LJmpI e idx s)"
| "ll3_init (x, LSeq e ls) = 
   (x, LSeq [] (map ll3_init ls))"


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

lemma cp_less_least :
"cp_less p k \<Longrightarrow> k \<noteq> []"
  apply(induction rule:cp_less.induct)
    apply(auto)
  done
type_synonym consume_label_result = "(ll3 list * childpath) option"

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

(* Predicate describing a series of changes in a list induced by ll3_consume_label calls *)
(* Another option: store lists rather than sets, but make assertions about sets of childpath * nat *)
inductive_set ll3_consumes :: "(ll3 list * (childpath * nat) list * ll3 list) set" where
"\<And> l . (l,[],l) \<in> ll3_consumes"
| "\<And> p n l l' . ll3_consume_label p n l = Some (l', []) \<Longrightarrow> (l,[],l') \<in> ll3_consumes"
| "\<And> p n l l' k pp . ll3_consume_label p n l = Some (l', pp@(k#p))  \<Longrightarrow> (l,[(pp@[k - n], length p)], l') \<in> ll3_consumes"
| "\<And> l s l' s' l'' . (l,s,l') \<in> ll3_consumes \<Longrightarrow>
      (l',s', l'') \<in> ll3_consumes \<Longrightarrow> 
      (l,s @ s',l'') \<in> ll3_consumes"

(* runnable version of ll3_consumes so we can define consumes alt,
uses dummy parameters to consumes *)
(* we may also later want a version that can run backward *)
(* should we use consume_label for this, or walk it ourselves? *)
fun ll3_do_consumes :: "ll3 list \<Rightarrow> (childpath * nat) list \<Rightarrow> ll3 list option" where
"ll3_do_consumes l [] = Some l"
| "ll3_do_consumes l ((p,d)#t) =
   (case ll3_consume_label (List.replicate d 0) 0 l of
      None \<Rightarrow> None
    | Some (l', p') \<Rightarrow> 
      (if p' = [] then None
     (* this isn't quite right, should be drop or something *)
       else if List.take (length p' - d) p' = p then ll3_do_consumes l' t
            else None))
"

inductive_set ll3_consumes_alt :: "(ll3 list * (childpath * nat) list * ll3 list) set" where
"\<And> l cs l' . ll3_do_consumes l cs = Some l' \<Longrightarrow> (l, cs, l') \<in> ll3_consumes_alt"


lemma haslast' :
"l = [] \<or> (? fi la . l = fi@[la])"
proof(induction l)
  case Nil thus ?case by auto
  case (Cons h t) thus ?case
    apply(auto) 
    done qed

lemma haslast2 : 
"l = h # t \<Longrightarrow> ? ch ct . l = ch @ [ct]"
  apply(insert haslast'[of "h#t"])
  apply(auto)
  done



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

lemma ll3_consumes_alt_eq_l2r [rule_format] :
"(! l l' . ll3_do_consumes l cs = Some l' \<longrightarrow> (l, cs, l') \<in> ll3_consumes)"
  apply(induction cs)
   apply(auto simp add:ll3_consumes.intros)
  apply(case_tac "ll3_consume_label (replicate b 0) 0 l", auto)
  apply(case_tac ba, auto)
  apply(case_tac "take (Suc (length list) - b) (ab # list) = a", auto)
  apply(subgoal_tac "(l, ([(take (Suc (length list) - b) (ab # list), b)]) @ cs, l') \<in> ll3_consumes")
   apply(rule_tac[2] ll3_consumes.intros) apply(auto)
  apply(frule_tac ll3_consume_label_char) apply(auto)
  apply(drule_tac ll3_consumes.intros) apply(auto)
  apply(case_tac pp, auto)
  done

lemma ll3_consume_nil_gen' :
"(! q p n e l l' . (t::ll3) = (q, LSeq e l) \<longrightarrow> ll3_consume_label p n l = Some (l', []) \<longrightarrow>
  (! p' n' . length p = length p' \<longrightarrow> ll3_consume_label p' n' l = Some (l, [])))
\<and> (! p n ls' . ll3_consume_label p n ls = Some (ls', []) \<longrightarrow>
  (! p' n' . length p = length p' \<longrightarrow> ll3_consume_label p' n' ls = Some (ls, [])))"
  apply(induction rule:my_ll_induct, auto 0 0)
  apply(case_tac ba, auto 0 0)
       apply(case_tac [1] "ll3_consume_label p (Suc n) l", auto 0 0)
apply(case_tac [1] "ll3_consume_label p' (Suc n') l", auto 0 0)
         apply(drule_tac [1] x = p in spec) apply(auto 0 0)

         apply(drule_tac [1] x = p in spec) apply(auto 0 0)
         apply(drule_tac [1] x = p in spec) apply(auto 0 0)

       apply(case_tac [1] "ll3_consume_label p (Suc n) l", auto 0 0)
apply(case_tac [1] "ll3_consume_label p' (Suc n') l", auto 0 0)
      apply(drule_tac [1] x = p in spec) apply(auto 0 0)
       apply(drule_tac [1] x = p in spec) apply(auto 0 0)
      apply(drule_tac [1] x = p in spec) apply(auto 0 0)

       apply(case_tac [1] "ll3_consume_label p (Suc n) l", auto 0 0)
apply(case_tac [1] "ll3_consume_label p' (Suc n') l", auto 0 0)
      apply(drule_tac [1] x = p in spec) apply(auto 0 0)
      apply(drule_tac [1] x = p in spec) apply(auto 0 0)
      apply(drule_tac [1] x = p in spec) apply(auto 0 0)

       apply(case_tac [1] "ll3_consume_label p (Suc n) l", auto 0 0)
apply(case_tac [1] "ll3_consume_label p' (Suc n') l", auto 0 0)
       apply(drule_tac [1] x = p in spec) apply(auto 0 0)
      apply(drule_tac [1] x = p in spec) apply(auto 0 0)
      apply(drule_tac [1] x = p in spec) apply(auto 0 0)

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

(* need a none_gen *)

lemma ll3_consume_none_gen' :
"(! q p n e l . (t::ll3) = (q, LSeq e l) \<longrightarrow> ll3_consume_label p n l = None \<longrightarrow>
  (! p' n' . length p = length p' \<longrightarrow> ll3_consume_label p' n' l = None))
\<and> (! p n . ll3_consume_label p n ls = None \<longrightarrow>
  (! p' n' . length p = length p' \<longrightarrow> ll3_consume_label p' n' ls = None))"
  apply(induction rule:my_ll_induct)
        apply(auto)
  apply(case_tac ba, auto)

       apply(case_tac "ll3_consume_label p (Suc n) l", auto)
     apply(case_tac "ll3_consume_label p (Suc n) l", auto)
       apply(case_tac "ll3_consume_label p (Suc n) l", auto)
       apply(case_tac "ll3_consume_label p (Suc n) l", auto)
       apply(case_tac "ll3_consume_label p (Suc n) l", auto)

  apply(case_tac[1] "ll3_consume_label (n # p) 0 x52", auto)
  apply(case_tac ba, auto)
  apply(case_tac "ll3_consume_label p (Suc n) l", auto)

  apply(case_tac " ll3_consume_label (n' # p') 0 x52", auto)
  apply(case_tac ba, auto)
  apply(drule_tac[1] p' = "n'#p'" and n' = 0 in ll3_consume_nil_gen) apply(auto)
  done


lemma ll3_consume_none_gen :
"ll3_consume_label p n ls = None \<Longrightarrow>
  length p = length p' \<Longrightarrow> ll3_consume_label p' n' ls = None"
  apply(insert ll3_consume_none_gen')
  apply(blast+)
  done


(* this statement isn't quite right *)
(* need to generalize each side more? *)
lemma ll3_consume_gen' [rule_format] :
"(! q e l . (t::ll3) = (q, LSeq e l) \<longrightarrow> 
    (! p n l' pp k p . ll3_consume_label p n l = Some (l', pp @ k # p) \<longrightarrow>
    (! p' . length p = length p' \<longrightarrow> (! n' . ll3_consume_label p' n' l = Some (l', pp@(k-n+n')#p')))))
\<and> (! p n ls' pp k . ll3_consume_label p n ls = Some (ls', pp @ k # p) \<longrightarrow>
  (! p'  . length p = length p' \<longrightarrow> (! n' . ll3_consume_label p' n' ls = Some (ls', pp @ (k-n+n')#p'))))"
  apply(induction rule:my_ll_induct, auto)

  apply(case_tac ba, auto 0 0)
      apply(case_tac "ll3_consume_label p (Suc n) l", auto 0 0)
       apply(frule_tac ll3_consume_label_char, auto 0 0)

      apply(case_tac "ll3_consume_label p (Suc n) l", auto 0 0)
      apply(frule_tac ll3_consume_label_char, auto 0 0)

      apply(case_tac "ll3_consume_label p (Suc n) l", auto 0 0)
  apply(frule_tac ll3_consume_label_char, auto 0 0)

      apply(case_tac "ll3_consume_label p (Suc n) l", auto 0 0)
  apply(frule_tac ll3_consume_label_char, auto 0 0)

      apply(case_tac "ll3_consume_label p (Suc n) l", auto 0 0)
   apply(frule_tac ll3_consume_label_char, auto 0 0)

  apply(case_tac " ll3_consume_label (n # p) 0 x52", auto)
  apply(case_tac ba, auto)
   apply(case_tac "ll3_consume_label p (Suc n) l", auto)
   apply(case_tac "ll3_consume_label (n' # p') 0 x52", auto)

(* 3 subcases of final case *)
    apply(drule_tac p' = "n'#p'" and n' = 0 in ll3_consume_nil_gen) apply(auto  0 0)

   apply(case_tac ba, simp)
    (* sub-subcase 1*)
    apply(frule_tac p' = "n'#p'" and n' = 0 in ll3_consume_nil_gen) apply(auto 0 0)
       apply(drule_tac ll3_consume_label_unch) apply(auto 0 0)
  apply(thin_tac "ll3_consume_label (n' # p') 0 ac =
       Some (ac, [])")
apply(thin_tac "ll3_consume_label (n # p) 0 ac =
       Some (aa, [])")
      apply(drule_tac ll3_consume_label_char) apply(auto 0 0)
    apply(frule_tac p' = "n'#p'" and n' = 0 in ll3_consume_nil_gen) apply(auto 0 0)
    (* sub-subcase 2 *) 
    apply(frule_tac p' = "ad#list" in ll3_consume_label_char) apply(auto 0 0)
    (* sub subcase 3*)
   apply(frule_tac p' ="n'#p'" and n' = 0 in ll3_consume_nil_gen) apply(auto 0 0)

  apply(case_tac "ll3_consume_label (n' # p') 0 x52", auto)
  (* subcase 1 *)
  apply(drule_tac p' = "n#p" and n' = 0 in ll3_consume_none_gen) apply(auto 0 0 )
  (* subcase 2 *)
  apply(case_tac ba, auto 0 0)
  (* several more subcases, split out *)
    apply(drule_tac p' = "n#p" and n' = 0 in ll3_consume_nil_gen) apply(auto 0 0)

  apply(thin_tac " \<forall>p n ls' pp k.
          ll3_consume_label p n l = Some (ls', pp @ k # p) \<longrightarrow>
          (\<forall>p'. length p = length p' \<longrightarrow>
                (\<forall>n'. ll3_consume_label p' n' l =
                      Some (ls', pp @ (k - n + n') # p')))")
   apply(frule_tac ll3_consume_label_char) apply(auto)

  apply(thin_tac " \<forall>p n ls' pp k.
          ll3_consume_label p n l = Some (ls', pp @ k # p) \<longrightarrow>
          (\<forall>p'. length p = length p' \<longrightarrow>
                (\<forall>n'. ll3_consume_label p' n' l =
                      Some (ls', pp @ (k - n + n') # p')))")
   apply(frule_tac ll3_consume_label_char) apply(auto)
  done


lemma ll3_consume_gen :
"ll3_consume_label p n ls = Some (ls', pp @ k # p) \<Longrightarrow>
  length p = length p' \<Longrightarrow>  ll3_consume_label p' n' ls = Some (ls', pp @ (k-n+n')#p')"
  apply(subgoal_tac "(! q e l . (t::ll3) = (q, LSeq e l) \<longrightarrow> 
    (! p n l' pp k p . ll3_consume_label p n l = Some (l', pp @ k # p) \<longrightarrow>
    (! p' . length p = length p' \<longrightarrow> (! n' . ll3_consume_label p' n' l = Some (l', pp@(k-n+n')#p')))))
\<and> (! p n ls' pp k . ll3_consume_label p n ls = Some (ls', pp @ k # p) \<longrightarrow>
  (! p'  . length p = length p' \<longrightarrow> (! n' . ll3_consume_label p' n' ls = Some (ls', pp @ (k-n+n')#p'))))")
   apply(rule_tac[2] ll3_consume_gen')
  apply(simp)
  done

lemma ll3_do_consumes_concat  [rule_format] :
"(! l l' . ll3_do_consumes l s = Some l' \<longrightarrow>
       (! s' l'' . ll3_do_consumes l' s' = Some l'' \<longrightarrow>
       ll3_do_consumes l (s @ s') = Some l''))"
  apply(induction s) apply(auto)

  apply(case_tac " ll3_consume_label (replicate b 0) 0 l", auto)
  apply(case_tac ba, auto)
  apply(case_tac "take (Suc (length list) - b) (ab # list)", auto)
   apply(case_tac a, auto)
  apply(case_tac "ac#lista = a", auto)
  done
  

(* we need a lemma about how if we find for one length of path we will find for any path of that length *)
lemma ll3_consumes_alt_eq_r2l [rule_format] :
"(l, cs, l') \<in> ll3_consumes \<Longrightarrow> ll3_do_consumes l cs = Some l'"
  apply(induction rule:ll3_consumes.induct)
     apply(auto)

    apply(drule_tac[1] ll3_consume_label_unch) apply(auto)

  apply(case_tac[1] "ll3_consume_label (replicate (length p) 0) 0
              l", auto)

     apply(rotate_tac[2] 1) apply(frule_tac[2] ll3_consume_label_char) apply(auto)
      apply(drule_tac[1] p' = p and n' = n in ll3_consume_none_gen) apply(auto)

     apply(drule_tac[1] p' = p and n' = n in ll3_consume_gen) apply(auto)

    apply(drule_tac[1] p' = p and n' = n in ll3_consume_gen) apply(auto)

  apply(rotate_tac[1])
   apply(frule_tac[1] ll3_consume_label_char) apply(auto)
     apply(drule_tac[1] p' = p and n' = n in ll3_consume_nil_gen) apply(auto)

    apply(drule_tac[1] p' = p and n' = n in ll3_consume_gen) apply(auto)

     apply(drule_tac[1] p' = p and n' = n in ll3_consume_gen) apply(auto)

  apply(rule_tac ll3_do_consumes_concat) apply(auto)
  done

lemma ll3_consumes_alt_eq_l2r2 [rule_format] :
"x \<in> ll3_consumes_alt \<Longrightarrow> x \<in> ll3_consumes"
  apply(case_tac x, auto)
  apply(drule_tac ll3_consumes_alt.cases, auto)
  apply(drule_tac ll3_consumes_alt_eq_l2r) apply(auto)
  done

lemma ll3_consumes_alt_eq_r2l2 [rule_format] :
"x \<in> ll3_consumes \<Longrightarrow> x \<in> ll3_consumes_alt"
  apply(case_tac x, auto)
  apply(drule_tac ll3_consumes_alt_eq_r2l)
  apply(auto simp add:ll3_consumes_alt.intros)
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


(* "hybrid approach" with sets and lists  *)
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


(* we need to establish links between consume_labels and descendents. *)

(* we need my_ll_induct *)


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
    ( ! q e d . h = (q, LLab e d) \<longrightarrow> e = True)) \<or> 
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
  apply(case_tac[1] "ll3_assign_label_list l", auto)

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
    ( ! q e d . h = (q, LLab e d) \<longrightarrow> e = True)) \<or> 
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
    ( ! q e d . h = (q, LLab e d) \<longrightarrow> e = True)) \<or> 
  (? q e e' lsdec lsdec'' .
    h = (q, LSeq e lsdec) \<and>
    h' = (q, LSeq e' lsdec'') \<and>
    (? lsdec' . ll3_consume_label [] 0 lsdec = Some (lsdec', rev e') \<and>
    ll3_assign_label_list lsdec' = Some lsdec'')
)))))
"
  apply(insert ll3_assign_label_preserve')
  apply(auto)
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
    ( ! q e d . h = (q, LLab e d) \<longrightarrow> e = True)) \<or> 
  (? q  e e' lsdec lsdec'' .
    h = (q, LSeq e lsdec) \<and>
    h' = (q, LSeq e' lsdec'') \<and>
    (? lsdec' . ll3_consume_label [] 0 lsdec = Some (lsdec', rev e') \<and>
    ll3_assign_label_list lsdec' = Some lsdec'')
))))))"
  apply(insert ll3_assign_label_preserve_new')
  apply(auto)
  done
  

(* we need versions of this that work backwards (?) *)
lemma ll3_assign_label_preserve2_gen' :
"(! c h  . length ls > c \<longrightarrow> ls ! c = h \<longrightarrow>
 (! ls' . ll3_assign_label_list ls = Some (ls') \<longrightarrow>
  (? h' . ls' ! c = h' \<and> 
    (( h = h' \<and>
    ( ! q e d . h = (q, LLab e d) \<longrightarrow> e = True)) \<or> 
  (? q e e' lsdec lsdec'' .
    h = (q, LSeq e lsdec) \<and>
    h' = (q, LSeq e' lsdec'') \<and>
    (? lsdec' . ll3_consume_label [] 0 lsdec = Some (lsdec', rev e') \<and>
    ll3_assign_label_list lsdec' = Some lsdec'')
)))))
"
  apply(induction ls)
   apply(auto)
  (* big goal 1 *)
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

  (* big goal 2 *)
  apply(case_tac [1] "ll3_assign_label ((a, b), ba)", auto)
apply(case_tac [1] "ll3_assign_label_list ls", auto)
  apply(case_tac[1] c, auto) apply(case_tac ls, auto)
   apply(case_tac[1] e, auto)
  apply(case_tac [1] "ll3_assign_label ((a, b), ba)", auto)
apply(case_tac [1] "ll3_assign_label_list list", auto)
   apply(case_tac[1] e, auto)
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




(* our course of action is still the following:
make a lemma saying that assign_label_list doesn't create
new descendents of the length of a descendece relationship
from any Seq node using that list 

in this one we need to include cases for all possibilities of c: either
- c is unchanged (c = c')
- or c was a label at the appropriate depth that got changed
- or c is a seq node computed from c' by a "consumes" and then an assign_labels*)



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
the problem is that the entire spine changes, we need to capture this

ll3_consume_label_restsame :
ll3_consume_label p n ls = Some (ls', p') \<longrightarrow> p' \<noteq> [] \<longrightarrow>
  ( ? pp k . p' = pp @ k # p \<and> k \<ge> n \<and>
  (? q' . ! e' . ((q, LSeq e' ls), (q', LLab False (length p' - 1)), (k - n)#(rev pp)) \<in> ll3'_descend \<and>
             ((q, LSeq e' ls'), (q', LLab True (length p' - 1)), (k - n)#(rev pp)) \<in> ll3'_descend)
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

lemma ll3_descend_singleton [rule_format] :
"(t1, t2, k) \<in> ll3'_descend \<Longrightarrow>
(! x . k = [x] \<longrightarrow>
  (? q1 e1 ls . t1 = (q1, LSeq e1 ls) \<and> ls ! x = t2))"
  apply(induction rule:ll3'_descend.induct)
   apply(auto)
  apply(case_tac n, auto) apply(drule_tac[1] ll3_descend_nonnil, auto)
    apply(drule_tac[1] ll3_descend_nonnil, auto)
    apply(drule_tac[1] ll3_descend_nonnil, auto)
   apply(drule_tac[1] ll3_descend_nonnil, auto) apply(drule_tac[1] ll3_descend_nonnil, auto)
  apply(drule_tac[1] ll3_descend_nonnil, auto) apply(drule_tac[1] ll3_descend_nonnil, auto)
  done


(* idea: here if both are non nil, we can split it *)

lemma ll_get_node_comp2 [rule_format] :
"(! p1 . ll_get_node t (p1@p2) = Some t'' \<longrightarrow>
 (? t' . ll_get_node t p1 = Some t' \<and>
         ll_get_node t' p2 = Some t''))
"     
proof(induction p2)
  case Nil
  then show ?case by auto
next
  case (Cons a k2t)
  then show ?case
    apply(auto)
    apply(drule_tac[1] x = "p1@[a]" in spec) apply(auto)
    apply(drule_tac[1] ll_get_node_last) apply(auto)
    apply(subgoal_tac[1] " ll_get_node ((aaa, bb), bc) ([a] @ k2t) =
       Some t''")
     apply(rule_tac[2] ll_get_node_comp) apply(auto)
    done
qed
  

lemma ll3_descend_splitpath :
"(t1, t3, k1@k2) \<in> ll3'_descend \<Longrightarrow>
( case k1 of
   [] \<Rightarrow> (case k2 of [] \<Rightarrow> False | _ \<Rightarrow> (t1, t3, k2) \<in> ll3'_descend)
   |  _ \<Rightarrow> (case k2 of [] \<Rightarrow> (t1, t3, k1) \<in> ll3'_descend
                    | _ \<Rightarrow> (? t2 . (t1, t2, k1) \<in> ll3'_descend \<and> (t2, t3, k2) \<in> ll3'_descend)))"
  apply(drule_tac ll_descend_eq_r2l2)
  apply(drule_tac ll3'_descend_alt.cases) apply(auto)
  apply(case_tac k1, auto)
   apply(rule_tac ll_descend_eq_l2r2) apply(auto simp add:ll3'_descend_alt.intros)

  apply(case_tac k2, auto)
   apply(rule_tac ll_descend_eq_l2r2) apply(auto simp add:ll3'_descend_alt.intros)

(* ll_get_node_comp2 here *)
  apply(subgoal_tac " ll_get_node ((a, b), ba)
        ((kh # list) @ (ab # lista)) = Some ((aa, bb), bc)")
   apply(drule_tac ll_get_node_comp2) apply(auto)
  apply(thin_tac "ll_get_node ((a, b), ba)
        (kh # list @ ab # lista) =
       Some ((aa, bb), bc)")
  apply(drule_tac ll3'_descend_alt.intros)
  apply(drule_tac ll3'_descend_alt.intros)
  apply(drule_tac ll_descend_eq_l2r2)
  apply(drule_tac ll_descend_eq_l2r2)
  apply(auto)
  done

lemma ll3_descend_unique :
"(t1, t2, k) \<in> ll3'_descend \<Longrightarrow>
 (t1, t2', k) \<in> ll3'_descend \<Longrightarrow>
  t2 = t2'"
  apply(drule_tac[1] ll_descend_eq_r2l2)
apply(drule_tac[1] ll3'_descend_alt.cases, auto)
  apply(drule_tac[1] ll_descend_eq_r2l2)
  apply(drule_tac[1] ll3'_descend_alt.cases, auto)
  done


(* we need to be able to "split" cons'd descends facts into head and tail *)

(* next up, need to characterize cases where consume_label fails *)
(* this doesn't take into account the fact that a failure will be masked
if we find an existing one first. 
however, we need something similar to prove the intersection theorem below
*)
(*
lemma ll3_consume_label_failure :
"
(! q e ls .  (t :: ll3) =  (q, LSeq e ls) \<longrightarrow>
(! q' e' d k . ((q, LSeq e' ls), (q', LLab True (d)), k) \<in> ll3'_descend \<longrightarrow>
(! p  . d = length k + length p - 1 \<longrightarrow>
(! n . ll3_consume_label p n ls = None))))
\<and>
(! q q' e' d k . ((q, LSeq e' ls), (q', LLab True (d)), k) \<in> ll3'_descend \<longrightarrow>
(! p  . d = length k + length p - 1 \<longrightarrow>
(! n . ll3_consume_label p n ls = None)))
"
proof(induction rule: my_ll_induct)
case (1 q e i)
then show ?case by auto
next
  case (2 q e idx)
  then show ?case by auto
next
  case (3 q e idx n)
  then show ?case by auto
next
  case (4 q e idx n)
  then show ?case by auto
next
  case (5 q e l) then show ?case
    apply(auto)
    apply(case_tac q, auto) done next
next
  case 6
  then show ?case 
    apply(auto)
    apply(drule_tac[1] ll3_hasdesc2) apply(auto) done next
  case (7 h l)
  then show ?case
    apply(auto)
    apply(frule_tac[1] ll3_descend_nonnil) apply(auto)

    apply(frule_tac[1] ll_descend_eq_r2l2) apply(drule_tac[1] ll3'_descend_alt.cases) apply(auto)
    apply(case_tac kh, auto)
    apply(case_tac kt, auto)

     apply(case_tac h, auto) apply(case_tac ba, auto)

     apply(case_tac "ll3_consume_label (n # p) 0 x52", auto)
    apply(thin_tac[1] 
" \<forall>a b aa ba e' d k.
          (((a, b), llt.LSeq e' l), ((aa, ba), llt.LLab True d), k) \<in> ll3'_descend \<longrightarrow>
          (\<forall>p. d = length k + length p - Suc 0 \<longrightarrow> (\<forall>n. ll3_consume_label p n l = None))
")
     apply(case_tac ba, auto)
    apply(case_tac[1] "ll3_consume_label p (Suc n) l", auto)
    apply(case_tac ba, auto)


     apply(subgoal_tac[1] "(((aa, b), llt.LSeq x51 x52), ((ac, bd), llt.LLab True (Suc (length list + length p))), a#list) \<in> ll3'_descend")
      apply(rule_tac[2] ll_descend_eq_l2r2)
      apply(drule_tac[1] x = ac in spec) apply(drule_tac[1] x = bd in spec) apply(drule_tac[1] x = x51 in spec)
      apply(drule_tac[1] x = "Suc (length list + length p)" in spec) apply(drule_tac[1] x = "a#list" in spec) apply(auto)

     apply(rule_tac[1] ll3'_descend_alt.intros) apply(simp)


(* this second case is tricky *)

    (* ac, bd are bogus *)
    apply(case_tac "ll3_consume_label p n (h#l)", auto)
    apply(frule_tac ll3_consume_label_found, auto)
    apply(drule_tac ll3_consume_label_none_descend, auto)
     apply(case_tac h, auto) apply(case_tac ba, auto)

    apply(case_tac[1] "ll3_consume_label p (Suc n) l", auto)

    apply(subgoal_tac[1] "(((ac, bd), llt.LSeq e' l), ((ac, bd), llt.LLab True ((length kt + length p))), nat#kt) \<in> ll3'_descend")
     apply(rule_tac[2] ll_descend_eq_l2r2)
     apply(rule_tac[2] ll3'_descend_alt.intros) apply(auto)
    apply(case_tac "ll3_consume_label p n (h # l)", auto)

    apply(frule_tac[1] ll3_consume_label_found) apply(auto)
     apply(case_tac h, auto) apply(case_tac ba, auto)

      apply(case_tac "x22 = length p", auto)
      apply(case_tac "~x21", auto)

     apply(case_tac " ll3_consume_label (n # p) 0 x52", auto)
     apply(case_tac ba, auto)

    apply(case_tac "k-n") apply(auto)

    apply(case_tac h, auto) apply(case_tac ba, auto)
         apply(frule_tac[1] ll3_consume_label_char) apply(auto)

    apply(thin_tac " \<forall>a b e ls.
          h = ((a, b), llt.LSeq e ls) \<longrightarrow>
          (\<forall>aa ba e' d k.
              (((a, b), llt.LSeq e' ls), ((aa, ba), llt.LLab True d), k) \<in> ll3'_descend \<longrightarrow>
              (\<forall>p. d = length k + length p - Suc 0 \<longrightarrow>
                   (\<forall>n. ll3_consume_label p n ls = None)))")
    apply(thin_tac "\<forall>a b aa ba e' d k.
          (((a, b), llt.LSeq e' l), ((aa, ba), llt.LLab True d), k) \<in> ll3'_descend \<longrightarrow>
          (\<forall>p. d = length k + length p - Suc 0 \<longrightarrow> (\<forall>n. ll3_consume_label p n l = None))")
    apply(drule_tac x = ab in spec)
    apply(drule_tac x = bb in spec)
    apply(drule_tac x = e' in spec) apply(auto)
    apply(frule_tac[1] ll3_consume_label_char) apply(auto)
    

      apply(drule_tac[1] x = ac in spec)
      apply(drule_tac[1] x = bd in spec)
apply(drule_tac[1] x = ac in spec)
      apply(drule_tac[1] x = bd in spec)
      apply(drule_tac[1] x = e' in spec)
apply(drule_tac[1] x = "length kt + length p" in spec)
apply(drule_tac[1] x = "nat#kt" in spec) apply(auto) apply(drule_tac x = p in spec,  auto)
    apply(case_tac "ll3_consume_label p (Suc n) l", auto)

      apply(drule_tac[1] x = ac in spec) apply(drule_tac[1] x = bd in spec) 
apply(drule_tac[1] x = ac in spec) apply(drule_tac[1] x = bd in spec)
    apply(drule_tac[1] x = e' in spec)
     apply(drule_tac[1] x = "(length kt + length p)" in spec)
     apply(drule_tac[1] x = "nat#kt" in spec) apply(auto)
     apply(drule_tac[1] x = p in spec) apply(auto)
     apply(drule_tac[1] x = "Suc n" in spec)
    
    
    apply(case_tac ba, auto)
      apply(case_tac "ll3_consume_label p (Suc n) l", auto)


          apply(case_tac[1] " ll3_consume_label p (Suc n) l", auto)
    apply(case_tac hd, auto)
    sorry
qed
*)

(* first, we show that we can't repeat consumed indices *)
lemma ll3_consumes_failure' : 
"(ls, cs, ls') \<in> ll3_consumes \<Longrightarrow>
(! cp cn . (cp, cn) \<in> set cs \<longrightarrow>
(! p . length p = cn \<longrightarrow> 
(! n . ll3_consume_label p n ls' = None)))
"
proof(induction rule:ll3_consumes.induct)
case (1 l)
then show ?case by auto
next
  case (2 p n l l')
  then show ?case by auto
next
  case (3 p n l l' k pp)
  then show ?case
    apply(auto)
    apply(frule_tac[1] ll3_consume_label_found) apply(auto)
    apply(frule_tac[1] ll3_consume_label_found) apply(auto)
    sorry
next
  case (4 l s l' s' l'')
  then show ?case sorry
qed

lemma ll3_consumes_intersection' :
"(ls, cs, ls') \<in> ll3_consumes \<Longrightarrow>
(distinct cs (*\<and>
(! ls' cs' ls'' . (ls', cs', ls'') \<in> ll3_consumes \<longrightarrow>
(distinct (cs @ cs')))*))"
proof(induction rule: ll3_consumes.induct)
case (1 l)
  then show ?case 
    apply(auto) done
next
  case (2 p n l l')
  then show ?case by auto
next
  case (3 p n l l' k pp)
  then show ?case
    apply(auto) (*
    apply(case_tac cs1) apply(auto)*)
    done
next
  case (4 l s l' s' l'')
  then show ?case
    apply(auto) sorry
qed

(* now we need a version of this for general consumes *)
(* this should be more of an if and only if 
the only if will also have to characterize how descended seq nodes are affected
maybe not, it might be sufficient to characterize how consumes affects true labels
*)
lemma ll3_consumes_found :
"(ls, cs, ls') \<in> ll3_consumes \<Longrightarrow>
(! p n . (p,n) \<in> set cs \<longrightarrow>
  (? pp k . p = pp @ [k] \<and>
  (? q' . ! q e  . ((q, LSeq e ls), (q', LLab False (length p + n - 1)), (k)#(rev pp)) \<in> ll3'_descend \<and>
               ((q, LSeq e ls'), (q', LLab True (length p + n - 1)), (k)#(rev pp)) \<in> ll3'_descend)))(* \<and>
(* probably easier to talk about all other paths k. options:
- unchanged
- seq, in which case we need to adjust the consumes parameters
-  *)
(! p n . (p, n) \<notin> set cs \<longrightarrow>
  )
)*)"
proof(induction rule:ll3_consumes.induct)
case (1 l)
  then show ?case by auto next
  case (2 p n l l')
  then show ?case by auto next
next
  case (3 p n l l' k pp)
  then show ?case 
    apply(auto)
    apply(drule_tac[1] ll3_consume_label_found) apply(auto)
    done
next
  case (4 l s l' s' l'')
  then show ?case
    apply(auto)
     apply(drule_tac[1] x = p in spec) apply(drule_tac[1] x = n in spec) apply(auto)
     apply(rule_tac[1] x = a in exI) apply(rule_tac [1] x = b in exI) apply(auto)
     apply(thin_tac[1] "(l, s, l') \<in> ll3_consumes") apply(drule_tac[1] ll3_consumes.cases)
         apply(auto)
       apply(drule_tac[1] ll3_consume_label_unch) apply(auto)
       
    (* case analysis on s'? *)
sorry qed

(* we need my_ll_induct here *)
lemma assign_label_list_child_nofalse' :
"
(! c . c < length ls \<longrightarrow> 
(! q e n  . ls ! c = (q, LLab e n) \<longrightarrow>
(! ls' . ll3_assign_label_list ls = Some ls' \<longrightarrow>
 e = True)))
"
  apply(induction ls) apply(auto)
  apply(case_tac [1] "ll3_assign_label ((a,b), ba)", auto)
  apply(case_tac [1] "ll3_assign_label_list ls", auto)
  apply(case_tac[1] c, auto)
  apply(case_tac ls, auto)
   apply(case_tac e, auto) 
  apply(case_tac [1] "ll3_assign_label ((a,b), ba)", auto)
  apply(case_tac [1] "ll3_assign_label_list list", auto)
  apply(case_tac e, auto)
  done

lemma assign_label_list_child_nofalse :
"
ls ! c = (q, LLab e n) \<Longrightarrow>
c < length ls \<Longrightarrow>
ll3_assign_label_list ls = Some ls' \<Longrightarrow>
e = True
"
  apply(insert assign_label_list_child_nofalse')
  apply(blast)
  done

(* add something about uniqueness of k? *)
(* or at least somehow describe the fact that we didn't see this label in previous children *)
(* new version that does not use consumes as a premise *)
(* we need to strengthen the conclusion with a fact that further
characterizes two equal sequences
*)

(* TODO: switch over to this one,
the others have problems *)
lemma ll3_assign_label_preserve_best [rule_format] :
"(! ls . ll3_assign_label_list ls = Some (ls') \<longrightarrow>
  (! c  . length ls' > c \<longrightarrow> 
  (? h . ls ! c = h \<and>
  (? h' . ls' ! c = h' \<and> 
    ((( h = h' \<and>
    ( ! q e d . h = (q, LLab e d) \<longrightarrow> e = True) \<and>
  (! edec lsdec q . h = (q, LSeq edec lsdec) \<longrightarrow>
        (ll3_consume_label [] 0 lsdec = Some (lsdec, []) \<and>
          ll3_assign_label_list lsdec = Some lsdec)))) \<or> 
  (? q e e' lsdec lsdec'' .
    h = (q, LSeq e lsdec) \<and>
    h' = (q, LSeq e' lsdec'') \<and>
    (? lsdec' . ll3_consume_label [] 0 lsdec = Some (lsdec', rev e') \<and>
    ll3_assign_label_list lsdec' = Some lsdec'')
))))))
"
  apply(induction ls')
   apply(auto)

  apply(frule_tac ll3_assign_label_length)
  apply(case_tac ls) apply(auto)

  apply(case_tac "ll3_assign_label ((aa, bb), bc)", auto)
  apply(case_tac "ll3_assign_label_list list", auto)

  apply(case_tac c, simp)
  apply(frule_tac ll3_assign_label_unch1) apply(auto)
   apply(case_tac [1] bc, auto)
    apply(case_tac x21, auto)
  apply(case_tac "ll3_consume_label [] 0 x52", auto)
   apply(case_tac "ll3_assign_label_list aa", auto)
   apply(drule_tac x = list in spec) apply(auto)

  apply(case_tac c, simp) apply(case_tac ls, auto)
   apply(case_tac "ll3_assign_label ((aa, bb), llt.LLab e d)", auto)
   apply(case_tac "ll3_assign_label_list list", auto)
   apply(case_tac e, auto)

apply(case_tac ls, auto)
   apply(case_tac "ll3_assign_label ((ab, bc), bd)", auto)
   apply(case_tac "ll3_assign_label_list list", auto)
  apply(drule_tac x = list in spec) apply(auto)


   apply(case_tac c, simp) apply(case_tac ls, auto)
  apply(case_tac "case ll3_consume_label [] 0 lsdec of None \<Rightarrow> None
             | Some (ls', p) \<Rightarrow>
                 (case ll3_assign_label_list ls' of None \<Rightarrow> None
                 | Some ls'' \<Rightarrow> Some ((aa, bb), llt.LSeq (rev p) ls''))
", auto)

    apply(case_tac "ll3_assign_label_list list", auto)
    apply(case_tac "ll3_consume_label [] 0 lsdec", auto)
     apply(case_tac "ll3_assign_label_list ab", auto)
    apply(case_tac "ll3_assign_label_list ab", auto)

   apply(case_tac ls,auto)
  apply(case_tac "ll3_assign_label ((ab, bc), bd)", auto)
    apply(case_tac "ll3_assign_label_list list", auto)
   apply(drule_tac x = list in spec) apply(auto)

   apply(case_tac c, simp) apply(case_tac ls, auto)
  apply(case_tac "case ll3_consume_label [] 0 lsdec of None \<Rightarrow> None
             | Some (ls', p) \<Rightarrow>
                 (case ll3_assign_label_list ls' of None \<Rightarrow> None
                 | Some ls'' \<Rightarrow> Some ((aa, bb), llt.LSeq (rev p) ls''))
", auto)

    apply(case_tac "ll3_assign_label_list list", auto)
   apply(case_tac "ll3_consume_label [] 0 lsdec", auto)
  apply(rename_tac boo)
     apply(case_tac "ll3_assign_label_list ab", auto)

   apply(case_tac ls,auto)
  apply(case_tac "ll3_assign_label ((ab, bc), bd)", auto)
    apply(case_tac "ll3_assign_label_list list", auto)
   apply(drule_tac x = list in spec) apply(auto)

  done

lemma ll3_descend_splitpath_cons :
"(t1, t3, k1#k2) \<in> ll3'_descend \<Longrightarrow>
( case k2 of
   [] \<Rightarrow> ((t1, t3, [k1]) \<in> ll3'_descend)
   |  _ \<Rightarrow> (? t2 . (t1, t2, [k1]) \<in> ll3'_descend \<and> (t2, t3, k2) \<in> ll3'_descend))"
  apply(insert ll3_descend_splitpath[of t1 t3 "[k1]" k2]) apply(auto)
  done

lemma ll3_consume_label_length1 :
"ll3_consume_label p n l1 = Some (l2, p') \<Longrightarrow>
length l1 = length l2"
  apply(insert ll3_consume_label_length)
  apply(blast)
  done



(* TODO: need another case for where
we overshoot vs undershoot?

TODO: returned list is wrong, i think it should be p'?

TODO: is "m - n = cn" the right condition?
 *)
lemma ll3_consume_label_forward_child_cases':
"
(! q e ls . (t :: ll3) = (q, LSeq e ls) \<longrightarrow>
(! cn aa bb c . length ls > cn \<longrightarrow> ls ! cn = ((aa, bb), c) \<longrightarrow>
(! p p'  n ls' . ll3_consume_label p n ls = Some (ls', p') \<longrightarrow>
   (? c' .
      (ls' ! cn = ((aa, bb), c') \<and>
      ((p' = [] \<and> c = c') \<or>
      (? pp m . p' = pp @ m # p \<and> n \<le> m \<and>
       ((m - n \<noteq> cn \<and> c = c' ) \<or>
       (m - n = cn \<and> 
        ( (c = LLab False (length p' - 1) \<and> c' = LLab True (length p' - 1)) 
          \<or> (? lsdec lsdec' edec . 
              (c = LSeq edec lsdec \<and> c' = LSeq edec lsdec' \<and>
               ll3_consume_label (m#p) 0 lsdec = Some (lsdec', p')))))))))))))
\<and>
(! cn aa bb c . length ls > cn \<longrightarrow> ls ! cn = ((aa, bb), c) \<longrightarrow>
(! p p'  n ls' . ll3_consume_label p n ls = Some (ls', p') \<longrightarrow>
   (? c' .
      (ls' ! cn = ((aa, bb), c') \<and>
      ((p' = [] \<and> c = c') \<or>
      (? pp m . p' = pp @ m # p \<and> n \<le> m \<and>
       ((m - n \<noteq> cn \<and> c = c' ) \<or>
       (m - n = cn \<and> 
        ( (c = LLab False (length p' - 1) \<and> c' = LLab True (length p' - 1)) 
          \<or> (? lsdec lsdec' edec . 
              (c = LSeq edec lsdec \<and> c' = LSeq edec lsdec' \<and>
               ll3_consume_label (m#p) 0 lsdec = Some (lsdec', p'))))))))))))
"
proof(induction rule:my_ll_induct)
case (1 q e i)
  then show ?case by auto
next
case (2 q e idx)
  then show ?case by auto
next
  case (3 q e idx n)
  then show ?case by auto
next
  case (4 q e idx n)
  then show ?case by auto
next
  case (5 q e l)
  then show ?case by auto
next
  case 6
  then show ?case by auto
next
  case (7 h l)
  then show ?case
    apply(auto)
    apply(case_tac cn, auto)

(* case not using inductive hyp (?) *)
    apply(case_tac c, auto)
    apply(case_tac "ll3_consume_label p (Suc n) l", auto)
         apply(case_tac p') apply(auto)
         apply(frule_tac ll3_consume_label_char) apply(auto)

        apply(case_tac "x22 = length p") apply(auto)
         apply(case_tac x21, auto)
    apply(case_tac "ll3_consume_label p (Suc n) l", auto)
         apply(case_tac p') apply(auto)
        apply(frule_tac ll3_consume_label_char) apply(auto)


    apply(case_tac "ll3_consume_label p (Suc n) l", auto)
         apply(case_tac p') apply(auto)
       apply(frule_tac ll3_consume_label_char) apply(auto)


    apply(case_tac "ll3_consume_label p (Suc n) l", auto)
         apply(case_tac p') apply(auto)
      apply(frule_tac ll3_consume_label_char) apply(auto)

     apply(case_tac "ll3_consume_label (n # p) 0 x52", auto)
     apply(case_tac b, auto)
      apply(case_tac "ll3_consume_label p (Suc n) l", auto)

    apply(case_tac p', auto)

    apply(frule_tac ll3_consume_label_unch, auto)
    apply(rotate_tac [1] -2)
       apply(frule_tac ll3_consume_label_char, auto)

      apply(frule_tac ll3_consume_label_unch, auto)

     apply(frule_tac ll3_consume_label_char, auto)
(*
     apply(frule_tac n' = 0 and p' = "0#p" in ll3_consume_gen) apply(auto)


       apply(frule_tac ll3_consume_label_char, auto)



    apply(rotate_tac [1] -1)
       apply(drule_tac x = "[]" in spec) apply(auto)
    apply(case_tac p', auto)
       apply(rotate_tac [1] -1)
      
       apply(drule_tac x = "n" in spec) apply(auto)
    apply(frule_tac ll3_consume_label_unch, auto)
       apply(drule_tac p' = "0#p" and n' = 0 in ll3_consume_nil_gen) apply(auto)

      apply(frule_tac ll3_consume_label_unch, auto)

    apply(frule_tac ll3_consume_label_char, auto)
     apply(frule_tac ll3_consume_gen) apply(auto)
*)
(* inductive hyp case (?) *)
    apply(rotate_tac [1] -4)
    apply(drule_tac x = nat in spec) apply(auto)

    apply(case_tac p', auto)
     apply(frule_tac ll3_consume_label_unch, auto)

    apply(frule_tac ll3_consume_label_char, auto)

    apply(frule_tac ll3_consume_label_length1, auto) apply(case_tac ls', auto)

    (* we run into problems with ma vs m.
       i think we need to constrain one of our existentials more?
*)

(* are we doing this case split before extracting some needed information?
(e.g. about lengths *)
(* doing length1 here seems to mess up the proof? *)
(*    apply(frule_tac ll3_consume_label_length1, auto) *)
    apply(case_tac h, auto)
    apply(case_tac bca, auto)

      apply(case_tac "ll3_consume_label p (Suc n) l", auto)
        apply(drule_tac x = p in spec)
        apply(drule_tac x = "pp@ m # p" in spec)
        apply(drule_tac x = "Suc n" in spec) apply(auto)
         apply(case_tac m, auto)
        apply(case_tac pp, auto)

       apply(case_tac "x22 = length p", auto)
        apply(case_tac x21, auto) 
       apply(case_tac "ll3_consume_label p (Suc n) l", auto)
       apply(drule_tac x = p in spec) apply(drule_tac x = "pp@ m # p" in spec)
       apply(drule_tac x = "Suc n" in spec)
       apply(drule_tac x = lista in spec) apply(auto)
        apply(case_tac m, auto)
    apply(case_tac pp, auto)

     apply(case_tac "ll3_consume_label p (Suc n) l", auto)
        apply(drule_tac x = p in spec)
        apply(drule_tac x = "pp@ m # p" in spec)
        apply(drule_tac x = "Suc n" in spec) apply(auto)
         apply(case_tac m, auto)
      apply(case_tac pp, auto)

     apply(case_tac "ll3_consume_label p (Suc n) l", auto)
        apply(drule_tac x = p in spec)
        apply(drule_tac x = "pp@ m # p" in spec)
        apply(drule_tac x = "Suc n" in spec) apply(auto)
         apply(case_tac m, auto)
        apply(case_tac pp, auto)

    apply(case_tac " ll3_consume_label (n # p) 0 x52", auto)
    apply(rename_tac boo)

    apply(case_tac boo, clarsimp)
  (* boo empty *)
     apply(case_tac[1] "ll3_consume_label p (Suc n) l", auto)
      apply(frule_tac[1] ll3_consume_label_unch, auto)
    apply(frule_tac[1] ll3_consume_label_char, auto)
      apply(rotate_tac 3)
      apply(drule_tac x = "p" in spec)
    apply(rotate_tac -1)
      apply(drule_tac x ="pp @ m # p" in spec) 
      apply(rotate_tac -1)
    apply(drule_tac x = "Suc n" in spec) apply(drule_tac x = lista in spec)
      apply(auto 0 0)
       apply(case_tac m, auto)
      apply(case_tac pp, auto)

  (* boo nonempty *)
     apply(frule_tac ll3_consume_label_found, auto)

    apply(frule_tac ll3_consume_label_found, auto)

    done qed

lemma ll3_consume_label_forward_child_cases [rule_format] :
"(! cn aa bb c . length ls > cn \<longrightarrow> ls ! cn = ((aa, bb), c) \<longrightarrow>
(! p p'  n ls' . ll3_consume_label p n ls = Some (ls', p') \<longrightarrow>
   (? c' .
      (ls' ! cn = ((aa, bb), c') \<and>
      ((p' = [] \<and> c = c') \<or>
      (? pp m . p' = pp @ m # p \<and> n \<le> m \<and>
       ((m - n \<noteq> cn \<and> c = c' ) \<or>
       (m - n = cn \<and> 
        ( (c = LLab False (length p' - 1) \<and> c' = LLab True (length p' - 1)) 
          \<or> (? lsdec lsdec' edec . 
              (c = LSeq edec lsdec \<and> c' = LSeq edec lsdec' \<and>
               ll3_consume_label (m#p) 0 lsdec = Some (lsdec', p'))))))))))))
"
  apply(insert ll3_consume_label_forward_child_cases')
  apply(auto)
  done

(* lemma ll3_consume_label_backward_child_cases' *)
(* lemma ll3_consume_label_forwards_fact *)
(* lemma ll3_consume_label_backwards_fact *)
(* lemma ll3_assign_label_? (analogue of forward child cases) *)
(* lemma ll3_cassign_label_? (analogue of backward child cases) *)
(* lemma ll3_assign_labels_forwards_fact *)
(* lemma ll3_assign_labels_backwards_fact *)

(* hopefully this should be enough to let us prove ll_valid3 *)


lemma ll3_consume_label_forwards_fact :
"(x, y, k) \<in> ll3'_descend \<Longrightarrow>
(! q e ls . x = (q, LSeq e ls) \<longrightarrow>
(! q' c . y = (q', c) \<longrightarrow>
(! p p'  n ls' . ll3_consume_label p n ls = Some (ls', p') \<longrightarrow>
   (? c' .
      (! enew . ((q, LSeq enew ls'), (q', c'), k) \<in> ll3'_descend \<and>
      ((p' = [] \<and> c = c') \<or>
      (? pp m . p' = pp @ m # p \<and> n \<le> m \<and>
       ((m - n)#(rev pp) \<noteq> k \<and> c = c' ) \<or>
       ((m - n)#(rev pp) = k \<and> 
        ( (c = LLab False (length p' - 1) \<and> c' = LLab True (length p' - 1)) 
          \<or> (? lsdec lsdec' edec . 
              (c = LSeq edec lsdec \<and> c' = LSeq edec lsdec' \<and>
               ll3_consume_label (pp@m#p) 0 lsdec = Some (lsdec', p')
)))))))))))"
proof(induction rule:ll3'_descend.induct)
  case (1 c q e ls t)
  then show ?case 
    apply(auto)
    apply(frule_tac ll3_consume_label_length1)
    apply(frule_tac ll3_consume_label_forward_child_cases) apply(auto)
       apply(rule_tac x = c' in exI) apply(auto)
       apply(rule_tac ll3'_descend.intros) apply(auto)

           apply(rule_tac x = c' in exI) apply(auto)
      apply(rule_tac ll3'_descend.intros) apply(auto)
    apply(rule_tac x = "llt.LLab True (length pp + length p)" in exI) apply(auto)
     apply(rule_tac ll3'_descend.intros) apply(auto)

    apply(rule_tac x = "llt.LSeq edec lsdec'" in exI) apply(auto)
       apply(rule_tac ll3'_descend.intros) apply(auto)

    apply(thin_tac "ll3_consume_label p n ls = Some (ls', pp @ m # p)")
    apply(frule_tac ll3_consume_label_char, auto)

    apply(rule_tac x = "[]" in exI)
    apply(rule_tac x = m in exI) apply(auto)
    done

next
  case (2 t t' n t'' n')
  then show ?case
    apply(auto)
    apply(case_tac t', auto)
    apply(rotate_tac 1)
    apply(frule_tac ll3_hasdesc, auto)
    apply(drule_tac x = p in spec) apply(rotate_tac -2)
    apply(drule_tac x = p' in spec) apply(drule_tac x =na in spec)
    apply(auto)

      apply(frule_tac ll3_consume_label_unch) apply(auto)
      apply(rule_tac x = c in exI) apply(auto)
      apply(drule_tac x = enew in spec) (* bogus *)
apply(drule_tac x = enew in spec)
      apply(auto simp add:ll3'_descend.intros)

    apply(rule_tac x = c in  exI) apply(auto)
apply(drule_tac x = enew in spec) (* bogus *)
      apply(drule_tac x = enew in spec)
      apply(auto simp add:ll3'_descend.intros)

     apply(rule_tac x = pp in exI) apply(rule_tac x = m in exI) apply(auto)

      apply(frule_tac ll3_consume_label_found) apply(auto)
      apply(drule_tac x = a in spec) apply(drule_tac x = b in spec)
      apply(rotate_tac -1) apply(drule_tac x = e in spec) apply(auto)
      (* ls \<rightarrow> c descend fact plus determinism of descend *)

    apply(subgoal_tac
"(((a, b), llt.LSeq e ls), ((aa, ba), c), n@n') \<in> ll3'_descend
"
)
       apply(drule_tac k = "n@n'" in ll3_descend_unique) apply(auto)
      apply(auto simp add:ll3'_descend.intros)

      apply(frule_tac ll3_consume_label_found) apply(auto)
      apply(drule_tac x = a in spec) apply(drule_tac x = b in spec)
     apply(rotate_tac -1) apply(drule_tac x = e in spec) apply(auto)

     apply(drule_tac x = e in spec) (*bogus*)
    apply(drule_tac x = e in spec)

        apply(subgoal_tac
"(((a, b), llt.LSeq e ls'), ((aa, ba), c), n@n') \<in> ll3'_descend
"
)
      apply(rotate_tac -1)
       apply(drule_tac k = "n@n'" in ll3_descend_unique) apply(auto)
      apply(auto simp add:ll3'_descend.intros)

    apply(drule_tac x = "pp@m#p" in spec)
    apply(rotate_tac -1) apply(drule_tac x = p' in spec)
    apply(drule_tac x = 0 in spec) apply(auto)

       apply(frule_tac ll3_consume_label_unch) apply(auto)
       apply(frule_tac p = "pp@m#p" in ll3_consume_label_unch, auto)
       apply(rule_tac x = c' in  exI) apply(auto)
    apply(drule_tac x = enew in spec) apply(drule_tac x = ea in spec)
        apply(drule_tac ll3'_descend.intros(2)) apply(auto)

      apply(rule_tac x = c' in exI) apply(auto)
       apply(drule_tac x = enew in spec)
       apply(drule_tac x = ea in spec)
    apply(rotate_tac -2)
        apply(drule_tac ll3'_descend.intros(2)) apply(auto)

      apply(rule_tac x = "ppa@ma#pp" in exI)
      apply(rule_tac x = m in exI) apply(auto)
      apply(frule_tac ll3_consume_label_char) apply(auto)

     apply(rule_tac x = "llt.LLab True (length p' - Suc 0)" in exI)
     apply(auto)

      apply(drule_tac x = enew in spec)
      apply(drule_tac x = ea in spec)
      apply(rotate_tac -2)
      apply(drule_tac ll3'_descend.intros(2)) apply(auto)

     apply(rule_tac x = "ppa @ (ma # pp)" in exI)
     apply(auto)

(* last subgoal *)
    apply(rule_tac x = "llt.LSeq edec lsdec'a" in exI)
    apply(auto)
      apply(drule_tac x = enew in spec)
      apply(drule_tac x = ea in spec)
      apply(rotate_tac -2)
      apply(drule_tac ll3'_descend.intros(2)) apply(auto)

     apply(case_tac p', auto)

     apply(frule_tac l = ls in ll3_consume_label_char, auto)
     apply(frule_tac l = lsa in ll3_consume_label_char, auto)
     apply(frule_tac l = lsdec in ll3_consume_label_char, auto)
     apply(drule_tac ll3_consume_label_char, auto)
apply(drule_tac ll3_consume_label_char, auto)
     apply(rotate_tac -3)

     apply(drule_tac x = "ppa @ ma # pp" in spec) apply(auto)

    apply(rotate_tac -1)
    apply(drule_tac x = "ppa @ ma # pp" in spec)
    
    apply(auto)
    done qed

(*
          (! b n . c = LLab b n \<longrightarrow> (b = True (*\<and> n + 1 \<ge> length k*))) \<and>
          (! edec lsdec . c = LSeq edec lsdec \<longrightarrow>
        (ll3_consume_label [] 0 lsdec = Some (lsdec, []) \<and>
          ll3_assign_label_list lsdec = Some lsdec)) (* \<and>
            ll3_assign_label (q', c) = Some (q', c) *) ) \<or>
       (? n . c = LLab False n \<and> c' = LLab True n \<and> n + 1 < length k) \<or>
       (? edec edec' lsdec lsdec2 lsdec3 . 
          c = LSeq edec lsdec \<and> c' = LSeq edec' lsdec3 \<and>
          ll3_consume_label [] 0 lsdec = Some (lsdec2, rev edec') \<and>
          ll3_assign_label_list lsdec2 = Some lsdec3 
"*)
(* *)
(*

TODO: forward_child_cases

*)

lemma ll3_assign_labels_forward_child_cases [rule_format] :
"(! q e ls q' c . ((q, LSeq e ls) , (q', c), k) \<in> ll3'_descend \<longrightarrow>
(! ls' enew . ll3_assign_label_list ls = Some ls' \<longrightarrow>
   (? c' . ((q, LSeq enew ls'), (q', c'), k) \<in> ll3'_descend \<and>

      ((c = c' \<and> (! b n . c = LLab b n \<longrightarrow> (b = True (*\<and> n + 1 \<ge> length k*)))) \<or>
       (? n . c = LLab False n \<and> c' = LLab True n \<and> n + 1 < length k) \<or>
       (? edec edec' lsdec lsdec2 lsdec3 . 
          c = LSeq edec lsdec \<and> c' = LSeq edec' lsdec3 \<and>
          ll3_consume_label [] 0 lsdec = Some (lsdec2, rev edec') \<and>
          ll3_assign_label_list lsdec2 = Some lsdec3)
      )
)))
"
  sorry

lemma ll3_assign_labels_backwards_fact :
" (x, y, k) \<in> ll3'_descend \<Longrightarrow>
(! q e ls' . x = (q, LSeq e ls') \<longrightarrow>
(! q' c' . y = (q', c') \<longrightarrow>
(! ls . ll3_assign_label_list ls = Some ls' \<longrightarrow>
   (? c . (! enew . ((q, LSeq enew ls), (q', c), k) \<in> ll3'_descend \<and>

      ((c = c' \<and> 
          (! b n . c = LLab b n \<longrightarrow> (b = True (*\<and> n + 1 \<ge> length k*))) \<and>
          (! edec lsdec . c = LSeq edec lsdec \<longrightarrow>
        (ll3_consume_label [] 0 lsdec = Some (lsdec, []) \<and>
          ll3_assign_label_list lsdec = Some lsdec)) (* \<and>
            ll3_assign_label (q', c) = Some (q', c) *) ) \<or>
       (? n . c = LLab False n \<and> c' = LLab True n \<and> n + 1 < length k) \<or>
       (? edec edec' lsdec lsdec2 lsdec3 . 
          c = LSeq edec lsdec \<and> c' = LSeq edec' lsdec3 \<and>
          ll3_consume_label [] 0 lsdec = Some (lsdec2, rev edec') \<and>
          ll3_assign_label_list lsdec2 = Some lsdec3 
(* *)
)
      )
)))))
"
proof(induction rule:ll3'_descend.induct)
  case (1 c q e ls t)
  then show ?case 
    apply(auto)
    apply(frule_tac[1] ll3_assign_label_length)
    apply(case_tac c', auto)
         apply(frule_tac[1] ll3_assign_label_preserve_new2_gen) apply(auto)
         apply(drule_tac[1] x = c in spec) apply(auto simp add:ll3'_descend.intros)

         apply(frule_tac[1] ll3_assign_label_preserve_new2_gen) apply(auto)
         apply(drule_tac[1] x = c in spec) apply(auto simp add:ll3'_descend.intros)

        (* need a lemma characterizing that if any descendent
is False at the wrong depth, assign_labels will return None 
In this case, a lemma saying that label nodes returned by the
assignment have to be "true" would suffice
*)
    apply(case_tac x21, auto)
         apply(frule_tac[1] ll3_assign_label_preserve_new2_gen) apply(auto)
       apply(drule_tac[1] x = c in spec) apply(auto)
    apply(thin_tac[1] "ls ! c = ((a, b), llt.LLab False x22)")
           apply(drule_tac[1] assign_label_list_child_nofalse) apply(auto)
    apply(thin_tac[1] "ls ! c = ((a, b), llt.LLab False x22)")
    apply(drule_tac[1] assign_label_list_child_nofalse) apply(auto)
    apply(thin_tac[1] "ls ! c = ((a, b), llt.LLab False x22)")
         apply(drule_tac[1] assign_label_list_child_nofalse) apply(auto)
    apply(thin_tac[1] "ls ! c = ((a, b), llt.LLab False x22)")
        apply(drule_tac[1] assign_label_list_child_nofalse) apply(auto)
    apply(thin_tac[1] "ls ! c = ((a, b), llt.LLab False x22)")
       apply(drule_tac[1] assign_label_list_child_nofalse) apply(auto)

         apply(frule_tac[1] ll3_assign_label_preserve_best) apply(auto)
       apply(auto simp add:ll3'_descend.intros)

     apply(frule_tac[1] ll3_assign_label_preserve_best) apply(auto)
       apply(auto simp add:ll3'_descend.intros)

    apply(frule_tac[1] ll3_assign_label_preserve_best) apply(simp)
     apply( auto)
    
     apply(rule_tac[1] x = "(llt.LSeq x51 x52)" in exI) apply(auto)
     apply(auto simp add:ll3'_descend.intros)

     apply(rule_tac[1] x = "(llt.LSeq e lsdec)" in exI) apply(auto)
     apply(auto simp add:ll3'_descend.intros)
    done
next
  case (2 t t' n t'' n')
  then show ?case 
    apply(auto)
    apply(case_tac[1] t', auto) apply(case_tac[1] bba, auto)
    apply(drule_tac[1] ll3_hasdesc) apply(drule_tac[1] ll3_hasdesc) apply(auto)
    apply(drule_tac[1] ll3_hasdesc) apply(drule_tac[1] ll3_hasdesc) apply(auto)
    apply(drule_tac[1] ll3_hasdesc) apply(drule_tac[1] ll3_hasdesc) apply(auto)
    apply(drule_tac[1] ll3_hasdesc) apply(drule_tac[1] ll3_hasdesc) apply(auto)


    apply(drule_tac[1] x = ls in spec) apply(auto)
     apply(drule_tac[1] x = x52 in spec) apply(auto)

       apply(rule_tac x = "c'" in exI)
       apply( auto)        
        apply(drule_tac x = enew in spec) apply(drule_tac x = x51 in spec)
       apply(rule_tac[1] ll3'_descend.intros) apply(auto)

apply(rule_tac x = "LLab True na" in exI)
       apply( auto)        
        apply(drule_tac x = enew in spec) apply(drule_tac x = x51 in spec)
      apply(rule_tac[1] ll3'_descend.intros) apply(auto)

     apply(rule_tac x = "llt.LSeq edec lsdec" in exI) apply(auto)
        apply(drule_tac x = enew in spec) apply(drule_tac x = x51 in spec)
     apply(rule_tac[1] ll3'_descend.intros) apply(auto)


    sorry qed
(*
    apply(drule_tac x = lsdec2 in spec) apply(auto)


          apply(case_tac x51, auto)
     apply(frule_tac ll3_consume_label_unch, auto)
    apply(drule_tac x = lsdec2 in spec) apply(auto)

           apply(drule_tac x = enew in spec) apply(drule_tac x = edec in spec)
           apply(drule_tac[1] t = "((a,b),LSeq enew ls)" in ll3'_descend.intros(2))
            apply(auto)
    apply(drule_tac ll3_consume_label_found, auto)

    apply(drule_tac x = lsdec2 in spec) apply(auto)
      apply(case_tac x51, auto)
    apply(frule_tac ll3_consume_label_unch, auto)
    apply(rule_tac x = c' in exI) apply(auto)
     apply(rule_tac[1] ll3'_descend.intros) apply(auto)

    apply(drule_tac x = lsdec3 in spec) apply(auto)

        apply(drule_tac x = enew in spec) apply(drule_tac x = x51 in spec)
       apply(rule_tac[1] ll3'_descend.intros) apply(auto)


         apply(auto simp add:ll3'_descend.intros)

    
    apply(drule_tac x = enew in spec)
    apply(auto)
     apply(rule_tac[1] x = "c'" in exI) apply(auto)
      apply(auto simp add:ll3'_descend.intros)
    apply(rotate_tac [1] -1)
    apply(drule_tac ll3_assign_labels_forwards_fact, auto)
    

  (* idea: Seq must be unchanged? *)

qed*)


(* TODO: this lemma is needed by the valid3' proof but we don't
have the necessary sublemmas to prove it yet *)
(* also i wonder if this will need to interact with consumes in some way? 
maybe that is where the bound on consumes comes in.*)
(* do we need to generalize to all greater lengths? *)
lemma ll3_assign_label_preserve_labels' :
" (x, y, k) \<in> ll3'_descend \<Longrightarrow>
(! q e ls' . x = (q, LSeq e ls') \<longrightarrow>
(! q' e' . y = (q', LLab e' (length k - 1)) \<longrightarrow>
(! ls enew . ll3_assign_label_list ls = Some ls' \<longrightarrow>
       ((q, LSeq enew ls), (q', LLab e' (length k - 1)), k) \<in> ll3'_descend)))
"
(*
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

           apply(drule_tac[1] ll3_hasdesc2) apply(auto)*)
  sorry
  (* idea ? - this is transitivity
     we should combine the two descends facts,
and then use a lemma about descends (?) 
no, that is just the same theorem again *)

(* do we need to use descend instead of set? *)
(* maybe not, but maaybe we can use "!" operator *)
(* s'@p' ?*)
(* is our use of "consumes" here reasonable? *)
(* do we need to bound the consumes depth here? *)

lemma my_rev_conv :
"l1 = l2 \<Longrightarrow>
rev l1 = rev l2"
  apply(insert List.rev_is_rev_conv)
  apply(auto)
  done

lemma ll3_consumes_qvalid' :
"
(((q, t) \<in> ll_valid_q \<longrightarrow>
 (! e l . t = LSeq e l \<longrightarrow>
  (! s l' . (l, s, l') \<in> ll3_consumes \<longrightarrow> (q, l') \<in> ll_validl_q ))))
\<and>
((((x,x'), l) \<in> ll_validl_q \<longrightarrow>
  (! s l' . (l, s, l') \<in> ll3_consumes \<longrightarrow> ((x,x'), l') \<in> ll_validl_q )))
"
  apply(induction rule:ll_valid_q_ll_validl_q.induct)
        apply(auto)
   apply(drule_tac[1] ll3_consumes_alt_eq_r2l) apply(case_tac s, auto)
   apply(rule_tac[1] ll_valid_q_ll_validl_q.intros)

  apply(frule_tac[1] ll3_consumes_length, simp)
  apply(case_tac l', auto)
  apply(drule_tac ll3_consumes_split) apply(auto)

    apply(auto simp add:ll_valid_q_ll_validl_q.intros)
  apply(rule_tac ll_valid_q_ll_validl_q.intros, auto)
  apply(drule_tac ll_valid_q.cases, auto)
  apply(rule_tac ll_valid_q_ll_validl_q.intros, auto)
  done

lemma ll3_consumes_qvalid :
"(q, l) \<in> ll_validl_q \<Longrightarrow>
 (l, s, l') \<in> ll3_consumes \<Longrightarrow>
 (q, l') \<in> ll_validl_q"
  apply(case_tac q)
  apply(insert ll3_consumes_qvalid')
  apply(auto)
  done

lemma ll3_consumes_unch :
"(l, [], l') \<in> ll3_consumes \<Longrightarrow>
l = l'"
  apply(drule_tac ll3_consumes_alt_eq_r2l2) apply(drule_tac ll3_consumes_alt.cases)
   apply(auto)
  done

lemma ll3_consume_label_tail' :
"
 (! q e h ls . (t :: ll3) = (q, LSeq e (h#ls)) \<longrightarrow>
  (! p n p' ls' . ll3_consume_label p n (h#ls) = Some (h#ls', p') \<longrightarrow>
ll3_consume_label p (n+1) ls = Some (ls', p')))
\<and>
(! h ls . (l :: ll3 list) = h#ls \<longrightarrow> 
  (! p n ls' p' . ll3_consume_label p n (h#ls) = Some (h#ls', p') \<longrightarrow>
ll3_consume_label p (n+1) ls = Some (ls', p')))"
  apply(induction rule:my_ll_induct)
        apply(auto)
  apply(case_tac ba, auto)

      apply(case_tac "ll3_consume_label p (Suc n) l", auto)
     apply(case_tac "x22 = length p", auto) apply(case_tac x21, auto)

     apply(case_tac "ll3_consume_label p (Suc n) l", auto)
    apply(case_tac "ll3_consume_label p (Suc n) l", auto)
   apply(case_tac "ll3_consume_label p (Suc n) l", auto)

  apply(case_tac "ll3_consume_label (n # p) 0 x52", auto)
  apply(case_tac ba, auto)
     apply(case_tac "ll3_consume_label p (Suc n) l", auto)

  apply(case_tac x52, auto)
  apply(case_tac ls', auto)
   apply(drule_tac ll3_consume_label_found) apply(auto)
   apply(drule_tac x = a in spec) apply(drule_tac x = b in spec)
  apply(thin_tac "\<forall>p n p' ls'.
          ll3_consume_label p n (((a, b), ba) # lista) =
          Some (((a, b), ba) # ls', p') \<longrightarrow>
          ll3_consume_label p (Suc n) lista = Some (ls', p')")
   apply(drule_tac x = "[]" in spec) apply(auto)
   apply(drule_tac ll3_descend_unique) apply(auto)

  apply(drule_tac ll3_consume_label_found) apply(auto)
  apply(drule_tac x = a in spec) apply(drule_tac x = b in spec)
  apply(thin_tac " \<forall>p n p' ls'.
          ll3_consume_label p n (((a, b), ba) # lista) =
          Some (((a, b), ba) # ls', p') \<longrightarrow>
          ll3_consume_label p (Suc n) lista = Some (ls', p')")
  apply(thin_tac "\<forall>p n ls' p'.
          ll3_consume_label p n (((aa, bb), bc) # listb) =
          Some (((aa, bb), bc) # ls', p') \<longrightarrow>
          ll3_consume_label p (Suc n) listb = Some (ls', p')")
  apply(drule_tac x = "[]" in spec) apply(auto)
  apply(drule_tac ll3_descend_unique) apply(auto)
  done

lemma ll3_consume_label_tail :
"ll3_consume_label p n (h#ls) = Some (h#ls', p') \<Longrightarrow>
ll3_consume_label p (n+1) ls = Some (ls', p')"
  apply(insert ll3_consume_label_tail') apply(blast+)
  done

lemma ll3_consume_label_sane2' :
"
 (! q e h ls . (t :: ll3) = (q, LSeq e ls) \<longrightarrow>
  (! p n p' ls' . ll3_consume_label p n ls = Some (ls, p') \<longrightarrow>
  p' = []))
\<and>
(! h ls . (l :: ll3 list) = ls \<longrightarrow> 
(! p n p' ls' . ll3_consume_label p n ls = Some (ls, p') \<longrightarrow>
  p' = []))"
  apply(induction rule:my_ll_induct)
        apply(auto)
  apply(case_tac ba, auto)

      apply(case_tac "ll3_consume_label p (Suc n) l", auto)
     apply(case_tac "x22 = length p", auto)
      apply(case_tac x21, auto)

      apply(case_tac "ll3_consume_label p (Suc n) l", auto)
      apply(case_tac "ll3_consume_label p (Suc n) l", auto)
      apply(case_tac "ll3_consume_label p (Suc n) l", auto)

  apply(case_tac "ll3_consume_label (n # p) 0 x52", auto)
  apply(case_tac ba, auto)
      apply(case_tac "ll3_consume_label p (Suc n) l", auto)
  done

lemma ll3_consume_label_sane2 :
"ll3_consume_label p n ls = Some (ls, p') \<Longrightarrow>
  p' = []"
  apply(insert ll3_consume_label_sane2')
  apply(auto)
  done


(* need a general splitting lemma for consume label, that subsumes tail and head? *)
(*lemma ll3_consume_label_split' : *)

lemma ll3_consume_label_head' :
"
 (! q e h ls . (t :: ll3) = (q, LSeq e (h#ls)) \<longrightarrow>
  (! p n p' h ls' . ll3_consume_label p n (h#ls) = Some (h#ls', p') \<longrightarrow>
  (! qdec edec lsdec . h = (qdec, LSeq edec lsdec) \<longrightarrow>
ll3_consume_label (0#p) 0 lsdec = Some (lsdec, []))))
\<and>
(! h ls . (l :: ll3 list) = h#ls \<longrightarrow> 
  (! p n ls' p' . ll3_consume_label p n (h#ls) = Some (h#ls', p') \<longrightarrow>
  (! qdec edec lsdec . h = (qdec, LSeq edec lsdec) \<longrightarrow>
ll3_consume_label (0#p) 0 lsdec = Some (lsdec, []))))"

  apply(induction rule:my_ll_induct)
        apply(auto)
  apply(case_tac "ll3_consume_label (n # p) 0 lsdec") apply(auto)
   apply(case_tac b, auto)
    apply(case_tac "ll3_consume_label p (Suc n) ls", auto)
    apply(drule_tac ll3_consume_nil_gen) apply(auto)
   apply(drule_tac ll3_consume_label_sane2, auto)

  apply(case_tac "ll3_consume_label (n # p) 0 lsdec", auto)
  apply(case_tac b, auto)
  apply(case_tac "ll3_consume_label p (Suc n) l", auto)
    apply(drule_tac ll3_consume_nil_gen) apply(auto)
   apply(drule_tac ll3_consume_label_sane2, auto)
  done

lemma ll3_consume_label_head :
"ll3_consume_label p n ((qdec, LSeq edec lsdec)#ls) = Some ((qdec, LSeq edec lsdec)#ls', p') \<Longrightarrow>
ll3_consume_label (0#p) 0 lsdec = Some (lsdec, [])"
  apply(insert ll3_consume_label_head') apply(auto)
  apply(case_tac "ll3_consume_label (n # p) 0 lsdec", auto)
  apply(case_tac b, auto)
   apply(case_tac "ll3_consume_label p (Suc n) ls", auto)
   apply(drule_tac ll3_consume_nil_gen, auto)
   apply(drule_tac ll3_consume_label_sane2, auto)
  done

lemma ll_valid3'_child :
"(q, LSeq p l) \<in> ll_valid3' \<Longrightarrow>
 x \<in> set l \<Longrightarrow>
 x \<in> ll_valid3'"
  apply(drule_tac ll_valid3'.cases, auto)
   apply(case_tac x, auto)
  apply(case_tac x, auto)
  done

lemma ll3_consume_label_length2 :
"ll3_consume_label p n l = Some (l', p') \<Longrightarrow> length l = length l'"
  apply(insert ll3_consume_label_length)
  apply(blast+)
  done

(*
lemma ll3'_descend_split :
"(t1, t2, k) \<in> ll3'_descend \<Longrightarrow>
 (? q e l . t1 = (q, LSeq e l) \<and> (? kh kt . k = kh # kt \<and>
  (! q' e' h . ((q', LSeq e' (h#l)), t2, (kh+1)#kt) \<in> ll3'_descend)))
"
*)

(* one possible way forward, a more encouraging
approach would be non interference of nil-returning consumes
*)
(*
lemma ll3_consume_label_noninterf' [rule_format] :
"(! p1 n1  l'1 . ll3_consume_label p1 n1 ls = Some (l'1, []) \<longrightarrow>
(! p2 n2 p' l' . ll3_consume_label p2 n2 ls = Some (l', p') \<longrightarrow>
(ll3_consume_label p1 n1 l' = Some (l', []))))"
  apply(induction ls) apply(auto)

  apply(case_tac ba, auto)

      apply(case_tac "ll3_consume_label p1 (Suc n1) ls")
  apply(auto)
      apply(case_tac "ll3_consume_label p2 (Suc n2) ls")
       apply(auto)

     apply(case_tac "x22 = length p1") apply(auto)
      apply(case_tac x21, auto)
     apply(case_tac "x22 = length p2") apply(auto)
      apply(case_tac x21, auto)
      apply(case_tac "ll3_consume_label p1 (Suc n1) ls", auto)
  apply(drule_tac ll3_consume_label_unch, auto)

      apply(case_tac "ll3_consume_label p1 (Suc n1) ls", auto)
      apply(case_tac "ll3_consume_label p2 (Suc n2) ls", auto)

      apply(case_tac "ll3_consume_label p1 (Suc n1) ls", auto)
    apply(case_tac "ll3_consume_label p2 (Suc n2) ls", auto)

      apply(case_tac "ll3_consume_label p1 (Suc n1) ls", auto)
   apply(case_tac "ll3_consume_label p2 (Suc n2) ls", auto)

  apply(case_tac "ll3_consume_label (n1 # p1) 0 x52") apply(auto)
  apply(case_tac ba, auto)
      apply(case_tac "ll3_consume_label p1 (Suc n1) ls", auto)
  apply(case_tac "ll3_consume_label (n2 # p2) 0 x52", auto)
  apply(case_tac ba, auto)
      apply(case_tac "ll3_consume_label p2 (Suc n2) ls", auto)

   apply(case_tac "ll3_consume_label (n1 # p1) 0 ac", auto)
    apply(drule_tac ls' = ac in ll3_consume_label_unch, auto)

  apply(case_tac ba, auto)
    apply(drule_tac ls' = ae in ll3_consume_label_unch, auto)
   apply(drule_tac ls' = ac in ll3_consume_label_unch, auto)

  apply(case_tac "ll3_consume_label (n1 # p1) 0 ac", auto)
   apply(drule_tac x = p1 in spec) apply(drule_tac x = "Suc n1" in spec)
  apply(auto)
*)
lemma ll3_consume_label_noninterf' :
"
(! q e ls . (t :: ll3) = (q, LSeq e (ls)) \<longrightarrow>
(! p1 n1 l'1 . ll3_consume_label p1 n1 ls = Some (l'1, []) \<longrightarrow>
(! p2 n2 p' l' . ll3_consume_label p2 n2 ls = Some (l', p') \<longrightarrow>
(ll3_consume_label p1 n1 l' = Some (l', [])))))
\<and>
(! p1 n1 l'1 . ll3_consume_label p1 n1 (l :: ll3 list) = Some (l'1, []) \<longrightarrow>
(! p2 n2 p' l' . ll3_consume_label p2 n2 l = Some (l', p') \<longrightarrow>
(ll3_consume_label p1 n1 l' = Some (l', []))))
"
  apply(induction rule:my_ll_induct)

        apply(simp) apply(auto)


  apply(case_tac ba, simp)

      apply(case_tac "ll3_consume_label p1 (Suc n1) l")
  apply(case_tac "ll3_consume_label p2 (Suc n2) l")
        apply(clarsimp)
       apply(clarsimp)
      apply(clarsimp)
    apply(case_tac "ll3_consume_label p2 (Suc n2) l")
      apply(clarsimp)
      apply(clarsimp)

  apply(clarsimp)
     apply(case_tac "x22 = length p1") apply(clarsimp)
  apply(case_tac "~x21") apply(clarsimp) apply(clarsimp)
     apply(simp)
     apply(case_tac "ll3_consume_label p1 (Suc n1) l") apply(clarsimp) apply(clarsimp)
         apply(case_tac "x22 = length p2") apply(clarsimp)
      apply(case_tac "~x21") apply(clarsimp)
       apply(drule_tac ll3_consume_label_unch, clarsimp)

      apply(case_tac "~x21") apply(clarsimp)
  apply(drule_tac ll3_consume_label_unch, clarsimp)
      apply(clarsimp)
    apply(case_tac "ll3_consume_label p2 (Suc n2) l")
      apply(clarsimp)
     apply(clarsimp)
    apply(clarsimp)

    apply(case_tac "ll3_consume_label p1 (Suc n1) l") apply(clarsimp) apply(clarsimp)
    apply(case_tac "ll3_consume_label p2 (Suc n2) l") apply(clarsimp) apply(clarsimp)

   apply(clarsimp)
    apply(case_tac "ll3_consume_label p1 (Suc n1) l") apply(clarsimp) apply(clarsimp)
   apply(case_tac "ll3_consume_label p2 (Suc n2) l") apply(clarsimp) apply(clarsimp)

  apply(clarify)
  apply(drule_tac x = x51 in spec) apply(drule_tac x = x52 in spec)
  apply(safe)

  apply(frule_tac ll3_consume_label_unch, clarify)

  apply(frule_tac ll3_consume_label_head)
  apply(rotate_tac 1)
  apply(drule_tac x = "0#p1" in spec) apply(drule_tac x = "0" in spec) apply(safe)
  apply(subgoal_tac "(\<exists>l'1. ll3_consume_label (0 # p1) 0 x52 =
              Some (l'1, []))") apply(rule_tac[2] x = x52 in exI) apply(safe)

  apply(frule_tac p' = p' in ll3_consume_label_length2)
  apply(case_tac l', safe)
  apply(thin_tac [1] "\<forall>p1 n1.
          (\<exists>l'1. ll3_consume_label p1 n1 l = Some (l'1, [])) \<longrightarrow>
          (\<forall>p2 n2 p' l'.
              ll3_consume_label p2 n2 l = Some (l', p') \<longrightarrow>
              ll3_consume_label p1 n1 l' = Some (l', []))") apply(simp)

  apply(frule_tac ll3_consume_label_tail)
  apply(drule_tac x = p1 in spec) apply(drule_tac x = "Suc n1" in spec)
  apply(safe)
   apply(subgoal_tac "\<exists> l'1. ll3_consume_label p1 (Suc n1) l = Some (l'1, [])")
    apply(rule_tac[2] x = l in exI) apply(simp)
   apply(auto)

  apply(case_tac "ll3_consume_label (n1 # p1) 0 x52", auto)
  apply(case_tac ba, auto)
  apply(case_tac "ll3_consume_label (n2 # p2) 0 x52", auto)
  apply(case_tac ba, auto)

  apply(case_tac "ll3_consume_label p2 (Suc n2) l", auto)
   apply(case_tac "ll3_consume_label (n1 # p1) 0 ab", auto)
    apply(rotate_tac 1)
    apply(drule_tac x = p2 in spec) apply(drule_tac x = "Suc n2" in spec)

    apply(auto)

    apply(drule_tac x = "n2#p2" in spec)
    apply(drule_tac x = "0" in spec)
    apply(simp) apply(rotate_tac -1)
    apply(drule_tac p = "0#p1" and p' = "n1#p1" and n' = 0 in ll3_consume_nil_gen) apply(auto)

   apply(case_tac b, auto)
    apply(rotate_tac -1) apply(drule_tac ll3_consume_label_unch, auto)

   apply(drule_tac x = "(n2#p2)" in spec) apply(drule_tac x = 0 in spec) apply(auto)
  apply(rotate_tac -1) apply(drule_tac p = "0#p1" and p' = "n1#p1" and n' = 0 in ll3_consume_nil_gen) apply(auto)

  apply(case_tac "ll3_consume_label (n1 # p1) 0 ab", auto)

   apply(drule_tac x = "(n2#p2)" in spec) apply(drule_tac x = 0 in spec) apply(auto)
   apply(rotate_tac -1) apply(drule_tac p = "0#p1" and p' = "n1#p1" and n' = 0 in ll3_consume_nil_gen) apply(auto)

  apply(case_tac b, auto)
   apply(drule_tac x = "(n2#p2)" in spec) apply(drule_tac x = 0 in spec) apply(auto)
   apply(rotate_tac -1) apply(drule_tac p = "0#p1" and p' = "n1#p1" and n' = 0 in ll3_consume_nil_gen) apply(auto)

     apply(drule_tac x = "(n2#p2)" in spec) apply(drule_tac x = 0 in spec) apply(auto)
  apply(rotate_tac -1) apply(drule_tac p = "0#p1" and p' = "n1#p1" and n' = 0 in ll3_consume_nil_gen) apply(auto)
  done
  
lemma ll3_consume_label_noninterf [rule_format] :
"
(ll3_consume_label p1 n1 (l :: ll3 list) = Some (l'1, []) \<Longrightarrow>
(ll3_consume_label p2 n2 l = Some (l', p') \<Longrightarrow>
(ll3_consume_label p1 n1 l' = Some (l', []))))
"
  (* bogus first argument *)
  apply(insert ll3_consume_label_noninterf'[of "((0,0), LLab True 0)" l]) apply(safe) apply(auto)
  done

lemma ll3_consume_label_find_conv :
"(l1, l2, k) \<in> ll3'_descend \<Longrightarrow>
 (! x1 e1 l1l' . l1 = (x1, LSeq e1 l1l') \<longrightarrow>
 (! x2 e2 d . l2 = (x2, LLab e2 d) \<longrightarrow>
 (! p n l1l . ll3_consume_label p n l1l = Some (l1l', []) \<longrightarrow>
 d + 1 \<noteq> length k + length p)))
"
  apply(induction rule:ll3'_descend.induct)
   apply(auto)
   apply(case_tac l1l, auto)
   apply(case_tac ba, auto)
       apply(case_tac "ll3_consume_label p (Suc n) list", auto)
  apply(case_tac c, auto)
  sorry

lemma ll_descend_eq_l2r_list :
" ll_get_node_list (l) (kh#kt) = Some t \<Longrightarrow>
    ((q, LSeq e l), t, kh#kt) \<in> ll3'_descend"
  apply(case_tac l, auto)
  apply(rule_tac ll_descend_eq_l2r) apply(auto)
  done

lemma ll_descend_eq_r2l_list :
"((q, LSeq e l), t, kh#kt) \<in> ll3'_descend \<Longrightarrow>
 ll_get_node_list (l) (kh#kt) = Some t "
  apply(case_tac l, auto)
  apply(case_tac t, auto)
   apply(drule_tac ll_descend_eq_r2l) apply(auto)

  apply(case_tac t, auto)
  apply(drule_tac ll_descend_eq_r2l) apply(auto)
  done

(* translation validation approach:
check to see if our ll3s are valid after the fact *)

(*
another idea? what if we change valid3' so that it tracks the
location of unconsumed labels?
*)

(* another idea: create a "gather" function tracking all childpaths that match
Lab nodes at correct depth *)
(*
TODO: need to revise these functions,
they can return [[]] in some cases it seems

also, we need to adjust when we are updating the depth
to compensate for the fact that gather_ll3_labels_list
is our real entry point
*)
(*fun gather_ll3_labels :: "('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll \<Rightarrow> childpath \<Rightarrow> nat \<Rightarrow> childpath list" 
and gather_ll3_labels_list :: "('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll list \<Rightarrow> childpath \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> childpath list" where *)
fun gather_ll3_labels :: "ll3 \<Rightarrow> childpath \<Rightarrow> nat \<Rightarrow> childpath list" 
and gather_ll3_labels_list :: "ll3 list \<Rightarrow> childpath \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> childpath list" where
"gather_ll3_labels (_, llt.L _ _) _ _ = []"
| "gather_ll3_labels (_, llt.LJmp _ _ _) _ _ = []"
| "gather_ll3_labels (_, llt.LJmpI _ _ _) _ _ = []"
| "gather_ll3_labels (_, llt.LLab _ n) cp d = 
     (if n = d then [cp] else [])"
| "gather_ll3_labels (_, LSeq _ ls) cp d =
   gather_ll3_labels_list ls cp 0 (d+1)"
| "gather_ll3_labels_list [] _ _ _ = []"
| "gather_ll3_labels_list (h#t) cp ofs d =
   gather_ll3_labels h (cp@[ofs]) (d) @
   gather_ll3_labels_list t cp (ofs+1) d"

(* TODO: use gather instead? *)
(*
fun check_ll3_seq_nolabel :: "ll3 \<Rightarrow> nat \<Rightarrow> bool" where
"check_ll3_seq_nolabel (_, llt.L _ _) _ = True"
| "check_ll3_seq_nolabel (_, llt.LJmp _ _ _) _ = True"
| "check_ll3_seq_nolabel (_, llt.LJmpI _ _ _) _ = True"
| "check_ll3_seq_nolabel (_, llt.LLab b n) d = (b = True \<and> n \<noteq> d)"
| "check_ll3_seq_nolabel (_, LSeq _ ls) d =
   List.list_all (\<lambda> x . check_ll3_seq_nolabel x (d+1)) ls"
*)


lemma numnodes_child [rule_format] :
"((a, b), ba) \<in> set ls \<Longrightarrow>
       numnodes ((a, b), ba)
       < Suc (numnodes_l ls)"
  apply(induction ls)
   apply(auto)
  done

   

(* use List.ex1 here? *)
(* problem: we need returned childpath to also be accurate *)
(* i think we can just tack this on as an extra condition to check
in check_ll3 *)
(* is the "set" formulation correct here? *)

(* another idea: enumerate paths up to d, and try them all? *)
(*
function check_ll3_seq_label :: "ll3 \<Rightarrow> nat \<Rightarrow> bool" where
"check_ll3_seq_label (_, llt.L _ _) _ = False"
| "check_ll3_seq_label (_, llt.LJmp _ _ _) _ = False"
| "check_ll3_seq_label (_, llt.LJmpI _ _ _) _ = False"
| "check_ll3_seq_label (_, llt.LLab b n) d = (b = True \<and> n = d)"
| "check_ll3_seq_label (_, LSeq _ ls) d =
   (?x . 
   List.list_ex1 (\<lambda> x . check_ll3_seq_label x (d+1)) ls"
  by pat_completeness auto
termination
  apply(relation "measure (\<lambda> (x, n) . numnodes x)")
   apply(auto)
  apply(rule_tac numnodes_child) apply(auto)
  done
*)
(*fun check_ll3 :: "('lix, 'ljx, 'ljix, 'ptx, 'pnx) ll3'  \<Rightarrow> bool" where*)
fun check_ll3 :: "ll3  \<Rightarrow> bool" where
"check_ll3 (_, llt.L _ _) = True"
| "check_ll3 (_, llt.LJmp _ _ _) = True"
| "check_ll3 (_, llt.LJmpI _ _ _) = True"
| "check_ll3 (_, llt.LLab b n) = (b = True)"
| "check_ll3 (_, llt.LSeq [] ls) =
   (List.list_all check_ll3 ls \<and>
   gather_ll3_labels_list ls [] 0 0 = [])"
| "check_ll3 (_, llt.LSeq p ls) =
   (List.list_all check_ll3 ls \<and>
    gather_ll3_labels_list ls [] 0 0 = [p])"

(* This should say something about how everything returned by 
gather should be a true descendent *)
(* we need my_ll_induct here*)
(*
lemma gather_ll3_labels_list_nil_gen [rule_format]:
"(! cp ofs d . gather_ll3_labels_list ls cp ofs d = [] \<longrightarrow>
 (! ofs' . gather_ll3_labels_list ls cp ofs' d = []))"
  apply(induction ls)
   apply(auto)
  apply(case_tac ba, auto)
  apply(case_tac x52, auto)

  apply(case_tac ba, auto)
  apply(case_tac x52, auto)

  apply(case_tac ba, auto)
  apply(case_tac x52, auto)
*)
(*
we probably need a general correctness lemma.
that is:
"IF i am in the output of gather, THEN i am an appropriately descended label
 IF i am an appropriate descendent THEN i will show up in the gather

this probably needs separate lemma for each side

we _do_ need both directions

we need to figure out how exactly gather_labels produces output relative to cp, off, and d
a "spec" lemma defining the returned paths in terms of these parameters
*)
(*
need my_ll_induct here
*)
lemma gather_ll3_fact [rule_format] :
" (! q e ls . (t :: ll3) = (q, LSeq e ls) \<longrightarrow>
(! x cp off d . x \<in> set (gather_ll3_labels_list ls cp off d) \<longrightarrow>
    (? n cpost . n < length ls \<and> x = cp@[n+off]@cpost)))
\<and> (! x cp off d . x \<in> set (gather_ll3_labels_list (ls :: ll3 list) cp off d) \<longrightarrow>
    (? n cpost . n < length ls \<and> x = cp@[n+off]@cpost))"
proof(induction rule:my_ll_induct)
  case (1 q e i)
  then show ?case by auto
  case (2 q e idx)
  then show ?case by auto
next
  case (3 q e idx n)
  then show ?case by auto
next
case (4 q e idx n)
  then show ?case by auto
next
  case (5 q e l)
  then show ?case by auto
next
case 6
  then show ?case by auto
next
  case (7 h l)
  then show ?case 
    apply(auto)
     apply(case_tac h, auto) apply(case_tac ba, auto)
     apply(drule_tac x = x in spec)
     apply(rotate_tac -1)
     apply(drule_tac x = "cp@[off]" in spec) apply(drule_tac x = 0 in spec) apply(auto)

    apply(drule_tac x = x in spec) apply(rotate_tac -1)
    apply(drule_tac x = cp in spec) apply(drule_tac x = "Suc off" in spec)
    apply(auto)
    done qed

lemma gather_ll3_fact2 [rule_format] :
"(! x cp off d . x \<in> set (gather_ll3_labels_list (ls :: ll3 list) cp off d) \<longrightarrow>
    (? n cpost . n < length ls \<and> x = cp@[n+off]@cpost))"
  apply(insert gather_ll3_fact)
  apply(blast)
  done

(* I am not even sure if we need the length argument! *)
lemma gather_ll3_nil_gen' [rule_format]:
" 
(! q e ls . (t :: ll3) = (q, LSeq e ls) \<longrightarrow>
(! cp off n . gather_ll3_labels_list ls cp off n = [] \<longrightarrow>
   (! cp' . length cp' = length cp \<longrightarrow>
   (! off' . gather_ll3_labels_list ls cp' off' n = []))))
\<and>
(! cp off n . gather_ll3_labels_list ls cp off n = [] \<longrightarrow>
   (! cp' . length cp' = length cp \<longrightarrow>
   (! off' . gather_ll3_labels_list ls cp' off' n = [])))"
proof(induction rule:my_ll_induct)
case (1 q e i)
  then show ?case 
    
    by auto
next
  case (2 q e idx)
  then show ?case by auto
next
  case (3 q e idx n)
  then show ?case by auto
next
  case (4 q e idx n)
  then show ?case by auto
next
  case (5 q e l)
  then show ?case by auto
next
  case 6
  then show ?case by auto
next
  case (7 h l)
  then show ?case
    apply(auto)
    apply(case_tac h, auto)
    apply(case_tac ba, auto)
    done
qed

lemma gather_ll3_nil_gen2 [rule_format]:
" 
gather_ll3_labels_list ls cp off n = [] \<Longrightarrow>
   length cp' = length cp \<Longrightarrow>
   gather_ll3_labels_list ls cp' off' n = []"
  apply(insert gather_ll3_nil_gen')
  apply(blast)
  done

lemma gather_ll3_singleton_gen' [rule_format]:
" 
(! q e ls . (t :: ll3) = (q, LSeq e ls) \<longrightarrow>
(! cp x off cpost n . gather_ll3_labels_list ls cp off n =  [cp@[x+off]@cpost] \<longrightarrow>
   (! cp' . length cp' = length cp \<longrightarrow>
   (! off' . gather_ll3_labels_list ls cp' off' n = [cp'@[x+off']@cpost]))))
\<and>
(! cp x off cpost n . gather_ll3_labels_list ls cp off n =  [cp@[x+off]@cpost] \<longrightarrow>
   (! cp' . length cp' = length cp \<longrightarrow>
   (! off' . gather_ll3_labels_list ls cp' off' n = [cp'@[x+off']@cpost])))"
proof(induction rule:my_ll_induct)
  case (1 q e i)
  then show ?case by auto
next
  case (2 q e idx)
  then show ?case by auto
next
  case (3 q e idx n)
  then show ?case by auto
next
  case (4 q e idx n)
  then show ?case by auto
next
  case (5 q e l)
  then show ?case 
    apply(clarify)
    apply(drule_tac x = cp in spec)
    apply(drule_tac x = x in spec)
    apply(drule_tac x = off in spec) apply(drule_tac x = cpost in spec)
    apply(drule_tac x = n in spec) apply(clarify)
    apply(drule_tac x = cp' in spec) apply(clarify) apply(drule_tac x = off' in spec) apply(auto)
    done
  next
  case 6
  then show ?case 
    apply(clarify) apply(simp)
    done
next
  case (7 h l)
  then show ?case 
    apply(clarify)
    apply(case_tac h)
    apply(safe) 
    apply(case_tac ba) 
    
(* L case*)
    apply(safe) 
        apply(simp (no_asm_use))
    apply(subgoal_tac "cp @ (x + off) # cpost \<in>  set (gather_ll3_labels_list l cp (Suc off) n)")
         apply(frule_tac gather_ll3_fact2) apply(clarify) apply(simp (no_asm_use)) apply(clarify)
         apply(drule_tac x = cp in spec) apply(drule_tac x = na in spec) apply(drule_tac x = "Suc off" in spec)
    apply(simp) apply(thin_tac "\<forall>cp x off cpost n.
          gather_ll3_labels_list l cp off n = [cp @ (x + off) # cpost] \<longrightarrow>
          (\<forall>cp'. length cp' = length cp \<longrightarrow>
                 (\<forall>off'. gather_ll3_labels_list l cp' off' n =
                         [cp' @ (x + off') # cpost]))") apply(simp)


(* Lab case *)
    apply(simp (no_asm_use))
       apply(case_tac "x22 = n") apply(clarify) apply(simp (no_asm_use))
    apply(clarify) apply(simp (no_asm_use))
         apply(frule_tac off' = "Suc off'" and cp' = cp' in gather_ll3_nil_gen2) apply(simp (no_asm_use)) 
         apply(clarify)

       apply(rule_tac conjI) apply(clarify)
       apply(subgoal_tac "cp @ (x + off) # cpost \<in> set (gather_ll3_labels_list l cp (Suc off) n)")
        apply(frule_tac gather_ll3_fact2) apply(clarify) apply(simp (no_asm_use)) apply(clarify)
        apply(drule_tac x = cp in spec) apply(drule_tac x = na in spec) apply(drule_tac x = "Suc off" in spec)
        apply(drule_tac x = cposta in spec) apply(simp)

    apply(thin_tac " \<forall>cp x off cpost n.
          gather_ll3_labels_list l cp off n = [cp @ (x + off) # cpost] \<longrightarrow>
          (\<forall>cp'. length cp' = length cp \<longrightarrow>
                 (\<forall>off'. gather_ll3_labels_list l cp' off' n =
                         [cp' @ (x + off') # cpost]))")
       apply(simp)

(* LJmp case *)
        apply(simp (no_asm_use))
    apply(subgoal_tac "cp @ (x + off) # cpost \<in>  set (gather_ll3_labels_list l cp (Suc off) n)")
         apply(frule_tac gather_ll3_fact2) apply(clarify) apply(simp (no_asm_use)) apply(clarify)
         apply(drule_tac x = cp in spec) apply(drule_tac x = na in spec) apply(drule_tac x = "Suc off" in spec)
    apply(simp) apply(thin_tac "\<forall>cp x off cpost n.
          gather_ll3_labels_list l cp off n = [cp @ (x + off) # cpost] \<longrightarrow>
          (\<forall>cp'. length cp' = length cp \<longrightarrow>
                 (\<forall>off'. gather_ll3_labels_list l cp' off' n =
                         [cp' @ (x + off') # cpost]))") apply(simp)



(* JmpI case *)
        apply(simp (no_asm_use))
    apply(subgoal_tac "cp @ (x + off) # cpost \<in>  set (gather_ll3_labels_list l cp (Suc off) n)")
         apply(frule_tac gather_ll3_fact2) apply(clarify) apply(simp (no_asm_use)) apply(clarify)
         apply(drule_tac x = cp in spec) apply(drule_tac x = na in spec) apply(drule_tac x = "Suc off" in spec)
    apply(simp) apply(thin_tac "\<forall>cp x off cpost n.
          gather_ll3_labels_list l cp off n = [cp @ (x + off) # cpost] \<longrightarrow>
          (\<forall>cp'. length cp' = length cp \<longrightarrow>
                 (\<forall>off'. gather_ll3_labels_list l cp' off' n =
                         [cp' @ (x + off') # cpost]))") apply(simp)



(* Seq case *)
     apply(simp (no_asm_use))
     apply(case_tac "gather_ll3_labels_list x52 (cp @ [off]) 0 (Suc n)") 
        (* case 1, found in tail *)
     apply(subgoal_tac "cp @ (x+off) # cpost \<in> set (gather_ll3_labels_list l cp (Suc off) n)")
    apply(frule_tac gather_ll3_fact2) apply(clarify)
       apply(thin_tac " \<forall>cp x off cpost n.
          gather_ll3_labels_list x52 cp off n =
          [cp @ (x + off) # cpost] \<longrightarrow>
          (\<forall>cp'. length cp' = length cp \<longrightarrow>
                 (\<forall>off'.
                     gather_ll3_labels_list x52 cp' off' n =
                     [cp' @ (x + off') # cpost]))")
    apply(subgoal_tac "gather_ll3_labels_list l cp (Suc off) n =
       [cp @ (na + Suc off) # cpost]")
       apply(drule_tac x = cp in spec)
       apply(drule_tac x = na in spec) apply(drule_tac x = "Suc off" in spec) apply(simp)
       apply(drule_tac x = cposta in spec) apply(drule_tac x = n in spec) apply(simp)
       apply(rule_tac gather_ll3_nil_gen2) apply(simp)
       apply(case_tac cp') apply(simp) apply(simp)

    apply(thin_tac "\<forall>cp x off cpost n.
          gather_ll3_labels_list l cp off n = [cp @ (x + off) # cpost] \<longrightarrow>
          (\<forall>cp'. length cp' = length cp \<longrightarrow>
                 (\<forall>off'. gather_ll3_labels_list l cp' off' n =
                         [cp' @ (x + off') # cpost]))") apply(simp)

    
    apply(thin_tac "\<forall>cp x off cpost n.
          gather_ll3_labels_list l cp off n = [cp @ (x + off) # cpost] \<longrightarrow>
          (\<forall>cp'. length cp' = length cp \<longrightarrow>
                 (\<forall>off'. gather_ll3_labels_list l cp' off' n =
                         [cp' @ (x + off') # cpost]))")
     apply(thin_tac "\<forall>cp x off cpost n.
          gather_ll3_labels_list x52 cp off n = [cp @ (x + off) # cpost] \<longrightarrow>
          (\<forall>cp'. length cp' = length cp \<longrightarrow>
                 (\<forall>off'. gather_ll3_labels_list x52 cp' off' n =
                         [cp' @ (x + off') # cpost]))")
     apply(simp)

    apply(subgoal_tac " gather_ll3_labels_list x52 (cp @ [off]) 0 (Suc n) = [cp @ (x + off) # cpost]")
    apply(thin_tac "\<forall>cp x off cpost n.
          gather_ll3_labels_list l cp off n = [cp @ (x + off) # cpost] \<longrightarrow>
          (\<forall>cp'. length cp' = length cp \<longrightarrow>
                 (\<forall>off'. gather_ll3_labels_list l cp' off' n =
                         [cp' @ (x + off') # cpost]))")
     apply(subgoal_tac "cp @ (x + off) # cpost \<in> set(gather_ll3_labels_list x52 (cp @ [off]) 0 (Suc n))")
    apply(frule_tac gather_ll3_fact2) apply(clarify) 

     apply(drule_tac x = "cp @ [off]" in spec) apply(drule_tac x = na in spec)
      apply(drule_tac x = 0 in spec) apply(drule_tac x = cposta in spec)
      apply(drule_tac x = "Suc n" in spec) apply(simp) apply(clarify)
      apply(rule_tac gather_ll3_nil_gen2) apply(simp) apply(simp)

    (*clearing subgoals *)
    apply(thin_tac " \<forall>cp x off cpost n.
          gather_ll3_labels_list x52 cp off n = [cp @ (x + off) # cpost] \<longrightarrow>
          (\<forall>cp'. length cp' = length cp \<longrightarrow>
                 (\<forall>off'. gather_ll3_labels_list x52 cp' off' n =
                         [cp' @ (x + off') # cpost]))")
     apply(simp)

    apply(thin_tac "\<forall>cp x off cpost n.
          gather_ll3_labels_list x52 cp off n = [cp @ (x + off) # cpost] \<longrightarrow>
          (\<forall>cp'. length cp' = length cp \<longrightarrow>
                 (\<forall>off'. gather_ll3_labels_list x52 cp' off' n =
                         [cp' @ (x + off') # cpost]))")
    apply(thin_tac " \<forall>cp x off cpost n.
          gather_ll3_labels_list l cp off n = [cp @ (x + off) # cpost] \<longrightarrow>
          (\<forall>cp'. length cp' = length cp \<longrightarrow>
                 (\<forall>off'. gather_ll3_labels_list l cp' off' n =
                         [cp' @ (x + off') # cpost]))")
    apply(simp)
    done qed

lemma gather_ll3_singleton_gen2 [rule_format]:
"(! cp x off cpost n . gather_ll3_labels_list ls cp off n =  [cp@[x+off]@cpost] \<longrightarrow>
   (! cp' . length cp' = length cp \<longrightarrow>
   (! off' . gather_ll3_labels_list ls cp' off' n = [cp'@[x+off']@cpost])))"
  apply(insert gather_ll3_singleton_gen'[of "((0,0),LSeq [] [])" ls])
  apply(clarify)
  apply(thin_tac " \<forall>q e ls.
          ((0, 0), llt.LSeq [] []) = (q, llt.LSeq e ls) \<longrightarrow>
          (\<forall>cp x off cpost n.
              gather_ll3_labels_list ls cp off n = [cp @ [x + off] @ cpost] \<longrightarrow>
              (\<forall>cp'. length cp' = length cp \<longrightarrow>
                     (\<forall>off'. gather_ll3_labels_list ls cp' off' n =
                             [cp' @ [x + off'] @ cpost])))")
  apply(blast)
done

(*
idea: if we are descended via k
then for any childpath cp
k@cp will be output by gather
applied to a depth of 0 (?)
how does depth fit into this?
depth fits in determining the offset of the label
*)
(*
lemma gather_ll3_labels_child' [rule_format] :
"
(! c aa bb e d . length ls > c \<longrightarrow> ls ! c = ((aa, bb), llt.LLab e d) \<longrightarrow>
 (_ \<in> set (gather_ll3_labels_list ls cp 0 d)))
*)
(* we will need to prove a single step version of this one
by my_ll_induct,
then use a descend induction to stitch it together
*)
lemma gather_ll3_correct2_child [rule_format]:
"  (! c . c < length ls \<longrightarrow>
       (! a b ba n . ls ! c = ((a, b), llt.LLab ba n) \<longrightarrow>
       (! cp off . cp @ [c+off] \<in> set (gather_ll3_labels_list ls cp off n))))"
proof(induction ls)
  case Nil
  then show ?case by auto
next
  case (Cons a ls)
  then show ?case 
    apply(auto)
    apply(case_tac c, auto)

    apply(drule_tac x = nat in spec) apply(auto)
    apply(drule_tac x = cp in spec) apply(drule_tac x = "Suc off" in spec) apply(auto)
    done
qed

lemma gather_ll3_correct2_child2' [rule_format] :
"
(! q e ls . (t :: ll3) = (q, LSeq e ls) \<longrightarrow>
(! c . c < length ls \<longrightarrow>
  (! a b e lsdec . ls ! c = ((a, b), llt.LSeq e lsdec) \<longrightarrow>
   (! d cp off1 off2 post . (cp@[c+off1]@post) \<in> set(gather_ll3_labels_list lsdec (cp@[c+off1]) 0 (Suc d))  \<longrightarrow>
          (cp@[c+off1]@post) \<in> set (gather_ll3_labels_list ls cp off1 d)
))))
\<and>
(! c . c < length ls \<longrightarrow>
  (! a b e lsdec . ls ! c = ((a, b), llt.LSeq e lsdec) \<longrightarrow>
   (! d cp off1 off2 post . (cp@[c+off1]@post) \<in> set(gather_ll3_labels_list lsdec (cp@[c+off1]) 0 (Suc d))  \<longrightarrow>
          (cp@[c+off1]@post) \<in> set (gather_ll3_labels_list ls cp off1 d)
)))"
(* we need a "gen" lemma to deal with offset discrepancies *)
proof(induction rule:my_ll_induct)
  case (1 q e i)
  then show ?case by auto
next
  case (2 q e idx)
  then show ?case by auto
next
  case (3 q e idx n)
  then show ?case by auto
next
  case (4 q e idx n)
  then show ?case by auto
next
  case (5 q e l)
  then show ?case by auto
next
  case 6
  then show ?case by auto
next
  case (7 h l)
  then show ?case
    apply(auto)
    apply(case_tac c, auto)
    apply(rotate_tac 1)
    apply(drule_tac x = nat in spec) apply(auto)
    apply(rotate_tac -1)
    apply(drule_tac x = d in spec) apply(rotate_tac -1)
    apply(drule_tac x = cp in spec) apply(rotate_tac -1)
    apply(drule_tac x = "Suc off1" in spec) apply(auto)
    done
qed
(* how are we going to handle changes of offset? *)
(* idea: off is our starting offset, want off+c *)
lemma gather_ll3_correct2_child2 [rule_format] :
"(! c . c < length ls \<longrightarrow>
  (! a b e lsdec . ls ! c = ((a, b), llt.LSeq e lsdec) \<longrightarrow>
   (! d cp off post . (cp@[c+off]@post) \<in> set(gather_ll3_labels_list lsdec (cp@[c+off]) 0 (Suc d))  \<longrightarrow>
          (cp@[c+off]@post) \<in> set (gather_ll3_labels_list ls cp off d)
)))
"
(* bogus first argument to induction principle *)
  apply(insert gather_ll3_correct2_child2'[of "((0,0),LSeq [] [])" ls])
  apply(auto)
  done

(* this needs to account for post *)
lemma gather_ll3_correct_desc' [rule_format] :
"(x, y, k) \<in> ll3'_descend \<Longrightarrow>
 (! q e ls . x = (q, LSeq e ls) \<longrightarrow>
 (! q' e' lsdec . y = (q', LSeq e' lsdec) \<longrightarrow>
  (! cp n post . (cp@k@post) \<in> set (gather_ll3_labels_list lsdec (cp@k) 0 (n + length k) ) \<longrightarrow>
     (cp@k@post) \<in> set (gather_ll3_labels_list ls cp 0 n))))"
proof(induction rule: ll3'_descend.induct)
  case (1 c q e ls t)
  then show ?case
    apply(auto)
    apply(frule_tac gather_ll3_fact2) apply(auto)
    apply(drule_tac post = "na#cpost" and cp = cp and d = n and off = 0 in gather_ll3_correct2_child2) apply(auto)
    done
next
  case (2 t t' n t'' n')
  then show ?case
    apply(auto)
    apply(rotate_tac 1)
    apply(frule_tac ll3_hasdesc) apply(auto)
    apply(rotate_tac 2)
    apply(drule_tac x = "cp@n" in spec) apply(rotate_tac -1)
    apply(drule_tac x = "na + length n" in spec) apply(auto)
    apply(rotate_tac -1)
    apply(drule_tac x = post in spec) apply(auto)
    (* unsure why i need this *)
    apply(subgoal_tac "na + (length n + length n') = na + length n + length n'")
     apply(auto)
    done
qed


(* need a lemma relating result of gather_labels
to result on its descendents *)

lemma gather_ll3_correct2 :
"(x, y, k) \<in> ll3'_descend \<Longrightarrow>
 (! q e ls . x = (q, LSeq e ls) \<longrightarrow>
 (! q' b n . y = (q', LLab b (length k - 1 + n)) \<longrightarrow>
  (! cp . (cp@k) \<in> set (gather_ll3_labels_list ls cp 0 n ))))"
proof(induction rule:ll3'_descend.induct)
case (1 c q e ls t)
  then show ?case 
    apply(auto)
    apply(drule_tac cp = cp and off = 0 in gather_ll3_correct2_child) apply(auto)
done next
  case (2 t t' n t'' n')
  then show ?case 
    apply(auto)
    apply(rotate_tac 1) apply(frule_tac ll3_hasdesc) apply(auto)
    apply(frule_tac ll3_descend_nonnil) apply(auto)
    apply(drule_tac x = "cp@n" in spec) apply(auto)
    apply(frule_tac gather_ll3_fact2)  apply(auto)
    apply(rotate_tac 1)
    apply(frule_tac gather_ll3_correct_desc' ) apply(auto)
    apply(subgoal_tac "length n + na = na + length n") apply(auto)
    done
qed



lemma gather_ll3_correct1' [rule_format] :
"
(! q e ls . (t :: ll3) = (q, LSeq e ls) \<longrightarrow>
(! d cp n off post . (cp@[n+off]@post) \<in> set (gather_ll3_labels_list ls cp off d) \<longrightarrow>
   (? q' b . ((q, LSeq e ls), (q', LLab b (d + length post)), (n)#post) \<in> ll3'_descend)))
\<and>
(! d cp n off post . (cp@[n+off]@post) \<in> set (gather_ll3_labels_list ls cp off d) \<longrightarrow>
   (? q' b . (! q e . ((q, LSeq e ls), (q', LLab b (d + length post)), (n)#post) \<in> ll3'_descend))
)"
proof(induction rule:my_ll_induct)
case (1 q e i)
then show ?case by auto
next
case (2 q e idx)
  then show ?case by auto
next
  case (3 q e idx n)
  then show ?case by auto
next
  case (4 q e idx n)
  then show ?case by auto
next
  case (5 q e l)
  then show ?case 
    apply(auto) apply(drule_tac x = d in spec) apply(drule_tac x = cp in spec) apply(drule_tac x = n in spec)
    apply(drule_tac x = off in spec) apply(drule_tac x = post in spec)
    apply(auto)
    apply(rule_tac x = a in exI)
    apply(rule_tac x = b in exI)
    apply(rule_tac x = ba in exI)
    apply(case_tac q, auto)
    done
next
  case 6
  then show ?case by auto
next
  case (7 h l)
  then show ?case
    apply(auto)
     apply(case_tac h, auto)
     apply(case_tac ba, auto)
    apply(rule_tac x = a in exI) apply(rule_tac x = b in exI) apply(rule_tac x = x21 in exI)
      apply(auto simp add:ll3'_descend.intros)

     apply(frule_tac gather_ll3_fact2, auto)
    apply(thin_tac "\<forall>d cp n off post.
          cp @ (n + off) # post \<in> set (gather_ll3_labels_list l cp off d) \<longrightarrow>
          (\<exists>a b ba.
              \<forall>aa bb e.
                 (((aa, bb), llt.LSeq e l),
                  ((a, b), llt.LLab ba (d + length post)), n # post)
                 \<in> ll3'_descend)")
     apply(drule_tac x = "Suc d" in spec) apply(drule_tac x = "cp @ [off]" in spec)
     apply(drule_tac x = na in spec) apply(drule_tac x = 0 in spec) apply(drule_tac x = cpost in spec)
    apply(auto)
     apply(rule_tac x = aa in exI) apply(rule_tac x = ba in  exI)
     apply(rule_tac x = bb in  exI) apply(auto)
     apply(rule_tac ll_descend_eq_l2r) apply(auto)
     apply(drule_tac ll_descend_eq_r2l) apply(auto)

    apply(thin_tac "\<forall>a b e ls.
          h = ((a, b), llt.LSeq e ls) \<longrightarrow>
          (\<forall>d cp n off post.
              cp @ (n + off) # post
              \<in> set (gather_ll3_labels_list ls cp off d) \<longrightarrow>
              (\<exists>aa ba bb.
                  (((a, b), llt.LSeq e ls),
                   ((aa, ba), llt.LLab bb (d + length post)), n # post)
                  \<in> ll3'_descend))")
     apply(frule_tac gather_ll3_fact2, auto)
    apply(drule_tac x = d in spec)
    apply(drule_tac x = cp in spec)
    apply(drule_tac x = na in spec)
    apply(drule_tac x = "Suc off" in spec)
    apply(drule_tac x = post in spec) apply(auto)
     apply(rule_tac x = a in exI) apply(rule_tac x = b in  exI)
    apply(rule_tac x = ba in  exI) apply(auto)
    apply(rule_tac ll_descend_eq_l2r) apply(auto)
  (* bogus *)
    apply(drule_tac x = a in spec) apply(drule_tac x = b in spec)
    apply(drule_tac x = "[]" in spec) apply(drule_tac ll_descend_eq_r2l) apply(auto)
    done 
qed

lemma gather_ll3_correct1 [rule_format]:
"(! d cp n off post . (cp@[n+off]@post) \<in> set (gather_ll3_labels_list ls cp off d) \<longrightarrow>
   (? q' b . (! q e . ((q, LSeq e ls), (q', LLab b (d + length post)), (n)#post) \<in> ll3'_descend))
)"
  apply(insert gather_ll3_correct1'[of "((0,0),LSeq [] [])" ls])
  apply(auto)
  done

lemma ll_valid3'_desc [rule_format] :
"(q, t) \<in> ll_valid3' \<Longrightarrow>
 (! q' k b n . ((q, t), (q', LLab b n), k) \<in> ll3'_descend \<longrightarrow>
  b = True 
)
"
proof(induction rule:ll_valid3'.induct)
case (1 i e x)
  then show ?case
    apply(auto)
    apply(drule_tac ll3_hasdesc) apply(auto)
    done
next
  case (2 x d)
  then show ?case
    apply(auto)
    apply(drule_tac ll3_hasdesc) apply(auto)
    done
next
  case (3 e x d s)
  then show ?case
    apply(auto)
    apply(drule_tac ll3_hasdesc) apply(auto)
    done
next
  case (4 e x d s)
then show ?case
    apply(auto)
    apply(drule_tac ll3_hasdesc) apply(auto)
  done
next
  case (5 x l e)
then show ?case
  apply(auto)
  apply(frule_tac ll3_descend_nonnil) apply(auto)
apply(frule_tac ll_descend_eq_r2l) apply(auto)

  apply(case_tac l, auto)
  apply(case_tac hd, auto)
  apply(thin_tac " \<forall>k a b e'.
          ((x, llt.LSeq e (((aa, bb), bc) # list)),
           ((a, b), llt.LLab e' (length k - Suc 0)), k)
          \<notin> ll3'_descend")

   apply(drule_tac x = aa in spec) apply(drule_tac x = bb in spec)
   apply(drule_tac x = bc in spec) apply(auto)
    apply(case_tac tl, auto)
  apply(drule_tac ll_valid3'.cases, auto)
  apply(drule_tac ll_descend_eq_l2r) 
    apply(drule_tac x = a in spec) apply(drule_tac x = b in spec)
    apply(drule_tac x = "ab # lista" in spec) apply(drule_tac x = ba in spec)
    apply(auto)

    apply(case_tac tl, auto)
  apply(drule_tac ll_valid3'.cases, auto)
   apply(drule_tac ll_descend_eq_l2r) 
  apply(thin_tac "\<forall>a b k ba.
          (\<exists>n. (((aa, bb), bc), ((a, b), llt.LLab ba n), k) \<in> ll3'_descend) \<longrightarrow> ba")
  apply(drule_tac x = a in spec) apply(drule_tac x = b in spec)
    apply(drule_tac x = "ab # lista" in spec) apply(drule_tac x = ba in spec)
   apply(auto)

  apply(thin_tac "\<forall>k a b e'.
          ((x, llt.LSeq e (((aa, bb), bc) # list)),
           ((a, b), llt.LLab e' (length k - Suc 0)), k)
          \<notin> ll3'_descend")
  apply(drule_tac ll3_descend_splitpath_cons) apply(case_tac tl, auto)
   apply(drule_tac ll3'_descend.cases) apply(auto)
    apply(drule_tac x = ac in spec) apply(drule_tac x = be in spec)
    apply(drule_tac x = " llt.LLab ba n" in spec) apply(clarify)
    apply(frule_tac List.nth_mem) apply(auto)
       apply(drule_tac ll_valid3'.cases) apply(auto)
      apply(drule_tac ll_valid3'.cases) apply(auto)
     apply(drule_tac ll_valid3'.cases) apply(auto)
     apply(drule_tac ll_valid3'.cases) apply(auto)
   apply(case_tac na, auto) apply(drule_tac ll3_descend_nonnil, auto)
  apply(rotate_tac -2)
   apply(drule_tac ll3_descend_nonnil, auto)

     apply(drule_tac ll3'_descend.cases) apply(auto)
   apply(drule_tac x = ae in spec) apply(drule_tac x = bg in spec)
   apply(drule_tac x = " bh" in spec) apply(clarify)
  apply(thin_tac " ae = aa \<and> bg = bb \<and> bh = bc \<longrightarrow>
       ((aa, bb), bc) \<in> ll_valid3' \<and>
       (\<forall>a b k ba.
           (\<exists>n. (((aa, bb), bc), ((a, b), llt.LLab ba n), k) \<in> ll3'_descend) \<longrightarrow> ba)")
   apply(frule_tac List.nth_mem) apply(auto)
   apply(drule_tac x = a in spec) apply(drule_tac x = b in spec)
   apply(drule_tac x = "ab#lista" in spec) apply(drule_tac x = ba in spec)
   apply(auto)

  apply(case_tac na, auto)
  apply(rotate_tac -3)
   apply(drule_tac ll3_descend_nonnil, auto)
  apply(rotate_tac -2)
   apply(drule_tac ll3_descend_nonnil, auto)
    done
next
next
  case (6 x l e k y)
  then show ?case
    apply(auto)
    apply(rotate_tac -1)
  apply(frule_tac ll3_descend_nonnil) apply(auto)
apply(frule_tac ll_descend_eq_r2l) apply(auto)

  apply(case_tac l, auto)
  apply(case_tac hd, auto)
  apply(thin_tac " \<forall>k'. (\<exists>a b ba.
                ((x, llt.LSeq e (((aa, bb), bc) # list)),
                 ((a, b), llt.LLab ba (length k' - Suc 0)), k')
                \<in> ll3'_descend) \<longrightarrow>
            k = k'")

     apply(case_tac tl, auto)
      apply(drule_tac x = a in spec) apply(drule_tac x = b in spec)
      apply(drule_tac x = "llt.LLab ba n" in spec)
      apply(clarify)
      apply(drule_tac ll3'_descend.cases, auto)
         apply(drule_tac ll_valid3'.cases, auto)
        apply(drule_tac ll_valid3'.cases, auto)
       apply(drule_tac ll_valid3'.cases, auto)
      apply(drule_tac ll_valid3'.cases, auto)

      apply(drule_tac x = aa in spec) apply(drule_tac x = bb in spec)
     apply(drule_tac x = "bc" in spec) apply(clarify)
    apply(thin_tac "((aa, bb), bc) \<in> set list \<longrightarrow>
       ((aa, bb), bc) \<in> ll_valid3' \<and>
       (\<forall>a b k ba.
           (\<exists>n. (((aa, bb), bc), ((a, b), llt.LLab ba n), k) \<in> ll3'_descend) \<longrightarrow> ba)")
     apply(auto)
     apply(drule_tac x = a in spec) apply(drule_tac x = b in spec)
    apply(drule_tac ll_descend_eq_l2r)
     apply(drule_tac x = "ab#lista" in spec) apply(drule_tac x = ba in spec)
     apply(auto)

    apply(thin_tac " \<forall>k'. (\<exists>a b ba.
                ((x, llt.LSeq e (((aa, bb), bc) # list)),
                 ((a, b), llt.LLab ba (length k' - Suc 0)), k')
                \<in> ll3'_descend) \<longrightarrow>
            k = k'")
    apply(frule_tac ll3_descend_nonnil) apply(auto)
    apply(case_tac x) apply(auto)
    apply(drule_tac ll_descend_eq_r2l) apply(auto)
    apply(drule_tac ll_descend_eq_l2r_list)
    apply(drule_tac ll3_descend_splitpath_cons)
    apply(case_tac tl, auto)
    apply(rotate_tac -1)
    apply(drule_tac ll3'_descend.cases) apply(auto)
      apply(drule_tac x = ad in spec) apply(drule_tac x = bf in spec)
      apply(drule_tac x = "llt.LLab ba n" in spec) apply(clarify)
    apply(thin_tac  "ad = aa \<and> bf = bb \<and> llt.LLab ba n = bc \<longrightarrow>
       ((aa, bb), bc) \<in> ll_valid3' \<and>
       (\<forall>a b k ba.
           (\<exists>n. (((aa, bb), bc), ((a, b), llt.LLab ba n), k) \<in> ll3'_descend) \<longrightarrow> ba)")  
    apply(frule_tac List.nth_mem)
      apply(auto)
      apply(drule_tac ll_valid3'.cases, auto)
     apply(case_tac na, auto) apply(rotate_tac -3)
    apply(frule_tac ll3_descend_nonnil) apply(auto)
     apply(rotate_tac -2)
    apply(frule_tac ll3_descend_nonnil) apply(auto)

    apply(rotate_tac -2)
    apply(drule_tac ll3'_descend.cases, auto)
     apply(drule_tac x = af in spec) apply(drule_tac x = bh in spec)
     apply(drule_tac x = bi in spec) apply(clarify)
    apply(thin_tac " af = aa \<and> bh = bb \<and> bi = bc \<longrightarrow>
       ((aa, bb), bc) \<in> ll_valid3' \<and>
       (\<forall>a b k ba.
           (\<exists>n. (((aa, bb), bc), ((a, b), llt.LLab ba n), k) \<in> ll3'_descend) \<longrightarrow> ba)")
        apply(frule_tac List.nth_mem)
     apply(auto)
     apply(drule_tac x = a in spec) apply(drule_tac x = b in spec)
     apply(drule_tac x = "ac#lista" in spec) apply(drule_tac x = ba in spec) apply(auto)

    apply(case_tac na, auto)
    apply(rotate_tac -3)
    apply(frule_tac ll3_descend_nonnil) apply(auto)
     apply(rotate_tac -2)
    apply(frule_tac ll3_descend_nonnil) apply(auto)

    done
qed

(* getting closer here hopefully *)
lemma check_ll3_valid :
"((q,t) \<in> ll_valid_q \<longrightarrow> check_ll3 (q, t) = True \<longrightarrow> (q, t) \<in> ll_valid3')
\<and> (((x,x'), ls) \<in> ll_validl_q \<longrightarrow> 
     (! e . check_ll3 ((x,x'), LSeq e ls) = True \<longrightarrow> ((x,x'), LSeq e ls) \<in> ll_valid3'))"
proof(induction rule:ll_valid_q_ll_validl_q.induct)
case (1 i x e)
  then show ?case
    apply(auto simp add:ll_valid3'.intros) done
next
  case (2 x d e)
  then show ?case
    apply(auto simp add:ll_valid3'.intros) done
next
  case (3 x d e s)
  then show ?case 
    apply(auto simp add:ll_valid3'.intros) done
next
  case (4 x d e s)
  then show ?case 
    apply(auto simp add:ll_valid3'.intros) done
next
  case (5 n l n' e)
  then show ?case 
    apply(auto simp add:ll_valid3'.intros) done
next
  case (6 n)
  then show ?case 
    apply(auto simp add:ll_valid3'.intros)
    apply(case_tac e, auto)
    apply(rule_tac ll_valid3'.intros) apply(auto simp add:ll_valid_q_ll_validl_q.intros)
    apply(drule_tac ll_descend_eq_r2l) apply(case_tac k) apply(auto)
    done
next
  case (7 n h n' t n'')
  then show ?case
    apply(clarify)
    apply(auto)
     apply(case_tac e, auto)

    apply(case_tac e, auto)
    apply(rule_tac ll_valid3'.intros, auto)
    apply(auto simp add:ll_valid_q_ll_validl_q.intros)
      apply(case_tac "check_ll3 ((n', n''), llt.LSeq [] t)")
       apply(drule_tac x = "[]" in spec) apply(auto)
       apply(drule_tac ll_valid3'_child, auto)
    apply(drule_tac gather_ll3_nil_gen2, auto)

      apply(drule_tac gather_ll3_correct2) apply(auto)
    apply(rotate_tac -1)
      apply(drule_tac x = "[]" in spec) apply(auto)


(* speculative work *)
    apply(case_tac a, auto)

     apply(case_tac "gather_ll3_labels_list t [] (Suc 0) 0", auto)
    apply(case_tac h, auto) apply(case_tac "x22 = 0", auto)
        apply(rule_tac y = "(n,n')" in ll_valid3'.intros(6), auto)
    apply(auto simp add:ll_valid_q_ll_validl_q.intros)
       apply(drule_tac x = "[]" in spec) apply(auto)
        apply(frule_tac gather_ll3_nil_gen2) apply(auto)
         apply(drule_tac ll_valid3'_child, auto)
        apply(rule_tac ll_descend_eq_l2r) apply(auto)
       apply(frule_tac ll3_descend_nonnil, auto) apply(case_tac hd, auto)
        apply(drule_tac ll_descend_eq_r2l) apply(auto)
        apply(drule_tac ll_descend_eq_l2r_list) apply(drule_tac gather_ll3_correct2) apply(auto)
        apply(drule_tac x = "[]" in spec) apply(auto)
         apply(drule_tac gather_ll3_nil_gen2) apply(auto)
    apply(drule_tac x = "[]" in spec)
        apply(drule_tac off' = 0 in gather_ll3_nil_gen2) apply(auto)
apply(case_tac hd, auto)
        apply(drule_tac ll_descend_eq_r2l) apply(auto)
        apply(case_tac tl, auto)
       apply(case_tac tl, auto)
       apply(drule_tac gather_ll3_correct2) apply(auto)
apply(drule_tac x = "[]" in spec)
        apply(drule_tac x = "[]" in spec) apply(auto)
      apply(drule_tac gather_ll3_nil_gen2) apply(auto)


    apply(drule_tac x = "[]" in spec)
      apply(drule_tac off' = 0 in gather_ll3_nil_gen2) apply(auto)
      apply(subgoal_tac "0#list \<in> set (gather_ll3_labels_list x52 [0] 0 (Suc 0))")
       apply(frule_tac gather_ll3_fact2) apply(auto)
      apply(subgoal_tac "[0]@[na + 0]@cpost \<in> set (gather_ll3_labels_list x52 [0] 0 (Suc 0))")
    apply(frule_tac gather_ll3_correct1) apply(auto)
    apply(rule_tac y = "(a, b)" in ll_valid3'.intros(6), auto)
         apply(auto simp add:ll_valid_q_ll_validl_q.intros)
    apply(thin_tac "((n, n'), llt.LSeq x51 x52) \<in> ll_valid3'")
        apply(drule_tac ll_valid3'_child, auto)

       apply(rule_tac ll_descend_eq_l2r) apply(auto)
      (* bogus *)
       apply(drule_tac x = 0 in spec) apply(drule_tac x = 0 in spec) apply(drule_tac x = "[]" in spec)
    apply(drule_tac ll_descend_eq_r2l) apply(auto)

    
       apply(drule_tac ll_descend_eq_l2r_list)
       apply(drule_tac ll_valid3'_desc) apply(auto)

      apply(frule_tac ll3_descend_nonnil, auto)
       apply(case_tac hd, auto)
       apply(frule_tac ll_descend_eq_r2l) apply(auto)
       apply(drule_tac ll_descend_eq_l2r_list) 
    apply(rotate_tac -1)
       apply(drule_tac gather_ll3_correct2) apply(auto)
       apply(drule_tac x = "[]" in spec) apply(auto)


    apply(case_tac hd, auto)
       apply(frule_tac ll_descend_eq_r2l) apply(auto)
       apply(case_tac tl, auto)
        apply(drule_tac ll_descend_eq_l2r_list) 
    apply(rotate_tac -1)
        apply(drule_tac gather_ll3_correct2) apply(auto)
    apply(drule_tac x = "[0]" in spec) apply(auto)
    apply(rotate_tac -1)
       apply(drule_tac gather_ll3_correct2) apply(auto)
       apply(drule_tac x = "[]" in spec) apply(auto)
        apply(drule_tac ll_descend_eq_l2r_list) 
            apply(drule_tac gather_ll3_correct2) apply(auto)
    apply(drule_tac x = "[0]" in spec) apply(auto)
       apply(frule_tac ll_descend_eq_r2l) apply(auto)
      apply(drule_tac ll_descend_eq_l2r_list) 
    apply(rotate_tac -1)
      apply(drule_tac gather_ll3_correct2) apply(auto)

    apply(subgoal_tac "gather_ll3_labels_list x52 [0] 0 (Suc 0) = [[0] @ [na + 0] @ cpost]")
       apply(frule_tac cp' = "[0]" in gather_ll3_singleton_gen2) apply(auto)
      apply(drule_tac x = "[]" in spec) apply(auto)

    apply(rule_tac ll_valid3'.intros(6)) apply(auto)
         apply(auto simp add:ll_valid_q_ll_validl_q.intros)
       apply(case_tac "gather_ll3_labels ((n, n'), h) [0] 0", auto)
    apply(subgoal_tac "0 # list \<in> set (gather_ll3_labels_list t [] (Suc 0) 0)")
        apply(drule_tac gather_ll3_fact2) apply(auto)

       apply(case_tac "gather_ll3_labels ((n, n'), h) [0] 0", auto)
      apply(rule_tac ll_descend_eq_l2r) apply(auto)
    apply(subgoal_tac "0 # list \<in> set (gather_ll3_labels_list t [] (Suc 0) 0)")
       apply(drule_tac gather_ll3_fact2) apply(auto)

     apply(frule_tac ll3_descend_nonnil, auto)
      apply(case_tac hd, auto)
       apply(frule_tac ll_descend_eq_r2l) apply(auto)
      apply(drule_tac ll_descend_eq_l2r_list) 
      apply(case_tac "gather_ll3_labels ((n, n'), h) [0] 0", auto)
    apply(subgoal_tac "0 # list \<in> set (gather_ll3_labels_list t [] (Suc 0) 0)")
       apply(drule_tac gather_ll3_fact2) apply(auto)

     apply(case_tac "gather_ll3_labels ((n, n'), h) [0] 0", auto)
         apply(subgoal_tac "0 # list \<in> set (gather_ll3_labels_list t [] (Suc 0) 0)")
      apply(drule_tac gather_ll3_fact2) apply(auto)

    apply(case_tac "gather_ll3_labels_list t [] (Suc 0) 0") apply(auto)
     apply(case_tac h, auto)
      apply(case_tac "x22 = 0") apply(auto)

     apply(subgoal_tac "Suc nat # list \<in> set (gather_ll3_labels_list x52 [0] (0) (Suc 0))")
      apply(drule_tac gather_ll3_fact2) apply(auto)

        apply(case_tac "gather_ll3_labels ((n, n'), h) [0] 0") apply(auto)
     apply(subgoal_tac "Suc nat # list \<in> set (gather_ll3_labels_list t [] (Suc 0) (0))")
     apply(drule_tac gather_ll3_fact2) apply(auto)

    apply(subgoal_tac "[] @ [nat + Suc 0] @ list \<in> set (gather_ll3_labels_list t [] (Suc 0) 0)")
     apply(drule_tac gather_ll3_correct1, auto)

    apply(rule_tac ll_valid3'.intros(6), auto)
         apply(auto simp add:ll_valid_q_ll_validl_q.intros)
      apply(drule_tac x = "nat#list" in spec) apply(auto)
       apply(subgoal_tac "gather_ll3_labels_list t [] (Suc 0) 0 = [[]@[nat + Suc 0] @list]")
        apply(drule_tac off'=0 in gather_ll3_singleton_gen2) apply(auto)
      apply(drule_tac ll_valid3'_child) apply(auto)
     apply(rule_tac ll_descend_eq_l2r) apply(auto)
     apply(drule_tac x = a in spec) apply(drule_tac x = b in spec)
    apply(rotate_tac -2)
     apply(drule_tac x = "[]" in spec)
     apply(drule_tac ll_descend_eq_r2l) apply(auto)
     apply(drule_tac x = "nat # list" in spec) apply(auto)
       apply(subgoal_tac "gather_ll3_labels_list t [] (Suc 0) 0 = [[]@[nat + Suc 0] @list]")
       apply(drule_tac off'=0 in gather_ll3_singleton_gen2) apply(auto)
     apply(case_tac t, auto)
      
    apply(drule_tac ll_descend_eq_l2r_list) apply(rotate_tac -5)
     apply(drule_tac ll_valid3'_desc) apply(auto)

    apply(frule_tac ll3_descend_nonnil, auto)
     apply(case_tac hd, auto)
      apply(drule_tac ll_descend_eq_r2l) apply(auto)
      apply(case_tac tl, auto)
      apply(drule_tac ll_descend_eq_l2r)
      apply(rotate_tac -1)
    apply(frule_tac ll3_hasdesc, auto)
      apply(drule_tac gather_ll3_correct2) apply(auto) apply(rotate_tac -1)
      apply(drule_tac x = "[0]" in spec) apply(auto)

    apply(rotate_tac -1)
     apply(frule_tac ll_descend_eq_r2l) apply(auto)
     apply(case_tac t, auto)
     apply(case_tac "gather_ll3_labels ((ab, bd), be) [Suc 0] 0", auto)
      apply(drule_tac ll_descend_eq_l2r_list) 
      apply(rotate_tac -1)
      apply(drule_tac gather_ll3_correct2) apply(auto)
    apply(rotate_tac -1) apply(drule_tac x = "[]" in spec)
      apply(auto)
    apply(case_tac be, auto)
       apply(drule_tac off' = 0 and cp' = "[0]" in gather_ll3_nil_gen2) apply(auto)
    apply(case_tac nat, auto)
       apply(subgoal_tac "Suc 0 # list \<in> set (gather_ll3_labels_list lista [] (Suc (Suc 0)) 0)")
    apply(rotate_tac -1)
        apply(frule_tac gather_ll3_fact2) apply(auto)
    apply(subgoal_tac "gather_ll3_labels_list lista [] (Suc (Suc 0)) 0 = [[]@ [natb + Suc (Suc 0)] @ list]")
       apply(drule_tac off' = 1 in gather_ll3_singleton_gen2) apply(auto) 
     apply(drule_tac ll_descend_eq_l2r_list)
     apply(drule_tac gather_ll3_correct2) apply(auto)
     apply(rotate_tac -1) apply(drule_tac x = "[]" in spec) apply(auto)


    apply(rotate_tac -1)
     apply(frule_tac ll_descend_eq_r2l) apply(auto)
     apply(case_tac t, auto)
     apply(case_tac "gather_ll3_labels ((ab, bd), be) [Suc 0] 0", auto)
      apply(drule_tac ll_descend_eq_l2r_list) 
      apply(rotate_tac -1)
      apply(drule_tac gather_ll3_correct2) apply(auto)
    apply(rotate_tac -1) apply(drule_tac x = "[]" in spec)
     apply(auto)

    apply(case_tac hd, auto)
    apply(case_tac tl, auto)
     apply(frule_tac ll_descend_eq_l2r) apply(rotate_tac -1)
     apply(drule_tac gather_ll3_correct2) apply(auto)
     apply(case_tac h, auto) apply(rotate_tac -2)
     apply(drule_tac x = "[0]" in spec) apply(auto)

    apply(case_tac nata, auto)
     apply(case_tac tl, auto)
     apply(frule_tac ll_descend_eq_l2r)
     apply(rotate_tac -1)
     apply(drule_tac ll_descend_eq_l2r)
    apply(frule_tac ll3_hasdesc) apply(auto)
     apply(drule_tac gather_ll3_correct2) apply(auto)
     apply(rotate_tac -1) apply(drule_tac x = "[]" in spec) apply(auto)

    apply(drule_tac ll_descend_eq_l2r_list)
    apply(rotate_tac -1)
    apply(drule_tac gather_ll3_correct2) apply(auto)
    apply(rotate_tac -1) apply(drule_tac x = "[]" in spec)
    apply(auto)
    apply(rotate_tac -2)
    apply(drule_tac off' = 0 in gather_ll3_nil_gen2) apply(auto)
    done
qed


(* old work, before i switched to translation validator approach *)
(*
(* new version, generalize to arbitrary offsets but nil paths *)
(* Unfortunately we still need to care about the nil (returned path) case*)
lemma ll3_assign_label_valid3' :
"((q,t::ll3t) \<in> ll_valid_q \<longrightarrow> 
    ((! q' t' . ll3_assign_label (q,t) = Some (q',t') \<longrightarrow> q = q' \<and> (q',t') \<in> ll_valid3')
\<and>  ((! e l . t = LSeq e l \<longrightarrow> (! s l' . (l,s,l') \<in> ll3_consumes \<longrightarrow>
                     (! pp m l'' p n . ll3_consume_label p n l' = Some (l'', pp@m#p) \<longrightarrow>
                               m \<ge> n \<longrightarrow>
                     (! l''' . ll3_assign_label_list l'' = Some l''' \<longrightarrow> 
                          (q, LSeq ((m-n)#rev pp) l''') \<in> ll_valid3')) \<and>
                          (True))))))
\<and> (((x,x'), (ls:: ll3 list)) \<in> ll_validl_q \<longrightarrow> 
     (!p n  s l' . (ls,s,l') \<in> ll3_consumes \<longrightarrow>
                     (! pp m l'' p n . ll3_consume_label p n l' = Some (l'', pp@m#p) \<longrightarrow>
                               m \<ge> n \<longrightarrow>
                     (! l''' . ll3_assign_label_list l'' = Some l''' \<longrightarrow> 
                          (q, LSeq ((m-n)#rev pp) l''') \<in> ll_valid3')) \<and>
                     (True)))"
proof(induction rule: ll_valid_q_ll_validl_q.induct)
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
    done next
  case (3 x d e s)
  then show ?case 
    apply(auto simp add:ll_valid3'.intros) done
next
  case (4 x d e s)
  then show ?case 
    apply(auto simp add:ll_valid3'.intros) done
next
  case (5 n l n' e) then show ?case
apply(auto simp add:ll_valid3'.intros)
      apply(case_tac "ll3_consume_label [] 0 l", auto)
       apply(case_tac "ll3_assign_label_list aa", auto)
       apply(case_tac "ll3_consume_label [] 0 l", auto)
      apply(case_tac "ll3_assign_label_list aa", auto)
       apply(case_tac "ll3_consume_label [] 0 l", auto)
     apply(case_tac "ll3_assign_label_list aa", auto)
 
     apply(case_tac ba, auto)
    apply(frule_tac ll3_consume_label_unch) apply(auto)
    apply(drule_tac [1] x = "[]" in spec)
      apply(drule_tac [1] x = "l" in spec) 
         apply(drule_tac [1] ll3_consumes.intros) apply(auto)

    apply(frule_tac ll3_consume_label_char, auto)
        apply(drule_tac [1] ll3_consumes.intros) apply(auto)

      apply(case_tac "ll3_consume_label [] 0 l", auto)
       apply(case_tac "ll3_assign_label_list aa", auto)
      apply(case_tac "ll3_consume_label [] 0 l", auto)
       apply(case_tac "ll3_assign_label_list aa", auto)
       apply(case_tac "ll3_consume_label [] 0 l", auto)
     apply(case_tac "ll3_assign_label_list aa", auto)

    

    apply(drule_tac x = 
    apply(frule_tac [1] ll3_consume_label_unch, auto)

    apply(frule_tac [1] ll3_consume_label_found, simp)
     apply(auto)
    apply(drule_tac[1] x = "[]" in spec) apply(drule_tac x = l in spec) apply(auto simp add:ll3_consumes.intros)
    apply(subgoal_tac[1] "k # rev pp = rev list @ [a]") apply(auto)
    apply(subgoal_tac[1] "rev (a # list) = rev (pp @ [k])") apply(auto)
    apply(drule_tac[1] my_rev_conv) apply(auto)
    done
next
  case (6 n)
  then show ?case
    apply(auto)
    apply(drule_tac[1] ll3_consumes_length) apply(auto)
    apply(rule_tac[1] ll_valid3'.intros) apply(auto)
     apply(auto simp add:ll_valid_q_ll_validl_q.intros)
    apply(drule_tac ll3_hasdesc2) apply(auto)
    done next

next
  case (7 n h n' t n'')
  then show ?case sorry
qed
*)

(*
(* more elaborated version, with the consumes premises *)

lemma ll3_assign_label_valid3' :
"((q,t::ll3t) \<in> ll_valid_q \<longrightarrow> 
    ((! q' t' . ll3_assign_label (q,t) = Some (q',t') \<longrightarrow> q = q' \<and> (q',t') \<in> ll_valid3')
\<and>  ((! e l . t = LSeq e l \<longrightarrow> (! s l' . (l,s,l') \<in> ll3_consumes \<longrightarrow>
                     (! p'' l'' . ll3_consume_label [] 0 l' = Some (l'', p'') \<longrightarrow>
                     (! l''' . ll3_assign_label_list l'' = Some l''' \<longrightarrow> 
                          (q, LSeq (rev p'') l''') \<in> ll_valid3')))))))
\<and> (((x,x'), (ls:: ll3 list)) \<in> ll_validl_q \<longrightarrow> 
     (!p n  s ls' . (ls,s,ls') \<in> ll3_consumes \<longrightarrow>
                     (! p'' ls'' . ll3_consume_label [] 0 ls' = Some (ls'', p'') \<longrightarrow>
                     (! ls''' . ll3_assign_label_list ls'' = Some ls''' \<longrightarrow> 
                        (((x,x'), LSeq (rev p'') ls''') \<in> ll_valid3')))))"

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

    apply(frule_tac [1] ll3_consume_label_found, simp)
     apply(auto)
    apply(drule_tac[1] x = "[]" in spec) apply(drule_tac x = l in spec) apply(auto simp add:ll3_consumes.intros)
    apply(subgoal_tac[1] "k # rev pp = rev list @ [a]") apply(auto)
    apply(subgoal_tac[1] "rev (a # list) = rev (pp @ [k])") apply(auto)
    apply(drule_tac[1] my_rev_conv) apply(auto)
    done
next
  case (6 n)
  then show ?case
    apply(auto)
    apply(drule_tac[1] ll3_consumes_length) apply(auto)
    apply(rule_tac[1] ll_valid3'.intros) apply(auto)
     apply(auto simp add:ll_valid_q_ll_validl_q.intros)
    apply(drule_tac ll3_hasdesc2) apply(auto)
    done next

  case (7 n h n' t n'')
  then show ?case 
    apply(auto)
    apply(subgoal_tac "((n,n''), ((n,n'),h)#t) \<in> ll_validl_q")
     apply(rule_tac[2] ll_valid_q_ll_validl_q.intros) apply(auto)
    apply(drule_tac ll3_consumes_qvalid, auto)
    apply(drule_tac ll3_consume_label_qvalid, auto)
    apply(drule_tac ls = ls'' in ll3_assign_label_qvalid2) apply(auto)

    apply(frule_tac ll3_consumes_length, auto) apply(case_tac ls', auto)
    apply(frule_tac ll3_consume_label_length2, auto)
    apply(case_tac ls'', auto)

    apply(case_tac "ll3_assign_label ((aa, bb), bc)", auto)
    apply(case_tac "ll3_assign_label_list lista", auto)

(* begin speculative work *)



(*
end speculative work
*)

    (* here we start branching *)
(* proof for the nil case is very inefficient but works *)
    apply(frule_tac ll3_consume_label_char, auto)

(* 
nil-label case
*)
     apply(frule_tac ll3_consume_label_unch, auto)
    
     apply(rule_tac e = "[]" in ll_valid3'.intros(5)) apply(auto)

       apply(drule_tac ll3_consumes_split, auto)
        apply(rule_tac ll_valid3'.intros)
        apply(case_tac na) apply(auto) apply(drule_tac ll_valid_q.cases, auto)
    apply(case_tac "ll3_consume_label [0] 0 ls2", auto)
       apply(case_tac b, auto)
       apply(case_tac "ll3_consume_label [] (Suc 0) lista", auto)
    apply(case_tac "ll3_consume_label [] 0 ls2", auto)
       apply(case_tac "ll3_assign_label_list a", auto)

      apply(drule_tac ll3_consumes_split, clarsimp)
    apply(auto)

    apply(drule_tac x = s' in spec) apply(drule_tac x = lista in spec) apply(auto)
    apply(drule_tac ll3_consume_label_tail, auto)
           apply(drule_tac [1] n' = "0" in ll3_consume_nil_gen, auto)
        apply(drule_tac ll_valid3'_child, auto)

       apply(case_tac na, auto)
    apply(case_tac "ll3_consume_label [] (Suc 0) lista", auto)
       apply(drule_tac x = s' in spec) apply(drule_tac x = lista in spec) apply(auto)
       apply(drule_tac [1] n' = "0" in ll3_consume_nil_gen, auto)
       apply(drule_tac ll_valid3'_child, auto)

      apply(case_tac "ll3_consume_label [0] 0 ls2", auto)
    apply(rename_tac boo) apply(case_tac boo, auto)
    apply(case_tac "ll3_consume_label [] (Suc 0) lista", auto)
    apply(case_tac "ll3_consume_label [] 0 ls2", auto)
      apply(case_tac "ll3_assign_label_list aa", auto)
    apply(thin_tac "  \<forall>s l'.
          (ls1, s, l') \<in> ll3_consumes \<longrightarrow>
          (\<forall>p'' l''.
              ll3_consume_label [] 0 l' = Some (l'', p'') \<longrightarrow>
              (\<forall>l'''.
                  ll3_assign_label_list l'' = Some l''' \<longrightarrow>
                  ((n, n'), llt.LSeq (rev p'') l''')
                  \<in> ll_valid3'))")
    apply(thin_tac "\<forall>a b t'.
          (case ll3_consume_label [] 0 ls1 of None \<Rightarrow> None
           | Some (ls', p) \<Rightarrow>
               (case ll3_assign_label_list ls' of None \<Rightarrow> None
               | Some ls'' \<Rightarrow>
                   Some ((n, n'), llt.LSeq (rev p) ls''))) =
          Some ((a, b), t') \<longrightarrow>
          n = a \<and> n' = b \<and> ((a, b), t') \<in> ll_valid3'")
       apply(drule_tac x = s' in spec) apply(drule_tac x = lista in spec) apply(auto)
       apply(drule_tac [1] n' = "0" and ls = lista in ll3_consume_nil_gen, auto)
      apply(drule_tac ll_valid3'_child, auto)

     apply(frule_tac ll3_descend_nonnil) apply(auto)
       apply(drule_tac ll3_consumes_split, auto)

     apply(case_tac hd, auto) 
      apply(frule_tac ll_descend_eq_r2l) apply(auto)
        apply(case_tac tl, auto)
    apply(drule_tac ll3_assign_label_preserve1, auto)

      apply(drule_tac ll_descend_eq_l2r)
    apply(frule_tac k = "aa#list" in ll3_hasdesc, auto)
      apply(frule_tac ll3_assign_label_preserve1, auto)
    apply(case_tac "ll3_consume_label [] 0 ls", auto)
       apply(case_tac "ll3_consume_label [0] 0 ls", auto)
       apply(rename_tac boo) apply(case_tac boo, auto)
       apply(case_tac "ll3_consume_label [] (Suc 0) lista", auto)
         apply(case_tac "ll3_assign_label_list ab", auto) apply(rotate_tac -1)
      apply(drule_tac k = "aa#list" in ll3_assign_labels_backwards_fact, auto)
         apply(rotate_tac -1) apply(drule_tac x = ab in spec) apply(auto)
         apply(rotate_tac -2) apply(drule_tac x = "[]" in spec)
         apply(frule_tac ll3_consume_label_noninterf) apply(auto)
         apply(rotate_tac -1) 
    apply(thin_tac "(((n, n''), llt.LSeq [] (((n, n'), llt.LSeq (rev ba) ls) # ac)),
        ((a, b), llt.LLab True (Suc (length list))), 0 # aa # list)
       \<in> ll3'_descend")
         apply(drule_tac ll3_consume_label_find) apply(auto) apply(rotate_tac -1)
    apply(drule_tac x = "[0]" in spec) apply(auto)

      apply(case_tac "ll3_consume_label [0] 0 lsa", auto)
    apply(case_tac ba, auto)
      apply(case_tac "ll3_consume_label [] (Suc 0) lista", auto)
      apply(drule_tac k = "aa#list" in ll3_assign_labels_backwards_fact, auto)
         apply(rotate_tac -1) apply(drule_tac x = ls' in spec) apply(auto)
         apply(rotate_tac -2) apply(drule_tac x = "[]" in spec)
         apply(frule_tac ll3_consume_label_noninterf) apply(auto)
        apply(rotate_tac -1) 
    apply(thin_tac "(((n, n''), llt.LSeq [] (((n, n'), llt.LSeq e ls) # ac)),
        ((a, b), llt.LLab True (Suc (length list))), 0 # aa # list)
       \<in> ll3'_descend")
         apply(drule_tac ll3_consume_label_find) apply(auto) apply(rotate_tac -1)
        apply(drule_tac x = "[0]" in spec) apply(auto)

       apply(frule_tac ll_descend_eq_r2l) apply(auto)
       apply(drule_tac q = "(n, n')" and e = "[]" in ll_descend_eq_l2r_list)
      apply(drule_tac k = "nat#tl" in ll3_assign_labels_backwards_fact, auto)
    apply(rotate_tac -1) apply(drule_tac x = lista in spec) apply(auto)
         apply(rotate_tac -2) apply(drule_tac x = "[]" in spec)
    apply(drule_tac ll3_consume_label_tail, auto)
       apply(rotate_tac -1)
       apply(frule_tac ll3_consume_label_noninterf, auto)  
    apply(thin_tac "(((n, n''), llt.LSeq [] (((n, n'), be) # ac)),
        ((a, b), llt.LLab True (length tl)), Suc nat # tl)
       \<in> ll3'_descend") apply(drule_tac ll3_consume_label_find, auto) apply(rotate_tac -1)
       apply(drule_tac x = "[]" in spec) apply(auto)

      apply(case_tac na, auto)
    apply(frule_tac ll3_descend_nonnil, auto)
    apply(case_tac "ll3_consume_label [] (Suc 0) lista", auto)
      apply(frule_tac ll_descend_eq_r2l) apply(auto)
      apply(case_tac hd, auto) apply(case_tac tl, auto)
      apply(drule_tac q = "(n, n')" and e = "[]" in ll_descend_eq_l2r_list)
    apply(thin_tac " (((n, n''), llt.LSeq [] (((n, n'), llt.LLab True (Suc nat)) # ac)),
        ((a, b), llt.LLab e' (length tl)), Suc nata # tl)
       \<in> ll3'_descend")
      apply(drule_tac ll3_assign_labels_backwards_fact, auto)
      apply(drule_tac x = lista in spec) apply(auto) apply(rotate_tac -2)
      apply(drule_tac x = "[]" in spec)
      apply(drule_tac ll3_consume_label_find) apply(auto) apply(rotate_tac -1)
      apply(drule_tac x=  "[]" in spec) apply(auto)

     apply(case_tac "ll3_consume_label [0] 0 ls2", auto)
    apply(case_tac ba, auto)
    apply(case_tac "ll3_consume_label [] (Suc 0) lista", auto)
     apply(case_tac "ll3_consume_label [] 0 ls2", auto)
     apply(case_tac "ll3_assign_label_list aa", auto)
    apply(frule_tac ll3_descend_nonnil, auto)
     apply(frule_tac ll_descend_eq_r2l) apply(auto)
     apply(case_tac hd, auto)
      
      apply(case_tac tl, auto)
       apply(drule_tac q = "(n, n')" and e = "rev ba" in ll_descend_eq_l2r_list)
      apply(drule_tac k = "ab#list" in ll3_assign_labels_backwards_fact, auto)
    apply(rotate_tac -1) apply(drule_tac x = aa in spec) apply(auto)
         apply(rotate_tac -2) apply(drule_tac x = "[]" in spec)
       apply(rotate_tac -1)
      apply(drule_tac ll3_consume_label_find) apply(auto) apply(rotate_tac -1)
      apply(drule_tac l = ls2 in ll3_consume_label_noninterf) apply(auto)
      apply(drule_tac x = "[0]" in spec) apply(auto)

    apply(thin_tac "(((n, n''), llt.LSeq [] (((n, n'), llt.LSeq (rev ba) ad) # ac)),
        ((a, b), llt.LLab e' (length tl)), Suc nat # tl)
       \<in> ll3'_descend")
    apply(drule_tac q = "(n, n')" and e = "[]" in ll_descend_eq_l2r_list)
                apply(drule_tac ll3_assign_labels_backwards_fact, auto)
      apply(drule_tac x = lista in spec) apply(auto) apply(rotate_tac -2)
      apply(drule_tac x = "[]" in spec)
      apply(drule_tac ll3_consume_label_find) apply(auto) apply(rotate_tac -1)
      apply(drule_tac x=  "[]" in spec) apply(auto)

(*
cons case
*)
(* we seem to need a new lemma here *)
(* in particular we need a lemma about combining together
valid3' facts *)
  (*  apply(rule_tac ll_valid3'.intros, auto)*)

(* one approach *)
      apply(subgoal_tac "0 < length (((a, b), ba) # list) ") 
       apply(drule_tac[1] ll3_consume_label_forward_child_cases) apply(auto)
      apply(drule_tac ll3_consume_label_tail) apply(auto)
    apply(frule_tac ll3_consumes_split) apply(auto)
        apply(drule_tac x = s' in spec) apply(rotate_tac -1)
        apply(drule_tac x = list in spec)
        apply(drule_tac n' = 0 in ll3_consume_gen) apply(auto)
    apply(case_tac ma, auto)
       apply(auto)
    apply(frule_tac [1] ll3_consumes.intros(4))
    apply(rule_tac[1] ll3_consumes.intros(3)) apply(auto)
(* older work *)
    apply(rotate_tac -1)
       apply(drule_tac ll3_consumes_split, simp) apply(auto 0 0)
      apply(rule_tac ll_valid3'.intros, auto 0 0)
      apply(drule_tac x = s' in spec) apply(rotate_tac -1)
    apply(drule_tac x = lista in spec) apply(auto 0 0)
    apply(rotate_tac -1)
       apply(drule_tac ll3_consumes_split, simp) apply(auto 0 0)

        apply(rule_tac ll_valid3'.intros) apply(auto 0 0)
        apply(drule_tac ll_valid_q.cases) apply(auto)

    apply(case_tac "ll3_consume_label [] 0
                 ls2", auto)
       apply(case_tac "ll3_assign_label_list aa", auto)

       apply(drule_tac ll3_consumes_split, simp) apply(auto 0 0)

      apply(drule_tac x = s' in spec) apply(rotate_tac -1)
    apply(drule_tac x = list in spec) apply(auto)

    (* idea: for this case we need to split consume_labels *)

    apply(rotate_tac -4)
    apply(drule_tac ll3_consumes_split) apply(auto 2 0)

       apply(drule_tac x = s'a in spec) apply(drule_tac x = list in spec) apply(auto 0 0)


      apply(drule_tac ll3_consumes_split, simp) apply(auto 0 0)
    
       apply(drule_tac x = s'a in spec) apply(drule_tac x = list in spec) apply(auto 0 0)
       apply(drule_tac ll3_consume_label_tail, auto 0 0)
    apply(frule_tac ll3_consume_label_char, auto 0 0)
       apply(drule_tac n' = 0 in ll3_consume_gen, auto 0 0)
    apply(case_tac m, auto 0 0 )
  
       apply(rule_tac ll_valid3'.intros(6), auto 0 0)
         apply(drule_tac ll_valid3'_child, auto 0 0)
        apply(rule_tac ll_descend_eq_l2r) apply(simp)
        apply(drule_tac ll3_consume_label_found, auto 0 0)

        apply(drule_tac x = n' in spec) apply(drule_tac x = n'' in spec)
    apply(thin_tac "\<forall>e l. h = llt.LSeq e l \<longrightarrow>
             (\<forall>s l'.
                 (l, s, l') \<in> ll3_consumes \<longrightarrow>
                 (\<forall>p'' l''.
                     ll3_consume_label [] 0 l' =
                     Some (l'', p'') \<longrightarrow>
                     (\<forall>l'''.
                         ll3_assign_label_list l'' =
                         Some l''' \<longrightarrow>
                         ((n, n'), llt.LSeq (rev p'') l''')
                         \<in> ll_valid3')))")
        apply(rule_tac ll_descend_eq_r2l_list) 
        apply(drule_tac x ="[]" in spec) apply(auto 0 0)
    apply(thin_tac "(((n', n''), llt.LSeq [] list),
        ((a, b), llt.LLab False (length pp)), nat # rev pp)
       \<in> ll3'_descend")

  (* one lemma we need is a forwards version of 'backwards_fact' *)
  (* maybe also need more non interference lemmas *)

(* for case 1 we need a forward fact about assign_labels not touching labels out of its depth *)
(* for case 2 ll3_consume_label_found might suffice  *)

    apply(drule_tac ll3_assign_label_preserve_labels') apply(auto 0 0)
    apply(simp)

    apply(frule_tac ll3_consume_label_found, auto)
      apply(case_tac m, auto) apply(rotate_tac -1)
    apply(drule_tac x = n in spec) apply(rotate_tac -1)
       apply(drule_tac x = n'' in spec) apply(rotate_tac -1)
    apply(drule_tac x = "[]" in spec) apply(auto)
       apply(rule_tac ll_valid3'.intros(6), auto)
    apply(case_tac h, safe)

    apply(thin_tac "((n', n''), t) \<in> ll_validl_q")
    apply(thin_tac "((n, n'), h) \<in> ll_valid_q") 
         apply(case_tac bc, auto)

 apply(thin_tac "((n', n''), t) \<in> ll_validl_q")
    apply(thin_tac "((n, n'), h) \<in> ll_valid_q") 
             apply(rule_tac ll_valid3'.intros)
             apply(drule_tac ll_validl_q.cases, auto)
              apply(drule_tac ll_valid_q.cases, auto)
             apply(drule_tac ll_valid_q.cases, auto)

 apply(thin_tac "((n', n''), t) \<in> ll_validl_q")
    apply(thin_tac "((n, n'), h) \<in> ll_valid_q") 
            apply(case_tac x21, auto)
             apply(rule_tac ll_valid3'.intros)
            apply(drule_tac ll_validl_q.cases, auto)
             apply(drule_tac ll_valid_q.cases, auto)

 apply(thin_tac "((n', n''), t) \<in> ll_validl_q")
    apply(thin_tac "((n, n'), h) \<in> ll_valid_q") 
                     apply(rule_tac ll_valid3'.intros)
             apply(drule_tac ll_validl_q.cases, auto)
              apply(drule_tac ll_valid_q.cases, auto)

 apply(thin_tac "((n', n''), t) \<in> ll_validl_q")
    apply(thin_tac "((n, n'), h) \<in> ll_valid_q") 
                     apply(rule_tac ll_valid3'.intros)
             apply(drule_tac ll_validl_q.cases, auto)
    apply(drule_tac ll_valid_q.cases, auto)

       apply(case_tac "ll3_consume_label [] 0 x52", auto)
    apply(rename_tac boo)
         apply(case_tac "ll3_assign_label_list ad", auto)
             apply(rule_tac ll_valid3'.intros, auto)

  (* seq case *)
 apply(thin_tac "((n', n''), t) \<in> ll_validl_q")
    apply(thin_tac "((n, n'), h) \<in> ll_valid_q") 
            apply(drule_tac ll_validl_q.cases, auto)
    apply(drule_tac ll_valid_q.cases, auto)

    apply(simp)

         apply(drule_tac x = s' in spec) apply(drule_tac x = list in spec) apply(auto)
         apply(case_tac h, auto)
             apply(case_tac "ll3_consume_label [] (Suc 0) list", auto)
            apply(case_tac x22, auto) apply(case_tac x21, auto)
            apply(case_tac "ll3_consume_label [] (Suc 0) list", auto)
           apply(case_tac "ll3_consume_label [] (Suc 0) list", auto)
          apply(case_tac "ll3_consume_label [] (Suc 0) list", auto)

         apply(case_tac "ll3_consume_label [] 0 x52a", auto)
          apply(case_tac "ll3_consume_label [0] 0 x52a", auto)
          apply(case_tac ba, auto)
            apply(case_tac "ll3_consume_label [] (Suc 0) list", auto)

    apply(drule_tac ll3_consume_label_tail)
    apply(case_tac boo, auto)

    apply(thin_tac "(((n, n''), llt.LSeq [] (((n, n'), be) # ac)),
        ((a, b), llt.LLab True (length tl)), Suc nat # tl)
       \<in> ll3'_descend") apply(drule_tac ll3_consume_label_find, auto) apply(rotate_tac -1)
       apply(drule_tac x = "[]" in spec) apply(auto)

    

(* things are sort of good up until here...*)
    apply(thin_tac "(((n, n''), llt.LSeq [] (((aa, bb), llt.LSeq e ls) # ac)),
        ((a, b), llt.LLab e' (Suc (length list))), 0 # ad # list)
       \<in> ll3'_descend")
      apply(drule_tac ll3_assign_labels_backwards_fact, auto)
    apply(drule_tac x = ls' in spec) apply(auto)

      apply(case_tac e, auto)
       apply(frule_tac ll3_consume_label_unch, auto)
       apply(rotate_tac [1] -2) apply(drule_tac x = "[]" in spec)
       apply(frule_tac ll3_consume_label_find, auto)
       apply(rotate_tac [1] -1) apply(drule_tac x = "[0]" in spec)
       apply(auto)

      apply(drule_tac ll3_consume_label_found, auto)
    apply(rotate_tac[1] -1)
    apply(drule_tac x = a in spec) apply(rotate_tac [1] -1) apply(drule_tac x = b in spec)
    apply(rotate_tac -2)
    apply(drule_tac ll3_assign_labels_backwards_fact, auto)
      apply(drule_tac l = lsa and p' = "rev listb @ [ab]" in ll3_consume_label_noninterf)
    apply(auto)

(*
    apply(frule_tac p = "[]" and ls = lsa in ll3_consume_label_found) apply(auto)
 *)     

       apply(frule_tac k = "ad#list" in ll3_consume_label_find) apply(auto)
    apply(rotate_tac[1] -1) apply(drule_tac x = "[0]" in spec) apply(auto)

(*
i think i have a plan of attack for this case
- prove a backwards fact about consumes
- prove non-interference between different depths of consumes
*)

    apply(case_tac "ll3_consume_label [] 0 ls")
          apply(auto)
    apply(rename_tac boo)
         apply(case_tac "ll3_assign_label_list ab", auto)
         apply(drule_tac ll_valid3'.cases, auto)
      
          apply(drule_tac[1] x = "aa # list" in spec)
    apply(rotate_tac [1] -1)
          apply(drule_tac[1] x = "a" in spec)     apply(rotate_tac [1] -1)
          apply(drule_tac[1] x = "b" in spec)    apply(rotate_tac[1] -1)
      
          apply(drule_tac[1] x = "e'" in spec)  apply(auto)
    apply(thin_tac "(((n, n''),
         llt.LSeq [] (((n, n'), llt.LSeq [] l) # ac)),
        ((a, b), llt.LLab e' (Suc (length list))),
        0 # aa # list)
       \<in> ll3'_descend")
    apply(drule_tac e' = e in ll3'_descend_relabel)
          apply(auto)

    apply(drule_tac [1] ll3_assign_labels_backwards_fact) apply(auto)
     apply(drule_tac ll3_consumes_split) apply(auto)
       apply(frule_tac ll3_descend_nonnil) apply(auto)
     apply(drule_tac ll3_consume_label_find) apply(auto)
     apply(rotate_tac[1] 5)
     apply(drule_tac x = "[]" in spec) apply(auto)
     apply(rotate_tac[1] -1)
    apply(drule_tac x = 

        apply(drule_tac ll3_consumes_split, clarsimp)
    apply(auto)
    apply(frule_tac ll3_consume_label_tail, auto)
           apply(drule_tac [1] n' = "0" in ll3_consume_nil_gen, auto)
       apply(frule_tac ll3_descend_nonnil) apply(auto)
       apply(drule_tac x = s' in spec) apply(rotate_tac [1] 3)
    apply(drule_tac x = lista in spec) apply(auto)
    apply(drule_tac ll_descend_eq_r2l) apply(auto)
       apply(case_tac hd, auto)
    apply(case_tac tl, auto)
        apply(drule_tac ll_descend_eq_l2r)

(* *)
       apply(drule_tac ll3_consume_label_find) apply(auto)

    apply(thin_tac "\<forall>e l. h = llt.LSeq e l \<longrightarrow>
             (\<forall>s l'. (l, s, l') \<in> ll3_consumes \<longrightarrow>
                     (\<forall>p'' l''.
                         ll3_consume_label [] 0 l' = Some (l'', p'') \<longrightarrow>
                         (\<forall>l'''. ll3_assign_label_list l'' = Some l''' \<longrightarrow>
                                 ((n, n'), llt.LSeq (rev p'') l''') \<in> ll_valid3')))")
    apply(drule_tac x = "[]" in spec) apply(auto)
    apply(thin_tac "ll3_consume_label [] 0 (((n, n'), h) # lista) =
       Some (((n, n'), h) # lista, [])")
       apply(drule_tac [1] n' = "0" in ll3_consume_nil_gen, auto)
       apply(rule_tac[1] ll_valid3'.intros) apply(auto)
        apply(drule_tac ll_valid3'_child, auto)

       apply(frule_tac[1] ll3_descend_nonnil) apply(auto)
       apply(case_tac hd, auto)
    apply(frule_tac ll3_consume_label_find, auto)
    apply(frule_tac[1] ll_descend_eq_r2l2) apply(drule_tac ll3'_descend_alt.cases, auto)
       apply(drule_tac ll_valid3'.cases) apply(auto)
    apply(case_tac [1] "ll3_consume_label p (Suc na) ac", auto)
    apply(case_tac be, auto)


    apply(thin_tac "\<forall>e l. h = llt.LSeq e l \<longrightarrow>
             (\<forall>s l'. (l, s, l') \<in> ll3_consumes \<longrightarrow>
                     (\<forall>p'' l''.
                         ll3_consume_label [] 0 l' = Some (l'', p'') \<longrightarrow>
                         (\<forall>l'''. ll3_assign_label_list l'' = Some l''' \<longrightarrow>
                                 ((n, n'), llt.LSeq (rev p'') l''') \<in> ll_valid3')))")
    apply(drule_tac[1] x = "[]" in spec) apply(drule_tac x = lista in spec) apply(auto)
    apply(drule_tac x = 


       apply(rule_tac ll_valid3'.intros) apply(auto)
    apply(case_tac "ll3_assign_label ((n, n'), h)", auto)
        apply(case_tac " ll3_assign_label_list list", auto)
        apply(drule_tac ll3_consume_label_tail)
      
        apply(drule_tac x = s' in spec)
        apply(drule_tac x = list in spec)
        apply(drule_tac x = "[]" in spec)
        apply(drule_tac n' = 0 and p' = "[]" in ll3_consume_nil_gen) apply(auto)
        apply(drule_tac ll_valid3'_child) apply(auto)

    apply(drule_tac ll_valid3'.cases) apply(auto)

        apply(drule_tac ll3_consumes.intros)
    apply(frule_tac s = "[]" in ll3_consumes_split, auto)
        
        apply(case_tac s'a, auto)
    apply(drule_tac ll3_consumes_unch, auto)
    apply(drule_tac ll3_consumes.cases, auto)
      
    apply(drule_tac x = list in spec) apply(auto)


    sorry
qed
*)


fun ll3_unwrap :: "(ll3 list \<Rightarrow> 'a option) \<Rightarrow> ll3  \<Rightarrow> 'a option" where
  "ll3_unwrap f (_, LSeq _ ls) = f ls"
  | "ll3_unwrap _ (_, _) = None"
 
value "(ll3_init (ll_pass1 (ll1.LSeq [ll1.LLab 0])))"
value "ll3_assign_label (ll3_init (ll_pass1 (ll1.LSeq [ll1.LLab 0])))"
value "ll3_assign_label (ll3_init (ll_pass1 (ll1.LSeq [ll1.LSeq [ll1.LLab 0], ll1.LSeq [], ll1.LSeq [ll1.LLab 1]])))"

(* get the label at the provided childpath, if it exists *)
(* rewrite in terms of get_node? *)
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

value "(case prog3 of
Some p' \<Rightarrow> Some (check_ll3 p')
| _ \<Rightarrow> None)"

(* TODO: a "wrapper" function for check_ll3
that doesn't increment counter the first time *)


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


(* this should take an ll4 *)
(*  TODO everything from here onward should take ll4 *)
(* make this mutually recursive with a "consume" function?  *)
(* the first nat argument is a location in buffer,
   the second is the current child index 
   the first nat should be optional, that is, None if there is
   no label at that node
*)
(* NB the childpath output by this function ought to be reversed *)
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

lemma divmod_decrease [rule_format]:
"(! n' . fst (Divides.divmod_nat n 256) = Suc n' \<longrightarrow>
    Suc n' < n)
 "
  apply(induction n)
   apply(auto)
  done

(* TODO ensure these are coming out in the right order *)
(* TODO this terminates because divmod decreases number *)
function output_address :: "nat \<Rightarrow> 8 word list" where
    "output_address n = (case Divides.divmod_nat n 256 of
                         (0, mo) \<Rightarrow> [Evm.byteFromNat mo]
                        |(Suc n, mo) \<Rightarrow> (Evm.byteFromNat mo)#(output_address (Suc n)))"
  by auto
termination
  apply(relation "measure (\<lambda> x . x)")
   apply(auto)
  apply(subgoal_tac "fst (Divides.divmod_nat n 256) = Suc nat")
   apply(drule_tac divmod_decrease) apply(simp)
  apply(case_tac "Divides.divmod_nat n
        256", auto)
  done

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

(* NEW pipeline
pass1 \<Rightarrow> ll3 init \<Rightarrow>
assign_label \<Rightarrow> check ll3 \<Rightarrow>
process_jumps_loop \<Rightarrow> (? check ll3?) \<Rightarrow> 
write_jump_targets \<Rightarrow> check ll3
*)
(*
lemmas we still need:
- bump preserves ll3 validity, but shifted (qvalidity might suffice)
- inc_jump preserves ll3 validity (maybe just qvalidity) for overall list (but may expand)
- process_jumps_loop preserves ll3 validity (maybe just qvalidity)
- if write_jump_targets succeeds, there was exactly enough room for all jumps
  (maybe just check this)
- if write_jump_targets succeeds, the target corresponds to the sequence node represented by the label
- finally we want a lemma related to the behavior of jumps within the sequence of instrs
  - ie, jumps resolve to the correct label
  - is it enough to just to have the previous lemma?
  - we probably need to relate it to the locations in the buffer occupied by the labels

More ideas:
jumps always follow push instructions (?)
*)
(*
by the end of this procedure, we should have valid3' as well as the fact that
jumps are all able to fit
*)

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



fun gather_ll1_labels :: "ll1 \<Rightarrow> childpath \<Rightarrow> nat \<Rightarrow> childpath list" 
and gather_ll1_labels_list :: "ll1 list \<Rightarrow> childpath \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> childpath list" where
"gather_ll1_labels (ll1.L _) _ _ = []"
| "gather_ll1_labels (ll1.LJmp _) _ _ = []"
| "gather_ll1_labels (ll1.LJmpI _) _ _ = []"
| "gather_ll1_labels (ll1.LLab n) cp d = 
     (if n = d then [cp] else [])"
| "gather_ll1_labels (ll1.LSeq ls) cp d =
   gather_ll1_labels_list ls cp 0 (d+1)"
| "gather_ll1_labels_list [] _ _ _ = []"
| "gather_ll1_labels_list (h#t) cp ofs d =
   gather_ll1_labels h (cp@[ofs]) (d) @
   gather_ll1_labels_list t cp (ofs+1) d"


(*Semantics for LL1
leave state parametric for now
allow for an interpretation of instructions on this state
as well as for deciding whether to jump *)
(* we will have to resolve some issues around program counter
   (probably hiding it completely from the source program) 
   we can have some kind of bogus injection back into "real" EVM states
   when we want to run an instruction
   later on we will probably have to revise
 *)
(* TODO: make ll1 parametric in an instruction type? *)
(* TODO: decrement fuel only for backwards jumps? *)
(*
TODO: change jmpred so it can change state
*)
fun ll1_sem :: 
  "ll1 \<Rightarrow>
   (inst \<Rightarrow> 'a \<Rightarrow> 'a option) \<Rightarrow> (* inst interpretation *)
   ('a \<Rightarrow> (bool * 'a) option) \<Rightarrow> (* whether JmpI should execute or noop in any given state *)
   nat \<Rightarrow> (* fuel *)
   nat option \<Rightarrow> (* depth, if we are scanning for a label *)
(* continuations corresponding to enclosing scopes *)
   (('a \<Rightarrow> 'a option) list) \<Rightarrow>
   ('a \<Rightarrow> 'a option) \<Rightarrow> (* continuation *)
   ('a \<Rightarrow> 'a option)" 
and ll1_list_sem ::
 "ll1 list \<Rightarrow>
   (inst \<Rightarrow> 'a \<Rightarrow> 'a option) \<Rightarrow> (* inst interpretation *)
   ('a \<Rightarrow> (bool * 'a) option) \<Rightarrow> (* whether JmpI should execute or noop in any given state *)
   nat \<Rightarrow> (* fuel *)
   nat option \<Rightarrow> (* depth, if we are scanning for a label *)
(* continuations corresponding to enclosing scopes *)
   (('a \<Rightarrow> 'a option) list) \<Rightarrow>
   ('a \<Rightarrow> 'a option) \<Rightarrow> (* continuation *)
   ('a \<Rightarrow> 'a option)" 
where

(* list_sem cases *)

(* non seeking, nil means noop *)
 "ll1_list_sem [] denote jmpd n None scopes cont = cont"
(* when seeking, nil means we failed to find something we should have *)
| "ll1_list_sem [] denote jmpd n (Some _) scopes cont = (\<lambda> _ . None)"

| "ll1_list_sem (h#t) denote jmpd n None scopes cont =
   (if n = 0 then (\<lambda> _ . None)
    else ll1_sem h denote jmpd (n - 1) None scopes
    (ll1_list_sem t denote jmpd (n - 1) None scopes cont))"

(* do we need to increment d here? *)
| "ll1_list_sem (h#t) denote jmpd n (Some d) ctx cont =
   (if n = 0 then (\<lambda> _ . None) else
   (case gather_ll1_labels h [] d of
    [] \<Rightarrow> ll1_list_sem t denote jmpd (n - 1) (Some d) ctx cont
   | _ \<Rightarrow> ll1_sem h denote jmpd (n - 1) (Some (Suc d)) ctx (ll1_list_sem t denote jmpd (n - 1) None ctx cont)))"


(* first, deal with scanning cases *)
(* TODO we should include semantics of the label itself *)

(* NB we only call ourselves in "seek" mode on a label when we are sure of finding a label *)
| "ll1_sem (ll1.LLab d) _ _ n (Some d') _ cont = 
   (if d + 1 = d' then cont
    else (\<lambda> s . None ))"

(* bail if we can't find a label in  the entire thing we were seeking in *)
(* TODO this case may still be messed up *)
| "ll1_sem (ll1.LSeq ls) denote jmpd n (Some d) scopes cont =
   (if n = 0 then (\<lambda> _ . None)
    else 
    ll1_list_sem ls denote jmpd (n - 1) (Some d)
       ((ll1_sem (ll1.LSeq ls) denote jmpd (n - 1) (Some 0) scopes cont)#scopes)
       cont)"

(* for anything else, seeking is a no op *)
| "ll1_sem _ _ _ n (Some d) _ cont = cont"

(* "normal" (non-"scanning") cases *)
| "ll1_sem (ll1.L i) denote _ n None scopes cont =
  (\<lambda> s . case denote i s of
           Some r \<Rightarrow> cont r
          | None \<Rightarrow> None)"
| "ll1_sem (ll1.LLab d) denote _ n None scopes cont = cont"
| "ll1_sem (ll1.LJmp d) denote _ n None scopes cont = scopes ! d"
| "ll1_sem (ll1.LJmpI d) denote jmpd n None scopes cont =
(\<lambda> s . case (jmpd s) of
        None \<Rightarrow> None
        | Some (True, s') \<Rightarrow> ((scopes ! d) s')
        | Some (False, s') \<Rightarrow> cont s')"

(* new idea for Seq case *)
(* problem - are we passing the wrong continuation in? *)
| "ll1_sem (ll1.LSeq ls) denote jmpd n None scopes cont =
   (if n = 0 then (\<lambda> _ . None)
    else
     ll1_list_sem ls denote jmpd (n - 1) None
      (* this scope continuation was ll1_sem before *)
      ((ll1_sem (ll1.LSeq ls) denote jmpd (n - 1) (Some 0) scopes cont)#scopes) cont)"

(* a sample instantiation of the parameters for our semantics *)
(* state is a single nat, ll1.L increments
except for SUB, which subtracts *)

fun silly_denote :: "inst \<Rightarrow> nat \<Rightarrow> nat option" where
"silly_denote (Arith SUB) 0 = None"
|"silly_denote (Arith SUB) (Suc n) = Some n"
|"silly_denote _ n = Some (Suc n)"

fun silly_jmpred :: "nat \<Rightarrow> bool" where
"silly_jmpred n = (n = 0)"

fun silly_ll1_sem :: 
  "ll1 \<Rightarrow>
   nat \<Rightarrow> (* fuel *)
(* continuations corresponding to enclosing scopes *)
   (nat \<Rightarrow> nat option) \<Rightarrow> (* continuation *)
   (nat \<Rightarrow> nat option)" where
"silly_ll1_sem x n c = ll1_sem x silly_denote silly_jmpred n None [] c"

definition ll1_sem_test1 where
"ll1_sem_test1 f i = silly_ll1_sem (ll1.LSeq [ll1.LLab 0, ll1.LJmpI 0]) f (Some) i"

(* weirdly it seems to crash in the generated code when it loops infinitely? *)
(* this could be a problem leading to need to better control execution *)
value "ll1_sem_test1 20 0"
value "ll1_sem_test1 20 3"

(* "if" statement *)
(* if 0, add 1. otherwise subtract 1*)
definition ll1_sem_test2 where
"ll1_sem_test2 f i = silly_ll1_sem
  (ll1.LSeq [
    ll1.LSeq [ ll1.LJmpI 0,
               ll1.L (Arith SUB),
               ll1.LJmp 1, 
               ll1.LLab 0,
               ll1.L (Arith ADD),
               ll1.LLab 1 ]]) f (Some) i"

value "ll1_sem_test2 100 0"
value "ll1_sem_test2 100 1"
value "ll1_sem_test2 100 2"

(* 1 armed if statement *)
definition ll1_sem_test2' where
"ll1_sem_test2' f i = silly_ll1_sem
  (ll1.LSeq [ll1.LJmpI 0,
               ll1.L (Arith ADD),
               ll1.LLab 0]) f (Some) i"


value "ll1_sem_test2' 100 0"
value "ll1_sem_test2' 100 27"

(* "do-while" loop *)
(* subtract 1 each iteration until 0 is reached *)
(* if we start at 0 return *)
(* something is wrong with loop case *)
definition ll1_sem_test3 where
"ll1_sem_test3 f i = silly_ll1_sem
(ll1.LSeq [ll1.LSeq [ll1.LJmpI 1,
                     ll1.LLab 0,
                     ll1.L (Arith SUB),
                     ll1.LJmpI 1,
                     ll1.LJmp 0, ll1.LLab 1]]) f Some i"

value "ll1_sem_test3 120 4"
value "ll1_sem_test3 120 0"

(* NB *)
value "ll1_sem_test3 20 15"
value "ll1_sem_test3 21 15"

(* test to ensure things are being run in correct order,
as well as check correctness for sequences without labels *)
definition ll1_sem_test4 where
"ll1_sem_test4 f i = silly_ll1_sem
(ll1.LSeq [ll1.L (Arith SUB), ll1.L (Arith ADD)]) f Some i"

value "ll1_sem_test4 10 0"
value "ll1_sem_test4 10 1"

(* ensure invalid jumps crash *)
definition ll1_sem_test5 where
"ll1_sem_test5 f i = silly_ll1_sem
(ll1.LSeq [ll1.LJmpI 0]) f Some i"

value "ll1_sem_test5 10 0"

(*
NB doing a small step version of this semantics would be hard
because the state is transiently different in terms of stack contents
*)

(* for now we are just passing constant context around too *)
type_synonym ellest = "variable_ctx * constant_ctx * network"

(* TODO: check that instruction is allowed *)
(* TODO: actually deal with InstructionToEnvironment reasonably *)
fun elle_denote :: "inst \<Rightarrow> ellest \<Rightarrow> ellest option" where
"elle_denote i (vc, cc, n) =
 (case instruction_sem vc cc i n of
  InstructionContinue vc' \<Rightarrow>
    Some(vc', cc, n)
  | InstructionToEnvironment _ vc' _ \<Rightarrow>
    Some(vc', cc, n))"

(* TODO need to unpack correctly *)
(* NB we make no update to keep the PC correct *)
fun elle_jmpd :: "ellest \<Rightarrow> (bool * ellest) option" where
"elle_jmpd (v, c, n) =
 (case (vctx_stack v) of
   cond # rest \<Rightarrow>
    (let new_env = (( v (| vctx_stack := (rest) |))) in
    strict_if (cond =(((word_of_int 0) ::  256 word)))
           (\<lambda> _ . Some (True, (new_env, c, n) ))
           (\<lambda> _ .Some (False, (new_env, c, n))))
  | _ \<Rightarrow> None)"

definition w256_0 where "w256_0 = word256FromNat 0"
definition w160_0 where "w160_0 = word160FromNatural 0"

(* now we need to get our hands on a valid initial state *)
(* body of this copied from Evm.thy *)
(* can we get away with this? *)
(* need to marshal things to w256 *)
(* TODO:
variable context:
- gas (supply this as an argument)
- block
*)

definition elle_init_block :: "block_info"
  where
"elle_init_block =\<lparr>
block_blockhash = (\<lambda> x . x),
  block_coinbase = w160_0,
  block_timestamp = w256_0,
  block_number = w256_0,
  block_difficulty = w256_0,
  block_gaslimit = w256_0 
\<rparr>"

definition elle_init_vctx :: "int \<Rightarrow> variable_ctx"
  where "elle_init_vctx gas_in = 
\<lparr> vctx_stack = ([]), (* The stack is initialized for every invocation *)
    vctx_memory = empty_memory, (* The memory is also initialized for every invocation *)
     vctx_memory_usage =(( 0 :: int)), (* The memory usage is initialized. *)
     vctx_storage = empty_storage, (* The storage is taken from the account state *)
     vctx_pc =(( 0 :: int)), (* The program counter is initialized to zero *)
     vctx_balance = (\<lambda> (addr::address) . 
                         w256_0 (* can we get away with this *)),
     vctx_caller = w160_0, (* the caller is specified by the environment *)
     vctx_value_sent = w256_0, (* the sent value is specified by the environment *)
     vctx_data_sent = [], (* the sent data is specified by the environment *)
     vctx_storage_at_call = empty_storage, (* the snapshot of the storage is remembered in case of failure *)
     vctx_balance_at_call = (\<lambda> (addr::address) . 
                         w256_0 (* can we get away with this *)), (* the snapshot of the balance is remembered in case of failure *)
     vctx_origin = w160_0, (* assume a 0 gas price *)
     vctx_ext_program = (\<lambda> _ . empty_program), (* external programs are empty. *)
     vctx_block = elle_init_block, (* bogus block. *)
     vctx_gas = gas_in, (* parameter. *)
     vctx_account_existence = (\<lambda> _ . False), (* existence is chosen arbitrarily *)
     vctx_touched_storage_index = ([]),
     vctx_logs = ([]),
     vctx_refund =(( 0 :: int)), (* the origin of the transaction is arbitrarily chosen *)
     vctx_gasprice = w256_0
   \<rparr>"

definition elle_init_cctx :: constant_ctx
  where
"elle_init_cctx =
\<lparr> cctx_program = empty_program,
  cctx_this = w160_0,
  cctx_hash_filter = (\<lambda> _ . False)
\<rparr>"

definition ellest_init :: "int \<Rightarrow> ellest" where
"ellest_init g = (elle_init_vctx g, elle_init_cctx, Metropolis)"


fun elle_sem :: 
  "ll1 \<Rightarrow>
   nat \<Rightarrow> (* fuel *)
(* continuations corresponding to enclosing scopes *)
   (ellest \<Rightarrow> ellest option) \<Rightarrow> (* continuation *)
   (ellest \<Rightarrow> ellest option)" where
"elle_sem x n c = ll1_sem x elle_denote elle_jmpd n None [] c"