theory ElleCorrect
  imports Main "ElleSyntax" "ElleSemantics" "ElleCompiler"
begin



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

(* TODO: need cp_less? cp_rev_less? *)

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

(* TODO: need consumes? *)

(* need:
- assign label qvalid
- 
*)
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

(* building up to assign label q valid proof *)
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


lemma ll3_descend_singleton [rule_format] :
"(t1, t2, k) \<in> ll3'_descend \<Longrightarrow>
(! x . k = [x] \<longrightarrow>
  (? q1 e1 ls . t1 = (q1, LSeq e1 ls) \<and> x < length ls \<and> ls ! x = t2))"
  apply(induction rule:ll3'_descend.induct)
   apply(auto)
  apply(case_tac n, auto) apply(drule_tac[1] ll3_descend_nonnil, auto)
    apply(drule_tac[1] ll3_descend_nonnil, auto)
    apply(drule_tac[1] ll3_descend_nonnil, auto)
   apply(drule_tac[1] ll3_descend_nonnil, auto) apply(drule_tac[1] ll3_descend_nonnil, auto)
  apply(drule_tac[1] ll3_descend_nonnil, auto) apply(drule_tac[1] ll3_descend_nonnil, auto)
  done

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

lemma my_rev_conv :
"l1 = l2 \<Longrightarrow>
rev l1 = rev l2"
  apply(insert List.rev_is_rev_conv)
  apply(auto)
  done

lemma numnodes_child [rule_format] :
"((a, b), ba) \<in> set ls \<Longrightarrow>
       numnodes ((a, b), ba)
       < Suc (numnodes_l ls)"
  apply(induction ls)
   apply(auto)
  done


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

lemma ll3_descend_splitpath_cons :
"(t1, t3, k1#k2) \<in> ll3'_descend \<Longrightarrow>
( case k2 of
   [] \<Rightarrow> ((t1, t3, [k1]) \<in> ll3'_descend)
   |  _ \<Rightarrow> (? t2 . (t1, t2, [k1]) \<in> ll3'_descend \<and> (t2, t3, k2) \<in> ll3'_descend))"
  apply(insert ll3_descend_splitpath[of t1 t3 "[k1]" k2]) apply(auto)
  done

lemma ll_descend_eq_l2r_list :
" ll_get_node_list (l) (kh#kt) = Some t \<Longrightarrow>
    ((q, LSeq e l), t, kh#kt) \<in> ll3'_descend"
  apply(case_tac l, auto)
  apply(rule_tac ll_descend_eq_l2r) apply(auto)
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

lemma ll_valid3'_child :
"(q, LSeq p l) \<in> ll_valid3' \<Longrightarrow>
 x \<in> set l \<Longrightarrow>
 x \<in> ll_valid3'"
  apply(drule_tac ll_valid3'.cases, auto)
   apply(case_tac x, auto)
  apply(case_tac x, auto)
  done


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

(* "q-validity" for backend functions
lemma ll_bump_valid [rule_format]:
  "((x, (t :: ('lix, 'llx, 'ljx, 'ljix, 'llx, 'ptx, 'pnx) llt)) \<in> ll_valid_q \<longrightarrow> (! b . ((ll_bump b (x,t))) \<in> ll_valid_q)) \<and>
   (((m,m'), (l :: ('lix, 'llx, 'ljx, 'ljix, 'llx, 'ptx, 'pnx) ll list)) \<in> ll_validl_q \<longrightarrow> (! b' .((m+b', m'+b'), map (ll_bump b') l) \<in> ll_validl_q))"
proof(induction rule: ll_valid_q_ll_validl_q.induct) 

*)

lemma ll4_init_qvalid [rule_format]:
  "((x, (t :: ll3t)) \<in> ll_valid_q \<longrightarrow> (((ll4_init (x,t))) \<in> ll_valid_q)) \<and>
   (((m,m'), (l :: ll3 list)) \<in> ll_validl_q \<longrightarrow> ((m, m'), map ll4_init l) \<in> ll_validl_q)"
proof(induction rule: ll_valid_q_ll_validl_q.induct)
case (1 i x e)
  then show ?case
    apply(auto simp add:ll_valid_q_ll_validl_q.intros)
done next
  case (2 x d e)
  then show ?case
    apply(case_tac x, auto simp add:ll_valid_q_ll_validl_q.intros)
    done
next
  case (3 x d e s)
  then show ?case
    apply(case_tac x, auto simp add:ll_valid_q_ll_validl_q.intros)
    done
next
case (4 x d e s)
  then show ?case
    apply(case_tac x, auto simp add:ll_valid_q_ll_validl_q.intros)
    done
next
  case (5 n l n' e)
  then show ?case 
    apply(case_tac x, auto simp add:ll_valid_q_ll_validl_q.intros)
    done
next
  case (6 n)
  then show ?case
    apply(auto simp add:ll_valid_q_ll_validl_q.intros)
    done
next
  case (7 n h n' t n'')
  then show ?case 
    apply(auto simp add:ll_valid_q_ll_validl_q.intros)
    apply(case_tac h, auto simp add:ll_valid_q_ll_validl_q.intros)
    done
qed 

lemma ll3_bump_qvalid' [rule_format]:
  "((x, (t :: ll3t)) \<in> ll_valid_q \<longrightarrow> 
      (! e ls . t = LSeq e ls \<longrightarrow>
      (! b .  ((fst x+b,snd x+b), LSeq e (ll3_bump b ls)) \<in> ll_valid_q))) \<and>
   (((m,m'), (l :: ll3 list)) \<in> ll_validl_q \<longrightarrow>
      (! b . ((m+b, m'+b), ll3_bump b l) \<in> ll_validl_q))"
proof(induction rule: ll_valid_q_ll_validl_q.induct)
case (1 i x e)
then show ?case by (auto simp add:ll_valid_q_ll_validl_q.intros)
next
  case (2 x d e)
  then show ?case by (auto simp add:ll_valid_q_ll_validl_q.intros)
next
  case (3 x d e s)
then show ?case by (auto simp add:ll_valid_q_ll_validl_q.intros)
next
  case (4 x d e s)
  then show ?case by (auto simp add:ll_valid_q_ll_validl_q.intros)
next
  case (5 n l n' e)
  then show ?case
    apply(auto)
    apply(rule_tac ll_valid_q_ll_validl_q.intros) apply(auto)
    done
next
  case (6 n)
  then show ?case
    apply(auto simp add:ll_valid_q_ll_validl_q.intros)
done next
  case (7 n h n' t n'')
  then show ?case 
    apply(auto simp add:ll_valid_q_ll_validl_q.intros)
    apply(drule_tac x = b in spec)
    apply(case_tac h, auto simp add:ll_valid_q_ll_validl_q.intros)
       apply(rule_tac ll_valid_q_ll_validl_q.intros) apply(auto)
    apply(drule_tac ll_valid_q.cases, auto)
       apply(auto simp add:ll_valid_q_ll_validl_q.intros)
      apply(drule_tac ll_valid_q.cases, auto)
      apply(auto simp add:ll_valid_q_ll_validl_q.intros)
      apply(drule_tac ll_valid_q.cases, auto)
     apply(auto simp add:ll_valid_q_ll_validl_q.intros)

      apply(drule_tac ll_valid_q.cases, auto)
    apply(auto simp add:ll_valid_q_ll_validl_q.intros)
    done

qed


lemma ll3_bump_qvalid [rule_format]:
"(((m,m'), (l :: ll3 list)) \<in> ll_validl_q \<longrightarrow>
      (! b . ((m+b, m'+b), ll3_bump b l) \<in> ll_validl_q))"
  apply(insert ll3_bump_qvalid')
  apply(blast)
  done

(*
prove ll3 bump is equal to ll bump
(TODO - i think we get all we need out of the qvalidity proof *)
(*
- ll4 init preserves q validity (done)
- ll3 bump (done)
- inc jump (done)
- inc jump wrap (done)
- process jumps loop (done)
(later we'll need to 
prove properties about resolve_jump)
- what about write_jump_targets?
  - prove it doesn't overflow available space, IF jump check succeeds 
  - need a jump space-validity predicate?
*)
(*
now we need a validity predicate for ll3s that are ready to become ll4s
(that is, ll3s output by successfully running inc_jumps)
*)

lemma ll3_inc_jump_nil [rule_format] :
"ll3_inc_jump [] na p = (l', b) \<Longrightarrow>
 l' = [] \<and> b = False
 "
  apply(simp)
  done

(* do we need my_ll_induct? *)
lemma ll3_inc_jump_nilcp' [rule_format] :
"((x, (t :: ll3t)) \<in> ll_valid_q \<longrightarrow>
  (! e ls . t = LSeq e ls \<longrightarrow>
   (! n ls' b . ll3_inc_jump ls n [] = (ls', b) \<longrightarrow>
    b = False))) \<and>
  (((m,m'), (l :: ll3 list)) \<in> ll_validl_q \<longrightarrow>
    (! n l' b . ll3_inc_jump l n [] = (l', b) \<longrightarrow>
    b = False))"
proof(induction rule: ll_valid_q_ll_validl_q.induct)
  case (1 i x e)
  then show ?case by auto
next
case (2 x d e)
  then show ?case by auto
next
  case (3 x d e s)
  then show ?case by auto
next
  case (4 x d e s)
  then show ?case by auto
next
  case (5 n l n' e)
  then show ?case by auto
next
  case (6 n)
  then show ?case by auto
next
  case (7 n h n' t n'')
  then show ?case
    apply(auto)
    apply(case_tac "ll3_inc_jump t (Suc na) []", auto)
    apply(drule_tac x = "Suc na" in spec)
    apply(drule_tac x = a in spec) apply(auto)
    done
qed

lemma ll3_inc_jump_nilcp [rule_format] :
"(((m,m'), (l :: ll3 list)) \<in> ll_validl_q \<longrightarrow>
    (! n l' b . ll3_inc_jump l n [] = (l', b) \<longrightarrow>
    b = False))"
  apply(insert ll3_inc_jump_nilcp')
  apply(auto) apply(blast)
  done

lemma ll3_inc_jump_qvalid'[rule_format]:
  "((x, (t :: ll3t)) \<in> ll_valid_q \<longrightarrow> 
      (! e ls . t = LSeq e ls \<longrightarrow>
      (! n p b ls' . ll3_inc_jump ls n p = (ls', b) \<longrightarrow>
         (if b then ((fst x, snd x +1), LSeq e ls') \<in> ll_valid_q
               else (x, LSeq e ls') \<in> ll_valid_q)))) \<and>
   (((m,m'), (l :: ll3 list)) \<in> ll_validl_q \<longrightarrow>
      (! n p b l' . ll3_inc_jump l n p = (l', b) \<longrightarrow>
         (if b then ((m,m'+1), l') \<in> ll_validl_q
               else ((m,m'), l') \<in> ll_validl_q)))"
proof(induction rule: ll_valid_q_ll_validl_q.induct)
case (1 i x e)
  then show ?case by auto
next
  case (2 x d e)
  then show ?case by auto
next
  case (3 x d e s)
  then show ?case by auto
next
  case (4 x d e s)
  then show ?case by auto
next
  case (5 n l n' e)
  then show ?case 
    apply(clarsimp)
    apply(drule_tac x = na in spec) apply(drule_tac x = p in spec)
    apply(drule_tac x = b in spec) apply(drule_tac x = ls' in spec) apply(auto)
     apply(auto simp add:ll_valid_q_ll_validl_q.intros)
    done
next
  case (6 n)
  then show ?case
    apply(auto simp add:ll_valid_q_ll_validl_q.intros)
    done
next
  case (7 n h n' t n'')
  then show ?case
    apply(clarify)
    apply(case_tac h, auto)
             apply(case_tac "ll3_inc_jump t (Suc na) p", auto)
             apply(drule_tac x = "Suc na" in spec) apply(drule_tac x = p in spec)
    apply(drule_tac x = True in spec) apply(drule_tac x = a in spec) apply(auto)
             apply(auto simp add:ll_valid_q_ll_validl_q.intros)

            apply(case_tac "ll3_inc_jump t (Suc na) p", auto)
             apply(drule_tac x = "Suc na" in spec) apply(drule_tac x = p in spec)
    apply(drule_tac x = False in spec) apply(drule_tac x = a in spec) apply(auto)
             apply(auto simp add:ll_valid_q_ll_validl_q.intros)

            apply(case_tac "ll3_inc_jump t (Suc na) p", auto)
             apply(drule_tac x = "Suc na" in spec) apply(drule_tac x = p in spec)
    apply(drule_tac x = True in spec) apply(drule_tac x = a in spec) apply(auto)
           apply(auto simp add:ll_valid_q_ll_validl_q.intros)

            apply(case_tac "ll3_inc_jump t (Suc na) p", auto)
             apply(drule_tac x = "Suc na" in spec) apply(drule_tac x = p in spec)
          apply(drule_tac x = False in spec) apply(drule_tac x = a in spec) apply(auto)
             apply(auto simp add:ll_valid_q_ll_validl_q.intros)

      (* LJmp, LJmpI cases *)
         apply(case_tac p, auto)
          apply(case_tac "ll3_inc_jump t (Suc na) []", auto)
             apply(drule_tac x = "Suc na" in spec) apply(drule_tac x = "[]" in spec)
          apply(drule_tac x = False in spec) apply(drule_tac x = a in spec) apply(auto)
(* need a lemma about nil childpath *)
          apply(drule_tac ll3_inc_jump_nilcp) apply(auto)
         apply(case_tac list, auto)
          apply(case_tac "na = a", auto) 
    apply(drule_tac b = 1 in ll3_bump_qvalid)
           apply(auto simp add:ll_valid_q_ll_validl_q.intros)
           apply(rule_tac ll_valid_q_ll_validl_q.intros) apply(auto)
    apply(drule_tac ll_valid_q.cases)
                apply(auto simp add:ll_valid_q_ll_validl_q.intros)
          apply(case_tac " ll3_inc_jump t (Suc na) [a]", auto)
          apply(drule_tac x = "Suc na" in spec) apply(drule_tac x = "[a]" in spec) apply(auto)
                    apply(auto simp add:ll_valid_q_ll_validl_q.intros)

         apply(case_tac "ll3_inc_jump t (Suc na) (a # aa # lista)", auto)
         apply(drule_tac x = "Suc na" in spec) apply(drule_tac x = "a#aa#lista" in spec) apply(auto)
         apply(drule_tac ll_valid_q.cases) apply(auto)
         apply(auto simp add:ll_valid_q_ll_validl_q.intros)

        apply(case_tac p, auto)
          apply(case_tac "ll3_inc_jump t (Suc na) []", auto)
             apply(drule_tac x = "Suc na" in spec) apply(drule_tac x = "[]" in spec)
          apply(drule_tac x = False in spec) apply(drule_tac x = a in spec) apply(auto)
         apply(drule_tac ll3_inc_jump_nilcp) apply(auto)
         apply(auto simp add:ll_valid_q_ll_validl_q.intros)
      
         apply(case_tac list, auto)
          apply(case_tac "na = a", auto) 
         apply(drule_tac b = 1 in ll3_bump_qvalid)
          apply(case_tac " ll3_inc_jump t (Suc na) [a]", auto)
         apply(auto simp add:ll_valid_q_ll_validl_q.intros)
         apply(case_tac "ll3_inc_jump t (Suc na) (a # aa # lista)", auto)
         apply(drule_tac x = "Suc na" in spec) apply(drule_tac x = "a#aa#lista" in spec) apply(auto)
         apply(drule_tac ll_valid_q.cases) apply(auto)
        apply(auto simp add:ll_valid_q_ll_validl_q.intros)

        
        apply(case_tac p, auto)
          apply(case_tac "ll3_inc_jump t (Suc na) []", auto)
             apply(drule_tac x = "Suc na" in spec) apply(drule_tac x = "[]" in spec)
          apply(drule_tac x = True in spec) apply(drule_tac x = a in spec) apply(auto)
         apply(drule_tac ll3_inc_jump_nilcp) apply(auto)
      
         apply(case_tac list, auto)
          apply(case_tac "na = a", auto) 
         apply(drule_tac b = 1 in ll3_bump_qvalid)
         apply(drule_tac ll_valid_q.cases) apply(auto)
         apply(auto simp add:ll_valid_q_ll_validl_q.intros)
        apply(case_tac " ll3_inc_jump t (Suc na) [a]", auto)
    apply(drule_tac x = "Suc na" in spec) apply(drule_tac x = "[a]" in spec) apply(auto)
         apply(auto simp add:ll_valid_q_ll_validl_q.intros)
         apply(case_tac "ll3_inc_jump t (Suc na) (a # aa # lista)", auto)
         apply(drule_tac x = "Suc na" in spec) apply(drule_tac x = "a#aa#lista" in spec) apply(auto)
         apply(drule_tac ll_valid_q.cases) apply(auto)
        apply(auto simp add:ll_valid_q_ll_validl_q.intros)

    apply(case_tac p, auto)
          apply(case_tac "ll3_inc_jump t (Suc na) []", auto)
             apply(drule_tac x = "Suc na" in spec) apply(drule_tac x = "[]" in spec)
          apply(drule_tac x = False in spec) apply(drule_tac x = a in spec) apply(auto)
         apply(drule_tac ll3_inc_jump_nilcp) apply(auto)
               apply(auto simp add:ll_valid_q_ll_validl_q.intros)

         apply(case_tac list, auto)
          apply(case_tac "na = a", auto) 
       apply(drule_tac b = 1 in ll3_bump_qvalid)
          apply(case_tac " ll3_inc_jump t (Suc na) [a]", auto)

         apply(drule_tac ll_valid_q.cases) apply(auto)
         apply(auto simp add:ll_valid_q_ll_validl_q.intros)
         apply(case_tac "ll3_inc_jump t (Suc na) (a # aa # lista)", auto)
         apply(drule_tac x = "Suc na" in spec) apply(drule_tac x = "a#aa#lista" in spec) apply(auto)
         apply(drule_tac ll_valid_q.cases) apply(auto)
        apply(auto simp add:ll_valid_q_ll_validl_q.intros)

    (* LSeq case *)
    apply(case_tac p, auto)
      apply(case_tac "ll3_inc_jump t (Suc na) []", auto) 
    apply(rotate_tac 3)
             apply(drule_tac x = "Suc na" in spec) apply(drule_tac x = "[]" in spec)
          apply(drule_tac x = False in spec) apply(drule_tac x = a in spec) apply(auto)
      apply(drule_tac ll3_inc_jump_nilcp) apply(auto)

     apply(case_tac "na = a", auto)
      apply(case_tac " ll3_inc_jump x52 0 list", auto)
      apply(case_tac ba, auto)
       apply(drule_tac x = 0 in spec) apply(drule_tac x = list in spec) apply(auto)
    apply(drule_tac b = 1 in ll3_bump_qvalid) apply(auto)
       apply(auto simp add:ll_valid_q_ll_validl_q.intros)

      apply(case_tac " ll3_inc_jump t a (a # list) ") apply(auto)
      apply(drule_tac x = 0 in spec) apply(drule_tac x = list in spec) apply(auto)
      apply(drule_tac x = a in spec) apply(drule_tac x = "a#list" in spec) 
    apply(auto)
       apply(auto simp add:ll_valid_q_ll_validl_q.intros)

     apply(case_tac " ll3_inc_jump t (Suc na) (a # list) ") apply(auto)
     apply(rotate_tac 3)
    
     apply(drule_tac x = "Suc na" in spec) apply(drule_tac x = "a#list" in spec) apply(auto)
       apply(auto simp add:ll_valid_q_ll_validl_q.intros)


        apply(case_tac p, auto)
      apply(case_tac "ll3_inc_jump t (Suc na) []", auto) 
    apply(rotate_tac 3)
             apply(drule_tac x = "Suc na" in spec) apply(drule_tac x = "[]" in spec)
     apply(drule_tac x = False in spec) apply(auto)
      apply(drule_tac ll3_inc_jump_nilcp) apply(auto)
       apply(auto simp add:ll_valid_q_ll_validl_q.intros)

    apply(case_tac "na = a", auto)
     apply(case_tac "ll3_inc_jump x52 0 list", auto)
    apply(case_tac ba, auto)
     apply(case_tac "ll3_inc_jump t a (a # list)", auto)
      apply(drule_tac x = 0 in spec) apply(drule_tac x = list in spec) apply(auto)
      apply(drule_tac x = a in spec) apply(drule_tac x = "a#list" in spec) 
    apply(auto)
     apply(auto simp add:ll_valid_q_ll_validl_q.intros)

    apply(case_tac "ll3_inc_jump t (Suc na) (a # list)") apply(auto)
    apply(rotate_tac 3)
      apply(drule_tac x = "Suc na" in spec) apply(drule_tac x = "a#list" in spec) 
    apply(auto)
    apply(auto simp add:ll_valid_q_ll_validl_q.intros)
    done
qed

lemma ll3_inc_jump_qvalid [rule_format] :
"   (((m,m'), (l :: ll3 list)) \<in> ll_validl_q \<longrightarrow>
      (! n p b l' . ll3_inc_jump l n p = (l', b) \<longrightarrow>
         (if b then ((m,m'+1), l') \<in> ll_validl_q
               else ((m,m'), l') \<in> ll_validl_q)))"
  (* need to give bogus arguments *)
  apply(insert ll3_inc_jump_qvalid'[of "(0,0)" "(LLab True 0)" m m' l])
  apply(auto)
  done

lemma ll3_inc_jump_wrap_qvalid [rule_format]:
"   (((t :: ll3)) \<in> ll_valid_q \<longrightarrow>
      (! t' p b . ll3_inc_jump_wrap t p = t' \<longrightarrow>
             (((t' :: ll3) \<in> ll_valid_q))))"
  apply(auto) apply(case_tac t, auto)
  apply(case_tac bba, auto)
  apply(case_tac "ll3_inc_jump x52 0 p") apply(auto)
  apply(case_tac bc, auto)
  apply(drule_tac ll_valid_q.cases) apply(auto)
  apply(frule_tac ll3_inc_jump_qvalid) apply(auto)
  apply(auto simp add:ll_valid_q_ll_validl_q.intros)
  done

(* pull process jumps loop to outside? *)
lemma process_jumps_loop_qvalid' [rule_format]:
"(! t t' . process_jumps_loop n t = Some t' \<longrightarrow>
  (t :: ll3) \<in> ll_valid_q \<longrightarrow>
  (t' :: ll3) \<in> ll_valid_q)"
proof(induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case 
    apply(auto)
  apply(case_tac "ll3_resolve_jump_wrap ((a,b),ba)")
      apply(auto)
    apply(case_tac "ll3_inc_jump_wrap ((a,b),ba) (rev x3)") apply(auto)
    apply(drule_tac x = ab in spec) apply(drule_tac x = bd in spec)
    apply(drule_tac x = bda in spec)
    apply(drule_tac x = aa in spec) apply(drule_tac x = bb in spec)
    apply(auto)
    apply(subgoal_tac "((ab, bd), bda) \<in> ll_valid_q")
     apply(rule_tac[2] ll3_inc_jump_wrap_qvalid) apply(auto)
    done
qed

(*
do we need to include all non-jump constructors here?
Obviously including the jump constructors would be wrong 
also - do we want a separate predicate describing correctness after
we write the addresses?
*)
(*
inductive_set ll_valid4 :: "ll4 set" where
"\<And> x e ls . ((x, LSeq e ls) :: ll4) \<in> ll_valid3' \<Longrightarrow> 
   (! e' y d s k . ((x, LSeq e ls), (y, LJmp e' d s), k) \<in> ll3'_descend \<longrightarrow>
     length k > d) \<Longrightarrow>
   (! e' y d s k . ((x, LSeq e ls), (y, LJmpI e' d s), k) \<in> ll3'_descend \<longrightarrow>
     length k > d) \<Longrightarrow>
   (x, LSeq e ls) \<in> ll_valid4"
| "\<And> x e i . ((x, L e i) :: ll4) \<in> ll_valid3' \<Longrightarrow>
     (x, L e i) \<in> ll_valid4"
| "\<And> x e d . ((x, LLab e d) :: ll4) \<in> ll_valid3' \<Longrightarrow>
    (x, LLab e d) \<in> ll_valid4" 
*)

(* this set captures the fact that no jumps should point upward to nil-labeled
Seq nodes. It will recurse to children by virtue of the fact that it requires
everything in the set of ls to also be valid4_inner, meaning if they themselves
are nil-labeled, no jumps point to them *)
inductive_set ll_valid4_inner :: "ll4 set" where
"\<And> ls . 
  (! x . x \<in> set ls \<longrightarrow> (x :: ll4) \<in> ll_valid4_inner) \<Longrightarrow>
  (! e' q1 q2 d s k . (((q1, LSeq [] ls)::ll4), (q2, LJmp e' d s), (k::nat list)) \<in> ll3'_descend \<longrightarrow>
     length k \<noteq> d + 1) \<Longrightarrow>
  (! e' q1 q2 d s k . (((q1, LSeq [] ls)::ll4), (q2, LJmpI e' d s), (k::nat list)) \<in> ll3'_descend \<longrightarrow>
     length k \<noteq> d + 1) \<Longrightarrow>
  ((q1, LSeq [] ls) :: ll4) \<in> ll_valid4_inner"
| "\<And> ls h t q .
     (! x . x \<in> set ls \<longrightarrow> (x :: ll4) \<in> ll_valid4_inner) \<Longrightarrow>
     ((q, LSeq (h#t) ls) :: ll4) \<in> ll_valid4_inner"
| "\<And> x e i . ((x, L e i) :: ll4) \<in> ll_valid4_inner"
| "\<And> x e d . ((x, LLab e d) :: ll4) \<in> ll_valid4_inner"
| "\<And> x e d s . ((x, LJmp e d s) :: ll4) \<in> ll_valid4_inner"
| "\<And> x e d s . ((x, LJmpI e d s) :: ll4) \<in> ll_valid4_inner"



inductive_set ll_valid4 :: "ll4 set" where
"\<And> x e ls . ((x, LSeq e ls) :: ll4) \<in> ll_valid3' \<Longrightarrow> 
   (! e' y d s k . ((x, LSeq e ls), (y, LJmp e' d s), k) \<in> ll3'_descend \<longrightarrow>
     length k > d) \<Longrightarrow>
   (! e' y d s k . ((x, LSeq e ls), (y, LJmpI e' d s), k) \<in> ll3'_descend \<longrightarrow>
     length k > d) \<Longrightarrow>
   (x, LSeq e ls) \<in> ll_valid4_inner \<Longrightarrow>
   (x, LSeq e ls) \<in> ll_valid4"
| "\<And> x e i . ((x, L e i) :: ll4) \<in> ll_valid3' \<Longrightarrow>
     (x, L e i) \<in> ll_valid4"
| "\<And> x e d . ((x, LLab e d) :: ll4) \<in> ll_valid3' \<Longrightarrow>
    (x, LLab e d) \<in> ll_valid4" 

(* need valid4_post, which includes the fact that jumps have been correctly assigned
look in your notebook for different formulations of this
ultimately we will need to tie write jumps spec to it*)

(* idea: if write_jumps succeeds, and the incoming thing was valid4 (i.e.,
already checked for both kinds of bad jumps)
then for every (seq, jump, k) \<in> descend
there exists an LLab appropriately descended from that seq node
such that the address present in the annotation equal the address of that llab
*)

(* getter that works based on location (location must be exact) *)
(* also note that we dive _into_ sequences rather than flagging entire sequence *)
fun getByLoc :: "('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll \<Rightarrow> nat \<Rightarrow> ('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll option"
and getByLocList :: "('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll list \<Rightarrow> nat \<Rightarrow> ('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll option" where
"getByLoc (_, LSeq e l) n = getByLocList l n"
| "getByLoc ((x,x'), T) n =
  (if n = x then Some ((x,x'), T)
   else None)"
| "getByLocList [] n = None"
| "getByLocList (h#t) n =
   (case getByLoc h n of
    Some r \<Rightarrow> Some r
    | None \<Rightarrow> getByLocList t n)
"

(* I am very tempted to have ll_valid4 include child as well as parent node.
However, I think this will cause problems around describing a lone jump as "valid" *)
(* this function should not flag a lone jump as valid (d must be strictly less than n,
for n=0 this isn't psosible) 
*)
fun ll4_jump_check :: "ll4 \<Rightarrow> nat \<Rightarrow> bool" where
"ll4_jump_check (x, LSeq e ls) n = 
  Lem.list_forall (\<lambda> l . ll4_jump_check l (n+1)) ls"
| "ll4_jump_check (x, LJmp e d s) n = (n > d)"
| "ll4_jump_check (x, LJmpI e d s) n = (n > d)"
| "ll4_jump_check _ _ = True"

(* not sure if these next 2 functions are helpful *)
(*
(* helper function for ll4 jump checker *)
fun bl_get :: "bool list \<Rightarrow> nat \<Rightarrow> bool" where
"bl_get [] _ = False"
| "bl_get (h#t) n =
   (if n = 0 then h else bl_get t (n-1))"

(* Makes sure jumps don't reach out of the syntax tree
and also don't point to labelless Seq nodes *)
fun ll4_jump_check_full :: "ll4 \<Rightarrow> bool list \<Rightarrow> bool" where
"ll4_jump_check_full (x, LSeq e ls) bs = 
  Lem.list_forall (\<lambda> l . ll4_jump_check_full l ((e \<noteq> [])#bs)) ls"
| "ll4_jump_check_full (x, LJmp e d s) bs = bl_get bs d"
| "ll4_jump_check_full (x, LJmpI e d s) bs = bl_get bs d"
| "ll4_jump_check_full _ _ = True"
*)
(* this is getting a little annoying... *)
(*
lemma ll4_jump_check_full_spec :
"(! n . ll4_jump_check t n = True \<longrightarrow>
   (! qd e d s k . (t, (qd,LJmp e d s), k) \<in> ll3'_descend \<longrightarrow>
    (? t' k' . (t = t' \<or> (? q es d ls k' . (t, (q, LSeq es ls), k'))) \<and>
       length k' = d \<and> es \<noteq> [])
   d - n < length k) \<and>
(! q' e d s k . (t, (q',LJmpI e d s), k) \<in> ll3'_descend \<longrightarrow>
   d - n < length k)
) \<and>
(! q e n . ll4_jump_check (q, LSeq e ls) n = True \<longrightarrow>
      (! q' e' d s k . ((q, LSeq e ls), (q',LJmp e' d s), k) \<in> ll3'_descend \<longrightarrow>
   d - n < length k) \<and>
(! q' e' d s k . ((q, LSeq e ls), (q',LJmpI e' d s), k) \<in> ll3'_descend \<longrightarrow>
   d - n < length k)
)
"
*)

(*
lemma ll4_jump_check_spec :
"(q, LSeq e ls) \<in> ll_valid3' \<Longrightarrow>
  (ll4_jump_check (q,LSeq e ls) 0 \<longrightarrow>
  (q, LSeq e ls) \<in> ll_valid4)"
proof(induction rule:ll_valid3'.induct)
case (1 i e x)
  then show ?case 
    apply (auto simp add:ll_valid4.intros)
    apply
   
next
  case (2 x d)
  then show ?case sorry
next
  case (3 e x d s)
  then show ?case sorry
next
  case (4 e x d s)
  then show ?case sorry
next
  case (5 x l e)
  then show ?case sorry
next
  case (6 x l e k y)
  then show ?case sorry
qed
*)
(*
need a sub-lemma, saying something like
"if we call ll4_jump_check on any tree,
and it returns true
then there must be no descended jump with higher depth"
*)

(* is this off by one?
i think this one is correct.
we want to make sure that d - n doesn't exceed length k,
since the total descent depth is n + length k
and d can be at most that minus one *)
lemma ll4_jump_check_spec' :
"(! n . ll4_jump_check t n = True \<longrightarrow>
   (! q' e d s k . (t, (q',LJmp e d s), k) \<in> ll3'_descend \<longrightarrow>
   d < length k + n) \<and>
(! q' e d s k . (t, (q',LJmpI e d s), k) \<in> ll3'_descend \<longrightarrow>
   d < length k + n)
) \<and>
(! q e n . ll4_jump_check (q, LSeq e ls) n = True \<longrightarrow>
      (! q' e' d s k . ((q, LSeq e ls), (q',LJmp e' d s), k) \<in> ll3'_descend \<longrightarrow>
   d < length k + n)\<and>
(! q' e' d s k . ((q, LSeq e ls), (q',LJmpI e' d s), k) \<in> ll3'_descend \<longrightarrow>
   d < length k + n)
)
"
proof(induction rule:my_ll_induct)
case (1 q e i)
  then show ?case 
    apply(auto) apply(drule_tac ll3_hasdesc, auto)
apply(drule_tac ll3_hasdesc, auto)
    done
next
  case (2 q e idx)
  then show ?case 
apply(auto) apply(drule_tac ll3_hasdesc, auto)
apply(drule_tac ll3_hasdesc, auto)
done next
  case (3 q e idx n)
  then show ?case
    apply(auto)
     apply(drule_tac ll3_hasdesc,auto)
apply(drule_tac ll3_hasdesc,auto)
    done
next
  case (4 q e idx n)
  then show ?case
    apply(auto)
     apply(drule_tac ll3_hasdesc,auto)
    apply(drule_tac ll3_hasdesc,auto)
    done
next
  case (5 q e l)
  then show ?case 
    apply(auto)
     apply(drule_tac x = "fst q " in spec)
     apply(drule_tac x = "snd q " in spec)
     apply(drule_tac x = e in spec) apply(auto)

     apply(drule_tac x = "fst q " in spec)
     apply(drule_tac x = "snd q " in spec)
    apply(drule_tac x = e in spec) apply(auto)
    done
next
  case 6
  then show ?case
    apply(auto)
     apply(drule_tac ll_descend_eq_r2l) apply(case_tac k, auto)
    apply(drule_tac ll_descend_eq_r2l) apply(case_tac k, auto)
    done
next
  case (7 h l)
  then show ?case
    apply(auto)
       apply(case_tac k, auto) apply(drule_tac ll3_descend_nonnil, auto)
       apply(drule_tac ll_descend_eq_r2l) apply(auto) apply(case_tac ab, auto)
    apply(case_tac list, auto)
      apply(drule_tac ll_descend_eq_l2r)
      apply(drule_tac x = "Suc n" in spec) apply(auto)
    apply(thin_tac "  \<forall>a b e d s k.
          (h, ((a, b), llt.LJmpI e d s), k) \<in> ll3'_descend \<longrightarrow>
        d  < Suc (length k + n)")  
    apply(rotate_tac -1)
      apply(drule_tac x = aa in spec)
      apply(rotate_tac -1) 
      apply(drule_tac x = ba in spec) 
    apply(rotate_tac -1)
      apply(drule_tac x  = e' in spec) apply(rotate_tac -1)
      apply(drule_tac x = d in spec) apply(rotate_tac -1)
      apply(drule_tac x = s in spec) apply(rotate_tac -1)
      apply(drule_tac x = "a#lista" in spec) apply(auto)

     apply(rotate_tac 1) (* bogus *) apply(drule_tac x = 0 in spec)
     apply(rotate_tac -1) apply(drule_tac x = 0 in spec)  apply(rotate_tac -1)
     apply(drule_tac x = "[]" in spec) apply(rotate_tac -1) apply(drule_tac x = n in spec)
    apply(auto)
     apply(drule_tac l = l and q = "(0,0)" and e = "[]" in ll_descend_eq_l2r_list) 
    apply(rotate_tac -3)
     apply(drule_tac x = aa in spec)
     apply(rotate_tac -1)
     apply(drule_tac x = ba in spec) apply(rotate_tac -1)
     apply(drule_tac x = e' in spec) apply(rotate_tac -1) apply(drule_tac x = d in spec)
     apply(rotate_tac -1) apply(drule_tac x = s in spec)
     apply(rotate_tac -1) apply(drule_tac x = "nat#list" in spec)
    apply(auto)

    apply(case_tac k, auto)
apply(drule_tac ll3_descend_nonnil, auto)
    apply(drule_tac ll_descend_eq_r2l, auto) apply(case_tac ab, auto)
     apply(drule_tac x = "Suc n" in spec) apply(rotate_tac -1)
     apply(auto) apply(case_tac list, auto)
     apply(drule_tac ll_descend_eq_l2r) apply(rotate_tac -2)
     apply(drule_tac x = aa in spec) apply(rotate_tac -1)
     apply(drule_tac x = ba in spec) apply(rotate_tac -1)
     apply(drule_tac x = e' in spec, rotate_tac -1)
     apply(drule_tac x = d in spec, rotate_tac -1)
apply(drule_tac x = s in spec, rotate_tac -1)
     apply(drule_tac x = "a#lista" in spec, rotate_tac -1) apply(auto)


     apply(rotate_tac 1) (* bogus *) apply(drule_tac x = 0 in spec)
     apply(rotate_tac -1) apply(drule_tac x = 0 in spec)  apply(rotate_tac -1)
     apply(drule_tac x = "[]" in spec) apply(rotate_tac -1) apply(drule_tac x = n in spec)
    apply(auto)
     apply(drule_tac l = l and q = "(0,0)" and e = "[]"  in ll_descend_eq_l2r_list) 
    apply(rotate_tac -2)
     apply(drule_tac x = aa in spec)
     apply(rotate_tac -1)
     apply(drule_tac x = ba in spec) apply(rotate_tac -1)
     apply(drule_tac x = e' in spec) apply(rotate_tac -1) apply(drule_tac x = d in spec)
     apply(rotate_tac -1) apply(drule_tac x = s in spec)
     apply(rotate_tac -1) apply(drule_tac x = "nat#list" in spec)
    apply(auto)
    done
qed

(* additional case ruling out lone jumps *)
lemma ll4_jump_check_spec_base [rule_format] :
"(! n . ll4_jump_check t 0 = True \<longrightarrow>
  (! q e d s . t \<noteq> (q, LJmp e d s)) \<and>
  (! q e d s . t \<noteq> (q, LJmpI e d s)))"
  apply(auto)
  done


(* now, we need another checker, that, at each non-labelled sequence node,
ensures it has no jumps
this may end up being a rather inefficient way to do this,
but it seems easier to verify
*)
fun ll4_ensure_no_jumps :: "ll4 \<Rightarrow> nat \<Rightarrow> bool" where
"ll4_ensure_no_jumps (x, LSeq _ ls) d =
  Lem.list_forall (\<lambda> l . ll4_ensure_no_jumps l (d+1)) ls"
| "ll4_ensure_no_jumps (x, LJmp e d' ls) d = (d' + 1 \<noteq> d)"
| "ll4_ensure_no_jumps (x, LJmpI e d' ls) d = (d' + 1 \<noteq> d)"
| "ll4_ensure_no_jumps _ _ = True"

(* any sequence node for which ensure_no_labels returns true
has no descended labels at same depth as label *)

(* the issue here is that we need to treat a program with a single
jump enclosed by no sequences as invalid. current we don't i think *)

(* TODO: I am very worried about an off by one sort of error here *)
(* any jump \<rightarrow> diff depth *)
(* d - n - 1 ? *)
lemma ll4_ensure_no_jumps_spec' :
"(! n . ll4_ensure_no_jumps t n = True \<longrightarrow>
   (! q' e d s k . (t, (q',LJmp e d s), k) \<in> ll3'_descend \<longrightarrow>
   d + 1 \<noteq> length k + n) \<and>
(! q' e d s k . (t, (q',LJmpI e d s), k) \<in> ll3'_descend \<longrightarrow>
   d + 1  \<noteq> length k + n)
) \<and>
(! q e n . ll4_ensure_no_jumps (q, LSeq e ls) n = True \<longrightarrow>
      (! q' e' d s k . ((q, LSeq e ls), (q',LJmp e' d s), k) \<in> ll3'_descend \<longrightarrow>
   d + 1 \<noteq> length k + n) \<and>
(! q' e' d s k . ((q, LSeq e ls), (q',LJmpI e' d s), k) \<in> ll3'_descend \<longrightarrow>
   d + 1 \<noteq> length k + n)
)
"
proof(induction rule:my_ll_induct)
  case (1 q e i)
  then show ?case 
    apply(auto) apply(drule_tac ll3_hasdesc, auto)
apply(drule_tac ll3_hasdesc, auto)
    done
next
  case (2 q e idx)
  then show ?case 
apply(auto) apply(drule_tac ll3_hasdesc, auto)
apply(drule_tac ll3_hasdesc, auto)
done next
  case (3 q e idx n)
  then show ?case
    apply(auto)
     apply(drule_tac ll3_hasdesc,auto)
apply(drule_tac ll3_hasdesc,auto)
    done
next
  case (4 q e idx n)
  then show ?case
    apply(auto)
     apply(drule_tac ll3_hasdesc,auto)
    apply(drule_tac ll3_hasdesc,auto)
    done
next
  case (5 q e l)
  then show ?case 
    apply(auto)
     apply(drule_tac x = "fst q " in spec)
     apply(drule_tac x = "snd q " in spec)
     apply(drule_tac x = e in spec) apply(drule_tac x = n in spec) apply(auto)
  
     apply(drule_tac x = "fst q " in spec)
     apply(drule_tac x = "snd q " in spec)
    apply(drule_tac x = e in spec) apply(auto)
    done
next
  case 6
  then show ?case
    apply(auto)
     apply(drule_tac ll_descend_eq_r2l) apply(case_tac k, auto)
    apply(drule_tac ll_descend_eq_r2l) apply(case_tac k, auto)
    done
next
  case (7 h l)
  then show ?case 
    apply(auto)
     apply(case_tac k, auto)
      apply(drule_tac ll3_descend_nonnil, auto)
     apply(drule_tac ll_descend_eq_r2l) apply(auto)
     apply(case_tac ab, auto)

      apply(case_tac list) apply(auto)
      apply(drule_tac ll_descend_eq_l2r) 
      apply(drule_tac x = "Suc n" in spec) apply(auto)
      apply(rotate_tac -2) apply(drule_tac x = aa in spec) apply(rotate_tac -1)
      apply(drule_tac x = ba in spec) apply(rotate_tac -1) apply(drule_tac x = e' in spec)
      apply(rotate_tac -1) apply(drule_tac x = "Suc (length lista + n)" in spec)
      apply(rotate_tac -1) apply(drule_tac x = s in spec) apply(auto)

    (* bogus params *)
     apply(drule_tac q = "(0,0)" and e = "[]" in ll_descend_eq_l2r_list)
     apply(rotate_tac 1)
     apply(drule_tac x = 0 in  spec) apply(rotate_tac -1)
     apply(drule_tac x = 0 in spec) apply(rotate_tac -1)
     apply(drule_tac x = "[]" in spec) apply(rotate_tac -1)
     apply(drule_tac x = n in spec) apply(auto) apply(rotate_tac -2)
     apply(drule_tac x = aa in spec) apply(rotate_tac -1)
     apply(drule_tac x = ba in spec) apply(rotate_tac -1) apply(drule_tac x = e' in spec)
    apply(rotate_tac -1)  apply(drule_tac x = "(length list + n)" in spec)
      apply(rotate_tac -1) apply(drule_tac x = s in spec) apply(auto)


     apply(case_tac k, auto)
      apply(drule_tac ll3_descend_nonnil, auto)
     apply(drule_tac ll_descend_eq_r2l) apply(auto)
     apply(case_tac ab, auto)

      apply(case_tac list) apply(auto)
      apply(drule_tac ll_descend_eq_l2r) 
      apply(drule_tac x = "Suc n" in spec) apply(auto)
      apply(rotate_tac -1) apply(drule_tac x = aa in spec) apply(rotate_tac -1)
      apply(drule_tac x = ba in spec) apply(rotate_tac -1) apply(drule_tac x = e' in spec)
      apply(rotate_tac -1) apply(drule_tac x = "Suc (length lista + n)" in spec)
      apply(rotate_tac -1) apply(drule_tac x = s in spec) apply(auto)

    (* bogus params *)
     apply(drule_tac q = "(0,0)" and e = "[]" in ll_descend_eq_l2r_list)
     apply(rotate_tac 1)
     apply(drule_tac x = 0 in  spec) apply(rotate_tac -1)
     apply(drule_tac x = 0 in spec) apply(rotate_tac -1)
     apply(drule_tac x = "[]" in spec) apply(rotate_tac -1)
    apply(drule_tac x = n in spec) apply(auto)
    apply(rotate_tac -1)
     apply(drule_tac x = aa in spec) apply(rotate_tac -1)
     apply(drule_tac x = ba in spec) apply(rotate_tac -1) apply(drule_tac x = e' in spec)
    apply(rotate_tac -1)  apply(drule_tac x = "(length list + n)" in spec)
      apply(rotate_tac -1) apply(drule_tac x = s in spec) apply(auto)
    done

qed

lemma ll4_ensure_no_jumps_spec [rule_format] :
"(! n . ll4_ensure_no_jumps t n \<longrightarrow>
   (! q' e d s k . (t, (q',LJmp e d s), k) \<in> ll3'_descend \<longrightarrow>
   d + 1 \<noteq> length k + n) \<and>
(! q' e d s k . (t, (q',LJmpI e d s), k) \<in> ll3'_descend \<longrightarrow>
   d + 1  \<noteq> length k + n)
)"
  apply(insert ll4_ensure_no_jumps_spec')
  apply(auto)
  done
 

fun ll4_emptylab_check :: "ll4 \<Rightarrow> bool" where
"ll4_emptylab_check (x, LSeq (h#t) ls) = 
  Lem.list_forall ll4_emptylab_check ls"
| "ll4_emptylab_check (x, LSeq [] ls) =
   (if ll4_ensure_no_jumps (x, LSeq [] ls) 0 then
      Lem.list_forall ll4_emptylab_check ls
    else False)"
| "ll4_emptylab_check _ = True"

(* if an ll4 passes emptylab_check, then
there exist no jump descendents for seq nodes with nil labels
(at that depth) *)

lemma ll4_emptylab_check_valid4_inner :
"(ll4_emptylab_check t \<longrightarrow> t \<in> ll_valid4_inner) \<and>
(! e x . ll4_emptylab_check (x, LSeq e ls)  \<longrightarrow> ((x, LSeq e ls) \<in> ll_valid4_inner))"
proof(induction rule:my_ll_induct)
case (1 q e i)
  then show ?case 
    apply(auto simp add:ll_valid4_inner.intros)
    done
next
  case (2 q e idx)
  then show ?case 
    apply(auto simp add:ll_valid4_inner.intros)
    done
next
  case (3 q e idx n)
  then show ?case
    apply(auto simp add:ll_valid4_inner.intros)
    done
next
  case (4 q e idx n)
  then show ?case
    apply(auto simp add:ll_valid4_inner.intros)
    done
next
  case (5 q e l)
  then show ?case
    apply(auto)
    apply(drule_tac x = e in spec)
    apply(drule_tac x = "fst q" in spec) apply(drule_tac x = "snd q" in spec)
    apply(auto simp add:ll_valid4_inner.intros)
    done
next
  case 6
  then show ?case 
    apply(auto)
    apply(case_tac e, auto)
     apply(auto simp add:ll_valid4_inner.intros)
    apply(rule_tac ll_valid4_inner.intros) apply(auto)
    apply(drule_tac ll_descend_eq_r2l) apply(case_tac k, auto)     
        apply(drule_tac ll_descend_eq_r2l) apply(case_tac k, auto)
done
next
  case (7 h l)
  then show ?case
    apply(auto)
     apply(case_tac e, auto)
    apply(case_tac "ll4_ensure_no_jumps h (Suc 0)", auto)
     apply(case_tac "\<forall>e\<in>set l. ll4_ensure_no_jumps e (Suc 0)", auto)

    apply(case_tac e, auto)
    apply(case_tac "ll4_ensure_no_jumps h (Suc 0)", auto)
     apply(case_tac "\<forall>e\<in>set l. ll4_ensure_no_jumps e (Suc 0)", auto)
     apply(rule_tac ll_valid4_inner.intros) apply(auto)

      apply(drule_tac x = "[]" in spec) apply(simp)
      (* bogus args *)
      apply(rotate_tac -1) apply(drule_tac x = 0 in spec)
      apply(rotate_tac -1) apply(drule_tac x= 0 in spec)
    apply(rotate_tac -1)
      apply(drule_tac ll_valid4_inner.cases) apply(auto)

     apply(case_tac k, auto) apply(case_tac ab, auto)
      apply(drule_tac  ll_descend_eq_r2l, auto)
      apply(case_tac list, auto) apply(drule_tac ll_descend_eq_l2r)
      apply(frule_tac ll4_ensure_no_jumps_spec) apply(auto)


       apply(rotate_tac -2) apply(drule_tac x = aa in spec)
      apply(rotate_tac -1) apply(drule_tac x = ba in spec)
       apply(rotate_tac -1) apply(drule_tac x = e' in spec)

       apply(rotate_tac -1) apply(drule_tac x = "Suc (length lista)" in spec)
      apply(rotate_tac -1) apply(drule_tac x = s in spec)
    apply(rotate_tac -1) apply(drule_tac x = "a#lista" in spec) apply(auto)

    (* better idea: use "split" lemma here? *)
     apply(drule_tac ll3_descend_splitpath_cons) apply(case_tac list, auto)
      apply(drule_tac ll3_descend_singleton) apply(auto)
      apply(drule_tac List.nth_mem) apply(auto)

      apply(drule_tac ll3_descend_singleton) apply(auto)
     apply(drule_tac List.nth_mem) apply(auto)
     apply(subgoal_tac "ll4_ensure_no_jumps ((ac, bb), bc) (Suc 0)") apply(auto)
     apply(drule_tac Set.bspec) apply(auto)

    apply(rotate_tac -1)
     apply(drule_tac ll4_ensure_no_jumps_spec) apply(auto)
     apply(rotate_tac -2) apply(drule_tac x = aa in spec) apply(rotate_tac -1)
     apply(drule_tac x = ba in spec) apply(rotate_tac -1)
      apply(drule_tac x = e' in spec) apply(rotate_tac -1)
      apply(drule_tac x = "Suc (length lista)" in spec) apply(rotate_tac -1)
    apply(drule_tac x = "s" in spec) apply(rotate_tac -1)
      apply(drule_tac x = "ab#lista" in spec) apply(rotate_tac -1) apply(auto)

     apply(case_tac k, auto) apply(drule_tac ll3_descend_splitpath_cons)
     apply(case_tac list, auto)
      apply(drule_tac ll3_descend_singleton, auto) apply(case_tac ab, auto)
      apply(drule_tac List.nth_mem, auto)
     apply(drule_tac ll3_descend_singleton, auto) apply(case_tac ab, auto)
      apply(drule_tac ll4_ensure_no_jumps_spec) apply(auto)
      apply(rotate_tac -1) apply(drule_tac x = aa in spec)
      apply(rotate_tac -1) apply(drule_tac x = ba in spec)
      apply(rotate_tac -1) apply(drule_tac x = e' in spec)
    apply(rotate_tac -1)
        apply(drule_tac x = "Suc (length lista)" in spec) apply(rotate_tac -1)
    apply(drule_tac x = "s" in spec) apply(rotate_tac -1)
      apply(drule_tac x = "ac#lista" in spec) apply(rotate_tac -1) apply(auto)

     apply(drule_tac List.nth_mem) apply(auto)
     apply(rotate_tac 3) apply(drule_tac Set.bspec) apply(auto)
     apply(rotate_tac -1) apply(drule_tac ll4_ensure_no_jumps_spec) apply(auto)
    apply(rotate_tac -1)  apply(drule_tac x = aa in spec)
      apply(rotate_tac -1) apply(drule_tac x = ba in spec)
      apply(rotate_tac -1) apply(drule_tac x = e' in spec)
    apply(rotate_tac -1)
        apply(drule_tac x = "Suc (length lista)" in spec) apply(rotate_tac -1)
    apply(drule_tac x = "s" in spec) apply(rotate_tac -1)
     apply(drule_tac x = "ac#lista" in spec) apply(rotate_tac -1) apply(auto)

    (* last part - nonnil label, less to check *)
  (* work below is speculative *)
(* I'm confused why this doesn't go through. need to generalize to all descendents? *) 
       apply(drule_tac x = "0#[]" in spec) apply(auto)

    apply(rule_tac ll_valid4_inner.intros) apply(auto)
    apply(case_tac ba, auto simp add:ll_valid4_inner.intros)
    (* bogus *)
    apply(drule_tac x = 0 in spec) apply(drule_tac x = 0 in spec)
    apply(rotate_tac -1)
    apply(drule_tac ll_valid4_inner.cases) apply(auto)
    done
qed

(* next: if a node is ll4 valid, and we call write_jump_targets on it,
and it succeeds, then
- for each jump that gets written (jump descended from the root Seq node at its depth)
- there must exist a Lab descended from that root seq node at its depth
- such that the address written is the address of the lab
*)

(* TODO: we probably eventually need to prove a relationship between
encode_size and the number of bytes output. the spec of this function ultimately
needs to talk about addresses in the output code being the right size *)
fun validate_addrs :: "ll4 \<Rightarrow> bool" where
"validate_addrs (x, LJmp a _ sz) = (encode_size a = sz)"
| "validate_addrs (x, LJmpI a _ sz) = (encode_size a = sz)"
| "validate_addrs (x, LSeq e ls) = Lem.list_forall validate_addrs ls"
| "validate_addrs _ = True"

(*
inductive_set ll_valid4_post :: "ll4 set" where
*)

(* this - which should be moved to a different file -
defines semantics of arbitrary lls,
as well as being useful for showing that compiler passes only
change annotations, thus do not change semantics *)
fun ll_purge_annot :: "('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll \<Rightarrow> ll1" where
"ll_purge_annot (_, L _ i) = ll1.L i"
| "ll_purge_annot (_, LLab _ idx) = ll1.LLab idx"
| "ll_purge_annot (_, LJmp _ idx _) = ll1.LJmp idx"
| "ll_purge_annot (_, LJmpI _ idx _) = ll1.LJmpI idx"
| "ll_purge_annot (_, LSeq _ ls) =
  ll1.LSeq (map ll_purge_annot ls)"

(* characterization of mypeel *)
lemma mypeel_spec1 [rule_format] :
"(! h l' . mypeel (h#t) = Some l' \<longrightarrow>
  (? h' t' . h = Some h' \<and> mypeel t = Some t' \<and> l' = h'#t'))
"
proof(induction t)
case Nil
  then show ?case 
    apply(auto) apply(case_tac h, auto)
    done
next
  case (Cons a t)
  then show ?case
    apply(auto)
    apply(case_tac h, auto)
    apply(case_tac a, auto)
    apply(case_tac " case mypeel t of None \<Rightarrow> None | Some t' \<Rightarrow> Some (aaa # t')", auto)
    done
qed

(* sub lemma needed to prove write_jumps *)
(* i think ll_get_label is fixed now *)
(* this lemma needs to be strengthened however *)
lemma ll_get_label_spec' [rule_format] :
"(! q e ls . (t :: ('a, 'b, 'c, 'd, 'e) ll3' ) = (q, LSeq e ls) \<longrightarrow>
  (! cp ad . ll_get_label (ls) cp = Some ad \<longrightarrow>
  (? q' e' idx .
  (! q e . ((q, LSeq e ls), (q', LLab e' idx), cp) \<in> ll3'_descend \<and>
    fst q' = ad))))
\<and>(! cp ad . ll_get_label (ls :: ('a, 'b, 'c, 'd, 'e) ll3' list) cp = Some ad \<longrightarrow>
  (? q' e' idx .
  (! q e . ((q, LSeq e ls), (q', LLab e' idx), cp) \<in> ll3'_descend \<and>
    fst q' = ad)))"
proof(induction rule:my_ll_induct)
  case (1 q e i)
  then show ?case
    apply(auto)
    done
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
  then show ?case 
    apply(auto)
    done
next
  case (7 h l)
  then show ?case 
    apply(auto)
    apply(case_tac cp, auto)
    apply(case_tac a, auto) apply(case_tac h, auto)
     apply(case_tac ba, auto) apply(case_tac list, auto)
       apply(rule_tac x = b in exI) apply(rule_tac x = x21 in exI)
       apply(rule_tac x = x22 in exI) apply(auto)
      apply(rule_tac ll_descend_eq_l2r) apply(auto)
     apply(drule_tac x = list in spec, rotate_tac -1)
     apply(drule_tac x = ad in spec, rotate_tac -1) apply(auto) 
     apply(rule_tac x = ba in exI)
     apply(rule_tac x = "e'" in exI)
     apply(rule_tac x = "idx" in exI)
     apply(auto) apply(rule_tac ll_descend_eq_l2r) apply(auto)
     apply(rotate_tac -1)
     apply(drule_tac x = a in spec, rotate_tac -1)
     apply(drule_tac x = b in spec, rotate_tac -1)
     apply(drule_tac x = x51 in spec, rotate_tac -1) 
     apply(drule_tac ll_descend_eq_r2l) apply(auto)

    apply(rotate_tac 1)
    apply(drule_tac x = "nat#list" in spec, rotate_tac -1)
    apply(drule_tac x = "ad" in spec, rotate_tac -1)
    apply(auto)
    apply(rule_tac x = b in exI) apply(rule_tac x = e' in exI)
    apply(rule_tac x = idx in exI) apply(auto)
    apply(rule_tac ll_descend_eq_l2r) apply(auto)
    apply(rotate_tac -1)
(* bogus *)
    apply(drule_tac x = 0 in spec, rotate_tac -1)
    apply(drule_tac x = 0 in spec, rotate_tac -1)
    apply(drule_tac x = "[]" in spec, rotate_tac -1)
    apply(drule_tac ll_descend_eq_r2l) apply(auto)
    done

qed

lemma ll_get_label_spec [rule_format] :
"(! cp ad . ll_get_label (ls :: ('a, 'b, 'c, 'd, 'e) ll3' list) cp = Some ad \<longrightarrow>
  (? q' e' idx .
  (! q e . ((q, LSeq e ls), (q', LLab e' idx), cp) \<in> ll3'_descend \<and>
    fst q' = ad)))
"
  apply(auto)
  apply(insert ll_get_label_spec'[of " ((0,0), llt.LSeq e ls)"])
  apply(auto )
  done

(* TODO i think this spec needs tightening
at the very least we should be relating the output jump address
to the address of the label.
but i think that's not why this doesn't hold inductively *)
(* do we need a separate case covering bare JMPs ? 
this could even be a separate lemma?
problem seems to come from the "k1@k2" part
*)
(*
idea: include premise stating that LSeq root node has an annotation?
but we should be able to still say something in the nil-annotation case
*)
(*
OK.

Without q-validity, we don't know anything about the label's index.
we just know it must exist at a certain depth and its path is the one we gave to get_label.
valid4 will ensure they are meaningful, but this theorem is structured so as not
to need it

Better idea: make the Seq explicit (in first line) instead of giving t'
*)
(*

lemma write_jump_targets_spec_simpler :
"  (! l t' . write_jump_targets l t = Some t' \<longrightarrow>
  (! qj ej idxj sz kj . (t', (qj, LJmp ej idxj sz), kj) \<in> ll3'_descend \<longrightarrow>
  ((\<exists> ql el idxl kl . (t', (ql, LLab el idxl), kl) \<in> ll3'_descend \<and> 
                (*idxl + 1 = length kl \<and> *)idxj + 1 = length kj \<and> fst ql = ej) \<or>
   (? n . mynth l n = Some ej \<and> length kj + n = idxj)
  ))) \<and>
(! q e l t' . write_jump_targets l (q, LSeq e ls) = Some t' \<longrightarrow>
(! qj ej idxj sz kj . (t', (qj, LJmp ej idxj sz), kj) \<in> ll3'_descend \<longrightarrow>
  ((\<exists> ql el idxl kl . (t', (ql, LLab el idxl), kl) \<in> ll3'_descend \<and> 
                (*idxl + 1 = length kl \<and> *) idxj + 1 = length kj \<and> fst ql = ej) \<or>
   (? n . mynth l n = Some ej \<and> length kj + n = idxj)
  )))
"
*)

(* todo: make sure this "simpler" lemma is actually provable
i think it is not what we want as the idxj+1=length kj premise seems not good
*)
(*
lemma write_jump_targets_spec_simpler :
"  (! l qr er ls  . write_jump_targets l t = Some (qr, LSeq er ls) \<longrightarrow>
  (! qj ej idxj sz kj . ((qr, LSeq er ls), (qj, LJmp ej idxj sz), kj) \<in> ll3'_descend \<longrightarrow>
  (idxj + 1 = length kj \<longrightarrow>
  ((\<exists> ql el idxl . ((qr, LSeq er ls), (ql, LLab el idxl), er) \<in> ll3'_descend \<and> fst ql = ej) \<or>
   (? n . mynth l n = Some ej \<and> length kj + n = idxj)
  ))) \<and>
(! q e l qr er ls . write_jump_targets l (q, LSeq e ls') = Some (qr, LSeq er ls) \<longrightarrow>
(! qj ej idxj sz kj . ((qr, LSeq er ls), (qj, LJmp ej idxj sz), kj) \<in> ll3'_descend \<longrightarrow>
  ((\<exists> ql el idxl . ((qr, LSeq er ls), (ql, LLab el idxl), er) \<in> ll3'_descend \<and> 
                (*idxl + 1 = length kl \<and> *) idxj + 1 = length kj \<and> fst ql = ej) \<or>
   (? n . mynth l n = Some ej \<and> length kj + n = idxj)
  ))))
"
proof(induction rule:my_ll_induct)
case (1 q e i)
then show ?case by auto
next
  case (2 q e idx)
  then show ?case by auto
next
  case (3 q e idx n)
  then show ?case 
    apply(auto)
     apply(case_tac q, auto) apply(case_tac "mynth l idx", auto)
     apply(drule_tac ll3_hasdesc, auto)
     apply(case_tac q, auto) apply(case_tac "mynth l idx", auto)
done next
  case (4 q e idx n)
  then show ?case
    apply(auto)
     apply(case_tac q, auto) apply(case_tac "mynth l idx", auto)
     apply(drule_tac ll3_hasdesc, auto)
     apply(case_tac q, auto) apply(case_tac "mynth l idx", auto)
done 
next
  case (5 q e l)
  then show ?case 
 apply(auto)
    apply(case_tac q, auto)
    apply(case_tac e, auto)
     apply(case_tac "mypeel (map (write_jump_targets (None # la)) l)", auto)
    (* bogus *)
     apply(drule_tac x = a in spec, rotate_tac -1)
     apply(drule_tac x = b in spec, rotate_tac -1)
    apply(drule_tac x = "[]" in spec, rotate_tac -1)
     apply(drule_tac x = "la" in spec, rotate_tac -1)
      apply(auto)
      apply(drule_tac x = aa in spec, rotate_tac -1)
     apply(drule_tac x = ba in spec, rotate_tac -1)
      apply(drule_tac x = "ej" in spec, rotate_tac -1)
    apply(drule_tac x = "idxj" in spec, rotate_tac -1)
      apply(drule_tac x = "sz" in spec, rotate_tac -1)
      apply(drule_tac x = "kj" in spec, rotate_tac -1) apply(auto)

     apply(case_tac "ll_get_label l (ac # list)", auto)
    apply(case_tac "mypeel (map (write_jump_targets (Some ad # la)) l)", auto)
      apply(drule_tac x = a in spec, rotate_tac -1)
     apply(drule_tac x = b in spec, rotate_tac -1)
     apply(drule_tac x = "ac#list" in spec, rotate_tac -1)
    apply(drule_tac x = la in spec, rotate_tac -1) apply(auto)
    apply(drule_tac x = "aa" in spec, rotate_tac -1)
      apply(drule_tac x = "ba" in spec, rotate_tac -1)
     apply(drule_tac x = "ej" in spec, rotate_tac -1) 
     apply(drule_tac x = "idxj" in spec, rotate_tac -1)
      apply(drule_tac x = "sz" in spec, rotate_tac -1)
     apply(drule_tac x = "kj" in spec, rotate_tac -1) apply(auto)

    apply(case_tac q, auto)
      apply(drule_tac x = ab in spec, rotate_tac -1)
     apply(drule_tac x = bb in spec, rotate_tac -1)
     apply(drule_tac x = "e" in spec, rotate_tac -1)
    apply(drule_tac x = la in spec, rotate_tac -1) 
    apply(drule_tac x = "a" in spec, rotate_tac -1)
      apply(drule_tac x = "b" in spec, rotate_tac -1)
     apply(drule_tac x = "er" in spec, rotate_tac -1) 
    apply(drule_tac x = "ls" in spec, rotate_tac -1) apply(auto)
      apply(drule_tac x = aa in spec, rotate_tac -1)
     apply(drule_tac x = ba in spec, rotate_tac -1)
     apply(drule_tac x = "ej" in spec, rotate_tac -1)
    apply(drule_tac x = idxj in spec, rotate_tac -1) 
      apply(drule_tac x = "sz" in spec, rotate_tac -1)
     apply(drule_tac x = "kj" in spec, rotate_tac -1) apply(auto)
    done
next
  case 6
  then show ?case 
    apply(auto)
     apply(case_tac e, auto) apply(drule_tac ll3_hasdesc2, auto)
    apply(case_tac e, auto) apply(drule_tac ll3_hasdesc2, auto)
    done
next
  case (7 h l)
  then show ?case
    apply(auto)
     apply(case_tac e, auto)
    apply(case_tac "mypeel
              (write_jump_targets (None # la) h #
               map (write_jump_targets (None # la)) l)", auto)
      apply(drule_tac mypeel_spec1, auto)
      apply(frule_tac ll3_descend_nonnil, auto)
      apply(drule_tac ll_descend_eq_r2l, auto) apply(case_tac hd, auto)
       apply(case_tac tl, auto)
        apply(case_tac h, auto)
        apply(case_tac bc, auto)
          apply(case_tac "mynth (None # la) x32", auto)

         apply(drule_tac x = "None#la" in spec, rotate_tac -1)
         apply(drule_tac x = "aa" in spec, rotate_tac -1)
         apply(drule_tac x = "bb" in spec, rotate_tac -1) apply(auto)
          apply(case_tac idxj, auto)

         apply(case_tac "mynth (None # la) x42", auto)

        apply(case_tac x51, auto)
    apply(case_tac "mypeel (map (write_jump_targets (None # None # la)) x52)", auto)
        apply(case_tac "ll_get_label x52 (ac # list)", auto)
        apply(case_tac "mypeel (map (write_jump_targets (Some ad # None # la)) x52)", auto)

       apply(case_tac h, auto) apply(case_tac bda, auto)
         apply(case_tac "mynth (None # la) x32", auto)
         apply(case_tac "mynth (None # la) x42", auto)
    apply(case_tac bc, auto)
         apply(drule_tac x = "None#la" in spec, rotate_tac -1)
         apply(drule_tac x = "a" in spec, rotate_tac -1)
       apply(drule_tac x = "b" in spec, rotate_tac -1) apply(auto)
    apply(drule_tac q = "(a,b)" and e = "x51a" in ll_descend_eq_l2r_list)
         apply(drule_tac x = "ab" in spec, rotate_tac -1)
       apply(drule_tac x = "bb" in spec, rotate_tac -1) 
                apply(drule_tac x = "ej" in spec, rotate_tac -1)
         apply(drule_tac x = "idxj" in spec, rotate_tac -1)
         apply(drule_tac x = "sz" in spec, rotate_tac -1)
         apply(drule_tac x = "ac#list" in spec, rotate_tac -1)

       apply(auto)
  (* bogus? *)
        apply(drule_tac x = a in spec, rotate_tac -1)
         apply(drule_tac x = "b" in spec, rotate_tac -1)
         apply(drule_tac x = "[]" in spec, rotate_tac -1)
        apply(auto)
        apply(drule_tac x = la in spec, rotate_tac -1)
         apply(drule_tac x = "a" in spec, rotate_tac -1)
        apply(drule_tac x = "b" in spec, rotate_tac -1)  
         apply(drule_tac x = "[]" in spec, rotate_tac -1)
        apply(drule_tac x = "t'" in spec, rotate_tac -1) apply(auto)

(* i'm confused here. *)

          apply(case_tac t, auto)

    sorry         apply(drule_tac x = "None#la" in spec, rotate_tac -1)

qed



case (1 q e i)
  then show ?case 
    apply(auto)
     apply(drule_tac ll3_hasdesc, auto)
    apply(drule_tac ll3_hasdesc, auto)

    done
next
  case (2 q e idx)
  then show ?case
    apply(auto)
     apply(drule_tac ll3_hasdesc, auto)
    apply(drule_tac ll3_hasdesc, auto)

    done
next
  case (3 q e idx n)
  then show ?case 
    apply(auto)
     apply(case_tac q, auto) apply(case_tac "mynth l idx", auto)
     apply(drule_tac ll3_hasdesc, auto)
     apply(case_tac q, auto) apply(case_tac "mynth l idx", auto)
     apply(drule_tac ll3_hasdesc, auto)
    done
next
  case (4 q e idx n)
  then show ?case
        apply(auto)
    apply(case_tac q, auto) apply(case_tac "mynth l idx", auto)
    apply(drule_tac x = idx in spec) apply(auto)
      apply(drule_tac ll3_hasdesc, auto)
     apply(drule_tac ll3_hasdesc, auto)
     apply(case_tac q, auto) apply(case_tac "mynth l idx", auto)
     apply(drule_tac ll3_hasdesc, auto)
    done
next
  case (5 q e l)
  then show ?case
    apply(auto)
    apply(case_tac q, auto)
    apply(case_tac e, auto)
     apply(case_tac "mypeel (map (write_jump_targets (None # la)) l)", auto)
    (* bogus *)
     apply(drule_tac x = 0 in spec, rotate_tac -1)
     apply(drule_tac x = 0 in spec, rotate_tac -1)
    apply(drule_tac x = "[]" in spec, rotate_tac -1)
     apply(drule_tac x = "la" in spec, rotate_tac -1)
    apply(auto)
    apply(case_tac "mypeel (map (write_jump_targets (None # None # la)) l)", auto)

next
  case 6
  then show ?case sorry
next
  case (7 h l)
  then show ?case sorry
qed
*)

(* validator to run after write_jump_targets *)
(*
fun ll4_validate_jump_targets :: "nat option list \<Rightarrow> ll4 \<Rightarrow> bool"
  where
"ll4_validate_jump_targets ns ((x,x'), LJmp a idx sz) =
  (case mynth ns idx of
    Some a' \<Rightarrow> (a = a')
   | None \<Rightarrow> False)"
| "ll4_validate_jump_targets ns ((x,x'), LJmpI a idx sz) =
  (case mynth ns idx of
    Some a' \<Rightarrow> (a = a')
   | None \<Rightarrow> False)"
| "ll4_validate_jump_targets ns (q, LSeq [] lsdec) = 
  (Lem.list_forall (ll4_validate_jump_targets (None#ns)) lsdec)"
| "ll4_validate_jump_targets ns (q, LSeq loc lsdec) = 
  (case ll_get_node (q, LSeq loc lsdec) loc of
   Some ((q, _), LLab e idx) \<Rightarrow> idx + 1 = length loc \<and>
     Lem.list_forall (ll4_validate_jump_targets ((Some q)#ns)) lsdec
   | _ \<Rightarrow> False)"
| "ll4_validate_jump_targets _ _ = True"
*)
(* the problem is that we end up repeatedly checking suffixes for
things, in the way we have this planned out
*)
(*
are we trying to do too much here? should we really worry about correctness
of the label?
*)
fun ll4_validate_jump_targets :: "nat option list \<Rightarrow> ll4 \<Rightarrow> bool" 
  where
"ll4_validate_jump_targets ns ((x,x'), LJmp a idx sz) =
  (case mynth ns idx of
    Some a' \<Rightarrow> (a = a')
   | None \<Rightarrow> False)"
| "ll4_validate_jump_targets ns ((x,x'), LJmpI a idx sz) =
  (case mynth ns idx of
    Some a' \<Rightarrow> (a = a')
   | None \<Rightarrow> False)"
| "ll4_validate_jump_targets ns (q, LSeq [] lsdec) = 
  (Lem.list_forall (ll4_validate_jump_targets (None#ns)) lsdec)"
| "ll4_validate_jump_targets ns (q, LSeq loc lsdec) = 
  (case ll_get_node (q, LSeq loc lsdec) loc of
   Some ((q, _), LLab e idx) \<Rightarrow> idx + 1 = length loc \<and>
     Lem.list_forall (ll4_validate_jump_targets ((Some q)#ns)) lsdec
   | _ \<Rightarrow> False)"
| "ll4_validate_jump_targets _ _ = True"

(* TODO: need to constrain llab jump target so it is a descendent of same seq? *)
(* are we taking the length of the wrong thing? *)
(* TODO: split into validate_jump_targets and
validate_jump_targets_list
this should make this doable *)
(*
make the second case a map or Forall, rather than a write_jump_targets on the Seq?
that might be better and alleviate the need to split in 2 functions
*)
(* old version of second part of this lemma *)
(*
(! q e l t' . write_jump_targets l (q, LSeq e ls) = Some t' \<longrightarrow>
  (! qj ej idxj sz kj . (t', (qj, LJmp ej idxj sz), kj) \<in> ll3'_descend \<longrightarrow>
  ((\<exists> qr er ls' ql el idxl  . t' = (qr, LSeq er ls') \<and> (t', (ql, LLab el idxl), er) \<in> ll3'_descend \<and> 
idxj + 1 = length kj \<and> fst ql = ej) \<or>
*)

(* root needs to be explicit LSeq *)
lemma ll_descend_prefix [rule_format] :
"(! a b e ls ad bd desc hk tk. 
  (((a, b), LSeq e ls), ((ad, bd), desc),  hk#tk) \<in> ll3'_descend \<longrightarrow>
   (! a' b' .
    (((a', b'), LSeq e (pref @ ls)), ((ad, bd), desc), ((hk + length pref) # tk)) \<in> ll3'_descend))
"
proof(induction pref)
case Nil
  then show ?case 
    apply(auto)
    apply(frule_tac ll3_hasdesc2, auto)
    apply(frule_tac ll3'_descend_relabelq)
     apply( rotate_tac[2] -1)
     apply(frule_tac[2] ll3'_descend_relabel) apply(auto)
    done
next
  case (Cons a pref)
  then show ?case
    apply(auto)
    apply(rule_tac ll_descend_eq_l2r, auto)
    apply(drule_tac x = a in spec)
    apply(drule_tac x = b in spec)
    apply(drule_tac x = e in spec)
    apply(drule_tac x = ls in spec)
    apply(drule_tac x = ad in spec)
    apply(drule_tac x = bd in spec)
    apply(drule_tac x = desc in spec)
    apply(drule_tac x = hk in spec)
    apply(drule_tac x = tk in spec)
    apply(auto)
    apply(drule_tac x = a in spec) apply(drule_tac x = a in spec)
    apply(rotate_tac 1)
    apply(drule_tac ll_descend_eq_r2l, auto)
    done
qed

(*
lemma ll_get_node_list_prefix :
ll_get_node_list
*)
lemma validate_jump_targets_spec :
"
  (! l . ll4_validate_jump_targets l t \<longrightarrow>
  (! qj ej idxj sz kj . (t, (qj, LJmp ej idxj sz), kj) \<in> ll3'_descend \<longrightarrow>
  ((\<exists> qr er ls ql el idxl  . t = (qr, LSeq er ls) \<and> (t, (ql, LLab el idxl), er) \<in> ll3'_descend \<and> 
                 idxj + 1 = length kj \<and> idxl + 1 = length er \<and> fst ql = ej) \<or>
   (? qd ed ls k1 k2 . (t, (qd, LSeq ed ls), k1) \<in> ll3'_descend \<and> 
    ((qd, LSeq ed ls), (qj, LJmp ej idxj sz), k2) \<in> ll3'_descend \<and>
    kj = k1 @ k2 \<and> idxj + 1 = length k2 \<and>
    ( ? ql el idxl kl . ((qd, LSeq ed ls), (ql, LLab el idxl), ed) \<in> ll3'_descend \<and> 
       idxl + 1 = length ed \<and> fst ql = ej)) \<or>
   (? n . mynth l n = Some ej \<and> length kj + n = idxj) 
  ))) \<and>
(* need to quantify over a prefix of the list here (i think) *)
(* we need to change kj = k1 @ k2, need to offset by list length
this also requires it being nonnil, of course *)
(! q e l pref . ll4_validate_jump_targets l (q, LSeq e (pref@ls)) \<longrightarrow>
  (! qj ej idxj sz kjh kjt . ((q, LSeq e ls), (qj, LJmp ej idxj sz), kjh#kjt) \<in> ll3'_descend \<longrightarrow>
  ((\<exists> qr  ql el idxl  . ((q, LSeq e (pref@ls)), (ql, LLab el idxl), e) \<in> ll3'_descend \<and> 
                 idxj  = length kjt \<and> idxl + 1 = length e \<and> fst ql = ej) \<or>
   (? qd ed lsd k1 k2 . ((q, LSeq e (pref@ls)), (qd, LSeq ed lsd), k1) \<in> ll3'_descend \<and> 
    ((qd, LSeq ed lsd), (qj, LJmp ej idxj sz), k2) \<in> ll3'_descend \<and>
    (kjh + length pref)#kjt = k1 @ k2 \<and> idxj + 1 = length k2 \<and>
    ( ? ql el idxl . ((qd, LSeq ed lsd), (ql, LLab el idxl), ed) \<in> ll3'_descend \<and> 
       idxl + 1 = length ed \<and> fst ql = ej)) \<or>
   (? n . mynth l n = Some ej \<and> length (kjh#kjt) + n = idxj) 
  )))
"
proof(induction rule:my_ll_induct)
case (1 q e i)
  then show ?case 
    apply(auto)
    apply(drule_tac ll3_hasdesc, auto)
    done
next
  case (2 q e idx)
  then show ?case
apply(auto)
    apply(drule_tac ll3_hasdesc, auto)
    done
next
  case (3 q e idx n)
  then show ?case
apply(auto)
    apply(drule_tac ll3_hasdesc, auto)
    done
next
  case (4 q e idx n)
  then show ?case
apply(auto)
    apply(drule_tac ll3_hasdesc, auto)
    done
next
  case (5 q e l)
  then show ?case 
(*proof of 5, without prefix *)

    apply(clarsimp)
    apply(case_tac e, clarsimp)
  (* now bogus *)
      apply(drule_tac x = "fst q" in  spec, rotate_tac -1)
      apply(drule_tac x = "snd q" in  spec, rotate_tac -1)
     apply(drule_tac x = "[]" in spec, rotate_tac -1)
     apply(drule_tac x = "la" in spec, rotate_tac -1)
     apply(drule_tac x = "[]" in spec, rotate_tac -1) apply(auto)
      apply(drule_tac x = "a" in  spec, rotate_tac -1)
      apply(drule_tac x = "b" in  spec, rotate_tac -1)
      apply(drule_tac x = "ej" in spec, rotate_tac -1)
apply(drule_tac x = "idxj" in  spec, rotate_tac -1)
      apply(drule_tac x = "sz" in  spec, rotate_tac -1)
    apply(frule_tac ll3_descend_nonnil, auto)
      apply(drule_tac x = "hd" in  spec, rotate_tac -1)
      apply(drule_tac x = "tl" in  spec, rotate_tac -1)
      apply(auto)

     apply(case_tac "ll_get_node_list l (aa#list)", auto)
     apply(rename_tac boo, case_tac boo, auto)
    apply(drule_tac x = "fst q" in  spec, rotate_tac -1)
      apply(drule_tac x = "snd q" in  spec, rotate_tac -1)
     apply(drule_tac x = "aa#list" in spec, rotate_tac -1)
     apply(drule_tac x = "la" in spec, rotate_tac -1)
     apply(drule_tac x = "[]" in spec, rotate_tac -1)
     apply(auto)
      apply(drule_tac x = "a" in  spec, rotate_tac -1)
      apply(drule_tac x = "b" in  spec, rotate_tac -1)
      apply(drule_tac x = "ej" in spec, rotate_tac -1)
apply(drule_tac x = "idxj" in  spec, rotate_tac -1)
     apply(drule_tac x = "sz" in  spec, rotate_tac -1)
    apply(frule_tac ll3_descend_nonnil, auto)
      apply(drule_tac x = "hd" in  spec, rotate_tac -1)
      apply(drule_tac x = "tl" in  spec, rotate_tac -1)
      apply(auto)

     apply(case_tac "ll_get_node_list l (aa#list)", auto)
     apply(rename_tac boo, case_tac boo, auto)
    apply(drule_tac x = "fst q" in  spec, rotate_tac -1)
      apply(drule_tac x = "snd q" in  spec, rotate_tac -1)
     apply(drule_tac x = "aa#list" in spec, rotate_tac -1)
    apply(drule_tac x = "la" in spec, rotate_tac -1)
    apply(drule_tac x = "[]" in spec, rotate_tac -1)
    apply(auto)
      apply(drule_tac x = "a" in  spec, rotate_tac -1)
      apply(drule_tac x = "b" in  spec, rotate_tac -1)
      apply(drule_tac x = "ej" in spec, rotate_tac -1)
apply(drule_tac x = "idxj" in  spec, rotate_tac -1)
    apply(drule_tac x = "sz" in  spec, rotate_tac -1)
    apply(frule_tac ll3_descend_nonnil, auto)

    apply(drule_tac x = "hd" in  spec, rotate_tac -1)
apply(drule_tac x = "tl" in  spec, rotate_tac -1)
    apply(auto)
    apply(drule_tac q = q and e = "aa#list" in ll_descend_eq_l2r_list)
  (* first, prove the two descendents are equal (determinism)
then, easy contradiction*)
    apply(subgoal_tac "ej = ab \<and> el = x21 \<and> bb = ba")
    apply(drule_tac x = bb in spec, rotate_tac -1)
    apply(drule_tac x = el in spec, rotate_tac -1)
    apply(drule_tac x = "length list" in spec, rotate_tac -1)
     apply(auto)
    done
next
  case 6
  then show ?case
    apply(clarsimp)
    apply(drule_tac ll3_hasdesc2, auto)
    done
next
  case (7 h l)
  then show ?case 
    apply(clarsimp)
    apply(case_tac e, auto)
    apply(case_tac kjh, auto)
       apply(drule_tac x = "None#la" in spec, auto) apply(rotate_tac -1)
       apply(frule_tac ll_descend_eq_r2l, auto)
       apply(case_tac kjt, auto)
        apply(case_tac "mynth (None # la) idxj", auto)
        apply(case_tac idxj, auto)
       apply(drule_tac ll_descend_eq_l2r)
apply(drule_tac x = aa in spec, rotate_tac -1)
apply(drule_tac x =ba in spec, rotate_tac -1)
    apply(drule_tac x = ej in spec, rotate_tac -1)
    apply(drule_tac x = idxj in spec, rotate_tac -1)
       apply(drule_tac x = sz in spec, rotate_tac -1)
apply(drule_tac x = "ab#list" in spec, rotate_tac -1)
       apply(auto)
    apply(rule_tac x = ac in exI)
    apply(rule_tac x = bb in exI)
         apply(rule_tac x = er in exI)
         apply(rule_tac x = ls in exI)
         apply(rule_tac x = "[length pref]" in exI)
         apply(auto)
         apply(auto simp add:ll3'_descend.intros)
(* next, length pref cons ... *)

    apply(rule_tac x = ac in exI)
    apply(rule_tac x = bb in exI)
         apply(rule_tac x = ed in exI)
        apply(rule_tac x = ls in exI)
         apply(rule_tac x = "length pref#k1" in exI)
        apply(auto)
    apply(subgoal_tac "(((a, b), llt.LSeq [] (pref @ h # l)),
        ((ac, bb), llt.LSeq ed ls), (0 + length pref) # k1)
       \<in> ll3'_descend")
         apply(rule_tac[2] a = a and b = b in ll_descend_prefix)
         apply(auto)
        apply(rule_tac ll_descend_eq_l2r, auto)
    apply(case_tac h, auto)
        apply(drule_tac k = k1 in ll_descend_eq_r2l) apply(auto)

       apply(case_tac n, auto)

      apply(frule_tac ll_descend_eq_r2l, auto)
      apply(rotate_tac 1)
      apply(drule_tac x = 0 in spec, rotate_tac -1)
      apply(drule_tac x = 0 in spec, rotate_tac -1)
      apply(drule_tac x = "[]" in spec, rotate_tac -1)
    apply(drule_tac x = la in spec, rotate_tac -1)
      apply(drule_tac x = "pref@[h]" in spec, rotate_tac -1) apply(auto)
      apply(drule_tac q = "(0,0)" and e = "[]" in ll_descend_eq_l2r_list)
      apply(drule_tac x = aa in spec, rotate_tac -1)
      apply(drule_tac x = ba in spec, rotate_tac -1)
apply(drule_tac x = ej in spec, rotate_tac -1)
apply(drule_tac x = idxj in spec, rotate_tac -1)
      apply(drule_tac x = sz in spec, rotate_tac -1)
apply(drule_tac x = nat in spec, rotate_tac -1)
apply(drule_tac x = kjt in spec, rotate_tac -1)
      apply(auto)
      apply(rule_tac x = ab in exI)
      apply(rule_tac x = bb in exI)
    apply(rule_tac x = ed in exI)
      apply(rule_tac x = lsd in exI)
      apply(rule_tac x = k1 in exI) apply(auto)
      apply(drule_tac k = k1 in ll3'_descend_relabelq) apply(auto)

     apply(case_tac "ll_get_node_list (pref @ h # l) (ab # list)", auto)
     apply(rename_tac boo, case_tac boo, auto)
     apply(case_tac kjh, auto)
      apply(frule_tac ll_descend_eq_r2l, auto)
    apply(drule_tac x = "Some ac # la" in spec, auto) apply(rotate_tac -1)
      apply(case_tac kjt, auto)
       apply(case_tac "mynth (Some ac # la) idxj", auto)
       apply(case_tac idxj, auto)
      apply(drule_tac ll_descend_eq_l2r) 
      apply(drule_tac x = aa in spec, rotate_tac -1)
  apply(drule_tac x = ba in spec, rotate_tac -1)
  apply(drule_tac x = ej in spec, rotate_tac -1)
  apply(drule_tac x = idxj in spec, rotate_tac -1)
      apply(drule_tac x = sz in spec, rotate_tac -1)
      apply(drule_tac x = "ad#lista" in spec, rotate_tac -1)
      apply(auto)
        apply(rule_tac x = ae in exI)
    apply(rule_tac x = bc in exI)
    apply(rule_tac x = er in exI)
    apply(rule_tac x = ls in exI)
    apply(rule_tac x = "[length pref]" in exI) apply(auto)
    apply(subgoal_tac "(((a, b),
         llt.LSeq (ab # list)
          (pref @ ((ae, bc), llt.LSeq er ls) # l)),
        ((ae, bc), llt.LSeq er ls), [0 + length pref])
       \<in> ll3'_descend")
    apply(rule_tac [2] a = a and b = b in ll_descend_prefix) apply(auto)
    apply(auto simp add:ll3'_descend.intros)
        apply(rule_tac x = ae in exI)
    apply(rule_tac x = bc in exI)
    apply(rule_tac x = ed in exI)
       apply(rule_tac x = ls in exI)
       apply(rule_tac x = "length pref # k1" in exI) apply(auto)
    apply(subgoal_tac "(((a, b), llt.LSeq (ab # list) (pref @ h # l)),
        ((ae, bc), llt.LSeq ed ls), (0 + length pref) # k1)
       \<in> ll3'_descend")
        apply(rule_tac [2] a = a and b = b in ll_descend_prefix) apply(auto)
       apply(rule_tac ll_descend_eq_l2r, auto)
    apply(case_tac h, auto)
    apply(drule_tac k = k1 in ll_descend_eq_r2l)
       apply(auto)

      apply(case_tac n, auto)

    apply(frule_tac ll_descend_eq_r2l, auto)
     apply(rotate_tac 1)
     apply(drule_tac x = 0 in spec, rotate_tac -1)
     apply(drule_tac x = 0 in spec, rotate_tac -1)
     apply(drule_tac x = "ab#list" in spec, rotate_tac -1)
     apply(drule_tac x = "la" in spec, rotate_tac -1)
     apply(drule_tac x = "pref @ [h]" in spec, rotate_tac -1) apply(auto)
     apply(drule_tac x = aa in spec, rotate_tac -1)
     apply(drule_tac x = ba in spec, rotate_tac -1)
    apply(drule_tac x = ej in spec, rotate_tac -1)
    apply(drule_tac x = idxj in spec, rotate_tac -1)
     apply(drule_tac x = sz in spec, rotate_tac -1)
    apply(drule_tac x = nat in spec, rotate_tac -1)
     apply(drule_tac x = kjt in spec, rotate_tac -1)
     apply(drule_tac q = "(0,0)" and e = "(ab # list)" and kh = "nat" in ll_descend_eq_l2r_list)
    apply(auto)
    apply(rule_tac x = ad in exI)
    apply(rule_tac x = bc in exI)
    apply(rule_tac x = ed in exI)
     apply(rule_tac x = lsd in exI)
     apply(rule_tac x = k1 in exI)
     apply(auto)
    apply(rule_tac ll3'_descend_relabelq) apply(auto)

    apply(case_tac "ll_get_node_list (pref @ h # l) (ab # list)", auto)
     apply(rename_tac boo, case_tac boo, auto)
     apply(case_tac kjh, auto)
      apply(frule_tac ll_descend_eq_r2l, auto)
    apply(drule_tac x = "Some ac # la" in spec, auto) apply(rotate_tac -1)
      apply(case_tac kjt, auto)
       apply(case_tac "mynth (Some ac # la) idxj", auto)
      apply(case_tac idxj, auto)
      apply(rotate_tac -4)
      apply(drule_tac x = bb in spec, rotate_tac -1)
    apply(drule_tac x = x21 in spec, rotate_tac -1)
      apply(drule_tac x = "length list" in spec, rotate_tac -1)
    apply(drule_tac q = "(a, b)" and e = "ab#list" in ll_descend_eq_l2r_list) apply(auto)
    apply(drule_tac ll_descend_eq_l2r)
     apply(drule_tac x = aa in spec, rotate_tac -1)
     apply(drule_tac x = ba in spec, rotate_tac -1)
    apply(drule_tac x = ej in spec, rotate_tac -1)
    apply(drule_tac x = idxj in spec, rotate_tac -1)
     apply(drule_tac x = sz in spec, rotate_tac -1)
     apply(drule_tac x = "ad#lista" in spec, rotate_tac -1)
     apply(auto)
       apply(rule_tac x = ae in exI)
       apply(rule_tac x = bc in exI)
       apply(rule_tac x = er in exI)
       apply(rule_tac x = ls in exI)
       apply(rule_tac x = "[length pref]" in exI)
       apply(auto)
    apply(subgoal_tac "(((a, b), llt.LSeq (ab # list) (pref @ ((ae, bc), llt.LSeq er ls) # l)),
        ((ae, bc), llt.LSeq er ls), [0 + length pref])
       \<in> ll3'_descend")
        apply(rule_tac[2] ll_descend_prefix) apply(auto)
       apply(rule_tac ll_descend_eq_l2r, auto)
      apply(rule_tac x = ae in exI)
      apply(rule_tac x = bc in exI)
apply(rule_tac x = ed in exI)
      apply(rule_tac x = ls in exI)
      apply(rule_tac x = "length pref#k1" in exI) apply(auto)
    apply(subgoal_tac "Suc idxl = length ed \<Longrightarrow>
       (((a, b), llt.LSeq (ab # list) (pref @ h # l)), ((ae, bc), llt.LSeq ed ls),
        (0 +length pref) # k1)
       \<in> ll3'_descend")
       apply(rule_tac [2] ll_descend_prefix) apply(auto)
      apply(rule_tac ll_descend_eq_l2r, auto)
    apply(case_tac h) apply(auto)
      apply(drule_tac k = k1 in ll_descend_eq_r2l) apply(auto)
     apply(case_tac n, auto)
    
     apply(rotate_tac 2)
     apply(drule_tac x = bb in spec, rotate_tac -1)
     apply(drule_tac x = x21 in spec, rotate_tac -1)
     apply(drule_tac x = "length list" in spec, rotate_tac -1)
    apply(drule_tac e = "ab#list" and q = "(a,b)" in ll_descend_eq_l2r_list)
    apply(auto)

    apply(frule_tac ll_descend_eq_r2l, auto)
    apply(rotate_tac 1)
     apply(drule_tac x = 0 in spec, rotate_tac -1)
     apply(drule_tac x = 0 in spec, rotate_tac -1)
     apply(drule_tac x = "ab#list" in spec, rotate_tac -1)
    apply(drule_tac x = "la" in spec, rotate_tac -1)
     apply(drule_tac x = "pref @ [h]" in spec, rotate_tac -1) apply(auto)
     apply(drule_tac x = aa in spec, rotate_tac -1)
     apply(drule_tac x = ba in spec, rotate_tac -1)
     apply(drule_tac x = "ej" in spec, rotate_tac -1)
    apply(drule_tac x = "idxj" in spec, rotate_tac -1)
    apply(drule_tac x = "sz" in spec, rotate_tac -1) 
        apply(drule_tac x = "nat" in spec, rotate_tac -1)
    apply(drule_tac x = "kjt" in spec, rotate_tac -1) 
    apply(drule_tac l = l and q = "(0,0)" and e = "ab#list" in ll_descend_eq_l2r_list)
    apply(auto)
     apply(rotate_tac -1)
    apply(frule_tac ll_descend_eq_r2l, auto)
     apply(drule_tac q' = "(a, b)" in ll3'_descend_relabelq) apply(auto)
    apply(rotate_tac 1)
    apply(drule_tac x = bc in spec, rotate_tac -1)
    apply(drule_tac x = el in spec, rotate_tac -1)
     apply(drule_tac x = "length list" in spec, rotate_tac -1)
    apply(auto)

    apply(rule_tac x = ad in exI)
    apply(rule_tac x = bc in exI)
    apply(rule_tac x = ed in exI)
    apply(rule_tac x = lsd in exI)
    apply(rule_tac x = k1 in exI)  
    apply(auto)
    apply(rule_tac ll3'_descend_relabelq)
    apply(auto)
    done
qed
(*
if we are valid 4
and we call write_jump_targets with context (list of nat) c
then for each jump descended from the root, 1 of 3 cases holds:
- the root has a (unique) descendent matching label with the address that is the address of the jump
- the root has a (unique) descended seq node, from which is descended both a (unique) matching label and
the jump, and the jump's stored address matches the label's
- (there is no matching label) and our jump's idx exceeds the depth of our
root descendent relation, but the address in the jump is equal to the one in context
(mynth, for appropriate value of n)
*)
(*
TODO: rewrite ll_get_label in terms of ll_get_node, or at least prove
the two equivalent
*)


(*
lemma ll4_emptylab_check :
*)

(*
idea: we should prove that after calling write_jumps on a buffer,
successfully,
each jump node will contain a location for which getByLoc will return
the same location as looking up their label's address directly
*)

(*
more necessary lemmas:
- if an ll4 is ll3_valid, then getting the location of a
seq node's destination in the buffer will succeed
and return a jump dest
- jumping to a jump dest will have the same
semantics as executing the sub-Sequence node starting
and the label - this should be restated in a lower level way
- finally, we can tie all this together and show that the JUMP instruction will have this effect
We will also need to push these results through to 
the bytecode output, probably by proving a
lemma about codegen'
(idea: lookups by location
in an ll4
(really "tail" subsequences)
are preserved when you look up in bytecode)
*)

(*
more concretely, take a whole program P that we have called write_jumps on.
If we have a node P' equal to or descended from P
that is a jump or jumpi,
it will have the address of a Label node in it (according to getByLoc).
Furthermore, this label will be such that
(it is descended from P' at depth equal to its depth annotation) and
(the jump is descended from P' at a depth equal to its depth annotation)

other validity predicates mean we do not need to reason about
the uniqueness of this label.
*)

(*
we can also state a theorem about getByLoc:
returned node will be descended (is this useful?)
how to further characterize this descent?
*)

(*
inductive_set ll_jumps_havespace
idea: the number of bytes set aside for the jump label
must be equal to the address mod 256 (?)
*)

end