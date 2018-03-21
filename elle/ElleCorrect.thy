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
  (? q1 e1 ls . t1 = (q1, LSeq e1 ls) \<and> ls ! x = t2))"
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

end