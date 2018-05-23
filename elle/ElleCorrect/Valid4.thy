theory Valid4
  imports "Valid3"
begin


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

lemma ll4_init_same :
"((! t' . ll4_init t = t' \<longrightarrow>
  ll_purge_annot t' = ll_purge_annot t)
\<and>
(! ts' . map ll4_init ts = ts' \<longrightarrow>
  map ll_purge_annot ts' = map ll_purge_annot ts))"
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
  then show ?case by auto
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

(* ll3_bump_same *)

lemma ll3_bump_same :
"
(! q e ls . (t :: ll3) = (q, LSeq e ls) \<longrightarrow>
  (! b . map ll_purge_annot ls = map ll_purge_annot (ll3_bump b ls)))
\<and>
(! b . map ll_purge_annot (l :: ll3 list) = map ll_purge_annot (ll3_bump b l))"
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
    apply(case_tac h, auto)
    apply(case_tac baa, auto)
    done
qed

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

(* inc_jump_same *)

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

(* need ll3_inc_jump_same *)
lemma ll3_inc_jump_same' :
"(! q e ls . (t :: ll3) = (q, LSeq e ls) \<longrightarrow>
  (! n p l' b . ll3_inc_jump (ls :: ll3 list) n p = (l', b) \<longrightarrow>
   map ll_purge_annot ls = map ll_purge_annot l')
)
\<and>
(! n p l' b . ll3_inc_jump (l :: ll3 list) n p = (l', b) \<longrightarrow>
   map ll_purge_annot l = map ll_purge_annot l')
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
    apply(case_tac h, auto)
    apply(case_tac baa, auto)
        apply(case_tac "ll3_inc_jump l (Suc n) p", auto)
        apply(drule_tac x=  "Suc n" in spec)
        apply(drule_tac x = p in spec)
        apply(drule_tac x = aa in spec) apply(auto)

        apply(case_tac "ll3_inc_jump l (Suc n) p", auto)
        apply(drule_tac x=  "Suc n" in spec)
        apply(drule_tac x = p in spec)
       apply(drule_tac x = aa in spec) apply(auto)
      apply(case_tac p, auto)
       apply(case_tac "ll3_inc_jump l (Suc n) []", auto)
       apply(drule_tac x = "Suc n" in spec)
       apply(drule_tac x = "[]" in spec)
       apply(drule_tac x = aa in spec) apply(auto)

      apply(case_tac list, auto)
       apply(case_tac "n=aa", auto)
        apply(insert ll3_bump_same)
        apply(auto)

       apply(case_tac "ll3_inc_jump l (Suc n) [aa]", auto)
       apply(drule_tac x = "Suc n" in spec, rotate_tac -1)
       apply(drule_tac x = "[aa]" in spec, rotate_tac -1)
       apply(drule_tac x = "ab" in spec, rotate_tac -1)
       apply(auto)

    apply(case_tac "ll3_inc_jump l (Suc n)
              (aa # ab # lista)", auto)
           apply(drule_tac x = "Suc n" in spec, rotate_tac -1)
       apply(drule_tac x = "(aa # ab # lista)" in spec, rotate_tac -1)
       apply(drule_tac x = "ac" in spec, rotate_tac -1)
      apply(auto)

     apply(case_tac p, auto)
      apply(case_tac "ll3_inc_jump l (Suc n) []", auto)
      apply(drule_tac x = "Suc n" in spec)
      apply(drule_tac x = "[]" in spec)
      apply(drule_tac x = "aa" in spec) apply(auto)

     apply(case_tac list, auto)
      apply(case_tac "n=aa", auto)
      apply(case_tac "ll3_inc_jump l (Suc n) [aa]", auto)
      apply(drule_tac x = "Suc n" in spec)
      apply(drule_tac x = "[aa]" in spec)
      apply(drule_tac x = "ab" in spec) apply(auto)

    apply(case_tac "ll3_inc_jump l (Suc n)
              (aa # ab # lista)", auto)
     apply(drule_tac x = "Suc n" in spec)
     apply(drule_tac x = "aa # ab # lista" in spec)
     apply(drule_tac x = ac in spec) apply(auto)

    apply(case_tac p, auto)
     apply(case_tac " ll3_inc_jump l (Suc n) []", auto)
    apply(rotate_tac 1)
     apply(drule_tac x = "Suc n" in spec, rotate_tac -1)
       apply(drule_tac x = "[]" in spec, rotate_tac -1)
     apply(drule_tac x = "aa" in spec, rotate_tac -1)
     apply(auto)

    apply(case_tac "n=aa", auto)

     apply(case_tac "ll3_inc_jump x52 0 list", auto)
     apply(case_tac bb, auto)
         apply(drule_tac x = "0" in spec, rotate_tac -1)
       apply(drule_tac x = "list" in spec, rotate_tac -1)
     apply(drule_tac x = "ab" in spec, rotate_tac -1)
      apply(auto)

     apply(case_tac "ll3_inc_jump l aa (aa # list)", auto)
           apply(drule_tac x = "0" in spec, rotate_tac -1)
       apply(drule_tac x = "list" in spec, rotate_tac -1)
     apply(drule_tac x = "ab" in spec, rotate_tac -1)
      apply(auto)

      apply(drule_tac x = "0" in spec, rotate_tac -1)
       apply(drule_tac x = "list" in spec, rotate_tac -1)
     apply(drule_tac x = "ab" in spec, rotate_tac -1)
      apply(auto)

    apply(case_tac "ll3_inc_jump l (Suc n)
              (aa # list) ", auto)
    apply(rotate_tac 1)
    apply(drule_tac x = "Suc n" in spec, rotate_tac -1)
    apply(drule_tac x = "aa#list" in spec, rotate_tac -1)
    apply(drule_tac x = "ab" in spec, rotate_tac -1)
    apply(auto)
    done
qed

lemma ll3_inc_jump_same [rule_format] :
"(! n p l' b . ll3_inc_jump (l :: ll3 list) n p = (l', b) \<longrightarrow>
   map ll_purge_annot l = map ll_purge_annot l')"
  apply(insert ll3_inc_jump_same')
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


(* need ll3_inc_jump_wrap_same *)
lemma ll3_inc_jump_wrap_same :
"ll3_inc_jump_wrap t p = t' \<Longrightarrow>
  ll_purge_annot t = ll_purge_annot t'"
  apply(auto)
  apply(case_tac t, auto)
  apply(case_tac ba, auto)
  apply(case_tac "ll3_inc_jump x52 0 p", auto)
  apply(case_tac ba, auto)
  apply(drule_tac ll3_inc_jump_same)
  apply(auto)
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

(* TODO: inductive argument here will need to change
when we de-fuel process_jumps_loop *)
lemma process_jumps_loop_same' [rule_format] :
"(!  t2 t' . process_jumps_loop n (t2 :: ll3) = Some t' \<longrightarrow>
(! t  . ll_purge_eq (t :: ll3) t2 \<longrightarrow>
    ll_purge_annot t = ll_purge_annot t'))
"
proof(induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case 
    apply(auto)
    apply(case_tac "ll3_resolve_jump_wrap
              ((a, b), ba)", auto)
     apply(drule_tac ll_purge_eq.cases, auto)
    apply(case_tac "ll3_inc_jump_wrap ((a, b), ba)
          (rev x3)", auto)
    apply(drule_tac x = ac in spec)
    apply(drule_tac x = bf in spec)
    apply(drule_tac x = bfa in spec)
    apply(drule_tac x = aa in spec)
    apply(drule_tac x = bb in spec)
    apply(drule_tac x = bc in spec)
    apply(auto)
    apply(drule_tac x = ac in spec)
    apply(drule_tac x = bf in spec)
    apply(subgoal_tac "ll_purge_eq ((ac, bf), bfa) ((ac, bf), bfa)")
    apply(rule_tac [2] ll_purge_eq_refl)
    apply(drule_tac x = bfa in spec) apply(auto)
    apply(frule_tac ll3_inc_jump_wrap_same)
    apply(drule_tac ll_purge_eq.cases)
     apply(auto)
    done
qed

lemma process_jumps_loop_same [rule_format] :
"(!  t t' . process_jumps_loop n (t :: ll3) = Some t' \<longrightarrow>
    ll_purge_annot t = ll_purge_annot t')
"
  apply(auto)
  apply(drule_tac process_jumps_loop_same')
   apply(auto)
  apply(rule_tac ll_purge_eq_refl)
  done

(* then need a proof in semantics about how the semantics
are the same if discarding annotations are same (?) *)

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

(* TODO: we probably eventually need to prove a relationship between
encode_size and the number of bytes output. the spec of this function ultimately
needs to talk about addresses in the output code being the right size *)
fun validate_addrs :: "ll4 \<Rightarrow> bool" where
"validate_addrs (x, LJmp a _ sz) = (encode_size a = sz)"
| "validate_addrs (x, LJmpI a _ sz) = (encode_size a = sz)"
| "validate_addrs (x, LSeq e ls) = Lem.list_forall validate_addrs ls"
| "validate_addrs _ = True"

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
lemma validate_jump_targets_spec' :
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

lemma validate_jump_targets_spec [rule_format] :
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
  )))
"
  apply(insert validate_jump_targets_spec')
  apply(auto)
  done



lemma write_jump_targets_same' :
"
(! l t' . write_jump_targets l (t :: ll4) = Some t' \<longrightarrow>
  ll_purge_annot t = ll_purge_annot t')
\<and>
(! l ls' . mypeel (map (write_jump_targets l) ls) = Some ls' \<longrightarrow>
  map ll_purge_annot ls = map ll_purge_annot ls'
)
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
    apply(case_tac q, auto)
    apply(case_tac "mynth l idx", auto)
    done
next
  case (4 q e idx n)
  then show ?case 
apply(auto)
    apply(case_tac q, auto)
    apply(case_tac "mynth l idx", auto)
    done
next
  case (5 q e l)
  then show ?case 
    apply(auto)
    apply(case_tac q, auto)
    apply(case_tac e, auto)
     apply(case_tac "mypeel (map (write_jump_targets (None # la)) l)", auto)
    apply(case_tac " ll_get_label l (ab # list)", auto)
    apply(case_tac "mypeel (map (write_jump_targets (Some ac # la)) l)", auto)
    done
next
  case 6
  then show ?case 
    apply(auto)
    done
next
  case (7 h l)
  then show ?case
    apply(auto)
    apply(drule_tac mypeel_spec1, auto)
    done
qed

(* write_jump_targets_qvalid - or is this needed? 
i think we need it to build a link between the address in EVM and the ll semantics *)

lemma write_jump_targets_qvalid' :
"((x, (t :: ll4t)) \<in> ll_valid_q \<longrightarrow> 
  (! lp x' t' . write_jump_targets lp (x, t) = Some (x', t') \<longrightarrow> 
    x = x' \<and>
    (x, t') \<in> ll_valid_q)) \<and>
 (((m,m'), (l :: ll4 list)) \<in> ll_validl_q \<longrightarrow> 
    (! lp l' . mypeel (map (write_jump_targets lp) l) = Some l' \<longrightarrow>
       ((m, m'), l') \<in> ll_validl_q))"
proof(induction rule: ll_valid_q_ll_validl_q.induct)
case (1 i x e)
  then show ?case 
    apply(auto simp add:ll_valid_q_ll_validl_q.intros)
    done
next
  case (2 x d e)
  then show ?case 
    apply(auto simp add:ll_valid_q_ll_validl_q.intros)
    done
next
  case (3 x d e s)
  then show ?case 
    apply(auto)
    apply(case_tac "mynth lp d") apply(auto)
     apply(case_tac "mynth lp d") apply(auto)
apply(case_tac "mynth lp d") apply(auto)
     apply(auto simp add:ll_valid_q_ll_validl_q.intros)
    done
next
  case (4 x d e s)
  then show ?case 
    apply(auto)
      apply(case_tac "mynth lp d") apply(auto)
     apply(case_tac "mynth lp d") apply(auto)
apply(case_tac "mynth lp d") apply(auto)
    apply(auto simp add:ll_valid_q_ll_validl_q.intros)
    done
next
  case (5 n l n' e)
  then show ?case 
    apply(clarsimp)
    apply(case_tac e, clarsimp)
    apply(auto)
    apply(case_tac " mypeel
              (map (write_jump_targets (None # lp)) l)", auto)
    apply(case_tac " mypeel
              (map (write_jump_targets (None # lp)) l)", auto)
    apply(case_tac " mypeel
              (map (write_jump_targets (None # lp)) l)", auto)
     apply(drule_tac x = "None#lp" in spec) apply(drule_tac x = aa in spec) apply(auto)
     apply(auto simp add:ll_valid_q_ll_validl_q.intros)

    apply(case_tac "ll_get_label l (aa#list)", auto)
    apply(case_tac "mypeel
              (map (write_jump_targets (Some ab # lp)) l)", auto)
    apply(case_tac "ll_get_label l (aa#list)", auto)
    apply(case_tac "mypeel
              (map (write_jump_targets (Some ab # lp)) l)", auto)

        apply(case_tac "ll_get_label l (aa#list)", auto)
    apply(case_tac "mypeel
              (map (write_jump_targets (Some ab # lp)) l)", auto)
    apply(drule_tac x = "Some ab # lp" in spec)
    apply(drule_tac x = "ac" in spec) apply(auto)
    apply(auto simp add:ll_valid_q_ll_validl_q.intros)
    done
next
  case (6 n)
  then show ?case 
    apply(auto)
    apply(rule_tac ll_valid_q_ll_validl_q.intros)
    done
next
  case (7 n h n' t n'')
  then show ?case 
    apply(auto)
    apply(drule_tac mypeel_spec1) apply(auto)
    apply(drule_tac x = lp in spec, rotate_tac -1)
    apply(drule_tac x = a in spec, rotate_tac -1)
    apply(drule_tac x = b in spec, rotate_tac -1)
    apply(drule_tac x = ba in spec, rotate_tac -1) apply(auto)
    apply(drule_tac x = lp in spec) 
    apply(drule_tac x = t' in spec) apply(auto)
    apply(auto simp add:ll_valid_q_ll_validl_q.intros)
    done
qed

lemma write_jump_targets_qvalid1 [rule_format] :
"((x, (t :: ll4t)) \<in> ll_valid_q \<longrightarrow> 
  (! lp x' tt' . write_jump_targets lp (x, t) = Some tt' \<longrightarrow>
    tt' \<in> ll_valid_q))
"
  (* last 3 args bogus *)
  apply(insert write_jump_targets_qvalid'[of x t 0 0 "[]"])
  apply(auto)
  done

(* Now, we need the final theorem
- if a Seq node is qvalid starting from 0
- and it has a descendent (that is qvalid)
  - and that descendent has a unique label
  - then executing that Seq in "skip mode" in the ll semantics
    is equivalent to executing the code generated from the root Seq node
    with PC equal to that address
      
Q: How to generalize over different continuations?
Is this necessary?
Is this possible?

Another idea: generalize over location. Have an address offset to make up the
difference between 0 and the Seq node's start
*)

(*

Idea: IF we are valid3
AND validate_jump_targets (on the root?) (with what scope arguments?) is true
AND we have an lc (continuations list, incoming to ll_sem)
AND for each item in the continuations list
  - either it is None, and there is a Seq with no descendents
  - or it is Some, and there is a Seq for which scanning to that seq at that depth in the tree has the same semantics

THEN

ll_sem x matches
program_sem (purge_annot (compile x))

*)

(*

Question: do we need to fix a root? I think we need to say either:
1. The incoming lc is nil, and the node we are on is the root
2. The incoming lc is nonnil, and we have a series of sub-roots
  - How does this shake out though?

*)

(*

How do we match up incoming LC with incoming addresses in validate_jump_targets?
  - the idea is that the address stored at each node should be the address of that label
    (and equal to the address that gets written in the jump)
  - jumps get resolved in 1 of 2 ways
    - 1. they are given by a continuation
      2. there exist a descendent, and semantics are equal to "scanning" that descendent at appropriate depth

is just positing the existence of such a root enough?

Also, what do we do induction on? My instinct is still that it should be on the syntax tree (ll)

*)

(* Another attempt at restating:

If we have a Seq node that is valid3' with some list l, then

1. l is nil and that Seq is the root. Then we have the following 2 results:
   a. The non-scanning semantics of Seq are the same as running the Seq starting from the beginning (pc = 0)
   b. Either
      i. There is no label, and scanning fails
      ii. There is a unique label, and the semantics of scanning are the same as jumping to that address

- important - how do we handle all these different nonnil cases? -
problem is that we may end up following one of the passed-in continuations
how do we account for that in our low-level semantic steps?
2. l is nonnil. Then there must be a root such that
- starting that root from the beginning has the same semantics as starting EVM semantics from beginning
  - (needed?)
- starting our node from the beginning (using continuations passed in
  has same semantics as starting EVM semantics from its beginning
- starting our node in scanning mode (if there is on)


2'. HOW do we make sure the continuations appropriately "match up"?
This seems to be the other missing piece.
- idea: (continuation, address) pairs are either both None
- or, running the continuation has same result as jumping to address in global
*)

(*

How to handle generalizing over different scanning depths?
  - that is the key. if we scan at 0, then we will look for descendents that point up at this node
  - if we scan at n, then we will need to compare to one of the passed-in continuations
    - idea: scanning at a value > 0 means we need to look up in the params (mynth)
      get the continuation, and then that continuation has semantics equal to scanning result at this node (?)

*)

(* we need a lemma allowing us to "push" facts about
locations through the codegen step
(in particular - if we are ll_valid, then
the labeled starting address equals the address
it is stored in the output buffer)
*)

(* how to deal with incoming continuation?
it may not get run at all.
the incoming continuation is what we do next,
in the absence of control flow.
so, we should have some kind of condition
relating it to the root

the only place where we discard the current continuation is on a jump
in this case, we are  jumping to a scope, which ought to have
the same "final" continuation somewhere in it.

*)

value "List.subseqs ([1, 2, 3] :: nat list)"

(* needed to describe relationship between descended childpath
and the series of assertions it will require about descended nodes'
scanning

for each element in the tails list of the root descendent childpath,

(do we need a similar "heads" function to describe how we actually get to the
node)
*)


(* the idea behind pathsplits is that
if we have nil, this cannot be a valid path (so no need to worry about case)
if we have a singleton, then this belongs to parent, tail is nil
(corresponding to case where we don't have to deal with further descendents*)

(*
fun pathsplits' :: "'a list \<Rightarrow> 'a list \<Rightarrow> ('a list * 'a list) list" where
"pathsplits' [] = []"
| "pathsplits' [h] = [([h], [])]"
| "pathsplits' (h#t) = 
   ((h#t), [])"
*)
fun tails :: "'a list \<Rightarrow> 'a list list" where
"tails [] = []"
| "tails (h#t) = ((h#t)#(tails t))"

value "tails ([1, 2, 3, 4] :: nat list)"

(*

cases for final correctness theorem

OVERALL thing that needs to be improved here:
how to deal with scanning cases where the scanning depth is > 0?
- idea: this will cause a jump into one of the passed-in continuations (?)
  - No - it has the same semantics as a jump to the PC stored at a higher level descendent
  - That is how we need to approach this.

I. node case

  1. Node is root
    A. Then non scanning semantics are same as compiling and starting pc=0
    B. Then scanning semantics are the same as setting pc = get_label (seq)
        - Scan depth will cannot be greater than 0
        - Or, are (\<lambda> _ . None) in the case that label is nil
    C. Continuation list has to be empty
      (Does "after" continuation need to be Some? - no, I don't think so)

  2. Node is a descendent
    A. passed in continuations have to match
       
       a. Final continuation must be same as root final continuation (?)
       b. We need to follow the descendents path, and ensure that
          each continuation either corresponds to (\<lambda> _ . None)
          or to result of jumping to the PC value embedded at that Seq
            - OR - can we get away with saying each continuation is result of calling
              ll_sem in scanning mode on that Seq node - I think we may need to do this
              actually, otherwise there will be more proof burden (?)
            - what is a compact way to state this?

      More ideas on how to state this:
        - Do we need to state this for all descendents, or just the relevant ones?
        - that is, 


     B. Then non scanning semantics are the same as compiling full program,
        and starting at pc = Seq's addr
      
     C. Scanning smeantics are the same as setting pc = address stored at
        Seq's label (or None, if there is none)
      - Or, if scan depth greater than 0, same as setting pc = get_label (ancestor)
        - Should we keep an explicit list of ancestors as we go?

II. list case

(do we need it? i have a feeling we do)


*)

(*

One big question that arises from the above.
In our assumptions about the ancestors, do we actually need to specify the semantics of each one
or do we get to assume that their semantics is the correct semantic of the jump we want?
It feels like that may be assuming too much.

Actually, maybe not! After all, we should be able to prove the "higher up" case of jumps
(e.g. jumps to the root's dest) without any arguments about parameters

How does the "scanning" case look in this case?

*)

(*

ll_valid3' t \<longrightarrow>
ll4_validate_jump_targets l t \<longrightarrow>
(* want ll'_sem here - need to access continuation list *)
ll'_sem t elle_denote elle_jmpd n None c st = Some st'' \<longrightarrow>
program_sem (\<lambda> _ . ())
            (fst st) n (snd st) = ProgramReturn (st') \<and>
  c st = st''
*)

(* gather all of the sequence nodes traversed along the way *)
(* is LL get node the best way here? *)
fun followcp:: "('a, 'b, 'c, 'd, 'e, 'f, 'g) ll \<Rightarrow> childpath \<Rightarrow>
               ('a, 'b, 'c, 'd, 'e, 'f, 'g) ll list option" where
"followcp _ [] = None"
| "followcp t [_] = Some [t]" (* ignore last child *)
| "followcp t (ch#ct) =
   (case ll_get_node t [ch] of
    None \<Rightarrow> None
    | Some t' \<Rightarrow> 
      (case followcp t' ct of 
       None \<Rightarrow> None
       | Some l' \<Rightarrow> Some (t'#l')))"

(* take in cont as an explicit parameter? 
this actually seems pretty annoying, do we also need to reproduce the
after-continuation?
it may actually always be the same?
yeah, i don't think we ever change the continuation in the recursive calls
we are doing for the scope
*)
(*
check to make sure n is greater than 0
if it is not, we'll need to do "const none"
question though - when do we "cut off" continuations?
*)
fun generate_conts ::
"('a, 'b, 'c, 'd, 'e, 'f, 'g) ll \<Rightarrow> childpath \<Rightarrow> nat \<Rightarrow>
     (ellest \<Rightarrow> ellest option) list \<Rightarrow> 
     (ellest \<Rightarrow> ellest option) \<Rightarrow>
     ((ellest \<Rightarrow> ellest option) list) option" where

"generate_conts t [] _ _ _ = None"

(* should this case be (n-1)? *)
| "generate_conts t [_] n scopes cont =
   Some ((ll'_sem t elle_denote elle_jmpd (n-1) (Some 0) scopes cont)#scopes)"

| "generate_conts t (ch#ct) n scopes cont =
   (case ll_get_node t [ch] of
    None \<Rightarrow> None
    | Some t' \<Rightarrow> generate_conts t' ct (n - 1 - ch) 
        ((ll'_sem t elle_denote elle_jmpd (n-1) (Some 0) scopes cont)#scopes) cont)"

(* we need to do something slightly more elaborate
when calculating the list of continuations.

at root, the continuation list is empty

at each step, we construct the following new continuation:
- call ourselves on the current node, with 1 less fuel
- use the continuation list generated from the last iteration

so, this is a paramorphism that also needs an additional index parameter
(the index parameter allows us to track fuel)

also, we can precisely calculate the elle-fuel parameter
in particular, fuel decrements when passing through a seq node
as well as 1 per child.

so, when following a childpath to construct a continuation list,
we should be able to reproduce the fuel exactly.
 *)

(*

Another key point. We need to deal with deeper scannings.
What does it mean for a (descendent) to be scanned at a 
deeper level?

- First, the depth of the scanning (beyond 0) must be equal to the length of the 
childpath of the descend relation
- will have the effect of setting the PC to the root's label

*)

(*

What about the "ll_list_sem" second half of this case?
I think we can just restate the first case in terms of
"LSeq e ls", hopefully that will suffice.

hmm, or do we need to do something more?
i think we need to say something like

1. if we are the root, then our scanning and non-scanning semantics are as expected
   (this case should look very similar to first case - I don't think we need a prefix)
2. if prefix@list is descended from the root, then
   we need cases based on where the label is.
   (idea: either we have already found the label, and so we
   call on the suffix in non-scanning mode
   or, we didn't find the label yet)
    - if "gather_labels" applied to prefix is True, then
      scanning on suffix should result in None
    - otherwise, "gather_labels" applied to suffix is True
      and scanning on suffix will have semantics of a jump to that
      label (similar to first case)

*)

fun setpc :: "ellest \<Rightarrow> nat \<Rightarrow> ellest" where
"setpc (e, e2, e3) n =
  ((e \<lparr> vctx_pc := (int n) \<rparr>)
  , e2
  , e3)"

fun clearprog :: "ellest \<Rightarrow> ellest" where
"clearprog (e1, e, e3) =
  (e1
  , (e \<lparr> cctx_program := empty_program \<rparr>)
  , e3)"

(* throw away program and pc *)
definition elleq :: "ellest \<Rightarrow> ellest \<Rightarrow> bool" where
"elleq a b = (setpc (clearprog a) 0 = setpc (clearprog b) 0)"

(* new pipeline *)

definition ellecompile_untrusted :: "ll1 \<Rightarrow> ll4 option" where
"ellecompile_untrusted l =
(case (ll3_assign_label (ll3_init (ll_pass1 l))) of
  Some l' \<Rightarrow> (case process_jumps_loop (get_process_jumps_fuel l') l' of
              Some l'' \<Rightarrow> (case write_jump_targets [] (ll4_init l'') of
                           Some l''' \<Rightarrow> Some l''')))"

(* blargh, we need to change the type of check_ll3... *)
(*
definition ellecompile :: "ll1 \<Rightarrow> program option" where
"ellecompile l =
(case ellecompile_untrusted l of
    Some l' \<Rightarrow>
    (* check ll3 valid *)
    (if check_ll3 l' then
      (if ll4_validate_jump_targets [] l' then
      (prog_init_cctx (codegen l'))
      else None)
    else None)
    | _ \<Rightarrow> None)"
*)

(* need a function for dumping an ll4 to a program *)
(* definition ll4_dump : "ll4 \<Rightarrow>  " *)

(* wrap program sem to take in an ellest' *)
fun my_program_sem :: "ellest \<Rightarrow> nat \<Rightarrow> ellest" where
"my_program_sem (vc, cc, net) n =
  (Evm.program_sem
    (\<lambda> _ . ())
    c n net
    (InstructionContinue vc))"

(* need to use program_sem, unpacking the thing *)

(* use valid3 induction principle? *)
lemma elle_correct :
"
t \<in> ll_valid3' \<longrightarrow>
validate_jump_targets [] t \<longrightarrow>
(
((! n st st'1 . ll'_sem n [] t None st = Some st'1 \<longrightarrow>
  (? st'2 . elleq st'1 st'2 \<and> vm_sem (dump t) (setpc st 0) = st'2))
 \<and>
 (ll'_sem n [] t (Some 0) st = Some st'1 \<longrightarrow>
    (? st'2 . elleq st'1 st'2 \<and> vm_sem (dump t) = st2)
    (t = LSeq lab ls \<and> 
      (? a . get_label t lab = Some a \<and> 
      evm_sem (dump t) (setpc st a) = st')))))
\<and>
((t, t', k) \<in> ll'_descend) \<longrightarrow>
  followcp t k = Some lt \<longrightarrow>
  ll'_sem n [] None st = Some st' \<longrightarrow>
  evm_sem (
)
"
    

end

