theory Gensym_Descend_Facts imports Gensym_Descend
begin


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
end