theory Gensym_Descend_Facts imports Gensym_Descend
begin

(*
lemma gensym_get_len [rule_format] :
"(! kh kt t' . gensym_get_list ts (kh#kt) = Some t' \<longrightarrow>
 kh < length ts)"
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
*)
lemma gensym_get_list_len  :
  fixes ts :: "('b, 'r, 'g) gensym list" 
  shows "\<And> kh kt t' . gensym_get_list ts (kh#kt) = Some t' \<Longrightarrow>
          kh < length ts"
proof(induction ts ) 
case Nil
then show ?case by auto
  next
  case (Cons th tt)
  then show ?case
    proof(cases kh)
    case 0
    then show ?thesis by auto
    next
      case (Suc n)
      then show ?thesis using Cons
        apply(auto)
        done
    qed 
  qed


lemma gensym_get_list_len' :
  assumes H:  "gensym_get_list ts (kh#kt) = Some t'"
  shows "kh < length (ts)" using H
proof(induct ts arbitrary:kh)
case Nil
    then show ?case by auto  next
case (Cons a ts)
    then show ?case
    proof(cases kh)
      case 0 then show ?thesis by auto  next
      case (Suc nat) then show ?thesis using Cons by auto
    qed
qed
    


lemma gensym_get_list_nth :
  shows "gensym_get_list ts [kh] = Some t' \<Longrightarrow>
          ts ! kh = t'"
proof(induction ts arbitrary:kh) 
  case Nil
then show ?case by auto
next
  case (Cons a ts)
  then show ?case
  proof(cases kh)
    case 0 then show ?thesis using Cons by auto next
    case (Suc nat) then show ?thesis using Cons by auto
  qed
qed

lemma gensym_get_list_nth2 :
  shows "kh < length ts \<Longrightarrow>
         ts ! kh = t' \<Longrightarrow>
         gensym_get_list ts [kh] = Some t'"
proof(induction ts arbitrary:kh)
  case Nil
  then show ?case by auto
next
  case (Cons a ts)
  then show ?case 
  proof(cases kh)
    case 0
    then show ?thesis using Cons by auto
  next
    case (Suc nat)
    then show ?thesis using Cons by auto 
  qed
qed

lemma gensym_get_list_child  :
  assumes H:  "gensym_get_list ts (kh#kt) = Some t'"
  shows (*glc_C1 :*) "kh < length ts" 
  and (*glc_C2:*) "gensym_get (ts ! kh) kt = Some t'"
  using H
proof(induction ts arbitrary:kh)
  case Nil 
  {    
  case 1 then show ?case  by auto
  next case 2
  then show ?case by auto
  }
  case (Cons a ts)
  {
    case 1 then show ?case
    proof(cases kh)
      case 0 thus ?thesis by auto next
      case (Suc n) thus ?thesis using Cons 1 by auto
    qed

    case 2 then show ?case
    proof(cases kh)
      case 0 thus ?thesis using Cons 2 by auto next
      case (Suc n) thus ?thesis using Cons 2 by auto
    qed
  }
qed

(* need converse of previous lemma, to prove last-child lemma *)
lemma gensym_get_list_child2 :
  assumes Hg: "gensym_get t kt = Some t'"
  and Hl: "kh < length ts"
  and Hc: "ts ! kh = t"
shows
    "gensym_get_list ts (kh#kt) = Some t'" using Hg Hl Hc
proof(induction ts arbitrary:kh) 
case Nil then show ?case by auto
next
  case (Cons a ts)
  then show ?case
  proof(cases kh)
    case 0
    then show ?thesis using Cons by auto
  next
    case (Suc nat)
    then show ?thesis using Cons by auto
  qed
qed

(* need to constrain t'1. need exists *)
lemma gensym_get_child :
  assumes H: "gensym_get t (kh#kt) = Some t'"
  shows  "\<exists> t'1 . gensym_get t [kh] = Some t'1 \<and>
            gensym_get t'1 kt = Some t'" using H
proof(cases t)
  case (GBase x11 x12)
  thus ?thesis using H by auto next
  case (GRec a1 a2 l)
  thus ?thesis using H gensym_get_list_child gensym_get_list_nth2
    by auto blast+
qed

lemma gensym_get_child2 :
  assumes H1 : "gensym_get t [kh] = Some t'1"
  and H2 : "gensym_get t'1 kt = Some t'"
  shows  "gensym_get t (kh#kt) = Some t'" using H1 H2
proof(cases t)
  case (GBase x11 x12)
  thus ?thesis using H1 H2 by auto next
  case (GRec a1 a2 l)
  thus ?thesis using H1 H2 gensym_get_list_child2[of t'1 kt t']
                           gensym_get_list_len[of l kh "[]" t'1]
                           gensym_get_list_nth[of l kh t'1] by auto
qed

lemma gensym_get_last :
  assumes H: "gensym_get t (k@[kl]) = Some t''"
  shows "\<exists> t' . (gensym_get t k = Some (t' :: ('a, 'b, 'c) gensym) \<and>
         gensym_get t' [kl] = Some t'')"  using H
proof(induction k arbitrary: t kl t'')
  case Nil then show ?case by auto next
  case (Cons a k) then show ?case
  proof(cases t)
    case (GBase x11 x12)
    then show ?thesis using Cons by auto
  next
    case (GRec a1 a2 l)
    hence 0: "gensym_get (l ! a) (k@[kl]) = Some t''" using Cons gensym_get_list_child GRec by auto
    hence 1: "\<exists> t' .  gensym_get (l ! a) k = Some t' \<and> gensym_get t' [kl] = Some t''" using Cons by auto
    hence 2: "a < length l" using Cons GRec gensym_get_list_len by auto
    thus ?thesis using GRec gensym_get_list_nth2 gensym_get_list_child2 0 1 by auto blast+
  qed
qed

lemma gensym_get_last2 :
  assumes H1: "gensym_get t k = Some t'"
  and H2: "gensym_get t' [kl] = Some t''"
shows "gensym_get t (k@[kl]) = Some t''"  using H1 H2
proof(induction k arbitrary: t t' kl t'')
  case Nil
  then show ?case by auto next

  case (Cons a k)
  then show ?case
  proof(cases t)
    case (GBase x11 x12)
    then show ?thesis using Cons by auto
  next
    case (GRec a1 a2 l)
    hence 0: "gensym_get (l!a) (k) = Some t'" using Cons gensym_get_list_child GRec by auto
    hence 1: "gensym_get (l!a) (k@[kl]) = Some t''" using Cons by auto
    hence 2: "a < length l" using Cons GRec gensym_get_list_len by auto
    show ?thesis using GRec gensym_get_list_child2 0 1 2 by auto blast+
  qed
qed

lemma gensym_get_comp :
  assumes H1: "gensym_get t' p' = Some t''"
  assumes H2: "gensym_get t p = Some t'"
  shows "gensym_get t (p@p') = Some t''" using H1 H2
proof(induction p' arbitrary: t' t'' t p)
  case Nil
  then show ?case by auto
next
  case (Cons a' p')
  then show ?case
  proof(cases t') 
    case (GBase x11 x12) thus ?thesis using Cons H1 H2
    proof(cases p)
      assume Nil' :"p=[]"
      show ?thesis using GBase Cons Nil' by auto next

      fix a list
      assume Cons' :"p=a#list"
      show ?thesis using GBase Cons Cons' by auto next
    qed next

    case (GRec a1 a2 l)
    obtain tmid where 1: "gensym_get t' [a'] = Some tmid \<and>
                 gensym_get tmid p' = Some t''" using Cons gensym_get_child by blast
    hence 2: "gensym_get t (p @ [a']) = Some tmid" using Cons gensym_get_last2 by blast
    hence 3: "gensym_get t ((p @ [a']) @ p') = Some t''" 
        using Cons.IH[of tmid t'' t "p@[a']"] 1
        by auto
      show ?thesis using 3 by auto
    qed
  qed

lemma gensym_get_comp2 :
  assumes H: "gensym_get t (p1@p2) = Some t''"
  shows  "\<exists> t' . gensym_get t p1 = Some t' \<and>
                 gensym_get t' p2 = Some t''" using H
proof(induction p2 arbitrary: t p1 t'')
  case Nil
  then show ?case by auto
next
  case (Cons a k2t)
  hence 1: "gensym_get t ((p1 @ [a])@k2t) = Some t''" by auto
  obtain t' where 2: "gensym_get t (p1@[a]) = Some t' \<and>
                        gensym_get t' k2t =
                        Some t''" using 1 Cons.IH[of t "p1@[a]" t''] by auto
  obtain t'2 where 3: "gensym_get t p1 = Some t'2 \<and>
                        gensym_get t'2 [a] = Some t'"
    using 2 gensym_get_last[of t p1 a t'] by auto
  show ?case using 2 3 gensym_get_child2 by auto blast+
qed

(* now we need to show compatibility with the inductive one *)
lemma gensym_descend_eq_l2r :
  assumes H: "gensym_get t (kh#kt) = Some t'"
  shows "gensym_descend t t'(kh#kt)" using H
proof(induction kt arbitrary: t kh t')
  case Nil
  then show ?case
  proof(cases t)
    case (GBase x11 x12)
    then show ?thesis 
      using Nil by auto
  next
    case (GRec x21 x22 l)
    then show ?thesis using Nil gensym_descend.intros(1)[of kh l]
              gensym_get_list_child[of l kh "[]" t'] by auto
  qed
next
  case (Cons a kt)
  then show ?case
  (* why do we need the rule here? *)
  proof(cases t rule:gensym.exhaust)
    case (GBase x11 x12)
    then show ?thesis using Cons by auto
  next
    case (GRec x21 x22 l)
    obtain tmid where 1 : "gensym_get t [kh] = Some tmid \<and> gensym_get tmid (a#kt) = Some t'"
      using gensym_get_child[of t kh "a#kt" t'] Cons by auto
    have 2 : "gensym_descend tmid t' (a#kt)" using Cons 1 by auto
    have 3: "gensym_descend t tmid [kh]" using 1 GRec gensym_descend.intros(1)[of kh l]
                                    gensym_get_list_child[of l kh "[]" tmid]
      by auto
    thus ?thesis using 2 gensym_descend.intros(2) by fastforce
  qed
qed

lemma ll3_descend_nonnil :
assumes H: "gensym_descend t t' k"
shows "\<exists> hd tl . k = hd # tl" using H
proof(induction rule:gensym_descend.induct)
  case 1 thus ?case by auto next
  case 2 thus ?case by auto
qed

lemma ll_descend_eq_r2l :
"gensym_descend t t' k \<Longrightarrow>
gensym_get t k = Some t'"
proof(induction rule:gensym_descend.induct)
  case (1 c q e ls t)
  then show ?case using gensym_get_list_nth2 by auto next
  case (2 t t' n t'' n')
  then show ?case using gensym_get_comp by fastforce
qed

lemma cp_next_nonnil' :
  shows (*C1 :*) "\<And> cp cp' . cp_next (t :: ('b, 'r, 'g) gensym) cp = Some cp' \<longrightarrow>
    (? cph' cpt' . cp' = cph' # cpt')"
  and (*C2 :*) "\<And> cp cp' . cp_next_list (l :: ('b, 'r, 'g) gensym list) cp = Some cp' \<longrightarrow>
    (? cph' cpt' . cp' = cph' # cpt')"
proof(induction t and l rule:gensym_induct)
case (1 g b)
  then show ?case
  proof(cases cp)
    case Nil then show ?thesis by auto next
    case (Cons a list) then show ?thesis by auto next
  qed
next

  case (2 g r l)
  then show ?case 
  proof(cases l)
    case Nil then show ?thesis by auto next
    case (Cons t list)
    then show ?thesis
    proof(cases cp)
      assume Nil': "cp = []"
      then show ?thesis using Cons by auto next

      fix a lista
      assume Cons' : "cp = a#lista"
      then show ?thesis using Cons 2 by auto next
    qed next
  qed next

  case (3) thus ?case by auto next

  case (4 t l)
  thus ?case
  proof(cases cp)
    case Nil
    then show ?thesis by auto next

    case (Cons a list)
    then show ?thesis using 4
    proof(cases a)
      case 0 then show ?thesis
      proof(cases l)
        assume Nil' : "l=[]"
        then show ?thesis
        proof(cases "cp_next t list")
          case None
          then show ?thesis using Nil' Cons 4 0 by auto
        next
          case (Some cpn)
          then show ?thesis using Nil' Cons 4 0 by auto
        qed next

        fix lh ll
        assume Cons' : "l = lh#ll"
        then show ?thesis
        proof(cases "cp_next t list")
          case None
          then show ?thesis using Cons' Cons 4 0 by auto
        next
          case (Some cpn)
          then show ?thesis using Cons Cons' 4 0 by auto
        qed
      qed next

      case (Suc nat)
      then show ?thesis
        proof(cases l)
          assume Nil' : "l=[]"
          then show ?thesis using Cons Suc 4 by auto
        next
          fix lh ll
          assume Cons' : "l=lh#ll"
          then show ?thesis using Cons Suc 4 
          proof(cases "cp_next_list (lh # ll) (nat # list)")
            case None
            then show ?thesis using Cons Cons' Suc 4 by auto
          next
            case (Some cpn)
            then show ?thesis
            proof(cases cpn)
              assume Nil'' : "cpn=[]"
              then show ?thesis using Cons Cons' Suc 4 Some by auto
            next
              fix cpnh cpnt
              assume Cons'' : "cpn=cpnh#cpnt"
              then show ?thesis using Cons Cons' Suc 4 Some by auto
            qed
          qed
        qed
      qed next
    qed next
  qed

end