theory Gensyn_Facts imports Gensyn Gensyn_Descend
begin

lemma gensyn_get_list_child :
  assumes H : "gensyn_get_list l [n] = Some t"
  shows "l ! n = t" using H
proof(induction l arbitrary: n t)
  case Nil
  then show ?case by auto
next
  case (Cons lh lt)
  then show ?case
  proof(cases n)
    case 0
    then show ?thesis using Cons by auto
  next
    case (Suc n')
    then show ?thesis using Cons by(auto)
  qed
qed

lemma gensyn_get_list_child_length :
  assumes H : "gensyn_get_list l [n] = Some t"
  shows "n < length l" using H
proof(induction l arbitrary: n)
  case Nil
  then show ?case by auto
next
  case (Cons lh lt)
  then show ?case
  proof(cases n)
    case 0
    then show ?thesis using Cons by auto
  next
    case (Suc n')
    then show ?thesis using Cons by(auto)
  qed
qed

lemma gensyn_get_list_child' :
  assumes H : "l ! n = t"
  assumes Hl : "n < length l"
  shows "gensyn_get_list l [n] = Some t" using H Hl
proof(induction l arbitrary: n t)
  case Nil
  then show ?case by(auto)
next
  case (Cons lh lt)
  then show ?case
  proof(cases n)
    case 0
    then show ?thesis using Cons by auto
  next
    case (Suc n')
    then show ?thesis using Cons by(auto)
  qed
qed

lemma gensyn_get_list_child_None :
  assumes H : "gensyn_get_list l [n] = None"
  shows "length l \<le> n" using H
proof(induction l arbitrary: n)
  case Nil
  then show ?case by auto
next
  case (Cons lh lt)
  then show ?case
  proof(cases n)
    case 0
    then show ?thesis using Cons by auto
  next
    case (Suc n')
    then show ?thesis using Cons by(auto)
  qed
qed

lemma gensyn_get_list_child_None' :
  assumes Hl : "length l \<le> n"
  shows "gensyn_get_list l [n] = None" using Hl
proof(induction l arbitrary: n)
  case Nil
  then show ?case by(auto)
next
  case (Cons lh lt)
  then show ?case
  proof(cases n)
    case 0
    then show ?thesis using Cons by auto
  next
    case (Suc n')
    then show ?thesis using Cons by(auto)
  qed
qed


(*
lemma gensyn_descend_correct1 :
  assumes H : "gensyn_descend t t' cp"
  shows "gensyn_get t cp = Some t'" using H
proof(induction rule: gensyn_descend.induct)
  case (1 c ls t x)
  then show ?case apply(auto)
next
  case (2 t t' l t'' l')
  then show ?case sorry
qed
*)

lemma gensyn_get_list_comp :
  assumes H1 : "gensyn_get_list l1 cp1 = Some (G x1 l2)"
  assumes H2 : "gensyn_get_list l2 cp2 = Some t3"
  shows "gensyn_get_list l1 (cp1@cp2) = Some t3" using assms
proof(induction l1 arbitrary: cp1 x1 l2 cp2 t3 rule: gensyn_induct')
  case (1 x l)
  then show ?case
  proof(cases cp1)
    case Nil
    then show ?thesis using 1 by auto
  next
    case (Cons cp1h cp1t)
    then show ?thesis using 1
    proof(cases cp1h)
      case 0
      show ?thesis
      proof(cases cp1t)
        case Nil' : Nil
        then show ?thesis using 1 Cons 0 
        proof(cases cp2)
          case Nil'' : Nil
          then show ?thesis using 1 Cons 0 Nil'
            by(cases l2; auto)
        next
          case Cons'' : (Cons cp2h cp3t)
          then show ?thesis using 1 Cons 0 Nil'
            by(auto)
        qed
      next
        case Cons' : (Cons cp1th cp1tt)
        then show ?thesis using "1.prems" "1.IH"[of cp1t] Cons 0
          by(auto)
      qed
    next
      case (Suc nat)
      then show ?thesis using 1 Cons
        by(auto)
    qed
  qed
next
  case 2
  then show ?case by auto
next
  case (3 t l)
  then show ?case 
  proof(cases cp1)
    case Nil
    then show ?thesis using 3 by auto
  next
    case (Cons cp1h cp1t)
    then show ?thesis 
    proof(cases cp1h)
      case 0
      show ?thesis
      proof(cases cp1t)
        case Nil' : Nil
        then show ?thesis using 3 Cons 0 
        proof(cases cp2)
          case Nil'' : Nil
          then show ?thesis using 3 Cons 0 Nil'
            by(cases l2; auto)
        next
          case Cons'' : (Cons cp2h cp3t)
          then show ?thesis using 3 Cons 0 Nil'
            by(auto)
        qed
      next
        case Cons' : (Cons cp1th cp1tt)

        obtain tx tl where T : "t = G tx tl" by(cases t; auto)

        then show ?thesis using "3.prems" "3.IH"(1)[of "cp1"] Cons 0 Cons'
          by(auto)
      qed
    next
      case (Suc cp1h')
      then show ?thesis using "3.prems" "3.IH"(2)[of "cp1h'#cp1t"] Cons
        by(auto)
    qed
  qed
qed

lemma gensyn_get_comp :
  assumes H1 : "gensyn_get t1 cp1 = Some t2"
  assumes H2 : "gensyn_get t2 cp2 = Some t3"
  shows "gensyn_get t1 (cp1@cp2) = Some t3" using assms
proof(cases cp1)
  case Nil
  then show ?thesis using H1 H2 by auto
next
  case (Cons cp1h cp1t)

  show ?thesis
  proof(cases cp2)
    case Nil' : Nil

    then show ?thesis using H1 H2 by auto
  next
    case Cons' : (Cons cp2h cp2t)

    obtain x1 l1 where T1 : "t1 = G x1 l1"
      by(cases t1; auto)
  
    obtain x2 l2 where T2 : "t2 = G x2 l2"
      by(cases t2; auto)
  
    have H1' : "gensyn_get_list l1 cp1 = Some (G x2 l2)"
      using T1 T2 H1 Cons
      by(auto)
  
    have H2' : "gensyn_get_list l2 cp2 = Some t3"
      using T2 H2 Cons'
      by(auto)

    show ?thesis using gensyn_get_list_comp[OF H1' H2'] Cons T1
      by(auto)
  qed
qed

lemma gensyn_get_list_comp_None :
  assumes H1 : "gensyn_get_list l1 cp1 = Some (G x1 l2)"
  assumes H2 : "gensyn_get_list l2 (cph2#cpt2) = None"
  shows "gensyn_get_list l1 (cp1@cph2#cpt2) = None" using assms
proof(induction l1 arbitrary: cp1 x1 l2 cph2 cpt2 rule: gensyn_induct')
  case (1 x l)
  then show ?case
  proof(cases cp1)
    case Nil
    then show ?thesis using 1 by auto
  next
    case (Cons cp1h cp1t)
    then show ?thesis using 1
    proof(cases cp1h)
      case 0
      show ?thesis
      proof(cases cp1t)
        case Nil' : Nil
        then show ?thesis using 1 Cons 0 by(auto)
      next
        case Cons' : (Cons cp1th cp1tt)
        then show ?thesis using "1.prems" "1.IH"[of cp1t] Cons 0
          by(auto)
      qed
    next
      case (Suc nat)
      then show ?thesis using 1 Cons
        by(auto)
    qed
  qed
next
  case 2
  then show ?case by auto
next
  case (3 t l)
  then show ?case 
  proof(cases cp1)
    case Nil
    then show ?thesis using 3 by auto
  next
    case (Cons cp1h cp1t)
    then show ?thesis 
    proof(cases cp1h)
      case 0
      show ?thesis
      proof(cases cp1t)
        case Nil' : Nil
        then show ?thesis using 3 Cons 0 by auto
      next
        case Cons' : (Cons cp1th cp1tt)

        obtain tx tl where T : "t = G tx tl" by(cases t; auto)

        then show ?thesis using "3.prems" "3.IH"(1)[of "cp1"] Cons 0 Cons'
          by(auto)
      qed
    next
      case (Suc cp1h')
      then show ?thesis using "3.prems" "3.IH"(2)[of "cp1h'#cp1t"] Cons
        by(auto)
    qed
  qed
qed

lemma gensyn_get_comp_None :
  assumes H1 : "gensyn_get t1 cp1 = Some t2"
  assumes H2 : "gensyn_get t2 cp2 = None"
  shows "gensyn_get t1 (cp1@cp2) = None" using assms
proof(cases cp1)
  case Nil
  then show ?thesis using H1 H2 by auto
next
  case (Cons cp1h cp1t)

  obtain x1 l1 where T1 : "t1 = G x1 l1"
    by(cases t1; auto)

  obtain x2 l2 where T2 : "t2 = G x2 l2"
    by(cases t2; auto)

  have H1' : "gensyn_get_list l1 cp1 = Some (G x2 l2)"
    using T1 T2 H1 Cons
    by(auto)

  show ?thesis
  proof(cases cp2)
    case Nil' : Nil
    then show ?thesis using Cons H2 by auto
  next
    case Cons' : (Cons cph2 cpt2)
  
    have H2' : "gensyn_get_list l2 (cph2#cpt2) = None"
      using T2 H2 Cons'
      by(auto)

    show ?thesis using gensyn_get_list_comp_None[OF H1' H2'] Cons T1 Cons'
      by(auto)
  qed
qed

lemma gensyn_get_list_nonnil :
  assumes H : "gensyn_get_list l cp = Some t"
  shows "cp \<noteq> []" using H
  by(cases cp; cases l; auto)

lemma gensyn_get_list_split :
  assumes H1 : "gensyn_get_list l1 (cph1#cpt1@cph2#cpt2) = Some t3"
  shows "\<exists> x2 l2 . gensyn_get_list l1 (cph1#cpt1) = Some (G x2 l2) \<and> 
                gensyn_get_list l2 (cph2#cpt2) = Some t3" using assms
proof(induction l1 arbitrary: cph1 cpt1 cph2 cpt2 t3 rule: gensyn_induct')
  case (1 x l)
  then show ?case
  proof(cases cph1)
    case 0
    show ?thesis
    proof(cases cpt1)
      case Nil
      then show ?thesis using 1 Cons 0 by(auto)
    next
      case (Cons cp1th cp1tt)
      then show ?thesis using "1.prems" "1.IH" 0
        by(auto)
    qed
  next
    case (Suc nat)
    then show ?thesis using 1 Cons
      by(auto)
  qed
next
  case 2
  then show ?case by auto
next
  case (3 t l)
  then show ?case  
  proof(cases cph1)
    case 0

    obtain tx tl where T : "t = G tx tl" by(cases t; auto)

    show ?thesis
    proof(cases cpt1)
      case Nil : Nil
      then show ?thesis using 3 0 T by(auto)
    next
      case Cons : (Cons cp1th cp1tt)

      then show ?thesis using "3.prems" "3.IH"(1)[of cph1 "cp1th#cp1tt"] Cons 0 T
        by(auto)
    qed
  next
    case (Suc cp1h')
    then show ?thesis using "3.prems" "3.IH"(2)[of "cp1h'" cpt1 cph2 cpt2] Cons
      by(auto)
  qed
qed

lemma gensyn_get_split :
  assumes H1 : "gensyn_get t1 (cp1@cp2) = Some t3"
  shows "\<exists> t2 . gensyn_get t1 (cp1) = Some t2 \<and> 
                gensyn_get t2 (cp2) = Some t3" using assms
proof(cases cp1)
  case Nil

  have Desc1 : "gensyn_get t1 cp1 = Some t1" using Nil by auto

  have Desc2 : "gensyn_get t1 cp2 = Some t3" using Nil H1
    by auto

  then show ?thesis using Desc1 Desc2 by blast
next
  case (Cons cph1 cpt1)
  then show ?thesis 

  proof(cases cp2)
    case Nil' : Nil

    have Desc1 : "gensyn_get t1 cp1 = Some t3" using Nil' H1 by auto
  
    have Desc2 : "gensyn_get t3 cp2 = Some t3" using Nil'
      by auto
  
    then show ?thesis using Desc1 Desc2 by blast
  next
    case Cons' : (Cons cph2 cpt2)

    obtain xt lt where T1 : "t1 = G xt lt" by(cases t1; auto)

    then show ?thesis using gensyn_get_list_split[of lt cph1 cpt1 cph2 cpt2 t3]
      H1 Cons Cons' T1
      by(auto)
  qed
qed

lemma gensyn_get_list_split_None :
  assumes H1 : "gensyn_get_list l1 (cp1 @ (cph2#cpt2)) = None"
  assumes H2 : "gensyn_get_list l1 cp1 = Some (G x2 l2)"
  shows "gensyn_get_list l2 (cph2#cpt2) = None"  using H1 H2
proof(induction l1 arbitrary:  cp1 cph2 cpt2 x2 l2 rule: gensyn_induct')
  case (1 x l)
  then show ?case
  proof(cases cp1)
    case Nil
    then show ?thesis using 1 by auto
  next
    case (Cons cph1 cpt1)

    then show ?thesis
    proof(cases cph1)

      case 0
      show ?thesis

      proof(cases cpt1)
        case Nil' : Nil
        then show ?thesis using 1 Cons 0 by(auto)
      next
        case Cons' : (Cons cpt1h cpt1t)
        then show ?thesis using "1.prems" "1.IH"[of "cpt1h # cpt1t"] Cons 0
          by(auto)
      qed
    next
      case (Suc nat)
      then show ?thesis using 1 Cons
        by(auto)
    qed
  qed
next
  case 2
  then show ?case by auto
next
  case (3 t l)
  then show ?case  

  proof(cases cp1)
    case Nil
    then show ?thesis using 3 by auto
  next
    case (Cons cph1 cpt1)
    then show ?thesis 
  
    proof(cases cph1)
      case 0
  
      obtain tx tl where T : "t = G tx tl" by(cases t; auto)
  
      show ?thesis
      proof(cases cpt1)
        case Nil : Nil
        then show ?thesis using 3 0 Cons T by(auto)
      next
        case Cons' : (Cons cpt1h cpt1t)
  
        then show ?thesis using "3.prems" "3.IH"(1)[of "0#cpt1h#cpt1t" cph2 cpt2] Cons 0 T
          by(auto)
      qed
    next
      case (Suc cp1h')
      then show ?thesis using "3.prems" "3.IH"(2)[of "cp1h'#cpt1" cph2 cpt2] Cons
        by(auto)
    qed
  qed
qed


lemma gensyn_get_split_None :
  assumes H1 : "gensyn_get t1 (cp1 @ cp2) = None"
  assumes H2 : "gensyn_get t1 cp1 = Some t2"
  shows "gensyn_get t2 cp2 = None"  using H1 H2
proof(cases cp2)
  case Nil
  then show ?thesis using H1 H2 by auto
next
  case (Cons cph2 cpt2)

  obtain tx1 tl1 where T1 : "t1 = G tx1 tl1" by(cases t1; auto)
  obtain tx2 tl2 where T2 : "t2 = G tx2 tl2" by(cases t2; auto)

  then show ?thesis 
    using gensyn_get_list_split_None[of tl1 cp1 cph2 cpt2] H1 H2 Cons T1 T2
    by(cases cp1; auto)
qed

lemma gensyn_descend_correct1 :
  assumes H : "gensyn_descend t t' cp"
  shows "gensyn_get t cp = Some t'" using H
proof(induction rule: gensyn_descend.induct)
  case (1 c ls t x)
  show ?case
  proof(cases ls)
    case Nil
    then show ?thesis using 1 by auto
  next
    case (Cons lh lt)
    then show ?thesis using 1 gensyn_get_list_child'[of "ls" c]
      by(auto)
  qed
next
  case (2 t t' l t'' l')

  obtain t'x t'l where T' : "t' = G t'x t'l" by(cases t'; auto)

  then show ?case using 2 gensyn_get_comp[of t l t' l' t'']
    by(auto)
qed

lemma gensyn_descend_nonnil :
  assumes H : "gensyn_descend t t' cp"
  shows "cp \<noteq> []" using H
proof(induction rule: gensyn_descend.induct)
  case (1 c ls t x)
  then show ?case by auto
next
  case (2 t t' l t'' l')
  then show ?case by auto
qed

lemma gensyn_descend_nonempty :
  assumes H : "gensyn_descend t t' cp"
  assumes H' : "t = G xt lt"
  shows "lt \<noteq> []" using assms
proof(induction arbitrary: t' cp xt lt rule: gensyn_descend.induct)
  case (1 c ls t x)
  then show ?case by(cases lt; auto)
next
  case (2 tc tc' lc tc'' lc')
  show ?case using "2.IH"[of xt lt] "2.prems"  
    by auto
qed


lemma gensyn_descend_child_zero :
  assumes H : "gensyn_descend t t' cp"
  assumes Hcp : "cp = 0#cp'"
  assumes Ht : "t = (G xr l1)"
  assumes Hl1 : "l1 = [z]"
  shows "gensyn_descend (G xr' (z#l)) t' cp" using assms
proof(induction arbitrary: xr xr' z cp' l1  l rule: gensyn_descend.induct)
  case (1 cc lsc tc xc)
  then show ?case
    by(auto intro: gensyn_descend.intros)
next
  case (2 tc tc' lc tc'' lc')

  obtain lch lct where Lc : "lc = lch#lct"
    using 2 gensyn_descend_nonnil[of tc tc' lc]
    by(cases lc; auto)

  have Lch : "lch = 0" using 2 Lc by auto

  have Desc1 : "gensyn_descend (G xr' (z # l)) tc' lc"
    using "2.IH"(1)[of lct xr l1 z] "2.prems" Lc Lch
    by(auto)

  show ?case using gensyn_descend.intros(2)[OF Desc1 "2.hyps"(2)] by auto
qed


lemma gensyn_descend_child_suc :
  assumes H : "gensyn_descend t t' cp"
  assumes Hcp : "cp = n#cp'"
  assumes Ht : "t = (G xr l1)"
  shows "gensyn_descend (G xr' (z#l1)) t' (Suc n # cp')" using assms
proof(induction arbitrary: xr xr' n z cp' l1 rule: gensyn_descend.induct)
  case (1 cc lsc tc xc)
  then show ?case 
    by(auto intro: gensyn_descend.intros)
next
  case (2 tc tc' lc tc'' lc')

  obtain lch lct where Lc : "lc = lch#lct"
    using 2 gensyn_descend_nonnil[of tc tc' lc]
    by(cases lc; auto)

  have Lch : "lch = n" using 2 Lc by auto

  have Desc1 : "gensyn_descend (G xr' (z # l1)) tc' (Suc lch # lct)"
    using "2.IH"(1)[of n lct xr l1 xr' z] "2.prems" Lc Lch
    by(auto)

  show ?case using gensyn_descend.intros(2)[OF Desc1 "2.hyps"(2)] Lch Lc "2.prems"
    by(auto)
qed

lemma gensyn_descend_correct2' :
  assumes H : "gensyn_get_list l cp = Some t'"
  shows "gensyn_descend (G xr l) t' cp" using assms
proof(induction l arbitrary: cp t' xr rule: gensyn_induct')
  case (1 x l)
  then show ?case
  proof(cases cp)
    case Nil
    then show ?thesis using 1 by auto
  next
    case (Cons cph cpt)
    then show ?thesis
    proof(cases cph)
      case 0
      then show ?thesis
      proof(cases cpt)
        case Nil' : Nil
        then show ?thesis using 1 Cons 0
          by(auto intro: gensyn_descend.intros) 
      next
        case Cons' : (Cons cph2 cpt2)
        have Desc1 : "gensyn_descend (G xr [G x l]) (G x l) [0]"
          by(auto intro: gensyn_descend.intros)

        have Desc2 : "gensyn_descend (G x l) t' cpt"
          using Cons' "1.prems" "1.IH"[of cpt t' x] Cons 0
          by auto

        show ?thesis using gensyn_descend.intros(2)[OF Desc1 Desc2]
          Cons' 0 Cons by auto
      qed
    next
      case (Suc cph')
      then show ?thesis using 1 Cons 
        by(auto)
    qed
  qed
next
  case 2
  then show ?case by auto
next
  case (3 t l)
  show ?case
  proof(cases cp)
    case Nil
    then show ?thesis using 3 by(auto)
  next
    case (Cons cph cpt)

    show ?thesis
    proof(cases cph)
      case 0

      show ?thesis
      proof(cases cpt)
        case Nil' : Nil
        then show ?thesis using "3.prems" "3.IH"(1) Cons 0 
          by(auto intro: gensyn_descend.intros)
      next
        case Cons' : (Cons cph2 cpt2)

        obtain xt lt where T : "t = G xt lt" by(cases t; auto)

        have Desc2' : "gensyn_descend (G xr [t]) t' cp"
          using Cons' "3.prems" "3.IH"(1)[of cp] Cons 0 T
          by(auto)

        show ?thesis
          using gensyn_descend_child_zero[OF Desc2'] 0 Cons
          by(auto)
      qed
    next
      case (Suc cph')

      obtain xt lt where T : "t = G xt lt" by(cases t; auto)

      have Desc2' : "gensyn_descend (G xr l) t' (cph'#cpt)"
        using "3.IH"(2)[of "cph'#cpt"] "3.prems" Cons Suc T
        by(auto)

      show ?thesis using gensyn_descend_child_suc[OF Desc2'] Suc Cons
        by auto
    qed
  qed
qed

(* relating skeletons to the structure of the original tree.
   NB: we could prove this for gensyn map in general
*)

lemma gs_implies_skel_Some' :
  assumes "gensyn_get_list ts cp = Some t'"
  shows "gensyn_get_list (map gs_sk ts) cp = Some (gs_sk t')" using assms
proof(induction ts arbitrary: cp t' rule: gensyn_induct')
case (1 x l)
  then show ?case 
  proof(cases cp)
    case Nil
    then show ?thesis using 1 by auto
  next
    case (Cons cph cpt)
    then show ?thesis
    proof(cases cph)
      case 0
      then show ?thesis
      proof(cases cpt)
        case Nil' : Nil
        then show ?thesis using 1 Cons 0
          by(auto)
      next
        case Cons' : (Cons cph2 cpt2)
        then show ?thesis using 1 Cons 0
          by(auto simp add: gs_sk_def)
      qed
    next
      case (Suc cph')
      then show ?thesis using 1 Cons
        by(auto)
    qed
  qed

next
  case 2
  then show ?case
    by(auto)
next
  case (3 t l)
  then show ?case 
  proof(cases cp)
    case Nil
    then show ?thesis using 3 by(auto)
  next
    case (Cons cph cpt)

    show ?thesis
    proof(cases cph)
      case 0

      show ?thesis
      proof(cases cpt)
        case Nil' : Nil
        then show ?thesis using "3.prems" "3.IH"(1) Cons 0 by auto
      next
        case Cons' : (Cons cph2 cpt2)
        then show ?thesis using "3.prems" "3.IH"(1)[of cp] Cons 0
          by(cases t; auto simp add: gs_sk_def)
      qed
    next
      case (Suc cph')
      then show ?thesis using "3.prems" "3.IH"(2) Cons
        by(auto)
    qed
  qed
qed

lemma gs_implies_skel_Some :
  assumes H: "gensyn_get t cp = Some t'"
  shows "gensyn_get (gs_sk t) cp = Some (gs_sk t')"
proof(cases cp)
  case Nil
  then show ?thesis using H
    by(auto)
next
  case (Cons cph cpt)

  obtain x l where T : "t = G x l"
    by(cases t; auto)

  have H' : "gensyn_get_list l cp = Some t'"
    using T H Cons
    by(auto)

  show "gensyn_get (gs_sk t) cp = Some (gs_sk t')"
    using gs_implies_skel_Some'[OF H'] H Cons T
    unfolding gs_sk_def
    by(auto)
qed

lemma gs_implies_skel_None' :
  assumes "gensyn_get_list ts cp = None"
  shows "gensyn_get_list (map gs_sk ts) cp = None" using assms
proof(induction ts arbitrary: cp  rule: gensyn_induct')
  case (1 x l)
  then show ?case 
  proof(cases cp)
    case Nil
    then show ?thesis using 1 by auto
  next
    case (Cons cph cpt)
    then show ?thesis
    proof(cases cph)
      case 0
      then show ?thesis
      proof(cases cpt)
        case Nil' : Nil
        then show ?thesis using 1 Cons 0
          by(auto)
      next
        case Cons' : (Cons cph2 cpt2)
        then show ?thesis using 1 Cons 0
          by(auto simp add: gs_sk_def)
      qed
    next
      case (Suc cph')
      then show ?thesis using 1 Cons
        by(auto)
    qed
  qed
next
  case 2
  then show ?case by auto
next
  case (3 t l)
  then show ?case
  proof(cases cp)
    case Nil
    then show ?thesis using 3 by(auto)
  next
    case (Cons cph cpt)

    show ?thesis
    proof(cases cph)
      case 0

      show ?thesis
      proof(cases cpt)
        case Nil' : Nil
        then show ?thesis using "3.prems" "3.IH"(1) Cons 0 by auto
      next
        case Cons' : (Cons cph2 cpt2)
        then show ?thesis using "3.prems" "3.IH"(1)[of cp] Cons 0
          by(cases t; auto simp add: gs_sk_def)
      qed
    next
      case (Suc cph')
      then show ?thesis using "3.prems" "3.IH"(2) Cons
        by(auto)
    qed
  qed
qed

lemma gs_implies_skel_None :
  assumes H: "gensyn_get t cp = None"
  shows "gensyn_get (gs_sk t) cp = None" using assms
proof(cases cp)
  case Nil
  then show ?thesis using H
    by(auto)
next
  case (Cons cph cpt)

  obtain x l where T : "t = G x l"
    by(cases t; auto)

  have H' : "gensyn_get_list l cp = None"
    using T H Cons
    by(auto)

  show "gensyn_get (gs_sk t) cp = None"
    using gs_implies_skel_None'[OF H'] H Cons T
    unfolding gs_sk_def
    by(auto)
qed


(* converses of the above *)
lemma gs_skel_implies_Some' :
  assumes "gensyn_get_list (map gs_sk ts) cp = Some t'sk "
  shows "\<exists> t' . gensyn_get_list ts cp = Some t' \<and> gs_sk t' = t'sk" using assms
proof(induction ts arbitrary: cp t'sk rule: gensyn_induct')
  case (1 x l)
  then show ?case 
  proof(cases cp)
    case Nil
    then show ?thesis using 1 by auto
  next
    case (Cons cph cpt)
    then show ?thesis
    proof(cases cph)
      case 0
      then show ?thesis
      proof(cases cpt)
        case Nil' : Nil
        then show ?thesis using 1 Cons 0
          by(auto)
      next
        case Cons' : (Cons cph2 cpt2)
        then show ?thesis using 1 Cons 0
          by(auto simp add: gs_sk_def)
      qed
    next
      case (Suc cph')
      then show ?thesis using 1 Cons
        by(auto)
    qed
  qed
next
  case 2
  then show ?case by auto
next
  case (3 t l)
  then show ?case
  proof(cases cp)
    case Nil
    then show ?thesis using 3 by(auto)
  next
    case (Cons cph cpt)

    show ?thesis
    proof(cases cph)
      case 0

      show ?thesis
      proof(cases cpt)
        case Nil' : Nil
        then show ?thesis using "3.prems" "3.IH"(1) Cons 0 by auto
      next
        case Cons' : (Cons cph2 cpt2)
        then show ?thesis using "3.prems" "3.IH"(1)[of cp] Cons 0
          by(cases t; auto simp add: gs_sk_def)
      qed
    next
      case (Suc cph')
      then show ?thesis using "3.prems" "3.IH"(2) Cons
        by(auto)
    qed
  qed
qed

lemma gs_skel_implies_Some :
  assumes H: "gensyn_get (gs_sk t) cp = Some t'sk "
  shows "\<exists> t' . gensyn_get t cp = Some t' \<and> gs_sk t' = t'sk" using assms
proof(cases cp)
  case Nil
  then show ?thesis using H
    by(auto)
next
  case (Cons cph cpt)

  obtain x l where T : "t = G x l"
    by(cases t; auto)

  have H' : "gensyn_get_list (map gs_sk l) cp = Some t'sk"
    using T H Cons unfolding gs_sk_def
    by(auto)

  show "\<exists>t'. gensyn_get t cp = Some t' \<and> gs_sk t' = t'sk"
    using gs_skel_implies_Some'[OF H'] H Cons T
    unfolding gs_sk_def
    by(auto)
qed

lemma gs_skel_implies_None' :
  assumes "gensyn_get_list (map gs_sk ts) cp = None "
  shows "gensyn_get_list ts cp = None" using assms
proof(induction ts arbitrary: cp rule: gensyn_induct')
  case (1 x l)
  then show ?case 
  proof(cases cp)
    case Nil
    then show ?thesis using 1 by auto
  next
    case (Cons cph cpt)
    then show ?thesis
    proof(cases cph)
      case 0
      then show ?thesis
      proof(cases cpt)
        case Nil' : Nil
        then show ?thesis using 1 Cons 0
          by(auto)
      next
        case Cons' : (Cons cph2 cpt2)
        then show ?thesis using 1 Cons 0
          by(auto simp add: gs_sk_def)
      qed
    next
      case (Suc cph')
      then show ?thesis using 1 Cons
        by(auto)
    qed
  qed
next
  case 2
  then show ?case by auto
next
  case (3 t l)
  then show ?case
  proof(cases cp)
    case Nil
    then show ?thesis using 3 by(auto)
  next
    case (Cons cph cpt)

    show ?thesis
    proof(cases cph)
      case 0

      show ?thesis
      proof(cases cpt)
        case Nil' : Nil
        then show ?thesis using "3.prems" "3.IH"(1) Cons 0 by auto
      next
        case Cons' : (Cons cph2 cpt2)
        then show ?thesis using "3.prems" "3.IH"(1)[of cp] Cons 0
          by(cases t; auto simp add: gs_sk_def)
      qed
    next
      case (Suc cph')
      then show ?thesis using "3.prems" "3.IH"(2) Cons
        by(auto)
    qed
  qed
qed

lemma gs_skel_implies_None :
  assumes H: "gensyn_get (gs_sk t) cp = None"
  shows "gensyn_get t cp = None" using assms
proof(cases cp)
  case Nil
  then show ?thesis using H
    by(auto)
next
  case (Cons cph cpt)

  obtain x l where T : "t = G x l"
    by(cases t; auto)

  have H' : "gensyn_get_list (map gs_sk l) cp = None"
    using T H Cons unfolding gs_sk_def
    by(auto)

  show "gensyn_get t cp = None"
    using gs_skel_implies_None'[OF H'] H Cons T
    unfolding gs_sk_def
    by(auto)
qed

(* specification for get_suffix *)
lemma get_suffix_spec :
  assumes H : "get_suffix l1 l2 = Some l3"
  shows "l1 @ l3 = l2" using H
proof(induction l1 arbitrary: l2 l3)
case Nil
  then show ?case 
    by(cases l2; auto)
next
  case (Cons l1h l1t)
  then show ?case
  proof(cases l2)
    case Nil' : Nil
    then show ?thesis using Cons by auto
  next
    case Cons' : (Cons l2h l2t)
    then show ?thesis
    proof(cases "l1h = l2h")
      case True
      then show ?thesis using Cons Cons' by auto
    next
      case False
      then show ?thesis using Cons Cons'
        by(auto)
    qed
  qed    
qed

lemma get_suffix_spec_conv :
  assumes H: "l1 @ (l2h#l2t) = l3"
  shows "get_suffix l1 l3 = Some (l2h#l2t)" using H
proof(induction l1 arbitrary: l2h l2t l3)
  case Nil
  then show ?case 
    by(auto)
next
  case (Cons l1h l1t)
  then show ?case
    by(auto)
qed  

(* specification for parent *)

lemma gensyn_cp_parent_spec :
  assumes H : "cp_parent cp = Some cp'"
  shows "\<exists> loc . cp = cp' @ [loc]" using H
proof(induction cp arbitrary: cp')
case Nil
  then show ?case by auto
next
  case (Cons cph cpt)
  then show ?case 
    by(cases cpt; auto)
qed

lemma gensyn_cp_parent_spec_conv :
  shows "cp_parent (cp' @ [loc]) = Some cp'"
proof(induction cp' arbitrary: loc)
case Nil
  then show ?case by auto
next
  case (Cons cph cpt)
  then show ?case by auto
qed

lemma get_suffix_nonnil :
  "get_suffix l1 l2 \<noteq> Some []"
proof(induction l1 arbitrary: l2)
  case Nil
  then show ?case by(cases l2; auto)
next
  case (Cons l1h l1t)
  then show ?case 
    by(cases l2; auto)
qed

end