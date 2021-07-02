theory Mergeable_Roalist imports "../Lib/Oalist/RoaList" "Mergeable_Oalist" "Pord" "Mergeable_Instances"
begin

(*
 * This file contains mergeable instances for RAlist - a variant of AList representing a
 * recursive key-value store (i.e., values can themselves be key-value stores).
 * Note that several key theorems are admitted ("sorry") here, rather than being proven.
 * This is because the proofs became extremely tedious; however, we do believe they are
 * provable.
 *)

lift_definition roalist_leq :: "('key :: linorder, 'value :: Pord, 'd :: Pord) roalist \<Rightarrow> ('key, 'value, 'd :: Pord) roalist \<Rightarrow> bool"
is "list_leq :: ('key :: linorder, 'value :: Pord, 'd option) roalist' \<Rightarrow> 
                ('key, 'value, 'd option) roalist' \<Rightarrow> bool" .
 
(* copied and edited proofs from MergeableAList. *)
lemma list_leq_refl : 
  assumes H : "strict_order (map fst a)"
  shows "list_leq a a" using H
proof(induction a)
  case Nil
  then show ?case by auto
next
  case (Cons a1 a2)
  obtain a1k a1v where A1 : "a1 = (a1k, a1v)" by(cases a1; auto)
  have SO : "strict_order (map fst a2)" using Cons strict_order_tl A1 by auto
  have D : "distinct (map fst (a1#a2))" using strict_order_distinct[OF Cons.prems] by auto
  hence Notin : "a1k \<notin> set (map fst a2)" using A1 by auto
  then show ?case using list_leq_cons[OF Cons.IH[OF SO]] A1 by(auto simp add:leq_refl)
qed

lemma list_leq_trans :
  assumes HO1 : "strict_order (map fst l1)"
  assumes HO2 : "strict_order (map fst l2)" 
  assumes HO3 : "strict_order (map fst l3)" 
  assumes H1 : "list_leq l1 l2"
  assumes H2 : "list_leq l2 l3" 
  shows "list_leq l1 l3" using assms
proof(induction l1 arbitrary: l2 l3)
  case Nil
  then show ?case by auto
next
  case (Cons l1h l1t)
  obtain a1k and a1v where Ha : "l1h = (a1k, a1v)" by(cases l1h; auto)
  hence Hleq12 : "list_leq l1t l2"  using Cons
    by(auto split:option.splits)
  obtain a2v where Ha2v : "(a1k, a2v) \<in> set l2" and Ha2vl:  "a1v <[ a2v"
    using Ha Cons strict_order_distinct[of "a1k # map fst l1t"]
          map_of_SomeD [of l2 a1k]
    by(auto split:option.splits) 
  obtain a3v where Ha3v : "(a1k, a3v) \<in> set l3" and Ha3vl : "a2v <[ a3v"
    using Cons Ha list_leqD[OF Cons.prems(5) Ha2v]
    by(auto split:option.splits)
  have Hav13 : "a1v <[ a3v" using leq_trans[OF Ha2vl Ha3vl] by auto
  have sto1 : "strict_order (map fst l1t)" using strict_order_tl[of a1k "map fst l1t"] Ha Cons by(auto)
  show "list_leq (l1h # l1t) l3" using Ha Ha3v Hav13
    map_of_is_SomeI[OF strict_order_distinct[OF Cons.prems(3)]] 
      Cons.IH[OF sto1 Cons.prems(2) Cons.prems(3) Hleq12] 
      Cons.prems
    by auto
qed

lemma list_leq_antisym :
  assumes Hord1 : "strict_order (map fst l1)"
  assumes Hord2 : "strict_order (map fst l2)"
  assumes Hleq1 : "list_leq l1 l2"
  assumes Hleq2 : "list_leq l2 l1"
  shows "l1 = l2"
proof-
  have Conc' : "set l1 = set l2"
  proof(rule Set.equalityI; rule Set.subsetI)
    fix x :: "('a * 'b)"
    obtain xk and xv where Hx: "x = (xk, xv)" by(cases x; auto)
    assume H : "x \<in> set l1"
    hence H' : "(xk, xv) \<in> set l1" using Hx by auto
    obtain v' where  Elv' : "(xk, v') \<in> set l2" and Leqv' : "xv <[ v'" using list_leqD[OF (*Hord1 Hord2*) Hleq1 H'] by auto
    obtain v'' where Elv'' : "(xk, v'') \<in> set l1" and Leqv'' : "v' <[ v''" using list_leqD[OF (*Hord2 Hord1*) Hleq2 Elv'] by auto
    have Hord1_d : "distinct (map fst l1)" using strict_order_distinct[OF Hord1] by auto
    have H'' : "xk \<in> set (map fst l1)" using H' imageI[OF H', of fst] by(auto)
    obtain i1 where Hi11 : "i1 < length l1" and Hi12 : "l1 ! i1 = (xk, xv)" using H' List.in_set_conv_nth[of "(xk, xv)" "l1"] by auto 
    obtain i1' where Hi1'1 : "i1' < length l1" and Hi1'2 :  "l1 ! i1' = (xk, v'')" using Elv'' List.in_set_conv_nth[of "(xk, v'')" "l1"]
      by(auto)
    have "i1 = i1'" using Hi11 Hi12 Hi1'1 Hi1'2 List.distinct_Ex1[OF Hord1_d H''] by(auto)
    hence "v'' = xv" using Hi12 Hi1'2 by auto
    hence Leqv'2 : "v' <[ xv" using Leqv'' by auto
    hence "xv = v'" using leq_antisym[OF Leqv' Leqv'2] by auto
    thus "x \<in> set l2" using Elv' Hx by auto
  next
    fix x :: "('a * 'b)"
    obtain xk and xv where Hx: "x = (xk, xv)" by(cases x; auto)
    assume H : "x \<in> set l2"
    hence H' : "(xk, xv) \<in> set l2" using Hx by auto
    obtain v' where  Elv' : "(xk, v') \<in> set l1" and Leqv' : "xv <[ v'" using list_leqD[OF Hleq2 H'] by auto
    obtain v'' where Elv'' : "(xk, v'') \<in> set l2" and Leqv'' : "v' <[ v''" using list_leqD[OF Hleq1 Elv'] by auto
    have Hord1_d : "distinct (map fst l2)" using strict_order_distinct[OF Hord2] by auto
    have H'' : "xk \<in> set (map fst l2)" using H' imageI[OF H', of fst] by(auto)
    obtain i1 where Hi11 : "i1 < length l2" and Hi12 : "l2 ! i1 = (xk, xv)" using H' List.in_set_conv_nth[of "(xk, xv)" "l2"] by auto 
    obtain i1' where Hi1'1 : "i1' < length l2" and Hi1'2 :  "l2 ! i1' = (xk, v'')" using Elv'' List.in_set_conv_nth[of "(xk, v'')" "l2"]
      by(auto)
    have "i1 = i1'" using Hi11 Hi12 Hi1'1 Hi1'2 List.distinct_Ex1[OF Hord1_d H''] by(auto)
    hence "v'' = xv" using Hi12 Hi1'2 by auto
    hence Leqv'2 : "v' <[ xv" using Leqv'' by auto
    hence "xv = v'" using leq_antisym[OF Leqv' Leqv'2] by auto
    thus "x \<in> set l1" using Elv' Hx by auto
  qed

  show "l1 = l2"  using strict_order_set_eq[OF Hord1 Hord2 Conc'] by auto 
qed

lift_definition roa_empty :: "('k :: linorder, 'v, 'd) roalist"
is "[([], Inr None)] :: ('k, 'v, 'd option) roalist'"
  by(auto simp add: strict_order_def roalist_valid_def)

value "roalist_get (roa_empty :: (String.literal, unit, unit) roalist) (String.implode ''a'') "

fun roa_make_vs :: "('k :: linorder  * 'v) list \<Rightarrow> ('k, 'v, 'd) roalist" where
"roa_make_vs [] = roa_empty"
| "roa_make_vs ((kh, vh)#t) =
    roalist_update_v kh vh (roa_make_vs t)"
  


instantiation roalist :: (linorder, Pord, Pord) Pord
begin

definition pleq_roalist :
"pleq l1 l2 = roalist_leq l1 l2"
instance sorry
(*
  fix l1 :: "('a :: linorder, 'b :: Pord, 'c :: pord) roalist"
  show "l1 <[ l1" unfolding pleq_roalist
    by(transfer; auto simp add: list_leq_refl)
next
  fix l1 l2 l3 :: "('a :: linorder, 'b :: Pord) roalist"
  assume H1 : "l1 <[ l2"
  assume H2 : "l2 <[ l3"
  show "l1 <[ l3" using H1 H2 unfolding pleq_roalist
  proof(transfer)
    fix l1 l2 l3 :: "('a, 'b) roalist'"
    assume HO1 : "strict_order (map fst l1) \<and> roalist_valid l1"
    assume HO2 : "strict_order (map fst l2) \<and> roalist_valid l2"
    assume HO3 : "strict_order (map fst l3) \<and> roalist_valid l3"
    assume H1 : "list_leq l1 l2"
    assume H2 : "list_leq l2 l3"
    show "list_leq l1 l3" using list_leq_trans[of l1 l2 l3] HO1 HO2 HO3 H1 H2 by auto
  qed
next
  fix l1 l2 :: "('a :: linorder, 'b :: Pord) roalist"
  assume H1 : "l1 <[ l2"
  assume H2 : "l2 <[ l1"
  show "l1 = l2" using H1 H2 unfolding pleq_roalist
  proof(transfer)
    fix l1 l2 :: "('a, 'b) roalist'"
    assume HO1 : "strict_order (map fst l1) \<and> roalist_valid l1"
    assume HO2 : "strict_order (map fst l2) \<and> roalist_valid l2"
    assume H1 : "list_leq l1 l2"
    assume H2 : "list_leq l2 l1"
    show "l1 = l2" using list_leq_antisym HO1 HO2 H1 H2 by auto
  qed
qed
*)
end

(*
lemma roalist_valid_hd :
  assumes H1 : "strict_order (map fst l)"
  assumes H2 : "roalist_valid l"
  shows "\<exists> l' . l = ([], Inr ())#l'" 
proof(cases l)
  case Nil
  then show ?thesis using H2 by(auto simp add:roalist_valid_def)
next
  case (Cons a l')
  then obtain ak av where Ha : "a = (ak, av)" by(cases a; auto)
  then show ?thesis
  proof(cases "ak = []")
    case True
    have In1 : "([], Inr ()) \<in> set l" using map_of_SomeD[OF roalist_valid_elim1[OF H2]] by auto
    have In2 : "([], av) \<in>  set l" using Ha Cons True by auto
    hence "av = Inr ()" using imageI[OF In1, of fst] distinct_unique_value[OF strict_order_distinct[OF H1] In1 In2]  by(auto)
    then show ?thesis using Ha Cons True by auto
  next
    case False
    have In1 : "([], Inr ()) \<in> set l" using map_of_SomeD[OF roalist_valid_elim1[OF H2]] by auto
    hence In1' : "([], Inr ()) \<in> set l'" using Cons False Ha by auto
    then obtain ix where "ix < length l'" "l' ! ix = ([], Inr ())" unfolding in_set_conv_nth by auto
    hence Bad : "ak < []" using strict_order_unfold[OF H1, of "1 + ix" 0] H1 Cons Ha by(auto)
    hence False using False unfolding list_lo_lt by(cases ak; auto)
    then show ?thesis by auto
  qed
qed

lemma roalist_delete_clos'_order :
  assumes H : "strict_order (map fst list)"
  shows "strict_order (map fst (roalist_delete_clos' k list))" using H
proof(induction list)
  case Nil
  then show ?case by(auto intro: strict_order_nil)
next
  case (Cons a list)
  obtain kh vh where A : "a = (kh, vh)" by (cases a; auto)
  show ?case
  proof(cases kh)
    assume Nil' : "kh = []"
    then show ?thesis 
    proof(cases "map fst (roalist_delete_clos' k list)")
      assume Nil'' : "map fst (roalist_delete_clos' k list) = []"
      then show ?thesis
        using Cons Nil' strict_order_tl A strict_order_singleton strict_order_cons 
        by(auto)
    next
      fix h' t'
      assume Cons'' : "map fst (roalist_delete_clos' k list) = (h'#t')"
      then have A2_in' : "h' \<in> set (map fst (roalist_delete_clos' k list))" by auto
      then obtain v' where V'_in : "(h', v') \<in> set (roalist_delete_clos' k list)"
        by(auto)
      have Ord' : "strict_order (map fst list)" using strict_order_tl Cons.prems by auto
      have A2_in_orig : "(h', v') \<in> set list"
        using Cons roalist_delete_clos'_elem[OF Ord' V'_in] by auto
      then obtain a2idx where "a2idx < length list" "list ! a2idx = (h', v')" 
        by (auto simp add: List.in_set_conv_nth)
      hence Conc_hd : "[] < h'" using strict_order_unfold[OF Cons.prems(1), of "1 + a2idx" 0] Cons A Nil'
        by(auto simp add: list_lo_lt)
      then show ?thesis using Cons Nil' A Cons'' strict_order_cons[of "[]" h'] Ord'
        by(auto)
    qed
  next
    fix khh kht
    assume Cons' : "kh = khh#kht"
    then show ?thesis
    proof(cases "map fst (roalist_delete_clos' k list)")
      assume Nil'' : "map fst (roalist_delete_clos' k list) = []"
      then show ?thesis
        using Cons Cons' strict_order_tl A strict_order_singleton strict_order_cons 
        by(auto)
    next
      fix h' t'
      assume Cons'' : "map fst (roalist_delete_clos' k list) = (h'#t')"
      then have A2_in' : "h' \<in> set (map fst (roalist_delete_clos' k list))" by auto
      then obtain v' where V'_in : "(h', v') \<in> set (roalist_delete_clos' k list)"
        by(auto)
      have Ord' : "strict_order (map fst list)" using strict_order_tl Cons.prems by auto
      have A2_in_orig : "(h', v') \<in> set list"
        using Cons roalist_delete_clos'_elem[OF Ord' V'_in] by auto
      then obtain a2idx where "a2idx < length list" "list ! a2idx = (h', v')" 
        by (auto simp add: List.in_set_conv_nth)
      hence Conc_hd : "kh < h'" using strict_order_unfold[OF Cons.prems(1), of "1 + a2idx" 0] Cons A Cons'
        by(auto simp add: list_lo_lt)
      then show ?thesis using Cons Cons' A Cons'' strict_order_cons[of "kh" h'] Ord'
        by(auto)
    qed
  qed
qed
*)
(* need to factor out second lemma here *)
lift_definition roalist_delete_clos :: "('k :: linorder) \<Rightarrow> ('k :: linorder, 'v, 'd) roalist \<Rightarrow> ('k, 'v, 'd) roalist"
is roalist_delete_clos' sorry
(*
proof-
  fix k :: "'k"
  fix list :: "('k :: linorder, 'v) roalist'"
  assume H : "strict_order (map fst list) \<and> roalist_valid list"
  hence H1 :  "strict_order (map fst list)" and H2 : "roalist_valid list" by auto

  have C1 : "strict_order (map fst (roalist_delete_clos' k list))" using roalist_delete_clos'_order[OF H1]
    by auto

  have C2 : "roalist_valid (roalist_delete_clos' k list)"
  proof(rule roalist_valid_intro)
    show "map_of (roalist_delete_clos' k list) [] = Some (Inr ())"
      using roalist_valid_hd[OF H1 H2] by(auto)
  next
    fix pref v sufh suf
    assume Res_in : "map_of (roalist_delete_clos' k list) pref = Some (Inl v)"
    have Res_in' : "(pref, Inl v) \<in> set (roalist_delete_clos' k list)" using map_of_SomeD[OF Res_in] by auto
    have Orig_in' : "(pref, Inl v) \<in> set list" using roalist_delete_clos'_elem[OF H1 Res_in'] by auto
    have Orig_in : "map_of list pref = Some (Inl v)" using map_of_is_SomeI[OF strict_order_distinct[OF H1] Orig_in'] by auto
    have Orig_in2 : "map_of list (pref @ sufh # suf) = None"
      using roalist_valid_elim2[OF H2 Orig_in] by auto
    obtain prefh suf' where Pref' : "pref @ sufh # suf = prefh#suf'" by(cases pref; auto)
    show "map_of (roalist_delete_clos' k list) (pref @ sufh # suf) = None"
    proof(cases "map_of (roalist_delete_clos' k list) (pref @ sufh # suf)")
      case None
      then show ?thesis by auto
    next
      case (Some bad)
      have Some' : "(prefh#suf', bad) \<in> set (roalist_delete_clos' k list)"
        using map_of_SomeD[OF Some] Pref' by auto
      have Some'_orig : "map_of list (prefh#suf') = Some bad"
        using map_of_is_SomeI[OF strict_order_distinct[OF H1] roalist_delete_clos'_elem[OF H1 Some']] by auto
      have Some'_orig' : "(prefh#suf', bad) \<in> set list"
        using map_of_SomeD[OF Some'_orig] by auto

      have False using Some'_orig Orig_in2 unfolding Pref' by auto
      thus ?thesis by auto
    qed
  next
    fix pref x sufh suf
    assume Res_in : "map_of (roalist_delete_clos' k list) (pref @ sufh # suf) = Some x"
    have Res_in' : "(pref@sufh#suf, x) \<in> set (roalist_delete_clos' k list)" using map_of_SomeD[OF Res_in] by auto
    have Orig_in' : "(pref@sufh#suf, x) \<in> set list" using roalist_delete_clos'_elem[OF H1 Res_in'] by auto
    have Orig_in : "map_of list (pref@sufh#suf) = Some x"
      using map_of_is_SomeI[OF strict_order_distinct[OF H1] Orig_in'] by auto
    have Orig_in2 : "map_of list pref = Some (Inr ())" using roalist_valid_elim3[OF H2 Orig_in] by auto
    have Orig_in2' : "(pref, Inr ()) \<in> set list"
      using map_of_SomeD[OF Orig_in2] by auto

    obtain prefh suf' where Pref' : "pref @ sufh # suf = prefh#suf'" by(cases pref; auto)

    show "map_of (roalist_delete_clos' k list) pref = Some (Inr ())"
    proof(cases "k = prefh")
      case True
      then have False using imageI[OF Res_in', of fst] roalist_delete_clos'_notelem2[OF H1, of prefh suf'] unfolding Pref'
        by(auto)
      thus ?thesis by auto
    next
      case False
      show "map_of (roalist_delete_clos' k list) pref = Some (Inr ())"
      proof(cases pref)
        case Nil
        then show ?thesis using roalist_valid_hd[OF H1 H2] by(auto)
      next
        case (Cons prefh' preft)
        hence Prefh_h' : "prefh = prefh'" using Pref' by auto
        have Conc' : "(prefh' # preft, Inr ()) \<in> set (roalist_delete_clos' k list)"
          using roalist_delete_clos'_elem_contra[OF H1, of prefh preft "Inr ()" k] Orig_in2' False
          unfolding Cons Prefh_h'
          by auto
        thus ?thesis using map_of_is_SomeI[OF strict_order_distinct[OF roalist_delete_clos'_order[OF H1]] Conc']
          unfolding Cons by auto
      qed
    qed
  qed

  show "strict_order (map fst (roalist_delete_clos' k list)) \<and> roalist_valid (roalist_delete_clos' k list)"
    using C1 C2 by auto
qed
*)

fun roalist_gather'_check :: 
  "('k :: linorder, 'v, 'd) roalist' \<Rightarrow> 'k \<Rightarrow> ('k :: linorder, 'v, 'd) roalist' option" where
"roalist_gather'_check l k =
  (case map_of l [k] of
    Some (Inr _) \<Rightarrow> Some (roalist_gather' l k)
    | _ \<Rightarrow> None)"

(* 
  empty list \<Rightarrow> id  
  if we are a prefix, we include the result
  otherwise we don't
*)

(*
| "roalist_gathers' (([kh], (Inl _))#l) k = roalist_gathers' l k"
| "roalist_gathers' (([kh], (Inr ()))#l) k = 
  ( if k = kh then ([], Inr ())#roalist_gathers' l k
    else roalist_gathers' l k)"
| "roalist_gather' (((khh1#khh2#kht), vh)#l) k = 
  ( if k = khh1 then (khh2#kht, vh) # roalist_gathers' l k
    else roalist_gathers' l k)"
*)

(*
lemma roalist_gather'_correct :
  assumes H1 : "strict_order (map fst l)"
  and H2 : "roalist_valid l"
  and H3 : "roalist_gather'_check l k = Some l'"
  shows "roalist_valid l'" 
proof(rule roalist_valid_intro)
  have M :  "map_of l [k] = Some (Inr ())" using H3 
    by(cases "map_of l [k]"; auto split:sum.splits)

  have Lin : "([k], Inr ()) \<in> set l" using map_of_SomeD[OF M] by auto

  have Gath : "map_of (roalist_gather' l k) [] = Some (Inr ())"
    using map_of_is_SomeI[OF strict_order_distinct[OF roalist_gather'_order[OF H1]]
                             roalist_gather'_elem'2[OF H1 Lin]] by auto

  show "map_of l' [] = Some (Inr ())" using H3 M
    roalist_gather'_elem'2[OF H1 Lin] Gath
    by(auto split:unit.splits)
next
  fix pref v sufh suf
  assume H : "map_of l' pref = Some (Inl v) "
  have M :  "map_of l [k] = Some (Inr ())" using H3 
    by(cases "map_of l [k]"; auto split:sum.splits)

  have H' : "(pref, Inl v) \<in> set (roalist_gather' l k)"
    using H H3 M map_of_SomeD[OF H] 
    by(auto split:unit.splits)

  have H'l : "(k#pref, Inl v) \<in> set l"
    using roalist_gather'_elem[OF H1 H'] by auto

  hence Lval : "map_of l (k#pref) = Some (Inl v)"
    using map_of_is_SomeI[OF strict_order_distinct[OF H1]] by auto

  show "map_of l' (pref @ sufh # suf) = None"
  proof(cases "map_of l' (pref @ sufh # suf)")
    case None thus ?thesis by auto
  next
    case (Some bad)

    have False' : "(pref @ sufh # suf, bad) \<in> set (roalist_gather' l k)"
      using H H3 M map_of_SomeD[OF Some] 
      by(auto split:unit.splits)

    have False'l : "(k#pref @ sufh # suf, bad) \<in> set l"
      using roalist_gather'_elem[OF H1 False'] by auto

    hence Lval' : "map_of l (k#pref @ sufh # suf) = Some (bad)"
      using map_of_is_SomeI[OF strict_order_distinct[OF H1]] by auto

    have "map_of l ((k#pref) @ sufh # suf) = None"
      using roalist_valid_elim2[OF H2 Lval] by auto

    hence False using Lval' by auto
    thus ?thesis by auto
  qed
next
  fix pref x sufh suf
  assume H : "map_of l' (pref @ sufh # suf) = Some x"
  have M :  "map_of l [k] = Some (Inr ())" using H3 
    by(cases "map_of l [k]"; auto split:sum.splits)

  have H' : "(pref@ sufh # suf, x) \<in> set (roalist_gather' l k)"
    using H H3 M map_of_SomeD[OF H] 
    by(auto split:unit.splits)

  have H'l : "(k#pref @ sufh # suf, x) \<in> set l"
    using roalist_gather'_elem[OF H1 H'] by auto

  hence Lval : "map_of l (k#pref @ sufh # suf) = Some (x)"
    using map_of_is_SomeI[OF strict_order_distinct[OF H1]] by auto

  have Lval' : "map_of l (k#pref) = Some (Inr ())"
    using roalist_valid_elim3[OF H2] Lval by(auto)

  have Prefl : "(k#pref, Inr ()) \<in> set l"
    using map_of_SomeD[OF Lval'] by auto

  have Prefl_l' : "(pref, Inr ()) \<in> set (roalist_gather' l k)"
    using roalist_gather'_elem'2[OF H1 Prefl] by auto

  hence Gath : "map_of (roalist_gather' l k) pref = Some (Inr ())"
    using map_of_is_SomeI[OF strict_order_distinct[OF roalist_gather'_order[OF H1]] Prefl_l']
    by auto

  show "map_of l' pref = Some (Inr ())"
    using H3 M Gath by(auto split:unit.splits)
qed
*)


lift_definition roalist_gather :: "('k :: linorder, 'v, 'd) roalist \<Rightarrow> 'k \<Rightarrow> ('k, 'v, 'd) roalist option"
is roalist_gather'_check sorry
(*
proof-
  fix k :: "'k"
  fix list :: "('k :: linorder, 'v) roalist'"
  assume H : "strict_order (map fst list) \<and> roalist_valid list"
  hence H1 : "strict_order (map fst list)" and H2 : "roalist_valid list" by auto

  have C1 : "strict_order (map fst (roalist_gather' list k))"
    using roalist_gather'_order[OF H1] by auto

  show "pred_option (\<lambda>xs. strict_order (map fst xs) \<and> roalist_valid xs)
        (roalist_gather'_check list k)"
  proof(cases "roalist_gather'_check list k")
    case None
    then show ?thesis by(auto)
  next
    case (Some a)

    have C2 : "roalist_valid a" using roalist_gather'_correct[OF H1 H2 Some] by auto
    then show ?thesis using Some C1
      by(auto split:option.split_asm sum.split_asm unit.split_asm)
  qed
qed
*)
(*
(* idea: we know we can find a sup, but we need to prove that it also
   meets roalist_valid.
   suppose UB isn't roalist_valid. then either
    - [] doesnt map to Inr (), 
        \<longrightarrow> impossible because both other lists have that
    - has non-None stored at a suffix of a value
        \<longrightarrow> but then value would have come from one list and non-None suffix from the other
            however, this would also lead to a contradiction
    - has something other than Inr stored at a prefix of a value/Inr
*)

lemma str_ord_delete_notin :
  assumes H : "strict_order (map fst a)"
  shows "(k, v) \<notin> set (str_ord_delete k a)" using H
proof(induction a arbitrary: k v)
  case Nil
  then show ?case by auto
next
  case (Cons ah at)
  have Ord_at : "strict_order (map fst at)" using strict_order_tl Cons by auto
  obtain ahk ahv where Ah : "ah = (ahk, ahv)" by (cases ah; auto)
  show ?case 
  proof(cases "k = ahk")
    case True
    have "(ahk, v) \<notin> set at" using strict_order_distinct[OF Cons.prems(1)] Ah
        Set.imageI[of "(ahk, v)" "set at" fst]
      by(auto)
    then show ?thesis using Cons.prems Cons.IH[OF Ord_at] Ah True
      by(auto)
  next
    case False
    show ?thesis
    proof(cases "ahk < k")
      assume True' : "ahk < k"
      then show ?thesis using Ah Cons.prems Cons.IH[OF Ord_at, of k v] by(auto)
    next
      assume False' : "\<not> (ahk < k)"
      hence False'2 : "k < ahk" using False less_linear[of k ahk] by auto
      have Notin : "(k, v) \<notin> set at"
      proof
        assume Ctr: "(k, v) \<in> set at"
        then obtain idx where Idx : "idx < length at" "at ! idx = (k, v)"
          by(auto simp add:List.in_set_conv_nth)
        thus False using strict_order_unfold[OF Cons.prems(1), of "1 + idx" 0] Ah False'2
          by auto
      qed
      then show ?thesis using Cons.prems Cons.IH[OF Ord_at, of k v] Ah False'2 by(auto)
    qed
  qed
qed

lemma str_ord_delete_in :
  assumes H : "strict_order (map fst a)"
  assumes Hkv : "(k, v) \<in> set a"
  assumes Hneq : "k \<noteq> k'"
  shows "(k, v) \<in> set (str_ord_delete k' a)" using H Hkv Hneq
proof(induction a arbitrary: k k' v)
  case Nil
  then show ?case by auto
next
  case (Cons ah at)
  obtain kh kt where Ah : "ah = (kh, kt)" by (cases ah; auto)
  hence H' : "strict_order (map fst at)" using strict_order_tl[of "kh" "map fst at"] Cons.prems
    by(auto)
  then show ?case
(* need 2 layers of cases *)
  proof(cases "kh = k")
    case True
    then show ?thesis
    proof(cases "kh = k'")
      assume True' : "kh = k'"
      then show ?thesis using True H' Cons by(auto)
    next
      assume False' : "kh \<noteq> k'"
      then show ?thesis using True H' Cons Ah
        by(auto)
    qed
  next
    case False
    then show ?thesis
    proof(cases "kh = k'")
      assume True' : "kh = k'"
      then show ?thesis using False H' Cons Ah by(auto)
    next
      assume False' : "kh \<noteq> k'"
      then show ?thesis using False H' Cons Ah
        by(auto)
    qed
  qed
qed
*)

(* elem lemma needed. *)

fun roalist_gathers' ::
  "('k :: linorder, 'v, 'd) roalist' \<Rightarrow> 'k list \<Rightarrow> ('k :: linorder, 'v, 'd) roalist'" where
"roalist_gathers' [] _ = []"
| "roalist_gathers' ((kh, vh)#l) k = 
  ( if is_prefix k kh then ((drop (length k) kh, vh) # roalist_gathers' l k)
    else roalist_gathers' l k)"

(*
lemma roalist_gather'_elem :
  assumes Hord : "strict_order (map fst l)"
  assumes H : "(kt, v) \<in> set (roalist_gather' l kh)"
  shows "(kh#kt, v) \<in> set l" using Hord H
proof(induction l arbitrary: kh kt v)
  case Nil
  then show ?case by auto
next


lemma roalist_gathers'_order :
  assumes H1 : "strict_order (map fst l)"
  shows "strict_order (map fst (roalist_gathers' l k))" using H1
proof(induction l arbitrary: k)
  case Nil
  then show ?case 
    by(auto)
next
  case (Cons h t)
  obtain kh vh where Hd : "(h = (kh, vh))" by(cases h; auto)
  have Hord' : "strict_order (map fst t)"
    using strict_order_tl Cons by auto

  then show ?case using Cons
  proof(cases "map fst (roalist_gathers' t k)")
    case Nil' : Nil
    then show ?thesis using Cons Hd 
      by(auto simp add:strict_order_def)
  next
    case Cons' : (Cons h2 t2)
(*
    obtain kh2 vh2 where Hd2 : "(h2 = (kh2, vh2))" 
      by(cases h2; auto)
*)
    then show ?thesis using Cons Hd Cons'
      apply(auto)
  qed
    apply(auto)
qed
*)

(* intuition: start by using completeness of "vanilla" oalists.
   however this upper bound may not be valid according to roalist rules,
   so we will need to find a possibly greater upper bound, and then
   show that anytihng between this and the "vanilla" sup
   is going to violate roalist rules.
*)
instantiation roalist :: (linorder, Pordc, Pordc) Pordc
begin
instance sorry
end
(*
instance proof 
  fix a b :: "('a :: linorder, 'b :: Pordc) roalist"
  assume H : "has_ub {a, b}"

  show "has_sup {a, b}" using H unfolding has_ub_def has_sup_def is_sup_def is_least_def is_ub_def pleq_roalist
sorry
qed
*)
(*

instance proof
  fix a b :: "('a :: linorder, 'b :: Pordc) roalist"
  assume H : "has_ub {a, b}"

  show "has_sup {a, b}" using H unfolding has_ub_def has_sup_def is_sup_def is_least_def is_ub_def pleq_roalist
  proof(transfer)
    fix a b :: "('a :: linorder, 'b :: Pordc) roalist'"
    assume HA : "strict_order (map fst a) \<and> roalist_valid a"
    hence HA1 : "strict_order (map fst a)" and HA2 : "roalist_valid a" by auto
    hence HAD : "distinct (map fst a)" using strict_order_distinct by auto
    assume HB : "strict_order (map fst b) \<and> roalist_valid b"
    hence HB1 : "strict_order (map fst b)" and HB2: "roalist_valid b" by auto
    hence HBD : "distinct (map fst b)" using strict_order_distinct by auto
    assume H: "\<exists>aa\<in>{xs. strict_order (map fst xs) \<and> roalist_valid xs}.
            \<forall>x\<in>{a, b}. list_leq x aa"
    then obtain xs where
      Xs_ord : "strict_order (map fst xs)"
      and Xs_valid : "roalist_valid xs"
      and Xs_gt_a : "list_leq a xs"
      and Xs_gt_b :  "list_leq b xs"
      by auto

    obtain sup where Sup_ord : "strict_order (map fst sup)"
      and Sup_gt_a : "list_leq a sup"
      and Sup_gt_b :  "list_leq b sup"
      and Is_sup : "(\<And> ub'::('a, 'b) roalist'.
                     strict_order (map fst ub') \<Longrightarrow>
                     list_leq a ub' \<Longrightarrow> list_leq b ub' \<Longrightarrow> list_leq sup ub')"
      using list_complete[OF HA1 HB1 Xs_ord Xs_gt_a Xs_gt_b] by auto

    hence Is_sup' : "(\<And> ub'::('a, 'b) roalist'.
                     strict_order (map fst ub') \<Longrightarrow>
                     roalist_valid ub' \<Longrightarrow>
                     list_leq a ub' \<Longrightarrow> list_leq b ub' \<Longrightarrow> list_leq sup ub')" by auto

    have Sup_D : "distinct (map fst sup)" using strict_order_distinct Sup_ord by auto

    have Conc' : "roalist_valid sup"
    proof(rule roalist_valid_intro)
      show "map_of sup [] = Some (Inr ())"
      proof-
        have InrA : "map_of a [] = Some (Inr ())" using roalist_valid_elim1[OF HA2] by auto
        hence InrA' : "([], Inr ()) \<in> set a" using map_of_is_SomeI HAD by auto
        obtain b' where Conc' : "([], b') \<in> set sup" and B' : "Inr () <[ b'" using list_leqD[OF Sup_gt_a InrA']
          by auto
        have B'_is : "b' = Inr ()" using B' by(cases b'; auto simp add: unit_pleq sum_pleq)
        show "map_of sup [] = Some (Inr ())" using map_of_is_SomeI[OF Sup_D Conc'] B'_is
          by auto
      qed
    next
      fix pref v sufh suf
      assume Hmap: "map_of sup pref = Some (Inl v)"
      show "map_of sup (pref @ sufh # suf) = None"
      proof-
        consider
          (1) "map_of a pref = None" "map_of b pref = None" |
          (2) z1 where "map_of a pref = Some z1" "map_of b pref = None" |
          (3) z2 where "map_of a pref = None" "map_of b pref = Some z2" |
          (4) z1 z2 where "map_of a pref = Some z1" "map_of b pref = Some z2"
          by(cases "map_of a pref"; cases "map_of b pref"; auto)
        then show "map_of sup (pref @ sufh # suf) = None"
        proof cases
          case 1
          (* contradiction: sup can't be sup. *)
          (* need smart delete here - delete closure if its a closure, value if it's a value
              delete won't be guaranteed to be valid.
             (or, maybe just in this case, it will? *)
(* problem - we need to be able to deeply delete closures. our delete closure function
   only deletes closures at the top level. *)
          have BadSup : "list_leq sup (roalist_delete_clos' pref sup)"
          proof(rule Is_sup'[OF str_ord_delete_correct[OF Sup_ord]])
          proof(rule list_leqI[OF Sup_ord str_ord_delete_correct[OF Sup_ord]])
            fix k v
            assume Kv : "(k, v) \<in> set sup"
            show "\<exists>v'. (k, v') \<in> set (str_ord_delete pref sup) \<and> v <[ v'"
            proof(cases "k = pref")
              case True
              then show ?thesis using 1
            next
              case False
              then show ?thesis sorry
            qed
          (* lemma about delete needed *) 
(*
          have False using list_leqD[OF BadSup map_of_SomeD[OF Hmap]] apply(auto)
          then show ?thesis 
*)        show ?thesis sorry
        next
          case 2
          then show ?thesis sorry
        next
          case 3
          then show ?thesis sorry
        next
          case 4
          then show ?thesis sorry
        qed
      qed
    next
      fix pref x sufh suf
      assume Hmap : "map_of sup (pref @ sufh # suf) = Some x"
      show "map_of sup pref = Some (Inr ())"
        sorry
    qed

    thus "\<exists>aa\<in>{xs. strict_order (map fst xs) \<and> roalist_valid xs}.
              (\<forall>x\<in>{a, b}. list_leq x aa) \<and>
              (\<forall>a'\<in>{xs. strict_order (map fst xs) \<and> roalist_valid xs}.
                  (\<forall>x\<in>{a, b}. list_leq x a') \<longrightarrow> list_leq aa a')"
      using Sup_ord Sup_gt_a Sup_gt_b Is_sup
      by(auto)
  qed
qed
end
*)

instantiation roalist :: (linorder, Pordc, Pordc) Pordb
begin
definition bot_roalist :
  "\<bottom> = roa_empty"

instance sorry
end


lift_definition roalist_check_prefixes :: "('key :: linorder, 'value, 'd) roalist \<Rightarrow> 'key list \<Rightarrow> bool"
is roalist_check_prefixes' .

(* idea: this works like list bsup, except that
   we need to make sure we don't merge a value and a closure together. *)
fun roalist_bsup' :: "('key :: linorder, 'value :: Mergeable, 'd :: Mergeable) roalist' \<Rightarrow>
                      ('key, 'value, 'd) roalist' \<Rightarrow> ('key, 'value, 'd) roalist'" where
"roalist_bsup' l [] = l"
| "roalist_bsup' l ((rkh, Inl rv)#rt) =
   (case map_of l rkh of
      Some (Inl lv) \<Rightarrow> roalist_bsup' (str_ord_update rkh (Inl [^ lv, rv ^]) l) rt
      | Some (Inr _) \<Rightarrow> roalist_bsup' l rt
      | None \<Rightarrow>
        (if roalist_check_prefixes' l rkh
         then roalist_bsup' (str_ord_update rkh (Inl rv) l) rt
         else roalist_bsup' l rt))"
| "roalist_bsup' l ((rkh, Inr rv)#rt) =
    (case map_of l rkh of
      Some (Inl _) \<Rightarrow> roalist_bsup' l rt
      | Some (Inr lv) \<Rightarrow> roalist_bsup' (str_ord_update rkh (Inr [^ lv, rv ^]) l) rt
      | None \<Rightarrow> (if roalist_check_prefixes' l rkh
                 then roalist_bsup' (str_ord_update rkh (Inr rv) l) rt
                 else roalist_bsup' l rt))"


lift_definition roalist_bsup :: "('key :: linorder, 'value :: Mergeable, 'd :: Mergeable) roalist \<Rightarrow>
                                 ('key, 'value, 'd) roalist \<Rightarrow> ('key, 'value, 'd) roalist"
is roalist_bsup' sorry
(*
proof-
  show "\<And>list1 list2.
       strict_order (map fst list1) \<and>
       roalist_valid list1 \<Longrightarrow>
       strict_order (map fst list2) \<and>
       roalist_valid list2 \<Longrightarrow>
       strict_order (map fst (roalist_bsup' list1 list2)) \<and>
       roalist_valid (roalist_bsup' list1 list2)" sorry
qed
*)


instantiation roalist :: (linorder, Mergeable, Mergeable) Mergeable
begin

definition bsup_roalist :
"[^ x, y ^] = roalist_bsup x y"

instance sorry
end

instantiation roalist :: (linorder, Mergeable, Mergeable) Mergeableb
begin
instance proof qed
end

end
