theory Mergeable_Oalist imports "../Lib/Oalist/Oalist" "Mergeable"
begin

(* 
 * Mergeable instance for AList, the type of (ordered) association lists defined
 * in Gazelle/Lib/AList/AList.
 *)

(* Comparisons for the underlying data of ALists. Note that the first component
 * must be of the linorder class - a builtin Isabelle typeclass capturing linear
 * orderings. (We could have extended our hierarchy of typeclasses to include
 * linorder, but opted not to do so - however, a deeper integration of the linorder
 * axioms into other data types might necessitate this).
 *)
fun list_leq :: "(('a :: linorder) * ('b :: Pord)) list \<Rightarrow> ('a * 'b) list \<Rightarrow> bool"
  where
"list_leq [] _ = True"
| "list_leq ((a, b)#l1') l2 =
    (case map_of l2 a of
      None \<Rightarrow> False
      | Some b' \<Rightarrow> (pleq b b' \<and> list_leq l1' l2))"

lemma list_leqI :
  assumes Hord1 : "strict_order (map fst l1)"
  assumes Hord2 : "strict_order (map fst l2)"
  assumes H : "\<And> k v . (k, v) \<in> set l1 \<Longrightarrow> (\<exists> v' . (k, v') \<in> set l2 \<and> v <[ v')"
  shows "list_leq l1 l2" using Hord1 Hord2 H
proof(induction l1 arbitrary: l2)
  case Nil
  then show ?case by auto
next
  fix a :: "'a * 'b"
  fix l1 l2 :: "('a * 'b) list"
  assume HI1 :
    "(\<And>l2. strict_order (map fst l1) \<Longrightarrow>
              strict_order (map fst l2) \<Longrightarrow> 
              (\<And>k v. (k, v) \<in> set l1 \<Longrightarrow> \<exists>v'. (k, v') \<in> set l2 \<and> v <[ v') \<Longrightarrow>
              list_leq l1 l2)"
  assume HI2 :
       "strict_order (map fst (a # l1))"
  assume  HI3 :
       "strict_order (map fst l2)" 
  assume HI4 : "(\<And>k v. (k, v) \<in> set (a # l1) \<Longrightarrow> \<exists>v'. (k, v') \<in> set l2 \<and> v <[ v')"
  obtain ak and av where Ha : "a = (ak, av)" by (cases a; auto)
  have HI2' : "strict_order (map fst l1)" using Ha strict_order_tl[of ak "map fst l1"] HI2 by auto
  have Case1 : "(ak, av) \<in> set (a#l1)" using Ha by auto
  have Distinct1 : "distinct (ak # map fst l1)" using Ha strict_order_distinct[OF HI2] by auto
  have Case2 : "(\<And>k v. (k, v) \<in> set l1 \<Longrightarrow> \<exists>v'. (k, v') \<in> set l2 \<and> v <[ v')"
  proof -
    fix k v
    assume Helm : "(k, v) \<in> set l1"
    have Nota : "(k, v) \<noteq> a" using Distinct1 Ha Helm imageI[OF Helm, of fst] by(auto)
    then show "\<exists>v'. (k, v') \<in> set l2 \<and> v <[ v'" using Helm HI4[of k v] by(auto)
  qed
  have Distinct2 : "distinct (map fst l2)" using strict_order_distinct[OF HI3] by auto
  show "list_leq (a#l1) l2" using Ha
      HI1[OF HI2' HI3 Case2] Case1 HI4[of ak av] map_of_is_SomeI[OF Distinct2]
    by(auto split:option.splits)  
qed


lemma list_leqD :
  fixes l1 l2 :: "(('a :: linorder) * 'b :: Pord) list"
  fixes a :: "'a"
  fixes b :: "'b"
  assumes H : "list_leq l1 l2"
  assumes Hk : "(a, b) \<in> set l1"
  shows "\<exists> b' . b <[ b' \<and> (a, b') \<in> set l2"
  using H Hk
proof(induction l1 arbitrary:l2 a b)
  case Nil
  then show ?case by auto
next
  case (Cons x l1)
  then show ?case
    by(cases x; auto split:option.splits elim:map_of_SomeD)
qed

lemma strict_order_set_eq :
  assumes H1 : "strict_order (map fst l1)"
  assumes H2 : "strict_order (map fst l2)"
  assumes Hset : "set l1 = set l2"
  shows "l1 = l2" using H1 H2 Hset
proof(induction l1 arbitrary: l2)
  case Nil
  then show ?case by auto
next
  fix a :: "('a :: linorder * 'b)"
  obtain ak and av where Ha : "a = (ak, av)" by (cases a; auto)
  fix l1 l2 :: "('a * 'b) list"
  assume IH : "(\<And>l2. strict_order (map fst l1) \<Longrightarrow>
              strict_order (map fst l2) \<Longrightarrow> set l1 = set l2 \<Longrightarrow> l1 = l2)"
  assume Hord1 : "strict_order (map fst (a # l1))"
  have Hord1' : "strict_order (map fst l1)" using Hord1 strict_order_tl[of ak "map fst l1"] Ha by auto
  assume Hord2 : "strict_order (map fst l2)"
  assume Hset : "set (a # l1) = set l2" 
  show "a # l1 = l2"
  proof(cases l2)
    case Nil
    then show ?thesis using Hset by auto
  next
    case (Cons a2 l2')
    have Helm2 : "a \<in> set (l2)" using Hset by auto
    obtain a2k and a2v where Ha2 : "a2 = (a2k, a2v)" by (cases a2; auto)

    consider (1) "ak < a2k" |
             (2) "ak = a2k" |
             (3) "a2k < ak" using less_linear[of ak a2k] by auto
    then show ?thesis
    proof cases
      case 1
      have "ak \<noteq> a2k" using less_le 1 by auto
      hence "a \<noteq> a2" using Ha Ha2 by auto
      hence "a \<in> set l2'" using Hset Cons by auto
      then obtain j where "j < length l2'" "l2' ! j = a" using in_set_conv_nth[of a l2'] by(auto)
      hence "a2k < ak" using strict_order_unfold[OF Hord2, of "(1 + j)" 0] Cons Ha Ha2 by(auto)
      hence False using order.asym[OF 1] by auto
      then show ?thesis by auto
    next
      case 2
      hence Eq12 : "a = a2" using Ha Ha2 strict_order_distinct[OF Hord2] Cons Helm2 imageI[of a "set l2'" fst] by(auto)
      have Notin1 : "a2 \<notin> set l1" using strict_order_distinct[OF Hord1] Eq12 by(auto)
      have Notin2 : "a2 \<notin> set l2'" using strict_order_distinct[OF Hord2] Cons by auto

      have Hord2' : "strict_order (map fst l2')" using Hord2 strict_order_tl[of a2k "map fst l2'"] Cons Ha2 by(auto)

      have Hset' : "set l1 = set l2'" using Eq12 Notin1 Notin2 Cons Hset by(auto)
      show ?thesis using IH[OF Hord1' Hord2' Hset'] Cons Eq12 by auto
    next
      case 3
      have "ak \<noteq> a2k" using less_le 3 by auto
      hence "a \<noteq> a2" using Ha Ha2 by auto
      hence "a2 \<in> set (l1)" using Cons Hset by(auto)
      then obtain j where "j < length l1" "l1 ! j = a2" using in_set_conv_nth[of a2 l1] by(auto)
      hence "ak < a2k" using strict_order_unfold[OF Hord1, of "(1 + j)" 0] Cons Ha Ha2 by(auto)
      hence False using order.asym[OF 3] by auto
      then show ?thesis by  auto
    qed
  qed
qed

lemma list_leq_cons :
  fixes l1 l2 :: "(('a :: linorder) * ('b :: Pord)) list"
  fixes x :: "('a * 'b)"
  assumes H : "list_leq l1 l2"
  assumes Hx : "fst x \<notin> set (map fst l1)"
  shows  "list_leq l1 ((x)#l2)" using H Hx
proof(induction l1 arbitrary:l2 x)
  case Nil
  then show ?case by auto
next
  case (Cons a l1)
  then show ?case 
    by(cases a; auto split:option.splits)
qed

lemma list_leq_cons' :
  fixes l1 l2 :: "(('a :: linorder) * 'b :: Pord) list"
  fixes x :: "('a * 'b)"
  assumes H : "list_leq (x#l1) l2"
  shows  "list_leq l1 (l2)" using H
proof(induction l1 arbitrary:l2 x)
  case Nil
  then show ?case by auto
next
  case (Cons a l1)
  then show ?case 
    by(cases x; auto split:option.splits)
qed


lift_definition oalist_leq ::
  "('a :: linorder, 'b :: Pord) oalist \<Rightarrow> ('a, 'b) oalist \<Rightarrow> bool"
is list_leq .

instantiation oalist :: (linorder, Pord) Pord
begin

definition pleq_oalist :
"pleq l1 l2 = oalist_leq l1 l2"
instance proof
  fix l1 :: "('a :: linorder, 'b :: Pord) oalist"
  show "l1 <[ l1" unfolding pleq_oalist
  proof(transfer)
    fix l1' :: "('a :: linorder * 'b :: Pord) list"
    assume Hd : "strict_order (map fst l1')"
    show "list_leq l1' l1'" using Hd
    proof(induction l1')
      case Nil
      then show ?case by auto
    next
      case (Cons a t1)
      obtain ak and av where Ha : "a = (ak, av)" by(cases a; auto)
      then show ?case using Cons list_leq_cons[of t1 t1 "a"] strict_order_distinct[of "ak # map fst t1"]
        strict_order_tl[of ak "map fst t1"] 
        by( auto simp add:leq_refl)
    qed
  qed
next

  fix l1 l2 l3 :: "('a :: linorder, 'b :: Pord) oalist"
  assume H1 : "l1 <[ l2"
  assume H2 : "l2 <[ l3"
  show "l1 <[ l3" using H1 H2 unfolding pleq_oalist
  proof(transfer)
    fix l1 l2 l3 :: "('a * 'b) list"
    show "strict_order (map fst l1) \<Longrightarrow>
       strict_order (map fst l2) \<Longrightarrow> list_leq l1 l2 \<Longrightarrow> strict_order (map fst l3) \<Longrightarrow> list_leq l2 l3 \<Longrightarrow> list_leq l1 l3"
    proof(induction l1)
      case Nil
      then show ?case by auto
    next
      fix a :: "'a * 'b"
      fix l1 :: "('a * 'b) list"
      assume HI1 :
        "(strict_order (map fst l1) \<Longrightarrow> strict_order (map fst l2) \<Longrightarrow> 
        list_leq l1 l2 \<Longrightarrow> strict_order (map fst l3) \<Longrightarrow> 
        list_leq l2 l3 \<Longrightarrow> list_leq l1 l3)"
      assume HI2 :
        "strict_order (map fst (a # l1))"
      assume HI3 : "strict_order (map fst l2)" 
      assume HI4 : "list_leq (a # l1) l2" 
      assume HI5 : "strict_order (map fst l3)"  
      assume HI6 : "list_leq l2 l3"
      obtain a1k and a1v where Ha : "a = (a1k, a1v)" by(cases a; auto)
      hence Hleq12 : "list_leq l1 l2"  using HI4
        by(auto split:option.splits)
      obtain a2v where Ha2v : "(a1k, a2v) \<in> set l2" and Ha2vl:  "a1v <[ a2v"
        using Ha HI2 HI4 strict_order_distinct[of "a1k # map fst l1"]
              map_of_SomeD [of l2 a1k]
        by(auto split:option.splits elim:map_of_SomeD) 
      obtain a3v where Ha3v : "(a1k, a3v) \<in> set l3" and Ha3vl : "a2v <[ a3v"
        using Cons Ha list_leqD[OF HI6 Ha2v]
        by(auto split:option.splits)
      have Hav13 : "a1v <[ a3v" using leq_trans[OF Ha2vl Ha3vl] by auto
      have sto1 : "strict_order (map fst l1)" using strict_order_tl[of a1k "map fst l1"] Ha HI2 by(auto)
      show "list_leq (a # l1) l3" using Ha Ha3v Hav13
        map_of_is_SomeI[OF strict_order_distinct[OF HI5]] HI1[OF sto1 HI3 Hleq12 HI5 HI6]
        by auto
    qed
  qed
next

  fix l1 l2 :: "('a :: linorder, 'b ::Pord) oalist"
  assume H1 : "l1 <[ l2"
  assume H2 : "l2 <[ l1"
  show "l1 = l2" using H1 H2 unfolding pleq_oalist
  proof(transfer)
    fix l1' l2' :: "('a * 'b) list"
    assume Hord1 : "strict_order (map fst l1')"
    assume Hord2 : "strict_order (map fst l2')" 
    assume Hleq1 : "list_leq l1' l2'" 
    assume Hleq2 : "list_leq l2' l1'" 

    have Conc' : "set l1' = set l2'"
    proof(rule Set.equalityI; rule Set.subsetI)
      fix x :: "('a * 'b)"
      obtain xk and xv where Hx: "x = (xk, xv)" by(cases x; auto)
      assume H : "x \<in> set l1'"
      hence H' : "(xk, xv) \<in> set l1'" using Hx by auto
      obtain v' where  Elv' : "(xk, v') \<in> set l2'" and Leqv' : "xv <[ v'" using list_leqD[OF (*Hord1 Hord2*) Hleq1 H'] by auto
      obtain v'' where Elv'' : "(xk, v'') \<in> set l1'" and Leqv'' : "v' <[ v''" using list_leqD[OF (*Hord2 Hord1*) Hleq2 Elv'] by auto
      have Hord1_d : "distinct (map fst l1')" using strict_order_distinct[OF Hord1] by auto
      have H'' : "xk \<in> set (map fst l1')" using H' imageI[OF H', of fst] by(auto)
      obtain i1 where Hi11 : "i1 < length l1'" and Hi12 : "l1' ! i1 = (xk, xv)" using H' List.in_set_conv_nth[of "(xk, xv)" "l1'"] by auto 
      obtain i1' where Hi1'1 : "i1' < length l1'" and Hi1'2 :  "l1' ! i1' = (xk, v'')" using Elv'' List.in_set_conv_nth[of "(xk, v'')" "l1'"]
        by(auto)
      have "i1 = i1'" using Hi11 Hi12 Hi1'1 Hi1'2 List.distinct_Ex1[OF Hord1_d H''] by(auto)
      hence "v'' = xv" using Hi12 Hi1'2 by auto
      hence Leqv'2 : "v' <[ xv" using Leqv'' by auto
      hence "xv = v'" using leq_antisym[OF Leqv' Leqv'2] by auto
      thus "x \<in> set l2'" using Elv' Hx by auto
    next
      fix x :: "('a * 'b)"
      obtain xk and xv where Hx: "x = (xk, xv)" by(cases x; auto)
      assume H : "x \<in> set l2'"
      hence H' : "(xk, xv) \<in> set l2'" using Hx by auto
      obtain v' where  Elv' : "(xk, v') \<in> set l1'" and Leqv' : "xv <[ v'" using list_leqD[OF Hleq2 H'] by auto
      obtain v'' where Elv'' : "(xk, v'') \<in> set l2'" and Leqv'' : "v' <[ v''" using list_leqD[OF Hleq1 Elv'] by auto
      have Hord1_d : "distinct (map fst l2')" using strict_order_distinct[OF Hord2] by auto
      have H'' : "xk \<in> set (map fst l2')" using H' imageI[OF H', of fst] by(auto)
      obtain i1 where Hi11 : "i1 < length l2'" and Hi12 : "l2' ! i1 = (xk, xv)" using H' List.in_set_conv_nth[of "(xk, xv)" "l2'"] by auto 
      obtain i1' where Hi1'1 : "i1' < length l2'" and Hi1'2 :  "l2' ! i1' = (xk, v'')" using Elv'' List.in_set_conv_nth[of "(xk, v'')" "l2'"]
        by(auto)
      have "i1 = i1'" using Hi11 Hi12 Hi1'1 Hi1'2 List.distinct_Ex1[OF Hord1_d H''] by(auto)
      hence "v'' = xv" using Hi12 Hi1'2 by auto
      hence Leqv'2 : "v' <[ xv" using Leqv'' by auto
      hence "xv = v'" using leq_antisym[OF Leqv' Leqv'2] by auto
      thus "x \<in> set l1'" using Elv' Hx by auto
    qed

    show "l1' = l2'"  using strict_order_set_eq[OF Hord1 Hord2 Conc'] by auto 
  qed
qed
end

lemma distinct_unique_value :
  assumes Hd : "distinct (map fst l1)"
  assumes Hv : "(k, v) \<in> set l1"
  assumes Hv' : "(k, v') \<in> set l1"
  shows "v = v'"
proof(-)
  obtain i1 where Hi11 : "i1 < length l1" and Hi12 : "l1 ! i1 = (k, v)"
    using List.in_set_conv_nth[of "(k, v)" l1] Hv by auto
  obtain i1' where Hi1'1 : "i1' < length l1" and Hi1'2 : "l1 ! i1' = (k, v')"
    using List.in_set_conv_nth[of "(k, v')" l1] Hv' by auto
  have Hk : "k \<in> set (map fst l1)" using imageI[OF Hv, of fst] by auto
  hence "i1 = i1'" using List.distinct_Ex1[OF Hd Hk] Hi11 Hi1'1 Hi12 Hi1'2 by(auto)
  thus "v = v'" using Hi12 Hi1'2 by auto
qed

(* This lemma deserves a bit of explanation: it is used in the Pordc implementation for ALists.
 * This lemma (in combination with Isabelle's choice operators) allows us to pull
 * the list we need "out of thin air" at a key moment during that proof. (see list_complete, below)
 *)
lemma concretize_alist :
  fixes S :: "('a :: linorder * 'b) set"
  assumes Hfin : "finite S"
  assumes Nodup : 
     "\<And> k1 v1 v2 . (k1, v1) \<in> S \<Longrightarrow> (k1, v2) \<in> S \<Longrightarrow> v1 = v2"
   shows "\<exists> l . strict_order (map fst l) \<and> set l = S" using Hfin Nodup
proof(induction "card (S :: ('a * 'b) set)" arbitrary: S)
  case 0
  then show ?case by(auto simp add:strict_order_def)
next
  fix x :: nat
  fix S :: "('a :: linorder * 'b) set"
  assume IH :
  "(\<And>(S :: ('a * 'b) set). x = card S \<Longrightarrow> finite S \<Longrightarrow>
      (\<And>k1 v1 v2. (k1, v1) \<in> S \<Longrightarrow> (k1, v2) \<in> S \<Longrightarrow> v1 = v2) \<Longrightarrow>
    \<exists>l. strict_order (map fst l) \<and> set l = S)"
  assume Hsuc : "Suc x = card S"
  hence Nonemp : "S \<noteq> {}" by auto
  hence Nonemp' : "(fst ` S) \<noteq> {}" by auto
  assume Hfin: "finite S"
  hence Hfin' : "finite (fst ` S)" by auto
  assume Hnodup : "(\<And>k1 v1 v2. (k1, v1) \<in> S \<Longrightarrow> (k1, v2) \<in> S \<Longrightarrow> v1 = v2)"

  obtain kl vl where Hkvl : "(kl,vl) \<in> S" and Hkl_min : "kl = Min (fst ` S)" 
    using linorder_class.Min_in[OF Hfin' Nonemp']
    by(auto)

  have Hkl_in : "kl \<in> (fst ` S)" using Hkvl imageI[OF Hkvl, of fst] by auto

  have Hcard : "x = card (S - {(kl, vl)})" using card_Diff_singleton[OF Hfin Hkvl] Hsuc by auto
  have Hfin'' : "finite (S - {(kl, vl)})" using Hfin by auto
  have Hnodup' : "(\<And>k1 v1 v2. (((k1, v1) \<in> S - {(kl, vl)}) \<Longrightarrow> ((k1, v2) \<in> S - {(kl, vl)}) \<Longrightarrow> v1 = v2))"
    using Hnodup
    by(auto)

  obtain tl where
    Hord_tl : "strict_order (map fst tl)" and Hset_tl : "set tl = (S - {(kl, vl)})"
    using IH[of "S - {(kl, vl)}", OF Hcard Hfin'' Hnodup'] by(fastforce)

  have Conc1 : "strict_order (map fst ((kl, vl) # tl))"
  proof(rule strict_order_intro)
    fix i j
    assume Hlen : "j < length (map fst ((kl, vl) # tl))"
    assume Hij : "i < j"
    obtain j' where Hj' : "j = 1 + j'" using Hij by (cases j; auto)

    have In_j1 : "tl ! j' \<in> set tl" using Hj' Hlen
      by(auto)
    hence In_j2 : "tl ! j' \<in> S" using Hset_tl
      by(auto)
    obtain k' v' where Hk'v': "tl ! j' = (k', v')" by (cases "tl ! j'"; auto)
    have In_j2_fst : "k' \<in> fst ` S" using imageI[OF In_j2, of fst] Hk'v' by auto
    have Kl_leq : "kl \<le> k'" using Hkl_min Min_le[OF Hfin' In_j2_fst] by(auto)
    have Kl_neq : "kl \<noteq> k'"
    proof(cases "kl = k'")
      case False thus ?thesis by auto next
      case True
      hence "(kl, vl) = (k', v')" using Hnodup[OF Hkvl, of v'] Hk'v' In_j2 by(auto)
      hence False using Hset_tl In_j1 Hk'v' by(auto)
      thus ?thesis by auto
    qed

    show "map fst ((kl, vl) # tl) ! i < map fst ((kl, vl) # tl) ! j"
    proof(cases i)
      case 0
      hence Conc1' : "kl < k'" using Kl_leq Kl_neq by auto
      have Conc2' : "map fst tl ! j' = k'" using Hj' Hk'v' Hlen by(auto)
      thus ?thesis using 0 Conc1' Hk'v' Hj'  by(auto)
    next
      fix i'
      assume Hi' : "i = Suc i'"
      hence Hlen_i' : "i' < length tl" using Hij Hlen by auto
      have Hi'j' : "i' < j'" using Hij Hi' Hj' by auto
      obtain k'i v'i where Hk'iv'i: "tl ! i' = (k'i, v'i)" by (cases "tl ! i'"; auto)
      have Hlen' : "j' < length (map fst tl)" using Hj' Hlen by auto
      have Conc' : "map fst (tl) ! i' < map fst (tl)! j'"
        using strict_order_unfold[OF Hord_tl Hlen' Hi'j'] by auto
      thus "map fst ((kl, vl) # tl) ! i < map fst ((kl, vl) # tl) ! j" using Hi' Hj' by auto
    qed
  qed

  have Conc2 : "set ((kl, vl) # tl) = S" using Hset_tl Set.insert_absorb[OF Hkvl] by auto

  have Conc : "strict_order (map fst ((kl, vl) # tl) ) \<and> set ((kl, vl) # tl)  = S"
    using Conc1 Conc2 by auto

  thus "\<exists>l. strict_order (map fst l) \<and> set l = S" by blast
qed

lemma list_complete :
  fixes l1 l2 ub :: "('a :: linorder * 'b :: Pordc) list"
  assumes Hord1 : "strict_order (map fst l1)"
  assumes Hord2 : "strict_order (map fst l2)"
  assumes Hordub : "strict_order (map fst ub)"
  assumes Hlt_1 : "list_leq l1 ub"
  assumes Hlt_2 : "list_leq l2 ub"
  shows "\<exists> sup . list_leq l1 sup \<and> list_leq l2 sup \<and> strict_order (map fst sup) \<and>
           (\<forall> ub' . strict_order (map fst ub') \<longrightarrow> list_leq l1 ub' \<longrightarrow> list_leq l2 ub' \<longrightarrow> list_leq sup ub')" using Hord1 Hord2 Hordub Hlt_1 Hlt_2
proof -

  (* S1 is the set of (key, value) pairs where the key is unique to l1;
   * S2 is the analogue but for l2 *)
  obtain S1 :: "('a * 'b) set" where S1def : "S1 = { kv . kv \<in> set (l1) \<and> fst kv \<notin> set (map fst l2) }"
    by auto
  obtain S2 :: "('a * 'b) set" where S2def : "S2 = { kv . fst kv \<notin> set (map fst l1) \<and> kv \<in> set (l2) }"
    by auto

  (* For overlapping keys, derive the existence of a supremum (using the fact that 'b
   * admits a complete partial order *)
  have Sups : "\<And> k v1 v2 .
                (k, v1) \<in> set l1 \<Longrightarrow>
                (k, v2) \<in> set l2 \<Longrightarrow>
                (\<exists>! sup . is_sup {v1, v2} sup)"
  proof(-)
    fix k v1 v2
    assume H1 : "(k, v1) \<in> set l1"
    assume H2 : "(k, v2) \<in> set l2"
    obtain vub where Hvub : "v1 <[ vub" and Helm : "(k, vub) \<in> set ub"
      using list_leqD[OF Hlt_1 H1] by auto
    obtain vub' where Hvub' : "v2 <[ vub'" and Helm' : "(k, vub') \<in> set ub"
      using list_leqD[OF Hlt_2 H2] by auto
    have "vub = vub'" using
      distinct_unique_value[OF strict_order_distinct[OF Hordub] Helm Helm'] by auto
    hence "has_ub {v1, v2}" using Hvub Hvub' by(auto simp add: is_ub_def has_ub_def)
    then obtain vsup where Hvsup : "is_sup {v1, v2} vsup" using complete2[of v1 v2]
      by (auto simp add:has_sup_def)

    hence "\<exists> sup . is_sup {v1, v2} sup" by auto

    thus "\<exists>!sup. is_sup {v1, v2} sup" using is_sup_unique[of "{v1, v2}", OF Hvsup] by(auto)
  qed

  (* A (non-computable) function giving us supremum of values from l1 and l2 for overlapping keys *)
  obtain f :: "'a \<Rightarrow> ('a * 'b)" where
    Hf : "f = (\<lambda> a . (a, THE b . (\<forall> v1 v2 . ((a, v1) \<in> set l1 \<longrightarrow> 
                                    (a, v2) \<in> set l2 \<longrightarrow> is_sup {v1, v2} b))))"
    by(auto)

  obtain S12k :: "'a set" where S12kdef :
      "S12k = { k . k \<in> set (map fst l1) \<and> k \<in> set (map fst l2) }" by auto

  hence Fin12k : "finite S12k" by auto

  obtain S12 :: "('a * 'b) set" where
    S12def : "S12 = f ` S12k"  by auto

  have Fin12 : "finite S12"  unfolding S12def
  proof(rule finite_imageI)
    show "finite S12k" using Fin12k by auto
  qed

  have Fin1 : "finite S1" using S1def by(auto)
  have Fin2 : "finite S2" using S2def by(auto)

  have Fin : "finite (S1 \<union> S2 \<union> S12)" using Fin12 Fin1 Fin2 by auto

  have l1dist : "distinct (map fst l1)" using strict_order_distinct[OF Hord1] by auto
  have l2dist : "distinct (map fst l2)" using strict_order_distinct[OF Hord2] by auto
  have ubdist : "distinct (map fst ub)" using strict_order_distinct[OF Hordub] by auto

  have Nodup :
     "\<And> k1 v1 v2 . (k1, v1) \<in> S1 \<union> S2 \<union> S12 \<Longrightarrow> (k1, v2) \<in> S1 \<union> S2 \<union> S12 \<Longrightarrow> v1 = v2"
  proof -
    fix k1 :: 'a
    fix v1 v2 :: 'b
    assume Hin1 : "(k1, v1) \<in> S1 \<union> S2 \<union> S12"
    assume Hin2 : "(k1, v2) \<in> S1 \<union> S2 \<union> S12"

    consider (1) "(k1, v1) \<in> S1" "(k1, v2) \<in> S1" |
             (2) "(k1, v1) \<in> S1" "(k1, v2) \<in> S2" |
             (3) "(k1, v1) \<in> S1" "(k1, v2) \<in> S12" |
             (4) "(k1, v1) \<in> S2" "(k1, v2) \<in> S1" |
             (5) "(k1, v1) \<in> S2" "(k1, v2) \<in> S2" |
             (6) "(k1, v1) \<in> S2" "(k1, v2) \<in> S12" |
             (7) "(k1, v1) \<in> S12" "(k1, v2) \<in> S1" |
             (8) "(k1, v1) \<in> S12" "(k1, v2) \<in> S2" |
             (9) "(k1, v1) \<in> S12" "(k1, v2) \<in> S12" using Hin1 Hin2 by auto
    then show "v1 = v2"
    proof cases
      case 1
      then show ?thesis unfolding S1def using distinct_unique_value[OF l1dist, of k1 v1 v2] by auto
    next
      case 2
      then show ?thesis unfolding S1def S2def using imageI[of "(k1, v1)" "set l1" fst] by(auto)
    next
      case 3
      then show ?thesis unfolding S1def S12def S12kdef Hf by(auto)
    next
      case 4
      then show ?thesis unfolding S1def S2def using imageI[of "(k1, v2)" "set l1" fst] by(auto)
    next
      case 5
      then show ?thesis unfolding S2def using distinct_unique_value[OF l2dist, of k1 v1 v2] by auto
    next
      case 6
      then show ?thesis unfolding S2def S12def S12kdef Hf by(auto)
    next
      case 7
      then show ?thesis unfolding S1def S12def S12kdef Hf by(auto)
    next
      case 8
      then show ?thesis unfolding S2def S12def S12kdef Hf by(auto)
    next
      case 9
      then show ?thesis unfolding S1def S12def S12kdef Hf by(auto)
    qed
  qed

  (* Use concretize_alist to pull the supremum "out of thin air" *)
  obtain lsup where Hlsup_ord : "strict_order (map fst lsup)" 
    and Hlsup_S : "set lsup = S1 \<union> S2 \<union> S12"
    using concretize_alist[OF Fin Nodup] by fastforce

  have Conc1 : "list_leq l1 lsup"
  proof(rule list_leqI[OF Hord1 Hlsup_ord])
    fix k :: 'a
    fix v :: 'b
    assume H : "(k, v) \<in> set l1"
    consider
      (1) "(k) \<in> fst ` S1" | (2) "k \<in> S12k" unfolding S1def S12kdef using imageI[OF H, of fst] by(auto)
    then show "\<exists>v'::'b. (k, v') \<in> set lsup \<and> v <[ v'"
    proof cases
      case 1
      hence Conc1 : "(k, v) \<in> set lsup" using H by(auto simp add:Hlsup_S S1def S12def S12kdef Hf)
      have Conc2 : "v <[ v" by(simp add:leq_refl)
      then show ?thesis using Conc1 by auto
    next
      case 2
      then obtain v' where Hv' : "(k, v') \<in>  S12" by(auto simp add:Hlsup_S S1def S12def S12kdef Hf)
      obtain v2 where Hv2 : "(k, v2) \<in> set l2" using 2 by(auto simp add:Hlsup_S S2def S1def S12def S12kdef Hf)
      have Conc1 : "(k, v') \<in> set lsup" using Hv' by(auto simp add:Hlsup_S S1def S12def S12kdef Hf)
      obtain sup  where Hsup : "is_sup {v, v2} sup" using Sups[OF H Hv2] by auto

      have Char1 : "\<And> sup' . (\<And> vc1 vc2. (k, vc1) \<in> set l1 \<Longrightarrow>  (k, vc2) \<in> set l2 \<Longrightarrow> is_sup {vc1, vc2} sup') \<Longrightarrow> sup' = sup"
      proof-
        fix sup' 
        assume CH :"(\<And> vc1 vc2. (k, vc1) \<in> set l1 \<Longrightarrow>  (k, vc2) \<in> set l2 \<Longrightarrow> is_sup {vc1, vc2} sup')"
        show "sup' = sup" using is_sup_unique[OF Hsup, of sup'] CH[OF H Hv2] by auto
      qed

      hence Char1' : "\<And> sup' . (\<forall>v1::'b. (k, v1) \<in> set l1 \<longrightarrow> (\<forall>v2::'b. (k, v2) \<in> set l2 \<longrightarrow> is_sup {v1, v2} sup')) \<Longrightarrow> sup' = sup"
        by( auto)

      have Char2 : "\<And> vc1 vc2 . (k, vc1) \<in> set l1 \<Longrightarrow> (k, vc2) \<in> set l2 \<Longrightarrow> is_sup {vc1, vc2} sup"
      proof-
        fix vc1 vc2
        assume CH1 : "(k, vc1) \<in> set l1"
        have CC1 : "vc1 = v" using distinct_unique_value[OF l1dist H CH1] by auto
        assume CH2 : "(k, vc2) \<in> set l2"
        have CC2 : "vc2 = v2" using distinct_unique_value[OF l2dist Hv2 CH2] by auto
        thus "is_sup {vc1, vc2} sup" using Hsup CC1 CC2 by auto
      qed

      have Char2' : "\<forall>v1::'b. (k, v1) \<in> set l1 \<longrightarrow> (\<forall>v2::'b. (k, v2) \<in> set l2 \<longrightarrow> is_sup {v1, v2} sup)" using Char2
        by(auto)

      have "v' = sup" using 
        the_equality[of "\<lambda> sup' . \<forall>v1::'b. (k, v1) \<in> set l1 \<longrightarrow> (\<forall>v2::'b. (k, v2) \<in> set l2 \<longrightarrow> is_sup {v1, v2} sup')" sup
                    , OF Char2' Char1'] 2 H Hv' Hv2
        by(auto simp add:Hlsup_S S1def S12def S12kdef Hf)

      hence Conc2 : "v <[ v'" using Hsup by(auto simp add:is_sup_def is_least_def is_ub_def)

      thus ?thesis using Conc1 by auto
    qed
  qed

  have Conc2 : "list_leq l2 lsup"
  proof(rule list_leqI[OF Hord2 Hlsup_ord])
    fix k :: 'a
    fix v :: 'b
    assume H : "(k, v) \<in> set l2"
    consider
      (1) "(k) \<in> fst ` S2" | (2) "k \<in> S12k" unfolding S2def S12kdef using imageI[OF H, of fst] by(auto)
    then show "\<exists>v'::'b. (k, v') \<in> set lsup \<and> v <[ v'"
    proof cases
      case 1
      hence Conc1 : "(k, v) \<in> set lsup" using H by(auto simp add:Hlsup_S S2def S12def S12kdef Hf)
      have Conc2 : "v <[ v" by(simp add:leq_refl)
      then show ?thesis using Conc1 by auto
    next
      case 2
      then obtain v' where Hv' : "(k, v') \<in>  S12" by(auto simp add:Hlsup_S S1def S12def S12kdef Hf)
      obtain v1 where Hv1 : "(k, v1) \<in> set l1" using 2 by(auto simp add:Hlsup_S S2def S1def S12def S12kdef Hf)
      have Conc1 : "(k, v') \<in> set lsup" using Hv' by(auto simp add:Hlsup_S S1def S12def S12kdef Hf)
      obtain sup  where Hsup : "is_sup {v1, v} sup" using Sups[OF Hv1 H] by auto

      have Char1 : "\<And> sup' . (\<And> vc1 vc2. (k, vc1) \<in> set l1 \<Longrightarrow>  (k, vc2) \<in> set l2 \<Longrightarrow> is_sup {vc1, vc2} sup') \<Longrightarrow> sup' = sup"
      proof-
        fix sup' 
        assume CH :"(\<And> vc1 vc2. (k, vc1) \<in> set l1 \<Longrightarrow>  (k, vc2) \<in> set l2 \<Longrightarrow> is_sup {vc1, vc2} sup')"
        show "sup' = sup" using is_sup_unique[OF Hsup, of sup'] CH[OF Hv1 H] by auto
      qed

      hence Char1' : "\<And> sup' . (\<forall>v1::'b. (k, v1) \<in> set l1 \<longrightarrow> (\<forall>v2::'b. (k, v2) \<in> set l2 \<longrightarrow> is_sup {v1, v2} sup')) \<Longrightarrow> sup' = sup"
        by( auto)

      have Char2 : "\<And> vc1 vc2 . (k, vc1) \<in> set l1 \<Longrightarrow> (k, vc2) \<in> set l2 \<Longrightarrow> is_sup {vc1, vc2} sup"
      proof-
        fix vc1 vc2
        assume CH1 : "(k, vc1) \<in> set l1"
        have CC1 : "vc1 = v1" using distinct_unique_value[OF l1dist Hv1 CH1] by auto
        assume CH2 : "(k, vc2) \<in> set l2"
        have CC2 : "vc2 = v" using distinct_unique_value[OF l2dist H CH2] by auto
        thus "is_sup {vc1, vc2} sup" using Hsup CC1 CC2 by auto
      qed

      have Char2' : "\<forall>v1::'b. (k, v1) \<in> set l1 \<longrightarrow> (\<forall>v2::'b. (k, v2) \<in> set l2 \<longrightarrow> is_sup {v1, v2} sup)" using Char2
        by(auto)

      have "v' = sup" using 
        the_equality[of "\<lambda> sup' . \<forall>v1::'b. (k, v1) \<in> set l1 \<longrightarrow> (\<forall>v2::'b. (k, v2) \<in> set l2 \<longrightarrow> is_sup {v1, v2} sup')" sup
                    , OF Char2' Char1'] 2 H Hv' Hv1
        by(auto simp add:Hlsup_S S1def S12def S12kdef Hf)

      hence Conc2 : "v <[ v'" using Hsup by(auto simp add:is_sup_def is_least_def is_ub_def)

      thus ?thesis using Conc1 by auto
    qed
  qed

  have Conc3 : "strict_order (map fst lsup)" using Hlsup_ord by auto

  have Conc4 : "\<And> ub' . strict_order (map fst ub') \<Longrightarrow> list_leq l1 ub' \<Longrightarrow> list_leq l2 ub' \<Longrightarrow> list_leq lsup ub'"
  proof -
    fix ub' :: "('a * 'b) list"
    assume Hordub' : "strict_order (map fst ub')"
    assume Hl1 : "list_leq l1 ub'"
    assume Hl2 : "list_leq l2 ub'"
    show "list_leq lsup ub'"
    proof(rule list_leqI[OF Hlsup_ord Hordub'])
      fix k :: 'a
      fix v :: 'b
      assume Hkvin : "(k, v) \<in> set lsup"
      then consider (1) "(k, v) \<in> S1" |
                    (2) "(k, v) \<in> S2" |
                    (3) "(k, v) \<in> S12" using Hlsup_S by auto
      then show "\<exists>v'::'b. (k, v') \<in> set ub' \<and> v <[ v'"
      proof cases
        case 1
        then show ?thesis using list_leqD[OF Hl1, of k v] by(auto simp add:S1def)
      next
        case 2
        then show ?thesis using list_leqD[OF Hl2, of k v] by(auto simp add:S2def)
      next
        case 3
        obtain v1 where Hv1 : "(k, v1) \<in> set l1"  using 3 by(auto simp add:Hlsup_S S2def S1def S12def S12kdef Hf)
        obtain v2 where Hv2 : "(k, v2) \<in> set l2" using 3 by(auto simp add:Hlsup_S S2def S1def S12def S12kdef Hf)

        obtain v'1 where Conc1 : "(k, v'1) \<in> set ub'" and V'_gt_1 : "v1 <[ v'1" using list_leqD[OF Hl1 Hv1] by(auto)
        obtain v'2 where Conc1' : "(k, v'2) \<in> set ub'" and V'_gt_2 : "v2 <[ v'2" using list_leqD[OF Hl2 Hv2] by(auto)

        have Hv'1v'2 : "v'1 = v'2" using 
          distinct_unique_value[OF strict_order_distinct[OF Hordub'] Conc1 Conc1'] by auto

        have Hub : "is_ub {v1, v2} v'1" using Conc1 V'_gt_1 V'_gt_2 Hv'1v'2 by(auto simp add:is_ub_def)

        obtain sup  where Hsup : "is_sup {v1, v2} sup" using Sups[OF Hv1 Hv2] by auto
  
        have Char1 : "\<And> sup' . (\<And> vc1 vc2. (k, vc1) \<in> set l1 \<Longrightarrow>  (k, vc2) \<in> set l2 \<Longrightarrow> is_sup {vc1, vc2} sup') \<Longrightarrow> sup' = sup"
        proof-
          fix sup' 
          assume CH :"(\<And> vc1 vc2. (k, vc1) \<in> set l1 \<Longrightarrow>  (k, vc2) \<in> set l2 \<Longrightarrow> is_sup {vc1, vc2} sup')"
          show "sup' = sup" using is_sup_unique[OF Hsup, of sup'] CH[OF Hv1 Hv2] by auto
        qed
  
        hence Char1' : "\<And> sup' . (\<forall>v1::'b. (k, v1) \<in> set l1 \<longrightarrow> (\<forall>v2::'b. (k, v2) \<in> set l2 \<longrightarrow> is_sup {v1, v2} sup')) \<Longrightarrow> sup' = sup"
          by( auto)
  
        have Char2 : "\<And> vc1 vc2 . (k, vc1) \<in> set l1 \<Longrightarrow> (k, vc2) \<in> set l2 \<Longrightarrow> is_sup {vc1, vc2} sup"
        proof-
          fix vc1 vc2
          assume CH1 : "(k, vc1) \<in> set l1"
          have CC1 : "vc1 = v1" using distinct_unique_value[OF l1dist Hv1 CH1] by auto
          assume CH2 : "(k, vc2) \<in> set l2"
          have CC2 : "vc2 = v2" using distinct_unique_value[OF l2dist Hv2 CH2] by auto
          thus "is_sup {vc1, vc2} sup" using Hsup CC1 CC2 by auto
        qed
  
        have Char2' : "\<forall>v1::'b. (k, v1) \<in> set l1 \<longrightarrow> (\<forall>v2::'b. (k, v2) \<in> set l2 \<longrightarrow> is_sup {v1, v2} sup)" using Char2
          by(auto)
  
        have "v = sup" using 
          the_equality[of "\<lambda> sup' . \<forall>v1::'b. (k, v1) \<in> set l1 \<longrightarrow> (\<forall>v2::'b. (k, v2) \<in> set l2 \<longrightarrow> is_sup {v1, v2} sup')" sup
                      , OF Char2' Char1'] 3 Hv1 Hv2
          by(auto simp add:Hlsup_S S1def S12def S12kdef Hf)
  
        hence Conc2 : "v <[ v'1" using is_supD2[OF Hsup Hub] by(auto)
  
        thus ?thesis using Conc1 by auto
      qed
    qed
  qed

  show " \<exists>sup::('a \<times> 'b) list. list_leq l1 sup \<and> list_leq l2 sup \<and> strict_order (map fst sup) \<and> (\<forall>ub'::('a \<times> 'b) list. strict_order (map fst ub') \<longrightarrow> list_leq l1 ub' \<longrightarrow> list_leq l2 ub' \<longrightarrow> list_leq sup ub')"
    using Conc1 Conc2 Conc3 Conc4 by auto
qed


instantiation oalist :: (linorder, Pordc) Pordc
begin

instance proof
  fix a b :: "('a :: linorder, 'b :: Pordc) oalist"
  assume H : "has_ub {a, b}"
(*
  then obtain ub where H : "is_ub {a, b} ub" by (auto simp add:has_ub_def)
*)

  show "has_sup {a, b}" using H unfolding has_ub_def has_sup_def is_sup_def is_least_def is_ub_def pleq_oalist
  proof(transfer)
    fix a b :: "('a :: linorder * 'b :: Pordc) list"
    assume Hord_a : "strict_order (map fst a)"
    assume Hord_b : "strict_order (map fst b)"
    assume Hub : "\<exists>aa\<in>{xs. strict_order (map fst xs)}. \<forall>x\<in>{a, b}. list_leq x aa"
    then obtain ub where Hord_ub : "strict_order (map fst ub)" and Hub' : "\<forall>x\<in>{a, b}. list_leq x ub" by auto
    have Hlt_a : "list_leq a ub" using Hub' by auto
    have Hlt_b : "list_leq b ub" using Hub' by auto

    show "\<exists>aa\<in>{xs. strict_order (map fst xs)}.
              (\<forall>x\<in>{a, b}. list_leq x aa) \<and>
              (\<forall>a'\<in>{xs. strict_order (map fst xs)}.
                  (\<forall>x\<in>{a, b}. list_leq x a') \<longrightarrow> list_leq aa a')"
      using list_complete[OF Hord_a Hord_b Hord_ub Hlt_a Hlt_b]
      by(auto)
  qed
qed
end

(* ALists always have a least element - namely, the empty list *)
instantiation oalist :: (linorder, Pord) Pordb
begin
  definition bot_oalist :
    "\<bottom> = empty"

instance proof
  fix a :: "('a :: linorder, 'b :: Pord) oalist"
  show "\<bottom> <[ a" unfolding bot_oalist pleq_oalist
    by(transfer; auto)
qed
end

fun list_bsup :: "('a :: linorder * 'b :: Mergeable) list \<Rightarrow> ('a * 'b) list \<Rightarrow> ('a * 'b) list" where
"list_bsup l1 [] = l1"
| "list_bsup l1 ((k2, v2)#l2t) =
   (case map_of l1 k2 of
      None \<Rightarrow> list_bsup (str_ord_update k2 v2 l1) l2t
      | Some v1 \<Rightarrow> list_bsup (str_ord_update k2 (bsup v1 v2) l1) l2t)"

lemma list_bsup_correct :
  fixes l1 l2 :: "(('a :: linorder) * ('b :: Mergeable)) list"
  assumes Hord1 :  "strict_order (map fst l1)"
  assumes Hord2 :  "strict_order (map fst l2)"
  shows "strict_order (map fst (list_bsup l1 l2))" using Hord1 Hord2
  proof(induction l2 arbitrary:l1)
    case Nil
    then show ?case by auto
  next
    fix h2 :: "('a :: linorder * 'b :: Mergeable)"
    obtain k2 v2 where Hh2 : "h2 = (k2, v2)" by(cases h2; auto)
    fix l2t l1 :: "('a * 'b) list"
    assume HI : "(\<And>l1::('a \<times> 'b) list.
             strict_order (map fst l1) \<Longrightarrow>
             strict_order (map fst l2t) \<Longrightarrow> strict_order (map fst (list_bsup l1 l2t)))"
    assume Hord1 : "strict_order (map fst l1)"
    assume Hord2 : "strict_order (map fst (h2#l2t))"
    hence Hord2t : "strict_order (map fst l2t)" using Hh2 strict_order_tl[of k2 "map fst l2t"] by auto

    show "strict_order (map fst (list_bsup l1 (h2#l2t)))"
    proof(cases "map_of l1 k2")
      case None
      have Hord1' : "strict_order (map fst (str_ord_update k2 v2 l1))"
        using str_ord_update_correct[OF Hord1, of k2 v2] by auto
      have "strict_order (map fst (list_bsup (str_ord_update k2 v2 l1) l2t))"
        using HI[OF Hord1' Hord2t] by auto
      thus ?thesis using None Hh2 by(auto)
    next
      case (Some v1)
      have Hord1' : "strict_order (map fst (str_ord_update k2 [^ v1, v2 ^] l1))"
        using str_ord_update_correct[OF Hord1, of k2 "[^ v1, v2 ^]"] by auto
      have "strict_order (map fst (list_bsup (str_ord_update k2 [^ v1, v2 ^] l1) l2t))"
        using HI[OF Hord1' Hord2t] by auto
      then show ?thesis using Some Hh2 by(auto)
    qed
  qed

lift_definition oalist_bsup :: "('a :: linorder, 'b :: Mergeable) oalist \<Rightarrow> ('a, 'b) oalist \<Rightarrow> ('a, 'b) oalist"
is list_bsup
proof -
  fix l1 l2 :: "('a :: linorder * 'b :: Mergeable) list"
  assume Hord1 :  "strict_order (map fst l1)"
  assume Hord2 :  "strict_order (map fst l2)"
  show "strict_order (map fst (list_bsup l1 l2))"
    using list_bsup_correct[OF Hord1 Hord2] by auto
qed

lemma list_leq_refl :
  fixes a :: "('a :: linorder * 'b :: Pord) list"
  assumes Horda : "strict_order (map fst a)"
  shows "list_leq a a"
  by(rule list_leqI[OF Horda Horda]; auto simp add:leq_refl)

lemma str_ord_update_inD :
  fixes k k' :: "'a :: linorder"
  fixes v v' :: "'b"
  fixes l :: "('a * 'b) list"
  assumes Hord : "strict_order (map fst l)"
  assumes Hk'v' : "(k', v') \<in> set (str_ord_update k v l)"
  shows "(k = k' \<and> v = v') \<or>
         ((k', v') \<in> set l)" using Hord Hk'v'
proof(induction l arbitrary: k v k' v')
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  obtain ak av where Ha : "a = (ak, av)" by(cases a; auto)
  have Hord' : "strict_order (map fst l)" using Cons Ha strict_order_tl[of ak "map fst l"] by auto
  show ?case using Cons.prems Cons.IH[OF Hord']  Ha by(auto split:if_splits)
qed

lemma str_ord_update_inD' :
  fixes k k' :: "'a :: linorder"
  fixes v v' :: "'b :: Pord"
  fixes l :: "('a * 'b) list"
  assumes Hord : "strict_order (map fst l)"
  assumes Hk'v' : "(k', v') \<in> set (str_ord_update k v l)"
  assumes Hneq : "k \<noteq> k'"
  shows "(k', v') \<in> set l" using Hord Hk'v' Hneq
proof(induction l arbitrary: k v k' v')
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  obtain ak av where Ha : "a = (ak, av)" by(cases a; auto)
  have Hord' : "strict_order (map fst l)" using Cons Ha strict_order_tl[of ak "map fst l"] by auto
  show ?case using Cons.prems Cons.IH[OF Hord']  Ha by(auto split:if_splits)
qed


lemma str_ord_update_inI1 :
  fixes k  :: "'a :: linorder"
  fixes v  :: "'b"
  fixes l :: "('a * 'b) list"
  assumes Hord : "strict_order (map fst l)"
  shows "(k, v) \<in> set (str_ord_update k v l)" using Hord 
proof(induction l)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  obtain ak av where Ha : "a = (ak, av)" by(cases a; auto)
  have Hord' : "strict_order (map fst l)" using Cons Ha strict_order_tl[of ak "map fst l"] by auto
  then show ?case using Cons.prems Cons.IH[OF Hord'] Ha
    by(auto split:if_splits)
qed  

lemma str_ord_update_inI2 :
  fixes k k'  :: "'a :: linorder"
  fixes v v' :: "'b"
  fixes l :: "('a * 'b) list"
  assumes Hord : "strict_order (map fst l)"
  assumes Hneq : "k \<noteq> k'"
  assumes Hin : "(k', v') \<in> set l"
  shows "(k', v') \<in> set (str_ord_update k v l)" using Hord Hneq Hin
proof(induction l)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  obtain ak av where Ha : "a = (ak, av)" by(cases a; auto)
  have Hord' : "strict_order (map fst l)" using Cons Ha strict_order_tl[of ak "map fst l"] by auto
  then show ?case using Cons.prems Cons.IH[OF Hord'] Ha
    by(auto split:if_splits)
qed

lemma get_update :
  fixes k :: "'a :: linorder"
  fixes v :: "'b"
  fixes l :: "('a, 'b) oalist"
  shows "get (update k v l) k = Some v"
proof(transfer)
  fix k :: "'a :: linorder"
  fix v :: "'b"
  fix l :: "('a * 'b) list"
  assume Hord : "strict_order (map fst l)"
  show "map_of (str_ord_update k v l) k = Some v"
    using str_ord_update_inI1[OF Hord, of k v] 
      map_of_eq_Some_iff[OF 
        strict_order_distinct[OF str_ord_update_correct[OF Hord, of k v]], of k v] by auto
qed


lemma list_bsup_disj_key1 :
  fixes k :: "'a :: linorder"
  fixes v :: "'b :: Mergeable"
  fixes a b :: "('a * 'b) list"
  assumes Hord1 : "strict_order (map fst a)"
  assumes Hord2 : "strict_order (map fst b)"
  assumes H1 : "(k, v) \<in> set a"
  assumes H2 : "k  \<notin> set (map fst b)"
  shows "(k, v) \<in> set (list_bsup a b)" using Hord1 Hord2 H1 H2
proof(induction b arbitrary: a)
  case Nil
  then show ?case
    by auto
next
  case (Cons bh bt)
  obtain bk and bv where Hbkv : "bh = (bk, bv)" by (cases bh; auto)
  have Hord2' : "strict_order (map fst bt)" using Hbkv strict_order_tl[of bk "map fst bt"] Cons.prems(2) by auto
  have Kbk_neq : "bk \<noteq> k" using Hbkv Cons.prems(4) by(auto)
  have Kbk_notin : "k \<notin> set (map fst bt)" using Hbkv Cons.prems(4) by(auto)

  have  H2' : "k \<notin> set (map fst bt)" using Cons.prems by auto
  then show ?case
  proof(cases "map_of a bk")
    case None
    have Ord_up : "strict_order (map fst (str_ord_update bk bv a))"
      using str_ord_update_correct[OF Cons.prems(1), of bk bv] by auto
    have Ord_bsup : "strict_order (map fst (list_bsup (str_ord_update bk bv a) bt))"
      using list_bsup_correct[OF Ord_up Hord2'] by auto
    have In_upd : "(k, v) \<in> set (str_ord_update bk bv a)" using str_ord_update_inI2[OF Cons.prems(1) Kbk_neq Cons.prems(3), of bv] by auto
    have "(k, v) \<in> set (list_bsup (str_ord_update bk bv a) bt)" using Cons.IH[OF Ord_up Hord2' In_upd Kbk_notin] by auto
    thus ?thesis using None
      by(auto simp add:Hbkv)
  next
    case (Some av)
    have Ord_up  : "strict_order (map fst (str_ord_update bk [^ av, bv ^] a))" 
      using str_ord_update_correct[OF Cons.prems(1), of bk "[^ av, bv ^]"] by auto
    have Ord_bsup : "strict_order (map fst (list_bsup (str_ord_update bk [^ av, bv ^] a) bt))"
      using list_bsup_correct[OF Ord_up Hord2'] by auto
    have In_upd : "(k, v) \<in> set (str_ord_update bk [^ av, bv ^] a)"
        using str_ord_update_inI2[OF Cons.prems(1) Kbk_neq Cons.prems(3), of "[^ av, bv ^]"] by auto
    have "(k, v) \<in> set (list_bsup (str_ord_update bk [^ av, bv ^] a) bt)" using Cons.IH[OF Ord_up Hord2' In_upd Kbk_notin] by auto
    then show ?thesis using Some Hbkv by(auto)
  qed
qed

lemma absent_key_value :
  assumes H : "k \<notin> set (map fst l)"
  shows "(k, v) \<notin> set (l)"
proof
  assume Hcontra : "(k, v) \<in> set l"
  have "k \<in> set (map fst l)" using imageI[OF Hcontra, of fst] by auto
  thus False using H by auto
qed

lemma list_bsup_disj_key2 :
  fixes k :: "'a :: linorder"
  fixes v :: "'b :: Mergeable"
  fixes a b :: "('a * 'b) list"
  assumes Hord1 : "strict_order (map fst a)"
  assumes Hord2 : "strict_order (map fst b)"
  assumes H1 : "(k, v) \<in> set b"
  assumes H2 : "k  \<notin> set (map fst a)"
  shows "(k, v) \<in> set (list_bsup a b)" using Hord1 Hord2 H1 H2
proof(induction b arbitrary: a)
  case Nil
  then show ?case by auto
next
  case (Cons bh bt)
  obtain bk and bv where Hbkv : "bh = (bk, bv)" by (cases bh; auto)
  have Hord2' : "strict_order (map fst bt)" using Hbkv strict_order_tl[of bk "map fst bt"] Cons.prems(2) by auto

  then show ?case
  proof(cases "map_of a bk")
    case None
    have Ord_up : "strict_order (map fst (str_ord_update bk bv a))"
      using str_ord_update_correct[OF Cons.prems(1), of bk bv] by auto
    have Ord_bsup : "strict_order (map fst (list_bsup (str_ord_update bk bv a) bt))"
      using list_bsup_correct[OF Ord_up Hord2'] by auto
    show ?thesis
    proof(cases "bk = k")
      case True
      have "(bk, bv) \<in> set (bh#bt)" using Hbkv by auto
      hence Hbvv : "bv = v" using 
          distinct_unique_value[OF strict_order_distinct[OF Cons.prems(2)], of bk bv v] True Cons.prems(3) by auto

      have In_upd : "(k, v) \<in> set (str_ord_update bk bv a)" using str_ord_update_inI1[OF Cons.prems(1), of bk bv]  True Hbvv by auto
      have Notin : "k \<notin>   set (map fst bt)" using strict_order_distinct[OF Cons.prems(2)] True Hbkv by auto
        
      then show ?thesis using list_bsup_disj_key1[OF Ord_up Hord2' In_upd Notin] None Hbkv by(auto)
    next
      case False
      have Hin : "(k, v) \<in> set bt" using Cons.prems False Hbkv by auto
      have Hnotin : "k \<notin> set (map fst (str_ord_update bk bv a))"
      proof
        assume Hcontra : "k \<in> set (map fst (str_ord_update bk bv a))"
        then obtain v where Hvc : "(k, v) \<in> set (str_ord_update bk bv a)" by auto
        hence "(k, v) \<in> set a" using str_ord_update_inD[OF Cons.prems(1) Hvc] Cons.prems(4) False by(auto)
        thus False using imageI[of "(k, v)" "set a" fst] Cons.prems(4) by auto
      qed
      show ?thesis using Cons.IH[OF Ord_up Hord2' Hin Hnotin] Hbkv None by auto
    qed
  next
    case (Some av)
    have Ord_up : "strict_order (map fst (str_ord_update bk [^ av, bv ^] a))"
      using str_ord_update_correct[OF Cons.prems(1), of bk "[^ av, bv ^]"] by auto
    have Ord_bsup : "strict_order (map fst (list_bsup (str_ord_update bk [^ av, bv ^] a) bt))"
      using list_bsup_correct[OF Ord_up Hord2'] by auto
    show ?thesis 
    proof(cases "bk = k")
      case True
      have "(bk, av) \<in> set (a)" using True map_of_SomeD[OF Some] by(auto)
      hence "bk \<in> set (map fst a)" using imageI[of "(bk, av)" "set a" fst] by auto
      hence False using Cons.prems(4) True by auto
      thus ?thesis by auto
    next
      case False
      have Hin : "(k, v) \<in> set bt" using Cons.prems False Hbkv by auto
      have Hnotin : "k \<notin> set (map fst (str_ord_update bk [^ av, bv ^] a))"
      proof
        assume Hcontra : "k \<in> set (map fst (str_ord_update bk [^ av, bv ^] a))"
        then obtain vc where Hvc : "(k, vc) \<in> set (str_ord_update bk [^ av, bv ^] a)" by auto
        hence "(k, vc) \<in> set a" using str_ord_update_inD[OF Cons.prems(1) Hvc] Cons.prems(4) False by(auto)
        thus False using imageI[of "(k, vc)" "set a" fst] Cons.prems(4) by auto
      qed
      show ?thesis using Cons.IH[OF Ord_up Hord2' Hin Hnotin] Hbkv Some by( auto)
    qed
  qed
qed

lemma list_bsup_overlap_key :
  fixes k :: "'a :: linorder"
  fixes v v' :: "'b :: Mergeable"
  fixes a b :: "('a * 'b) list"
  assumes Hord1 : "strict_order (map fst a)"
  assumes Hord2 : "strict_order (map fst b)"
  assumes H1 : "(k, v) \<in> set a"
  assumes H2 : "(k, v') \<in> set b"
  shows "(k, [^ v, v' ^]) \<in> set (list_bsup a b)" using Hord1 Hord2 H1 H2
proof(induction b arbitrary: a)
  case Nil
  then show ?case by auto
next
  case (Cons bh bt)
  obtain bk and bv where Hbkv : "bh = (bk, bv)" by (cases bh; auto)
  have Hord2' : "strict_order (map fst bt)" using Hbkv strict_order_tl[of bk "map fst bt"] Cons.prems(2) by auto

  then show ?case 
  proof(cases "map_of a bk")
    case None
    have Ord_up : "strict_order (map fst (str_ord_update bk bv a))"
      using str_ord_update_correct[OF Cons.prems(1), of bk bv] by auto
    have Ord_bsup : "strict_order (map fst (list_bsup (str_ord_update bk bv a) bt))"
      using list_bsup_correct[OF Ord_up Hord2'] by auto
    show ?thesis
    proof(cases "bk = k")
      case True
      have "bk \<notin> set (map fst a)" using None map_of_eq_None_iff[of a bk] by auto
      hence "k \<notin> set (map fst a)" using True by auto
      hence "(k, v) \<notin> set a" using absent_key_value[of k a v] by auto
      hence False using Cons.prems by auto
      then show ?thesis by auto
    next
      case False
      have Hin_b : "(k, v') \<in> set bt" using Cons.prems False Hbkv by auto
      have Hin_a : "(k, v) \<in> set (str_ord_update bk bv a)"
        using str_ord_update_inI2[OF Cons.prems(1) False Cons.prems(3)] by auto
      show ?thesis using Cons.IH[OF Ord_up Hord2' Hin_a Hin_b] Hbkv None by(auto)
    qed
  next
    case (Some av)
    have Ord_up : "strict_order (map fst (str_ord_update bk [^av, bv^] a))"
      using str_ord_update_correct[OF Cons.prems(1), of bk "[^av, bv^]"] by auto
    show ?thesis
    proof(cases "bk = k")
      case True
      have Inb : "(bk, bv) \<in> set (bh#bt)" using Hbkv by auto
      hence Hbvv : "bv = v'" using 
          distinct_unique_value[OF strict_order_distinct[OF Cons.prems(2)], of bk bv v'] True Cons.prems by auto
      
      have  "(bk, av) \<in> set (a)" using map_of_SomeD[OF Some] by(auto)
      hence Havv : "av = v" using
          distinct_unique_value[OF strict_order_distinct[OF Cons.prems(1)], of bk av v] True Cons.prems by auto
      have Notin : "k \<notin>   set (map fst bt)" using strict_order_distinct[OF Cons.prems(2)] True Hbkv by auto
      have Hin : "(k, [^ v, v' ^]) \<in> set (str_ord_update bk [^ av, bv ^] a)"
        using str_ord_update_inI1[OF Cons.prems(1), of bk "[^ av, bv ^]"] Hbvv Havv True by(auto)
      show ?thesis using
           list_bsup_disj_key1[OF Ord_up Hord2' Hin Notin] Cons.prems Some Hbkv by auto
    next
      case False
      have Hin_b : "(k, v') \<in> set bt" using Cons.prems False Hbkv by auto
      have Hin_a : "(k, v) \<in> set (str_ord_update bk [^av, bv^] a)"
        using str_ord_update_inI2[OF Cons.prems(1) False Cons.prems(3)] by auto
      show ?thesis using Cons.IH[OF Ord_up Hord2' Hin_a Hin_b] Hbkv Some by(auto)
    qed
  qed
qed

lemma list_bsup_absent_key :
  fixes k :: "'a :: linorder"
  fixes v :: "'b :: Mergeable"
  fixes a b :: "('a * 'b) list"
  assumes Hord1 : "strict_order (map fst a)"
  assumes Hord2 : "strict_order (map fst b)"
  assumes H1 : "k  \<notin> set (map fst a)"
  assumes H2 : "k  \<notin> set (map fst b)"
  shows "k \<notin> set (map fst (list_bsup a b))" using Hord1 Hord2 H1 H2
proof(induction b arbitrary: a)
  case Nil
  then show ?case
    by auto
next

  case (Cons bh bt)
  obtain bk and bv where Hbkv : "bh = (bk, bv)" by (cases bh; auto)
  have Hord2' : "strict_order (map fst bt)" using Hbkv strict_order_tl[of bk "map fst bt"] Cons.prems(2) by auto

  show ?case
  proof(cases "map_of a bk")
    case None
    have Ord_up : "strict_order (map fst (str_ord_update bk bv a))"
      using str_ord_update_correct[OF Cons.prems(1), of bk bv] by auto
    have Ord_bsup : "strict_order (map fst (list_bsup (str_ord_update bk bv a) bt))"
      using list_bsup_correct[OF Ord_up Hord2'] by auto

    have Notin' : "k \<notin> (set (map fst  (str_ord_update bk bv a)))"

    proof(cases "bk = k")
      case True
      hence  "k \<in> set (map fst (bh # bt))" using Hbkv by(auto)
      hence False using Cons.prems by auto
      thus ?thesis by auto
    next
      case False
      have Contr : "\<And> vcontra . (k, vcontra) \<in>  set (str_ord_update bk bv a) \<Longrightarrow> False"
      proof -
        fix vcontra
        assume HC : "(k, vcontra) \<in> set (str_ord_update bk bv a)"
        have HC' : "(k, vcontra) \<in> set a" using str_ord_update_inD'[OF Cons.prems(1) HC False] by auto
        show False using Cons.prems(3) imageI[OF HC', of fst] by auto
      qed

      thus ?thesis by auto
    qed

    have Notin'_bt : "k \<notin> set (map fst bt)" using Cons.prems(4) by auto

    have Conc' : "k \<notin> set (map fst (list_bsup (str_ord_update bk bv a) bt))"
      using Cons.IH[OF Ord_up Hord2' Notin' Notin'_bt] by auto

    thus ?thesis using Cons.prems None Hbkv by(auto)
  next
    case (Some av)
    have Ord_up : "strict_order (map fst (str_ord_update bk [^ av, bv ^] a))"
      using str_ord_update_correct[OF Cons.prems(1), of bk "[^ av, bv ^]"] by auto
    have Ord_bsup : "strict_order (map fst (list_bsup (str_ord_update bk [^ av, bv ^] a) bt))"
      using list_bsup_correct[OF Ord_up Hord2'] by auto

    have Notin' : "k \<notin> (set (map fst  (str_ord_update bk [^ av, bv ^] a)))"

    proof(cases "bk = k")
      case True
      hence  "k \<in> set (map fst (bh # bt))" using Hbkv by(auto)
      hence False using Cons.prems by auto
      thus ?thesis by auto
    next
      case False
      have Contr : "\<And> vcontra . (k, vcontra) \<in>  set (str_ord_update bk [^ av, bv ^] a) \<Longrightarrow> False"
      proof -
        fix vcontra
        assume HC : "(k, vcontra) \<in> set (str_ord_update bk [^ av, bv ^] a)"
        have HC' : "(k, vcontra) \<in> set a" using str_ord_update_inD'[OF Cons.prems(1) HC False] by auto
        show False using Cons.prems(3) imageI[OF HC', of fst] by auto
      qed

      thus ?thesis by auto
    qed

    have Notin'_bt : "k \<notin> set (map fst bt)" using Cons.prems(4) by auto

    have Conc' : "k \<notin> set (map fst (list_bsup (str_ord_update bk [^ av, bv ^] a) bt))"
      using Cons.IH[OF Ord_up Hord2' Notin' Notin'_bt] by auto

    thus ?thesis using Cons.prems Some Hbkv by(auto)
  qed
qed


lemma list_bsup_is_bsup1 :
  fixes a b :: "('a :: linorder * 'b :: Mergeable) list"
  assumes Horda : "strict_order (map fst a)"
  assumes Hordb : "strict_order (map fst b)"
  shows "list_leq a (list_bsup a b)"
proof(rule list_leqI[OF Horda list_bsup_correct[OF Horda Hordb]])
  fix k :: "'a"
  fix v :: "'b"
  assume H : "(k, v) \<in> set a"
  then show "\<exists>v'. (k, v') \<in> set (list_bsup a b) \<and> v <[ v'"
  proof(cases "k \<in> set (map fst b)")
    case True
    then obtain v' where Hv' : "(k, v') \<in> set b" by auto
    have Leq : "v <[ [^ v, v' ^]" using bsup_leq[OF bsup_spec[of v v']] by auto
    then show ?thesis using list_bsup_overlap_key[OF Horda Hordb H Hv'] by auto
  next
    case False
    have Leq : "v <[ v" using leq_refl[of v] by auto
    then show ?thesis using list_bsup_disj_key1[OF Horda Hordb H False] by auto
  qed
qed

lemma update_leq1 :
  assumes Hord : "strict_order (map fst l)"
  assumes Hnotin : "k \<notin> set (map fst l)"
  shows "list_leq l (str_ord_update k v l)"
proof(rule list_leqI[OF Hord str_ord_update_correct[OF Hord]])
  fix k' v'
  assume H: "(k', v') \<in> set l"
  show "\<exists>v''. (k', v'') \<in> set (str_ord_update k v l) \<and> v' <[ v''"
  proof(cases "k = k'")
    case True
    have "k \<in> set (map fst l)" using imageI[OF H, of fst] True by auto
    hence False using Hnotin by auto
    then show ?thesis by auto
  next
    case False
    have Conc1 : "(k', v') \<in> set (str_ord_update k v l)"
      using str_ord_update_inI2[OF Hord False H] by auto
    have Conc2 : "v' <[ v'" by(simp add:leq_refl)
    then show ?thesis  using Conc1 Conc2 by auto
  qed
qed

lemma update_leq2 :
  assumes Hord : "strict_order (map fst l)"
  assumes Hin : "(k, v) \<in> set (l)"
  assumes Hleq : "v <[ v'"
  shows "list_leq l (str_ord_update k v' l)"
proof(rule list_leqI[OF Hord str_ord_update_correct[OF Hord]])
  fix kx vx
  assume H : "(kx, vx) \<in> set l"
  show "\<exists>v''. (kx, v'') \<in> set (str_ord_update k v' l) \<and> vx <[ v''"
  proof(cases "k = kx")
    case True
    have H' : "(k, vx) \<in> set l" using True H by auto
    have Conc1 : "(k, v') \<in> set (str_ord_update k v' l)" using str_ord_update_inI1[OF Hord] by auto

    have "vx = v" using distinct_unique_value[OF strict_order_distinct[OF Hord] H' Hin] by auto
    hence Conc2 : "vx <[ v'" using Hleq by auto
    then show ?thesis using Conc1 Conc2 True by auto
  next
    case False
    have Conc1 : "(kx, vx) \<in> set (str_ord_update k v' l)"
      using str_ord_update_inI2[OF Hord False H] by auto
    have Conc2 : "vx <[ vx" by(simp add:leq_refl)
    then show ?thesis  using Conc1 Conc2 by auto
  qed
qed

lemma update_leq2' :
  assumes Hord : "strict_order (map fst l)"
  assumes Hin : "(k, v) \<in> set (l)"
  assumes Hleq : "v' <[ v"
  shows "list_leq (str_ord_update k v' l) l"
proof(rule list_leqI[OF str_ord_update_correct[OF Hord] Hord])
  fix kx vx
  assume H : "(kx, vx) \<in>  set (str_ord_update k v' l) "
  show "\<exists>v''. (kx, v'') \<in> set l \<and> vx <[ v''"
  proof(cases "k = kx")
    case True
    have H' : "(k, vx) \<in> set (str_ord_update k v' l)" using True H by auto
    show ?thesis
    proof(cases "(k, vx) \<in> set l")
      assume H'' : "(k, vx) \<in> set l "
      hence "v = vx" using distinct_unique_value[OF strict_order_distinct[OF Hord] H'' Hin] by auto
      have Conc2 : "vx <[ vx" by(simp add:leq_refl)
      show "\<exists>v''. (kx, v'') \<in> set l \<and> vx <[ v''" using True H'' Conc2 by auto
    next
      assume H'' : "(k, vx) \<notin> set l "
      hence "v' = vx" using str_ord_update_inD[OF Hord H'] by auto
      then show "\<exists>v''. (kx, v'') \<in> set l \<and> vx <[ v''" using True Hin Hleq by(auto)
    qed
  next
    case False
    have Conc1 : "(kx, vx) \<in> set l" using str_ord_update_inD'[OF Hord H False] by auto
    have Conc2 : "vx <[ vx" by(simp add:leq_refl)
    show "\<exists>v''. (kx, v'') \<in> set l \<and> vx <[ v''" using Conc1 Conc2 by auto
  qed
qed
      

lemma list_bsup_is_bsup2 :
  fixes a b bd sd :: "('a :: linorder * 'b :: Mergeable) list"
  assumes Horda : "strict_order (map fst a)"
  assumes Hordb : "strict_order (map fst b)"
  assumes Hordbd : "strict_order (map fst bd)"
  assumes Hordsd : "strict_order (map fst sd)"
  assumes Hleq : "list_leq bd b"
  assumes Hub_a : "list_leq a sd"
  assumes Hub_bd : "list_leq bd sd"
  assumes Hsup :
    "\<And> a' ::('a \<times> 'b) list . strict_order (map fst a') \<Longrightarrow>
       list_leq a a' \<Longrightarrow> list_leq bd a' \<Longrightarrow> list_leq sd a'"
  shows "list_leq sd (list_bsup a b)"
proof(rule list_leqI[OF Hordsd list_bsup_correct[OF Horda Hordb]])
  fix k v
  assume H : "(k, v) \<in> set sd"
  consider (1) "k \<in> set (map fst a)" "k \<in> set (map fst b)" |
           (2) "k \<in> set (map fst a)" "k \<notin> set (map fst b)" |
           (3) "k \<notin> set (map fst a)" "k \<in> set (map fst b)" |
           (4) "k \<notin> set (map fst a)" "k \<notin> set (map fst b)" by auto
  then show "\<exists>v'. (k, v') \<in> set (list_bsup a b) \<and> v <[ v'"
  proof cases
    case 1
    obtain va where Hva : "(k, va) \<in> set a" using 1 by(auto)
    obtain va' where Hva'1 :  "va <[ va'" and Hva'2 : "(k, va') \<in> set sd" using list_leqD[OF Hub_a Hva] by auto
    have Hva'_v : "va' = v" using distinct_unique_value[OF strict_order_distinct[OF Hordsd] H Hva'2] by auto
    obtain vb where Hvb : "(k, vb) \<in> set b" using 1 by(auto)
    have Conc1 : "(k, [^ va, vb ^]) \<in> set (list_bsup a b)"
      using list_bsup_overlap_key[OF Horda Hordb Hva Hvb] by auto
    have Conc2 : "(v <[ [^ va, vb ^])"
    proof(cases "k \<in> set (map fst bd)")
      case True
      obtain vbd where Hvbd : "(k, vbd) \<in> set bd" using True by auto
      obtain vbd' where Hvbd'1 :  "vbd <[ vbd'" and Hvbd'2 : "(k, vbd') \<in> set sd" using list_leqD[OF Hub_bd Hvbd] by auto
      have Hvbd'_v : "vbd' = v" using distinct_unique_value[OF strict_order_distinct[OF Hordsd] H Hvbd'2] by auto
      have Conc' : "is_sup {va, vbd} v"
      proof(rule is_supI)
        fix x
        show "x \<in> {va, vbd} \<Longrightarrow> x <[ v" using Hva'1 Hva'_v Hvbd'1 Hvbd'_v by auto
      next
        fix x'
        assume Hub : "is_ub {va, vbd} x'"
        
        hence Hleq_va_x' : "va <[ x'" by(simp add:is_ub_def)
        have  Hleq_vbd_x' : "vbd <[ x'" using Hub by(simp add:is_ub_def)

        have Listlt_1 : "list_leq a (str_ord_update k x' sd)"
        proof(rule list_leqI[OF Horda str_ord_update_correct[OF Hordsd]])
          fix ka kv
          assume Hinner : "(ka, kv) \<in> set a"
          show "\<exists>v'. (ka, v') \<in> set (str_ord_update k x' sd) \<and> kv <[ v'"
          proof(cases "k = ka")
            case True
            hence Hkvva : "kv = va"
                  using distinct_unique_value[OF strict_order_distinct[OF Horda] Hinner, of va] Hva by auto
            hence "(ka, x') \<in> set (str_ord_update k x' sd)" using True str_ord_update_inI1[OF Hordsd, of ka x'] by auto
            then show ?thesis  using Hleq_va_x' Hkvva by auto
          next
            case False
            obtain x'' where Hx'' : "(ka, x'') \<in> set sd" and Hx''_leq : "kv <[ x''" using list_leqD[OF Hub_a Hinner] by auto
            have Conc' : "(ka, x'') \<in> set (str_ord_update k x' sd)" using str_ord_update_inI2[OF Hordsd False Hx''] by auto
            thus ?thesis using Hx''_leq by auto
          qed
        qed

        have Listlt_2 : "list_leq bd (str_ord_update k x' sd)"
        proof(rule list_leqI[OF Hordbd str_ord_update_correct[OF Hordsd]])
          fix ka kv
          assume Hinner : "(ka, kv) \<in> set bd"
          show "\<exists>v'. (ka, v') \<in> set (str_ord_update k x' sd) \<and> kv <[ v'"
          proof(cases "k = ka")
            case True
            hence Hkvvbd : "kv = vbd"
                  using distinct_unique_value[OF strict_order_distinct[OF Hordbd] Hinner, of vbd] Hvbd by auto
            hence "(ka, x') \<in> set (str_ord_update k x' sd)" using True str_ord_update_inI1[OF Hordsd, of ka x'] by auto
            then show ?thesis  using Hleq_vbd_x' Hkvvbd by auto
          next
            case False
            obtain x'' where Hx'' : "(ka, x'') \<in> set sd" and Hx''_leq : "kv <[ x''" using list_leqD[OF Hub_bd Hinner] by auto
            have Conc' : "(ka, x'') \<in> set (str_ord_update k x' sd)" using str_ord_update_inI2[OF Hordsd False Hx''] by auto
            thus ?thesis using Hx''_leq by auto
          qed
        qed

        have Conc'1 : "list_leq sd (str_ord_update k x' sd)" using
          Hsup[OF str_ord_update_correct[OF Hordsd] Listlt_1 Listlt_2] by auto

        hence Conc'2 : "(k, x') \<in> set (str_ord_update k x' sd)" using str_ord_update_inI1[OF Hordsd] by auto

        then obtain x'' where Hx'' : "(k, x'') \<in> set (str_ord_update k x' sd)" and Hx''_leq : "v <[ x''"
          using list_leqD[OF Conc'1 H] by auto

        have "x' = x''" using distinct_unique_value[OF 
                strict_order_distinct[OF str_ord_update_correct[OF Hordsd]] Conc'2 Hx'' ] by auto

        thus "v <[ x'" using Hx''_leq by auto
      qed

      obtain vb' where Hvb' : "vbd <[ vb'" and Hvb'_in : "(k, vb') \<in> set b" using list_leqD[OF Hleq Hvbd] by auto
      have "vb' = vb" using distinct_unique_value[OF strict_order_distinct[OF Hordb] Hvb Hvb'_in] by auto
      hence Conc'' : "vbd <[ vb" using Hvb' by auto
      
      thus "v <[ [^ va, vb ^]" using is_bsupD2[OF bsup_spec[of va vb] Conc'' Conc'] by auto
    next
      case False

      have Listlt_1 : "list_leq a (str_ord_update k va sd)"
      proof(rule list_leqI[OF Horda str_ord_update_correct[OF Hordsd]])
        fix ka kv
        assume Hinner : "(ka, kv) \<in> set a"
        show "\<exists>v'. (ka, v') \<in> set (str_ord_update k va sd) \<and> kv <[ v'"
        proof(cases "k = ka")
          case True
          hence Hkvva : "kv = va"
                using distinct_unique_value[OF strict_order_distinct[OF Horda] Hinner, of va] Hva by auto
          hence "(ka, va) \<in> set (str_ord_update k va sd)" using True str_ord_update_inI1[OF Hordsd, of ka va] by auto
          then show ?thesis  using  Hkvva leq_refl[of va] by auto
        next
          case False
          obtain x'' where Hx'' : "(ka, x'') \<in> set sd" and Hx''_leq : "kv <[ x''" using list_leqD[OF Hub_a Hinner] by auto
          have Conc' : "(ka, x'') \<in> set (str_ord_update k va sd)" using str_ord_update_inI2[OF Hordsd False Hx''] by auto
          thus ?thesis using Hx''_leq by auto
        qed
      qed

      have Listlt_2 : "list_leq bd (str_ord_update k va sd)"
      proof(rule list_leqI[OF Hordbd str_ord_update_correct[OF Hordsd]])
        fix ka kv
        assume Hinner : "(ka, kv) \<in> set bd"
        show "\<exists>v'. (ka, v') \<in> set (str_ord_update k va sd) \<and> kv <[ v'"
        proof(cases "k = ka")
          case True
          hence False using False imageI[OF Hinner, of fst] by auto
          thus ?thesis by auto
        next
          case False
          obtain x'' where Hx'' : "(ka, x'') \<in> set sd" and Hx''_leq : "kv <[ x''" using list_leqD[OF Hub_bd Hinner] by auto
          have Conc' : "(ka, x'') \<in> set (str_ord_update k va sd)" using str_ord_update_inI2[OF Hordsd False Hx''] by auto
          thus ?thesis using Hx''_leq by auto
        qed
      qed

      have Conc'1 : "list_leq sd (str_ord_update k va sd)" using
        Hsup[OF str_ord_update_correct[OF Hordsd] Listlt_1 Listlt_2] by auto

      hence Conc'2 : "(k, va) \<in> set (str_ord_update k va sd)" using str_ord_update_inI1[OF Hordsd] by auto

      then obtain x'' where Hx'' : "(k, x'') \<in> set (str_ord_update k va sd)" and Hx''_leq : "v <[ x''"
        using list_leqD[OF Conc'1 H] by auto

      have "va = x''" using distinct_unique_value[OF 
              strict_order_distinct[OF str_ord_update_correct[OF Hordsd]] Conc'2 Hx'' ] by auto

      hence Hv_lt_va : "v <[ va" using Hva'_v Hva'1 using Hx''_leq by auto

      thus "v <[ [^ va, vb ^]" using leq_trans[OF Hv_lt_va is_bsupD1[OF bsup_spec[of va vb]]] by auto
    qed

    thus ?thesis using Conc1 Conc2 by auto

  next

    case 2
    obtain va where Hva : "(k, va) \<in> set a" using 2 by(auto)
    obtain va' where Hva'1 :  "va <[ va'" and Hva'2 : "(k, va') \<in> set sd" using list_leqD[OF Hub_a Hva] by auto
    have Hva'_v : "va' = v" using distinct_unique_value[OF strict_order_distinct[OF Hordsd] H Hva'2] by auto

    have Conc1: "(k, va) \<in> set (list_bsup a b)" using list_bsup_disj_key1[OF Horda Hordb Hva 2(2)] by auto

    have Conc2 :"v <[ va"
    proof(cases "k \<in> set (map fst bd)")
      case True
      then obtain bdv where Hbdv_in : "(k, bdv) \<in> set bd" by auto
      then obtain bdv_b where Hbdv_b_in : "(k, bdv_b) \<in> set b" using list_leqD[OF Hleq Hbdv_in] by auto
      have "k \<in> set (map fst b)" using imageI[OF Hbdv_b_in, of fst] by auto
      hence False using 2 by auto
      then show ?thesis by auto
    next
      case False

      have Listlt_1 : "list_leq a (str_ord_update k va sd)"
      proof(rule list_leqI[OF Horda str_ord_update_correct[OF Hordsd]])
        fix ka kv
        assume Hinner : "(ka, kv) \<in> set a"
        show "\<exists>v'. (ka, v') \<in> set (str_ord_update k va sd) \<and> kv <[ v'"
        proof(cases "k = ka")
          case True
          hence Hkvva : "kv = va"
                using distinct_unique_value[OF strict_order_distinct[OF Horda] Hinner, of va] Hva by auto
          hence "(ka, va) \<in> set (str_ord_update k va sd)" using True str_ord_update_inI1[OF Hordsd, of ka va] by auto
          then show ?thesis  using  Hkvva leq_refl[of va] by auto
        next
          case False
          obtain x'' where Hx'' : "(ka, x'') \<in> set sd" and Hx''_leq : "kv <[ x''" using list_leqD[OF Hub_a Hinner] by auto
          have Conc' : "(ka, x'') \<in> set (str_ord_update k va sd)" using str_ord_update_inI2[OF Hordsd False Hx''] by auto
          thus ?thesis using Hx''_leq by auto
        qed
      qed

      have Listlt_2 : "list_leq bd (str_ord_update k va sd)"
      proof(rule list_leqI[OF Hordbd str_ord_update_correct[OF Hordsd]])
        fix ka kv
        assume Hinner : "(ka, kv) \<in> set bd"
        show "\<exists>v'. (ka, v') \<in> set (str_ord_update k va sd) \<and> kv <[ v'"
        proof(cases "k = ka")
          case True
          hence False using False imageI[OF Hinner, of fst] by auto
          thus ?thesis by auto
        next
          case False
          obtain x'' where Hx'' : "(ka, x'') \<in> set sd" and Hx''_leq : "kv <[ x''" using list_leqD[OF Hub_bd Hinner] by auto
          have Conc' : "(ka, x'') \<in> set (str_ord_update k va sd)" using str_ord_update_inI2[OF Hordsd False Hx''] by auto
          thus ?thesis using Hx''_leq by auto
        qed
      qed

      have Conc'1 : "list_leq sd (str_ord_update k va sd)" using
        Hsup[OF str_ord_update_correct[OF Hordsd] Listlt_1 Listlt_2] by auto

      hence Conc'2 : "(k, va) \<in> set (str_ord_update k va sd)" using str_ord_update_inI1[OF Hordsd] by auto

      then obtain x'' where Hx'' : "(k, x'') \<in> set (str_ord_update k va sd)" and Hx''_leq : "v <[ x''"
        using list_leqD[OF Conc'1 H] by auto

      have "va = x''" using distinct_unique_value[OF 
              strict_order_distinct[OF str_ord_update_correct[OF Hordsd]] Conc'2 Hx'' ] by auto

      then show ?thesis using Hx''_leq by auto
    qed

    thus ?thesis using Conc1 Conc2 by auto

  next
    case 3
    obtain vb where Hvb : "(k, vb) \<in> set b" using 3 by(auto)
    have Conc1 : "(k, vb) \<in> set (list_bsup a b)"
      using list_bsup_disj_key2[OF Horda Hordb Hvb 3(1)] by auto
    have Conc2 : "(v <[ vb)"

    (* TODO: we do not need this case split here (or perhaps anywhere)
     * The proofs could probably be cleaned up without it, but the current versions
     * get the job done... *)
    proof(cases "k \<in> set (map fst bd)")
      case True

      have Listlt_1 : "list_leq a (str_ord_update k vb sd)"
      proof(rule list_leqI[OF Horda str_ord_update_correct[OF Hordsd]])
        fix ka kv
        assume Hinner : "(ka, kv) \<in> set a"
        show "\<exists>v'. (ka, v') \<in> set (str_ord_update k vb sd) \<and> kv <[ v'"
        proof(cases "k = ka")
          case True
          have "k \<in> set (map fst a)" using imageI[OF Hinner, of fst] True by auto
          hence False using 3 by auto
          then show ?thesis by auto
        next
          case False
          obtain x'' where Hx'' : "(ka, x'') \<in> set sd" and Hx''_leq : "kv <[ x''" using list_leqD[OF Hub_a Hinner] by auto
          have Conc' : "(ka, x'') \<in> set (str_ord_update k vb sd)" using str_ord_update_inI2[OF Hordsd False Hx''] by auto
          thus ?thesis using Hx''_leq by auto
        qed
      qed

      have Listlt_2 : "list_leq bd (str_ord_update k vb sd)"
      proof(rule list_leqI[OF Hordbd str_ord_update_correct[OF Hordsd]])
        fix ka kv
        assume Hinner : "(ka, kv) \<in> set bd"
        show "\<exists>v'. (ka, v') \<in> set (str_ord_update k vb sd) \<and> kv <[ v'"
        proof(cases "k = ka")
          assume True' : "k = ka"
          have "(k, vb) \<in> set (str_ord_update k vb sd)" using str_ord_update_inI1[OF Hordsd, of k vb] by auto
          hence Conc'1 : "(ka, vb) \<in> set (str_ord_update k vb sd)" using True' by auto
          obtain vb' where Hvb' : "kv <[ vb'" and Hvb'_in :  "(ka, vb') \<in> set b" using list_leqD[OF Hleq Hinner] by auto
          have Hvb_eq_vb' : "vb = vb'" using
            distinct_unique_value[OF strict_order_distinct[OF Hordb] Hvb'_in, of vb] True' Hvb by auto
          thus ?thesis using Hvb' Conc'1 by auto
        next
          case False
          obtain x'' where Hx'' : "(ka, x'') \<in> set sd" and Hx''_leq : "kv <[ x''" using list_leqD[OF Hub_bd Hinner] by auto
          have Conc' : "(ka, x'') \<in> set (str_ord_update k vb sd)" using str_ord_update_inI2[OF Hordsd False Hx''] by auto
          thus ?thesis using Hx''_leq by auto
        qed
      qed

      have Conc'1 : "list_leq sd (str_ord_update k vb sd)" using
        Hsup[OF str_ord_update_correct[OF Hordsd] Listlt_1 Listlt_2] by auto

      hence Conc'2 : "(k, vb) \<in> set (str_ord_update k vb sd)" using str_ord_update_inI1[OF Hordsd] by auto

      then obtain x'' where Hx'' : "(k, x'') \<in> set (str_ord_update k vb sd)" and Hx''_leq : "v <[ x''"
        using list_leqD[OF Conc'1 H] by auto

      have "vb = x''" using distinct_unique_value[OF 
              strict_order_distinct[OF str_ord_update_correct[OF Hordsd]] Conc'2 Hx'' ] by auto

      then show ?thesis using Hx''_leq by auto

    next

      case False

      have Listlt_1 : "list_leq a (str_ord_update k vb sd)"
      proof(rule list_leqI[OF Horda str_ord_update_correct[OF Hordsd]])
        fix ka kv
        assume Hinner : "(ka, kv) \<in> set a"
        show "\<exists>v'. (ka, v') \<in> set (str_ord_update k vb sd) \<and> kv <[ v'"
        proof(cases "k = ka")
          case True
          have "k \<in> set (map fst a)" using imageI[OF Hinner, of fst] True by auto
          hence False using 3 by auto
          then show ?thesis by auto
        next
          case False
          obtain x'' where Hx'' : "(ka, x'') \<in> set sd" and Hx''_leq : "kv <[ x''" using list_leqD[OF Hub_a Hinner] by auto
          have Conc' : "(ka, x'') \<in> set (str_ord_update k vb sd)" using str_ord_update_inI2[OF Hordsd False Hx''] by auto
          thus ?thesis using Hx''_leq by auto
        qed
      qed

      have Listlt_2 : "list_leq bd (str_ord_update k vb sd)"
      proof(rule list_leqI[OF Hordbd str_ord_update_correct[OF Hordsd]])
        fix ka kv
        assume Hinner : "(ka, kv) \<in> set bd"
        show "\<exists>v'. (ka, v') \<in> set (str_ord_update k vb sd) \<and> kv <[ v'"
        proof(cases "k = ka")
          assume True' : "k = ka"
          have "(k, vb) \<in> set (str_ord_update k vb sd)" using str_ord_update_inI1[OF Hordsd, of k vb] by auto
          hence Conc'1 : "(ka, vb) \<in> set (str_ord_update k vb sd)" using True' by auto
          obtain vb' where Hvb' : "kv <[ vb'" and Hvb'_in :  "(ka, vb') \<in> set b" using list_leqD[OF Hleq Hinner] by auto
          have Hvb_eq_vb' : "vb = vb'" using
            distinct_unique_value[OF strict_order_distinct[OF Hordb] Hvb'_in, of vb] True' Hvb by auto
          thus ?thesis using Hvb' Conc'1 by auto
        next
          case False
          obtain x'' where Hx'' : "(ka, x'') \<in> set sd" and Hx''_leq : "kv <[ x''" using list_leqD[OF Hub_bd Hinner] by auto
          have Conc' : "(ka, x'') \<in> set (str_ord_update k vb sd)" using str_ord_update_inI2[OF Hordsd False Hx''] by auto
          thus ?thesis using Hx''_leq by auto
        qed
      qed

      have Conc'1 : "list_leq sd (str_ord_update k vb sd)" using
        Hsup[OF str_ord_update_correct[OF Hordsd] Listlt_1 Listlt_2] by auto

      hence Conc'2 : "(k, vb) \<in> set (str_ord_update k vb sd)" using str_ord_update_inI1[OF Hordsd] by auto

      then obtain x'' where Hx'' : "(k, x'') \<in> set (str_ord_update k vb sd)" and Hx''_leq : "v <[ x''"
        using list_leqD[OF Conc'1 H] by auto

      have "vb = x''" using distinct_unique_value[OF 
              strict_order_distinct[OF str_ord_update_correct[OF Hordsd]] Conc'2 Hx'' ] by auto

      then show ?thesis using Hx''_leq by auto
    qed

    thus ?thesis using Conc1 Conc2 by auto
  next

    case 4

    have Hconcr1  : "finite (set sd - {(k, v)})" by auto

    have Hconcr2 : "\<And> k1 v1 v2 . (k1, v1) \<in> set sd - {(k, v)} \<Longrightarrow> (k1, v2) \<in> set sd - {(k, v)} \<Longrightarrow> v1 = v2"
      using distinct_unique_value[OF strict_order_distinct[OF Hordsd]] by auto

    obtain sd' where Hordsd' : "strict_order (map fst sd')" and Hsd' : "set sd' = (set sd - {(k, v)})"
      using concretize_alist[OF Hconcr1] Hconcr2 by(blast)


    have Listlt_1 : "list_leq a sd'"
    proof(rule list_leqI[OF Horda Hordsd'])
      fix ka kv
      assume Hinner : "(ka, kv) \<in> set a"

      show "\<exists>v'. (ka, v') \<in> set sd' \<and> kv <[ v'"
      proof(cases "ka = k")
        case True
        have "(k, kv) \<in> set a" using Hinner True by auto
        hence "k \<in> set (map fst a)" using imageI[of "(k, kv)" "set a" fst] by auto
        hence False using 4 by auto
        then show ?thesis by auto
      next
        case False
        obtain kv' where Kv_in : "(ka, kv') \<in> set sd" and Conc' : "kv <[ kv'"
          using list_leqD[OF Hub_a Hinner] by auto
        have "(ka, kv') \<in> set sd - {(k, v)}" using Kv_in False by auto
        thus ?thesis using Conc' Hsd' by auto
      qed
    qed

    have Listlt_2 : "list_leq bd sd'"
    proof(rule list_leqI[OF Hordbd Hordsd'])
      fix ka kv
      assume Hinner : "(ka, kv) \<in> set bd"

      show "\<exists>v'. (ka, v') \<in> set sd' \<and> kv <[ v'"
      proof(cases "ka = k")
        case True
        have "(k, kv) \<in> set bd" using Hinner True by auto
        then obtain kv' where Kv'_in : "(k, kv') \<in> set b"
          using list_leqD[OF Hleq  Hinner] True by auto
        
        hence "k \<in> set (map fst b)" using imageI[of "(k, kv')" "set b" fst] by auto
        hence False using 4 by auto
        then show ?thesis by auto
      next
        case False
        obtain kv' where Kv_in : "(ka, kv') \<in> set sd" and Conc' : "kv <[ kv'"
          using list_leqD[OF Hub_bd Hinner] by auto
        have "(ka, kv') \<in> set sd - {(k, v)}" using Kv_in False by auto
        thus ?thesis using Conc' Hsd' by auto
      qed
    qed

    have Leq_contr : "list_leq sd sd'" using Hsup[OF Hordsd' Listlt_1 Listlt_2] by auto
    obtain vcontr where Hvcontr_in : "(k, vcontr) \<in> set sd'"
      using list_leqD[OF Leq_contr H] by auto
    hence Vcontr_neq : "vcontr \<noteq> v" using Hsd' by auto
    have Vcontr_in : "(k, vcontr) \<in> set sd" using Hvcontr_in Vcontr_neq Hsd' by auto

    have False using
      distinct_unique_value[OF strict_order_distinct[OF Hordsd] H Vcontr_in] Vcontr_neq
      by auto
    thus ?thesis by auto
  qed
qed

lemma list_bsup_is_bsup3 :
  fixes a b a' :: "('a :: linorder * 'b :: Mergeable) list"
  assumes Horda : "strict_order (map fst a)"
  assumes Hordb : "strict_order (map fst b)"
  assumes Horda' : "strict_order (map fst a')"
  assumes Hleq : "list_leq a a'"
  assumes Hbub :
    "\<And> bd sd .
      strict_order (map fst bd) \<Longrightarrow> strict_order (map fst sd) \<Longrightarrow>
      list_leq bd b \<Longrightarrow>
      list_leq a sd \<Longrightarrow>
      list_leq bd sd \<Longrightarrow>
      (\<And> a'' . strict_order (map fst a'') \<Longrightarrow> list_leq a a'' \<Longrightarrow> list_leq bd a'' \<Longrightarrow> list_leq sd a'') \<Longrightarrow>
      list_leq sd a'
      "
  shows "list_leq (list_bsup a b) a'"
proof(rule list_leqI[OF list_bsup_correct[OF Horda Hordb] Horda'])
  fix k v
  assume H : "(k, v) \<in> set (list_bsup a b)" 

  consider (1) "k \<in> set (map fst a)" "k \<in> set (map fst b)" |
           (2) "k \<in> set (map fst a)" "k \<notin> set (map fst b)" |
           (3) "k \<notin> set (map fst a)" "k \<in> set (map fst b)" |
           (4) "k \<notin> set (map fst a)" "k \<notin> set (map fst b)" by auto
  then show "\<exists>v'. (k, v') \<in> set a' \<and> v <[ v'"
  proof cases
    case 1
    obtain va where Hva : "(k, va) \<in> set a" using 1 by(auto)
    obtain va' where Hva'1 :  "va <[ va'" and Hva'2 : "(k, va') \<in> set a'" using list_leqD[OF Hleq Hva] by auto

    obtain vb where Hvb : "(k, vb) \<in> set b" using 1 by auto

    have H' : "(k, [^ va, vb ^]) \<in> set (list_bsup a b)" using list_bsup_overlap_key[OF Horda Hordb Hva Hvb] by auto

    have Hv_bsup : "v = [^ va, vb ^]" using
      distinct_unique_value[OF strict_order_distinct[OF list_bsup_correct[OF Horda Hordb]] H H'] by auto

    have Hbub_elem : "is_bub va vb va'"
    proof(rule is_bubI)
      show "va <[ va'" using Hva'1 by auto
    next
      fix bd sd
      assume Hin_lt : "bd <[ vb"
      assume Hin_sup : "is_sup {va, bd} sd" 

      have Hin_sup_va : "va <[ sd" using Hin_sup
        by(auto simp add:is_sup_def is_least_def is_ub_def)


      have Hin_sup_bd : "bd <[ sd" using Hin_sup
        by(auto simp add:is_sup_def is_least_def is_ub_def)

      (* bd = [bd]
         sd = update k sd a 
      *)
      have Ord_bd : "strict_order (map fst [(k, bd)])"
        by(auto simp add: strict_order_def)
      have Ord_in : "(k, bd) \<in> set [(k, bd)]" by auto
      have X1 : "list_leq [(k, bd)] b" 
      proof(rule list_leqI[OF Ord_bd Hordb])
        fix kbx :: 'a
        fix vbx :: 'b
        assume Hin: "(kbx, vbx) \<in> set [(k, bd)]"
        hence Hin_k : "kbx = k" and Hin'_v : "vbx = bd" using Ord_in by auto
          
        show "\<exists>v'. (kbx, v') \<in> set b \<and> vbx <[ v'" using Hin_lt Hin'_v Hin_k Hvb
          by(auto)
      qed
      have X2 : "list_leq [(k, bd)] (str_ord_update k sd a)"
      proof(rule list_leqI[OF Ord_bd str_ord_update_correct[OF Horda]])
        fix kax :: 'a
        fix vax :: 'b
        assume Hin: "(kax, vax) \<in> set [(k, bd)]"
        hence Hin_k : "kax = k" and Hin'_v : "vax = bd" using Ord_in by auto
        have Hin_upda : "(k, sd) \<in> set (str_ord_update k sd a)"
          using str_ord_update_inI1[OF Horda] by auto

        show "\<exists>v'. (kax, v') \<in> set (str_ord_update k sd a) \<and> vax <[ v'"
          using Hin'_v Hin_upda Hin_k Hin_sup_bd by auto
      qed

      have X3 : "list_leq a (str_ord_update k sd a)"
      proof(rule update_leq2[OF Horda Hva])
        show "va <[ sd" using Hin_sup_va by auto
      qed

      have X4 : "strict_order (map fst [(k, bd)])" 
        by(auto simp add:strict_order_def)
      have X5 : "strict_order (map fst (str_ord_update k sd a))"
        using str_ord_update_correct[OF Horda] by auto

      have Conc' : "(\<And>a''. strict_order (map fst a'') \<Longrightarrow> list_leq a a'' \<Longrightarrow> list_leq [(k, bd)] a'' \<Longrightarrow>
        list_leq (str_ord_update k sd a) a'') "
      proof-
        fix a'' :: "('a * 'b) list"
        assume XX1 : "strict_order ( map fst a'')"
        assume XX2 : "list_leq a a''"
        assume XX3 : "list_leq [(k, bd)] a''"

        show "list_leq (str_ord_update k sd a) a''"
        proof(rule list_leqI[OF X5 XX1])
          fix kax :: 'a
          fix vax :: 'b
          assume Hin' : "(kax, vax) \<in> set (str_ord_update k sd a)"

          show "\<exists>v'. (kax, v') \<in> set a'' \<and> vax <[ v'"
          proof(cases "k = kax")
            case True
            have "(k, sd) \<in> set (str_ord_update k sd a)" using str_ord_update_inI1[OF Horda] by auto
            hence Vax_sd : "(vax = sd)"
              using distinct_unique_value[OF strict_order_distinct[OF str_ord_update_correct[OF Horda]] Hin', of sd] using True
              by auto
            hence Vax_lt : "vax <[ sd" using leq_refl by auto
            obtain vax' where Hvax : "(kax, vax') \<in> set a''" 
              using list_leqD[OF XX2 Hva] using True by auto

            have Hin_ub : "is_ub {va, bd} vax'"
            proof(rule is_ubI)
              fix xin :: 'b

              obtain val' where Val'1 : "(k, val') \<in> set a''" and Val'2 : "va <[ val'" using list_leqD[OF XX2 Hva] by auto
              have Val'_val : "val' = vax'"
                using distinct_unique_value[OF strict_order_distinct[OF XX1] Hvax, of val'] using True Val'1 by auto
              

              have Conc1 : "va <[ vax'" using Val'2 Val'_val by(auto)

              have Hkbd : "(k, bd) \<in> set [(k, bd)]" by auto
              obtain val' where Val'1 : "(k, val') \<in> set a''" and Val'2 : "bd <[ val'" using list_leqD[OF XX3 Hkbd] by auto
              have Val'_val : "val' = vax'"
                using distinct_unique_value[OF strict_order_distinct[OF XX1] Hvax, of val'] using True Val'1 by auto
              hence Conc2 : "bd <[ vax'" using Val'2 by auto

              show "\<And>x. x \<in> {va, bd} \<Longrightarrow> x <[ vax'" using Conc1 Conc2 by auto
            qed

            have "vax <[ vax'" using is_supD2[OF Hin_sup Hin_ub] Vax_sd by auto
            
            then show ?thesis using Hvax by auto
          next
            case False
            have Hvax : "(kax, vax) \<in> set a" using str_ord_update_inD'[OF Horda Hin' False] by auto
            obtain vax' where Hvax' : "(kax, vax') \<in> set a''" and Hvax'_leq : "vax <[ vax'"
              using list_leqD[OF XX2 Hvax] by auto
            then show ?thesis using Hvax' Hvax'_leq by auto
          qed
        qed
      qed

      have  Conc'' : "list_leq (str_ord_update k sd a) a'" using Hbub[OF X4 X5 X1 X3 X2] Conc' by auto

      have "(k, sd) \<in> set (str_ord_update k sd a)" using str_ord_update_inI1[OF Horda] by auto
      
      then obtain va'' where "(k, va'') \<in> set a'" and Conc''' : "sd <[ va''" using list_leqD[OF Conc''] by auto

      hence "va'' = va'" using
        distinct_unique_value[OF strict_order_distinct[OF Horda'] Hva'2, of va''] by auto

      thus "sd <[ va'"  using Conc''' by auto
    qed

    show ?thesis using is_bsupD3[OF bsup_spec[of va vb] Hbub_elem] Hv_bsup Hva'2 by auto
  next
    case 2
    obtain va where Hva : "(k, va) \<in> set a" using 2 by(auto)
    obtain va' where Hva'1 :  "va <[ va'" and Hva'2 : "(k, va') \<in> set a'" using list_leqD[OF Hleq Hva] by auto
    have H' : "(k, va) \<in> set (list_bsup a b)" using list_bsup_disj_key1[OF Horda Hordb Hva] 2 by auto
    have Hv_va : "v = va" using
      distinct_unique_value[OF strict_order_distinct[OF list_bsup_correct[OF Horda Hordb]] H H'] by auto

    show ?thesis using Hva'1 Hva'2 Hv_va by(auto)
  next
    case 3
    obtain vb where Hvb : "(k, vb) \<in> set b" using 3 by auto

    have H' : "(k, vb) \<in> set (list_bsup a b)" using list_bsup_disj_key2[OF Horda Hordb Hvb] 3 by auto

    have Hv_vb : "v = vb" using
      distinct_unique_value[OF strict_order_distinct[OF list_bsup_correct[OF Horda Hordb]] H H'] by auto

    have Ord_bd : "strict_order (map fst [(k, v)])"
      by(auto simp add: strict_order_def)
    have Bd_in : "(k, v) \<in> set [(k, v)]" by auto
    have X1 : "list_leq [(k, v)] b" 
    proof(rule list_leqI[OF Ord_bd Hordb])
      fix kbx :: 'a
      fix vbx :: 'b
      assume Hin: "(kbx, vbx) \<in> set [(k, v)]"
      hence Hin_k : "kbx = k" and Hin'_v : "vbx = v" using Bd_in by auto
      have "vbx <[ vbx" using leq_refl by auto
      thus "\<exists>v'. (kbx, v') \<in> set b \<and> vbx <[ v'" using  Hin'_v Hin_k Hvb Hv_vb
        by(auto)
    qed

    have X2 : "list_leq a (str_ord_update k v a)"
      using update_leq1[OF Horda 3(1)] by auto

    have X3 : "list_leq [(k, v)] (str_ord_update k v a)"
    proof(rule list_leqI[OF Ord_bd str_ord_update_correct[OF Horda]])
      fix kbx :: 'a
      fix vbx :: 'b
      assume Hin: "(kbx, vbx) \<in> set [(k, v)]"
      hence Hin_k : "kbx = k" and Hin_v : "vbx = v" using Bd_in by auto

      have Hin' : "(k, v) \<in> set (str_ord_update k v a)"
        using str_ord_update_inI1[OF Horda] by auto

      have "vbx <[ vbx" using leq_refl by auto
      thus "\<exists>v'. (kbx, v') \<in> set (str_ord_update k v a) \<and> vbx <[ v'"
        using Hin_v Hin_k Hvb Hv_vb Hin' by auto
    qed

    have Conc' : "(\<And>a''. strict_order (map fst a'') \<Longrightarrow> list_leq a a'' \<Longrightarrow> list_leq [(k, v)] a'' \<Longrightarrow>
                  list_leq (str_ord_update k v a) a'') "
    proof-
      fix a'' :: "('a * 'b) list"
      assume XX1 : "strict_order ( map fst a'')"
      assume XX2 : "list_leq a a''"
      assume XX3 : "list_leq [(k, v)] a''"
      show "list_leq (str_ord_update k v a) a''"
      proof(rule list_leqI[OF str_ord_update_correct[OF Horda] XX1])
        fix kax :: 'a
        fix vax :: 'b
        assume Hkax :"(kax, vax) \<in> set (str_ord_update k v a)"
        
        show "\<exists>v'. (kax, v') \<in> set a'' \<and> vax <[ v'"
        proof(cases "k = kax")
          case True
          have Hvvax'1 : "(k, v) \<in> set (str_ord_update k v a)" using str_ord_update_inI1[OF Horda] by auto
          hence Hvvax'2 :  "(kax, v) \<in> set (str_ord_update k v a)" using True by auto
          have Hvvax : "vax = v" using 
            distinct_unique_value[OF strict_order_distinct[OF str_ord_update_correct[OF Horda]] Hkax Hvvax'2] by auto

          obtain vax' where "(k, vax') \<in> set a''" and "v <[ vax'" using list_leqD[OF XX3 Bd_in] by auto
          then show ?thesis using True Hvvax by auto
        next
          case False
          have Hkax' : "(kax, vax) \<in> set a" using str_ord_update_inD'[OF Horda Hkax False] by auto
          obtain vax' where "(kax, vax') \<in> set a''" and "vax <[ vax'" using list_leqD[OF XX2 Hkax'] by auto
          then show ?thesis by auto
        qed
      qed
    qed

    have Conc'' : "list_leq (str_ord_update k v a) a'"
      using Hbub[OF Ord_bd str_ord_update_correct[OF Horda] X1 X2 X3 Conc']
      by auto

    have "(k, v) \<in> set (str_ord_update k v a)" using str_ord_update_inI1[OF Horda] by auto
      
    then obtain va'' where "(k, va'') \<in> set a'" and Conc''' : "v <[ va''" using list_leqD[OF Conc''] by auto
    thus ?thesis by auto
  next
    case 4

    have "k \<notin> set (map fst (list_bsup a b))" using list_bsup_absent_key[OF Horda Hordb 4(1) 4(2)] by auto
    hence False using imageI[OF H, of fst] by auto
    then show ?thesis by auto
  qed
qed


lemma list_bsup_is_bsup :
  fixes a b :: "('a :: linorder * 'b :: Mergeable) list"
  assumes Horda : "strict_order (map fst a)"
  assumes Hordb : "strict_order (map fst b)"
  shows "     
       (list_leq a (list_bsup a b) \<and>
        (\<forall>bd::('a \<times> 'b) list\<in>{xs::('a \<times> 'b) list. strict_order (map fst xs)}.
            \<forall>sd::('a \<times> 'b) list\<in>{xs::('a \<times> 'b) list. strict_order (map fst xs)}.
               list_leq bd b \<longrightarrow>
               (\<forall>x::('a \<times> 'b) list\<in>{a, bd}. list_leq x sd) \<and> 
               (\<forall>a'::('a \<times> 'b) list\<in>{xs::('a \<times> 'b) list. strict_order (map fst xs)}. (\<forall>x::('a \<times> 'b) list\<in>{a, bd}. list_leq x a') \<longrightarrow> list_leq sd a') \<longrightarrow>
               list_leq sd (list_bsup a b))) \<and>
       (\<forall>a'::('a \<times> 'b) list\<in>{xs::('a \<times> 'b) list. strict_order (map fst xs)}.
           list_leq a a' \<and>
           (\<forall>bd::('a \<times> 'b) list\<in>{xs::('a \<times> 'b) list. strict_order (map fst xs)}.
               \<forall>sd::('a \<times> 'b) list\<in>{xs::('a \<times> 'b) list. strict_order (map fst xs)}.
                  list_leq bd b \<longrightarrow>
                  (\<forall>x::('a \<times> 'b) list\<in>{a, bd}. list_leq x sd) \<and> (\<forall>a'::('a \<times> 'b) list\<in>{xs::('a \<times> 'b) list. strict_order (map fst xs)}. (\<forall>x::('a \<times> 'b) list\<in>{a, bd}. list_leq x a') \<longrightarrow> list_leq sd a') \<longrightarrow> list_leq sd a') \<longrightarrow>
           list_leq (list_bsup a b) a')"
proof(rule conjI)
  show "list_leq a (list_bsup a b) \<and>
    (\<forall>bd\<in>{xs. strict_order (map fst xs)}.
        \<forall>sd\<in>{xs. strict_order (map fst xs)}.
           list_leq bd b \<longrightarrow>
           (\<forall>x\<in>{a, bd}. list_leq x sd) \<and>
           (\<forall>a'\<in>{xs. strict_order (map fst xs)}. (\<forall>x\<in>{a, bd}. list_leq x a') \<longrightarrow> list_leq sd a') \<longrightarrow>
           list_leq sd (list_bsup a b))"
  proof (rule conjI)
    show "list_leq a (list_bsup a b)" using Horda Hordb list_bsup_is_bsup1 by blast
  next
    show "\<forall>bd\<in>{xs. strict_order (map fst xs)}.
       \<forall>sd\<in>{xs. strict_order (map fst xs)}.
          list_leq bd b \<longrightarrow>
          (\<forall>x\<in>{a, bd}. list_leq x sd) \<and>
          (\<forall>a'\<in>{xs. strict_order (map fst xs)}. (\<forall>x\<in>{a, bd}. list_leq x a') \<longrightarrow> list_leq sd a') \<longrightarrow>
          list_leq sd (list_bsup a b)" using list_bsup_is_bsup2[OF Horda Hordb] by blast
  qed
next
  show "\<forall>a'\<in>{xs. strict_order (map fst xs)}.
       list_leq a a' \<and>
       (\<forall>bd\<in>{xs. strict_order (map fst xs)}.
           \<forall>sd\<in>{xs. strict_order (map fst xs)}.
              list_leq bd b \<longrightarrow>
              (\<forall>x\<in>{a, bd}. list_leq x sd) \<and>
              (\<forall>a'\<in>{xs. strict_order (map fst xs)}. (\<forall>x\<in>{a, bd}. list_leq x a') \<longrightarrow> list_leq sd a') \<longrightarrow>
              list_leq sd a') \<longrightarrow>
       list_leq (list_bsup a b) a'"
  proof
    fix a' :: "('a * 'b) list"
    assume Ha' : "a' \<in> {xs. strict_order (map fst xs)}"
    hence Horda' : "strict_order (map fst a')" by auto
    
    show "list_leq a a' \<and>
          (\<forall>bd\<in>{xs. strict_order (map fst xs)}.
              \<forall>sd\<in>{xs. strict_order (map fst xs)}.
                 list_leq bd b \<longrightarrow>
                 (\<forall>x\<in>{a, bd}. list_leq x sd) \<and>
                 (\<forall>a'\<in>{xs. strict_order (map fst xs)}. (\<forall>x\<in>{a, bd}. list_leq x a') \<longrightarrow> list_leq sd a') \<longrightarrow>
                 list_leq sd a') \<longrightarrow>
          list_leq (list_bsup a b) a'"
      using list_bsup_is_bsup3[OF Horda Hordb Horda'] by blast
  qed
qed

(* Finally, the punchline - a Mergeable instance for OAlist. *)

instantiation oalist :: (linorder, Mergeable) Mergeable
begin
definition bsup_oalist :
"bsup l1 l2 = oalist_bsup l1 l2"

instance proof
  fix a b :: "('a :: linorder, 'b :: Mergeable) oalist"
  show "is_bsup a b [^ a, b ^]"
    unfolding is_bsup_def is_sup_def is_least_def is_bub_def is_ub_def pleq_oalist bsup_oalist
  proof(transfer)
    fix a b :: "('a * 'b) list"
    assume Horda : "strict_order (map fst a)" 
    assume Hordb : "strict_order (map fst b)"
  
    show "strict_order (map fst a) \<Longrightarrow>
           strict_order (map fst b) \<Longrightarrow>
           (list_leq a (list_bsup a b) \<and>
            (\<forall>bd\<in>{xs. strict_order (map fst xs)}.
                \<forall>sd\<in>{xs. strict_order (map fst xs)}.
                   list_leq bd b \<longrightarrow>
                   (\<forall>x\<in>{a, bd}. list_leq x sd) \<and>
                   (\<forall>a'\<in>{xs. strict_order (map fst xs)}. (\<forall>x\<in>{a, bd}. list_leq x a') \<longrightarrow> list_leq sd a') \<longrightarrow>
                   list_leq sd (list_bsup a b))) \<and>
           (\<forall>a'\<in>{xs. strict_order (map fst xs)}.
               list_leq a a' \<and>
               (\<forall>bd\<in>{xs. strict_order (map fst xs)}.
                   \<forall>sd\<in>{xs. strict_order (map fst xs)}.
                      list_leq bd b \<longrightarrow>
                      (\<forall>x\<in>{a, bd}. list_leq x sd) \<and>
                      (\<forall>a'\<in>{xs. strict_order (map fst xs)}. (\<forall>x\<in>{a, bd}. list_leq x a') \<longrightarrow> list_leq sd a') \<longrightarrow>
                      list_leq sd a') \<longrightarrow>
               list_leq (list_bsup a b) a')"
      using list_bsup_is_bsup[OF Horda Hordb] by blast
  qed
qed
end

instantiation oalist :: (linorder, Mergeable) Mergeableb
begin

instance proof qed
end

end