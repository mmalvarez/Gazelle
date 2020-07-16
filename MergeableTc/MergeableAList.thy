theory MergeableAList imports MergeableInstances HOL.List "HOL-Library.DAList"
begin

(* TODO:
clean up proofs for update and delete
try to see if we can use the linorder stuff from
Lists.thy
(we may not be able to unless we want to separate out
sortedness and distinctness as properties, which might be
a good idea, but what i have here seems to work. *)


definition strict_order ::
  "('a :: linorder) list \<Rightarrow> bool" where
"strict_order l =
  (\<forall> i j . j < length l \<longrightarrow> i < j \<longrightarrow>
     (l ! i) < (l ! j))"

lemma strict_order_unfold :
  fixes l :: "('a :: linorder) list"
  fixes i j :: nat
  assumes H  : "strict_order l"
  assumes Hln : "j < length l"
  assumes Hij : "i < j"
  shows "l ! i < l ! j" using H Hln Hij
  by(auto simp add:strict_order_def)

lemma strict_order_intro :
  fixes l :: "('a :: linorder) list"
  assumes H : "\<And> i j . j < length l \<Longrightarrow> i < j \<Longrightarrow> (l ! i) < (l ! j)"
  shows "strict_order l" using H
  by(auto simp add:strict_order_def)

(* inspired by HOL-Library.DAList *)

lemma strict_order_tl :
  fixes l :: "('a :: linorder) list"
  fixes x :: "'a"
  assumes H : "strict_order (x#l)"
  shows "strict_order l"
proof(rule strict_order_intro)
  fix i j :: nat
  assume Hlen : "j < length l"
  assume Hij : "i < j"
  show "l ! i < l ! j"
    using strict_order_unfold[OF H, of "1 + j" "1 + i"] Hlen Hij
    by(auto)
qed

lemma strict_order_distinct :
  fixes l :: "('a :: linorder) list"
  assumes Hs : "strict_order l"
  shows "distinct l" using Hs
proof(induction l)
  case Nil
  then show ?case by(auto simp add:strict_order_def)
next
  case (Cons a l)
  then show ?case
  proof(cases "a \<in> set l")
    assume Hin1 : "(strict_order l \<Longrightarrow> distinct l)"
    assume Hin2 : "strict_order (a#l)"
    assume Hin3 : "a \<in> set l"
    then obtain i where Hi: "l ! i = a" and Hil : "1 + i < length (a#l)" by(auto simp add:in_set_conv_nth)
    hence Hfound : "(a # l)!(1 + i) = a" by(auto)
    have "(a#l)! 0 < (a#l) ! (1 + i)"
      using strict_order_unfold[OF Hin2 Hil, of 0] by auto
    hence "a < a" using Hfound by auto
    hence False using less_le by auto
    then show ?thesis by auto
  next
    assume Hin1 : "(strict_order l \<Longrightarrow> distinct l)"
    assume Hin2 : "strict_order (a#l)"
    assume Hin3 : "a \<notin> set l"
    then show ?thesis using Hin1 strict_order_tl[OF Hin2] Hin3
      by auto
  qed
qed

lemma strict_order_cons :
  fixes h1 h2 :: "('a :: linorder)"
  fixes l :: "'a list"
  assumes Hleq : "h1 < h2"
  assumes Hs : "strict_order (h2 # l)"
  shows "strict_order (h1 # h2 # l)"
proof(rule strict_order_intro)
  fix i j :: nat
  assume Hj : "j < length (h1 # h2 # l)"
  assume Hij : "i < j"
  
  show "(h1 # h2 # l) ! i < (h1 # h2 # l) ! j"
  proof(cases i)
    case 0
    have H0' : "1 \<le> j" using Hij by(cases j; auto)
    then show ?thesis (*using strict_order_unfold[OF Hs] 0 *)
    proof(cases "j = 1")
      case True
      then show ?thesis using Hleq 0 by auto
    next
      case False
      hence Hfalse' : "2 \<le> j" using H0' by auto
      then obtain j' where "j = Suc j'" by(cases j; auto)
      then show ?thesis using 0 Hfalse' Hj Hleq strict_order_unfold[OF Hs, of j', of 0]
        by(auto)
    qed
  next
    case (Suc i')
    hence Hsuc' : "2 \<le> j" using Hij by auto
    then obtain j' where "j = Suc j'" by(cases j; auto)
    then show ?thesis using Suc Hsuc' Hj Hij Hleq strict_order_unfold[OF Hs, of j', of i']
      by(auto)
  qed
qed

typedef (overloaded) ('key, 'value) oalist =
  "{xs :: (('key :: linorder) * 'value) list .
       strict_order (map fst xs)}"
  morphisms impl_of Oalist
proof
  show "[] \<in> {xs :: ('key * 'value) list . strict_order (map fst xs)}"
    by(auto simp add:strict_order_def)
qed

setup_lifting type_definition_oalist

lemma alist_ext: "impl_of xs = impl_of ys \<Longrightarrow> xs = ys"
  by (simp add: impl_of_inject)

lemma alist_eq_iff: "xs = ys \<longleftrightarrow> impl_of xs = impl_of ys"
  by (simp add: impl_of_inject)

lemma impl_of_distinct [simp, intro]: "distinct (map fst (impl_of xs))"
  using impl_of[of xs] strict_order_distinct[of "map fst (impl_of xs)"] by simp

lemma Alist_impl_of [code abstype]: "Oalist (impl_of xs) = xs"
  by (rule impl_of_inverse)

(* primitives *)

fun str_ord_update :: "('key :: linorder) \<Rightarrow> 'value \<Rightarrow> ('key * 'value) list \<Rightarrow> ('key * 'value) list" where
"str_ord_update k v [] = [(k, v)]"
| "str_ord_update k v ((k', v')#t) =
    (if k < k'
     then (k, v) # (k', v') # t
     else (if k = k'
           then (k, v) # t
           else (k', v') # (str_ord_update k v t)))"

lemma str_ord_update_head :
  fixes l :: "(('key :: linorder) * 'value) list"
  shows "(hd (str_ord_update k v ((hk, hv)#l)) = (k, v) \<and> k \<le> hk) \<or>
         (hd (str_ord_update k v ((hk, hv)#l)) = (hk, hv) \<and> hk \<le> k)"
proof(-)
  consider (1) "k < hk" |
           (2) "k = hk" |
           (3) "hk < k"
    using less_linear[of k hk] by auto
  then show "(hd (str_ord_update k v ((hk, hv) # l)) = (k, v) \<and> (k \<le> hk)) \<or> (hd (str_ord_update k v ((hk, hv) # l)) = (hk, hv) \<and> hk \<le> k)"
  proof cases
    case 1
    then show ?thesis by auto
  next
    case 2 thus ?thesis by auto
  next
    case 3 thus ?thesis by auto
  qed
qed


declare [[show_types = false]]

lemma str_ord_update_correct :
  fixes l :: "(('key :: linorder) * 'value) list"
  fixes k :: 'key
  fixes v :: 'value
  assumes H : "strict_order (map fst l)"
  shows "strict_order (map fst (str_ord_update k v l))" using H
proof(induction l arbitrary: k v)
    case Nil
    then show ?case by(auto simp add:strict_order_def)
  next
    fix a :: "'key * 'value"
    fix l' :: "('key * 'value) list"
    fix k :: 'key
    fix v :: 'value
    obtain ak and av where Ha: "a = (ak, av)" by(cases a; auto)
    assume Hin1 : "\<And> k v .(strict_order (map fst l') \<Longrightarrow>
                    strict_order (map fst (str_ord_update k v l')))"
    assume Hin2: "strict_order (map fst (a # l'))"
    hence Hin2' : "strict_order (ak # map fst l')" using Ha by auto
    have Hord_l' : "strict_order (map fst l')" using strict_order_tl[OF Hin2'] by auto
    have Hin1': "strict_order (map fst (str_ord_update k v l'))" using Hin1[OF Hord_l'] by auto

    consider (1) "k < ak" |
             (2) "k = ak" |
             (3) "ak < k"
      using Ha less_linear[of k ak] by auto

    then show "strict_order (map fst (str_ord_update k v (a # l')))"
    proof cases
      case 1
      then show ?thesis using Ha Hin2' strict_order_cons[OF 1, of "map fst l'"]
        by(auto)
    next
      case 2
      then show ?thesis using Ha Hin2'
        by(auto)
    next
      case 3
      then show ?thesis
      proof(cases "(str_ord_update k v l')")
        case Nil
        show ?thesis
        proof(rule strict_order_intro)
          fix i j :: nat
          show "j < length (map fst (str_ord_update k v (a # l'))) \<Longrightarrow> i < j \<Longrightarrow>
                            map fst (str_ord_update k v (a # l')) ! i < 
                            map fst (str_ord_update k v (a # l')) ! j"
            using 3 Ha Nil by(cases i; auto)
        qed
      next
        fix a' :: "'key * 'value"
        fix l'' :: "('key * 'value) list"
        obtain a'k and a'v where Ha' : "a' = (a'k, a'v)" by(cases a'; auto) 
        assume Hcons : "(str_ord_update k v l') = a'#l''"
        show ?thesis
        proof(cases l')
          case Nil
          show ?thesis
          proof(rule strict_order_intro)
            fix i j :: nat
            show " j < length (map fst (str_ord_update k v (a # l'))) \<Longrightarrow> i < j \<Longrightarrow>
                    map fst (str_ord_update k v (a # l')) ! i <
                    map fst (str_ord_update k v (a # l')) ! j"
              using 3 Ha Nil by(cases i; auto)
          qed
        next
          fix x :: "'key * 'value"
          fix m :: "('key * 'value) list"
          obtain xk and xv where Hx : "x = (xk, xv)" by (cases x; auto)
          assume Hcons2 : "l' = x#m"
          consider (C3_1) "(hd (str_ord_update k v l') = (xk, xv))" and "xk \<le> k" |
                   (C3_2) "(hd (str_ord_update k v l')) = (k, v)" and "k \<le> xk"
            using Hcons Ha' Hcons2 Hx str_ord_update_head[of k v xk xv m]
            by( auto simp del:str_ord_update.simps)
          then show ?thesis
          proof cases
            case C3_1
            have "ak < xk" using Ha Ha' Hx Hcons2 strict_order_unfold[OF Hin2', of 1 0] by auto
            then show ?thesis using C3_1 3 Ha Ha' Hx Hcons Hcons2 Hin1' apply(auto)
              apply(rule_tac strict_order_cons) apply(auto)
              done
          next
            case C3_2
            then show ?thesis using 3 Ha Ha' Hx Hcons Hcons2 Hin1' apply(auto)
              apply(rule_tac strict_order_cons) apply(auto)
              done
          qed
        qed
      qed
    qed
  qed
     

lift_definition lookup :: "('key :: linorder, 'value) oalist \<Rightarrow> 'key \<Rightarrow> 'value option" is map_of  .

lift_definition empty :: "('key :: linorder, 'value) oalist" is "[]"
  by(simp add:strict_order_def)

lift_definition update :: "('key :: linorder) \<Rightarrow> 'value \<Rightarrow> ('key, 'value) oalist \<Rightarrow> ('key, 'value) oalist"
  is str_ord_update
proof(-)
  fix k :: "'key :: linorder"
  fix v :: "'value"
  fix l :: "('key * 'value) list"
  assume H : "strict_order (map fst l)"
  show "strict_order (map fst (str_ord_update k v l))" using str_ord_update_correct[OF H] by auto
qed

value "update (1 :: nat) (True) empty"

fun str_ord_delete :: "('key :: linorder) \<Rightarrow> ('key * 'value) list \<Rightarrow> ('key * 'value) list" where
"str_ord_delete k [] = []"
| "str_ord_delete k ((k', v')#t) =
    (if k < k'
     then (k', v')#t
     else (if k = k'
           then t
           else (k', v') # (str_ord_delete k t)))"


lemma str_ord_delete_head :
  fixes l :: "(('key :: linorder) * 'value) list"
  assumes H : "strict_order (hk # map fst l)"
  shows "(hd (str_ord_delete k ((hk, hv)#l)) = (hk, hv) \<and> hk \<noteq> k) \<or>
         (\<exists> k' v' . hd (str_ord_delete k ((hk, hv)#l)) = (k', v') \<and> k = hk \<and> hk < k') \<or>
         (l = [])"
proof(cases l)
  case Nil
  then show ?thesis by auto
next
  fix a l'
  assume Hcons : "l = a # l'"
  obtain ak and av where Ha: "a = (ak, av)" by(cases a; auto)
  consider (1) "k < hk" |
           (2) "k = hk" |
           (3) "hk < k"
    using less_linear[of k hk] by auto
  then show "hd (str_ord_delete k ((hk, hv) # l)) = (hk, hv) \<and> hk \<noteq> k \<or>
    (\<exists>k' v'. hd (str_ord_delete k ((hk, hv) # l)) = (k', v') \<and> k = hk \<and> hk < k') \<or> l = []"
  proof cases
    case 1
    then show ?thesis by auto
  next
    case 2 thus ?thesis using H Hcons Ha strict_order_unfold[OF H, of 1 0] by(auto)
  next
    case 3 thus ?thesis by auto
  qed
qed

lemma strict_order_2nd :
  assumes H : "strict_order (h1 # h2 # t)"
  shows "strict_order (h1 # t)"
proof(rule strict_order_intro)
  fix i j :: nat
  assume Hlen : "j < length (h1 # t)"
  assume Hlt : "i < j"
  show "(h1 # t) ! i < (h1 # t) ! j"
  proof(cases i)
    case 0
    obtain j' where "j = 1 + j'" using Hlt by (cases j; auto)
    then show ?thesis using 0 Hlen strict_order_unfold[OF H, of "1 + j" "0"] by(auto)
  next
    case (Suc nat)
    obtain j' where "j = 1 + j'" using Hlt by (cases j; auto)
    then show ?thesis using Suc Hlen Hlt strict_order_unfold[OF H, of "1 + j" "1 + i"] by(auto)  
  qed
qed

(* need a similar cons lemma for this one. *)
lemma str_ord_delete_correct :
  fixes k :: "'key :: linorder"
  fixes l :: "('key * 'value) list"
  assumes H : "strict_order (map fst l)"
  shows "strict_order (map fst (str_ord_delete k l))" using H
proof(induction l)
  case Nil
  then show ?case by(auto simp add:strict_order_def)
next
  fix a :: "('key * 'value)"
  fix l' :: "('key * 'value) list"
  assume Hi1 : "(strict_order (map fst l') \<Longrightarrow> strict_order (map fst (str_ord_delete k l')))"
  assume Hi2 : "strict_order (map fst (a # l'))"
  obtain ak and av where Ha: "a = (ak, av)" by(cases a; auto)
  
  have Hi1' : "strict_order (map fst (str_ord_delete k l'))" using Ha Hi1 Hi2 strict_order_tl[of ak "map fst l'"]
    by(auto)

  consider (1) "k < ak" |
           (2) "k = ak" |
           (3) "ak < k"
    using less_linear[of k ak] by auto
  then show "strict_order (map fst (str_ord_delete k (a # l')))"
  proof cases
    case 1
    then show ?thesis using Ha Hi2 by(auto)
  next
    case 2
    have Hi2' : "strict_order (map fst l')" using Ha Hi2 strict_order_tl[of ak "map fst l'"] by auto
    then show ?thesis using 2 Ha by(auto)
  next
    case 3
    have Hi2' : "strict_order (map fst l')" using Ha Hi2 strict_order_tl[of ak "map fst l'"] by auto
    show ?thesis using 3
    proof(cases "(str_ord_delete k l')")
      case Nil
      show ?thesis
      proof(rule strict_order_intro)
        fix i j :: nat
        show "j < length (map fst (str_ord_delete k (a # l'))) \<Longrightarrow>
           i < j \<Longrightarrow> map fst (str_ord_delete k (a # l')) ! i < map fst (str_ord_delete k (a # l')) ! j"
          using 3 Ha Nil by(cases i; auto)
      qed
    next
      fix a' :: "'key * 'value"
      fix l'' :: "('key * 'value) list"
      obtain a'k and a'v where Ha' : "a' = (a'k, a'v)" by(cases a'; auto) 
      assume Hcons : "(str_ord_delete k l') = a'#l''"
      show ?thesis
      proof(cases l')
        case Nil
        show ?thesis
        proof(rule strict_order_intro)
          fix i j :: nat
          show "j < length (map fst (str_ord_delete k (a # l'))) \<Longrightarrow>
           i < j \<Longrightarrow> map fst (str_ord_delete k (a # l')) ! i < map fst (str_ord_delete k (a # l')) ! j"
            using 3 Ha Nil by(cases i; auto split:if_split_asm)
        qed
      next
        fix x :: "'key * 'value"
        fix m :: "('key * 'value) list"
        obtain xk and xv where Hx : "x = (xk, xv)" by (cases x; auto)
        assume Hcons2 : "l' = x#m"
        have Hi2'' : "strict_order (xk # map fst m)" using Hcons2 Hx Hi2' by auto
        consider (C3_1) "hd (str_ord_delete k ((xk, xv)#m)) = (xk, xv)" and "xk \<noteq> k" |
                 (C3_2) k' v' where "hd (str_ord_delete k ((xk, xv)#m)) = (k', v')" and "k = xk" and "xk < k'" |
                 (C3_3) "(l' = [])"
          using str_ord_delete_head[OF Hi2'', of k xv] Hcons Hcons2 Ha Hi2' Hx by(auto split:if_split_asm)
        then show ?thesis
        proof cases
          case C3_1
          have Hcons_a_x : "strict_order (ak # xk # map fst m)" using Hcons2 Hx Ha Hi2 by(auto)
          show ?thesis using C3_1 3 Ha  Ha' Hx Hi1' strict_order_unfold[OF Hcons_a_x, of 1 0] Hcons Hcons2
            apply(auto)
            apply(rule_tac strict_order_cons) apply(auto split:if_splits)
            done
        next
          case C3_2
          have Hcons_a_x : "strict_order (ak # xk # map fst m)" using Hcons2 Hx Ha Hi2 by(auto)
          show ?thesis using 3 Ha  Ha' Hx Hi1' Hcons2 Hcons_a_x strict_order_2nd[OF Hcons_a_x]
            strict_order_unfold[OF Hcons_a_x, of 1 0]
            apply(auto)
            apply(rule_tac strict_order_cons) apply(auto split:if_splits)
            done
        next
          case C3_3
          then show ?thesis using Ha by(auto simp add:strict_order_def)
        qed
      qed
    qed
  qed
qed

lift_definition delete :: "('key :: linorder) \<Rightarrow> ('key, 'value) oalist \<Rightarrow> ('key, 'value) oalist"
is str_ord_delete
proof(-)
  fix k :: "'key :: linorder"
  fix l :: "('key * 'value) list"
  assume H : "strict_order (map fst l)"
  show "strict_order (map fst (str_ord_delete k l))" using str_ord_delete_correct[OF H] by auto
qed
value "DAList.update (3 :: nat) True DAList.empty"

fun to_oalist :: "(('a :: linorder) * 'b) list \<Rightarrow> ('a, 'b) oalist" where
"to_oalist [] = empty"
| "to_oalist ((a, b)#l) = 
     update a b (to_oalist l)"

value "impl_of (to_oalist ([(1 :: nat, True)]))"

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
  assumes Hord1 : "strict_order (map fst l1)"
  assumes Hord2 : "strict_order (map fst l2)"
  assumes H : "list_leq l1 l2"
  assumes Helm : "(k, v) \<in> set l1"
  shows "(\<exists> v' . (k, v') \<in> set l2 \<and> v <[ v')"
   using Hord1 Hord2 H Helm
proof(induction l1 arbitrary: l2 k v)
  case Nil
  then show ?case by auto
next
  fix a :: "'a * 'b"
  fix l1 l2 :: "('a * 'b) list"
  fix k :: 'a
  fix v :: 'b
  assume HI1 :
    "(\<And>l2 k v.
           strict_order (map fst l1) \<Longrightarrow>
           strict_order (map fst l2) \<Longrightarrow> list_leq l1 l2 \<Longrightarrow> (k, v) \<in> set l1 \<Longrightarrow> 
           \<exists>v'. (k, v') \<in> set l2 \<and> v <[ v')"
  assume HI2 :
       "strict_order (map fst (a # l1))"
  assume  HI3 :
       "strict_order (map fst l2)" 
  assume HI4 : "list_leq (a # l1) l2"
  assume HI5 : "(k, v) \<in> set (a # l1)"
  obtain ak and av where Ha : "a = (ak, av)" by (cases a; auto)
  have HI2' : "strict_order (map fst l1)" using Ha strict_order_tl[of ak "map fst l1"] HI2 by auto
  have Distinct1 : "distinct (ak # map fst l1)" using Ha strict_order_distinct[OF HI2] by auto

  show "\<exists>v'. (k, v') \<in> set l2 \<and> v <[ v'"
  proof(cases "a = (k, v)")
    case True
    then show ?thesis using HI4 map_of_SomeD[of l2 k] by(auto split:option.splits)
  next
    case False
    have HFalse' : "(k, v) \<in> set l1" using HI5 False by auto
    have HI4' : "list_leq l1 l2" using Ha HI4 by (auto split:option.splits)
    show ?thesis using HI1[OF HI2' HI3 HI4' HFalse'] by auto
  qed
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

lemma list_leq_keys :
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
        using Cons Ha list_leq_keys[OF HI6 Ha2v]
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
      obtain v' where  Elv' : "(xk, v') \<in> set l2'" and Leqv' : "xv <[ v'" using list_leqD[OF Hord1 Hord2 Hleq1 H'] by auto
      obtain v'' where Elv'' : "(xk, v'') \<in> set l1'" and Leqv'' : "v' <[ v''" using list_leqD[OF Hord2 Hord1 Hleq2 Elv'] by auto
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
      obtain v' where  Elv' : "(xk, v') \<in> set l1'" and Leqv' : "xv <[ v'" using list_leqD[OF Hord2 Hord1 Hleq2 H'] by auto
      obtain v'' where Elv'' : "(xk, v'') \<in> set l2'" and Leqv'' : "v' <[ v''" using list_leqD[OF Hord1 Hord2 Hleq1 Elv'] by auto
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
(*
lemma list_complete
  fixes l1 l2 :: "('a :: linorder * 'b :: Pordc) list"
  

declare [[show_types]]
*)
(*
instantiation oalist :: (linorder, Pordc) Pordc
begin

instance proof
  fix a b :: "('a :: linorder, 'b :: Pordc) oalist"
  assume H : "has_ub {a, b}"
  then obtain ub where H : "is_ub {a, b} ub" by (auto simp add:has_ub_def)

  show "has_sup {a, b}"
  proof(rule has_sup_intro)

  show "has_sup {a, b}" using H unfolding has_ub_def has_sup_def is_sup_def is_least_def is_ub_def pleq_oalist
  proof(transfer)
    fix 
*)
(*
instantiation oalist :: (linorder, Pord) Pordb
begin
  definition bot_oalist :
    "\<bottom> = empty"

instance proof
*)
end