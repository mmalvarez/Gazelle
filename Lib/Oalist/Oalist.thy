theory Oalist imports Main
begin

(* Implementation of association lists with ordered keys
 * This is based somewhat on the implementation of association lists from
 * HOL/Library/AList.thy and HOL/Library/DAlist.thy, with the twist that
 * keys are required to be in strictly increasing order.
 * This gives us the property that all sets of (key, value) pairs have a canonical representation,
 * which is necessary to satisfy the ordering laws used by Gazelle
 * (see Mergeable/Pord.thy, Mergeable/Mergeable.thy)
 *
 * TODO: Implementations given here are not necessarily as efficient as they could be
 *)

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

type_synonym ('key) kmap =
  "('key, unit) oalist"

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

fun to_oalist :: "(('a :: linorder) * 'b) list \<Rightarrow> ('a, 'b) oalist" where
"to_oalist [] = empty"
| "to_oalist ((a, b)#l) = 
     update a b (to_oalist l)"

lift_definition get :: "('key, 'value) oalist \<Rightarrow> ('key :: linorder) \<Rightarrow>  'value option"
is map_of .

definition has_key :: "('key) kmap \<Rightarrow> 'key :: linorder \<Rightarrow> bool" where
"has_key l k = (get l k = Some ())"

(* possibly useful for semantics - if a key map describing updated values
   has only one entry, we can pull it out. *)
definition kmap_singleton :: "('key :: linorder) kmap \<Rightarrow> 'key" where
"kmap_singleton l =
  (case impl_of l of
    [k] \<Rightarrow> fst k)"

definition add_key :: "('key) kmap \<Rightarrow> 'key :: linorder \<Rightarrow> 'key kmap" where
"add_key l k = update k () l"

(* some useful functions for combining oalists *)
fun oalist_merge' :: "(('key :: linorder) * 'value) list \<Rightarrow> ('key, 'value) oalist \<Rightarrow> ('key, 'value) oalist"
  where
"oalist_merge' [] l2 = l2"
| "oalist_merge' ((k,v)#t) l2 =
   update k v (oalist_merge' t l2)"

lift_definition oalist_merge ::
"('key :: linorder, 'value) oalist \<Rightarrow> ('key, 'value) oalist \<Rightarrow> ('key, 'value) oalist"
is oalist_merge' .

(* zip two oalists together using the given functions -
 * one for both keys present, one for left key present, one for right key present *)
fun str_ord_zip ::
  "('key \<Rightarrow> 'value1 \<Rightarrow> 'value2 \<Rightarrow> 'value3 ) \<Rightarrow>
   ('key \<Rightarrow> 'value1 \<Rightarrow> 'value3) \<Rightarrow>
   ('key \<Rightarrow> 'value2 \<Rightarrow> 'value3) \<Rightarrow>
   (('key :: linorder) * 'value1) list \<Rightarrow> ('key * 'value2) list \<Rightarrow>
   ('key * 'value3) list" where
"str_ord_zip flr fl fr [] [] = []"
| "str_ord_zip flr fl fr ((lk, lh)#lt) [] =
    (lk, fl lk lh)#str_ord_zip flr fl fr lt []"
| "str_ord_zip flr fl fr [] ((rk, rh)#rt) =
    (rk, fr rk rh)#str_ord_zip flr fl fr [] rt"
| "str_ord_zip flr fl fr ((lk, lh)#lt) ((rk, rh)#rt) =
  (if (lk < rk)
   then (lk, fl lk lh) # str_ord_zip flr fl fr lt ((rk, rh)#rt)
   else (if lk = rk
         then (lk, flr lk lh rh) # str_ord_zip flr fl fr lt rt
         else (rk, fr rk rh) # str_ord_zip flr fl fr ((lk, lh) # lt) (rt)))"
(*
lemma str_ord_zip_induct_help :
  fixes P :: "(('key :: linorder) * 'value) list \<Rightarrow> ('key * 'value) list \<Rightarrow> bool"
  assumes Hl : "\<And> l . P l []"
  assumes Hr : "\<And> r . P [] r"
  assumes Hlt : "\<And> lk rk lv rv lt rt .
                  lk < rk \<Longrightarrow> P lt ((rk, rv)#rt) \<Longrightarrow> P ((lk, lv)#lt) ((rk, rv)#rt)"
  assumes Heq : "\<And> lk rk lv rv lt rt .
                  lk = rk \<Longrightarrow> P lt rt \<Longrightarrow> P ((lk, lv)#lt) ((rk, rv)#rt)"
  assumes Hgt : "\<And> lk rk lv rv lt rt .
                  lk > rk \<Longrightarrow> P ((lk, lv)#lt) rt \<Longrightarrow> P ((lk, lv)#lt) ((rk, rv)#rt)"
  shows "P l r" using Hl Hr Hlt Heq Hgt
proof(induction l arbitrary: r)
  case Nil
  then show ?case by auto
next
  case (Cons lh1 lt1 r)
  then show ?case 
*)
(*
  proof(cases r)
    case Nil' : Nil
    then show ?thesis using Cons  by auto
  next
    case Cons' : (Cons rh1 rt1)

    obtain lk1 lv1 where Lh : "lh1 = (lk1, lv1)"
      by(cases lh1; auto)

    obtain rk1 rv1 where Rh : "rh1 = (rk1, rv1)"
      by(cases rh1; auto)

    consider (LT) "lk1 < rk1" |
             (EQ) "lk1 = rk1" |
             (GT) "lk1 > rk1"
      using less_linear[of lk1 rk1] by blast
  
    then show ?thesis
    proof cases
      case LT
      then show ?thesis sorry
    next
      case EQ
      then show ?thesis using Cons unfolding Cons' sorry
    next
      case GT

      have Conc' : "P ((lk1, lv1) # lt1) (rt1)"
        using Cons.IH[OF Cons.prems(1) Cons.prems(2) Cons.prems(3) Cons.prems(4)] 

      show ?thesis
        using Cons.prems(5)[OF GT Conc'] unfolding Lh Rh Cons' by auto
    qed
*)


(* NB this is just List.list_induct2' *)
(*
lemma either_list_induct :
  assumes H0 : "P [] []"
  assumes Hl : "\<And> lh lt r . P lt r \<Longrightarrow> P (lh#lt) r"
  assumes Hr : "\<And> rh rt l . P l rt \<Longrightarrow> P l (rh#rt)"
  
  shows "P l r" using H0 Hl Hr 
proof(induction l arbitrary: r)
  case Nil
  then show ?case 
  proof(induction x)
    case Nil' : Nil
    then show ?case by auto
  next
    case Cons' : (Cons rh rt)
    then show ?case 
      by auto
  qed
next
  case (Cons lh lt)
  then show ?case
  proof(induction x arbitrary: lh lt)
    case Nil' : Nil
    then show ?case by auto
  next
    case Cons' : (Cons rh rt)
    then show ?case 
      by(auto)
  qed
qed
*)
(*
lemma either_list_induct2 :
  assumes H0 : "P [] []"
  assumes Hl : "\<And> lh lt r . P lt r \<Longrightarrow> P (lh#lt) r"
  assumes Hr : "\<And> rh rt l . P l rt \<Longrightarrow> P l (rh#rt)"
  
  shows "P l r" using H0 Hl Hr 
proof(induction l arbitrary: r)
  case Nil
  then show ?case 
  proof(induction x)
    case Nil' : Nil
    then show ?case by auto
  next
    case Cons' : (Cons rh rt)
    then show ?case 
      by auto
  qed
next
  case (Cons lh lt)
  then show ?case
  proof(induction x arbitrary: lh lt)
    case Nil' : Nil
    then show ?case by auto
  next
    case Cons' : (Cons rh rt)
    then show ?case 
      by(auto)
  qed
qed
*)

(*
lemma str_ord_zip_correct' :
  fixes k :: "'key :: linorder"
  fixes ll :: "('key * 'value1) list"
  fixes lr :: "('key * 'value2) list"
  assumes Hl : "strict_order (map fst (ll))"
  assumes Hr : "strict_order (map fst (rl))"
  shows "strict_order (map fst (str_ord_zip flr fl fr ll rl))"
  using Hl Hr
proof(induction ll arbitrary: rl)
  case Nil
  then show ?case sorry
next
  case (Cons lh1 ll)

  obtain lk1 lv1 where Lh : "lh1 = (lk1, lv1)"
    by(cases lh1; auto)

  show ?case
  proof(cases rl)
    case Nil

    then show ?thesis using Cons Lh
      sorry
  next
    case Cons' : (Cons rh1 rl1)

    obtain rk1 rv1 where Rh : "rh1 = (rk1, rv1)"
      by(cases rh1; auto)

    show ?thesis using Cons Cons' Lh Rh
      apply(auto)
  qed

  show ?case using Cons Lh
    apply(auto)
qed


lemma str_ord_zip_correct' :
  fixes k :: "'key :: linorder"
  fixes ll :: "('key * 'value1) list"
  fixes lr :: "('key * 'value2) list"
  assumes Hl : "strict_order (map fst ((lk, lv)# ll))"
  assumes Hr : "strict_order (map fst ((rk, rv)# rl))"
  shows "strict_order (map fst (str_ord_zip flr fl fr ll rl))"
  using Hl Hr
proof(induction ll arbitrary: lk lv rk rv rl)
  case Nil
  then show ?case sorry
next
  case (Cons lh1 ll)

  obtain lk1 lv1 where Lh : "lh1 = (lk1, lv1)"
    by(cases lh1; auto)

  show ?case
  proof(cases rl)
    case Nil

    then show ?thesis using Cons Lh
      apply(auto)
  next
    case (Cons a list)
    then show ?thesis sorry
  qed

  show ?case using Cons Lh
    apply(auto)
qed
*)

lemma strict_order_singleton :
  "strict_order [x]"
proof(rule strict_order_intro)
  fix i j
  assume H1 : "j < length [x]"
  assume H2 : "i < j" 
  show "[x] ! i < [x] ! j" using H1 H2
    by(auto)
qed

lemma str_ord_zip_correct' :
  fixes k :: "'key :: linorder"
  fixes ll :: "('key * 'value1) list"
  fixes lr :: "('key * 'value2) list"
  assumes Hl : "strict_order (map fst (lh#ll))"
  assumes Hr : "strict_order (map fst (rh#rl))"
  shows "strict_order (map fst (str_ord_zip flr fl fr (lh#ll) (rh#rl)))"
  using Hl Hr
proof(induction ll arbitrary: lh rh rl)
  case Nil
  obtain lk lv where Lh : "lh = (lk, lv)"
    by(cases lh; auto)

  obtain rk rv where Rh : "rh = (rk, rv)"
    by(cases rh; auto)

  show ?case using Lh Rh Nil
    sorry
next
  case (Cons lh1 ll)

  obtain lk lv where Lh : "lh = (lk, lv)"
    by(cases lh; auto)

  obtain rk rv where Rh : "rh = (rk, rv)"
    by(cases rh; auto)

  obtain lk1 lv1 where Lh1 : "lh1 = (lk1, lv1)"
    by(cases lh1; auto)

  show ?case using Cons Lh Rh Lh1
    apply(auto)

qed
  case 1

  obtain lk lv where Lh : "lh = (lk, lv)"
    by(cases lh; auto)

  obtain rk rv where Rh : "rh = (rk, rv)"
    by(cases rh; auto)

  then show ?case using Lh Rh strict_order_singleton strict_order_cons
    by(auto)
next
  case (2 lh1 lt)

  obtain lk lv where Lh : "lh = (lk, lv)"
    by(cases lh; auto)

  obtain lk1 lv1 where Lh1 : "lh1 = (lk1, lv1)"
    by(cases lh1; auto)

  obtain rk rv where Rh : "rh = (rk, rv)"
    by(cases rh; auto)

  show ?case using 2 Lh Lh1 Rh
      sorry
next
  case (3 rh1 rt)

  obtain lk lv where Lh : "lh = (lk, lv)"
    by(cases lh; auto)

  obtain rk rv where Rh : "rh = (rk, rv)"
    by(cases rh; auto)

  obtain rk1 rv1 where Rh1 : "rh1 = (rk1, rv1)"
    by(cases rh1; auto)

  show ?case using 3 Lh Rh Rh1
    sorry
next
  case (4 lh1 lt rh1 rt)

  obtain lk0 lv0 where Lh : "lh = (lk0, lv0)"
    by(cases lh; auto)

  obtain lk1 lv1 where Lh1 : "lh1 = (lk1, lv1)"
    by(cases lh1; auto)

  obtain rk0 rv0 where Rh : "rh = (rk0, rv0)"
    by(cases rh; auto)

  obtain rk1 rv1 where Rh1 : "rh1 = (rk1, rv1)"
    by(cases rh1; auto)

  consider (LT) "lk0 < rk0" |
           (EQ) "lk0 = rk0" |
           (GT) "lk0 > rk0"
    using less_linear[of lk0 rk0] by blast

  then show ?case
  proof cases
    case LT
    then show ?thesis using "4.prems" "4.IH" Lh Rh 
      apply(auto)
  next
    case EQ
    then show ?thesis sorry
  next
    case GT
    then show ?thesis sorry
  qed

  then show ?case sorry
qed
  case Nil
  then show ?case 
  proof(cases lr)
    case Nil' : Nil
    then show ?thesis using Nil by auto
  next
    case (Cons rh rt)
    then show ?thesis
      apply(auto)
  qed
next
  case (Cons a ll)
  then show ?case sorry
qed


lemma str_ord_zip_correct' :
  fixes k :: "'key :: linorder"
  fixes ll :: "('key * 'value1) list"
  fixes lr :: "('key * 'value2) list"
  assumes Hl : "strict_order (map fst (lh#ll))"
  assumes Hr : "strict_order (map fst (rh#rl))"
  shows "strict_order (map fst (str_ord_zip flr fl fr (lh#ll) (rh#rl)))"
  using Hl Hr
proof(induction ll rl arbitrary: lh rh rule:list_induct2')
  case 1

  obtain lk lv where Lh : "lh = (lk, lv)"
    by(cases lh; auto)

  obtain rk rv where Rh : "rh = (rk, rv)"
    by(cases rh; auto)

  then show ?case using Lh Rh strict_order_singleton strict_order_cons
    by(auto)
next
  case (2 lh1 lt)

  obtain lk lv where Lh : "lh = (lk, lv)"
    by(cases lh; auto)

  obtain lk1 lv1 where Lh1 : "lh1 = (lk1, lv1)"
    by(cases lh1; auto)

  obtain rk rv where Rh : "rh = (rk, rv)"
    by(cases rh; auto)

  show ?case using 2 Lh Lh1 Rh
      sorry
next
  case (3 rh1 rt)

  obtain lk lv where Lh : "lh = (lk, lv)"
    by(cases lh; auto)

  obtain rk rv where Rh : "rh = (rk, rv)"
    by(cases rh; auto)

  obtain rk1 rv1 where Rh1 : "rh1 = (rk1, rv1)"
    by(cases rh1; auto)

  show ?case using 3 Lh Rh Rh1
    sorry
next
  case (4 lh1 lt rh1 rt)

  obtain lk0 lv0 where Lh : "lh = (lk0, lv0)"
    by(cases lh; auto)

  obtain lk1 lv1 where Lh1 : "lh1 = (lk1, lv1)"
    by(cases lh1; auto)

  obtain rk0 rv0 where Rh : "rh = (rk0, rv0)"
    by(cases rh; auto)

  obtain rk1 rv1 where Rh1 : "rh1 = (rk1, rv1)"
    by(cases rh1; auto)

  consider (LT) "lk0 < rk0" |
           (EQ) "lk0 = rk0" |
           (GT) "lk0 > rk0"
    using less_linear[of lk0 rk0] by blast

  then show ?case
  proof cases
    case LT
    then show ?thesis using "4.prems" "4.IH" Lh Rh 
      apply(auto)
  next
    case EQ
    then show ?thesis sorry
  next
    case GT
    then show ?thesis sorry
  qed

  then show ?case sorry
qed
  case Nil
  then show ?case 
  proof(cases lr)
    case Nil' : Nil
    then show ?thesis using Nil by auto
  next
    case (Cons rh rt)
    then show ?thesis
      apply(auto)
  qed
next
  case (Cons a ll)
  then show ?case sorry
qed



end