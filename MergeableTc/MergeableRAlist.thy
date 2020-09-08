theory MergeableRAlist
  imports MergeableAList

begin

(* implementation and Mergeable
   instances for a recursive version of ordered alist
   (i.e., ordered alist where values are ordered alists of the same type)
   this is needed for e.g. closures. *)

fun alist_map_val ::
  "('v1 \<Rightarrow> 'v2) \<Rightarrow> ('key * 'v1) list \<Rightarrow> ('key * 'v2) list" where
"alist_map_val f l =
  map (map_prod id f) l"
(*
"alist_map_val f [] = []"
| "alist_map_val f ((k, v)#t) =
   ((k, f v)# alist_map_val f t)"
*)

lemma strict_order_nil : "strict_order []"
  by(rule strict_order_intro; auto)

lift_definition
  oalist_map_val ::
  "('v1 \<Rightarrow> 'v2) \<Rightarrow> ('key :: linorder, 'v1) oalist \<Rightarrow> ('key, 'v2) oalist"
 is alist_map_val
  by (auto intro: strict_order_nil)

(* another option: maybe we can somehow represent the alist in a way that isn't explicitly
   recursive.
e.g. suppose we want an alist clos = (str \<Rightarrow> (int + clos))
maybe we can capture the nesting in the index?

(str * closid \<Rightarrow> (int + closid))?
problem: risk of infinite recursion
maybe this is OK though. all we really need to do is reconstruct the closure stored at each thing.
if the closures are infinite our implementation will spin. but maybe this is a price worth paying.

so, at closid = 0
*)

type_synonym closid = nat

instantiation prod :: (linorder, linorder) linorder
begin

definition prod_lo_leq :
"p1 \<le> p2 =
  (fst p1 < fst p2 \<or> 
  (fst p1 = fst p2 \<and> snd p1 \<le> snd p2))"

definition prod_lo_lt :
"p1 < p2 =
  (fst p1 < fst p2 \<or>
  (fst p1 = fst p2 \<and> snd p1 < snd p2))"

instance proof
  fix x y :: "('a * 'b)"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by(cases x; cases y; auto simp add:prod_lo_leq prod_lo_lt)
next
  fix x :: "('a * 'b)"
  show "x \<le> x"
    by(cases x; auto simp add:prod_lo_leq)
next
  fix x y z :: "('a * 'b)"
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by(cases x; cases y; cases z; auto simp add:prod_lo_leq)
next
  fix x y :: "('a * 'b)"
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by(cases x; cases y; auto simp add:prod_lo_leq prod_lo_lt)
next
  fix x y :: "('a * 'b)"
  show "x \<le> y \<or> y \<le> x"
    by(cases x; cases y; auto simp add:prod_lo_leq prod_lo_lt)
qed
end

fun list_lo_leq' ::
  "('a :: linorder) list \<Rightarrow> ('a :: linorder) list \<Rightarrow> bool" where
"list_lo_leq' [] _ = True"
| "list_lo_leq' (h#t) [] = False"
| "list_lo_leq' (h1#t1) (h2#t2) =
   (h1 < h2 \<or>
   (h1 = h2 \<and> list_lo_leq' t1 t2))"

fun list_lo_lt' ::
  "('a :: linorder) list \<Rightarrow> ('a :: linorder) list \<Rightarrow> bool" where
"list_lo_lt' [] [] = False"
| "list_lo_lt' [] (h#t) = True"
| "list_lo_lt' (h#t) [] = False"
| "list_lo_lt' (h1#t1) (h2#t2) =
   (h1 < h2 \<or>
   (h1 = h2 \<and> list_lo_lt' t1 t2))"


lemma list_lo_lt'_imp_leq' :
"list_lo_lt' l1 l2 \<Longrightarrow> list_lo_leq' l1 l2"
proof(induction l1 arbitrary: l2)
  case Nil
  then show ?case by auto
next
  case (Cons a l1)
  then show ?case 
    by(cases l2; auto)
qed

lemma list_lo_lt'_nosym :
  "list_lo_lt' l1 l2 \<Longrightarrow> list_lo_lt' l2 l1 \<Longrightarrow> False"
proof(induction l1 arbitrary: l2)
  case Nil
  then show ?case by(cases l2; auto)
next
  case (Cons a l1)
  then show ?case by(cases l2; auto)
qed

lemma list_lo_lt'_irref :
  "list_lo_lt' l l \<Longrightarrow> False"
proof(induction l)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case by auto
qed

lemma list_lo_leq'_lt'_or_eq :
  "list_lo_leq' l1 l2 \<Longrightarrow>
   list_lo_lt' l1 l2 \<or> l1 = l2"
proof(induction l1 arbitrary: l2)
  case Nil
  then show ?case by(cases l2; auto)
next
  case (Cons a l1)
  then show ?case
    by(cases l2; auto)
qed

instantiation list :: (linorder) linorder
begin

definition list_lo_leq :
"l1 \<le> l2 = list_lo_leq' l1 l2"

definition list_lo_lt :
"l1 < l2 = list_lo_lt' l1 l2"

instance proof
  fix x y :: "'a list"

  have L2R_1 : "x < y \<Longrightarrow> x \<le> y" 
    unfolding list_lo_leq list_lo_lt using list_lo_lt'_imp_leq' by auto

  have L2R_2 : "x < y \<Longrightarrow> \<not> y \<le> x"
    unfolding list_lo_leq list_lo_lt
  proof
    assume HC1 : "list_lo_lt' x y"
    assume HC2 : "list_lo_leq' y x"

    consider (1) "list_lo_lt' y x" | (2) "x = y"
      using list_lo_leq'_lt'_or_eq[OF HC2]  by auto
    then show False
    proof cases
      case 1
      then show ?thesis using list_lo_lt'_nosym[OF HC1 1] by auto
    next
      case 2
      then show ?thesis using HC1 list_lo_lt'_irref[of x] by auto
    qed
  qed

  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" using L2R_1 L2R_2 list_lo_leq'_lt'_or_eq[of x y]
    unfolding list_lo_leq list_lo_lt
    by(blast)
next
  fix x :: "'a list"
  show "x \<le> x"
  proof(induction x)
    case Nil
    then show ?case by(auto simp add:list_lo_leq)
  next
    case (Cons a x)
    then show ?case by(auto simp add:list_lo_leq)
  qed
next
  fix x y z :: "'a list"
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  proof(induction x arbitrary: y z)
    case Nil
    then show ?case by(auto simp add:list_lo_leq)
  next
    case (Cons a x)
    then show ?case 
      by(cases y; cases z; auto simp add:list_lo_leq)
  qed
next
  fix x y :: "'a list"
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
  proof(induction x arbitrary: y)
    case Nil
    then show ?case by(cases y; auto simp add: list_lo_leq)
  next
    case (Cons a x)
    then show ?case by(cases y; auto simp add: list_lo_leq)
  qed
next
  fix x y :: "'a list"
  show "x \<le> y \<or> y \<le> x"
  proof(induction x arbitrary: y)
    case Nil
    then show ?case by(cases y; auto simp add: list_lo_leq)
  next
    case (Cons a x)
    then show ?case by(cases y; auto simp add: list_lo_leq)
  qed
qed
end

type_synonym ('k, 'v) alist = "('k * 'v) list"

(* want 'v option here. problem - is this going to create issues for our data ordering? *)
type_synonym ('k, 'v) roalist' =
  "(('k list) * ('v + unit)) list"

(* also this lacks a canonical representation, I think *)
(*
type_synonym ('k, 'v) recclos =
  "(('k list), ('v + unit)) alist"
*)

fun roalist_gather' :: "('k :: linorder, 'v) roalist' \<Rightarrow> 'k \<Rightarrow> ('k :: linorder, 'v) roalist'" where
"roalist_gather' [] _ = []"
| "roalist_gather' (([], vh)#l) k = roalist_gather' l k"
| "roalist_gather' (((khh#kht), vh)#l) k = 
  ( if k = khh then (kht, vh) # roalist_gather' l k
    else roalist_gather' l k)"

lemma roalist_gather'_elem :
  assumes Hord : "strict_order (map fst l)"
  assumes H : "(kt, v) \<in> set (roalist_gather' l k)"
  shows "(k#kt, v) \<in> set l" using Hord H
proof(induction l arbitrary: k kt v)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then have Ord_tl : "strict_order (map fst l)" using strict_order_tl by auto
  obtain k1 v1 where H1 : "(a = (k1, v1))" by (cases a; auto)

  then show ?case
  proof(cases k1)
    assume Nil' : "k1 = []"
    then show ?thesis using Cons H1 Ord_tl by auto
  next
    fix h1 t1
    assume Cons' : "k1 = h1 # t1"
    then show ?thesis
    proof(cases "h1 = k")
      case False
      then show ?thesis using Cons H1 Cons' Ord_tl by(auto)
    next
      case True
      then show ?thesis using Cons.prems Cons.IH[OF Ord_tl] H1 Cons' by(auto)
    qed
  qed
qed

lemma oalist_gather'_order :
  assumes Hord : "strict_order (map fst l)"
  shows "strict_order (map fst (roalist_gather' l k))" using Hord
proof(induction l arbitrary: k)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then have Ord_tl : "strict_order (map fst l)" using strict_order_tl by auto
  obtain k1 v1 where H1 : "(a = (k1, v1))" by (cases a; auto)
  show ?case
  proof(cases k1)
    case Nil
    then show ?thesis using H1 Cons.IH[OF Ord_tl] by(auto)
  next
    fix h1 t1
    assume Cons' : "k1 = h1 # t1"
    show ?thesis
    proof(cases "h1 = k")
      case False
      then show ?thesis using Cons H1 Cons' Ord_tl by(auto)
    next
      case True
      show ?thesis
      proof(cases "map fst (roalist_gather' l k)")
        case Nil
        then show ?thesis  using H1 Cons' True by(auto simp add:strict_order_def)
      next
        fix t2 l2
        assume Cons'' : "map fst (roalist_gather' l k) = t2 # l2"
        hence Cons''_in : "t2 \<in> set (map fst (roalist_gather' l k))" by auto
        then obtain v2 where H2 : "(t2, v2) \<in> set (roalist_gather' l k)" by(auto)
        have H2_l : "(k#t2, v2) \<in> set l" using roalist_gather'_elem[OF Ord_tl H2] by auto
        then obtain idx where "idx < length l" "l ! idx = (k#t2, v2)" 
          unfolding in_set_conv_nth
          by auto

        then have Lt : "t1 < t2"
          using strict_order_unfold[OF Cons.prems, of "1 + idx" 0] H1 Cons' True
          by(auto simp add: list_lo_lt)

        show ?thesis using
          strict_order_cons[OF Lt]
          Cons.prems Cons.IH[OF Ord_tl, of k] H1 Cons' Cons'' True by(auto)
      qed
    qed
  qed
qed

(*
lift_definition rc_gather :: "('k :: linorder, 'v) recclos \<Rightarrow> 'k \<Rightarrow> ('k, 'v) recclos"
is rc_gather'
(*
  sorry (* can't be bothered to show this now, but it's a rather obvious fact.
           probably need some more generalized induction *)
*)
(* so now (i think) we can just reuse the mergeable instance for oalist *)

(* need a lemma that relates rc_gather to mapping tail over the list of keys *)
proof-
  fix list :: "('k, 'v) recclos'"
  fix k :: "'k"
  assume H : "strict_order (map fst list)"
  show "strict_order (map fst (rc_gather' list k))" using H
  proof(induction list)
    case Nil
    then show ?case by(auto intro: strict_order_nil)
  next
    case (Cons a list)
    obtain kh vh where Hd : "a = (kh, vh)" by(cases a; auto)
    show ?case
    proof(cases kh)
      assume Nil' : "kh = []"
      show ?thesis using Cons Hd Nil' strict_order_tl by auto
    next
      fix khh kht
      assume Cons' : "kh = khh#kht"
      show ?thesis
      proof(cases "k = khh")
        case False
        then show ?thesis using Cons Hd Cons' strict_order_tl by auto
      next
        case True
        then show ?thesis
        proof(cases "map fst (rc_gather' list khh)")
          assume Nil'' : "map fst (rc_gather' list khh) = []"
          then show ?thesis using Cons Hd Cons' True by(auto simp add:strict_order_def)
        next
          fix a2 list2
          assume Cons'' : "map fst (rc_gather' list khh) = (a2#list2)"
          then have A2_in' : "a2 \<in> set (map fst (rc_gather' list khh))" by auto
          then obtain a2v where A2_in : "(a2, a2v) \<in> set (rc_gather' list khh)"
            by(auto)
          have Ord' : "strict_order (map fst list)" using strict_order_tl Cons.prems by auto
          have A2_in_orig : "(khh#a2, a2v) \<in> set list"
            using Cons Hd Cons' True Cons'' rc_gather'_elem[OF Ord' A2_in] by auto
          then obtain a2idx where "a2idx < length list" "list ! a2idx = (khh#a2, a2v)" 
            by (auto simp add: List.in_set_conv_nth)
          hence Conc_hd : "kht < a2" using strict_order_unfold[OF Cons.prems(1), of "1 + a2idx" 0] Cons Hd Cons' True Cons''
            by(auto simp add: list_lo_lt)
          then show ?thesis using Cons Hd Cons' True Cons'' Ord' strict_order_cons 
            by(auto)
        qed
      qed
    qed
  qed
qed
*)
fun roalist_get :: "('k :: linorder, 'v) roalist' \<Rightarrow> 'k \<Rightarrow> ('v + ('k, 'v) roalist') option" where
"roalist_get r k =
  (case map_of r [k] of
    None \<Rightarrow> None
    | Some (Inl v) \<Rightarrow> Some (Inl v)
    | Some (Inr ()) \<Rightarrow> Some (Inr (roalist_gather' r k)))"

(* delete a closure *)
fun roalist_delete_clos' :: "('k :: linorder) \<Rightarrow> ('k :: linorder, 'v) roalist' \<Rightarrow> ('k, 'v) roalist'" where
"roalist_delete_clos' _ [] = []"
| "roalist_delete_clos' k (([], vh)#t) = ([], vh)#roalist_delete_clos' k t"
| "roalist_delete_clos' k (((khh#kht), vh)#t) =
  (if k = khh then roalist_delete_clos' k t
   else ((khh#kht), vh)# roalist_delete_clos' k t)"

lemma strict_order_singleton :
  "strict_order [x]"
  by(auto simp add:strict_order_def)

lemma strict_order_consE :
  assumes H : "strict_order (h1 # h2 # l)"
  shows "h1 < h2"
  using strict_order_unfold[OF H, of 1 0] by auto

lemma roalist_delete_clos'_elem :
  assumes Hord : "strict_order (map fst l)"
  assumes H : "(k', v) \<in> set (roalist_delete_clos' k l)"
  shows "(k', v) \<in> set l" using Hord H
proof(induction l arbitrary: k v)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then have Ord_tl : "strict_order (map fst l)" using strict_order_tl by auto
  obtain k1 v1 where H1 : "(a = (k1, v1))" by (cases a; auto)

  then show ?case
  proof(cases k1)
    assume Nil' : "k1 = []"
    then show ?thesis using Cons H1 Ord_tl by auto
  next
    fix h1 t1
    assume Cons' : "k1 = h1 # t1"
    then show ?thesis
    proof(cases "h1 = k")
      case False
      then show ?thesis using Cons H1 Cons' Ord_tl by(auto)
    next
      case True
      then show ?thesis using Cons.prems Cons.IH[OF Ord_tl] H1 Cons' by(auto)
    qed
  qed
qed

lemma roalist_delete_clos'_elem_contra :
  assumes Hord : "strict_order (map fst l)"
  assumes H : "(kh#kt, v) \<in> set l"
  assumes Hk : "(k \<noteq> kh)"
  shows "(kh#kt, v) \<in> set (roalist_delete_clos' k l)" using Hord H Hk
proof(induction l arbitrary: kh kt k v)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then have Ord_tl : "strict_order (map fst l)" using strict_order_tl by auto
  obtain k1 v1 where H1 : "(a = (k1, v1))" by (cases a; auto)
  then show ?case
  proof(cases k1)
    case Nil
    then show ?thesis using Cons H1 Ord_tl by(auto)
  next
    fix h1 t1
    assume Cons' : "k1 = h1 # t1"
    then show ?thesis
    proof(cases "h1 = k")
      case False
      then show ?thesis using Cons H1 Cons' Ord_tl by(auto)
    next
      case True
      then show ?thesis using Cons.prems Cons.IH[OF Ord_tl] H1 Cons' by(auto)
    qed
  qed  
qed
(*
lemma roalist_delete_clos'_notelem1 :
  assumes Hord : "strict_order (map fst l)"
  assumes H1 : "(kh'#kt) \<notin> set (map fst (roalist_delete_clos' kh l))"
  assumes H2 : "kh \<noteq> kh'"
  shows "(kh'#kt) \<notin> set (map fst (roalist_delete_clos' kh l))" using Hord H1 H2
proof(induction l arbitrary: kh kh' kt)
  case Nil
  then show ?case  by auto
next
  case (Cons a l')
  then obtain ak av where Akv : "a = (ak, av)" by(cases a; auto)
  have Hord' : "strict_order (map fst l')" using Cons.prems strict_order_tl Akv by auto
  show ?case
  proof(cases ak)
    case Nil
    then show ?thesis using Cons Akv by(auto)
  next
    fix akh akt
    assume Cons' : "ak = akh#akt"
    show ?thesis
    proof(cases "akh = kh")
      case True
      then show ?thesis using Cons.prems Cons.IH[OF Hord'] Cons' Akv by(auto)
    next
      case False
      then show ?thesis using Cons.prems Cons.IH[OF Hord'] Cons' Akv by(auto)
    qed
  qed
qed
*)
lemma roalist_delete_clos'_notelem2 :
  assumes Hord : "strict_order (map fst l)"
  shows "(kh#kt) \<notin> set (map fst (roalist_delete_clos' kh l))" using Hord
proof(induction l arbitrary: kh kt)
  case Nil
  then show ?case by auto
next
  case (Cons h t)
  obtain k1 v1 where Hkv1 : "h = (k1, v1)" by(cases h; auto)
  have Hord' : "strict_order (map fst t)" using strict_order_tl Cons.prems Hkv1 by auto
  then show ?case
  proof(cases "k1")
    case Nil
    then show ?thesis using Cons.IH[OF Hord', of kh kt] Hkv1 by(auto)
  next
    fix k1h k1t
    assume Cons' : "k1 = (k1h # k1t)"
    show ?thesis
    proof(cases "k1h = kh")
      case True
      then show ?thesis using Cons.prems Cons.IH[OF Hord'] Cons' Hkv1 by(auto)
    next
      case False
      then show ?thesis using Cons.prems Cons.IH[OF Hord'] Cons' Hkv1 by(auto)
    qed
  qed
qed
(*
fun rc_update_v :: "('key :: linorder) \<Rightarrow> 'value \<Rightarrow> ('key, 'value) recclos \<Rightarrow> ('key, 'value) recclos" where
"rc_update_v k v l =
  update [k] (Inl v) (rc_delete_clos k l)"

(* unsafe because it doesn't check for presence of a value *)
fun rc_update_clos_unsafe' :: "('key :: linorder) \<Rightarrow> ('key, 'value) recclos' \<Rightarrow> ('key, 'value) recclos \<Rightarrow> ('key, 'value) recclos" where
"rc_update_clos_unsafe' k [] l = l"
| "rc_update_clos_unsafe' k ((clkh,clvh)#clt) l =
   update (k#clkh) clvh (rc_update_clos_unsafe' k clt l)"

lift_definition rc_update_clos_unsafe :: "('key :: linorder) \<Rightarrow> ('key, 'value) recclos' \<Rightarrow> ('key, 'value) recclos \<Rightarrow> ('key, 'value) recclos" 
is rc_update_clos_unsafe' .

fun rc_update_clos :: "('key :: linorder) \<Rightarrow> ('key, 'value) recclos' \<Rightarrow> ('key, 'value) recclos \<Rightarrow> ('key, 'value) recclos"
  where
"rc_update_clos k cl l =
  update [k] (Inr ()) (rc_update_clos_unsafe k cl (rc_delete_clos k l))"
*)
(* cannot store a value and a closure at the same key *)
definition roalist_valid :: "('k :: linorder, 'v) roalist' \<Rightarrow> bool" where
"roalist_valid l =
  (map_of l [] = Some (Inr ()) \<and>
   (\<forall> pref v sufh suf . map_of l pref = Some (Inl v) \<longrightarrow>
            map_of l (pref@(sufh#suf)) = None) \<and>
   (\<forall> pref x sufh suf . map_of l (pref@(sufh#suf)) = Some x \<longrightarrow>
            map_of l pref = Some (Inr ())))"

lemma roalist_valid_intro :
  assumes H1 : "map_of l [] = Some (Inr ())"
  assumes H2 : "\<And> pref v sufh suf . map_of l pref = Some (Inl v) \<Longrightarrow> 
                                    map_of l (pref @ (sufh # suf)) = None"
  assumes H3 : "\<And> pref x sufh suf . map_of l (pref @ sufh # suf) = Some x \<Longrightarrow>
                                    map_of l pref = Some (Inr ())"
  shows "roalist_valid l" using H1 H2 H3 unfolding roalist_valid_def
  by(blast)

typedef (overloaded) ('key, 'value) roalist =
  "{xs :: (('key :: linorder), 'value) roalist' .
       strict_order (map fst xs) \<and> roalist_valid xs}"
  morphisms impl_of Oalist
proof
  have C1: "strict_order (map fst ([([], Inr ())] :: ('key, 'value) roalist'))"
    by(auto simp add:strict_order_def)
  have C2 : "roalist_valid  ([([], Inr ())] :: ('key, 'value) roalist')"
  proof(rule roalist_valid_intro)
    show "map_of [([], Inr ())] [] = Some (Inr ())"
      by(auto)
  next
    fix pref suf :: "'key list"
    fix sufh :: "'key"
    fix v :: "'value"
    assume H : "map_of [([], Inr ())] pref = Some (Inl v)"
    show "map_of [([], Inr ())] (pref @ sufh # suf) = None"
      by(auto)
  next  
    fix pref suf :: "'key list"
    fix sufh :: "'key"
    fix x :: "'value + unit"
    assume H: "map_of [([], Inr ())] (pref @ sufh # suf) = Some x"
    then show "map_of [([], Inr ())] pref = Some (Inr ())"
      by(auto)
  qed
  show "[([], Inr ())]  \<in> 
          { rc :: (('key :: linorder), 'value) roalist' . strict_order (map fst rc) \<and> roalist_valid rc }" 
    using C1 C2 by auto
qed


setup_lifting type_definition_roalist

lemma roalist_valid_elim1 :
  assumes Hv : "roalist_valid l"
  shows "map_of l [] = Some (Inr ())"
  using Hv unfolding roalist_valid_def by blast

lemma roalist_valid_elim2 :
  assumes Hv : "roalist_valid l"
  assumes H : "map_of l pref = Some (Inl v)"
  shows "map_of l (pref @ (sufh # suf)) = None"
  using Hv H unfolding roalist_valid_def by blast

lemma roalist_valid_elim3 :
  assumes Hv : "roalist_valid l"
  assumes H : "map_of l (pref @ (sufh#suf)) = Some x"
  shows "map_of l pref = Some (Inr ())"
  using Hv H unfolding roalist_valid_def by blast


(* check if first argument is a prefix of the second *)
fun is_prefix :: "'k list \<Rightarrow> 'k list \<Rightarrow> bool" where
"is_prefix [] _ = True"
| "is_prefix (h#t) [] = False"
| "is_prefix (h1#t1) (h2#t2) =
   (if h1 = h2 then is_prefix t1 t2
    else False)"

(* idea
   given a key, make sure there is no value stored in any prefix *)
(* we also need a function to "fill in" missing prefixes
   that is, if there is nothing at a particular prefix, we must add it (?)
    (or, does validity handle this?)
*)
fun rc_check_prefixes' :: "('key, 'value) roalist' \<Rightarrow> 'key list \<Rightarrow> bool" where
"rc_check_prefixes' [] _ = True"
| "rc_check_prefixes' ((kh, (Inr ()))#t) k = rc_check_prefixes' t k"
| "rc_check_prefixes' ((kh, (Inl v))#t) k =
   (if is_prefix kh k then False
    else rc_check_prefixes' t k)"

lift_definition roalist_leq :: "('key :: linorder, 'value :: Pord) roalist \<Rightarrow> ('key, 'value) roalist \<Rightarrow> bool"
is "list_leq :: ('key :: linorder, 'value :: Pord) roalist' \<Rightarrow> ('key, 'value) roalist' \<Rightarrow> bool" .

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

instantiation roalist :: (linorder, Pord) Pord
begin

definition pleq_roalist :
"pleq l1 l2 = roalist_leq l1 l2"
instance proof
  fix l1 :: "('a :: linorder, 'b :: Pord) roalist"
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
end

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

lift_definition roalist_delete_clos :: "('k :: linorder) \<Rightarrow> ('k :: linorder, 'v) roalist \<Rightarrow> ('k, 'v) roalist"
is roalist_delete_clos'
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


instantiation roalist :: (linorder, Pordc) Pordc
begin

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
          (* need smart delete here - delete won't be guaranteed to be valid.
             (or, maybe just in this case, it will? *)
          have BadSup : "list_leq sup (str_ord_delete pref sup)"
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

lift_definition roa_empty :: "('k :: linorder, 'v) roalist"
is "[([], Inr ())] :: ('k, 'v) roalist'"
  by(auto simp add: strict_order_def roalist_valid_def)

instantiation roalist :: (linorder, Pordc) Pordb
begin
definition bot_roalist :
  "\<bottom> = roa_empty"

instance proof
  fix a :: "('a :: linorder, 'b :: Pordc) roalist"
  show "\<bottom> <[ a"
    unfolding bot_roalist pleq_roalist
  proof(transfer)
    fix x :: "('a, 'b) roalist'"
    assume "strict_order (map fst x) \<and> roalist_valid x"
    hence Hx1 : "strict_order (map fst x)" and Hx2 : "roalist_valid x" by auto
    show "list_leq [([], Inr ())] x"
    proof(rule list_leqI[OF _ Hx1])
      show "strict_order (map fst [([], Inr ())])" by(auto simp add:strict_order_def)
    next
      fix k v
      assume Kv : "(k, v) \<in> set ([([], Inr ())] :: ('a, 'b) roalist')"
      hence Conc' : "(k, v) \<in> set x" using map_of_SomeD[OF roalist_valid_elim1[OF Hx2]]
        by(auto)
      thus "\<exists>v'. (k, v') \<in> set x \<and> v <[ v'"
        by(auto simp add:leq_refl)
    qed
  qed
qed
(*
lift_definition rc_check_prefixes :: "('key :: linorder, 'value) recclos \<Rightarrow> 'key list \<Rightarrow> bool"
is rc_check_prefixes' .
*)
(*
fun recclos_bsup' :: "('key :: linorder, 'value :: Mergeable) recclos \<Rightarrow>
                      ('key, 'value) recclos' \<Rightarrow> ('key, 'value) recclos" where
"recclos_bsup' l [] = l"
| "recclos_bsup' l ((rkh, Inl rv)#rt) =
   (case get l rkh of
      Some (Inl lv) \<Rightarrow> recclos_bsup' (update rkh (Inl [^ lv, rv ^]) l) rt
      | Some (Inr ()) \<Rightarrow> recclos_bsup' l rt
      | None \<Rightarrow>
        (if rc_check_prefixes l rkh
         then recclos_bsup' (update rkh (Inl rv) l) rt
         else recclos_bsup' l rt))"
| "recclos_bsup' l ((rkh, Inr ())#rt) =
    (case get l rkh of
      Some (Inl lv) \<Rightarrow> recclos_bsup' l rt
      | Some (Inr ()) \<Rightarrow> recclos_bsup' l rt
      | None \<Rightarrow> (if rc_check_prefixes l rkh
                 then recclos_bsup' (update rkh (Inr ()) l) rt
                 else recclos_bsup' l rt))"
*)
(*
lift_definition recclos_bsup :: "('key :: linorder, 'value :: Mergeable) recclos \<Rightarrow>
                                 ('key, 'value) recclos \<Rightarrow> ('key, 'value) recclos"
is recclos_bsup' .
*)
(*
definition test_rc1 :: "(String.literal, int md_triv option) recclos'" where
"test_rc1 = 
  to_oalist [([], Inr ())
            ,([STR ''x''], Inr ())
            ,([STR ''x'', STR ''y''], Inl (Some (mdt 0)))
            ,([STR ''y''], Inl (Some (mdt 1)))
            ,([STR ''z''], Inl None)]"

definition test_rc2 :: "(String.literal, int md_triv option) recclos'" where
"test_rc2 = 
  to_oalist [([], Inr ())
            ,([STR ''y''], Inr ())
            ,([STR ''y'', STR ''y''], Inl (Some (mdt 0)))
            ,([STR ''x''], Inl (Some (mdt 1)))
            ,([STR ''z''], Inl (Some (mdt 2)))]"

value "recclos_bsup test_rc1 test_rc2"
value "recclos_bsup test_rc2 test_rc1"

lift_definition cxt_bsup :: "('key :: linorder, 'value :: Mergeable) cxt \<Rightarrow>
                             ('key, 'value) cxt \<Rightarrow> ('key, 'value) cxt"
is "recclos_bsup :: ('key :: linorder, 'value :: Mergeable) recclos \<Rightarrow>
                                 ('key, 'value) recclos \<Rightarrow> ('key, 'value) recclos"
  
  fix l1 l2 :: "('key list, 'value + unit) oalist"
  assume H1 : "rc_valid l1"
  assume H2 : "rc_valid l2"
  show "rc_valid (recclos_bsup l1 l2)" using H1 H2
  proof(induction l2 arbitrary: l1)
    case (Oalist y)
    then show ?case sorry
  qed
  .
*)
            

(* we should make sure this works, then redo it for first arg and
   output type being ctx. *)

(* merging
  - for each LHS variable
    - if it is a value, and RHS is value, merge values
    - if it is a value, and RHS is closure, keep LHS
    - if it is closure, and RHS is closure merge closures (recursively?)
    - if it is a closure and RHS is a value, keep LHS
  - merge closures 
  - 
  -
 *)

(* another idea:
   - take list of keys from LHS
   - 
*)

(*
    mergeAt function for merging at a specific key (?)
    mutual recursion with bsup? seems annoying
    another approach is to "recurse" into gather results
    (but: size issues)

    
*)
(* bsup implementation *)
(*
fun rc_merge :: "('k :: linorder, 'v) recclos \<Rightarrow> ('k, 'v) recclos \<Rightarrow> ('k, 'v) recclos" where
(* remaining to do:
   - show our safe operations preserve recclos
   - implement safe leq (should be same as leq - lift)
   - implement safe merging
   - typeclass instance
*)

(* when we merge rc_valid things, do we still get an rc_valid thing? *)

(*
        proof(cases list)
          assume Nil'' : "list = []"
          then show ?thesis using True Hd Cons' by(auto simp add:strict_order_def)
        next
          fix a' list'
          assume Cons'' : "list = a' # list'"
          obtain kh' vh' where Hd' : "a' = (kh', vh')" by(cases a'; auto)
          show ?thesis
          using Cons Hd Cons' True
          
          
          apply(auto)
        apply(case_tac "list") apply(auto)
           apply(simp add:strict_order_def) 
          apply(case_tac aa; auto)
          defer (* contradictory hyp *)
          defer (* this should be easy - from hyp can prove tails are leq *)
  qed
*)
*)
end

