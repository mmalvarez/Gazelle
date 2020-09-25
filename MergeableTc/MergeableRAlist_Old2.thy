theory MergeableRAlist_Old
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

(* needed for bnf so we can hopefully get relators *)
lift_definition oamap :: "('v \<Rightarrow> 'v2) \<Rightarrow> ('k ::linorder, 'v) oalist \<Rightarrow>  ('k, 'v2) oalist"
is "\<lambda> f l . map (map_prod id f) l" by auto

lift_definition oaset :: "('k :: linorder, 'v) oalist \<Rightarrow> 'v set"
is "\<lambda> l . set (map snd l)" .

lift_definition oapred :: "('v \<Rightarrow> bool) \<Rightarrow> ('k :: linorder, 'v) oalist \<Rightarrow> bool"
is "\<lambda> P l . list_all P (map snd l)" .

(* generalize for different key spaces?
   i think we actually need key sets to be
   identical here for this to work... *)
(*
lift_definition oarel :: "('v1 \<Rightarrow> 'v2 \<Rightarrow> bool) \<Rightarrow> 
                          ('k :: linorder, 'v1) oalist \<Rightarrow> 
                          ('k :: linorder, 'v2) oalist \<Rightarrow> bool"
is "\<lambda> P l1 l2 . list_all2 P (map snd l1) (map snd l2)" .
*)

lift_definition oarel :: "('v1 \<Rightarrow> 'v2 \<Rightarrow> bool) \<Rightarrow> 
                          ('k :: linorder, 'v1) oalist \<Rightarrow> 
                          ('k :: linorder, 'v2) oalist \<Rightarrow> bool"
is "\<lambda> P l1 l2 . list_all2 
        (\<lambda> kv1 kv2 . 
          (case (kv1, kv2) of
            ((k1, v1), (k2, v2)) \<Rightarrow>
              (k1 = k2) \<and> (P v1 v2))) l1 l2" .

(*
lift_definition
  oalist_map_val ::
  "('v1 \<Rightarrow> 'v2) \<Rightarrow> ('key :: linorder, 'v1) oalist \<Rightarrow> ('key, 'v2) oalist"
 is alist_map_val
  by (auto intro: strict_order_nil)
*)


lift_bnf (dead 'k :: linorder, set : 'v) oalist 
  [wits: "[] :: ('k :: linorder * 'v) list"]
  for map: oamap rel: oarel
  using strict_order_nil
  by(auto)

declare [[show_types]]
(*
bnf "('k :: linorder, 'v) oalist"
  map : oamap
  sets : oaset
  bd : natLeq
  rel : oarel
  pred : oapred
proof
  fix x :: "('k :: linorder, 'v) oalist" 
  show "oamap id x = id x"
  proof(transfer)
    fix x :: "('k * 'v) list"
    show "map (map_prod id id) x = id x"
    proof(induction x)
      case Nil
      then show ?case by  auto
    next
      case (Cons a x)
      then show ?case by(auto)
    qed
  qed
next
  fix f :: "'v1 \<Rightarrow> 'v2"
  fix g :: "'v2 \<Rightarrow> 'v3"
  show "oamap (g \<circ> f) = oamap g \<circ> oamap f"
  proof
    fix x :: "('k :: linorder, 'v1) oalist"
    show "oamap (g \<circ> f) x = (oamap g \<circ> oamap f) x"
      by(transfer; induction x; auto)
  qed
next
  fix x :: "('k :: linorder, 'v1) oalist"
  fix f g :: "'v1 \<Rightarrow> 'v2"
  assume H : "(\<And>z. z \<in> oaset x \<Longrightarrow> f z = g z)"
  thus "oamap f x = oamap g x"
  proof(transfer)
    fix x :: "('k * 'v1) list"
    fix f g :: "'v1 \<Rightarrow> 'v2"
    assume H : "(\<And>z. z \<in> set (map snd x) \<Longrightarrow> f z = g z)"
    show "map (map_prod id f) x = map (map_prod id g) x" using H
      by(induction x; auto)
  qed
next
  fix f :: "'v1 \<Rightarrow> 'v2"
  show "oaset \<circ> oamap f = (`) f \<circ> oaset"
  proof
    fix x :: "('k :: linorder, 'v1) oalist"
    show "(oaset \<circ> oamap f) x = ((`) f \<circ> oaset) x"
    proof(transfer)
      fix f :: "'v1 \<Rightarrow> 'v2"
      fix x :: "('k * 'v1) list"
      show "((\<lambda>l. set (map snd l)) \<circ> map (map_prod id f)) x =
           ((`) f \<circ> (\<lambda>l. set (map snd l))) x"
        by(induction x; auto)
    qed
  qed
next
  show "card_order natLeq" 
    by(rule natLeq_card_order)
next
  show "BNF_Cardinal_Arithmetic.cinfinite natLeq"
    by(rule natLeq_cinfinite)
next
  fix x :: "('k :: linorder, 'v) oalist"
  show "ordLeq3 (card_of (oaset x)) natLeq"
  proof(transfer)
    fix x :: "('k * 'v) list"
    show "ordLeq3 (card_of (set (map snd x))) natLeq"
    proof(rule ordLess_imp_ordLeq)
      show "ordLess2 (card_of (set (map snd x))) natLeq"
        by(simp add: finite_iff_ordLess_natLeq[symmetric])
    qed
  qed
next

  fix R :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  fix S :: "'b \<Rightarrow> 'c \<Rightarrow> bool"
  show "oarel R OO oarel S \<le> oarel (R OO S)"
(*
  proof
    fix x :: "('k :: linorder, 'a) oalist"
    fix y :: "('k :: linorder, 'c) oalist"
    assume H : "(oarel R OO oarel S) x y"
    then show "oarel (R OO S) x y"
    proof(transfer)
      fix R' :: "'a \<Rightarrow> 'b \<Rightarrow> bool" 
      fix S' :: "'b \<Rightarrow> 'c \<Rightarrow> bool"
      fix x' :: "('k * 'a) list"
      fix y' :: "('k * 'c) list"
      assume H0 : "strict_order (map fst x')"
      assume H1 : "strict_order (map fst y')"
      assume H : "\<exists>ya\<in>{xs. strict_order (map fst xs)}.
          list_all2 (\<lambda>kv1 kv2. case (kv1, kv2) of ((k1, v1), k2, v2) \<Rightarrow> k1 = k2 \<and> R' v1 v2) x' ya \<and>
          list_all2 (\<lambda>kv1 kv2. case (kv1, kv2) of ((k1, v1), k2, v2) \<Rightarrow> k1 = k2 \<and> S' v1 v2) ya y'"
      show "list_all2 (\<lambda>kv1 kv2. case (kv1, kv2) of ((k1, v1), k2, v2) \<Rightarrow> k1 = k2 \<and> (R' OO S') v1 v2) x' y'"
      proof(rule list_all2I; rule)
        fix xy
        assume Hx : "xy \<in> set (zip x' y')"
        obtain k1 v1 k2 v2 where Hkv : "xy = ((k1, v1), (k2, v2))"
          by(cases xy; auto)
        then show "case xy of
             (kv1, kv2) \<Rightarrow>
               case (kv1, kv2) of
               ((k1, v1), k2, v2) \<Rightarrow> k1 = k2 \<and> (R' OO S') v1 v2" using H
          apply(auto simp add: list.rel_compp list_all2_iff split:prod.splits)
          apply(
    qed
  qed
*)
  sorry
next
  fix R :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  show "oarel R =
       (\<lambda>(x::('d, 'a) oalist) y::('d, 'b) oalist.
           \<exists>z::('d, 'a \<times> 'b) oalist.
              oaset z \<subseteq> {(x::'a, y::'b). R x y} \<and>
              oamap fst z = x \<and> oamap snd z = y)"
(*
  proof
    fix x :: "('k :: linorder, 'a) oalist"
    show "oarel R x =
       (\<lambda>y::('k, 'b) oalist.
           \<exists>z::('k, 'a \<times> 'b) oalist.
              oaset z \<subseteq> {(x::'a, y::'b). R x y} \<and>
              oamap fst z = x \<and> oamap snd z = y)"
    proof
      fix y :: "('k, 'b) oalist"
      show "oarel R x y =
       (\<exists>z::('k, 'a \<times> 'b) oalist.
           oaset z \<subseteq> {(x::'a, y::'b). R x y} \<and>
           oamap fst z = x \<and> oamap snd z = y)"
      proof
        assume H : "oarel R x y"
        obtain z where
          Z : "z = map2
        show "\<exists>z::('k, 'a \<times> 'b) oalist.
              oaset z \<subseteq> {(x::'a, y::'b). R x y} \<and>
              oamap fst z = x \<and> oamap snd z = y"
          apply(transfer) apply(auto)
      unfolding fun_eq_iff
      apply(transfer)
      apply(auto)
*)
    sorry
next
  fix P :: "'a \<Rightarrow> bool"
  show "oapred P = (\<lambda>x::('d, 'a) oalist. Ball (oaset x) P)"
  proof(rule; transfer)
    fix x :: "('d * 'a) list"
    fix P' :: "'a \<Rightarrow> bool"
    show "list_all P' (map snd x) = Ball (set (map snd x)) P'"
      by(auto simp add: list_all_iff)
  qed
qed
*)
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

(* want 'v option here. problem - is this going to create issues for our data ordering? *)
type_synonym ('k, 'v) recclos' =
  "(('k list) * ('v + unit)) list"

(* separate closid storage? how do we track what our next closid should be? *)
(* also this lacks a canonical representation, I think *)
type_synonym ('k, 'v) recclos =
  "(('k list), ('v + unit)) oalist"

fun rc_gather' :: "('k :: linorder, 'v) recclos' \<Rightarrow> 'k \<Rightarrow> ('k :: linorder, 'v) recclos'" where
"rc_gather' [] _ = []"
| "rc_gather' (([], vh)#l) k = rc_gather' l k"
| "rc_gather' (((khh#kht), vh)#l) k = 
  ( if k = khh then (kht, vh) # rc_gather' l k
    else rc_gather' l k)"

(*
lemma rc_gather'_elem :
  assumes Hord : "strict_order (map fst l)"
  assumes H : "(kt, v) \<in> set (rc_gather' l k)"
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
*)
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
(*
fun rc_get :: "('k :: linorder, 'v) recclos \<Rightarrow> 'k \<Rightarrow> ('v + ('k, 'v) recclos) option" where
"rc_get r k =
  (case get r [k] of
    None \<Rightarrow> None
    | Some (Inl v) \<Rightarrow> Some (Inl v)
    | Some (Inr ()) \<Rightarrow> Some (Inr (rc_gather r k)))"

(* delete a closure *)
fun rc_delete_clos' :: "('k :: linorder) \<Rightarrow> ('k :: linorder, 'v) recclos' \<Rightarrow> ('k, 'v) recclos'" where
"rc_delete_clos' _ [] = []"
| "rc_delete_clos' k (([], vh)#t) = ([], vh)#rc_delete_clos' k t"
| "rc_delete_clos' k (((khh#kht), vh)#t) =
  (if k = khh then rc_delete_clos' k t
   else ((khh#kht), vh)# rc_delete_clos' k t)"

lemma strict_order_singleton :
  "strict_order [x]"
  by(auto simp add:strict_order_def)

lemma strict_order_consE :
  assumes H : "strict_order (h1 # h2 # l)"
  shows "h1 < h2"
  using strict_order_unfold[OF H, of 1 0] by auto

lemma rc_delete_clos'_elem :
  assumes Hord : "strict_order (map fst l)"
  assumes H : "(k', v) \<in> set (rc_delete_clos' k l)"
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


lift_definition rc_delete_clos :: "('k :: linorder) \<Rightarrow> ('k :: linorder, 'v) recclos \<Rightarrow> ('k, 'v) recclos"
is rc_delete_clos'
proof-
  fix k :: "'k"
  fix list :: "('k :: linorder, 'v) recclos'"
  assume H : "strict_order (map fst list)"
  show "strict_order (map fst (rc_delete_clos' k list))" using H
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
      proof(cases "map fst (rc_delete_clos' k list)")
        assume Nil'' : "map fst (rc_delete_clos' k list) = []"
        then show ?thesis
          using Cons Nil' strict_order_tl A strict_order_singleton strict_order_cons 
          by(auto)
      next
        fix h' t'
        assume Cons'' : "map fst (rc_delete_clos' k list) = (h'#t')"
        then have A2_in' : "h' \<in> set (map fst (rc_delete_clos' k list))" by auto
        then obtain v' where V'_in : "(h', v') \<in> set (rc_delete_clos' k list)"
          by(auto)
        have Ord' : "strict_order (map fst list)" using strict_order_tl Cons.prems by auto
        have A2_in_orig : "(h', v') \<in> set list"
          using Cons rc_delete_clos'_elem[OF Ord' V'_in] by auto
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
      proof(cases "map fst (rc_delete_clos' k list)")
        assume Nil'' : "map fst (rc_delete_clos' k list) = []"
        then show ?thesis
          using Cons Cons' strict_order_tl A strict_order_singleton strict_order_cons 
          by(auto)
      next
        fix h' t'
        assume Cons'' : "map fst (rc_delete_clos' k list) = (h'#t')"
        then have A2_in' : "h' \<in> set (map fst (rc_delete_clos' k list))" by auto
        then obtain v' where V'_in : "(h', v') \<in> set (rc_delete_clos' k list)"
          by(auto)
        have Ord' : "strict_order (map fst list)" using strict_order_tl Cons.prems by auto
        have A2_in_orig : "(h', v') \<in> set list"
          using Cons rc_delete_clos'_elem[OF Ord' V'_in] by auto
        then obtain a2idx where "a2idx < length list" "list ! a2idx = (h', v')" 
          by (auto simp add: List.in_set_conv_nth)
        hence Conc_hd : "kh < h'" using strict_order_unfold[OF Cons.prems(1), of "1 + a2idx" 0] Cons A Cons'
          by(auto simp add: list_lo_lt)
        then show ?thesis using Cons Cons' A Cons'' strict_order_cons[of "kh" h'] Ord'
          by(auto)
      qed
    qed
  qed
qed


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
definition rc_valid :: "('k :: linorder, 'v) recclos \<Rightarrow> bool" where
"rc_valid l =
  (get l [] = Some (Inr ()) \<and>
   (\<forall> pref v sufh suf . get l pref = Some (Inl v) \<longrightarrow>
            get l (pref@(sufh#suf)) = None) \<and>
   (\<forall> pref x sufh suf . get l (pref@(sufh#suf)) = Some x \<longrightarrow>
            get l pref = Some (Inr ())))"

lemma rc_valid_intro :
  assumes H1 : "get l [] = Some (Inr ())"
  assumes H2 : "\<And> pref v sufh suf . get l pref = Some (Inl v) \<Longrightarrow> 
                                    get l (pref @ (sufh # suf)) = None"
  assumes H3 : "\<And> pref x sufh suf . get l (pref @ sufh # suf) = Some x \<Longrightarrow>
                                    get l pref = Some (Inr ())"
  shows "rc_valid l" using H1 H2 H3 unfolding rc_valid_def
  by(blast)

lemma rc_valid_elim1 :
  assumes Hv : "rc_valid l"
  shows "get l [] = Some (Inr ())"
  using Hv unfolding rc_valid_def by blast

lemma rc_valid_elim2 :
  assumes Hv : "rc_valid l"
  assumes H : "get l pref = Some (Inl v)"
  shows "get l (pref @ (sufh # suf)) = None"
  using Hv H unfolding rc_valid_def by blast

lemma rc_valid_elim3 :
  assumes Hv : "rc_valid l"
  assumes H : "get l (pref @ (sufh#suf)) = Some x"
  shows "get l pref = Some (Inr ())"
  using Hv H unfolding rc_valid_def by blast

lemma get_empty :
  shows "get (empty :: ('k :: linorder, 'v) oalist) k = (None :: 'v option)"
  by(transfer; auto)


lemma Rel_oalist :
  assumes 0 : "Quotient (=) id id (=)"
  assumes 1: "Quotient R Abs Rep T"
  shows "Quotient (oarel R) (oamap Abs) (oamap Rep) (oarel T)"
  sorry
(*
proof(rule QuotientI)
  fix a :: "('c, 'b) oalist"
  show "oamap Abs (oamap Rep a) = a" using Quotient_abs_rep[OF 1]
  proof(transfer)
    fix Abs :: "'a \<Rightarrow> 'b" fix Rep ::"'b \<Rightarrow> 'a" fix a'::"('c \<times> 'b) list"
    assume H' : "(\<And>a::'b. Abs (Rep a) = a)"
    hence "map (map_prod id Abs \<circ> map_prod id Rep) a' = map id a'"
      unfolding map_eq_conv by(auto)
    thus "map (map_prod id Abs) (map (map_prod id Rep) a') = a'"
      by(auto)
  qed
next
  fix a :: "('c, 'b) oalist"
  show "oarel R (oamap Rep a) (oamap Rep a)" using Quotient_rep_reflp[OF 1]
    sorry
(*
  proof(transfer)
    fix R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    fix Rep:: "'b \<Rightarrow> 'a" 
    fix a:: "('c \<times> 'b) list"
    assume H' : "(\<And>a::'b. R (Rep a) (Rep a))"
    thus "list_all2 (rel_prod (=) R)
        (map (map_prod id Rep) a)
        (map (map_prod id Rep) a)"
      unfolding list_all2_map1 list_all2_map2 list_all2_iff using H'
      sorry
  qed
*)
next
  fix r s :: "('c, 'a) oalist"
  show "oarel R r s = (oarel R r r \<and> oarel R s s \<and> oamap Abs r = oamap Abs s)"
    using Quotient_rel[OF 1]
    sorry
(*
  proof(transfer)
    fix R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    fix r:: "('c \<times> 'a) list"
    fix s:: "('c \<times> 'a) list"
    fix Abs :: "'a \<Rightarrow> 'b"
    assume H' : "(\<And>(r::'a) s::'a.
           (R r r \<and> R s s \<and> Abs r = Abs s) = R r s)"
    thus "list_all2 (rel_prod (=) R) r s =
       (list_all2 (rel_prod (=) R) r r \<and>
        list_all2 (rel_prod (=) R) s s \<and>
        map (map_prod id Abs) r =
        map (map_prod id Abs) s)"
      apply(auto simp add:list_all2_iff zip_same)
      sorry
  qed
*)
next
  (* Quotient_rel_rep? *)
  show "oarel T = (\<lambda>(x::('c, 'a) oalist) y::('c, 'b) oalist. oarel R x x \<and> oamap Abs x = y)"
    using Quotient_cr_rel[OF 1]
    sorry
qed
*)

declare [[show_types]]
typedef (overloaded) ('key, 'value) cxt =
  "{ rc :: (('key :: linorder), 'value) recclos .
     rc_valid rc }"
  morphisms cx_impl_of Cxt
proof
  have "rc_valid ((update [] (Inr ())) empty :: ('key list, ('value + unit)) oalist)"
  proof(rule rc_valid_intro)
    show "get (update [] (Inr ()) MergeableAList.empty) [] = Some (Inr ())"
      by(rule MergeableAList.get_update)
  next
    fix pref suf :: "'key list"
    fix sufh :: "'key"
    fix v :: "'value"
    assume H : "get (update [] (Inr ()) MergeableAList.empty) pref = Some (Inl v)"
    show "get (update [] (Inr ()) MergeableAList.empty) (pref @ sufh # suf) = None"
      by(transfer; auto)
  next  
    fix pref suf :: "'key list"
    fix sufh :: "'key"
    fix x :: "'value + unit"
    assume H: "get (update [] (Inr ()) empty) (pref @ sufh # suf) = Some x"
    then show "get (update [] (Inr ()) empty) pref = Some (Inr () :: ('value + unit))"
      by(transfer; auto)
  qed
  thus "(update [] (Inr ())) empty  \<in> 
          { rc :: (('key :: linorder), 'value) recclos . rc_valid rc }" by auto
qed

declare Rel_oalist[quot_map]
print_quot_maps
(* ok, i think the issue here is about the dead variable *)
setup_lifting type_definition_cxt

lift_bnf (dead 'key :: linorder, 'value) cxt [wits: "(update [] (Inr ())) (empty :: ('key :: linorder, 'value) recclos)"]
  apply(auto)

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
fun rc_check_prefixes' :: "('key, 'value) recclos' \<Rightarrow> 'key list \<Rightarrow> bool" where
"rc_check_prefixes' [] _ = True"
| "rc_check_prefixes' ((kh, (Inr ()))#t) k = rc_check_prefixes' t k"
| "rc_check_prefixes' ((kh, (Inl v))#t) k =
   (if is_prefix kh k then False
    else rc_check_prefixes' t k)"

lift_definition rc_check_prefixes :: "('key :: linorder, 'value) recclos \<Rightarrow> 'key list \<Rightarrow> bool"
is rc_check_prefixes' .

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

lift_definition recclos_bsup :: "('key :: linorder, 'value :: Mergeable) recclos \<Rightarrow>
                                 ('key, 'value) recclos \<Rightarrow> ('key, 'value) recclos"
is recclos_bsup' .

definition test_rc1 :: "(String.literal, int md_triv option) recclos" where
"test_rc1 = 
  to_oalist [([], Inr ())
            ,([STR ''x''], Inr ())
            ,([STR ''x'', STR ''y''], Inl (Some (mdt 0)))
            ,([STR ''y''], Inl (Some (mdt 1)))
            ,([STR ''z''], Inl None)]"

definition test_rc2 :: "(String.literal, int md_triv option) recclos" where
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

fun rc_merge :: "('k :: linorder, 'v) recclos \<Rightarrow> ('k, 'v) recclos \<Rightarrow> ('k, 'v) recclos" where
"rc_merge

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
end

