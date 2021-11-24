theory Linorder_Insts imports Main
begin

(* Instances of Linorder (built-in typeclass for linear orderings with a trichotomy law)
 * for several types, intended for use with Oalist *)

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

end