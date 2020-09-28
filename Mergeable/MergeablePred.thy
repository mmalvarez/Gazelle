theory MergeablePred imports MergeableInstances

begin

class Booly =
  fixes bD :: "'a \<Rightarrow> bool"
  fixes bR :: "bool \<Rightarrow> 'a"
  assumes bDR1 : "\<And> b . bD (bR b) = b"
  assumes bDR2 : "\<And> x . bR (bD x) = x"

declare [[show_types]]

instantiation bool :: Booly begin
definition bool_bD : "bD b = (b :: bool)"
definition bool_bR : "bR b = (b :: bool)"
instance proof
  fix b :: bool
  show "bD (bR b :: bool)= b" unfolding bool_bD bool_bR by auto
next
  fix x :: bool
  show "bR (bD x) = x" unfolding bool_bD bool_bR by auto
qed
end

declare bool_bD bool_bR [simp]

instantiation "fun"  :: (_, Booly) Pord_Weak
begin
definition pred_pleq :
  "((f1 :: 'a \<Rightarrow> 'b) <[ (f2 :: 'a \<Rightarrow> 'b)) =
   (\<forall> x . bD (f2 x) \<longrightarrow> bD (f1 x))"
instance proof
  fix P :: "'a \<Rightarrow> 'b"
  show "P <[ P" unfolding pred_pleq by auto
next
  fix P1 P2 P3 :: "'a \<Rightarrow> 'b"
  show "P1 <[ P2 \<Longrightarrow> P2 <[ P3 \<Longrightarrow> P1 <[ P3" unfolding pred_pleq by auto
qed
end

instantiation "fun" :: (_, Booly) Pord
begin
instance proof
  fix a b :: "'a \<Rightarrow> 'b"
  assume H1 : "a <[ b"
  assume H2 : "b <[ a"
  have H1' : "\<And> x . bD (b x) \<Longrightarrow> bD (a x)" using H1 unfolding pred_pleq by auto
  have H2' : "\<And> x . bD (a x) \<Longrightarrow> bD (b x)" using H2 unfolding pred_pleq by auto
  show "a = b"
  proof(rule ext)
    fix x :: 'a
    show "a x = b x"
    proof(cases "bD (a x)")
      case True
      then show ?thesis using H2'[OF True]
    next
      case False
      then show ?thesis sorry
qed
qed
end
end