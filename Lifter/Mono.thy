theory Mono
imports LiftUtils "../Mergeable/Mergeable"

begin

(* Parameterize over a set *)
(* monotonicity for functions over Pord *)
definition monot :: "'a set \<Rightarrow> (('a :: Pord_Weak) \<Rightarrow> 'a) \<Rightarrow> bool" where
"monot S f \<equiv>
  (\<forall> x . x \<in> S \<longrightarrow> x <[ f x)"

lemma monotI :
  assumes H : "\<And> x . x \<in> S \<Longrightarrow> x <[ f x"
  shows "monot S f" using H unfolding monot_def by auto

lemma monotD :
  assumes H : "monot S f"
  assumes Hx : "x \<in> S"
  shows "x <[ f x" using assms unfolding monot_def by auto

(* weak monotonicity - f never makes input less *)
definition monotw ::"'a set \<Rightarrow> (('a :: Pord_Weak) \<Rightarrow> 'a) \<Rightarrow> bool" where
"monotw S f \<equiv>
  (\<forall> x . x \<in> S \<longrightarrow> (\<not> f x <[ x))"

(* antitonicity *)
definition antit :: "'a set \<Rightarrow> (('a :: Pord_Weak) \<Rightarrow> 'a) \<Rightarrow> bool" where
"antit S f \<equiv>
  (\<forall> x . x \<in> S \<longrightarrow> f x <[ x)"

lemma antitI :
  assumes H : "\<And> x . x \<in> S \<Longrightarrow> f x <[ x"
  shows "antit S f" using H unfolding antit_def by auto

lemma antitD :
  assumes H : "antit S f"
  assumes Hx : " x \<in> S "
  shows "f x <[ x" using assms unfolding antit_def by auto

(* weak antitonicity - f never makes input greater *)
definition antitw :: "'a set \<Rightarrow> (('a :: Pord) \<Rightarrow> 'a) \<Rightarrow> bool" where
"antitw S f \<equiv>
  (\<forall> x . x \<in> S \<longrightarrow> (\<not> f x <[ x))"

(* lemma: lifted functions are monotone (if lifted using a valid lifting) *)
lemma lift_monot :
  assumes Hv : "lifting_valid l S"
  shows "monot (S (l' syn)) (lift_map_s l' l f syn)"
proof(rule monotI)
  fix x
  assume Hx : "x \<in> S (l' syn)"

  show "x <[ lift_map_s l' l f syn x"
  unfolding monot_def lift_map_s_def
  using lifting_validDI[OF Hv Hx]
  by auto
qed

(* A more general variant *)
definition gmono :: "'a set \<Rightarrow> (('a :: Pord_Weak) \<Rightarrow> ('b :: Pord_Weak)) \<Rightarrow> bool"
  where
"gmono S f \<equiv>
  (\<forall> x x' . x \<in> S \<longrightarrow> x' \<in> S \<longrightarrow> x <[ x' \<longrightarrow> f x <[ f x')"

abbreviation gmono' :: "(('a :: Pord_Weak) \<Rightarrow> ('b :: Pord_Weak)) \<Rightarrow> bool"
  where
"gmono' f \<equiv> gmono UNIV f"

lemma gmonoI :
  assumes H : "\<And> x x' . x \<in> S \<Longrightarrow> x' \<in> S \<Longrightarrow> x <[ x' \<Longrightarrow> f x <[ f x'"
  shows "gmono S f"
  using H unfolding gmono_def by auto

lemma gmonoD :
  assumes H : "gmono S f"
  assumes Hx : "x \<in> S"
  assumes Hx' : "x' \<in> S"
  assumes Hleq : "x <[ x'"
  shows "f x <[ f x'" using assms unfolding gmono_def
  by auto

lemma gmono'I :
  assumes H : "\<And> x x' . x <[ x' \<Longrightarrow> f x <[ f x'"
  shows "gmono' f" using H unfolding gmono_def by auto

lemma gmono'D :
  assumes H : "gmono' f"
  assumes Hleq : "x <[ x'"
  shows "f x <[ f x'" using assms unfolding gmono_def
  by auto

typedef (overloaded) ('a, 'b) mfun =
  "{(f :: ('a :: Pord_Weak \<Rightarrow> 'b :: Pord_Weak)) . 
    gmono' f}"
proof-
  have "(\<lambda> _ . undefined ) \<in> {f. gmono' f}"
    by(simp add: gmono_def leq_refl)
  thus "\<exists>x. x \<in> {f. gmono' f}"
    by auto
qed

end