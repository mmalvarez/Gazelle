theory Splittable
  imports "Pord"
begin

(* idea: "project a into set yielding a'" *)
definition is_project :: "('a :: Pord_Weak) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
"is_project a A a' =
  (is_greatest (\<lambda> x . x \<in> A \<and> x <[ a) a')"

lemma is_project_unfold1 :
  assumes H : "is_project a A a'"
  shows "a' \<in> A" using H
  by(auto simp add:is_greatest_def is_project_def)

lemma is_project_unfold2 :
  assumes H : "is_project a A a'"
  shows "a' <[ a" using H
  by(auto simp add:is_greatest_def is_project_def)

lemma is_project_unfold3 :
  assumes H : "is_project a A a'"
  assumes H1a' : "a'' \<in> A"
  assumes H2a' : "a'' <[ a"
  shows "a'' <[ a'" using H H1a' H2a'
  by(auto simp add:is_greatest_def is_project_def)

lemma is_project_intro :
  fixes a a' :: "'a :: Pord_Weak"
  assumes Hin : "a' \<in> A"
  assumes Hless : "a' <[ a"
  assumes Hgreatest : "\<And> x . x \<in> A \<Longrightarrow> x <[ a \<Longrightarrow> x <[ a'"
  shows "is_project a A a'" using Hin Hless Hgreatest
  by(auto simp add:is_greatest_def is_project_def)


class Splittable = Pordc +
  fixes projs :: "(('a :: Pordc) set * ('a \<Rightarrow> 'a)) list"
  assumes projs_spec :
    "\<And> d f x . (d, f) \<in> set projs \<Longrightarrow>
               is_project x d (f x)"

class Splittableb =
  Splittable +
  Pordb

end