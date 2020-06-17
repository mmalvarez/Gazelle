theory Splittable
  imports "Pord" "HOL.String"
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

type_synonym 'a projs_t = "(char list * ('a) set * ('a \<Rightarrow> 'a)) list"

class Splittable = Pordc +
  fixes projs :: "('a :: Pordc) projs_t"
  assumes projs_spec :
    "\<And> s d f x . (s, d, f) \<in> set projs \<Longrightarrow>
               is_project x d (f x)"
  assumes projs_distinct :
     "distinct (map fst projs)"

lemma projs_distinct' :
  fixes projs' :: "('a :: Splittable) projs_t"
  assumes H : "projs' = projs"
  shows "distinct (map fst projs')" using H
  apply(simp)
  apply(rule projs_distinct)
  done


class Splittableb =
  Splittable +
  Pordb

definition projs_names :: "('a :: Splittable) itself \<Rightarrow> char list set" where
"projs_names a = set (map fst (projs :: 'a projs_t))"

definition sdomi :: "nat \<Rightarrow> ('a :: Splittable) set" where
"sdomi n = fst (snd (projs ! n))"

definition sdom' :: "char list \<Rightarrow> ('a :: Splittable) set option" where
"sdom' = map_option fst o Map.map_of (projs :: 'a projs_t)"

definition sdom :: "char list \<Rightarrow> ('a :: Splittable) set" where
"sdom x = (case sdom' x of Some x' \<Rightarrow> x')"

definition sprji :: "nat \<Rightarrow> (('a :: Splittable) \<Rightarrow> 'a)" where
"sprji n = snd (snd (projs ! n))"

definition sprj' :: "char list \<Rightarrow> ('a :: Splittable \<Rightarrow> 'a) option" where
"sprj' = map_option snd o Map.map_of (projs :: 'a projs_t)"

definition sprj :: "char list \<Rightarrow> ('a :: Splittable \<Rightarrow> 'a)" where
"sprj x = (case sprj' x of Some x' \<Rightarrow> x')"

lemma projs_bot :
  fixes d :: "('a :: Splittableb) set"
  fixes f :: "'a \<Rightarrow> 'a"
  fixes s :: "char list"
  assumes H : "(s, d, f) \<in> set projs"
  shows "\<bottom> \<in> d"
proof(-)
  have Hproj : "is_project \<bottom> d (f \<bottom>)" using H projs_spec by auto
  have 0 : "(f \<bottom>) \<in> d" using is_project_unfold1[OF Hproj] by auto
  have "f \<bottom> <[ \<bottom>" using is_project_unfold2[OF Hproj] by auto
  hence "f \<bottom> = \<bottom>" using leq_antisym[OF bot_spec[of "f \<bottom>"]]  by (auto)

  thus "\<bottom> \<in> d" using 0 by auto
(* we should add some utilities for lifting. *)
qed

lemma sdom_defined :
  fixes d :: "('a :: Splittableb) set"
  fixes f :: "'a \<Rightarrow> 'a"
  fixes s :: "char list"
  assumes H : "(s, d, f) \<in> set projs"

  shows "sdom s = d" using map_of_is_SomeI[OF projs_distinct H]
    by(auto simp add:sdom_def sdom'_def)

lemma sprj_defined :
  fixes d :: "('a :: Splittableb) set"
  fixes f :: "'a \<Rightarrow> 'a"
  fixes s :: "char list"
  assumes H : "(s, d, f) \<in> set projs"

  shows "sprj s = f" using map_of_is_SomeI[OF projs_distinct H]
    by(auto simp add:sprj_def sprj'_def)

end