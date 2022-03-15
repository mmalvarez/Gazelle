theory Wrappers imports Main
begin

(* Here we define a few datatypes that are going to be tied to specific orderings,
 * for use with the Mergeable typeclass. Generally, when working with arbitrary data in
 * Gazelle (i.e., state types for language components), this data will not come equipped
 * with a natural ordering. These types help us impose such an ordering.
 *)

(* md_triv = "Mergeable Data: Trivial"
 * this imposes a trivial ordering (x <[ x \<leftrightarrow> x = x)
 *)
text_raw \<open>%Snippet gazelle__mergeable__wrappers__md_triv\<close>
datatype 'a md_triv =
  mdt 'a
text_raw \<open>%EndSnippet\<close>

definition mdt_get :: "'a md_triv \<Rightarrow> 'a" where
"mdt_get x = (case x of (mdt x') \<Rightarrow> x')"

definition mdt_put :: "'a \<Rightarrow> 'a md_triv" where
"mdt_put x = mdt x"

declare mdt_get_def mdt_put_def [simp]

(* md_prio = "Mergeable Data: Priority
 * We pair a datum with a natural number representing "priority".
 * When comparing elements we will first compare priorities, then enclosed data.
 *)
text_raw \<open>%Snippet gazelle__mergeable__wrappers__md_prio\<close>
datatype 'a md_prio =
  mdp nat 'a
text_raw \<open>%EndSnippet\<close>
definition mdp_get :: "'a md_prio \<Rightarrow> (nat * 'a)" where
"mdp_get x = (case x of (mdp n y) \<Rightarrow> (n, y))"

definition mdp_get_pri :: "'a md_prio \<Rightarrow> nat" where
"mdp_get_pri x = (case x of (mdp n _) \<Rightarrow> n)"

definition mdp_get_data :: "'a md_prio \<Rightarrow> 'a" where
"mdp_get_data x = (case x of (mdp _ y) \<Rightarrow> y)"

definition mdp_put :: "nat \<Rightarrow> 'a \<Rightarrow> 'a md_prio" where
"mdp_put = mdp"

declare mdp_get_def mdp_get_pri_def mdp_get_data_def mdp_put_def [simp]

end