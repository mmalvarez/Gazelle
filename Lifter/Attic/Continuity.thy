theory Continuity imports LangCompSimple
begin

(* Scott continuity-like definitions *)

(* directed set. pairs or arbitrary sets? *)

definition dirset :: "('a :: Pord) set \<Rightarrow> bool" where
"dirset S \<equiv>
  (\<forall> x y . x \<in> S \<longrightarrow> 
           y \<in> S \<longrightarrow> 
           (\<exists> z . is_ub {x, y} z \<and> z \<in> S))"

(* literal translation of wikipedia *)

definition scont :: "('a :: Pord \<Rightarrow> 'b :: Pord) \<Rightarrow> bool" where
"scont f =
  (\<forall> D supr . dirset D \<longrightarrow>
   is_sup D supr \<longrightarrow> 
   is_sup (f ` D) (f supr))"

definition scross :: "('a \<Rightarrow> 'b) set \<Rightarrow> 'a set \<Rightarrow> 'b set" where
"scross Fs Xs =
  { x . \<exists> f y . f \<in> Fs \<and> y \<in> Xs \<and> x = f y }"

lemma scross_inI :
  assumes Hf : "f \<in> Fs"
  assumes Hx : "x \<in> Xs"
  assumes Heq : "res = f x"
  shows "res \<in> scross Fs Xs" using assms
  unfolding scross_def
  by blast

lemma scross_inD  :
  assumes "res \<in> scross Fs Xs"
  shows "\<exists> f y . f \<in> Fs \<and> y \<in> Xs \<and> res = f y" using assms
  unfolding scross_def
  by blast

(* TODO: do we really need the nonemptiness requirement for Fs'? *)
(* TODO: unlike scott continuity, we don't have the "closure" property
   here (that the set is closed under LUBs 
*)
(* binary sups_pres 
   (f1, x1) (f2, x2)
*)
definition sups_pres_new :: 
  "('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> bool" where
"sups_pres_new f1 f2 =
  (\<forall> x y syn supr .
     is_sup {x, y} supr \<longrightarrow>
     (\<exists> supr' . is_sup {f1 syn x, f2 syn y} supr' \<and>
        is_sup {f1 syn supr, f2 syn supr} supr'))"

end