theory Auto_Lift_Snippets
    imports Main "../Lifter/Auto_Lifter_Datatypes" "../Mergeable/Mergeable" "../Lifter/Lifter_Instances" 
      "HOL-Library.Adhoc_Overloading"
begin

text_raw \<open>%Snippet paper_examples__auto_lift_snippets__classes\<close>
class schem
class basename
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__auto_lift_snippets__names_classes\<close>
datatype nA =
  NA
datatype nB =
  NB

class n_A
class hasntA

class n_B
class hasntB
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__auto_lift_snippets__names_schem\<close>
instantiation nA :: schem begin
instance proof qed
end

instantiation nB :: schem begin
instance proof qed
end
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__auto_lift_snippets__names_basename\<close>
instantiation nA :: basename begin
instance proof qed
end

instantiation nB :: basename begin
instance proof qed
end
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__auto_lift_snippets__names_hasnt\<close>
instantiation nA :: hasntB begin
instance proof qed
end
instantiation nB :: hasntA begin
instance proof qed
end
text_raw \<open>%EndSnippet\<close>


text_raw \<open>%Snippet paper_examples__auto_lift_snippets__types\<close>
datatype ('a, 'b) sprod = 
  SP "'a" "'b"

(* x is syntax (needed for priority functions) *)
datatype ('x, 'a) sprio =
  SPR "('x => nat)" "('x => nat => nat)" "'a"

datatype 'a soption =
  SO "'a"

datatype 'a sid =
  SID "'a"

datatype ('x, 'da, 'db, 'a) sinject =
  SINJ "('x, 'da, 'db) lifting" "'a"

datatype ('a, 'b) smerge =
  SM "'a" "'b"
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__auto_lift_snippets__option_prod_instances\<close>
instantiation soption :: (schem) schem begin
instance proof qed
end

instantiation soption :: (hasntA) hasntA begin
instance proof qed
end

instantiation sprod :: (schem, schem) schem begin
instance proof qed
end

instantiation sprod :: (hasntA, hasntA) hasntA begin
instance proof qed
end
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__auto_lift_snippets__schem_lift\<close>
type_synonym ('s1, 's2, 'x, 'a, 'b) schem_lift =
"('s1 \<Rightarrow> 's2 \<Rightarrow> ('x, 'a, 'b) lifting)"

consts schem_lift ::
  "('s1 :: schem, 's2 :: schem, 'x, 'a, 'b) schem_lift"
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__auto_lift_snippets__schem_lift_base_trivA\<close>
definition schem_lift_base_trivA ::  "('n :: n_A, 'n, 'x, 'a :: Bogus, 'a md_triv) schem_lift" where
"schem_lift_base_trivA _ _ =
  triv_l"
text_raw \<open>%EndSnippet\<close>

definition schem_lift_base_trivB ::  "('n :: n_B, 'n, 'x, 'a :: Bogus, 'a md_triv) schem_lift" where
"schem_lift_base_trivB _ _ =
  triv_l"


text_raw \<open>%Snippet paper_examples__auto_lift_snippets__schem_lift_option_recR\<close>
definition schem_lift_option_recR ::
  "('n, 'ls, 'x, 'a, 'b2 :: Pord) schem_lift \<Rightarrow>
   ('n, 'ls soption, 'x, 'a, 'b2 option) schem_lift" where
"schem_lift_option_recR rec n s =
  (case s of
    SO s' \<Rightarrow>
      option_l (rec n s'))"
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__auto_lift_snippets__schem_lift_prod_recR_A\<close>
definition schem_lift_prod_recR_A_left ::
  "('n, 'ls, 'x, 'a, 'b2 :: Pord) schem_lift \<Rightarrow>
   ('n :: n_A, ('ls, 'rs :: hasntA) sprod, 'x, 'a, 'b2 * ('rest :: Pordb)) schem_lift" where
"schem_lift_prod_recR_A_left rec n s =
  (case s of
    SP ls rs \<Rightarrow>
      fst_l (rec n ls))"

definition schem_lift_prod_recR_A_right ::
  "('n, 'rs, 'x, 'a, 'b2 :: Pord) schem_lift \<Rightarrow>
   ('n :: n_A, ('ls :: hasntA, 'rs ) sprod, 'x, 'a, ('rest :: Pordb) * ('b2)) schem_lift" where
"schem_lift_prod_recR_A_right rec n s =
  (case s of
    SP ls rs \<Rightarrow>
      snd_l (rec n rs))"
text_raw \<open>%EndSnippet\<close>

definition schem_lift_prod_recR_B_left ::
  "('n, 'ls, 'x, 'a, 'b2 :: Pord) schem_lift \<Rightarrow>
   ('n :: n_B, ('ls, 'rs :: hasntB) sprod, 'x, 'a, 'b2 * ('rest :: Pordb)) schem_lift" where
"schem_lift_prod_recR_B_left rec n s =
  (case s of
    SP ls rs \<Rightarrow>
      fst_l (rec n ls))"

definition schem_lift_prod_recR_B_right ::
  "('n, 'rs, 'x, 'a, 'b2 :: Pord) schem_lift \<Rightarrow>
   ('n :: n_B, ('ls :: hasntB, 'rs ) sprod, 'x, 'a, ('rest :: Pordb) * ('b2)) schem_lift" where
"schem_lift_prod_recR_B_right rec n s =
  (case s of
    SP ls rs \<Rightarrow>
      snd_l (rec n rs))"


text_raw \<open>%Snippet paper_examples__auto_lift_snippets__schem_lift_recL\<close>
definition schem_lift_recL ::
  "('s1l, 's2, 'x, 'a1l, 'b2) schem_lift \<Rightarrow>
   ('s1r, 's2, 'x, 'a1r, 'b2) schem_lift \<Rightarrow>
   (('s1l :: schem, 's1r :: schem) sprod, 's2 :: schem, 'x, 
   (('a1l :: Bogus) * ('a1r :: Bogus)), 'b2 :: Mergeable) schem_lift" where
"schem_lift_recL recl recr s1 s2 =
  (case s1 of
    SP s1l s1r \<Rightarrow>
      merge_l (recl s1l s2) (recr s1r s2))"
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__auto_lift_snippets__schem_lift_merge_recR\<close>
definition schem_lift_merge_recR_A_left ::
  "('n, 'ls, 'x, 'a, 'b2) schem_lift \<Rightarrow>
   ('n :: n_A, ('ls, 'rs :: hasntA) smerge, 'x, 'a, 'b2) schem_lift" where
"schem_lift_merge_recR_A_left rec n s =
  (case s of
    SM ls rs \<Rightarrow>
      (rec n ls))"

definition schem_lift_merge_recR_A_right ::
  "('n, 'rs, 'x, 'a, 'b2) schem_lift \<Rightarrow>
   ('n :: n_A, ('ls :: hasntA, 'rs) smerge, 'x, 'a, 'b2) schem_lift" where
"schem_lift_merge_recR_A_right rec n s =
  (case s of
    SM ls rs \<Rightarrow>
      (rec n rs))"
text_raw \<open>%EndSnippet\<close>

definition schem_lift_merge_recR_B_left ::
  "('n, 'ls, 'x, 'a, 'b2) schem_lift \<Rightarrow>
   ('n :: n_B, ('ls, 'rs :: hasntB) smerge, 'x, 'a, 'b2) schem_lift" where
"schem_lift_merge_recR_B_left rec n s =
  (case s of
    SM ls rs \<Rightarrow>
      (rec n ls))"

definition schem_lift_merge_recR_B_right ::
  "('n, 'rs, 'x, 'a, 'b2) schem_lift \<Rightarrow>
   ('n :: n_B, ('ls :: hasntB, 'rs) smerge, 'x, 'a, 'b2) schem_lift" where
"schem_lift_merge_recR_B_right rec n s =
  (case s of
    SM ls rs \<Rightarrow>
      (rec n rs))"

text_raw \<open>%Snippet paper_examples__auto_lift_snippets__schem_lift_overloading\<close>
adhoc_overloading schem_lift

"schem_lift_base_trivA"
"schem_lift_base_trivB"
(*...*)
"schem_lift_prod_recR_A_left schem_lift"
"schem_lift_prod_recR_A_right schem_lift"
"schem_lift_prod_recR_B_left schem_lift"
"schem_lift_prod_recR_B_right schem_lift"

"schem_lift_option_recR schem_lift"
"schem_lift_merge_recR_A_left schem_lift"
"schem_lift_merge_recR_A_right schem_lift"
"schem_lift_merge_recR_B_left schem_lift"
"schem_lift_merge_recR_B_right schem_lift"
(*...*)

"schem_lift_recL schem_lift schem_lift"
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__auto_lift_snippets__option_l_valid_weak_intro\<close>
\<comment> \<open>option\_l\_valid\_weak.intro:\<close>
text \<open>@{thm [display] option_l_valid_weak.intro}\<close>
text_raw \<open>%EndSnippet\<close>

(*
text_raw \<open>%Snippet paper_examples__auto_lift_snippets__option_l_valid_weak_intro_nope\<close>
lemma option_l_valid_weak.intro: "\<And> l S . lifting_valid_weak l S \<Longrightarrow> option_l_valid_weak l S"
  text_raw \<open>%EndSnippet\<close>
  oops
*)

text_raw \<open>%Snippet paper_examples__auto_lift_snippets__option_l_valid_weak_ax\<close>
lemma (in option_l_valid_weak) ax :
  shows "lifting_valid_weak (option_l l) (option_l_S S)"
text_raw \<open>%EndSnippet\<close>
  using out.lifting_valid_weak_axioms
    by auto
(*
text_raw \<open>%Snippet paper_examples__auto_lift_snippets__option_l_valid_weak_ax_nope\<close>
lemma option_l_valid_weak.ax: "\<And> l S . 
	option_l_valid_weak l S \<Longrightarrow> lifting_valid_weak (option_l l) (option_l_S S)"
  text_raw \<open>%EndSnippet\<close>
  oops
*)

text_raw \<open>%Snippet paper_examples__auto_lift_snippets__option_l_valid_weak_ax_g\<close>
lemma (in option_l_valid_weak) ax_g :
  assumes "S' = option_l_S S"
  shows "lifting_valid_weak (option_l l) S'"
text_raw \<open>%EndSnippet\<close>
  using out.lifting_valid_weak_axioms assms
  by auto



(*
text_raw \<open>%Snippet paper_examples__auto_lift_snippets__option_l_valid_weak_ax_g_nope\<close>
lemma option_l_valid_weak.ax_g: "\<And> l s .
	option_l_valid_weak l S \<Longrightarrow> S' = option_l_S S \<Longrightarrow> lifting_valid_weak (option_l l) S'"
text_raw \<open>%EndSnippet\<close>
  oops
*)

end