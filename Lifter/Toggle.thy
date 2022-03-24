theory Toggle
  imports Lifter
begin
(*
idea: based on the syntax, we can decide to do a no-op
otherwise we have to obey normal lifting rules.
*)

definition LtUpd ::
  "('syn, 'a, 'b) lifting \<Rightarrow>
   ('syn \<Rightarrow> bool) \<Rightarrow>
   'syn \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" where
"LtUpd l tg syn a b =
  (if tg syn then LUpd l syn a b
   else b)"

definition LtMap ::
  "('syn, 'a, 'b) lifting \<Rightarrow>
   ('syn \<Rightarrow> bool) \<Rightarrow>
   ('syn \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>
   'syn \<Rightarrow> 'b \<Rightarrow> 'b"
  where
"LtMap l tg f syn x =
  (if tg syn then LMap l f syn x
   else x)"

(* a variant of lift_map_s that syntax-translates the semantics but not the toggle
 *)

(* a variant that translates both the semantics and the toggle
 * (possibly more useful for multiple stages of language composition)
 *)
text_raw \<open>%Snippet gazelle__lifter__toggle__lift_map_t_s\<close>
definition
  lift_map_t_s ::
  "('b1 \<Rightarrow> 'a1) \<Rightarrow>
   ('a1, 'a2, 'b2::Pord) lifting \<Rightarrow>
   ('b1 \<Rightarrow> bool) \<Rightarrow>
   ('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a2) \<Rightarrow>
   'b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2" where
"lift_map_t_s l' l tg f syn st =
  (if tg syn then lift_map_s l' l f syn st
   else st)"
text_raw \<open>%EndSnippet\<close>

definition
  lift_map_st_s ::
  "('b1 \<Rightarrow> 'a1) \<Rightarrow>
   ('a1, 'a2, 'b2::Pord) lifting \<Rightarrow>
   ('a1 \<Rightarrow> bool) \<Rightarrow>
   ('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a2) \<Rightarrow>
   'b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2" where
"lift_map_st_s l' l tg f syn st =
  (if tg (l' syn) then lift_map_s l' l f syn st
   else st)"

(* old definition, harder to use in theorems because of the need to 
 * reuse syntax parameter in toggle-predicate and then again in function*)
text_raw \<open>%Snippet gazelle__lifter__toggle__toggle\<close>
definition toggle ::
  "('syn \<Rightarrow> bool) \<Rightarrow>
   ('syn \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow>
   ('syn \<Rightarrow> 'b \<Rightarrow> 'b)" where
"toggle tg f syn st =
  (if (tg syn) then f syn st else st)"
text_raw \<open>%EndSnippet\<close>

(*
definition toggle ::
  "'syn \<Rightarrow>
   ('syn \<Rightarrow> bool) \<Rightarrow>
   ('syn \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow>
   ('b \<Rightarrow> 'b)" where
"toggle syn tg f st =
  (if (tg syn) then f syn st else st)"
*)

lemma lift_map_t_s_toggle :
  "lift_map_t_s l' l tg f =
   toggle tg (lift_map_s l' l f)"
  unfolding lift_map_t_s_def toggle_def
  by(auto)


end