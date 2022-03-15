theory Composition1 imports Main
begin

datatype syn =
  Inst1
  | Inst2

datatype state = int

definition compose_states :: "state \<Rightarrow> state \<Rightarrow> state" where
  "compose_states _ _ = undefined"

text_raw \<open>%Snippet paper_examples__composition1__composition_sketch\<close>

(*
datatype syn = (* ... *)

datatype state = (* ... *)
*)

definition f1 :: "syn \<Rightarrow> state \<Rightarrow> state"
  where
"f1 x st = undefined" (* ... f1 definition *)

definition f2 :: "syn \<Rightarrow> state \<Rightarrow> state"
  where
"f2 x st = undefined" (* ... f2 definition *)

definition composed :: "syn \<Rightarrow> state \<Rightarrow> state" where
"composed x st = (compose_states (f1 x st) (f2 x st))"(* composition of f1 and f2, described next *)

text_raw \<open>%EndSnippet\<close>

end