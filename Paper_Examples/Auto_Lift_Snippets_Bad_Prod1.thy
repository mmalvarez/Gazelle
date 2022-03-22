theory Auto_Lift_Snippets_Bad_Prod1
  imports Main "../Lifter/Auto_Lifter_Datatypes" "../Mergeable/Mergeable" "../Lifter/Lifter_Instances" 
    "HOL-Library.Adhoc_Overloading"
  
begin
class schem
class basename

datatype nA =
  NA
datatype nZ =
  NB
(* ... *)
class n_A
class hasntA

class n_Z
class hasZ
(* ... *)

datatype ('a, 'b) sprod = 
  SP "'a" "'b"

text_raw \<open>%Snippet paper_examples__auto_lift_snippets_bad_prod1__bad_prod1\<close>
instantiation sprod :: (hasZ, _) hasZ begin
instance proof qed end
text_raw \<open>%EndSnippet\<close>
(* only one of these two definitions is allowed *)
(*
instantiation sprod :: (_, hasZ) hasZ begin
instance proof qed end
*)

end