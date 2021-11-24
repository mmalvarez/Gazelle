theory Cond imports Main
begin

(* conditional/boolean expressions *)
datatype cond =
  Seqz
  | Sltz
  | Sgtz
  | Sskip_cond

(* first int is a boolean flag. *)
type_synonym cond_state = "int * int"

abbreviation encode_bool :: "bool \<Rightarrow> int" where
"encode_bool b \<equiv>
  (if b then 1 else 0)"

definition cond_sem :: "cond \<Rightarrow> cond_state \<Rightarrow> cond_state" where
"cond_sem x s =
  (case s of (b, i) \<Rightarrow>
    (case x of
      Seqz \<Rightarrow> (encode_bool (i = 0), i)
      | Sltz \<Rightarrow> (encode_bool (i < 0), i)
      | Sgtz \<Rightarrow> (encode_bool (i > 0), i)
      | Sskip_cond \<Rightarrow> s))"


end