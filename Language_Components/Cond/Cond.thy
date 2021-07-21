theory Cond imports Main
begin

(* conditional/boolean expressions *)
datatype cond =
  Seqz
  | Sltz
  | Sgtz
  | Sskip_cond

type_synonym cond_state = "bool * int"

definition cond_sem :: "cond \<Rightarrow> cond_state \<Rightarrow> cond_state" where
"cond_sem x s =
  (case s of (b, i) \<Rightarrow>
    (case x of
      Seqz \<Rightarrow> ((i = 0), i)
      | Sltz \<Rightarrow> ((i < 0), i)
      | Sgtz \<Rightarrow> ((i > 0), i)
      | Sskip_cond \<Rightarrow> s))"


end