theory Myopt imports Main

begin

(*
typedef 'a myopt =
  "UNIV :: ('a + unit) set"
  by auto

setup_lifting type_definition_myopt

lift_definition inc :: "nat myopt \<Rightarrow> nat myopt"
  is "(\<lambda> x . (1 :: nat) + x)"
*)
end