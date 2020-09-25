theory Subtyping_Test
imports Main
begin

typedef nznat = "{ (x :: nat) .  x \<noteq> (0 :: nat)}"
proof(auto)
qed

lemma funex :
  "(\<And> x . f x = g x) \<Longrightarrow>
   f = g"
  apply(blast)
  done

quotient_type nznat' = "nat option" / 
    partial:
    "\<lambda> n1 n2 . case (n1, n2) of
                (None, None) \<Rightarrow> True
                | (Some 0, None) \<Rightarrow> True
                | (None, Some 0) \<Rightarrow> True
                | (_, _) \<Rightarrow> n1 = n2"
  apply(rule part_equivpI)

    apply(rule_tac x = None in exI) apply(fastforce)

  apply(simp add:symp_def)
  apply(rule_tac allI)
apply(rule_tac allI)
  apply(case_tac x, case_tac y, auto)
        apply(case_tac a, auto)
   apply(case_tac a, auto)

   apply(case_tac y, auto)

  apply(simp add:transp_def)
  apply(rule_tac allI)
  apply(rule_tac allI)

  apply(case_tac x, case_tac y, auto)
   apply(case_tac a, auto)
   apply(case_tac z, auto)

  apply(case_tac a, auto)
  apply(case_tac y, auto)
   apply(case_tac z, auto)

  apply(case_tac a, auto)
  done

setup_lifting type_definition_nznat

lift_definition getnat :: "nznat \<Rightarrow> nat" is id
  done

lift_definition getnznat :: "nat \<Rightarrow> nznat" is
  "Abs_nznat"
  done

declare [[coercion_enabled]]

(*declare [[coercion Rep_nznat]]*)
declare [[coercion Abs_nznat]]

(* problem is that we can only go one direction
with coercions *)

value  "(3 :: nat)"

datatype 'a booly =
  Mybooly "'a" "bool"

value "Mybooly (3 :: nat) True"
value "(Mybooly ((3 :: nat)) True) :: nznat booly"

value [nbe] "Rep_nznat (Abs_nznat (0 :: nat))"

end