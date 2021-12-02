theory Bump
  imports Mergeable
begin

(* Captures an important extension of mergeable - 
 * situations where we are dealing with a type (such as md_prio)
 * where we can easily calculate, for any valid x, the "next
 * largest value with the same contents
 *)

(* This is most useful when used with liftings; see the Lifter directory for details. *)

class Bump = Pord_Weak +
  fixes bump :: "'a \<Rightarrow> 'a"
  assumes bump_neq : "\<And> x . bump x \<noteq> x"
  assumes bump_geq : "\<And> x . x <[ bump x"

end