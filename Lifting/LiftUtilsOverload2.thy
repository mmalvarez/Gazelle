theory LiftUtilsOverload2
  imports "LiftUtils" "LiftInstances" "HOL-Library.Adhoc_Overloading"
begin

consts default_lifting :: 
"('a, 'b, 'c) lifting"

class base =
  fixes dob :: "'a \<Rightarrow> 'a"

class triv 
class opt 

instantiation nat :: base begin
definition dobn : "dob = (id :: nat \<Rightarrow> nat)"
instance proof qed
end

instantiation bool :: base begin
definition dobb : "dob = (id :: bool \<Rightarrow> bool)"
instance proof qed
end

instantiation unit :: base begin
definition dobu : "dob = (id :: unit \<Rightarrow> unit)"
instance proof qed
end

class lev1
instantiation option :: (base) lev1 begin
instance proof qed
end
instantiation md_triv :: (base) lev1 begin
instance proof qed
end

class lev2
instantiation option :: (lev1) lev2 begin
instance proof qed
end

instantiation md_triv :: (lev1) lev2 begin
instance proof qed
end

(*
type_synonym lift_spec = "('a itself * 'b itself * 'c itself)"
*)
overloading 
  dlb \<equiv> "default_lifting :: ('a, 'b, 'b) lifting" (unchecked)
  dlo1 \<equiv> "default_lifting :: ('a, 'b, 'c option) lifting" (unchecked)
  dlt1 \<equiv> "default_lifting :: ('a, 'b, 'c md_triv) lifting" (unchecked)

begin

definition dlb :: "('a, 'b, 'b :: base) lifting"  where "dlb = id_l"
definition dlo1 :: "('a, 'b, 'c option) lifting" where "dlo1 = option_l default_lifting"
definition dlt1 :: "('a, 'b, 'c md_triv) lifting" where "dlt1 = triv_l default_lifting"

end

declare [[show_variants]]

declare [[show_types]]

term "default_lifting :: (unit, nat, nat option) lifting"
value [nbe] "default_lifting :: (unit, nat, nat md_triv option) lifting"

lemma "(default_lifting :: (unit, nat, nat md_triv option) lifting) =
       option_l (triv_l id_l)" 
  apply(simp add: dlb_def dlo1_def dlt1_def)

(*
adhoc_overloading default_lifting
"id_l :: ('a, 'b, 'b :: base) lifting"
"(triv_l default_lifting) :: ('a, 'b, ('b :: base) md_triv) lifting"
"(option_l default_lifting)  :: ('a, 'b, ('b :: base) option) lifting"

declare [[show_variants]]
*)
term "default_lifting :: (unit, nat, nat) lifting"
term "default_lifting :: (unit, nat, nat option) lifting"


end