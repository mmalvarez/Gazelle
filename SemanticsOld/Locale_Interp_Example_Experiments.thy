theory Locale_Interp_Example_Experiments imports Main
begin

datatype wrapnat =
  WN nat

locale InnerS =
  (*fixes aty :: "'a itself"*)
  fixes denote :: "'a \<Rightarrow> nat"

locale Inner =
  InnerS +
  assumes "\<And> x . denote x < 42"

begin

fun isGood :: "'a \<Rightarrow> bool" where
"isGood x =  (denote x = 0)"


end

locale OuterS =
 (* fixes oty :: "'a itself" *)
  fixes denote2 :: "'a \<Rightarrow> wrapnat"

locale Outer = OuterS +
  assumes Hout : "\<And> x n . denote2 x = WN n \<Longrightarrow> n < 42"
begin

fun denote' :: "'a \<Rightarrow> nat" where
"denote' a = 
  (case denote2 a of
    WN n \<Rightarrow> n)"
(*
interpretation InnerInt1 : Inner  denote'
  done

lemma igForce : "? x . InnerInt1.isGood = x"
proof(blast)
qed
*)
end

(*
sublocale Outer \<subseteq> Inner where denote = denote'
  done
*)
  
print_locale! Outer

sublocale Outer \<subseteq> Inner  where denote = denote'
  apply(unfold_locales) apply(auto simp add:Hout)
  apply(case_tac "denote2 x") apply(auto simp add:Hout)
  done

print_locale Outer


global_interpretation InnerInt : Inner "(\<lambda> (_ :: nat) . 0)"
  defines InnerInt_code_isGood = InnerInt.isGood
  apply(unfold_locales, auto)
  done

lemmas [code_unfold] = InnerInt.isGood.simps

value "InnerInt.isGood 3"

global_interpretation OuterInt : Outer "(\<lambda> (_ :: nat) . WN 0)"
  defines OuterInt_Code_denote' = OuterInt.denote'
    and OuterInt_Code_isGood = OuterInt.isGood
  apply(unfold_locales, auto)
  done

(*lemmas [code] = InnerInt.isGood.simps*)
lemmas [code_unfold] = OuterInt.denote'.simps
lemmas [code_unfold] = OuterInt.isGood.simps

term "Inner.isGood"
term "OuterInt.isGood"
term "InnerInt.isGood"
term "OuterInt.isGood"

value [nbe] "OuterInt.isGood 3"

(*
definition OuterInt_code_denote' :: "_" where
[code del]: "OuterInt_code_denote' = Outer.denote' (\<lambda> _ . WN 0)"

definition OuterInt_code_isGood :: "_" where
[code del]: "OuterInt_code_isGood = Inner.isGood OuterInt_code_denote'"

interpretation OuterInt :
  Outer "(\<lambda> _ . WN 0)" rewrites
    "Outer.denote' (\<lambda> _ . WN 0)  = OuterInt_code_denote' " and
    "Inner.isGood (OuterInt_code_denote')  = OuterInt_code_isGood"
    
  apply(unfold_locales) apply(auto simp add: fun_eq_iff OuterInt_code_isGood_def OuterInt_code_denote'_def)
  done


(* I expect ExampleInt2.ExampleInt.isGood to be added to the
   local context, but it does not seem to be. The following
   line fails. *)


(* if we interpret ExampleInt directly into the local theory, we
 get what I expect, though there are no code equations. *)
interpretation InnerInt2 :
  Inner "\<lambda> (x :: nat) . 0"
  done


*)

end