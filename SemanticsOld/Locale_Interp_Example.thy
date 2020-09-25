theory Locale_Interp_Example imports Main
begin

datatype wrapnat =
  WN nat

locale Inner =
  fixes denote :: "'a \<Rightarrow> nat"
begin

fun isGood :: "'a \<Rightarrow> bool" where
"isGood x =  (denote x = 0)"

end

locale Outer =
  fixes denote2 :: "'a \<Rightarrow> wrapnat"
begin

fun denote' :: "'a \<Rightarrow> nat" where
"denote' a = 
  (case denote2 a of
    WN n \<Rightarrow> n)"

interpretation  InnerInt1 :
  Inner denote'
  done
end

interpretation OuterInt :
  Outer "(\<lambda> _ . WN 0)" 
  done

print_interps Inner

(* I expect ExampleInt2.ExampleInt.isGood to be added to the
   local context, but it does not seem to be. The following
   line fails. *)
term "OuterInt.InnerInt1.isGood"


(* if we interpret ExampleInt directly into the local theory, we
 get what I expect, though there are no code equations. *)
interpretation InnerInt2 :
  Inner "\<lambda> (x :: nat) . 0"
  done

term "InnerInt2.isGood"


end