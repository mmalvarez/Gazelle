theory RepeatedSublocales imports Main

begin

locale wrap =
  fixes change :: "nat \<Rightarrow> nat"
begin

definition doit :: "nat \<Rightarrow> nat" where
"doit n = (change n) + 1"

end

definition doitt :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
"doitt change n = change n + 1"

value "doitt (\<lambda> x . x * 2) 1"

definition somemath :: "nat \<Rightarrow> nat" where
"somemath x = x * 2"


interpretation swag0 : wrap somemath 
  done


lemmas [code] =  wrap.doit_def

value "swag0.doit 1"

interpretation swag1 : wrap somemath
  done

lemma huhh : "swag0.doit 1 = 3"
  apply(simp) apply(simp add: swag0.doit_def) apply(simp add:somemath_def)
  done


  
locale testy = wrap

print_locale! wrap
print_locale! testy


sublocale testy \<subseteq> other : wrap
  where change = "\<lambda> x . change (doit x)"
  done

print_locale! wrap
print_locale! testy

interpretation swag2 : testy somemath  
  done


value [simp]  "swag2.other.doit 1"

end