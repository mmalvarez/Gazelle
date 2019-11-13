theory Prism imports "../Syntax_Utils"
begin

record ('s1, 'c) prism_parms =
  cases :: "('c \<Rightarrow> 's1 + 'c)"
  inj :: "('s1 \<Rightarrow> 'c)"

declare prism_parms.defs [simp]

(* Prism is dual to lens *)
locale Prism =
  fixes Prism_parms ::
    "('s1, 'c) prism_parms"

begin

abbreviation cases :: "'c \<Rightarrow> ('s1 + 'c)" where
"cases \<equiv> prism_parms.cases Prism_parms"

abbreviation inj :: "'s1 \<Rightarrow> 'c" where
"inj \<equiv> prism_parms.inj Prism_parms"

definition lifts :: "('a \<Rightarrow> 's1) \<Rightarrow> ('a \<Rightarrow> 'c)" where
"lifts f x =
  inj (f x)"

definition lowers :: "('c \<Rightarrow> 'a) \<Rightarrow> ('s1 \<Rightarrow> 'a)" where
"lowers f x =
  f (inj x)"

definition liftp :: "('s1 \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'a)" where
"liftp f x =
  f (SOME x' . cases x = Inl x')"

definition lowerp :: "('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 's1)" where
"lowerp f x = (SOME x' . cases (f x) = Inl x')"


end

locale Prism_Spec = Prism +
  assumes CaseInj : "\<And> s1 . cases (inj s1) = Inl s1"
  assumes InjCase : "\<And> c . sfan2 (smap2 (inj, id) (cases c)) = c"
  (* should be provable from the other 2 *)
  assumes CaseCase : "\<And> c . smap2 (id, cases) (cases c) = smap2 (id, Inr) (cases c)"


begin

lemma CaseInr :
  fixes c c'
  shows "cases c = Inr c' \<Longrightarrow> c = c'"
  apply(insert InjCase[of c])
  apply(simp)
  done

lemma CaseInl :
  fixes c x
  shows "cases c = Inl x \<Longrightarrow> inj x = c"
  apply(insert InjCase[of c])
  apply(simp)
  done
  

end

end