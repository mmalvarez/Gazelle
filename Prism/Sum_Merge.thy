theory Sum_Merge imports "Prism"

begin

record ('s1, 's2, 'c) sum_merge_parms =
  prism1 :: "('s1, 'c) prism_parms"
  prism2 :: "('s2, 'c) prism_parms"

declare sum_merge_parms.defs [simp]
locale Sum_Merge' =
  fixes Sum_Merge_parms :: 
      "('a, 'b, 'c) sum_merge_parms"

locale Sum_Merge = Sum_Merge' +
  P1 : Prism "prism1 Sum_Merge_parms" +
  P2 : Prism "prism2 Sum_Merge_parms"

begin

abbreviation cases1 :: "('c \<Rightarrow> 'a + 'c)" where
"cases1 \<equiv> P1.cases"

abbreviation cases2 :: "('c \<Rightarrow> 'b + 'c)" where
"cases2 \<equiv> P2.cases"

abbreviation inj1 :: "('a \<Rightarrow> 'c)" where
"inj1 \<equiv> P1.inj "

abbreviation inj2 :: "('b \<Rightarrow> 'c)" where
"inj2 \<equiv> P2.inj"

(*declare case1_def case2_def inj1_def inj2_def [simp]*)
(*
definition lift1s :: "('a \<Rightarrow> 's1) \<Rightarrow> ('a \<Rightarrow> 'c)" where
"lift1s f x =
  inj1 (f x)"

definition lift2s :: "('a \<Rightarrow> 's2) \<Rightarrow> ('a \<Rightarrow> 'c)" where
"lift2s f x =
  inj2 (f x)"

definition lower1s :: "('c \<Rightarrow> 'a) \<Rightarrow> ('s1 \<Rightarrow> 'a)" where
"lower1s f x =
  f (inj1 x)"

definition lower2s :: "('c \<Rightarrow> 'a) \<Rightarrow> ('s2 \<Rightarrow> 'a)" where
"lower2s f x =
  f (inj2 x)"
(* warning: these are not fully concrete *)
(* question: are these "more restricted" than the dual
   ones for products? if so, why? do we need separate ones
   to deal with booleans? *)
(* optionize these? *)
definition lift1p :: "('s1 \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'a)" where
"lift1p f x =
  f (SOME x' . case1 x = Inl x')"

definition lift2p :: "('s2 \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'a)" where
"lift2p f x =
  f (SOME x' . case2 x = Inl x')"

definition lower1p :: "('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 's1)" where
"lower1p f x =
  (SOME x' . case1 (f x) = Inl x')"

definition lower2p :: "('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 's2)" where
"lower2p f x =
  (SOME x' . case2 (f x) = Inl x')"
*)
end

(* TODO: prove some sanity-check lemmas here *)
locale Sum_Merge_Spec = Sum_Merge +
  SP1 : Prism_Spec "prism1 Sum_Merge_parms" +
  SP2 : Prism_Spec "prism2 Sum_Merge_parms" +

(* TODO: have a version of this that is even more obviously dual to the Coh for Prod_Merge? *)
assumes Coh' :
    "\<And> c .
          smap2 (sfan2, Inl) (deassoc_sum (smap3 (inj1, inj2, id) (smap2 (id, cases2) (cases1 c)))) =
          smap2 (sfan2, Inr) (deassoc_sum (smap3 (inj2, inj1, id) (smap2 (id, cases1) (cases2 c))))"

begin

lemma Coh1 :
  fixes c c'
  shows "cases1 c = Inr c' \<Longrightarrow>
   (\<exists> c2 . cases2 c' = Inl c2 \<and> inj2 c2 = c)"
  apply(insert Coh'[of c]) apply(simp) apply(case_tac "cases1 c") apply(simp)
  apply(simp) apply(case_tac "cases2 c'") apply(simp)
apply(insert SP2.InjCase[of c]) 
   apply(case_tac "cases2 c") apply(simp)
   apply(insert SP2.InjCase[of c]) apply(simp)

   apply(case_tac "cases2 c") apply(simp)
  apply(insert SP2.InjCase[of c]) apply(simp)
  done

lemma Coh2 :
  "cases2 c = Inr c' \<Longrightarrow>
   (\<exists> c1 . cases1 c' = Inl c1 \<and> inj1 c1 = c)"
  apply(insert Coh'[of c]) apply(simp) apply(case_tac "cases2 c") apply(simp)
  apply(simp) apply(case_tac "cases1 c'") apply(simp)
apply(insert SP1.InjCase[of c]) 
   apply(case_tac "cases1 c") apply(simp)
   apply(insert SP1.InjCase[of c]) apply(simp)

   apply(case_tac "cases1 c") apply(simp)
  apply(insert SP1.InjCase[of c]) apply(simp)
  done


end