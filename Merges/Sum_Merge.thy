theory Sum_Merge imports "../Syntax_Utils"

begin

locale Sum_Merge =
  fixes parms :: 
      "(('c \<Rightarrow> 's1 + 'c) *
        ('c \<Rightarrow> 's2 + 'c) *
        ('s1 \<Rightarrow> 'c) *
        ('s2 \<Rightarrow> 'c))"

begin

definition case1 :: "('c \<Rightarrow> 's1 + 'c)" where
"case1 = fst (parms)"

definition case2 :: "('c \<Rightarrow> 's2 + 'c)" where
"case2 = tnth2h (parms)"

definition inj1 :: "('s1 \<Rightarrow> 'c)" where
"inj1 = tnth3h (parms)"

definition inj2 :: "('s2 \<Rightarrow> 'c)" where
"inj2 = tnth3t (parms)"

(*declare case1_def case2_def inj1_def inj2_def [simp]*)

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

end

(* TODO: prove some sanity-check lemmas here *)
locale Sum_Merge_Spec = Sum_Merge +
  assumes Hinj1 : "\<And> s1 . case1 (inj1 s1) = Inl s1"
  assumes Hinj2 : "\<And> s2 . case2 (inj2 s2) = Inl s2"
  assumes Hcase12 : "\<And> (c :: 'a) (c' :: 'a) .
      sfan3 (smap3 (inj1, inj2, const c') (smap2 (id, case2) (case1 c))) = c"
  assumes Hcase21 : "\<And> (c :: 'a) (c' :: 'a) . 
      sfan3 (smap3 (inj1, inj2, const c') (scomm3_1_2 (smap2 (id, case1) (case2 c)))) = c"


end