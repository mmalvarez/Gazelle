theory Prod_Merge imports "../Syntax_Utils"

begin

locale Prod_Merge =
  fixes parms :: 
      "(('m1 * 'c \<Rightarrow> 'c) *
        ('m2 * 'c \<Rightarrow> 'c) *
        ('c \<Rightarrow> 'm1) *
        ('c \<Rightarrow> 'm2))"
begin

definition upd1 :: "('m1 * 'c \<Rightarrow> 'c)" where
"upd1 = fst parms"

definition upd2 :: "('m2 * 'c \<Rightarrow> 'c)" where
"upd2 = tnth2h parms"

definition proj1 :: "('c \<Rightarrow> 'm1)" where
"proj1 = tnth3h parms"

definition proj2 :: "('c \<Rightarrow> 'm2)" where
"proj2 = tnth3t parms"

definition lift1p :: "('m1 \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'a)" where
"lift1p f x = f (proj1 x)"

definition lift2p :: "('m2 \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'a)" where
"lift2p f x = f (proj2 x)"

definition lower1p :: "('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'm1)" where
"lower1p f x = proj1 (f x)"

definition lower2p :: "('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'm2)" where
"lower2p f x = proj2 (f x)"

(* these are not fully concrete *)
(* also i am not fully convinced these definitions
are dual *)
definition lift1s :: "('a \<Rightarrow> 'm1) \<Rightarrow> ('a \<Rightarrow> 'c)" where
"lift1s f x =
  upd1 (SOME x' . fst x' = f x)"

definition lift2s :: "('a \<Rightarrow> 'm2) \<Rightarrow> ('a \<Rightarrow> 'c)" where
"lift2s f x =
  upd2 (SOME x' . fst x' = f x)"

definition lower1s :: "('c \<Rightarrow> 'a) \<Rightarrow> ('m1 \<Rightarrow> 'a)" where
"lower1s f x =
  f (upd1 (SOME x' . fst x' = x ))"

definition lower2s :: "('c \<Rightarrow> 'a) \<Rightarrow> ('m2 \<Rightarrow> 'a)" where
"lower2s f x =
  f (upd2 (SOME x' . fst x' = x ))"

end

locale Prod_Merge_Spec = Prod_Merge +
  assumes Hprod1 : "\<And> m1c . proj1 (upd1 m1c) = fst m1c"
  assumes Hprod2 : "\<And> m2c . proj2 (upd2 m2c) = fst m2c"
  assumes Hupd12 : "\<And> (c :: 'b) (c' :: 'b) .
    upd1 (pmap2 (id, upd2) (pmap3 (proj1, proj2, (const c')) (pfan3 c))) = c"
assumes Hupd21 : "\<And> (c :: 'b) (c' :: 'b) .
    upd2 (pmap2 (id, upd1) (pcomm3_1_2 (pmap3 (proj1, proj2, (const c')) (pfan3 c)))) = c"