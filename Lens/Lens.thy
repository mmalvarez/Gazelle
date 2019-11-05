theory Lens imports "../Syntax_Utils"

begin

record ('m1, 'c) lens_parms =
  upd :: "('m1 * 'c \<Rightarrow> 'c)"
  proj :: "('c \<Rightarrow> 'm1)"

declare lens_parms.defs [simp]

locale Lens =
  fixes Lens_parms ::
    "('m1, 'c) lens_parms"

begin

abbreviation upd :: "('m1 * 'c \<Rightarrow> 'c)" where
"upd \<equiv> lens_parms.upd Lens_parms"

abbreviation proj :: "('c \<Rightarrow> 'm1)" where
"proj \<equiv> lens_parms.proj Lens_parms"

definition liftp :: "('m1 \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'a)" where
"liftp f x = f (proj x)"

definition lowerp :: "('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'm1)" where
"lowerp f x = proj (f x)"

(* not fully concrete, use with care *)
definition lifts :: "('a \<Rightarrow> 'm1) \<Rightarrow> ('a \<Rightarrow> 'c)" where
"lifts f x =
  upd (SOME x' . fst x' = f x)"

definition lowers :: "('c \<Rightarrow> 'a) \<Rightarrow> ('m1 \<Rightarrow> 'a)" where
"lowers f x =
  f (upd (SOME x' . fst x' = x ))"

end

locale Lens_Spec = Lens +
  assumes GetPut : "\<And> m1c . proj (upd m1c) = fst m1c"
  assumes PutGet' : "\<And> c . upd (pmap2 (proj, id) (pfan2 c)) = c"
  assumes PutPut' : "\<And> m1m1'c .
                         upd (pmap2 (id, upd) m1m1'c) = upd (pmap2 (id, snd) m1m1'c)"

begin

lemma PutGet : "\<And> c . upd (proj c, c) = c"
  apply(insert PutGet') apply(simp)
  done

lemma PutPut : 
  fixes m m' c
  shows "upd (m, upd (m', c)) = upd( m, c)"
  apply(insert PutPut'[of "(m, m', c)"]) apply(simp)
  done  

end

end