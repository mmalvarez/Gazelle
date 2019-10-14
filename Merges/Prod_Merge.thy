theory Prod_Merge imports "Lens"

begin

record ('s1, 's2, 'c) prod_merge_parms =
  lens1 :: "('s1, 'c) lens_parms"
  lens2 :: "('s2, 'c) lens_parms"

declare prod_merge_parms.defs [simp]

locale Prod_Merge' =
  fixes Prod_Merge_Parms :: "('a, 'b, 'c) prod_merge_parms" 

locale Prod_Merge = Prod_Merge' +
  L1 : Lens "prod_merge_parms.lens1 Prod_Merge_Parms" +
  L2 : Lens "prod_merge_parms.lens2 Prod_Merge_Parms"
begin

print_context

abbreviation upd1 :: "('a * 'c \<Rightarrow> 'c)" where
"upd1 \<equiv> L1.upd"

abbreviation upd2 :: "('b * 'c \<Rightarrow> 'c)" where
"upd2 \<equiv> L2.upd"

abbreviation proj1 :: "('c \<Rightarrow> 'a)" where
"proj1 \<equiv> L1.proj"

abbreviation proj2 :: "('c \<Rightarrow> 'b)" where
"proj2 \<equiv> L2.proj"

(*
definition lift1p :: "('a \<Rightarrow> 'x) \<Rightarrow> ('c \<Rightarrow> 'x)" where
"lift1p = L1.liftp"

definition lift2p :: "('b \<Rightarrow> 'x) \<Rightarrow> ('c \<Rightarrow> 'x)" where
"lift2p = L2.liftp"

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
*)
end

locale Prod_Merge_Spec = Prod_Merge +
  SL1 : Lens_Spec "prod_merge_parms.lens1 Prod_Merge_Parms" +
  SL2 : Lens_Spec "prod_merge_parms.lens2 Prod_Merge_Parms" +

(* use "total" instead? *)
assumes Put12' : "\<And> m1m2cc' .
    upd1 (pmap2 (id, upd2) (pmap3 (id, id, fst) m1m2cc')) =
    upd1 (pmap2 (id, upd2) (pmap3 (id, id, snd) m1m2cc'))"

assumes Put21' : "\<And> m2m1cc' .
    upd2 (pmap2 (id, upd1) (pmap3 (id, id, fst) m2m1cc')) =
    upd2 (pmap2 (id, upd1) (pmap3 (id, id, snd) m2m1cc'))"

assumes Coh' : "\<And> cc'c'' . 
    upd1 (pmap2 (id, upd2) (pmap3 (proj1, proj2, id) (reassoc_prod (pmap2 (pfan2, fst) cc'c'')))) =
    upd2 (pmap2 (id, upd1) (pmap3 (proj2, proj1, id) (reassoc_prod (pmap2 (pfan2, snd) cc'c''))))"
begin

lemma Coh :
  fixes c c' c''
  shows "upd1 (proj1 c, upd2 (proj2 c, c')) =
                               upd2 (proj2 c, upd1 (proj1 c, c''))"
  apply(insert Coh'[of "(c, c', c'')"]) apply(simp)
  done

lemma Put12 :
  fixes m1 m2 c c'
  shows "upd1 (m1, (upd2 (m2, c))) = upd1 (m1, (upd2 (m2, c')))"
  apply(insert Put12'[of "(m1, m2, c, c')"]) apply(simp)
  done

lemma Put21 :
  fixes m2 m1 c c'
  shows  "upd2 (m2, (upd1 (m1, c))) = upd2 (m2, (upd1 (m1, c')))"
  apply(insert Put21'[of"(m2, m1, c, c')"]) apply(simp)
  done

lemma Coh_id1 :
  fixes c c'
  shows "upd1 (proj1 c, upd2 (proj2 c, c')) = c"
  apply(insert Put12[of "proj1 c" "proj2 c" c' c])
  apply(insert SL2.PutGet[of c]) apply(simp)
  apply(insert SL1.PutGet[of c]) apply(simp)
  done

lemma Coh_id2 :
  fixes c c'
  shows "upd2 (proj2 c, upd1 (proj1 c, c')) = c"
  apply(insert Put21[of "proj2 c" "proj1 c" c' c])
  apply(insert SL1.PutGet[of c]) apply(simp)
  apply(insert SL2.PutGet[of c]) apply(simp)
  done

(* TODO: use total as an axiom? *)
lemma total :
  fixes c1 c2
  shows "proj1 c1 = proj1 c2 \<Longrightarrow> proj2 c1 = proj2 c2 \<Longrightarrow> c1 = c2"
  apply(insert Coh[of c1 c2 c1])
  apply(insert Coh_id2[of c1 c1]) apply(simp)
  apply(simp add:SL2.PutGet)
  apply(thin_tac "upd2 (proj2 c2, upd1 (proj1 c2, c1)) = c1")
  apply(simp add:SL1.PutGet)
  done

end