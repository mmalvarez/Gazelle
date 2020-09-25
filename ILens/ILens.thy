theory ILens imports Main
begin

record ('i, 'm, 'c) ilens_parms =
  upd :: "('i * 'm * 'c) \<Rightarrow> 'c"
  proj :: "('i * 'c) \<Rightarrow> ('m + 'c)"

declare ilens_parms.defs [simp]

locale ILens =
  fixes ILens_parms :: "('i, 'm, 'c) ilens_parms"

begin

abbreviation upd :: "(('i * 'm * 'c) \<Rightarrow> 'c)" where
"upd \<equiv> ilens_parms.upd ILens_parms"

abbreviation proj :: "(('i * 'c) \<Rightarrow> ('m + 'c))" where
"proj \<equiv> ilens_parms.proj ILens_parms"


end

locale ILens_Spec = ILens +
(*
  assumes GetPut : "\<And> i m c . 
        (case proj (i, upd (i, m, c)) of
          Inl m' \<Rightarrow> m = m'
          | Inr c' \<Rightarrow> c = c')"
*)

(* idea: update might fail if we tried to update the wrong component (?) *)
assumes GetPut : "\<And> i m c m' . 
        proj (i, upd (i, m, c)) = Inl m' \<Longrightarrow> m = m'"

assumes PutGet1 : "\<And> i c m .
    proj (i, c) = Inl m \<Longrightarrow> upd (i, m, c) = c"

assumes PutGet2 : "\<And> i c c' .
    proj (i, c) = Inr c' \<Longrightarrow> c = c'"

assumes PutPut : "\<And> i m m' c .
        (upd (i, m, (upd (i, m', c))) = upd (i, m, c))"


locale ILens_Total_Spec = ILens_Spec +
  assumes Total: "\<And> i c . \<exists> m . proj (i, c) = Inl m"

locale ILens_Prism_Total_Spec = ILens_Spec +
  assumes PTotal : "\<And> c. \<exists> i m . proj (i, c) = Inl m"

(* i'm confused, do we neven need to prove these? *)
locale ILens_Coh_Spec = ILens_Spec +
  assumes Coh12 : "\<And> i i' c m m' .
        proj (i, c) = Inl m \<Longrightarrow>
        proj (i', c) = Inl m' \<Longrightarrow>
        upd (i, m, (upd (i', m', c))) = c"
  assumes Coh21 : "\<And> i i' c m m' .
        proj (i, c) = Inl m \<Longrightarrow>
        proj (i', c) = Inl m' \<Longrightarrow>
        upd (i', m', (upd (i, m, c))) = c"

locale ILens_Prism_Coh_Spec = ILens_Spec +
  assumes PCoh : "\<And> i i' c m m' .
        proj (i, c) = Inl m \<Longrightarrow>
        proj (i', c) = Inl m' \<Longrightarrow>
        upd (i, m, (upd (i', m', c))) =
        upd (i', m', (upd (i, m, c)))"

(*
locale IPrism =
  fixes ILens_parms :: "('i, 'm, 'c) ilens_parms"

begin

abbreviation cases :: "(('i * 'c) \<Rightarrow> ('m + 'c))" where
"cases \<equiv> ilens_parms.proj ILens_parms"

abbreviation inj :: "(('i * 'm * 'c) \<Rightarrow> 'c)" where
"inj \<equiv> ilens_parms.upd ILens_parms"

end

locale IPrism_Spec = IPrism +
(* can this fail? *)
  assumes CaseInj : "\<And> i m c . cases (i, inj (i, m, c)) = Inl m"
*)


record ('ii, 'i, 'oi, 'o, 'i1, 'i2, 'm1, 'm2, 'c1, 'c2, 'm, 'c) ilens_merge_parms =
  li :: "('ii, 'i, ('i1 + 'i2)) ilens_parms"
  oi :: "('oi, ('i1 + 'i2), 'o) ilens_parms"
  l1 :: "('i1, 'm1, 'c1) ilens_parms"
  l2 :: "('i2, 'm2, 'c2) ilens_parms"
  lm :: "('i, 'm, ('m1 + 'm2)) ilens_parms"
  lc :: "('o, ('c1 + 'c2), 'c) ilens_parms"
 

locale ILens_Merge' =
  fixes ILens_Merge_parms :: "('ii, 'i, 'oi, 'o, 'i1, 'i2, 'm1, 'm2, 'c1, 'c2, 'm, 'c) ilens_merge_parms"

begin
abbreviation li' where "li' \<equiv> li ILens_Merge_parms"
abbreviation oi' where "oi' \<equiv> oi ILens_Merge_parms"
abbreviation l1' where "l1' \<equiv> l1 ILens_Merge_parms"
abbreviation l2' where "l2' \<equiv> l2 ILens_Merge_parms"
abbreviation lm' where "lm' \<equiv> lm ILens_Merge_parms"
abbreviation lc' where "lc' \<equiv> lc ILens_Merge_parms"

end

locale ILens_Merge = ILens_Merge' +
  ILI : ILens li' +
  IOI : ILens oi' +
  IL1 : ILens l1' +
  IL2 : ILens l2' +
  ILM : ILens lm' +
  ILC : ILens lc'
begin
print_context
fun upd :: "('a * 