theory View_Rep3 imports View "../Isos/Iso"

begin

type_synonym ('l, 'r) iso_parm = "('l \<Rightarrow> 'r) * ('r \<Rightarrow> 'l)"

locale View_Rep' =
  (*fixes zy :: "('z, 'w * 'y) iso_parm" *)
  (*fixes fzy :: "('z \<Rightarrow> 'y)"*)
  fixes repp :: "('a, (('x + ('z) + ('b * 'y)))) iso_parm"

locale View_Rep =
  View_Rep' +
  (*Izy : Iso_Spec "zy :: ('z, 'y * 'w) iso_parm" + *)
  I : Iso_Spec "repp :: ('a, (('x + ('z) + ('b * 'y)))) iso_parm"

begin

fun prj' :: "'a \<Rightarrow> ('b + 'a)" where
"prj' a =
  (case I.to_r a of
    (Inl _) \<Rightarrow> Inr a
    | (Inr (Inl _)) \<Rightarrow> Inr a
    | (Inr (Inr (b, _))) \<Rightarrow> Inl b)"

fun inj' :: "'b * 'a \<Rightarrow> 'a" where
"inj' (b, a) =
  (case I.to_r a of
    (Inl _) \<Rightarrow> a
    | (Inr (Inl (z))) \<Rightarrow> I.to_l (Inr (Inr (b, fzy z)))
    | (Inr (Inr (b', y))) \<Rightarrow> I.to_l (Inr (Inr (b, y))))"

abbreviation vp :: "('b, 'a) view_parms" where
"vp \<equiv> \<lparr> inj = inj', prj = prj' \<rparr>"

end

(* soundness *)
locale View_Rep_Sound = View_Rep
begin

end
sublocale View_Rep_Sound \<subseteq> View_Spec vp

  apply(unfold_locales)
      apply(simp split:sum.splits prod.splits)

      apply(cut_tac l = r in I.Hisol) apply(simp)

      apply(simp split:sum.splits prod.splits)
  
      apply(simp split:sum.splits prod.splits)
     apply(simp add: I.Hisol I.Hisor)

    apply(simp add: I.Hisol I.Hisor)

   apply(simp split:sum.splits prod.splits)
    apply(simp add: I.Hisol I.Hisor)

      apply(clarsimp)
      apply(simp add: I.Hisol I.Hisor)

  apply(clarsimp)
     apply(simp add: I.Hisol I.Hisor)

  apply(clarsimp)
     apply(simp add: I.Hisol I.Hisor)

  apply(clarsimp)
     apply(simp add: I.Hisol I.Hisor)

  apply(clarsimp)
     apply(simp split:sum.splits prod.splits add: I.Hisol I.Hisor)
  done

(* completeness *)
locale View_Rep_Complete' = View_Spec

begin

(* need to separately specify our input parameters so that we can get a valid iso *)
definition X :: "'b set" where
  "X = { (b :: 'b) . \<exists> a' b' . prj (inj (a', b)) = Inr b' }"

definition Y :: "('a \<Rightarrow> 'b) set" where
  "Y = { (f ) . \<exists> b .  f = (\<lambda> a . inj (a, b)) \<and>
        (\<forall> a . prj (f a) = Inl a) }"
(*
definition Z :: "(('a \<Rightarrow> 'b) * ('b \<Rightarrow> 'b)) set" where
  "Z = {(f :: ('a \<Rightarrow> 'b), g :: ('b \<Rightarrow> 'b)) .
          (\<exists> (b :: 'b) . f = (\<lambda> a . inj (a, b)) \<and>
          (\<exists> (a :: 'a) (a' :: 'a) . prj (inj (a, b)) = Inl a') \<and>
          (\<forall> bx . g bx = bx)) }"
*)

definition Z :: "(('a \<Rightarrow> 'b) * 'b) set" where
  "Z = { (f, b) . f = (\<lambda> a . inj (a, b)) \<and>
        prj b = Inr b \<and>
          (\<forall> (a :: 'a) . prj (f a) = Inl a) }"

(*
definition Z :: "(('a \<Rightarrow> 'b) * ('b \<Rightarrow> 'b)) set" where
  "Z = {(f :: ('a \<Rightarrow> 'b), g :: ('b \<Rightarrow> 'b)) .
          (\<exists> (b :: 'b) . f = (\<lambda> a . inj (a, b)) \<and>
          (\<exists> (a :: 'a) (a' :: 'a) . prj (inj (a, b)) = Inl a') \<and>
          (\<forall> bx . prj (g bx) = Inr bx)) }"
*)
(*
definition Z :: "('a \<Rightarrow> 'b) set" where
  "Z = {f :: ('a \<Rightarrow> 'b) .
          (\<exists> (b :: 'b) . f = (\<lambda> a . inj (a, b)) \<and>
          (\<exists> (a :: 'a) . prj b = Inl a)) }"
*)
end

locale View_Rep_Complete = View_Rep_Complete' +
  fixes Xrep :: "'x \<Rightarrow> 'b"
  fixes Xabs :: "'b \<Rightarrow> 'x"
  fixes Yrep :: "'y \<Rightarrow> ('a \<Rightarrow> 'b)"
  fixes Yabs :: "('a \<Rightarrow> 'b) \<Rightarrow> 'y"
  fixes Zrep :: "'z \<Rightarrow> (('a \<Rightarrow> 'b) * 'b)"
  fixes Zabs :: "(('a \<Rightarrow> 'b) * 'b) \<Rightarrow> 'z"

  assumes Xrep_spec : "\<And> x . Xrep x \<in> X"
  assumes Yrep_spec : "\<And> y . Yrep y \<in> Y"
  assumes Zrep_spec : "\<And> z . Zrep z \<in> Z"


assumes Xrep_inverse : "\<And> x . Xabs (Xrep x) = x"
assumes Yrep_inverse : "\<And> y . Yabs (Yrep y) = y"
assumes Zrep_inverse : "\<And> z . Zabs (Zrep z) = z"


assumes Xabs_inverse : "\<And> b . b \<in> X \<Longrightarrow> Xrep (Xabs b) = b"
assumes Yabs_inverse : "\<And> b . b \<in> Y \<Longrightarrow> Yrep (Yabs b) = b"
assumes Zabs_inverse : "\<And> b . b \<in> Z \<Longrightarrow> Zrep (Zabs b) = b"

begin

print_context

(*
fun to_r' :: "'b \<Rightarrow> ('x + ('y * 'z) + ('a * 'z))" where
"to_r' b =
  (case prj b of
      Inr _ \<Rightarrow> Inl (Xabs b)
    | Inl a \<Rightarrow> Inr (Inr (a, Zabs (\<lambda> a . inj (a, b)))))"
*)

fun fzy' :: "'z \<Rightarrow> 'y" where
"fzy' z =
  Yabs (fst (Zrep z))"


fun to_r' :: "'b \<Rightarrow> (('z \<Rightarrow> 'y) * ('x + ('z) + ('a * 'y)))" where
"to_r' b =
  (case prj b of
      Inr _ \<Rightarrow> (case prj (inj (undefined, b)) of
                      Inr _ \<Rightarrow> (fzy', Inl (Xabs b))
                      | Inl _ \<Rightarrow> (fzy', Inr (Inl (Zabs (\<lambda> a . inj(a, b), b)))))
    | Inl a \<Rightarrow> (fzy', Inr (Inr (a, Yabs (\<lambda> a. inj (a, b))))))"


(*
fun to_l' :: "('x + ('y * 'z) + ('a * 'z)) \<Rightarrow> 'b" where
"to_l' (Inl x) = Xrep x"
| "to_l' (Inr (Inl (y, z))) = Yrep y" (* this one is bad. *)
| "to_l' (Inr (Inr (a, z))) =
    Zrep z a"
*)

fun to_l' :: "(('z \<Rightarrow> 'y) * ('x + ('z) + ('a * 'y))) \<Rightarrow> 'b" where
"to_l' (_, Inl x) = Xrep x"
| "to_l' (_, Inr (Inl (z))) = 
    snd (Zrep z)"

| "to_l' (_, Inr (Inr (a, y))) =
    Yrep y a"

(*
fun to_l' :: "('x + ('z) + ('a * 'y)) \<Rightarrow> 'b" where
"to_l' (Inl x) = Xrep x"
| "to_l' (Inr (Inl (z))) = 
    Zrep z"

| "to_l' (Inr (Inr (a, y))) =
    inj (a, Yrep y)"
*)
(*
| "to_l' (Inr (Inr (a, y))) =
    Yrep y"
*)
(*
fun to_l' :: "('x + ('y * 'z) + ('a * 'z)) \<Rightarrow> 'b" where
"to_l' (Inl x) = Xrep x"
| "to_l' (Inr (Inl (y, z))) =
    (case prj (Yrep y) of
        Inl a \<Rightarrow> Zrep z a
        | Inr _ \<Rightarrow> (Yrep y))" (* this one was bad. and still is... *)
| "to_l' (Inr (Inr (a, z))) =
    Zrep z a"
 *)

abbreviation rep' :: "('b, ('z \<Rightarrow> 'y) * ('x + ('z) + ('a * 'y))) iso_parm" where
"rep' \<equiv> (to_r', to_l')"

(* idea: need to define x and y,
   as well as iso *)

end

sublocale View_Rep_Complete \<subseteq> View_Rep rep'
  apply(unfold_locales)
   apply(simp split:sum.splits prod.splits) apply(safe)


  apply(cut_tac b = "(\<lambda>a. local.inj (a, l))" in Yabs_inverse)
       apply(simp add:Y_def) apply(auto)
  apply(case_tac "local.prj (local.inj (a, l))")

        apply(frule_tac d = a in InjPrj1) apply(simp)
       apply(frule_tac d' = undefined in InjPrj2) apply(simp)

       apply(frule_tac r = l in PrjInj1)
      apply(simp)

     apply(cut_tac b = "((\<lambda>a. local.inj (a, l), l))" in Zabs_inverse)
      apply(simp add:Z_def) apply(frule_tac PrjInj2) apply(simp)
      apply(clarsimp)

      apply(case_tac "local.prj (local.inj (a, x2))")
       apply (frule_tac d = a in InjPrj1) apply(simp)
  apply(frule_tac d' = undefined in InjPrj2) apply(simp)

     apply(clarsimp)
    apply(frule_tac d' = x1 in InjPrj2)
  apply(frule_tac PrjInj1) apply(simp)

     apply(cut_tac b = l in Xabs_inverse) apply(simp add:X_def) apply(auto)

  apply(auto split:sum.splits prod.splits)
  apply(case_tac b, auto)

      apply(cut_tac x = aa in Xrep_spec) apply(simp add:X_def) apply(clarsimp)
      apply(drule_tac d' = undefined in InjPrj2) apply(simp)

     apply(case_tac ba, clarsimp)
        apply(cut_tac z = aa in Zrep_spec) apply(simp add:Z_def)
  apply(simp split:prod.splits)

     apply(clarsimp)
       apply(cut_tac y = b in Yrep_spec) apply(simp add:Y_def) apply(auto)
       apply(simp add:InjInj) apply(cut_tac y = ba in Yrep_inverse) apply(simp)

    apply(case_tac r) apply(clarsimp)

      apply(cut_tac x = a in Xrep_spec) apply(simp add:X_def) apply(clarsimp)
      apply(drule_tac d' = undefined in InjPrj2) apply(simp)

       apply(clarsimp)
       apply(case_tac b, clarsimp)
        apply(cut_tac z = a in Zrep_spec) apply(simp add:Z_def split:prod.splits)
        apply(cut_tac z = a in Zrep_inverse) apply(simp)

    apply(clarsimp)
  apply(cut_tac y = ba in Yrep_spec) apply(simp add:Y_def)

   apply(case_tac r) apply(clarsimp)
  apply(frule_tac r = "Xrep a" in PrjInj1)
      apply(cut_tac x = a in Xrep_spec) apply(simp add:X_def) apply(clarsimp)
    apply(drule_tac d' = x1 in InjPrj2) apply(simp)

        apply(clarsimp)
   apply(case_tac b, clarsimp)
    apply(frule_tac r = "(snd (Zrep a))" in PrjInj1)
    apply(drule_tac d' = x1 in InjPrj2) apply(simp)

  apply(clarsimp)

    apply(frule_tac r = "Yrep ba a" in PrjInj1)
    apply(drule_tac d' = x1 in InjPrj2) apply(simp)


  apply(case_tac r, clarsimp)
  apply(simp add:Xrep_inverse)

  apply(clarsimp)

  apply(case_tac b, clarsimp)
   apply(cut_tac z = a in Zrep_spec) apply(simp add:Z_def) apply(simp split:prod.splits)
  apply(auto)

  apply(cut_tac y = ba in Yrep_spec) apply(simp add:Y_def)
  done


(*
typedef ('a, 'b, 'x, 'y) view_rep =
  "{ (x :: 'x, y :: 'y, 
      i :: ('a, ('x + 'y + ('b * 'y))) iso_parm ) . 
      Iso_Spec i}"
  apply(auto) 
  apply(rule_tac x = "undefined" in exI) 
  apply(rule_tac x = "undefined" in exI)
  apply(simp add:Iso_Spec_def)
  *)
end