theory ViewRep5 imports View "../Isos/Iso"

begin

type_synonym ('l, 'r) iso_parm = "('l \<Rightarrow> 'r) * ('r \<Rightarrow> 'l)"

locale View_Rep' =
  fixes iso1p :: "('a, ('x + ('b \<Rightarrow> 'z) + ('b * ('b \<Rightarrow> 'z)))) iso_parm"
  

locale View_Rep =
  View_Rep' +
  I : Iso_Spec "iso1p :: ('a, ('x + ('b \<Rightarrow> 'z) + ('b * ('b \<Rightarrow> 'z)))) iso_parm"

begin

fun prj' :: "'a \<Rightarrow> ('b + 'a)" where
"prj' a =
  (case I.to_r a of
    Inl _ \<Rightarrow> Inr a
    | Inr (Inl _) \<Rightarrow> Inr a
    | Inr (Inr (b, z)) \<Rightarrow> Inl b)"

fun inj' :: "'b * 'a \<Rightarrow> 'a" where
"inj' (b, a) =
  (case I.to_r a of
    Inl _ \<Rightarrow> a
    | Inr (Inl (y)) \<Rightarrow> I.to_l (Inr (Inr (b, y)))
    | Inr (Inr (b',z)) \<Rightarrow> I.to_l (Inr (Inr (b,z))))"

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
  print_context
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
  apply(simp split:sum.splits prod.splits add: I.Hisol I.Hisor)

  apply(clarsimp)
  apply(simp split:sum.splits prod.splits add: I.Hisol I.Hisor)

  apply(clarsimp)
  apply(simp split:sum.splits prod.splits add: I.Hisol I.Hisor)


  done

(* completeness *)
locale View_Rep_Complete' = View_Spec

begin

(* need to separately specify our input parameters so that we can get a valid iso *)
definition X :: "'b set" where
  "X = { (b :: 'b) . \<exists> a' b' . prj (inj (a', b)) = Inr b' }"

definition Z :: "('a \<Rightarrow> 'b) set" where
  "Z = {f :: ('a \<Rightarrow> 'b) .
          (\<exists> (b :: 'b) . 
              \<forall> (a :: 'a) . f a  = (inj (a, b)) \<and>
              (\<exists> (a :: 'a) . prj b = Inl a)) }"

(*
definition Y :: "('b) set" where
  "Y = { (b :: 'b) .
          (\<exists> b' . prj b = Inr b') \<and>
          (\<exists> (a' :: 'a) . prj (inj (a', b)) = Inl a') }"
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
  fixes Yrep :: "'y \<Rightarrow> 'b"
  fixes Yabs :: "'b \<Rightarrow> 'y" 
  fixes Zrep :: "'z \<Rightarrow> ('a\<Rightarrow> 'b)"
  fixes Zabs :: "('a \<Rightarrow> 'b) \<Rightarrow> 'z"

  assumes Xrep_spec : "\<And> x . Xrep x \<in> X"
(*  assumes Yrep_spec : "\<And> y . Yrep y \<in> Y" *)
  assumes Zrep_spec : "\<And> z . Zrep z \<in> Z"


assumes Xrep_inverse : "\<And> x . Xabs (Xrep x) = x"
assumes Yrep_inverse : "\<And> y . Yabs (Yrep y) = y"
assumes Zrep_inverse : "\<And> z . Zabs (Zrep z) = z"


assumes Xabs_inverse : "\<And> b . b \<in> X \<Longrightarrow> Xrep (Xabs b) = b"
(*assumes Yabs_inverse : "\<And> b . b \<in> Y \<Longrightarrow> Yrep (Yabs b) = b" *)
assumes Zabs_inverse : "\<And> f . f \<in> Z \<Longrightarrow> Zrep (Zabs f) = f"

begin

print_context

(*
fun to_r' :: "'b \<Rightarrow> ('x + ('y * 'z) + ('a * 'z))" where
"to_r' b =
  (case prj b of
      Inr _ \<Rightarrow> Inl (Xabs b)
    | Inl a \<Rightarrow> Inr (Inr (a, Zabs (\<lambda> a . inj (a, b)))))"
*)

fun to_r' :: "'b \<Rightarrow> (('x + ('a \<Rightarrow> 'z) + ('a * ('a \<Rightarrow> 'z))))" where
"to_r' b =
  (case prj b of
      Inr _ \<Rightarrow> (case prj (inj (undefined, b)) of
                      Inr _ \<Rightarrow> Inl (Xabs b)
                      | Inl _ \<Rightarrow> Inr (Inl (Zabs (\<lambda> a . inj (a, b)))))
    | Inl a \<Rightarrow> Inr (Inr (a, (\<lambda> b . Zabs (\<lambda> a . inj (a, b))))))"


(*
fun to_l' :: "('x + ('y * 'z) + ('a * 'z)) \<Rightarrow> 'b" where
"to_l' (Inl x) = Xrep x"
| "to_l' (Inr (Inl (y, z))) = Yrep y" (* this one is bad. *)
| "to_l' (Inr (Inr (a, z))) =
    Zrep z a"
*)

(*
fun to_l' :: "('x + ('y * 'z) + ('a * 'z)) \<Rightarrow> 'b" where
"to_l' (Inl x) = Xrep x"
| "to_l' (Inr (Inl (y, z))) = Yrep y" (* this one is bad. *)
| "to_l' (Inr (Inr (a, z))) =
    Zrep z a"
*)

fun to_l' :: "('x + ('y * ('b \<Rightarrow> 'z)) + ('a * ('b \<Rightarrow> 'z))) \<Rightarrow> 'b" where
"to_l' (Inl x) = Xrep x"
| "to_l' (Inr (Inl (y, z))) = Yrep y" (* this one is bad. *)
| "to_l' (Inr (Inr (a, z))) =
    Zrep (z a)"

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

abbreviation rep' :: "('b, ('x + ('y * 'z) + ('a * 'z))) iso_parm" where
"rep' \<equiv> (to_r', to_l')"

(* idea: need to define x and y,
   as well as iso *)

end

sublocale View_Rep_Complete \<subseteq> View_Rep rep'
  apply(unfold_locales)
   apply(simp split:sum.splits) apply(safe)
    apply(cut_tac f = "(\<lambda>a. local.inj (a, l))" in "Zabs_inverse")
     apply(simp add:Z_def) apply(auto)
    apply(simp add: PrjInj1)

     apply(cut_tac b = "(\<lambda> f . l)" in Yabs_inverse)
      apply(simp add:Y_def) apply(auto)
     apply(rule_tac x = undefined in exI) apply(simp)

     apply(drule_tac InjPrj1) apply(simp)

    apply(cut_tac f = "(\<lambda>a. local.inj (a, l))" in Zabs_inverse)
     apply(simp add: Z_def) apply(auto)
    apply(simp add:PrjInj1)

   apply(cut_tac b = l in Xabs_inverse)
    apply(simp add:X_def) apply(auto)

(* old proof inserted here *)

   apply(simp split:sum.splits) apply(safe)
     apply(case_tac r) apply(clarsimp)
      apply(cut_tac x = a in Xrep_spec) apply(auto simp add:X_def)
      apply(frule_tac d' = undefined in InjPrj2) apply(auto)

     apply(case_tac b) apply(clarsimp)
      apply(cut_tac y = a in Yrep_spec) apply(auto simp add:Y_def)

  apply(cut_tac y = a in Yrep_spec) apply(auto simp add:Y_def)

       apply(cut_tac z = ba in Zrep_spec) apply(auto simp add:Z_def)
       apply(drule_tac x = "(\<lambda>a. local.inj (a, b))" in spec) apply(simp)



      apply(cut_tac z = ba in Zrep_spec) apply(auto simp add:Z_def)
  apply(frule_tac d = a in InjPrj1) apply(simp)


      apply(cut_tac z = ba in Zrep_spec) apply(auto simp add:Z_def)
     apply(simp add: InjInj)
     apply(cut_tac z = "ba" in Zrep_inverse) apply(simp)

  apply(case_tac r) apply(clarsimp)
      apply(cut_tac x = a in Xrep_spec) apply(auto simp add:X_def)
      apply(frule_tac d' = undefined in InjPrj2) apply(auto)

    apply(case_tac b) apply(simp) apply(clarsimp) apply(auto)

      apply(cut_tac y = a in Yrep_spec) apply(auto simp add:Y_def)
      apply(cut_tac z = ba in Zrep_spec) apply(simp add: Z_def)
      
apply(auto simp add:Z_def)

      apply(drule_tac x = "(\<lambda>a. local.inj (a, b))" in spec)
      apply(clarsimp)
      apply(frule_tac PrjInj2) apply(clarsimp)
      apply(frule_tac InjPrj1) apply(clarsimp)
  apply(frule_tac r = b in PrjInj1)
(*  *)

      apply(frule_tac r = l in PrjInj1) 
  apply(cut_tac f = 
" (\<lambda>a. local.inj (a, l))" in Zabs_inverse)
       apply(simp add:Z_def) apply(auto)

  apply(frule_tac InjPrj1) apply(clarsimp)

     apply(cut_tac b = l in Yabs_inverse) apply(simp add: Y_def)
      apply(auto)
     apply(frule_tac PrjInj2) apply(simp)

    apply(cut_tac f = "(\<lambda>a. local.inj (a, l))" in Zabs_inverse)
     apply(simp add:Z_def) apply(auto)
    apply(frule_tac r = l in PrjInj1) apply(simp)

   apply(cut_tac b = l in Xabs_inverse) apply(simp add: X_def)
    apply(auto)

  apply(simp split:sum.splits) apply(safe)
     apply(case_tac r) apply(clarsimp)
      apply(cut_tac x = a in Xrep_spec) apply(simp add: X_def)
      apply(auto)
      apply(frule_tac d' = undefined in InjPrj2) apply(simp)

     apply(case_tac b) apply(clarsimp)
      apply(simp split:sum.splits) 
       apply(cut_tac y = a in Yrep_spec) apply(simp add:Y_def)

     apply(clarsimp) apply(auto)
      apply(cut_tac z = ba in Zrep_spec) apply(simp add:Z_def)
      apply(auto)
      apply(frule_tac d' = x1a in InjPrj1) apply(simp)

      apply(cut_tac z = ba in Zrep_spec) apply(simp add:Z_def)
      apply(auto)
     apply(frule_tac d' = x1a in InjPrj1) apply(simp)
     apply(simp add:InjInj)
     apply(cut_tac z = "ba" in Zrep_inverse) apply(simp)

    apply(case_tac r) apply(clarsimp)
     apply(cut_tac x = a in Xrep_spec) apply(simp add:X_def) apply(auto)
     apply(frule_tac d' = undefined in InjPrj2)
     apply(simp)

    apply(case_tac b) apply(clarsimp) apply(auto split:sum.splits)
        apply(cut_tac y = a in Yrep_spec) apply(auto simp add:Y_def)
       apply(cut_tac y = a in Yrep_spec) apply(auto simp add:Y_def)
      apply(simp add: Yrep_inverse)

          apply(cut_tac y = a in Yrep_spec) apply(auto simp add:Y_def)


(* problem: reproducing the correct ba when b is Inr (Inl) *)
     apply(cut_tac y = a in Yrep_spec) apply(auto simp add:Y_def)
     apply(frule_tac PrjInj2) apply(clarsimp)
  apply(frule_tac r = "Yrep a" in PrjInj2) apply(clarsimp)
  

  apply(simp add:Zrep_inverse)
    

       apply(cut_tac b = l in Yabs_inverse) apply(simp add: Y_def)
      apply(auto)
     apply(frule_tac PrjInj2) apply(simp)

       apply(cut_tac b = l in Yabs_inverse) apply(simp add: Y_def)
      apply(auto)
     apply(frule_tac PrjInj2) apply(simp)


(* old proof follows *)

  apply(simp split:sum.splits) apply(safe)
  apply(case_tac r) apply(clarsimp)
      apply(cut_tac x = a in Xrep_spec) apply(simp add:X_def) apply(clarsimp)
      apply(drule_tac d' = undefined in InjPrj2) apply(simp)

  apply(clarsimp)
  apply(case_tac b) apply(simp)
      apply(clarsimp)
      apply(cut_tac y = a in Yrep_spec) apply(simp add:Y_def) apply(clarsimp)

     apply (cut_tac z = ba in Zrep_spec) apply(simp add: Z_def) apply(clarsimp) apply(auto)
      apply(drule_tac d = a in InjPrj1) apply(simp)
     apply(simp add: InjInj)
     apply(cut_tac z = ba in Zrep_inverse) apply(simp)

    apply(case_tac r) apply(clarsimp)
     apply(cut_tac x = a in Xrep_spec) apply(simp add: X_def) apply(clarsimp)
     apply(drule_tac d = a' and d' = undefined in InjPrj2) apply(simp)

  (* to_l' is throwing something away? when input is Inr (Inl) *)
    apply(clarsimp) apply(case_tac b) apply(clarsimp) apply(auto)
      apply(simp add: Yrep_inverse)
     apply(cut_tac y = a in Yrep_spec) apply(simp add: Y_def) apply(clarsimp)
  apply(frule_tac InjPrj1) apply(simp)
  
  apply(rotate_tac 1)

  apply(simp

   apply(case_tac "(Iso.to_r rep' l)") apply(clarsimp)
  
  apply(clarsimp)
  
  
  apply(simp split:prod.splits sum.splits)


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