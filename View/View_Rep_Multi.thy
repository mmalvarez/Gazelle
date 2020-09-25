theory View_Rep_Multi imports View "../Isos/Iso"

begin

(* idea: our a is iso to
   ('x * ('a + 'y) ) *)

type_synonym ('l, 'r) iso_parm = "('l \<Rightarrow> 'r) * ('r \<Rightarrow> 'l)"

locale View_Rep' =
  fixes iso_big :: "('a, 'z + ('x * ('y + 'bu))) iso_parm"
  fixes iso_small :: "('b, ('x * 'bu)) iso_parm"

locale View_Rep =
  View_Rep' +
  Ib : Iso_Spec "iso_big :: ('a, 'z + ('x * ('y + 'bu))) iso_parm" +
  Is : Iso_Spec "iso_small :: ('b, ('x * 'bu)) iso_parm"

begin
print_context
fun prj' :: "'a \<Rightarrow> ('b + 'a)" where
"prj' a =
  (case Ib.to_r a of
    Inl z \<Rightarrow> Inr a
    | Inr (x, Inl y) \<Rightarrow> Inr a
    | Inr (x, Inr bu) \<Rightarrow> Inl (Is.to_l (x, bu)))"

fun inj' :: "'b * 'a \<Rightarrow> 'a" where
"inj' (b, a) =
  (case Is.to_r b of
    (x, bu) \<Rightarrow> Ib.to_l (Inr (x, Inr bu)))"

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
      apply(auto)
  apply(auto simp add: Is.Hisol Is.Hisor Ib.Hisol Ib.Hisor)
      apply(cut_tac l = r in Ib.Hisol) apply(simp)

      apply(simp split:sum.splits prod.splits)
  
      apply(simp split:sum.splits prod.splits)
  apply(auto simp add: Is.Hisol Is.Hisor Ib.Hisol Ib.Hisor)
      apply(cut_tac l = d in Is.Hisol) apply(simp)
  apply(simp split:sum.splits prod.splits)
  apply(auto simp add: Is.Hisol Is.Hisor Ib.Hisol Ib.Hisor)
  done

(* completeness *)
locale View_Rep_Complete' = View_Spec

begin

(* OK. so, we have x, y, and bu. have representing sets (need to define)
   and we know the laws.
   We need to demonstrate all the isos. *)

(* need to separately specify our input parameters so that we can get a valid iso *)

(* z = garbage, not injectable *)
definition Z :: "'b set" where
  "Z = { (b :: 'b) . \<exists> a' b' . prj (inj (a', b)) = Inr b' }"

(* x = overlap
   should this be an ('a \<Rightarrow> 'b) \<Rightarrow> 'b *)
definition X :: "(('a \<Rightarrow> 'b) \<Rightarrow> 'b) set" where
  "X = {f :: (('a \<Rightarrow> 'b) \<Rightarrow> 'b) . 
        \<forall> fi b . fi = (\<lambda> a . inj (a, b)) \<longrightarrow>
        f fi = b }"

(* y = thing that's not an 'b
   should this be a plain b or a function?  *)
definition Y :: "('a \<Rightarrow> 'b) set" where
  "Y = { (f :: ('a \<Rightarrow> 'b)) .
          (\<exists> b . f = (\<lambda> a . inj (a, b)) \<and>
          (prj (b) = Inr b)) }"


(* bu is the thing that's an a (the rest of it) *)
definition BU :: "('a \<Rightarrow> 'b) set" where
  "BU = {f :: ('a \<Rightarrow> 'b) .
          (\<exists> (b :: 'b) . f = (\<lambda> a . inj (a, b)) \<and>
          (\<exists> (a :: 'a) . prj b = Inl a)) }"
end

locale View_Rep_Complete = View_Rep_Complete' +

(*'a \<Rightarrow> 'b or 'b \<Rightarrow> 'a? *)
  fixes Zrep :: "'z \<Rightarrow> 'b"
  fixes Zabs :: "'b \<Rightarrow> 'z"
  fixes Yrep :: "'y \<Rightarrow> ('a \<Rightarrow> 'b)"
  fixes Yabs :: "('a \<Rightarrow> 'b) \<Rightarrow> 'y"
  fixes Burep :: "'bu \<Rightarrow> ('a \<Rightarrow> 'b)"
  fixes Buabs :: "('a \<Rightarrow> 'b) \<Rightarrow> 'bu"
  fixes Xrep :: "'x \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> 'b)"
  fixes Xabs :: "(('a \<Rightarrow> 'b) \<Rightarrow> 'b) \<Rightarrow> 'x"

assumes Zrep_spec : "\<And> z . Zrep z \<in> Z"
  assumes Yrep_spec : "\<And> y . Yrep y \<in> Y"
  assumes Xrep_spec : "\<And> x . Xrep x \<in> X"
  assumes Burep_spec : "\<And> bu . Burep bu \<in> BU"


assumes Xrep_inverse : "\<And> x . Xabs (Xrep x) = x"
assumes Yrep_inverse : "\<And> y . Yabs (Yrep y) = y"
assumes Zrep_inverse : "\<And> z . Zabs (Zrep z) = z"
assumes Burep_inverse : "\<And> bu . Buabs (Burep bu) = bu"


assumes Xabs_inverse : "\<And> x . x \<in> X \<Longrightarrow> Xrep (Xabs x) = x"
assumes Yabs_inverse : "\<And> y . y \<in> Y \<Longrightarrow> Yrep (Yabs x) = x"
assumes Zabs_inverse : "\<And> z . z \<in> Z \<Longrightarrow> Zrep (Zabs z) = z"
assumes Buabs_inverse : "\<And> bu . bu \<in> BU \<Longrightarrow> Burep (Buabs bu) = bu"

begin

print_context

fun to_r_s :: "'a \<Rightarrow> ('x * 'bu)" where
"to_r_s a =
    (Xabs (\<lambda> fi . fi a), Buabs (\<lambda> a . inj (a, undefined)))"

fun to_l_s :: "('x * 'bu) \<Rightarrow> 'a" where
"to_l_s (x, bu) = Xrep x (Burep bu)"

(*
fun to_r' :: "'b \<Rightarrow> ('x + ('y * 'z) + ('a * 'z))" where
"to_r' b =
  (case prj b of
      Inr _ \<Rightarrow> Inl (Xabs b)
    | Inl a \<Rightarrow> Inr (Inr (a, Zabs (\<lambda> a . inj (a, b)))))"
*)

fun to_r' :: "'b \<Rightarrow> ('x + ('y * 'z) + ('a * 'z))" where
"to_r' b =
  (case prj b of
      Inr _ \<Rightarrow> (case prj (inj (undefined, b)) of
                      Inr _ \<Rightarrow> Inl (Xabs b)
                      | Inl _ \<Rightarrow> Inr (Inl (Yabs b, Zabs (\<lambda> a . inj (a, b)))))
    | Inl a \<Rightarrow> Inr (Inr (a, Zabs (\<lambda> a . inj (a, b)))))"


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


fun to_l' :: "('x + ('y * 'z) + ('a * 'z)) \<Rightarrow> 'b" where
"to_l' (Inl x) = Xrep x"
| "to_l' (Inr (Inl (y, z))) = Yrep y" (* this one is bad. *)
| "to_l' (Inr (Inr (a, z))) =
    Zrep z a"

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

     apply(cut_tac b = l in Yabs_inverse)
      apply(simp add:Y_def) apply(auto)
     apply(rule_tac x = undefined in exI) apply(simp)

     apply(drule_tac InjPrj1) apply(simp)

    apply(cut_tac f = "(\<lambda>a. local.inj (a, l))" in Zabs_inverse)
     apply(simp add: Z_def) apply(auto)
    apply(simp add:PrjInj1)

   apply(cut_tac b = l in Xabs_inverse)
    apply(simp add:X_def) apply(auto)


 

   apply(simp split:sum.splits) apply(safe)
     apply(case_tac r) apply(clarsimp)
      apply(cut_tac x = a in Xrep_spec) apply(auto simp add:X_def)
      apply(frule_tac d' = undefined in InjPrj2) apply(auto)

     apply(case_tac b) apply(clarsimp)
      apply(cut_tac y = a in Yrep_spec) apply(auto simp add:Y_def)

      apply(cut_tac z = ba in Zrep_spec) apply(auto simp add:Z_def)
      apply(frule_tac d = a in InjPrj1) apply(auto)

     apply(cut_tac z = ba in Zrep_spec) apply(auto simp add:Z_def)
     apply(simp add:InjInj) apply(cut_tac z = "ba"
in Zrep_inverse) apply(auto)

  apply(case_tac r) apply(clarsimp)
      apply(cut_tac x = a in Xrep_spec) apply(auto simp add:X_def)
      apply(frule_tac d' = undefined in InjPrj2) apply(auto)

    apply(case_tac b) apply(simp) apply(clarsimp)
      apply(simp add: Yrep_inverse)

      apply(cut_tac y = a in Yrep_spec) apply(auto simp add:Y_def)


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