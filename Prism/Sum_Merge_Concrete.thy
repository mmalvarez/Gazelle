theory Sum_Merge_Concrete imports Sum_Merge "../Reify" Prism
begin

(* idea: we are going to define a target for merging
   ints and bools, such that ?
*)

fun i2b_cast ::
  "int \<Rightarrow> bool option" where
"i2b_cast i = 
 (if i = 0 then Some False
  else if i = 1 then Some True
  else None)"

fun b2i_cast ::
  "bool \<Rightarrow> int option" where
"b2i_cast b =
  (if b then Some 1 else Some 0)"

fun s_cases1 :: "('a + 'b) \<Rightarrow> ('a + ('a + 'b))" where
"s_cases1 (Inl a) = Inl a"
| "s_cases1 x = Inr x"

fun s_cases2 :: "('a + 'b) \<Rightarrow> ('b + ('a + 'b))" where
"s_cases2 (Inr b) = Inl b"
| "s_cases2 x = Inr x"

(* this kind of encoding only works when one type is
   strictly more informative... *)
(*
typedef ib_target =
  "{ib :: (bool + int) .
    (\<forall> i . ib = Inr i \<longrightarrow>
      i2b_cast i = None)}"
*)
(*
interpretation ib_merge :
  Sum_Merge_Spec 
    "\<lparr> prism1 = \<lparr> cases = s_cases1 o Rep_ib_target
                , inj = Abs_ib_target o Inl \<rparr>
     , prism2 = \<lparr> cases = s_cases2 o Rep_ib_target
                , inj = 
                (\<lambda> i .  \<rparr>
*)
(*
typedef (overloaded) ('a, 'b) smc_target =
  "{ (ab :: ('a + 'b)) .
    (\<exists> (f :: 'b \<Rightarrow> 'a option) (f' :: 'a \<Rightarrow> 'b option) .
     (\<forall> b a . f b = Some a \<longrightarrow> f' a = Some b) \<and>
     (\<forall> a b . f' a = Some b \<longrightarrow> f b = Some a) \<and>
     (case ab of
        Inl a \<Rightarrow> True
        | Inr b \<Rightarrow> f b = None)) }"
  apply(rule_tac x = "(Inl undefined)" in exI)
  apply(clarsimp)
  apply(rule_tac x = "\<lambda> _ . None" in exI)
  apply(rule_tac x = "\<lambda> _ . None" in exI)
  apply(clarsimp)
  done
*)

(*
type_synonym ('a, 'b) cast_pair =
  "(('b \<Rightarrow> 'a option) * ('a \<Rightarrow> 'b option))"

fun cast_pair_valid :: "('a, 'b) cast_pair \<Rightarrow> bool" where
  "cast_pair_valid (cast1, cast2) =  
    ((\<forall> a b . cast1 b = Some a \<longrightarrow> cast2 a = Some b) \<and>
      (\<forall> b a . cast2 b = Some a \<longrightarrow> cast1 a = Some b))"

typedef ('a, 'b) smc_target' =
  "{ (ab :: ('a + 'b), cast1 :: ('b \<Rightarrow> 'a option), cast2 :: ('a \<Rightarrow> 'b option)) .
     (cast_pair_valid (cast1, cast2) \<and>
     (case ab of
        Inl a \<Rightarrow> True
        | Inr b \<Rightarrow> cast1 b = None)) }"
  apply(rule_tac x = "(Inl undefined,  \<lambda> _ . None, \<lambda> _ . None)" in exI)
  apply(clarsimp)
  done
*)
(*
typedef (overloaded) ('a, 'b)  smc_target =
  "{ (ab :: 'a + 'b) .
     (case ab of
        Inl a \<Rightarrow> True
        | Inr b \<Rightarrow> cast1 b = None) }"
  apply(rule_tac x = "(Inl undefined,  \<lambda> _ . None, \<lambda> _ . None)" in exI)
  apply(clarsimp)
  done
*)

(* use local typedefs? *)
locale Sum_Merge_Concrete =

fixes cast1 :: "'b \<Rightarrow> 'a option"
fixes cast2 :: "'a \<Rightarrow> 'b option"


assumes Cast12 :
  "cast1 b = Some a \<Longrightarrow> cast2 a = Some b' \<Longrightarrow> b = b'"
assumes Cast21 :
  "cast2 a = Some b \<Longrightarrow> cast1 b = Some a' \<Longrightarrow> a = a'"

begin


(* question: do we need to worry about overlaps? *)
(*
fun inj1' :: "('a \<Rightarrow> ('a + 'b + ('a * 'b)))" where
"inj1' a =
  (case cast2 a of
    None \<Rightarrow> Inl a
    | Some b \<Rightarrow> Inr (Inr (a, b)))"

fun inj2' :: "('b \<Rightarrow> ('a + 'b + ('a * 'b)))" where
"inj2' b = 
  (case cast1 b of
    None \<Rightarrow> Inr (Inl b)
    | Some a \<Rightarrow> Inr (Inr (a, b)))"

(* idea: just like for products, we have some
"badly behaved" elements that we won't be able to guarantee certain behaviors for *)
(*
fun cases1' :: "('a + 'b + ('a * 'b)) \<Rightarrow> ('a + ('a + 'b + ('a * 'b)))" where
"cases1' (Inl a) = 
  (case cast2 a of
     None \<Rightarrow> Inl a
     | _ \<Rightarrow> Inr (Inl a))"
| "cases1' (Inr (Inl b)) = Inr (Inr (Inl b))"
| "cases1' (Inr (Inr (a, b))) = 
    (if (cast1 b = Some a \<or> cast2 a = Some b) then
      Inl a
     else Inr (Inr (Inr (a, b))))"
*)
fun cases1' :: "('a + 'b + ('a * 'b)) \<Rightarrow> ('a + ('a + 'b + ('a * 'b)))" where
"cases1' (Inl a) = 
  (case cast2 a of
     None \<Rightarrow> Inl a
     | _ \<Rightarrow> Inr (Inl a))"
| "cases1' (Inr (Inl b)) = Inr (Inr (Inl b))"
| "cases1' (Inr (Inr (a, b))) =
  (if cast1 b = Some a then Inl a
   else Inr (Inr (Inr (a, b))))"

fun cases2' :: "('a + 'b + ('a * 'b)) \<Rightarrow> ('b + ('a + 'b + ('a * 'b)))" where
"cases2' (Inl a) = Inr (Inl a)"
| "cases2' (Inr (Inl b)) = 
  (case cast1 b of
      None \<Rightarrow> Inl b
      | _ \<Rightarrow> Inr (Inr (Inl b)))"
| "cases2' (Inr (Inr (a, b))) = 
    (if cast1 b = Some a then Inl b
      else Inr (Inr (Inr (a, b))))"

abbreviation pp1 :: "('a, ('a + 'b + ('a * 'b))) prism_parms"
  where
  "pp1 \<equiv> \<lparr> cases = cases1', inj = inj1' \<rparr>"

abbreviation pp2 :: "('b, ('a + 'b + ('a * 'b))) prism_parms"
  where
  "pp2 \<equiv> \<lparr> cases = cases2', inj = inj2' \<rparr>"

abbreviation smp :: "('a, 'b, ('a + 'b + ('a * 'b))) sum_merge_parms"
  where
"smp \<equiv> \<lparr> prism1 = pp1, prism2 = pp2 \<rparr>"
*)

(* true means right side is cast of left
   false means left side is cast of right *)

fun inj1' :: "('a \<Rightarrow> ('a + 'b + ('a * 'b * bool)))" where
"inj1' a =
  (case cast2 a of
    None \<Rightarrow> Inl a
    | Some b \<Rightarrow> Inr (Inr (a, b, True)))"

fun inj2' :: "('b \<Rightarrow> ('a + 'b + ('a * 'b * bool)))" where
"inj2' b = 
  (case cast1 b of
    None \<Rightarrow> Inr (Inl b)
    | Some a \<Rightarrow> Inr (Inr (a, b, False)))"

(* idea: just like for products, we have some
"badly behaved" elements that we won't be able to guarantee certain behaviors for *)

(*
fun cases1' :: "('a + 'b + ('a * 'b)) \<Rightarrow> ('a + ('a + 'b + ('a * 'b)))" where
"cases1' (Inl a) = 
  (case cast2 a of
     None \<Rightarrow> Inl a
     | _ \<Rightarrow> Inr (Inl a))"
| "cases1' (Inr (Inl b)) = Inr (Inr (Inl b))"
| "cases1' (Inr (Inr (a, b))) = 
    (if (cast1 b = Some a \<or> cast2 a = Some b) then
      Inl a
     else Inr (Inr (Inr (a, b))))"
*)
(*
fun cases1' :: "('a + 'b + ('a * 'b)) \<Rightarrow> ('a + ('a + 'b + ('a * 'b)))" where
"cases1' (Inl a) = 
  (case cast2 a of
     None \<Rightarrow> Inl a
     | _ \<Rightarrow> Inr (Inl a))"
| "cases1' (Inr (Inl b)) = Inr (Inr (Inl b))"
| "cases1' (Inr (Inr (a, b))) =
  (if cast2 a = Some b then Inl a
   else Inr (Inr (Inr (a, b))))"

fun cases2' :: "('a + 'b + ('a * 'b)) \<Rightarrow> ('b + ('a + 'b + ('a * 'b)))" where
"cases2' (Inl a) = Inr (Inl a)"
| "cases2' (Inr (Inl b)) = 
  (case cast1 b of
      None \<Rightarrow> Inl b
      | _ \<Rightarrow> Inr (Inr (Inl b)))"
| "cases2' (Inr (Inr (a, b))) = 
    (if cast1 b = Some a then Inl b
      else Inr (Inr (Inr (a, b))))"

*)


fun cases1' :: "('a + 'b + ('a * 'b * bool)) \<Rightarrow> ('a + ('a + 'b + ('a * 'b * bool)))" where
"cases1' (Inl a) = 
  (case cast2 a of
     None \<Rightarrow> Inl a
     | _ \<Rightarrow> Inr (Inl a))"
| "cases1' (Inr (Inl b)) = Inr (Inr (Inl b))"
| "cases1' (Inr (Inr (a, b, True))) =
  (if cast2 a = Some b then Inl a
   else Inr (Inr (Inr (a, b, True))))"
| "cases1' (Inr (Inr (a, b, False))) = Inr (Inr (Inr (a, b, False)))"

fun cases2' :: "('a + 'b + ('a * 'b * bool)) \<Rightarrow> ('b + ('a + 'b + ('a * 'b * bool)))" where
"cases2' (Inl a) = Inr (Inl a)"
| "cases2' (Inr (Inl b)) = 
  (case cast1 b of
      None \<Rightarrow> Inl b
      | _ \<Rightarrow> Inr (Inr (Inl b)))"
| "cases2' (Inr (Inr (a, b, True))) = Inr (Inr (Inr (a, b, True)))"
| "cases2' (Inr (Inr (a, b, False))) = 
    (if cast1 b = Some a then Inl b
      else Inr (Inr (Inr (a, b, False))))"

abbreviation pp1 :: "('a, ('a + 'b + ('a * 'b * bool))) prism_parms"
  where
  "pp1 \<equiv> \<lparr> prism_parms.cases = cases1', inj = inj1' \<rparr>"

abbreviation pp2 :: "('b, ('a + 'b + ('a * 'b * bool))) prism_parms"
  where
  "pp2 \<equiv> \<lparr> prism_parms.cases = cases2', inj = inj2' \<rparr>"

abbreviation vwb'' where
"vwb'' \<equiv> {x . 
            (\<forall> a . x = Inl a \<longrightarrow> cast2 a = None) \<and>
            (\<forall> b . x = Inr (Inl b) \<longrightarrow> cast1 b = None) \<and>
            (\<forall> a b c . x = Inr (Inr (a, b, c)) \<longrightarrow>
                   ((c \<and> cast2 a = Some b) \<or>
                    (\<not> c \<and> cast1 b = Some a)))}"

abbreviation smp :: "('a, 'b, ('a + 'b + ('a * 'b * bool))) sum_merge_parms"
  where
"smp \<equiv> \<lparr> prism1 = pp1, prism2 = pp2,
    vwb = vwb'' \<rparr>"

(* i feel like we have swept something under
the rug with our treatment of overlap... *)
(*
fun inj1' :: "('a \<Rightarrow> 'a + 'b)" where
"inj1' a = Inl a"

fun inj2' :: "('b \<Rightarrow> 'a + 'b)" where
"inj2' b = Inr b"

fun cases1' :: "('a + 'b) \<Rightarrow> ('a + ('a + 'b))" where
"cases1' (Inl a) = Inl a"
| "cases1' (Inr b) = 
  (case cast1 b of
    None \<Rightarrow> Inr (Inr b)
    | Some a \<Rightarrow> Inl a)"

fun cases2' :: "('a + 'b) \<Rightarrow> ('b + ('a + 'b))" where
"cases2' (Inl a) =
  (case cast2 a of
    None \<Rightarrow> Inr (Inl a)
    | Some b \<Rightarrow> Inl b)"
| "cases2' (Inr b) =
  Inl b"

abbreviation pp1 :: "('a, ('a  + 'b)) prism_parms"
  where
  "pp1 \<equiv> \<lparr> prism_parms.cases = cases1', inj = inj1' \<rparr>"

abbreviation pp2 :: "('b, ('a + 'b)) prism_parms"
  where
  "pp2 \<equiv> \<lparr> prism_parms.cases = cases2', inj = inj2' \<rparr>"

abbreviation smp :: "('a, 'b, ('a + 'b)) sum_merge_parms"
  where
"smp \<equiv> \<lparr> prism1 = pp1, prism2 = pp2,
  vwb = {x . True}  \<rparr>"
*)

(*
fun inj1' :: "('a \<Rightarrow> 't)" where
"inj1' a = tin1 a"

fun inj2' :: "('b \<Rightarrow> 't)" where
"inj2' b = tin2 b"

fun cases1' :: "'t \<Rightarrow> ('a + 't)" where
"cases1' t =
  (case tout t of
    Inl a \<Rightarrow> Inl a
    | Inr b \<Rightarrow> (case cast1 b of Some a \<Rightarrow> Inl a
                | _ \<Rightarrow> Inr (t)))"

fun cases2' :: "'t \<Rightarrow> ('b + ('t))" where
"cases2' (t) =
  (case tout t of
      Inl a \<Rightarrow> Inr t
      | Inr b \<Rightarrow> Inl b)"

abbreviation pp1 :: "('a, ('t)) prism_parms"
  where
  "pp1 \<equiv> \<lparr> prism_parms.cases = cases1', inj = inj1' \<rparr>"

abbreviation pp2 :: "('b, ('t)) prism_parms"
  where
  "pp2 \<equiv> \<lparr> prism_parms.cases = cases2', inj = inj2' \<rparr>"

abbreviation smp :: "('a, 'b, ('t)) sum_merge_parms"
  where
"smp \<equiv> \<lparr> prism1 = pp1, prism2 = pp2,
  vwb = {x . True}  \<rparr>"
*)
end

sublocale Sum_Merge_Concrete \<subseteq> Sum_Merge_Total_Spec "smp"


(*
  apply(unfold_locales)
         apply(clarsimp)
(* inj case *)
       apply(simp split:sum.splits option.splits)
        apply(case_tac c) apply(simp)
        apply(clarsimp)
  apply(case_tac "cast1 b") apply(simp) apply(simp)
*)
(* old proof*)
  apply(unfold_locales)
(* case after inj *)
         apply(clarsimp)
(* inj after case *)

         apply(simp split:sum.splits option.splits)

         apply(clarsimp)
          apply(simp split:sum.splits option.splits)
         apply(simp split:sum.splits option.splits)
apply(simp split:sum.splits option.splits)

        apply(case_tac c) apply(simp)
apply(simp split:sum.splits option.splits)
        apply(clarsimp)
        apply(case_tac b) apply(simp) apply(simp)
        apply(case_tac ba) apply(clarsimp)
        apply(case_tac c) apply(clarsimp) apply(clarsimp)
apply(case_tac c) apply(clarsimp) 
apply(simp split:sum.splits option.splits)

apply(case_tac c) apply(clarsimp) 
       apply(simp split:sum.splits option.splits)
        apply(case_tac b) apply(simp) apply(simp)
       apply(case_tac bb) apply(simp) 
       apply(case_tac ca) apply(simp) apply(simp)

  apply(clarsimp)  apply(simp split:sum.splits option.splits)
        apply(case_tac c) apply(simp)
apply(simp split:sum.splits option.splits)
        apply(clarsimp)
     apply(case_tac b) apply(simp)
      
  apply(simp split:sum.splits option.splits)
  apply(simp)
        apply(case_tac ba) apply(clarsimp)
     apply(case_tac c) apply(clarsimp) apply(clarsimp)

apply(case_tac c) apply(clarsimp) 
apply(simp split:sum.splits option.splits)

        apply(clarsimp) 
    apply(case_tac b) apply(clarsimp)
     apply(simp split:sum.splits option.splits)
    apply(clarsimp)
        apply(case_tac ba) apply(clarsimp) apply(clarsimp)

   apply(clarsimp)
     apply(case_tac c) apply(clarsimp) apply(clarsimp)
   apply(case_tac b) apply(clarsimp) apply(clarsimp)
   apply(case_tac ba) apply(clarsimp) apply(clarsimp)

   apply(clarsimp)
     apply(case_tac c) apply(clarsimp) apply(clarsimp)
   apply(case_tac b) apply(clarsimp) apply(clarsimp)
  apply(case_tac ba) apply(clarsimp) apply(clarsimp)

  done
  
end