theory Explore imports Main
begin

(* extremely general syntax tree type for use with Elle *)
datatype ('b, 'r, 'g) gensym' = 
  GBase "'b"
  | GRec "'r" "('g * ('b, 'r, 'g) gensym') list"

type_synonym ('b, 'r, 'g) gensym = "('g * ('b, 'r, 'g) gensym')"

type_synonym ('inst, 'lix, 'b, 'r, 'g) gazelle' =
  "(('inst * 'lix) + 'b, 'r, 'g) gensym'"



  (* TODO these names are very confusing.
     for extl and extr we need to decide about tree weighting *)
  type_synonym ('t, 'left) exl = "('left + 't)"
  type_synonym ('t, 'right) exr = "('t + 'right)"

  type_synonym ('t, 'left, 'right) pkg = "('left + 't + 'right)"

  value "Inr (Inl True) :: (bool, unit, (int, unit, unit) pkg) pkg"
  value "Inr (Inl True) :: (((int, unit, unit) pkg, bool ) exl, unit) exl"

value "Inr (Inr (Inr (Inl 1 ))) :: (bool, unit, (int, unit, unit) pkg) pkg"
  value "Inr (Inr (Inr (Inl 1))) :: (((int, unit, unit) pkg, bool ) exl, unit) exl"

definition mkExl :: "'t \<Rightarrow> ('t, 'left) exl" where
"mkExl t = Inr t"

definition mkExr :: "'t \<Rightarrow> ('t, 'right) exr" where
"mkExr t = Inl t"

definition mkPkg :: "'t \<Rightarrow> ('t, 'left, 'right) pkg" where
"mkPkg t = Inr (Inl t)"

  
  (* need to be able to translate properties about something of type t
     to properties about something of type (t, _) exl and (t, _) exr
*)

(* also need to be able to translate properties about something of type t
   to properties about something of type (_, t, _) exr
*)

fun lift_exl :: "('t \<Rightarrow> 'o) \<Rightarrow> 'o \<Rightarrow> ('t, 'left) exl \<Rightarrow> 'o" where
  "lift_exl f _ (Inr t) = f t"
  | "lift_exl _ d _ = d"

fun lift_exl_part :: "('t \<Rightarrow> 'o) \<Rightarrow> ('t, 'left) exl \<Rightarrow> 'o" where
  "lift_exl_part f (Inr t) = f t"
  
fun lift_exr :: "('t \<Rightarrow> 'o) \<Rightarrow> 'o \<Rightarrow> ('t, 'right) exr \<Rightarrow> 'o" where
  "lift_exr f _ (Inl t) = f t"
  | "lift_exr _ d _ = d"

fun lift_exr_part :: "('t \<Rightarrow> 'o) \<Rightarrow> ('t, 'right) exr \<Rightarrow> 'o" where
  "lift_exr_part f (Inl t) = f t"

fun lift_pkg :: "('t \<Rightarrow> 'o) \<Rightarrow> 'o \<Rightarrow> ('t, 'left, 'right) pkg \<Rightarrow> 'o" where
  "lift_pkg f _ (Inr (Inl t)) = f t"
  | "lift_pkg _ d _ = d"

fun lift_pkg_part :: "('t \<Rightarrow> 'o) \<Rightarrow> ('t, 'left, 'right) pkg \<Rightarrow> 'o" where
  "lift_pkg_part f (Inr (Inl t)) = f t"
  
definition lift_exl_predT :: "('t \<Rightarrow> bool) \<Rightarrow> ('t, 'left) exl \<Rightarrow> bool" where
  "lift_exl_predT p et = lift_exl p True et"

definition lift_exl_predF :: "('t \<Rightarrow> bool) \<Rightarrow> ('t, 'left) exl \<Rightarrow> bool" where
  "lift_exl_predF p et = lift_exl p False et"

definition lift_exl_predU :: "('t \<Rightarrow> bool) \<Rightarrow> ('t, 'left) exl \<Rightarrow> bool" where
  "lift_exl_predU p et = lift_exl_part p et"

definition lift_exr_predT :: "('t \<Rightarrow> bool) \<Rightarrow> ('t, 'left) exr \<Rightarrow> bool" where
  "lift_exr_predT p et = lift_exr p True et"

definition lift_exr_predF :: "('t \<Rightarrow> bool) \<Rightarrow> ('t, 'left) exr \<Rightarrow> bool" where
  "lift_exr_predF p et = lift_exr p False et"
  
definition lift_exr_predU :: "('t \<Rightarrow> bool) \<Rightarrow> ('t, 'left) exr \<Rightarrow> bool" where
  "lift_exr_predU p et = lift_exr_part p et"

definition lift_pkg_predT :: "('t \<Rightarrow> bool) \<Rightarrow> ('t, 'left, 'right) pkg \<Rightarrow> bool" where
  "lift_pkg_predT p et = lift_pkg p True et"

definition lift_pkg_predF :: "('t \<Rightarrow> bool) \<Rightarrow> ('t, 'left, 'right) pkg \<Rightarrow> bool" where
  "lift_pkg_predF p et = lift_pkg p False et"
  
definition lift_pkg_predU :: "('t \<Rightarrow> bool) \<Rightarrow> ('t, 'left, 'right) pkg  \<Rightarrow> bool" where
  "lift_pkg_predU p et = lift_pkg_part p et"

  lemma udt : "((undefined :: bool) \<or> True) = True"
  proof(simp)
  qed

  lemma weird : "x = undefined :: bool \<Longrightarrow> y = undefined :: bool \<Longrightarrow> x = y"
  apply(simp)
  done

  

  record ('a, 'b) mypair =
    left :: 'a
    right :: 'b

    definition myinl :: "'a \<Rightarrow> ('a, 'b) mypair" where
       "myinl x = \<lparr> left = x, right = undefined \<rparr>"

    definition myinr :: "'b \<Rightarrow> ('a, 'b) mypair" where
       "myinr x = \<lparr> left = undefined, right = x \<rparr>"

       lemma characterize :
        "(x = myinl 1 \<and> x = myinr True) \<Longrightarrow>
         (x = \<lparr> left = 1, right = True\<rparr>)"
         apply(auto simp add:myinr_def myinl_def)
         done

         datatype threeVal =
         tTrue | tFalse | tUndef

     fun threeValD :: "threeVal \<Rightarrow> bool" where
     "threeValD tTrue = True" 
     | "threeValD tFalse = False"

     datatype pTag =
      pLeft | pRight | pBoth | pNeither

type_synonym ('a, 'b) mysum = "pTag * 'a * 'b"

definition pInl :: "'a \<Rightarrow> ('a, 'b) mysum" where
"pInl a = (pLeft, a, undefined)"

definition pInr :: "'b \<Rightarrow> ('a, 'b) mysum" where
"pInr b = (pRight, undefined, b)"



(* options for representing multiple inheritance:

1. list of "aspects", each of which is a sum type

2. "object" type which is a "special union" over everything

*)

(* approach 1. *)

record mammal =
  breathe :: "nat"

  definition mammal_correct :: "mammal \<Rightarrow> bool" where
    "mammal_correct m = (breathe m > 3 )"

    record flyer =
      hasWings :: bool

      definition flyer_correct :: "flyer \<Rightarrow> bool" where
      "flyer_correct f = hasWings f"
      
      type_synonym ('t1, 't2, 't3) batMix =
        "(mammal, (flyer, 't1, 't2) pkg, 't3) pkg"

        fun batMix_getMammal :: "('t1, 't2, 't3) batMix \<Rightarrow> mammal option" where
          "batMix_getMammal (Inr (Inl m)) = Some m"
          | "batMix_getMammal _ = None"

          fun batMix_getFlyer :: "('t1, 't2, 't3) batMix \<Rightarrow> flyer option" where
            "batMix_getFlyer (Inl (Inr (Inl f))) = Some f"
            | "batMix_getFlyer _ = None"
          
        type_synonym ('t1, 't2, 't3) batDesc =
        "('t1, 't2, 't3) batMix list"

        definition mammal1 :: mammal where
        "mammal1 = \<lparr> breathe = 4 \<rparr>"

        definition mammal2 :: mammal where
        "mammal2 = \<lparr> breathe =  0 \<rparr>"

        definition flyer1 :: flyer where
        "flyer1 = \<lparr> hasWings = True \<rparr>"

        definition flyer2 :: flyer where
        "flyer2 = \<lparr> hasWings = False \<rparr>"

        value "Inr (Inl mammal1) :: (unit, unit, unit) batMix"
        
        definition bat1 (*:: "(unit, unit, unit) batDesc"*) where "bat1 = [(Inr (Inl mammal1)), (Inl (Inr (Inl flyer1)))]"
        
        value "List.filter (lift_pkg_predF mammal_correct) (bat1 :: (unit, unit, unit) batDesc)"
        value "List.filter (lift_exr_predF (lift_pkg_predF flyer_correct)) (bat1 :: (unit, unit, unit) batDesc)"

        record magical =
          castSpell :: "nat set"

          definition magical_correct :: "magical \<Rightarrow> bool" where
            "magical_correct m = (castSpell m \<noteq> {})"

            definition magical1 where "magical1 = \<lparr> castSpell = {42} \<rparr>"

            definition magicBat where
              "magicBat = (bat1 @ [(Inr (Inr (Inr (Inl magical1)))) :: (unit, unit, (magical, unit, unit) pkg) batMix])"

              definition magicBat' where
              "magicBat' = bat1 @ [(Inr (Inr (Inr (Inl magical1))))]"
              
              value "magicBat :: (unit, unit, (magical, unit, unit) pkg) batDesc"


              

              (* we have to use nbe here, code generator seems broken lol *)
              value [nbe] "magicBat' :: (unit, unit, (magical, unit, unit) pkg) batDesc"

              
              value "List.filter (lift_exl_predF (lift_exl_predF (lift_pkg_predF magical_correct))) (magicBat :: (unit, unit, (magical, unit, unit) pkg) batDesc)"
            
        (* idea: a correct bat needs to meet all the following:
            - exactly 1 flyer aspect
              - flyer aspect is valid

            - exactly 1 mammal aspect
              - mammal aspect is valid

            - how to enforce these?
              - filter by idMammal \<and> mammalValid, length must be 1
              - filter by idFlyer \<and> flyerValid, length must be 1              
        *)
(*
  (* another test: multiple inheritance with records? *)
  record 'l extr =
    lx :: 'l

    record boring =
      xb :: unit

      record boring2 =
        xb2 :: unit
      
    record 'l mammal = "'l extr"  +
      breathe :: "nat \<Rightarrow> nat"
      
    record 'l flyer = "'l extr" +
      fly :: "nat \<Rightarrow> nat"
      
      record 'l bat1 = "'l mammal" +
        fly :: "nat \<Rightarrow> nat"

        record 'l bat2 = "'l flyer" +
          breathe :: "nat \<Rightarrow> nat"
*)
      
(* want an explicit data type for 3-valued logic? could make it easier to compute on things. *)
  
(* characterize the results of lifting *)        


  type_synonym ('left, 't, 'right) extl = "(('left + 't) + 'right)"
  type_synonym ('left, 't, 'right) extr = "('left + ('t + 'right))"

  type_synonym ('left, 'right) A = "('left, bool, 'right) extr"
  type_synonym ('left, 'right) B = "('left, int, 'right) extl"

  type_synonym ('left, 'mid, 'right) Alpha = "(('left, 'mid) A, 'right) exr"
  type_synonym ('left, 'mid, 'right) Beta = "('left, ('mid, 'right) B) exl"

  value "Inl (Inr (Inl True)) :: (unit, unit, ((unit, unit) B)) Alpha"
  value "Inl (Inr (Inl True)) :: (((unit, unit) A), unit, unit) Beta"

(* ok, let's extend this construction! *)

datatype tern =
  Greater
  | EqTo
  | Less

type_synonym ('left, 'right) D = "('left, tern, 'right) extl"

type_synonym ('left, 'mid, 'right) A2 =
  "('left, ('mid, 'right) D) A"

type_synonym ('left, 'm1, 'm2, 'right) Alpha2 =
  "(('left, 'm1, 'm2) A2, 'right) exr"

  value "Inl (Inr (Inr (Inl (Inr EqTo)))) :: (unit, unit, unit, (unit, unit) B) Alpha2"
    value "Inl (Inr (Inr (Inl (Inr EqTo)))) :: ((unit, unit, unit) A2, unit, unit) Beta"

(* more minimal a la carte experiment *)

datatype ('left, 'right) xthing = Xthing "'left + 'right"

type_synonym ('left, 'right) intthingl = "(('left + int), 'right) xthing"
type_synonym ('left, 'right) intthingr = "(('left), (int + 'right)) xthing"

type_synonym ('left, 'right) boolthingl = "(('left + bool), 'right) xthing"
type_synonym ('left, 'right) boolthingr = "(('left), (bool + 'right)) xthing"

(* now, start building some ibthing's *)

(* experiment in "a la carte" construction of types *)

datatype ('left, 't, 'right) thing = Thing "'left + 't + 'right"

type_synonym ('left, 'right) intthing = "('left, int, 'right) thing"

type_synonym ('left, 'right) boolthing = "('left, bool, 'right) thing"

type_synonym ibthing1 = "(bool, unit) intthing"

type_synonym ibthing2 = "(unit, int) boolthing"

type_synonym ibthing1' = "(unit, (int, unit) intthing) boolthing"

type_synonym ibthing2' = "((int, unit) boolthing, unit) intthing"

(* question: can we get the same piece of data to check
at both types? *)
value "Thing (Inl True) :: ibthing1"
value "Thing (Inr (Inl True)) :: ibthing2"

value "Thing (Inr (Inl True)) :: ibthing1'"
(*value "Thing (Inr (Inl True)) :: ibthing2'"*)

term "True"

record blah =
  n :: nat
record ('left, 't, 'right) rthing =
  l :: 'left
  t :: 't
  r :: 'right

  (*
  term "\<lparr> l = THE x . True,
          t = 1,
          r = THE x . True, ... = foo \<rparr> :: ('a, nat, 'b) rthing"
    *)      
  
datatype ('left, 'right) thingy = Thingy "'left + 'right"

(* record tutorial stuff *)

record point = 
  Xcoord :: int
  Ycoord :: int

  record cpoint = point + 
color :: nat

(*type_synonym ('left, 'right) intthingy = "('left, int, 'right) thing" *)

(*

what about coercions?
- we can use this to force a certain associativity
- we can't do this in general, type parameters already force a certain notion of subtyping
*)


fun reassoc :: "(('a + 'b) + 'c) \<Rightarrow> ('a + 'b + 'c)" where
"reassoc (Inl (Inl x)) = Inl x"
| "reassoc (Inl (Inr x)) = Inr (Inl x)"
| "reassoc (Inr x) = Inr (Inr x)"

fun reassoc2 :: "('a + 'b + 'c) \<Rightarrow> (('a + 'b) + 'c)" where
"reassoc2 ((Inl x)) = (Inl (Inl x))"
| "reassoc2 (Inr (Inl x)) = Inl (Inr x)"
| "reassoc2 (Inr (Inr x)) = (Inr x)"

definition reassoc_n :: "((nat + nat) + nat) \<Rightarrow> (nat + nat + nat)" where
"reassoc_n = reassoc"

definition reassoc2_n :: "(nat + nat + nat) \<Rightarrow> ((nat + nat) + nat)" where
"reassoc2_n = reassoc2"

definition reassoc_blurb :: "((nat + bool) + unit) \<Rightarrow> (nat + bool + unit)" where
"reassoc_blurb = reassoc"

datatype loob =
lfalse | ltrue

fun doloob :: "bool \<Rightarrow> loob" where
"doloob False = lfalse"
| "doloob True = ltrue"

datatype 'a wrap =
wrap 'a


fun reassoc_blurb_wrap :: "((nat + bool) + unit) wrap \<Rightarrow> (nat + bool + unit)" where
"reassoc_blurb_wrap (wrap x) = (reassoc x)"

declare [[coercion_enabled]]

declare [[coercion doloob]]




declare [[coercion reassoc_blurb_wrap]]

term "(wrap (Inl (Inl (3)) :: ((nat + bool) + unit)) :: (nat + bool + unit))"
print_coercions
declare [[coercion reassoc_n]]
declare [[coercion reassoc2_n]]

term "(Inl (Inl (2 :: nat))) :: (nat + nat) + nat"

(* attempting to use gensyn *)

(* idea:
- define a type of integer nodes
  - valid means even
- define a type of bool nodes
  - valid means true

then:

- show that we can create a mixed version
- show that we can do the subtyping trick

*)

type_synonym ('a, 'b) ipkg = "(int, 'a, 'b) pkg"
type_synonym ('a, 'b) bpkg = "(bool, 'a, 'b) pkg"

type_synonym ('a, 'b) gs1 = "(('a, 'b) ipkg, unit, unit) gensym"
type_synonym ('a, 'b) gs2 = "(('a, 'b) bpkg, unit, unit) gensym"

(* idea: also need type synonyms for "extensions" of ipkg/bpkg
i.e. to deal with the fact that bool is on the left
and int is on the right
*)

(*

another question. how do we 

*)

term "((), GRec () []) :: ('a, 'b) gs2"

end