theory Compose
  imports "../Mergeable/Mergeable" "../Mergeable/Pord"
begin

(* idea. for composition we need
- an ordered domain (for the output semantics)
- two input types
- semantics on the input types
- inject and project

*)

(* NOTE: while we don't require the Mergeable instance here
to have a least element, it very likely will need one to
make the injections/projections work. Likewise, the "source" types
for the Views will need to be ordered *)

(* TODO: do we need ordering on domains? or can we get away with just
   ordering on range? *)

locale View' =
  fixes ts :: "'a itself" 
  fixes tb :: "'b itself" 
(*  fixes pleqa :: "'a \<Rightarrow> 'a \<Rightarrow> bool" *)
  fixes pleqb :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
  fixes bsupb :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
  fixes inj :: "'a \<Rightarrow> 'b"
  fixes prj :: "'b \<Rightarrow> 'a"

locale View = View' +
  OMB : Mergeable pleqb bsupb

locale View_Spec = View +
  OBS : Mergeable_Spec pleqb bsupb +
  assumes PrjInj : "prj (inj a) = a"
  assumes InjPrj : "pleqb (inj (prj b)) b"

locale Comp' =
  fixes tsl :: "'a itself" 
  fixes tsr :: "'b itself"
  fixes tb  :: "'c itself" 

locale Comp = Comp' +
  MC : Mergeable pleqb bsupb +
  VL : View tsl tb pleqb bsupb injl prjl +
  VR : View tsr tb pleqb bsupb injr prjr
  for pleqb bsupb injl prjl injr prjr
begin
definition liftl1 :: "('a \<Rightarrow> 'a) \<Rightarrow> ('d \<Rightarrow> 'd)" where
"liftl1 f =
  (\<lambda> b . injl (f (prjl b)))"

definition liftr1 :: "('b \<Rightarrow> 'b) \<Rightarrow> ('d \<Rightarrow> 'd)" where
"liftr1 f =
  (\<lambda> b . injr (f (prjr b)))"

definition liftlp1 :: "('a \<Rightarrow> bool) \<Rightarrow> ('d \<Rightarrow> bool)" where
"liftlp1 P =
  (\<lambda> b . P (prjl b))"

(* TODO: contravariant version? *)
definition liftlp2 :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('d \<Rightarrow> 'd \<Rightarrow> bool)" where
"liftlp2 P =
  (\<lambda> b b' . P (prjl b) (prjl b'))"

definition liftrp1 :: "('b \<Rightarrow> bool) \<Rightarrow> ('d \<Rightarrow> bool)" where
"liftrp1 P =
  (\<lambda> b . P (prjr b))"

(* TODO: contravariant version? *)
definition liftrp2 :: "('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('d \<Rightarrow> 'd \<Rightarrow> bool)" where
"liftrp2 P =
  (\<lambda> b b' . P (prjr b) (prjr b'))"
end

(* TODO: need more? *)
locale Comp_Spec = Comp +
  MCS : Mergeable_Spec pleqb bsupb +
  V1S : View_Spec tsl tb pleqb bsupb injl prjl +
  V2S : View_Spec tsr tb pleqb bsupb injr prjr
  
locale SemComp = Comp +
  fixes seml :: "'a \<Rightarrow> 'a"
  fixes semr :: "'b \<Rightarrow> 'b"

begin

(* lifted semantics *)
definition seml_l :: "'c \<Rightarrow> 'c" where
"seml_l =
  liftl1 seml"

declare seml_l_def [simp add]

definition semr_l :: "'c \<Rightarrow> 'c" where
"semr_l =
  liftr1 semr"

declare semr_l_def [simp add]

(* parallel composition *)
definition pcomp :: "'c \<Rightarrow> 'c" where
"pcomp b =
  bsupb (bsupb (seml_l b) (semr_l b)) b"

(* flipped version, equal to original if the
semantics are "well-behaved" (i.e. we have a Spec instance) *)
definition pcomp' :: "'c \<Rightarrow> 'c" where
"pcomp' b =
  bsupb (bsupb (semr_l b) (seml_l b)) b"

(* "real" parallel semantics, which may contain more information *)
definition pcomp_real :: "'c \<Rightarrow> 'c" where
"pcomp_real b =
  bsupb (seml_l b) (bsupb (semr_l b) b)"

definition pcomp_real' :: "'c \<Rightarrow> 'c" where
"pcomp_real' b =
  bsupb (semr_l b) (bsupb (seml_l b) b)"

(* serial composition *)
(* problem - feels like this may not work unless semantics are idempotent
   or monotone, or have some stronger property *)
(*
definition scomp :: "'c \<Rightarrow> 'c" where
"scomp b =
  bsupb (bsupb (seml_l (pcomp b)) (semr_l (pcomp b))) b"

(* "real" serial semantics *)
definition scomp_real :: "'c \<Rightarrow> 'c" where
"scomp_real b =
  bsupb (seml_l (bsupb (semr_l b) b)) b"

definition scomp_real' :: "'c \<Rightarrow> 'c" where
"scomp_real' b =
  bsupb (semr_l (bsupb (seml_l b) b)) b"
*)

(* TODO: there may be an intermediate version
   in between "real" and "scomp" *)

end

print_locale SemComp

locale SemComp_Spec = SemComp +
  assumes lool : True
begin
print_context
end
(*
  assumes pres_lub :
    "\<And> a b . has_ub (inj1 a) (inj2 b) \<Longrightarrow>
             OMB.has_lub (inj1 (sem1 a)) (inj1 (sem1 b))"
  *)

end