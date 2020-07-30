theory LiftUtilsOverload
  imports "LiftUtils" "LiftInstances" "HOL-Library.Adhoc_Overloading"
begin

datatype  reified =
  RNat nat
  | RUnit unit
  | RBool bool
  | RProd "reified * reified"
  | RSum "reified + reified"
  | ROpt "reified option"
  | RTriv "reified md_triv"

datatype rtype =
  TNat
  | TUnit
  | TBool
  | TOpt "rtype"
  | TTriv "rtype"

class reiden =
  fixes reify :: "'a \<Rightarrow> reified"  
  fixes denote :: "reified \<Rightarrow> 'a"

class reident =
  fixes reifyt :: "'a itself \<Rightarrow> rtype"  
  fixes denotet :: "rtype \<Rightarrow> 'a itself"

instantiation nat :: reiden
begin
definition rnat_def : "reify x = RNat x"
definition dnat_def :
  "denote x = (case x of (RNat n) \<Rightarrow> n)"
instance proof qed
end

instantiation unit :: reiden
begin
definition runit_def : "reify x = RUnit x"
definition dunit_def :
  "denote x = (case x of (RUnit n) \<Rightarrow> n)"
instance proof qed
end

instantiation bool :: reiden
begin
definition rbool_def : "reify x = RBool x"
definition dbool_def : "denote x = (case x of (RBool n) \<Rightarrow> n)"
instance proof qed
end

instantiation md_triv :: (reiden) reiden
begin
definition rtriv_def : "reify (x :: ('a :: reiden) md_triv) =
    (case x of (mdt x') \<Rightarrow>  RTriv (mdt (reify x')))"
definition dtriv_def : "denote x = (case x of (RTriv (mdt n)) \<Rightarrow> mdt (denote n))"
instance proof 
qed
end

instantiation option :: (reiden) reiden
begin
definition ropt_def : "reify x =
    ROpt (map_option reify x)"
definition dopt_def : "denote x = 
  (case x of (ROpt x') \<Rightarrow> 
    (case x' of
      None \<Rightarrow> None
      | Some x'' \<Rightarrow> Some (denote x'')))"
instance proof 
qed
end

instantiation prod :: (reiden, reiden) reiden
begin
definition rprod_def : "reify x =
  RProd (map_prod reify reify x)"
definition dprod_def : "denote x =
  (case x of (RProd (x1, x2)) \<Rightarrow>
      (denote x1, denote x2))"
instance proof qed
end

instantiation nat :: reident
begin
definition rtnat_def : "reifyt (x :: nat itself) = TNat"
definition dtnat_def : "denotet x = (case x of (TNat) \<Rightarrow> (TYPE(nat)))"
instance proof qed
end

instantiation bool :: reident
begin
definition rtbool_def : "reifyt (x :: bool itself) = TBool"
definition dtbool_def : "denotet x = (case x of (TBool) \<Rightarrow> (TYPE(bool)))"
instance proof qed
end

instantiation unit :: reident
begin
definition rtunit_def : "reifyt (x :: unit itself) = TUnit"
definition dtunit_def : "denotet x = (case x of (TUnit) \<Rightarrow> (TYPE(unit)))"
instance proof qed
end

instantiation md_triv :: (reident) reident
begin
definition rttriv_def : "reifyt (x :: ('a :: reident) md_triv itself) =
    (TTriv (reifyt (TYPE('a))))"

definition dttriv_def : "denotet x = 
  (case x of (TTriv (n)) \<Rightarrow> 
    let (n' :: 'a itself) = denotet n in
    TYPE('a md_triv))"
instance proof 
qed
end

instantiation option :: (reident) reident
begin
definition rtopt_def : "reifyt (x :: ('a :: reident) option itself) =
    (TOpt (reifyt (TYPE('a))))"

definition dtopt_def : "denotet x = 
  (case x of (TOpt (n)) \<Rightarrow> 
    let (n' :: 'a itself) = denotet n in
    TYPE('a option))"
instance proof 
qed
end

definition get_lift :: "('a :: reiden, 'b :: reiden, 'c) lifting \<Rightarrow> (reified, reified, 'c) lifting" where
"get_lift t =
  \<lparr> LIn1 = (\<lambda> s a . LIn1 t (denote s) (denote a))
  , LIn2 = (\<lambda> s a b . LIn2 t (denote s) (denote a) b)
  , LOut1 = (\<lambda> s b . reify (LOut1 t (denote s) b)) \<rparr>"

definition get_lift' :: "(reified, 'b :: reiden, 'c) lifting \<Rightarrow> (reified, reified, 'c) lifting" where
"get_lift' t =
  \<lparr> LIn1 = (\<lambda> s a . LIn1 t s (denote a))
  , LIn2 = (\<lambda> s a b . LIn2 t s (denote a) b)
  , LOut1 = (\<lambda> s b . reify (LOut1 t s b)) \<rparr>"


class lifty =
  fixes default_liftr :: "(reified, reified, 'a) lifting"

instantiation nat :: lifty begin
definition dlr_nat :
  "default_liftr = ((get_lift' id_l) :: (reified, reified, nat) lifting)"
instance proof qed
end

instantiation bool :: lifty begin
definition dlr_bool :
  "default_liftr = ((get_lift' id_l) :: (reified, reified, bool) lifting)"
instance proof qed
end

instantiation option :: (lifty) lifty begin
definition dlr_opt :
  "default_liftr = (option_l default_liftr :: (reified, reified, 'a option) lifting)"
instance proof qed
end

instantiation md_triv :: (lifty) lifty begin
definition dlr_triv :
  "default_liftr = (triv_l default_liftr :: (reified, reified, 'a md_triv) lifting)"
instance proof qed
end

(* can we do something very hacky here
   in terms of looking at the reified types and deciding if we want one component or the other? *)
instantiation prod :: (lifty, lifty) lifty begin
definition dlr_prod :
  "default_liftr =
    


definition liftD1 :: "(reified, reified, 'c) lifting \<Rightarrow> (reified, 'b :: reiden, 'c) lifting" where
"liftD1 t =
  \<lparr> LIn1 = (\<lambda> s a . LIn1 t s (reify a))
  , LIn2 = (\<lambda> s a b . LIn2 t s (reify a) b)
  , LOut1 = (\<lambda> s b . denote (LOut1 t s b)) \<rparr>"

definition liftD2 :: "(reified, reified, 'c) lifting \<Rightarrow> ('a :: reiden, 'b :: reiden, 'c) lifting" where
"liftD2 t =
  \<lparr> LIn1 = (\<lambda> s a . LIn1 t (reify s) (reify a))
  , LIn2 = (\<lambda> s a b . LIn2 t (reify s) (reify a) b)
  , LOut1 = (\<lambda> s b . denote (LOut1 t (reify s) b)) \<rparr>"

declare [[show_variants]]

value [nbe] "liftD2 default_liftr :: (unit, nat, nat option) lifting"

value [nbe] "LIn1 (liftD2 default_liftr) () (3 :: nat) :: nat option"

value [nbe] "LIn1 (liftD2 default_liftr) () (3 :: nat) :: nat option md_triv"


type_synonym liftrt = "(rtype * rtype * rtype)"
(*
class liftable = reident +
  fixes default_lift' :: "rtype \<Rightarrow> rtype \<Rightarrow> 'a liftrt"

instantiation option :: (liftable) liftable
begin

term "\<lambda> synt stt . (let (stt' :: ('b :: reident) itself) = denotet stt in
    default_lift' synt (reifyt (TYPE('b option))))"
definition optlb :
"default_lift' synt stt = 
  (let (stt' :: ('b :: reident) itself) = denotet stt in
    default_lift' synt (reifyt (TYPE('b option))))"
*)



end