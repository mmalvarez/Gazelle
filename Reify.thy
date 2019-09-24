theory Reify imports Main
begin

type_synonym 'a lbd = "(char list * 'a)"

(* test - small programming language for arithmetic *)
datatype calc =
  AccAdd nat
  | AccSub nat
  | AccReset

datatype  reified =
  RNat nat
  | RUnit unit
  | RBool bool
  | RCalc calc
  | RProd "reified * reified"
  | RSum "reified + reified"


definition rpair :: "reified \<Rightarrow> reified \<Rightarrow> reified" where
"rpair r1 r2 = RProd (r1, r2)"

definition rsplit ::
  "(reified \<Rightarrow> 'a) \<Rightarrow> (reified \<Rightarrow> 'b) \<Rightarrow> reified \<Rightarrow>
    'a * 'b" where
"rsplit da db r =
  (case r of
    RProd (a, b) \<Rightarrow> (da a, db b)
    | _ \<Rightarrow> undefined)"

definition rinl :: "reified \<Rightarrow> reified" where
"rinl r = RSum (Inl r)"

definition rinr :: "reified \<Rightarrow> reified" where
"rinr r = RSum (Inr r)"

class reified =
  fixes reify :: "'a \<Rightarrow> reified"  

instantiation nat :: reified
begin
definition rnat_def : "reify x = RNat x"
instance proof qed
end

instantiation unit :: reified
begin
definition runit_def : "reify x = RUnit x"
instance proof qed
end

instantiation bool :: reified
begin
definition rbool_def : "reify x = RBool x"
instance proof qed
end

instantiation calc :: reified
begin
definition rcalc_def : "reify x = RCalc x"
instance proof qed
end


class denoted =
  fixes denote :: "reified \<Rightarrow> 'a"

instantiation nat :: denoted
begin
definition dnat_def :
  "denote x = (case x of (RNat n) \<Rightarrow> n | _ \<Rightarrow> undefined)"
instance proof qed
end

instantiation unit :: denoted
begin
definition dunit_def :
  "denote x = (case x of (RUnit n) \<Rightarrow> n | _ \<Rightarrow> undefined)"
instance proof qed
end

instantiation bool :: denoted
begin
definition dbool_def :
  "denote x = (case x of (RBool n) \<Rightarrow> n | _ \<Rightarrow> undefined)"
instance proof qed
end

instantiation calc :: denoted
begin
definition dcalc_def :
  "denote x = (case x of (RCalc n) \<Rightarrow> n | _ \<Rightarrow> undefined)"
instance proof qed
end

instantiation prod :: (reified, reified) reified
begin

definition rprod_def :
  "reify x = RProd (reify (fst x), reify (snd x))"

instance proof qed
end

instantiation prod :: (denoted, denoted) denoted
begin

definition dprod_def :
  "denote x = 
    (case x of (RProd (x1, x2)) \<Rightarrow> (denote x1, denote x2)
      | _ \<Rightarrow> undefined)"

instance proof qed
end

instantiation sum :: (reified, reified) reified
begin

definition rsum_def :
  "reify x = (case x of
      (Inl x1) \<Rightarrow> RSum (Inl (reify x1))
      | (Inr x2) \<Rightarrow> RSum (Inr (reify x2)))"

instance proof qed
end

instantiation sum :: (denoted, denoted) denoted
begin

definition dsum_def :
  "denote x = (case x of
      RSum (Inl x1) \<Rightarrow> Inl (denote x1)
      | RSum (Inr x2) \<Rightarrow> (Inr (denote x2)))"

instance proof qed
end

definition docons :: "char list \<Rightarrow> char list \<Rightarrow> 
                  reified \<Rightarrow> (reified \<Rightarrow> 'xp * 'o1) \<Rightarrow> (char list \<Rightarrow> reified \<Rightarrow> char list * 'xp * 'o2) \<Rightarrow>
                  (char list * 'xp * ('o1 + 'o2))" where
"docons s1 s2 a  fa fb =
  (if s1 = s2 then
    (case fa a of
      (xp, x) \<Rightarrow> (s2, xp, Inl x))
    else
    (case (fb s2 a) of
      (rs, xp, rx) \<Rightarrow> (rs, xp, Inr rx)))"


definition bail :: "'a \<Rightarrow> 'b" where
"bail x = undefined"

(* examples/tests *)

type_synonym result = "(unit * (nat + bool + unit)) lbd"

term "docons"

fun uwrap :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> (unit * 'b))" where
"uwrap f x = ((), f x)"

value "docons ''nat'' ''bool'' (reify (True)) (uwrap  denote) 
       (\<lambda> s r . docons s ''bool'' r (uwrap  denote) bail ) :: result"

value "docons ''nat'' ''bool'' (reify (True)) (uwrap denote) 
       (\<lambda> s r . docons s ''bool'' r (uwrap denote) bail ) :: result"

value "docons ''nat'' ''nat'' (reify (0 :: nat)) (uwrap denote) 
       (\<lambda> s r . docons s ''bool'' r (uwrap denote) bail ) :: result"

(* another option: reifying everything *)

term "(\<lambda> ti to1 to2 s1 s2 x f1 f2 . docons_right ti to1 to2 s1 s2 x f2)"
(*adhoc_overloading constr "(\<lambda> ti to1 to2 s1 s2 x f1 f2 . docons_left ti to2 s1 s2 x)"*)



end