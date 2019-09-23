theory Reify imports Main
begin

type_synonym 'a lbd = "(char list * 'a)"


datatype  reified =
  RNat nat
  | RUnit unit
  | RBool bool
  | RProd "reified * reified"
  | RSum "reified + reified"

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

definition doconsR :: "char list \<Rightarrow> char list \<Rightarrow> 
                  reified \<Rightarrow> (reified \<Rightarrow> 'o1) \<Rightarrow> (char list \<Rightarrow> reified \<Rightarrow> 'o2) \<Rightarrow>
                  ((char list *'o1) + 'o2)" where
"doconsR s1 s2 a fa fb =
  (if s1 = s2 then (Inl (s1, fa a)) else
      Inr (fb s2 a))"


definition bail :: "'a \<Rightarrow> 'b" where
"bail x = undefined"

(* examples/tests *)

type_synonym result = "((nat lbd) + (bool lbd + unit lbd))"

term "doconsR'"

value "doconsR ''nat'' ''bool'' (reify (True)) (denote) 
       (\<lambda> s r . doconsR s ''bool'' r denote bail ) :: result"

value "doconsR ''nat'' ''bool'' (reify (True)) (denote) 
       (\<lambda> s r . doconsR s ''bool'' r denote bail ) :: result"

value "doconsR ''nat'' ''nat'' (reify (0 :: nat)) (denote) 
       (\<lambda> s r . doconsR s ''bool'' r denote bail ) :: result"

(* another option: reifying everything *)

term "(\<lambda> ti to1 to2 s1 s2 x f1 f2 . docons_right ti to1 to2 s1 s2 x f2)"
(*adhoc_overloading constr "(\<lambda> ti to1 to2 s1 s2 x f1 f2 . docons_left ti to2 s1 s2 x)"*)



value "''abc''"

value "constr (TYPE(nat)) (TYPE(_)) (TYPE(_))  ''abc'' ''abc'' (0 :: nat) id 
      (\<lambda> s (_ :: nat) . undefined)  :: result"

value "constr (TYPE(_)) (TYPE(_)) (TYPE(_))  ''abc'' ''abc'' (0 :: nat) id 
      (bail :: char list \<Rightarrow> nat \<Rightarrow> _) :: result"

value "constr (TYPE(_)) (TYPE(_)) (TYPE(_))  ''abc'' ''abc'' (0 :: nat) bail 
      (\<lambda> s x . docons_left (TYPE(_)) (TYPE(_))  ''def'' s x)  :: result"

value "constr (TYPE(_)) (TYPE(_)) (TYPE(_))  ''abc'' ''abc'' (0 :: nat) bail 
      (\<lambda> s x . constr (TYPE(_)) (TYPE(_)) (TYPE(_)) ''def'' s x bail bail)  :: result"

value "constr (TYPE(_)) (TYPE(_)) (TYPE(_))  ''abc'' ''def'' (True :: bool) bail
    (\<lambda> s x . constr (TYPE(_)) (TYPE(_)) (TYPE(_)) ''def'' s x bail bail) :: result"


term "docons_right (TYPE(_)) (TYPE(_)) (TYPE(_))  ''abc'' ''def'' (True :: bool)
    (\<lambda> s x . docons_left (TYPE(_)) (TYPE(_)) ''def'' s x) :: result"


value "docons_right (TYPE(_)) (TYPE(_)) (TYPE(_))  ''abc'' ''def'' (True :: bool)
    (\<lambda> s x . docons_left (TYPE(_)) (TYPE(_)) ''def'' s x) :: result"

value "constr (TYPE(_)) (TYPE(_)) (TYPE(_))  ''abc'' ''def'' (True :: bool) bail
    (\<lambda> s x . docons_left (TYPE(_)) (TYPE(_)) ''def'' s x) :: result"

value "constr (TYPE(_)) (TYPE(_)) (TYPE(_))  ''abc'' ''def'' (True :: bool) bail
       (\<lambda> c i . docons_left (TYPE(_)) (TYPE(_))  c ''def'' i) :: result"


value "constr (TYPE(_)) (TYPE(_)) (TYPE(_))  ''abc'' ''def'' (True :: bool) bail
       bail :: result"



end