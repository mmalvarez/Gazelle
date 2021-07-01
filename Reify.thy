theory Reify imports "AList/AList"
begin

(* 
*)

(* do we want this kind of reification?
   or some kind of string reification?
   arbitrary ancestor?
*)

datatype  reified =
  RNat nat
  | RUnit unit
  | RBool bool
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


class reiden =
  fixes reify :: "'a \<Rightarrow> reified"  
  fixes denote :: "reified \<Rightarrow> 'a option"
  assumes RD : "denote r = Some x ==> reify x = r"
  assumes DR : "denote (reify x) = Some x"
begin


(*
definition cases where
"cases = (\<lambda> r . case (denote r) of Some x \<Rightarrow> Inl x
          | _ \<Rightarrow> Inr r)"
definition inj where
"inj = reify"

lemma DRCorrect : "denote (reify x) = Some x"
  apply(insert HPrism) apply(simp add: Prism_Spec_def) apply(safe)
  apply(drule_tac x = x in spec) apply(case_tac "denote (reify x)")
   apply(auto)
  done

lemma RDCorrect : "denote r = Some x \<Longrightarrow> reify x = r"
  apply(insert HPrism) apply(simp add: Prism_Spec_def) apply(safe)
  apply(drule_tac x = r in spec) apply(clarsimp)
  done
*)
end


instantiation nat :: reiden
begin
definition rnat_def : "reify x = RNat x"
definition dnat_def :
  "denote x = (case x of (RNat n) \<Rightarrow> Some n | _ \<Rightarrow> None)"
instance proof
  fix r :: reified
  fix x :: nat
  show "denote r = Some x \<Longrightarrow> reify x = r"
    by(auto simp add: rnat_def dnat_def split:reified.splits)
next
  show "\<And>(x :: nat). denote (reify x) = Some x"
      by(auto simp add: rnat_def dnat_def split:reified.splits)
qed
end

instantiation unit :: reiden
begin
definition runit_def : "reify x = RUnit x"
definition dunit_def :
  "denote x = (case x of (RUnit n) \<Rightarrow> Some n | _ \<Rightarrow> None)"
instance proof
  fix r :: reified
  fix x :: unit
  show "denote r = Some x \<Longrightarrow> reify x = r"
    by(auto simp add: runit_def dunit_def split:reified.splits)
next
  show "\<And>(x :: unit). denote (reify x) = Some x"
      by(auto simp add: runit_def dunit_def split:reified.splits)
qed
end

instantiation bool :: reiden
begin
definition rbool_def : "reify x = RBool x"
definition dbool_def : "denote x = (case x of (RBool n) \<Rightarrow> Some n | _ \<Rightarrow> None)"
instance proof
  fix r :: reified
  fix x :: bool
  show "denote (r :: reified) = Some (x :: bool) \<Longrightarrow> reify x = r"
    by(auto simp add: rbool_def dbool_def split:reified.splits)
next
  show "\<And>(x :: bool). denote (reify x) = Some x"
      by(auto simp add: rbool_def dbool_def split:reified.splits)
qed
end

instantiation prod :: (reiden, reiden) reiden
begin

definition rprod_def :
  "reify x = RProd (reify (fst x), reify (snd x))"
definition dprod_def :
  "denote x = 
    (case x of (RProd (x1, x2)) \<Rightarrow>
      ( case (denote x1, denote x2) of
              (Some x1', Some x2') \<Rightarrow> Some (x1', x2')
              | _ \<Rightarrow> None)
      | _ \<Rightarrow> None)"
instance proof
  fix r :: reified
  fix x :: "'a * 'b"
  show "denote (r :: reified) = Some x \<Longrightarrow> reify x = r" using RD
    sorry
next
  show "\<And>(x :: 'a * 'b). denote (reify x) = Some x"
sorry
qed
end

instantiation sum :: (reiden, reiden) reiden

begin

definition rsum_def :
  "reify x = (case x of
      (Inl x1) \<Rightarrow> RSum (Inl (reify x1))
      | (Inr x2) \<Rightarrow> RSum (Inr (reify x2)))"

definition dsum_def :
  "denote x = (case x of
      RSum (Inl x1) \<Rightarrow> 
          map_option Inl (denote x1)
      | RSum (Inr x2) \<Rightarrow> map_option Inr (denote x2)
      | _ \<Rightarrow> None)"

instance proof
  fix r :: reified
  fix x :: "'a + 'b
  show "denote (r :: reified) = Some (x :: 'a + 'b) \<Longrightarrow> reify x = r"
sorry
next
  show "\<And>(x :: 'a + 'b). denote (reify x) = Some x"
sorry
qed
end

end