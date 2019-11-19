theory Reify imports Main "Prism/Prism"
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


class reiden =
  fixes reify :: "'a \<Rightarrow> reified"  
  fixes denote :: "reified \<Rightarrow> 'a option"
  assumes HPrism : "Prism.Prism_Spec \<lparr> cases = (\<lambda> r . case (denote r) of Some x \<Rightarrow> Inl x
                                                                         | _ \<Rightarrow> Inr r)
                                     , inj = reify \<rparr>"
begin



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

end


instantiation nat :: reiden
begin
definition rnat_def : "reify x = RNat x"
definition dnat_def :
  "denote x = (case x of (RNat n) \<Rightarrow> Some n | _ \<Rightarrow> None)"
instance proof
  fix r :: reified
  show "Prism_Spec
     \<lparr>prism_parms.cases =
        \<lambda>r. case denote r of None \<Rightarrow> Inr r
             | Some (x :: nat) \<Rightarrow> Inl x,
        inj = reify\<rparr>"
    apply(simp add:Prism_Spec_def) apply(safe)
      apply(simp add:rnat_def dnat_def)
     apply(simp add:rnat_def dnat_def split:reified.splits)
    apply(simp add:rnat_def dnat_def split:reified.splits)
    done
qed
end

instantiation unit :: reiden
begin
definition runit_def : "reify x = RUnit x"
definition dunit_def :
  "denote x = (case x of (RUnit n) \<Rightarrow> Some n | _ \<Rightarrow> None)"
instance proof
  show "Prism_Spec
     \<lparr>prism_parms.cases =
        \<lambda>r. case denote r of None \<Rightarrow> Inr r
             | Some (x :: unit) \<Rightarrow> Inl x,
        inj = reify\<rparr>"
    apply(simp add:Prism_Spec_def) 
    apply(auto simp add:runit_def dunit_def split:reified.splits)
    done
qed
end

instantiation bool :: reiden
begin
definition rbool_def : "reify x = RBool x"
definition dbool_def : "denote x = (case x of (RBool n) \<Rightarrow> Some n | _ \<Rightarrow> None)"
instance proof
  show "Prism_Spec
     \<lparr>prism_parms.cases =
        \<lambda>r. case denote r of None \<Rightarrow> Inr r
             | Some (x :: bool) \<Rightarrow> Inl x,
        inj = reify\<rparr>"
    apply(simp add:Prism_Spec_def) 
    apply(auto simp add:rbool_def dbool_def split:reified.splits)
    done
qed
end

instantiation calc :: reiden
begin
definition rcalc_def : "reify x = RCalc x"
definition dcalc_def : "denote x = (case x of (RCalc n) \<Rightarrow> Some n | _ \<Rightarrow> None)"
instance proof 
  show "Prism_Spec
     \<lparr>prism_parms.cases =
        \<lambda>r. case denote r of None \<Rightarrow> Inr r
             | Some (x :: calc) \<Rightarrow> Inl x,
        inj = reify\<rparr>"
    apply(auto simp add:Prism_Spec_def rcalc_def dcalc_def split:reified.splits)
      done
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
  fix x :: "'a * 'b"
  show "Prism_Spec
     \<lparr>prism_parms.cases =
        \<lambda>r. case denote r of None \<Rightarrow> Inr r
             | Some (x :: 'a * 'b) \<Rightarrow> Inl x,
        inj = reify\<rparr>"

    apply(simp add:Prism_Spec_def) 
      apply(auto simp add:Prism_Spec_def rprod_def dprod_def split:reified.splits)
      apply(auto split:option.splits)      
        apply(auto simp add:DRCorrect)
      apply(auto simp add:Prism_Spec_def rprod_def dprod_def split:reified.splits)
        apply(auto simp add:RDCorrect)
    done
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
  fix x :: "'a + 'b"
  show "Prism_Spec
     \<lparr>prism_parms.cases =
        \<lambda>r. case denote r of None \<Rightarrow> Inr r
             | Some (x :: 'a + 'b) \<Rightarrow> Inl x,
        inj = reify\<rparr>"
    apply(simp add:Prism_Spec_def)
    apply(auto simp add: rsum_def dsum_def RDCorrect DRCorrect split:sum.splits reified.splits option.splits)
    done
qed
end

(*
definition docons :: "char list \<Rightarrow> char list \<Rightarrow> 
                  reified \<Rightarrow> (reified \<Rightarrow> ('xp * 'o1)) \<Rightarrow> 
                  (char list \<Rightarrow> reified \<Rightarrow> (char list * 'xp * 'o2) option) \<Rightarrow>
                  (char list * 'xp * ('o1 + 'o2)) option" where
"docons s1 s2 a  fa fb =
  (if s1 = s2 then
    (case fa a of
      (xp, x) \<Rightarrow> Some (s2, xp, Inl x))
    else
    (case (fb s2 a) of
      Some (rs, xp, rx) \<Rightarrow> Some (rs, xp, Inr rx)
     | None \<Rightarrow> None))"


definition bail :: "'a \<Rightarrow> 'b" where
"bail x = undefined"

fun force :: "'a option \<Rightarrow> 'a" where
"force (Some a) = a"
| "force None = undefined"

(* examples/tests *)

type_synonym result = "(unit * (nat + bool + unit)) lbd"

term "docons"

fun uwrap :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> (unit * 'b))" where
"uwrap f x = ((), f x)"

fun nonewrap :: "'a \<Rightarrow> 'b \<Rightarrow> 'c option" where
"nonewrap _ _ = None"

value "docons ''nat'' ''bool'' (reify (True)) (uwrap  denote) 
       (\<lambda> s r . docons s ''bool'' r (uwrap  denote) nonewrap ) :: result option"

value "docons ''nat'' ''bool'' (reify (True)) (uwrap denote) 
       (\<lambda> s r . docons s ''bool'' r (uwrap denote) nonewrap ) :: result option"

value "docons ''nat'' ''nat'' (reify (0 :: nat)) (uwrap denote) 
       (\<lambda> s r . docons s ''bool'' r (uwrap denote) nonewrap ) :: result option"

(* another option: reifying everything *)

term "(\<lambda> ti to1 to2 s1 s2 x f1 f2 . docons_right ti to1 to2 s1 s2 x f2)"
(*adhoc_overloading constr "(\<lambda> ti to1 to2 s1 s2 x f1 f2 . docons_left ti to2 s1 s2 x)"*)
*)


end