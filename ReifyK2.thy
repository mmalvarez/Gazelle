theory ReifyK2 imports Main
begin

(*
declare [[coercion_enabled]]
*)

datatype 'a reicon =
  RProd "'a * 'a"
  | RSum "'a + 'a"
  | ROption "'a option"

datatype reity =
  RTNat
  | RTUnit
  | RTBool

datatype reity2 =
  RTOption
  | RTList

datatype  rei =
  RNat nat
  | RUnit unit
  | RBool bool
  | RC "rei reicon"



(* idea: anything that can be reified at level 0 can be reified
   at level 1 *)
datatype  rei1 =
  R1 "rei"
  | RC1 "rei1 reicon"
  | RF1  "rei \<Rightarrow> rei1"

datatype rei2 =
  R2 "rei1"
  | RC2 "rei2 reicon"
  | RF2  "rei1 \<Rightarrow> rei2"

datatype  rei3 =
  R3 "rei2"
  | RC3 "rei3 reicon"
  | RF3  "rei2 \<Rightarrow> rei3"

datatype reiX =
  RX3 "rei3"
  | RX2 "rei2"
  | RX1 "rei1"
  | RX0 "rei"

(* new idea:
- reify into reiX
- need an easy way to coerce reiX's into rei1/2/3?
*)
datatype 'a gNat = 
  GN nat

(*
class reiden3 =
  fixes reifyX :: "'a \<Rightarrow> reiX"
  fixes denoteX :: "reiX \<Rightarrow> 'a"

class reiden2 = 
  fixes reifyX :: "'a \<Rightarrow> reiX"
  fixes denoteX :: "reiX \<Rightarrow> 'a"

class reiden1 = 
  fixes reifyX :: "'a \<Rightarrow> reiX"
  fixes denoteX :: "reiX \<Rightarrow> 'a"

class reiden0 = 
  fixes reifyX :: "'a \<Rightarrow> reiX"
  fixes denoteX :: "reiX \<Rightarrow> 'a"
*)
class reidenX =
  fixes reifyX :: "'a \<Rightarrow> reiX"
  fixes denoteX :: "reiX \<Rightarrow> 'a"
  fixes level :: "'a itself \<Rightarrow> 'a gNat"
  (*fixes inhab :: "'a itself \<Rightarrow> 'a"*)

(* need "squish" functions to normalize our reified things *)
(* idea: have a function that goes 3 \<Rightarrow> 2 if possible
   stays same otherwise *)

(* maybe we can reify different parts of the component separately
   at different levels? *)
fun squishcon :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a reicon \<Rightarrow> 'b reicon option" where 
"squishcon f (RProd (a,b)) =
  (case (f a, f b) of
    (Some a', Some b') \<Rightarrow> Some (RProd (a',b'))
    | _ \<Rightarrow> None )"
|"squishcon f (RSum (Inl a)) =
  (case f a of Some a' \<Rightarrow> Some (RSum (Inl a'))
    | _ \<Rightarrow> None)"
|"squishcon f (RSum (Inr a)) =
  (case f a of Some a' \<Rightarrow> Some (RSum (Inr a'))
    | _ \<Rightarrow> None)"
|"squishcon f (ROption None) = Some (ROption None)"
|"squishcon f (ROption (Some a)) =
  (case f a of Some a' \<Rightarrow> Some (ROption (Some a'))
    | _ \<Rightarrow> None)"

(* TODO: implement actual squishing for constructors
   unfortunately this requires type-level information. *)
fun squish1 :: "rei1 \<Rightarrow> reiX" where
"squish1 (R1 r) = (RX0 r)"
| "squish1 (RC1 rc) = (RX1 (RC1 rc))"
| "squish1 (RF1 f) = RX1 (RF1 f)"

fun squish2 :: "rei2 \<Rightarrow> reiX" where
"squish2 (R2 r) = squish1 r"
| "squish2 (RC2 rc) = (RX2 (RC2 rc))"
| "squish2 (RF2 f) = (RX2 (RF2 f))"

fun squish3 :: "rei3 \<Rightarrow> reiX" where
"squish3 (R3 r) = squish2 r"
| "squish3 (RC3 rc) = (RX3 (RC3 rc))"
| "squish3 (RF3 f) = (RX3 (RF3 f))"


(* now we need a way to get lower reification levels so that
   we can make our function thing work.
   for instance nat is always reified at level 0, but we
   need to promote it to level 2 *)
(* ideally there should be some kind of hierarchy that can capture
   this idea of "if we can reify it at level 0 we can reify it at any higher level *)
(* new idea: "type-level nat" for representing levels
this way we can say "if we are reifiable at level 2 then we
are reifiable at level 3 ? *)

(*
assumes corr1 : "denote0 (reify0 x) = x"
assumes corr2 : "reify0 (denote0 y :: 'a) = y"
*)
(*
datatype 'a higho =
  Base 'a
  | Func "'a \<Rightarrow> 'a"
*)

term "huh"

(* TODO: see if we can reduce the boilerplate in these denotations *)
instantiation rei3 :: reidenX
begin
print_context
definition rr3_def : "reifyX x = RX3 x"
definition dr3_def : "denoteX x = 
    (case x of (RX3 x') \<Rightarrow> x'
               | (RX2 x') \<Rightarrow> R3 x'
               | (RX1 x') \<Rightarrow> R3 (R2 x')
               | (RX0 x') \<Rightarrow> R3 (R2 (R1 x')))"
definition rl3_def : "level = (\<lambda> (x :: rei3 itself) . GN 3)"
(*definition ri3_def : "inhab = (\<lambda> (x :: rei3 itself) . R3 (R2 (R1 (RUnit ()))))"*)

instance proof qed
end

instantiation rei2 :: reidenX
begin

definition rr2_def : "reifyX x = RX2 x"
definition dr2_def : "denoteX x = 
    (case x of 
      RX3 (R3 x') \<Rightarrow> x'
      | RX2 (x') \<Rightarrow> x'
      | RX1 x' \<Rightarrow> R2 x'
      | RX0 x' \<Rightarrow> R2 (R1 x'))"
definition rl2_def : "level = (\<lambda> (x :: rei2 itself) . GN 2)"
(*definition ri2_def : "inhab = (\<lambda> (x :: rei2 itself) . (R2 (R1 (RUnit ()))))"*)
instance proof qed
end

instantiation rei1 :: reidenX
begin

definition rr1_def : "reifyX x = RX1 x"
definition dr1_def : "denoteX x = 
    (case x of 
          RX3 (R3 (R2 x')) \<Rightarrow> x'
          | RX2 (R2 x') \<Rightarrow> x' 
          | RX1 (x') \<Rightarrow> x'
          | RX0 x' \<Rightarrow> R1 x' )"
definition rl1_def : "level = (\<lambda> (x :: rei1 itself) . GN 1)"
(*definition ri1_def : "inhab = (\<lambda> (x :: rei1 itself) . ((R1 (RUnit ()))))"*)

instance proof qed
end

instantiation rei :: reidenX
begin

definition rr0_def : "reifyX x = RX0 x"
definition dr0_def : "denoteX x = 
    (case x of 
            RX3 (R3 (R2 (R1 x'))) \<Rightarrow> x'
          | RX2 (R2 (R1 x')) \<Rightarrow> x'
          |  RX0 (x') \<Rightarrow> x')"
definition rl0_def : "level = (\<lambda> (x :: rei itself) . GN 0)"
(*definition ri0_def : "inhab = (\<lambda> (x :: rei itself) . (((RUnit ()))))"*)

instance proof qed
end


instantiation nat :: reidenX
begin
definition rn0_def : "reifyX n = RX0 (RNat n)"
definition dn0_def : "denoteX x = (case x of RX0 (RNat n) \<Rightarrow> n)"
definition leveln_def : "level = (\<lambda> (x :: nat itself) . GN 0)"
(* standard *)
instance proof qed
end


instantiation unit :: reidenX
begin
definition ru0_def : "reifyX n = RX0 (RUnit n)"
definition du0_def : "denoteX x = (case x of RX0 (RUnit n) \<Rightarrow> n)"
definition levelu_def : "level = (\<lambda> (x :: unit itself) . GN 0)"
(* standard *)
instance proof qed
end

(*
instantiation rei :: reiden0
begin
definition rr0_def : "reify0 x = x"
definition dr0_def : "denote0 x = x"
instance proof qed
(*
instance proof
  fix x :: rei
  show " denote0 (reify0 x) = x"
    apply(simp add:rr0_def dr0_def)
    done 
  fix y :: rei
  have "reify0 (denote0 y :: rei) = denote0 y"
    apply(rule_tac rr0_def) done 
  thus " reify0 (denote0 y :: rei) = y"
    apply(simp add:dr0_def)
    done
  qed
*)
end

instantiation rei :: reiden1
begin
definition rr1_def : "reify1 x = R1 x"
definition dr1_def : "denote1 x = (case x of R1 x \<Rightarrow> x)"
instance proof qed
end

value "reify0 (0 :: nat)"
value "reify1 (0 :: nat)"
*)

(*
instantiation rei1 :: reiden1
begin
definition rr1_def : "reify1 x = x"
definition dr1_def : "denote1 x = x"
instance proof qed
end

instantiation rei2 :: reiden2
begin
definition rr2_def : "reify x = (R3 x)"
definition dr2_def : "denote x =
  (case x of (R3 x) \<Rightarrow> x)"
instance proof qed
end

instantiation nat :: reiden
begin
definition rnat_def : "reify x = reify (RNat x)"
definition dnat_def : "denote x = 
  (case denote x of (RNat x) \<Rightarrow> x)"
instance proof qed
end

instantiation unit :: reiden
begin
definition runit_def : "reify x = reify (RUnit x)"
definition dunit_def : "denote x =
  (case x of (R3 (R2 (R1 (RUnit x)))) \<Rightarrow> x)"
instance proof qed
end

instantiation "fun" :: (reiden, reiden) reiden
begin

definition rfun_def : "reify f =
  RF3 (\<lambda> x . (reify (f (denote x))))"

end
*)
(*
instantiation bool :: reiden
begin
definition rbool_def : "reify x = RBool x"
definition dbool_def : "denote x = 
  (case x of (RBool x) \<Rightarrow> x)"
instance proof qed
end

instantiation prod :: (reiden, reiden) reiden
begin

definition rprod_def :
  "reify x = RProd (reify (fst x), reify (snd x))"

definition dprod_def :
  "denote x = 
    (case x of (RProd (x1, x2)) \<Rightarrow> (denote x1, denote x2)
      | _ \<Rightarrow> undefined)"

instance proof qed
end
*)

(*
instantiation option :: (reiden0) reiden0
begin
definition roption0_def :
  "reify0 x = (case x of None \<Rightarrow> RC (ROption None)
              | Some x' \<Rightarrow> RC (ROption (Some (reify0 x'))))"

definition doption0_def :
  "denote0 x = (case x of RC (ROption (Some x')) \<Rightarrow> Some (denote0 x')
                    | RC (ROption None) \<Rightarrow> None)"

instance proof qed
(*
  fix x :: "'a option"
  have "(denote0 (reify0 x) :: 'a option) = (x :: 'a option)"
    apply(case_tac x)
     apply(simp add:roption0_def doption0_def)
    apply(simp add:roption0_def doption0_def)
    apply(simp add:corr1)
    done
    fix x :: rei
*)


end
*)
instantiation "fun" :: (reidenX, reidenX) reidenX
begin
(* RF3 needs an RF2 \<Rightarrow> RF3 *)
(* f has type 'a \<Rightarrow> 'b
   where 'a can be reified at some level
   'b can be reified at some level
*)
print_context
 
(* idea here: we need to get the level of the argument type,
   and use that. as well as the level of the return type *)
(* this gives us the final level to reify on. At this point,
   we then need to do the following: 
   - select reification level based on max of ((parm + 1), result)
   - 
*)

value "case (True) of True \<Rightarrow> (2 :: nat)"


(* RF1 needs rei \<Rightarrow> rei1 *)
(* we are applying inhab to the wrong thing. *)
(* idea: how do we grab hold of the output type? *)
(*
level (\<lambda> x' . let bogusf = (\<lambda> woo . x' = f woo) in
*)

(* problem - how to force calculation of the result's level? *)
definition rfun1_def :
"reifyX (f :: 'a \<Rightarrow> 'b) = 
  (case (level (TYPE('a))) of
    GN ll \<Rightarrow> 
      (case (level (TYPE('b))) of
      GN lr \<Rightarrow> 
        let m =  (max (ll + 1) (lr)) :: nat in
                (case m = 1 of
                 True \<Rightarrow>  RX1 (RF1 (\<lambda> (x :: rei) . (denoteX (reifyX ((f (denoteX (reifyX x) :: 'a)) :: 'b)))) :: rei1)
                 | False \<Rightarrow> 
                 (case m = 2 of
                 True \<Rightarrow> RX2 (RF2 (\<lambda> (x :: rei1) . (denoteX (reifyX (f (denoteX (reifyX x) :: 'a)))) :: rei2))
                 | False \<Rightarrow>
                 (case m = 3 of
                  True \<Rightarrow> RX3 (RF3 ((\<lambda> (x :: rei2) . (denoteX (reifyX (f (denoteX (reifyX x) :: 'a)))) :: rei3))))))))"

definition dfun1_def :
  "denoteX r =
    (case r of
      (RX3 (RF3 f)) \<Rightarrow> (\<lambda> (x :: 'a) . denoteX (reifyX (f (denoteX (reifyX x)))) :: 'b)
      | (RX2 (RF2 f)) \<Rightarrow> (\<lambda> (x :: 'a) . denoteX (reifyX (f (denoteX (reifyX x)))) :: 'b)
      | (RX1 (RF1 f)) \<Rightarrow> (\<lambda> (x :: 'a) . denoteX (reifyX (f (denoteX (reifyX x)))) :: 'b))" 

definition dlevel_def :
  "level (tf :: ('a \<Rightarrow> 'b) itself) =
    (case (level (TYPE('a))) of
      GN ll \<Rightarrow> case (level (TYPE('b))) of
        GN lr \<Rightarrow> GN (max (ll + 1) (lr) :: nat))"
instance proof qed
end

value [simp] "denoteX (reifyX (RUnit ()))"

value [simp] "reifyX (\<lambda> (x :: unit) . ())"

value [simp] "(denoteX (reifyX (\<lambda> (x :: unit) . ())) :: (unit \<Rightarrow> unit)) ()"
(*
    RX1 (RF1 (\<lambda> (x :: rei) . ((f (RX0 x))))))
     RX1 (RF1 (\<lambda> (x ) . (denoteX (reifyX (f (denoteX (reifyX x)))))))"

"reifyXz f = 
  (case level (\<lambda> x . let bogus = f x in ()) of
    GN 0 \<Rightarrow> RX1 (RF1 (\<lambda> (x :: rei) . ((f (RX0 x))))))"
*)

(*
definition dfun1_def :
  "denoteX rf =
    (case rf of 
        RX3 (RF3 f) \<Rightarrow> (\<lambda> x . denoteX (RX3 (f (case (reifyX x) of
        RX2 x' \<Rightarrow> x')))))"
      *)
instance proof qed
end

value "(reifyX (\<lambda> (x :: nat) . x + 1))"

value "(denoteX (reifyX (\<lambda> (x :: nat) . x + 1)) :: nat \<Rightarrow> nat) 2"

value "reify1 (0 :: nat)"

value "reify2 (\<lambda> (x :: nat) . x + 1)"       

instantiation option ::  (reiden) rfunctor
begin
definition fmap_def :
  "fmap f x =
    reify (case x of
      None \<Rightarrow> None
      | Some x' \<Rightarrow> f x')"

instance proof qed
end

value "rfmap ((\<lambda> x . x + 1 :: nat))"

end
