theory Access 
    imports Main Mergeable "../Lifting/LiftInstances" "HOL-Library.Adhoc_Overloading"
begin

(* attempt to write a typeclass-driven version of Splittable.
or, can we somehow combine splittable and liftings to get something user-friendly?

problem with splittable is that we are forced into a fixed representation.
goal of liftings is precisely to deal with different representations.
 *)

(* for now, suppose we just want to support projections out of tuples. *)

datatype  reified =
  RNat nat
  | RInt int
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
begin

(*
definition cases where
"cases = (\<lambda> r . case (denote r) of Some x \<Rightarrow> Inl x
          | _ \<Rightarrow> Inr r)"
definition inj where
"inj = reify"
*)

fun denote' :: "reified \<Rightarrow> 'a" where
"denote' r =
  (case denote r of (Some x) \<Rightarrow> x)"

end

instantiation nat :: reiden begin
definition reify_nat where
"reify n = RNat n"

definition denote_nat where
"denote r = 
  (case r of
    (RNat n) \<Rightarrow> Some n
    | _ \<Rightarrow> None)"
instance proof qed
end

instantiation int :: reiden begin
definition reify_int where
"reify i = RInt i"

definition denote_int where
"denote r = 
  (case r of
    (RInt i) \<Rightarrow> Some i
    | _ \<Rightarrow> None)"
instance proof qed
end

instantiation unit :: reiden begin
definition reify_unit where
"reify x = RUnit x"

definition denote_unit where
"denote r = 
  (case r of
    (RUnit x) \<Rightarrow> Some x
    | _ \<Rightarrow> None)"
instance proof qed
end

instantiation bool :: reiden begin
definition reify_bool where
"reify x = RBool x"

definition denote_bool where
"denote r = 
  (case r of
    (RBool x) \<Rightarrow> Some x
    | _ \<Rightarrow> None)"
instance proof qed
end

instantiation prod :: (reiden, reiden) reiden begin
definition reify_prod where
"reify x = 
  (case x of (x1, x2) \<Rightarrow> RProd (reify x1, reify x2))"

definition denote_prod where
"denote r = 
  (case r of
    (RProd (r1, r2)) \<Rightarrow> 
      (case denote r1 of
        Some x1 \<Rightarrow>
          (case denote r2 of
            Some x2 \<Rightarrow> Some (x1, x2)
            | _ \<Rightarrow> None)
        | _ \<Rightarrow> None)
    | _ \<Rightarrow> None)"
instance proof qed
end

instantiation sum :: (reiden, reiden) reiden begin
definition reify_sum where
"reify x =
  (case x of
    Inl x1 \<Rightarrow> RSum (Inl (reify x1))
    | Inr x2 \<Rightarrow> RSum (Inr (reify x2)))"

definition denote_sum where
"denote r = 
  (case r of
    (RSum (Inl r1)) \<Rightarrow> 
      (case (denote r1) of
        Some x1 \<Rightarrow> Some (Inl x1)
        | _ \<Rightarrow> None)
    | (RSum (Inr r2)) \<Rightarrow>
      (case (denote r2) of
        Some x2 \<Rightarrow> Some (Inr x2)
        | _ \<Rightarrow> None)
    | _ \<Rightarrow> None)"
instance proof qed
end

datatype 'a labd =
  L "String.literal" "'a"

class labld =
  fixes lget :: "String.literal list \<Rightarrow> 'a \<Rightarrow> reified option"

instantiation labd :: (reiden) labld begin
definition lget_labd where
"lget s x =
  (case x of
    (L s' d) \<Rightarrow> (if s = [s'] then Some (reify d) else None))"

instance proof qed
end
(*
instantiation prod :: (labld, labld) labld begin
definition lget_prod where
"lget s p =
  (case p of
    (x1, x2) \<Rightarrow>
      (case s of
        [] \<Rightarrow> None
        | sh#st \<Rightarrow>
          (if sh = STR ''fst''
           then lget st x1
           else
            (if sh = STR ''snd''
             then lget st x2
             else None))))"

instance proof qed
end
*)

instantiation prod :: (labld, labld) labld begin
definition lget_prod where
"lget s p =
  (case p of
    (x1, x2) \<Rightarrow>
      (case (lget s x1) of
        None \<Rightarrow> lget s x2
        | Some r \<Rightarrow> Some r))"
instance proof qed
end

(* 'a is for schema labels *)
datatype 'a rtyp =
  TNat 'a
  | TInt 'a
  | TUnit 'a
  | TBool 'a
  | TProd 'a "'a rtyp" "'a rtyp"
  | TSum 'a "'a rtyp" "'a rtyp"

fun rt_strip :: "'a rtyp \<Rightarrow> unit rtyp" where
"rt_strip (TNat _) = TNat ()"
| "rt_strip (TInt _) = TInt ()"
| "rt_strip (TUnit _) = TUnit ()"
| "rt_strip (TBool _) = TBool ()"
| "rt_strip (TProd _ x y) =
    TProd () (rt_strip x) (rt_strip y)"
| "rt_strip (TSum _ x y) =
    TSum () (rt_strip x) (rt_strip y)"

class reident =
  fixes reifyt :: "'a itself \<Rightarrow> unit rtyp"  
  fixes denotet :: "unit rtyp \<Rightarrow> 'a itself option"
begin

end

instantiation nat :: reident begin
definition reifyt_nat where
"reifyt (x :: nat itself) = TNat ()"

definition denotet_nat where
"denotet rt = 
  (case rt of
    (TNat _) \<Rightarrow> Some (TYPE(nat))
    | _ \<Rightarrow> None)"
instance proof qed
end

instantiation int :: reident begin
definition reifyt_int where
"reifyt (i :: int itself) = TInt ()"

definition denotet_int where
"denotet rt = 
  (case rt of
    (TInt _) \<Rightarrow> Some (TYPE(int))
    | _ \<Rightarrow> None)"
instance proof qed
end

instantiation unit :: reident begin
definition reifyt_unit where
"reifyt (x :: unit itself) = TUnit ()"

definition denotet_unit where
"denotet rt = 
  (case rt of
    (TUnit x) \<Rightarrow> Some (TYPE(unit))
    | _ \<Rightarrow> None)"
instance proof qed
end

instantiation bool :: reident begin
definition reifyt_bool where
"reifyt (x :: bool itself) = TBool ()"

definition denotet_bool where
"denotet rt = 
  (case rt of
    (TBool x) \<Rightarrow> Some (TYPE(bool))
    | _ \<Rightarrow> None)"
instance proof qed
end

instantiation prod :: (reident, reident) reident begin
definition reifyt_prod where
"reifyt (x :: ('a * 'b) itself) = 
  TProd () (reifyt (TYPE('a))) (reifyt (TYPE('b)))"

definition denotet_prod where
"denotet rt = 
  (case rt of
    (TProd x t1 t2) \<Rightarrow> 
      (case (denotet t1 :: 'a itself option) of
        Some x1 \<Rightarrow>
          (case (denotet t2 :: 'b itself option) of
            Some x2 \<Rightarrow> Some (TYPE('a * 'b))
            | _ \<Rightarrow> None)
        | _ \<Rightarrow> None)
    | _ \<Rightarrow> None)"
instance proof qed
end

instantiation sum :: (reident, reident) reident begin
definition reifyt_sum where
"reifyt (x :: ('a + 'b) itself) = 
  TSum () (reifyt (TYPE('a))) (reifyt (TYPE('b)))"

definition denotet_sum where
"denotet rt = 
  (case rt of
    (TSum x t1 t2) \<Rightarrow> 
      (case (denotet t1 :: 'a itself option) of
        Some x1 \<Rightarrow>
          (case (denotet t2 :: 'b itself option) of
            Some x2 \<Rightarrow> Some (TYPE('a + 'b))
            | _ \<Rightarrow> None)
        | _ \<Rightarrow> None)
    | _ \<Rightarrow> None)"
instance proof qed
end

(*
datatype ('name, 'a, 'b) nprod =
  NP "'name" "'a" "'b"

(*
instantiation nprod :: "(_, _,
*)
(*
instantiation nprod :: (n_A, _, _) hasA
begin
definition gtA_nprod where
"gtA (x :: ('a, 'b,'c) nprod) = True"
instance proof qed
end
*)

(*
instantiation nprod :: (n_A, _, _) has_A_I begin
instance proof qed
end

instantiation nprod :: (_, has_A, _) has_A_L begin
*)

(* can we separate out schema? *)

class NonLeaf

instantiation nprod :: (_, _, _) NonLeaf begin
instance proof qed
end

consts findA :: "'a \<Rightarrow> String.literal list option"

definition hereA :: "('n :: n_A, 'a, 'b) nprod \<Rightarrow> 
                    String.literal list option" where
"hereA np = Some [STR ''fst'']"

definition digA12 :: "('a :: NonLeaf \<Rightarrow> String.literal list option) \<Rightarrow>
                    ('b :: NonLeaf \<Rightarrow> String.literal list option) \<Rightarrow>
                    ('n :: n_notA, 'a, 'b) nprod \<Rightarrow>
                    String.literal list option" where
"digA12 fd1 fd2 np =
  (case np of
    (NP nm a b) \<Rightarrow>
      (case fd1 a of
        None \<Rightarrow> (case fd2 b of
                  None \<Rightarrow> None
                  | Some x \<Rightarrow> Some ((STR ''snd'')#x))
        | Some x \<Rightarrow> Some ((STR ''fst'')#x)))"

definition digA1 ::
  "('a :: NonLeaf \<Rightarrow> String.literal list option) \<Rightarrow>
   ('n :: n_notA, 'a, 'b) nprod \<Rightarrow>
   String.literal list option" where
"digA1 fd np = 
  (case np of
      (NP nm a b) \<Rightarrow>
        (case fd a of
          None \<Rightarrow> None
          | Some x \<Rightarrow> Some ((STR ''fst'')#x)))"

definition digA2 ::
  "('b :: NonLeaf \<Rightarrow> String.literal list option) \<Rightarrow>
   ('n :: n_notA, 'a, 'b) nprod \<Rightarrow>
   String.literal list option" where
"digA2 fd np = 
  (case np of
      (NP nm a b) \<Rightarrow>
        (case fd b of
          None \<Rightarrow> None
          | Some x \<Rightarrow> Some ((STR ''snd'')#x)))"

(* ok, should we have the schema pulled out separately? 
have a datatype that pairs a schema with a data structure (?)
how can we have this work as a typeclass?
*)

(* schema =
   name,
   schema (?),
   schema (?) *)

(* n-ary ness of schemas? for now let's assume binary *)

(*
definition sndA :: "('n, 'a, 'b) nprod \<Rightarrow>
*)

adhoc_overloading findA hereA "digA2 findA" "digA1 findA"  "digA12 findA findA"
value [nbe] "findA (NP NB (0 :: int) (NP NB (1 :: int) (NP NA (1 :: int) (0 :: int))))"

(*
value [nbe] "findA (NP NB (NP NB (0 :: int) (1 :: int)) (NP NA (1 :: int) (0 :: int)))"
*)

consts findA1 :: "'a \<Rightarrow> String.literal list option"

consts navigate :: "'a \<Rightarrow> String.literal list \<Rightarrow> 'b option"
*)
(*
definition navProduct :: "('a1 \<Rightarrow> String.literal list \<Rightarrow> 'b option) \<Rightarrow>
                          ('a2 \<Rightarrow> String.literal list \<Rightarrow> 'b option) \<Rightarrow>
                          ('a1 * 'a2) \<Rightarrow> String.literal list \<Rightarrow> 'b option" where
"navProduct nv1 nv2 p l =
  (case l of
    [] \<Rightarrow> None
    | lh#lt \<Rightarrow> 
      (case p of
        (p1, p2) \<Rightarrow>
          (if l = 
*)

class n_A

class n_B

class n_C

class n_D

class n_E

class n_X

datatype nA = NA

datatype nB = NB

datatype nC = NC

datatype nD = ND

datatype nE = NE

datatype nX = NX

instantiation nA :: n_A begin
instance proof qed
end

instantiation nB :: n_B begin
instance proof qed
end

instantiation nC :: n_C begin
instance proof qed
end

instantiation nD :: n_D begin
instance proof qed
end

instantiation nE :: n_E begin
instance proof qed
end

instantiation nX :: n_X begin
instance proof qed
end


datatype ('a, 'b) sprod = 
  SP "'a" "'b"

class schem

instantiation nA :: schem begin
instance proof qed
end

instantiation nB :: schem begin
instance proof qed
end

instantiation nC :: schem begin
instance proof qed
end

instantiation nD :: schem begin
instance proof qed
end

instantiation nE :: schem begin
instance proof qed
end

instantiation nX :: schem begin
instance proof qed
end

instantiation sprod :: (schem, schem) schem begin
instance proof qed
end

term "SP NA (SP NA NB) :: _ :: schem"

class hasntA

class hasntB

class hasntC

class hasntD

class hasntE

(* class hasntX *)

instantiation nA :: "{hasntB, hasntC, hasntD, hasntE}" begin
instance proof qed
end

instantiation nB :: "{hasntA, hasntC, hasntD, hasntE}" begin
instance proof qed
end

instantiation nC :: "{hasntA, hasntB, hasntD, hasntE}" begin
instance proof qed
end

instantiation nD :: "{hasntA, hasntB, hasntC, hasntE}" begin
instance proof qed
end

instantiation nE :: "{hasntA, hasntB, hasntC, hasntD}" begin
instance proof qed
end

instantiation nX :: "{hasntA, hasntB, hasntC, hasntD, hasntE}" begin
instance proof qed
end


class hasA1

class hasA2

(* ok. so we need to account for all inputs. but, we still want to label since
   associativity isn't clear. *)

(* so what we want is
   schem (input) \<Rightarrow>
   schem (output) \<Rightarrow>
   (input, output) lifting *)

(* for now, let's try to do  schem(input)  \<Rightarrow> input \<Rightarrow> name \<Rightarrow> field *)

consts schem_get :: "'a :: schem \<Rightarrow> 'n \<Rightarrow> 'b  \<Rightarrow> 'x"

definition schem_get_base_A ::
  "'a :: n_A \<Rightarrow> 'b \<Rightarrow> 'n :: n_A \<Rightarrow> 'b" where
"schem_get_base_A _ b _ = b"

definition schem_get_base_B ::
  "'a :: n_B \<Rightarrow> 'b \<Rightarrow> 'n :: n_B \<Rightarrow> 'b" where
"schem_get_base_B _ b _ = b"

instantiation sprod :: (hasntA, hasntA) hasntA begin
instance proof qed
end

instantiation sprod :: (hasntB, hasntB) hasntB begin
instance proof qed
end

instantiation sprod :: (hasntC, hasntC) hasntC begin
instance proof qed
end

instantiation sprod :: (hasntD, hasntD) hasntD begin
instance proof qed
end

instantiation sprod :: (hasntE, hasntE) hasntE begin
instance proof qed
end

definition schem_getA_here :: "'a :: n_A \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" where
"schem_getA_here n _ b = b"

value "schem_getA NA NA (1 :: int)"

definition schem_getA_left ::
  "('ls \<Rightarrow> 'n \<Rightarrow> 'l \<Rightarrow> 'x) \<Rightarrow>
   ('ls, 'rs :: hasntA) sprod \<Rightarrow> 
   'n :: n_A \<Rightarrow> 
   ('l * 'r) \<Rightarrow>
   'x" where
"schem_getA_left getl sc n p =
  (case sc of
    SP ls rs \<Rightarrow>
      (case p of
        (l, r) \<Rightarrow>
          getl ls n l))"

definition schem_getA_right ::
  "('rs \<Rightarrow> 'n \<Rightarrow> 'r \<Rightarrow> 'x) \<Rightarrow>
   ('ls :: hasntA, 'rs) sprod \<Rightarrow> 
   'n :: n_A \<Rightarrow> 
   ('l * 'r) \<Rightarrow>
   'x" where
"schem_getA_right getr sc n p =
  (case sc of
    SP ls rs \<Rightarrow>
      (case p of
        (l, r) \<Rightarrow>
          getr rs n r))"

definition schem_getB_here :: "'a :: n_B \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" where
"schem_getB_here n _ b = b"

value "schem_getB NA NA (1 :: int)"

definition schem_getB_left ::
  "('ls \<Rightarrow> 'n \<Rightarrow> 'l \<Rightarrow> 'x) \<Rightarrow>
   ('ls, 'rs :: hasntB) sprod \<Rightarrow> 
   'n :: n_B \<Rightarrow> 
   ('l * 'r) \<Rightarrow>
   'x" where
"schem_getB_left getl sc n p =
  (case sc of
    SP ls rs \<Rightarrow>
      (case p of
        (l, r) \<Rightarrow>
          getl ls n l))"

definition schem_getB_right ::
  "('rs \<Rightarrow> 'n \<Rightarrow> 'r \<Rightarrow> 'x) \<Rightarrow>
   ('ls :: hasntB, 'rs) sprod \<Rightarrow> 
   'n :: n_B \<Rightarrow> 
   ('l * 'r) \<Rightarrow>
   'x" where
"schem_getB_right getr sc n p =
  (case sc of
    SP ls rs \<Rightarrow>
      (case p of
        (l, r) \<Rightarrow>
          getr rs n r))"

adhoc_overloading 
  schem_get
  schem_getA_here
  "schem_getA_left schem_get"
  "schem_getA_right schem_get"
  schem_getB_here
  "schem_getB_left schem_get"
  "schem_getB_right schem_get"
   
value "schem_get (SP NA NB) NA (0 :: int, 1 :: int)"

value "schem_get (SP (SP NB NA) (SP NB NB)) NA ((True, 0 :: int), 1 :: int)"

type_synonym ('n, 's, 'x, 'a, 'b, 'c) name_lift =
"'n  \<Rightarrow> 's \<Rightarrow>
   ('x, 'a, 'b) lifting \<Rightarrow> 
   ('x, 'a, 'c) lifting"

consts name_lift ::
  "('n, 's :: schem, 'x, 'a, 'b, 'c) name_lift"

(*
consts name_lift ::
  "'n  \<Rightarrow> 's :: schem \<Rightarrow>
   ('x, 'a, 'b) lifting \<Rightarrow> 
   ('x, 'a, 'c) lifting"
*)

(*
definition name_lift_baseA ::
  "'n :: n_A \<Rightarrow>
   'n \<Rightarrow>
   ('x, 'a, 'a :: Mergeable) lifting \<Rightarrow> 
   ('x, 'a, 'a :: Mergeable) lifting" where
"name_lift_baseA _ _ =
  id"
*)

definition name_lift_baseA ::
  "('n :: n_A, 'n, 'x, 'a, 'a, 'a) name_lift" where
"name_lift_baseA _ _ =
  id"

definition name_lift_baseB ::
  "'n :: n_B \<Rightarrow>
   'n \<Rightarrow>
   ('x, 'a, 'a :: Mergeable) lifting \<Rightarrow> 
   ('x, 'a, 'a :: Mergeable) lifting" where
"name_lift_baseB _ _ =
  id"

(*
definition name_lift_recA_left ::
  "('n \<Rightarrow> 'ls \<Rightarrow> ('x, 'a, 'b1 ) lifting \<Rightarrow> 
                 ('x, 'a, 'b2 ) lifting) \<Rightarrow>
   'n :: n_A \<Rightarrow>
   ('ls, 'rs :: hasntA) sprod \<Rightarrow>
   ('x, 'a, 'b1) lifting \<Rightarrow> 
   ('x, 'a, 'b2 * ('rest :: Pordb)) lifting" where
"name_lift_recA_left rec n s =
  (case s of
    SP ls rs \<Rightarrow>
      fst_l o (rec n ls))"
*)

definition name_lift_recA_left ::
  "('n, 'ls, 'x, 'a, 'b1, 'b2) name_lift \<Rightarrow>
   ('n :: n_A, ('ls, 'rs :: hasntA) sprod, 'x, 'a, 'b1, 'b2 * ('rest :: Pordb)) name_lift" where
"name_lift_recA_left rec n s =
  (case s of
    SP ls rs \<Rightarrow>
      fst_l o (rec n ls))"


definition name_lift_recA_right ::
  "('n \<Rightarrow> 'rs \<Rightarrow> ('x, 'a, 'b1 ) lifting \<Rightarrow> 
                 ('x, 'a, 'b2 ) lifting) \<Rightarrow>
   'n :: n_A \<Rightarrow>
   ('ls :: hasntA, 'rs) sprod \<Rightarrow>
   ('x, 'a, 'b1) lifting \<Rightarrow> 
   ('x, 'a, ('rest :: Pordb) * ('b2)) lifting" where
"name_lift_recA_right rec n s =
  (case s of
    SP ls rs \<Rightarrow>
      snd_l o (rec n rs))"

adhoc_overloading name_lift
  name_lift_baseA
  "name_lift_recA_left name_lift"
  "name_lift_recA_right name_lift"

value [nbe]
  "name_lift NA
    (SP NB NA)"

(* next up: we want
   - name
   - schema of output type
   - lifting from input to output
( do we need input type also?)
*)

(* OK... can we do this with liftings? 
   Ideally want to handle associativity on "left side" (i.e. in source/small state type)
*)

(* need a type alias for schem_lift *)

(*
type_synonym ('s1, 's2, 'x, 'a, 'b, 'c) schem_lift =
"('s1 \<Rightarrow> 's2 \<Rightarrow> ('x, 'a, 'b) lifting \<Rightarrow> ('x, 'a, 'c) lifting)"
*)


type_synonym ('s1, 's2, 'x, 'a, 'b) schem_lift =
"('s1 \<Rightarrow> 's2 \<Rightarrow> ('x, 'a, 'b) lifting)"

consts schem_lift ::
  "('s1 :: schem, 's2 :: schem, 'x, 'a, 'b :: Mergeable) schem_lift"

definition schem_lift_baseA ::  "('n :: n_A, 'n, 'x, 'a :: Bogus, 'a) schem_lift" where
"schem_lift_baseA _ _ =
  id_l"

definition schem_lift_baseB ::  "('n :: n_B, 'n, 'x, 'a :: Bogus, 'a) schem_lift" where
"schem_lift_baseB _ _ =
  id_l"

definition schem_lift_baseC ::  "('n :: n_C, 'n, 'x, 'a :: Bogus, 'a) schem_lift" where
"schem_lift_baseC _ _ =
  id_l"

definition schem_lift_baseD ::  "('n :: n_D, 'n, 'x, 'a :: Bogus, 'a) schem_lift" where
"schem_lift_baseD _ _ =
  id_l"

definition schem_lift_baseE ::  "('n :: n_E, 'n, 'x, 'a :: Bogus, 'a) schem_lift" where
"schem_lift_baseE _ _ =
  id_l"

definition schem_lift_prod_recR_A_left ::
  "('n, 'ls, 'x, 'a, 'b2) schem_lift \<Rightarrow>
   ('n :: n_A, ('ls, 'rs :: hasntA) sprod, 'x, 'a, 'b2 * ('rest :: Pordb)) schem_lift" where
"schem_lift_prod_recR_A_left rec n s =
  (case s of
    SP ls rs \<Rightarrow>
      fst_l (rec n ls))"

definition schem_lift_prod_recR_A_right ::
  "('n, 'rs, 'x, 'a, 'b2) schem_lift \<Rightarrow>
   ('n :: n_A, ('ls :: hasntA, 'rs ) sprod, 'x, 'a, ('rest :: Pordb) * ('b2)) schem_lift" where
"schem_lift_prod_recR_A_right rec n s =
  (case s of
    SP ls rs \<Rightarrow>
      snd_l (rec n rs))"

definition schem_lift_prod_recR_B_left ::
  "('n, 'ls, 'x, 'a, 'b2) schem_lift \<Rightarrow>
   ('n :: n_B, ('ls, 'rs :: hasntB) sprod, 'x, 'a, 'b2 * ('rest :: Pordb)) schem_lift" where
"schem_lift_prod_recR_B_left rec n s =
  (case s of
    SP ls rs \<Rightarrow>
      fst_l  (rec n ls))"

definition schem_lift_prod_recR_B_right ::
  "('n, 'rs, 'x, 'a, 'b2) schem_lift \<Rightarrow>
   ('n :: n_B, ('ls :: hasntB, 'rs ) sprod, 'x, 'a, ('rest :: Pordb) * ('b2)) schem_lift" where
"schem_lift_prod_recR_B_right rec n s =
  (case s of
    SP ls rs \<Rightarrow>
      snd_l (rec n rs))"

definition schem_lift_prod_recR_C_left ::
  "('n, 'ls, 'x, 'a, 'b2) schem_lift \<Rightarrow>
   ('n :: n_C, ('ls, 'rs :: hasntC) sprod, 'x, 'a, 'b2 * ('rest :: Pordb)) schem_lift" where
"schem_lift_prod_recR_C_left rec n s =
  (case s of
    SP ls rs \<Rightarrow>
      fst_l  (rec n ls))"

definition schem_lift_prod_recR_C_right ::
  "('n, 'rs, 'x, 'a, 'b2) schem_lift \<Rightarrow>
   ('n :: n_C, ('ls :: hasntC, 'rs ) sprod, 'x, 'a, ('rest :: Pordb) * ('b2)) schem_lift" where
"schem_lift_prod_recR_C_right rec n s =
  (case s of
    SP ls rs \<Rightarrow>
      snd_l (rec n rs))"

definition schem_lift_prod_recR_D_left ::
  "('n, 'ls, 'x, 'a, 'b2) schem_lift \<Rightarrow>
   ('n :: n_D, ('ls, 'rs :: hasntD) sprod, 'x, 'a, 'b2 * ('rest :: Pordb)) schem_lift" where
"schem_lift_prod_recR_D_left rec n s =
  (case s of
    SP ls rs \<Rightarrow>
      fst_l  (rec n ls))"

definition schem_lift_prod_recR_D_right ::
  "('n, 'rs, 'x, 'a, 'b2) schem_lift \<Rightarrow>
   ('n :: n_D, ('ls :: hasntD, 'rs ) sprod, 'x, 'a, ('rest :: Pordb) * ('b2)) schem_lift" where
"schem_lift_prod_recR_D_right rec n s =
  (case s of
    SP ls rs \<Rightarrow>
      snd_l (rec n rs))"

definition schem_lift_prod_recR_E_left ::
  "('n, 'ls, 'x, 'a, 'b2) schem_lift \<Rightarrow>
   ('n :: n_E, ('ls, 'rs :: hasntE) sprod, 'x, 'a, 'b2 * ('rest :: Pordb)) schem_lift" where
"schem_lift_prod_recR_E_left rec n s =
  (case s of
    SP ls rs \<Rightarrow>
      fst_l  (rec n ls))"

definition schem_lift_prod_recR_E_right ::
  "('n, 'rs, 'x, 'a, 'b2) schem_lift \<Rightarrow>
   ('n :: n_E, ('ls :: hasntE, 'rs ) sprod, 'x, 'a, ('rest :: Pordb) * ('b2)) schem_lift" where
"schem_lift_prod_recR_E_right rec n s =
  (case s of
    SP ls rs \<Rightarrow>
      snd_l (rec n rs))"

definition schem_lift_recL ::
  "('s1l, 's2, 'x, 'a1l, 'b2) schem_lift \<Rightarrow>
   ('s1r, 's2, 'x, 'a1r, 'b2) schem_lift \<Rightarrow>
   (('s1l :: schem, 's1r :: schem) sprod, 's2 :: schem, 'x, 
   (('a1l :: Bogus) * ('a1r :: Bogus)), 'b2 :: Mergeable) schem_lift" where
"schem_lift_recL recl recr s1 s2 =
  (case s1 of
    SP s1l s1r \<Rightarrow>
      merge_l (recl s1l s2) (recr s1r s2))"

adhoc_overloading schem_lift 
  "schem_lift_baseA" 
  "schem_lift_baseB"
  "schem_lift_baseC"
  "schem_lift_baseD"
  "schem_lift_baseE"
  "schem_lift_prod_recR_A_left schem_lift"
  "schem_lift_prod_recR_A_right schem_lift"
  "schem_lift_prod_recR_B_left schem_lift"
  "schem_lift_prod_recR_B_right schem_lift"
  "schem_lift_prod_recR_C_left schem_lift"
  "schem_lift_prod_recR_C_right schem_lift"
  "schem_lift_prod_recR_D_left schem_lift"
  "schem_lift_prod_recR_D_right schem_lift"
  "schem_lift_prod_recR_E_left schem_lift"
  "schem_lift_prod_recR_E_right schem_lift"
  "schem_lift_recL schem_lift schem_lift"

(* need more constraints to prevent going down unhappy paths 
   problem is getting confused; instances for a come up when searching for a b
   (or vice versa?)*)

value [nbe] "schem_lift (SP (SP NC NA) NB) (SP NA (SP NC (SP NX NB)))"

(* other needed primitives:
   - option
   - triv
   - prio (here we need to specify some kind of descriptor)
   - sum (left/right)
   - list_hd
   -
   - list_map (?)
   - oalist_map (?)
*)


(* next step. we need to figure out how to thread through constructors. 

*)
(* another concept: what if we recurse left only when we have something other than a name
   on LHS *)

(*
definition schem_lift_prodL ::
  "('s1l :: schem, 's2 :: schem, 'x, 'a, 'bl :: Mergeable, 'c :: Mergeable) schem_lift \<Rightarrow>
   ('s1r :: schem, 's2 :: schem, 'x, 'a, 'br :: Mergeable, 'c :: Mergeable) schem_lift \<Rightarrow>
   (('s1l, 's1r) sprod, 's2, 'x, 'a, ('bl * 'br), 'c) schem_lift" where
"schem_lift_prodL sll slr sp s2 =
  (case sp of
    SP ls rs \<Rightarrow>
      merge_l (sll ls 
*)
(*
consts schem_lift ::
  "('s0  \<Rightarrow> 's2 :: schem \<Rightarrow>
   ('x, 'a, 'b) lifting \<Rightarrow> 
   ('x, 'a, 'c) lifting) \<Rightarrow>
  's1 :: schem \<Rightarrow> 's2 :: schem \<Rightarrow>
  ('x, 'a, 'b :: Mergeable) lifting \<Rightarrow> 
  ('x, 'a, 'c :: Mergeable) lifting"
*)
(* algorithm (no assoc. for now)
   - walk along source
   - if we find a name, we need to find a lifting
   - then use merge to combine; recurse.
*)

(*
definition schem_lift_base ::
  "('s1 :: schem  \<Rightarrow> 's2 :: schem \<Rightarrow>
   ('x, 'a, 'b) lifting \<Rightarrow> 
   ('x, 'a, 'c) lifting) \<Rightarrow>
   's1   \<Rightarrow> 's2 :: schem \<Rightarrow>
   ('x, 'a, 'b :: Mergeable) lifting \<Rightarrow> 
   ('x, 'a, 'c :: Mergeable) lifting" where
"schem_lift_base nl n s =
  nl n s"

(* arguments:
   - schem lift
   - schem lift
   - name lift *)

definition schem_lift_prod ::
  "('s0 :: schem  \<Rightarrow> 's2 :: schem \<Rightarrow>
   ('x, 'a, 'b) lifting \<Rightarrow> 
   ('x, 'a, 'c) lifting) \<Rightarrow>
   ('s0 :: schem  \<Rightarrow> 's2 :: schem \<Rightarrow>
   ('x, 'a, 'b) lifting \<Rightarrow> 
   ('x, 'a, 'c) lifting) \<Rightarrow>
   ('s0 :: schem  \<Rightarrow> 's2 :: schem \<Rightarrow>
   ('x, 'a, 'b) lifting \<Rightarrow> 
   ('x, 'a, 'c) lifting) \<Rightarrow>
   ('s1l, 's1r) sprod \<Rightarrow> 's2 :: schem \<Rightarrow>
   ('x, 'a, 'b :: Mergeable) lifting \<Rightarrow>
   ('x, 'a, 'c :: Mergeable) lifting" where
"schem_lift_prod sll slr nl p s l =
  (case p of
    (ls, rs) \<Rightarrow>
      "
*)
adhoc_overloading schem_lift "schem_lift_base"

value [nbe] "schem_lift name_lift (NA) (NA)"


(* OK, is there a way we can separate out schemas? Maybe typeclass doesn't permit it. *)

(* now we have reified types.
   next step: specify a language of accessors corresponding to lifting stuff

*)

(* another idea: define a type class for each name. then we can try to use inference
   to find descendents with the right name. *)

(* another idea. LiftInto typeclass, where the type parameter is the "output"/"big" type 
LHS/input type is going to be some kind of dummy/reified type that needs to be filled in later*)

(* in fact what we want is a "reified" representation of liftings, that we can then
   convert into a real lifting. this language will have fst, snd, etc. 

so e.g. 

then (i think) we can use an adhoc overloading to denote into the lifting we want
*)


(* OK - we also need 'type-level' names in order to index on *)
  

end