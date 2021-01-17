theory AutoLift
    imports Main "../Mergeable/Mergeable" LiftInstances "HOL-Library.Adhoc_Overloading"
begin

(* Automated lifting generation, using some typeclass "magic" *)

(* TODO: I don't think we currently support "copying" one field via multiple liftings
   perhaps we cannot do this in general anyway
   worth thinking about though. *)

(* We support a limited (but extensible) set of names. *)
(* Each name N gets a class n_N *)
class n_A

class n_B

class n_C

class n_D

class n_E

class n_X


(* class collecting all "base" names *)
class basename


(* each name N gets a dummy datatype NN *)
datatype nA = NA

datatype nB = NB

datatype nC = NC

datatype nD = ND

datatype nE = NE

datatype nX = NX

instantiation nA :: n_A begin
instance proof qed
end

instantiation nA :: basename begin
instance proof qed
end

instantiation nB :: n_B begin
instance proof qed
end

instantiation nB :: basename begin
instance proof qed
end

instantiation nC :: n_C begin
instance proof qed
end

instantiation nC :: basename begin
instance proof qed
end

instantiation nD :: n_D begin
instance proof qed
end

instantiation nD :: basename begin
instance proof qed
end

instantiation nE :: n_E begin
instance proof qed
end

instantiation nE :: basename begin
instance proof qed
end

instantiation nX :: n_X begin
instance proof qed
end

(* representing datatypes in schema *)
datatype ('a, 'b) sprod = 
  SP "'a" "'b"
(*
datatype 'a striv =
  ST "'a"
*)
(* x is syntax (needed for priority functions) *)
datatype ('x, 'a) sprio =
  SPR "('x \<Rightarrow> nat)" "('x \<Rightarrow> nat \<Rightarrow> nat)" "'a"

(* x is syntax, k is key *)
datatype 'a soption =
  SO "'a"

datatype ('x, 'k, 'a) soalist =
  SL "'x \<Rightarrow> ('k :: linorder) option" "'a"

datatype ('x, 'k, 'a) sroalist =
  SRL "'x \<Rightarrow> ('k :: linorder) option" "'a"

datatype ('x, 'da, 'c, 'a) sfan =
  SFAN "'x \<Rightarrow> 'da \<Rightarrow> 'c" "'a"

(* make identity rather than triv explicit. *)
datatype 'a sid =
  SID "'a"

(* convenience function for injecting existing liftings *)
datatype ('x, 'da, 'db, 'a) sinject =
  SINJ "('x, 'da, 'db) lifting" "'a"

(* dealing with the situation where we need to merge multiple (LHS) fields
   into one (RHS) field. *)

datatype ('a, 'b) smerge =
  SM "'a" "'b"

(* schem is going to include both names (fields) as well as compound structures *)
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
(*
instantiation striv :: (schem) schem begin
instance proof qed
end
*)
instantiation sprio :: (_, schem) schem begin
instance proof qed
end

instantiation soption :: (schem) schem begin
instance proof qed
end

instantiation soalist :: (_, linorder, schem) schem begin
instance proof qed
end

instantiation sroalist :: (_, linorder, schem) schem begin
instance proof qed
end

instantiation smerge :: (schem, schem) schem begin
instance proof qed
end

instantiation sfan :: (_, _, _, schem) schem begin
instance proof qed
end

instantiation sinject :: (_ , _, _, schem) schem
begin
instance proof qed
end

instantiation sid :: (schem) schem
begin
instance proof qed
end

(* declare which names are _not_ in which classes
   (this helps us avoid the need for backtracking, which Isabelle
   typeclasses don't support) *)
class hasntA

class hasntB

class hasntC

class hasntD

class hasntE

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

(* we use X to denote names we don't care about (think "_" in pattern-match) *)
instantiation nX :: "{hasntA, hasntB, hasntC, hasntD, hasntE}" begin
instance proof qed
end

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

(*
instantiation striv :: (hasntA) hasntA begin
instance proof qed
end

instantiation striv :: (hasntB) hasntB begin
instance proof qed
end

instantiation striv :: (hasntC) hasntC begin
instance proof qed
end

instantiation striv :: (hasntD) hasntD begin
instance proof qed
end

instantiation striv :: (hasntE) hasntE begin
instance proof qed
end
*)

instantiation sprio :: (_, hasntA) hasntA begin
instance proof qed
end

instantiation sprio :: (_, hasntB) hasntB begin
instance proof qed
end

instantiation sprio :: (_, hasntC) hasntC begin
instance proof qed
end

instantiation sprio :: (_, hasntD) hasntD begin
instance proof qed
end

instantiation sprio :: (_, hasntE) hasntE begin
instance proof qed
end


instantiation soption :: (hasntA) hasntA begin
instance proof qed
end

instantiation soption :: (hasntB) hasntB begin
instance proof qed
end

instantiation soption :: (hasntC) hasntC begin
instance proof qed
end

instantiation soption :: (hasntD) hasntD begin
instance proof qed
end

instantiation soption :: (hasntE) hasntE begin
instance proof qed
end


instantiation soalist :: (_, linorder, hasntA) hasntA begin
instance proof qed
end

instantiation soalist :: (_, linorder, hasntB) hasntB begin
instance proof qed
end

instantiation soalist :: (_, linorder, hasntC) hasntC begin
instance proof qed
end

instantiation soalist :: (_, linorder, hasntD) hasntD begin
instance proof qed
end

instantiation soalist :: (_, linorder, hasntE) hasntE begin
instance proof qed
end


instantiation sroalist :: (_, linorder, hasntA) hasntA begin
instance proof qed
end

instantiation sroalist :: (_, linorder, hasntB) hasntB begin
instance proof qed
end

instantiation sroalist :: (_, linorder, hasntC) hasntC begin
instance proof qed
end

instantiation sroalist :: (_, linorder, hasntD) hasntD begin
instance proof qed
end

instantiation sroalist :: (_, linorder, hasntE) hasntE begin
instance proof qed
end


instantiation smerge :: (hasntA, hasntA) hasntA begin
instance proof qed
end

instantiation smerge :: (hasntB, hasntB) hasntB begin
instance proof qed
end

instantiation smerge :: (hasntC, hasntC) hasntC begin
instance proof qed
end

instantiation smerge :: (hasntD, hasntD) hasntD begin
instance proof qed
end

instantiation smerge :: (hasntE, hasntE) hasntE begin
instance proof qed
end


instantiation sfan :: (_, _, _, hasntA) hasntA begin
instance proof qed
end

instantiation sfan :: (_, _, _, hasntB) hasntB begin
instance proof qed
end

instantiation sfan :: (_, _, _, hasntC) hasntC begin
instance proof qed
end

instantiation sfan :: (_, _, _, hasntD) hasntD begin
instance proof qed
end

instantiation sfan :: (_, _, _, hasntE) hasntE begin
instance proof qed
end


instantiation sinject :: (_, _, _, hasntA) hasntA begin
instance proof qed
end

instantiation sinject :: (_, _, _, hasntB) hasntB begin
instance proof qed
end

instantiation sinject :: (_, _, _, hasntC) hasntC begin
instance proof qed
end

instantiation sinject :: (_, _, _, hasntD) hasntD begin
instance proof qed
end

instantiation sinject :: (_, _, _, hasntE) hasntE begin
instance proof qed
end

instantiation sid :: (hasntA) hasntA begin
instance proof qed
end

instantiation sid :: (hasntB) hasntB begin
instance proof qed
end

instantiation sid :: (hasntC) hasntC begin
instance proof qed
end

instantiation sid :: (hasntD) hasntD begin
instance proof qed
end

instantiation sid :: (hasntE) hasntE begin
instance proof qed
end



type_synonym ('s1, 's2, 'x, 'a, 'b) schem_lift =
"('s1 \<Rightarrow> 's2 \<Rightarrow> ('x, 'a, 'b) lifting)"

(* id liftings (base case) *)
(*
consts schem_lift ::
  "('s1 :: schem, 's2 :: schem, 'x, 'a, 'b :: Mergeable) schem_lift"
*)
(* YOU ARE HERE
TODOs
- update to use new liftings/signatures (biggest change is that
triv replaces triv o id)
- basic proof automation (probably just a set for auto intros:)
  to make it easier to prove correctness of composite liftings
- ideally it would be awesome to be able to prove
  orthogonality automatically as well.
*)
consts schem_lift ::
  "('s1 :: schem, 's2 :: schem, 'x, 'a, 'b) schem_lift"

(* TODO: can we have a single base case? (Have a typeclass capturing all base names)*)
(*
definition schem_lift_baseA ::  "('n :: n_A, 'n, 'x, 'a :: Bogus, 'a md_triv) schem_lift" where
"schem_lift_baseA _ _ =
  triv_l"

definition schem_lift_baseB ::  "('n :: n_B, 'n, 'x, 'a :: Bogus, 'a md_triv) schem_lift" where
"schem_lift_baseB _ _ =
  triv_l"

definition schem_lift_baseC ::  "('n :: n_C, 'n, 'x, 'a :: Bogus, 'a md_triv) schem_lift" where
"schem_lift_baseC _ _ =
  triv_l"

definition schem_lift_baseD ::  "('n :: n_D, 'n, 'x, 'a :: Bogus, 'a md_triv) schem_lift" where
"schem_lift_baseD _ _ =
  triv_l"

definition schem_lift_baseE ::  "('n :: n_E, 'n, 'x, 'a :: Bogus, 'a md_triv) schem_lift" where
"schem_lift_baseE _ _ =
  triv_l"
*)

(* need to make these 2 base cases (identity and triv) ergonomic *) 
(*
definition schem_lift_base_triv ::  "('n :: basename, 'n, 'x, 'a :: Bogus, 'a md_triv) schem_lift" where
"schem_lift_base_triv _ _ =
  triv_l"

definition schem_lift_base_id ::
  "('n, 'n sid, 'x, 'a :: {Bogus, Pord}, 'a) schem_lift" where
"schem_lift_base_id _ _ =
  id_l"
*)

(* TODO: we could probably reduce these by using the basename typeclass.
   not doing this for now in case it is causing a bug. *)

definition schem_lift_base_trivA ::  "('n :: n_A, 'n, 'x, 'a :: Bogus, 'a md_triv) schem_lift" where
"schem_lift_base_trivA _ _ =
  triv_l"

definition schem_lift_base_trivB ::  "('n :: n_B, 'n, 'x, 'a :: Bogus, 'a md_triv) schem_lift" where
"schem_lift_base_trivB _ _ =
  triv_l"

definition schem_lift_base_trivC ::  "('n :: n_C, 'n, 'x, 'a :: Bogus, 'a md_triv) schem_lift" where
"schem_lift_base_trivC _ _ =
  triv_l"

definition schem_lift_base_trivD ::  "('n :: n_D, 'n, 'x, 'a :: Bogus, 'a md_triv) schem_lift" where
"schem_lift_base_trivD _ _ =
  triv_l"

definition schem_lift_base_trivE ::  "('n :: n_E, 'n, 'x, 'a :: Bogus, 'a md_triv) schem_lift" where
"schem_lift_base_trivE _ _ =
  triv_l"

definition schem_lift_base_idA ::
  "('n :: n_A, 'n sid, 'x, 'a :: {Bogus, Pord}, 'a) schem_lift" where
"schem_lift_base_idA _ _ =
  id_l"

definition schem_lift_base_idB ::
  "('n :: n_B, 'n sid, 'x, 'a :: {Bogus, Pord}, 'a) schem_lift" where
"schem_lift_base_idB _ _ =
  id_l"

definition schem_lift_base_idC ::
  "('n :: n_C, 'n sid, 'x, 'a :: {Bogus, Pord}, 'a) schem_lift" where
"schem_lift_base_idC _ _ =
  id_l"

definition schem_lift_base_idD ::
  "('n :: n_D, 'n sid, 'x, 'a :: {Bogus, Pord}, 'a) schem_lift" where
"schem_lift_base_idD _ _ =
  id_l"

definition schem_lift_base_idE ::
  "('n :: n_E, 'n sid, 'x, 'a :: {Bogus, Pord}, 'a) schem_lift" where
"schem_lift_base_idE _ _ =
  id_l"


(*
(* right-side recursion (triv) *)
(* TODO: do we need to specialize this on a per-name basis? *)
definition schem_lift_triv_recR ::
  "('n, 'ls, 'x, 'a, 'b2 :: Pord) schem_lift \<Rightarrow>
   ('n, 'ls striv, 'x, 'a, 'b2 md_triv) schem_lift" where
"schem_lift_triv_recR rec n s =
  (case s of
    ST s' \<Rightarrow>
      triv_l (rec n s'))"
*)

(* right-side recursion (prio) *)

definition schem_lift_prio_recR ::
  "('n, 'ls, 'x, 'a, 'b2 :: Pord) schem_lift \<Rightarrow>
   ('n, ('x, 'ls) sprio, 'x, 'a, 'b2 md_prio) schem_lift" where
"schem_lift_prio_recR rec n s =
  (case s of
    SPR f1 f2 s' \<Rightarrow>
      prio_l f1 f2 (rec n s'))"

(* right-side recursion (option) *)
definition schem_lift_option_recR ::
  "('n, 'ls, 'x, 'a, 'b2 :: Pord) schem_lift \<Rightarrow>
   ('n, 'ls soption, 'x, 'a, 'b2 option) schem_lift" where
"schem_lift_option_recR rec n s =
  (case s of
    SO s' \<Rightarrow>
      option_l (rec n s'))"

(* right-side recursion (oalist) *)

definition schem_lift_oalist_recR ::
  "('n, 'ls, 'x, 'a, 'b2 :: Pord) schem_lift \<Rightarrow>
   ('n, ('x, 'k :: linorder, 'ls) soalist, 'x, 'a, ('k, 'b2) oalist) schem_lift" where
"schem_lift_oalist_recR rec n s =
  (case s of
    SL f1 s' \<Rightarrow>
      oalist_l f1 (rec n s'))"

(* right-side recursion (roalist) *)

(* NB we don't allow lifting into the "inr" data of the roalist.
   a separate lifting could allow this. *)
definition schem_lift_roalist_recR ::
  "('n, 'ls, 'x, 'a, 'b2 :: Pord) schem_lift \<Rightarrow>
   ('n, ('x, 'k :: linorder, 'ls) sroalist, 'x, 'a, ('k, 'b2, 'z :: Pord) roalist) schem_lift" where
"schem_lift_roalist_recR rec n s =
  (case s of
    SRL f1 s' \<Rightarrow>
      roalist_l f1 (rec n s'))"

(* right-side recursion (prod) *)
definition schem_lift_prod_recR_A_left ::
  "('n, 'ls, 'x, 'a, 'b2 :: Pord) schem_lift \<Rightarrow>
   ('n :: n_A, ('ls, 'rs :: hasntA) sprod, 'x, 'a, 'b2 * ('rest :: Pordb)) schem_lift" where
"schem_lift_prod_recR_A_left rec n s =
  (case s of
    SP ls rs \<Rightarrow>
      fst_l (rec n ls))"

definition schem_lift_prod_recR_A_right ::
  "('n, 'rs, 'x, 'a, 'b2 :: Pord) schem_lift \<Rightarrow>
   ('n :: n_A, ('ls :: hasntA, 'rs ) sprod, 'x, 'a, ('rest :: Pordb) * ('b2)) schem_lift" where
"schem_lift_prod_recR_A_right rec n s =
  (case s of
    SP ls rs \<Rightarrow>
      snd_l (rec n rs))"

definition schem_lift_prod_recR_B_left ::
  "('n, 'ls, 'x, 'a, 'b2 :: Pord) schem_lift \<Rightarrow>
   ('n :: n_B, ('ls, 'rs :: hasntB) sprod, 'x, 'a, 'b2 * ('rest :: Pordb)) schem_lift" where
"schem_lift_prod_recR_B_left rec n s =
  (case s of
    SP ls rs \<Rightarrow>
      fst_l  (rec n ls))"

definition schem_lift_prod_recR_B_right ::
  "('n, 'rs, 'x, 'a, 'b2 :: Pord) schem_lift \<Rightarrow>
   ('n :: n_B, ('ls :: hasntB, 'rs ) sprod, 'x, 'a, ('rest :: Pordb) * ('b2)) schem_lift" where
"schem_lift_prod_recR_B_right rec n s =
  (case s of
    SP ls rs \<Rightarrow>
      snd_l (rec n rs))"

definition schem_lift_prod_recR_C_left ::
  "('n, 'ls, 'x, 'a, 'b2 :: Pord) schem_lift \<Rightarrow>
   ('n :: n_C, ('ls, 'rs :: hasntC) sprod, 'x, 'a, 'b2 * ('rest :: Pordb)) schem_lift" where
"schem_lift_prod_recR_C_left rec n s =
  (case s of
    SP ls rs \<Rightarrow>
      fst_l  (rec n ls))"

definition schem_lift_prod_recR_C_right ::
  "('n, 'rs, 'x, 'a, 'b2 :: Pord) schem_lift \<Rightarrow>
   ('n :: n_C, ('ls :: hasntC, 'rs ) sprod, 'x, 'a, ('rest :: Pordb) * ('b2)) schem_lift" where
"schem_lift_prod_recR_C_right rec n s =
  (case s of
    SP ls rs \<Rightarrow>
      snd_l (rec n rs))"

definition schem_lift_prod_recR_D_left ::
  "('n, 'ls, 'x, 'a, 'b2 :: Pord) schem_lift \<Rightarrow>
   ('n :: n_D, ('ls, 'rs :: hasntD) sprod, 'x, 'a, 'b2 * ('rest :: Pordb)) schem_lift" where
"schem_lift_prod_recR_D_left rec n s =
  (case s of
    SP ls rs \<Rightarrow>
      fst_l  (rec n ls))"

definition schem_lift_prod_recR_D_right ::
  "('n, 'rs, 'x, 'a, 'b2 :: Pord) schem_lift \<Rightarrow>
   ('n :: n_D, ('ls :: hasntD, 'rs ) sprod, 'x, 'a, ('rest :: Pordb) * ('b2)) schem_lift" where
"schem_lift_prod_recR_D_right rec n s =
  (case s of
    SP ls rs \<Rightarrow>
      snd_l (rec n rs))"

definition schem_lift_prod_recR_E_left ::
  "('n, 'ls, 'x, 'a, 'b2 :: Pord) schem_lift \<Rightarrow>
   ('n :: n_E, ('ls, 'rs :: hasntE) sprod, 'x, 'a, 'b2 * ('rest :: Pordb)) schem_lift" where
"schem_lift_prod_recR_E_left rec n s =
  (case s of
    SP ls rs \<Rightarrow>
      fst_l  (rec n ls))"

definition schem_lift_prod_recR_E_right ::
  "('n, 'rs, 'x, 'a, 'b2 :: Pord) schem_lift \<Rightarrow>
   ('n :: n_E, ('ls :: hasntE, 'rs ) sprod, 'x, 'a, ('rest :: Pordb) * ('b2)) schem_lift" where
"schem_lift_prod_recR_E_right rec n s =
  (case s of
    SP ls rs \<Rightarrow>
      snd_l (rec n rs))"

(* right-side recursion (merging multiple fields into one) *)
definition schem_lift_merge_recR_A_left ::
  "('n, 'ls, 'x, 'a, 'b2) schem_lift \<Rightarrow>
   ('n :: n_A, ('ls, 'rs :: hasntA) smerge, 'x, 'a, 'b2) schem_lift" where
"schem_lift_merge_recR_A_left rec n s =
  (case s of
    SM ls rs \<Rightarrow>
      (rec n ls))"

definition schem_lift_merge_recR_A_right ::
  "('n, 'rs, 'x, 'a, 'b2) schem_lift \<Rightarrow>
   ('n :: n_A, ('ls :: hasntA, 'rs) smerge, 'x, 'a, 'b2) schem_lift" where
"schem_lift_merge_recR_A_right rec n s =
  (case s of
    SM ls rs \<Rightarrow>
      (rec n rs))"

definition schem_lift_merge_recR_B_left ::
  "('n, 'ls, 'x, 'a, 'b2) schem_lift \<Rightarrow>
   ('n :: n_B, ('ls, 'rs :: hasntB) smerge, 'x, 'a, 'b2) schem_lift" where
"schem_lift_merge_recR_B_left rec n s =
  (case s of
    SM ls rs \<Rightarrow>
      (rec n ls))"

definition schem_lift_merge_recR_B_right ::
  "('n, 'rs, 'x, 'a, 'b2) schem_lift \<Rightarrow>
   ('n :: n_B, ('ls :: hasntB, 'rs) smerge, 'x, 'a, 'b2) schem_lift" where
"schem_lift_merge_recR_B_right rec n s =
  (case s of
    SM ls rs \<Rightarrow>
      (rec n rs))"

definition schem_lift_merge_recR_C_left ::
  "('n, 'ls, 'x, 'a, 'b2) schem_lift \<Rightarrow>
   ('n :: n_C, ('ls, 'rs :: hasntC) smerge, 'x, 'a, 'b2) schem_lift" where
"schem_lift_merge_recR_C_left rec n s =
  (case s of
    SM ls rs \<Rightarrow>
      (rec n ls))"

definition schem_lift_merge_recR_C_right ::
  "('n, 'rs, 'x, 'a, 'b2) schem_lift \<Rightarrow>
   ('n :: n_C, ('ls :: hasntC, 'rs) smerge, 'x, 'a, 'b2) schem_lift" where
"schem_lift_merge_recR_C_right rec n s =
  (case s of
    SM ls rs \<Rightarrow>
      (rec n rs))"

definition schem_lift_merge_recR_D_left ::
  "('n, 'ls, 'x, 'a, 'b2) schem_lift \<Rightarrow>
   ('n :: n_D, ('ls, 'rs :: hasntD) smerge, 'x, 'a, 'b2) schem_lift" where
"schem_lift_merge_recR_D_left rec n s =
  (case s of
    SM ls rs \<Rightarrow>
      (rec n ls))"

definition schem_lift_merge_recR_D_right ::
  "('n, 'rs, 'x, 'a, 'b2) schem_lift \<Rightarrow>
   ('n :: n_D, ('ls :: hasntD, 'rs) smerge, 'x, 'a, 'b2) schem_lift" where
"schem_lift_merge_recR_D_right rec n s =
  (case s of
    SM ls rs \<Rightarrow>
      (rec n rs))"

definition schem_lift_merge_recR_E_left ::
  "('n, 'ls, 'x, 'a, 'b2) schem_lift \<Rightarrow>
   ('n :: n_E, ('ls, 'rs :: hasntE) smerge, 'x, 'a, 'b2) schem_lift" where
"schem_lift_merge_recR_E_left rec n s =
  (case s of
    SM ls rs \<Rightarrow>
      (rec n ls))"

definition schem_lift_merge_recR_E_right ::
  "('n, 'rs, 'x, 'a, 'b2) schem_lift \<Rightarrow>
   ('n :: n_E, ('ls :: hasntE, 'rs) smerge, 'x, 'a, 'b2) schem_lift" where
"schem_lift_merge_recR_E_right rec n s =
  (case s of
    SM ls rs \<Rightarrow>
      (rec n rs))"


definition schem_lift_fan_recR ::
  "('n, 'ls, 'x, 'a, 'b2 :: Pord) schem_lift \<Rightarrow>
   ('n, ('x, 'a, 'c :: Pord, 'ls) sfan, 'x, 'a, ('c * 'b2)) schem_lift" where
"schem_lift_fan_recR rec n s =
  (case s of
    SFAN f ls \<Rightarrow>
      prod_fan_l f (rec n ls))"


definition schem_lift_inject ::
  " ('n, ('x, 'a, 'b, 'n) sinject, 'x, 'a, 'b ) schem_lift" where
"schem_lift_inject n s =
  (case s of
    SINJ l ls \<Rightarrow> l)"

(* left-side recursion (merge) *)
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

(*
  "schem_lift_base_triv"
  "schem_lift_base_id"
*)

  "schem_lift_base_trivA"
  "schem_lift_base_trivB"
  "schem_lift_base_trivC"
  "schem_lift_base_trivD"
  "schem_lift_base_trivE"

  "schem_lift_base_idA"
  "schem_lift_base_idB"
  "schem_lift_base_idC"
  "schem_lift_base_idD"
  "schem_lift_base_idE"

(*
  "schem_lift_triv_recR schem_lift"
*)
  "schem_lift_option_recR schem_lift"

  "schem_lift_prio_recR schem_lift"

  "schem_lift_oalist_recR schem_lift"

  "schem_lift_roalist_recR schem_lift"

  "schem_lift_fan_recR schem_lift"

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

  "schem_lift_merge_recR_A_left schem_lift"
  "schem_lift_merge_recR_A_right schem_lift"
  "schem_lift_merge_recR_B_left schem_lift"
  "schem_lift_merge_recR_B_right schem_lift"
  "schem_lift_merge_recR_C_left schem_lift"
  "schem_lift_merge_recR_C_right schem_lift"
  "schem_lift_merge_recR_D_left schem_lift"
  "schem_lift_merge_recR_D_right schem_lift"
  "schem_lift_merge_recR_E_left schem_lift"
  "schem_lift_merge_recR_E_right schem_lift"

  "schem_lift_recL schem_lift schem_lift"

  "schem_lift_inject"


(* convenience abbreviations for priorities *)
abbreviation SPR0 where
"SPR0 x \<equiv>
  SPR (\<lambda> _ . 0) (\<lambda> _ _ . 0) x"

abbreviation SPRK where
"SPRK x \<equiv>
  SPR (\<lambda> _ . 0) (\<lambda> _ z . z) x"

abbreviation SPRI where
"SPRI x \<equiv>
  SPR (\<lambda> _ . 0) (\<lambda> _ z . 1 + z) x"

abbreviation SPRIN where
"SPRIN n x \<equiv>
  SPR (\<lambda> _ . n) (\<lambda> _ z . n + z) x"

(* NB: differs from prio_l_case_inc behavior *)
abbreviation SPRC where
"SPRC f x \<equiv>
  SPR (\<lambda> s . f s) (\<lambda> s z . (f s) + z) x"

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