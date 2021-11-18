theory Auto_Lifter_Sets
  imports Auto_Lifter_Lifters
begin



(* Automation for constructing valid-sets for liftings specified through schema
 * See Auto_Lifter.thy for details on how this works.
 *)

type_synonym ('s1, 's2, 'x, 'b) schem_lift_S =
"('s1 \<Rightarrow> 's2 \<Rightarrow> ('x, 'b) valid_set)"

consts schem_lift_S ::
  "('s1 :: schem, 's2 :: schem, 'x, 'b) schem_lift_S"


(* can't have both base and triv - otherwise we have ambiguous instances.
 * fortunately this isn't much of an issue as they both do the same thing *)
(*
definition schem_lift_S_base_trivA ::
  "('n :: n_A, 'ls, 'x, 'a md_triv) schem_lift_S" where
"schem_lift_S_base_trivA _ _ _ =
  UNIV"
definition schem_lift_S_base_trivB ::
  "('n :: n_B, 'ls, 'x, 'a md_triv) schem_lift_S" where
"schem_lift_S_base_trivB _ _ _ =
  UNIV"
definition schem_lift_S_base_trivC ::
  "('n :: n_C, 'ls, 'x, 'a md_triv) schem_lift_S" where
"schem_lift_S_base_trivC _ _ _ =
  UNIV"
definition schem_lift_S_base_trivD ::
  "('n :: n_D, 'ls, 'x, 'a md_triv) schem_lift_S" where
"schem_lift_S_base_trivD _ _ _ =
  UNIV"
definition schem_lift_S_base_trivE ::
  "('n :: n_E, 'ls, 'x, 'a md_triv) schem_lift_S" where
"schem_lift_S_base_trivE _ _ _ =
  UNIV"
definition schem_lift_S_base_trivF ::
  "('n :: n_F, 'ls, 'x, 'a md_triv) schem_lift_S" where
"schem_lift_S_base_trivF _ _ _ =
  UNIV"
definition schem_lift_S_base_trivG ::
  "('n :: n_G, 'ls, 'x, 'a md_triv) schem_lift_S" where
"schem_lift_S_base_trivG _ _ _ =
  UNIV"
definition schem_lift_S_base_trivH ::
  "('n :: n_H, 'ls, 'x, 'a md_triv) schem_lift_S" where
"schem_lift_S_base_trivH _ _ _ =
  UNIV"
definition schem_lift_S_base_trivI ::
  "('n :: n_I, 'ls, 'x, 'a md_triv) schem_lift_S" where
"schem_lift_S_base_trivI _ _ _ =
  UNIV"
definition schem_lift_S_base_trivJ ::
  "('n :: n_J, 'ls, 'x, 'a md_triv) schem_lift_S" where
"schem_lift_S_base_trivJ _ _ _ =
  UNIV"
definition schem_lift_S_base_trivK ::
  "('n :: n_K, 'ls, 'x, 'a md_triv) schem_lift_S" where
"schem_lift_S_base_trivK _ _ _ =
  UNIV"
*)

definition schem_lift_S_base_idA ::
  "('n :: n_A, 'n, 'x, 'a) schem_lift_S" where
"schem_lift_S_base_idA _ _ _ =
  UNIV"
definition schem_lift_S_base_idB ::
  "('n :: n_B, 'n, 'x, 'a) schem_lift_S" where
"schem_lift_S_base_idB _ _ _ =
  UNIV"
definition schem_lift_S_base_idC ::
  "('n :: n_C, 'n, 'x, 'a) schem_lift_S" where
"schem_lift_S_base_idC _ _ _ =
  UNIV"
definition schem_lift_S_base_idD ::
  "('n :: n_D, 'n, 'x, 'a) schem_lift_S" where
"schem_lift_S_base_idD _ _ _ =
  UNIV"
definition schem_lift_S_base_idE ::
  "('n :: n_E, 'n, 'x, 'a) schem_lift_S" where
"schem_lift_S_base_idE _ _ _ =
  UNIV"
definition schem_lift_S_base_idF ::
  "('n :: n_F, 'n, 'x, 'a) schem_lift_S" where
"schem_lift_S_base_idF _ _ _ =
  UNIV"
definition schem_lift_S_base_idG ::
  "('n :: n_G, 'n, 'x, 'a) schem_lift_S" where
"schem_lift_S_base_idG _ _ _ =
  UNIV"
definition schem_lift_S_base_idH ::
  "('n :: n_H, 'n, 'x, 'a) schem_lift_S" where
"schem_lift_S_base_idH _ _ _ =
  UNIV"
definition schem_lift_S_base_idI ::
  "('n :: n_I, 'n, 'x, 'a) schem_lift_S" where
"schem_lift_S_base_idI _ _ _ =
  UNIV"
definition schem_lift_S_base_idJ ::
  "('n :: n_J, 'n, 'x, 'a) schem_lift_S" where
"schem_lift_S_base_idJ _ _ _ =
  UNIV"
definition schem_lift_S_base_idK ::
  "('n :: n_K, 'n, 'x, 'a) schem_lift_S" where
"schem_lift_S_base_idK _ _ _ =
  UNIV"


(* right-side recursion (prio) *)
definition schem_lift_S_prio_recR ::
  "('n, 'ls, 'x, 'b2 :: Pord) schem_lift_S \<Rightarrow>
   ('n, ('x, 'ls) sprio, 'x, 'b2 md_prio) schem_lift_S" where
"schem_lift_S_prio_recR rec n s =
  (case s of
    SPR f1 f2 s' \<Rightarrow>
      prio_l_S (rec n s'))"

(* right-side recursion (option) *)
definition schem_lift_S_option_recR ::
  "('n, 'ls, 'x, 'b2 :: Pord) schem_lift_S \<Rightarrow>
   ('n, 'ls soption, 'x, 'b2 option) schem_lift_S" where
"schem_lift_S_option_recR rec n s =
  (case s of
    SO s' \<Rightarrow>
      option_l_S (rec n s'))"

(*
(* right-side recursion (oalist) *)
definition schem_lift_S_oalist_recR ::
  "('n, 'ls, 'x, 'b2 :: Pord) schem_lift_S \<Rightarrow>
   ('n, ('x, 'k :: linorder, 'ls) soalist, 'x, ('k, 'b2) oalist) schem_lift_S" where
"schem_lift_S_oalist_recR rec n s =
  (case s of
    SL f1 s' \<Rightarrow>
      oalist_l_S f1 (rec n s'))"
*)

(*
(* right-side recursion (roalist) *)
(* NB we don't allow lifting into the "inr" data of the roalist.
   a separate lifting could allow this. *)
definition schem_lift_S_roalist_recR ::
  "('n, 'ls, 'x, 'b2 :: Pord) schem_lift_S \<Rightarrow>
   ('n, ('x, 'k :: linorder, 'ls) sroalist, 'x, ('k, 'b2, 'z :: Pord) roalist) schem_lift_S" where
"schem_lift_S_roalist_recR rec n s =
  (case s of
    SRL f1 s' \<Rightarrow>
      roalist_l_S f1 (rec n s'))"
*)

definition schem_lift_S_prod_recR_A_left ::
  "('n, 'ls, 'x, 'b2 :: Pord) schem_lift_S =>
   ('n :: n_A, ('ls, 'rs :: hasntA) sprod, 'x, 'b2 * ('rest :: Pordb)) schem_lift_S" where
"schem_lift_S_prod_recR_A_left rec n s =
  (case s of
    SP ls rs =>
      fst_l_S (rec n ls))"

definition schem_lift_S_prod_recR_A_right ::
  "('n, 'rs, 'x, 'b2 :: Pord) schem_lift_S =>
   ('n :: n_A, ('ls :: hasntA, 'rs ) sprod, 'x, ('rest :: Pordb) * ('b2)) schem_lift_S" where
"schem_lift_S_prod_recR_A_right rec n s =
  (case s of
    SP ls rs =>
      snd_l_S (rec n rs))"

definition schem_lift_S_prod_recR_B_left ::
  "('n, 'ls, 'x, 'b2 :: Pord) schem_lift_S =>
   ('n :: n_B, ('ls, 'rs :: hasntB) sprod, 'x, 'b2 * ('rest :: Pordb)) schem_lift_S" where
"schem_lift_S_prod_recR_B_left rec n s =
  (case s of
    SP ls rs =>
      fst_l_S (rec n ls))"

definition schem_lift_S_prod_recR_B_right ::
  "('n, 'rs, 'x, 'b2 :: Pord) schem_lift_S =>
   ('n :: n_B, ('ls :: hasntB, 'rs ) sprod, 'x, ('rest :: Pordb) * ('b2)) schem_lift_S" where
"schem_lift_S_prod_recR_B_right rec n s =
  (case s of
    SP ls rs =>
      snd_l_S (rec n rs))"

definition schem_lift_S_prod_recR_C_left ::
  "('n, 'ls, 'x, 'b2 :: Pord) schem_lift_S =>
   ('n :: n_C, ('ls, 'rs :: hasntC) sprod, 'x, 'b2 * ('rest :: Pordb)) schem_lift_S" where
"schem_lift_S_prod_recR_C_left rec n s =
  (case s of
    SP ls rs =>
      fst_l_S (rec n ls))"

definition schem_lift_S_prod_recR_C_right ::
  "('n, 'rs, 'x, 'b2 :: Pord) schem_lift_S =>
   ('n :: n_C, ('ls :: hasntC, 'rs ) sprod, 'x, ('rest :: Pordb) * ('b2)) schem_lift_S" where
"schem_lift_S_prod_recR_C_right rec n s =
  (case s of
    SP ls rs =>
      snd_l_S (rec n rs))"

definition schem_lift_S_prod_recR_D_left ::
  "('n, 'ls, 'x, 'b2 :: Pord) schem_lift_S =>
   ('n :: n_D, ('ls, 'rs :: hasntD) sprod, 'x, 'b2 * ('rest :: Pordb)) schem_lift_S" where
"schem_lift_S_prod_recR_D_left rec n s =
  (case s of
    SP ls rs =>
      fst_l_S (rec n ls))"

definition schem_lift_S_prod_recR_D_right ::
  "('n, 'rs, 'x, 'b2 :: Pord) schem_lift_S =>
   ('n :: n_D, ('ls :: hasntD, 'rs ) sprod, 'x, ('rest :: Pordb) * ('b2)) schem_lift_S" where
"schem_lift_S_prod_recR_D_right rec n s =
  (case s of
    SP ls rs =>
      snd_l_S (rec n rs))"

definition schem_lift_S_prod_recR_E_left ::
  "('n, 'ls, 'x, 'b2 :: Pord) schem_lift_S =>
   ('n :: n_E, ('ls, 'rs :: hasntE) sprod, 'x, 'b2 * ('rest :: Pordb)) schem_lift_S" where
"schem_lift_S_prod_recR_E_left rec n s =
  (case s of
    SP ls rs =>
      fst_l_S (rec n ls))"

definition schem_lift_S_prod_recR_E_right ::
  "('n, 'rs, 'x, 'b2 :: Pord) schem_lift_S =>
   ('n :: n_E, ('ls :: hasntE, 'rs ) sprod, 'x, ('rest :: Pordb) * ('b2)) schem_lift_S" where
"schem_lift_S_prod_recR_E_right rec n s =
  (case s of
    SP ls rs =>
      snd_l_S (rec n rs))"

definition schem_lift_S_prod_recR_F_left ::
  "('n, 'ls, 'x, 'b2 :: Pord) schem_lift_S =>
   ('n :: n_F, ('ls, 'rs :: hasntF) sprod, 'x, 'b2 * ('rest :: Pordb)) schem_lift_S" where
"schem_lift_S_prod_recR_F_left rec n s =
  (case s of
    SP ls rs =>
      fst_l_S (rec n ls))"

definition schem_lift_S_prod_recR_F_right ::
  "('n, 'rs, 'x, 'b2 :: Pord) schem_lift_S =>
   ('n :: n_F, ('ls :: hasntF, 'rs ) sprod, 'x, ('rest :: Pordb) * ('b2)) schem_lift_S" where
"schem_lift_S_prod_recR_F_right rec n s =
  (case s of
    SP ls rs =>
      snd_l_S (rec n rs))"

definition schem_lift_S_prod_recR_G_left ::
  "('n, 'ls, 'x, 'b2 :: Pord) schem_lift_S =>
   ('n :: n_G, ('ls, 'rs :: hasntG) sprod, 'x, 'b2 * ('rest :: Pordb)) schem_lift_S" where
"schem_lift_S_prod_recR_G_left rec n s =
  (case s of
    SP ls rs =>
      fst_l_S (rec n ls))"

definition schem_lift_S_prod_recR_G_right ::
  "('n, 'rs, 'x, 'b2 :: Pord) schem_lift_S =>
   ('n :: n_G, ('ls :: hasntG, 'rs ) sprod, 'x, ('rest :: Pordb) * ('b2)) schem_lift_S" where
"schem_lift_S_prod_recR_G_right rec n s =
  (case s of
    SP ls rs =>
      snd_l_S (rec n rs))"

definition schem_lift_S_prod_recR_H_left ::
  "('n, 'ls, 'x, 'b2 :: Pord) schem_lift_S =>
   ('n :: n_H, ('ls, 'rs :: hasntH) sprod, 'x, 'b2 * ('rest :: Pordb)) schem_lift_S" where
"schem_lift_S_prod_recR_H_left rec n s =
  (case s of
    SP ls rs =>
      fst_l_S (rec n ls))"

definition schem_lift_S_prod_recR_H_right ::
  "('n, 'rs, 'x, 'b2 :: Pord) schem_lift_S =>
   ('n :: n_H, ('ls :: hasntH, 'rs ) sprod, 'x, ('rest :: Pordb) * ('b2)) schem_lift_S" where
"schem_lift_S_prod_recR_H_right rec n s =
  (case s of
    SP ls rs =>
      snd_l_S (rec n rs))"

definition schem_lift_S_prod_recR_I_left ::
  "('n, 'ls, 'x, 'b2 :: Pord) schem_lift_S =>
   ('n :: n_I, ('ls, 'rs :: hasntI) sprod, 'x, 'b2 * ('rest :: Pordb)) schem_lift_S" where
"schem_lift_S_prod_recR_I_left rec n s =
  (case s of
    SP ls rs =>
      fst_l_S (rec n ls))"

definition schem_lift_S_prod_recR_I_right ::
  "('n, 'rs, 'x, 'b2 :: Pord) schem_lift_S =>
   ('n :: n_I, ('ls :: hasntI, 'rs ) sprod, 'x, ('rest :: Pordb) * ('b2)) schem_lift_S" where
"schem_lift_S_prod_recR_I_right rec n s =
  (case s of
    SP ls rs =>
      snd_l_S (rec n rs))"

definition schem_lift_S_prod_recR_J_left ::
  "('n, 'ls, 'x, 'b2 :: Pord) schem_lift_S =>
   ('n :: n_J, ('ls, 'rs :: hasntJ) sprod, 'x, 'b2 * ('rest :: Pordb)) schem_lift_S" where
"schem_lift_S_prod_recR_J_left rec n s =
  (case s of
    SP ls rs =>
      fst_l_S (rec n ls))"

definition schem_lift_S_prod_recR_J_right ::
  "('n, 'rs, 'x, 'b2 :: Pord) schem_lift_S =>
   ('n :: n_J, ('ls :: hasntJ, 'rs ) sprod, 'x, ('rest :: Pordb) * ('b2)) schem_lift_S" where
"schem_lift_S_prod_recR_J_right rec n s =
  (case s of
    SP ls rs =>
      snd_l_S (rec n rs))"

definition schem_lift_S_prod_recR_K_left ::
  "('n, 'ls, 'x, 'b2 :: Pord) schem_lift_S =>
   ('n :: n_K, ('ls, 'rs :: hasntK) sprod, 'x, 'b2 * ('rest :: Pordb)) schem_lift_S" where
"schem_lift_S_prod_recR_K_left rec n s =
  (case s of
    SP ls rs =>
      fst_l_S (rec n ls))"

definition schem_lift_S_prod_recR_K_right ::
  "('n, 'rs, 'x, 'b2 :: Pord) schem_lift_S =>
   ('n :: n_K, ('ls :: hasntK, 'rs ) sprod, 'x, ('rest :: Pordb) * ('b2)) schem_lift_S" where
"schem_lift_S_prod_recR_K_right rec n s =
  (case s of
    SP ls rs =>
      snd_l_S (rec n rs))"


definition schem_lift_S_merge_recR_A_left ::
  "('n, 'ls, 'x, 'b2) schem_lift_S =>
   ('n :: n_A, ('ls, 'rs :: hasntA) smerge, 'x, 'b2) schem_lift_S" where
"schem_lift_S_merge_recR_A_left rec n s =
  (case s of
    SM ls rs =>
      (rec n ls))"

definition schem_lift_S_merge_recR_A_right ::
  "('n, 'rs, 'x, 'b2) schem_lift_S =>
   ('n :: n_A, ('ls :: hasntA, 'rs) smerge, 'x, 'b2) schem_lift_S" where
"schem_lift_S_merge_recR_A_right rec n s =
  (case s of
    SM ls rs =>
      (rec n rs))"

definition schem_lift_S_merge_recR_B_left ::
  "('n, 'ls, 'x, 'b2) schem_lift_S =>
   ('n :: n_B, ('ls, 'rs :: hasntB) smerge, 'x, 'b2) schem_lift_S" where
"schem_lift_S_merge_recR_B_left rec n s =
  (case s of
    SM ls rs =>
      (rec n ls))"

definition schem_lift_S_merge_recR_B_right ::
  "('n, 'rs, 'x, 'b2) schem_lift_S =>
   ('n :: n_B, ('ls :: hasntB, 'rs) smerge, 'x, 'b2) schem_lift_S" where
"schem_lift_S_merge_recR_B_right rec n s =
  (case s of
    SM ls rs =>
      (rec n rs))"

definition schem_lift_S_merge_recR_C_left ::
  "('n, 'ls, 'x, 'b2) schem_lift_S =>
   ('n :: n_C, ('ls, 'rs :: hasntC) smerge, 'x, 'b2) schem_lift_S" where
"schem_lift_S_merge_recR_C_left rec n s =
  (case s of
    SM ls rs =>
      (rec n ls))"

definition schem_lift_S_merge_recR_C_right ::
  "('n, 'rs, 'x, 'b2) schem_lift_S =>
   ('n :: n_C, ('ls :: hasntC, 'rs) smerge, 'x, 'b2) schem_lift_S" where
"schem_lift_S_merge_recR_C_right rec n s =
  (case s of
    SM ls rs =>
      (rec n rs))"

definition schem_lift_S_merge_recR_D_left ::
  "('n, 'ls, 'x, 'b2) schem_lift_S =>
   ('n :: n_D, ('ls, 'rs :: hasntD) smerge, 'x, 'b2) schem_lift_S" where
"schem_lift_S_merge_recR_D_left rec n s =
  (case s of
    SM ls rs =>
      (rec n ls))"

definition schem_lift_S_merge_recR_D_right ::
  "('n, 'rs, 'x, 'b2) schem_lift_S =>
   ('n :: n_D, ('ls :: hasntD, 'rs) smerge, 'x, 'b2) schem_lift_S" where
"schem_lift_S_merge_recR_D_right rec n s =
  (case s of
    SM ls rs =>
      (rec n rs))"

definition schem_lift_S_merge_recR_E_left ::
  "('n, 'ls, 'x, 'b2) schem_lift_S =>
   ('n :: n_E, ('ls, 'rs :: hasntE) smerge, 'x, 'b2) schem_lift_S" where
"schem_lift_S_merge_recR_E_left rec n s =
  (case s of
    SM ls rs =>
      (rec n ls))"

definition schem_lift_S_merge_recR_E_right ::
  "('n, 'rs, 'x, 'b2) schem_lift_S =>
   ('n :: n_E, ('ls :: hasntE, 'rs) smerge, 'x, 'b2) schem_lift_S" where
"schem_lift_S_merge_recR_E_right rec n s =
  (case s of
    SM ls rs =>
      (rec n rs))"

definition schem_lift_S_merge_recR_F_left ::
  "('n, 'ls, 'x, 'b2) schem_lift_S =>
   ('n :: n_F, ('ls, 'rs :: hasntF) smerge, 'x, 'b2) schem_lift_S" where
"schem_lift_S_merge_recR_F_left rec n s =
  (case s of
    SM ls rs =>
      (rec n ls))"

definition schem_lift_S_merge_recR_F_right ::
  "('n, 'rs, 'x, 'b2) schem_lift_S =>
   ('n :: n_F, ('ls :: hasntF, 'rs) smerge, 'x, 'b2) schem_lift_S" where
"schem_lift_S_merge_recR_F_right rec n s =
  (case s of
    SM ls rs =>
      (rec n rs))"

definition schem_lift_S_merge_recR_G_left ::
  "('n, 'ls, 'x, 'b2) schem_lift_S =>
   ('n :: n_G, ('ls, 'rs :: hasntG) smerge, 'x, 'b2) schem_lift_S" where
"schem_lift_S_merge_recR_G_left rec n s =
  (case s of
    SM ls rs =>
      (rec n ls))"

definition schem_lift_S_merge_recR_G_right ::
  "('n, 'rs, 'x, 'b2) schem_lift_S =>
   ('n :: n_G, ('ls :: hasntG, 'rs) smerge, 'x, 'b2) schem_lift_S" where
"schem_lift_S_merge_recR_G_right rec n s =
  (case s of
    SM ls rs =>
      (rec n rs))"

definition schem_lift_S_merge_recR_H_left ::
  "('n, 'ls, 'x, 'b2) schem_lift_S =>
   ('n :: n_H, ('ls, 'rs :: hasntH) smerge, 'x, 'b2) schem_lift_S" where
"schem_lift_S_merge_recR_H_left rec n s =
  (case s of
    SM ls rs =>
      (rec n ls))"

definition schem_lift_S_merge_recR_H_right ::
  "('n, 'rs, 'x, 'b2) schem_lift_S =>
   ('n :: n_H, ('ls :: hasntH, 'rs) smerge, 'x, 'b2) schem_lift_S" where
"schem_lift_S_merge_recR_H_right rec n s =
  (case s of
    SM ls rs =>
      (rec n rs))"

definition schem_lift_S_merge_recR_I_left ::
  "('n, 'ls, 'x, 'b2) schem_lift_S =>
   ('n :: n_I, ('ls, 'rs :: hasntI) smerge, 'x, 'b2) schem_lift_S" where
"schem_lift_S_merge_recR_I_left rec n s =
  (case s of
    SM ls rs =>
      (rec n ls))"

definition schem_lift_S_merge_recR_I_right ::
  "('n, 'rs, 'x, 'b2) schem_lift_S =>
   ('n :: n_I, ('ls :: hasntI, 'rs) smerge, 'x, 'b2) schem_lift_S" where
"schem_lift_S_merge_recR_I_right rec n s =
  (case s of
    SM ls rs =>
      (rec n rs))"

definition schem_lift_S_merge_recR_J_left ::
  "('n, 'ls, 'x, 'b2) schem_lift_S =>
   ('n :: n_J, ('ls, 'rs :: hasntJ) smerge, 'x, 'b2) schem_lift_S" where
"schem_lift_S_merge_recR_J_left rec n s =
  (case s of
    SM ls rs =>
      (rec n ls))"

definition schem_lift_S_merge_recR_J_right ::
  "('n, 'rs, 'x, 'b2) schem_lift_S =>
   ('n :: n_J, ('ls :: hasntJ, 'rs) smerge, 'x, 'b2) schem_lift_S" where
"schem_lift_S_merge_recR_J_right rec n s =
  (case s of
    SM ls rs =>
      (rec n rs))"

definition schem_lift_S_merge_recR_K_left ::
  "('n, 'ls, 'x, 'b2) schem_lift_S =>
   ('n :: n_K, ('ls, 'rs :: hasntK) smerge, 'x, 'b2) schem_lift_S" where
"schem_lift_S_merge_recR_K_left rec n s =
  (case s of
    SM ls rs =>
      (rec n ls))"

definition schem_lift_S_merge_recR_K_right ::
  "('n, 'rs, 'x, 'b2) schem_lift_S =>
   ('n :: n_K, ('ls :: hasntK, 'rs) smerge, 'x, 'b2) schem_lift_S" where
"schem_lift_S_merge_recR_K_right rec n s =
  (case s of
    SM ls rs =>
      (rec n rs))"


(* left-side recursion (merge)
 * Here we have baked in the assumption that the two
 * valid-sets to be merged are equal (so, WLOG, we choose the left one)
 * TODO: make sure this is a valid assumption
 *)
definition schem_lift_S_recL ::
  "('s1l, 's2, 'x, 'b2) schem_lift_S \<Rightarrow>
   ('s1r, 's2, 'x, 'b2) schem_lift_S \<Rightarrow>
   (('s1l :: schem, 's1r :: schem) sprod, 's2 :: schem, 'x, 'b2 :: Mergeable) schem_lift_S" where
"schem_lift_S_recL recl recr s1 s2 =
  (case s1 of
    SP s1l s1r \<Rightarrow> (\<lambda> syn . (recl s1l s2) syn \<inter> (recr s1r s2) syn))"
(*(\<lambda> syn . (recl s1l s2) syn \<inter> (recr s1r s2) syn)*)


adhoc_overloading schem_lift_S

(*
"schem_lift_S_base_trivA"
"schem_lift_S_base_trivB"
"schem_lift_S_base_trivC"
"schem_lift_S_base_trivD"
"schem_lift_S_base_trivE"
"schem_lift_S_base_trivF"
"schem_lift_S_base_trivG"
"schem_lift_S_base_trivH"
"schem_lift_S_base_trivI"
"schem_lift_S_base_trivJ"
"schem_lift_S_base_trivK"
*)

"schem_lift_S_base_idA"
"schem_lift_S_base_idB"
"schem_lift_S_base_idC"
"schem_lift_S_base_idD"
"schem_lift_S_base_idE"
"schem_lift_S_base_idF"
"schem_lift_S_base_idG"
"schem_lift_S_base_idH"
"schem_lift_S_base_idI"
"schem_lift_S_base_idJ"
"schem_lift_S_base_idK"

"schem_lift_S_option_recR schem_lift_S"
"schem_lift_S_prio_recR schem_lift_S"
(*"schem_lift_S_oalist_recR schem_lift_S"*)
(*"schem_lift_S_roalist_recR schem_lift_S"*)


"schem_lift_S_prod_recR_A_left schem_lift_S"
"schem_lift_S_prod_recR_A_right schem_lift_S"
"schem_lift_S_prod_recR_B_left schem_lift_S"
"schem_lift_S_prod_recR_B_right schem_lift_S"
"schem_lift_S_prod_recR_C_left schem_lift_S"
"schem_lift_S_prod_recR_C_right schem_lift_S"
"schem_lift_S_prod_recR_D_left schem_lift_S"
"schem_lift_S_prod_recR_D_right schem_lift_S"
"schem_lift_S_prod_recR_E_left schem_lift_S"
"schem_lift_S_prod_recR_E_right schem_lift_S"
"schem_lift_S_prod_recR_F_left schem_lift_S"
"schem_lift_S_prod_recR_F_right schem_lift_S"
"schem_lift_S_prod_recR_G_left schem_lift_S"
"schem_lift_S_prod_recR_G_right schem_lift_S"
"schem_lift_S_prod_recR_H_left schem_lift_S"
"schem_lift_S_prod_recR_H_right schem_lift_S"
"schem_lift_S_prod_recR_I_left schem_lift_S"
"schem_lift_S_prod_recR_I_right schem_lift_S"
"schem_lift_S_prod_recR_J_left schem_lift_S"
"schem_lift_S_prod_recR_J_right schem_lift_S"
"schem_lift_S_prod_recR_K_left schem_lift_S"
"schem_lift_S_prod_recR_K_right schem_lift_S"

"schem_lift_S_merge_recR_A_left schem_lift_S"
"schem_lift_S_merge_recR_A_right schem_lift_S"
"schem_lift_S_merge_recR_B_left schem_lift_S"
"schem_lift_S_merge_recR_B_right schem_lift_S"
"schem_lift_S_merge_recR_C_left schem_lift_S"
"schem_lift_S_merge_recR_C_right schem_lift_S"
"schem_lift_S_merge_recR_D_left schem_lift_S"
"schem_lift_S_merge_recR_D_right schem_lift_S"
"schem_lift_S_merge_recR_E_left schem_lift_S"
"schem_lift_S_merge_recR_E_right schem_lift_S"
"schem_lift_S_merge_recR_F_left schem_lift_S"
"schem_lift_S_merge_recR_F_right schem_lift_S"
"schem_lift_S_merge_recR_G_left schem_lift_S"
"schem_lift_S_merge_recR_G_right schem_lift_S"
"schem_lift_S_merge_recR_H_left schem_lift_S"
"schem_lift_S_merge_recR_H_right schem_lift_S"
"schem_lift_S_merge_recR_I_left schem_lift_S"
"schem_lift_S_merge_recR_I_right schem_lift_S"
"schem_lift_S_merge_recR_J_left schem_lift_S"
"schem_lift_S_merge_recR_J_right schem_lift_S"
"schem_lift_S_merge_recR_K_left schem_lift_S"
"schem_lift_S_merge_recR_K_right schem_lift_S"

"schem_lift_S_recL schem_lift_S schem_lift_S"

end
