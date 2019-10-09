theory Syn_I imports "Syntax"
begin
(* Syntax with instructions *)
(* This serves as a template for what
base-case syntax instatiations look like *)

locale Syn_I = Syn_Sig

(*fixes xi :: "'i itself"
fixes xp :: "'xp itself"
fixes xs :: "'xs itself"*)
(*
fixes rxi :: "'i \<Rightarrow> reified"
fixes dxi :: "reified \<Rightarrow> 'i"
fixes rxp :: "'xp \<Rightarrow> reified"
fixes dxp :: "reified \<Rightarrow> 'xp"
(*
fixes rxs :: "'xs \<Rightarrow> reified"
fixes dxs :: "reified \<Rightarrow> 'xs"
*)
fixes othercases ::
    "char list \<Rightarrow> reified \<Rightarrow> (char list * 'xp * 'xs) option"
*)
begin

print_context

definition C' ::
  "char list \<Rightarrow> reified \<Rightarrow> 
    (char list \<Rightarrow> reified \<Rightarrow> (char list * 'xp * 'xs) option) \<Rightarrow>
    ('i, 'xp, 'xs) mpackf option" where
"C' s xpi others =
  docons ''Inst'' s xpi (rsplit dxp dxi) others"

definition C ::
  "char list \<Rightarrow> reified \<Rightarrow> reified \<Rightarrow> ('i, 'xp, 'xs) mpackf option"
  where
"C s xp i = (C' s (rpair xp i) othercases)"

(* TODO: where to do force? *)
definition LInst :: "'xp \<Rightarrow> 'i \<Rightarrow> ('i, 'xp, 'xs) mpackf" where
"LInst xp i = force (C ''Inst'' (rxp xp) (rxi i))"

end




(*
datatype ('t) reified' =
  RR "'t"

fun do_denote' :: "'a reified' \<Rightarrow> 'a" where
"do_denote' (RR x) = x"

consts reify' :: "'a \<Rightarrow> 'b reified'"

adhoc_overloading reify' RR

consts denote' :: "'a reified' \<Rightarrow> 'b"

adhoc_overloading denote' do_denote'

(* we could even encode type names as strings here. *)
fun denNat :: "('a, 'b) reified \<Rightarrow> nat" where
"denNat (RNat n) = n"
| "denNat _ = undefined"

fun denUnit :: "('a, 'b) reified \<Rightarrow> unit" where
"denUnit (RUnit n) = n"
| "denUnit _ = undefined"

fun denBool :: "('a, 'b) reified \<Rightarrow> bool" where
"denBool (RBool n) = n"
| "denBool _ = undefined"


term "RProd"

consts reify :: "'a \<Rightarrow> ('x, 'y) reified"

adhoc_overloading reify "(\<lambda> x :: nat . RNat x)"
adhoc_overloading reify "(\<lambda> x :: unit . RUnit x)"
adhoc_overloading reify "(\<lambda> x :: bool . RBool x)"
adhoc_overloading reify "(\<lambda> x :: ('t1 * 't2) . (case x of
          (a, b) \<Rightarrow> (RProd (a, b))))"

consts denote :: "('x, 'y) reified \<Rightarrow> 'a"

adhoc_overloading denote denNat
adhoc_overloading denote denUnit
adhoc_overloading denote denBool

fun denProd :: "('a, 'b) reified \<Rightarrow> 'a * 'b" where
  "denProd (RProd (r1, r2)) = (r1, r2)"

adhoc_overloading denote "denProd"

value "denote' (RR True) :: bool"

value "denote (RBool True) :: bool"
*)
(*
definition docons :: "'i itself \<Rightarrow> 
                      'o1 itself \<Rightarrow> 'o2 itself \<Rightarrow>
                  char list \<Rightarrow> char list \<Rightarrow> 
                  'i \<Rightarrow> ('i \<Rightarrow> 'o1) \<Rightarrow> (char list \<Rightarrow> 'i \<Rightarrow> 'o2) \<Rightarrow>
                  ((char list *'o1) + 'o2)" where
"docons ti to1 to2 s1 s2 a fa fb =
  (if s1 = s2 then (Inl (s1, fa a)) else
      Inr (fb s2 a))"
*)



(*
definition LInst :: "'i \<Rightarrow> 'xp \<Rightarrow> ('i, 'xp, 'xs) syn_i" where
"LInst x xp = (Inl x, xp)"
*)
(*
type_synonym ('d, 'bp, 'ap, 'bs, 'as)  syn_i = "('d, 'bp, 'ap, 'bs, 'as) pack"
type_synonym 'i dsyn_i = "'i dpack"

(* there are other discriminator forms, see Alt_Sym.thy.
   i think this is the one we want... *)
type_synonym ('i, 'xb, 'xa, 'o) syn_i_disc =
  "('xb * ('i \<Rightarrow> 'o) * 'xa)"

fun syn_i_cases ::
  "('i, 'xb, 'xa) syn_i \<Rightarrow> ('i, 'xb \<Rightarrow> 'o, 'xa \<Rightarrow> 'o, 'o) syn_i_disc \<Rightarrow> 'o" where
  "syn_i_cases s d = disc3 s d"

(* may run into issues with phantom type variables here *)
definition LInst :: "'i \<Rightarrow> ('i, 'xb, 'xa) syn_i" where
    "LInst x = snth2h x"

(* have a syn_i_dat definition to allow more annotations at the node?
   see seq e.g. *)
*)

end