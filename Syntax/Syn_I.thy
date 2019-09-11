theory Syn_I imports "../Syntax_Utils"
begin
(* Syntax with instructions *)
(* This serves as a template for what
base-case syntax instatiations look like *)


type_synonym ('i, 'xb, 'xa) syn_i =
  "('xb + 'i + 'xa)"

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

end