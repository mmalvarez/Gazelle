theory Syn_Elle imports Main "../Syntax_Utils" "../Gensyn" (*Syn_I*)
begin

(* Elle syntax *)

(* TODO: do we even need to import Syn_I? *)

type_synonym ('llx, 'ljx, 'ljix, 'xb, 'xa) syn_elle =
  "'xb + 'llx + 'ljx + 'ljix + 'xa"

type_synonym ('llx, 'ljx, 'ljix, 'xb, 'xa, 'o) syn_elle_disc =
  "('xb * ('llx \<Rightarrow> 'o) * ('ljx \<Rightarrow> 'o) * ('ljix \<Rightarrow> 'o) * 'xa)"

fun syn_elle_cases ::
  "('llx, 'ljx, 'ljix, 'xb, 'xa) syn_elle \<Rightarrow> 
   ('llx, 'ljx, 'ljix, 'xb \<Rightarrow> 'o, 'xa \<Rightarrow> 'o, 'o) syn_elle_disc \<Rightarrow> 'o" where
  "syn_elle_cases s d = disc5 s d"


definition LLab :: "'llx \<Rightarrow> ('llx, 'ljx, 'ljix, 'xb, 'xa) syn_elle" where
"LLab x = snth2h x"

definition LJump :: "'ljx \<Rightarrow> ('llx, 'ljx, 'ljix, 'xb, 'xa) syn_elle" where
"LJump x = snth3h x"

definition LJumpI :: "'ljix \<Rightarrow> ('llx, 'ljx, 'ljix, 'xb, 'xa) syn_elle" where
"LJumpI x = snth4h x"

type_synonym ('llx ,'xb, 'xa) dat_elle_lab =
  "'xb * 'llx * 'xa"

type_synonym ('ljx ,'xb, 'xa) dat_elle_jump =
  "'xb * 'ljx * 'xa"

type_synonym ('ljix ,'xb, 'xa) dat_elle_jumpi =
  "'xb * 'ljix  * 'xa"

type_synonym
  ('lxb, 'lxa, 'ljb, 'lja, 'ljib, 'ljia, 'xb, 'xa) syn_elle_full =
"((nat, 'lxb, 'lxa) dat_elle_lab,
  (nat, 'ljb, 'lja) dat_elle_jump,
  (nat, 'ljib, 'ljia) dat_elle_jumpi, 'xb, 'xa) syn_elle"

fun get_dat :: "('a * 'b * 'c) \<Rightarrow> 'b" where
"get_dat (a, b, c) = b"

end