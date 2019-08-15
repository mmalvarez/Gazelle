theory I_Semantics imports "Gensyn_Semantics" "../Syntax/Syn_I"
begin

(* Do we interpret or extend?
sublocale? 
use rewrites to change base_sem and rec_sem?
should this have trivial control flow, or allow insts
to do weird control flow things?
*)
(* Do we want both a regular and exec? i think so *)

(* options

(idea: is generic gensym_sem the "top" or "bottom"
element of our "lattice" of semantics?)

1. take just i_sem. do semantics for gensyms extending
instruction sym, but return None on unknown ones
- rely on being "downcalled" from higher levels

2. take a gensym semantics and override it in the
case of instructions
- "upcall" in the case of unknown instructions
- what if higher levels impose restrictions on
instructions?
  - could use explicit subtyping...
eed

*)

(* want "a gensyn that includes at least a sym_i" *)

(* this doesn't work, need gensyn tree *)

locale I_Semantics = 
  fixes i_sem :: "'i \<Rightarrow> 'mstate => 'mstate \<Rightarrow> bool"

begin

(* 2 approaches.
   approach 1: i_semantics builds a gensym semantics "from nothing"
   if instruction execution fails, we halt.

   approach 2: i_semantics takes an existing gensym semantics
   and "adds in" instructions.

   approach 1 is better because it allows the _user_ to later define
   approach 2 style semantics (mixins)
*)

(* question: dealing with interactions between global parameters
   and other things?
  sized insts?
*)

(* we can probably generalize this, by using unknown type parameters
  for everything, but this may not be necessary *)

(* we can also probably generalize over result/error types if we really
   want *)
(* TODO make sure this is a general enough type  in terms of
where quantifiers are*)

(* we need some way of selecting the next instruction
this depends on the kind of parent node we have
do we need another extension point to allow for this?. *)

inductive i_base_sem :: "'g \<Rightarrow> 
                         ('i, 'xb, 'xa) syn_i \<Rightarrow> 
                         'mstate \<Rightarrow>
                         'mstate \<Rightarrow>
                          childpath \<Rightarrow> (('i, 'xb, 'xa) syn_i, 'r, 'g) gensyn \<Rightarrow> 
                          ('xrs) gs_result \<Rightarrow> bool" where
"i_sem i m m' \<Longrightarrow> i_base_sem g (LInst i) m m' cp sk GRUnhandled"

(* We still need a way to handle different kinds of gs results *)

(* key thing here: we are not actually descending into recursive nodes
as this would require a recursive semantics; we use nosem *)

interpretation Gensyn_Semantics_I :
  Gensyn_Semantics i_base_sem nosem_rec_sem
  done

end

print_locale Gensyn_Semantics

(* testing out sublocales *)
(* i think the problem with this is that we cannot further
sub-locale-ize I_Semantics *)

(* test - small programming language for arithmetic *)
datatype calc =
  AccAdd nat
  | AccSub nat
  | AccReset

fun calc_sem :: "calc \<Rightarrow> nat \<Rightarrow> nat" where
"calc_sem (AccAdd x) n = x + n"
| "calc_sem (AccSub x) n = x - n"
| "calc_sem (AccReset) _ = 42"

inductive calc_semb :: "calc \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"calc c n = n' \<Longrightarrow> calc_semb c n n'"

interpretation I_Semantics_Calc :
  I_Semantics calc_semb
  done
print_theory
print_locale I_Semantics

(*
interpretation Gensyn_Semantics_Calc :
  Gensyn_Semantics I_Semantics_Calc.i_base_sem nosem_rec_sem
  done
*)

end