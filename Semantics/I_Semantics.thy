theory I_Semantics imports "Gensyn_Semantics_TypeParam" "../Syntax/Syn_I"
begin

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

locale I_Semantics_Sig =
  fixes xr :: "'rs itself"
  fixes ms :: "'mstate itself"
  fixes i_sem :: "'i \<Rightarrow> 'mstate => 'mstate \<Rightarrow> bool"


locale I_Semantics = I_Semantics_Sig 
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

print_context

inductive i_base_sem :: "'g \<Rightarrow>
                         ('c, 'xb, 'xa) syn_i \<Rightarrow> 
                         'b \<Rightarrow>
                         'b \<Rightarrow>
                          childpath \<Rightarrow> (('c, 'xb, 'xa) syn_i, 'r, 'g) gensyn \<Rightarrow> 
                          ('a) gs_result \<Rightarrow> bool" where
"i_sem i m m' \<Longrightarrow> i_base_sem g (LInst i) m m' cp sk GRUnhandled"

(* We still need a way to handle different kinds of gs results *)

(* key thing here: we are not actually descending into recursive nodes
as this would require a recursive semantics; we use nosem *)


end


locale Gensyn_Semantics_I = I_Semantics 

(* this seems like a bad idea unless we can make things work out
   when we combine together multiple locales *)
sublocale Gensyn_Semantics_I \<subseteq> Gensyn_Semantics_Base_Sig
  where base_sem = i_base_sem
  done


locale RecSem_Test

sublocale RecSem_Test \<subseteq> Gensyn_Semantics_Rec_SigO
  where rec_sem = nosem_rec_sem
  done

print_locale! RecSem_Test

(* how can we fuse a base and rec sem together in a modular/separated way?
can we?*)

locale Gensyn_Semantics_Full_I' = Gensyn_Semantics_I

sublocale Gensyn_Semantics_Full_I' \<subseteq> RecSem_Test
  done

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
"\<And> c n n' . calc_sem c n = n' \<Longrightarrow> calc_semb c n n'"

interpretation I_Semantics_Calc :
  I_Semantics "TYPE(unit)" _ calc_semb
  done


interpretation Gensyn_Semantics_Calc :
  Gensyn_Semantics "TYPE(unit)" _ I_Semantics_Calc.i_base_sem nosem_rec_sem
  done


locale Gensyn_Base_Override_Unhandled =
  fixes base_sem :: "'g \<Rightarrow> 
                          'b \<Rightarrow> 
                           'mstate \<Rightarrow>
                           'mstate \<Rightarrow>
                           childpath \<Rightarrow> ('b, 'r, 'g) gensyn \<Rightarrow> 
                           ('xrs) gs_result \<Rightarrow> bool"
begin

inductive base_sem_done :: "'g \<Rightarrow> 
                          'b \<Rightarrow> 
                           'mstate \<Rightarrow>
                           'mstate \<Rightarrow>
                           childpath \<Rightarrow> ('b, 'r, 'g) gensyn \<Rightarrow> 
                           ('xrs) gs_result \<Rightarrow> bool"
  where
"base_sem g b m m' cp t GRUnhandled \<Longrightarrow>
 base_sem_done g b m m' cp t GRDone"

| "base_sem g b m m' cp t res \<Longrightarrow>
  base_sem_done g b m m' cp t res"

end

locale I_Semantics_Done = Gensyn_Base_Override_Unhandled


sublocale I_Semantics \<subseteq> Gensyn_Base_Override_Unhandled
  where base_sem = i_base_sem
  done
  

sublocale Gensyn_Semantics_Full_I' \<subseteq> Gensyn_Semantics
  where base_sem = base_sem_done
  and rec_sem = rec_semO
  done

interpretation Gensyn_Semantics_Full_Calc :
  Gensyn_Semantics_Full_I' "TYPE(unit)" _ calc_semb
  done

term Gensyn_Semantics_Calc.gensyn_sem

lemma testout1 : "Gensyn_Semantics_Full_Calc.gensyn_sem (GBase () (LInst AccReset)) [] 0 42"
  apply(rule Gensyn_Semantics_Full_Calc.gensyn_sem.intros) apply(auto)
  apply(rule Gensyn_Base_Override_Unhandled.base_sem_done.intros)
  apply(rule I_Semantics.i_base_sem.intros)
  apply(rule calc_semb.intros)
  apply(auto)
  done

end