theory I_Semantics imports "Gensyn_Semantics" "../Syntax/Syn_I"
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

locale I_Semantics_Sig = Syn_I +
  fixes xr :: "'rs itself"
  fixes i_sem :: "'a \<Rightarrow> 'mstate => 'mstate \<Rightarrow> bool"

locale I_Semantics = I_Semantics_Sig 
begin
print_context

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

inductive x_sem_i :: "  ('a, 'b, 'c) mpackf \<Rightarrow> 
                         'e \<Rightarrow>
                         'e \<Rightarrow>
                          childpath \<Rightarrow> ('a, 'b, 'c) mpackf gensyn \<Rightarrow> 
                          ('d) gs_result \<Rightarrow> bool" where
"i_sem i m m' \<Longrightarrow> x_sem_i (LInst xp i) m m' cp t GRUnhandled"

(* We still need a way to handle different kinds of gs results *)

(* key thing here: we are not actually descending into recursive nodes
as this would require a recursive semantics; we use nosem *)


end


(* this seems like a bad idea unless we can make things work out
   when we combine together multiple locales *)
(*
sublocale Gensyn_Semantics_I \<subseteq> Gensyn_Semantics_Base_Sig
  where base_sem = i_base_sem
  done
*)


(* testing out sublocales *)
(* i think the problem with this is that we cannot further
sub-locale-ize I_Semantics *)



fun calc_sem :: "calc \<Rightarrow> nat \<Rightarrow> nat" where
"calc_sem (AccAdd x) n = x + n"
| "calc_sem (AccSub x) n = x - n"
| "calc_sem (AccReset) _ = 42"

inductive calc_semb :: "calc \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"\<And> c n n' . calc_sem c n = n' \<Longrightarrow> calc_semb c n n'"

print_locale I_Semantics

(*
interpretation I_Semantics_Calc :
  I_Semantics
  reify denote reify denote
      bail "TYPE(unit)" calc_semb
  done


interpretation Gensyn_Semantics_Calc :
  Gensyn_Semantics "TYPE(unit)" _ I_Semantics_Calc.x_sem_i
  done
*)

locale Gensyn_Base_Oneshot =
  fixes ms :: "'mstate itself"
  fixes x_sem :: "'x \<Rightarrow>
                           'mstate \<Rightarrow>
                           'mstate \<Rightarrow>
                           childpath \<Rightarrow> ('x) gensyn \<Rightarrow> 
                           ('xrs) gs_result \<Rightarrow> bool"
begin

inductive x_sem_oneshot :: "'x \<Rightarrow> 
                           'mstate \<Rightarrow>
                           'mstate \<Rightarrow>
                           childpath \<Rightarrow> ('x) gensyn \<Rightarrow> 
                           ('xrs) gs_result \<Rightarrow> bool"
  where
"x_sem x m m' cp t GRUnhandled \<Longrightarrow>
 x_sem_oneshot x m m' cp t GRDone"

| "x_sem x m m' cp t res \<Longrightarrow>
  x_sem_oneshot x m m' cp t res"

end

print_locale! I_Semantics


locale I_Semantics_Oneshot = I_Semantics

print_locale! I_Semantics_Oneshot

sublocale I_Semantics_Oneshot \<subseteq> Gensyn_Base_Oneshot
  where x_sem = x_sem_i
  done
  

sublocale I_Semantics_Oneshot \<subseteq> Gensyn_Semantics
  where x_sem = x_sem_oneshot
  done

print_locale! I_Semantics_Oneshot


global_interpretation Gensyn_Semantics_Calc_Oneshot? :
  I_Semantics_Oneshot reify denote reify denote bail "TYPE(unit)" calc_semb
  done

term "Gensyn_Semantics_Calc_Oneshot.LInst"

term gensyn_sem

lemma testout1 : "gensyn_sem 
    (G (LInst () AccReset) []) [] 0 42"
  apply(rule gensyn_sem.intros) apply(auto)
  apply(rule x_sem_oneshot.intros)
  apply(rule I_Semantics.x_sem_i.intros)
  apply(rule calc_semb.intros)
  apply(auto)
  done

end