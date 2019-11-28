theory CalcsExample imports View

begin

type_synonym cstate = "int * bool"

datatype calc = 
    CInc
    | CDec
    | CMode

type_synonym 'a seq_syntax = "'a list"


fun calc_semantics :: "calc \<Rightarrow> int * bool \<Rightarrow> int * bool" where
"calc_semantics CInc (i, True) = (i + 1, True)"
| "calc_semantics CInc (i, False) = (i + 2, False)"
| "calc_semantics CDec (i, True) = (i - 1, True)"
| "calc_semantics CDec (i, False) = (i - 2, False)"
| "calc_semantics CMode (i, b) = (i, \<not> b)"

fun seq_semantics :: "'a seq_syntax \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 's \<Rightarrow> 's" where
 "seq_semantics [] f s = s"
| "seq_semantics (h#t) f s =
    seq_semantics t f (f h s)"

definition calc_seq_semantics where
  "calc_seq_semantics s = seq_semantics s calc_semantics"

value "calc_seq_semantics ([CDec, CMode, CInc]) (0, True)"

type_synonym combined = "int * int * bool"

fun inj1m :: "cstate * combined \<Rightarrow> combined" where
"inj1m ((i, b), (i1, i2, b')) = (i, i2, b)"

fun prj1m :: "combined \<Rightarrow> cstate + combined" where
"prj1m (i1, i2, b) = Inl (i1, b)"

fun inj2m :: "cstate * combined \<Rightarrow> combined" where
"inj2m ((i, b), (i1, i2, b')) = (i1, i, b)"

fun prj2m :: "combined \<Rightarrow> cstate + combined" where
"prj2m (i1, i2, b) = Inl (i2, b)"

(* these should satisfy the view laws, but i'm not going to prove it *)
type_synonym combined_syn = "(calc + calc) seq_syntax"

(* in the future we should be able to compose these more nicely *)
fun inj1s :: "calc * combined_syn \<Rightarrow> combined_syn" where
"inj1s (s, l) = (Inl s)#l"

fun prj1s :: "combined_syn \<Rightarrow> calc + combined_syn" where
"prj1s [] = Inr []"
| "prj1s ((Inl h1)#t) = Inl h1"
| "prj1s x = Inr x"

fun inj2s :: "(calc  * combined_syn) \<Rightarrow> combined_syn" where
"inj2s (s, l) = (Inr s)#l"

fun prj2s :: "combined_syn \<Rightarrow> calc + combined_syn" where
"prj2s [] = Inr []"
| "prj2s ((Inr h2)#t) = Inl h2"
| "prj2s x = Inr x"

(*
fun prj2s :: "combined_syn \<Rightarrow> calc_syntax + combined_syn" where
"prj2s (Inr s) = Inl s"
| "prj2s _ = undefined"
*)

(* how are we going to do sequencing though? *)

(* combined semantics, using these primitives *)
(* do we want to fall back to other semantics if the state is not valid? *)
fun combined_semantics_noseq :: "combined_syn \<Rightarrow> combined \<Rightarrow> combined" where
"combined_semantics_noseq sy st =
  (case prj1s sy of
    Inl sy1 \<Rightarrow> (case prj1m st of
                Inl st1 \<Rightarrow> inj1m (calc_semantics sy1 st1, st)
                | _ \<Rightarrow> undefined)
    | _ \<Rightarrow> (case prj2s sy of
              Inl sy2 \<Rightarrow> (case prj2m st of
                              Inl st2 \<Rightarrow> inj2m (calc_semantics sy2 st2, st))))"


fun injc :: "(combined_syn * combined_syn) \<Rightarrow> combined_syn" where
"injc (x, _) = x"


fun prjc :: "combined_syn \<Rightarrow> (combined_syn + combined_syn)" where
"prjc [] = Inr []"
| "prjc (h#t) = Inl t"

value "combined_semantics_noseq ([Inl CDec, Inl CMode, Inr CInc]) (0, 1, True)"

function combined_semantics_fix :: "combined_syn \<Rightarrow> combined \<Rightarrow> combined" where
"combined_semantics_fix sy st =
  (case prjc sy of
    Inl syt \<Rightarrow> 
     combined_semantics_fix syt 
     (case prj1s sy of
          Inl sy1 \<Rightarrow> (case prj1m st of
                        Inl st1 \<Rightarrow> inj1m (calc_semantics sy1 st1, st))
          | _ \<Rightarrow> (case prj2s sy of
                  Inl sy2 \<Rightarrow> (case prj2m st of
                                Inl st2 \<Rightarrow> inj2m (calc_semantics sy2 st2, st))))
    | Inr _ \<Rightarrow> st)"
  by pat_completeness auto
termination combined_semantics_fix
  apply(relation 
     "measure (\<lambda> (csy, csm) .
        case (prjc csy) of
          Inl l \<Rightarrow> length l + 1
          | Inr l' \<Rightarrow> 0)")
   apply(auto)
  apply(case_tac sy, clarsimp) apply(clarsimp)
  apply(auto split: sum.splits)
  apply(case_tac a) apply(clarsimp) apply(clarsimp)
  done

value "combined_semantics_fix ([Inl CDec, Inr CMode, Inr CInc]) (0, 1, True)"


end