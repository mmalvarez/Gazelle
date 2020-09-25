theory CalcsExample imports ViewRef5 "../Gensyn" "../Semantics/Gensyn_Semantics" "../Semantics/Seq_Semantics"

begin


datatype calc = 
    CInc
    | CDec
    | Jnzero "childpath"

type_synonym seq = "unit"

(* maybe childpath does not need to be an option here. *)
type_synonym cstate = "int * childpath option * nat"
type_synonym sstate = "childpath option * nat"

fun calc_semantics :: "calc \<Rightarrow> (cstate) \<Rightarrow> (cstate)" where
"calc_semantics CInc (i, cpo, _)  = (i + 1, (cpo, 0))"
| "calc_semantics CDec (i, cpo, _)  = (i - 1, (cpo, 0))"
| "calc_semantics (Jnzero cp') (i, (Some cp), _) =
  (if i \<noteq> 0 then (i, (Some cp', 2))
   else (i, (Some cp, 0)))"
| "calc_semantics (Jnzero cp') (i, (None), _) = (i, None, 0)"

fun seq_semantics :: 
    "'a gensyn \<Rightarrow> unit \<Rightarrow> sstate \<Rightarrow> sstate" where
"seq_semantics g () (Some cp, n) = (gensyn_cp_next g cp, 1)"
| "seq_semantics g () (None, n) = (None, 1)"

fun cstate_leq :: "cstate \<Rightarrow> cstate \<Rightarrow> bool" where
"cstate_leq (i1, c1, n1) (i2, c2, n2) =
 (i1 = i2 \<and>
  (if n1 = n2 then c1 = c2
   else n1 < n2))"

(* one very hacky fix for monotonicity: just keep on incrementing the
   value of n. but this seems terrible. somehow though it seems like we need to have
   a dependence of the output value of n on the input value. *)
(* i think we can use a list of natural numbers and just drop the tail every time.
   since we only seem to need the previous one. *)

type_synonym lang = "calc + seq"

fun prjs1 :: "lang \<Rightarrow> calc + lang" where
"prjs1 (Inl c) = Inl c"
| "prjs1 x = Inr x"

fun injs1 :: "calc \<Rightarrow> lang" where
"injs1 c = Inl c"

fun prjs2 :: "lang \<Rightarrow> seq + lang" where
"prjs2 (Inr s) = Inl s"
| "prjs2 _ = Inl ()"

fun injs2 :: "seq \<Rightarrow> lang \<Rightarrow> lang" where
"injs2 _ l = l"

(* cstate (calc state) is also the combined state *)

fun prj1 :: "cstate \<Rightarrow> cstate + cstate" where
"prj1 cs = Inl cs"

fun inj1 :: "cstate \<Rightarrow> cstate \<Rightarrow> cstate" where
"inj1 cs cs' = cs"

fun prj2 :: "cstate \<Rightarrow> sstate + cstate" where
"prj2 (i, c, n) = Inl (c, n)"

fun inj2 :: "sstate \<Rightarrow> cstate \<Rightarrow> cstate" where
"inj2 (c', n') (i, c, n) =
  (if n' > n then (i, c', n')
   else (i, c, n))"

fun x_sem' :: "lang \<Rightarrow> cstate \<Rightarrow> childpath \<Rightarrow> (lang option) gensyn \<Rightarrow> (cstate * unit gs_result)" where
"x_sem' l cst _ g =
  (case prjs1 l of
    Inl c \<Rightarrow> (case prj1 cst of
              Inr _ \<Rightarrow> undefined
              | Inl cst' \<Rightarrow>  let c1 = inj1 (calc_semantics c cst') cst in
                  (case prjs2 l of
                     _ \<Rightarrow> (case prj2 c1 of
                        Inr _ \<Rightarrow> undefined
                        | Inl c1' \<Rightarrow> let c2 = inj2 (seq_semantics g () c1') c1 in
                          (case c2 of
                            (_ , Some cp', _) \<Rightarrow> (c2, GRPath cp')
                            | _ \<Rightarrow> (c2, GRDone))))))"

definition x_sem :: "lang \<Rightarrow> cstate \<Rightarrow> cstate \<Rightarrow> childpath \<Rightarrow> (lang option) gensyn \<Rightarrow> unit gs_result \<Rightarrow> bool" where
"x_sem l c c' cp g r \<equiv>
  (x_sem' l c cp g = (c', r))"

interpretation CSem :
  Gensyn_Semantics x_sem
  done

abbreviation test :: "lang gensyn" where
"test \<equiv> G (Inr ()) [G (Inl CInc) [], G (Inl CInc) [], G (Inl CInc) []]"

lemma test_lem :
  "CSem.gensyn_sem test [0] (0, Some [0], 0) (3, None, 1)"

  apply(rule_tac CSem.gensyn_sem.intros(2))
    apply(simp) apply(simp add: CSem.x_sem_def)
   apply(simp add:x_sem_def)

  apply(rule_tac CSem.gensyn_sem.intros(2))
  apply(simp)
   apply(simp add: CSem.x_sem_def)
   apply(simp add:x_sem_def)

    apply(rule_tac CSem.gensyn_sem.intros(1))
  apply(simp)
   apply(simp add: CSem.x_sem_def)
  apply(simp add:x_sem_def)
  done

abbreviation test2 :: "lang gensyn" where
"test2 \<equiv> G (Inr ()) [G (Inl CDec) [], G (Inl (Jnzero [0])) [], G (Inl CInc) []]"

lemma test_lem2 :
  "CSem.gensyn_sem test2 [0] (2, Some [0], 0) (1, None, 1)"

  apply(rule_tac CSem.gensyn_sem.intros(2))
    apply(simp) apply(simp add: CSem.x_sem_def)
   apply(simp add:x_sem_def)


  apply(rule_tac CSem.gensyn_sem.intros(2))
    apply(simp) apply(simp add: CSem.x_sem_def)
   apply(simp add:x_sem_def)


  apply(rule_tac CSem.gensyn_sem.intros(2))
    apply(simp) apply(simp add: CSem.x_sem_def)
   apply(simp add:x_sem_def)


  apply(rule_tac CSem.gensyn_sem.intros(2))
    apply(simp) apply(simp add: CSem.x_sem_def)
   apply(simp add:x_sem_def)


    apply(rule_tac CSem.gensyn_sem.intros(1))
   apply(simp)
   apply(simp add: CSem.x_sem_def x_sem_def)

  done

(*
fun prj2s :: "combined_syn \<Rightarrow> calc_syntax + combined_syn" where
"prj2s (Inr s) = Inl s"
| "prj2s _ = undefined"
*)

(* how are we going to do sequencing though? *)

(*
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
*)

end