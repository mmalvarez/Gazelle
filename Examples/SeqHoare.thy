theory SeqHoare imports "../Hoare/Multistep_Hoare"  "Seq" "../Gensyn_Facts"
begin

(* "local" Hoare rule for sequencing *)

(* idea: we need all the following to impply postcondition for sequencing, given precondition P
   - on entry, P holds
   - when going to first child, P (?) still holds (or, alternately, new P1)
*)

(*

P \<longrightarrow> P0 (or actually, P0 is just P, with path updated)

(* have a predicate for each child to string along the reasoning *)
(* on exit, we need to show exit implies final Q
*)
forall n :: int . n < length l


*)

(* another option we will explore in a bit: have a "list" version for dealing
   with the children *)

(* do we want a "local" one or a full one?
   the nice thing about the local one is we know how to lift it.
*)

(* this is a good step forward but not quite right.
   where it is wrong is that we need to actually be going to the parent.

   also we need to examine whether we are setting xcp correctly in all cases in the implementation of Seq.
*)

(* meaning of xcp: node where this signal _originated_
- empty seq means signal from seq node
- sskip means signal from that node

*)
(* empty = done
   parent = if get_parent returns True, then Q holds on result (Up from current path, parent path is new path)
   done = if get parent returns False, same, but Done instead of parent path
   0: done (on entering, Q should hold on first child)
   H : Done?
   Hfin : Done?
*)

(* Hparent and Hdone need to take into account the possibility that we will
   still have more children to visit. *)

definition is_grpath :: "'a gs_result \<Rightarrow> bool" where
"is_grpath r =
  (case r of
    GRPath _ \<Rightarrow> True
    | _ \<Rightarrow> False)"

lemma SeqStep :

  (* general hypotheses *)
  assumes Hskel : "gs_sk prog = skel"
  assumes Hstate : "\<And> st . P st \<Longrightarrow> (case st of (sk, r, _) \<Rightarrow> (sk = skel \<and> r =  GRPath p))"
  assumes Hget : "gensyn_get prog p = Some (G Sseq l)"

  (* case hypotheses. *)
  (* entering an empty sequence node (going down) *)
  assumes Hemp : "\<And> st . P st \<Longrightarrow> st = (skel, GRPath p, Down) \<Longrightarrow> length l = 0 \<Longrightarrow> 
                         Q (skel, GRPath p, Up p)"

  (* entering a nonempty sequence node (down) *)
  assumes H0 : "\<And> st  . P st \<Longrightarrow>  st = (skel, GRPath p, Down) \<Longrightarrow> 0 < length l \<Longrightarrow> Q (skel, GRPath (p@[0]), Down)"

  (* returning from the final child of a sequence node *)
  assumes Hparent : "\<And> st n p' loc suf . P st \<Longrightarrow> p = p' @ [loc] \<Longrightarrow> 
                                          st = (skel, GRPath p, Up (p@n#suf)) \<Longrightarrow>
                                          length l \<le> n + 1 \<Longrightarrow>
                                          Q (skel, GRPath p', Up p)"

  (* returning from the final child of a sequence node (no parent) *)
  assumes Hdone : "\<And> st n suf . P st \<Longrightarrow> p = [] \<Longrightarrow>  st = (skel, GRPath p, Up ([n]@suf)) \<Longrightarrow>
                                            length l \<le> n + 1 \<Longrightarrow>
                                            Q (skel, GRDone, Up p)"

  (* case when signal is coming from this node *)
  assumes Hself: "\<And> st loc p' . P st \<Longrightarrow> p = p' @ [loc] \<Longrightarrow>  st = (skel, GRPath p, Up p) \<Longrightarrow> 
                 Q (skel, GRPath p', Up p)"

 (* case when signal is coming from this node and no parent*)
  assumes Hself_done : "\<And> st loc . P st \<Longrightarrow> p = [] \<Longrightarrow> st = (skel, GRPath p, Up p) \<Longrightarrow>
  Q (skel, GRDone, Up p)"

  (* we received an invalid signal at this node (i.e., not corresponding to immediate child *)
  assumes Hbadpath : "\<And> st n p' . P st \<Longrightarrow> st = (skel, GRPath p, Up p') \<Longrightarrow> (\<And> suf . p' \<noteq> p @ suf) \<Longrightarrow>
    Q (skel, GRCrash, Up p)"
  (* returning from one child, entering the next *)  
  assumes Hnext : "\<And> st  n suf . P st \<Longrightarrow> st = (skel, GRPath p, Up (p@n#suf)) \<Longrightarrow> n + 1 < length l \<Longrightarrow> Q (skel, GRPath (p@[n+1]), Down)"

  (* if we are not in GRPath state, no-op *)
  assumes Hhalt : "\<And> st res dir . P st \<Longrightarrow> st = (skel, res, dir) \<Longrightarrow> \<not> is_grpath res \<Longrightarrow> Q st"

  shows "(!seq_sem) % {{P}} Sseq {{Q}}"
proof(rule VTI)
  fix st st'
  assume HP  : "P st"
  assume "(! seq_sem) Sseq st st'"
  hence Exec : "seq_sem Sseq st = st'"
    unfolding semprop2_def by simp

  obtain result dir where St :
    "st = (skel, result, dir)" using Hskel Hstate[OF HP] by(cases st; auto)

  show "Q st'"
  proof(cases "is_grpath result")
    case False

    then show ?thesis using Hhalt[OF HP ] Exec  St
      by(cases result; auto simp add: seq_sem_def is_grpath_def)
  next
    case True

    then obtain pd where Psub : "result = GRPath pd"
      by(cases result; auto simp add: is_grpath_def)

    show ?thesis
    proof(cases dir)
      case Down
      show ?thesis
      proof(cases "gensyn_get skel (p @ [0])")
        case None

        have None' : "gensyn_get prog (p@[0]) = None"
          using gs_skel_implies_None None St Hskel by auto

        have "gensyn_get (G Sseq l) [0] = None"
          using gensyn_get_split_None[OF None' Hget] by auto

        hence "length l = 0" by(cases l; auto)

        then show ?thesis using Psub Down Exec St Hemp[OF HP] St Exec Hstate[OF HP] None
          by(simp add: seq_sem_def)
      next
        case (Some sk_node)

        obtain node where Node:  "gensyn_get prog (p@[0]) = Some node" and
          Node_skel : "gs_sk node = sk_node"
          using gs_skel_implies_Some[of prog "(p @ [0])"] St Some unfolding sym[OF Hskel]
          by(auto)
          
        have "gensyn_get (G Sseq l) [0] = Some node"
          using gensyn_get_split[OF Node] Hget by auto

        hence "0 < length l" by(cases l; auto)

        then show ?thesis using Psub Down Exec St H0[OF HP] St Exec Hstate[OF HP] Some
          by(simp add: seq_sem_def)
      qed
    next

      case (Up x2)
      show ?thesis
      proof(cases "get_suffix p x2")
        case None

        then show ?thesis 
        proof(cases "p = x2")
          case False

          have Nosuf : "(\<And>suf. x2 \<noteq> p @ suf)"
          proof
            fix suf
            assume Hcontra : "x2 = p @ suf"

            show False
            proof(cases suf)
              case Nil
              then show ?thesis using False Hcontra by auto
            next
              case (Cons sufh suft)
              then show ?thesis using None get_suffix_spec_conv[of p sufh suft x2] Hcontra by auto
            qed
          qed

          then show ?thesis  using Up None Hbadpath[OF HP _ Nosuf] St Hstate[OF HP] Hskel Psub Exec False
            by(auto simp add: seq_sem_def)
        next
          case True
          then show ?thesis
    
          proof(cases "cp_parent p")
            case None' : None
  
            hence Pnil : "p = []" by(cases p; auto)
  
            then show ?thesis using Up Hself_done[OF HP] St Hstate[OF HP] Hskel Psub None None' Exec True
              by(auto simp add: seq_sem_def)
          next
            case Some' : (Some a)

            obtain loc where "p = a @ [loc]" using gensyn_cp_parent_spec[OF Some'] by auto

            then show ?thesis using Up St Hskel Psub None Some' Exec True Hself[OF HP] Hstate[OF HP]
              by(auto simp add: seq_sem_def)
          qed
        qed
      next
        case (Some suf)

        have Suf : "p @ suf = x2" using get_suffix_spec[OF Some] by auto

        then show ?thesis
        proof(cases suf)
          case Nil
          hence False using get_suffix_nonnil Some by auto
          thus ?thesis by auto
        next
          case (Cons sufh suft)

          have SkGet : "gensyn_get skel p = Some (G () (map gs_sk l))"
            using gs_implies_skel_Some[OF Hget] Hskel by(auto simp add: gs_sk_def)

          show ?thesis 
          proof(cases "gensyn_get skel (p @ [1+sufh])")
            case None' : None

            have Get' : "gensyn_get (G () (map gs_sk l)) [1+sufh] = None"
              using gensyn_get_split_None[OF None'] SkGet by auto

            have Done : "length l \<le> 1 + sufh" using 
              gensyn_get_list_child_None[of "map gs_sk l" "1+sufh"] Get'
              by(auto)

            show ?thesis 
            proof(cases "cp_parent p")
              case None'' : None

              hence Pnil : "p = []" by(cases p; auto)
  
              then show ?thesis using Up St Hskel Psub Some Cons None' None'' Exec Suf
                  Hdone[OF HP] St Hstate[OF HP] Done
                by(auto simp add: seq_sem_def)

            next
              case Some'' : (Some a)

              obtain loc where "p = a @ [loc]" using gensyn_cp_parent_spec[OF Some''] by auto

              then show ?thesis using Up St Hskel Psub Some Cons None' Some'' Exec Suf
                  Hparent[OF HP] St Hstate[OF HP] Done
                by(auto simp add: seq_sem_def)
            qed
          next
            case Some' : (Some desc)

            have Get' : "gensyn_get (G () (map gs_sk l)) [1+sufh] = Some desc"
              using gensyn_get_split[OF Some'] SkGet by auto

            have Next : "1 + sufh < length l" using 
              gensyn_get_list_child_length[of "map gs_sk l" "1+sufh"] Get'
              by(auto)

            show ?thesis using Up St Hskel Psub Some Some' Exec Cons Suf Next
              Hstate[OF HP] Hnext[OF HP, of sufh suft] 
              by(simp add: seq_sem_def)
          qed
        qed
      qed
    qed
  qed
qed

(* is there a nicer way to express this?
   e.g. can we rely on the assumption that control flow is "well bracketed"
   to make a more streamlined statement?
*)

(*

first of all, if there were no control flow weirdness, what would the rule for n-ary Seq look like?

- we would probably want a list rule as a helper
- {P}* [] {P}
  - relating to the location?

- {P} h {Q}
  {Q}* t {R}
------------

  {P}* h#t {R}

------------

{P}* l {Q} \<Longrightarrow> {P} Seq l {Q}

-------------

-------------



*)

(*
lemma SeqH :
  assumes Hget : "gensyn_get prog p = Some (G Sseq l)"
  assumes Hinit : "\<And> st . P st \<Longrightarrow> st = (skel, GPath p, Down)"
  assumes HXs :
    "\<And> n . n < length l \<Longrightarrow>
      Q (skel, GPath (p @ [n]), Down)"
*)
(*

*)
(*
shows "(! seq_sem) % {{P}} Sseq 
                     {{(\<lambda> st . Q st)}}"
*)


end