theory Lambda
  imports Main "../../MergeableTc/MergeableRAlist"
          "../../Gensyn" "../../Semantics/Gensyn_Sem" "../../Gensyn_Descend" "../../MergeableTc/Mergeable" "../../MergeableTc/MergeableInstances"
          "../../Lifting/LiftUtils" "../../Lifting/LiftInstances" "../Seq"


begin


(* lambda calculus 
   need to deal with renaming? i think the stack
   takes care of this.
*)
datatype syn =
  Sapp
  | Sabs "String.literal"
  | Svar "String.literal"
  | Sskip 

instantiation roalist :: (linorder, _, _) Bogus begin
definition roalist_bogus :
"bogus = (roa_empty :: ('a :: linorder, 'b, 'c) roalist)"
instance proof qed
end

(* idea: we separate concerns here. so inner data doesn't
   need to show up in this specification (can merge in) *)
type_synonym valu = unit
type_synonym env = "(String.literal, valu, (childpath * String.literal)) roalist"

(* environment needs to know about name bindings. *)

(* binding name + code pointer + environment *)
type_synonym clos = "childpath * String.literal * env"

(* elements of SEC state:
   - S = list of values
   - E = environment
   - C = flag (representing special "ap" symbol) and control stack
   - last field of SECD (bool) is a flag saying whether we should halt. *)

type_synonym sec = "(valu + clos) list * env * (childpath * dir) list"

type_synonym secd = "gensyn_skel * sec * sec list * bool"

(* idea: we are pulling the outermost control element to the top level
   since it is going to be shared with the gensyn evaluator *)
type_synonym secd_full = "(gensyn_skel * unit gs_result) * secd"

(* invariant: syn will always be at location given by top control stack element *)
(* down or up after applying? *)
(* TODO: we need to finesse how we are handling code pointers in the environment.
   this is still not quite right. *)

(* TODO: factor out gensyn_skel (not doing this right now as it may become useful here *)
definition secd_sem :: "syn \<Rightarrow> secd \<Rightarrow> secd" where
"secd_sem x st =
  (case st of 
    (g, _, _, True) \<Rightarrow> st
    | (g, (s, e, (cp, dr)#c'), d, b) \<Rightarrow>
      (case x of
        Sskip \<Rightarrow> st
        | Sapp \<Rightarrow> (case dr of
                   Down \<Rightarrow> (g, (s, e, ((cp @ [1]), Down)#
                                  ((cp @ [0]), Down)#
                                  ((cp, (Up []))#c')), d, b)
                  | Up xcp \<Rightarrow> (case s of (Inr (code, name, env))#arg#s' \<Rightarrow> 
                              (g, ( []
                               , (case arg of
                                  Inl val \<Rightarrow> (roalist_update_v name val env)
                                  | Inr (code', name', env') \<Rightarrow> (roalist_update_clos name (Some (code', name')) env' env))
                               , [(code, Down)])
                              , (s', e, c')#d, b))
                  )
        | Svar v \<Rightarrow> (g, ( (case roalist_get e v of
                          Some (Inl val) \<Rightarrow> Inl val # s
                          | Some (Inr (Some (cp', name'), env')) \<Rightarrow>
                            Inr (cp', name', env') # s)
                      , e
                      , c')
                      , d
                      , b)
          | Sabs v \<Rightarrow>
                (g, ( Inr (cp @ [0], v, e)#s
                  , e
                  , c')
                  , d
                  , b))
      | (g, (h#s, e, []), (ds, de, dc)#dt, b) \<Rightarrow>
         (g, (h#ds, de, dc), dt, b)
      | (g, (s, e, []), [], b) \<Rightarrow> (g, (s, e, []), [], True) \<comment> \<open> done, need to signal \<close>
      )"

(* problem - need to figure out best way to signal "done" *)

(* i think we are signaling exit too early - not enough time to clean up stack. *)
fun dump_get_next_path :: "sec list \<Rightarrow> (childpath * dir) option" where
"dump_get_next_path [] = None"
| "dump_get_next_path ((s, e, chdir#ct)#dt) = Some chdir"
| "dump_get_next_path ((s, e, [])#dt) = dump_get_next_path dt"

(*
definition secd_gsx_info :: "syn \<Rightarrow> secd \<Rightarrow> (gensyn_skel * unit gs_result)" where
"secd_gsx_info syn st =
  (case st of
    (g, (s, e, (cp, _)#c'), d, b) \<Rightarrow> (g, GRPath cp)
    | (g, (s, e, []), d) \<Rightarrow>
      (case dump_get_next_path d of
        None \<Rightarrow> (g, GRDone)
        | Some (cp, _) \<Rightarrow> (g, GRPath cp)))"
*)

(* TODO: this program-counter handling is rather odd; it maintains a sort of "designated
   nowhere-node" that could cause very strange interactions with other sub-languages 
   ugh... no this doesn't work.*)
definition secd_gsx_info :: "syn \<Rightarrow> secd \<Rightarrow> (gensyn_skel * unit gs_result)" where
"secd_gsx_info syn st =
  (case st of
    (g, _, _, True) \<Rightarrow> (g, GRDone)
    | (g, (s, e, (cp, _)#c'), d, b) \<Rightarrow> (g, GRPath cp)
    | (g, (s, e, []), d, b) \<Rightarrow> (case dump_get_next_path d of
        None \<Rightarrow> (g, GRPath []) \<comment> \<open> bogus... \<close>
        | Some (cp, _) \<Rightarrow> (g, GRPath cp)))"

definition secd_sem_l :: "(syn, secd) x_sem'" where
"secd_sem_l =
  l_map_s id
    (prod_fan_l secd_gsx_info id_l) secd_sem"

term "xsem secd_sem_l"
term  "gensyn_sem_exec (xsem secd_sem_l)"

term "gensyn_sem_exec"

definition gsx :: "syn gensyn \<Rightarrow> childpath \<Rightarrow> secd \<Rightarrow> nat \<Rightarrow> secd option" where
"gsx =
  gensyn_sem_exec (xsem secd_sem_l)"

definition testprog :: "syn gensyn" where
"testprog = 
  G (Svar (String.implode ''abcd'')) []"

definition init_env :: "(String.literal * unit) list" where
"init_env = [(String.implode ''abcd'', ())]"

definition initial :: "syn gensyn \<Rightarrow> (String.literal, unit, childpath * String.literal) roalist \<Rightarrow> secd" where
"initial g e = (gs_sk g, ([], e, [([], Down)]), [], False)"

(* problem is that Isabelle lifting library does not allow wrapping in abstract types.
   solution might be to declare our own type. (wrapping) *)
value "gsx testprog [] (initial testprog (roa_make_vs init_env)) 4"

value "MergeableAList.get (to_oalist ([(1, 2), (3, 4)])) (3 :: nat) :: nat option"

definition testprog2 :: "syn gensyn" where
"testprog2 =
  G (Sabs (String.implode ''x'')) [G (Svar (String.implode ''x'')) []]"

value [nbe] "gsx testprog2 [] (initial testprog2 roa_empty) 20"

definition testprog3 :: "syn gensyn" where
"testprog3 =
  G Sapp
  [G (Sabs (String.implode ''x'')) [G (Svar (String.implode ''x'')) []]
  ,G (Sabs (String.implode ''x'')) [G (Svar (String.implode ''x'')) []]]"

value [nbe] "gsx testprog3 [] (initial testprog3 roa_empty) 10"

definition testprog4 :: "syn gensyn" where
"testprog4 =
  G Sapp
  [G (Sabs (String.implode ''x'')) [G (Svar (String.implode ''x'')) []]
  ,G (Svar (String.implode ''abcd'')) []]"

value [nbe] "gsx testprog4 [] (initial testprog4 (roa_make_vs init_env)) 10"


(* need an advanced sort of fanout lifting. idea is that we have either a bool or a piece of data
capturing whether we are done.*)

(* values (S) = literals (how to represent? want separation of concerns
   or closures *)
(* closure is an environment plus a control (child-path) pointer *)
(* environments (E) bind free variables to values *)
(* control (C) is a child-path in the tree
   evaluation exits when we reach the root (i.e., we don't keep returning up out of sub expressions
   necessarily - thus need to keep the root around in state somewhere *)
(* Dump = stack (list) of S, E, C triples *)

(* stack, environment, control, dump *)
(*
type_synonym secd =
  *)

(* for a traditional SECD machine, we need a stack. *)
(* explicit return instruction? *)

(* evaluation:
   - evaluate arguments first
   - end up with a stack/list of values/closures
   - closure is a function pointer + environment
     - i.e., recursive structure

*)

(* in SECD machine, we use D to deal with closures
   i think the goal of that is to get around the issues
   with that recursion.
*)

(* values = integers (?) or closures - contents of S
   control elements = childpaths in tree - contents of C
   bindings = (id \<rightarrow> value) mapping
   D = stack of (S * E * C)
*)

(* data structures
   S = int list = (nat, value) alist
   E = (string, int) alist
   C = (nat, childpath) alist
   D = (nat, S * E * C alist)
*)

(* value is (string, value) alist
   \<longrightarrow> seems like we still can't break this recursion
   so, we will need to find a way around this.
*)
   

end