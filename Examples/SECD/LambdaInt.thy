theory LambdaInt
    imports Lambda "../Imp/MemImp" "../../Mergeable/MergeableRAList" "../Seq"
begin

(* things needed here:
  - translate calc2 (arith lang) into unified syntax
  - translate lambda into unified syntax
  - liftings
    - challenge (?): using state (S component of SECD) as a memory
*)

(* do we want to try to use Mem for Lit support? *)

datatype syn =
  Sl "Lambda.syn"
  | Sc "calc2" "str" "str"
  | Si "int"
  | Cpush
  | Cseq

datatype push_syn =
    Ppush
  | Pskip

fun lambda_trans :: "syn \<Rightarrow> Lambda.syn" where
"lambda_trans (Sl l) = l"
| "lambda_trans _ = Lambda.Sskip"

fun calc_trans :: "syn \<Rightarrow> calc2" where
"calc_trans (Sc x _ _) = x"
| "calc_trans _ = Cskip"

fun push_trans :: "syn \<Rightarrow> push_syn" where
"push_trans Cpush = Ppush"
| "push_trans _ = Pskip"

fun seq_trans ::
  "syn \<Rightarrow> Seq.syn" where
"seq_trans _ = Seq.Sskip"

fun const_trans :: "syn \<Rightarrow> int option" where
"const_trans (Si i) = Some i"
| "const_trans _ = None"

fun calc2_key1 :: "syn \<Rightarrow> str option" where
"calc2_key1 (Sc _ s1 _) = Some s1"
| "calc2_key1 _ = None"

fun calc2_key2 :: "syn \<Rightarrow> str option" where
"calc2_key2 (Sc _ _ s2) = Some s2"
| "calc2_key2 _ = None"

(* next, need to lift
   idea: take key1, key2 out of environment
   push result onto stack
*)

type_synonym clos_info = "(childpath * String.literal)"

(* roalist lifting vs oalist lifting? *)
(* product this with stack 
   i.e. we need a way to lift onto stack
  
*)

(* wrapped versions of SECD state types ('a should already be wrapped) *)

type_synonym 'a envw = "(String.literal, 'a, (childpath * String.literal) swr) roalist"

type_synonym 'a closw = "childpath swr * String.literal swr * 'a envw"

type_synonym 'a secw = "('a + 'a closw) list swr * 'a envw * (childpath * dir) list swr"

type_synonym 'a secdw = "gensyn_skel md_triv option * 'a secw * 'a secw list swr * bool swr"

(* idea: secd state + int register for results of int machine *)
type_synonym state' =
  "int secd_full * int"

type_synonym state = 
  "childpath md_triv option * int swr secdw * int swr"

(* starting at state
- t2 = secdw
\<rightarrow> t2 = secw
\<rightarrow> t1 = list swr
\<rightarrow> list head
\<rightarrow> inl *)

(* need a special sub-language for initializing a stack element
   (this is due to the nature of liftings.)
*)

type_synonym 'a push_state =
  "(('a + 'a closw) list)"

type_synonym const_state =
  "(int)"

(* push needs to take a child-path *)
(* TODO: this is sort of hacky. we don't allow push_sem to signal being done.
   so it cannot exist as the root. *)
fun push_sem :: "push_syn \<Rightarrow> ('a :: Bogus) push_state \<Rightarrow> ('a :: Bogus) push_state" where
"push_sem Pskip l = l"
| "push_sem Ppush l = (bogus)#l"

fun const_sem :: "int option \<Rightarrow> const_state \<Rightarrow> const_state" where
"const_sem None x = x"
| "const_sem (Some i) x = i"


(* idea: we are going to overwrite, unless we are Sskip *)
fun lambda_prio :: "syn \<Rightarrow> nat" where
"lambda_prio (Sl _) = 3"
| "lambda_prio _ = 2"

fun push_prio :: "syn \<Rightarrow> nat" where
"push_prio Cpush = 3"
| "push_prio _ = 1"

fun const_prio :: "syn \<Rightarrow> nat" where
"const_prio (Si _) = 3"
| "const_prio _ = 1"

fun calc_prio :: "syn \<Rightarrow> nat" where
"calc_prio (Sc _ _ _) = 3"
| "calc_prio _ = 1"
(*
definition calc2_key_lift :: "(syn, calc2_state, int swr envw * int swr) lifting" where
"calc2_key_lift =
  prod_deassoca_l (prod_l (
    merge_l
      (roalist_l calc2_key1 ((prio_l_keep o option_l o triv_l) id_l))
      (roalist_l calc2_key2 ((prio_l_keep o option_l o triv_l) id_l)))
        ((prio_l_case_inc calc_prio o option_l o triv_l) id_l))"
*)

definition calc2_key_lift :: "(syn, calc2_state, int swr envw * int swr) lifting" where
"calc2_key_lift =
  schem_lift
  (SP NA (SP NB NC))
  (SP (SM (SRL calc2_key1 (SPRK (SOT NA)))
          (SRL calc2_key2 (SPRK (SOT NB))))
      (SPRC calc_prio (SOT NC)))"


(*
  schem_lift
  (SP NA (SP NB NC))
  (SP NX 
      (SP 
        (SP NX)
        NX))
*)

(* need inl/inr liftings *)
(* maybe we should also add some more letters. would be good scaling test anyway.
*)
definition calc2_lift :: "(syn, calc2_state, state) lifting" where
"calc2_lift =
merge_l
  ((t2_l o t2_l o t2_l) (roalist_l calc2_key1 ((prio_l_keep o option_l o triv_l) id_l)))
  (merge_l
    ((t2_l o t2_l o t2_l) (roalist_l calc2_key1 ((prio_l_keep o option_l o triv_l) id_l)))
    ((t2_l o t2_l o t1_l o prio_l_case_inc calc_prio o option_l o triv_l o list_hd_l o inl_l)
      ((prio_l_case_inc calc_prio o option_l o triv_l) id_l)))"


(* scratch work for building up calc2_lift *)

term "((t2_l o t2_l o t2_l ) 
        (roalist_l calc2_key1 ((prio_l_inc o option_l o triv_l) id_l)))"

term "merge_l
      ((t2_l o t2_l o t2_l ) 
        (roalist_l calc2_key1 ((prio_l_inc o option_l o triv_l) id_l)))
       ((t2_l o t2_l o t2_l ) 
        (roalist_l calc2_key1 ((prio_l_inc o option_l o triv_l) id_l))) :: (syn, int * int, state) lifting"

term "(t2_l o t2_l o t1_l o prio_l_inc o option_l o triv_l o list_hd_l o inl_l)
      ((prio_l_inc o option_l o triv_l) id_l) :: (syn, int, state) lifting"

term "
merge_l
  ((t2_l o t2_l o t2_l) (roalist_l calc2_key1 ((prio_l_inc o option_l o triv_l) id_l)))
  (merge_l
    ((t2_l o t2_l o t2_l) (roalist_l calc2_key1 ((prio_l_inc o option_l o triv_l) id_l)))
    ((t2_l o t2_l o t1_l o prio_l_inc o option_l o triv_l o list_hd_l o inl_l)
      ((prio_l_inc o option_l o triv_l) id_l)))
:: (syn, calc2_state, state) lifting
"

definition calc_sem_l :: "syn \<Rightarrow> state \<Rightarrow> state" where
"calc_sem_l =
  l_map_s id
  calc2_lift
  (calc2_sem o calc_trans)"


definition env_lift ::
"(syn, ('a :: Bogus) env, 'a swr envw) lifting"
where
"env_lift =
  roalist_map_l ((prio_l_case_inc lambda_prio o ot_l) id_l) 
                ((prio_l_case_inc lambda_prio o ot_l) id_l)"

definition clos_lift ::
"(syn, ('a :: Bogus) clos, 'a swr closw) lifting" where
"clos_lift =
  prod_l
    ((prio_l_case_inc lambda_prio o ot_l) id_l)
    (prod_l
      ((prio_l_case_inc lambda_prio o ot_l) id_l)
      (env_lift))"


definition sec_lift ::
"(syn, ('a :: Bogus) sec, 'a swr secw) lifting" where
"sec_lift =
  prod_l
    ((prio_l_case_inc lambda_prio o ot_l o list_map_l)
      (sum_map_l 
        ((prio_l_case_inc lambda_prio o ot_l) id_l)
        clos_lift))
  (prod_l
      env_lift
      ((prio_l_case_inc lambda_prio o ot_l) id_l))"

definition secd_lift ::
"(syn, ('a :: Bogus) secd, 'a swr secdw) lifting" where
"secd_lift =
  prod_l
    (ot_l id_l)
    (prod_l
      sec_lift
      (prod_l
        ((prio_l_case_inc lambda_prio o ot_l) (list_map_l sec_lift))
        ((prio_l_case_inc lambda_prio o ot_l) id_l)))"



(* need to branch on whether the lambda instruction is an SSkip (a la seq)
   if it is, then we will need to write at low priority.
*)
definition lambda_state_lift ::
"(syn, (int) secd_full,  state) lifting"
where
"lambda_state_lift =
  prod_l
    (ot_l id_l)
    (fst_l secd_lift)"

definition lambda_sem_l :: "syn \<Rightarrow> state \<Rightarrow> state" where
"lambda_sem_l =
  l_map_s id
    lambda_state_lift
    (secd_sem o lambda_trans)"

definition const_lift :: "(syn, const_state, state) lifting" where
"const_lift =
    (t2_l o t2_l o t1_l o prio_l_case_inc const_prio o ot_l o list_hd_l o inl_l o prio_l_inc2 o ot_l) id_l"

(*
definition const_lift :: "(syn, const_state, state) lifting" where
"const_lift =
    (t2_l o t2_l o t1_l o prio_l_case_inc const_prio o ot_l o prod_commb_l o list_hd_sc_l o prod_l o inl_l o prio_l_inc2 o ot_l) id_l"

term "(prod_assocb_l o snd_l o prod_commb_l o list_hd_sc_l) id_l"
*)

definition const_sem_l :: "syn \<Rightarrow> state \<Rightarrow> state" where
"const_sem_l =
  l_map_s id
    const_lift
    (const_sem o const_trans)"

definition push_lift :: "(syn, int swr push_state, state) lifting" where
"push_lift =
  (t2_l o t2_l o t1_l o prio_l_case_inc push_prio o ot_l) id_l"

definition push_sem_l :: "syn \<Rightarrow> state \<Rightarrow> state" where
"push_sem_l =
  l_map_s id
  push_lift
  (push_sem o push_trans)"

definition sems where
"sems = [calc_sem_l, lambda_sem_l, const_sem_l, push_sem_l]"

(* remaining tasks
   - update Lambda so that it will push all children paths (done)
   - add a Seq node that is "Sskip" for everything (done)
   - make sure we use low priority when overwriting rest of state
      on Lambda Sskip *)

(* problem seems to be that we are pushing zero too many times
(also possibly that we are not successfully updating it?) *)

definition gsx_info :: 
  "syn \<Rightarrow> state \<Rightarrow> (gensyn_skel * unit gs_result)" where
"gsx_info syn st =
  secd_gsx_info
    (lambda_trans syn)
    (LOut lambda_state_lift syn st)"

definition sem_final :: "(syn, state) x_sem'" where
"sem_final =
  l_map_s id
    (prod_fan_l gsx_info id_l) (pcomps sems)"

definition gsx :: "syn gensyn \<Rightarrow> childpath \<Rightarrow> state \<Rightarrow> nat \<Rightarrow> state option" where
"gsx = gensyn_sem_exec (xsem sem_final)"

(* next: testprog, initial states, etc. *)
definition initial :: "syn gensyn \<Rightarrow> 
                      (String.literal, int swr, (childpath * String.literal) swr) roalist \<Rightarrow> 
                      state" where
"initial p env = 
  ( Some (mdt [])
  , ( Some (mdt (gs_sk p))
      , ( mdp 0 (Some (mdt []))
        , env
        , mdp 0 (Some (mdt ([([], Down)]))))
      , mdp 0 (Some (mdt []))
      , mdp 0 (Some (mdt False)))
  , mdp 0 (Some (mdt (0 :: int))))"


(* not clear to me why this is needed... *)
instantiation  roalist :: (linorder, equal, equal) equal begin
definition equal_roalist :
"(equal_class.equal (a :: ('a :: linorder, 'b :: equal, 'c :: equal) roalist)  b) \<equiv>
   (a = b)"
instance proof 
  fix x y :: "('a :: linorder, 'b :: equal, 'c :: equal) roalist"
  show "equal_class.equal x y = (x = y)"
    by(simp add: equal_roalist)
qed
end

definition testprog1 :: "syn gensyn" where
"testprog1 =
  G (Sl (Sabs (STR ''x'')))
    [G (Sl (Svar (STR ''x''))) []]"

definition testprog2 :: "syn gensyn" where
"testprog2 =
  G (Sl Sapp)
    [ G (Sl (Sabs (STR ''x'')))
        [G (Sl (Svar (STR ''x''))) []]
    , G Cseq [G Cpush [],  G (Si 5) []] 
    ]"

definition testprog3 :: "syn gensyn" where
"testprog3 =  
  G Cpush [G (Si 5) []]"

definition testprog4 :: "syn gensyn" where
"testprog4 =
  G (Sl Sapp)
    [ G (Sl (Sabs (STR ''x'')))
        [G (Sl (Svar (STR ''x''))) []]
    ,  G (Sl (Sabs (STR ''x'')))
        [G (Sl (Svar (STR ''x''))) []]
    ]"

(* is the problem that Cpush is running twice?
   it seems to not be running at all... 
   let's see about getting rid of the need for CPush by having Int constants
   use a different lifting.
   integrating Mem would be even better.
*)
value "children_control (gs_sk testprog2) [1]"

value "gensyn_get testprog2 [0]"

(* this looks possibly OK *)
value [nbe] "gsx testprog1 [] (initial testprog1 (roa_make_vs [])) 10"

(* this is running into some kind of problem *)
definition badtest where
"badtest = gsx testprog2 [] (initial testprog2 (roa_make_vs [])) 80"

(* remaining problem: environment isn't properly cleaned up.
   this appears to be because we aren't using a priority wrapper around the environment *)
export_code badtest in OCaml
  module_name Bad file "./lambda_bad.ml"

(* this is better, but now
   - we are pushing an extra 0 onto the stack (2 extra zeroes, in fact... *)

value [nbe] "gsx testprog2 [] (initial testprog2 (roa_make_vs [])) 80"

value [nbe] "gsx testprog3 [] (initial testprog3 (roa_make_vs [])) 80"


value [nbe] "gsx testprog4 [] (initial testprog4 (roa_make_vs [])) 80"


(* now we need to figure out how to push
the wrapping through the list. *)
(*
term "
prod_l
  (triv_l ((t2_l
*)

(* then we just need to give liftings for plugging everything together. *)

end