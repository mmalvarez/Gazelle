theory LambdaInt
    imports Lambda "../Imp/MemImp" "../../Mergeable/MergeableRAList"
begin

(* things needed here:
  - translate calc2 (arith lang) into unified syntax
  - translate lambda into unified syntax
  - liftings
    - challenge (?): using state (S component of SECD) as a memory
*)

datatype syn =
  Sl "Lambda.syn"
  | Sc "calc2" "str" "str"
  | Si "int"
  | Cpush

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

fun const_trans :: "syn \<Rightarrow> int option" where
"const_trans (Si i) = Some i"
| "const_trans _ = None"

fun calc2_key1 :: "syn \<Rightarrow> str  option" where
"calc2_key1 (Sc _ s1 _) = Some s1"
| "calc2_key1 _ = None"

fun calc2_key2 :: "syn \<Rightarrow> str  option" where
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

(* idea: we are pulling the outermost control element to the top level
   since it is going to be shared with the gensyn evaluator *)
type_synonym 'a secdw_full = "(childpath) * 'a secdw"

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
  "(gensyn_skel * childpath * dir * 'a list)"

type_synonym const_state =
  "(gensyn_skel * childpath * int)"

(* push needs to take a child-path *)
(* TODO: this is sort of hacky. we don't allow push_sem to signal being done.
   so it cannot exist as the root. *)
fun push_sem :: "('a :: Bogus) push_state \<Rightarrow> ('a :: Bogus) push_state" where
"push_sem (sk, cp, Up _, l) = 
  (case gensyn_cp_parent sk cp of Some cp' \<Rightarrow> (sk, cp', Up cp, l))"
| "push_sem (sk, cp, Down, l) =
  (sk, cp @ [0], Down, l)"

fun const_sem :: "int option \<Rightarrow> const_state \<Rightarrow> const_state" where
"const_sem None (sk, cp, x) = 
  (case gensyn_cp_parent sk cp of Some cp' \<Rightarrow> (sk, cp', x))"
| "const_sem (Some i) (sk, cp, x) = 
  (case gensyn_cp_parent sk cp of Some cp' \<Rightarrow> (sk, cp', i))"


(* TODO: we need to make sure we are properly accounting for the overlaps,
   and doing appropriate "prio_l_case_inc" in those places. Here is where
   this will happen:
- value stack. langs: push, const, lambda, calc
- environment stack: lambda, calc
    (NB this should be pretty easy since calc only needs read only access)
- control info: childpath, gensyn skel, etc.

We may already have this set up except for control info.
Control info is probably not being managed correctly anyhow (e.g. for calc)
Perhaps having a "lambda-seq" kind of thing would be useful. Need to think
about how best to structure that.
*)

(* full state:
- secd state
- int result register
- some way to push int result onto stack in an idempotent way
  - one very cheesy way to do this: have a "CPush" instruction that just creates a new
    list entry using contents of int result register
*)

(* OK - need to figure out exactly how to do the key lift. It is a little different
than memimp because the third argument does not live inside the swr we are lifting into.
*)

(* another lifting for products, needed here:
   if we can lift each component, we can lift the whole *)

(*
definition prod_map_pl ::
  "('x, 'b1, 'c1, 'z2) plifting_scheme \<Rightarrow>
   ('x, 'b2, 'c2, 'z3) plifting_scheme \<Rightarrow>
   ('x, 'a, 'b1 * 'b2, 'z1) plifting_scheme \<Rightarrow>
   ('x, 'a, 'c1 * 'c2) plifting" where
"prod_map_pl lfst lsnd l =
  \<lparr> LUpd =
    (\<lambda> s a b . (case a of (a1, a2) \<Rightarrow>
                  (case b of (b1, b2) \<Rightarrow>
                    (LUpd t1 s a1 b1, LUpd t2 s a2 b2))))
  , LOut =
    (\<lambda> s b . (case b of (b1, b2) \<Rightarrow>
                (LOut t1 s b1, LOut t2 s b2)))
  , LBase =
    (\<lambda> s . (LBase t1 s, LBase t2 s)) \<rparr>"

definition prod_l ::
  "('x, 'a1, 'b1, 'z1) lifting_scheme \<Rightarrow>
   ('x, 'a2, 'b2, 'z2) lifting_scheme \<Rightarrow>
   ('x, 'a1 * 'a2, 'b1 * 'b2) lifting" where
"prod_l t1 t2 =
  plifting.extend (prod_pl t1 t2)
    \<lparr> LPost = (\<lambda> s b . (case b of (b1, b2) \<Rightarrow> (LPost t1 s b1, LPost t2 s b2))) \<rparr>"
*)

term "snd_l (snd_l (fst_l (snd_l ( (roalist_l calc2_key1 ((prio_l_keep o option_l o triv_l) id_l))))))"

term "(prod_l (
    merge_l
      (roalist_l calc2_key1 ((prio_l_keep o option_l o triv_l) id_l))
      (roalist_l calc2_key2 ((prio_l_keep o option_l o triv_l) id_l)))
        ((prio_l_inc o option_l o triv_l) id_l))"

definition calc2_key_lift :: "(syn, calc2_state, int swr envw * int swr) lifting" where
"calc2_key_lift =
  prod_deassoca_l (prod_l (
    merge_l
      (roalist_l calc2_key1 ((prio_l_keep o option_l o triv_l) id_l))
      (roalist_l calc2_key2 ((prio_l_keep o option_l o triv_l) id_l)))
        ((prio_l_inc o option_l o triv_l) id_l))"

(*
term "((snd_l o snd_l o fst_l o fst_l o prio_l_inc o option_l o triv_l o list_hd_l o inl_l ) 
        (roalist_l calc2_key1 ((prio_l_keep o option_l o triv_l) id_l)))"

term "((snd_l o snd_l o fst_l o snd_l o prio_l_inc o option_l o triv_l o list_hd_l o inl_l ) 
        (roalist_l calc2_key1 ((prio_l_keep o option_l o triv_l) id_l))) :: (syn, calc2_state, state) lifting"

*)

definition calc2_lift :: "(syn, calc2_state, state) lifting" where
"calc2_lift =
merge_l
  ((t2_l o t2_l o t2_l) (roalist_l calc2_key1 ((prio_l_inc o option_l o triv_l) id_l)))
  (merge_l
    ((t2_l o t2_l o t2_l) (roalist_l calc2_key1 ((prio_l_inc o option_l o triv_l) id_l)))
    ((t2_l o t2_l o t1_l o prio_l_inc o option_l o triv_l o list_hd_l o inl_l)
      ((prio_l_inc o option_l o triv_l) id_l)))"

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

term "prod_l "

(* OK, so it looks like we need map-liftings for
- sum
- roalist
both are done now
*)
(* secd_full has:
   - childpath \<Rightarrow> lift into state
   - secd \<Rightarrow> lift into secd_w
   - int (unneeded, use fst/deassoc.) *)

definition env_lift ::
"(syn, ('a :: Bogus) env, 'a swr envw) lifting"
where
"env_lift =
  roalist_map_l ((prio_l_inc o ot_l) id_l) 
                ((prio_l_inc o ot_l) id_l)"

definition clos_lift ::
"(syn, ('a :: Bogus) clos, 'a swr closw) lifting" where
"clos_lift =
  prod_l
    ((prio_l_inc o ot_l) id_l)
    (prod_l
      ((prio_l_inc o ot_l) id_l)
      (env_lift))"

definition sec_lift ::
"(syn, ('a :: Bogus) sec, 'a swr secw) lifting" where
"sec_lift =
  prod_l
    ((prio_l_inc o ot_l o list_map_l)
      (sum_map_l 
        ((prio_l_inc o ot_l) id_l)
        clos_lift))
  (prod_l
      env_lift
      ((prio_l_inc o ot_l) id_l))"

definition secd_lift ::
"(syn, ('a :: Bogus) secd, 'a swr secdw) lifting" where
"secd_lift =
  prod_l
    (ot_l id_l)
    (prod_l
      sec_lift
      (prod_l
        ((prio_l_inc o ot_l) (list_map_l sec_lift))
        ((prio_l_inc o ot_l) id_l)))"


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

definition sems where
"sems = [calc_sem_l, lambda_sem_l]"

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


(* now we need to figure out how to push
the wrapping through the list. *)
(*
term "
prod_l
  (triv_l ((t2_l
*)

(* then we just need to give liftings for plugging everything together. *)

end