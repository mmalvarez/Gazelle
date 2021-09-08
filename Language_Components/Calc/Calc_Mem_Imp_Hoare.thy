theory Calc_Mem_Imp_Hoare
  imports Calc_Mem_Imp "../../Hoare/Hoare_Step" "../../Hoare/Hoare_Lift" "../Mem/Mem_Simple"
begin

(* final definitions that perhaps should be in mem_simple (TODO) *)


(* Deriving a set of Hoare logic rules useful for reasoning about imperative code in Imp.
 * then, proceeding with an example.
 *)

abbreviation sems where
"sems \<equiv> {calc_sem_l, mem_sem_l, cond_sem_l, imp_sem_l, seq_sem_l}"

abbreviation sems_nos where
"sems_nos \<equiv> {calc_sem_l, mem_sem_l, cond_sem_l, imp_sem_l}"

definition sem_final' :: "syn \<Rightarrow> ('s, _) state \<Rightarrow> ('s, _) state" where
"sem_final' =
  pcomps [calc_sem_l, mem_sem_l, cond_sem_l, imp_sem_l, seq_sem_l]"

(* New idea: have a lifting for use in theorems about the state. *)
(* in this case we can just use mem_lift1 I think. *)

term "sems"

(* OK, how to prove sups_pres.
 * 
*)

lemma pres :
"sups_pres sems"
proof(rule sups_presI)

  fix x :: "('a, 'b) state"
  fix sup :: "('a, 'b) state"
  fix syn :: syn
  fix Xs :: "('a, 'b) state set"
  fix Fs' :: "(syn \<Rightarrow> ('a, 'b) state \<Rightarrow> ('a, 'b) state) set"
  fix f :: "(syn \<Rightarrow> ('a, 'b) state \<Rightarrow> ('a, 'b) state)"
  assume In_Xs : "x \<in> Xs"
  assume Fin_Xs : "finite Xs"
  assume Sup : "is_sup Xs sup"
  assume Fs' : "Fs' \<subseteq> (sems :: (syn \<Rightarrow> ('a, 'b) state \<Rightarrow> ('a, 'b) state) set)"
  assume "f \<in> Fs'"
  show "\<exists>sup'.
          is_sup ((\<lambda>f. f syn sup) ` Fs') sup' \<and> is_sup (scross ((\<lambda>f. f syn) ` Fs') Xs) sup'"
    using Fs'
    apply(auto simp add: is_sup_def is_least_def is_ub_def)
  sorry

(*
lemma calc_dom :
  "\<And> c . calc_sem_l \<downharpoonleft> sems_nos (Sc c)"
  sorry

lemma cond_dom :
  "\<And> b . cond_sem_l \<downharpoonleft> sems_nos (Sb b)"
  sorry

lemma mem_dom :
  "\<And> m . mem_sem_l \<downharpoonleft> sems_nos (Sm m)"
  sorry

lemma seq_dom :
  "\<And> s . seq_sem_l \<downharpoonleft> sems (Ss s)"
  sorry

lemma imp_dom :
  "\<And> i . imp_sem_l \<downharpoonleft> sems (Si i)"
  sorry
*)

(* concrete state *)
type_synonym cstate = "(syn, unit) Mem_Simple.state"

definition start_state :: "syn gensyn \<Rightarrow> (syn, unit) Mem_Simple.state" where
"start_state prog =
  ( Swr [prog]
  , mdp 0 None
  , Swr 0, Swr 0, Swr 0, Swr 0
  , Swr empty
  , ())"

definition state_mem where
"state_mem st =
  (case st of
    (_, _, _, _, _, _, m, _) \<Rightarrow> m)"

definition prog_mini :: "syn gensyn" where
"prog_mini =  G (Sc (Cnum 42)) []
"

(* first test: a simple arithmetic *)
definition prog0 :: "syn gensyn" where
"prog0 =
  G (Ss Sseq)
  [ G (Sc (Cnum 42)) []
  , G (Sm (Swrite (STR ''A'') Reg_c)) []
  ]"

definition prog00 :: "syn gensyn" where
"prog00 =
  G (Sb (Seqz)) []
  "


(* multiplication as repeated addition *)
(* start with c = 0
 * add arg1 to c
 * decrement arg2 *)

definition prog1 :: "int \<Rightarrow> int \<Rightarrow> syn gensyn" where
"prog1 i1 i2 =
  G (Ss Sseq)
  [ G (Sc (Cnum i1)) []
  , G (Sm (Swrite (STR ''arg1'') (Reg_c))) []
  , G (Sc (Cnum i2)) []
  , G (Sm (Swrite (STR ''arg2'') (Reg_c))) []
  , G (Sc (Cnum 1)) []
  , G (Sm (Swrite (STR ''one'') (Reg_c))) []
  , G (Sc (Cnum 0)) []
  , G (Sm (Swrite (STR ''acc'') (Reg_c))) []

  , G (Sm (Sread (STR ''arg2'') (Reg_c))) []
  , G (Sb Sgtz) []

  , G (Si SwhileC)
    [ G (Ss Sseq)
      [G (Sm (Sread (STR ''arg1'') (Reg_a))) []
      , G (Sm (Sread (STR ''acc'') (Reg_b))) []
      , G (Sc Cadd) []
      , G (Sm (Swrite (STR ''acc'') (Reg_c))) []
      , G (Sm (Sread (STR ''arg2'') (Reg_a))) []
      , G (Sm (Sread (STR ''one'') (Reg_b))) []
      , G (Sc Csub) []
      , G (Sm (Swrite (STR ''arg2'') (Reg_c))) []
      , G (Sm (Sread (STR ''arg2'') (Reg_c))) []
      , G (Sb Sgtz) []
      ]
    ]
  ]
"

term "sem_run sem_final"

value "sem_run sem_final 100 (start_state prog0)"

(* calc_sem_l and cond_sem_l
*)
value "sem_run (pcomps [calc_sem_l, mem_sem_l, seq_sem_l, cond_sem_l]) 100 (start_state prog_mini)"


value "sem_run sem_final 100 (start_state prog_mini)"

value "sem_run sem_final 100 (start_state (prog1 2 3))"

(* quick n dirty approach: we should be able to get this information from the liftings,
   but this requires more machinery *)
(* TODO: change this to use liftings
*)
(*
definition st_valid where
"st_valid st = 
  (case st of
   (mdp _ (Some _), mdp _ (Some _)
   ,mdp _ (Some _), _, _) \<Rightarrow> True
   | _ \<Rightarrow> False)"
  *)

(* this will eventually be the valid-set for our lifting. *)
consts state_S :: "syn \<Rightarrow> cstate set"

term "lifting_validb"

lemma calc_lift_v :
  "lifting_validb (l_synt calc_trans calc_lift) state_S" sorry


(* ok great - so this finally works. now let's see if we can prove anything. *)

declare [[show_types = false]]
declare [[show_sorts = false]]

(* individual pieces.
*)

lemma HCalc_calc :
  assumes Hc : "c \<noteq> Cskip"
  shows "Calc.calc_sem % {{P1}} c
                         {{(\<lambda> st . case st of
                              (x1, x2, x3) \<Rightarrow> 
                              (\<exists> x3' . P1 (x1, x2, x3')) \<and>
                              (\<forall> x3' . calc_sem c (x1, x2, x3') = st))}}"
proof(rule HTSI)
  fix a
  assume H : "P1 a"

  show "case calc_sem c a of (x1, x2, x3) \<Rightarrow> (\<exists>x3'. P1 (x1, x2, x3')) \<and> (\<forall>x3'. calc_sem c (x1, x2, x3') = calc_sem c a)"
    using Hc H
    by(cases c; cases a; auto simp add: split: prod.splits)
qed

lemma HCond_cond :
  assumes Hc : "c \<noteq> Cond.Sskip_cond"
  shows "Cond.cond_sem % {{P1}} c
                         {{(\<lambda> st . case st of
                              (x1, x2) \<Rightarrow> 
                              (\<exists> x1' . P1 (x1', x2)) \<and>
                              (\<forall> x1' . cond_sem c (x1', x2) = st))}}"
proof(rule HTSI)
  fix a
  assume H : "P1 a"

  show "case cond_sem c a of
         (x1, x2) \<Rightarrow> (\<exists>x1'. P1 (x1', x2)) \<and> (\<forall>x1'. cond_sem c (x1', x2) = cond_sem c a)"
    using Hc H
    by(cases c; cases a; auto simp add: cond_sem_def split: prod.splits)
qed


(* need to push through lifting first. *)
(*
lemma HCalc_calc' :
  fixes P1
  assumes Hc : "c \<noteq> Cskip"
  shows "Calc.calc_sem % {{P1}} c
                         {{(\<lambda> X st . case st of
                              (x1, x2, x3) \<Rightarrow> 
                              (\<exists> x3' . X (x1, x2, x3')) \<and>
                              (\<forall> x3' . calc_sem c (x1, x2, x3') = st)) P1}}"
  using HCalc_calc Hc
  by auto
*)
(*declare [[show_sorts]]*)
(* problem here is with where the syntax translation is happening, I think. *)

(*
term "calc_lift"
lemma HCalc_calc'' :
  fixes P' :: "('a, ('b :: {Okay,Bogus,Mergeableb})) state \<Rightarrow> bool"
  assumes Hv : "  lifting_valid (calc_lift :: (calc, calc_state, ('a, 'b) state) lifting) S"
  assumes Hs : "Calc_Mem_Imp.calc_trans x' = c"
  assumes Hc : "c \<noteq> Cskip"
  shows "Calc_Mem_Imp.calc_sem_l % {{P'}} x' {{liftt_conc
         Calc_Mem_Imp.calc_trans calc_lift x'
         (\<lambda>P st.
             case st of
             (x1, x2, x3) \<Rightarrow>
               (\<exists>x3'. P (x1, x2, x3')) \<and>
               (\<forall>x3'. calc_sem c (x1, x2, x3') = st))
         P'}}"
  using assms liftt_conc_spec[OF _ HCalc_calc'[OF Hc], of calc_lift _ calc_trans _,
      folded calc_sem_l_def, OF Hv Hs, of P']
  by auto
*)
(* next: if P' implies OK, then liftt_conc of P'
will also be OK (assuming valid lifting)
*)

(*
lemma whoa :
    assumes "liftt_conc
         Calc_Mem_Imp.calc_trans calc_lift x'
         (\<lambda>P st.
             case st of
             (x1, x2, x3) \<Rightarrow>
               (\<exists>x3'. P (x1, x2, x3')) \<and>
               (\<forall>x3'. calc_sem c (x1, x2, x3') = st))
         P' st = z"
    shows False using assms
  apply(auto simp add: liftt_conc_def calc_lift_def)
  *)

  
(*
  have False
    using liftt_conc_spec[OF _ HCalc_calc'[OF Hc], of calc_lift _ calc_trans _,
folded calc_sem_l_def]
*)
  


lemma HCalc_skip :
  shows "Calc.calc_sem % {{P1}} Cskip
                         {{P1}}"
proof(rule HTSI)
  fix a
  assume H : "P1 a"

  show "P1 (calc_sem Cskip a)"
    using H
    by(cases a; auto simp add: split: prod.splits)
qed

lemma HCalc_Cnum :
  shows "Calc.calc_sem % {{P1}} (Cnum i)
         {{(\<lambda> st . 
            case st of (c1, c2, x) \<Rightarrow> x = i \<and> (\<exists> old . P1 (c1, c2, old)))}}"
proof(rule HTSI)
  fix a
  assume H : "P1 a"

  show "case calc_sem (Cnum i) a of
         (c1, c2, x) \<Rightarrow>
           x = i \<and>
           (\<exists>old. P1 (c1, c2, old))" using H
    by(cases a; auto simp add: split: prod.splits)
qed

lemma HCalc_Cadd :
  shows "Calc.calc_sem % {{P1}} (Cadd)
         {{(\<lambda> st . 
            case st of (c1, c2, x) \<Rightarrow> x = c1 + c2 \<and> 
            (\<exists> old . P1 (c1, c2, old)))}}"
proof(rule HTSI)
  fix a
  assume H : "P1 a"

  show "case calc_sem Cadd a of
         (c1, c2, x) \<Rightarrow>
           x = c1 + c2 \<and>
           (\<exists>old. P1 (c1, c2, old))" using H
    by(cases a; auto simp add: split: prod.splits)
qed

(* HCalc_Csub *)
lemma HCalc_Csub :
  shows "Calc.calc_sem % {{P1}} (Csub)
         {{(\<lambda> st . 
            case st of (c1, c2, x) \<Rightarrow> x = c1 - c2 \<and> 
            (\<exists> old . P1 (c1, c2, old)))}}"
proof(rule HTSI)
  fix a
  assume H : "P1 a"

  show "case calc_sem Csub a of
         (c1, c2, x) \<Rightarrow>
           x = c1 - c2 \<and>
           (\<exists>old. P1 (c1, c2, old))" using H
    by(cases a; auto simp add: split: prod.splits)
qed

lemma HCalc_Cmul :
  shows "Calc.calc_sem % {{P1}} (Cmul)
         {{(\<lambda> st . 
            case st of (c1, c2, x) \<Rightarrow> x = c1 * c2 \<and> 
            (\<exists> old . P1 (c1, c2, old)))}}"
proof(rule HTSI)
  fix a
  assume H : "P1 a"

  show "case calc_sem Cmul a of
         (c1, c2, x) \<Rightarrow>
           x = c1 * c2 \<and>
           (\<exists>old. P1 (c1, c2, old))" using H
    by(cases a; auto simp add: split: prod.splits)
qed

lemma HCond_Seqz :
  shows "Cond.cond_sem % {{P1}} (Seqz)
          {{(\<lambda> st . 
              case st of (c, i) \<Rightarrow> c = encode_bool (i = 0) \<and>
                (\<exists> old . P1 (old, i)))}}"
proof(rule HTSI)
  fix a
  assume H : "P1 a"

  show "case cond_sem Seqz a of
         (c, i) \<Rightarrow>
           c = encode_bool (i = 0) \<and>
           (\<exists>old. P1 (old, i))" using H
    by(cases a; auto simp add: cond_sem_def)
qed

lemma HCond_Sltz :
  shows "Cond.cond_sem % {{P1}} (Sltz)
          {{(\<lambda> st . 
              case st of (c, i) \<Rightarrow> c = encode_bool (i < 0) \<and>
                (\<exists> old . P1 (old, i)))}}"
proof(rule HTSI)
  fix a
  assume H : "P1 a"

  show "case cond_sem Sltz a of
         (c, i) \<Rightarrow>
           c = encode_bool (i < 0) \<and>
           (\<exists>old. P1 (old, i))" using H
    by(cases a; auto simp add: cond_sem_def)
qed

lemma HCond_Sgtz :
  shows "Cond.cond_sem % {{P1}} (Sgtz)
          {{(\<lambda> st . 
              case st of (c, i) \<Rightarrow> c = encode_bool (i > 0) \<and>
                (\<exists> old . P1 (old, i)))}}"
proof(rule HTSI)
  fix a
  assume H : "P1 a"

  show "case cond_sem Sgtz a of
         (c, i) \<Rightarrow>
           c = encode_bool (i > 0) \<and>
           (\<exists>old. P1 (old, i))" using H
    by(cases a; auto simp add: cond_sem_def)
qed

lemma HCond_skip :
  shows "Cond.cond_sem % {{P1}} Sskip_cond
                         {{P1}}"
proof(rule HTSI)
  fix a
  assume H : "P1 a"

  show "P1 (cond_sem Sskip_cond a)"
    using H
    by(cases a; auto simp add: cond_sem_def split: prod.splits)
qed

definition oalist_check' :: "('a :: linorder * 'b md_triv option md_prio) list \<Rightarrow> bool"
  where
"oalist_check' l =
  list_all
    (\<lambda> x . case x of
      (k, mdp _ (Some (mdt _))) \<Rightarrow> True
      | _ \<Rightarrow> False ) l"

lift_definition oalist_check :: "('a :: linorder, 'b md_triv option md_prio) oalist \<Rightarrow> bool"
is oalist_check' .

fun oalist_unwrap' ::
"('a :: linorder * 'b md_triv option md_prio) list \<Rightarrow>
 ('a :: linorder * 'b) list option"
where
"oalist_unwrap' [] = Some []"
| "oalist_unwrap' (h#t) =
  (case h of
    (k, mdp _ (Some (mdt v))) \<Rightarrow>
      (case oalist_unwrap' t of
        Some t' \<Rightarrow> Some ((k, v)#t')
        | None \<Rightarrow> None)
    | _ \<Rightarrow> None)"

lemma oalist_unwrap'_keys :
  "oalist_unwrap' l = Some l' \<Longrightarrow>
   map fst l = map fst l'"
proof(induction l arbitrary: l')
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case 
    by(auto split: prod.splits option.splits md_triv.splits md_prio.splits)
qed

lift_definition oalist_unwrap ::
"('a :: linorder, 'b md_triv option md_prio) oalist \<Rightarrow> 
 ('a :: linorder, 'b ) oalist option"
is oalist_unwrap' 
proof-
  fix list :: "('a :: linorder * 'b md_triv option md_prio) list"
  assume H : "strict_order (map fst list)"
  
  show "pred_option (\<lambda>xs. strict_order (map fst xs))
        (oalist_unwrap' list)"
    using H oalist_unwrap'_keys[of list]
    by(auto simp add: pred_option_def)
qed

(*
definition mem_ok :: "('s, 'x) Mem_Simple.state \<Rightarrow> bool" where
"mem_ok st =
  (case st of
    ((mdp _ (Some (mdt _)))
    , (mdp _ None)
    , (mdp _ (Some (mdt _)))
    , (mdp _ (Some (mdt _)))
    , (mdp _ (Some (mdt _)))
    , (mdp _ (Some (mdt _)))
    , (mdp _ (Some (mdt l)))
    , _) \<Rightarrow> oalist_check l
    | _ \<Rightarrow> False)"


definition mem_unwrap :: "('s, 'x) Mem_Simple.state \<Rightarrow> Mem_Simple.state0 option"
where
"mem_unwrap st =
 (case st of
    ((mdp _ (Some (mdt _)))
    , (mdp _ None)
    , (mdp _ (Some (mdt reg_flag)))
    , (mdp _ (Some (mdt reg_c)))
    , (mdp _ (Some (mdt reg_a)))
    , (mdp _ (Some (mdt reg_b)))
    , l
    , _) \<Rightarrow> 
      (case oalist_unwrap l of
       Some l' \<Rightarrow> Some (reg_flag, reg_c, reg_a, reg_b, l')
       | None \<Rightarrow> None)
    | _ \<Rightarrow> None)"
*)  
(* Mem_Read *)
(*
need to figure out a couple of things
1. should we have the predicate P1 be over the inner data, or the "raw" wrapped data? 
2. how to handle the different cases about whether there was or wasn't a value at that location before?
   (this is more of a concern for write)
*)

lemma HMem_Sread :
  shows "mem0_sem % {{ P1 }} (Sread s r)
                   {{ (\<lambda> st .
                        (case st of (reg_flag, reg_c, reg_a, reg_b, m) \<Rightarrow>
                          (case get m s of
                           Some v \<Rightarrow> 
                           (case r of Reg_a \<Rightarrow> reg_a = v \<and> (\<exists> old . P1 (reg_flag, reg_c, old, reg_b, m))
                                      | Reg_b \<Rightarrow> reg_b = v \<and> (\<exists> old . P1 (reg_flag, reg_c, reg_a, old, m))
                                      | Reg_c \<Rightarrow> reg_c = v \<and> (\<exists> old . P1 (reg_flag, old, reg_a, reg_b, m))
                                      | Reg_flag \<Rightarrow> reg_flag = v \<and> (\<exists> old . P1 (old, reg_c, reg_a, reg_b, m)))
                            | None \<Rightarrow> P1 st))) }}"
proof(rule HTSI)      
  fix a
  assume H : "P1 a"

  obtain reg_flag reg_c reg_a reg_b m where
    A : "a = (reg_flag, reg_c, reg_a, reg_b, m)"
    by(cases a; auto)

  obtain reg_flag' reg_c' reg_a' reg_b' m' where
    Result : "mem0_sem (Sread s r) a = (reg_flag', reg_c', reg_a', reg_b', m')"
    by(cases "mem0_sem (Sread s r) a"; auto)

  show "case mem0_sem (Sread s r) a of
         (reg_flag, reg_c, reg_a, reg_b, m) \<Rightarrow>
           (case get m s of None \<Rightarrow> P1 (mem0_sem (Sread s r) a)
             | Some v \<Rightarrow>
                 (case r of
                   Reg_a \<Rightarrow>
                     reg_a = v \<and>
                     (\<exists>old. P1 (reg_flag, reg_c, old, reg_b, m))
                   | Reg_b \<Rightarrow>
                       reg_b = v \<and>
                       (\<exists>old. P1 (reg_flag, reg_c, reg_a, old, m))
                   | Reg_c \<Rightarrow>
                       reg_c = v \<and>
                       (\<exists>old. P1 (reg_flag, old, reg_a, reg_b, m))
                   | Reg_flag \<Rightarrow>
                       reg_flag = v \<and>
                       (\<exists>old. P1 (old, reg_c, reg_a, reg_b, m))))"
  proof(cases "get m s")
    case None

    then show ?thesis
      using H Result A
      by(auto split: option.splits reg_id.splits)
  next
    case (Some v)
    then show ?thesis using H Result A
      by(auto split: option.splits reg_id.splits)
  qed
qed


lemma str_ord_undo_update1 :
  assumes H : "strict_order (map fst l)"
  assumes Hget : "map_of l k = None"
  shows "str_ord_delete k (str_ord_update k v l) = l"
  using assms
proof(induction l)
  case Nil
  then show ?case
    by auto
next
  case (Cons h l)

  obtain hk hv where Hkv : "h = (hk, hv)"
    by(cases h; auto)

  have Ord' : "strict_order (map fst l)"
    using Cons.prems(1) strict_order_tl[of hk "map fst l"]
    unfolding Hkv
    by auto

  show ?case
  proof(cases "k = hk")
    case True
    then show ?thesis using Cons Hkv by auto
  next
    case False
    then show ?thesis using Cons.prems Cons.IH[OF Ord'] Hkv
      by(auto)
  qed
qed

lemma undo_update1 :
  "get m k = None \<Longrightarrow> delete k (update k v m) = m"
  by(transfer; auto intro: str_ord_undo_update1)              

lemma str_ord_undo_update2 :
  assumes H : "strict_order (map fst l)"
  assumes Hget : "map_of l k = Some v"
  shows "str_ord_update k v (str_ord_update k v' l) = l"
  using assms
proof(induction l)
  case Nil
  then show ?case
    by auto
next
  case (Cons h l)

  obtain hk hv where Hkv : "h = (hk, hv)"
    by(cases h; auto)

  have Ord' : "strict_order (map fst l)"
    using Cons.prems(1) strict_order_tl[of hk "map fst l"]
    unfolding Hkv
    by auto

  show ?case
  proof(cases "k = hk")
    case True
    then show ?thesis using Cons Hkv by auto
  next
    case False

    have Hget' : "map_of l k = Some v"
      using Cons.prems Cons.IH[OF Ord'] Hkv False
      by(auto)

    have Hget'' : "(k, v) \<in> set l"
      using map_of_SomeD[OF Hget'] by simp

    then obtain idx where Get_idx : "l ! idx = (k, v)" "idx < length l"
      unfolding in_set_conv_nth by auto

    show ?thesis 
      using Hkv False Cons.prems strict_order_unfold[OF Cons.prems(1), of "idx + 1" 0] Get_idx
        Cons.IH[OF Ord']
      by(auto)
  qed
qed

lemma undo_update2 :
  "get m k = Some v \<Longrightarrow> update k v (update k v' m) = m"
  by(transfer; auto intro: str_ord_undo_update2)              

lemma str_ord_update_noop :
  assumes H : "strict_order (map fst l)"
  assumes Hget : "map_of l k = Some v"
  shows "str_ord_update k v l = l" using assms
proof(induction l)
  case Nil
  then show ?case 
    by auto
next
  case (Cons h l)

  obtain hk hv where Hkv : "h = (hk, hv)"
    by(cases h; auto)

  have Ord' : "strict_order (map fst l)"
    using Cons.prems(1) strict_order_tl[of hk "map fst l"]
    unfolding Hkv
    by auto

  show ?case
  proof(cases "k = hk")
    case True
    then show ?thesis using Cons Hkv by auto
  next
    case False
    have Hget' : "map_of l k = Some v"
      using Cons.prems Cons.IH[OF Ord'] Hkv False
      by(auto)

    have Hget'' : "(k, v) \<in> set l"
      using map_of_SomeD[OF Hget'] by simp

    then obtain idx where Get_idx : "l ! idx = (k, v)" "idx < length l"
      unfolding in_set_conv_nth by auto

    show ?thesis 
      using Hkv False Cons.prems strict_order_unfold[OF Cons.prems(1), of "idx + 1" 0] Get_idx
        Cons.IH[OF Ord']
      by(auto)
  qed
qed

lemma update_noop :
  assumes Hget : "get l k = Some v"
  shows "update k v l = l" using assms
  by(transfer; auto intro: str_ord_update_noop)              

lemma HMem_Swrite :
  shows "mem0_sem % {{ P1 }} (Swrite s r)
                    {{ (\<lambda> st . 
                        (case st of (reg_flag, reg_c, reg_a, reg_b, m) \<Rightarrow>
                          (case r of
                            Reg_a \<Rightarrow> get m s = Some reg_a
                            | Reg_b \<Rightarrow> get m s = Some reg_b
                            | Reg_c \<Rightarrow> get m s = Some reg_c
                            | Reg_flag \<Rightarrow> get m s = Some reg_flag) \<and>
                          (((\<exists>old. P1 (reg_flag, reg_c, reg_a, reg_b, update s old m)) \<or>
                           (P1 (reg_flag, reg_c, reg_a, reg_b, delete s m)))))) }}"
proof(rule HTSI)
  fix a

  assume H: "P1 a"

  show "case mem0_sem (Swrite s r) a of
         (reg_flag, reg_c, reg_a, reg_b, m) \<Rightarrow>
           (case r of
             Reg_a \<Rightarrow>
               get m s = Some reg_a 
             | Reg_b \<Rightarrow>
                 get m s = Some reg_b
             | Reg_c \<Rightarrow>
                 get m s = Some reg_c
             | Reg_flag \<Rightarrow>
                 get m s = Some reg_flag) \<and>
             ((\<exists>old. P1 (reg_flag, reg_c, reg_a, reg_b, update s old m)) \<or>
             (P1 (reg_flag, reg_c, reg_a, reg_b, delete s m))) "
  proof-
  
    obtain reg_flag reg_c reg_a reg_b m where
      A : "a = (reg_flag, reg_c, reg_a, reg_b, m)"
      by(cases a; auto)
  
    obtain reg_flag' reg_c' reg_a' reg_b' m' where
      Result : "mem0_sem (Swrite s r) a = (reg_flag', reg_c', reg_a', reg_b', m')"
      by(cases "mem0_sem (Swrite s r) a"; auto)
  
    show ?thesis
    proof(cases "get m s")
      case None
      then show ?thesis using A Result H undo_update1[OF None]
        by(cases r; auto simp add: get_update update_update)
    next
      case (Some v)
  
      have Conc' :
        "P1 (reg_flag', reg_c', reg_a', reg_b', update s v m)"
        using A Result H update_noop[OF Some]
        by(cases r; auto simp add: get_update update_update )
  
      then show ?thesis using A Result H update_noop[OF Some]
        by(cases r; auto simp add: get_update update_update; blast)
    qed 
  qed
qed

(*

*)

term "sem_final"

definition calc_lift' where
"calc_lift' =  (schem_lift (SP NA (SP NB NC)) (SP NX (SP (SPRC calc_prio (SO NC)) (SP (SPRI (SO NA)) (SP (SPRI (SO NB)) NX)))))"

term "mem_sem_lifting_gen"
term "calc_lift'"
(* TODO: the requirement that new and old reg_a and reg_b be equal is a hack. *)
lemma Calc_Final : 
  fixes gs :: "syn \<Rightarrow> (syn, (_ ::{Okay,Mergeableb,Bogus})) state \<Rightarrow> (syn, (_ ::{Okay,Bogus,Mergeableb})) state"
  assumes P1_ok : "\<And> st . P st \<Longrightarrow> st \<in> ok_S"
  assumes HP : "\<And> st . P st \<Longrightarrow> P' (LOut calc_lift' y st)"

  shows "|gs| {~ (\<lambda> st . P st) ~} [G (Sc y) z] 
    {~ (\<lambda> st . \<exists> old_big small_new . P old_big \<and> (case small_new of
                                  (x1, x2, x3) \<Rightarrow>
                                    (\<exists>x3'. P' (x1, x2, x3')) \<and>
                                    (\<forall>x3'. calc_sem y (x1, x2, x3') = small_new)) \<and>
                                 st = LUpd calc_lift' y small_new old_big) ~}"
  apply(rule HTS_imp_HT'')
            apply(rule_tac HCalc_calc)
  sorry

(* Allows us to use the fact that the original inputs are unchanged.
 * if this ends up helping we need to find a way to generalize/standardize this. *)
lemma Add_Final : 
  fixes gs :: "syn \<Rightarrow> (syn, (_ ::{Okay,Mergeableb,Bogus})) state \<Rightarrow> (syn, (_ ::{Okay,Bogus,Mergeableb})) state"
  assumes P1_ok : "\<And> st . P st \<Longrightarrow> st \<in> ok_S"
  assumes HP : "\<And> st . P st \<Longrightarrow> P' (LOut calc_lift' Cadd st)"

  shows "|gs| {~ (\<lambda> st . P st) ~} [G (Sc (Cadd)) z] 
    {~ (\<lambda> st . \<exists> old_big small_new . P old_big \<and> (case small_new of
                                  (c1, c2, x) \<Rightarrow> x = c1 + c2 \<and> (\<exists>old. P' (c1, c2, old) \<and> LOut calc_lift' Cadd old_big = (c1, c2, old))) \<and>
                                 st = LUpd calc_lift' Cadd small_new old_big) ~}"
(*  apply(rule HTS_imp_HT'') *)
(*            apply(rule_tac HCalc_Cadd) *)
  sorry

lemma Sub_Final : 
  fixes gs :: "syn \<Rightarrow> (syn, (_ ::{Okay,Mergeableb,Bogus})) state \<Rightarrow> (syn, (_ ::{Okay,Bogus,Mergeableb})) state"
  assumes P1_ok : "\<And> st . P st \<Longrightarrow> st \<in> ok_S"
  assumes HP : "\<And> st . P st \<Longrightarrow> P' (LOut calc_lift' Csub st)"

  shows "|gs| {~ (\<lambda> st . P st) ~} [G (Sc (Csub)) z] 
    {~ (\<lambda> st . \<exists> old_big small_new . P old_big \<and> (case small_new of
                                  (c1, c2, x) \<Rightarrow> x = c1 - c2 \<and> (\<exists>old. P' (c1, c2, old) \<and> LOut calc_lift' Cadd old_big = (c1, c2, old))) \<and>
                                 st = LUpd calc_lift' Csub small_new old_big) ~}"
(*  apply(rule HTS_imp_HT'') *)
(*            apply(rule_tac HCalc_Cadd) *)
  sorry


definition cond_lift' where
"cond_lift' = (schem_lift (SP NA NB) (SP (SPRC cond_prio (SO NA)) (SP (SPRK (SO NB)) NX)))"

lemma Cond_Final : 
  fixes gs :: "syn \<Rightarrow> (syn, (_ ::{Okay,Mergeableb,Bogus})) state \<Rightarrow> (syn, (_ ::{Okay,Bogus,Mergeableb})) state"
  assumes P1_ok : "\<And> st . P st \<Longrightarrow> st \<in> ok_S"
  assumes HP : "\<And> st . P st \<Longrightarrow> P' (LOut cond_lift' y st)"

  shows "|gs| {~ (\<lambda> st . P st) ~} [G (Sb y) z] 
    {~ (\<lambda> st . \<exists> old_big small_new . P old_big \<and> (case small_new of
                                  (x1', x2) \<Rightarrow>
                                    (\<exists>x1'. P' (x1', x2) ) \<and>
                                    (\<forall>x1'. cond_sem y (x1', x2) = small_new)) \<and>
                                 st = LUpd cond_lift' y small_new old_big) ~}"
  apply(rule HTS_imp_HT'')
            apply(rule_tac HCond_cond)
  sorry

(* As with arith. Need to see if we can standardize this. *)
lemma Gtz_Final :
  fixes gs :: "syn \<Rightarrow> (syn, (_ ::{Okay,Mergeableb,Bogus})) state \<Rightarrow> (syn, (_ ::{Okay,Bogus,Mergeableb})) state"
  assumes P1_ok : "\<And> st . P st \<Longrightarrow> st \<in> ok_S"
  assumes HP : "\<And> st . P st \<Longrightarrow> P' (LOut cond_lift' (Sgtz) st)"

  shows "|gs| {~ (\<lambda> st . P st) ~} [G (Sb y) z] 
    {~ (\<lambda> st . \<exists> old_big small_new . P old_big \<and> (case small_new of
                                  (x1', x2) \<Rightarrow> x1' = encode_bool (x2 > 0) \<and> (\<exists> old . P' (old, x2) \<and> LOut cond_lift' Sgtz (old_big) = (old, x2)))
                                    \<and>
                                 st = LUpd cond_lift' Sgtz small_new old_big) ~}"
  sorry


(* TODO: correctly capture case where variable is empty 
 * do we need HGet, or don't we?*)
lemma Mem_Read_Final : 
  fixes gs :: "syn \<Rightarrow> (syn, (_ ::{Okay,Mergeableb,Bogus})) state \<Rightarrow> (syn, (_ ::{Okay,Bogus,Mergeableb})) state"
  assumes P1_ok : "\<And> st . P st \<Longrightarrow> st \<in> ok_S"
  assumes HP : "\<And> st . P st \<Longrightarrow> P' (LOut mem_lift1 (Sread v r) st)"
(*
  assumes Hget : "\<And> st . P st \<Longrightarrow>
    (case st of (_, _, _, _, m, _) \<Rightarrow>
      (case m of
        mdp p (Some (mdt m')) \<Rightarrow> 
          (case get m' v of
            Some _ \<Rightarrow> True
            | _ \<Rightarrow> False)
         | _ \<Rightarrow> False))"
*)
(*
  shows "|gs| {~ (\<lambda> st . P st) ~} [G (Sm (Sread v r)) z] 
    {~ (\<lambda> st . \<exists> old_big small_new . P old_big \<and> (case small_new of
                                  (reg_flag, reg_c, reg_a, reg_b, m) \<Rightarrow>
                                        case get m ?s of None \<Rightarrow> ?P1.0 st
                                        | Some v \<Rightarrow>
                                            case ?r of Reg_a \<Rightarrow> reg_a = v \<and> (\<exists>old. ?P1.0 (reg_flag, reg_c, old, reg_b, m))
                                            | Reg_b \<Rightarrow> reg_b = v \<and> (\<exists>old. ?P1.0 (reg_flag, reg_c, reg_a, old, m)) | Reg_c \<Rightarrow> reg_c = v \<and> (\<exists>old. ?P1.0 (reg_flag, old, reg_a, reg_b, m))
                                            | Reg_flag \<Rightarrow> reg_flag = v \<and> (\<exists>old. ?P1.0 (old, reg_c, reg_a, reg_b, m))) \<and>
                                 st = LUpd mem_sem_lifting_inner y small_new old_big) ~}"
*)
shows " |gs| {~P~} [G (Calc_Mem_Imp.syn.Sm (Sread v r))
                 z] {~(\<lambda>st. \<exists>old_big small_new.
                                 P old_big \<and>
                                 (case small_new of
(reg_flag, reg_c, reg_a, reg_b, m) \<Rightarrow>
  case get m v of None \<Rightarrow> False
  | Some v \<Rightarrow>
      case r of Reg_a \<Rightarrow> reg_a = v \<and> (\<exists>old. P' (reg_flag, reg_c, old, reg_b, m))
      | Reg_b \<Rightarrow> reg_b = v \<and> (\<exists>old. P' (reg_flag, reg_c, reg_a, old, m))
      | Reg_c \<Rightarrow> reg_c = v \<and> (\<exists>old. P' (reg_flag, old, reg_a, reg_b, m))
      | Reg_flag \<Rightarrow> reg_flag = v \<and> (\<exists>old. P' (old, reg_c, reg_a, reg_b, m))) \<and>
                                 st =
                                 LUpd mem_lift1 (Sread v r) small_new
old_big)~}"
  using HTS_imp_HT''[where l' = mem_trans, where x = "Sm (Sread v r)",
unfolded mem_trans.simps, OF HMem_Sread]

  sorry

(* TODO: write version of Read_Final lemma *)
lemma Mem_Write_Final : 
  fixes gs :: "syn \<Rightarrow> (syn, (_ ::{Okay,Mergeableb,Bogus})) state \<Rightarrow> (syn, (_ ::{Okay,Bogus,Mergeableb})) state"
  assumes P1_ok : "\<And> st . P st \<Longrightarrow> st \<in> ok_S"
  assumes HP : "\<And> st . P st \<Longrightarrow> P' (LOut mem_lift1 (Swrite v r) st)"

(*
  shows "|gs| {~ (\<lambda> st . P st) ~} [G (Sm (Sread v r)) z] 
    {~ (\<lambda> st . \<exists> old_big small_new . P old_big \<and> (case small_new of
                                  (reg_flag, reg_c, reg_a, reg_b, m) \<Rightarrow>
                                        case get m ?s of None \<Rightarrow> ?P1.0 st
                                        | Some v \<Rightarrow>
                                            case ?r of Reg_a \<Rightarrow> reg_a = v \<and> (\<exists>old. ?P1.0 (reg_flag, reg_c, old, reg_b, m))
                                            | Reg_b \<Rightarrow> reg_b = v \<and> (\<exists>old. ?P1.0 (reg_flag, reg_c, reg_a, old, m)) | Reg_c \<Rightarrow> reg_c = v \<and> (\<exists>old. ?P1.0 (reg_flag, old, reg_a, reg_b, m))
                                            | Reg_flag \<Rightarrow> reg_flag = v \<and> (\<exists>old. ?P1.0 (old, reg_c, reg_a, reg_b, m))) \<and>
                                 st = LUpd mem_sem_lifting_inner y small_new old_big) ~}"
*)
shows " |gs| {~P~} [G (Calc_Mem_Imp.syn.Sm (Swrite v r))
                 z] {~(\<lambda>st. \<exists>old_big small_new.
                                 P old_big \<and>
                                 (case small_new of
                                  (reg_flag, reg_c, reg_a, reg_b, m) \<Rightarrow>
                                    (case r of Reg_a \<Rightarrow> get m v = Some reg_a
                                     | Reg_b \<Rightarrow> get m v = Some reg_b
                                     | Reg_c \<Rightarrow> get m v = Some reg_c
                                     | Reg_flag \<Rightarrow> get m v = Some reg_flag) \<and>
                                    ((\<exists>old. P' (reg_flag, reg_c, reg_a, reg_b,
 update v old m)) \<or>
                                     P' (reg_flag, reg_c, reg_a, reg_b, delete v m))) \<and>
                                 st = LUpd mem_lift1 (Swrite v r) small_new old_big)~}"
  using HTS_imp_HT''[where l' = mem_trans, where x = "Sm (Swrite v r)",
unfolded mem_trans.simps, OF HMem_Swrite]

  sorry

(* TODO: need to figure out how the lifting works. *)

(*
lemma Merge_Out :
  shows "LOut (merge_l l1 l2) = (\<lambda> a b . (LOut (fst_l l1) a b, LOut (snd_l l2) a b))"

  term "l2"
  sorry
*)

(* now need a sequencing stepping lemma. *)

lemma prog1_spec :
  assumes Hi1 : "0 < i1" (* TODO: this should be \<le>, but for (i think) a technical reason this makes things hard (existential quantifier related problems) *)
  assumes Hi2 : "0 \<le> i2"

(* TODO: st_valid need to be replaced *)

(* ok, st_valid should be somethng like (is in a valid_s of some kind) *)

(* use Ok here.
problem: will this be enough? or will we still need to figure out how to "frame out" everything else?
*)

(* need to make these a bit more ergonomic, but hopefully they will work.
one approach would be to special case this for each rule.
 *)

(* prog1 *)
(*
arg1 := i1
arg2 := i2
one := 1
acc := 0
while (arg2 > 0) {
  acc := acc + arg1
  arg2 := arg2 - one
}

*)

shows "|sem_final| {~ (\<lambda> st . st \<in> ok_S) ~}
                   [prog1 i1 i2]
                   {~ (\<lambda> st . st \<in> ok_S \<and>
                      (case st of
                        (reg_flag, reg_c, reg_a, reg_b, mem, xz) \<Rightarrow>
                          (case mem of
                            (mdp p (Some (mdt mem'))) \<Rightarrow> get mem'(STR ''acc'') = Some (i1 * i2)
                            | _ \<Rightarrow> False)))
  ~}"
(*
  using HTS_imp_HT''[where l' = calc_trans, where x = "Calc_Mem_Imp.syn.Sc (Cnum i1)"
        , unfolded calc_trans.simps, OF HCalc_Cnum]
*)
proof-
  fix gs P z l

  have 1: "|sem_final| {~(\<lambda> st . st \<in> ok_S) ~}
[ G (Sc (Cnum i1)) []] 
  {~(\<lambda> st . st \<in> ok_S \<and> 
    (case st of (reg_flag, reg_c, reg_a, reg_b, mem, xz) \<Rightarrow>
      (case reg_c of mdp p reg_c' \<Rightarrow> reg_c' = Some (mdt i1))))~}"
(is "|sem_final| {~ ?P0 ~}
[ G (Sc (Cnum i1)) []] 
  {~ ?P1~}")

    apply(rule HT'Conseq)
      apply(rule_tac P' = "\<lambda> _ . True" in Calc_Final)
       apply(fast) apply(fast) apply(fast)
    apply(force  simp add: calc_lift'_def schem_lift_defs merge_l_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S)
    done

(*
(\<lambda>st. \<exists>old_big small_new.
                                 P old_big \<and>
                                 (case small_new of
                                  (reg_flag, reg_c, reg_a, reg_b, m) \<Rightarrow>
                                    (case r of Reg_a \<Rightarrow> get m v = Some reg_a | Reg_b \<Rightarrow> get m v = Some reg_b
                                     | Reg_c \<Rightarrow> get m v = Some reg_c | Reg_flag \<Rightarrow> get m v = Some reg_flag) \<and>
                                    ((\<exists>old. True) \<or> True)) \<and>
                                 st = LUpd mem_lift1 (Swrite v r) small_new old_big
*)

(* NB: this used to work before we plugged in i1, but that is what we really want here. *)
(* TODO: need oalist zip vs get lemma *)
  have 2 : "|sem_final| 
    {~ ?P1 ~}
    [G (Sm (Swrite (STR ''arg1'') (Reg_c))) []]
{~(\<lambda>st. st \<in> ok_S \<and> (case st of
                     (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow>
                      (case m of
                        mdp p (Some (mdt m')) \<Rightarrow> get m' (STR ''arg1'') = Some i1
                         | _ \<Rightarrow> False)))~}"
(is "|sem_final| 
    {~ ?P1 ~}
    [G (Sm (Swrite (STR ''arg1'') (Reg_c))) []]
  {~ ?P2 ~}")


    apply(rule HT'Conseq)
      apply(rule_tac
 P = ?P1
and P' = "\<lambda> st . case st of (_, x, _, _) \<Rightarrow> x = i1"
in  Mem_Write_Final
;
fastforce simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
LNew_def)



     apply(fast)

      apply(fastforce simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def) 


    done

(* TODO: need assumption about mem being empty? *)
  have 3: "|sem_final| {~ ?P2~}
[ G (Sc (Cnum i2)) []] 
  {~(\<lambda> st . ?P2 st \<and> (case st of (reg_flag, reg_c, reg_a, reg_b, mem, xz) \<Rightarrow>
      (case reg_c of mdp p reg_c' \<Rightarrow> reg_c' = Some (mdt i2))))~}"
(is "|sem_final| {~ ?P2 ~}
[ G (Sc (Cnum i2)) []] 
  {~ ?P3~}")
    apply(rule HT'Conseq)
      apply(rule_tac P = ?P2 and P' = "\<lambda> _ . True" in Calc_Final)
       apply(fast) apply(fast) 

      apply(fastforce simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def) 

  apply(force simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

    done

  have 4 : "|sem_final| 
    {~ ?P3 ~}
    [G (Sm (Swrite (STR ''arg2'') (Reg_c))) []]
{~(\<lambda>st. st \<in> ok_S \<and> (case st of
                     (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow>
                      (case m of
                        mdp p (Some (mdt m')) \<Rightarrow> 
                          get m' (STR ''arg1'') = Some i1 \<and> get m' (STR ''arg2'') = Some i2
                         | _ \<Rightarrow> False)))~}"
(is "|sem_final| 
    {~ ?P3 ~}
    [G (Sm (Swrite (STR ''arg2'') (Reg_c))) []]
  {~ ?P4 ~}")

    apply(rule HT'Conseq)
      apply(rule_tac P = ?P3
and P' = "\<lambda> st . case st of (_, x, _, _, m) \<Rightarrow> x = i2 \<and> get m (STR ''arg1'') = Some i1"
  in Mem_Write_Final)
       apply(fast) 

      apply(fastforce simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

  apply(force simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
(* YOU ARE HERE. *)
(* wat *)
  apply(auto simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def get_update_neq get_delete_neq
split:md_triv.splits) 
    done

  have 5 : "|sem_final| 
    {~ ?P4 ~}
    [G (Calc_Mem_Imp.syn.Sc (Cnum 1)) []]
{~(\<lambda>st. st \<in> ok_S \<and> ?P4 st \<and> (case st of (reg_flag, reg_c, reg_a, reg_b, mem, xz) \<Rightarrow>
      (case reg_c of mdp p reg_c \<Rightarrow> reg_c = Some (mdt 1))))~}"
(is "|sem_final| 
    {~ ?P4 ~}
    _
  {~ ?P5 ~}")

    apply(rule HT'Conseq)
      apply(rule_tac P = ?P4
and P' = "\<lambda> _ . True"
  in Calc_Final)
       apply(fast) 

      apply(fastforce simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

  apply(force simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

  apply(force simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

    done

  have 6 : "|sem_final| 
    {~ ?P5 ~}
    [G (Calc_Mem_Imp.syn.Sm (Swrite STR ''one'' Reg_c)) []]
{~(\<lambda>st. st \<in> ok_S \<and> (case st of
                     (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow>
                      (case m of
                        mdp p (Some (mdt m')) \<Rightarrow> 
                          get m' (STR ''arg1'') = Some i1 \<and> get m' (STR ''arg2'') = Some i2 \<and> get m' (STR ''one'') = Some 1
                         | _ \<Rightarrow> False)))~}"
(is "|sem_final| 
    {~ ?P5 ~}
    _
  {~ ?P6 ~}")

    apply(rule HT'Conseq)
    apply(rule_tac P = ?P5
and P' = "\<lambda> st . case st of (_, x, _, _, m) \<Rightarrow> x = 1 \<and> get m (STR ''arg1'') = Some i1 \<and> get m (STR ''arg2'') = Some i2"
in Mem_Write_Final)
       apply(fast) 

      apply(fastforce simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

  apply(force simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

  apply(force simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def get_update_neq get_delete_neq
split: md_triv.splits) 

    done

  have 7 : "|sem_final| 
    {~ ?P6 ~}
    [G (Calc_Mem_Imp.syn.Sc (Cnum 0)) []]
{~(\<lambda>st. st \<in> ok_S \<and> ?P6 st \<and> (case st of (reg_flag, reg_c, reg_a, reg_b, mem, xz) \<Rightarrow>
      (case reg_c of mdp p reg_c \<Rightarrow> reg_c = Some (mdt 0))))~}"
(is "|sem_final| 
    {~ ?P6 ~}
    _
  {~ ?P7 ~}")
    apply(rule HT'Conseq)
      apply(rule_tac P = ?P6
and P' = "\<lambda> _ . True"
  in Calc_Final)
       apply(fast) 

      apply(fastforce simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

  apply(force simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

  apply(force simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

    done

  have 8 : "|sem_final| 
    {~ ?P7 ~}
    [G (Calc_Mem_Imp.syn.Sm (Swrite STR ''acc'' Reg_c)) []]
{~(\<lambda>st. st \<in> ok_S \<and> (case st of
                     (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow>
                      (case m of
                        mdp p (Some (mdt m')) \<Rightarrow> 
                          get m' (STR ''arg1'') = Some i1 \<and> get m' (STR ''arg2'') = Some i2 \<and> get m' (STR ''one'') = Some 1 \<and> get m' (STR ''acc'') = Some 0
                         | _ \<Rightarrow> False)))~}"
(is "|sem_final| 
    {~ ?P7 ~}
    _
  {~ ?P8 ~}")

    apply(rule HT'Conseq)
    apply(rule_tac P = ?P7
and P' = "\<lambda> st . case st of (_, x, _, _, m) \<Rightarrow> x = 0 \<and> get m (STR ''arg1'') = Some i1 
          \<and> get m (STR ''arg2'') = Some i2
          \<and> get m (STR ''one'') = Some 1"
        
in Mem_Write_Final)
       apply(fast) 

      apply(fastforce simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

  apply(force simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

  apply(auto simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def get_update_neq get_delete_neq) 

    done

(* TODO: we need to strengthen mem_read_final
along the same lines as mem_write_final. *)
  have 9 : "|sem_final| 
    {~ ?P8 ~}
    [G (Calc_Mem_Imp.syn.Sm (Sread STR ''arg2'' Reg_c)) []]
{~ (\<lambda> st . st \<in> ok_S \<and> (case st of
                     (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow>
                      (case m of
                        mdp p (Some (mdt m')) \<Rightarrow> 
                          get m' (STR ''arg1'') = Some i1 \<and> get m' (STR ''arg2'') = Some i2 \<and> get m' (STR ''one'') = Some 1 \<and> get m' (STR ''acc'') = Some 0
                         | _ \<Rightarrow> False) \<and>
                      (case reg_c of 
                        mdp p (Some (mdt x)) \<Rightarrow> x = i2
                        | _ \<Rightarrow> False))) ~}"
(is "|sem_final| 
    {~ ?P8 ~}
    _
  {~ ?P9 ~}")

    apply(rule HT'Conseq)
    apply(rule_tac P = ?P8
and P' = "\<lambda> st . (case st of
                     (reg_flag, reg_c, reg_a, reg_b,  m) \<Rightarrow>
                      get m (STR ''arg1'') = Some i1 
          \<and> get m (STR ''arg2'') = Some i2
          \<and> get m (STR ''one'') = Some 1
          \<and> get m (STR ''acc'') = Some 0)"
in Mem_Read_Final)

       apply(fast) 

      apply(fastforce simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

      apply(fastforce simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

(*
  apply(fastforce simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
*)

    apply(clarify)

  apply(simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def get_update_neq get_delete_neq
split: md_triv.splits) 

    apply(clarify)

    apply(simp split: md_prio.splits md_triv.splits option.splits)


    done

(* establishing the invariant. *)
(*
invariant: acc = i1 * (arg2 - i2)
*)


  have 10 : "|sem_final| 
    {~ ?P9 ~}
    [G (Sb Sgtz) []]
    {~ (\<lambda> st . st \<in> ok_S \<and> (case st of
                     (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow>
                      (case m of
                        mdp p (Some (mdt m')) \<Rightarrow> 
                          get m' (STR ''arg1'') = Some i1 \<and> get m' (STR ''arg2'') = Some i2 \<and> get m' (STR ''one'') = Some 1 \<and> get m' (STR ''acc'') = Some 0 \<and>
                         (case reg_flag of
                          mdp p (Some (mdt reg_flag')) \<Rightarrow>
                            (reg_flag' = 0 \<and> i2 \<le> 0) \<or> (reg_flag' = 1 \<and> i2 > 0)
                          | _ \<Rightarrow> False)
                         | _ \<Rightarrow> False))) ~}"
(is "|sem_final|{~ ?P9 ~}
    [G (Sb Sgtz) []]
    {~ ?P10 ~}")
    apply(rule HT'Conseq)
    apply(rule_tac P = ?P9 and P' = "\<lambda> st . (case st of (b, x) \<Rightarrow> x = i2)"
in Cond_Final)
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
    apply(clarify)
  apply(simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def cond_sem_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
    apply(clarify)
    apply(case_tac "(0 < i2)")
  apply(simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def cond_sem_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def cond_sem_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
    done

  obtain Inv :: "(_ :: {Bogus,Okay,Mergeableb}) Mem_Simple.state1 \<Rightarrow> bool" where Inv_def :
  "Inv = (\<lambda> st . st \<in> ok_S \<and> (case st of
                     (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow>
                      (case m of
                        mdp p (Some (mdt m')) \<Rightarrow> 
                          (\<exists> (idx :: int) . get m' (STR ''arg1'') = Some i1 \<and> 
                                       get m' (STR ''arg2'') = Some idx \<and>
                                       get m' (STR ''one'') = Some 1 \<and>
                                       get m' (STR ''acc'') = Some (i1 * (i2 - idx)) \<and>
                                       i2 \<ge> idx \<and>
                                       (case reg_flag of mdp p (Some (mdt reg_flag')) \<Rightarrow>
                                         ((reg_flag' = 1 \<and> idx > 0) \<or> (reg_flag' = 0 \<and> idx = 0))
                                         | _ \<Rightarrow> False))
                        | _ \<Rightarrow> False)))"
    by simp


  have Inv_10 :
    "\<And> st . (?P10 st) \<Longrightarrow>
  Inv st"
    using Hi2 unfolding Inv_def
    by(auto split: md_triv.splits md_prio.splits option.splits)

(* while loop body *)
  have Body1 : 
"|sem_final| {~ (\<lambda> st . 
                  Inv st \<and>
                  (case st of (mdp p (Some (mdt reg_flag')), _) \<Rightarrow>
                    reg_flag' = 1
                   | _ \<Rightarrow> False)) ~}
  [G (Calc_Mem_Imp.syn.Sm (Sread STR ''arg1'' Reg_a)) []]
  {~ (\<lambda> st . st \<in> ok_S \<and> (case st of (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow> 
      (case reg_a of
        mdp p (Some (mdt reg_a')) \<Rightarrow> reg_a' = i1 \<and>
        (case m of
          mdp p (Some (mdt m')) \<Rightarrow> 
            (\<exists> idx . 
get m' (STR ''arg1'') = Some i1 \<and>
get m' (STR ''arg2'') = Some idx \<and>
                     get m' (STR ''one'') = Some 1 \<and>
                     get m' (STR ''acc'') = Some (i1 * (i2 - idx)) \<and>
                     i2 \<ge> idx \<and>idx > 0)
          | _ \<Rightarrow> False)
        | _ \<Rightarrow> False))) ~}"
(is "|sem_final| {~ ?B0 ~} _ {~ ?B1 ~}")
    apply(rule HT'Conseq)
    apply(rule_tac P = ?B0
and P' = "\<lambda> st . (case st of
                     (reg_flag, reg_c, reg_a, reg_b,  m) \<Rightarrow>
                     reg_flag = 1 \<and>
                     (\<exists> (idx :: int) . get m (STR ''arg1'') = Some i1 \<and> 
                                 get m (STR ''arg2'') = Some idx \<and>
                                 get m (STR ''one'') = Some 1 \<and>
                                 get m (STR ''acc'') = Some (i1 * (i2 - idx)) \<and>
                                 i2 \<ge> idx \<and>idx > 0))"
in Mem_Read_Final)

  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(force  simp add: Inv_def cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
 
  apply(force  simp add: Inv_def cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

  apply(fastforce simp add: Inv_def cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def cond_sem_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits option.splits) 
 
    done

(*
(\<lambda> st . st \<in> ok_S \<and> (case st of
                     (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow>
                      (case m of
                        mdp p (Some (mdt m')) \<Rightarrow> 
                          (\<exists> idx . get m' (STR ''arg1'') = Some i1 \<and> 
                                       get m' (STR ''arg2'') = Some idx \<and>
                                       get m' (STR ''one'') = Some 1 \<and>
                                       get m' (STR ''acc'') = Some (i1 * (i2 - idx)) \<and>
                                       i2 \<ge> idx \<and>idx \<ge> 0))))
*)
  have Body2 :
"|sem_final| {~ ?B1 ~}
  [G (Calc_Mem_Imp.syn.Sm (Sread STR ''acc'' Reg_b)) []]
  {~ (\<lambda> st . ?B1 st \<and> (case st of (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow> 
      (case reg_b of
        mdp p (Some (mdt reg_b')) \<Rightarrow> 
        (case m of
          mdp p (Some (mdt m')) \<Rightarrow>
            (\<exists> (idx :: int) . i2 \<ge>  idx \<and> idx > 0 \<and> reg_b' = i1 * (i2 - idx) \<and> 
            get m' (STR ''arg1'') = Some i1 \<and>
            get m' (STR ''arg2'') = Some idx \<and>
            get m' (STR ''acc'') = Some (i1 * (i2 - idx)))
                      | _ \<Rightarrow> False)
                    | _ \<Rightarrow> False))) ~}"

(is "|sem_final| {~ _ ~} _ {~ ?B2 ~}")
    apply(rule HT'Conseq)
    apply(rule_tac P = ?B1
and P' = "\<lambda> st . (case st of
                     (reg_flag, reg_c, reg_a, reg_b,  m) \<Rightarrow>
                     (\<exists> idx . get m (STR ''arg1'') = Some i1 \<and> i1 = reg_a \<and>
                                 get m (STR ''arg2'') = Some idx \<and>
                                 get m (STR ''one'') = Some 1 \<and>
                                 get m (STR ''acc'') = Some (i1 * (i2 - idx)) \<and>
                                 i2 \<ge> idx \<and>idx > 0))"
in Mem_Read_Final)


  apply(force  simp add: Inv_def cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def cond_sem_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

    apply(clarify)

  apply(simp add: Inv_def cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
      apply(clarify)
  apply(simp add: Inv_def cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
     apply(clarify)
  apply(simp add: Inv_def cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

    apply(clarify)

     apply(
 simp add: Inv_def cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits option.splits) 

    apply(clarify)
    apply(blast)

    done

  have Body3 :
(*
"|sem_final| {~ ?B2 ~}
  [G (Calc_Mem_Imp.syn.Sc Cadd) []]
  {~ (\<lambda> st . st \<in> ok_S \<and>(case st of (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow> 
      (case (reg_a, reg_b, reg_c) of
        (mdp _ (Some (mdt reg_a')), mdp _ (Some (mdt reg_b')), mdp _ (Some (mdt reg_c'))) \<Rightarrow> 
        (case m of
          mdp p (Some (mdt m')) \<Rightarrow>
            (\<exists> idx . reg_c' = i1 * (i2 - idx) + i1 \<and>
                     reg_a' = i1 \<and> reg_b' = i1 * (i2 - idx) \<and>  get m' (STR ''acc'') = Some (i1 * (i2 - idx)) \<and>
                     i2 \<ge> idx \<and> idx \<ge> 0)
          | _ \<Rightarrow> False)
        | _ \<Rightarrow> False))) ~}"
(is "|sem_final| {~ _ ~} _ {~ ?B3 ~}")
*)
(*
"|sem_final| {~ ?B2 ~}
  [G (Calc_Mem_Imp.syn.Sc Cadd) []]
  {~ (\<lambda> st . ?B2 st \<and>(case st of (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow> 
      (case (reg_a, reg_b, reg_c) of
        (mdp _ (Some (mdt reg_a')), mdp _ (Some (mdt reg_b')), mdp _ (Some (mdt reg_c'))) \<Rightarrow> 
        (case m of
          mdp p (Some (mdt m')) \<Rightarrow>
            (\<exists> (idx :: int) . reg_c' = i1 + i1 * (i2 - idx) \<and>
                     reg_a' = i1 \<and> reg_b' = i1 * (i2 - idx) \<and>  
                     get m' (STR ''acc'') = Some (i1 * (i2 - idx)) \<and>
                     get m' (STR ''arg2'') = Some idx \<and>
                     i2 \<ge> idx \<and> idx \<ge> 0)
          | _ \<Rightarrow> False)
        | _ \<Rightarrow> False))) ~}"
*)
(*
"|sem_final| {~ ?B2 ~}
  [G (Calc_Mem_Imp.syn.Sc Cadd) []]
  {~ (\<lambda> st . ?B2 st \<and>(case st of (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow> 
      (case (reg_a, reg_b, reg_c) of
        (mdp _ (Some (mdt reg_a')), mdp _ (Some (mdt reg_b')), mdp _ (Some (mdt reg_c'))) \<Rightarrow> 
        reg_a' = i1 \<and>
         (\<exists> (idx :: int) . i2 \<ge> idx \<and> idx > 0 \<and> reg_b' = i1 * (i2 - idx) \<and> reg_c' = i1 + i1 * (i2 - idx))
        | _ \<Rightarrow> False))) ~}"
*)
(*maybe we need a different calc rule(unchanged stuff *)
"|sem_final| {~ ?B2 ~}
  [G (Calc_Mem_Imp.syn.Sc Cadd) []]
  {~ (\<lambda> st . ?B2 st \<and>(case st of (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow> 
      (case (reg_a, reg_b, reg_c) of
        (mdp _ (Some (mdt reg_a')), mdp _ (Some (mdt reg_b')), mdp _ (Some (mdt reg_c'))) \<Rightarrow> 
        reg_c' = reg_a' + reg_b'
                | _ \<Rightarrow> False))) ~}"

(is "|sem_final| {~ _ ~} _ {~ ?B3 ~}")

    apply(rule HT'Conseq)
(*
    apply(rule_tac P = ?B2
and P' = "\<lambda> _ . True"
in Calc_Final)
*)
    apply(rule_tac P = ?B2
and P' = "\<lambda> st . case st of (reg_a, reg_b, reg_c) \<Rightarrow>
          reg_a = i1 \<and>
          (\<exists> (idx :: int) . i2 \<ge> idx \<and> idx > 0 \<and> reg_b = i1 * (i2 - idx))"
in Add_Final)


  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

    apply(insert Hi2)
    apply(insert Hi1)
    apply(simp add: Inv_def cond_lift'_def calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def 
split: md_triv.splits md_prio.splits)
      apply(clarify)
    apply(simp add: Inv_def cond_lift'_def calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def 
split: md_triv.splits md_prio.splits)
      apply(clarify)

    apply(simp add: Inv_def cond_lift'_def calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def 
split: md_triv.splits md_prio.splits)
    apply(clarify)


    apply(simp)
    apply(insert Hi2)
    apply(insert Hi1)

  apply(simp add: Inv_def cond_lift'_def calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def 
split: md_triv.splits) 

    apply(clarify)
    apply(simp (no_asm_simp))

  apply(simp add: Inv_def cond_lift'_def calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def split: md_triv.splits
) 

    done

  have Body4 :
"|sem_final| {~ ?B3 ~}
  [G (Calc_Mem_Imp.syn.Sm (Swrite STR ''acc'' Reg_c)) []]
  {~ (\<lambda> st .  st \<in> ok_S \<and> (case st of (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow> 
      (case (reg_a, reg_b, reg_c, m) of
        (mdp _ (Some (mdt reg_a')), mdp _ (Some (mdt reg_b')), mdp _ (Some (mdt reg_c')), mdp _ (Some (mdt m'))) \<Rightarrow> 
        \<exists> (idx :: int) . i2 \<ge>  idx \<and> idx > 0 \<and> reg_b' = i1 * (i2 - idx) \<and> reg_c' = i1 + i1 * (i2 - idx) \<and> reg_a' = i1 \<and>
            get m' (STR ''arg1'') = Some i1 \<and>
            get m' (STR ''arg2'') = Some idx \<and>
            get m' (STR ''one'') = Some (1) \<and>
            get m' (STR ''acc'') = Some ( i1 + i1 * (i2 - idx))
        | _ \<Rightarrow> False))) ~}"

(is "|sem_final| {~ _ ~} _ {~ ?B4 ~}")

    apply(rule HT'Conseq)
(*
    apply(rule_tac P = ?B2
and P' = "\<lambda> _ . True"
in Calc_Final)
*)
    apply(rule_tac P = ?B3
and P' = "\<lambda> st . case st of (reg_flag', reg_c', reg_a', reg_b', m') \<Rightarrow>
            \<exists> (idx :: int) . i2 \<ge>  idx \<and> idx > 0 \<and> reg_b' = i1 * (i2 - idx) \<and> reg_c' = i1 + i1 * (i2 - idx) \<and> reg_a' = i1 \<and>
            get m' (STR ''arg1'') = Some i1 \<and>
            get m' (STR ''arg2'') = Some idx \<and>
            get m' (STR ''acc'') = Some ( i1 * (i2 - idx)) \<and>
 get m' (STR ''one'') = Some (1)"
in Mem_Write_Final)


  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def get_update_neq get_delete_neq get_update
split: md_triv.splits) 
    done

  have Body5 : 
    "|sem_final| {~ ?B4 ~}
  [G (Calc_Mem_Imp.syn.Sm (Sread STR ''arg2'' Reg_a)) []]
  {~ (\<lambda> st .  st \<in> ok_S \<and> (case st of (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow> 
      (case (reg_a, reg_b, reg_c, m) of
        (mdp _ (Some (mdt reg_a')), mdp _ (Some (mdt reg_b')), mdp _ (Some (mdt reg_c')), mdp _ (Some (mdt m'))) \<Rightarrow> 
        \<exists> (idx :: int) . i2 \<ge>  idx \<and> idx > 0 \<and> reg_b' = i1 * (i2 - idx) \<and> reg_c' = i1 + i1 * (i2 - idx) \<and> reg_a' = idx \<and>
            get m' (STR ''arg1'') = Some i1 \<and>
            get m' (STR ''arg2'') = Some idx \<and>
            get m' (STR ''one'') = Some (1) \<and>
            get m' (STR ''acc'') = Some ( i1 + i1 * (i2 - idx))
        | _ \<Rightarrow> False))) ~}"

(is "|sem_final| {~ _ ~} _ {~ ?B5 ~}")
    apply(rule HT'Conseq)
    apply(rule_tac P = ?B4
and P' = "\<lambda> st . case st of (reg_flag', reg_c', reg_a', reg_b', m') \<Rightarrow>
            \<exists> (idx :: int) . i2 \<ge>  idx \<and> idx > 0 \<and> reg_b' = i1 * (i2 - idx) \<and> reg_c' = i1 + i1 * (i2 - idx) \<and> reg_a' = i1 \<and>
            get m' (STR ''arg1'') = Some i1 \<and>
            get m' (STR ''arg2'') = Some idx \<and>
            get m' (STR ''acc'') = Some (i1 + i1 * (i2 - idx)) \<and>
 get m' (STR ''one'') = Some (1)"
in Mem_Read_Final)

  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def get_update_neq get_delete_neq get_update
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def get_update_neq get_delete_neq get_update
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def get_update_neq get_delete_neq get_update
split: md_triv.splits) 
    apply(simp add: Inv_def cond_lift'_def calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def 
split: md_triv.splits md_prio.splits)
      apply(clarify)
    apply(simp add: Inv_def cond_lift'_def calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def 
split: md_triv.splits md_prio.splits)
      apply(clarify)

    apply(simp add: Inv_def cond_lift'_def calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def 
split: md_triv.splits md_prio.splits)
    apply(auto split: option.splits)
    done


  have Body6 :
    "|sem_final| {~ ?B5 ~}
  [G (Calc_Mem_Imp.syn.Sm (Sread STR ''one'' Reg_b)) []]
  {~ (\<lambda> st .  st \<in> ok_S \<and> (case st of (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow> 
      (case (reg_a, reg_b, reg_c, m) of
        (mdp _ (Some (mdt reg_a')), mdp _ (Some (mdt reg_b')), mdp _ (Some (mdt reg_c')), mdp _ (Some (mdt m'))) \<Rightarrow> 
        \<exists> (idx :: int) . i2 \<ge>  idx \<and> idx > 0 \<and> reg_b' = 1 \<and> reg_c' = i1 + i1 * (i2 - idx) \<and> reg_a' = idx \<and>
            get m' (STR ''arg1'') = Some i1 \<and>
            get m' (STR ''arg2'') = Some idx \<and>
            get m' (STR ''one'') = Some (1) \<and>
            get m' (STR ''acc'') = Some ( i1 + i1 * (i2 - idx))
        | _ \<Rightarrow> False))) ~}"
(is "|sem_final| {~ _ ~} _ {~ ?B6 ~}")
    apply(rule HT'Conseq)
    apply(rule_tac P = ?B5
and P' = "\<lambda> st . case st of (reg_flag', reg_c', reg_a', reg_b', m') \<Rightarrow>
            \<exists> (idx :: int) . i2 \<ge>  idx \<and> idx > 0 \<and> reg_b' = i1 * (i2 - idx) \<and> reg_c' = i1 + i1 * (i2 - idx) \<and> reg_a' = idx \<and>
            get m' (STR ''arg1'') = Some i1 \<and>
            get m' (STR ''arg2'') = Some idx \<and>
            get m' (STR ''acc'') = Some (i1 + i1 * (i2 - idx)) \<and>
 get m' (STR ''one'') = Some (1)"
in Mem_Read_Final)

  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def get_update_neq get_delete_neq get_update
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def get_update_neq get_delete_neq get_update
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def get_update_neq get_delete_neq get_update
split: md_triv.splits) 
    apply(simp add: Inv_def cond_lift'_def calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def 
split: md_triv.splits md_prio.splits)
      apply(clarify)
    apply(simp add: Inv_def cond_lift'_def calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def 
split: md_triv.splits md_prio.splits)
      apply(clarify)

    apply(simp add: Inv_def cond_lift'_def calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def 
split: md_triv.splits md_prio.splits)
    apply(auto split: option.splits)
    done

  have Body7 :
    "|sem_final| {~ ?B6 ~}
  [G (Calc_Mem_Imp.syn.Sc Csub) []]
  {~ (\<lambda> st .  st \<in> ok_S \<and> (case st of (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow> 
      (case (reg_a, reg_b, reg_c, m) of
        (mdp _ (Some (mdt reg_a')), mdp _ (Some (mdt reg_b')), mdp _ (Some (mdt reg_c')), mdp _ (Some (mdt m'))) \<Rightarrow> 
        \<exists> (idx :: int) . i2 \<ge>  idx \<and> idx > 0 \<and> reg_b' = 1 \<and> reg_c' = idx - 1 \<and> reg_a' = idx \<and>
            get m' (STR ''arg1'') = Some i1 \<and>
            get m' (STR ''arg2'') = Some idx \<and>
            get m' (STR ''one'') = Some (1) \<and>
            get m' (STR ''acc'') = Some ( i1 + i1 * (i2 - idx))
        | _ \<Rightarrow> False))) ~}"
(is "|sem_final| {~ _ ~} _ {~ ?B7 ~}")
    apply(rule HT'Conseq)
    apply(rule_tac P = ?B6
and P' = "\<lambda> st . case st of (reg_a', reg_b', reg_c') \<Rightarrow>
            \<exists> (idx :: int) . i2 \<ge>  idx \<and> idx > 0 \<and> reg_b' = 1  \<and> reg_a' = idx"
in Sub_Final)
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 


    apply(insert Hi2)
    apply(insert Hi1)
    apply(simp add: Inv_def cond_lift'_def calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def 
split: md_triv.splits md_prio.splits)
      apply(clarify)
    apply(simp add: Inv_def cond_lift'_def calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def 
split: md_triv.splits md_prio.splits)
     apply(clarify)

    apply(simp)
    apply(clarify)
    apply(simp add: Inv_def cond_lift'_def calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def 
split: md_triv.splits)
    apply(clarify)


  apply(simp add: Inv_def cond_lift'_def calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def 
split: md_triv.splits) 

    done

    have Body8 :
    "|sem_final| {~ ?B7 ~}
  [G (Calc_Mem_Imp.syn.Sm (Swrite STR ''arg2'' Reg_c)) []]
  {~ (\<lambda> st .  st \<in> ok_S \<and> (case st of (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow> 
      (case (reg_a, reg_b, reg_c, m) of
        (mdp _ (Some (mdt reg_a')), mdp _ (Some (mdt reg_b')), mdp _ (Some (mdt reg_c')), mdp _ (Some (mdt m'))) \<Rightarrow> 
        \<exists> (idx :: int) . i2 \<ge>  idx \<and> idx > 0 \<and> reg_b' = 1 \<and> reg_c' = idx - 1 \<and> reg_a' = idx \<and>
            get m' (STR ''arg1'') = Some i1 \<and>
            get m' (STR ''arg2'') = Some (idx - 1) \<and>
            get m' (STR ''one'') = Some (1) \<and>
            get m' (STR ''acc'') = Some ( i1 + i1 * (i2 - idx))
        | _ \<Rightarrow> False))) ~}"
(is "|sem_final| {~ _ ~} _ {~ ?B8 ~}")
      apply(rule_tac HT'Conseq)
    apply(rule_tac P = ?B7
and P' = "\<lambda> st . case st of (reg_flag', reg_c', reg_a', reg_b', m') \<Rightarrow>
            \<exists> (idx :: int) . i2 \<ge>  idx \<and> idx > 0 \<and> reg_b' = 1 \<and> reg_c' = idx - 1 \<and> reg_a' = idx \<and>
            get m' (STR ''arg1'') = Some i1 \<and>
            get m' (STR ''arg2'') = Some idx \<and>
            get m' (STR ''acc'') = Some ( i1 + i1 * (i2 - idx))\<and>
 get m' (STR ''one'') = Some (1)"
in Mem_Write_Final)


  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def get_update_neq get_delete_neq get_update
split: md_triv.splits) 
      done

    have Body9 :
    "|sem_final| {~ ?B8 ~}
  [G (Calc_Mem_Imp.syn.Sm (Sread STR ''arg2'' Reg_c)) []]
  {~ (\<lambda> st .  st \<in> ok_S \<and> (case st of (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow> 
      (case (reg_a, reg_b, reg_c, m) of
        (mdp _ (Some (mdt reg_a')), mdp _ (Some (mdt reg_b')), mdp _ (Some (mdt reg_c')), mdp _ (Some (mdt m'))) \<Rightarrow> 
        \<exists> (idx :: int) . i2 \<ge>  idx \<and> idx > 0 \<and> reg_b' = 1 \<and> reg_c' = idx - 1 \<and> reg_a' = idx \<and>
            get m' (STR ''arg1'') = Some i1 \<and>
            get m' (STR ''arg2'') = Some (idx - 1) \<and>
            get m' (STR ''one'') = Some (1) \<and>
            get m' (STR ''acc'') = Some ( i1 + i1 * (i2 - idx))
        | _ \<Rightarrow> False))) ~}"
(is "|sem_final| {~ _ ~} _ {~ ?B9 ~}")
      apply(rule_tac HT'Conseq)
    apply(rule_tac P = ?B8
and P' = "\<lambda> st . case st of (reg_flag', reg_c', reg_a', reg_b', m') \<Rightarrow>
            \<exists> (idx :: int) . i2 \<ge>  idx \<and> idx > 0 \<and> reg_b' = 1 \<and> reg_c' = idx - 1 \<and> reg_a' = idx \<and>
            get m' (STR ''arg1'') = Some i1 \<and>
            get m' (STR ''arg2'') = Some (idx - 1) \<and>
            get m' (STR ''acc'') = Some ( i1 + i1 * (i2 - idx))\<and>
 get m' (STR ''one'') = Some (1)"
in Mem_Read_Final)


  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(simp add: Inv_def cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

    apply(clarify)

     apply(
 simp add: Inv_def cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits option.splits) 

      done

    have Helper : "\<And> (x :: int) (y :: int) . x + x * y = x * (1 + y)"
    proof-
      fix x y :: int
      show "x + x * y = x * (1 + y)"
        using int_distrib
        by auto
    qed

    have Body10:
    "|sem_final| {~ ?B9 ~}
  [G (Sb Sgtz) []]
  {~ Inv ~}"
(is "|sem_final| {~ _ ~} _ {~ _ ~}")
      apply(rule_tac HT'Conseq)
        apply(rule_tac
P = ?B9 and
P' = "\<lambda> st . (case st of (b, x) \<Rightarrow> \<exists> idx . i2 \<ge>  idx \<and> idx > 0 \<and> x = (idx - 1))" in
 Gtz_Final)
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def cond_sem_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
      apply(clarify)
  apply(simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def int_distrib
split: md_triv.splits) 
      done

      have Conclusion :
        "\<And> st . Inv st \<Longrightarrow> 
         get_cond st = Some False \<Longrightarrow>
    (case st of (_, _, _, _, mdp p (Some (mdt m')), _) \<Rightarrow> get m' (STR ''acc'') = Some (i1 * i2)
     | _ \<Rightarrow> False
      )"
    using Hi1 Hi2 unfolding Inv_def
    apply(auto simp add: get_cond_def split: md_triv.splits md_prio.splits)
    apply(case_tac x2a; simp)
    apply(case_tac a; simp)
    apply(case_tac x2; simp)
    apply(case_tac ad; simp)
    apply(case_tac "xa = 0"; simp)
    done


(* YOU ARE HERE *)

(* TODO: is our loop invariant correct? *)


(*
 [, ,
          , , , G (Calc_Mem_Imp.syn.Sm (Sread STR ''arg2'' Reg_c)) [], G (Sb Sgtz) []]]]
*)
*)


end