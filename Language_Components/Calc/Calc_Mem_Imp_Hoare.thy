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

term "(x :: (_, _) state)"

(* New idea: have a lifting for use in theorems about the state. *)
(* in this case we can just use mem_lift1 I think. *)
  

lemma pres :
"sups_pres sems"
  sorry

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

(* concrete state *)
type_synonym cstate = "(syn, unit) Mem_Simple.state"

definition start_state :: "syn gensyn \<Rightarrow> (syn, unit) Mem_Simple.state" where
"start_state prog =
  ( Swr [prog]
  , mdp 0 None
  , Swr 0, Swr 0, Swr 0, Swr 0
  , empty
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

definition mem_ok :: "('s, 'x) Mem_Simple.state \<Rightarrow> bool" where
"mem_ok st =
  (case st of
    ((mdp _ (Some (mdt _)))
    , (mdp _ None)
    , (mdp _ (Some (mdt _)))
    , (mdp _ (Some (mdt _)))
    , (mdp _ (Some (mdt _)))
    , (mdp _ (Some (mdt _)))
    , l
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
"calc_lift' =  (schem_lift (SP NA (SP NB NC)) (SP NX (SP (SPRC calc_prio (SO NC)) (SP (SPRK (SO NA)) (SP (SPRK (SO NB)) NX)))))"

term "mem_sem_lifting_gen"

(* ok, we need to restructure mem_simple. except, we can't because we need overlap with control. *)

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

(* TODO: fix this so that it matches what we proved before (HMem_Read) *)
(* TODO: this isn't tight enough. we need to do something about the "inner" precondition. *)
lemma Mem_Read_Final : 
  fixes gs :: "syn \<Rightarrow> (syn, (_ ::{Okay,Mergeableb,Bogus})) state \<Rightarrow> (syn, (_ ::{Okay,Bogus,Mergeableb})) state"
  assumes P1_ok : "\<And> st . P st \<Longrightarrow> st \<in> ok_S"
  assumes HP : "\<And> st . P st \<Longrightarrow> P' (LOut mem_lift1 (Sread v r) st)"

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
  case get m v of None \<Rightarrow> True
  | Some v \<Rightarrow>
      case r of Reg_a \<Rightarrow> reg_a = v \<and> (\<exists>old. True)
      | Reg_b \<Rightarrow> reg_b = v \<and> (\<exists>old. True)
      | Reg_c \<Rightarrow> reg_c = v \<and> (\<exists>old. True)
      | Reg_flag \<Rightarrow> reg_flag = v \<and> (\<exists>old. True)) \<and>
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
  assumes Hi1 : "0 \<le> i1"
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
                          \<exists> p . get mem (STR ''acc'') = Some (mdp p (Some (mdt (i1 * i2))))))
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
      (case reg_c of mdp p reg_c \<Rightarrow> reg_c = Some (mdt i1))))~}"
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
                     (reg_flag, mdp pc (Some (mdt reg_c)), reg_a, reg_b,  m, xz) \<Rightarrow>
                          \<exists> p . get m (STR ''arg1'') = Some (mdp p (Some  (mdt i1)))))~}"
(is "|sem_final| 
    {~ ?P1 ~}
    [G (Sm (Swrite (STR ''arg1'') (Reg_c))) []]
  {~ ?P2 ~}")


    apply(rule HT'Conseq)
      apply(rule_tac
 P = ?P1
and P' = "\<lambda> st . case st of (_, x, _, _) \<Rightarrow> x = i1"
in  Mem_Write_Final
)



       apply(fast)

      (* apply(simp add: mem_lift1_def schem_lift_defs ) *)
(* inspect *)

      apply(fastforce simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
oalist_zip_get oalist_all_val_get_eq LNew_def
split: option.splits md_prio.splits)
      apply(fastforce simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
oalist_zip_get oalist_all_val_get_eq LNew_def
split: option.splits md_prio.splits)
      apply(fastforce simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
oalist_zip_get oalist_all_val_get_eq LNew_def
split: option.splits md_prio.splits)

    done

(*
    apply(fastforce simp add: calc_lift'_def schem_lift_defs merge_l_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S
split:
option.splits md_prio.splits md_triv.splits prod.splits)
*)
(*
    apply(simp only: mem_lift1_def schem_lift_defs merge_l_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
oalist_map_l_def mem_sem_lifting_inner_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S)
  *)  

(* TODO: we need some kind of way to deal with oalist_zip (lemmas to characterize it)
we may also want to prove a smaller lemma that shows that the ?P1 fact about
the calc state implies something about the mem state.
*)    

    
(*
    apply(auto  simp add: calc_lift'_def schem_lift_defs merge_l_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
mem_lift1_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S
split:
option.splits md_prio.splits md_triv.splits prod.splits)
*)



(*
    apply(auto simp add: calc_lift'_def schem_lift_defs merge_l_def
mem_lift1_def mem_sem_lifting_inner_def

fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S
split:
md_prio.splits md_triv.splits prod.splits)
    apply(auto split: option.splits)
*)

(* TODO: need assumption about mem being empty? *)
  have 3: "|sem_final| {~ ?P2~}
[ G (Sc (Cnum i2)) []] 
  {~(\<lambda> st . ?P2 st \<and> (\<exists> x1 x2 . LOut calc_lift' (Cnum i2) st = (x1, x2, i2)))~}"
(is "|sem_final| {~ ?P2 ~}
[ G (Sc (Cnum i2)) []] 
  {~ ?P3~}")
    apply(rule HT'Conseq)
      apply(rule_tac P' = "\<lambda> _ . True" in Calc_Final)
       apply(fast) apply(fast) 

      apply(simp add: mem_lift1_def calc_lift'_def schem_lift_defs merge_l_def snd_l_def fst_l_def
     prio_l_def option_l_def triv_l_def)

     apply(simp)

      apply( simp add: mem_lift1_def calc_lift'_def schem_lift_defs merge_l_def snd_l_def fst_l_def
     prio_l_def option_l_def triv_l_def
)
    apply(fastforce)


    apply(simp add: calc_lift'_def schem_lift_defs merge_l_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
mem_lift1_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S
split:
option.splits md_prio.splits md_triv.splits prod.splits)
    done


    (*
      , G (Sm (Sread (STR ''arg2'') (Reg_c))) []
      , G (Sb Sgtz) []

*)
end