theory ComposeExamples imports  "../MergeableTc/Mergeable" "../MergeableTc/MergeableInstances" "../MergeableTc/SplittableInstances" HOL.Lifting HOL.Lifting_Set LiftUtils

begin

(* new approach
   - define syntax, semantics as normal
   - define a combined representation using Mergeable+Splittable
   - ** use "lifting" to translate semantics into the projected version
*)

datatype calc =
  Cadd int
  | Csub int
  | Cmul int
  | Cdiv int
  | Creset int
  | Cskip

(*
datatype calc_st = CSi int
*)
definition calc_sem :: "calc \<Rightarrow> int \<Rightarrow> int" where
"calc_sem syn st = 
  (case syn of
     (Cadd i) \<Rightarrow> st + i
    |(Csub i) \<Rightarrow> st - i
    |(Cmul i) \<Rightarrow> st * i
    |(Cdiv i) \<Rightarrow> divide_int_inst.divide_int st i
    |(Creset i) \<Rightarrow> i
    | Cskip \<Rightarrow> st)"



(* need "liftable" typeclass"? *)

datatype print =
  Pprint
  | Preset
  | Pskip


type_synonym state = "int md_triv option md_prio * int list md_triv option"

datatype syn =
  Sadd int
  | Ssub int
  | Smul int
  | Sdiv int
  | Sreset int
  | Sseq

definition print_trans :: "syn \<Rightarrow> print" where
"print_trans c = 
  (case c of
    Sreset _ \<Rightarrow> Preset
    | Sseq \<Rightarrow> Pskip
    | _ \<Rightarrow> Pprint)"

definition calc_trans :: "syn \<Rightarrow> calc" where
"calc_trans c =
  (case c of
    Sadd i \<Rightarrow> (Cadd i)
    | Ssub i \<Rightarrow> (Csub i)
    | Smul i \<Rightarrow> (Cmul i)
    | Sdiv i \<Rightarrow> (Cdiv i)
    | Sreset i \<Rightarrow> (Creset i)
    | _ \<Rightarrow> Cskip)"
    

type_synonym print_st = "(int * int list)"
definition print_sem :: "print \<Rightarrow> print_st \<Rightarrow> print_st" where
"print_sem syn st =
  (case st of
    (sti, stl) \<Rightarrow>
      (case syn of
         Pprint \<Rightarrow> (sti, stl @ [sti])
         | Preset \<Rightarrow> (sti, [])))"



(*
definition print_sem_l :: "syn \<Rightarrow> state \<Rightarrow> state" where
  "print_sem_l = 
    l_map2' (print_trans)
            (prod_lm ((fst_l (prio_l_zero (option_l (triv_l (id_l))))))
                     ((snd_l (option_l (triv_l (id_l)))))) print_sem"
*)
definition print_sem_l :: "syn \<Rightarrow> state \<Rightarrow> state" where
  "print_sem_l = 
    l_map2' (print_trans)
            (prod_l ((prio_l_zero (option_l (triv_l (id_l)))))
                    ((option_l (triv_l (id_l))))) print_sem"


term "(prod_lm ((fst_l (prio_l_zero (option_l (triv_l (id_l))))))
                     ((snd_l (option_l (triv_l (id_l))))))"
term "(prod_l ((prio_l_zero (option_l (triv_l (id_l)))))
                     ((option_l (triv_l (id_l)))))"
term "(fst_l (prio_l_zero (option_l (triv_l (id_l)))))"
term "(snd_l (option_l (triv_l (id_l))))"

value "print_sem_l (Sreset 0)
               (mdp 1 (Some (mdt 1)), Some (mdt []))"

definition calc_sem_l :: "syn \<Rightarrow> state \<Rightarrow> state" where
"calc_sem_l =
  l_map2' calc_trans
    (fst_l (prio_l_inc (option_l (triv_l (id_l))))) calc_sem"

value "calc_sem_l (Sreset 0)
(mdp 1 (Some (mdt 1)), Some (mdt []))"

record ('a, 'b) langcomp =
  Sem1 :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
  Sem2 :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"

definition sup_pres ::
  "('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) \<Rightarrow>
   ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> bool" where
"sup_pres f1 f2 =
 (\<forall> syn :: 'a .
   \<forall> st1 st2 :: 'b .
     has_sup {st1, st2} \<longrightarrow>
     has_sup {f1 syn st1, f2 syn st2})"

lemma sup_pres_unfold :
  fixes f1 f2 :: "('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b)"
  fixes syn :: 'a
  fixes st1 st2 :: 'b
  assumes H : "sup_pres f1 f2"
  assumes Hsup : "has_sup {st1, st2}"
  shows "has_sup {f1 syn st1, f2 syn st2}" using H Hsup
  by(auto simp add:sup_pres_def)

lemma sup_pres_intro :
  fixes f1 f2 :: "('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b)"
  assumes H : "\<And> (syn :: 'a) (st1 :: 'b) (st2 :: 'b) .
                  has_sup {st1, st2} \<Longrightarrow> has_sup {f1 syn st1, f2 syn st2}"
  shows "sup_pres f1 f2" using H
  by(auto simp add:sup_pres_def)

definition sup_pres' ::
  "(('a :: Mergeable) \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) \<Rightarrow>
   ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> bool" where
"sup_pres' f1 f2 =
 (\<forall> syn1 syn2 :: 'a .
   \<forall> st1 st2 :: 'b .
     has_sup {st1, st2} \<longrightarrow>
     has_sup {syn1, syn2} \<longrightarrow>
     has_sup {f1 syn1 st1, f2 syn2 st2})"

(* LIn1 vs LIn2 *)
definition sup_l ::
  "('a1, ('b :: Mergeable)) lifting \<Rightarrow>
   ('a2, ('b :: Mergeable)) lifting \<Rightarrow>
   bool" where
"sup_l l1 l2 =
  (\<forall> a1 a2 b1 b2 .
    has_sup {LIn1 l1 a1, LIn1 l2 a2} \<and>
    (has_sup {b1, b2} \<longrightarrow> has_sup {LIn2 l1 a1 b1, LIn2 l2 a2 b2}))"

lemma sup_l_intro :
  fixes l1 :: "('a1, 'b :: Mergeable) lifting"
  fixes l2 :: "('a2, 'b :: Mergeable) lifting"
  assumes H1 : "\<And> a1 a2 . has_sup {LIn1 l1 a1, LIn1 l2 a2}"
  assumes H2 : "\<And> a1 a2 b1 b2 . has_sup {b1, b2} \<Longrightarrow> has_sup {LIn2 l1 a1 b1, LIn2 l2 a2 b2}"
  shows "sup_l l1 l2" using H1 H2
  by(auto simp add:sup_l_def)

lemma sup_l_unfold1 :
  fixes l1 :: "('a1, 'b :: Mergeable) lifting"
  fixes l2 :: "('a2, 'b :: Mergeable) lifting"
  assumes H : "sup_l l1 l2"
  shows "has_sup {LIn1 l1 a1, LIn1 l2 a2}"
  using H   by(auto simp add:sup_l_def)

lemma sup_l_unfold2 :
  fixes l1 :: "('a1, 'b :: Mergeable) lifting"
  fixes l2 :: "('a2, 'b :: Mergeable) lifting"
  assumes H : "sup_l l1 l2"
  assumes Hb : "has_sup {b1, b2}"
  shows "has_sup {LIn2 l1 a1 b1, LIn2 l2 a2 b2}"
    using H Hb
  by(auto simp add:sup_l_def)


lemma sup_l_prod_fst :
  fixes l1  :: "('a1, 'b1 :: Mergeableb) lifting"
  fixes l1' :: "('a2, 'b1 :: Mergeableb) lifting"
  fixes l2  :: "('a3, 'b2 :: Mergeableb) lifting"
  assumes H : "sup_l l1 l1'"
  shows "sup_l (prod_l l1 l2) (fst_l l1')"
proof(rule sup_l_intro)
  fix a1 :: "('a1 \<times> 'a3)" 
  fix a2 :: "'a2"
  obtain x1 and x2 where Hx : "a1 = (x1, x2)" by (cases a1; auto)
  obtain ub where Hub : "is_sup {LIn1 l1 x1, LIn1 l1' a2} ub"
      using sup_l_unfold1[OF H] Hx
      by(auto simp add:prod_l_def fst_l_def has_sup_def split:prod.splits)
  
  have "is_sup {LIn1 (prod_l l1 l2) a1, LIn1 (fst_l l1') a2} (ub, LIn1 l2 x2)" using  Hub Hx
    by(auto simp add:has_sup_def is_sup_def is_least_def is_ub_def
        prod_pleq prod_l_def fst_l_def bot_spec leq_refl split:prod.splits)
  thus "has_sup {LIn1 (prod_l l1 l2) a1, LIn1 (fst_l l1') a2}" by (auto simp add:has_sup_def)
next
  fix a1::"'a1 \<times> 'a3"
  fix a2::"'a2"
  fix b1 b2:: "'b1 \<times> 'b2"
  assume Hb : "has_sup {b1, b2}"
  obtain x1 and x2 where Hx : "a1 = (x1, x2)" by (cases a1; auto)
  obtain y1 and y2 where Hy : "b1 = (y1, y2)" by (cases b1; auto)
  obtain z1 and z2 where Hz : "b2 = (z1, z2)" by (cases b2; auto)

  have Hub1 : "has_sup {y1, z1}" using Hy Hz Hb
    by(auto simp add:has_sup_def is_sup_def is_least_def is_ub_def prod_pleq)

  obtain ub where Hub : "is_sup {LIn2 l1 x1 y1, LIn2 l1' a2 z1} ub"
      using sup_l_unfold2[OF H Hub1] Hx Hy Hz
      by(auto simp add:prod_l_def fst_l_def has_sup_def split:prod.splits)

  have "is_sup {LIn2 (prod_l l1 l2) a1 b1, LIn2 (fst_l l1') a2 b2} (ub, LIn2 l2 x2 y2)" using  Hub Hx Hy Hz
    by(auto simp add:has_sup_def is_sup_def is_least_def is_ub_def
        prod_pleq prod_l_def fst_l_def bot_spec leq_refl split:prod.splits)
  thus "has_sup {LIn2 (prod_l l1 l2) a1 b1, LIn2 (fst_l l1') a2 b2}" by (auto simp add:has_sup_def)
qed

lemma sup_l_inc_zero :
  fixes l1 :: "('a1, 'b :: Mergeableb) lifting"
  fixes l2:: "('a2, 'b :: Mergeableb) lifting"
  shows "sup_l (prio_l_zero l1) (prio_l_inc l2)"
proof(rule sup_l_intro)
  fix a1 :: "'a1"
  fix a2 :: "'a2"

  (* this is kind of a bogus case *)
  have "is_ub {LIn1 (prio_l_zero l1) a1, LIn1 (prio_l_inc l2) a2} (mdp 1 \<bottom>)"
    by(auto simp add:prio_l_zero_def prio_l_const_def prio_l_def prio_l_inc_def
            has_sup_def is_sup_def is_least_def is_ub_def prio_pleq bot_spec split:md_prio.splits)

  hence 0 : "has_ub {LIn1 (prio_l_zero l1) a1, LIn1 (prio_l_inc l2) a2}"
    by(auto simp add:has_ub_def)

  obtain lub where
    "is_sup {LIn1 (prio_l_zero l1) a1, LIn1 (prio_l_inc l2) a2} lub" 
    using complete2[OF 0] by(auto simp add:has_sup_def)
  

  thus "has_sup {LIn1 (prio_l_zero l1) a1, LIn1 (prio_l_inc l2) a2}"
    by(auto simp add:has_sup_def)
next
  fix a1 :: "'a1"
  fix a2 :: "'a2"
  fix b1 :: "'b md_prio"
  fix b2 :: "'b md_prio"
  assume Hsup : "has_sup {b1, b2}"


  have "is_ub {LIn2 (prio_l_zero l1) a1 b1, LIn2 (prio_l_inc l2) a2 b2} (LIn2 (prio_l_inc l2) a2 b2)"
    by(auto simp add:prio_l_zero_def prio_l_const_def prio_l_def prio_l_inc_def
            leq_refl
            has_sup_def is_sup_def is_least_def is_ub_def prio_pleq bot_spec split:md_prio.splits)

  hence 0 : "has_ub  {LIn2 (prio_l_zero l1) a1 b1, LIn2 (prio_l_inc l2) a2 b2}"
    by(auto simp add:has_ub_def)

  obtain lub where
    "is_sup {LIn2 (prio_l_zero l1) a1 b1, LIn2 (prio_l_inc l2) a2 b2} lub"
    using complete2[OF 0] by(auto simp add:has_sup_def)

  thus "has_sup {LIn2 (prio_l_zero l1) a1 b1, LIn2 (prio_l_inc l2) a2 b2}"
    by(auto simp add:has_sup_def)
qed


(* TODO: could generalize this to talk about syntaxes having supremum *)
definition lc_valid :: "('a, 'b :: Mergeable) langcomp \<Rightarrow> bool" where
"lc_valid l =
  sup_pres (Sem1 l) (Sem2 l)"

definition lc_valid' :: "('a :: Mergeable, 'b :: Mergeable) langcomp \<Rightarrow> bool" where
"lc_valid' l =
  sup_pres' (Sem1 l) (Sem2 l)"


lemma lc_valid_intro :
  fixes l :: "('a, 'b :: Mergeable) langcomp"
  assumes H: "\<And> syn st1 st2 . has_sup {st1, st2} \<Longrightarrow> has_sup {Sem1 l syn st1, Sem2 l syn st2}"
  shows "lc_valid l" using H
  by(auto simp add:lc_valid_def sup_pres_def)

lemma lc_valid_unfold :
  fixes l :: "('a, 'b :: Mergeable) langcomp"
  fixes syn :: 'a
  fixes st1 st2 :: 'b
  assumes H : "lc_valid l"
  assumes Hsup : "has_sup {st1, st2}"
  shows "has_sup {Sem1 l syn st1, Sem2 l syn st2}"
  using H Hsup
  by(auto simp add:lc_valid_def sup_pres_def)


(* new issue: we need to deal with the disconnect between
- sup_l: assumes same initial state
- sup_pres: doesn't
*)
lemma sup_l_pres :
  fixes l1 :: "('a1, 'b :: Mergeable) lifting"
  fixes l2 :: "('a2, 'b :: Mergeable) lifting"
  fixes syn_trans1 :: "'syn \<Rightarrow> 'syn1"
  fixes syn_trans2 :: "'syn \<Rightarrow> 'syn2"
  fixes f1 :: "'syn1 \<Rightarrow> 'a1 \<Rightarrow> 'a1"
  fixes f2 :: "'syn2 \<Rightarrow> 'a2 \<Rightarrow> 'a2"
  assumes Hsl : "sup_l l1 l2"
  shows "sup_pres
    (l_map2' syn_trans1 l1 f1)
    (l_map2' syn_trans2 l2 f2)"
proof(rule sup_pres_intro)
  fix syn :: 'syn
  fix st1 :: 'b
  fix st2 :: 'b
  assume Hsup : "has_sup {st1, st2}"
  show "has_sup {l_map2' syn_trans1 l1 f1 syn st1, l_map2' syn_trans2 l2 f2 syn st2}"
    using Hsup sup_l_unfold2[OF Hsl]
    by(auto simp add: l_map2'_def split:option.splits)
qed

definition pcomp :: "('a, 'b :: Mergeable) langcomp \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b)" where
"pcomp l a b =
  [^ [^ Sem1 l a b, Sem2 l a b ^], b ^]"

definition pcomp' :: "('a, 'b :: Mergeable) langcomp \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b)" where
"pcomp' l a b =
  [^ [^ Sem2 l a b, Sem1 l a b ^], b ^]"

lemma lc_valid_comp :
  fixes l :: "('a, 'b :: Mergeable) langcomp"
  assumes Hv : "lc_valid l"
  shows "pcomp l = pcomp' l"
proof(-)
  have Conc' : "\<And> (b :: 'b ::Mergeable) (a :: 'a) . pcomp l a b = pcomp' l a b"
  proof(-)
    fix a :: 'a
    fix b :: "'b :: Mergeable"
    have "is_sup {b} b"
      using leq_refl by(auto simp add:is_sup_def has_sup_def is_least_def is_ub_def)
    hence 0 : "has_sup {b, b}" by (auto simp add:has_sup_def)
    thus  "pcomp l a b = pcomp' l a b"
      using bsup_comm[OF lc_valid_unfold[OF Hv 0]]
      by(simp add:pcomp_def pcomp'_def)
  qed
  
  thus ?thesis
    by auto
qed
    

definition example_lc :: "(syn, state) langcomp" where
"example_lc =
  \<lparr> Sem1 = calc_sem_l
  , Sem2 = print_sem_l \<rparr>"

value "pcomp example_lc (Smul 9) (mdp 3 (Some (mdt 1)), Some (mdt []))"
value "pcomp' example_lc (Smul 2) (mdp 1 (Some (mdt 1)), Some (mdt []))"

(*
lemma sup_l_pres :
  fixes l1 :: "('a1, 'b :: Mergeableb) lifting"
  fixes l2:: "('a2, 'b :: Mergeableb) lifting"
  assumes H :"sup_l l1 l2"
  
shows "l_map2' syn_trans l1 f1
*)
(* remaining steps
- link sup_l to lc_valid
- link to l_map2'
- figure otu an ergonomic way to apply this to our semantics
- make sure syntax translation doesn't cause headaches *)

lemma lc_valid_lift :
  assumes Hlc : "lc = \<lparr> Sem1 = (l_map2' syn_trans1 l1 f1)
                      , Sem2 = (l_map2' syn_trans2 l2 f2) \<rparr>" 
  assumes Hsl : "sup_l l1 l2"
  shows "lc_valid lc"
proof(-)
  have "sup_pres
    (l_map2' syn_trans1 l1 f1)
    (l_map2' syn_trans2 l2 f2)" using sup_l_pres[OF Hsl] by auto

  thus "lc_valid lc" by(auto simp add:Hlc lc_valid_def)
qed


lemma sup_l_comm :
  fixes l1  :: "('a1, 'b :: Mergeableb) lifting"
  fixes l2 :: "('a2, 'b :: Mergeableb) lifting"
  assumes H : "sup_l l1 l2"
  shows "sup_l l2 l1"
proof(rule sup_l_intro)
  fix a2 :: 'a2
  fix a1 :: "'a1"
  have "{LIn1 l2 a2, LIn1 l1 a1} = {LIn1 l1 a1, LIn1 l2 a2}" by auto
  thus "has_sup {LIn1 l2 a2, LIn1 l1 a1}" using sup_l_unfold1[OF H, of a1 a2] by auto
next
  fix a2 :: 'a2
  fix a1 :: 'a1
  fix b1 b2 :: 'b
  assume Hs : "has_sup {b1, b2}"

  have "{b2, b1} = {b1, b2}" by auto
  hence Hs' : "has_sup {b2, b1}" using Hs by auto
  have "{LIn2 l1 a1 b2, LIn2 l2 a2 b1} = {LIn2 l2 a2 b1, LIn2 l1 a1 b2}" by auto

  thus "has_sup {LIn2 l2 a2 b1, LIn2 l1 a1 b2}"
    using sup_l_unfold2[OF H Hs', of a1 a2] by auto
qed

(* need lemmas to help us talk about sup's with lifting
   the main thing here is priority guaranteeing existence of
   sup *)
lemma ex_lc_valid :
  "lc_valid example_lc" 
  apply(rule lc_valid_lift)
   apply(simp add: example_lc_def calc_sem_l_def print_sem_l_def)
  apply(rule sup_l_comm)
  apply(rule sup_l_prod_fst)
  apply(rule sup_l_inc_zero)
  done
  


(*
setup_lifting type_definition_synsem_t

lift_definition print_sem_l_t :: "synsem_t \<Rightarrow> synsem_t \<Rightarrow> synsem_t" is print_sem_l
  done

instantiation synsem_t :: Pord_Weak begin
lift_definition synsem_t_pleq' :: "synsem_t \<Rightarrow> synsem_t \<Rightarrow> bool" 
is "pleq :: synsem \<Rightarrow> synsem \<Rightarrow> bool" done

definition synsem_t_pleq :
"pleq = synsem_t_pleq'"

instance proof
  fix a :: synsem_t
  show "a <[ a" 
    apply(simp add:synsem_t_pleq) apply(transfer) apply(auto intro:leq_refl)
    done
next
  fix a b c :: synsem_t
  show "a <[ b \<Longrightarrow> b <[ c \<Longrightarrow> a <[ c"
    apply(simp add:synsem_t_pleq) apply(transfer) apply(auto elim:leq_trans)
    done
qed
end

instantiation synsem_t :: Pord begin
instance proof
  fix a b :: synsem_t
  show "a <[ b \<Longrightarrow> b <[ a \<Longrightarrow> a = b" using leq_antisym[of "Rep_synsem_t a" ]
    apply(simp add:synsem_t_pleq; transfer)
    apply(auto)
    done
qed
end

instantiation synsem_t :: Pordc begin
instance proof
  fix a b :: synsem_t
  show " has_ub {a, b} \<Longrightarrow> has_sup {a, b}"
    using complete2[of"Rep_synsem_t a" ]
    apply(simp only:has_ub_def has_sup_def is_sup_def is_ub_def
          is_least_def synsem_t_pleq)
    apply(transfer)
    apply(auto)
    done
qed end

instantiation synsem_t :: Pordb begin
lift_definition synsem_t_bot' :: "synsem_t" 
is "bot :: synsem" done

definition synsem_t_bot :
"bot = synsem_t_bot'"

instance proof
  fix a :: synsem_t
  show "\<bottom> <[ a"
    using bot_spec[of"Rep_synsem_t a" ]
    apply(simp only:synsem_t_pleq synsem_t_bot)
    apply(transfer)
    apply(auto)
    done
qed end

instantiation synsem_t :: Mergeable begin
lift_definition synsem_t_bsup' :: "synsem_t \<Rightarrow> synsem_t \<Rightarrow> synsem_t"
is "bsup :: synsem \<Rightarrow> synsem \<Rightarrow> synsem"
  done
definition synsem_t_bsup :
"bsup = synsem_t_bsup'"

instance proof
  fix a b :: synsem_t
  show "is_bsup a b [^ a, b ^]" 
    using bsup_spec[of "Rep_synsem_t a"]
    unfolding  synsem_t_pleq synsem_t_bot synsem_t_bsup
      is_bsup_def is_sup_def is_ub_def is_least_def is_bub_def
    by(transfer;auto)
qed
end

(* new idea
   we need some kind of way to talk about injecting combined syntax in
   we also need to talk about the domains
   for now we don't need Splittable I think. could be useful later
*)

instantiation synsem_t :: Mergeableb begin
instance proof qed
end



instantiation synsem_t :: Splittableb begin
lift_definition synsem_t_projs' :: "synsem_t projs_t"
is "projs" done

definition synsem_t_projs :
"projs = synsem_t_projs'"

instance proof
  fix s::"char list"
  fix d::"synsem_t set"
  fix f::"synsem_t \<Rightarrow> synsem_t"
  fix x :: "synsem_t"
  assume "(s, d, f) \<in> set projs"
  thus "is_project x d (f x)"
    using projs_spec[of s "Rep_synsem_t ` d" _ "Rep_synsem_t x"]
    unfolding synsem_t_pleq synsem_t_projs is_project_def is_greatest_def
      synsem_t_pleq
    apply(transfer)
    apply(auto)
    done
next
  show "distinct (map fst (projs :: synsem_t projs_t))"
    using projs_distinct'[of "projs :: synsem projs_t"]
    unfolding synsem_t_projs
    apply(transfer) apply(auto)
    done
qed
end
*)

(*
definition sem_lift_triv_prod1 :: "(('a * 'b) \<Rightarrow> ('a * 'b)) \<Rightarrow>
                                   (('a triv * 'b) \<Rightarrow> ('a triv * 'b))" where
"sem_lift_triv_prod1 =
  "
*)

(*
definition print_sem' :: "print md_triv option \<Rightarrow> (int md_triv option md_prio * int list md_triv option)" where
"print_sem'
*)

(* Here the user has to specify the combined state explicitly. I wonder if
  there is a way to avoid even this. *)
(*
   I also wonder if there is a nicer way to specify the overlap.
*)
(* define subtype, 
*)
(*
type_synonym ex_st_t = "(int md_triv option md_prio * int list md_triv option)"
type_synonym ex_syn_t = "(calc md_triv option)"
type_synonym ex_t = "(ex_syn_t * ex_st_t)"
*)

end


(*

instantiation example :: "Pordc" begin
instance proof
  fix a b :: example
  assume H : "has_ub {a, b}"
  show "has_sup {a, b}" using H 
    unfolding has_ub_def is_ub_def has_sup_def is_sup_def is_least_def example_pleq
      
    apply(transfer)
    apply(fold is_ub_def; fold has_ub_def; 
          fold is_least_def; fold is_sup_def; fold has_sup_def)
    apply(rule_tac complete2; auto)
    done
qed

instantiation example :: Mergeable begin
definition example_bsup :
  "bsup = bsup_e"
instance proof
  show
"\<And>(a::example) b::example. is_bsup a b [^ a, b ^]" 
    unfolding is_bsup_def is_sup_def is_least_def is_bub_def is_ub_def example_pleq example_bsup
    
    apply(transfer)
    apply(fold is_ub_def; fold is_least_def; fold is_sup_def; fold is_bub_def)
    apply(fold is_least_def) apply(fold is_bsup_def) apply(rule bsup_spec)
    done
qed
end

instantiation example :: Mergeableb begin
instance proof qed
end

instantiation example :: Comp begin
definition example_dom1 :
  "dom1 = dom1_e"
definition example_dom2 :
  "dom2 = dom2_e"
definition example_sem1 :
  "sem1 = seml_e"
definition example_sem2 :
  "sem2 = semr_e"

instance proof
  show "(\<bottom> :: example) \<in> dom1"
    unfolding example_dom1 example_bot
    apply(transfer)
    apply(simp add:prio_bot prod_bot option_bot)
    done
next
  show "(\<bottom> :: example) \<in> dom2"
    unfolding example_dom2 example_bot
    apply(transfer)
    apply(simp add:prio_bot prod_bot option_bot)
    done
next
  fix x :: example
  assume H1 : "x \<in> dom1"
  show "sem1 x \<in> dom1" using H1
    apply(simp add:example_sem1 example_dom1)
    apply(transfer)
    apply(simp add:seml'' seml'_def split:prod.splits option.splits md_triv.splits md_prio.splits)
    done
next
  fix x :: example
  assume H1 : "x \<in> dom2"
  show "sem2 x \<in> dom2" using H1
    apply(simp add:example_sem2 example_dom2)
    apply(transfer)
    apply(simp add:seml'' seml'_def split:prod.splits option.splits md_triv.splits md_prio.splits)
    done
next

  fix x1 x2 :: example
  assume H1 : "x1 \<in> dom1"
  assume H2 : "x2 \<in> dom2"
  assume Hsup : "has_sup {x1, x2}"

  have "has_ub {x1, x2}" using Hsup by(auto simp add:has_sup_def is_least_def has_ub_def is_sup_def)
  then obtain ub  where Hub :  "is_ub {x1, x2} ub" by (auto simp add:has_ub_def)

  have "has_ub {sem1 x1, sem2 x2}" using H1 H2 Hub
     unfolding has_sup_def has_ub_def is_sup_def is_least_def is_ub_def example_sem1 example_sem2 example_dom1 example_dom2 example_pleq
   proof(transfer)
     fix x1 x2 ub :: ex_syn
     assume H1t : "x1 \<in> {x. \<exists>n x'. x = (mdp n x', None)}"
     assume H2t : "x2 \<in> UNIV"
     assume "\<forall>x\<in>{x1, x2}. x <[ ub"
     hence  Hubt : "is_ub {x1, x2} ub" by(auto simp add:is_ub_def)

     obtain x1l and x1r where "x1 = (x1l, x1r)" by (cases x1; auto)
     then obtain x1p and x1' where Hx1 : "x1 = (mdp x1p x1', x1r)" by (cases x1l; auto)
     obtain x2l and x2r where "x2 = (x2l, x2r)" by (cases x2; auto)
     then obtain x2p and x2' where Hx2 : "x2 = (mdp x2p x2', x2r)" by (cases x2l; auto)
     obtain ubl and ubr where "ub = (ubl, ubr)" by (cases ub; auto)
     then obtain ubp and ub' where Hub' : "ub = (mdp ubp ub', ubr)" by (cases ubl; auto)

     obtain x1'l and x1'r where "seml'' x1 = (x1'l, x1'r)" by(cases "seml'' x1"; auto) 
     then obtain x1'p and x1'' where Hx1' : "seml'' x1 = (mdp x1'p x1'', x1'r)" by (cases x1'l; auto)

     obtain x2'l and x2'r where "semr' x2 = (x2'l, x2'r)" by (cases "semr' x2"; auto)
     then obtain x2'p and x2'' where Hx2' : "semr' x2 = (mdp x2'p x2'', x2'r)" by (cases x2'l; auto)

     have 0 : "ubp \<ge> x1p" using Hx1 Hubt Hub'
       by(auto simp add:is_ub_def prod_pleq prio_pleq triv_pleq split:md_prio.splits if_splits)

     have 1 : "ubp \<ge> x2p" using Hx2 Hubt Hub'
       by(auto simp add:is_ub_def prod_pleq prio_pleq triv_pleq split:md_prio.splits if_splits)

     have Conc'1 : "seml'' x1 <[ (mdp (2 + ubp) None, x2'r)" using Hx1 Hx2 Hx1' Hx2' Hubt Hub' H1t 0
       apply(auto simp add:seml'' semr'_def seml'_def prod_pleq prio_pleq triv_pleq leq_refl option_pleq option_bot is_ub_def split:option.splits md_triv.splits)
       done

     have Conc'2 : "semr' x2 <[ (mdp (2 + ubp) None, x2'r)" using Hx1 Hx2 Hx1' Hx2' Hubt Hub' H1t 1
       by(auto simp add:seml'' semr'_def seml'_def prod_pleq prio_pleq triv_pleq leq_refl option_pleq option_bot split:option.splits md_triv.splits)

     show "\<exists>a. \<forall>x\<in>{seml'' x1, semr' x2}. x <[ a" using Conc'1 Conc'2 by auto
   qed

   thus "has_sup {sem1 x1, sem2 x2}" using complete2 by auto

 qed
end


value [simp] "pcomp (exi (mdp (0 :: nat) (Some (mdt (5 :: int))), Some (mdt [])))"
*)