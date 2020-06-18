theory Compose
  imports "../MergeableTc/Mergeable" "../MergeableTc/Pord" "../MergeableTc/Splittable"
begin

(* idea. for composition we need
- an ordered domain (for the output semantics)
- two input types
- semantics on the input types
- inject and project

*)

(* NOTE: while we don't require the Mergeable instance here
to have a least element, it very likely will need one to
make the injections/projections work. Likewise, the "source" types
for the Views will need to be ordered *)

(* TODO: do we need ordering on domains? or can we get away with just
   ordering on range? *)

(* TODO: is what follows sufficient?

*)

(* TODO: make this n-ary instead of binary? *)
class Comp = Mergeableb + Splittableb +
  (* idea: we call these with
     - an 'a \<in> syn1 representing the syntax
     - an 'a \<in> st1 representing the state *)
  fixes sem1 :: "('a :: Splittable) \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes sem2 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

  fixes st1_name :: "'a itself \<Rightarrow> char list"
  fixes st2_name :: "'a itself \<Rightarrow> char list"
  fixes syn1_name :: "'a itself \<Rightarrow> char list"
  fixes syn2_name :: "'a itself \<Rightarrow> char list"

  assumes Proj_Wf_St1 : "st1_name t \<in> projs_names (t)"
  assumes Proj_Wf_St2 : "st2_name t \<in> projs_names (t)"
  assumes Proj_Wf_Syn1 : "syn1_name t \<in> projs_names (t)"
  assumes Proj_Wf_Syn2 : "syn2_name t \<in> projs_names (t)"

  assumes Sem1_Dom : "st \<in> (sdom (sem1_name t)) \<Longrightarrow>
                      syn \<in> (sdom (syn1_name t)) \<Longrightarrow>
                      sem1 syn st \<in> (sdom (sem1_name t))"
  assumes Sem2_Dom : "st \<in> (sdom (sem2_name t)) \<Longrightarrow>
                      syn \<in> (sdom (syn1_name t)) \<Longrightarrow>
                      sem2 syn st \<in> (sdom (sem2_name t))"

  assumes Sem1_Mono : "syn \<in> (sdom (syn1_name t)) \<Longrightarrow>
                       syn' \<in> (sdom (syn1_name t)) \<Longrightarrow>
                       syn <[ syn' \<Longrightarrow>
                       sem1 syn st <[ sem1 syn' st"

  assumes Sem2_Mono : "syn \<in> (sdom (syn2_name t)) \<Longrightarrow>
                       syn' \<in> (sdom (syn2_name t)) \<Longrightarrow>
                       syn <[ syn' \<Longrightarrow>
                       sem2 syn st <[ sem2 syn' st"

  (* TODO: are these axioms enough? *)
  assumes Pres :
  "st1 \<in> (sdom (st1_name t)) \<Longrightarrow>
   st2 \<in> (sdom (st2_name t)) \<Longrightarrow>
   syn1 \<in> (sdom (syn1_name t)) \<Longrightarrow>
   syn2 \<in> (sdom (syn2_name t)) \<Longrightarrow>
   has_sup {st1, st2} \<Longrightarrow>
   has_sup {syn1, syn2} \<Longrightarrow>
   has_sup {sem1 syn1 st1, sem2 syn2 st2}"

definition cst_l :: "('a :: Comp) set" where
"cst_l = (sdom (st1_name (TYPE('a))))"

definition cstprj_l :: "'a :: Comp \<Rightarrow> 'a" where
"cstprj_l = sprj (st1_name (TYPE('a)))"

definition cst_r :: "('a :: Comp) set" where
"cst_r = (sdom (st2_name (TYPE('a))))"

definition cstprj_r :: "'a :: Comp \<Rightarrow> 'a" where
"cstprj_r = sprj (st2_name (TYPE('a)))"

definition csyn_l :: "('a :: Comp) set" where
"csyn_l = (sdom (syn1_name (TYPE('a))))"

definition csynprj_l :: "'a :: Comp \<Rightarrow> 'a" where
"csynprj_l = sprj (syn1_name (TYPE('a)))"

definition csyn_r :: "('a :: Comp) set" where
"csyn_r = (sdom (syn2_name (TYPE('a))))"

definition csynprj_r :: "'a :: Comp \<Rightarrow> 'a" where
"csynprj_r = sprj (syn2_name (TYPE('a)))"


typedef (overloaded) 'a cst_lt = "cst_l :: ('a :: Comp) set"
proof(-)

  obtain d and f where Hdf : "Some (d, f) = map_of (projs :: ('a projs_t)) (st1_name (TYPE('a)))"
      using Proj_Wf_St1[of "(TYPE('a))"]
            projs_distinct'[of "projs :: 'a projs_t"]
      by(auto simp add:projs_names_def)
    

  hence "(st1_name (TYPE('a)), d, f) \<in> set (projs :: 'a projs_t)"
    by(auto intro:map_of_SomeD)

  hence "\<bottom> \<in> d" by (auto elim:projs_bot)

  thus ?thesis using Hdf by(cases "map_of (projs :: 'a projs_t) (st1_name (TYPE('a)))"; auto simp add:cst_l_def sdom_def sdom'_def)
qed

typedef (overloaded) 'a cst_rt = "cst_r :: ('a :: Comp) set"
proof(-)

  obtain d and f where Hdf : "Some (d, f) = map_of (projs :: ('a projs_t)) (st2_name (TYPE('a)))"
      using Proj_Wf_St2[of "(TYPE('a))"]
            projs_distinct'[of "projs :: 'a projs_t"]
      by(auto simp add:projs_names_def)
    

  hence "(st2_name (TYPE('a)), d, f) \<in> set (projs :: 'a projs_t)"
    by(auto intro:map_of_SomeD)

  hence "\<bottom> \<in> d" by (auto elim:projs_bot)

  thus ?thesis using Hdf by(cases "map_of (projs :: 'a projs_t) (st2_name (TYPE('a)))"; auto simp add:cst_r_def sdom_def sdom'_def)
qed

typedef (overloaded) 'a csyn_lt = "csyn_l :: ('a :: Comp) set"
proof(-)

  obtain d and f where Hdf : "Some (d, f) = map_of (projs :: ('a projs_t)) (syn1_name (TYPE('a)))"
      using Proj_Wf_Syn1[of "(TYPE('a))"]
            projs_distinct'[of "projs :: 'a projs_t"]
      by(auto simp add:projs_names_def)
    

  hence "(syn1_name (TYPE('a)), d, f) \<in> set (projs :: 'a projs_t)"
    by(auto intro:map_of_SomeD)

  hence "\<bottom> \<in> d" by (auto elim:projs_bot)

  thus ?thesis using Hdf by(cases "map_of (projs :: 'a projs_t) (syn1_name (TYPE('a)))"; auto simp add:csyn_l_def sdom_def sdom'_def)
qed

typedef (overloaded) 'a csyn_rt = "csyn_r :: ('a :: Comp) set"
proof(-)

  obtain d and f where Hdf : "Some (d, f) = map_of (projs :: ('a projs_t)) (syn2_name (TYPE('a)))"
      using Proj_Wf_Syn2[of "(TYPE('a))"]
            projs_distinct'[of "projs :: 'a projs_t"]
      by(auto simp add:projs_names_def)
    

  hence "(syn2_name (TYPE('a)), d, f) \<in> set (projs :: 'a projs_t)"
    by(auto intro:map_of_SomeD)

  hence "\<bottom> \<in> d" by (auto elim:projs_bot)

  thus ?thesis using Hdf by(cases "map_of (projs :: 'a projs_t) (syn2_name (TYPE('a)))"; auto simp add:csyn_r_def sdom_def sdom'_def)
qed


(*
typedef (overloaded) 'a dom2 = "cdom_r :: ('a :: Comp) set"
*)
(* parallel composition *)
definition pcomp :: "('a :: Comp) \<Rightarrow> 'a \<Rightarrow> 'a" where
"pcomp syn st =
  [^ [^ sem1 (csynprj_l syn) (cstprj_l st), sem2 (csynprj_r syn) (cstprj_r st) ^], st ^]"

definition pcomp' :: "('a :: Comp) \<Rightarrow> 'a \<Rightarrow> 'a" where
"pcomp' syn st =
  [^ [^ sem2 (csynprj_r syn) (cstprj_r st), sem1 (csynprj_l syn) (cstprj_l st) ^], st ^]"

(* "real" parallel semantics, which may contain more information *)
definition pcomp_real :: "('a :: Comp) \<Rightarrow> 'a \<Rightarrow> 'a" where
"pcomp_real syn st =
  [^ sem1 (csynprj_l syn) (cstprj_l st), [^ sem2 (csynprj_r syn) (cstprj_r st), st ^]^]"

definition pcomp_real' :: "('a :: Comp) \<Rightarrow> 'a \<Rightarrow> 'a" where
"pcomp_real' syn st =
  [^ sem2 (csynprj_r syn) (cstprj_r st), [^ sem1 (csynprj_l syn) (cstprj_l st), st ^]^]"


end