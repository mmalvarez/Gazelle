theory Compose
  imports "../MergeableTc/Mergeable" "../MergeableTc/Pord" "../MergeableTc/Splittable"
  "../MergeableTc/MergeableInstances"
  "../MergeableTc/SplittableInstances"
begin

(* idea. for composition we need
- an ordered domain (for the output semantics)
- two input types
- semantics on the input types
- inject and project

*)

class PreComp = Mergeableb + Splittableb +
  assumes projs_orth :
    "\<And> s1 s2 .
      s1 \<in> projs_names (TYPE('a)) \<Longrightarrow>
      s2 \<in> projs_names (TYPE('a)) \<Longrightarrow>
      s1 \<noteq> s2 \<Longrightarrow>
      sdom s1 \<inter> sdom s2 = {\<bottom> :: ('a :: {Mergeableb, Splittableb})}"

lemma projs_orth' :
  fixes projs' :: "('a :: PreComp) projs_t"
  fixes s1 s2 :: "char list"
  assumes Hp : "projs' = projs"
  assumes Hs1 : "s1 \<in> projs_names (TYPE('a))"
  assumes Hs2 : "s2 \<in> projs_names (TYPE('a))"
  assumes Hneq : "s1 \<noteq> s2"
  shows "sdom s1 \<inter> sdom s2 = {\<bottom> :: ('a :: {PreComp})}" using 
    projs_orth[OF Hs1 Hs2 Hneq]
  by(auto)

(* problem: this can be Some (None) e.g. (for the option option case) *)
instantiation option :: (PreComp) PreComp begin
instance proof
  fix s1 s2 :: "char list"
  assume Hs1 : "s1 \<in> projs_names (TYPE('a option))"
  assume Hs2 : "s2 \<in> projs_names (TYPE('a option))"
  assume Hneq : "s1 \<noteq> s2"
  show "sdom s1 \<inter> sdom s2 = {\<bottom> :: 'a option}"
  proof(-)
    obtain d1 and f1 where Hl1 : "(s1, d1, f1) \<in> set (projs :: 'a option projs_t)" 
      using s_name_lookup[OF Hs1] by auto
    obtain d2 and f2 where Hl2 : "(s2, d2, f2) \<in> set (projs :: 'a option projs_t)"
      using s_name_lookup[OF Hs2] by auto

    have Hsdom'1 : "sdom' s1 = Some d1" using sdom'_defined[OF Hl1] by auto
    have Hsdom'2 : "sdom' s2 = Some d2" using sdom'_defined[OF Hl2] by auto

    obtain d1' and f1' and s1' where Hd1' : "d1 = Some ` d1' \<union> {None}" and Hf1' : "f1 = map_option f1'" and Hs1' : "s1 = ''some.''@s1'" and Hprojs1' : "(s1', d1', f1') \<in> set projs" using Hl1
      by(auto simp add: str_app_def option_projs)
  
    obtain d2' and f2' and s2' where Hd2' : "d2 = Some ` d2' \<union> {None}" and Hf' : "f2 = map_option f2'" and Hs2': "s2 = ''some.''@s2'" and Hprojs2' : "(s2', d2', f2') \<in> set projs" using Hl2
      by(auto simp add: str_app_def option_projs)

    have Hsdom'1' : "sdom' s1' = Some d1'" using sdom'_defined[OF Hprojs1'] by auto
    have Hsdom'2' : "sdom' s2' = Some d2'" using sdom'_defined[OF Hprojs2'] by auto


    have Hneq' : "s1' \<noteq> s2'" using Hs1' Hs2' Hneq by auto
  
    have Hname1' : "s1' \<in> projs_names (TYPE('a))" using Hprojs1' imageI[OF Hprojs1', of fst]
      by(auto simp add:projs_names_def option_projs )
  
    have Hname2' : "s2' \<in> projs_names (TYPE('a))" using Hprojs1' imageI[OF Hprojs2', of fst]
      by(auto simp add:projs_names_def option_projs )
  
    have Conc' : "sdom s1' \<inter> sdom s2' = {\<bottom> :: 'a}" using
        projs_orth[OF Hname1' Hname2' Hneq'] by auto

    hence Conc' : "d1' \<inter> d2' = {\<bottom> :: 'a}" using Hsdom'1' Hsdom'2' 
      by(simp add: sdom_def)

    thus ?thesis using Hd1' Hd2' Hsdom'1 Hsdom'2

      apply(auto simp add: option_bot sdom_def)
      apply(auto simp add: sdom_def sdom'_def)

(* union = bsup (?)
   intersection = project into each other *)
fun pr_opD :: "('a :: PreComp) itself \<Rightarrow> pr_op \<Rightarrow> ('a set * ('a \<Rightarrow> 'a)) option" where
"pr_opD _ (pr_s s) = map_of (projs :: 'a projs_t) s"
| "pr_opD t (pr_union o1 o2) =
   (case (pr_opD t o1) of
      None \<Rightarrow> None
      | Some (s1, f1) \<Rightarrow>
        (case (pr_opD t o2) of
          None \<Rightarrow> None
          | Some (s2, f2) \<Rightarrow>
              Some ({ x . \<exists> x1 x2 . x1 \<in> s1 \<and> x2 \<in> s2 \<and>
                      x = bsup x1 x2},
                    (\<lambda> x . bsup (f1 x) (f2 x)))))"
| "pr_opD _ _ = None"


(* TODO: make this n-ary instead of binary? *)
class Comp = PreComp +
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