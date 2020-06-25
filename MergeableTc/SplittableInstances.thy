theory SplittableInstances imports Splittable MergeableInstances
begin

instantiation md_triv :: (_) Splittable
begin
definition triv_projs :
"projs =
  [(''triv'', Set.UNIV :: 'a md_triv set, id :: ('a md_triv \<Rightarrow> 'a md_triv))]"

instance proof
  fix d :: "'a md_triv set"
  fix f :: "'a md_triv \<Rightarrow> 'a md_triv"
  fix x :: "'a md_triv"
  fix s :: "char list"
  assume H : "(s, d, f) \<in> set projs"

  consider (1)  "d = UNIV" "f = id" using H
    by(auto simp add:triv_projs)
  then show "is_project x d (f x)"
  proof cases
    case 1
    show "is_project x d (f x)" using 1 
      by(auto simp add:is_project_def is_greatest_def leq_refl)
  qed

next
  show "distinct (map fst (projs :: 'a md_triv projs_t))"
    by(auto simp add:triv_projs)

qed
end

lemma app_inj :
  fixes s1
  shows "inj (\<lambda> s2 . s1 @ s2)"
  by(auto simp add: inj_def)


definition str_app :: "char list \<Rightarrow> char list \<Rightarrow> char list"
  (infixl "[@]" 50)
  where
"str_app a b = a @ b"

lemma str_app_inj :
  fixes s1
  shows "inj (\<lambda> s2 . s1 [@] s2)"
  by(auto simp add: inj_def str_app_def)
 
instantiation option :: (Splittable) Splittableb
begin
(* TODO: make sure this is really what we want *)
(*definition option_projs :
"projs =
  (map (\<lambda> df . 
              case df of (s, d, f) \<Rightarrow> 
                   (''some.''@ s, (Some ` d) \<union> {None}, map_option f)) projs)"
 *)
definition option_projs :
"projs =
  map (map_prod (\<lambda> s . ''some.''[@] s) (map_prod (\<lambda> d . (Some ` d) \<union> {None}) map_option)) projs"
instance proof
  fix d :: "'a option set"
  fix f :: "'a option \<Rightarrow> 'a option"
  fix x :: "'a option"
  fix s :: "char list"
  assume H : "(s, d, f) \<in> set projs"

  obtain d' and f' and s' where Hd' : "d = Some ` d' \<union> {None}" and Hf' : "f = map_option f'" and "s = ''some.''@s'" and Hprojs' : "(s', d', f') \<in> set projs" using H
    by(auto simp add: str_app_def option_projs)

  show "is_project x d (f x)"
  proof(rule is_project_intro)
    show "f x \<in> d"
    proof(cases x)
      case None
      then show ?thesis using Hd' Hf' by auto
    next
      case (Some x')
      have "is_project x' d' (f' x')" using projs_spec[OF Hprojs'] by auto
      hence  "f' x' \<in> d'" by(auto elim:is_project_unfold1)
      then show ?thesis using Hd' Hf' Some by auto
    qed
  next
    show "f x <[ x"
    proof(cases x)
      case None
      then show ?thesis using Hd' Hf' by (auto simp add:leq_refl)
    next
      case (Some x')
      then show ?thesis using Hd' Hf' projs_spec[OF Hprojs', of x']
        by(auto simp add:option_pleq split:option.splits elim:is_project_unfold2)
    qed
  next

    fix xa :: "'a option"
    assume Hi1 : "xa \<in> d"
    assume Hi2 : "xa <[ x"

    consider (1) "xa = None" "x = None" |
             (2) x'  where "xa = None" "x = Some x'" |
             (3) xa' x' where "xa = Some xa'" "x = Some x'"
      using Hi2
      by(cases xa; cases x; auto simp add:option_pleq)
    then  show "xa <[ f x"
    proof cases
      case 1
      thus "xa <[ f x" by (auto simp add:option_pleq bot_spec)
    next
      case 2
      thus "xa <[ f x" by(auto simp add:option_pleq bot_spec)
    next
      case 3
      have H3a : "is_project x' d' (f' x')" using projs_spec[OF Hprojs'] by auto
      have H3b : "xa' \<in> d'" using 3 Hi1 Hd' by(auto)
      have H3c : "xa' <[ x'" using 3 Hi2 by(auto simp add:option_pleq)
      have "xa' <[ f' x'" using is_project_unfold3[OF H3a H3b H3c] by auto
      thus "xa <[ f x" using Hf' 3 by(auto simp add:option_pleq bot_spec split:option.splits)
    qed
  qed

next
  show "distinct (map fst (projs :: 'a option projs_t))"
    using projs_distinct'[of "(projs :: 'a projs_t)"] app_inj
    by(auto simp add:option_projs distinct_map inj_def inj_on_def str_app_def)
qed
end

definition md_prio_map :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a md_prio) \<Rightarrow> ('b md_prio)" where
"md_prio_map f p =
(case p of
  mdp ip p' \<Rightarrow> mdp ip (f p'))"

instantiation md_prio :: (Splittableb) Splittableb
begin
(*
definition prio_projs :
"projs = 
  map (\<lambda> df . case df of (s, d, f) \<Rightarrow> 
          (''prio.''@s, {p . \<exists> i x . x \<in> d \<and> p = mdp i x }, map_md_prio f)) projs"
*)
definition prio_projs :
"projs = 
  map (map_prod
          (\<lambda> s . ''prio.''[@]s) (map_prod (\<lambda> d .  {p . \<exists> i x . x \<in> d \<and> p = mdp i x }) map_md_prio)) projs"
instance proof
  fix d :: "'a md_prio set"
  fix f :: "'a md_prio \<Rightarrow> 'a md_prio"
  fix x :: "'a md_prio"
  fix s :: "char list"
  assume H : "(s, d, f) \<in> set projs"

  obtain d' and f' and s' where Hd' : "d = {p . \<exists> i x . x \<in> d' \<and> p = mdp i x }" and Hf' : "f = map_md_prio f'" and Hs' : "s = ''prio.''@s'"
    and Hprojs' : "(s', d', f') \<in> set projs" using H
    by(auto simp add:prio_projs str_app_def)

  obtain ix and x' where Hx : "x = mdp ix x'" by(cases x; auto)

  have Hproject' : "is_project x' d' (f' x')" using projs_spec[OF Hprojs'] by auto

  show "is_project x d (f x)"
  proof(rule is_project_intro)
    have "f' x' \<in> d'" using is_project_unfold1[OF Hproject'] by auto
    thus "f x \<in> d" using Hd' Hf' Hx by(auto)

  next
    have "f' x' <[ x'" using is_project_unfold2[OF Hproject'] by auto
    thus "f x <[ x" using Hd' Hf' Hx by (auto simp add:prio_pleq)

  next
    fix xa :: "'a md_prio"
    assume Hi1 : "xa \<in> d"
    assume Hi2 : "xa <[ x"

    obtain ixa and xa' where Hxa : "xa = mdp ixa xa'" by(cases xa; auto)
    obtain fx' where Hfx : "f x = mdp ix fx'" using Hf' Hx by(cases "f x"; auto)
    
    consider (1) "ixa < ix" |
             (2) "ixa > ix" |
             (3) "ixa = ix" "xa' <[ x'" using Hi2 Hxa Hfx Hx
      by(auto simp add:prio_pleq split:md_prio.splits if_split_asm) 
    then show "xa <[ f x"
    proof cases
      case 1
      thus "xa <[ f x" using Hi2 Hxa Hfx Hx by(auto simp add:prio_pleq)
    next
      case 2
      thus "xa <[ f x" using Hi2 Hxa Hfx Hx by(auto simp add:prio_pleq)
    next
      case 3
      have H3a : "is_project x' d' (f' x')" using projs_spec[OF Hprojs'] by auto
      have H3b : "xa' \<in> d'" using 3 Hi1 Hd' Hxa by(auto)
      have H3c : "xa' <[ x'" using 3 Hi2 by(auto simp add:option_pleq)
      have "xa' <[ f' x'" using is_project_unfold3[OF H3a H3b H3c] by auto
      thus "xa <[ f x" using Hf' 3 Hxa Hfx Hf' Hx by(auto simp add:prio_pleq bot_spec split:md_prio.splits)
    qed
  qed

next
  show "distinct (map fst (projs :: 'a md_prio projs_t))"
    using projs_distinct'[of "(projs :: 'a projs_t)"] app_inj
    by(auto simp add:prio_projs distinct_map inj_def inj_on_def str_app_def)
qed
end


instantiation prod :: (Splittableb, Splittableb) Splittableb
begin
(*
definition prod_projs :
"projs =
  (''fst'', { ab . \<exists> a . ab = (a, \<bottom>)}, map_prod id (\<lambda> _ . \<bottom>)) #
  (''snd'', { ab . \<exists> b . ab = (\<bottom>, b)}, map_prod (\<lambda> _ . \<bottom>) id) #
  (map (\<lambda> (sdf :: char list * 'a set * ('a \<Rightarrow> 'a)) . 
              case sdf of (s, d, f) \<Rightarrow> 
                   (''fst.'' @ s, { ab . \<exists> a . ab = (a, \<bottom>) \<and> a \<in> d}, map_prod f (\<lambda> _ . \<bottom>))) projs) @
  (map (\<lambda> (sdf :: char list * 'b set * ('b \<Rightarrow> 'b)) .
              case sdf of (s, d, f) \<Rightarrow>
                   (''snd.'' @ s, { ab . \<exists> b . ab = (\<bottom>, b) \<and> b \<in> d}, map_prod (\<lambda> _ . \<bottom>) f)) projs)"
*)
definition prod_projs :
"projs =
  (''fst'', { ab . \<exists> a . ab = (a, \<bottom>)}, map_prod id (\<lambda> _ . \<bottom>)) #
  (''snd'', { ab . \<exists> b . ab = (\<bottom>, b)}, map_prod (\<lambda> _ . \<bottom>) id) #
  (map (map_prod (\<lambda> s . ''fst.'' [@] s) (map_prod (\<lambda> d . { ab . \<exists> a . ab = (a, \<bottom>) \<and> a \<in> d}) (\<lambda> f . map_prod f (\<lambda> _ . \<bottom>)))) projs) @
  (map (map_prod (\<lambda> s . ''snd.'' [@] s) (map_prod (\<lambda> d . { ab . \<exists> b . ab = (\<bottom>, b) \<and> b \<in> d}) (\<lambda> f . map_prod (\<lambda> _ . \<bottom>) f))) projs)"

instance proof
  fix d :: "('a * 'b) set"
  fix f :: "('a * 'b \<Rightarrow> 'a * 'b)"
  fix x :: "'a * 'b"
  fix s :: "char list"
  assume Hproj : "(s, d, f) \<in> set projs"

  obtain xa and xb where Hx : "x = (xa, xb)" by(cases x; auto)

  consider (1) s' d' f' where "d = { ab . \<exists> a . ab = (a, \<bottom>) \<and> a \<in> d'}" and "f = map_prod f' (\<lambda> _ . \<bottom>)" and "s = ''fst.''@ s'" and "(s', d', f') \<in> set projs" |
           (2) s' d' f' where "d = { ab . \<exists> b . ab = (\<bottom>, b) \<and> b \<in> d'}" and "f = map_prod (\<lambda> _ . \<bottom>) f'" and "s = ''snd.''@ s'" and "(s', d', f') \<in> set projs" |
           (3) "s = ''fst''" and "d = { ab . \<exists> a . ab = (a, \<bottom>)}" and "f = map_prod id (\<lambda> _ . \<bottom>)" |
           (4) "s = ''snd''" and "d = { ab . \<exists> b . ab = (\<bottom>, b)}" and "f = map_prod (\<lambda> _ . \<bottom>) id"
    using Hproj
    by(auto simp add:prod_projs str_app_def)

  then show "is_project x d (f x)"
  proof cases
    case 1
    assume Hd' : "d = { ab . \<exists> a . ab = (a, \<bottom>) \<and> a \<in> d'}"
    assume Hf' : "f = map_prod f' (\<lambda> _ . \<bottom>)"
    assume Hproj' : "(s', d', f') \<in> set projs"

    have Hproject' : "is_project xa d' (f' xa)" using projs_spec[OF Hproj'] by auto

    show "is_project x d (f x)"
    proof(rule is_project_intro)
      have "f' xa \<in> d'" using is_project_unfold1[OF Hproject'] by auto
      thus "f x \<in> d" using Hd' Hf' Hx by(auto)

    next
      have "f' xa <[ xa" using is_project_unfold2[OF Hproject'] by auto
      thus "f x <[ x" using Hd' Hf' Hx bot_spec by(auto simp add:prod_pleq)

    next
      fix y :: "'a * 'b"
      assume Hi1 : "y \<in> d"
      assume Hi2 : "y <[ x"

      obtain ya and yb where Hy : "y = (ya, yb)" by(cases y; auto)
      have H3a : "is_project xa d' (f' xa)" using projs_spec[OF Hproj'] by auto
      have H3b : "ya \<in> d'" using Hproj' Hi1 Hd' Hy by(auto)
      have H3c : "ya <[ xa" using  Hproj' Hi2 Hy Hx by(auto simp add:prod_pleq)
      have "ya <[ f' xa" using is_project_unfold3[OF H3a H3b H3c] by auto
      thus "y <[ f x" using Hi1 Hf' Hx Hy Hd' by(auto simp add:prod_pleq bot_spec)
    qed

  next
    case 2
    assume Hd' : "d = { ab . \<exists> b . ab = (\<bottom>, b) \<and> b \<in> d'}"
    assume Hf' : "f = map_prod (\<lambda> _ . \<bottom>) f'"
    assume Hproj' : "(s', d', f') \<in> set projs"

    have Hproject' : "is_project xb d' (f' xb)" using projs_spec[OF Hproj'] by auto

    show "is_project x d (f x)"
    proof(rule is_project_intro)
      have "f' xb \<in> d'" using is_project_unfold1[OF Hproject'] by auto
      thus "f x \<in> d" using Hd' Hf' Hx by(auto)

    next
      have "f' xb <[ xb" using is_project_unfold2[OF Hproject'] by auto
      thus "f x <[ x" using Hd' Hf' Hx bot_spec by(auto simp add:prod_pleq)

    next
      fix y :: "'a * 'b"
      assume Hi1 : "y \<in> d"
      assume Hi2 : "y <[ x"

      obtain ya and yb where Hy : "y = (ya, yb)" by(cases y; auto)
      have H3a : "is_project xb d' (f' xb)" using projs_spec[OF Hproj'] by auto
      have H3b : "yb \<in> d'" using Hproj' Hi1 Hd' Hy by(auto)
      have H3c : "yb <[ xb" using  Hproj' Hi2 Hy Hx by(auto simp add:prod_pleq)
      have "yb <[ f' xb" using is_project_unfold3[OF H3a H3b H3c] by auto
      thus "y <[ f x" using Hi1 Hf' Hx Hy Hd' by(auto simp add:prod_pleq bot_spec)
    qed

  next
    case 3
    assume Hd : "d = { ab . \<exists> a . ab = (a, \<bottom>)}"
    assume Hf : "f = map_prod id (\<lambda> _ . \<bottom>)"

    show "is_project x d (f x)"
    proof(rule is_project_intro)
      show "f x \<in> d" using Hd Hf Hx by(auto)

    next
      show "f x <[ x" using Hd Hf Hx 
        by(auto simp add:prod_pleq leq_refl bot_spec)

    next
      fix y :: "'a * 'b"
      assume Hi1 : "y \<in> d"
      assume Hi2 : "y <[ x"

      show "y <[ f x" using Hi1 Hi2 Hd Hf Hx
        by(auto simp add:is_project_def prod_pleq leq_refl)
    qed

  next
    case 4
    assume Hd : "d = { ab . \<exists> b . ab = (\<bottom>, b)}"
    assume Hf : "f = map_prod (\<lambda> _ . \<bottom>) id"

    show "is_project x d (f x)"
    proof(rule is_project_intro)
      show "f x \<in> d" using Hd Hf Hx by(auto)

    next
      show "f x <[ x" using Hd Hf Hx 
        by(auto simp add:prod_pleq leq_refl bot_spec)

    next
      fix y :: "'a * 'b"
      assume Hi1 : "y \<in> d"
      assume Hi2 : "y <[ x"

      show "y <[ f x" using Hi1 Hi2 Hd Hf Hx
        by(auto simp add:is_project_def prod_pleq leq_refl)
    qed
  qed

next
  show "distinct (map fst (projs :: ('a * 'b) projs_t))"
    using projs_distinct'[of "(projs :: 'a projs_t)"]
          projs_distinct'[of "(projs :: 'b projs_t)"] app_inj
    by(auto simp add:prod_projs distinct_map inj_def inj_on_def str_app_def)
qed
end
(*
instantiation sum :: (Splittableb, Splittableb) Splittableb
begin
definition sum_projs :
"projs =
  (''inl'', { ab . \<exists> a . ab = Inl a} \<union> {Inr \<bottom>}, map_sum id (\<lambda> _ . \<bottom>)) #
  (''inr'', { ab . \<exists> b . ab = Inr b} \<union> {Inl \<bottom>}, map_sum (\<lambda> _ . \<bottom>) id) #
  (map (map_prod (\<lambda> s . ''inl.'' @ s) (map_prod (\<lambda> d . { ab . \<exists> a . ab = Inl a \<and> a \<in> d} \<union> {Inr \<bottom>}) (\<lambda> f . map_sum f (\<lambda> _ . \<bottom>)))) projs) @
  (map (map_prod (\<lambda> s . ''inr.'' @ s) (map_prod (\<lambda> d . { ab . \<exists> b . ab = Inr b\<and> b \<in> d} \<union> {Inl \<bottom>}) (\<lambda> f . map_sum (\<lambda> _ . \<bottom>) f))) projs)"
*)
end