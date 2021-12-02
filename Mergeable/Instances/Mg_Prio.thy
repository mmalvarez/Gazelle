theory Mg_Prio imports "../Pord" "../Mergeable" "../Mergeable_Facts" "../Bump"
begin
(* md_prio pairs objects with natural numbers, in which the comparison is
 * "lexicographic-like" in that the comparison is made first between the natural numbers,
 * then the data. This is an extremely useful wrapper type in contexts where we want to
 * allow one language component's semantics to "override" the behavior of another,
 * disregarding the ordering of the data being output by the two semantics.
 *)
instantiation md_prio :: (Pord_Weak) Pord_Weak
begin
definition prio_pleq :
"x <[ y =
  (case x of
      mdp xi x' \<Rightarrow> (case y of
                    mdp yi y' \<Rightarrow> (if (xi \<le> yi) then
                                      (if (yi \<le> xi) then pleq x' y' else True)
                                    else False)))"

instance proof
  fix a :: "'a md_prio"
  show "pleq a a" by (auto simp add:prio_pleq leq_refl split:md_prio.splits)
next
  fix a b c :: "'a md_prio"
  assume H1 : "pleq a b"
  assume H2 : "pleq b c"

  obtain ai and a' where Ha : "a = mdp ai a'" by (cases a; auto)
  obtain bi and b' where Hb : "b = mdp bi b'" by (cases b; auto)
  obtain ci and c' where Hc : "c = mdp ci c'" by (cases c; auto)

  show "pleq a c"
  proof(cases "ci \<le> ai")
    case False
    then show ?thesis using H1 H2 Ha Hb Hc 
      by(auto simp add:prio_pleq split:if_splits)
  next
    case True
    then show ?thesis using H1 H2 Ha Hb Hc leq_trans[of a' b' c']
      by(auto simp add:prio_pleq split:if_splits)
  qed
qed
end

instantiation md_prio :: (Pord) Pord
begin
instance proof

  fix a b :: "'a md_prio"
  obtain ai and a' where Ha : "a = mdp ai a'" by (cases a; auto)
  obtain bi and b' where Hb : "b = mdp bi b'" by (cases b; auto)

  assume H1 : "pleq a b"
  assume H2 : "pleq b a"

  show "a = b" using H1 H2 Ha Hb leq_antisym[of a' b']
    by(auto simp add:prio_pleq split:if_splits)
qed
end

instantiation md_prio :: (Pord_Weakb) Pord_Weakb
begin

definition prio_bot :
"\<bottom> = mdp 0 bot"

instance proof
  fix a :: "'a md_prio"
  show "pleq bot a" using bot_spec
    by(auto simp add: prio_pleq prio_bot split:md_prio.splits)
qed
end

instantiation md_prio :: (Pordb) Pordb
begin
instance proof qed
end

instantiation md_prio :: (Pordbc) Pordbc
begin
instance proof
  fix a b :: "'a md_prio"

  assume H : "has_ub {a, b}"
  obtain ai and a' where Ha : "a = mdp ai a'" by (cases a; auto)
  obtain bi and b' where Hb : "b = mdp bi b'" by (cases b; auto)

  obtain c where Hub : "is_ub {a, b} c" using H by (auto simp add:has_ub_def)
  obtain ci and c' where Hc : "c = mdp ci c'" by (cases c; auto)

  show "has_sup {a, b}"
  proof(cases "ai \<le> bi")
    assume True : "ai \<le> bi"
    show ?thesis
    proof(cases "bi \<le> ai")
      assume True' : "bi \<le> ai"
      have Haibi : "ai = bi" using True True' by auto
      show ?thesis
      proof(cases "has_ub {a', b'}")
        assume True'' : "has_ub {a', b'}"
        have Hhassup' : "has_sup {a', b'}" using complete2[OF True''] by auto
        obtain sup' where Hsup' : "is_sup {a', b'} sup'" using Hhassup' by(auto simp add:has_sup_def)
        have "is_sup {a, b} (mdp ai sup')" using Haibi Ha Hb Hc Hsup'
          by(auto simp add: is_sup_def is_least_def is_ub_def prio_pleq split:md_prio.splits)
        thus ?thesis by (auto simp add:has_sup_def)
      next
        assume False'' : "\<not> has_ub {a', b'}" 
        have "is_sup {a, b} (mdp (1 + ai) bot)"
        proof(rule is_supI)
          fix x
          assume Hi : "x \<in> {a, b}"
          show "pleq x (mdp (1 + ai) bot)" using Hi Ha Hb Haibi
            by(auto simp add: prio_pleq)
        next

          fix ub 
          assume Hi : "is_ub {a, b} ub"
          obtain ubi and ub' where Hub2 : "ub = mdp ubi ub'" by (cases ub; auto)
          show "pleq (mdp (1 + ai) bot) ub" using Hi Hub2
          proof(cases "ubi \<ge> 1 + ai")
            assume True''' : "ubi \<ge> 1 + ai" 
            thus ?thesis using Hi Hub2 bot_spec by(auto simp add:prio_pleq)

          next

            assume False''' : "\<not> ubi \<ge> 1 + ai"
            have Haiubi : "ai = ubi" using False''' Hi Hub2 Ha Hb  Haibi
              by(auto simp add:is_ub_def prio_pleq split:if_split_asm) 
            have "is_ub {a', b'} ub'" using Hi Hub2 False''' Haibi Haiubi Ha Hb
              by(auto simp add:is_sup_def is_least_def is_ub_def prio_pleq split:if_split_asm)
            hence "has_ub {a', b'}" by(auto simp add: has_ub_def)
            thus ?thesis using False'' by auto
          qed
        qed
        thus ?thesis by(auto simp add:has_sup_def)
      qed

    next

      assume False' : "\<not> bi \<le> ai"
      hence "is_sup {a, b} b" using Ha Hb leq_refl by(auto simp add: is_sup_def is_least_def is_ub_def prio_pleq)
      thus ?thesis by(auto simp only:has_sup_def)
    qed

  next
    assume False : "\<not> ai \<le> bi"
    hence "is_sup {a, b} a" using Ha Hb leq_refl by(auto simp add: is_sup_def is_least_def is_ub_def prio_pleq)
    thus ?thesis by(auto simp only:has_sup_def)
  qed
qed
end

fun prio_val :: "'a md_prio \<Rightarrow> 'a" where 
"prio_val (mdp _ x) = x"

fun prio_prio :: "'a md_prio \<Rightarrow> nat" where
"prio_prio (mdp n _) = n"


(* Probably a useful theorem, but not sure if it helps immediately here. *)

lemma prio_always_sup :
  fixes V :: "('a :: Pordbc) md_prio set"
  assumes Hfin : "finite V"
  assumes Hnemp : "v \<in> V"
  shows "has_sup V"
proof-

  obtain V' where SV' : "(\<lambda> x . case x of (mdp p m) \<Rightarrow> m) ` V = V'"
    by(blast)

  obtain v' pv' where V' : "v = mdp pv' v'" "v' \<in> V'"
    using SV' imageI[OF Hnemp, of "(\<lambda>x. case x of mdp p m \<Rightarrow> m)"]
    by(cases v; auto)

  obtain Vmax where VSmax : "Vmax = {w . w \<in> V \<and> 
    (\<exists> w' pw' . w = mdp pw' w' \<and>
     (\<forall> y y' py' . y \<in> V \<longrightarrow> y = mdp py' y' \<longrightarrow> py' \<le> pw'))}"
    by auto

  obtain pbig' where Pbig' : "\<And> n . n\<in>(prio_prio ` V) \<Longrightarrow> n \<le> pbig'"
    using Hfin finite_nat_set_iff_bounded_le[of "prio_prio ` V"]
    by auto

  have VSmax_eq : "\<And> w y pw' w' py' y' .
    w \<in> Vmax \<Longrightarrow> y \<in> Vmax \<Longrightarrow>
    w = mdp pw' w' \<Longrightarrow>
    y = mdp py' y' \<Longrightarrow>
    pw' = py'"
  proof-
    fix w y pw' w' py' y'
    assume Hw1 : "w \<in> Vmax"
    assume Hy1 : "y \<in> Vmax"
    assume Hwp1 : "w = mdp pw' w'"
    assume Hyp1 : "y = mdp py' y'"

    have Hw1_v : "w \<in> V" using VSmax Hw1 by blast
    have Hy1_v : "y \<in> V" using VSmax Hy1 by blast


    have "py' \<le> pw'"
      using Set.subsetD[OF Set.equalityD1[OF VSmax] Hw1] Hy1_v Hyp1 Hwp1
      by auto

    have "pw' \<le> py'"
      using Set.subsetD[OF Set.equalityD1[OF VSmax] Hy1] Hw1_v Hyp1 Hwp1
      by auto

    show "pw' = py'"
      using `py' \<le> pw'` `pw' \<le> py'`
      by auto
  qed

  have Vmax_fact2 : "\<And> n . Vmax = {} \<Longrightarrow>
    (\<exists> w pw' w' . w \<in> V \<and> w = mdp pw' w' \<and> pw' > n)"
  proof-
    fix n
    assume Contr : "Vmax = {}"
    then show "(\<exists> w pw' w' . w \<in> V \<and> w = mdp pw' w' \<and> pw' > n)"
    proof(induction n)
      case 0
      then show ?case unfolding VSmax using V' Hnemp apply(auto)
        apply(drule_tac x = v in spec)
        apply(auto)
        done
    next
      case (Suc n)

      obtain w pw' w' where W: "w \<in> V" "w = mdp pw' w'" "n < pw'"
        using Suc.IH[OF Suc.prems] by auto

      show ?case using W Suc.prems
        unfolding VSmax using V' Hnemp apply(auto)
        apply(drule_tac x = w in spec)
        apply(auto)
        done
    qed
  qed

  have VSmax_nemp : "Vmax = {} \<Longrightarrow> False"
  proof-

    assume Contr : "Vmax = {}"

    obtain w pw' w' where W: "w \<in> V" "w = mdp pw' w'" "pbig' < pw'"
      using Vmax_fact2[OF Contr, of pbig']
      by auto

    have Pw'_prio_prio : "pw' \<in> prio_prio ` V"
      using imageI[OF W(1), of prio_prio] W
      by(auto)

    then show False using Pbig'[OF Pw'_prio_prio] W(3)
      by(auto)
  qed

  hence "Vmax \<noteq> {}" by auto

  then obtain m where M : "m \<in> Vmax"
    unfolding sym[OF ex_in_conv]
    by(auto)

  obtain pm' m' where M' : "m = mdp pm' m'"
    by(cases m; auto)

  have "m \<in> V"
    using VSmax M by auto

  obtain Vmaxp where VSmaxp : "Vmaxp = (\<lambda> x . (case x of (mdp px' x') \<Rightarrow> px')) ` Vmax"
    by simp

  obtain Vmaxv where VSmaxv : "Vmaxv = (\<lambda> x . (case x of (mdp px' x') \<Rightarrow> x')) ` Vmax"
    by simp

  have In_Vmax  :
    "\<And> w pw' w' y y' py'. w \<in> Vmax \<Longrightarrow>  w = mdp pw' w' \<Longrightarrow>
      y \<in> V \<Longrightarrow> y = mdp py' y'\<Longrightarrow> py'\<le> pw'"
    unfolding VSmax
    by blast

  have In_Vmax_Conv :       
    "\<And> w pw' w' y y' py'. w \<in> Vmax \<Longrightarrow>  w = mdp pw' w' \<Longrightarrow>
      y \<in> V \<Longrightarrow> y = mdp pw' y'\<Longrightarrow> y \<in> Vmax"
    unfolding VSmax
    by(auto)

  have Notin_Vmax : 
    "\<And> w pw' w' y y' py'. w \<in> Vmax \<Longrightarrow>  w = mdp pw' w' \<Longrightarrow>
      y \<in> V \<Longrightarrow> y \<notin> Vmax \<Longrightarrow> y = mdp py' y'\<Longrightarrow> py' < pw'"
  proof-
    fix w pw' w' y y' py'
    assume Win : "w \<in> Vmax"
    assume W' : "w = mdp pw' w'"
    assume Yin : "y \<in> V"
    assume Ynotin : "y \<notin> Vmax"
    assume Y' : "y = mdp py' y'"

    have "py' \<le> pw'" using In_Vmax[OF Win W' Yin Y'] by simp

    show "py' < pw'"
    proof(cases "py' = pw'")
      case False
      then show ?thesis using `py' \<le> pw'` by simp
    next
      case True

      then have "y \<in> Vmax" using In_Vmax_Conv[OF Win W' Yin] Y'
        by auto

      then have False using Ynotin by simp

      thus ?thesis by simp
    qed
  qed

  show "has_sup V"
  proof(cases "has_sup Vmaxv")
    case False

    have "is_sup V (mdp (1 + pm') \<bottom>)"
    proof(rule is_supI)
      fix w
      assume W: "w \<in> V"

      obtain pw' w' where W' : "w = (mdp pw' w')"
        by(cases w; auto)

      have "pw' \<le> pm'"
        using In_Vmax[OF M M' W W'] by auto

      then show "w <[ mdp (1 + pm') \<bottom>"
        unfolding W'
        by(auto simp add: prio_pleq)
    next

      fix z
      assume Ub : "is_ub V z"

      obtain pz' z' where Z' : "z = mdp pz' z'"
        by(cases z; auto)

      consider (1) "pz' < pm'"
        | (2) "pz' = pm'"
        | (3) "pz' = 1 + pm'"
        | (4) "pz' > 1 + pm'"
        by(arith)
      then show "mdp (1 + pm') \<bottom> <[ z"
      proof cases
        case 1

        then have False using is_ubE[OF Ub `m \<in> V`]
          unfolding M' Z'
          by(auto simp add: prio_pleq)

        then show ?thesis by auto
      next

        case 2

        have "m' \<in> Vmaxv"
          using imageI[OF M, of "case_md_prio (\<lambda>px' x'. x')"] M'
          unfolding VSmaxv
          by auto

        have "finite Vmaxv"
          using Hfin
          unfolding VSmaxv VSmax
          by auto

        have "is_ub Vmaxv z'"
        proof(rule is_ubI)
          fix w'

          assume "w' \<in> Vmaxv"

          then obtain pw' w where W: "w = mdp pw' w'" "w \<in> Vmax"
            unfolding VSmaxv
            by(auto split: md_prio.splits)

          then have "pw' = pm'"
            using VSmax_eq[OF M W(2) M' W(1)] by auto

          have "w \<in> V" using W unfolding VSmax
            by auto

          then have "w <[ mdp pm' z'"
            using is_ubE[OF Ub, of w]
            unfolding Z' 2
            by auto

          then show "w' <[ z'"
            unfolding W Z' `pw' = pm'`
            by(auto simp add: prio_pleq)
        qed

        then have "has_sup Vmaxv"
          using finite_complete[OF `finite Vmaxv`  `m' \<in> Vmaxv`, of z']
          by(auto simp add: has_sup_def)

        then have False using False by auto

        then show ?thesis by auto
      next

        case 3

        then show ?thesis using bot_spec[of z']
          unfolding Z'
          by(auto simp add: prio_pleq)
      next

        case 4

        then show ?thesis
          unfolding Z'
          by(auto simp add: prio_pleq)
      qed
    qed

    then show ?thesis
      by(auto simp add: has_sup_def)
  next

    case True

    then obtain supr' where Supr' : "is_sup Vmaxv supr'"
      by(auto simp add: has_sup_def)

    have "is_sup V (mdp pm' supr')"
    proof(rule is_supI)
      fix w

      assume W : "w \<in> V"
      then obtain pw' w' where W' : "w = mdp pw' w'"
        by(cases w; auto)

      show "w <[ mdp pm' supr'"
      proof(cases "w \<in> Vmax")
        case True' : True

        then have "w' \<in> Vmaxv"
          using imageI[OF True', of "case_md_prio (\<lambda>px' x'. x')"]
          unfolding VSmaxv W'
          by(auto split: md_prio.splits)

        then have "w' <[ supr'"
          using is_supD1[OF Supr']
          by auto

        have "pw' = pm'"
          using VSmax_eq[OF M True' M' W'] by auto

        then show "w <[ mdp pm' supr'"
          using `w' <[ supr'`
          unfolding W'
          by(auto simp add: prio_pleq)
      next
        case False' : False

        have "pw' < pm'"
          using Notin_Vmax[OF M M' W False' W']
          by auto

        then show "w <[ mdp pm' supr'"
          unfolding W'
          by(auto simp add: prio_pleq)
      qed
    next

      fix z

      assume Ub : "is_ub V z"

      obtain pz' z' where Z' : "z = mdp pz' z'"
        by(cases z; auto)

      have "Vmax \<subseteq> V"
        unfolding VSmax
        by auto

      then have Ub' : "is_ub Vmax z"
        using ub_subset[OF Ub]
        by auto

      consider (1) "pz' < pm'"
        | (2) "pz' = pm'"
        | (3) "pz' > pm'"
        by(arith)
      then show "mdp pm' supr' <[ z"
      proof cases
        case 1

        then have "m <[ z"
          using is_ubE[OF Ub' M] by auto

        then have False using 1
          unfolding M' Z'
          by(auto simp add: prio_pleq)

        then show ?thesis by auto
      next

        case 2

        have Ub'' : "is_ub Vmaxv z'"
        proof(rule is_ubI)

          fix w'
          assume W' : "w' \<in> Vmaxv"

          then obtain pw' where Pw' : "mdp pw' w' \<in> Vmax"
            unfolding VSmaxv
            by(auto split: md_prio.splits)

          have "pw' = pm'"
            using VSmax_eq[OF M Pw' M' refl]
            by auto

          have "mdp pw' w' <[ z"
            using is_ubE[OF Ub' Pw']
            unfolding Z'
            by(auto)

          then show "w' <[ z'" using `pw' = pm'` 2
            unfolding Z'
            by(auto simp add: prio_pleq split: if_splits)
        qed

        have "supr' <[ z'"
          using is_supD2[OF Supr' Ub'']
          by auto

        then show "mdp pm' supr' <[ z"
          using 2
          unfolding Z'
          by(auto simp add: prio_pleq)
      next
        case 3

        then show "mdp pm' supr' <[ z"
          unfolding Z'
          by(auto simp add: prio_pleq)
      qed
    qed

    then show "has_sup V"
      by(auto simp add: has_sup_def)
  qed
qed

instantiation md_prio :: (Pordbc) Pordbps
begin
instance proof

  fix a b c :: "'a md_prio"

  show "has_sup {a, b, c}"
    using prio_always_sup[of "{a, b, c}" a]
    by auto
qed
end

instantiation md_prio :: (Mergeableb) Mergeableb
begin

definition prio_bsup :
"bsup a b =
  (case a of
    mdp ai a' \<Rightarrow> (case b of
                  mdp bi b' \<Rightarrow> (if ai \<le> bi then
                                  (if bi \<le> ai then
                                    (if pleq b' (bsup a' b') then
                                         mdp ai (bsup a' b')
                                         else mdp (1 + ai) bot)
                                                 else mdp bi b')
                               else mdp ai a')))"

instance proof
  fix a b :: "('a md_prio)"
  obtain ai and a' where Ha : "a = mdp ai a'" by (cases a; auto)
  obtain bi and b' where Hb : "b = mdp bi b'" by (cases b; auto)

  obtain bsi and bs' where Hbs : "bsup a b = mdp bsi bs'" by (cases "bsup a b"; auto)

  show "is_bsup a b (bsup a b)"
  proof(rule is_bsupI)

    show "pleq a (bsup a b)" using Ha Hb leq_refl bsup_leq bsup_spec[of a' b']
      by(auto simp add: prio_pleq prio_bsup)
  next

    fix bd sd :: "'a md_prio"

    obtain bdi and bd' where Hbd : "bd = mdp bdi bd'" by (cases bd; auto)
    obtain sdi and sd' where Hsd : "sd = mdp sdi sd'" by (cases sd; auto)

    assume H1 : "pleq bd b"
    assume H2 : "is_sup {a, bd} sd"

    show "pleq sd (bsup a b)" using H1 H2

    proof(cases "ai \<le> bi")
      case True
      then show ?thesis
      proof(cases "bi \<le> ai")
        assume True' : "bi \<le> ai"
        have Haibi : "ai = bi" using True True' by auto

        show "pleq sd (bsup a b)"
        proof(cases "bdi < bi")
          assume True'' : "bdi < bi"

          have "pleq bd a" using True'' H1 H2 Haibi Ha Hb Hbd
            by(auto simp add:prio_pleq)
          hence "is_sup {a, bd} a" by(auto simp add:is_sup_def is_least_def is_ub_def leq_refl)
          hence "sd = a" using is_sup_unique[OF H2] by auto

          thus "pleq sd (bsup a b)"
            using Ha Hb leq_refl bsup_leq bsup_spec[of a' b']
            by(auto simp add:prio_pleq prio_bsup)

        next

          assume False'' : "\<not> bdi < bi"

          hence Hbdibi : "bdi = bi" using H1 Hb Hbd by(auto simp add:prio_pleq split:if_split_asm)
          hence Hbd'b' : "pleq bd' b'" using H1 Hb Hbd by(auto simp add:prio_pleq)

          show "pleq sd (bsup a b)"
          proof(cases "pleq b' (bsup a' b')")
            assume True''' : "pleq b' (bsup a' b')"

            have "pleq a' (bsup a' b')" using bsup_leq[OF bsup_spec[of a' b']] by auto
            hence "is_ub {a', b'} (bsup a' b')" using True''' by (auto simp add:is_ub_def)
            hence "has_ub {a', b'}" by(auto simp add:has_ub_def)
            hence "has_sup {a', b'}" using complete2 by auto
            then obtain sup' where Hsup' : "is_sup {a', b'} sup'" by(auto simp add:has_sup_def)

            have Bssup' : "is_sup {a', b'} (bsup a' b')" using bsup_sup[OF Hsup' bsup_spec[of a' b']] by auto
            hence  "is_ub {a, b} (bsup a b)" using H2 Ha Hb Hsd Hbd Haibi Hbdibi Hbd'b' True''' bsup_leq[OF bsup_spec[of a' b']]
              by(auto simp add:prio_pleq prio_bsup is_ub_def)

            hence "is_ub {a, bd} (bsup a b)" using leq_trans[of bd b "bsup a b"] H1
              by(auto simp add:is_ub_def)

            thus ?thesis using is_supD2[OF H2] by auto
          next

            assume False''' : "\<not> pleq b' (bsup a' b')"

            have "bsup a b = mdp (1 + ai) bot" using Ha Hb Haibi True True' False''' by(auto simp add:prio_bsup)
            hence "is_ub {a, bd} (bsup a b)" using Ha Hb Haibi Hbdibi Hbd by(auto simp add:prio_pleq is_ub_def)
            hence "is_ub {a, bd} (bsup a b)" using leq_trans[of bd b "bsup a b"] H1
              by(auto simp add:is_ub_def)

            thus ?thesis using is_supD2[OF H2] by auto
          qed
        qed

      next
        assume False' : "\<not> bi \<le> ai"
        hence Hbsupb : "bsup a b = b" using Ha Hb
        by(auto simp add:prio_pleq prio_bsup is_sup_def is_least_def is_ub_def split:if_split_asm)

      have Hub : "is_ub {a, bd} b" using Ha Hb False' leq_refl H1
        by(auto simp add: prio_pleq prio_bsup is_sup_def is_least_def is_ub_def split:if_split_asm)

      show ?thesis using Hbsupb is_supD2[OF H2 Hub]
        by auto
      qed

    next
      case False
      hence Hbsupa : "bsup a b = a" using Ha Hb
        by(auto simp add: prio_pleq prio_bsup is_sup_def is_least_def is_ub_def split:if_split_asm)

      have Hub : "is_ub {a, bd} a" using Ha Hb False leq_refl H1
        by(auto simp add:prio_pleq prio_bsup is_sup_def is_least_def is_ub_def split:if_split_asm md_prio.splits)

      show ?thesis using Hbsupa is_supD2[OF H2 Hub]
        by auto
    qed
  next

    fix x :: "'a md_prio"
    obtain xi and x' where Hx : "x = mdp xi x'" by (cases x; auto)

    assume H : "is_bub a b x"
    have Hax : "pleq a x" using is_bubD1[OF H] by auto

    show "pleq (bsup a b) x"
    proof(cases "ai \<le> bi")
      case True
      then show ?thesis
      proof(cases "bi \<le> ai")
        assume True' : "bi \<le> ai"
        have Haibi : "ai = bi" using True True' by auto

        show "?thesis"
        proof(cases "pleq b' (bsup a' b')")
          assume True'' : "pleq b' (bsup a' b')"

          hence 0 : "bsup a b = mdp ai (bsup a' b')" using Ha Hb True True' True'' by (auto simp add:prio_bsup)

          hence 1 : "pleq b (bsup a b)" using Hb Haibi True''
            by(auto simp add:prio_pleq)

          have 2 : "is_sup {a', b'} (bsup a' b')" using bsup_imp_sup[OF bsup_spec[of a' b'] True''] by auto

          thus ?thesis
          proof(cases "bi \<le> xi")
            assume True''' : "bi \<le> xi"

            thus ?thesis
            proof(cases "xi \<le> bi")
              assume True'''' : "xi \<le> bi"

              have Hxibi : "xi = bi" using True''' True'''' by auto

              have "is_sup {a, b} (bsup a b)" using Ha Hb Hx Haibi Hax True''' True'''' 0 2
                by(auto simp add: is_ub_def prio_pleq is_bub_def is_sup_def is_least_def split:md_prio.splits)

              thus ?thesis using is_bubD2[OF H leq_refl[of b]] by auto
            next

              assume False'''' : "\<not> xi \<le> bi"

              thus ?thesis using False'''' Haibi Ha Hb Hx bot_spec[of x']
                by(auto simp add:prio_pleq prio_bsup)
            qed

          next
            assume False''' : "\<not> bi \<le> xi"
            thus ?thesis using Haibi Ha Hb Hx Hax
              by(auto simp add:prio_pleq prio_bsup)
          qed
        next
          assume False'' : "\<not> pleq b' (bsup a' b')"

          hence 0 : "bsup a b = mdp (1 + ai) bot" using Ha Hb Hx Haibi
            by (auto simp add:prio_pleq prio_bsup)

          have "\<not> has_ub {a', b'}" using bsup_imp_sup_conv[OF bsup_spec[of a' b'] False'']
            by(auto simp add:has_ub_def)

          hence 1 : "is_sup {a, b} (bsup a b)" using Ha Hb Haibi 0 bot_spec
            by(auto simp add:is_sup_def is_least_def is_ub_def has_ub_def prio_pleq split:md_prio.splits)

          show ?thesis
          proof(cases "bi \<le> xi")
            assume True''' : "bi \<le> xi"

            thus ?thesis
            proof(cases "xi \<le> bi")
              assume True'''' : "xi \<le> bi"

              have Hxibi : "xi = bi" using True''' True'''' by auto

              thus ?thesis using is_bubD2[OF H leq_refl[of b]] 1 by auto
            next

              assume False'''' : "\<not> xi \<le> bi"

              thus ?thesis using 0 Ha Hb Hx Haibi bot_spec
                by(auto simp add:prio_pleq)
            qed
          next

            assume False''' : "\<not> bi \<le> xi"

            thus ?thesis using is_bubD2[OF H leq_refl[of b]] 1 by auto
          qed
        qed
      next
        assume False' : "\<not> bi \<le> ai"

        have "is_sup {a, b} (bsup a b)"  using True False' Ha Hb Hx leq_refl
          by(auto simp add:prio_pleq prio_bsup is_sup_def is_least_def is_ub_def)
        thus ?thesis using is_bubD2[OF H leq_refl[of b]] by auto
      qed
    next
      assume False : "\<not> ai \<le> bi"
        have "is_sup {a, b} (bsup a b)"  using False Ha Hb Hx leq_refl
          by(auto simp add:prio_pleq prio_bsup is_sup_def is_least_def is_ub_def)
        thus ?thesis using is_bubD2[OF H leq_refl[of b]] by auto
    qed
  qed
qed
end

(* NB: if we were to separate Pordc_all from Pordc,
 * we could show this for arbitrary Pord type parameter.
 * However that might not be that useful.
 *)
instantiation md_prio :: ("{Pordbc}") Pordc_all
begin
instance proof
  fix a b :: "'a md_prio"

  obtain pa' a' where A : "a = mdp pa' a'"
    by(cases a; auto)

  obtain pb' b' where B: "b = mdp pb' b'"
    by(cases b; auto)

  consider (1) "pa' < pb'" |
           (2) "pb' < pa'" |
           (3) "pa' = pb'"
    by arith

  then show "has_ub {a, b}"
  proof cases
    case 1

    then have "a <[ b"
      using A B
      by(auto simp add: prio_pleq)

    then have "is_ub {a, b} b"
      by(auto simp add: is_ub_def leq_refl)

    then show ?thesis
      by(auto simp add: has_ub_def)
  next

    case 2
    then have "b <[ a"
      using A B
      by(auto simp add: prio_pleq)

    then have "is_ub {a, b} a"
      by(auto simp add: is_ub_def leq_refl)

    then show ?thesis
      by(auto simp add: has_ub_def)
  next

    case 3

    have A_leq : "a <[ mdp (1 + pa') a'"
      using A
      by(auto simp add: prio_pleq)

    have B_leq : "b <[ mdp (1 + pa') a'"
      using B 3
      by(auto simp add: prio_pleq)

    have "is_ub {a, b} (mdp (1 + pa') a')"
      using A_leq B_leq
      by(auto simp add: is_ub_def)

    then show "has_ub {a, b}"
      by(auto simp add: has_ub_def)
  qed
qed
end

instantiation md_prio :: (Pord_Weak) Bump
begin
definition prio_bump :
  "bump x = (case x of (mdp px' x') \<Rightarrow> (mdp (1 + px') x'))"

instance proof
  fix x :: "'a md_prio"
  show "bump x \<noteq> x"
    by(cases x; auto simp add: prio_bump)
next
  fix x :: "'a md_prio"
  show "x <[ bump x"
    by(cases x; auto simp add: prio_bump prio_pleq)
qed
end

end