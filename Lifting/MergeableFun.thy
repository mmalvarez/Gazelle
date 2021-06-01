theory MergeableFun
imports Mono "../Mergeable/Mergeable" "LangComp"
begin

(* hmm. we need monotonicity... *)
instantiation "fun" :: (_, Pord_Weak) Pord_Weak
begin

definition fun_pleq :
"((f1 :: ('a \<Rightarrow> ('b :: Pord_Weak))) <[ f2) \<equiv>
 (\<forall> x . f1 x <[ f2 x)"

instance proof
  fix f1 :: "('a \<Rightarrow> 'b)"

  show "f1 <[ f1" unfolding fun_pleq
    using leq_refl
    by auto
next
  fix f1 f2 f3 :: "('a \<Rightarrow> 'b)"

  assume H1 : "f1 <[ f2"
  assume H2 : "f2 <[ f3"

  show "f1 <[ f3" using H1 H2 unfolding fun_pleq
    using leq_trans
    by blast
qed
end 

instantiation "fun" :: (_, Pord) Pord
begin

instance proof
  fix f1 f2 :: "('a \<Rightarrow> 'b)"
  assume H1 : "f1 <[ f2"
  assume H2 : "f2 <[ f1"

  show "f1 = f2" using H1 H2 unfolding fun_pleq
    using leq_antisym
    by blast
qed
end

instantiation "fun" :: (_, Pordc) Pordc
begin

instance proof
  fix f1 f2 :: "('a \<Rightarrow> 'b)"
  assume H : "has_ub {f1, f2}"

  have "is_sup {f1, f2}
    (\<lambda> x .  (SOME x' . is_sup {f1 x, f2 x} x'))"
  proof(rule is_sup_intro)
    fix fx

    assume Hfx : "fx \<in> {f1, f2}"

    show "fx <[ (\<lambda>x. SOME x'. is_sup {f1 x, f2 x} x')"
      unfolding fun_pleq
    proof
      fix x

      have Hub : "has_ub {f1 x, f2 x}"
        using H unfolding has_ub_def is_ub_def fun_pleq
        by auto

      obtain fxx where Fxx : "is_sup {f1 x, f2 x} fxx"
        using complete2[OF Hub] 
        unfolding has_sup_def
        by auto

      have Leq : "fx x <[ fxx"
        using is_sup_unfold1[OF Fxx, of "fx x"] using Hfx
        by auto

      have SomeEq : "Eps (is_sup {f1 x, f2 x}) = fxx"
      proof(rule some1_equality)
        show "\<exists>!xa. is_sup {f1 x, f2 x} xa"
        proof
          show "is_sup {f1 x, f2 x} fxx" using Fxx by auto
        next
          show "\<And>xa. is_sup {f1 x, f2 x} xa \<Longrightarrow> xa = fxx" using is_sup_unique[OF Fxx] by auto
        qed
      next
        show "is_sup {f1 x, f2 x} fxx" using Fxx by auto
      qed
      show "fx x <[ Eps (is_sup {f1 x, f2 x})"
        unfolding SomeEq using Leq by auto
    qed
  next
    fix fx'

    assume Hfx' : "is_ub {f1, f2} fx'"

    show "(\<lambda>x. SOME x'. is_sup {f1 x, f2 x} x') <[ fx'" unfolding fun_pleq
    proof
      fix x

      have Hub : "has_ub {f1 x, f2 x}"
        using H unfolding has_ub_def is_ub_def fun_pleq
        by auto

      obtain fxx where Fxx : "is_sup {f1 x, f2 x} fxx"
        using complete2[OF Hub] 
        unfolding has_sup_def
        by auto

      have Fx'x : "is_ub {f1 x, f2 x} (fx' x)"
        using Hfx'
        unfolding is_ub_def fun_pleq
        by auto

      have Leq : "fxx <[ fx' x"
        using is_sup_unfold2[OF Fxx Fx'x]
        by auto

      have SomeEq : "Eps (is_sup {f1 x, f2 x}) = fxx"
      proof(rule some1_equality)
        show "\<exists>!xa. is_sup {f1 x, f2 x} xa"
        proof
          show "is_sup {f1 x, f2 x} fxx" using Fxx by auto
        next
          show "\<And>xa. is_sup {f1 x, f2 x} xa \<Longrightarrow> xa = fxx" using is_sup_unique[OF Fxx] by auto
        qed
      next
        show "is_sup {f1 x, f2 x} fxx" using Fxx by auto
      qed
      show "Eps (is_sup {f1 x, f2 x}) <[ fx' x"
        unfolding SomeEq using Leq by auto
    qed
  qed

  thus "has_sup {f1, f2}" unfolding has_sup_def by auto
qed
end

instantiation "fun" :: (_, Pordb) Pordb
begin

definition fun_bot : 
"(bot :: 'a \<Rightarrow> 'b) \<equiv> (\<lambda> _ . (\<bottom> :: 'b))"

instance proof
  fix f :: "('a \<Rightarrow> 'b)"
  show "pleq bot f"
    unfolding fun_bot fun_pleq
    using bot_spec
    by auto
qed
end

lemma fun_ub_results :
  assumes H : "is_ub Fs (f :: 'a \<Rightarrow> ('b :: Pord_Weak))"
  shows "is_ub ((\<lambda> f . f x) ` Fs) (f x)" using H
  unfolding is_ub_def fun_pleq
  by auto

lemma fun_sup_results :
  assumes H : "is_sup Fs (f :: 'a \<Rightarrow> ('b :: Pord_Weak))"
  shows "is_sup ((\<lambda> f . f x) ` Fs) (f x)"
proof(rule is_sup_intro)
  fix xa
  assume Xa : "xa \<in> (\<lambda>f. f x) ` Fs" 

  obtain g where G : "g \<in> Fs" and
    Gxa : "g x = xa"
    using Xa
    by blast

  show "xa <[ f x"
    using is_sup_unfold1[OF H G]
    unfolding fun_pleq sym[OF Gxa]
    by auto
next
  fix x'
  assume Hx' : "is_ub ((\<lambda>f. f x) ` Fs) x'"  

  have Ub : "is_ub Fs (\<lambda> z . (if z = x then x' else f z))"
  proof(rule is_ub_intro)
    fix xa

    assume Hxa : "xa \<in> Fs"

    show "xa <[ (\<lambda>z. if z = x then x' else f z)"
      unfolding fun_pleq
    proof
      fix xb
      show "xa xb <[ (if xb = x then x' else f xb)"
      proof(cases "xb = x")
        case True
        then show ?thesis 
          using is_ub_unfold[OF Hx', of "xa xb"] Hxa
          unfolding fun_pleq
          by auto
      next
        case False
        then show ?thesis 
          using is_sup_unfold1[OF H Hxa]
          unfolding fun_pleq
          by auto
      qed
    qed
  qed

  have C' : "\<And> xa .  f xa <[ (if xa = x then x' else f xa)"
    using is_sup_unfold2[OF H Ub]
    unfolding fun_pleq
    by auto

  then show "f x <[ x'"
    using C'[of x]
    by auto
qed

(* I don't think we can have a mergeable instance for Fun unless we allow bot values.
   this is because we cannot use the fact that there is a biased UB between f1 and f2
   unless we can construct an appropriate bd and sd functions. But we only
   get the fact that there is a biased UB at one point.
*)
(* TODO: make sure that I can't do a mergeable-without-bot instance
*)
instantiation "fun" :: (_, Mergeableb) Mergeableb begin
definition fun_bsup :
  "[^ f1, f2 ^] \<equiv> (\<lambda> x . [^ f1 x, f2 x ^])"

instance proof
  fix f1 f2 :: "('a \<Rightarrow> 'b)"

  show "is_bsup f1 f2 [^ f1, f2 ^]"
    unfolding fun_bsup
  proof(rule is_bsup_intro)
    show "f1 <[ (\<lambda>x. [^ f1 x, f2 x ^])"
      unfolding fun_pleq
    proof
      fix x
      show "f1 x <[ [^ f1 x, f2 x ^]"
        using is_bsup_unfold1[OF bsup_spec[of "f1 x" "f2 x"]]
        by auto
    qed
  next
    fix bd sd
    assume Bd : "bd <[ f2" 
    assume Sd :"is_sup {f1, bd} sd"
    show "sd <[ (\<lambda>x. [^ f1 x, f2 x ^])" unfolding fun_pleq
    proof
      fix x

      have Sup' : "is_sup {f1 x, bd x} (sd x)"
        using fun_sup_results[OF Sd]
        by auto

      have Sdx : "[^ f1 x, bd x ^] = sd x"
        using bsup_sup[OF Sup' bsup_spec[of "f1 x" "bd x"] ]
              is_sup_unique[OF Sup', of "[^ f1 x, bd x ^]"]
        by auto

      have Sdx_bsup : "is_bsup (f1 x) (bd x) (sd x)"
        using bsup_spec[of "f1 x" "bd x"]
        unfolding Sdx
        by auto

      have Bdx : "bd x <[ f2 x"
        using Bd
        unfolding fun_pleq
        by auto

      show "sd x <[ [^ f1 x, f2 x ^]" 
        using is_bsup_unfold2[OF bsup_spec[of "f1 x" "f2 x"] Bdx Sup']
        by auto
    qed
  next
    fix f'
    assume H : "is_bub f1 f2 f'"

    show "(\<lambda>x. [^ f1 x, f2 x ^]) <[ f'" unfolding fun_pleq
    proof
      fix x

      have Bub' : "is_bub (f1 x) (f2 x) (f' x)"
      proof(rule is_bub_intro)
        show "f1 x <[ f' x"
          using is_bub_unfold1[OF H]
          unfolding fun_pleq
          by auto
      next
        fix bd sd
        assume Bd : "bd <[ f2 x"
        assume Sd : "is_sup {f1 x, bd} sd" 

        have Bd' : "(\<lambda> z . (if z = x then bd else \<bottom>)) <[ f2"
          unfolding fun_pleq
        proof
          fix z
          show "(if z = x then bd else \<bottom>) <[ f2 z"
            using Bd leq_refl bot_spec
            by auto
        qed

        have Sd' : "is_sup {f1, \<lambda>z. if z = x then bd else \<bottom>} (\<lambda> z . if z = x then sd else f1 z)"
        proof(rule is_sup_intro)
          fix xa

          assume Hxa : "xa \<in> {f1, \<lambda>z. if z = x then bd else \<bottom>}"
          show "xa <[ (\<lambda>z. if z = x then sd else f1 z)"
            unfolding fun_pleq
          proof
            fix xb
            show "xa xb <[ (if xb = x then sd else f1 xb)"
            proof(cases "xa = f1")
              case True
              then show ?thesis
              proof(cases "xb = x")
                case True' : True
                then show ?thesis using is_sup_unfold1[OF Sd] True
                  by(auto)
              next
                case False' : False
                then show ?thesis using True leq_refl[of "f1 xb"]
                  by auto
              qed
            next
              case False

              hence False_alt : "xa = (\<lambda>z. if z = x then bd else \<bottom>)"
                using Hxa by auto

              then show ?thesis 
              proof(cases "xb = x")
                case True' : True
                then show ?thesis using is_sup_unfold1[OF Sd] False_alt
                  by(auto)
              next
                case False' : False
                then show ?thesis using False_alt bot_spec[of "f1 xb"]
                  by auto
              qed
            qed
          qed
        next
          fix x'

          assume Hub : "is_ub {f1, \<lambda>z. if z = x then bd else \<bottom>} x'"

          show "(\<lambda>z. if z = x then sd else f1 z) <[ x'"
            unfolding fun_pleq
          proof
            fix xa

            have F1_leq : "f1 xa <[ x' xa"
              using is_ub_unfold[OF Hub, of f1]
              unfolding fun_pleq
              by auto

            have "(\<lambda>z. if z = x then bd else \<bottom>) <[ x'"
              using Hub unfolding is_ub_def by auto

            hence Point_leq : "\<And> xa. (if xa = x then bd else \<bottom>) <[ x' xa"
              unfolding fun_pleq
              by auto

            show "(if xa = x then sd else f1 xa) <[ x' xa"

            proof(cases "xa = x")
              case True

              have Bd_leq : "bd <[ x' xa"
                using True
                Point_leq[of xa]
                by auto

              have Ub' : "is_ub {f1 x, bd} (x' xa)" 
              proof(rule is_ub_intro)
                fix xb
                assume "xb \<in> {f1 x, bd}"

                then show "xb <[ x' xa"
                  using Bd_leq F1_leq True
                  by(cases "xb = f1 x"; auto)
              qed

              show ?thesis
                using True is_sup_unfold2[OF Sd Ub']
                by auto
            next
              case False

              then show ?thesis using F1_leq by auto
            qed
          qed
        qed

        have Unf : "\<And> xa. (if xa = x then sd else f1 xa) <[ f' xa"
          using is_bub_unfold2[OF H Bd' Sd']
          unfolding fun_pleq
          by auto

        have "(\<lambda>z. if z = x then sd else f1 z) x <[ f' x"
          using Unf[of x]
          by auto

        then show "sd <[ f' x" by auto
      qed

      show "[^ f1 x, f2 x ^] <[ f' x"
        using is_bsup_unfold3[OF bsup_spec[of "f1 x" "f2 x"] Bub']
        by auto
    qed
  qed
qed
end


end
