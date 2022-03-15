theory Mg_Option
  imports "../Pord" "../Mergeable"
begin

(* Option is used to express a pointed ordering with a least element (None).
 * It can be seen as lifting an ordering on 'a to a pointed ordering on 'a option *)
text_raw \<open>%Snippet gazelle__mergeable__instances__mg_option__pord_weak\<close>
instantiation option :: (Pord_Weak) Pord_Weak
begin
definition option_pleq : "(x :: 'a option) <[ y =
(case x of
      None \<Rightarrow> True
      | Some x' \<Rightarrow>
        (case y of
          None \<Rightarrow> False
          | Some y' \<Rightarrow> (pleq x' y')))"
text_raw \<open>%EndSnippet\<close>

instance proof
  show "\<And> (a :: 'a option) . pleq a a"
  proof(-)
    fix a :: "'a option"
    show "pleq a a"
      by(cases a; auto simp add:option_pleq leq_refl)
  qed
next
  fix a b c :: "'a option"
  assume H1 : "pleq a b"
  assume H2 : "pleq b c"
  show "pleq a c" using leq_trans H1 H2
    by(auto simp add:option_pleq split:option.splits)
qed
end

instantiation option :: (Pord) Pord
begin

instance proof
  fix a b :: "'a option"
  assume H1 : "pleq a b"
  assume H2 : "pleq b a"
  show "a = b" using H1 H2 leq_antisym
    by(auto simp add:option_pleq split:option.splits)
qed
end

instantiation option :: (Pordc) Pordc
begin

instance proof
  fix a b :: "'a option"
  assume H : "has_ub {a, b}"
  show "has_sup {a, b}"
  proof(cases a)
    case None
    then show ?thesis
    proof(cases b) 
      show "a = None \<Longrightarrow> b = None \<Longrightarrow> has_sup {a, b}"      
        by(auto simp add:
              option_pleq
              has_ub_def  is_ub_def
              has_sup_def is_sup_def is_least_def All_def split:option.splits)
      show " \<And>aa::'a. a = None \<Longrightarrow> b = Some aa \<Longrightarrow> has_sup {a, b}" using H leq_refl
        by(auto simp add:
              option_pleq
              has_ub_def  is_ub_def
              has_sup_def is_sup_def is_least_def All_def split:option.splits) 
      qed
    next
    case (Some a')
    then show ?thesis
    proof(cases b)
      show "a = Some a' \<Longrightarrow> b = None \<Longrightarrow> has_sup {a, b}" using H leq_refl
      by(auto simp add:
              option_pleq
              has_ub_def  is_ub_def
              has_sup_def is_sup_def is_least_def All_def split:option.splits) 

      show "\<And>aa::'a. a = Some a' \<Longrightarrow> b = Some aa \<Longrightarrow> has_sup {a, b}"
        proof(-)
        fix aa
        assume Hi1 : "a = Some a'"
        assume Hi2 : "b = Some aa"
        
        have OUb : "has_ub {a', aa}"  using H Hi1 Hi2
          by(auto simp add:option_pleq is_ub_def has_ub_def split:option.splits)
        obtain x where OSup : "is_sup {a', aa} x" using complete2[OF OUb]
          by(auto simp add:option_pleq has_sup_def)

        have "is_sup  {a, b} (Some x)" 
        proof(rule is_supI)
          fix xa
          assume Hxa : "xa \<in> {a, b}"
          obtain xa' where Hxa' : "xa = Some xa' \<and> (xa' = a' \<or> xa' = aa)" using Hi1 Hi2 Hxa
            by(auto simp add:
                option_pleq is_ub_def is_least_def has_ub_def split:option.splits elim:is_supD1 is_supD2)
          have 0 : "pleq xa' x" using Hxa' OSup
            by(auto simp add:is_sup_def is_least_def is_ub_def)
          show "pleq xa (Some x)" using 0 Hxa'
            by(auto simp add:option_pleq)
        next
          fix x'
          assume Hx' : "is_ub {a, b} x'"
          show "pleq (Some x) x'" using Hx' Hi1 Hi2 OSup
            by(auto simp add:
                option_pleq is_ub_def is_sup_def is_least_def split:option.splits)
        qed
        thus "has_sup {a, b}" by (auto simp add:has_sup_def)
      qed
    qed
  qed
qed
end



lemma is_sup_union_ub :
  assumes Hsup : "is_sup Xs x"
  assumes Hy : "is_ub Ys x"
  shows "is_sup (Xs \<union> Ys) x"
proof(rule is_supI)
  fix z
  assume "z \<in> Xs \<union> Ys"
  then consider (Z1) "z \<in> Xs" | (Z2) "z \<in> Ys"
    by(auto)
  then show "z <[ x"
  proof cases
    case Z1
    then show ?thesis using is_supD1[OF Hsup] by auto
  next
    case Z2
    then show ?thesis using is_ubE[OF Hy] by auto
  qed
next

  fix x'
  assume Ub: "is_ub (Xs \<union> Ys) x'"

  have "is_ub Xs x'"
  proof(rule is_ubI)
    fix w
    assume "w \<in> Xs"
    then have "w \<in> Xs \<union> Ys" by auto
    then show "w <[ x'"
      using is_ubE[OF Ub] by auto
  qed

  then show "x <[ x'"
    using is_supD2[OF Hsup] by auto
qed

lemma is_sup_Some :
  assumes Hnemp : "x \<in> Xs"
  assumes H : "is_sup Xs supr"
  shows "is_sup (Some ` Xs) (Some supr)"
proof(rule is_supI)
  fix z
  assume Z : "z \<in> Some ` Xs"
  then obtain z' where Z' : "z = Some z'" "z' \<in> Xs"
    by auto

  show "z <[ Some supr"
    using is_supD1[OF H Z'(2)] Z'(1)
    by(auto simp add: option_pleq)
next
  fix w
  assume Ub : "is_ub (Some ` Xs) w"

  have "Some x \<in> Some ` Xs"
    using Hnemp by auto

  then have "Some x <[ w"
    using is_ubE[OF Ub]
    by auto

  then obtain w' where W' : "w = Some w'"
    by(cases w; auto simp add: option_pleq)

  have "is_ub Xs w'"
  proof
    fix z'

    assume Z': "z' \<in> Xs"

    then have "Some z' \<in> Some ` Xs"
      by auto

    then have "Some z' <[ w"
      using is_ubE[OF Ub] by auto

    then show "z' <[ w'" using W' by(auto simp add: option_pleq)
  qed

  then have "supr <[ w'"
    using is_supD2[OF H] by auto

  then show "Some supr <[ w"
    using W' by(auto simp add: option_pleq)
qed

lemma is_sup_Some' :
  assumes Hnemp : "x \<in> Xs"
  assumes H: "is_sup (Some ` Xs) (Some supr)"
  shows "is_sup Xs supr"
proof(rule is_supI)
  fix z

  assume Z: "z \<in> Xs"

  then have "Some z <[ Some supr"
    using is_supD1[OF H, of "Some z"] by auto

  then show "z <[ supr"
    by(simp add: option_pleq)
next

  fix w

  assume Ub : "is_ub Xs w"

  have "is_ub (Some ` Xs) (Some w)"
  proof(rule is_ubI)

    fix z'
    assume Z' : "z' \<in> Some ` Xs"

    then obtain z where Z: "z' = Some z" "z \<in> Xs"
      by auto

    have "z <[ w" using is_ubE[OF Ub Z(2)]
      by auto

    then show "z' <[ Some w"
      using Z by(auto simp add: option_pleq)
  qed

  then have "Some supr <[ Some w"
    using is_supD2[OF H] by auto

  then show "supr <[ w"
    by(auto simp add: option_pleq)
qed


lemma is_ub_Some :
  assumes Hnemp : "x \<in> Xs"
  assumes H : "is_ub Xs ub"
  shows "is_ub (Some ` Xs) (Some ub)"
proof(rule is_ubI)
  fix z
  assume Z : "z \<in> Some ` Xs"
  then obtain z' where Z' : "z = Some z'" "z' \<in> Xs"
    by auto

  show "z <[ Some ub"
    using is_ubE[OF H Z'(2)] Z'(1)
    by(auto simp add: option_pleq)
qed

lemma is_ub_Some' :
  assumes Hnemp : "x \<in> Xs"
  assumes H: "is_ub (Some ` Xs) (Some ub)"
  shows "is_ub Xs ub"
proof(rule is_ubI)
  fix z

  assume Z: "z \<in> Xs"
  
  then have "Some z <[ Some ub"
    using is_ubE[OF H, of "Some z"] by auto

  then show "z <[ ub"
    by(simp add: option_pleq)
qed

instantiation option :: (Pordps) Pordps
begin
instance proof
  fix a b c :: "'a option"

  assume "has_sup {a, b}"
  then obtain sup_ab where Sup_ab : "is_sup {a, b} sup_ab"
    by(auto simp add: has_sup_def)

  assume Sup_bc : "has_sup {b, c}"
  then obtain sup_bc where Sup_bc : "is_sup {b, c} sup_bc"
    by(auto simp add: has_sup_def)

  assume Sup_ac : "has_sup {a, c}"
  then obtain sup_ac where Sup_ac : "is_sup {a, c} sup_ac"
    by(auto simp add: has_sup_def)

  show "has_sup {a, b, c}"
  proof(cases a)
    case ANone : None

    then have "is_ub {a} sup_bc"
      by(auto simp add: is_ub_def option_pleq)

    then have "is_sup {a, b, c} sup_bc"
      using is_sup_union_ub[OF Sup_bc, of "{a}"] by auto

    then show ?thesis
      by(auto simp add: has_sup_def)
  next
    case ASome : (Some a')

    show ?thesis
    proof(cases b)

      case BNone : None

      have Comm : "{b, a, c} = {a, b, c}"
        by auto

      have "is_ub {b} sup_ac" using BNone
        by(auto simp add: is_ub_def option_pleq)
  
      then have "is_sup {a, b, c} sup_ac"
        using is_sup_union_ub[OF Sup_ac, of "{b}"] Comm
        by(auto)
  
      then show ?thesis
        by(auto simp add: has_sup_def)
    next

      case BSome : (Some b')

      show ?thesis
      proof(cases c)

        case CNone : None

        have Comm : "{c, a, b} = {a, b, c}"
          by auto
  
        have "is_ub {c} sup_ab" using CNone
          by(auto simp add: is_ub_def option_pleq)
    
        then have "is_sup {a, b, c} sup_ab"
          using is_sup_union_ub[OF Sup_ab, of "{c}"] Comm
          by(auto)
    
        then show ?thesis
          by(auto simp add: has_sup_def)
      next

        case CSome : (Some c')

        obtain sup_ab' where Sup_ab' :
          "sup_ab = Some sup_ab'"
          using Sup_ab ASome
          by(cases sup_ab; auto simp add: is_sup_def is_least_def is_ub_def option_pleq)

        obtain sup_bc' where Sup_bc' :
          "sup_bc = Some sup_bc'"
          using Sup_bc BSome
          by(cases sup_bc; auto simp add: is_sup_def is_least_def is_ub_def option_pleq)

        obtain sup_ac' where Sup_ac' :
          "sup_ac = Some sup_ac'"
          using Sup_ac ASome
          by(cases sup_ac; auto simp add: is_sup_def is_least_def is_ub_def option_pleq)

        have Has_ab':
          "has_sup {a', b'}"
          using Sup_ab Sup_ab' ASome BSome is_sup_Some'[of a' "{a', b'}" sup_ab']
          by(auto simp add: has_sup_def)

        have Has_bc':
          "has_sup {b', c'}"
          using Sup_bc Sup_bc' BSome CSome is_sup_Some'[of b' "{b', c'}" sup_bc']
          by(auto simp add: has_sup_def)

        have Has_ac':
          "has_sup {a', c'}"
          using Sup_ac Sup_ac' ASome CSome is_sup_Some'[of a' "{a', c'}" sup_ac']
          by(auto simp add: has_sup_def)

        obtain sup' where Sup' : "is_sup {a', b', c'} sup'"
          using pairwise_sup[OF Has_ab' Has_bc' Has_ac']
          by(auto simp add: has_sup_def)

        have "is_sup {a, b, c} (Some sup')"
          using is_sup_Some[OF _ Sup'] ASome BSome CSome
          by auto

        then show ?thesis
          by(auto simp add: has_sup_def)
      qed
    qed
  qed
qed
end

instantiation option :: (Pordpsok) Pordpsok
begin
instance proof
  fix a b supr :: "'a option"
  assume Aok : "a \<in> ok_S"
  assume Bok : "b \<in> ok_S"
  assume Sup : "is_sup {a, b} supr"

  obtain a' where A' : "a = Some a'" "a' \<in> ok_S" using Aok
    by(cases a; auto simp add: option_ok_S)

  obtain b' where B' : "b = Some b'" "b' \<in> ok_S" using Bok
    by(cases b; auto simp add: option_ok_S)

  show "supr \<in> ok_S"
  proof(cases supr)
    case None

    then have "a <[ None"
      using is_supD1[OF Sup, of a]
      by auto

    then have False using A'
      by(auto simp add: option_pleq)

    then show ?thesis by auto
  next
    case (Some supr')

    have Supr' : "is_sup {a', b'} (supr')"
      using is_sup_Some'[of "a'" "{a', b'}" supr'] using Sup
      unfolding A' B' Some
      by auto

    then have "supr' \<in> ok_S"
      using pairwise_sup_ok[OF A'(2) B'(2) Supr'] by auto

    then show ?thesis using Some
      by(auto simp add: option_ok_S)
  qed
qed
end

text_raw \<open>%Snippet gazelle__mergeable__instances__mg_option__pord_weakb\<close>
instantiation option :: (Pord_Weak) Pord_Weakb
begin

definition option_bot : "bot = (None :: 'a option)"
text_raw \<open>%EndSnippet\<close>

instance proof
next
  fix a :: "'a option"
  show "\<bottom> <[ a"
    by(auto simp add:option_pleq option_bot)
qed
end


instantiation option :: (Pord) Pordb
begin
instance proof qed
end

instantiation option :: (Pordc) Pordbc
begin
instance proof qed
end

text_raw \<open>%Snippet gazelle__mergeable__instances__mg_option__mergeable\<close>
instantiation option :: (Mergeable) Mergeableb
begin
definition option_bsup: "[^(x :: 'a option), y^] =
  (case x of
    None \<Rightarrow> y
    | Some x' \<Rightarrow> (case y of
                       None \<Rightarrow> Some x'
                       | Some y' \<Rightarrow> Some (bsup x' y')))"
text_raw \<open>%EndSnippet\<close>

instance proof
  fix a b :: "'a option"
  show "is_bsup a b (bsup a b)"
  proof(cases a)
    case None
    then show ?thesis
    proof(cases b)
      show "a = None \<Longrightarrow> b = None \<Longrightarrow> is_bsup a b (bsup a b)"
        by(auto simp add: option_pleq option_bsup is_bsup_def is_least_def is_bub_def is_sup_def is_ub_def)

      fix b'
      assume Hi1 : "a = None"
      assume Hi2 : "b = Some b'"
      show "is_bsup a b (bsup a b)"
      proof(rule is_bsupI)
        show "pleq a (bsup a b)" using Hi1 Hi2
          by(simp add: option_pleq option_bsup is_bsup_def is_least_def is_bub_def is_sup_def is_ub_def split:option.splits)
      next

        fix bd sd
        assume Hii1 : "pleq bd b"
        assume Hii2 : "is_sup {a, bd} sd"

        show "pleq sd (bsup a b)" 
        proof(cases bd)
          assume Hiii1 : "bd = None"
          have "is_sup {None} None" by (auto simp add:is_sup_def is_least_def is_ub_def option_pleq)
          hence "sd = None" using Hi1 Hii2 Hiii1 is_sup_unique by(cases sd; auto)
          thus "pleq sd (bsup a b)"
            by(auto simp add:option_pleq split:option.splits)
        next
          fix bd'
          assume Hiii1 : "bd = Some bd'"
          have "is_sup {None, Some bd'} (Some bd')" by(auto simp add:is_sup_def is_least_def is_ub_def option_pleq leq_refl)
          hence "sd = Some bd'" using Hi1 Hii2 Hiii1 is_sup_unique 
            by(cases sd; auto)
          thus "pleq sd (bsup a b)" using Hi1 Hi2 Hii1 Hiii1
            by(auto simp add:option_pleq option_bsup split:option.splits)
        qed
      next
        fix x'
        assume H : "is_bub a b x'"
        show "pleq (bsup a b) x'" using is_bubD2[OF H]
        proof(-)
          assume Hleast : "(\<And>(bd::'a option) sd::'a option. pleq bd b \<Longrightarrow> is_sup {a, bd} sd \<Longrightarrow> pleq sd x')"

          have 0 : "pleq (Some b') (b)" using Hi2 by(simp add: leq_refl)

          have 1 : "is_sup {a, (Some b')} (Some b')" using Hi1
            by(auto simp add:option_pleq is_sup_def is_least_def is_ub_def leq_refl)

          show "pleq (bsup a b) x'" using Hleast[OF 0 1]
            by(simp add: Hi1 Hi2 option_bsup)
        qed
      qed
    qed
  next
    case (Some a')
    then show ?thesis
    proof(cases b)
      assume Hi1 : "a = Some a'"
      assume Hi2 : "b = None"
      show "is_bsup a b (bsup a b)"
      proof(rule is_bsupI)
        show "pleq a (bsup a b)" using Hi1 Hi2
          by(simp add: option_pleq option_bsup is_bsup_def is_least_def is_bub_def is_sup_def is_ub_def leq_refl split:option.splits)
      next
        fix bd sd
        assume Hii1 : "pleq bd b"
        assume Hii2 : "is_sup {a, bd} sd"

        show "pleq sd (bsup a b)" 
        proof(cases bd)
          assume Hiii1 : "bd = None"
          have "is_sup {Some a', None} (Some a')" by(auto simp add:is_sup_def is_least_def is_ub_def option_pleq leq_refl)
          hence "sd = Some a'" using Hi1 Hi2 Hii1 Hii2 Hiii1 is_sup_unique by(cases sd; auto)
          thus "pleq sd (bsup a b)" using Hi1 Hi2 leq_refl
            by(auto simp add:option_pleq option_bsup)
        next
          fix bd'
          assume Hiii1 : "bd = Some bd'"
          (* contradiction *)
          thus "pleq sd (bsup a b)" using Hi2 Hii1 Hiii1 
            by(auto simp add:option_pleq option_bsup)
        qed

      next
          fix x'
          assume H : "is_bub a b x'"
          show "pleq (bsup a b) x'" using is_bubD2[OF H]
          proof(-)
            assume Hleast : "(\<And>(bd::'a option) sd::'a option. pleq bd b \<Longrightarrow> is_sup {a, bd} sd \<Longrightarrow> pleq sd x')"

            have 0 : "pleq (None) (b)" using Hi2 by(simp add: leq_refl)

            have 1 : "is_sup {a, None} (a)" using Hi1
              by(auto simp add:option_pleq is_sup_def is_least_def is_ub_def leq_refl)

            show "pleq (bsup a b) x'" using Hleast[OF 0 1]
              by(simp add: Hi1 Hi2 option_bsup)
          qed
        qed

      next

        fix b'
        assume Hi1 : "a = Some a'"
        assume Hi2 : "b = Some b'"
        show "is_bsup a b (bsup a b)"
        proof(rule is_bsupI)
          show "pleq a (bsup a b)" using Hi1 Hi2 bsup_leq bsup_spec[of a' b']
            by(auto simp add: option_pleq option_bsup is_bsup_def is_least_def is_bub_def is_sup_def is_ub_def leq_refl split:option.splits)
        next

          fix bd sd
          assume Hii1 : "pleq bd b"
          assume Hii2 : "is_sup {a, bd} sd"
          show "pleq sd (bsup a b)"
          proof(cases bd)
            assume Hiii1 : "bd = None"  
            have "is_sup {Some a', None} (Some a')" by(auto simp add:is_sup_def is_least_def is_ub_def option_pleq leq_refl)
            hence "sd = Some a'" using Hi1 Hi2 Hii1 Hii2 Hiii1 is_sup_unique by(cases sd; auto)
            thus "pleq sd (bsup a b)" using Hi1 Hi2 bsup_leq bsup_spec[of a' b']
              by(auto simp add:option_pleq option_bsup)
          next
            fix bd'
            assume Hiii1 : "bd = Some bd'"
            obtain sd' where Hsd' : "sd = Some sd'"
              using Hii2 Hi1
              by(auto simp add:is_sup_def is_least_def is_ub_def option_pleq split:option.splits)

            have OSup :  "is_sup {a', bd'} sd'" 
            proof(rule is_supI)
              fix x'
              assume H : "x' \<in> {a', bd'}"
              have 0 : "pleq a' sd'"  using Hii2 Hi1 Hsd'
                by(auto simp add:is_sup_def is_least_def is_ub_def option_pleq split:option.splits)

              have 1 : "pleq bd' sd'" using Hii2 Hiii1 Hsd'
                by(auto simp add:is_sup_def is_least_def is_ub_def option_pleq split:option.splits)

              show "pleq x' sd'" using H 0 1 by auto
            next
              fix x'
              assume H : "is_ub {a', bd'} x'"

              show "pleq sd' x'" using H Hi1 Hii2 Hiii1 Hsd'
                by(auto simp add:is_sup_def is_least_def is_ub_def option_pleq split:option.splits)
            qed

            have OBsup : "is_bsup a' b' (bsup a' b')" by (auto simp add:bsup_spec)

            have Hbbd' : "pleq bd' b'" using Hi2 Hii1 Hiii1
              by(auto simp add:option_pleq)
            
            show "pleq sd (bsup a b)" using is_bsupD2[OF OBsup Hbbd' OSup] Hsd' Hi1 Hi2 Hiii1
              by(auto simp add:option_pleq option_bsup)
          qed

        next
          fix x
          assume H: "is_bub a b x"

          obtain x' where Hx' : "x = Some x'" using Hi1 Hi2 H 
            by(auto simp add:is_bub_def option_pleq split:option.splits)

          have Bub' : "is_bub a' b' x'" 
          proof(rule is_bubI)
            show "pleq a' x'" using Hi1 Hx' is_bubD1[OF H]
              by(auto simp add:option_pleq)

          next

            fix bd' sd'
            assume Hpleq' : "pleq bd' b'"
            assume HOsup : "is_sup {a', bd'} sd'"

            have Hpleq : "pleq (Some bd') (b)" using Hi2 Hpleq' by (auto simp add:option_pleq)

            have HSup : "is_sup {a, Some bd'} (Some sd')"
              using Hi1 HOsup 
              by(auto simp add:option_pleq is_sup_def is_least_def is_ub_def split:option.splits)

            show "pleq sd' x'" using Hi1 Hx' is_bubD2[OF H Hpleq HSup]
              by(auto simp add:option_pleq is_sup_def)
          qed


          show "pleq (bsup a b) x" using Hx' Hi1 Hi2 Bub' bsup_spec[of a' b']
            by(auto simp add:option_pleq option_bsup is_bsup_def is_least_def)
        qed
      qed
    qed
  qed
end

instantiation option :: (Pordc_all) Pordc_all
begin
instance proof
  fix a b :: "('a option)"

  show "has_ub {a, b}"
  proof(cases a)
    case None
    then have "is_ub {a, b} b"
      by(cases b; auto simp add: is_ub_def option_pleq leq_refl)
    then show ?thesis
      by(auto simp add: has_ub_def)
  next
    case (Some a')
    show ?thesis
    proof(cases b)
      case None' : None
      then have "is_ub {a, b} a" using Some
        by(auto simp add: is_ub_def option_pleq leq_refl)
      then show ?thesis
        by(auto simp add: has_ub_def)
    next
      case Some' : (Some b')

      obtain ub where Ub: "is_ub {a', b'} ub"
        using ub2_all
        by(auto simp add: has_ub_def)

      then have "is_ub {a, b} (Some ub)"
        unfolding Some Some'
        using is_ub_Some[OF _ Ub]
        by auto

      then show ?thesis
        by(auto simp add: has_ub_def)
    qed
  qed
qed   

end

end