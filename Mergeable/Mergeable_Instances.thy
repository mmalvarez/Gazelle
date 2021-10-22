theory Mergeable_Instances imports Mergeable Wrappers Mergeable_Facts
begin

(* 
 * Here we instantiate the Mergeable typeclass (and friends) for a of built-in
 * Isabelle types, as well as for the types defined in Wrappers.
 * The instances defined here are sufficient for many purposes.
 * In order to work with Gazelle, data (state types used by merged semantics)
 * need to (at least) satisfy the Mergeable typeclass.
 * Any datatype can be used with Gazelle if wrapped in the "md_triv" wrapper, which induces
 * a trivial ordering. If a more interesting ordering is desired, 
 * Mergeable must be instantiated at a new datatype corresponding to data with that
 * ordering (see, for instance Mergeable_AList.thy)
 *)

(* Trivial ordering: (x <[ x \<leftrightarrow> x = x)
 * md_triv is complete, but lacks a least element.
 *)
instantiation md_triv :: (_) Pord_Weak
begin
definition triv_pleq : "(a :: 'a md_triv) <[ b = (a = b)"
  instance proof
    fix a :: "'a md_triv"
    show "a <[ a" unfolding triv_pleq
      by auto
  next
    fix a b c :: "'a md_triv"
    show "a <[ b \<Longrightarrow> b <[ c \<Longrightarrow> a <[ c"
      unfolding triv_pleq by auto
  qed
end

instantiation md_triv :: (_) Pord
begin
instance proof
  fix a b :: "'a md_triv"
  show "a <[ b \<Longrightarrow> b <[ a \<Longrightarrow> a = b"
    unfolding triv_pleq by auto
qed
end

instantiation md_triv :: (_) Pordc
begin
instance proof
 fix a b :: "'a md_triv"
    assume "has_ub {a, b :: 'a md_triv}"
    show "has_ub {a, b} \<Longrightarrow> has_sup {a, b}" unfolding triv_pleq
      by(auto simp add:
    has_ub_def is_ub_def
    has_sup_def is_sup_def is_least_def triv_pleq)
  qed
end

instantiation md_triv :: (_) Pordps
begin
instance proof
  fix a b c :: "'a md_triv"

  assume "has_sup {a, b}"
  then have "a = b"
  by(auto simp add:
      has_ub_def is_ub_def
      has_sup_def is_sup_def is_least_def triv_pleq)

  assume "has_sup {b, c}"
  then have "b = c"
  by(auto simp add:
      has_ub_def is_ub_def
      has_sup_def is_sup_def is_least_def triv_pleq)

  assume "has_sup {a, c}"

  show "has_sup {a, b, c}"
    unfolding `a = b` `b = c`
  by(auto simp add:
      has_ub_def is_ub_def
      has_sup_def is_sup_def is_least_def triv_pleq)
qed
end

instantiation md_triv :: (_) Mergeable 
begin

definition triv_bsup : "[^(a :: 'a md_triv), b^] = a"

instance proof
    fix a b :: "'a md_triv"
    show "is_bsup a b (bsup a b)" unfolding triv_pleq triv_bsup
      by( simp only:
             triv_pleq triv_bsup is_bsup_def is_least_def is_bub_def is_sup_def is_ub_def;
             fast)
  qed
end

(* Option is used to express a pointed ordering with a least element (None).
 * It can be seen as lifting an ordering on 'a to a pointed ordering on 'a option *)
instantiation option :: (Pord_Weak) Pord_Weak
begin
definition option_pleq : "(x :: 'a option) <[ y =
(case x of
      None \<Rightarrow> True
      | Some x' \<Rightarrow>
        (case y of
          None \<Rightarrow> False
          | Some y' \<Rightarrow> (pleq x' y')))"

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

instantiation option :: (Pord_Weak) Pord_Weakb
begin

definition option_bot : "bot = (None :: 'a option)"

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

instantiation option :: (Mergeable) Mergeableb
begin
definition option_bsup: "[^(x :: 'a option), y^] =
  (case x of
    None \<Rightarrow> y
    | Some x' \<Rightarrow> (case y of
                       None \<Rightarrow> Some x'
                       | Some y' \<Rightarrow> Some (bsup x' y')))"
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

(* For product types, we impose an ordering that requires that _all_ components of
 * product a be less than or equal to their corresponding components of b,
 * in order for a <[ b to hold.
 *
 * In other words, this is _not_ a lexicographic ordering. Lexicographic orderings
 * where the first component is arbitrary create problems around completeness.
 * This is why we work with a more restricted version of a lexicographic-like ordering, md_prio,
 * a pair where the first component is guaranteed to be a natural number, and the ordering
 * is lexicographic (see below)
 *)


instantiation prod :: (Pord_Weak, Pord_Weak) Pord_Weak
begin
  definition prod_pleq : 
  "(x :: 'a * 'b) <[ y =
    (case x of
        (x1, x2) \<Rightarrow> (case y of
                      (y1, y2) \<Rightarrow> (pleq x1 y1 \<and> pleq x2 y2)))"
instance proof
  fix a :: "('a * 'b)"
  show "pleq a a" by (auto simp add:prod_pleq leq_refl split:prod.splits)
next
  fix a b c :: "('a * 'b)"
  assume H1 : "pleq a b"
  assume H2 : "pleq b c"

  obtain a1 and a2 where 0 : "a = (a1, a2)" by (cases a; auto)
  obtain b1 and b2 where 1 : "b = (b1, b2)" by (cases b; auto)
  obtain c1 and c2 where 2 : "c = (c1, c2)" by (cases c; auto)

  show "pleq a c" using H1 H2 0 1 2 leq_trans[of a1 b1 c1] leq_trans[of a2 b2 c2]
    by (auto simp add:prod_pleq)
qed
end

instantiation prod :: (Pord, Pord) Pord
begin
instance proof
  fix a b :: "('a * 'b)"
  assume H1 : "pleq a b"
  assume H2 : "pleq b a"

  obtain a1 and a2 where 0 : "a = (a1, a2)" by (cases a; auto)
  obtain b1 and b2 where 1 : "b = (b1, b2)" by (cases b; auto)

  show "a = b" using H1 H2 0 1 leq_antisym[of a1 b1] leq_antisym[of a2 b2]
    by(auto simp add:prod_pleq)
qed
end

instantiation prod :: (Pordc, Pordc) Pordc
begin
instance proof

  fix a b :: "('a * 'b)"
  assume H : "has_ub {a, b}"

  obtain a1 and a2 where 0 : "a = (a1, a2)" by (cases a; auto)
  obtain b1 and b2 where 1 : "b = (b1, b2)" by (cases b; auto)

  obtain ub where HUb : "is_ub {a, b} ub" using H by (auto simp add:has_ub_def)
  obtain ub1 and ub2 where HUb' : "ub = (ub1, ub2)" by (cases ub; auto)

  have Ub1 : "is_ub {a1, b1} ub1" using H 0 1 HUb HUb'
    by(auto simp add:prod_pleq is_ub_def)
  have Ub2 : "is_ub {a2, b2} ub2" using H 0 1 HUb HUb'
    by(auto simp add:prod_pleq is_ub_def)

  obtain sup1 where Sup1 : "is_sup {a1, b1} sup1" using complete2[of a1 b1] Ub1
    by(auto simp add: has_sup_def has_ub_def)

  obtain sup2 where Sup2 : "is_sup {a2, b2} sup2"
    using complete2[of a2 b2] Ub2
    by(auto simp add: has_sup_def has_ub_def)

  have Sup : "is_sup {(a1, a2), (b1, b2)} (sup1, sup2)" using Sup1 Sup2
    by(auto simp add: prod_pleq is_sup_def is_ub_def is_least_def)

  thus "has_sup {a, b}" using 0 1 by (auto simp add:has_sup_def)
qed
end
lemma is_sup_fst :
  assumes Hnemp : "x \<in> Xs"
  assumes H : "is_sup Xs supr"
  shows "is_sup ((\<lambda> w . (w, x')) ` Xs) (supr, x')"
proof(rule is_supI)
  fix x

  assume X: "x \<in> (\<lambda>w. (w, x')) ` Xs"

  then obtain x1 where X1 :
    "x = (x1, x')" "x1 \<in> Xs"
    by auto

  have "x1 <[ supr"
    using is_supD1[OF H X1(2)] by auto

  then show "x <[ (supr, x')"
    using X1
    by(auto simp add: prod_pleq leq_refl)
next

  fix y

  assume Y: "is_ub ((\<lambda>w. (w, x')) ` Xs) y"

  obtain y1 y2 where Y1_2 : "y = (y1, y2)"
    by(cases y; auto)

  have "is_ub Xs y1"
  proof(rule is_ubI)
    fix z

    assume Z: "z \<in> Xs"

    then have "(z, x') <[ y"
      using is_ubE[OF Y] by auto

    then show "z <[ y1"
      using Y1_2
      by(auto simp add: prod_pleq)
  qed

  then have "supr <[ y1"
    using is_supD2[OF H]
    by auto

  have "(x, x') <[ y"
    using is_ubE[OF Y] Hnemp
    by auto

  then have "x' <[ y2"
    using Y1_2
    by(auto simp add: prod_pleq)

  show "(supr, x') <[ y"
    using `supr <[ y1` `x' <[ y2` Y1_2
    by(auto simp add: prod_pleq)
qed

lemma is_sup_fst' :
  assumes Hnemp : "xy \<in> Xys"
  assumes H : "is_sup Xys (s1, s2)"
  shows "is_sup (fst ` Xys) s1"
proof(rule is_supI)

  fix x

  assume X: "x \<in> fst ` Xys"
  then obtain y where Xy : "(x, y) \<in> Xys"
    by(auto)

  then have "(x, y) <[ (s1, s2)"
    using is_supD1[OF H Xy]
    by auto

  then show "x <[ s1"
    by(auto simp add: prod_pleq)
next

  fix x'

  assume X' : "is_ub (fst ` Xys) x'"

  have Ub' : "is_ub Xys (x', s2)"
  proof(rule is_ubI)

    fix w

    assume W : "w \<in> Xys"

    obtain w1 w2 where W1_2 :
      "w = (w1, w2)"
      by(cases w; auto)

    then have "w1 \<in> fst ` Xys" using imageI[OF W, of fst]
      by auto

    then have "w1 <[ x'"
      using is_ubE[OF X'] by auto

    have "w2 \<in> snd ` Xys" using imageI[OF W, of snd] W1_2
      by auto

    then have "w2 <[ s2"
      using is_supD1[OF H W] W1_2
      by(auto simp add: prod_pleq)

    then show "w <[ (x', s2)"
      using `w1 <[ x'` W1_2
      by(auto simp add: prod_pleq)
  qed

  show "s1 <[ x'"
    using is_supD2[OF H Ub']
    by(auto simp add: prod_pleq)
qed

lemma is_sup_snd :
  assumes Hnemp : "x \<in> Xs"
  assumes H : "is_sup Xs supr"
  shows "is_sup ((\<lambda> w . (x', w)) ` Xs) (x', supr)"
proof(rule is_supI)
  fix x

  assume X: "x \<in> (\<lambda>w. (x', w)) ` Xs"

  then obtain x2 where X2 :
    "x = (x', x2)" "x2 \<in> Xs"
    by auto

  have "x2 <[ supr"
    using is_supD1[OF H X2(2)] by auto

  then show "x <[ (x', supr)"
    using X2
    by(auto simp add: prod_pleq leq_refl)
next

  fix y

  assume Y: "is_ub ((\<lambda>w. (x', w)) ` Xs) y"

  obtain y1 y2 where Y1_2 : "y = (y1, y2)"
    by(cases y; auto)

  have "is_ub Xs y2"
  proof(rule is_ubI)
    fix z

    assume Z: "z \<in> Xs"

    then have "(x', z) <[ y"
      using is_ubE[OF Y] by auto

    then show "z <[ y2"
      using Y1_2
      by(auto simp add: prod_pleq)
  qed

  then have "supr <[ y2"
    using is_supD2[OF H]
    by auto

  have "(x', x) <[ y"
    using is_ubE[OF Y] Hnemp
    by auto

  then have "x' <[ y1"
    using Y1_2
    by(auto simp add: prod_pleq)

  show "(x', supr) <[ y"
    using `supr <[ y2` `x' <[ y1` Y1_2
    by(auto simp add: prod_pleq)
qed

lemma is_sup_snd' :
  assumes Hnemp : "xy \<in> Xys"
  assumes H : "is_sup Xys (s1, s2)"
  shows "is_sup (snd ` Xys) s2"
proof(rule is_supI)

  fix y

  assume Y: "y \<in> snd ` Xys"
  then obtain x where Xy : "(x, y) \<in> Xys"
    by(auto)

  then have "(x, y) <[ (s1, s2)"
    using is_supD1[OF H Xy]
    by auto

  then show "y <[ s2"
    by(auto simp add: prod_pleq)
next

  fix y'

  assume Y' : "is_ub (snd ` Xys) y'"

  have Ub' : "is_ub Xys (s1, y')"
  proof(rule is_ubI)

    fix w

    assume W : "w \<in> Xys"

    obtain w1 w2 where W1_2 :
      "w = (w1, w2)"
      by(cases w; auto)

    then have "w2 \<in> snd ` Xys" using imageI[OF W, of snd]
      by auto

    then have "w2 <[ y'"
      using is_ubE[OF Y'] by auto

    have "w1 \<in> fst ` Xys" using imageI[OF W, of fst] W1_2
      by auto

    then have "w1 <[ s1"
      using is_supD1[OF H W] W1_2
      by(auto simp add: prod_pleq)

    then show "w <[ (s1, y')"
      using `w2 <[ y'` W1_2
      by(auto simp add: prod_pleq)
  qed

  show "s2 <[ y'"
    using is_supD2[OF H Ub']
    by(auto simp add: prod_pleq)
qed

lemma is_sup_prod :
  assumes Hx : "is_sup Xs suprx"
  assumes Hy : "is_sup Ys supry"
  assumes S1 : "fst ` S = Xs"
  assumes S2 : "snd ` S = Ys"
  shows "is_sup S (suprx, supry)"
proof(rule is_supI)
  fix w
  assume W_in : "w \<in> S"

  obtain w1 w2 where W:
    "w = (w1, w2)"
    by(cases w; auto)

  have W_Xs : "w1 \<in> Xs" and W_Ys : "w2 \<in> Ys"
    using S1 S2 W_in W
    using imageI[OF W_in, of fst] imageI[OF W_in, of snd]
    by(auto)

  have "w1 <[ suprx" "w2 <[ supry"
    using is_supD1[OF Hx W_Xs] is_supD1[OF Hy W_Ys] W
    by auto

  then show "w <[ (suprx, supry)"
    using W by(auto simp add: prod_pleq)
next

  fix w'
  assume Ub : "is_ub S w'"

  obtain w'1 w'2 where W':
    "w' = (w'1, w'2)"
    by(cases w'; auto)

  have Ub_Xs : "is_ub Xs w'1"
  proof(rule is_ubI)
    fix x

    assume X : "x \<in> Xs"

    then obtain y where Y: "(x, y) \<in> S"
      using S1
      by(auto)

    have "(x, y) <[ w'"
      using is_ubE[OF Ub Y]
      by auto

    then show "x <[ w'1"
      using W'
      by(auto simp add: prod_pleq)
  qed

  have Ub_Ys : "is_ub Ys w'2"
  proof(rule is_ubI)
    fix y

    assume Y : "y \<in> Ys"

    then obtain x where X: "(x, y) \<in> S"
      using S2
      by(auto)

    have "(x, y) <[ w'"
      using is_ubE[OF Ub X]
      by auto

    then show "y <[ w'2"
      using W'
      by(auto simp add: prod_pleq)
  qed

  have "suprx <[ w'1" "supry <[ w'2"
    using is_supD2[OF Hx Ub_Xs] is_supD2[OF Hy Ub_Ys]
    by auto

  then show "(suprx, supry) <[ w'"
    using W'
    by(auto simp add: prod_pleq)
qed

instantiation prod :: (Pordps, Pordps) Pordps
begin
instance proof
  fix a b c :: "'a * 'b"

  assume "has_sup {a, b}"
  then obtain sup_ab
    where Sup_ab : "is_sup {a, b} sup_ab"
    by(auto simp add: has_sup_def)

  obtain sup_ab1 sup_ab2 where
    Sup_ab12 : "sup_ab = (sup_ab1, sup_ab2)"
    by(cases sup_ab; auto)

  assume Sup_bc : "has_sup {b, c}"
  then obtain sup_bc
    where Sup_bc : "is_sup {b, c} sup_bc"
    by(auto simp add: has_sup_def)

  obtain sup_bc1 sup_bc2 where
    Sup_bc12 : "sup_bc = (sup_bc1, sup_bc2)"
    by(cases sup_bc; auto)

  assume Sup_ac : "has_sup {a, c}"
  then obtain sup_ac
    where Sup_ac : "is_sup {a, c} sup_ac"
    by(auto simp add: has_sup_def)

  obtain sup_ac1 sup_ac2 where
    Sup_ac12 : "sup_ac = (sup_ac1, sup_ac2)"
    by(cases sup_ac; auto)

  obtain a1 a2 where A: "a = (a1, a2)"
    by(cases a; auto)

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  obtain c1 c2 where C: "c = (c1, c2)"
    by(cases c; auto)

  have Has_sup_ab1 :
    "has_sup {a1, b1}"
    using Sup_ab Sup_ab12 A B
      is_sup_fst'[of a "{a, b}" sup_ab1 sup_ab2]
    by(auto simp add: has_sup_def)

  have Has_sup_ab2 :
    "has_sup {a2, b2}"
    using Sup_ab Sup_ab12 A B
      is_sup_snd'[of a "{a, b}" sup_ab1 sup_ab2]
    by(auto simp add: has_sup_def)

  have Has_sup_bc1 :
    "has_sup {b1, c1}"
    using Sup_bc Sup_bc12 B C
      is_sup_fst'[of b "{b, c}" sup_bc1 sup_bc2]
    by(auto simp add: has_sup_def)

  have Has_sup_bc2 :
    "has_sup {b2, c2}"
    using Sup_bc Sup_bc12 B C
      is_sup_snd'[of b "{b, c}" sup_bc1 sup_bc2]
    by(auto simp add: has_sup_def)

  have Has_sup_ac1 :
    "has_sup {a1, c1}"
    using Sup_ac Sup_ac12 A C
      is_sup_fst'[of a "{a, c}" sup_ac1 sup_ac2]
    by(auto simp add: has_sup_def)

  have Has_sup_ac2 :
    "has_sup {a2, c2}"
    using Sup_ac Sup_ac12 A C
      is_sup_snd'[of a "{a, c}" sup_ac1 sup_ac2]
    by(auto simp add: has_sup_def)

  obtain sup1 where Sup1 :
    "is_sup {a1, b1, c1} sup1"
    using pairwise_sup[OF Has_sup_ab1 Has_sup_bc1 Has_sup_ac1]
    by(auto simp add: has_sup_def)

  obtain sup2 where Sup2 :
    "is_sup {a2, b2, c2} sup2"
    using pairwise_sup[OF Has_sup_ab2 Has_sup_bc2 Has_sup_ac2]
    by(auto simp add: has_sup_def)

  have "is_sup {a, b, c} (sup1, sup2)"
    using is_sup_prod[OF Sup1 Sup2, of "{a, b, c}"]
    unfolding A B C
    by auto

  then show "has_sup {a, b, c}"
    by(auto simp add: has_sup_def)
qed
end

instantiation prod :: (Pord_Weakb, Pord_Weakb) Pord_Weakb
begin
definition prod_bot : 
  "(bot :: 'a * 'b) = (bot, bot)"
instance proof
  fix a :: "'a * 'b"
  show "pleq bot a"
    by(cases a; auto simp add:prod_pleq prod_bot bot_spec)
qed
end

instantiation prod :: (Pordb, Pordb) Pordb
begin
instance proof
qed
end

instantiation prod :: (Mergeableb, Mergeableb) Mergeableb
begin

definition prod_bsup :
"[^ a, b ^] =
  (case a of
    (a1, a2) \<Rightarrow> (case b of
                  (b1, b2) \<Rightarrow> (bsup a1 b1, bsup a2 b2)))"

instance proof
  fix a :: "'a  * 'b"
  fix b :: "'a * 'b"

  obtain a1 and a2 where Ha : "a = (a1, a2)" by(cases a; auto)
  obtain b1 and b2 where Hb : "b = (b1, b2)" by(cases b; auto)

  show "is_bsup a b (bsup a b)"
  proof(rule is_bsupI)

    show "pleq a (bsup a b)" using Ha Hb bsup_leq[OF bsup_spec[of a1 b1]] bsup_leq[OF bsup_spec[of a2 b2]]
      by(auto simp add:prod_bsup prod_pleq split:prod.splits)

  next
    fix bd :: "'a * 'b"
    fix sd :: "'a * 'b"

    obtain a1 and a2 where Ha : "a = (a1, a2)" by(cases a; auto)
    obtain b1 and b2 where Hb : "b = (b1, b2)" by(cases b; auto)
    obtain bd1 and bd2 where Hbd : "bd = (bd1, bd2)" by(cases bd; auto)
    obtain sd1 and sd2 where Hsd : "sd = (sd1, sd2)" by(cases sd; auto)

    obtain bsupv1 and bsupv2 where Hbsup : "bsup a b = (bsupv1, bsupv2)" by (cases "(bsup a b)"; auto)

    assume Hleq : "pleq bd b"
    assume Hsup : "is_sup {a, bd} sd"

    have Hbsv1 : "bsupv1 = bsup a1 b1" using Ha Hb Hbsup
      by(auto simp add:prod_bsup)
    have Hbsv2 : "bsupv2 = bsup a2 b2" using Ha Hb Hbsup
      by(auto simp add:prod_bsup)

    have Sup1 : "is_sup {a1, bd1} sd1" using Ha Hbd Hsd Hsup
      by(auto simp add: prod_pleq is_sup_def is_least_def is_ub_def)

    have Sup2 : "is_sup {a2, bd2} sd2" using Ha Hbd Hsd Hsup
      by(auto simp add: prod_pleq is_sup_def is_least_def is_ub_def)

    have Leq1 : "pleq bd1 b1" using Hb Hbd Hleq
      by(auto simp add: prod_pleq is_sup_def is_least_def is_ub_def)

    have Leq2 : "pleq bd2 b2" using Hb Hbd Hleq
      by(auto simp add: prod_pleq is_sup_def is_least_def is_ub_def)

    have Bsup1 : "is_bsup a1 b1 bsupv1" using Hbsup Ha Hb bsup_spec[of a1 b1]
      by(auto simp add:prod_bsup)

    have Bsup2 : "is_bsup a2 b2 bsupv2" using Hbsup Ha Hb bsup_spec[of a2 b2]
      by(auto simp add:prod_bsup)

    have Conc1 : "pleq sd1 (bsup a1 b1)" using is_bsupD2[OF Bsup1 Leq1 Sup1] Hbsv1
      by(auto simp add:is_bsup_def is_least_def is_bub_def)
      
    have Conc2 : "pleq sd2 (bsup a2 b2)" using is_bsupD2[OF Bsup2 Leq2 Sup2] Hbsv2
      by(auto simp add:is_bsup_def is_least_def is_bub_def)

    show "pleq sd (bsup a b)" using Ha Hb Hbsup Hbsv1 Hbsv2 Hsd Conc1 Conc2
      by(auto simp add: prod_pleq prod_bsup)

  next

      fix x :: "'a * 'b"
      obtain a1 and a2 where Ha : "a = (a1, a2)" by(cases a; auto)
      obtain b1 and b2 where Hb : "b = (b1, b2)" by(cases b; auto)
      obtain x1 and x2 where Hx : "x = (x1, x2)" by(cases x; auto)
      obtain bsupv1 and bsupv2 where Hbsup : "bsup a b = (bsupv1, bsupv2)" by (cases "(bsup a b)"; auto)

      have Hbsv1 : "bsupv1 = bsup a1 b1" using Ha Hb Hbsup
        by(auto simp add:prod_bsup)
      have Hbsv2 : "bsupv2 = bsup a2 b2" using Ha Hb Hbsup
        by(auto simp add:prod_bsup)

      assume Hbub : "is_bub a b x"

      have Hbub1 : "is_bub a1 b1 x1"
      proof(rule is_bubI)
        show "pleq a1 x1" using Hbub Ha Hx by(auto simp add:is_bub_def is_sup_def prod_pleq)
      next
        fix bd1 :: 'a
        fix sd1 :: 'a
        assume H1 : "pleq bd1 b1"
        assume H2 : "is_sup {a1,bd1} sd1"

        have Hpleq' : "pleq (bd1, bot) b" using H1 Hb bot_spec[of b2]
          by (auto simp add: prod_pleq)
        
        have Hsup' : "is_sup {a, (bd1, bot)} (sd1, a2)" using Ha bot_spec[of a2] H2
          by(auto simp add:is_sup_def is_least_def is_ub_def leq_refl prod_pleq)

        show "pleq sd1 x1" using is_bubD2[OF Hbub Hpleq' Hsup'] Hx
          by(simp add:prod_pleq)
      qed
  
      have Hbub2 : "is_bub a2 b2 x2" 
      proof(rule is_bubI)
        show "pleq a2 x2" using Hbub Ha Hx by(auto simp add:is_bub_def is_sup_def prod_pleq)
      next
        fix bd2 :: 'b
        fix sd2 :: 'b
        assume H1 : "pleq bd2 b2"
        assume H2 : "is_sup {a2,bd2} sd2"

        have Hpleq' : "pleq (bot, bd2) b" using H1 Hb bot_spec[of b1]
          by (auto simp add: prod_pleq)
        
        have Hsup' : "is_sup {a, (bot, bd2)} (a1, sd2)" using Ha bot_spec[of a1] H2
          by(auto simp add:is_sup_def is_least_def is_ub_def leq_refl prod_pleq)

        show "pleq sd2 x2" using is_bubD2[OF Hbub Hpleq' Hsup'] Hx
          by(simp add:prod_pleq)
      qed

      show "pleq (bsup a b) x" using Hx Ha Hb Hbub1 Hbub2 bsup_spec[of a1 b1] bsup_spec[of a2 b2]
        by(auto simp add:is_bsup_def is_least_def prod_pleq prod_bsup)
    qed
  qed
end


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

(* TODO: could we get away with md_prio :: (Pordb) Pordbc?
 *)
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


(*
(* This is easy if we know Pordb. But what if we do not?
i don't think we can show this in general - can't conclude that {a, b, c}
having supremum means that the pairs do. *)
instantiation md_prio :: (Pord) Pordps
begin
instance proof

  fix a b c :: "'a md_prio"

  obtain pa' a' where A: "a = mdp pa' a'"
    by(cases a; auto)

  obtain pb' b' where B: "b = mdp pb' b'"
    by(cases b; auto)

  obtain pc' c' where C: "c = mdp pc' c'"
    by(cases c; auto)

  assume "has_sup {a, b}"
  then obtain sup_ab where Sup_ab :
    "is_sup {a, b} sup_ab"
    by(auto simp add: has_sup_def)

  obtain psup_ab' sup_ab' where Sup_ab' :
    "sup_ab = mdp psup_ab' sup_ab'"
    by(cases sup_ab; auto)

  assume "has_sup {b, c}"
  then obtain sup_bc where Sup_bc :
    "is_sup {b, c} sup_bc"
    by(auto simp add: has_sup_def)

  obtain psup_bc' sup_bc' where Sup_bc' :
    "sup_bc = mdp psup_bc' sup_bc'"
    by(cases sup_bc; auto)

  assume "has_sup {a, c}"
  then obtain sup_ac where Sup_ac :
    "is_sup {a, c} sup_ac"
    by(auto simp add: has_sup_def)

  obtain psup_ac' sup_ac' where Sup_ac' :
    "sup_ac = mdp psup_ac' sup_ac'"
    by(cases sup_ac; auto)

(* there is probably a more elegant way to do this. *)
  consider
    (Amax) "pb' < pa'" "pc' < pa'" |
    (Bmax) "pa' < pb'" "pc' < pb'" |
    (Cmax) "pa' < pc'" "pb' < pc'" |
    (ABmax) "pa' = pb'" "pc' < pa'" |
    (BCmax) "pa' < pb'" "pb' = pc'" |
    (ACmax) "pb' < pa'" "pa' = pc'" |
    (ABCmax) "pa' = pb'" "pb' = pc'"
    by(arith)

  then show "has_sup {a, b, c}"
  proof cases
    case Amax

    have "is_sup {a, b, c} a"
    proof(rule is_supI)
      fix x
      assume In : "x \<in> {a, b, c}"
      then show "x <[ a"
        using Amax
        unfolding A B C
        by(auto simp add: leq_refl prio_pleq)
    next
      fix x'
      assume Ub: "is_ub {a, b, c} x'"
      then show "a <[ x'"
        using is_ubE[OF Ub, of a] by auto
    qed

    then show ?thesis
      by(auto simp add: has_sup_def)
  next
    case Bmax
    have "is_sup {a, b, c} b"
    proof(rule is_supI)
      fix x
      assume In : "x \<in> {a, b, c}"
      then show "x <[ b"
        using Bmax
        unfolding A B C
        by(auto simp add: leq_refl prio_pleq)
    next
      fix x'
      assume Ub: "is_ub {a, b, c} x'"
      then show "b <[ x'"
        using is_ubE[OF Ub, of b] by auto
    qed

    then show ?thesis
      by(auto simp add: has_sup_def)
  next
    case Cmax
    have "is_sup {a, b, c} c"
    proof(rule is_supI)
      fix x
      assume In : "x \<in> {a, b, c}"
      then show "x <[ c"
        using Cmax
        unfolding A B C
        by(auto simp add: leq_refl prio_pleq)
    next
      fix x'
      assume Ub: "is_ub {a, b, c} x'"
      then show "c <[ x'"
        using is_ubE[OF Ub, of c] by auto
    qed

    then show ?thesis
      by(auto simp add: has_sup_def)
  next
    case ABmax

    have "is_sup {a, b, c} sup_ab"
    proof(rule is_supI)
      fix x
      assume In: "x \<in> {a, b, c}"
      then show "x <[ sup_ab"
      using is_supD1[OF Sup_ab, of a] is_supD1[OF Sup_ab, of b] ABmax
      unfolding A B C Sup_ab'
        by(auto simp add: prio_pleq split:if_splits)
    next

      fix w
      assume Ub : "is_ub {a, b, c} w"

      have Ub' : "is_ub {a, b} w"
      proof(rule is_ubI)
        fix z

        assume "z \<in> {a, b}" 
        then have In' : "z \<in> {a, b, c}" by auto
        show "z <[ w" using is_ubE[OF Ub In']
          by auto
      qed

      then show "sup_ab <[ w"
        using is_supD2[OF Sup_ab]
        by auto
    qed

    then show ?thesis by(auto simp add: has_sup_def)

  next
    case ACmax

    have "is_sup {a, b, c} sup_ac"
    proof(rule is_supI)
      fix x
      assume In: "x \<in> {a, b, c}"
      then show "x <[ sup_ac"
      using is_supD1[OF Sup_ac, of a] is_supD1[OF Sup_ac, of c] ACmax
      unfolding A B C Sup_ac'
        by(auto simp add: prio_pleq split:if_splits)
    next

      fix w
      assume Ub : "is_ub {a, b, c} w"

      have Ub' : "is_ub {a, c} w"
      proof(rule is_ubI)
        fix z

        assume "z \<in> {a, c}" 
        then have In' : "z \<in> {a, b, c}" by auto
        show "z <[ w" using is_ubE[OF Ub In']
          by auto
      qed

      then show "sup_ac <[ w"
        using is_supD2[OF Sup_ac]
        by auto
    qed

    then show ?thesis by(auto simp add: has_sup_def)

  next
    case BCmax

    have "is_sup {a, b, c} sup_bc"
    proof(rule is_supI)
      fix x
      assume In: "x \<in> {a, b, c}"
      then show "x <[ sup_bc"
      using is_supD1[OF Sup_bc, of b] is_supD1[OF Sup_bc, of c] BCmax
      unfolding A B C Sup_bc'
        by(auto simp add: prio_pleq split:if_splits)
    next

      fix w
      assume Ub : "is_ub {a, b, c} w"

      have Ub' : "is_ub {b, c} w"
      proof(rule is_ubI)
        fix z

        assume "z \<in> {b, c}" 
        then have In' : "z \<in> {a, b, c}" by auto
        show "z <[ w" using is_ubE[OF Ub In']
          by auto
      qed

      then show "sup_bc <[ w"
        using is_supD2[OF Sup_bc]
        by auto
    qed

    then show ?thesis by(auto simp add: has_sup_def)

  next

    case ABCmax

    show ?thesis
    proof(cases "has_sup {a', b', c'}")
      case True

      then obtain sup' where Sup'_sup : "is_sup {a', b', c'} sup'"
        by(auto simp add: has_sup_def)

      have "is_sup {a, b, c} (mdp pa' sup')"
      proof(rule is_supI)
        fix x

        assume X: "x \<in> {a, b, c}"
        then obtain px' x' where X' : "x = mdp px' x'" "x' \<in> {a', b', c'}"
          unfolding A B C 
          by(cases x; auto) 

        have "x' <[ sup'"
          using is_supD1[OF Sup'_sup X'(2)] by auto

        then show "x <[ mdp pa' sup'"
          using X unfolding X' A B C ABCmax
          by(auto simp add: prio_pleq)
      next

        fix w

        assume W: "is_ub {a, b, c} w"

        then obtain pw' w' where W' : "w = mdp pw' w'"
          by(cases w; auto)

        consider (WLt) "pw' < pa'" |
                 (WEq) "pw' = pa'" |
                 (WGt) "pa' < pw'"
          by arith
        then show "mdp pa' sup' <[ w"
        proof cases
          case WLt

          then have False using is_ubE[OF W, of a]
            unfolding A W'
            by(auto simp add: prio_pleq)

          then show ?thesis by auto
        next
          case WEq

          have Ub' : "is_ub {a', b', c'} w'"
          proof(rule is_ubI)
            fix z'
  
            assume Z': "z' \<in> {a', b', c'}"
  
            then have Z_in : "mdp pa' z' \<in> {a, b, c}"
              unfolding A B C ABCmax
              by auto
  
            then have "mdp pa' z' <[ mdp pa' w'"
              using is_ubE[OF W Z_in]
              unfolding W' WEq
              by auto

            then show "z' <[ w'"
              by(auto simp add: prio_pleq)
          qed

          (* problem: what if there is no least upper bound for the pairs?
             i think we can force one using \<bottom>. but then we don't need to do any of this. *)
          have Sup_ab'_inner : "is_sup {a', b'} sup_ab'"
          proof(rule is_supI)
            fix x'

            assume X' : "x' \<in> {a', b'}"
            then have X_in : "mdp pa' x' \<in> {a, b}"
              unfolding A B ABCmax
              by auto

            show "x' <[ sup_ab'"
              using is_supD1[OF Sup_ab X_in]
              unfolding Sup_ab' 

          then show ?thesis
            using pairwise_sup Sup_ab
        next
          case WGt
          then show ?thesis 
            unfolding W'
            by(auto simp add: prio_pleq)
        qed


      qed

        sorry

      then show ?thesis by(auto simp add: has_sup_def)
    next

      case False
(* idea: we know one of the three pairs must not have a sup. consider to find which one. *)
      then have "is
*)
(*

      then show ?thesis sorry
    next
      case False
      then show ?thesis sorry
    qed

(* maybe we can avoid all this mess... *)

    consider (AB_Lt) "psup_ab' < pa'" |
             (AB_Gt) "pa' < psup_ab'" |
             (AB_Eq) "pa' = psup_ab'"
      by arith

    then show ?thesis
    proof cases
      case AB_Lt

      then have False using is_supD1[OF Sup_ab, of a]
        unfolding A Sup_ab'
        by(auto simp add: prio_pleq)

      then show ?thesis by auto
    next
      case AB_Gt

      have Ub_ab: "is_ub {a, b} (mdp (pa' + 1) sup_ab')"
      proof(rule is_ubI)
        fix x
        assume "x \<in> {a, b}"
        then show "x <[ mdp (pa' + 1) sup_ab'"
          unfolding A B C ABCmax Sup_ab'
          by(auto simp add: prio_pleq)
      qed

      then have "psup_ab' = pa' + 1"
        using is_supD2[OF Sup_ab Ub_ab] AB_Gt
        unfolding Sup_ab'
        by(auto simp add: prio_pleq split: if_splits)

      consider (BC_Lt) "psup_bc' < pa'" |
               (BC_Gt) "pa' < psup_bc'" |
               (BC_Eq) "pa' = psup_bc'"
        by arith

      then show ?thesis
      proof cases

        case BC_Lt

        then have False using is_supD1[OF Sup_bc, of b]
          unfolding B Sup_bc' ABCmax
          by(auto simp add: prio_pleq)

        then show ?thesis by auto
      next

        case BC_Gt

        have Ub_bc: "is_ub {b, c} (mdp (pa' + 1) sup_bc')"
        proof(rule is_ubI)
          fix x
          assume "x \<in> {b, c}"
          then show "x <[ mdp (pa' + 1) sup_bc'"
            unfolding A B C ABCmax Sup_bc'
            by(auto simp add: prio_pleq)
        qed
  
        then have "psup_bc' = pa' + 1"
          using is_supD2[OF Sup_bc Ub_bc] BC_Gt
          unfolding Sup_bc'
          by(auto simp add: prio_pleq split: if_splits)
  
        consider (AC_Lt) "psup_ac' < pa'" |
                 (AC_Gt) "pa' < psup_ac'" |
                 (AC_Eq) "pa' = psup_ac'"
          by arith

          then show ?thesis
          proof cases
            case AC_Lt
  
            then have False using is_supD1[OF Sup_ac, of a]
              unfolding A Sup_ac' ABCmax
              by(auto simp add: prio_pleq)
    
            then show ?thesis by auto
          next
            case AC_Gt

            have Ub_ac: "is_ub {a, c} (mdp (pa' + 1) sup_ac')"
            proof(rule is_ubI)
              fix x
              assume "x \<in> {a, c}"
              then show "x <[ mdp (pa' + 1) sup_ac'"
                unfolding A B C ABCmax Sup_ac'
                by(auto simp add: prio_pleq)
            qed
      
            then have "psup_ac' = pa' + 1"
              using is_supD2[OF Sup_ac Ub_ac] AC_Gt
              unfolding Sup_ac'
              by(auto simp add: prio_pleq split: if_splits)

            

            then show ?thesis sorry
          next
            case AC_Eq
            then show ?thesis sorry
          qed
      
      next
        case AB_Eq
        then show ?thesis sorry
      qed


    have Sup_ab_inner :
      "is_sup {a', b'} sup_ab'"
    proof(rule is_supI)
      fix x
      assume In: "x \<in> {a', b'}"
      then show "x <[ sup_ab'"
        using is_supD1[OF Sup_ab, of a] is_supD1[OF Sup_ab, of b] ABCmax
        unfolding A B Sup_ab'
        apply(auto simp add: prio_pleq split:if_splits)

      obtain pw' w' where W: "w = mdp pw' w'"
        by(cases w; auto)

      consider
        (Pw'_lt) "pw' < pa'" |
        (Pw'_eq) "pw' = pa'" |
        (Pw'_gt) "pw' > pa'"
        by arith

      then show "sup_ab <[ w"
      proof cases
        case Pw'_lt

        then have False using is_ubE[OF Ub, of a]
          unfolding A W
          by(auto simp add: prio_pleq split: if_splits)

        then show ?thesis by auto
      next
        case Pw'_eq
        then show ?thesis sorry
      next
        case Pw'_gt
        then show ?thesis sorry
      qed


    then show ?thesis sorry
  next
    case BCmax
    then show ?thesis sorry
  next
    case ACmax
    then show ?thesis sorry
  next
    case ABCmax
    then show ?thesis sorry
  qed
*)

(* This is easy if we know Pordb. But what if we do not? *)
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


(* Sums are mergeable if their components are.
 * Note that talking about least elements (that is, having a pordb instance) for sum is
 * tricky, as we would need to arbitrarily decide that inl \<bottom> <[ inr \<bottom>,
 * or vice versa (but not both, since inl \<bottom> \<noteq> inr \<bottom>, and there is nothing we can do about
 * that)
 * Rather than doing this, we do not derive a Pordb instance for sum; if the user wishes
 * to induce a least element, they can wrap the sum in an option (a more "neutral" choice
 * than picking one side or the other); or they can derive their own ordering
 * for a copy of the sum type. *)
instantiation sum :: (Pord_Weak, Pord_Weak) Pord_Weak
begin
definition sum_pleq : "(x :: 'a + 'b) <[ y =
(case x of
      Inl x' \<Rightarrow> (case y of
                  Inl y' \<Rightarrow> x' <[ y'
                  | _ \<Rightarrow> False)
      | Inr x' \<Rightarrow> (case y of
                  Inr y' \<Rightarrow> x' <[ y'
                  | _ \<Rightarrow> False))"

instance proof
  fix a :: "'a + 'b"
  show "a <[ a" 
  proof(cases a)
    case (Inl a)
      then show ?thesis by(simp add:sum_pleq leq_refl)
    next
    case (Inr b)
    then show ?thesis by(simp add:sum_pleq leq_refl)
  qed
next
  fix a b c :: "'a + 'b"
  assume H1 : "a <[ b"
  assume H2 : "b <[ c"
    consider (1) a' b' c' where "(a = Inl a' \<and> b = Inl b' \<and> c = Inl c')" |
             (2) a' b' c' where "(a = Inl a' \<and> b = Inl b' \<and> c = Inr c')" |
             (3) a' b' c' where "(a = Inl a' \<and> b = Inr b' \<and> c = Inl c')" |
             (4) a' b' c' where "(a = Inl a' \<and> b = Inr b' \<and> c = Inr c')" |
             (5) a' b' c' where "(a = Inr a' \<and> b = Inl b' \<and> c = Inl c')" |
             (6) a' b' c' where "(a = Inr a' \<and> b = Inl b' \<and> c = Inr c')" |
             (7) a' b' c' where "(a = Inr a' \<and> b = Inr b' \<and> c = Inl c')" |
             (8) a' b' c' where "(a = Inr a' \<and> b = Inr b' \<and> c = Inr c')"
        by (cases a; cases b; cases c; auto)
    then show "a <[ c"
  proof cases
    case 1 thus ?thesis using H1 H2 by(auto simp add:sum_pleq elim: leq_trans) next
    case 2 thus ?thesis using H1 H2 by(auto simp add:sum_pleq elim: leq_trans) next
    case 3 thus ?thesis using H1 H2 by(auto simp add:sum_pleq elim: leq_trans) next
    case 4 thus ?thesis using H1 H2 by(auto simp add:sum_pleq elim: leq_trans) next
    case 5 thus ?thesis using H1 H2 by(auto simp add:sum_pleq elim: leq_trans) next
    case 6 thus ?thesis using H1 H2 by(auto simp add:sum_pleq elim: leq_trans) next
    case 7 thus ?thesis using H1 H2 by(auto simp add:sum_pleq elim: leq_trans) next
    case 8 thus ?thesis using H1 H2 by(auto simp add:sum_pleq elim: leq_trans)
  qed
qed
end

instantiation sum :: (Pord, Pord) Pord
begin

instance proof
  fix a b :: "'a + 'b"
  assume H1 : "a <[ b"
  assume H2 : "b <[ a"
  consider (1) a' b' where "(a = Inl a' \<and> b = Inl b')" |
           (2) a' b' where "(a = Inl a' \<and> b = Inr b')" |
           (3) a' b' where "(a = Inr a' \<and> b = Inl b')" |
           (4) a' b' where "(a = Inr a' \<and> b = Inr b')" 
    by(cases a; cases b; auto)
  then  show "a = b"
  proof cases
    case 1 thus ?thesis using H1 H2 by(auto simp add:sum_pleq elim: leq_antisym) next
    case 2 thus ?thesis using H1 H2 by(auto simp add:sum_pleq elim: leq_antisym) next
    case 3 thus ?thesis using H1 H2 by(auto simp add:sum_pleq elim: leq_antisym) next
    case 4 thus ?thesis using H1 H2 by(auto simp add:sum_pleq elim: leq_antisym) next
  qed
qed
end

instantiation sum :: (Pordc, Pordc) Pordc
begin

instance proof
  fix a b :: "'a + 'b"
  assume "has_ub {a, b}"
  then obtain ub where H : "is_ub {a, b} ub" by (auto simp add:has_ub_def)
  consider (1) a' b' ub' where "(a = Inl a' \<and> b = Inl b' \<and> ub = Inl ub')" |
           (2) a' b' ub' where "(a = Inr a' \<and> b = Inr b' \<and> ub = Inr ub')" using H
    by(cases a; cases b; cases ub; auto simp add:is_ub_def sum_pleq)
  then  show "has_sup {a, b}"
  proof cases
    case 1
    hence Hub' : "has_ub {a', b'}" using H by(auto simp add:has_ub_def is_ub_def sum_pleq)
    obtain s' where Hsup : "is_sup {a', b'} s'" using complete2[OF Hub'] by(auto simp add:has_sup_def)
    hence "is_sup {a, b} (Inl s')" using 1
      by (auto simp add:is_sup_def has_sup_def sum_pleq is_least_def is_ub_def split:sum.splits)
    thus ?thesis by (auto simp add:has_sup_def)
  next
    case 2
    hence Hub' : "has_ub {a', b'}" using H by(auto simp add:has_ub_def is_ub_def sum_pleq)
    obtain s' where Hsup : "is_sup {a', b'} s'" using complete2[OF Hub'] by(auto simp add:has_sup_def)
    hence "is_sup {a, b} (Inr s')" using 2
      by (auto simp add:is_sup_def has_sup_def sum_pleq is_least_def is_ub_def split:sum.splits)
    thus ?thesis by (auto simp add:has_sup_def)
  qed
qed
end

instantiation sum :: (Mergeable, Mergeable) Mergeable
begin
definition sum_bsup :
"bsup (a :: 'a + 'b) (b :: 'a + 'b) =
  (case a of
    Inl a' \<Rightarrow> (case b of
                Inl b' \<Rightarrow> Inl ([^ a', b' ^])
                | Inr b' \<Rightarrow> Inl a')
    | Inr a' \<Rightarrow> (case b of
                Inl b' \<Rightarrow> Inr a'
                | Inr b' \<Rightarrow> Inr ([^ a', b' ^])))"

instance proof 
  fix a b :: "'a + 'b"
  consider (1) a' b' bsup' where "a = Inl a'" "b = Inl b'" "bsup a b = Inl bsup'" |
           (2) a' b' bsup' where "a = Inl a'" "b = Inr b'" "bsup a b = Inl bsup'" |
           (3) a' b' bsup' where "a = Inr a'" "b = Inr b'" "bsup a b = Inr bsup'" |
           (4) a' b' bsup' where "a = Inr a'" "b = Inl b'" "bsup a b = Inr bsup'"
    by(cases a; cases b; cases "bsup a b"; auto simp add:sum_pleq sum_bsup)
  then show "is_bsup a b (bsup a b)"
  proof cases
    case 1
    hence Hbsup' : "is_bsup a' b' (bsup a' b')" by(auto intro: bsup_spec)
    have Hbsup : "bsup a b = Inl (bsup a' b')" using 1 by(auto simp add:sum_bsup)
    show ?thesis
    proof(rule is_bsupI)
      show "a <[ bsup a b" using 1 is_bsupD1[OF Hbsup'] Hbsup 
        by(auto simp add:sum_bsup sum_pleq is_bsup_def)
    next

      fix bd sd :: "'a + 'b"
      assume Hbd : "bd <[ b"
      assume Hsup : "is_sup {a, bd} sd"
      
      obtain sd' where Hsd' : "sd = Inl sd'" using 1 Hsup
        by(auto simp add:sum_pleq is_least_def is_ub_def is_sup_def split:sum.splits)

      obtain bd' where Hbd' : "bd = Inl bd'" using 1 Hbd
        by(auto simp add:sum_pleq split:sum.splits)

      have Hsup' : "is_sup {a', bd'} (sd')" using Hbd' Hsd' Hsup 1
        by(auto simp add:sum_pleq is_sup_def is_least_def is_ub_def split:sum.splits)

      have "sd' <[ bsup a' b'" using is_bsupD2[OF Hbsup' _ Hsup'] Hbd' Hbd 1
        by(auto simp add:sum_pleq)

      thus "sd <[ bsup a b" using Hbsup Hsd'
        by(auto simp add:sum_pleq sum_bsup)
    next

      fix bub :: "'a + 'b"
      assume Hbub : "is_bub a b (bub)"

      obtain bub' where Hbub' : "bub = Inl bub'" using 1 Hbub
        by(auto simp add:sum_pleq is_bub_def is_least_def is_ub_def is_sup_def split:sum.splits)

      have "is_bub a' b' bub'" 
      proof(rule is_bubI)
        show "a' <[ bub'" using 1 is_bubD1[OF Hbub] Hbub'
          by(auto simp add:sum_pleq is_bub_def is_least_def is_ub_def is_sup_def split:sum.splits)
      next
        fix bd' sd' :: "'a"
        assume Hbd : "bd' <[ b'"
        assume Hsup : "is_sup {a', bd'} sd'"

        have Hsup' : "is_sup {a, Inl bd'} (Inl sd')" using 1 Hsup
          by(auto simp add:sum_pleq is_sup_def is_least_def is_ub_def split:sum.splits)

        have Hbd' : "Inl bd' <[ b" using Hbd 1 by(auto simp add:sum_pleq)

        have "Inl sd' <[ Inl bub'" using is_bubD2[OF Hbub Hbd' Hsup'] Hbub' 1  by(auto simp add:sum_pleq)

        thus "sd' <[ bub'" using 1 Hbub' by (auto simp add:sum_pleq)
      qed

      hence "bsup a' b' <[ bub'" using is_bsupD3[OF Hbsup'] by auto

      thus "bsup a b <[ bub" using 1 Hbub Hbub' Hbsup by(auto simp add:sum_pleq)
    qed

  next

    case 2
    have Hbsup : "bsup a b = Inl (a')" using 2 by(auto simp add:sum_bsup)
    show ?thesis
    proof(rule is_bsupI)
      show "a <[ bsup a b" using 2 Hbsup leq_refl[of a]
        by(auto simp add:sum_bsup sum_pleq )
    next
      fix bd sd :: "'a + 'b"
      assume Hbd : "bd <[ b"
      assume Hsup : "is_sup {a, bd} sd"

      obtain bd' where Hbd' : "bd = Inr bd'" using 2 Hbd
        by(auto simp add:sum_pleq split:sum.splits)

      hence False using 2 Hbd Hsup Hbsup
        by(auto simp add:sum_pleq sum_bsup is_sup_def is_least_def is_ub_def split:sum.splits)

      thus "sd <[ [^ a, b ^]" by auto

    next
      
      fix bub :: "'a + 'b"
      assume Hbub : "is_bub a b (bub)"

      show "bsup a b <[ bub" using 2 Hbub
        by(auto simp add:sum_pleq sum_bsup is_bub_def is_sup_def is_least_def is_ub_def split:sum.splits)
    qed

  next

    case 3
    hence Hbsup' : "is_bsup a' b' (bsup a' b')" by(auto intro: bsup_spec)
    have Hbsup : "bsup a b = Inr (bsup a' b')" using 3 by(auto simp add:sum_bsup)
    show ?thesis
    proof(rule is_bsupI)
      show "a <[ bsup a b" using 3 is_bsupD1[OF Hbsup'] Hbsup 
        by(auto simp add:sum_bsup sum_pleq is_bsup_def)
    next

      fix bd sd :: "'a + 'b"
      assume Hbd : "bd <[ b"
      assume Hsup : "is_sup {a, bd} sd"
      
      obtain sd' where Hsd' : "sd = Inr sd'" using 3 Hsup
        by(auto simp add:sum_pleq is_least_def is_ub_def is_sup_def split:sum.splits)

      obtain bd' where Hbd' : "bd = Inr bd'" using 3 Hbd
        by(auto simp add:sum_pleq split:sum.splits)

      have Hsup' : "is_sup {a', bd'} (sd')" using Hbd' Hsd' Hsup 3
        by(auto simp add:sum_pleq is_sup_def is_least_def is_ub_def split:sum.splits)

      have "sd' <[ bsup a' b'" using is_bsupD2[OF Hbsup' _ Hsup'] Hbd' Hbd 3
        by(auto simp add:sum_pleq)

      thus "sd <[ bsup a b" using Hbsup Hsd'
        by(auto simp add:sum_pleq sum_bsup)
    next

      fix bub :: "'a + 'b"
      assume Hbub : "is_bub a b (bub)"

      obtain bub' where Hbub' : "bub = Inr bub'" using 3 Hbub
        by(auto simp add:sum_pleq is_bub_def is_least_def is_ub_def is_sup_def split:sum.splits)

      have "is_bub a' b' bub'" 
      proof(rule is_bubI)
        show "a' <[ bub'" using 3 is_bubD1[OF Hbub] Hbub'
          by(auto simp add:sum_pleq is_bub_def is_least_def is_ub_def is_sup_def split:sum.splits)
      next
        fix bd' sd' :: "'b"
        assume Hbd : "bd' <[ b'"
        assume Hsup : "is_sup {a', bd'} sd'"

        have Hsup' : "is_sup {a, Inr bd'} (Inr sd')" using 3 Hsup
          by(auto simp add:sum_pleq is_sup_def is_least_def is_ub_def split:sum.splits)

        have Hbd' : "Inr bd' <[ b" using Hbd 3 by(auto simp add:sum_pleq)

        have "Inr sd' <[ Inr bub'" using is_bubD2[OF Hbub Hbd' Hsup'] Hbub' 3  by(auto simp add:sum_pleq)

        thus "sd' <[ bub'" using 3 Hbub' by (auto simp add:sum_pleq)
      qed

      hence "bsup a' b' <[ bub'" using is_bsupD3[OF Hbsup'] by auto

      thus "bsup a b <[ bub" using 3 Hbub Hbub' Hbsup by(auto simp add:sum_pleq)
    qed

  next

    case 4
    have Hbsup : "bsup a b = Inr (a')" using 4 by(auto simp add:sum_bsup)
    show ?thesis
    proof(rule is_bsupI)
      show "a <[ bsup a b" using 4 Hbsup leq_refl[of a]
        by(auto simp add:sum_bsup sum_pleq )
    next
      fix bd sd :: "'a + 'b"
      assume Hbd : "bd <[ b"
      assume Hsup : "is_sup {a, bd} sd"

      obtain bd' where Hbd' : "bd = Inl bd'" using 4 Hbd
        by(auto simp add:sum_pleq split:sum.splits)

      hence False using 4 Hbd Hsup Hbsup
        by(auto simp add:sum_pleq sum_bsup is_sup_def is_least_def is_ub_def split:sum.splits)

      thus "sd <[ [^ a, b ^]" by auto

    next
      
      fix bub :: "'a + 'b"
      assume Hbub : "is_bub a b (bub)"

      show "bsup a b <[ bub" using 4 Hbub
        by(auto simp add:sum_pleq sum_bsup is_bub_def is_sup_def is_least_def is_ub_def split:sum.splits)
    qed
  qed
qed
end

(*
 * Finally we derive Mergeable for the unit type. This is useful in the
 * implementation of Mergeable for RAList (see Mergeable_RAList.thy), as well as
 * (presumably) some other applications.
 *)

instantiation unit :: Pord_Weak begin
definition unit_pleq : 
"(a :: unit) <[ b = True"

instance proof 
  show "\<And>a::unit. a <[ a" by (auto simp add: unit_pleq)
next
  show "\<And>(a::unit) (b::unit) c::unit. a <[ b \<Longrightarrow> b <[ c \<Longrightarrow> a <[ c"
    by(auto simp add: unit_pleq)
qed
end

instantiation unit :: Pord begin
instance proof
  show " \<And>(a::unit) b::unit. a <[ b \<Longrightarrow> b <[ a \<Longrightarrow> a = b"
    by(auto simp add: unit_pleq)
qed
end

instantiation unit :: Pordc begin
instance proof
  show "\<And>(a::unit) b::unit. has_ub {a, b} \<Longrightarrow> has_sup {a, b}"
    by(auto simp add: unit_pleq has_ub_def has_sup_def is_ub_def is_sup_def is_least_def)
qed
end

instantiation unit :: Pord_Weakb begin
definition unit_bot :
"(\<bottom> :: unit) = ()"
instance proof
  show "\<And>a::unit. \<bottom> <[ a"
    by(auto simp add: unit_pleq unit_bot)
qed
end


instantiation unit :: Pordb begin
instance proof
qed
end

instantiation unit :: Mergeable begin
definition unit_bsup :
"[^ (a :: unit), (b :: unit) ^] = ()"

instance proof
  show "\<And>(a::unit) b::unit. is_bsup a b [^ a, b ^]"
    by(auto simp add:
          unit_pleq is_bsup_def is_least_def is_ub_def is_bub_def)
qed
end

instantiation unit :: Mergeableb begin
instance proof qed
end

definition hmm :: "('a :: Pordbc \<Rightarrow> bool)" where
"hmm x = True"

end