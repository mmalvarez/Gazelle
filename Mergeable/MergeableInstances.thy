theory MergeableInstances imports Mergeable HOL.Lifting
begin

(* goal: make these proofs more manageable by generalizing
*)

(* define some partial orders:
   trivial: leq means a = b
   option : None < Some
   pairs: (a, b) < (c, d) means (a < c \<and>b < d)
   lexicographical
      (a, b) < (c, d) means (a < c) and (c < a \<longrightarrow> b < d)
 *)

(* define some Mergeables:
  trivial (bsup takes first one)
  option (see test0)
  pairs (see test?)
  lexicographical (do this one later) 
*)

datatype 'a md_triv =
  mdt 'a

definition mdt_get :: "'a md_triv \<Rightarrow> 'a" where
"mdt_get x = (case x of (mdt x') \<Rightarrow> x')"

definition mdt_put :: "'a \<Rightarrow> 'a md_triv" where
"mdt_put x = mdt x"

declare mdt_get_def mdt_put_def [simp]

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

instantiation option :: (Pord_Weak) Pord_Weak
begin
definition option_pleq : "(x :: 'a option) <[ y =
(case x of
      None \<Rightarrow> True
      | Some x' \<Rightarrow>
        (case y of
          None \<Rightarrow> False
          | Some y' \<Rightarrow> (pleq x' y')))"
(*
instantiation option :: (Pordc) Pordb
begin

*)
(*definition option_bot : "bot = (None :: 'a option)"*)

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

(* definition option_bot : "bot = (None :: 'a option)" *)
instantiation option :: (Pordc) Pordb
begin
definition option_bot : "bot = (None :: 'a option)"

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
        proof(rule is_sup_intro)
          fix xa
          assume Hxa : "xa \<in> {a, b}"
          obtain xa' where Hxa' : "xa = Some xa' \<and> (xa' = a' \<or> xa' = aa)" using Hi1 Hi2 Hxa
            by(auto simp add:
                option_pleq is_ub_def is_least_def has_ub_def split:option.splits elim:is_sup_unfold1 is_sup_unfold2)
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
next
  fix a :: "'a option"
  show "\<bottom> <[ a"
    by(auto simp add:option_pleq option_bot)
qed
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
      proof(rule is_bsup_intro)
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
        show "pleq (bsup a b) x'" using is_bub_unfold2[OF H]
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
      proof(rule is_bsup_intro)
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
          show "pleq (bsup a b) x'" using is_bub_unfold2[OF H]
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
        proof(rule is_bsup_intro)
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
            proof(rule is_sup_intro)
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
            
            show "pleq sd (bsup a b)" using is_bsup_unfold2[OF OBsup Hbbd' OSup] Hsd' Hi1 Hi2 Hiii1
              by(auto simp add:option_pleq option_bsup)
          qed

        next
          fix x
          assume H: "is_bub a b x"

          obtain x' where Hx' : "x = Some x'" using Hi1 Hi2 H 
            by(auto simp add:is_bub_def option_pleq split:option.splits)

          have Bub' : "is_bub a' b' x'" 
          proof(rule is_bub_intro)
            show "pleq a' x'" using Hi1 Hx' is_bub_unfold1[OF H]
              by(auto simp add:option_pleq)

          next

            fix bd' sd'
            assume Hpleq' : "pleq bd' b'"
            assume HOsup : "is_sup {a', bd'} sd'"

            have Hpleq : "pleq (Some bd') (b)" using Hi2 Hpleq' by (auto simp add:option_pleq)

            have HSup : "is_sup {a, Some bd'} (Some sd')"
              using Hi1 HOsup 
              by(auto simp add:option_pleq is_sup_def is_least_def is_ub_def split:option.splits)

            show "pleq sd' x'" using Hi1 Hx' is_bub_unfold2[OF H Hpleq HSup]
              by(auto simp add:option_pleq is_sup_def)
          qed


          show "pleq (bsup a b) x" using Hx' Hi1 Hi2 Bub' bsup_spec[of a' b']
            by(auto simp add:option_pleq option_bsup is_bsup_def is_least_def)
        qed
      qed
    qed
  qed
end

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

instantiation prod :: (Pordb, Pordb) Pordb
begin
definition prod_bot : 
  "(bot :: 'a * 'b) = (bot, bot)"
instance proof
  fix a :: "'a * 'b"
  show "pleq bot a"
    by(cases a; auto simp add:prod_pleq prod_bot bot_spec)
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
  proof(rule is_bsup_intro)

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

    have Conc1 : "pleq sd1 (bsup a1 b1)" using is_bsup_unfold2[OF Bsup1 Leq1 Sup1] Hbsv1
      by(auto simp add:is_bsup_def is_least_def is_bub_def)
      
    have Conc2 : "pleq sd2 (bsup a2 b2)" using is_bsup_unfold2[OF Bsup2 Leq2 Sup2] Hbsv2
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
      proof(rule is_bub_intro)
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

        show "pleq sd1 x1" using is_bub_unfold2[OF Hbub Hpleq' Hsup'] Hx
          by(simp add:prod_pleq)
      qed
  
      have Hbub2 : "is_bub a2 b2 x2" 
      proof(rule is_bub_intro)
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

        show "pleq sd2 x2" using is_bub_unfold2[OF Hbub Hpleq' Hsup'] Hx
          by(simp add:prod_pleq)
      qed

      show "pleq (bsup a b) x" using Hx Ha Hb Hbub1 Hbub2 bsup_spec[of a1 b1] bsup_spec[of a2 b2]
        by(auto simp add:is_bsup_def is_least_def prod_pleq prod_bsup)
    qed
  qed
end

datatype 'a md_prio =
  mdp nat 'a

definition mdp_get :: "'a md_prio \<Rightarrow> (nat * 'a)" where
"mdp_get x = (case x of (mdp n y) \<Rightarrow> (n, y))"

definition mdp_get_pri :: "'a md_prio \<Rightarrow> nat" where
"mdp_get_pri x = (case x of (mdp n _) \<Rightarrow> n)"

definition mdp_get_data :: "'a md_prio \<Rightarrow> 'a" where
"mdp_get_data x = (case x of (mdp _ y) \<Rightarrow> y)"

definition mdp_put :: "nat \<Rightarrow> 'a \<Rightarrow> 'a md_prio" where
"mdp_put = mdp"

declare mdp_get_def mdp_get_pri_def mdp_get_data_def mdp_put_def [simp]

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

instantiation md_prio :: (Pordb) Pordb
begin
definition prio_bot :
"\<bottom> = mdp 0 bot"
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
        proof(rule is_sup_intro)
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

next

  fix a :: "'a md_prio"
  show "pleq bot a" using bot_spec
    by(auto simp add: prio_pleq prio_bot split:md_prio.splits)
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
  proof(rule is_bsup_intro)

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

            thus ?thesis using is_sup_unfold2[OF H2] by auto
          next

            assume False''' : "\<not> pleq b' (bsup a' b')"

            have "bsup a b = mdp (1 + ai) bot" using Ha Hb Haibi True True' False''' by(auto simp add:prio_bsup)
            hence "is_ub {a, bd} (bsup a b)" using Ha Hb Haibi Hbdibi Hbd by(auto simp add:prio_pleq is_ub_def)
            hence "is_ub {a, bd} (bsup a b)" using leq_trans[of bd b "bsup a b"] H1
              by(auto simp add:is_ub_def)

            thus ?thesis using is_sup_unfold2[OF H2] by auto
          qed
        qed

      next
        assume False' : "\<not> bi \<le> ai"
        hence Hbsupb : "bsup a b = b" using Ha Hb
        by(auto simp add:prio_pleq prio_bsup is_sup_def is_least_def is_ub_def split:if_split_asm)

      have Hub : "is_ub {a, bd} b" using Ha Hb False' leq_refl H1
        by(auto simp add: prio_pleq prio_bsup is_sup_def is_least_def is_ub_def split:if_split_asm)

      show ?thesis using Hbsupb is_sup_unfold2[OF H2 Hub]
        by auto
      qed

    next
      case False
      hence Hbsupa : "bsup a b = a" using Ha Hb
        by(auto simp add: prio_pleq prio_bsup is_sup_def is_least_def is_ub_def split:if_split_asm)

      have Hub : "is_ub {a, bd} a" using Ha Hb False leq_refl H1
        by(auto simp add:prio_pleq prio_bsup is_sup_def is_least_def is_ub_def split:if_split_asm md_prio.splits)

      show ?thesis using Hbsupa is_sup_unfold2[OF H2 Hub]
        by auto
    qed
  next

    fix x :: "'a md_prio"
    obtain xi and x' where Hx : "x = mdp xi x'" by (cases x; auto)

    assume H : "is_bub a b x"
    have Hax : "pleq a x" using is_bub_unfold1[OF H] by auto

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

              thus ?thesis using is_bub_unfold2[OF H leq_refl[of b]] by auto
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

              thus ?thesis using is_bub_unfold2[OF H leq_refl[of b]] 1 by auto
            next

              assume False'''' : "\<not> xi \<le> bi"

              thus ?thesis using 0 Ha Hb Hx Haibi bot_spec
                by(auto simp add:prio_pleq)
            qed
          next

            assume False''' : "\<not> bi \<le> xi"

            thus ?thesis using is_bub_unfold2[OF H leq_refl[of b]] 1 by auto
          qed
        qed
      next
        assume False' : "\<not> bi \<le> ai"

        have "is_sup {a, b} (bsup a b)"  using True False' Ha Hb Hx leq_refl
          by(auto simp add:prio_pleq prio_bsup is_sup_def is_least_def is_ub_def)
        thus ?thesis using is_bub_unfold2[OF H leq_refl[of b]] by auto
      qed
    next
      assume False : "\<not> ai \<le> bi"
        have "is_sup {a, b} (bsup a b)"  using False Ha Hb Hx leq_refl
          by(auto simp add:prio_pleq prio_bsup is_sup_def is_least_def is_ub_def)
        thus ?thesis using is_bub_unfold2[OF H leq_refl[of b]] by auto
    qed
  qed
qed
end

datatype 'a md_wrap =
  mdw 'a

definition md_wrap_get :: "'a md_wrap \<Rightarrow> 'a" where
"md_wrap_get x = (case x of (mdw x') \<Rightarrow> x')"

declare md_wrap_get_def [simp]
(*
instantiation md_wrap :: (Pord_Weak) Pord_Weak begin
definition wrap_pleq :
  "pleq x y = pleq (md_wrap_get x) (md_wrap_get y)"


instance proof
  fix a :: "'a md_wrap"
  show "a <[ a"
    by(auto simp add: wrap_pleq leq_refl split:md_wrap.splits)
next
  fix a b c :: "'a md_wrap"
  show "a <[ b \<Longrightarrow> b <[ c \<Longrightarrow> a <[ c"
    by(auto simp add: wrap_pleq elim: leq_trans split:md_wrap.splits)
qed
end

instantiation md_wrap :: (Pord) Pord begin
instance proof
  fix a b :: "'a md_wrap"
  show "a <[ b \<Longrightarrow> b <[ a \<Longrightarrow> a = b"
    by(auto simp add:wrap_pleq elim: leq_antisym split:md_wrap.splits)
qed
end

instantiation md_wrap :: (Pordc) Pordc begin
instance proof
  fix a b :: "'a md_wrap"
  assume H : "has_ub {a, b}" 

  show "has_sup {a, b}" using H
        apply(auto simp add:wrap_pleq has_ub_def has_sup_def is_ub_def is_sup_def is_least_def ) 


  obtain a' where Ha : "a = mdw a'" by(cases a; auto)
  obtain b' where Hb : "b = mdw b'" by(cases b; auto)
  obtain ub where Hub : "is_ub {a, b} ub" using H
    by(auto simp add:has_ub_def)
  obtain ub' where Hub' : "ub = mdw ub'" by(cases ub; auto)

  have "is_ub {a', b'} ub'" using Ha Hb Hub Hub'
    by(auto simp add:has_ub_def is_ub_def wrap_pleq split:md_wrap.splits)

  hence "has_sup {a', b'}" using complete2
    by(auto simp add:has_ub_def)

  then obtain sup' where Hsup' : "is_sup {a', b'} sup'" by(auto simp add:has_sup_def)

  hence "is_sup {a, b} (mdw sup')" using is_sup_unfold1[OF Hsup']
    apply(auto simp add:wrap_pleq has_ub_def has_sup_def is_ub_def is_sup_def is_least_def split:md_wrap.splits) 
qed
end
*)

(* formulation of sum that doesn't allow for a least element *)
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
declare [[show_types]]
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
    proof(rule is_bsup_intro)
      show "a <[ bsup a b" using 1 is_bsup_unfold1[OF Hbsup'] Hbsup 
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

      have "sd' <[ bsup a' b'" using is_bsup_unfold2[OF Hbsup' _ Hsup'] Hbd' Hbd 1
        by(auto simp add:sum_pleq)

      thus "sd <[ bsup a b" using Hbsup Hsd'
        by(auto simp add:sum_pleq sum_bsup)
    next

      fix bub :: "'a + 'b"
      assume Hbub : "is_bub a b (bub)"

      obtain bub' where Hbub' : "bub = Inl bub'" using 1 Hbub
        by(auto simp add:sum_pleq is_bub_def is_least_def is_ub_def is_sup_def split:sum.splits)

      have "is_bub a' b' bub'" 
      proof(rule is_bub_intro)
        show "a' <[ bub'" using 1 is_bub_unfold1[OF Hbub] Hbub'
          by(auto simp add:sum_pleq is_bub_def is_least_def is_ub_def is_sup_def split:sum.splits)
      next
        fix bd' sd' :: "'a"
        assume Hbd : "bd' <[ b'"
        assume Hsup : "is_sup {a', bd'} sd'"

        have Hsup' : "is_sup {a, Inl bd'} (Inl sd')" using 1 Hsup
          by(auto simp add:sum_pleq is_sup_def is_least_def is_ub_def split:sum.splits)

        have Hbd' : "Inl bd' <[ b" using Hbd 1 by(auto simp add:sum_pleq)

        have "Inl sd' <[ Inl bub'" using is_bub_unfold2[OF Hbub Hbd' Hsup'] Hbub' 1  by(auto simp add:sum_pleq)

        thus "sd' <[ bub'" using 1 Hbub' by (auto simp add:sum_pleq)
      qed

      hence "bsup a' b' <[ bub'" using is_bsup_unfold3[OF Hbsup'] by auto

      thus "bsup a b <[ bub" using 1 Hbub Hbub' Hbsup by(auto simp add:sum_pleq)
    qed

  next

    case 2
    have Hbsup : "bsup a b = Inl (a')" using 2 by(auto simp add:sum_bsup)
    show ?thesis
    proof(rule is_bsup_intro)
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
    proof(rule is_bsup_intro)
      show "a <[ bsup a b" using 3 is_bsup_unfold1[OF Hbsup'] Hbsup 
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

      have "sd' <[ bsup a' b'" using is_bsup_unfold2[OF Hbsup' _ Hsup'] Hbd' Hbd 3
        by(auto simp add:sum_pleq)

      thus "sd <[ bsup a b" using Hbsup Hsd'
        by(auto simp add:sum_pleq sum_bsup)
    next

      fix bub :: "'a + 'b"
      assume Hbub : "is_bub a b (bub)"

      obtain bub' where Hbub' : "bub = Inr bub'" using 3 Hbub
        by(auto simp add:sum_pleq is_bub_def is_least_def is_ub_def is_sup_def split:sum.splits)

      have "is_bub a' b' bub'" 
      proof(rule is_bub_intro)
        show "a' <[ bub'" using 3 is_bub_unfold1[OF Hbub] Hbub'
          by(auto simp add:sum_pleq is_bub_def is_least_def is_ub_def is_sup_def split:sum.splits)
      next
        fix bd' sd' :: "'b"
        assume Hbd : "bd' <[ b'"
        assume Hsup : "is_sup {a', bd'} sd'"

        have Hsup' : "is_sup {a, Inr bd'} (Inr sd')" using 3 Hsup
          by(auto simp add:sum_pleq is_sup_def is_least_def is_ub_def split:sum.splits)

        have Hbd' : "Inr bd' <[ b" using Hbd 3 by(auto simp add:sum_pleq)

        have "Inr sd' <[ Inr bub'" using is_bub_unfold2[OF Hbub Hbd' Hsup'] Hbub' 3  by(auto simp add:sum_pleq)

        thus "sd' <[ bub'" using 3 Hbub' by (auto simp add:sum_pleq)
      qed

      hence "bsup a' b' <[ bub'" using is_bsup_unfold3[OF Hbsup'] by auto

      thus "bsup a b <[ bub" using 3 Hbub Hbub' Hbsup by(auto simp add:sum_pleq)
    qed

  next

    case 4
    have Hbsup : "bsup a b = Inr (a')" using 4 by(auto simp add:sum_bsup)
    show ?thesis
    proof(rule is_bsup_intro)
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
  unit instances 
  useful for RAlist
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

instantiation unit :: Pordb begin
definition unit_bot :
"(\<bottom> :: unit) = ()"
instance proof
  show "\<And>a::unit. \<bottom> <[ a"
    by(auto simp add: unit_pleq unit_bot)
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

(* Formulation of sum allowing for a least element
i think it would be better to just wrap it in option, though *)
(*
instantiation sum :: (Pordb, Pord_Weak) Pord_Weak
begin
definition sum_pleq : "(x :: 'a + 'b) <[ y =
(case x of
      Inl x' \<Rightarrow> (case y of
                  Inl y' \<Rightarrow> x' <[ y'
                  | _ \<Rightarrow> x' <[ \<bottom>)
      | Inr x' \<Rightarrow> (case y of
                  Inr y' \<Rightarrow> x' <[ y'
                  | _ \<Rightarrow> False))"
declare [[show_types]]
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

instantiation sum :: (Pordb, Pord) Pord
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

instantiation sum :: (Pordb, Pordc) Pordc
begin

instance proof
  fix a b :: "'a + 'b"
  assume "has_ub {a, b}"
  then obtain ub where H : "is_ub {a, b} ub" by (auto simp add:has_ub_def)
  consider (1) a' b' ub' where "(a = Inl a' \<and> b = Inl b' \<and> ub = Inl ub')" |
           (2) a' b' ub' where "(a = Inr a' \<and> b = Inr b' \<and> ub = Inr ub')" |
           (3) a' b' ub' where "(a = Inl a' \<and> b = Inr b' \<and> ub = Inr ub')" |
           (4) a' b' ub' where "(a = Inr a' \<and> b = Inl b' \<and> ub = Inr ub')" |
           (5) a' b' ub' where "(a = Inl a' \<and> b = Inl b' \<and> ub = Inr ub')"using H
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
  next
    case 3
    hence Habot : "a' <[ \<bottom>" using H by(auto simp add:has_ub_def is_ub_def sum_pleq)
    hence "a' = \<bottom>" using H leq_antisym[OF Habot bot_spec] by(auto simp add:has_ub_def is_ub_def sum_pleq)
    hence "is_sup {a, b} (Inr b')" using 3
      by(auto simp add:is_sup_def has_sup_def sum_pleq is_least_def is_ub_def leq_refl split:sum.splits)
    thus ?thesis by (auto simp add:has_sup_def)
  next
    case 4
    hence Hbbot : "b' <[ \<bottom>" using H by(auto simp add:has_ub_def is_ub_def sum_pleq)
    hence "b' = \<bottom>" using H leq_antisym[OF Hbbot bot_spec] by(auto simp add:has_ub_def is_ub_def sum_pleq)
    hence "is_sup {a, b} (Inr a')" using 4
      by(auto simp add:is_sup_def has_sup_def sum_pleq is_least_def is_ub_def leq_refl split:sum.splits)
    thus ?thesis by (auto simp add:has_sup_def)

  next
    case 5
    have Habot : "a' <[ \<bottom>" using H 5 by(auto simp add:has_ub_def is_ub_def sum_pleq)
    have Hbbot : "b' <[ \<bottom>" using H 5 by(auto simp add:has_ub_def is_ub_def sum_pleq)
    have "is_sup {a, b} (Inl \<bottom>)" using 5  Habot Hbbot bot_spec
      by(auto simp add:is_sup_def has_sup_def sum_pleq is_least_def is_ub_def leq_refl split:sum.splits)
    thus ?thesis by (auto simp add:has_sup_def)
  qed
qed
end

instantiation sum :: (Mergeableb, Mergeable) Mergeable
begin
definition sum_bsup :
"bsup (a :: 'a + 'b) (b :: 'a + 'b) =
  (case a of
    Inl a' \<Rightarrow> (case b of
                Inl b' \<Rightarrow> Inl ([^ a', b' ^])
                | Inr b' \<Rightarrow> (if a' <[ \<bottom> then Inr b' else Inl a'))
    | Inr a' \<Rightarrow> (case b of
                Inl b' \<Rightarrow> Inr a'
                | Inr b' \<Rightarrow> Inr ([^ a', b' ^])))"

instance proof 
  fix a b :: "'a + 'b"
  consider (1) a' b' bsup' where "a = Inl a'" "b = Inl b'" "bsup a b = Inl bsup'" |
           (2) a' b' bsup' where "a = Inl a'" "b = Inr b'" "bsup a b = Inl bsup'" |
           (3) a' b' bsup' where "a = Inr a'" "b = Inr b'" "bsup a b = Inr bsup'" |
           (4) a' b' bsup' where "a = Inr a'" "b = Inl b'" "bsup a b = Inr bsup'" |
           (5) a' b' bsup' where "a = Inl a'" "b = Inr b'" "bsup a b = Inr bsup'" 
    by(cases a; cases b; cases "bsup a b"; auto simp add:sum_pleq sum_bsup)
  then show "is_bsup a b (bsup a b)"
  proof cases
    case 1
    hence Hbsup' : "is_bsup a' b' (bsup a' b')" by(auto intro: bsup_spec)
    have Hbsup : "bsup a b = Inl (bsup a' b')" using 1 by(auto simp add:sum_bsup)
    show ?thesis
    proof(rule is_bsup_intro)
      show "a <[ bsup a b" using 1 is_bsup_unfold1[OF Hbsup'] Hbsup 
        by(auto simp add:sum_bsup sum_pleq is_bsup_def)
    next

      fix bd sd :: "'a + 'b"
      assume Hbd : "bd <[ b"
      assume Hsup : "is_sup {a, bd} sd"
      
      obtain sd' where Hsd' : "sd = Inl sd'" using 1 Hsup
        apply(auto simp add:sum_pleq is_least_def is_ub_def is_sup_def split:sum.splits)

      obtain bd' where Hbd' : "bd = Inl bd'" using 1 Hbd
        by(auto simp add:sum_pleq split:sum.splits)

      have Hsup' : "is_sup {a', bd'} (sd')" using Hbd' Hsd' Hsup 1
        by(auto simp add:sum_pleq is_sup_def is_least_def is_ub_def split:sum.splits)

      have "sd' <[ bsup a' b'" using is_bsup_unfold2[OF Hbsup' _ Hsup'] Hbd' Hbd 1
        by(auto simp add:sum_pleq)

      thus "sd <[ bsup a b" using Hbsup Hsd'
        by(auto simp add:sum_pleq sum_bsup)
    next

      fix bub :: "'a + 'b"
      assume Hbub : "is_bub a b (bub)"

      obtain bub' where Hbub' : "bub = Inl bub'" using 1 Hbub
        by(auto simp add:sum_pleq is_bub_def is_least_def is_ub_def is_sup_def split:sum.splits)

      have "is_bub a' b' bub'" 
      proof(rule is_bub_intro)
        show "a' <[ bub'" using 1 is_bub_unfold1[OF Hbub] Hbub'
          by(auto simp add:sum_pleq is_bub_def is_least_def is_ub_def is_sup_def split:sum.splits)
      next
        fix bd' sd' :: "'a"
        assume Hbd : "bd' <[ b'"
        assume Hsup : "is_sup {a', bd'} sd'"

        have Hsup' : "is_sup {a, Inl bd'} (Inl sd')" using 1 Hsup
          by(auto simp add:sum_pleq is_sup_def is_least_def is_ub_def split:sum.splits)

        have Hbd' : "Inl bd' <[ b" using Hbd 1 by(auto simp add:sum_pleq)

        have "Inl sd' <[ Inl bub'" using is_bub_unfold2[OF Hbub Hbd' Hsup'] Hbub' 1  by(auto simp add:sum_pleq)

        thus "sd' <[ bub'" using 1 Hbub' by (auto simp add:sum_pleq)
      qed

      hence "bsup a' b' <[ bub'" using is_bsup_unfold3[OF Hbsup'] by auto

      thus "bsup a b <[ bub" using 1 Hbub Hbub' Hbsup by(auto simp add:sum_pleq)
    qed

  next

    case 2
    have Hbsup : "bsup a b = Inl (a')" using 2 by(auto simp add:sum_bsup)
    show ?thesis
    proof(rule is_bsup_intro)
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
    proof(rule is_bsup_intro)
      show "a <[ bsup a b" using 3 is_bsup_unfold1[OF Hbsup'] Hbsup 
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

      have "sd' <[ bsup a' b'" using is_bsup_unfold2[OF Hbsup' _ Hsup'] Hbd' Hbd 3
        by(auto simp add:sum_pleq)

      thus "sd <[ bsup a b" using Hbsup Hsd'
        by(auto simp add:sum_pleq sum_bsup)
    next

      fix bub :: "'a + 'b"
      assume Hbub : "is_bub a b (bub)"

      obtain bub' where Hbub' : "bub = Inr bub'" using 3 Hbub
        by(auto simp add:sum_pleq is_bub_def is_least_def is_ub_def is_sup_def split:sum.splits)

      have "is_bub a' b' bub'" 
      proof(rule is_bub_intro)
        show "a' <[ bub'" using 3 is_bub_unfold1[OF Hbub] Hbub'
          by(auto simp add:sum_pleq is_bub_def is_least_def is_ub_def is_sup_def split:sum.splits)
      next
        fix bd' sd' :: "'b"
        assume Hbd : "bd' <[ b'"
        assume Hsup : "is_sup {a', bd'} sd'"

        have Hsup' : "is_sup {a, Inr bd'} (Inr sd')" using 3 Hsup
          by(auto simp add:sum_pleq is_sup_def is_least_def is_ub_def split:sum.splits)

        have Hbd' : "Inr bd' <[ b" using Hbd 3 by(auto simp add:sum_pleq)

        have "Inr sd' <[ Inr bub'" using is_bub_unfold2[OF Hbub Hbd' Hsup'] Hbub' 3  by(auto simp add:sum_pleq)

        thus "sd' <[ bub'" using 3 Hbub' by (auto simp add:sum_pleq)
      qed

      hence "bsup a' b' <[ bub'" using is_bsup_unfold3[OF Hbsup'] by auto

      thus "bsup a b <[ bub" using 3 Hbub Hbub' Hbsup by(auto simp add:sum_pleq)
    qed

  next

    case 4
    have Hbsup : "bsup a b = Inr (a')" using 4 by(auto simp add:sum_bsup)
    show ?thesis
    proof(rule is_bsup_intro)
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
*)



(* TODO: need an instance for fun? *)
end