theory MergeableInstances imports Mergeable Tord
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

locale Pord_Trivial =
  fixes t :: "'a itself"
begin
definition pleq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
"pleq a b = (a = b)"

end

locale Pordc_Trivial_Spec = Pord_Trivial

sublocale Pordc_Trivial_Spec \<subseteq> Pordc_Spec "pleq"
proof(unfold_locales)
  show "pleq a a" for a by (simp add:pleq_def)

  show "\<And>a b c. pleq a b \<Longrightarrow> pleq b c \<Longrightarrow> pleq a c"
    by (simp add:pleq_def)

  show "\<And>a b. pleq a b \<Longrightarrow> pleq b a \<Longrightarrow> a = b"
    by (simp add:pleq_def)

  show "\<And>a b. Pord.has_ub pleq {a, b} \<Longrightarrow> Pord.has_sup pleq {a, b}"
by(auto simp add:
pleq_def
Pord.has_ub_def Pord.is_ub_def
Pord.has_sup_def Pord.is_sup_def Pord.is_least_def All_def)
qed

locale Mg_Trivial = Pord_Trivial
begin
definition bsup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"bsup a b = a"

end

locale Mg_Trivial_Spec =
  Mg_Trivial + Pordc_Trivial_Spec

sublocale Mg_Trivial_Spec \<subseteq> Mergeable_Spec pleq bsup
proof(auto simp only:Mergeable_Spec_def)
  show "Pordc_Spec pleq" by (rule local.Pordc_Spec_axioms)

  show "Mergeable_Spec_axioms pleq bsup"
  proof(unfold_locales)
    show "\<And> (a :: 'a) b. is_bsup a b (bsup a b)"
      by( simp only:
           pleq_def bsup_def is_bsup_def is_least_def is_bub_def is_sup_def is_ub_def;
           fast)
   qed
qed

locale Pbord_Option' =
  fixes pleq' :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin
definition pleq :: "'a option \<Rightarrow> 'a option \<Rightarrow> bool" where
"pleq x y =
  (case x of
      None \<Rightarrow> True
      | Some x' \<Rightarrow>
        (case y of
          None \<Rightarrow> False
          | Some y' \<Rightarrow> (pleq' x' y')))"

definition bot :: "'a option" where
"bot = None"
end

locale Pbord_Option = Pbord_Option' +
  O : Pord pleq' 

sublocale Pbord_Option \<subseteq> Pbord "pleq" "bot"
  done

locale Pbordc_Option_Spec = Pbord_Option +
  OS : Pordc_Spec pleq'

sublocale Pbordc_Option_Spec \<subseteq> Pordc_Spec "pleq"
proof(unfold_locales)
  show "\<And> a . pleq a a"
  proof(-)
    fix a
    show "pleq a a"
      by(cases a; auto simp add:pleq_def OS.leq_refl)
  qed

  show "\<And>a b c. pleq a b \<Longrightarrow> pleq b c \<Longrightarrow> pleq a c"
  proof(-)
    fix a b c
    assume H1 : "pleq a b"
    assume H2 : "pleq b c"
    show "pleq a c" using OS.leq_trans H1 H2
      by(auto simp add:pleq_def split:option.splits)
  qed

  show "\<And>a b. pleq a b \<Longrightarrow> pleq b a \<Longrightarrow> a = b"
  proof(-)
    fix a b
    assume H1 : "pleq a b"
    assume H2 : "pleq b a"
    show "a = b" using H1 H2 OS.leq_antisym
      by(auto simp add:pleq_def split:option.splits)
  qed

  show "\<And>a b. Pord.has_ub pleq {a, b} \<Longrightarrow> Pord.has_sup pleq {a, b}"
  proof(-)
    fix a b
    assume H : "Pord.has_ub pleq {a, b}"
    show "Pord.has_sup pleq {a, b}" 
    proof(cases a)
      case None
      then show ?thesis
      proof(cases b) 
        show "a = None \<Longrightarrow> b = None \<Longrightarrow> Pord.has_sup pleq {a, b}"      
          by(auto simp add:
                pleq_def
                Pord.has_ub_def  Pord.is_ub_def
                Pord.has_sup_def Pord.is_sup_def Pord.is_least_def All_def split:option.splits)
        show " \<And>aa::'a. a = None \<Longrightarrow> b = Some aa \<Longrightarrow> Pord.has_sup pleq {a, b}" using H OS.leq_refl
          by(auto simp add:
                pleq_def
                Pord.has_ub_def  Pord.is_ub_def
                Pord.has_sup_def Pord.is_sup_def Pord.is_least_def All_def split:option.splits) 
        qed
      next
      case (Some a')
      then show ?thesis
      proof(cases b)
        show "a = Some a' \<Longrightarrow> b = None \<Longrightarrow> Pord.has_sup pleq {a, b}" using H OS.leq_refl
        by(auto simp add:
                pleq_def
                Pord.has_ub_def  Pord.is_ub_def
                Pord.has_sup_def Pord.is_sup_def Pord.is_least_def All_def split:option.splits) 

        show "\<And>aa::'a. a = Some a' \<Longrightarrow> b = Some aa \<Longrightarrow> Pord.has_sup pleq {a, b}"
          proof(-)
          fix aa
          assume Hi1 : "a = Some a'"
          assume Hi2 : "b = Some aa"
          
          have OUb : "O.has_ub {a', aa}"  using H Hi1 Hi2
            by(auto simp add:pleq_def Pord.is_ub_def Pord.has_ub_def split:option.splits)
          obtain x where OSup : "O.is_sup {a', aa} x" using OS.complete2[OF OUb]
            by(auto simp add:pleq_def Pord.has_sup_def)
  
          have "is_sup  {a, b} (Some x)" 
          proof(rule is_sup_intro)
            fix xa
            assume Hxa : "xa \<in> {a, b}"
            obtain xa' where Hxa' : "xa = Some xa' \<and> (xa' = a' \<or> xa' = aa)" using Hi1 Hi2 Hxa
              by(auto simp add:
                  pleq_def is_ub_def is_least_def has_ub_def split:option.splits elim:O.is_sup_unfold1 O.is_sup_unfold2)
            have 0 : "pleq' xa' x" using Hxa' OSup
              by(auto simp add:O.is_sup_def O.is_least_def O.is_ub_def)
            show "pleq xa (Some x)" using 0 Hxa'
              by(auto simp add:pleq_def)
          next
            fix x'
            assume Hx' : "is_ub {a, b} x'"
            show "pleq (Some x) x'" using Hx' Hi1 Hi2 OSup
              by(auto simp add:
                  pleq_def is_ub_def O.is_sup_def O.is_least_def O.is_ub_def is_least_def split:option.splits)
          qed
          thus "Pord.has_sup pleq {a, b}" by (auto simp add:Pord.has_sup_def)
        qed
      qed
    qed
  qed
qed

sublocale Pbordc_Option_Spec \<subseteq> Pbordc_Spec "pleq" "bot"
proof(unfold_locales)
  fix a
  show "pleq bot a"
    by(auto simp add:bot_def pleq_def)
qed


locale Mg_Option' = Pbord_Option +
  fixes bsup' :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
begin

definition bsup :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
"bsup x y =
  (case x of
    None \<Rightarrow> y
    | Some x' \<Rightarrow> (case y of
                       None \<Rightarrow> Some x'
                       | Some y' \<Rightarrow> Some (bsup' x' y')))"
end

locale Mg_Option = Mg_Option' +
  OM : Mergeable pleq' bsup'

locale Mg_Option_Spec = Mg_Option +
  Pbordc_Option_Spec +
  OMS : Mergeable_Spec pleq' bsup'

sublocale Mg_Option_Spec \<subseteq> Mergeable_Spec pleq bsup
proof(auto simp only:Mergeable_Spec_def)
  show "Pordc_Spec pleq" by (rule local.Pordc_Spec_axioms)

  show "Mergeable_Spec_axioms pleq bsup"
  proof(unfold_locales)
    fix a b
    show "is_bsup a b (bsup a b)"
    proof(cases a)
      case None
      then show ?thesis
      proof(cases b)
        show "a = None \<Longrightarrow> b = None \<Longrightarrow> is_bsup a b (bsup a b)"
          by(auto simp add: pleq_def bsup_def is_bsup_def is_least_def is_bub_def is_sup_def is_ub_def)

        fix b'
        assume Hi1 : "a = None"
        assume Hi2 : "b = Some b'"
        show "is_bsup a b (bsup a b)"
        proof(rule is_bsup_intro)
          show "pleq a (bsup a b)" using Hi1 Hi2
            by(simp add: pleq_def bsup_def is_bsup_def is_least_def is_bub_def is_sup_def is_ub_def split:option.splits)
        next

          fix bd sd
          assume Hii1 : "pleq bd b"
          assume Hii2 : "is_sup {a, bd} sd"

          show "pleq sd (bsup a b)" 
          proof(cases bd)
            assume Hiii1 : "bd = None"
            have "is_sup {None} None" by (auto simp add:is_sup_def is_least_def is_ub_def pleq_def)
            hence "sd = None" using Hi1 Hii2 Hiii1 is_sup_unique by(cases sd; auto)
            thus "pleq sd (bsup a b)"
              by(auto simp add:pleq_def split:option.splits)
          next
            fix bd'
            assume Hiii1 : "bd = Some bd'"
            have "is_sup {None, Some bd'} (Some bd')" by(auto simp add:is_sup_def is_least_def is_ub_def pleq_def OS.leq_refl)
            hence "sd = Some bd'" using Hi1 Hii2 Hiii1 is_sup_unique 
              by(cases sd; auto)
            thus "pleq sd (bsup a b)" using Hi1 Hi2 Hii1 Hiii1
              by(auto simp add:pleq_def bsup_def split:option.splits)
          qed
        next
          fix x'
          assume H : "is_bub a b x'"
          show "pleq (bsup a b) x'" using is_bub_unfold2[OF H]
          proof(-)
            assume Hleast : "(\<And>(bd::'a option) sd::'a option. pleq bd b \<Longrightarrow> is_sup {a, bd} sd \<Longrightarrow> pleq sd x')"

            have 0 : "pleq (Some b') (b)" using Hi2 by(simp add: leq_refl)

            have 1 : "is_sup {a, (Some b')} (Some b')" using Hi1
              by(auto simp add:pleq_def is_sup_def is_least_def is_ub_def OS.leq_refl)

            show "pleq (bsup a b) x'" using Hleast[OF 0 1]
              by(simp add: Hi1 Hi2 bsup_def)
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
            by(simp add: pleq_def bsup_def is_bsup_def is_least_def is_bub_def is_sup_def is_ub_def OS.leq_refl split:option.splits)
        next
          fix bd sd
          assume Hii1 : "pleq bd b"
          assume Hii2 : "is_sup {a, bd} sd"

          show "pleq sd (bsup a b)" 
          proof(cases bd)
            assume Hiii1 : "bd = None"
            have "is_sup {Some a', None} (Some a')" by(auto simp add:is_sup_def is_least_def is_ub_def pleq_def OS.leq_refl)
            hence "sd = Some a'" using Hi1 Hi2 Hii1 Hii2 Hiii1 is_sup_unique by(cases sd; auto)
            thus "pleq sd (bsup a b)" using Hi1 Hi2 OS.leq_refl
              by(auto simp add:pleq_def bsup_def)
          next
            fix bd'
            assume Hiii1 : "bd = Some bd'"
            (* contradiction *)
            thus "pleq sd (bsup a b)" using Hi2 Hii1 Hiii1 
              by(auto simp add:pleq_def)
          qed

        next
            fix x'
            assume H : "is_bub a b x'"
            show "pleq (bsup a b) x'" using is_bub_unfold2[OF H]
            proof(-)
              assume Hleast : "(\<And>(bd::'a option) sd::'a option. pleq bd b \<Longrightarrow> is_sup {a, bd} sd \<Longrightarrow> pleq sd x')"

              have 0 : "pleq (None) (b)" using Hi2 by(simp add: leq_refl)

              have 1 : "is_sup {a, None} (a)" using Hi1
                by(auto simp add:pleq_def is_sup_def is_least_def is_ub_def OS.leq_refl)
  
              show "pleq (bsup a b) x'" using Hleast[OF 0 1]
                by(simp add: Hi1 Hi2 bsup_def)
            qed
          qed

        next

          fix b'
          assume Hi1 : "a = Some a'"
          assume Hi2 : "b = Some b'"
          show "is_bsup a b (bsup a b)"
          proof(rule is_bsup_intro)
            show "pleq a (bsup a b)" using Hi1 Hi2 O.bsup_leq OMS.bsup_spec[of a' b']
              by(auto simp add: pleq_def bsup_def is_bsup_def is_least_def is_bub_def is_sup_def is_ub_def OS.leq_refl split:option.splits)
          next

            fix bd sd
            assume Hii1 : "pleq bd b"
            assume Hii2 : "is_sup {a, bd} sd"
            show "pleq sd (bsup a b)"
            proof(cases bd)
              assume Hiii1 : "bd = None"  
              have "is_sup {Some a', None} (Some a')" by(auto simp add:is_sup_def is_least_def is_ub_def pleq_def OS.leq_refl)
              hence "sd = Some a'" using Hi1 Hi2 Hii1 Hii2 Hiii1 is_sup_unique by(cases sd; auto)
              thus "pleq sd (bsup a b)" using Hi1 Hi2 O.bsup_leq OMS.bsup_spec[of a' b']
                by(auto simp add:pleq_def bsup_def)
            next
              fix bd'
              assume Hiii1 : "bd = Some bd'"
              obtain sd' where Hsd' : "sd = Some sd'"
                using Hii2 Hi1
                by(auto simp add:is_sup_def is_least_def is_ub_def pleq_def split:option.splits)

              have OSup :  "O.is_sup {a', bd'} sd'" 
              proof(rule O.is_sup_intro)
                fix x'
                assume H : "x' \<in> {a', bd'}"
                have 0 : "pleq' a' sd'"  using Hii2 Hi1 Hsd'
                  by(auto simp add:is_sup_def is_least_def is_ub_def pleq_def split:option.splits)
  
                have 1 : "pleq' bd' sd'" using Hii2 Hiii1 Hsd'
                  by(auto simp add:is_sup_def is_least_def is_ub_def pleq_def split:option.splits)

                show "pleq' x' sd'" using H 0 1 by auto
              next
                fix x'
                assume H : "O.is_ub {a', bd'} x'"

                show "pleq' sd' x'" using H Hi1 Hii2 Hiii1 Hsd'
                  by(auto simp add:is_sup_def is_least_def is_ub_def pleq_def O.is_ub_def split:option.splits)
              qed

              have OBsup : "O.is_bsup a' b' (bsup' a' b')" by (auto simp add:OMS.bsup_spec)

              have Hbbd' : "pleq' bd' b'" using Hi2 Hii1 Hiii1
                by(auto simp add:pleq_def)
              
              show "pleq sd (bsup a b)" using O.is_bsup_unfold2[OF OBsup Hbbd' OSup] Hsd' Hi1 Hi2 Hiii1
                by(auto simp add:pleq_def bsup_def)
            qed

          next
            fix x
            assume H: "is_bub a b x"

            obtain x' where Hx' : "x = Some x'" using Hi1 Hi2 H 
              by(auto simp add:is_bub_def pleq_def split:option.splits)

            have Bub' : "O.is_bub a' b' x'" 
            proof(rule OS.is_bub_intro)
              show "pleq' a' x'" using Hi1 Hx' is_bub_unfold1[OF H]
                by(auto simp add:pleq_def)

            next

              fix bd' sd'
              assume Hpleq' : "pleq' bd' b'"
              assume HOsup : "O.is_sup {a', bd'} sd'"

              have Hpleq : "pleq (Some bd') (b)" using Hi2 Hpleq' by (auto simp add:pleq_def)

              have HSup : "is_sup {a, Some bd'} (Some sd')"
                using Hi1 HOsup 
                by(auto simp add:pleq_def O.is_sup_def O.is_least_def O.is_ub_def is_sup_def is_least_def is_ub_def split:option.splits)

              show "pleq' sd' x'" using Hi1 Hx' is_bub_unfold2[OF H Hpleq HSup]
                by(auto simp add:pleq_def O.is_sup_def)
            qed


            show "pleq (bsup a b) x" using Hx' Hi1 Hi2 Bub'
                                                       OMS.bsup_spec[of a' b']
              by(auto simp add:pleq_def bsup_def O.is_bsup_def O.is_least_def)
          qed
        qed
      qed
    qed
  qed


locale Pbord_Pair' =
  fixes pleq1 :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes pleq2 :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
  fixes bot1 :: "'a"
  fixes bot2 :: "'b"
begin
definition pleq :: "('a * 'b) \<Rightarrow> ('a * 'b) \<Rightarrow> bool" where
"pleq x y =
  (case x of
      (x1, x2) \<Rightarrow> (case y of
                    (y1, y2) \<Rightarrow> (pleq1 x1 y1 \<and> pleq2 x2 y2)))"

definition bot :: "('a * 'b)" where
"bot = (bot1, bot2)"
end

locale Pbord_Pair = Pbord_Pair' +
  O1 : Pbord pleq1 bot1 +
  O2 : Pbord pleq2 bot2

sublocale Pbord_Pair \<subseteq> Pbord "pleq" "bot"
  done

locale Pordc_Pair_Spec = Pbord_Pair +
  OS1 : Pbordc_Spec pleq1 bot1 +
  OS2 : Pbordc_Spec pleq2 bot2
  
sublocale Pordc_Pair_Spec \<subseteq> Pordc_Spec "pleq"
proof(unfold_locales)

  fix a
  show "pleq a a" by (auto simp add:pleq_def OS1.leq_refl OS2.leq_refl split:prod.splits)

next

  fix a b c
  assume H1 : "pleq a b"
  assume H2 : "pleq b c"

  obtain a1 and a2 where 0 : "a = (a1, a2)" by (cases a; auto)
  obtain b1 and b2 where 1 : "b = (b1, b2)" by (cases b; auto)
  obtain c1 and c2 where 2 : "c = (c1, c2)" by (cases c; auto)

  show "pleq a c" using H1 H2 0 1 2 OS1.leq_trans[of a1 b1 c1] OS2.leq_trans[of a2 b2 c2]
    by (auto simp add:pleq_def)

next

  fix a b
  assume H1 : "pleq a b"
  assume H2 : "pleq b a"

  obtain a1 and a2 where 0 : "a = (a1, a2)" by (cases a; auto)
  obtain b1 and b2 where 1 : "b = (b1, b2)" by (cases b; auto)

  show "a = b" using H1 H2 0 1 OS1.leq_antisym[of a1 b1] OS2.leq_antisym[of a2 b2]
    by(auto simp add:pleq_def)

next

  fix a b
  assume H : "has_ub {a, b}"

  obtain a1 and a2 where 0 : "a = (a1, a2)" by (cases a; auto)
  obtain b1 and b2 where 1 : "b = (b1, b2)" by (cases b; auto)

  obtain ub where HUb : "is_ub {a, b} ub" using H by (auto simp add:has_ub_def)
  obtain ub1 and ub2 where HUb' : "ub = (ub1, ub2)" by (cases ub; auto)

  have Ub1 : "O1.is_ub {a1, b1} ub1" using H 0 1 HUb HUb'
    by(auto simp add:pleq_def is_ub_def O1.is_ub_def)
  have Ub2 : "O2.is_ub {a2, b2} ub2" using H 0 1 HUb HUb'
    by(auto simp add:pleq_def is_ub_def O2.is_ub_def)

  obtain sup1 where Sup1 : "O1.is_sup {a1, b1} sup1" using OS1.complete2[of a1 b1] Ub1
    by(auto simp add: O1.has_sup_def O1.has_ub_def)

  

  obtain sup2 where Sup2 : "O2.is_sup {a2, b2} sup2"
    using OS2.complete2[of a2 b2] Ub2
    by(auto simp add: O2.has_sup_def O2.has_ub_def)

  have Sup : "is_sup {(a1, a2), (b1, b2)} (sup1, sup2)" using Sup1 Sup2
    by(auto simp add: pleq_def is_sup_def is_ub_def is_least_def
                         O1.is_sup_def O1.is_ub_def O1.is_least_def
                         O2.is_sup_def O2.is_ub_def O2.is_least_def)

  thus "has_sup {a, b}" using 0 1 by (auto simp add:has_sup_def)
qed

sublocale Pordc_Pair_Spec \<subseteq> Pbordc_Spec "pleq" "bot"
proof(unfold_locales)
  fix a
  show "pleq bot a"
    by(cases a; auto simp add:pleq_def bot_def OS1.bot_spec OS2.bot_spec)
qed

locale Mg_Pair' = Pbord_Pair +
  fixes bsup1 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes bsup2 :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
begin

definition bsup :: "('a * 'b) \<Rightarrow> ('a * 'b) \<Rightarrow> ('a * 'b)" where
"bsup a b =
  (case a of
    (a1, a2) \<Rightarrow> (case b of
                  (b1, b2) \<Rightarrow> (bsup1 a1 b1, bsup2 a2 b2)))"
end

locale Mg_Pair = Mg_Pair' +
  OM1 : Mergeable pleq1 bsup1 +
  OM2 : Mergeable pleq2 bsup2

locale Mg_Pair_Spec = Mg_Pair +
  Pordc_Pair_Spec +
  OMS1 : Mergeable_Spec pleq1 bsup1 +
  OMS2 : Mergeable_Spec pleq2 bsup2

sublocale Mg_Pair_Spec \<subseteq> Mergeable_Spec pleq bsup
proof(auto simp only:Mergeable_Spec_def)
  show "Pordc_Spec pleq" by (rule local.Pordc_Spec_axioms)

next
  show "Mergeable_Spec_axioms pleq bsup"
  proof(unfold_locales)

    fix a :: "'a  * 'b"
    fix b :: "'a * 'b"

    obtain a1 and a2 where Ha : "a = (a1, a2)" by(cases a; auto)
    obtain b1 and b2 where Hb : "b = (b1, b2)" by(cases b; auto)

    show "is_bsup a b (bsup a b)"
    proof(rule is_bsup_intro)

      show "pleq a (bsup a b)" using Ha Hb O1.bsup_leq[OF OMS1.bsup_spec[of a1 b1]] O2.bsup_leq[OF OMS2.bsup_spec[of a2 b2]]
        by(auto simp add:pleq_def bsup_def split:prod.splits)

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

      have Hbsv1 : "bsupv1 = bsup1 a1 b1" using Ha Hb Hbsup
        by(auto simp add:bsup_def)
      have Hbsv2 : "bsupv2 = bsup2 a2 b2" using Ha Hb Hbsup
        by(auto simp add:bsup_def)

      have Sup1 : "O1.is_sup {a1, bd1} sd1" using Ha Hbd Hsd Hsup
        by(auto simp add: pleq_def is_sup_def is_least_def is_ub_def O1.is_sup_def O1.is_least_def O1.is_ub_def)

      have Sup2 : "O2.is_sup {a2, bd2} sd2" using Ha Hbd Hsd Hsup
        by(auto simp add: pleq_def is_sup_def is_least_def is_ub_def O2.is_sup_def O2.is_least_def O2.is_ub_def)

      have Leq1 : "pleq1 bd1 b1" using Hb Hbd Hleq
        by(auto simp add: pleq_def is_sup_def is_least_def is_ub_def)

      have Leq2 : "pleq2 bd2 b2" using Hb Hbd Hleq
        by(auto simp add: pleq_def is_sup_def is_least_def is_ub_def)

      have Bsup1 : "O1.is_bsup a1 b1 bsupv1" using Hbsup Ha Hb OMS1.bsup_spec[of a1 b1]
        by(auto simp add:bsup_def)

      have Bsup2 : "O2.is_bsup a2 b2 bsupv2" using Hbsup Ha Hb OMS2.bsup_spec[of a2 b2]
        by(auto simp add:bsup_def)

      have Conc1 : "pleq1 sd1 (bsup1 a1 b1)" using O1.is_bsup_unfold2[OF Bsup1 Leq1 Sup1] Hbsv1
        by(auto simp add:O1.is_bsup_def O1.is_least_def O1.is_bub_def)
        
      have Conc2 : "pleq2 sd2 (bsup2 a2 b2)" using O2.is_bsup_unfold2[OF Bsup2 Leq2 Sup2] Hbsv2
        by(auto simp add:O2.is_bsup_def O2.is_least_def O2.is_bub_def)

      show "pleq sd (bsup a b)" using Ha Hb Hbsup Hbsv1 Hbsv2 Hsd Conc1 Conc2
        by(auto simp add:pleq_def bsup_def)

    next

      fix x :: "'a * 'b"
      obtain a1 and a2 where Ha : "a = (a1, a2)" by(cases a; auto)
      obtain b1 and b2 where Hb : "b = (b1, b2)" by(cases b; auto)
      obtain x1 and x2 where Hx : "x = (x1, x2)" by(cases x; auto)
      obtain bsupv1 and bsupv2 where Hbsup : "bsup a b = (bsupv1, bsupv2)" by (cases "(bsup a b)"; auto)

      have Hbsv1 : "bsupv1 = bsup1 a1 b1" using Ha Hb Hbsup
        by(auto simp add:bsup_def)
      have Hbsv2 : "bsupv2 = bsup2 a2 b2" using Ha Hb Hbsup
        by(auto simp add:bsup_def)


      assume Hbub : "is_bub a b x"

      have Hbub1 : "O1.is_bub a1 b1 x1"
      proof(rule OS1.is_bub_intro)
        show "pleq1 a1 x1" using Hbub Ha Hx by(auto simp add:is_bub_def is_sup_def pleq_def)
      next
        fix bd1 :: 'a
        fix sd1 :: 'a
        assume H1 : "pleq1 bd1 b1"
        assume H2 : "O1.is_sup {a1,bd1} sd1"

        have Hpleq' : "pleq (bd1, bot2) b" using H1 Hb OS2.bot_spec[of b2]
          by (auto simp add: pleq_def)
        
        have Hsup' : "is_sup {a, (bd1, bot2)} (sd1, a2)" using Ha OS2.bot_spec[of a2] H2
          by(auto simp add:is_sup_def is_least_def is_ub_def pleq_def O1.is_sup_def O1.is_least_def O1.is_ub_def OS2.leq_refl)

        show "pleq1 sd1 x1" using is_bub_unfold2[OF Hbub Hpleq' Hsup'] Hx
          by(simp add:pleq_def)
      qed
  
      have Hbub2 : "O2.is_bub a2 b2 x2" 
      proof(rule OS2.is_bub_intro)
        show "pleq2 a2 x2" using Hbub Ha Hx by(auto simp add:is_bub_def is_sup_def pleq_def)
      next
        fix bd2 :: 'b
        fix sd2 :: 'b
        assume H1 : "pleq2 bd2 b2"
        assume H2 : "O2.is_sup {a2,bd2} sd2"

        have Hpleq' : "pleq (bot1, bd2) b" using H1 Hb OS1.bot_spec[of b1]
          by (auto simp add: pleq_def)
        
        have Hsup' : "is_sup {a, (bot1, bd2)} (a1, sd2)" using Ha OS1.bot_spec[of a1] H2
          by(auto simp add:is_sup_def is_least_def is_ub_def pleq_def O2.is_sup_def O2.is_least_def O2.is_ub_def OS1.leq_refl)

        show "pleq2 sd2 x2" using is_bub_unfold2[OF Hbub Hpleq' Hsup'] Hx
          by(simp add:pleq_def)
      qed

      show "pleq (bsup a b) x" using Hx Ha Hb Hbub1 Hbub2 OMS1.bsup_spec[of a1 b1] OMS2.bsup_spec[of a2 b2]
        by(auto simp add:pleq_def bsup_def O1.is_bsup_def O1.is_least_def O2.is_bsup_def O2.is_least_def)
    qed
  qed
qed

locale Pbord_Priority' =
  fixes pleq' :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes bot'  :: "'a"
begin
definition pleq :: "(nat * 'a) \<Rightarrow> (nat * 'a) \<Rightarrow> bool" where
"pleq x y =
  (case x of
      (xi, x') \<Rightarrow> (case y of
                    (yi, y') \<Rightarrow> (if (xi \<le> yi) then
                                      (if (yi \<le> xi) then pleq' x' y' else True)
                                    else False)))"

definition bot :: "nat * 'a" where
"bot = (0, bot')"

end

locale Pbord_Priority = Pbord_Priority' +
  O : Pbord pleq' bot'

sublocale Pbord_Priority \<subseteq> Pbord "pleq" "bot"
  done

locale Pbordc_Priority_Spec = Pbord_Priority +
  OS : Pbordc_Spec pleq' bot'


sublocale Pbordc_Priority_Spec \<subseteq> Pbordc_Spec "pleq" "bot"
proof(unfold_locales)

  fix a
  show "pleq a a" by (auto simp add:pleq_def OS.leq_refl split:prod.splits)

next

  fix a :: "(nat * 'a)"
  fix b :: "(nat * 'a)"
  fix c :: "(nat * 'a)"

  assume H1 : "pleq a b"
  assume H2 : "pleq b c"

  obtain ai and a' where Ha : "a = (ai, a')" by (cases a; auto)
  obtain bi and b' where Hb : "b = (bi, b')" by (cases b; auto)
  obtain ci and c' where Hc : "c = (ci, c')" by (cases c; auto)

  show "pleq a c"
  proof(cases "ci \<le> ai")
    case False
    then show ?thesis using H1 H2 Ha Hb Hc 
      by(auto simp add:pleq_def split:if_splits)
  next
    case True
    then show ?thesis using H1 H2 Ha Hb Hc OS.leq_trans[of a' b' c']
      by(auto simp add:pleq_def split:if_splits)
  qed

next

  fix a :: "(nat * 'a)"
  fix b :: "(nat * 'a)"
  obtain ai and a' where Ha : "a = (ai, a')" by (cases a; auto)
  obtain bi and b' where Hb : "b = (bi, b')" by (cases b; auto)

  assume H1 : "pleq a b"
  assume H2 : "pleq b a"

  show "a = b" using H1 H2 Ha Hb OS.leq_antisym[of a' b']
    by(auto simp add:pleq_def split:if_splits)

next

  fix a :: "(nat * 'a)"
  fix b :: "(nat * 'a)"

  assume H : "has_ub {a, b}"
  obtain ai and a' where Ha : "a = (ai, a')" by (cases a; auto)
  obtain bi and b' where Hb : "b = (bi, b')" by (cases b; auto)

  obtain c where Hub : "is_ub {a, b} c" using H by (auto simp add:has_ub_def)
  obtain ci and c' where Hc : "c = (ci, c')" by (cases c; auto)

  show "has_sup {a, b}"
  proof(cases "ai \<le> bi")
    assume True : "ai \<le> bi"
    show ?thesis
    proof(cases "bi \<le> ai")
      assume True' : "bi \<le> ai"
      have Haibi : "ai = bi" using True True' by auto
      show ?thesis
      proof(cases "O.has_ub {a', b'}")
        assume True'' : "O.has_ub {a', b'}"
        have Hhassup' : "O.has_sup {a', b'}" using OS.complete2[OF True''] by auto
        obtain sup' where Hsup' : "O.is_sup {a', b'} sup'" using Hhassup' by(auto simp add:O.has_sup_def)
        have "is_sup {a, b} (ai, sup')" using Haibi Ha Hb Hc Hsup'
          by(auto simp add: is_sup_def is_least_def is_ub_def pleq_def O.is_sup_def O.is_least_def O.is_ub_def)
        thus ?thesis by (auto simp add:has_sup_def)
      next
        assume False'' : "\<not> O.has_ub {a', b'}" 
        have "is_sup {a, b} (1 + ai, bot')"
        proof(rule is_sup_intro)
          fix x
          assume Hi : "x \<in> {a, b}"
          show "pleq x (1 + ai, bot')" using Hi Ha Hb Haibi
            by(auto simp add: pleq_def)
        next

          fix ub 
          assume Hi : "is_ub {a, b} ub"
          obtain ubi and ub' where Hub2 : "ub = (ubi, ub')" by (cases ub; auto)
          show "pleq (1 + ai, bot') ub" using Hi Hub2
          proof(cases "ubi \<ge> 1 + ai")
            assume True''' : "ubi \<ge> 1 + ai" 
            thus ?thesis using Hi Hub2 OS.bot_spec by(auto simp add:pleq_def)

          next

            assume False''' : "\<not> ubi \<ge> 1 + ai"
            have Haiubi : "ai = ubi" using False''' Hi Hub2 Ha Hb  Haibi
              by(auto simp add:is_ub_def pleq_def split:if_split_asm) 
            have "O.is_ub {a', b'} ub'" using Hi Hub2 False''' Haibi Haiubi Ha Hb
              by(auto simp add:pleq_def O.is_sup_def O.is_least_def O.is_ub_def is_ub_def split:if_split_asm)
            hence "O.has_ub {a', b'}" by(auto simp add: O.has_ub_def)
            thus ?thesis using False'' by auto

          qed
        qed
        thus ?thesis by(auto simp add:has_sup_def)
      qed

    next

      assume False' : "\<not> bi \<le> ai"
      hence "is_sup {a, b} b" using Ha Hb OS.leq_refl by(auto simp add: is_sup_def is_least_def is_ub_def pleq_def)
      thus ?thesis by(auto simp only:has_sup_def)
    qed

  next
    assume False : "\<not> ai \<le> bi"
    hence "is_sup {a, b} a" using Ha Hb OS.leq_refl by(auto simp add: is_sup_def is_least_def is_ub_def pleq_def)
    thus ?thesis by(auto simp only:has_sup_def)
  qed

next

  fix a
  show "pleq bot a" using OS.bot_spec
    by(auto simp add: pleq_def bot_def)
qed
        


locale Mg_Priority' = Pbord_Priority +
  fixes bsup' :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

begin

(*
definition bsup :: "('a * 'b) \<Rightarrow> ('a * 'b) \<Rightarrow> ('a * 'b)" where
"bsup a b =
  (case a of
    (a1, a2) \<Rightarrow> (case b of
                  (b1, b2) \<Rightarrow> (if pleq a1 b1 then
                                  (if pleq b1 a1 then (a1, bsup2 a2 b2)
                                                 else (b1, b2))
                               else (if pleq b1 a1 then (a1, a2)
                                        else (bsup a1 b1, a2)))))"
*)
definition bsup :: "(nat * 'a) \<Rightarrow> (nat * 'a) \<Rightarrow> (nat * 'a)" where
"bsup a b =
  (case a of
    (ai, a') \<Rightarrow> (case b of
                  (bi, b') \<Rightarrow> (if ai \<le> bi then
                                  (if bi \<le> ai then
                                    (if pleq' b' (bsup' a' b') then
                                         (ai, bsup' a' b')
                                         else (1 + ai, bot'))
                                                 else (bi, b'))
                               else (ai, a'))))"

end

locale Mg_Priority = Mg_Priority' +
  OM : Mergeable pleq' bsup'

locale Mg_Priority_Spec = Mg_Priority +
  Pbordc_Priority_Spec +
  OMS : Mergeable_Spec pleq' bsup'

sublocale Mg_Priority_Spec \<subseteq> Mergeable_Spec pleq bsup
proof(auto simp only:Mergeable_Spec_def)
  show "Pordc_Spec pleq" by (rule local.Pordc_Spec_axioms)

next
  show "Mergeable_Spec_axioms pleq bsup"
  proof(unfold_locales)
    fix a :: "(nat * 'a)"
    fix b :: "(nat * 'a)"
    obtain ai and a' where Ha : "a = (ai, a')" by (cases a; auto)
    obtain bi and b' where Hb : "b = (bi, b')" by (cases b; auto)

    obtain bsi and bs' where Hbs : "bsup a b = (bsi, bs')" by (cases "bsup a b"; auto)

    show "is_bsup a b (bsup a b)"
    proof(rule is_bsup_intro)

      show "pleq a (bsup a b)" using Ha Hb OS.leq_refl O.bsup_leq OMS.bsup_spec[of a' b']
        by(auto simp add: pleq_def bsup_def)

    next

      fix bd :: "(nat * 'a)"
      fix sd :: "(nat * 'a)"

      obtain bdi and bd' where Hbd : "bd = (bdi, bd')" by (cases bd; auto)
      obtain sdi and sd' where Hsd : "sd = (sdi, sd')" by (cases sd; auto)

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
              by(auto simp add:pleq_def)
            hence "is_sup {a, bd} a" by(auto simp add:is_sup_def is_least_def is_ub_def leq_refl)
            hence "sd = a" using is_sup_unique[OF H2] by auto

            thus "pleq sd (bsup a b)"
              using Ha Hb OS.leq_refl O.bsup_leq OMS.bsup_spec[of a' b']
              by(auto simp add: pleq_def bsup_def)

          next

            assume False'' : "\<not> bdi < bi"

            hence Hbdibi : "bdi = bi" using H1 Hb Hbd by(auto simp add:pleq_def split:if_split_asm)
            hence Hbd'b' : "pleq' bd' b'" using H1 Hb Hbd by(auto simp add:pleq_def)

            show "pleq sd (bsup a b)"
            proof(cases "pleq' b' (bsup' a' b')")
              assume True''' : "pleq' b' (bsup' a' b')"

              have "pleq' a' (bsup' a' b')" using O.bsup_leq[OF OMS.bsup_spec[of a' b']] by auto
              hence "O.is_ub {a', b'} (bsup' a' b')" using True''' by (auto simp add:O.is_ub_def)
              hence "O.has_ub {a', b'}" by(auto simp add:O.has_ub_def)
              hence "O.has_sup {a', b'}" using OS.complete2 by auto
              then obtain sup' where Hsup' : "O.is_sup {a', b'} sup'" by(auto simp add:O.has_sup_def)

              have Bssup' : "O.is_sup {a', b'} (bsup' a' b')" using OS.bsup_sup[OF Hsup' OMS.bsup_spec[of a' b']] by auto
              hence  "is_ub {a, b} (bsup a b)" using H2 Ha Hb Hsd Hbd Haibi Hbdibi Hbd'b' True''' O.bsup_leq[OF OMS.bsup_spec[of a' b']]
                by(auto simp add:pleq_def bsup_def is_ub_def)

              hence "is_ub {a, bd} (bsup a b)" using leq_trans[of bd b "bsup a b"] H1
                by(auto simp add:is_ub_def)

              thus ?thesis using is_sup_unfold2[OF H2] by auto
            next

              assume False''' : "\<not> pleq' b' (bsup' a' b')"

              have "bsup a b = (1 + ai, bot')" using Ha Hb Haibi True True' False''' by(auto simp add:bsup_def)
              hence "is_ub {a, bd} (bsup a b)" using Ha Hb Haibi Hbdibi Hbd by(auto simp add:pleq_def is_ub_def)
              hence "is_ub {a, bd} (bsup a b)" using leq_trans[of bd b "bsup a b"] H1
                by(auto simp add:is_ub_def)

              thus ?thesis using is_sup_unfold2[OF H2] by auto
            qed
          qed

        next
          assume False' : "\<not> bi \<le> ai"
          hence Hbsupb : "bsup a b = b" using Ha Hb
          by(auto simp add:pleq_def bsup_def is_sup_def is_least_def is_ub_def split:if_split_asm)

        have Hub : "is_ub {a, bd} b" using Ha Hb False' OS.leq_refl H1
          by(auto simp add:pleq_def bsup_def is_sup_def is_least_def is_ub_def split:if_split_asm)

        show ?thesis using Hbsupb is_sup_unfold2[OF H2 Hub]
          by auto
        qed

      next
        case False
        hence Hbsupa : "bsup a b = a" using Ha Hb
          by(auto simp add:pleq_def bsup_def is_sup_def is_least_def is_ub_def split:if_split_asm)

        have Hub : "is_ub {a, bd} a" using Ha Hb False OS.leq_refl H1
          by(auto simp add:pleq_def bsup_def is_sup_def is_least_def is_ub_def split:if_split_asm)

        show ?thesis using Hbsupa is_sup_unfold2[OF H2 Hub]
          by auto
      qed
    next

      fix x :: "(nat * 'a)"
      obtain xi and x' where Hx : "x = (xi, x')" by (cases x; auto)

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
          proof(cases "pleq' b' (bsup' a' b')")
            assume True'' : "pleq' b' (bsup' a' b')"

            hence 0 : "bsup a b = (ai, bsup' a' b')" using Ha Hb True True' True'' by (auto simp add:bsup_def)

            hence 1 : "pleq b (bsup a b)" using Hb Haibi True''
              by(auto simp add:pleq_def)

            have 2 : "O.is_sup {a', b'} (bsup' a' b')" using OS.bsup_imp_sup[OF OMS.bsup_spec[of a' b'] True''] by auto

            thus ?thesis
            proof(cases "bi \<le> xi")
              assume True''' : "bi \<le> xi"

              thus ?thesis
              proof(cases "xi \<le> bi")
                assume True'''' : "xi \<le> bi"

                have Hxibi : "xi = bi" using True''' True'''' by auto

                have "is_sup {a, b} (bsup a b)" using Ha Hb Hx Haibi Hax True''' True'''' 0 2
                  apply(auto simp add: O.is_ub_def pleq_def is_bub_def O.is_bub_def is_sup_def is_least_def is_ub_def O.is_sup_def O.is_least_def)
                  done

                thus ?thesis using is_bub_unfold2[OF H leq_refl[of b]] by auto
              next

                assume False'''' : "\<not> xi \<le> bi"

                thus ?thesis using False'''' Haibi Ha Hb Hx OS.bot_spec[of x']
                  by(auto simp add:pleq_def bsup_def)
              qed

            next
              assume False''' : "\<not> bi \<le> xi"
              thus ?thesis using Haibi Ha Hb Hx Hax
                by(auto simp add:pleq_def bsup_def)
            qed
          next
            assume False'' : "\<not> pleq' b' (bsup' a' b')"

            hence 0 : "bsup a b = (1 + ai, bot')" using Ha Hb Hx Haibi
              by (auto simp add:pleq_def bsup_def)

            have "\<not> O.has_ub {a', b'}" using OS.bsup_imp_sup_conv[OF OMS.bsup_spec[of a' b'] False'']
              by(auto simp add:O.has_ub_def)

            hence 1 : "is_sup {a, b} (bsup a b)" using Ha Hb Haibi 0 OS.bot_spec
              by(auto simp add:is_sup_def is_least_def is_ub_def pleq_def O.has_ub_def O.is_ub_def)

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

                thus ?thesis using 0 Ha Hb Hx Haibi OS.bot_spec
                  by(auto simp add:pleq_def)
              qed
            next

              assume False''' : "\<not> bi \<le> xi"

              thus ?thesis using is_bub_unfold2[OF H leq_refl[of b]] 1 by auto
            qed
          qed
        next
          assume False' : "\<not> bi \<le> ai"

          have "is_sup {a, b} (bsup a b)"  using True False' Ha Hb Hx OS.leq_refl
            by(auto simp add:pleq_def bsup_def is_sup_def is_least_def is_ub_def)
          thus ?thesis using is_bub_unfold2[OF H leq_refl[of b]] by auto
        qed
      next
        assume False : "\<not> ai \<le> bi"
          have "is_sup {a, b} (bsup a b)"  using False Ha Hb Hx OS.leq_refl
            by(auto simp add:pleq_def bsup_def is_sup_def is_least_def is_ub_def)
          thus ?thesis using is_bub_unfold2[OF H leq_refl[of b]] by auto
      qed
    qed
  qed
qed

end