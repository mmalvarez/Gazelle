theory Mergeable_Instances imports Mergeable Wrappers Mergeable_Facts
 (* imports "./Instances/Mg_Triv" "./Instances/Mg_Option.thy" "./Instances/Mg_Prio.thy"
          "./Instances/Mg_Prod.thy" (* "./Instances/Mg_Oalist.thy" "./Instances/Mg_Roalist.thy *)
          "./Mergeable_Facts.thy" *)
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

end