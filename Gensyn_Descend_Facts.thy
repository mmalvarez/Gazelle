theory Gensyn_Descend_Facts imports Gensyn_Descend
begin

lemma gensyn_get_list_len  :
  fixes ts :: "('x) gensyn list" 
  shows "\<And> kh kt t' . gensyn_get_list ts (kh#kt) = Some t' \<Longrightarrow>
          kh < length ts"
proof(induction ts ) 
case Nil
then show ?case by auto
  next
  case (Cons th tt)
  then show ?case
    proof(cases kh)
    case 0
    then show ?thesis by auto
    next
      case (Suc n)
      then show ?thesis using Cons
        apply(auto)
        done
    qed 
  qed


lemma gensyn_get_list_len' :
  assumes H:  "gensyn_get_list ts (kh#kt) = Some t'"
  shows "kh < length (ts)" using H
proof(induct ts arbitrary:kh)
case Nil
    then show ?case by auto  next
case (Cons a ts)
    then show ?case
    proof(cases kh)
      case 0 then show ?thesis by auto  next
      case (Suc nat) then show ?thesis using Cons by auto
    qed
qed
    


lemma gensyn_get_list_nth :
  shows "gensyn_get_list ts [kh] = Some t' \<Longrightarrow>
          ts ! kh = t'"
proof(induction ts arbitrary:kh) 
  case Nil
then show ?case by auto
next
  case (Cons a ts)
  then show ?case
  proof(cases kh)
    case 0 then show ?thesis using Cons by auto next
    case (Suc nat) then show ?thesis using Cons by auto
  qed
qed

lemma gensyn_get_list_nth2 :
  shows "kh < length ts \<Longrightarrow>
         ts ! kh = t' \<Longrightarrow>
         gensyn_get_list ts [kh] = Some t'"
proof(induction ts arbitrary:kh)
  case Nil
  then show ?case by auto
next
  case (Cons a ts)
  then show ?case 
  proof(cases kh)
    case 0
    then show ?thesis using Cons by auto
  next
    case (Suc nat)
    then show ?thesis using Cons by auto 
  qed
qed

lemma gensyn_get_list_child  :
  assumes H:  "gensyn_get_list ts (kh#kt) = Some t'"
  shows (*glc_C1 :*) "kh < length ts" 
  and (*glc_C2:*) "gensyn_get (ts ! kh) kt = Some t'"
  using H
proof(induction ts arbitrary:kh)
  case Nil 
  {    
  case 1 then show ?case  by auto
  next case 2
  then show ?case by auto
  }
  case (Cons a ts)
  {
    case 1 then show ?case
    proof(cases kh)
      case 0 thus ?thesis by auto next
      case (Suc n) thus ?thesis using Cons 1 by auto
    qed

    case 2 then show ?case
    proof(cases kh)
      case 0 thus ?thesis using Cons 2
        apply(case_tac kt) apply(auto)
        apply(case_tac a) apply(auto) done next
      case (Suc n) thus ?thesis using Cons 2 by auto
    qed
  }
qed

(* need converse of previous lemma, to prove last-child lemma *)
lemma gensyn_get_list_child2 :
  assumes Hg: "gensyn_get t kt = Some t'"
  and Hl: "kh < length ts"
  and Hc: "ts ! kh = t"
shows
    "gensyn_get_list ts (kh#kt) = Some t'" using Hg Hl Hc
proof(induction ts arbitrary:kh) 
case Nil then show ?case by auto
next
  case (Cons a ts)
  then show ?case
  proof(cases kh)
    case 0
    then show ?thesis using Cons
      apply(case_tac kt) apply(auto)
      apply(case_tac a) apply(auto) done
  next
    case (Suc nat)
    then show ?thesis using Cons by auto
  qed
qed

(* need to constrain t'1. need exists *)
lemma gensyn_get_child :
  assumes H: "gensyn_get t (kh#kt) = Some t'"
  shows  "\<exists> t'1 . gensyn_get t [kh] = Some t'1 \<and>
            gensyn_get t'1 kt = Some t'" using H
proof(cases t)
  case (G x l)
  thus ?thesis using H gensyn_get_list_child gensyn_get_list_nth2
    by auto blast+
qed

lemma gensyn_get_child2 :
  assumes H1 : "gensyn_get t [kh] = Some t'1"
  and H2 : "gensyn_get t'1 kt = Some t'"
  shows  "gensyn_get t (kh#kt) = Some t'" using H1 H2
proof(cases t)
  case (G x l)
  thus ?thesis  using H1 H2 gensyn_get_list_child2[of t'1 kt t']
                           gensyn_get_list_len[of l kh "[]" t'1]
                           gensyn_get_list_nth[of l kh t'1] by auto
qed

lemma gensyn_get_last :
  assumes H: "gensyn_get t (k@[kl]) = Some t''"
  shows "\<exists> t' . (gensyn_get t k = Some (t' :: ('x) gensyn) \<and>
         gensyn_get t' [kl] = Some t'')"  using H
proof(induction k arbitrary: t kl t'')
  case Nil then show ?case by auto next
  case (Cons a k) then show ?case
  proof(cases t)
    case (G x l)
    hence 0: "gensyn_get (l ! a) (k@[kl]) = Some t''" using Cons gensyn_get_list_child G by auto
    hence 1: "\<exists> t' .  gensyn_get (l ! a) k = Some t' \<and> gensyn_get t' [kl] = Some t''" using Cons by auto
    hence 2: "a < length l" using Cons G gensyn_get_list_len by auto
    thus ?thesis using G gensyn_get_list_nth2 gensyn_get_list_child2 0 1 by auto blast+
  qed
qed

lemma gensyn_get_last2 :
  assumes H1: "gensyn_get t k = Some t'"
  and H2: "gensyn_get t' [kl] = Some t''"
shows "gensyn_get t (k@[kl]) = Some t''"  using H1 H2
proof(induction k arbitrary: t t' kl t'')
  case Nil
  then show ?case by auto next

  case (Cons a k)
  then show ?case
  proof(cases t)
    case (G x l)
    hence 0: "gensyn_get (l!a) (k) = Some t'" using Cons gensyn_get_list_child G by auto
    hence 1: "gensyn_get (l!a) (k@[kl]) = Some t''" using Cons by auto
    hence 2: "a < length l" using Cons G gensyn_get_list_len by auto
    show ?thesis using G gensyn_get_list_child2 0 1 2 by auto blast+
  qed
qed

lemma gensyn_get_comp :
  assumes H1: "gensyn_get t' p' = Some t''"
  assumes H2: "gensyn_get t p = Some t'"
  shows "gensyn_get t (p@p') = Some t''" using H1 H2
proof(induction p' arbitrary: t' t'' t p)
  case Nil
  then show ?case by auto
next
  case (Cons a' p')
  then show ?case
  proof(cases t') 
    case (G x l) (* thus ?thesis using Cons H1 H2 *)
    obtain tmid where 1: "gensyn_get t' [a'] = Some tmid \<and>
                 gensyn_get tmid p' = Some t''" using Cons gensyn_get_child by blast
    hence 2: "gensyn_get t (p @ [a']) = Some tmid" using Cons gensyn_get_last2 by blast
    hence 3: "gensyn_get t ((p @ [a']) @ p') = Some t''" 
        using Cons.IH[of tmid t'' t "p@[a']"] 1
        by auto
      show ?thesis using 3 by auto
    qed
  qed

lemma gensyn_get_comp2 :
  assumes H: "gensyn_get t (p1@p2) = Some t''"
  shows  "\<exists> t' . gensyn_get t p1 = Some t' \<and>
                 gensyn_get t' p2 = Some t''" using H
proof(induction p2 arbitrary: t p1 t'')
  case Nil
  then show ?case by auto
next
  case (Cons a k2t)
  hence 1: "gensyn_get t ((p1 @ [a])@k2t) = Some t''" by auto
  obtain t' where 2: "gensyn_get t (p1@[a]) = Some t' \<and>
                        gensyn_get t' k2t =
                        Some t''" using 1 Cons.IH[of t "p1@[a]" t''] by auto
  obtain t'2 where 3: "gensyn_get t p1 = Some t'2 \<and>
                        gensyn_get t'2 [a] = Some t'"
    using 2 gensyn_get_last[of t p1 a t'] by auto
  show ?case using 2 3 gensyn_get_child2 by auto blast+
qed

(* now we need to show compatibility with the inductive one *)
lemma gensyn_descend_eq_l2r :
  assumes H: "gensyn_get t (kh#kt) = Some t'"
  shows "gensyn_descend t t'(kh#kt)" using H
proof(induction kt arbitrary: t kh t')
  case Nil
  then show ?case
  proof(cases t)
    case (G x l)
    then show ?thesis 
      using Nil gensyn_descend.intros(1)[of kh l]
              gensyn_get_list_child[of l kh "[]" t'] by auto
  qed
next
  case (Cons a kt)
  then show ?case
  (* why do we need the rule here? *)
  proof(cases t rule:gensyn.exhaust)
    case (G x l)
    obtain tmid where 1 : "gensyn_get t [kh] = Some tmid \<and> gensyn_get tmid (a#kt) = Some t'"
      using gensyn_get_child[of t kh "a#kt" t'] Cons by auto
    have 2 : "gensyn_descend tmid t' (a#kt)" using Cons 1 by auto
    have 3: "gensyn_descend t tmid [kh]" using 1 G gensyn_descend.intros(1)[of kh l]
                                    gensyn_get_list_child[of l kh "[]" tmid]
      by auto
    thus ?thesis using 2 gensyn_descend.intros(2) by fastforce
  qed
qed

lemma ll3_descend_nonnil :
assumes H: "gensyn_descend t t' k"
shows "\<exists> hd tl . k = hd # tl" using H
proof(induction rule:gensyn_descend.induct)
  case 1 thus ?case by auto next
  case 2 thus ?case by auto
qed

lemma ll_descend_eq_r2l :
"gensyn_descend t t' k \<Longrightarrow>
gensyn_get t k = Some t'"
proof(induction rule:gensyn_descend.induct)
  case (1 c ls t x)
  then show ?case using gensyn_get_list_nth2 by auto next
  case (2 t t' n t'' n')
  then show ?case using gensyn_get_comp by fastforce
qed

lemma cp_next_list_nonnil :
  shows "\<And> cp cp' . gensyn_cp_next_list (l :: ('x) gensyn list) cp = Some cp' \<longrightarrow>
    (? cph' cpt' . cp' = cph' # cpt')"
proof(induction l rule:gensyn_induct')
  case (1 x l)
  then show ?case 
   proof(cases cp)
    case Nil then show ?thesis by auto next
    case (Cons a list) then show ?thesis
      apply(case_tac a) apply(clarsimp) apply(simp split:option.splits) apply(auto)
      done
  qed

next
  case 2
  then show ?case by auto
next
  case (3 t l)
  then show ?case
  proof(cases cp)
    case Nil
    then show ?thesis by auto
  next
    case (Cons a list)
    then show ?thesis using 3        
    proof(cases l)
        assume Nil' : "l=[]"
        then show ?thesis using Nil' Cons 3 by auto next

        fix lh ll
        assume Cons' : "l = lh#ll"
        then show ?thesis
        proof(cases a)
          case 0
          then show ?thesis using Cons Cons' 3 
            apply(case_tac t, auto)
            apply(auto split:option.splits)
            done
        next
          case (Suc nat)
          then show ?thesis using Cons Cons' 3
            apply(case_tac t, auto)
            apply(auto split:option.splits list.splits)
            done
        qed
        qed
      qed
qed


lemma gensyn_cp_next_list_lesser:
  
    assumes H: "a < length lt"
    shows "Some [Suc a] = gensyn_cp_next_list (lh # lt) [a]" using H
proof(induction a arbitrary: lt lh)
  case 0
  then show ?case
    apply(case_tac lt) apply(auto)
    apply(case_tac lh) apply(auto)
    apply(case_tac x2, auto)
    done
next
  case (Suc a)
  then show ?case
    apply(case_tac lt) apply(auto)
    done
qed

lemma gensyn_cp_next_list_greater:
    assumes H: "\<not> a < length lt"
    shows "None = gensyn_cp_next_list (lh # lt) [a]" using H
proof(induction a arbitrary: lt lh)
  case 0
  then show ?case
    apply(case_tac lt) apply(auto)
    apply(case_tac lh) apply(auto)
    apply(case_tac x2) apply(auto)
    done
next
  case (Suc a)
  then show ?case
    apply(case_tac lt) apply(auto)
    done
next
qed

(* TODO: finish this proof *)
(* problem - these are not actually the same
   the prime version returns None more often than
   the original version. however, it will only do so
for invalid paths, and we aren't using it for such
paths anyhow.
*)

(*
lemma gensyn_cp_next'_eq' :
  assumes H: "gensyn_get s (h#c) = Some s'"
  shows "gensyn_cp_next' s (h#c) = gensyn_cp_next s (h#c)" using H
proof(induction c arbitrary: s h s')
  case Nil
  then show ?case
  proof(cases s)
    case (GBase x11 x12)
    then show ?thesis by auto
  next
    case (GRec x21 x22 x23)
    then show ?thesis 
      apply(case_tac x23) apply(auto)
      apply(drule_tac gensyn_cp_next_list_lesser) apply(auto)
      apply(drule_tac gensyn_cp_next_list_greater) apply(auto)
      done
  qed
next
  case (Cons a c)
  then show ?case 
  proof(cases s)
    case (GBase x11 x12)
    then show ?thesis using Cons by auto
  next
    case (GRec x21 x22 x23)
    then show ?thesis
    proof(cases x23)
      assume Nil' : "x23 = []"
      then show ?thesis using Cons GRec by auto
    next
      fix h23 t23
      assume Cons' : "x23 = h23#t23"
      then show ?thesis
      proof(cases "rev c @ [a, h]")
        assume Nil'' : "rev c @ [a, h] = []"
        thus ?thesis by auto
      next
        fix rch rct
        assume Cons'' : "rev c @ [a, h] = rch # rct"
        thus ?thesis using Cons GRec Cons'
        proof(cases h)
          case 0
          print_cases
          then show ?thesis using Cons.prems Cons.IH[of h23 a s'] GRec Cons' Cons''
            apply(auto)
            apply(case_tac "rev c @ [a]") apply(auto)
        next
          case (Suc nat)
          then show ?thesis sorry
        qed
          apply(auto)
      qed
qed
*)

(* define and use an ordering on childpaths? *)
(* TODO: inductive version of this? *)
(* TODO: change definition of "less" for
childpaths to make prefixes less than suffixes? *)
fun cp_less_nilmax :: "childpath \<Rightarrow> childpath \<Rightarrow> bool"
  where
"cp_less_nilmax [] _ = False"
| "cp_less_nilmax (h#_) [] = True"
| "cp_less_nilmax (h1#t1) (h2#t2) = 
  (if h1<h2 then True
   else (if h1 = h2 then cp_less_nilmax t1 t2
   else False))"

fun cp_less_nilmin :: "childpath \<Rightarrow> childpath \<Rightarrow> bool"
  where
"cp_less_nilmin _ [] = False"
| "cp_less_nilmin [] (h#_) = True"
| "cp_less_nilmin (h1#t1) (h2#t2) = 
  (if h1<h2 then True
   else (if h1 = h2 then cp_less_nilmin t1 t2
   else False))"

fun cp_less :: "childpath \<Rightarrow> childpath \<Rightarrow> bool"
  where
"cp_less (h1#t1) (h2#t2) =
  (if h1 < h2 then True
    else (if h1 = h2 then cp_less t1 t2
    else False))"
| "cp_less _ _ = False"

lemma cp_next_less_minmax :
  "cp_less a b = (cp_less_nilmin a b \<and> cp_less_nilmax a b)"
proof(induction a arbitrary: b)
case Nil
then show ?case by auto
next
  case (Cons a1 a2)
  then show ?case 
  proof(cases b)
    assume Nil' : "b = []"
    thus ?thesis by auto
  next
    fix bh bt
    assume Cons' : "b = bh#bt"
    thus ?thesis using Cons by auto
  qed
qed

(*
lemma cp_less_get_genind :
  fixes t :: "('a, 'b, 'c) gensyn"
  and l :: "('a, 'b, 'c) gensyn list"
  shows
    "\<And> c d c' . gensyn_get t c = Some d \<Longrightarrow>
     cp_less c' c \<Longrightarrow>
     (\<exists> d' . gensyn_get t c' = Some d')"
  and
"\<And> c d c' . gensyn_get_list l c = Some d \<Longrightarrow>
     cp_less c' c \<Longrightarrow>
     (\<exists> d' . gensyn_get_list l c' = Some d')"
proof(induction t and l rule: gensyn_induct)
case (1 g b)
  then show ?case by (cases c, auto)
next
  case (2 g r l)
  then show ?case 
  proof (cases c)
    case Nil
    then show ?thesis using 2 by auto
  next
    case (Cons a list)
    then show ?thesis 
    proof(cases c')
      assume Nil' : "c' = []" thus ?thesis by auto
    next
      fix c'h c't
      assume Cons' : "c' = c'h#c't"
      thus ?thesis using Cons "2.prems" "2.IH"[of "a#list" d c'] by auto
    qed
  qed
next
  case 3
  then show ?case by (cases c, auto)
next
  case (4 t l)
  then show ?case 
  proof(cases c)
    case Nil
    then show ?thesis using 4 by auto
    next
  case (Cons a list)
  then show ?thesis 
  proof(cases a)
    case 0
    then show ?thesis
    proof(cases c')
      assume Nil' : "c' = []"
      then show ?thesis using 4 Cons 0 by auto
    next
      fix c'h c't
      assume Cons' : "c' = c'h#c't"
      then show ?thesis using "4.prems" "4.IH"(1)[of list d c't] Cons 0 
        by(cases c'h, auto)
    qed
  next
    case (Suc nat)
    then show ?thesis
    proof(cases c')
      assume Nil' : "c' = []"
      then show ?thesis using 4 Cons Suc by auto
    next
      fix c'h c't
      assume Cons' : "c' = c'h#c't"
      then show ?thesis
      proof(cases c'h)
        assume Zero' : "c'h = 0"
        then show ?thesis using "4.prems" "4.IH" Cons Suc Cons'
          apply(auto)
  qed
qed
qed
*)

(*
lemma gensyn_next_spec' :
(*  assumes H: "gensyn_cp_next' s c = Some c'"
  shows "cp_next_less c c' \<and>
         (! c'' . cp_next_less c c'' \<longrightarrow>
              ((? suf . c'' = c'@suf) \<or> cp_next_less c' c''))" using H *)
"(! s c' .
(gensyn_cp_next' (s :: ('a, 'b, 'c) gensyn) c = Some c' \<longrightarrow>
cp_less c c' \<and>
(! s' c'' . gensyn_get s c'' = Some (s' :: ('a, 'b, 'c) gensyn) \<longrightarrow>
        cp_less c c'' \<longrightarrow>
        (c'' = c' \<or> cp_less_nilmin c' c'')))
\<and>
(gensyn_cp_next' s c = None \<longrightarrow>
  (! s' c'' . gensyn_get s c'' = Some (s' :: ('a, 'b, 'c) gensyn) \<longrightarrow>
            \<not> cp_less c c''
            ))
)"

proof(induction "c")
  case Nil
  then show ?case by auto
next
  case (Cons a c)
  then show ?case
    apply(auto)
     apply(case_tac "rev c") apply(auto)
      apply(case_tac s, auto) apply(case_tac "Suc a < length x23", auto)


     apply(case_tac a, auto) apply(case_tac s, auto)
       apply(case_tac x23, auto)

    apply(case_tac "gensyn_get aaa (rev list)", auto)
       apply(case_tac ab, auto)
       apply(case_tac "Suc aa < length x23", auto)

        defer

        apply(drule_tac x = aaa in spec) apply(auto)
         apply(case_tac list, auto)

         apply(case_tac "gensyn_get aaa (rev listb)", auto)
         apply(drule_tac x = "ac" in spec)
         apply(drule_tac x = "rev listb" in spec)
         apply(auto)
           apply(case_tac ac, auto)
    apply(case_tac "Suc ab < length x23a", auto)

    apply(case_tac c', auto)

      apply(case_tac "gensyn_get lol (rev list)", auto)
      apply(rename_tac blah)
      apply(case_tac blah, auto)
      apply(case_tac "Suc aa < length x23") apply(auto)

       defer (* easy *)

    apply(case_tac list, auto)
       apply(case_tac hoo, auto)

      apply(frule_tac gensyn_get_comp2, auto)
       apply(case_tac t', auto)

       apply(case_tac " Suc aaa < length x23a", auto)

        defer



       apply(drule_tac spec) apply(drule_tac x = lol in spec)
    apply(auto)

       apply(drule_tac x = lol in spec, auto)


    apply(case_tac list, auto) apply(case_tac hoo, auto)

(* still stuck going in circles here *)
       apply(drule_tac spec) apply(auto)
       apply(drule_tac x = lol in spec, auto)
       apply(case_tac "gensyn_get lol (rev lista)", auto)
       apply(case_tac ab, auto)
    apply(case_tac "Suc aaa < length x23a") apply(auto)


    apply(drule_tac spec, auto)

    apply(drule_tac
qed
*)

lemma gensyn_cp_next_list_spec' [rule_format]:
  fixes s :: "('x) gensyn list"
  shows "! c c' c'' s'. 
        (gensyn_cp_next_list l c = Some c' \<longrightarrow>
         cp_less c c' \<and>
          (
               gensyn_get_list l c'' = Some s' \<longrightarrow>
               cp_less c c'' \<longrightarrow>
              (c''= c' \<or> cp_less_nilmin c' c'')))
        \<and>
        (gensyn_cp_next_list l c = None \<longrightarrow>
          gensyn_get_list l c'' = Some s' \<longrightarrow>
          \<not> cp_less c c'')"
proof(induction l rule:gensyn_induct')
  case (1 x l)
  then show ?case
    apply(clarsimp)
    apply(case_tac c, auto) apply(case_tac a, auto) apply(simp split:option.splits)
       apply(case_tac c') apply(auto)
     apply(case_tac c') apply(auto)
    apply(case_tac c'') apply(auto)

    apply(case_tac a, auto)
      apply(simp split:if_split_asm option.splits)
    apply(case_tac c'') apply(auto)
      apply(simp split:if_split_asm option.splits)
      apply(simp split:if_split_asm option.splits)
     apply(case_tac listb) apply(auto)

    apply(case_tac c'') apply(auto)
      apply(simp split:if_split_asm option.splits)
     apply(case_tac aa, auto)
apply(case_tac aa, auto)
      apply(simp split:if_split_asm option.splits)

    apply(case_tac lista) apply(auto)
    done
next
  case 2
  then show ?case by auto
next
  case (3 t l)
  then show ?case
    proof(cases l)
      case Nil
      then show ?thesis using 3
        apply(clarsimp) 
        done
  next
    case (Cons a list)
    then show ?thesis using 3
      apply(clarsimp)
      apply(case_tac t, clarsimp)
      apply(case_tac "gensyn_cp_next_list (G x1 x2 # a # list) c")

       apply(clarsimp)
       apply(case_tac c) apply(clarsimp) apply(clarsimp)
       apply(case_tac aa) apply(clarsimp) 
        apply(simp split:option.split_asm)
       apply(clarsimp)        
        apply(simp split:option.split_asm)

        apply(rotate_tac -3)
        apply(drule_tac x = "nat#lista" in spec)  apply(clarsimp)
        apply(case_tac c'') apply(clarsimp) apply(clarsimp)
        apply(simp split:if_split_asm)

         apply(case_tac aa) apply(clarsimp) apply(clarsimp)
         apply(rotate_tac -5) apply(drule_tac x = "nata#listaa" in spec)
         apply(clarsimp)

      apply(clarsimp)
         apply(rotate_tac -5) apply(drule_tac x = "nat#listaa" in spec)
        apply(clarsimp)

      apply(case_tac x2a) apply(clarsimp) 
         apply(rotate_tac 4) apply(drule_tac x = "nat#lista" in spec)
        apply(clarsimp)

      apply(case_tac x2a) apply(clarsimp) 
         apply(rotate_tac 4) apply(drule_tac x = "nat#lista" in spec)
        apply(clarsimp)

      apply(clarsimp)
       apply(case_tac c) apply(clarsimp) apply(clarsimp)
       apply(case_tac aa) apply(clarsimp) 
        apply(simp split:option.split_asm)
        apply(clarsimp)        
        apply(case_tac c'') apply(clarsimp) apply(clarsimp)
        apply(simp split:if_split_asm)

      apply(case_tac listaa) apply(clarsimp) apply(clarsimp)

      apply(clarsimp)
         apply(drule_tac x = "0#lista" in spec)
        apply(clarsimp)
      apply(rotate_tac -1)
        apply(drule_tac x = "0#listaa" in spec) apply(clarsimp)
      apply(case_tac listaa) apply(clarsimp) apply(clarsimp)

       apply(clarsimp)
         apply(drule_tac x = "0#lista" in spec)
        apply(clarsimp)
      apply(rotate_tac -1)
      apply(case_tac c'') apply(clarsimp) apply(clarsimp)
       apply(simp split:if_split_asm)
       apply(drule_tac x = "0#listaa" in spec) apply(clarsimp)
       apply(case_tac listaa) apply(clarsimp) apply(clarsimp)



      apply(clarsimp)
      apply(case_tac " gensyn_cp_next_list (a # list) (nat # lista)")
       apply(clarsimp)
      apply(clarsimp)
      apply(case_tac aa) apply(clarsimp) apply(clarsimp)
      apply(rotate_tac -3) apply(drule_tac x = "nat#lista" in spec) apply(clarsimp)
      apply(simp split:if_split_asm) apply(clarsimp)
       apply(case_tac c'') apply(clarsimp) apply(clarsimp)
       apply(simp split:if_split_asm) apply(clarsimp)
         apply(drule_tac x = "aa # listb" in spec) apply(clarsimp)

      apply(case_tac ab) apply(clarsimp) apply(clarsimp)
        apply(drule_tac x = "nata # listb" in spec) apply(clarsimp)

      apply(case_tac ab) apply(clarsimp) apply(clarsimp)
       apply(drule_tac x = "nata # listb" in spec) apply(clarsimp)

       apply(case_tac c'') apply(clarsimp) apply(clarsimp)
         apply(drule_tac x = "aa # listb" in spec) apply(clarsimp)
      done
  qed
qed


lemma cp_less_irref :
"\<not> cp_less c c"
proof(induction c, auto)
qed


lemma cp_less_irref2 :
"cp_less c c \<Longrightarrow> False"
proof(induction c, auto)
qed


lemma cp_less_last :
 "cp_less (c@[t]) (c@[Suc t])"
proof(induction c, auto)
qed

lemma cp_less_suf :
  assumes H: "cp_less c1 c2"
  shows "cp_less (c1@suf) c2" using H
proof(induction c1 arbitrary: c2 suf)
  case Nil
then show ?case by auto
next
  case (Cons a c1)
  then show ?case
    apply(case_tac c2, auto)
    apply(case_tac "a < aa", auto)
    done
qed

(*
lemma gensyn_next_spec :
  fixes s :: "('a, 'b, 'c) gensyn"
  and l :: "('a, 'b, 'c) gensyn list"
shows "! c c' c'' s'. 
         (gensyn_cp_next' s c = Some c' \<longrightarrow>
          cp_less c c' \<and>
         ( 
               gensyn_get s c'' = Some s' \<longrightarrow>
               cp_less c c'' \<longrightarrow>
              (c'' = c' \<or> cp_less_nilmin c' c'')))
          \<and>
          (gensyn_cp_next' s c = None \<longrightarrow>
          gensyn_get s c'' = Some s' \<longrightarrow>
          \<not> cp_less c c'')"
  and "! c c' c'' s' x1 x2. 
        (gensyn_cp_next' (GRec x1 x2 l) c = Some c' \<longrightarrow>
         cp_less c c' \<and>
          (
               gensyn_get_list l c'' = Some s' \<longrightarrow>
               cp_less c c'' \<longrightarrow>
              (c''= c' \<or> cp_less_nilmin c' c'')))
        \<and>
        (gensyn_cp_next (GRec x1 x2 l) c = None \<longrightarrow>
          gensyn_get_list l c'' = Some s' \<longrightarrow>
          \<not> cp_less c c'')"
proof(induction s and l rule:gensyn_induct)
case (1 g b)
  then show ?case
    apply(auto)
      apply(case_tac "rev c", auto)
      apply(case_tac "rev list", auto)

      apply(case_tac "rev c", auto)
     apply(case_tac "rev list", auto)

      apply(case_tac "rev c", auto)
    apply(case_tac "rev list", auto)

     apply(case_tac c'', auto)
    apply(case_tac c'', auto)
    done
next
  case (2 g r l)
 show ?case using "2.prems" apply(auto)
      apply(case_tac "rev c", auto)
     apply(case_tac "rev list", auto)
      apply(case_tac "Suc a < length l", auto)

     apply(case_tac " gensyn_get_list l (aa # lista)", auto)
     apply(case_tac ab, auto)
     apply(case_tac "Suc a < length x23", auto simp del:gensyn_cp_next'.simps)

   apply(rule_tac cp_less_last)

      apply(insert "2.IH")
      apply(drule_tac x = "aa#lista" in spec)
      apply(drule_tac x = "c'" in spec)
      apply(drule_tac x = "aa#lista" in spec)
      apply(drule_tac x = "GRec x21 x22 x23" in spec)
      apply(drule_tac x = g in spec) apply(drule_tac x = r in spec)
      apply(auto simp del:gensyn_cp_next'.simps)

         apply(drule_tac cp_less_suf, auto)
        apply(drule_tac cp_less_suf, auto)

       apply(drule_tac cp_less_irref2, auto)

        apply(drule_tac cp_less_suf, auto)

        apply(drule_tac cp_less_suf, auto)
   sorry
    

next
  case 3
  then show ?case 
    apply(auto)
    apply(case_tac "rev c", auto)
next
  case (4 t l)
  then show ?case sorry
qed
*)

end