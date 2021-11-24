theory Roalist
imports Oalist Linorder_Insts
begin
(* implementation of a recursive AList
   (i.e., ordered alist where values are ordered alists of the same type)
   this is needed for e.g. closures. *)

type_synonym closid = nat

type_synonym ('k, 'v) alist = "('k * 'v) list"

(* want 'v option here. problem - is this going to create issues for our data ordering? *)
(* 'd stores variable names (useful for representing closures *)
type_synonym ('k, 'v, 'd) roalist' =
  "(('k list) * ('v + 'd)) list"

(* also this lacks a canonical representation, I think *)
(*
type_synonym ('k, 'v) recclos =
  "(('k list), ('v + unit)) alist"
*)

(* old version that does not check validity *)

fun roalist_gather' :: "('k :: linorder, 'v, 'd) roalist' \<Rightarrow> 'k \<Rightarrow> ('k :: linorder, 'v, 'd) roalist'" where
"roalist_gather' [] _ = []"
| "roalist_gather' (([], vh)#l) k = roalist_gather' l k"
| "roalist_gather' (([kh], (Inl _))#l) k = roalist_gather' l k"
| "roalist_gather' (([kh], (Inr d))#l) k = 
  ( if k = kh then ([], Inr d)#roalist_gather' l k
    else roalist_gather' l k)"
| "roalist_gather' (((khh1#khh2#kht), vh)#l) k = 
  ( if k = khh1 then (khh2#kht, vh) # roalist_gather' l k
    else roalist_gather' l k)"

lemma roalist_gather'_elem :
  assumes Hord : "strict_order (map fst l)"
  assumes H : "(kt, v) \<in> set (roalist_gather' l kh)"
  shows "(kh#kt, v) \<in> set l" using Hord H
proof(induction l arbitrary: kh kt v)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then have Ord_tl : "strict_order (map fst l)" using strict_order_tl by auto
  obtain k1 v1 where H1 : "(a = (k1, v1))" by (cases a; auto)

  then show ?case
  proof(cases k1)
    assume Nil' : "k1 = []"
    then show ?thesis using Cons H1 Ord_tl by auto
  next
    fix h1 t1
    assume Cons' : "k1 = h1 # t1"
    then show ?thesis
    proof(cases t1)
      case Nil
      then show ?thesis  
      proof(cases v1)
        case (Inl a)
        then show ?thesis using Cons H1 Cons' Ord_tl Nil
          by(auto)
      next
        case (Inr b)  
        then show ?thesis
        proof(cases "h1 = kh")
          case False
          then show ?thesis using Cons H1 Cons' Nil Ord_tl Inr by(auto)
        next
          case True
          then show ?thesis using Cons.prems Cons.IH[OF Ord_tl] H1 Cons' Nil Inr
            by(auto)
        qed
      qed
    next
      fix h2 t2
      assume Cons'' : "t1 = h2#t2"
      then show ?thesis 
      proof(cases "h1 = kh")
        case False
        then show ?thesis using Cons H1 Cons' Cons'' Ord_tl by(auto)
      next
        case True
        then show ?thesis using Cons.prems Cons.IH[OF Ord_tl] H1 Cons' Cons'' by(auto)
      qed
    qed
  qed
qed

lemma roalist_gather'_elem'1 :
  assumes Hord : "strict_order (map fst l)"
  assumes H : "(kh1#kh2#kt, v) \<in> set l"
  shows "(kh2#kt, v) \<in> set (roalist_gather' l kh1)"
     using Hord H
proof(induction l arbitrary: kh1 kh2 kt v)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then have Ord_tl : "strict_order (map fst l)" using strict_order_tl by auto
  obtain k1 v1 where H1 : "(a = (k1, v1))" by (cases a; auto)

  show ?case
  proof(cases k1)
    assume Nil' : "k1 = []"
    then show ?thesis using Cons H1 Ord_tl by auto
  next
    fix h1 t1
    assume Cons' : "k1 = h1 # t1"
    then show ?thesis
    proof(cases t1)
      case Nil
      then show ?thesis  
      proof(cases v1)
        case (Inl a)
        then show ?thesis using Cons H1 Cons' Ord_tl Nil
          by(auto)
      next
        case (Inr b)  
        then show ?thesis
        proof(cases "h1 = kh1")
          case False
          then show ?thesis using Cons H1 Cons' Nil Ord_tl Inr by(auto)
        next
          case True
          then show ?thesis using Cons.prems Cons.IH[OF Ord_tl] H1 Cons' Nil Inr
            by(auto)
        qed
      qed
    next
      fix h2 t2
      assume Cons'' : "t1 = h2#t2"
      then show ?thesis 
      proof(cases "h1 = kh1")
        case False
        then show ?thesis using Cons H1 Cons' Cons'' Ord_tl by(auto)
      next
        case True
        then show ?thesis using Cons.prems Cons.IH[OF Ord_tl] H1 Cons' Cons'' by(auto)
      qed
    qed
  qed
qed

lemma roalist_gather'_elem'2 :
  assumes Hord : "strict_order (map fst l)"
  assumes H : "(kh1#kt, Inr d) \<in> set l"
  shows "(kt, Inr d) \<in> set (roalist_gather' l kh1)"
     using Hord H
proof(induction l arbitrary: kh1 kt)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then have Ord_tl : "strict_order (map fst l)" using strict_order_tl by auto
  obtain k1 v1 where H1 : "(a = (k1, v1))" by (cases a; auto)

  show ?case
  proof(cases k1)
    assume Nil' : "k1 = []"
    then show ?thesis using Cons H1 Ord_tl by auto
  next
    fix h1 t1
    assume Cons' : "k1 = h1 # t1"
    then show ?thesis
    proof(cases t1)
      case Nil
      then show ?thesis  
      proof(cases v1)
        case (Inl a)
        then show ?thesis using Cons H1 Cons' Ord_tl Nil
          by(auto)
      next
        case (Inr b)  
        then show ?thesis
        proof(cases "h1 = kh1")
          case False
          then show ?thesis using Cons H1 Cons' Nil Ord_tl Inr by(auto)
        next
          case True
          then show ?thesis using Cons.prems Cons.IH[OF Ord_tl] H1 Cons' Nil Inr
            by(auto)
        qed
      qed
    next
      fix h2 t2
      assume Cons'' : "t1 = h2#t2"
      then show ?thesis 
      proof(cases "h1 = kh1")
        case False
        then show ?thesis using Cons H1 Cons' Cons'' Ord_tl by(auto)
      next
        case True
        then show ?thesis using Cons.prems Cons.IH[OF Ord_tl] H1 Cons' Cons'' by(auto)
      qed
    qed
  qed
qed

lemma roalist_gather'_order :
  assumes Hord : "strict_order (map fst l)"
  shows "strict_order (map fst (roalist_gather' l k))" using Hord
proof(induction l arbitrary: k)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then have Ord_tl : "strict_order (map fst l)" using strict_order_tl by auto
  obtain k1 v1 where H1 : "(a = (k1, v1))" by (cases a; auto)
  show ?case
  proof(cases k1)
    case Nil
    then show ?thesis using H1 Cons.IH[OF Ord_tl] by(auto)
  next
    fix h1 t1
    assume Cons' : "k1 = h1 # t1"
    show ?thesis
    proof(cases t1)
      case Nil
      show ?thesis
      proof(cases v1)
        case (Inl a)
        then show ?thesis using Cons H1 Cons' Ord_tl Nil
          by(auto)
      next
        case (Inr b)  
        then show ?thesis using Cons H1 Cons' Nil Ord_tl Inr 
(* need an argument similar to cons case here. *)
        proof(cases "h1 = k")
          case False
          then show ?thesis using Cons H1 Cons' Nil Ord_tl Inr by(auto)
        next
          case True
          then show ?thesis
          proof(cases "map fst (roalist_gather' l k)")
            case Nil' : Nil
            then show ?thesis  using H1 Cons' Nil Inr True by(auto simp add:strict_order_def)
          next
            case Cons'' : (Cons h2 t2)
  
            hence Cons'''_in : "h2 \<in> set (map fst (roalist_gather' l k))" by auto
            then obtain v3 where H2 : "(h2, v3) \<in> set (roalist_gather' l k)" by(auto)
            have H2_l : "(k#h2, v3) \<in> set l"
              using roalist_gather'_elem[OF Ord_tl H2]  by auto
            then obtain idx where "idx < length l" "l ! idx = (k#h2, v3)" 
              unfolding in_set_conv_nth
              by auto
    
            then have Lt : "t1 < h2"
              using strict_order_unfold[OF Cons.prems, of "1 + idx" 0] H1 Cons' True
              by(auto simp add: list_lo_lt)
    
            show ?thesis using
              strict_order_cons[OF Lt]
              Cons.prems Cons.IH[OF Ord_tl, of k] H1 Cons' Cons'' Inr Nil True
              by(auto)
          qed
        qed
      qed
    next
      fix h2 t2
      assume Cons'' : "t1 = h2#t2"
      then show ?thesis
      proof(cases "h1 = k")
        case False
        then show ?thesis using Cons H1 Cons' Cons'' Ord_tl by(auto)
      next
        case True
        show ?thesis
        proof(cases "map fst (roalist_gather' l k)")
          case Nil
          then show ?thesis  using H1 Cons' Cons'' True by(auto simp add:strict_order_def)
        next
          fix h3 t3
          assume Cons''' : "map fst (roalist_gather' l k) = h3 # t3"
          hence Cons'''_in : "h3 \<in> set (map fst (roalist_gather' l k))" by auto
          then obtain v3 where H2 : "(h3, v3) \<in> set (roalist_gather' l k)" by(auto)
          have H2_l : "(k#h3, v3) \<in> set l"  (*roalist_gather'_elem[OF Ord_tl H2] by auto *)
            using roalist_gather'_elem[OF Ord_tl H2]  by auto
          then obtain idx where "idx < length l" "l ! idx = (k#h3, v3)" 
            unfolding in_set_conv_nth
            by auto
  
          then have Lt : "t1 < h3"
            using strict_order_unfold[OF Cons.prems, of "1 + idx" 0] H1 Cons' True
            by(auto simp add: list_lo_lt)
  
          show ?thesis using
            strict_order_cons[OF Lt]
            Cons.prems Cons.IH[OF Ord_tl, of k] H1 Cons' Cons'' Cons''' True
            by(auto)
        qed
      qed
    qed
  qed
qed


(*
lift_definition rc_gather :: "('k :: linorder, 'v) recclos \<Rightarrow> 'k \<Rightarrow> ('k, 'v) recclos"
is rc_gather'
(*
  sorry (* can't be bothered to show this now, but it's a rather obvious fact.
           probably need some more generalized induction *)
*)
(* so now (i think) we can just reuse the mergeable instance for oalist *)

(* need a lemma that relates rc_gather to mapping tail over the list of keys *)
proof-
  fix list :: "('k, 'v) recclos'"
  fix k :: "'k"
  assume H : "strict_order (map fst list)"
  show "strict_order (map fst (rc_gather' list k))" using H
  proof(induction list)
    case Nil
    then show ?case by(auto intro: strict_order_nil)
  next
    case (Cons a list)
    obtain kh vh where Hd : "a = (kh, vh)" by(cases a; auto)
    show ?case
    proof(cases kh)
      assume Nil' : "kh = []"
      show ?thesis using Cons Hd Nil' strict_order_tl by auto
    next
      fix khh kht
      assume Cons' : "kh = khh#kht"
      show ?thesis
      proof(cases "k = khh")
        case False
        then show ?thesis using Cons Hd Cons' strict_order_tl by auto
      next
        case True
        then show ?thesis
        proof(cases "map fst (rc_gather' list khh)")
          assume Nil'' : "map fst (rc_gather' list khh) = []"
          then show ?thesis using Cons Hd Cons' True by(auto simp add:strict_order_def)
        next
          fix a2 list2
          assume Cons'' : "map fst (rc_gather' list khh) = (a2#list2)"
          then have A2_in' : "a2 \<in> set (map fst (rc_gather' list khh))" by auto
          then obtain a2v where A2_in : "(a2, a2v) \<in> set (rc_gather' list khh)"
            by(auto)
          have Ord' : "strict_order (map fst list)" using strict_order_tl Cons.prems by auto
          have A2_in_orig : "(khh#a2, a2v) \<in> set list"
            using Cons Hd Cons' True Cons'' rc_gather'_elem[OF Ord' A2_in] by auto
          then obtain a2idx where "a2idx < length list" "list ! a2idx = (khh#a2, a2v)" 
            by (auto simp add: List.in_set_conv_nth)
          hence Conc_hd : "kht < a2" using strict_order_unfold[OF Cons.prems(1), of "1 + a2idx" 0] Cons Hd Cons' True Cons''
            by(auto simp add: list_lo_lt)
          then show ?thesis using Cons Hd Cons' True Cons'' Ord' strict_order_cons 
            by(auto)
        qed
      qed
    qed
  qed
qed
*)
fun roalist_get' :: "('k :: linorder, 'v, 'd) roalist' \<Rightarrow> 'k \<Rightarrow> ('v + ('d * ('k, 'v, 'd) roalist')) option" where
"roalist_get' r k =
  (case map_of r [k] of
    None \<Rightarrow> None
    | Some (Inl v) \<Rightarrow> Some (Inl v)
    | Some (Inr d) \<Rightarrow> Some (Inr (d, roalist_gather' r k)))"

(* delete a closure *)
fun roalist_delete_clos' :: "('k :: linorder) \<Rightarrow> ('k :: linorder, 'v, 'd) roalist' \<Rightarrow> ('k, 'v, 'd) roalist'" where
"roalist_delete_clos' _ [] = []"
| "roalist_delete_clos' k (([], vh)#t) = ([], vh)#roalist_delete_clos' k t"
| "roalist_delete_clos' k (((khh#kht), vh)#t) =
  (if k = khh then roalist_delete_clos' k t
   else ((khh#kht), vh)# roalist_delete_clos' k t)"

lemma strict_order_singleton :
  "strict_order [x]"
  by(auto simp add:strict_order_def)

lemma strict_order_consE :
  assumes H : "strict_order (h1 # h2 # l)"
  shows "h1 < h2"
  using strict_order_unfold[OF H, of 1 0] by auto

(*
lemma roalist_delete_clos'_elem :
  assumes Hord : "strict_order (map fst l)"
  assumes H : "(k', v) \<in> set (roalist_delete_clos' k l)"
  shows "(k', v) \<in> set l" using Hord H
proof(induction l arbitrary: k v)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then have Ord_tl : "strict_order (map fst l)" using strict_order_tl by auto
  obtain k1 v1 where H1 : "(a = (k1, v1))" by (cases a; auto)

  then show ?case
  proof(cases k1)
    assume Nil' : "k1 = []"
    then show ?thesis using Cons H1 Ord_tl by auto
  next
    fix h1 t1
    assume Cons' : "k1 = h1 # t1"
    then show ?thesis
    proof(cases "h1 = k")
      case False
      then show ?thesis using Cons H1 Cons' Ord_tl by(auto)
    next
      case True
      then show ?thesis using Cons.prems Cons.IH[OF Ord_tl] H1 Cons' by(auto)
    qed
  qed
qed

lemma roalist_delete_clos'_elem_contra :
  assumes Hord : "strict_order (map fst l)"
  assumes H : "(kh#kt, v) \<in> set l"
  assumes Hk : "(k \<noteq> kh)"
  shows "(kh#kt, v) \<in> set (roalist_delete_clos' k l)" using Hord H Hk
proof(induction l arbitrary: kh kt k v)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then have Ord_tl : "strict_order (map fst l)" using strict_order_tl by auto
  obtain k1 v1 where H1 : "(a = (k1, v1))" by (cases a; auto)
  then show ?case
  proof(cases k1)
    case Nil
    then show ?thesis using Cons H1 Ord_tl by(auto)
  next
    fix h1 t1
    assume Cons' : "k1 = h1 # t1"
    then show ?thesis
    proof(cases "h1 = k")
      case False
      then show ?thesis using Cons H1 Cons' Ord_tl by(auto)
    next
      case True
      then show ?thesis using Cons.prems Cons.IH[OF Ord_tl] H1 Cons' by(auto)
    qed
  qed  
qed
*)
(*
lemma roalist_delete_clos'_notelem1 :
  assumes Hord : "strict_order (map fst l)"
  assumes H1 : "(kh'#kt) \<notin> set (map fst (roalist_delete_clos' kh l))"
  assumes H2 : "kh \<noteq> kh'"
  shows "(kh'#kt) \<notin> set (map fst (roalist_delete_clos' kh l))" using Hord H1 H2
proof(induction l arbitrary: kh kh' kt)
  case Nil
  then show ?case  by auto
next
  case (Cons a l')
  then obtain ak av where Akv : "a = (ak, av)" by(cases a; auto)
  have Hord' : "strict_order (map fst l')" using Cons.prems strict_order_tl Akv by auto
  show ?case
  proof(cases ak)
    case Nil
    then show ?thesis using Cons Akv by(auto)
  next
    fix akh akt
    assume Cons' : "ak = akh#akt"
    show ?thesis
    proof(cases "akh = kh")
      case True
      then show ?thesis using Cons.prems Cons.IH[OF Hord'] Cons' Akv by(auto)
    next
      case False
      then show ?thesis using Cons.prems Cons.IH[OF Hord'] Cons' Akv by(auto)
    qed
  qed
qed
*)
(*
lemma roalist_delete_clos'_notelem2 :
  assumes Hord : "strict_order (map fst l)"
  shows "(kh#kt) \<notin> set (map fst (roalist_delete_clos' kh l))" using Hord
proof(induction l arbitrary: kh kt)
  case Nil
  then show ?case by auto
next
  case (Cons h t)
  obtain k1 v1 where Hkv1 : "h = (k1, v1)" by(cases h; auto)
  have Hord' : "strict_order (map fst t)" using strict_order_tl Cons.prems Hkv1 by auto
  then show ?case
  proof(cases "k1")
    case Nil
    then show ?thesis using Cons.IH[OF Hord', of kh kt] Hkv1 by(auto)
  next
    fix k1h k1t
    assume Cons' : "k1 = (k1h # k1t)"
    show ?thesis
    proof(cases "k1h = kh")
      case True
      then show ?thesis using Cons.prems Cons.IH[OF Hord'] Cons' Hkv1 by(auto)
    next
      case False
      then show ?thesis using Cons.prems Cons.IH[OF Hord'] Cons' Hkv1 by(auto)
    qed
  qed
qed
*)

fun roalist_update_v' :: "('key :: linorder) \<Rightarrow> 'value \<Rightarrow> ('key, 'value, 'd) roalist' \<Rightarrow> ('key, 'value, 'd) roalist'" where
"roalist_update_v' k v l =
  str_ord_update [k] (Inl v) (roalist_delete_clos' k l)"

(* unsafe because it doesn't check for presence of a value *)
fun roalist_update_clos_unsafe' :: "('key :: linorder) \<Rightarrow> ('key, 'value, 'd) roalist' \<Rightarrow> ('key, 'value, 'd) roalist' \<Rightarrow> ('key, 'value, 'd) roalist'" where
"roalist_update_clos_unsafe' k [] l = l"
| "roalist_update_clos_unsafe' k ((clkh,clvh)#clt) l =
   str_ord_update (k#clkh) clvh (roalist_update_clos_unsafe' k clt l)"

fun roalist_update_clos' :: "('key :: linorder) \<Rightarrow> 'd \<Rightarrow> ('key, 'value, 'd) roalist' \<Rightarrow> ('key, 'value, 'd) roalist' \<Rightarrow> ('key, 'value, 'd) roalist'"
  where
"roalist_update_clos' k d cl l =
  str_ord_update [k] (Inr d) (roalist_update_clos_unsafe' k cl (roalist_delete_clos' k l))"


(* cannot store a value and a closure at the same key *)

definition roalist_valid :: "('k :: linorder, 'v, 'd) roalist' \<Rightarrow> bool" where
"roalist_valid l =
  ((\<exists> d . map_of l [] = Some (Inr d)) \<and>
   (\<forall> pref v sufh suf . map_of l pref = Some (Inl v) \<longrightarrow>
            map_of l (pref@(sufh#suf)) = None) \<and>
   (\<forall> pref x sufh suf . map_of l (pref@(sufh#suf)) = Some x \<longrightarrow>
            (\<exists> d . map_of l pref = Some (Inr d))))"

lemma roalist_valid_intro :
  assumes H1 : "map_of l [] = Some (Inr x)"
  assumes H2 : "\<And> pref v sufh suf . map_of l pref = Some (Inl v) \<Longrightarrow> 
                                    map_of l (pref @ (sufh # suf)) = None"
  assumes H3 : "\<And> pref x sufh suf . map_of l (pref @ sufh # suf) = Some x \<Longrightarrow>
                                    (\<exists> d . map_of l pref = Some (Inr ()))"
  shows "roalist_valid l" using H1 H2 H3 unfolding roalist_valid_def
  by(blast)

(* TODO: bogus *)
typedef (overloaded) ('key, 'value, 'd) roalist =
  "{xs :: (('key :: linorder), 'value, 'd option) roalist' .
       strict_order (map fst xs) \<and> roalist_valid xs}"
  morphisms impl_of Oalist
proof
  show "[([], Inr None)]  \<in> 
          { rc :: (('key :: linorder), 'value, 'd option) roalist' . strict_order (map fst rc) \<and> roalist_valid rc }" 
    sorry
(*
  have C1: "strict_order (map fst ([([], Inr ())] :: ('key, 'value, 'd) roalist'))"
    by(auto simp add:strict_order_def)
  have C2 : "roalist_valid  ([([], Inr ())] :: ('key, 'value, 'd) roalist')"
  proof(rule roalist_valid_intro)
    show "map_of [([], Inr ())] [] = Some (Inr ())"
      by(auto)
  next
    fix pref suf :: "'key list"
    fix sufh :: "'key"
    fix v :: "'value"
    assume H : "map_of [([], Inr ())] pref = Some (Inl v)"
    show "map_of [([], Inr ())] (pref @ sufh # suf) = None"
      by(auto)
  next  
    fix pref suf :: "'key list"
    fix sufh :: "'key"
    fix x :: "'value + unit"
    assume H: "map_of [([], Inr ())] (pref @ sufh # suf) = Some x"
    then show "map_of [([], Inr ())] pref = Some (Inr ())"
      by(auto)
  qed
  show "[([], Inr ())]  \<in> 
          { rc :: (('key :: linorder), 'value) roalist' . strict_order (map fst rc) \<and> roalist_valid rc }" 
    using C1 C2 by auto
qed
*)
qed


setup_lifting type_definition_roalist
(*
lemma roalist_valid_elim1 :
  assumes Hv : "roalist_valid l"
  shows "map_of l [] = Some (Inr ())"
  using Hv unfolding roalist_valid_def by blast

lemma roalist_valid_elim2 :
  assumes Hv : "roalist_valid l"
  assumes H : "map_of l pref = Some (Inl v)"
  shows "map_of l (pref @ (sufh # suf)) = None"
  using Hv H unfolding roalist_valid_def by blast

lemma roalist_valid_elim3 :
  assumes Hv : "roalist_valid l"
  assumes H : "map_of l (pref @ (sufh#suf)) = Some x"
  shows "map_of l pref = Some (Inr ())"
  using Hv H unfolding roalist_valid_def by blast
*)

(* check if first argument is a prefix of the second *)
fun is_prefix :: "'k list \<Rightarrow> 'k list \<Rightarrow> bool" where
"is_prefix [] _ = True"
| "is_prefix (h#t) [] = False"
| "is_prefix (h1#t1) (h2#t2) =
   (if h1 = h2 then is_prefix t1 t2
    else False)"


lift_definition roalist_gather :: "('k :: linorder, 'v, 'd) roalist \<Rightarrow> 'k \<Rightarrow> ('k, 'v, 'd) roalist"
is roalist_gather' sorry


lift_definition roalist_update_v :: 
  "('key :: linorder) \<Rightarrow> 'value \<Rightarrow> ('key, 'value, 'd) roalist \<Rightarrow> ('key, 'value, 'd) roalist" 
is roalist_update_v' sorry

lift_definition roalist_update_clos ::
  "('key :: linorder) \<Rightarrow> 'd option \<Rightarrow> ('key, 'value, 'd) roalist \<Rightarrow> ('key, 'value, 'd) roalist \<Rightarrow> ('key, 'value, 'd) roalist" 
is roalist_update_clos' sorry
(*
lift_definition roalist_get ::
"('k :: linorder, 'v, 'd) roalist \<Rightarrow> 'k \<Rightarrow> ('v + ('d option * ('k, 'v, 'd) roalist)) option"
is roalist_get' sorry
*)

fun roalist_is_val' :: "('k :: linorder, 'v, 'd) roalist' \<Rightarrow> 'k \<Rightarrow> bool option" where
"roalist_is_val' r k =
  (case map_of r [k] of
    None \<Rightarrow> None
    | Some (Inl _) \<Rightarrow> Some True
    | Some (Inr _) \<Rightarrow> Some False)"

lift_definition roalist_is_val ::
  "('k :: linorder, 'v, 'd) roalist \<Rightarrow> 'k \<Rightarrow> bool option"
is roalist_is_val' .

fun roalist_get_v' :: "('k :: linorder, 'v, 'd) roalist' \<Rightarrow> 'k \<Rightarrow> 'v option" where
"roalist_get_v' l k =
  (case map_of l [k] of
    Some (Inl v) \<Rightarrow> Some v
    | _ \<Rightarrow> None)"


lift_definition roalist_get_v :: "('k :: linorder, 'v, 'd) roalist \<Rightarrow> 'k \<Rightarrow> 'v option"
is roalist_get_v' .

fun roalist_get_d' :: "('k :: linorder, 'v, 'd option) roalist' \<Rightarrow> 'k \<Rightarrow> 'd option" where
"roalist_get_d' l k =
  (case map_of l [k] of
    Some (Inr d) \<Rightarrow> d
    | _ \<Rightarrow> None)"

term "roalist_get_d'"

lift_definition roalist_get_d :: "('k :: linorder, 'v, 'd) roalist \<Rightarrow> 'k \<Rightarrow> 'd option"
is "roalist_get_d' :: ('k :: linorder, 'v, 'd option) roalist' \<Rightarrow> 'k \<Rightarrow> 'd option" .


fun roalist_get :: "('k :: linorder, 'v, 'd) roalist \<Rightarrow> 'k \<Rightarrow> 
  ('v + ('d option * ('k, 'v, 'd) roalist)) option"
  where
"roalist_get r k =
  (case roalist_get_v r k of
    Some v \<Rightarrow> Some (Inl v)
    | None \<Rightarrow> Some (Inr( (roalist_get_d r k), (roalist_gather r k))))"



fun roalist_update :: 
  "('key :: linorder) \<Rightarrow> ('value + ('key, 'value, 'd) roalist) \<Rightarrow> 
        ('key, 'value, 'd) roalist \<Rightarrow> ('key, 'value, 'd) roalist"
  where
"roalist_update k (Inl v) l = roalist_update_v k v l"
| "roalist_update k (Inr c) l = 
    (case roalist_get l k of
      Some (Inr (d, _)) \<Rightarrow> roalist_update_clos k d c l
      | _ \<Rightarrow> roalist_update_clos k None c l)"

(* idea
   given a key, make sure there is no value stored in any prefix *)
(* we also need a function to "fill in" missing prefixes
   that is, if there is nothing at a particular prefix, we must add it (?)
    (or, does validity handle this?)
*)
fun roalist_check_prefixes' :: "('key, 'value, 'd) roalist' \<Rightarrow> 'key list \<Rightarrow> bool" where
"roalist_check_prefixes' [] _ = True"
| "roalist_check_prefixes' ((kh, (Inr d))#t) k = roalist_check_prefixes' t k"
| "roalist_check_prefixes' ((kh, (Inl v))#t) k =
   (if is_prefix kh k then False
    else roalist_check_prefixes' t k)"


lift_definition roalist_empty :: "('k :: linorder, 'v, 'd) roalist"
is "[([], Inr None)]"
  by(auto simp add: strict_order_def roalist_valid_def)

fun roalist_map' :: "('k :: linorder list \<Rightarrow> 'v1 \<Rightarrow> 'v2) \<Rightarrow> 
                     ('k :: linorder list \<Rightarrow> 'd1 \<Rightarrow> 'd2) \<Rightarrow>
                     ('k :: linorder, 'v1, 'd1 option) roalist' \<Rightarrow> 
                     ('k :: linorder, 'v2, 'd2 option) roalist'" where
"roalist_map' fv fd [] = []"
| "roalist_map' fv fd ((kh, Inl vh)#t) =
    ((kh, Inl (fv kh vh))#roalist_map' fv fd t)"
| "roalist_map' fv fd ((kh, Inr None)#t) =
    ((kh, Inr None)# roalist_map' fv fd t)"
| "roalist_map' fv fd ((kh, Inr (Some d))#t) =
    ((kh, Inr (Some (fd kh d)))#roalist_map' fv fd t)"

lift_definition roalist_map :: 
"('k :: linorder list \<Rightarrow> 'v1 \<Rightarrow> 'v2) \<Rightarrow> 
 ('k :: linorder list \<Rightarrow> 'd1 \<Rightarrow> 'd2) \<Rightarrow>
 ('k :: linorder, 'v1, 'd1) roalist \<Rightarrow> 
 ('k :: linorder, 'v2, 'd2) roalist"
is roalist_map' sorry

fun roalist_keys' :: "('k :: linorder, 'v, 'd) roalist' \<Rightarrow>
                      ('k :: linorder) list list" where
"roalist_keys' r = map fst r"

lift_definition roalist_keys :: "('k :: linorder, 'v, 'd) roalist \<Rightarrow>
                                 ('k :: linorder) list list"
is roalist_keys' .

(* problem - need a way of figuring out how to deal with weird cases around
e.g. what if roalist elements at same keys have different value types?
(values vs closures)
etc
*)

(* used in defining liftings for roalist *)
(* idea. we start with a list of values to lift,
   as well as a "current" list of values we are updating.
   this works like map2, except that
   if we ever encounter a type mismatch or key mismatch,
   we use a default value instead *)
(*
proving correctness could end up being annoying
*)
(* this has been moved to LiftInstances, since it is
easier to express in terms of liftings *)
(*
fun roalist_fuse2_safe' ::
"('k :: linorder list \<Rightarrow> 'v1 \<Rightarrow> 'v2 \<Rightarrow> 'v2) \<Rightarrow> 
 ('k :: linorder list \<Rightarrow> 'd1 \<Rightarrow> 'd2 \<Rightarrow> 'd2) \<Rightarrow>
                     ('k :: linorder, 'v1, 'd1 option) roalist' \<Rightarrow> 
                     ('k :: linorder, 'v2, 'd2 option) roalist' \<Rightarrow>
                     ('k :: linorder, 'v2, 'd2 option) roalist'" where
"roalist_fuse2_safe' fv fd [] [] = Some []"
| "roalist_map2_safe' fv fd ((kh1, Inl vh1)#t1) ((kh2, Inl vh2)#t2) =
  (if kh1 = kh2 then 
    (case roalist_map2_safe' fv fd t1 t2 of
     Some t3 \<Rightarrow> Some ((kh1, Inl (fv kh1 vh1 vh2))#t3)
     | _ \<Rightarrow> None)
   else None)"
| "roalist_map2_safe' fv fd ((kh1, Inr None)#t1) ((kh2, Inr None)#t2) =
    (if kh1 = kh2 then
      (case roalist_map2_safe' fv fd t1 t2 of
       Some t3 \<Rightarrow> Some ((kh1, Inr None)#t3)
       | _ \<Rightarrow> None)
    else None)"
| "roalist_map2_safe' fv fd ((kh1, Inr (Some dh1))#t1) ((kh2, Inr (Some dh2))#t2) =
    (if kh1 = kh2 then
      (case roalist_map2_safe' fv fd t1 t2 of
       Some t3 \<Rightarrow> Some ((kh1, Inr (Some (fd kh1 dh1 dh2)))#t3)
       | _ \<Rightarrow> None)
    else None)"
| "roalist_map2_safe' _ _ _ _ = None"

lift_definition roalist_map2_safe :: 
"('k :: linorder list \<Rightarrow> 'v1 \<Rightarrow> 'v2 \<Rightarrow> 'v3) \<Rightarrow> 
 ('k :: linorder list \<Rightarrow> 'd1 \<Rightarrow> 'd2 \<Rightarrow> 'd3) \<Rightarrow>
 ('k :: linorder, 'v1, 'd1) roalist \<Rightarrow> 
 ('k :: linorder, 'v2, 'd2) roalist \<Rightarrow>
 ('k :: linorder, 'v3, 'd3) roalist option"
is roalist_map2_safe'
  apply(simp add: pred_option_def set_option_def)
*)

end