theory Lifter_idem
 imports  "../Mergeable/Mergeable_Instances" "../Mergeable/Mergeable_Oalist" "../Mergeable/Mergeable_Roalist" "../Mergeable/Mono"
begin

(* When we lift syntaxes we reverse the function arrow *)
type_synonym ('a, 'b) syn_lifting = "('b \<Rightarrow> 'a)"

(*
datatype ('syn, 'a, 'b) lifting =
  LMake  (LUpd : "('syn \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b)")
         (LOut : "('syn \<Rightarrow> 'b \<Rightarrow> 'a)")
         (LBase : "('syn \<Rightarrow> 'b)")
*)

(*
"mappable" typeclass?
*)

(* need a generic way to talk about things over which LMap makes sense.

*)

datatype ('syn, 'a, 'b, 'f) lifting =
  LMake  (LUpd_Idem : "('syn \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b)")
         (LPost : "('syn \<Rightarrow> 'b \<Rightarrow> 'b)")
         (LOut : "('syn \<Rightarrow> 'b \<Rightarrow> 'a)")
         (LBase : "('syn \<Rightarrow> 'b)")
         (LFD : "'f \<Rightarrow> 'syn \<Rightarrow> 'a \<Rightarrow> 'a")

type_synonym ('syn, 'a, 'b) lifting' =
  "('syn, 'a, 'b, 'syn \<Rightarrow> 'a \<Rightarrow> 'a) lifting"

definition LUpd ::
  "('syn, 'a, 'b, 'f) lifting \<Rightarrow> 'syn \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" where
"LUpd l s a b =
  LPost l s (LUpd_Idem l s a b)"


definition LMap_Idem ::
  "('x, 'a, 'b, 'f) lifting \<Rightarrow> 'f \<Rightarrow> ('x \<Rightarrow> 'b \<Rightarrow> 'b)" where
"LMap_Idem l f s b =
  LUpd_Idem l s (LFD l f s (LOut l s b)) b"

definition LMap ::
  "('x, 'a, 'b, 'f) lifting \<Rightarrow> 'f \<Rightarrow> ('x \<Rightarrow> 'b \<Rightarrow> 'b)" where
"LMap l f s b =
  LUpd l s (LFD l f s (LOut l s b)) b"


definition LNew :: "('syn, 'a, 'b, 'f) lifting \<Rightarrow> 'syn \<Rightarrow> 'a \<Rightarrow> 'b"  where
"LNew l s a = LUpd l s a (LBase l s)"

(* TODO: make sure this is a good idea. *)
declare LNew_def [simp]
declare LMap_def [simp]
declare LMap_Idem_def [simp]
declare LUpd_def [simp]

type_synonym ('syn, 'b) valid_set =
"'syn \<Rightarrow> 'b set"

(* liftings can have several kinds of validity properties, only some of
   which depend on others.
*)

(* TODO: for inference purposes we are probably going to
 * still have to use something like our current formulation. *)

class Okay =
  fixes ok_S :: "('a) set"


instantiation md_triv :: (_) Okay
begin
definition triv_ok_S : "(ok_S :: 'a md_triv set) = UNIV"
instance proof
qed
end

instantiation md_prio :: (Okay) Okay
begin
definition prio_ok_S : "(ok_S :: 'a md_prio set) = ({x . \<exists> px vx . x = mdp vx px \<and> px \<in> ok_S})"
instance proof qed
end

instantiation option :: (Okay) Okay
begin
definition option_ok_S : "(ok_S :: 'a option set) = (Some ` ok_S)"
instance proof qed
end

instantiation prod :: (Okay, Okay) Okay
begin
definition prod_ok_S : "(ok_S :: ('a * 'b) set) = { x :: 'a * 'b . \<exists> a' b' . x = (a', b') \<and> a' \<in> ok_S \<and> b' \<in> ok_S}"
instance proof qed
end

instantiation oalist :: (linorder, Okay) Okay
begin

definition oalist_ok_S :
  "(ok_S :: ('a, 'b) oalist set) = { x  :: ('a, 'b) oalist . oalist_all_val (\<lambda> y . y \<in> ok_S) x }"
instance proof qed
end

instantiation unit :: Okay
begin
definition unit_ok_S :
  "(ok_S :: unit set) = UNIV"
instance proof qed
end

locale lifting_valid_weak =
  fixes l :: "('syn, 'a, 'b :: Pord_Weak, 'f) lifting"
  fixes S :: "('syn, 'b) valid_set"
  assumes put_get : "\<And> s a b . LOut l s (LUpd_Idem l s a b) = a"
  assumes post_nop : "\<And> s b . LOut l s (LPost l s b) = LOut l s b"
  assumes put_S : "\<And> s a b . LUpd_Idem l s a b \<in> S s"
  assumes post_S : "\<And> s b . b \<in> S s \<Longrightarrow> LPost l s b \<in> S s"
  assumes post_geq : "\<And> s b . b <[ LPost l s b"
  assumes get_put_weak : "\<And> s b . b \<in> S s \<Longrightarrow> b = LUpd_Idem l s (LOut l s b) b"
  

locale lifting_putonly =
  fixes l :: "('syn, 'a, 'b :: Pord_Weak, 'f) lifting"
  fixes S :: "('syn, 'b) valid_set"
  assumes put_S : "\<And> s a b . LUpd l s a b \<in> S s"

(* TODO reexamine this *)
locale lifting_presonly =
  fixes l :: "('syn, 'a, 'b :: Pord_Weak, 'f) lifting"
  fixes S :: "('syn, 'b) valid_set"
  assumes pres :
    "\<And> v V supr f s . 
         v \<in> V \<Longrightarrow>
         V \<subseteq> S s \<Longrightarrow>
         is_sup V supr \<Longrightarrow> supr \<in> S s \<Longrightarrow> is_sup (LMap_Idem l f s ` V) (LMap_Idem l f s supr)"
  assumes pres_post :
    "\<And> v V supr s .
      v \<in> V \<Longrightarrow>
      V \<subseteq> S s \<Longrightarrow>
      is_sup V supr \<Longrightarrow>
      supr \<in> S s \<Longrightarrow>
      is_sup (LPost l s ` V) (LPost l s supr)"
    

(* reduced version of lifting-valid, for use with
 * improper merges (when using merge_l as a tool for combining
 * semantics) *)
locale lifting_valid_presonly =
  lifting_putonly + lifting_presonly

locale lifting_valid = lifting_valid_weak +
  assumes put_put : "\<And> s a1 a2 b . LUpd_Idem l s a1 (LUpd_Idem l s a2 b) = LUpd_Idem l s a1 b"

locale lifting_valid_weak_base = lifting_valid_weak +
  assumes base : "\<And> s . LBase l s = \<bottom>"

locale lifting_valid_base = lifting_valid + lifting_valid_weak_base

locale lifting_valid_weak_ok = lifting_valid_weak +
  assumes ok_S_valid : "\<And> s . ok_S \<subseteq> S s"
  assumes ok_S_put : "\<And> s a b . b \<in> ok_S \<Longrightarrow> LUpd_Idem l s a b \<in> ok_S"
  assumes ok_S_post : "\<And> s b . b \<in> ok_S \<Longrightarrow> LPost l s b \<in> ok_S"

locale lifting_valid_ok = lifting_valid + lifting_valid_weak_ok

locale lifting_valid_weak_base_ok = lifting_valid_weak_ok + lifting_valid_weak_base

locale lifting_valid_base_ok = lifting_valid_ok + lifting_valid_base

locale lifting_valid_weak_pres = lifting_valid_weak +
  lifting_presonly
(*
sublocale lifting_valid_weak_pres \<subseteq> lifting_valid_presonly
proof
  show "\<And>s a b. LUpd l s a b \<in> S s"
    using put_S by auto
next
  show "\<And>v V supr f s.
       v \<in> V \<Longrightarrow>
       V \<subseteq> S s \<Longrightarrow>
       is_sup V supr \<Longrightarrow>
       supr \<in> S s \<Longrightarrow>
       is_sup (LMap l f s ` V)
        (LMap l f s supr)"
    using pres 
    by auto
qed
*)

locale lifting_valid_pres = lifting_valid + lifting_valid_weak_pres

locale lifting_valid_weak_base_pres = lifting_valid_weak_pres + lifting_valid_weak_base +
  assumes bot_bad : "\<And> s . \<bottom> \<notin> S s"

locale lifting_valid_base_pres = lifting_valid_pres + lifting_valid_weak_base_pres

locale lifting_valid_weak_ok_pres = lifting_valid_weak_pres + lifting_valid_weak_ok

locale lifting_valid_ok_pres = lifting_valid_pres + lifting_valid_ok

locale lifting_valid_weak_base_ok_pres =
  lifting_valid_weak_base_pres + lifting_valid_weak_base_ok

(* generally we are assuming we won't be using ok and pres separately.
 * we could if we wanted to though. *)
locale lifting_valid_base_ok_pres =
  lifting_valid_base_pres + lifting_valid_base_ok

(* orthogonality, used to define merge correctness *)
(*
these were originally pord_weak, but this was
(i think) insufficient to prove fst_l_ortho;
the strengthening to pord shouldn't be an issue though.
*)
locale l_ortho' =
  fixes l1 :: "('a, 'b1, 'c :: Pord, 'f1) lifting"
  fixes S1 :: "'a \<Rightarrow> 'c set"
  fixes l2 :: "('a, 'b2, 'c :: Pord, 'f2) lifting"
  fixes S2 :: "'a \<Rightarrow> 'c set"

(* need set membership constraints. *)
locale l_ortho =
  l_ortho' +

  assumes eq_base : "\<And> s . LBase l1 s = LBase l2 s"
  assumes compat_idem : "\<And> s a1 a2 b1 b2 supr .  
    is_sup {b1, b2} supr \<Longrightarrow>
    has_sup {LUpd_Idem l1 s a1 b1, LUpd_Idem l2 s a2 b2}"

  assumes compat_post : "\<And> b1 b2 s supr . is_sup {b1, b2} supr \<Longrightarrow> has_sup {LPost l1 s b1, LPost l2 s b2}"

  assumes compat_idem_S : "\<And> s a1 a2 b1 b2 supr0 supr . 
      is_sup {b1, b2} supr0 \<Longrightarrow>
      is_sup {LUpd_Idem l1 s a1 b1, LUpd_Idem l2 s a2 b2} supr \<Longrightarrow>
                        supr \<in> (S1 s \<inter> S2 s)"

  assumes compat_post_S : "\<And> s b1 b2 supr0 supr .
        is_sup {b1, b2} supr0 \<Longrightarrow>
        supr0 \<in> S1 s \<Longrightarrow>
        supr0 \<in> S2 s \<Longrightarrow>
        is_sup {LPost l1 s b1, LPost l2 s b2} supr \<Longrightarrow>
        supr \<in> (S1 s \<inter> S2 s)"

  assumes compat_idem_get1 : 
      "\<And> s a1 a2 b1 b2 supr0 supr .
         is_sup {b1, b2} supr0 \<Longrightarrow>
         is_sup {LUpd_Idem l1 s a1 b1, LUpd_Idem l2 s a2 b2} supr \<Longrightarrow>
                        LOut l1 s supr = a1"
  
    assumes compat_idem_get2 : "\<And> s a1 a2 b1 b2 supr0 supr . 
         is_sup {b1, b2} supr0 \<Longrightarrow>
          is_sup {LUpd_Idem l1 s a1 b1, LUpd_Idem l2 s a2 b2} supr \<Longrightarrow>
                        LOut l2 s supr = a2"

  assumes compat_post_get1 : "\<And> s b1 b2 supr0 supr . 
     is_sup {b1, b2} supr0 \<Longrightarrow>
     is_sup {LPost l1 s b1, LPost l2 s b2} supr \<Longrightarrow>
      LOut l1 s supr = LOut l1 s supr0"
  
  assumes compat_post_get2 : "\<And> s b1 b2 supr0 supr . 
    is_sup {b1, b2} supr0 \<Longrightarrow>
    is_sup {LPost l1 s b1, LPost l2 s b2} supr \<Longrightarrow>
        LOut l2 s supr = LOut l2 s supr0"

  assumes put1_S2 : "\<And> s a b . b \<in> S2 s \<Longrightarrow> LUpd_Idem l1 s a b \<in> S2 s"
  assumes put2_S1 : "\<And> s a b . b \<in> S1 s \<Longrightarrow> LUpd_Idem l2 s a b \<in> S1 s"

(* TODO: this feels weird*)
locale l_ortho_strong = l_ortho +
  assumes compat_put_put :
    "\<And> s x1 x2 y1 y2 b1 b2 supr0 supr1 supr2 supr3.
      is_sup {b1, b2} supr0 \<Longrightarrow>
      is_sup {LUpd_Idem l1 s y1 b1, LUpd_Idem l2 s y2 b2} supr1 \<Longrightarrow>
      is_sup {LUpd_Idem l1 s x1 supr1, LUpd_Idem l2 s x2 supr1} supr2 \<Longrightarrow>
      is_sup {LUpd_Idem l1 s x1 b1, LUpd_Idem l2 s x2 b2} supr3 \<Longrightarrow>
      supr2 = supr3"

lemma (in l_ortho) compat :
  fixes s a1 a2 b1 b2 supr
  assumes Supr : "is_sup {b1, b2} supr"
  shows "has_sup {LUpd l1 s a1 b1, LUpd l2 s a2 b2}"
proof-

  obtain supr' where Supr' : "is_sup {LUpd_Idem l1 s a1 b1, LUpd_Idem l2 s a2 b2} supr'"
    using compat_idem[OF Supr]
    by(fastforce simp add: has_sup_def)

  show "has_sup {LUpd l1 s a1 b1, LUpd l2 s a2 b2}"
    using compat_post[OF Supr']
    unfolding LUpd_def
    by(auto)
qed

lemma (in l_ortho) compat_get1 :
  fixes s a1 a2 b1 b2 supr0 supr
  assumes Supr0 : "is_sup {b1, b2} supr0"
  assumes Supr : "is_sup {LUpd l1 s a1 b1, LUpd l2 s a2 b2} supr"
  shows "LOut l1 s supr = a1"
proof-

  obtain supr' where Supr' : "is_sup {LUpd_Idem l1 s a1 b1, LUpd_Idem l2 s a2 b2} supr'"
    using compat_idem[OF Supr0]
    by(fastforce simp add: has_sup_def)

  have "LOut l1 s supr' = a1"
    using compat_idem_get1[OF Supr0 Supr']
    by auto

  then show "LOut l1 s supr = a1"
    using compat_post_get1[OF Supr'] Supr
    unfolding LUpd_def
    by(auto simp add: LUpd_def)
qed

lemma (in l_ortho) compat_get2 :
  fixes s a1 a2 b1 b2 supr0 supr
  assumes Supr0 : "is_sup {b1, b2} supr0"
  assumes Supr : "is_sup {LUpd l1 s a1 b1, LUpd l2 s a2 b2} supr"
  shows "LOut l2 s supr = a2"
proof-

  obtain supr' where Supr' : "is_sup {LUpd_Idem l1 s a1 b1, LUpd_Idem l2 s a2 b2} supr'"
    using compat_idem[OF Supr0]
    by(fastforce simp add: has_sup_def)

  have "LOut l2 s supr' = a2"
    using compat_idem_get2[OF Supr0 Supr']
    by auto

  then show "LOut l2 s supr = a2"
    using compat_post_get2[OF Supr'] Supr
    unfolding LUpd_def
    by(auto simp add: LUpd_def)
qed

lemma (in l_ortho) compat_S :
  fixes s a1 a2 b1 b2 supr0 supr
  assumes Supr0 : "is_sup {b1, b2} supr0"
  assumes Supr : "is_sup {LUpd l1 s a1 b1, LUpd l2 s a2 b2} supr"
  shows "supr \<in> S1 s \<inter> S2 s"
proof-
   obtain supr' where Supr' : "is_sup {LUpd_Idem l1 s a1 b1, LUpd_Idem l2 s a2 b2} supr'"
     using compat_idem[OF Supr0]
     by(fastforce simp add: has_sup_def)

  have Supr'_in : "supr' \<in> S1 s" "supr' \<in> S2 s"
    using compat_idem_S[OF Supr0 Supr']
    by auto

  obtain supr'2 where Supr'2 : "is_sup {LPost l1 s (LUpd_Idem l1 s a1 b1), LPost l2 s (LUpd_Idem l2 s a2 b2)} supr'2"
    using compat_post[OF Supr']
    by(fastforce simp add: has_sup_def)

  have Supr'2_supr : "supr'2 = supr"
    using is_sup_unique[OF Supr[unfolded LUpd_def] Supr'2]
    by simp

  show "supr \<in> S1 s \<inter> S2 s"
    using compat_post_S[OF Supr' Supr'_in(1) Supr'_in(2) Supr'2]
    unfolding Supr'2_supr
    by auto
qed

locale l_ortho_base' =
  fixes l1 :: "('a, 'b1, 'c :: Pord_Weakb, 'f1) lifting"
  fixes l2 :: "('a, 'b2, 'c, 'f2) lifting"

locale l_ortho_base = l_ortho + l_ortho_base' +
  assumes compat_bases : "\<And> s . is_sup {LBase l1 s, LBase l2 s} \<bottom>"

locale l_ortho_ok' =
  fixes l1 :: "('a, 'b1, 'c :: {Pord_Weakb, Okay}, 'f1) lifting"
  fixes l2 :: "('a, 'b2, 'c, 'f2) lifting"

locale l_ortho_ok = l_ortho + l_ortho_ok' +
  assumes compat_idem_ok :
    "\<And> s a1 a2 b supr . b \<in> ok_S \<Longrightarrow> 
    is_sup {LUpd_Idem l1 s a1 b, LUpd_Idem l2 s a2 b} supr \<Longrightarrow> supr \<in> ok_S"
  assumes compat_post_ok :
    "\<And> s b supr . b \<in> ok_S \<Longrightarrow>
    is_sup {LPost l1 s b, LPost l2 s b} supr \<Longrightarrow> supr \<in> ok_S"
  

(* lift_map_s is LMap plus a syntax translation *)
definition lift_map_s ::
  "('b1 \<Rightarrow> 'a1) \<Rightarrow>
   ('a1, 'a2, 'b2 :: Pord, 'f) lifting \<Rightarrow>
   'f \<Rightarrow>
   ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2)" where
"lift_map_s l' l sem syn st =
  LMap l sem (l' syn) st"


(* commutativity of l_ortho *)
sublocale l_ortho \<subseteq> comm :
  l_ortho l2 S2 l1 S1
proof

  fix s
  show "LBase l2 s = LBase l1 s"
    using eq_base by auto
next

  fix s a1 a2 b1 b2 supr

  have Comm : "{LUpd_Idem l2 s a1 b1, LUpd_Idem l1 s a2 b2} = 
               {LUpd_Idem l1 s a2 b2, LUpd_Idem l2 s a1 b1}"
    by auto

  have Comm' : "{b1, b2} = {b2, b1}"
    by auto

  assume "is_sup {b1, b2} supr"
  then have "has_sup {b2, b1}" unfolding Comm' by auto

  then show "has_sup
        {LUpd_Idem l2 s a1 b1,
         LUpd_Idem l1 s a2 b2}"
    using compat_idem[of b2 b1 s a2 a1]
    unfolding Comm
    by auto

next
  fix s
  fix b1 b2 :: 'c

  have Comm : "{LPost l2 s b1, LPost l1 s b2} = {LPost l1 s b2, LPost l2 s b1}"
    by auto

  have Comm' : "{b1, b2} = {b2, b1}"
    by auto

  assume Sup : "has_sup {b1, b2}"

  then show "has_sup {LPost l2 s b1, LPost l1 s b2}"
    using compat_post[OF Sup[unfolded Comm']] unfolding Comm 
    by auto
next
  fix b s a1 a2
  fix b1 b2 supr :: 'c

  have Comm' : "{b1, b2} = {b2, b1}"
    by auto

  have Comm: "{LUpd_Idem l2 s a1 b1, LUpd_Idem l1 s a2 b2} = {LUpd_Idem l1 s a2 b2, LUpd_Idem l2 s a1 b1}"
    by auto

  assume Sup_b : "has_sup {b1, b2}"
  assume Sup : "is_sup {LUpd_Idem l2 s a1 b1, LUpd_Idem l1 s a2 b2} supr"

  then show "supr \<in> S2 s \<inter> S1 s"
    using compat_S[OF Sup_b[unfolded Comm'] Sup[unfolded Comm]]
    by auto

next

  fix s a b

  show "b \<in> S1 s \<Longrightarrow>
       LUpd_Idem l2 s a b \<in> S1 s"
    using put2_S1[of b s a]
    by auto
next

  fix s a b

  show "b \<in> S2 s \<Longrightarrow>
       LUpd_Idem l1 s a b \<in> S2 s"
    using put1_S2[of b s a]
    by auto
qed

sublocale l_ortho_base \<subseteq> comm :
  l_ortho_base l2 S2 l1 S1
proof
  fix s

  have Comm : "{LBase l2 s, LBase l1 s} = {LBase l1 s, LBase l2 s}"
    by auto

  show "is_sup {LBase l2 s, LBase l1 s} \<bottom>"
    using compat_bases unfolding Comm
    by auto
qed

sublocale l_ortho_ok \<subseteq> comm :
  l_ortho_ok l2 S2 l1 S1
proof
  fix s a1 a2 b supr

  assume Sup : "is_sup {LUpd l2 s a1 b, LUpd l1 s a2 b} supr"

  assume Bok : "b \<in> ok_S"

  have Comm : "{LUpd l2 s a1 b, LUpd l1 s a2 b} = 
               {LUpd l1 s a2 b, LUpd l2 s a1 b}"
    by auto

  show "supr \<in> ok_S"
    using compat_ok[OF Bok Sup[unfolded Comm]]
    by auto
qed
(*
lemma (in l_ortho) compat'_comm :
  shows "LUpd l1 s a1 (LUpd l2 s a2 b) = LUpd l2 s a2 (LUpd l1 s a1 b)"
  using is_sup_unique[OF compat'1 compat'2]
  by auto
*)
end