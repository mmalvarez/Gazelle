theory Lifter_New 
 imports  "../Mergeable/Mergeable_Instances" "../Mergeable/Mergeable_Oalist" "../Mergeable/Mergeable_Roalist" "../Mergeable/Mono"
begin

(* When we lift syntaxes we reverse the function arrow *)
type_synonym ('a, 'b) syn_lifting = "('b \<Rightarrow> 'a)"

datatype ('syn, 'a, 'b) lifting =
  LMake  (LUpd : "('syn \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b)")
         (LOut : "('syn \<Rightarrow> 'b \<Rightarrow> 'a)")
         (LBase : "('syn \<Rightarrow> 'b)")

definition LMap ::
  "('x, 'a, 'b) lifting \<Rightarrow> ('x \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('x \<Rightarrow> 'b \<Rightarrow> 'b)" where
"LMap l f s b =
  LUpd l s (f s (LOut l s b)) b"

definition LNew :: "('syn, 'a, 'b) lifting \<Rightarrow> 'syn \<Rightarrow> 'a \<Rightarrow> 'b"  where
"LNew l s a = LUpd l s a (LBase l s)"

(* TODO: make sure this is a good idea. *)
declare LNew_def [simp]
declare LMap_def [simp]

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

(* weak + (strong?) + (base?) + (ok?) + (pres?) *)
(* TODO: support for vsg style reasoning *)
locale lifting_valid_weak =
  fixes l :: "('syn, 'a, 'b :: Pord_Weak) lifting"
  fixes S :: "('syn, 'b) valid_set"
  assumes put_get : "\<And> a . LOut l s (LUpd l s a b) = a"
  assumes get_put_weak : "\<And> s b . b \<in> S s \<Longrightarrow> b <[ LUpd l s (LOut l s b) b"
  assumes put_S : "\<And> s a b . LUpd l s a b \<in> S s"

locale lifting_valid = lifting_valid_weak +
  assumes get_put : "\<And> s a b . b \<in> S s \<Longrightarrow> b <[ LUpd l s a b"

locale lifting_valid_weak_base = lifting_valid_weak +
  assumes base : "\<And> s . LBase l s = \<bottom>"

locale lifting_valid_base = lifting_valid + lifting_valid_weak_base

locale lifting_valid_weak_ok = lifting_valid_weak +
  assumes ok_S_valid : "\<And> s . ok_S \<subseteq> S s"
  assumes ok_S_put : "\<And> s a b . b \<in> ok_S \<Longrightarrow> LUpd l s a b \<in> ok_S"

locale lifting_valid_ok = lifting_valid + lifting_valid_weak_ok

locale lifting_valid_weak_base_ok = lifting_valid_weak_ok + lifting_valid_weak_base

locale lifting_valid_base_ok = lifting_valid_ok + lifting_valid_base

locale lifting_valid_weak_pres = lifting_valid_weak +
  assumes pres :
    "\<And> v V supr f s . 
         v \<in> V \<Longrightarrow>
         V \<subseteq> S s \<Longrightarrow>
         is_sup V supr \<Longrightarrow> supr \<in> S s \<Longrightarrow> is_sup (LMap l f s ` V) (LMap l f s supr)"

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

end