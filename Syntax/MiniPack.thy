theory MiniPack imports "../Syntax_Utils"

begin

type_synonym ('d, 'xp, 'xs) mpackf =
  "char list * 'xp * ('d + 'xs)"

type_synonym ('d, 'xp, 'xs) mpack =
  "'xp * ('d + 'xs)"


type_synonym ('d, 'x) mmpack =
  "('d + 'x)"

type_synonym ('d, 'xp, 'xs) mmppack =
  "'xp * ('d + 'xs)"

(* idea: represent constructors for our data
   if the name matches, we put it in the current data slot
   otherwise it becomes an xp *)
type_synonym ('i, 'o1, 'o2) ctor =
  "('i \<Rightarrow> 'o1) + ((('i \<Rightarrow> 'o1) * ('o1 \<Rightarrow> 'o2)))"


(* we may have subtyping issues here. *)
type_synonym ('d, 'xp, 'xs, 'o) mp_disc =
  "((('xp * 'd) \<Rightarrow> 'o) * (('xp * 'xs) \<Rightarrow> 'o))"

fun mp_constr ::
  "'xp \<Rightarrow> 'd \<Rightarrow> ('d, 'xp, 'xs) mpack" where
"mp_constr xp d = (xp, Inl d)"

fun mp_disc_apply ::
  "('d, 'xp, 'xs, 'o) mp_disc \<Rightarrow>
   ('d, 'xp, 'xs) mpack \<Rightarrow> 'o" where
"mp_disc_apply (fd, fxs) (xp, Inl d) = fd (xp, d)"
| "mp_disc_apply (fd, fxs) (xp, Inr xs) = fxs (xp, xs)"

fun mp_comms:: "('d, 'xp, 'xs) mpack \<Rightarrow> 'xp * ('xs + 'd)" where
"mp_comms (xs, Inl d) = (xs, Inr d)"
| "mp_comms (xs, Inr xp) = (xs, Inl xp)"

(* prod.swap lets us do the other swap *)
fun mp_commp :: "('d, 'xp, 'xs) mpack \<Rightarrow> ('d  + 'xs) * 'xp" where
"mp_commp x = prod.swap x"

(* we need a way of adapting one mpack into another *)
locale iso =
  fixes to_r :: "'l \<Rightarrow> 'r"
  fixes to_l :: "'r \<Rightarrow> 'l"
  assumes Hisol : "\<And> l . to_l (to_r l) = l"
  assumes Hisor : "\<And> r . to_r (to_l r) = r"

begin

fun lift_l :: "('l \<Rightarrow> 'o) \<Rightarrow> ('r \<Rightarrow> 'o)" where
  "lift_l fl = (\<lambda> r . fl (to_l r))"

fun lift_r :: "('r \<Rightarrow> 'o) \<Rightarrow> ('l \<Rightarrow> 'o)" where
  "lift_r fr = (\<lambda> l . fr (to_r l))"

lemma iso_lift_fr : "\<And> fr . lift_r (lift_l fr) = fr"
  apply(clarsimp)
  apply(simp add:Hisol)
  done

lemma iso_lift_fl : "\<And> fl . lift_l (lift_r fl) = fl"
  apply(clarsimp)
  apply(simp add:Hisor)
  done

lemma iso_lift_pred_r :
  "P r \<Longrightarrow> lift_r P (to_l r)"
  apply(clarsimp)
  apply(simp add:Hisor)
  done

lemma iso_lift_pred_l :
  "P l \<Longrightarrow> lift_l P (to_r l)"
  apply(clarsimp)
  apply(simp add:Hisol)
  done


end

end