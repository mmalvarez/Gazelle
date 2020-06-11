theory Mergeable imports Pord 

begin

(* mergeable is a type with an ordering, as well as a way to
  "naturally" (-ish) merge elements that may not have a LUB *)
class Mergeable =
  Pordc + (* TODO: do we want to allow defining mergeables that have no Bot? *)
  fixes bsup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("[^ _, _ ^]")

assumes bsup_spec :
  "\<And> a b . is_bsup a b (bsup a b)"

begin
declare [[show_types]]
lemma bsup_comm :

  assumes H : "has_sup {a, b}"
  shows "bsup a b = bsup b a"
proof -
  obtain x where  0 : "is_sup {a, b} x" using H
    by (auto simp add:is_sup_def has_sup_def)
  have 1 : "is_sup {a, b} (bsup a b)" using bsup_sup[OF 0 bsup_spec[of a b]] 
    by auto 
  hence 3 : "bsup a b = x " using 0 1
    by(auto simp add:is_sup_def is_least_unique)
  from H have 4: "has_sup {b, a}"
    by(auto simp add: has_sup_def elim:is_sup_comm2)
  hence 5: "is_sup {b, a} x" using 0
    by(auto simp add: has_sup_def is_sup_unique elim:is_sup_comm2[of a b x])
  have 6 : "is_sup {b, a} (bsup b a)" using bsup_sup[OF 5 bsup_spec[of b a]]
    by auto

  have 7 : "bsup b a = x" using 5 and 6
    by(auto simp add:is_sup_unique)
  show ?thesis using 7 and 3 by auto
qed


lemma bsup_assoc_fact1 :
  "bsup a (bsup b c) = (bsup (bsup a b) (bsup b c))"
proof(-)
  have 0:  "pleq a (bsup a b)" using 
        bsup_leq[OF bsup_spec [of "a" "b"]]
    by(simp add:bsup_leq)
  have 1:  "pleq b (bsup b c)" using bsup_leq[OF bsup_spec[of b c]]
    by(auto)
  have 2 : "pleq (bsup a b) (bsup a (bsup b c))"
    using bsup_mono2[OF 1 bsup_spec[of a b] bsup_spec[of a "bsup b c"]] by auto

  have LtoR : "pleq (bsup a (bsup b c)) (bsup (bsup a b) (bsup b c))"
    using bsup_compare1[OF bsup_spec bsup_spec 0 2] by auto

  have RtoL : "pleq (bsup (bsup a b) (bsup b c)) (bsup a (bsup b c))"
    using bsup_compare2[OF bsup_spec bsup_spec 0 2] by auto

  thus ?thesis using leq_antisym[OF LtoR RtoL] by auto
qed


lemma bsup_assoc_fact2 :
  "pleq (bsup (bsup a b) c) (bsup (bsup a b) (bsup a c))"
proof(-)
  have 0 : "pleq (bsup a b) (bsup a b)" using leq_refl by auto

  have 1 : "pleq (bsup a b) (bsup (bsup a b) c)" using bsup_leq bsup_spec
    by blast

  have 2 : "pleq (bsup a b) (bsup (bsup a b) (bsup a c))" using bsup_leq bsup_spec
    by blast

  have 3 : "(\<And>bd sd. pleq bd (c) \<Longrightarrow> is_sup {(bsup a b), bd} sd \<Longrightarrow> pleq bd ((bsup a c)))"
  proof(-)
    fix bd sd
    assume Hpleq : "pleq bd (c)"
    assume Hsup : "is_sup {(bsup a b), bd} sd"

    have in1 : "has_sup {(bsup a b), bd}" using Hsup by (auto simp add:has_sup_def)
    have in2 : "pleq (a) ((bsup a b))" using bsup_leq bsup_spec by blast 
    have in3 : "has_sup {a, bd}" using leq_completion[OF in2 Hsup] by auto
    then obtain sd' where Hsd : "is_sup {a, bd} sd'"
      by (auto simp add:has_sup_def)

    have in4 : "pleq sd' ((bsup a c))" using Hsd Hpleq bsup_spec[of a c]
      by(auto simp add: is_bsup_def is_least_def is_bub_def)

    have in5 : "pleq bd sd'" using Hsd by (simp add:is_sup_def is_ub_def is_least_def)

    show "pleq bd ((bsup a c))" using leq_trans[OF in5 in4] by auto
  qed

  thus ?thesis using bsup_compare1[OF bsup_spec bsup_spec 0 1 3] by auto
qed


(* remaining facts we want:
has_sup a b \<Longrightarrow> (bsup a (bsup b c)) = (bsup b (bsup a c))
has_sup a b \<Longrightarrow> (bsup (bsup a b)) c \<le> bsup a (bsup b c)

*)

lemma sup_assoc1 :
  fixes a b c
  assumes Hsup : "has_sup {a, b}"
  shows "bsup (bsup a b) c = bsup (bsup b a) c"
  using bsup_comm[OF Hsup] by auto

lemma sup_assoc_lb1 :
  fixes a b c
  assumes Hsup : "has_sup {a, b}"
  shows "pleq (bsup (bsup a b) c) (bsup a (bsup b c))"
proof(-)
  have 0 : "bsup (bsup a b) c = bsup (bsup b a) c"                
    using bsup_comm[OF Hsup]  by auto

  have 1 : "pleq (bsup (bsup b a) c) (bsup (bsup b a) (bsup b c))"
    using bsup_assoc_fact2 by auto

  have 3 : "bsup (bsup b a) (bsup b c) = bsup (bsup a b) (bsup b c)"
    using bsup_comm[OF Hsup] by auto

  have 4 : "bsup (bsup a b) (bsup b c) = bsup a (bsup b c)"
    using bsup_assoc_fact1 by auto

  show ?thesis using 0 1 3 4 by auto
qed

lemma sup_assoc_2 :
  fixes a b c
  assumes Hsup : "has_sup {a, b}"
  shows "pleq (bsup (bsup a b) c) (bsup b (bsup a c))"
proof(-)

(*  have "bsup (bsup a b) c = bsup (bsup b a) c" using sup_assoc_fact2[OF Hsup] by auto *)

  have 1 : "pleq (bsup (bsup a b) c) (bsup (bsup a b) (bsup a c))"
    using bsup_assoc_fact2 by auto

  have 2 : "bsup (bsup a b) (bsup a c) = bsup (bsup b a) (bsup a c)"
    using bsup_comm[OF Hsup] by auto

  have 3 : "bsup (bsup b a) (bsup a c) = bsup b (bsup a c)" 
    using bsup_assoc_fact1 by auto

  show ?thesis using 1 2 3 by auto

qed

end

class Mergeableb = Mergeable +
  Pordb

end
