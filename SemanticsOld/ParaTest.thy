theory ParaTest imports Main
begin

locale Parametric 

begin

abbreviation parid2 :: "'x \<Rightarrow> 'x" where
"parid2 \<equiv> undefined"

end

consts tcharc :: "'z \<Rightarrow> bool"

print_locale Parametric
locale Deep = Parametric
begin


abbreviation thingy :: " 'z" where
"thingy \<equiv> SOME x . tcharc x"


abbreviation wacky :: " 'b" where 
"wacky \<equiv> parid2 thingy"

end


overloading
 tcharc' \<equiv> "tcharc :: nat \<Rightarrow> bool"
begin

definition tcharc' where
"tcharc' (z :: nat) = (z = (2 :: nat))"


declare tcharc'_def [simp]

value [nbe] "tcharc 3"

print_codesetup

end

overloading
  tcharc'' \<equiv> "tcharc :: nat \<Rightarrow> bool"
begin
  definition tcharc'' where
"tcharc'' (z :: nat) = (z = (3 :: nat))"
end

(* THIS *)
declare tcharc'_def [code_unfold]

value "tcharc (2 :: nat)"

lemma "tcharc (3 :: nat) = False"
  apply(simp)
  apply(simp add:tcharc'_def)
  done
export_code tcharc




locale Deeper = Deep +
  assumes "thingy = (2 :: nat)"
begin
end

interpretation deepering : Deeper
proof(unfold_locales)
  have "(SOME x. tcharc x) = 2"
    
  done

(*
definition wacky :: "'b" where
"wacky = coe2 (parid (coe1 thingy))"
*)
definition wacky2 :: "_" where
"wacky2 = parid2 thingy"

end

global_interpretation boom : Parametric id
  defines boom_parid2 = boom.parid2
proof(unfold_locales)
  show "\<And> x . id x = x"
  apply(auto)
    done
qed


definition idspec :: "nat \<Rightarrow> nat" where
"idspec n = n"

global_interpretation boom2 : Parametric idspec
  defines boom2_parid2 = boom.parid2
proof(unfold_locales)
  show "\<And> x . idspec x = x"
    apply(auto simp add:idspec_def)
    done
qed

global_interpretation final : Deep idspec id id "(1 :: nat)"
proof(unfold_locales)
qed



datatype 'a thingy =
Thing 'a 

locale Thing_sem =
  fixes tden :: "'a \<Rightarrow> 'mstate \<Rightarrow> 'mstate"
  fixes parm :: "'b \<Rightarrow> 'mstate \<Rightarrow> 'mstate"
begin

fun doit :: "'a thingy \<Rightarrow> 'mstate \<Rightarrow> 'mstate"
  where
"doit (Thing xt) = tden xt"

fun laze :: "'mstate \<Rightarrow> 'mstate" where
  "laze x = parm undefined x"

end

interpretation Thinginterp :
  Thing_sem "(\<lambda> (x :: nat) (b :: bool) . b)"
            "(\<lambda> (x :: 'b) (b :: bool) . b)"
  done

value[nbe] "Thinginterp.laze _ True"

end