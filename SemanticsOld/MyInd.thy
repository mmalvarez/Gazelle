theory MyInd
imports Main
begin

datatype myNat =
  MyZero 
| MySucc "myNat"

fun add :: "myNat \<Rightarrow> myNat \<Rightarrow> myNat" where
"add MyZero x = x"
| "add (MySucc n) x = MySucc (add n x)"

lemma myzero1 : "add MyZero x = x"
proof(simp)
qed

lemma myzero2 : "add x MyZero = x"
  apply(induction x)
   apply(simp)

  apply(simp)
  done

end