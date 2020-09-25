structure MemTest : sig
  type inta
  type syn
  type ('b, 'a) oalist
  type 'a md_prio
  type 'a md_triv
  val test2 :
    (inta md_triv option) md_prio *
      (string, (inta md_triv option) md_prio) oalist
end = struct

datatype num = One | Bit0 of num | Bit1 of num;

datatype inta = Zero_int | Pos of num | Neg of num;

val one_inta : inta = Pos One;

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_int = {one = one_inta} : inta one;

fun plus_num (Bit1 m) (Bit1 n) = Bit0 (plus_num (plus_num m n) One)
  | plus_num (Bit1 m) (Bit0 n) = Bit1 (plus_num m n)
  | plus_num (Bit1 m) One = Bit0 (plus_num m One)
  | plus_num (Bit0 m) (Bit1 n) = Bit1 (plus_num m n)
  | plus_num (Bit0 m) (Bit0 n) = Bit0 (plus_num m n)
  | plus_num (Bit0 m) One = Bit1 m
  | plus_num One (Bit1 n) = Bit0 (plus_num n One)
  | plus_num One (Bit0 n) = Bit1 n
  | plus_num One One = Bit0 One;

fun uminus_inta (Neg m) = Pos m
  | uminus_inta (Pos m) = Neg m
  | uminus_inta Zero_int = Zero_int;

fun bitM One = One
  | bitM (Bit0 n) = Bit1 (bitM n)
  | bitM (Bit1 n) = Bit1 (Bit0 n);

fun dup (Neg n) = Neg (Bit0 n)
  | dup (Pos n) = Pos (Bit0 n)
  | dup Zero_int = Zero_int;

fun plus_inta (Neg m) (Neg n) = Neg (plus_num m n)
  | plus_inta (Neg m) (Pos n) = sub n m
  | plus_inta (Pos m) (Neg n) = sub m n
  | plus_inta (Pos m) (Pos n) = Pos (plus_num m n)
  | plus_inta Zero_int l = l
  | plus_inta k Zero_int = k
and sub (Bit0 m) (Bit1 n) = minus_int (dup (sub m n)) one_inta
  | sub (Bit1 m) (Bit0 n) = plus_inta (dup (sub m n)) one_inta
  | sub (Bit1 m) (Bit1 n) = dup (sub m n)
  | sub (Bit0 m) (Bit0 n) = dup (sub m n)
  | sub One (Bit1 n) = Neg (Bit0 n)
  | sub One (Bit0 n) = Neg (bitM n)
  | sub (Bit1 m) One = Pos (Bit0 m)
  | sub (Bit0 m) One = Pos (bitM m)
  | sub One One = Zero_int
and minus_int (Neg m) (Neg n) = sub n m
  | minus_int (Neg m) (Pos n) = Neg (plus_num m n)
  | minus_int (Pos m) (Neg n) = Pos (plus_num m n)
  | minus_int (Pos m) (Pos n) = sub m n
  | minus_int Zero_int l = uminus_inta l
  | minus_int k Zero_int = k;

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

val plus_int = {plus = plus_inta} : inta plus;

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_int = {zero = Zero_int} : inta zero;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a numeral =
  {one_numeral : 'a one, semigroup_add_numeral : 'a semigroup_add};
val one_numeral = #one_numeral : 'a numeral -> 'a one;
val semigroup_add_numeral = #semigroup_add_numeral :
  'a numeral -> 'a semigroup_add;

val semigroup_add_int = {plus_semigroup_add = plus_int} : inta semigroup_add;

val numeral_int =
  {one_numeral = one_int, semigroup_add_numeral = semigroup_add_int} :
  inta numeral;

type 'a uminus = {uminus : 'a -> 'a};
val uminus = #uminus : 'a uminus -> 'a -> 'a;

val uminus_int = {uminus = uminus_inta} : inta uminus;

val bogus_inta : inta = Zero_int;

type 'a bogus = {bogus : 'a};
val bogus = #bogus : 'a bogus -> 'a;

val bogus_int = {bogus = bogus_inta} : inta bogus;

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_literal = {equal = (fn a => fn b => ((a : string) = b))} :
  string equal;

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

val ord_literal =
  {less_eq = (fn a => fn b => a <= b), less = (fn a => fn b => a < b)} :
  string ord;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

val preorder_literal = {ord_preorder = ord_literal} : string preorder;

val order_literal = {preorder_order = preorder_literal} : string order;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

val linorder_literal = {order_linorder = order_literal} : string linorder;

datatype syn = Sread of string | Swrite of string | Sskip;

datatype nat = Zero_nat | Suc of nat;

datatype ('b, 'a) oalist = Oalist of ('b * 'a) list;

datatype 'a md_prio = Mdp of nat * 'a;

datatype 'a md_triv = Mdt of 'a;

datatype ('a, 'b, 'c) lifting_ext = Lifting_ext of ('a -> 'b -> 'b) * 'c;

datatype ('a, 'b, 'c, 'd) plifting_ext =
  Plifting_ext of ('a -> 'b -> 'c -> 'c) * ('a -> 'c -> 'b) * ('a -> 'c) * 'd;

fun id x = (fn xa => xa) x;

fun eq A_ a b = equal A_ a b;

fun swr a = Mdp (Zero_nat, SOME (Mdt a));

fun numeral A_ (Bit1 n) =
  let
    val m = numeral A_ n;
  in
    plus ((plus_semigroup_add o semigroup_add_numeral) A_)
      (plus ((plus_semigroup_add o semigroup_add_numeral) A_) m m)
      (one (one_numeral A_))
  end
  | numeral A_ (Bit0 n) =
    let
      val m = numeral A_ n;
    in
      plus ((plus_semigroup_add o semigroup_add_numeral) A_) m m
    end
  | numeral A_ One = one (one_numeral A_);

fun str_ord_update (A1_, A2_) k v [] = [(k, v)]
  | str_ord_update (A1_, A2_) ka va ((k, v) :: t) =
    (if less ((ord_preorder o preorder_order o order_linorder) A2_) ka k
      then (ka, va) :: (k, v) :: t
      else (if eq A1_ ka k then (ka, va) :: t
             else (k, v) :: str_ord_update (A1_, A2_) ka va t));

fun impl_of B_ (Oalist x) = x;

fun update (A1_, A2_) xc xd xe =
  Oalist (str_ord_update (A1_, A2_) xc xd (impl_of A2_ xe));

fun empty A_ = Oalist [];

fun to_oalist (A1_, A2_) [] = empty A2_
  | to_oalist (A1_, A2_) ((a, b) :: l) =
    update (A1_, A2_) a b (to_oalist (A1_, A2_) l);

fun test_store (A1_, A2_, A3_) =
  to_oalist (equal_literal, linorder_literal)
    [("a", swr (zero A2_)), ("b", swr (numeral A3_ (Bit0 One))),
      ("z", swr (uminus A1_ (one (one_numeral A3_))))];

fun test_state (A1_, A2_, A3_) =
  (swr (Pos (Bit1 One)), test_store (A1_, A2_, A3_));

fun lBase (Plifting_ext (lUpd, lOut, lBase, more)) = lBase;

fun lUpd (Plifting_ext (lUpd, lOut, lBase, more)) = lUpd;

fun lOut (Plifting_ext (lUpd, lOut, lBase, more)) = lOut;

fun extend r more = Plifting_ext (lUpd r, lOut r, lBase r, more);

fun plus_nat (Suc m) n = plus_nat m (Suc n)
  | plus_nat Zero_nat n = n;

val one_nat : nat = Suc Zero_nat;

fun lPost (Plifting_ext (lUpd, lOut, lBase, Lifting_ext (lPost, more))) = lPost;

fun prio_pl f0 t =
  Plifting_ext
    ((fn s => fn a => fn Mdp (m, b) => Mdp (m, lUpd t s a b)),
      (fn s => fn Mdp (_, a) => lOut t s a), (fn s => Mdp (f0 s, lBase t s)),
      ());

fun prio_l f0 f1 t =
  extend (prio_pl f0 t)
    (Lifting_ext ((fn s => fn Mdp (m, b) => Mdp (f1 s m, lPost t s b)), ()));

fun prio_l_inc x = prio_l (fn _ => Zero_nat) (fn _ => plus_nat one_nat) x;

fun lNew l s a = lUpd l s a (lBase l s);

fun option_pl t =
  Plifting_ext
    ((fn s => fn a => fn b =>
       (case b of NONE => SOME (lNew t s a) | SOME ba => SOME (lUpd t s a ba))),
      (fn s => fn a =>
        (case a of NONE => lOut t s (lBase t s) | SOME aa => lOut t s aa)),
      (fn _ => NONE), ());

fun option_l t =
  extend (option_pl t)
    (Lifting_ext
      ((fn s => fn a =>
         (case a of NONE => NONE | SOME b => SOME (lPost t s b))),
        ()));

fun map_of A_ ((l, v) :: ps) k = (if eq A_ l k then SOME v else map_of A_ ps k)
  | map_of A_ [] k = NONE;

fun get (A1_, A2_) xa = map_of A1_ (impl_of A2_ xa);

fun oalist_pl (B1_, B2_) f t =
  Plifting_ext
    ((fn s => fn a => fn l =>
       (case f s of NONE => l
         | SOME k =>
           (case get (B1_, B2_) l k
             of NONE => update (B1_, B2_) k (lNew t s a) l
             | SOME v => update (B1_, B2_) k (lUpd t s a v) l))),
      (fn s => fn l =>
        (case f s of NONE => lOut t s (lBase t s)
          | SOME k =>
            (case get (B1_, B2_) l k of NONE => lOut t s (lBase t s)
              | SOME a => lOut t s a))),
      (fn s =>
        (case f s of NONE => empty B2_
          | SOME k => update (B1_, B2_) k (lBase t s) (empty B2_))),
      ());

fun oalist_l (B1_, B2_) f t =
  extend (oalist_pl (B1_, B2_) f t)
    (Lifting_ext
      ((fn s => fn l =>
         (case f s of NONE => l
           | SOME k =>
             (case get (B1_, B2_) l k of NONE => l
               | SOME a => update (B1_, B2_) k (lPost t s a) l))),
        ()));

fun triv_pl t =
  Plifting_ext
    ((fn s => fn a => fn Mdt b => Mdt (lUpd t s a b)),
      (fn s => fn Mdt a => lOut t s a), (fn s => Mdt (lBase t s)), ());

fun triv_l t =
  extend (triv_pl t)
    (Lifting_ext ((fn s => fn Mdt b => Mdt (lPost t s b)), ()));

fun prod_pl t1 t2 =
  Plifting_ext
    ((fn s => fn a => fn b => let
                                val (a1, a2) = a;
                                val (b1, b2) = b;
                              in
                                (lUpd t1 s a1 b1, lUpd t2 s a2 b2)
                              end),
      (fn s => fn (b1, b2) => (lOut t1 s b1, lOut t2 s b2)),
      (fn s => (lBase t1 s, lBase t2 s)), ());

fun prod_l t1 t2 =
  extend (prod_pl t1 t2)
    (Lifting_ext ((fn s => fn (b1, b2) => (lPost t1 s b1, lPost t2 s b2)), ()));

fun id_pl B_ =
  Plifting_ext
    ((fn _ => fn a => fn _ => a), (fn _ => fn a => a), (fn _ => bogus B_), ());

fun pl_map_s la l sem syn st =
  lUpd l (la syn) (sem (la syn) (lOut l (la syn) st)) st;

fun l_map_s la l sem syn st = lPost l (la syn) (pl_map_s la l sem syn st);

fun mem_keys (Sread s) = SOME s
  | mem_keys (Swrite s) = SOME s
  | mem_keys Sskip = NONE;

fun mem0_sem Sskip s = s
  | mem0_sem (Swrite uu) (reg, store) = (reg, reg)
  | mem0_sem (Sread uv) (reg, store) = (store, store);

fun mem_sem x =
  l_map_s id
    (prod_l
      ((prio_l_inc o option_l o triv_l)
        (extend (id_pl bogus_int) (Lifting_ext ((fn _ => fn a => a), ()))))
      (oalist_l (equal_literal, linorder_literal) mem_keys
        ((prio_l_inc o option_l o triv_l)
          (extend (id_pl bogus_int) (Lifting_ext ((fn _ => fn a => a), ()))))))
    mem0_sem x;

val test2 :
  (inta md_triv option) md_prio * (string, (inta md_triv option) md_prio) oalist
  = mem_sem (Swrite "f") (test_state (uminus_int, zero_int, numeral_int));

end; (*struct MemTest*)
