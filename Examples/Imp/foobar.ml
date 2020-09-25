module Fun : sig
  val id : 'a -> 'a
  val comp : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
end = struct

let rec id x = (fun xa -> xa) x;;

let rec comp f g = (fun x -> f (g x));;

end;; (*struct Fun*)

module HOL : sig
  type 'a equal = {equal : 'a -> 'a -> bool}
  val equal : 'a equal -> 'a -> 'a -> bool
  val eq : 'a equal -> 'a -> 'a -> bool
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let rec eq _A a b = equal _A a b;;

end;; (*struct HOL*)

module Map : sig
  val map_of : 'a HOL.equal -> ('a * 'b) list -> 'a -> 'b option
end = struct

let rec map_of _A
  x0 k = match x0, k with
    (l, v) :: ps, k -> (if HOL.eq _A l k then Some v else map_of _A ps k)
    | [], k -> None;;

end;; (*struct Map*)

module Arith : sig
  type num = One | Bit0 of num | Bit1 of num
  type int = Zero_int | Pos of num | Neg of num
  type 'a one = {one : 'a}
  val one : 'a one -> 'a
  type 'a plus
  type 'a zero = {zero : 'a}
  val zero : 'a zero -> 'a
  val zero_int : int zero
  type 'a semigroup_add
  type 'a numeral =
    {one_numeral : 'a one; semigroup_add_numeral : 'a semigroup_add}
  val numeral_int : int numeral
  type 'a uminus = {uminus : 'a -> 'a}
  val uminus : 'a uminus -> 'a -> 'a
  val uminus_int : int uminus
  type nat = Zero_nat | Suc of nat
  val one_nat : nat
  val numeral : 'a numeral -> num -> 'a
  val plus_nat : nat -> nat -> nat
end = struct

type num = One | Bit0 of num | Bit1 of num;;

type int = Zero_int | Pos of num | Neg of num;;

let one_inta : int = Pos One;;

type 'a one = {one : 'a};;
let one _A = _A.one;;

let one_int = ({one = one_inta} : int one);;

let rec plus_num
  x0 x1 = match x0, x1 with Bit1 m, Bit1 n -> Bit0 (plus_num (plus_num m n) One)
    | Bit1 m, Bit0 n -> Bit1 (plus_num m n)
    | Bit1 m, One -> Bit0 (plus_num m One)
    | Bit0 m, Bit1 n -> Bit1 (plus_num m n)
    | Bit0 m, Bit0 n -> Bit0 (plus_num m n)
    | Bit0 m, One -> Bit1 m
    | One, Bit1 n -> Bit0 (plus_num n One)
    | One, Bit0 n -> Bit1 n
    | One, One -> Bit0 One;;

let rec uminus_inta = function Neg m -> Pos m
                      | Pos m -> Neg m
                      | Zero_int -> Zero_int;;

let rec bitM = function One -> One
               | Bit0 n -> Bit1 (bitM n)
               | Bit1 n -> Bit1 (Bit0 n);;

let rec dup = function Neg n -> Neg (Bit0 n)
              | Pos n -> Pos (Bit0 n)
              | Zero_int -> Zero_int;;

let rec plus_inta k l = match k, l with Neg m, Neg n -> Neg (plus_num m n)
                    | Neg m, Pos n -> sub n m
                    | Pos m, Neg n -> sub m n
                    | Pos m, Pos n -> Pos (plus_num m n)
                    | Zero_int, l -> l
                    | k, Zero_int -> k
and sub
  x0 x1 = match x0, x1 with Bit0 m, Bit1 n -> minus_int (dup (sub m n)) one_inta
    | Bit1 m, Bit0 n -> plus_inta (dup (sub m n)) one_inta
    | Bit1 m, Bit1 n -> dup (sub m n)
    | Bit0 m, Bit0 n -> dup (sub m n)
    | One, Bit1 n -> Neg (Bit0 n)
    | One, Bit0 n -> Neg (bitM n)
    | Bit1 m, One -> Pos (Bit0 m)
    | Bit0 m, One -> Pos (bitM m)
    | One, One -> Zero_int
and minus_int k l = match k, l with Neg m, Neg n -> sub n m
                | Neg m, Pos n -> Neg (plus_num m n)
                | Pos m, Neg n -> Pos (plus_num m n)
                | Pos m, Pos n -> sub m n
                | Zero_int, l -> uminus_inta l
                | k, Zero_int -> k;;

type 'a plus = {plus : 'a -> 'a -> 'a};;
let plus _A = _A.plus;;

let plus_int = ({plus = plus_inta} : int plus);;

type 'a zero = {zero : 'a};;
let zero _A = _A.zero;;

let zero_int = ({zero = Zero_int} : int zero);;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};;

type 'a numeral =
  {one_numeral : 'a one; semigroup_add_numeral : 'a semigroup_add};;

let semigroup_add_int = ({plus_semigroup_add = plus_int} : int semigroup_add);;

let numeral_int =
  ({one_numeral = one_int; semigroup_add_numeral = semigroup_add_int} :
    int numeral);;

type 'a uminus = {uminus : 'a -> 'a};;
let uminus _A = _A.uminus;;

let uminus_int = ({uminus = uminus_inta} : int uminus);;

type nat = Zero_nat | Suc of nat;;

let one_nat : nat = Suc Zero_nat;;

let rec numeral _A
  = function
    Bit1 n ->
      (let m = numeral _A n in
        plus _A.semigroup_add_numeral.plus_semigroup_add
          (plus _A.semigroup_add_numeral.plus_semigroup_add m m)
          (one _A.one_numeral))
    | Bit0 n ->
        (let m = numeral _A n in
          plus _A.semigroup_add_numeral.plus_semigroup_add m m)
    | One -> one _A.one_numeral;;

let rec plus_nat x0 n = match x0, n with Suc m, n -> plus_nat m (Suc n)
                   | Zero_nat, n -> n;;

end;; (*struct Arith*)

module MergeableInstances : sig
  type 'a md_prio = Mdp of Arith.nat * 'a
  type 'a md_triv = Mdt of 'a
end = struct

type 'a md_prio = Mdp of Arith.nat * 'a;;

type 'a md_triv = Mdt of 'a;;

end;; (*struct MergeableInstances*)

module Orderings : sig
  type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool}
  val less_eq : 'a ord -> 'a -> 'a -> bool
  val less : 'a ord -> 'a -> 'a -> bool
  type 'a preorder = {ord_preorder : 'a ord}
  type 'a order = {preorder_order : 'a preorder}
  type 'a linorder = {order_linorder : 'a order}
end = struct

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

type 'a preorder = {ord_preorder : 'a ord};;

type 'a order = {preorder_order : 'a preorder};;

type 'a linorder = {order_linorder : 'a order};;

end;; (*struct Orderings*)

module MergeableAList : sig
  type ('b, 'a) oalist
  val get :
    'a HOL.equal * 'a Orderings.linorder -> ('a, 'b) oalist -> 'a -> 'b option
  val empty : 'a Orderings.linorder -> ('a, 'b) oalist
  val update :
    'a HOL.equal * 'a Orderings.linorder ->
      'a -> 'b -> ('a, 'b) oalist -> ('a, 'b) oalist
  val to_oalist :
    'a HOL.equal * 'a Orderings.linorder -> ('a * 'b) list -> ('a, 'b) oalist
end = struct

type ('b, 'a) oalist = Oalist of ('b * 'a) list;;

let rec impl_of _B (Oalist x) = x;;

let rec get (_A1, _A2) xa = Map.map_of _A1 (impl_of _A2 xa);;

let rec empty _A = Oalist [];;

let rec str_ord_update (_A1, _A2)
  k v x2 = match k, v, x2 with k, v, [] -> [(k, v)]
    | ka, va, (k, v) :: t ->
        (if Orderings.less
              _A2.Orderings.order_linorder.Orderings.preorder_order.Orderings.ord_preorder
              ka k
          then (ka, va) :: (k, v) :: t
          else (if HOL.eq _A1 ka k then (ka, va) :: t
                 else (k, v) :: str_ord_update (_A1, _A2) ka va t));;

let rec update (_A1, _A2)
  xc xd xe = Oalist (str_ord_update (_A1, _A2) xc xd (impl_of _A2 xe));;

let rec to_oalist (_A1, _A2)
  = function [] -> empty _A2
    | (a, b) :: l -> update (_A1, _A2) a b (to_oalist (_A1, _A2) l);;

end;; (*struct MergeableAList*)

module LiftUtils : sig
  type ('a, 'b, 'c) lifting_ext = Lifting_ext of ('a -> 'b -> 'b) * 'c
  type ('a, 'b, 'c, 'd) plifting_ext =
    Plifting_ext of
      ('a -> 'b -> 'c -> 'c) * ('a -> 'c -> 'b option) * ('a -> 'c) * 'd
  val lBase : ('a, 'b, 'c, 'd) plifting_ext -> 'a -> 'c
  val lUpd : ('a, 'b, 'c, 'd) plifting_ext -> 'a -> 'b -> 'c -> 'c
  val lNew : ('a, 'b, 'c, 'd) plifting_ext -> 'a -> 'b -> 'c
  val lPost :
    ('a, 'b, 'c, ('a, 'c, 'd) lifting_ext) plifting_ext -> 'a -> 'c -> 'c
  val lOut : ('a, 'b, 'c, 'd) plifting_ext -> 'a -> 'c -> 'b option
  val l_map_s :
    ('a -> 'b) ->
      ('b, 'c, 'd, ('b, 'd, 'e) lifting_ext) plifting_ext ->
        ('b -> 'c -> 'c) -> 'a -> 'd -> 'd
  val extend :
    ('a, 'b, 'c, unit) plifting_ext -> 'd -> ('a, 'b, 'c, 'd) plifting_ext
end = struct

type ('a, 'b, 'c) lifting_ext = Lifting_ext of ('a -> 'b -> 'b) * 'c;;

type ('a, 'b, 'c, 'd) plifting_ext =
  Plifting_ext of
    ('a -> 'b -> 'c -> 'c) * ('a -> 'c -> 'b option) * ('a -> 'c) * 'd;;

let rec lBase (Plifting_ext (lUpd, lOut, lBase, more)) = lBase;;

let rec lUpd (Plifting_ext (lUpd, lOut, lBase, more)) = lUpd;;

let rec lNew l s a = lUpd l s a (lBase l s);;

let rec lPost
  (Plifting_ext (lUpd, lOut, lBase, Lifting_ext (lPost, more))) = lPost;;

let rec lOut (Plifting_ext (lUpd, lOut, lBase, more)) = lOut;;

let rec pl_map_s
  la l sem syn st =
    (match lOut l (la syn) st with None -> st
      | Some out -> lUpd l (la syn) (sem (la syn) out) st);;

let rec l_map_s la l sem syn st = lPost l (la syn) (pl_map_s la l sem syn st);;

let rec extend r more = Plifting_ext (lUpd r, lOut r, lBase r, more);;

end;; (*struct LiftUtils*)

module LiftInstances : sig
  val id_pl : ('a, 'b, 'b, unit) LiftUtils.plifting_ext
  val prod_l :
    ('a, 'b, 'c, ('a, 'c, 'd) LiftUtils.lifting_ext) LiftUtils.plifting_ext ->
      ('a, 'e, 'f, ('a, 'f, 'g) LiftUtils.lifting_ext) LiftUtils.plifting_ext ->
        ('a, ('b * 'e), ('c * 'f), ('a, ('c * 'f), unit) LiftUtils.lifting_ext)
          LiftUtils.plifting_ext
  val triv_l :
    ('a, 'b, 'c, ('a, 'c, 'd) LiftUtils.lifting_ext) LiftUtils.plifting_ext ->
      ('a, 'b, 'c MergeableInstances.md_triv,
        ('a, 'c MergeableInstances.md_triv, unit) LiftUtils.lifting_ext)
        LiftUtils.plifting_ext
  val oalist_l :
    'b HOL.equal * 'b Orderings.linorder ->
      ('a -> 'b option) ->
        ('a, 'c, 'd, ('a, 'd, 'e) LiftUtils.lifting_ext)
          LiftUtils.plifting_ext ->
          ('a, 'c, ('b, 'd) MergeableAList.oalist,
            ('a, ('b, 'd) MergeableAList.oalist, unit) LiftUtils.lifting_ext)
            LiftUtils.plifting_ext
  val option_l :
    ('a, 'b, 'c, ('a, 'c, 'd) LiftUtils.lifting_ext) LiftUtils.plifting_ext ->
      ('a, 'b, ('c option), ('a, ('c option), unit) LiftUtils.lifting_ext)
        LiftUtils.plifting_ext
  val prio_l_inc :
    ('a, 'b, 'c, ('a, 'c, unit) LiftUtils.lifting_ext) LiftUtils.plifting_ext ->
      ('a, 'b, 'c MergeableInstances.md_prio,
        ('a, 'c MergeableInstances.md_prio, unit) LiftUtils.lifting_ext)
        LiftUtils.plifting_ext
end = struct

let id_pl : ('a, 'b, 'b, unit) LiftUtils.plifting_ext
  = LiftUtils.Plifting_ext
      ((fun _ a _ -> a), (fun _ -> (fun a -> Some a)),
        (fun _ -> failwith "undefined"), ());;

let rec prio_pl
  f0 t =
    LiftUtils.Plifting_ext
      ((fun s a (MergeableInstances.Mdp (m, b)) ->
         MergeableInstances.Mdp (m, LiftUtils.lUpd t s a b)),
        (fun s (MergeableInstances.Mdp (_, a)) -> LiftUtils.lOut t s a),
        (fun s -> MergeableInstances.Mdp (f0 s, LiftUtils.lBase t s)), ());;

let rec prio_l
  f0 f1 t =
    LiftUtils.extend (prio_pl f0 t)
      (LiftUtils.Lifting_ext
        ((fun s (MergeableInstances.Mdp (m, b)) ->
           MergeableInstances.Mdp (f1 s m, LiftUtils.lPost t s b)),
          ()));;

let rec prod_pl
  t1 t2 =
    LiftUtils.Plifting_ext
      ((fun s a b ->
         (let (a1, a2) = a in
          let (b1, b2) = b in
           (LiftUtils.lUpd t1 s a1 b1, LiftUtils.lUpd t2 s a2 b2))),
        (fun s (b1, b2) ->
          (match LiftUtils.lOut t1 s b1 with None -> None
            | Some b1o ->
              (match LiftUtils.lOut t2 s b2 with None -> None
                | Some b2o -> Some (b1o, b2o)))),
        (fun s -> (LiftUtils.lBase t1 s, LiftUtils.lBase t2 s)), ());;

let rec prod_l
  t1 t2 =
    LiftUtils.extend (prod_pl t1 t2)
      (LiftUtils.Lifting_ext
        ((fun s (b1, b2) -> (LiftUtils.lPost t1 s b1, LiftUtils.lPost t2 s b2)),
          ()));;

let rec triv_pl
  t = LiftUtils.Plifting_ext
        ((fun s a (MergeableInstances.Mdt b) ->
           MergeableInstances.Mdt (LiftUtils.lUpd t s a b)),
          (fun s (MergeableInstances.Mdt a) -> LiftUtils.lOut t s a),
          (fun s -> MergeableInstances.Mdt (LiftUtils.lBase t s)), ());;

let rec triv_l
  t = LiftUtils.extend (triv_pl t)
        (LiftUtils.Lifting_ext
          ((fun s (MergeableInstances.Mdt b) ->
             MergeableInstances.Mdt (LiftUtils.lPost t s b)),
            ()));;

let rec oalist_pl (_B1, _B2)
  f t = LiftUtils.Plifting_ext
          ((fun s a l ->
             (match f s with None -> l
               | Some k ->
                 (match MergeableAList.get (_B1, _B2) l k
                   with None ->
                     MergeableAList.update (_B1, _B2) k (LiftUtils.lNew t s a) l
                   | Some v ->
                     MergeableAList.update (_B1, _B2) k (LiftUtils.lUpd t s a v)
                       l))),
            (fun s l ->
              (match f s with None -> LiftUtils.lOut t s (LiftUtils.lBase t s)
                | Some k ->
                  (match MergeableAList.get (_B1, _B2) l k with None -> None
                    | Some a -> LiftUtils.lOut t s a))),
            (fun s ->
              (match f s with None -> MergeableAList.empty _B2
                | Some k ->
                  MergeableAList.update (_B1, _B2) k (LiftUtils.lBase t s)
                    (MergeableAList.empty _B2))),
            ());;

let rec oalist_l (_B1, _B2)
  f t = LiftUtils.extend (oalist_pl (_B1, _B2) f t)
          (LiftUtils.Lifting_ext
            ((fun s l ->
               (match f s with None -> l
                 | Some k ->
                   (match MergeableAList.get (_B1, _B2) l k with None -> l
                     | Some a ->
                       MergeableAList.update (_B1, _B2) k
                         (LiftUtils.lPost t s a) l))),
              ()));;

let rec option_pl
  t = LiftUtils.Plifting_ext
        ((fun s a b ->
           (match b with None -> Some (LiftUtils.lNew t s a)
             | Some ba -> Some (LiftUtils.lUpd t s a ba))),
          (fun s a ->
            (match a with None -> None | Some aa -> LiftUtils.lOut t s aa)),
          (fun _ -> None), ());;

let rec option_l
  t = LiftUtils.extend (option_pl t)
        (LiftUtils.Lifting_ext
          ((fun s a ->
             (match a with None -> None
               | Some b -> Some (LiftUtils.lPost t s b))),
            ()));;

let rec prio_l_inc
  x = prio_l (fun _ -> Arith.Zero_nat) (fun _ -> Arith.plus_nat Arith.one_nat)
        x;;

end;; (*struct LiftInstances*)

module Stringa : sig
  val equal_literal : string HOL.equal
  val linorder_literal : string Orderings.linorder
end = struct

let equal_literal =
  ({HOL.equal = (fun a b -> ((a : string) = b))} : string HOL.equal);;

let ord_literal =
  ({Orderings.less_eq = (fun a b -> ((a : string) <= b));
     Orderings.less = (fun a b -> ((a : string) < b))}
    : string Orderings.ord);;

let preorder_literal =
  ({Orderings.ord_preorder = ord_literal} : string Orderings.preorder);;

let order_literal =
  ({Orderings.preorder_order = preorder_literal} : string Orderings.order);;

let linorder_literal =
  ({Orderings.order_linorder = order_literal} : string Orderings.linorder);;

end;; (*struct Stringa*)

module Mem : sig
  type syn
  val test :
    (Arith.int MergeableInstances.md_triv option) MergeableInstances.md_prio *
      (string,
        (Arith.int MergeableInstances.md_triv option)
          MergeableInstances.md_prio)
        MergeableAList.oalist
end = struct

type syn = Sread of string | Swrite of string | Sskip;;

let rec swr
  a = MergeableInstances.Mdp (Arith.Zero_nat, Some (MergeableInstances.Mdt a));;

let rec test_store (_A1, _A2, _A3)
  = MergeableAList.to_oalist (Stringa.equal_literal, Stringa.linorder_literal)
      [("a", swr (Arith.zero _A2));
        ("b", swr (Arith.numeral _A3 (Arith.Bit0 Arith.One)));
        ("z", swr (Arith.uminus _A1 (Arith.one _A3.Arith.one_numeral)))];;

let rec test_state (_A1, _A2, _A3)
  = (swr Arith.Zero_int, test_store (_A1, _A2, _A3));;

let rec mem_keys = function Sread s -> Some s
                   | Swrite s -> Some s
                   | Sskip -> None;;

let rec mem0_sem x0 s = match x0, s with Sskip, s -> s
                   | Swrite uu, (reg, store) -> (reg, reg)
                   | Sread uv, (reg, store) -> (store, store);;

let rec mem_sem
  x = LiftUtils.l_map_s Fun.id
        (LiftInstances.prod_l
          (Fun.comp (Fun.comp LiftInstances.prio_l_inc LiftInstances.option_l)
            LiftInstances.triv_l
            (LiftUtils.extend LiftInstances.id_pl
              (LiftUtils.Lifting_ext ((fun _ a -> a), ()))))
          (LiftInstances.oalist_l
            (Stringa.equal_literal, Stringa.linorder_literal) mem_keys
            (Fun.comp (Fun.comp LiftInstances.prio_l_inc LiftInstances.option_l)
              LiftInstances.triv_l
              (LiftUtils.extend LiftInstances.id_pl
                (LiftUtils.Lifting_ext ((fun _ a -> a), ()))))))
        mem0_sem x;;

let test :
  (Arith.int MergeableInstances.md_triv option) MergeableInstances.md_prio *
    (string,
      (Arith.int MergeableInstances.md_triv option) MergeableInstances.md_prio)
      MergeableAList.oalist
  = mem_sem Sskip
      (test_state (Arith.uminus_int, Arith.zero_int, Arith.numeral_int));;

end;; (*struct Mem*)
