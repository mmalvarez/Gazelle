theory MergeableRAlist2
  imports MergeableAList

begin

(* implementation and Mergeable
   instances for a recursive version of ordered alist
   (i.e., ordered alist where values are ordered alists of the same type)
   this is needed for e.g. closures. *)

fun alist_map_val ::
  "('v1 \<Rightarrow> 'v2) \<Rightarrow> ('key * 'v1) list \<Rightarrow> ('key * 'v2) list" where
"alist_map_val f l =
  map (map_prod id f) l"
(*
"alist_map_val f [] = []"
| "alist_map_val f ((k, v)#t) =
   ((k, f v)# alist_map_val f t)"
*)

lemma strict_order_nil : "strict_order []"
  by(rule strict_order_intro; auto)

lift_definition
  oalist_map_val ::
  "('v1 \<Rightarrow> 'v2) \<Rightarrow> ('key :: linorder, 'v1) oalist \<Rightarrow> ('key, 'v2) oalist"
 is alist_map_val
  by (auto intro: strict_order_nil)


declare [[show_types]]
lift_bnf (dead 'k :: linorder, 'v) oalist [wits: "Nil :: (('k :: linorder) * 'v) list"]
  by(auto intro: strict_order_nil) 

(* TODO: use gensyn here instead? *)
datatype ('key, 'value) ralist =
  RA "('key * ('value + ('key, 'value) ralist)) list"

(* another option: maybe we can somehow represent the alist in a way that isn't explicitly
   recursive.
e.g. suppose we want an alist clos = (str \<Rightarrow> (int + clos))
maybe we can capture the nesting in the index?

(str * closid \<Rightarrow> (int + closid))?
problem: risk of infinite recursion
maybe this is OK though. all we really need to do is reconstruct the closure stored at each thing.
if the closures are infinite our implementation will spin. but maybe this is ap 

so, at closid = 0
*)

declare [[typedef_overloaded]]
datatype ('key :: linorder, 'value) roalist  =
  RL "('key, ('value + ('key, 'value) roalist)) oalist"

fun ralist_leq :: "('key :: linorder, 'value :: Pord) ralist \<Rightarrow> ('key, 'value) ralist \<Rightarrow> bool" where
"ralist_leq (RA []) (RA _) = True"
| "ralist_leq (RA ((a, Inl bv)#l1')) (RA l2) =
  (case map_of l2 a of
    Some (Inl bv') \<Rightarrow> (pleq bv bv' \<and> ralist_leq (RA l1') (RA l2))
    | _ \<Rightarrow> False)"
| "ralist_leq (RA ((a, Inr bl)#l1')) (RA l2) =
  (case map_of l2 a of
    Some (Inr bl') \<Rightarrow> (ralist_leq bl bl' \<and> ralist_leq (RA l1') (RA l2))
    | _ \<Rightarrow> False)"

(*
fun roalist_unwrap :: "('key :: linorder, 'value) roalist \<Rightarrow> ('key, 'value) ralist" where
"roalist_unwrap (RL l) =
  RA (map (\<lambda> x .
    (case x of
      (k, Inl v) \<Rightarrow> (k, Inl v)
      | (k, Inr l) \<Rightarrow> (k, Inr (roalist_unwrap l)))) (impl_of l))"  
*)

(* proving termination on this is too hard lolol *)
function (sequential) ralist_size' ::  "('key :: linorder * ('value + ('key, 'value :: Pord) roalist)) list \<Rightarrow> nat"
  where
"ralist_size' [] = 1"
| "ralist_size' ((a, Inl bv)#l') = 1 + ralist_size' l'"
| "ralist_size' ((a, Inr (RL bl))#l') = 1 + ralist_size' (impl_of bl) + ralist_size' l'"
  by pat_completeness (auto split: option.splits prod.splits sum.splits)
termination 
  apply(relation "measure (\<lambda> l . length l)")
  apply(lexicographic_order)
fun roalist_size :: "('k :: linorder, 'v) roalist \<Rightarrow> nat" where
"roalist_size (RL l) = 
  (case (impl_of l) of
    [] \<Rightarrow> 1
    | Inl h # t \<Rightarrow> 1 + ra"
| "ralist_size (RL (Inl h # t)) = 1 + ralist_size t


function (sequential) ralist_leq' ::
  "('key :: linorder * ('value + ('key, 'value :: Pord) roalist)) list \<Rightarrow>
   ('key * ('value + ('key, 'value) roalist)) list \<Rightarrow>
   bool" where
"ralist_leq' [] _ = True"
| "ralist_leq' ((a, Inl bv)#l1') l2 =
  (case map_of l2 a of
    Some (Inl bv') \<Rightarrow> (pleq bv bv' \<and> ralist_leq' l1' l2)
    | _ \<Rightarrow> False)"
| "ralist_leq' ((a, Inr (RL bl))#l1') l2 =
  (case map_of l2 a of
    Some (Inr (RL bl')) \<Rightarrow> (ralist_leq' (impl_of bl) (impl_of bl') \<and> ralist_leq' l1' l2)
    | _ \<Rightarrow> False)"
  by pat_completeness (auto split: option.splits prod.splits sum.splits)
termination 
  apply(lexicographic_order)

lift_definition roalist_leq' :: "('key :: linorder, ('value :: Pord + ('key, 'value) roalist)) oalist \<Rightarrow> ('key, ('value + ('key, 'value) roalist)) oalist \<Rightarrow> bool"
is ralist_leq' .

fun roalist_leq :: "('k :: linorder, 'v :: Pord) roalist \<Rightarrow> ('k, 'v) roalist \<Rightarrow> bool" where
"roalist_leq (RL l1) (RL l2) = roalist_leq' l1 l2"
(*
lift_definition roalist_leq :: "('key :: linorder, 'value :: Pord) roalist \<Rightarrow> ('key, 'value) roalist \<Rightarrow> bool"
is ralist_leq
*)

fun roalist_leq :: "('key :: linorder, 'value) roalist \<Rightarrow> ('key, 'value) roalist \<Rightarrow> bool" where
"roalist_leq (RL []) (RL _) = True"
| "roalist_leq (RL ((a, b)#l1')
  

instantiation roalist :: (linorder, Pord) Pord begin


end

