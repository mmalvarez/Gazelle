theory Merge_Syntax imports "Syntax"

begin

fun flip :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'c)" where
"flip f b a = f a b"

fun olift :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a option \<Rightarrow> 'b option" where
"olift f None = None"
| "olift f (Some x) = Some (f x)"

fun osmash :: "('a option \<Rightarrow> 'b option) \<Rightarrow> 'a \<Rightarrow> 'b option" where
"osmash f x = f (Some x)"

fun obnd :: "'a option \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> 'b option" (infixl "|>" 400) where
"obnd (Some a) f = (f a)"
| "obnd None _ = None"

fun liftl :: "('l, 'xp, 'xsl) mpackf \<Rightarrow> ('l, 'xp, ('r, 'xsl + 'xsr) mmpack) mpackf"
  where
"liftl (c, p, Inl l) = (c, p, Inl l)"
| "liftl (c, p, Inr xsl) = (c, p, Inr (Inr (Inl xsl)))"

fun lowerl :: "('l, 'xp, ('r, 'xsl + 'xsr) mmpack) mpackf \<Rightarrow> ('l, 'xp, 'xsl) mpackf option"
  where
"lowerl (c, p, Inl l) = Some (c, p, Inl l)"
| "lowerl (c, p, Inr (Inr (Inl xsl))) = Some (c, p, Inr xsl)"
| "lowerl _ = None"

fun liftxl :: "(char list * 'xp * ('xsl)) \<Rightarrow>
                (char list * 'xp * ('xsl + 'xsr))" where
"liftxl (c, p, xsl) = (c, p, Inl xsl)"

fun lowerxl :: "(char list * 'xp * ('xsl + 'xsr)) \<Rightarrow>
                (char list * 'xp * 'xsl) option" where
"lowerxl (c, p, Inl l) = Some (c, p, l)"
| "lowerxl _ = None"


fun liftr :: "('r, 'xp, 'xsr) mpackf \<Rightarrow> ('l, 'xp, ('r, 'xsl + 'xsr) mmpack) mpackf"
  where
"liftr (c, p, Inl l) = (c, p, Inr ((Inl l)))"
| "liftr (c, p, Inr xsr) = (c, p, Inr (Inr (Inr (xsr))))"


fun liftxr :: "(char list * 'xp * ('xsr)) \<Rightarrow>
                (char list * 'xp * ('xsl + 'xsr))" where
"liftxr (c, p, xsr) = (c, p, Inr xsr)"


fun lowerxr :: "(char list * 'xp * ('xsl + 'xsr)) \<Rightarrow>
                (char list * 'xp * 'xsr) option" where
"lowerxr (c, p, Inr r) = Some (c, p, r)"
| "lowerxr _ = None"


fun lowerr :: "('l, 'xp, ('r, 'xsl + 'xsr) mmpack) mpackf \<Rightarrow> ('r, 'xp, 'xsr) mpackf option"
  where
"lowerr (c, p, Inr (Inl l)) = Some (c, p, Inl l)"
| "lowerr (c, p, Inr (Inr (Inr xsr))) = Some (c, p, Inr xsr)"
| "lowerr _ = None"

fun merge_others ::
"(char list \<Rightarrow> reified \<Rightarrow> (char list * 'xp * 'xsl) option) \<Rightarrow>
 (char list \<Rightarrow> reified \<Rightarrow> (char list * 'xp * 'xsr) option) \<Rightarrow>
 (char list \<Rightarrow> reified \<Rightarrow> (char list * 'xp * ('xsl + 'xsr)) option)"   where
"merge_others f1 f2 c r =
  (case f1 c r of
    None \<Rightarrow> (case f2 c r of
              None \<Rightarrow> None
              | Some (c', xp, r') \<Rightarrow> Some (c', xp, Inr r'))
  | Some (c', xp, l') \<Rightarrow> Some (c', xp, Inl l'))"


locale Syn_Merge =

fixes rxl :: "'l \<Rightarrow> reified"
fixes dxl :: "reified \<Rightarrow> 'l"
fixes rxr :: "'r \<Rightarrow> reified"
fixes dxr :: "reified \<Rightarrow> 'r"
fixes rxp :: "'xp \<Rightarrow> reified"
fixes dxp :: "reified \<Rightarrow> 'xp"

fixes C'l ::
  "char list \<Rightarrow> reified  \<Rightarrow>
    (char list \<Rightarrow> reified \<Rightarrow> (char list * 'xp * 'xsl) option) \<Rightarrow>
     ('l, 'xp, 'xsl) mpackf option"

(* need "others" or just inline? *)
fixes othersl ::
"(char list \<Rightarrow> reified \<Rightarrow> (char list * 'xp * 'xsl) option)"

fixes C'r ::
  "char list \<Rightarrow> reified  \<Rightarrow> 
  (char list \<Rightarrow> reified \<Rightarrow> (char list * 'xp * 'xsr) option) \<Rightarrow>
  ('r, 'xp, 'xsr) mpackf option"

fixes othersr ::
"(char list \<Rightarrow> reified \<Rightarrow> (char list * 'xp * 'xsr) option)"

begin


(* might be worth proving correctness of these, will probably do later *)


definition C' ::
  "char list \<Rightarrow> reified \<Rightarrow> 
    (char list \<Rightarrow> reified \<Rightarrow> (char list * 'xp * ('xsl + 'xsr)) option) \<Rightarrow>
    ('l, 'xp, ('r, 'xsl + 'xsr) mmpack) mpackf option" where
"C' s data other =
  (case
      C'l s data (\<lambda> c r .
                    (case other c r of
                      None \<Rightarrow> None
                      | Some (c', xp, Inr _) \<Rightarrow> None
                      | Some (c', xp, Inl xsl) \<Rightarrow> Some (c', xp, xsl)))
      of
        None \<Rightarrow> (case (C'r s data (\<lambda> c r .
                    (case other c r of
                     None \<Rightarrow> None
                     | Some (c', xp, Inl _) \<Rightarrow> None
                     | Some (c', xp, Inr xsr) \<Rightarrow> Some (c', xp, xsr)))) of
                  None \<Rightarrow> None
                | Some (c', xp, xcr) \<Rightarrow> Some (liftr (c', xp, xcr)))
      | Some (c', xp, xcl) \<Rightarrow> Some (liftl (c', xp, xcl)))" 

definition C ::
  "char list \<Rightarrow> reified \<Rightarrow> reified \<Rightarrow>
  ('l, 'xp, ('r, 'xsl + 'xsr) mmpack) mpackf option" where
"C s xp i =
  (C' s (rpair xp i) (merge_others othersl othersr))"

(*(\<lambda> s' data' .
    (case other s' data' of
      Some (c, p, l) \<Rightarrow> Some (c, p, Inl l)
    | None \<Rightarrow> None))"
*)

end

end  