theory Seq_Semantics imports "Gensyn_Semantics_TypeParam" "../Syntax/Syn_Seq"
begin

locale Seq_Semantics_Sig =
  fixes xr :: "'xr itself"
  fixes ms :: "'mstate itself"
  fixes seq_sem :: "'g \<Rightarrow> 'sq \<Rightarrow> 'mstate \<Rightarrow> 'mstate \<Rightarrow> bool"

inductive seq_nop :: "'g \<Rightarrow> 'sq \<Rightarrow> 'mstate \<Rightarrow> 'mstate \<Rightarrow> bool" where
"seq_nop _ _ m m"

locale Seq_Semantics = Seq_Semantics_Sig 
begin

print_context

(* problem - this specifies next behavior for all base nodes
   is that really what we want? it may actually be, i'm just not sure. *)
(* another option is to just have this encapsulate descending into a base
   node and handling "next" elsewhere, perhaps at the "elle" level... *)
(* a third option is to only use "unhandled" cases *)
(* another way to get at this: what should the hierarchy look like? *)
(* hierarchy: can we worry about it later? *)
inductive seq_rec_sem :: "'c \<Rightarrow> ('d, 'xb, 'xa) syn_seq \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow>
  childpath \<Rightarrow> ('bs, ('d, 'xb, 'xa) syn_seq, 'c) gensyn \<Rightarrow> ('a) gs_result \<Rightarrow> bool" where
"seq_sem g s m m' \<Longrightarrow> seq_rec_sem g (LSeq s) m m' cp sk (GRPath (cp@[0]))"

end

(* sublocale Seq_Semantics \<subseteq> Gensyn_Semantics
  ...
*)

locale Base_Next_Semantics = Gensyn_Semantics_Base_Sig 
begin

print_context

inductive base_sem_next ::
    "'c \<Rightarrow> 'd \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> childpath \<Rightarrow>
            ('d, 'e, 'c) gensyn \<Rightarrow>
                 ('a) gs_result \<Rightarrow> bool"
    where
"base_sem g b m m' cp t GRUnhandled \<Longrightarrow>
 gensyn_cp_next t cp = Some cp' \<Longrightarrow>
  base_sem_next g b m m' cp t (GRPath cp')"
| "base_sem g b m m' cp t GRUnhandled \<Longrightarrow>
  gensyn_cp_next t cp = None \<Longrightarrow>
  base_sem_next g b m m' cp t (GRDone)"
| "base_sem g b m m' cp t res \<Longrightarrow>
  base_sem_next g b m m' cp t res"

end

(*
locale Seq_Next_Semantics = Seq_Semantics +
  fixes base_sem :: "'g \<Rightarrow> 'b \<Rightarrow> 'mstate \<Rightarrow> 'mstate \<Rightarrow> childpath \<Rightarrow>
                 ('b, ('sq, 'xbr, 'xar) syn_seq, 'g) gensyn \<Rightarrow>
                     ('xrs) gs_result \<Rightarrow> bool"

begin

inductive base_sem_next ::
    "'g \<Rightarrow> 'b \<Rightarrow> 'mstate \<Rightarrow> 'mstate \<Rightarrow> childpath \<Rightarrow>
            ('b, ('sq, 'xbr, 'xar) syn_seq, 'g) gensyn \<Rightarrow>
                 ('xrs) gs_result \<Rightarrow> bool"
    where
"base_sem g b m m' cp t GRUnhandled \<Longrightarrow>
 gensyn_cp_next t cp = Some cp' \<Longrightarrow>
  base_sem_next g b m m' cp t (GRPath cp')"
| "base_sem g b m m' cp t GRUnhandled \<Longrightarrow>
  gensyn_cp_next t cp = None \<Longrightarrow>
  base_sem_next g b m m' cp t (GRDone)"
| "base_sem g b m m' cp t res \<Longrightarrow>
  base_sem_next g b m m' cp t res"

end
*)
end