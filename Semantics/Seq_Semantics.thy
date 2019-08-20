theory Seq_Semantics imports "Gensyn_Semantics_Fuse2" "../Syntax/Syn_Seq"
begin

locale Seq_Semantics_Sig =
  fixes seq_sem :: "'g \<Rightarrow> 'sq \<Rightarrow> 'mstate \<Rightarrow> 'mstate \<Rightarrow> bool"



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
inductive seq_rec_sem :: "'a \<Rightarrow> ('b, 'xb, 'xa) syn_seq \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow>
  childpath \<Rightarrow> ('bs, ('b, 'xb, 'xa) syn_seq, 'a) gensyn \<Rightarrow> ('xr) gs_result \<Rightarrow> bool" where
"seq_sem g s m m' \<Longrightarrow> seq_rec_sem g (LSeq s) m m' cp sk (GRPath (cp@[0]))"

end

(* sublocale Seq_Semantics \<subseteq> Gensyn_Semantics
  ...
*)

locale Base_Next_Semantics = Gensyn_Semantics_Base_Sig 
begin
inductive base_sem_next ::
    "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> childpath \<Rightarrow>
            ('b, 'd, 'a) gensyn \<Rightarrow>
                 ('e) gs_result \<Rightarrow> bool"
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