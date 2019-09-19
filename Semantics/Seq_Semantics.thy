theory Seq_Semantics imports "Gensyn_Semantics" "../Syntax/Syn_Seq"
begin

locale Seq_Semantics_Sig =
  fixes xr :: "'xr itself"
  fixes ms :: "'mstate itself"
  fixes seq_sem :: "'sq \<Rightarrow> 'mstate \<Rightarrow> 'mstate \<Rightarrow> bool"

inductive seq_nop :: "'sq \<Rightarrow> 'mstate \<Rightarrow> 'mstate \<Rightarrow> bool" where
"seq_nop _ m m"

locale Seq_Semantics = Seq_Semantics_Sig 
begin

print_context

inductive x_sem_seq :: "('c, 'xp, 'xs) syn_seq \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow>
  childpath \<Rightarrow> ('c, 'xp, 'xs) syn_seq gensyn \<Rightarrow> ('a) gs_result \<Rightarrow> bool" where
"seq_sem s m m' \<Longrightarrow> x_sem_seq (LSeq s xp) m m' cp g (GRPath (cp@[0]))"

end

(* sublocale Seq_Semantics \<subseteq> Gensyn_Semantics
  ...
*)

locale Base_Next_Semantics = Gensyn_Semantics_Sig
begin

print_context

inductive x_sem_next ::
    "'c \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> childpath \<Rightarrow>
            ('c) gensyn \<Rightarrow>
                 ('a) gs_result \<Rightarrow> bool"
    where
"x_sem x m m' cp t GRUnhandled \<Longrightarrow>
 gensyn_cp_next t cp = Some cp' \<Longrightarrow>
  x_sem_next x m m' cp t (GRPath cp')"
| "x_sem x m m' cp t GRUnhandled \<Longrightarrow>
  gensyn_cp_next t cp = None \<Longrightarrow>
  x_sem_next x m m' cp t (GRDone)"
| "x_sem x m m' cp t res \<Longrightarrow>
  x_sem_next x m m' cp t res"

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