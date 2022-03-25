theory Prog1_Annotated
  imports "../Languages/Imp/Calc_Mem_Imp_Hoare"
begin
text_raw \<open>%Snippet paper_examples__prog1_annotated__comment\<close>
\<comment> \<open>this is a comment\<close>
text_raw \<open>%EndSnippet\<close>
text_raw \<open>%Snippet paper_examples__prog1_annotated__prog1_annotated\<close>
definition prog1_annotated :: "int \<Rightarrow> int \<Rightarrow> syn gensyn" where
"prog1_annotated i1 i2 =
  \<comment> \<open> True \<close>
  \<diamond> (Ss Sseq)
  [ \<comment> \<open> True \<close>
    \<dagger> Sc (Cnum i1)
    \<comment> \<open>reg_c = i1\<close>
  , \<dagger> Sm (Swrite (STR ''arg1'') (Reg_c))
    \<comment> \<open>reg_c = i1; mem[''arg1''] = i1\<close>
  , \<dagger> Sc (Cnum i2)
    \<comment> \<open>reg_c = i2; mem[''arg1''] = i1\<close>
  , \<dagger> Sm (Swrite (STR ''arg2'') (Reg_c))
    \<comment> \<open>reg_c = i2; mem[''arg1''] = i1; mem[''arg2''] = i2\<close>
  , \<dagger> Sc (Cnum 1)
    \<comment> \<open>reg_c = 1; mem[''arg1''] = i1; mem[''arg2''] = i2 \<close>
  , \<dagger> Sm (Swrite (STR ''one'') (Reg_c))
    \<comment> \<open>reg_c = 1; mem[''arg1''] = i1; mem[''arg2''] = i2; mem[''one''] = 1\<close>
  , \<dagger> Sc (Cnum 0)
    \<comment> \<open>reg_c = 0; mem[''arg1''] = i1; mem[''arg2''] = i2; mem[''one''] = 1\<close>
  , \<dagger> Sm (Swrite (STR ''acc'') (Reg_c))
    \<comment> \<open>reg_c = 0; mem[''arg1''] = i1; mem[''arg2''] = i2; mem[''one''] = 1; mem[''acc''] = 0\<close>
  , \<dagger> Sm (Sread (STR ''arg2'') (Reg_c))
    \<comment> \<open>reg_c = i2; mem[''arg1''] = i1; mem[''arg2''] = i2; mem[''one''] = 1; mem[''acc''] = 0\<close>
  , \<dagger> Sb Sgtz
    \<comment> \<open>reg_c = i2; reg_flag = (i2 > 0) mem[''arg1''] = i1; mem[''arg2''] = i2; mem[''one''] = 1; mem[''acc''] = 0\<close>

    \<comment> \<open>
     LOOP INVARIANT I: exists idx such that:
     reg_flag = 1 iff idx > 0;
     mem[''arg1''] = i1; mem[''arg2''] = idx; mem[''one''] = 1;
     mem[''acc''] = i1 * (i2 - idx);
     i2 \<ge> idx;
     
     holds initially for idx = i2\<close>
  , \<diamond> (Si SwhileC)
    [ \<comment> \<open>I; reg_flag = 1\<close>
      \<diamond> (Ss Sseq)
      [ \<comment> \<open>I; reg_flag = 1. We can restate this as:
            mem[''arg1''] = i1; mem[''arg2''] = idx; mem[''one''] = 1;
            mem[''acc''] = i1 * (i2 - idx);
            i2 >= idx; idx > 0\<close>
        \<dagger> Sm (Sread (STR ''arg1'') (Reg_a))
        \<comment> \<open>reg_a = i1;
            mem[''arg1''] = i1; mem[''arg2''] = idx; mem[''one''] = 1;
     	      mem[''acc''] = i1 * (i2 - idx);
     	      i2 >= idx; idx > 0\<close>
      , \<dagger> Sm (Sread (STR ''acc'') (Reg_b))
        \<comment> \<open>reg_a = i1; reg_b = i1 * (i2 - idx);
            mem[''arg1''] = i1; mem[''arg2''] = idx; mem[''one''] = 1;
     	      mem[''acc''] = i1 * (i2 - idx);
     	      i2 >= idx; idx > 0\<close>
      , \<dagger> Sc Cadd
        \<comment> \<open>reg_a = i1; reg_b = i1 * (i2 - idx); reg_c = reg_c = i1 * (i2 - idx) + i1;
            mem[''arg1''] = i1; mem[''arg2''] = idx; mem[''one''] = 1;
     	      mem[''acc''] = i1 * (i2 - idx);
     	      i2 >= idx; idx > 0\<close>
      , \<dagger> Sm (Swrite (STR ''acc'') (Reg_c))
        \<comment> \<open>reg_a = i1; reg_b = i1 * (i2 - idx); reg_c = reg_c = i1 * (i2 - idx) + i1;
            mem[''arg1''] = i1; mem[''arg2''] = idx; mem[''one''] = 1;
     	      mem[''acc''] = i1 * (i2 - idx) + i1;
     	      i2 >= idx; idx > 0\<close>
      , \<dagger> Sm (Sread (STR ''arg2'') (Reg_a))
        \<comment> \<open>reg_a = idx; reg_b = i1 * (i2 - idx); reg_c = reg_c = i1 * (i2 - idx) + i1;
            mem[''arg1''] = i1; mem[''arg2''] = idx; mem[''one''] = 1;
     	      mem[''acc''] = i1 * (i2 - idx) + i1;
     	      i2 >= idx; idx > 0\<close>
      , \<dagger> Sm (Sread (STR ''one'') (Reg_b))
        \<comment> \<open>reg_a = idx; reg_b = 1; reg_c = reg_c = i1 * (i2 - idx) + i1;
            mem[''arg1''] = i1; mem[''arg2''] = idx; mem[''one''] = 1;
     	      mem[''acc''] = i1 * (i2 - idx) + i1;
     	      i2 >= idx; idx > 0\<close>
      , \<dagger> Sc Csub
        \<comment> \<open>reg_a = idx; reg_b = 1; reg_c = idx - 1;
            mem[''arg1''] = i1; mem[''arg2''] = idx; mem[''one''] = 1;
     	      mem[''acc''] = i1 * (i2 - idx) + i1;
     	      i2 >= idx; idx > 0\<close>
      , \<dagger> Sm (Swrite (STR ''arg2'') (Reg_c))
        \<comment> \<open>reg_a = idx; reg_b = 1; reg_c = idx - 1;
            mem[''arg1''] = i1; mem[''arg2''] = idx - 1; mem[''one''] = 1;
     	      mem[''acc''] = i1 * (i2 - idx) + i1;
     	      i2 >= idx; idx > 0\<close>
      , \<dagger> Sm (Sread (STR ''arg2'') (Reg_c))
        \<comment> \<open>reg_a = idx; reg_b = 1; reg_c = idx - 1;
            mem[''arg1''] = i1; mem[''arg2''] = idx - 1; mem[''one''] = 1;
     	      mem[''acc''] = i1 * (i2 - idx) + i1;
     	      i2 >= idx; idx > 0\<close>
      , \<dagger> Sb Sgtz
        \<comment> \<open>reg_a = idx; reg_b = 1; reg_c = idx - 1; reg_flag = 1 iff idx' > 0
            mem[''arg1''] = i1; mem[''arg2''] = idx - 1; mem[''one''] = 1;
     	      mem[''acc''] = i1 * (i2 - idx) + i1;
     	      i2 >= idx\<close>
        \<comment> \<open>let idx' = idx - 1. Then:
            reg_flag = 1 iff idx' > 0;
            mem[''arg1''] = i1; mem[''arg2''] = idx'; mem[''one''] = 1;
            mem[''acc''] = i1 * (i2 - (idx' + 1)) + i1 = i1 * (i2 - idx');
            i2 >= idx'\<close>
        \<comment> \<open>Therefore invariant I is reestablished for idx'\<close>
      ]
    ]
    \<comment> \<open>I; reg_flag = 0\<close>
  ]
  \<comment> \<open>I; reg_flag = 0\<close>"
text_raw \<open>%EndSnippet\<close>
end