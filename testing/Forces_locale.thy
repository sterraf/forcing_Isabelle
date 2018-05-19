theory Forces_locale imports Interface forcing_posets begin

locale forcing_data = forcing_poset +
  fixes M enum
  assumes trans_M:          "Transset(M)"
      and M_model_ZF:       "satT(M,ZFTh,[])"
      and M_countable:      "enum\<in>bij(nat,M)"
      and P_in_M:           "P \<in> M"
      and zero_in_M:        "0\<in> M"


begin
lemma to_M_basic_no_repl :
  "M_basic_no_repl(##M)"
  by (insert trans_M M_model_ZF zero_in_M,rule interface_M_basic)

interpretation M?: M_basic_no_repl "##M" by (rule to_M_basic_no_repl)

lemma sep_instance_abs:
  "\<lbrakk> \<phi> \<in> formula ; arity(\<phi>) = 7 ; a1\<in>M ; a2\<in>M ; a3\<in>M ; a4\<in>M ; a5\<in>M ;A\<in>M\<rbrakk> \<Longrightarrow> 
    {x\<in>A. sats(M,\<phi>,[x,A,a1,a2,a3,a4,a5])} \<in> M"
   apply (subgoal_tac "separation(##M,\<lambda>x. sats(M,\<phi>,[x,A,a1,a2,a3,a4,a5]))") 
   apply (simp del:setclass_iff add:setclass_iff[symmetric])
  sorry

end

end