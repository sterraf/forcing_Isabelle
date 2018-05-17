theory Forces_locale imports Interface begin

locale forcing_poset =
  fixes P leq uno
  assumes uno_in_P:         "uno \<in> P"
      and leq_preord:       "preorder_on(P,leq)"
      and uno_max:          "\<forall>p\<in>P. <p,uno>\<in>leq"

locale forcing_data = forcing_poset +
  fixes M enum
  assumes trans_M:          "Transset(M)"
      and M_model_ZF:       "satT(M,ZFTh,[])"
      and M_countable:      "enum\<in>bij(nat,M)"
      and P_in_M:           "P \<in> M"
      (* TODO: Quitar estas assumptions cuando tengamos el Relative hacked *)
      and M_repl:           "\<And>P. replacement(##M,P)"
      and M_nat:            "nat \<in> M"


begin
lemma to_M_basic :
  "PROP M_basic(##M)"
  by (insert trans_M M_model_ZF M_repl M_nat,rule interface_M_basic)

interpretation M?: M_basic "##M" by (rule to_M_basic)

lemma sep_instance_abs:
  "\<lbrakk> \<phi> \<in> formula ; arity(\<phi>) = 7 ; a1\<in>M ; a2\<in>M ; a3\<in>M ; a4\<in>M ; a5\<in>M ;A\<in>M\<rbrakk> \<Longrightarrow> 
    {x\<in>A. sats(M,\<phi>,[x,A,a1,a2,a3,a4,a5])} \<in> M"
   apply (subgoal_tac "separation(##M,\<lambda>x. sats(M,\<phi>,[x,A,a1,a2,a3,a4,a5]))") 
   apply (simp del:setclass_iff add:setclass_iff[symmetric])
  sorry

end

end