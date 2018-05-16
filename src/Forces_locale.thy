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

(* TODO: Quitar assumptions cuando tengamos el Relative hacked *)
lemma (in forcing_data) to_M_basic :
  "\<lbrakk> \<And>P. replacement(##M,P) ; nat \<in> M \<rbrakk> \<Longrightarrow> PROP M_basic(##M)"
  by (insert trans_M M_model_ZF,rule interface_M_basic)


end