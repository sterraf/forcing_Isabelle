theory Rasiowa_Sikorski imports Forcing_Notions Pointed_DC begin

context countable_generic
begin

lemma RS_relation:
  assumes
        1:  "p\<in>P"
            and
        2:  "n\<in>nat"
  shows
            "\<exists>y\<in>P. \<langle>p,y\<rangle> \<in> (\<lambda>m\<in>nat. {\<langle>x,y\<rangle>\<in>P*P. \<langle>y,x\<rangle>\<in>leq \<and> y\<in>\<D>`(pred(m))})`n"
proof -
  from seq_of_denses and 2 have "dense(\<D> ` pred(n))" by (simp)
  with 1 have
            "\<exists>d\<in>\<D> ` Arith.pred(n). \<langle>d, p\<rangle> \<in> leq"
    unfolding dense_def by (simp)
  then obtain d where
        3:  "d \<in> \<D> ` Arith.pred(n) \<and> \<langle>d, p\<rangle> \<in> leq"
    by (rule bexE, simp)
  from countable_subs_of_P have
            "\<D> ` Arith.pred(n) \<in> Pow(P)"
    using 2 by (blast dest:apply_funtype intro:pred_type) (* (rule apply_funtype [OF _ pred_type]) *)
  then have
            "\<D> ` Arith.pred(n) \<subseteq> P" 
    by (rule PowD)
  then have
            "d \<in> P \<and> \<langle>d, p\<rangle> \<in> leq \<and> d \<in> \<D> ` Arith.pred(n)"
    using 3 by auto
  then show ?thesis using 1 and 2 by auto
qed

lemma DC_imp_RS_sequence:
  assumes "p\<in>P"
  shows 
     "\<exists>f. f: nat\<rightarrow>P \<and> f ` 0 = p \<and> 
     (\<forall>n\<in>nat. \<langle>f ` succ(n), f ` n\<rangle> \<in> leq \<and> f ` succ(n) \<in> \<D> ` n)"
proof -
  let ?S="(\<lambda>m\<in>nat. {\<langle>x,y\<rangle>\<in>P*P. \<langle>y,x\<rangle>\<in>leq \<and> y\<in>\<D>`(pred(m))})"
  have "\<forall>x\<in>P. \<forall>n\<in>nat. \<exists>y\<in>P. \<langle>x,y\<rangle> \<in> ?S`n" 
    using RS_relation by (auto)
  then
  have "\<forall>a\<in>P. (\<exists>f \<in> nat\<rightarrow>P. f`0 = a \<and> (\<forall>n \<in> nat. \<langle>f`n,f`succ(n)\<rangle>\<in>?S`succ(n)))"
    using sequence_DC by (blast)
  with \<open>p\<in>P\<close>
  show ?thesis by auto
qed
  
theorem rasiowa_sikorski:
  "p\<in>P \<Longrightarrow> \<exists>G. p\<in>G \<and> D_generic(G)"
  using RS_sequence_imp_rasiowa_sikorski by (auto dest:DC_imp_RS_sequence)

end (* countable_generic *)

end