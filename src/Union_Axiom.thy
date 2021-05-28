section\<open>The Axiom of Unions in $M[G]$\<close>
theory Union_Axiom
  imports Names
begin

context forcing_data
begin


definition Union_name_body :: "[i,i,i,i] \<Rightarrow> o" where
  "Union_name_body(P',leq',\<tau>,\<theta>p) \<equiv> (\<exists> \<sigma>[##M].
           \<exists> q[##M]. (q\<in> P' \<and> (\<langle>\<sigma>,q\<rangle> \<in> \<tau> \<and>
            (\<exists> r[##M].r\<in>P' \<and> (\<langle>fst(\<theta>p),r\<rangle> \<in> \<sigma> \<and> \<langle>snd(\<theta>p),r\<rangle> \<in> leq' \<and> \<langle>snd(\<theta>p),q\<rangle> \<in> leq')))))"

definition Union_name_fm :: "i" where
  "Union_name_fm \<equiv>
    Exists(
    Exists(And(pair_fm(1,0,2),
    Exists (
    Exists (And(Member(0,7),
      Exists (And(And(pair_fm(2,1,0),Member(0,6)),
        Exists (And(Member(0,9),
         Exists (And(And(pair_fm(6,1,0),Member(0,4)),
          Exists (And(And(pair_fm(6,2,0),Member(0,10)),
          Exists (And(pair_fm(7,5,0),Member(0,11)))))))))))))))))"

lemma Union_name_fm_type [TC]:
  "Union_name_fm \<in>formula"
  unfolding Union_name_fm_def by simp


lemma arity_Union_name_fm :
  "arity(Union_name_fm) = 4"
  unfolding Union_name_fm_def upair_fm_def pair_fm_def
  by(auto simp add: nat_simp_union)

lemma sats_Union_name_fm :
  "\<lbrakk> env \<in> list(M); P' \<in> M ; p \<in> M ; \<theta> \<in> M ; \<tau> \<in> M ; leq' \<in> M \<rbrakk> \<Longrightarrow>
     sats(M,Union_name_fm,[\<langle>\<theta>,p\<rangle>,\<tau>,leq',P']@env) \<longleftrightarrow>
     Union_name_body(P',leq',\<tau>,\<langle>\<theta>,p\<rangle>)"
  unfolding Union_name_fm_def Union_name_body_def tuples_in_M
  by (subgoal_tac "\<langle>\<theta>,p\<rangle> \<in> M", auto simp add : tuples_in_M)

definition Union_name :: "i \<Rightarrow> i" where
  "Union_name(\<tau>) \<equiv>
    {u \<in> domain(\<Union>(domain(\<tau>))) \<times> P . Union_name_body(P,leq,\<tau>,u)}"

lemma Union_name_M : assumes "\<tau> \<in> M"
  shows "Union_name(\<tau>) \<in> M"
proof -
  let ?P="\<lambda> x . sats(M,Union_name_fm,[x,\<tau>,leq,P])"
  let ?Q="\<lambda> x . Union_name_body(P,leq,\<tau>,x)"
  from \<open>\<tau>\<in>M\<close>
  have "domain(\<Union>(domain(\<tau>)))\<in>M" (is "?d \<in> _") using domain_closed Union_closed by simp
  then
  have "?d \<times> P \<in> M" using cartprod_closed P_in_M by simp
  have "arity(Union_name_fm)\<le>4" using arity_Union_name_fm by simp
  with \<open>\<tau>\<in>M\<close> P_in_M leq_in_M
  have "separation(##M,?P)"
    using separation_ax by simp
  with \<open>?d \<times> P \<in> M\<close>
  have A:"{ u \<in> ?d \<times> P . ?P(u) } \<in> M"
    using separation_iff by force
  have "?P(x)\<longleftrightarrow> ?Q(x)" if "x\<in>?d\<times>P" for x
  proof -
    from \<open>x\<in>?d\<times>P\<close>
    have "x = \<langle>fst(x),snd(x)\<rangle>" using Pair_fst_snd_eq by simp
    with \<open>x\<in>?d\<times>P\<close> \<open>?d\<in>M\<close>
    have "fst(x) \<in> M" "snd(x) \<in> M"
      using transitivity fst_type snd_type P_in_M by auto
    then
    have "?P(\<langle>fst(x),snd(x)\<rangle>) \<longleftrightarrow>  ?Q(\<langle>fst(x),snd(x)\<rangle>)"
      using P_in_M sats_Union_name_fm P_in_M \<open>\<tau>\<in>M\<close> leq_in_M by simp
    with \<open>x = \<langle>fst(x),snd(x)\<rangle>\<close>
    show "?P(x) \<longleftrightarrow> ?Q(x)" using \<open>x\<in>_\<close> by simp
  qed
  then show ?thesis using Collect_cong A unfolding Union_name_def by simp
qed

lemma Union_MG_Eq :
  assumes "a \<in> M[G]" and "a = val(P,G,\<tau>)" and "filter(G)" and "\<tau> \<in> M"
  shows "\<Union> a = val(P,G,Union_name(\<tau>))"
proof -
  {
    fix x
    assume "x \<in> \<Union> (val(P,G,\<tau>))"
    then obtain i where "i \<in> val(P,G,\<tau>)" "x \<in> i" by blast
    with \<open>\<tau> \<in> M\<close> obtain \<sigma> q where
      "q \<in> G" "\<langle>\<sigma>,q\<rangle> \<in> \<tau>" "val(P,G,\<sigma>) = i" "\<sigma> \<in> M"
      using elem_of_val_pair domain_trans[OF trans_M] by blast
    with \<open>x \<in> i\<close> obtain \<theta> r where
      "r \<in> G" "\<langle>\<theta>,r\<rangle> \<in> \<sigma>" "val(P,G,\<theta>) = x" "\<theta> \<in> M"
      using elem_of_val_pair domain_trans[OF trans_M] by blast
    with \<open>\<langle>\<sigma>,q\<rangle>\<in>\<tau>\<close> have "\<theta> \<in> domain(\<Union>(domain(\<tau>)))" by auto
    with \<open>filter(G)\<close> \<open>q\<in>G\<close> \<open>r\<in>G\<close> obtain p where
      A: "p \<in> G" "\<langle>p,r\<rangle> \<in> leq" "\<langle>p,q\<rangle> \<in> leq" "p \<in> P" "r \<in> P" "q \<in> P"
      using low_bound_filter filterD  by blast
    then
    have "p \<in> M" "q\<in>M" "r\<in>M"
      using P_in_M by (auto dest:transM)
    with A \<open>\<langle>\<theta>,r\<rangle> \<in> \<sigma>\<close> \<open>\<langle>\<sigma>,q\<rangle> \<in> \<tau>\<close> \<open>\<theta> \<in> M\<close> \<open>\<theta> \<in> domain(\<Union>(domain(\<tau>)))\<close>  \<open>\<sigma>\<in>M\<close>
    have "\<langle>\<theta>,p\<rangle> \<in> Union_name(\<tau>)"
      unfolding Union_name_def Union_name_body_def
      by auto
    with \<open>p\<in>P\<close> \<open>p\<in>G\<close>
    have "val(P,G,\<theta>) \<in> val(P,G,Union_name(\<tau>))"
      using val_of_elem by simp
    with \<open>val(P,G,\<theta>)=x\<close>
    have "x \<in> val(P,G,Union_name(\<tau>))" by simp
  }
  with \<open>a=val(P,G,\<tau>)\<close>
  have 1: "x \<in> \<Union> a \<Longrightarrow> x \<in> val(P,G,Union_name(\<tau>))" for x by simp
  {
    fix x
    assume "x \<in> (val(P,G,Union_name(\<tau>)))"
    then obtain \<theta> p where
      "p \<in> G" "\<langle>\<theta>,p\<rangle> \<in> Union_name(\<tau>)" "val(P,G,\<theta>) = x"
      using elem_of_val_pair by blast
    with \<open>filter(G)\<close> have "p\<in>P" using filterD by simp
    from \<open>\<langle>\<theta>,p\<rangle> \<in> Union_name(\<tau>)\<close> obtain \<sigma> q r where
      "\<sigma> \<in> domain(\<tau>)"  "\<langle>\<sigma>,q\<rangle> \<in> \<tau> " "\<langle>\<theta>,r\<rangle> \<in> \<sigma>" "r\<in>P" "q\<in>P" "\<langle>p,r\<rangle> \<in> leq" "\<langle>p,q\<rangle> \<in> leq"
      unfolding Union_name_def Union_name_body_def by force
    with \<open>p\<in>G\<close> \<open>filter(G)\<close> have "r \<in> G" "q \<in> G"
      using filter_leqD by auto
    with \<open>\<langle>\<theta>,r\<rangle> \<in> \<sigma>\<close> \<open>\<langle>\<sigma>,q\<rangle>\<in>\<tau>\<close> \<open>q\<in>P\<close> \<open>r\<in>P\<close> have
      "val(P,G,\<sigma>) \<in> val(P,G,\<tau>)" "val(P,G,\<theta>) \<in> val(P,G,\<sigma>)"
      using val_of_elem by simp+
    then have "val(P,G,\<theta>) \<in> \<Union> val(P,G,\<tau>)" by blast
    with \<open>val(P,G,\<theta>)=x\<close> \<open>a=val(P,G,\<tau>)\<close> have
      "x \<in> \<Union> a" by simp
  }
  with \<open>a=val(P,G,\<tau>)\<close>
  have "x \<in> val(P,G,Union_name(\<tau>)) \<Longrightarrow> x \<in> \<Union> a" for x by blast
  then
  show ?thesis using 1 by blast
qed

lemma union_in_MG : assumes "filter(G)"
  shows "Union_ax(##M[G])"
proof -
  { fix a
    assume "a \<in> M[G]"
    then
    interpret mgtrans : M_trans "##M[G]"
      using transitivity_MG by (unfold_locales; auto)
    from \<open>a\<in>_\<close> obtain \<tau> where "\<tau> \<in> M" "a=val(P,G,\<tau>)" using GenExtD by blast
    then
    have "Union_name(\<tau>) \<in> M" (is "?\<pi> \<in> _") using Union_name_M unfolding Union_name_def by simp
    then
    have "val(P,G,?\<pi>) \<in> M[G]" (is "?U \<in> _") using GenExtI by simp
    with \<open>a\<in>_\<close>
    have "(##M[G])(a)" "(##M[G])(?U)" by auto
    with \<open>\<tau> \<in> M\<close> \<open>filter(G)\<close> \<open>?U \<in> M[G]\<close> \<open>a=val(P,G,\<tau>)\<close>
    have "big_union(##M[G],a,?U)"
      using Union_MG_Eq Union_abs by simp
    with \<open>?U \<in> M[G]\<close>
    have "\<exists>z[##M[G]]. big_union(##M[G],a,z)" by auto
  }
  then
  show ?thesis unfolding Union_ax_def by simp
qed

theorem Union_MG : "M_generic(G) \<Longrightarrow> Union_ax(##M[G])"
  by (simp add:M_generic_def union_in_MG)

end (* forcing_data *)
end