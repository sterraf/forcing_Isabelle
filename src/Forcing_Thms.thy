theory Forcing_Thms
  imports
    Forces_Definition

begin

context forces_rename
begin

lemma leq_transD:  "\<langle>a,b\<rangle> \<in> leq \<Longrightarrow> \<langle>b,c\<rangle> \<in> leq \<Longrightarrow> a \<in> P\<Longrightarrow> b \<in> P\<Longrightarrow> c \<in> P\<Longrightarrow> \<langle>a,c\<rangle> \<in> leq"
  using leq_preord trans_onD unfolding preorder_on_def by blast

lemma leq_reflI: "p\<in>P \<Longrightarrow> <p,p>\<in>leq"
 using leq_preord unfolding preorder_on_def refl_def by blast

lemma dense_belowD [dest]: 
  assumes "dense_below(D,p)" "q\<in>P" "<q,p>\<in>leq"
  shows "\<exists>d\<in>D. d\<in>P \<and> <d,q>\<in>leq"
  using assms unfolding dense_below_def by simp
(*obtains d where "d\<in>D" "d\<in>P" "<d,q>\<in>leq"
  using assms unfolding dense_below_def by blast *)

lemma dense_belowI [intro!]: 
  assumes "\<And>q. q\<in>P \<Longrightarrow> <q,p>\<in>leq \<Longrightarrow> \<exists>d\<in>D. d\<in>P \<and> <d,q>\<in>leq" 
  shows "dense_below(D,p)"
  using assms unfolding dense_below_def by simp

lemma dense_below_cong: "p\<in>P \<Longrightarrow> D = D' \<Longrightarrow> dense_below(D,p) \<longleftrightarrow> dense_below(D',p)"
  by blast

lemma dense_below_cong': "p\<in>P \<Longrightarrow> \<lbrakk>\<And>x. x\<in>P \<Longrightarrow> Q(x) \<longleftrightarrow> Q'(x)\<rbrakk> \<Longrightarrow> 
           dense_below({q\<in>P. Q(q)},p) \<longleftrightarrow> dense_below({q\<in>P. Q'(q)},p)"
  by blast

lemma dense_below_mono: "p\<in>P \<Longrightarrow> D \<subseteq> D' \<Longrightarrow> dense_below(D,p) \<Longrightarrow> dense_below(D',p)"
  by blast

lemma dense_below_under:
  assumes "dense_below(D,p)" "p\<in>P" "q\<in>P" "<q,p>\<in>leq"
  shows "dense_below(D,q)"
  using assms leq_transD by blast

lemma ideal_dense_below:
  assumes "\<And>q. q\<in>P \<Longrightarrow> <q,p>\<in>leq \<Longrightarrow> q\<in>D"
  shows "dense_below(D,p)"
  using assms leq_reflI by blast

lemma dense_below_dense_below: 
  assumes "dense_below({q\<in>P. dense_below(D,q)},p)" "p\<in>P" 
  shows "dense_below(D,p)"  
  using assms leq_transD leq_reflI  by blast
(* Long proof *)
(*  unfolding dense_below_def
proof (intro ballI impI)
  fix r
  assume "r\<in>P" \<open><r,p>\<in>leq\<close>
  with assms
  obtain q where "q\<in>P" "<q,r>\<in>leq" "dense_below(D,q)"
    using assms by auto
  moreover from this
  obtain d where "d\<in>P" "<d,q>\<in>leq" "d\<in>D"
    using assms leq_preord unfolding preorder_on_def refl_def by blast
  moreover
  note \<open>r\<in>P\<close>
  ultimately
  show "\<exists>d\<in>D. d \<in> P \<and> \<langle>d, r\<rangle> \<in> leq"
    using leq_preord trans_onD unfolding preorder_on_def by blast
qed *)

lemma forces_mem_iff_dense_below:  "p\<in>P \<Longrightarrow> forces_mem(P,leq,p,t1,t2) \<longleftrightarrow> dense_below(
    {q\<in>P. \<exists>s. \<exists>r. r\<in>P \<and> <s,r> \<in> t2 \<and> <q,r>\<in>leq \<and> forces_eq(P,leq,q,t1,s)}
    ,p)"
  using def_forces_mem[of p t1 t2] by blast

lemma strengthening_eq: 
  assumes "p\<in>P" "r\<in>P" "<r,p>\<in>leq" "forces_eq(P,leq,p,t1,t2)"
  shows "forces_eq(P,leq,r,t1,t2)"
  using assms def_forces_eq[of _ t1 t2] leq_transD by blast
(* Long proof *)
(*
proof -
  {
    fix s q
    assume "\<langle>q, r\<rangle> \<in> leq" "q\<in>P"
    with assms
    have "<q,p>\<in>leq"
      using leq_preord unfolding preorder_on_def trans_on_def by blast
    moreover 
    note \<open>q\<in>P\<close> assms
    moreover
    assume "s\<in>domain(t1) \<union> domain(t2)" 
    ultimately
    have "forces_mem(P, leq, q, s, t1) \<longleftrightarrow> forces_mem(P, leq, q, s, t2)"
      using def_forces_eq[of p t1 t2] by simp
  }
  with \<open>r\<in>P\<close>
  show ?thesis using def_forces_eq[of r t1 t2] by blast
qed
*)

lemma strengthening_mem: 
  assumes "p\<in>P" "r\<in>P" "<r,p>\<in>leq" "forces_mem(P,leq,p,t1,t2)"
  shows "forces_mem(P,leq,r,t1,t2)"
  using assms forces_mem_iff_dense_below dense_below_under by auto

lemma density_mem: 
  assumes "p\<in>P"
  shows "forces_mem(P,leq,p,t1,t2)  \<longleftrightarrow> dense_below({q\<in>P. forces_mem(P,leq,q,t1,t2)},p)"
proof
  assume "forces_mem(P,leq,p,t1,t2)"
  with assms
  show "dense_below({q\<in>P. forces_mem(P,leq,q,t1,t2)},p)"
    using forces_mem_iff_dense_below strengthening_mem[of p] ideal_dense_below by auto
next
  assume "dense_below({q \<in> P . forces_mem(P, leq, q, t1, t2)}, p)"
  with assms
  have "dense_below({q\<in>P. 
    dense_below({q'\<in>P. \<exists>s r. r \<in> P \<and> \<langle>s,r\<rangle>\<in>t2 \<and> \<langle>q',r\<rangle>\<in>leq \<and> forces_eq(P,leq,q',t1,s)},q)
    },p)"
    using forces_mem_iff_dense_below by simp
  with assms
  show "forces_mem(P,leq,p,t1,t2)"
    using dense_below_dense_below forces_mem_iff_dense_below[of p t1 t2] by blast
qed

lemma density_eq:
  assumes "p\<in>P"
  shows "forces_eq(P,leq,p,t1,t2)  \<longleftrightarrow> dense_below({q\<in>P. forces_eq(P,leq,q,t1,t2)},p)"
proof
  assume "forces_eq(P,leq,p,t1,t2)"
  with \<open>p\<in>P\<close>
  show "dense_below({q\<in>P. forces_eq(P,leq,q,t1,t2)},p)"
    using strengthening_eq ideal_dense_below by auto
next
  assume "dense_below({q\<in>P. forces_eq(P,leq,q,t1,t2)},p)"
  {
    fix s q 
    let ?D1="{q'\<in>P. \<forall>s\<in>domain(t1) \<union> domain(t2). \<forall>q. q \<in> P \<and> \<langle>q,q'\<rangle>\<in>leq \<longrightarrow>
           forces_mem(P,leq,q,s,t1)\<longleftrightarrow>forces_mem(P,leq,q,s,t2)}"
    let ?D2="{q'\<in>P. \<forall>q. q\<in>P \<and> \<langle>q,q'\<rangle>\<in>leq \<longrightarrow> forces_mem(P,leq,q,s,t1) \<longleftrightarrow> forces_mem(P,leq,q,s,t2)}"
    assume "s\<in>domain(t1) \<union> domain(t2)" "q \<in> P" "<q,p>\<in>leq"
    then
    have "?D1\<subseteq>?D2" by blast
    with \<open>dense_below(_,p)\<close>
    have "dense_below({q'\<in>P. \<forall>s\<in>domain(t1) \<union> domain(t2). \<forall>q. q \<in> P \<and> \<langle>q,q'\<rangle>\<in>leq \<longrightarrow>
           forces_mem(P,leq,q,s,t1)\<longleftrightarrow>forces_mem(P,leq,q,s,t2)},p)"
      using dense_below_cong'[OF \<open>p\<in>P\<close> def_forces_eq[of _ t1 t2]] by simp
    with \<open>p\<in>P\<close> \<open>?D1\<subseteq>?D2\<close>
    have dbp:"dense_below({q'\<in>P. \<forall>q. q\<in>P \<and> \<langle>q,q'\<rangle>\<in>leq \<longrightarrow> 
            forces_mem(P,leq,q,s,t1) \<longleftrightarrow> forces_mem(P,leq,q,s,t2)},p)"
      using dense_below_mono by simp
    have "forces_mem(P,leq,q,s,t1) \<Longrightarrow> dense_below({r\<in>P. forces_mem(P,leq,r,s,t2)},q)"
    proof
      fix r
      assume "r\<in>P" "\<langle>r,q\<rangle> \<in> leq"
      moreover from this and \<open>p\<in>P\<close> \<open><q,p>\<in>leq\<close> \<open>q\<in>P\<close>
      have "<r,p>\<in>leq"
        using leq_transD by simp
      moreover
      assume "forces_mem(P,leq,q,s,t1)" 
      moreover 
      note dbp \<open>q\<in>P\<close>
      ultimately
      obtain q1 where "<q1,r>\<in>leq" "q1\<in>P" "forces_mem(P,leq,q1,s,t2)"
        using strengthening_mem[of q _ s t1] leq_reflI leq_transD[of _ r q] by blast
      then
      show "\<exists>d\<in>{r \<in> P . forces_mem(P, leq, r, s, t2)}. d \<in> P \<and> \<langle>d, r\<rangle> \<in> leq"
        by blast
    qed
    moreover
    have "forces_mem(P,leq,q,s,t2) \<Longrightarrow> dense_below({r\<in>P. forces_mem(P,leq,r,s,t1)},q)"
    proof (* Copy-paste of previous proof. FIX THIS*)
      fix r
      assume "r\<in>P" "\<langle>r,q\<rangle> \<in> leq"
      moreover from this and \<open>p\<in>P\<close> \<open><q,p>\<in>leq\<close> \<open>q\<in>P\<close>
      have "<r,p>\<in>leq"
        using leq_transD by simp
      moreover
      assume "forces_mem(P,leq,q,s,t2)" 
      moreover 
      note dbp \<open>q\<in>P\<close>
      ultimately
      obtain q1 where "<q1,r>\<in>leq" "q1\<in>P" "forces_mem(P,leq,q1,s,t1)"
        using strengthening_mem[of q _ s t2] leq_reflI leq_transD[of _ r q] by blast
      then
      show "\<exists>d\<in>{r \<in> P . forces_mem(P, leq, r, s, t1)}. d \<in> P \<and> \<langle>d, r\<rangle> \<in> leq"
        by blast
    qed
    ultimately
    have "forces_mem(P, leq, q, s, t1) \<longleftrightarrow> forces_mem(P, leq, q, s, t2)"
      using density_mem[OF \<open>q\<in>P\<close>] by blast
  }
  with \<open>p\<in>P\<close>
  show "forces_eq(P,leq,p,t1,t2)" using def_forces_eq by blast
qed

end

end