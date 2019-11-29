theory Forcing_Thms
  imports
    Forces_Definition

begin

context forcing_data
begin

definition
  Forces :: "i \<Rightarrow> i \<Rightarrow> i\<Rightarrow> o" ("_ \<tturnstile> _ _" 60) where
  "Forces(p,\<phi>,env) \<equiv> sats(M,forces(\<phi>), [P,leq,one,p] @ env)"

lemma leq_transD:  "\<langle>a,b\<rangle> \<in> leq \<Longrightarrow> \<langle>b,c\<rangle> \<in> leq \<Longrightarrow> a \<in> P\<Longrightarrow> b \<in> P\<Longrightarrow> c \<in> P\<Longrightarrow> \<langle>a,c\<rangle> \<in> leq"
  using leq_preord trans_onD unfolding preorder_on_def by blast

lemma leq_reflI: "p\<in>P \<Longrightarrow> <p,p>\<in>leq"
 using leq_preord unfolding preorder_on_def refl_def by blast

lemma dense_iff [iff] : "dense(D) \<longleftrightarrow> (\<forall>p\<in>P. \<exists>d\<in>D. \<langle>d, p\<rangle> \<in> leq)"
  unfolding dense_def ..

declare dense_iff[simp del]

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

lemma forces_mem_iff_dense_below:  "p\<in>P \<Longrightarrow> forces_mem(p,t1,t2) \<longleftrightarrow> dense_below(
    {q\<in>P. \<exists>s. \<exists>r. r\<in>P \<and> <s,r> \<in> t2 \<and> <q,r>\<in>leq \<and> forces_eq(q,t1,s)}
    ,p)"
  using def_forces_mem[of p t1 t2] by blast

(* Kunen 2013, Lemma IV.2.37(a) *)
lemma strengthening_eq: 
  assumes "p\<in>P" "r\<in>P" "<r,p>\<in>leq" "forces_eq(p,t1,t2)"
  shows "forces_eq(r,t1,t2)"
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
    have "forces_mem(q, s, t1) \<longleftrightarrow> forces_mem(q, s, t2)"
      using def_forces_eq[of p t1 t2] by simp
  }
  with \<open>r\<in>P\<close>
  show ?thesis using def_forces_eq[of r t1 t2] by blast
qed
*)

(* Kunen 2013, Lemma IV.2.37(a) *)
lemma strengthening_mem: 
  assumes "p\<in>P" "r\<in>P" "<r,p>\<in>leq" "forces_mem(p,t1,t2)"
  shows "forces_mem(r,t1,t2)"
  using assms forces_mem_iff_dense_below dense_below_under by auto

(* Kunen 2013, Lemma IV.2.37(b) *)
lemma density_mem: 
  assumes "p\<in>P"
  shows "forces_mem(p,t1,t2)  \<longleftrightarrow> dense_below({q\<in>P. forces_mem(q,t1,t2)},p)"
proof
  assume "forces_mem(p,t1,t2)"
  with assms
  show "dense_below({q\<in>P. forces_mem(q,t1,t2)},p)"
    using forces_mem_iff_dense_below strengthening_mem[of p] ideal_dense_below by auto
next
  assume "dense_below({q \<in> P . forces_mem(q, t1, t2)}, p)"
  with assms
  have "dense_below({q\<in>P. 
    dense_below({q'\<in>P. \<exists>s r. r \<in> P \<and> \<langle>s,r\<rangle>\<in>t2 \<and> \<langle>q',r\<rangle>\<in>leq \<and> forces_eq(q',t1,s)},q)
    },p)"
    using forces_mem_iff_dense_below by simp
  with assms
  show "forces_mem(p,t1,t2)"
    using dense_below_dense_below forces_mem_iff_dense_below[of p t1 t2] by blast
qed

lemma aux_density_eq:
  assumes 
    "dense_below(
    {q'\<in>P. \<forall>q. q\<in>P \<and> \<langle>q,q'\<rangle>\<in>leq \<longrightarrow> forces_mem(q,s,t1) \<longleftrightarrow> forces_mem(q,s,t2)}
    ,p)"
    "forces_mem(q,s,t1)" "q\<in>P" "p\<in>P" "<q,p>\<in>leq"
  shows
    "dense_below({r\<in>P. forces_mem(r,s,t2)},q)"
proof
  fix r
  assume "r\<in>P" "\<langle>r,q\<rangle> \<in> leq"
  moreover from this and \<open>p\<in>P\<close> \<open><q,p>\<in>leq\<close> \<open>q\<in>P\<close>
  have "<r,p>\<in>leq"
    using leq_transD by simp
  moreover
  note \<open>forces_mem(q,s,t1)\<close> \<open>dense_below(_,p)\<close> \<open>q\<in>P\<close>
  ultimately
  obtain q1 where "<q1,r>\<in>leq" "q1\<in>P" "forces_mem(q1,s,t2)"
    using strengthening_mem[of q _ s t1] leq_reflI leq_transD[of _ r q] by blast
  then
  show "\<exists>d\<in>{r \<in> P . forces_mem(r, s, t2)}. d \<in> P \<and> \<langle>d, r\<rangle> \<in> leq"
    by blast
qed

(* Kunen 2013, Lemma IV.2.37(b) *)
lemma density_eq:
  assumes "p\<in>P"
  shows "forces_eq(p,t1,t2)  \<longleftrightarrow> dense_below({q\<in>P. forces_eq(q,t1,t2)},p)"
proof
  assume "forces_eq(p,t1,t2)"
  with \<open>p\<in>P\<close>
  show "dense_below({q\<in>P. forces_eq(q,t1,t2)},p)"
    using strengthening_eq ideal_dense_below by auto
next
  assume "dense_below({q\<in>P. forces_eq(q,t1,t2)},p)"
  {
    fix s q 
    let ?D1="{q'\<in>P. \<forall>s\<in>domain(t1) \<union> domain(t2). \<forall>q. q \<in> P \<and> \<langle>q,q'\<rangle>\<in>leq \<longrightarrow>
           forces_mem(q,s,t1)\<longleftrightarrow>forces_mem(q,s,t2)}"
    let ?D2="{q'\<in>P. \<forall>q. q\<in>P \<and> \<langle>q,q'\<rangle>\<in>leq \<longrightarrow> forces_mem(q,s,t1) \<longleftrightarrow> forces_mem(q,s,t2)}"
    assume "s\<in>domain(t1) \<union> domain(t2)" 
    then
    have "?D1\<subseteq>?D2" by blast
    with \<open>dense_below(_,p)\<close>
    have "dense_below({q'\<in>P. \<forall>s\<in>domain(t1) \<union> domain(t2). \<forall>q. q \<in> P \<and> \<langle>q,q'\<rangle>\<in>leq \<longrightarrow>
           forces_mem(q,s,t1)\<longleftrightarrow>forces_mem(q,s,t2)},p)"
      using dense_below_cong'[OF \<open>p\<in>P\<close> def_forces_eq[of _ t1 t2]] by simp
    with \<open>p\<in>P\<close> \<open>?D1\<subseteq>?D2\<close>
    have "dense_below({q'\<in>P. \<forall>q. q\<in>P \<and> \<langle>q,q'\<rangle>\<in>leq \<longrightarrow> 
            forces_mem(q,s,t1) \<longleftrightarrow> forces_mem(q,s,t2)},p)"
      using dense_below_mono by simp
    moreover from this (* Automatic tools can't handle this symmetry 
                          in order to apply aux_density_eq below *)
    have  "dense_below({q'\<in>P. \<forall>q. q\<in>P \<and> \<langle>q,q'\<rangle>\<in>leq \<longrightarrow> 
            forces_mem(q,s,t2) \<longleftrightarrow> forces_mem(q,s,t1)},p)"
      by blast
    moreover
    assume "q \<in> P" "<q,p>\<in>leq"
    moreover
    note \<open>p\<in>P\<close>
    ultimately (*We can omit the next step but it is slower *)
    have "forces_mem(q,s,t1) \<Longrightarrow> dense_below({r\<in>P. forces_mem(r,s,t2)},q)"
         "forces_mem(q,s,t2) \<Longrightarrow> dense_below({r\<in>P. forces_mem(r,s,t1)},q)" 
      using aux_density_eq by simp_all
    then
    have "forces_mem(q, s, t1) \<longleftrightarrow> forces_mem(q, s, t2)"
      using density_mem[OF \<open>q\<in>P\<close>] by blast
  }
  with \<open>p\<in>P\<close>
  show "forces_eq(p,t1,t2)" using def_forces_eq by blast
qed

definition
  forces_neq :: "[i,i,i] \<Rightarrow> o" where
  "forces_neq(p,t1,t2) \<equiv> \<not> (\<exists>q\<in>P. <q,p>\<in>leq \<and> forces_eq(q,t1,t2))"

definition
  forces_nmem :: "[i,i,i] \<Rightarrow> o" where
  "forces_nmem(p,t1,t2) \<equiv> \<not> (\<exists>q\<in>P. <q,p>\<in>leq \<and> forces_mem(q,t1,t2))"

(* Kunen 2013, Lemma IV.2.38 *)
lemma not_forces_neq:
  assumes "p\<in>P"
  shows "forces_eq(p,t1,t2) \<longleftrightarrow> \<not> (\<exists>q\<in>P. <q,p>\<in>leq \<and> forces_neq(q,t1,t2))"
  using assms density_eq unfolding forces_neq_def by blast

(* Kunen 2013, Lemma IV.2.38 *)
lemma not_forces_nmem:
  assumes "p\<in>P"
  shows "forces_mem(p,t1,t2) \<longleftrightarrow> \<not> (\<exists>q\<in>P. <q,p>\<in>leq \<and> forces_nmem(q,t1,t2))"
  using assms density_mem unfolding forces_nmem_def by blast

(* Use the newer versions in Forces_Definition! *)
(* (and adequate the rest of the code to them)  *)
lemma sats_forces_Equal':
  assumes
    "p\<in>P" "t1\<in>M" "t2\<in>M" "env\<in>list(M)" "nth(n,env) = t1" "nth(m,env) = t2" "n\<in>nat" "m\<in>nat"
  shows
    "sats(M,forces(Equal(n,m)),[P,leq,one,p] @ env) \<longleftrightarrow> forces_eq(p,t1,t2)"
  using assms sats_forces_Equal forces_eq_abs Transset_intf[OF trans_M] P_in_M 
  by simp

lemma sats_forces_Member':
  assumes
    "p\<in>P" "t1\<in>M" "t2\<in>M" "env\<in>list(M)" "nth(n,env) = t1" "nth(m,env) = t2" "n\<in>nat" "m\<in>nat"
  shows
    "sats(M,forces(Member(n,m)),[P,leq,one,p] @ env) \<longleftrightarrow> forces_mem(p,t1,t2)"
  using assms sats_forces_Member forces_mem_abs Transset_intf[OF trans_M] P_in_M 
  by simp

lemma sats_forces_Nand':
  assumes
    "p\<in>P" "\<phi>\<in>formula" "\<psi>\<in>formula" "env \<in> list(M)" 
  shows
    "sats(M,forces(Nand(\<phi>,\<psi>)),[P,leq,one,p] @ env) \<longleftrightarrow> 
     \<not>(\<exists>q\<in>M. q\<in>P \<and> (\<exists>qp\<in>M. pair(##M,q,p,qp) \<and> qp\<in>leq) \<and> 
          (sats(M,forces(\<phi>),[P,leq,one,q]@env)\<and> sats(M,forces(\<psi>),[P,leq,one,q]@env)))"
  using assms sats_forces_Nand[OF assms(2-4) Transset_intf[OF trans_M \<open>p\<in>P\<close>]]
  P_in_M leq_in_M one_in_M unfolding forces_def
  by simp

lemma sats_forces_Neg':
  assumes
    "p\<in>P" "env \<in> list(M)" "\<phi>\<in>formula"
  shows
    "sats(M,forces(Neg(\<phi>)),[P,leq,one,p] @ env) \<longleftrightarrow> 
     \<not>(\<exists>q\<in>M. q\<in>P \<and> (\<exists>qp\<in>M. pair(##M,q,p,qp) \<and> qp\<in>leq) \<and> 
               (sats(M,forces(\<phi>),[P,leq,one,q]@env)))"
  using assms sats_forces_Neg Transset_intf[OF trans_M] 
  P_in_M leq_in_M one_in_M  unfolding forces_def
  by (simp, blast)

lemma sats_forces_Forall':
  assumes
    "p\<in>P" "env \<in> list(M)" "\<phi>\<in>formula"
  shows
    "sats(M,forces(Forall(\<phi>)),[P,leq,one,p] @ env) \<longleftrightarrow> 
     (\<forall>x\<in>M. sats(M, forces(\<phi>),[P,leq,one,p,x] @ env))"
  using assms sats_forces_Forall Transset_intf[OF trans_M] 
  P_in_M leq_in_M one_in_M sats_ren_forces_forall unfolding forces_def
  by simp

lemma Forces_Equal:
  assumes
    "p\<in>P" "t1\<in>M" "t2\<in>M" "env\<in>list(M)" "nth(n,env) = t1" "nth(m,env) = t2" "n\<in>nat" "m\<in>nat" 
  shows
    "p \<tturnstile> Equal(n,m) env \<longleftrightarrow> forces_eq(p,t1,t2)"
  unfolding Forces_def using sats_forces_Equal' assms .

lemma Forces_Member:
  assumes
    "p\<in>P" "t1\<in>M" "t2\<in>M" "env\<in>list(M)" "nth(n,env) = t1" "nth(m,env) = t2" "n\<in>nat" "m\<in>nat" 
  shows
    "p \<tturnstile> Member(n,m) env \<longleftrightarrow> forces_mem(p,t1,t2)"
  unfolding Forces_def using sats_forces_Member' assms .

lemma Forces_Neg:
  assumes
    "p\<in>P" "env \<in> list(M)" "\<phi>\<in>formula" 
  shows
    "p \<tturnstile> Neg(\<phi>) env \<longleftrightarrow> \<not>(\<exists>q\<in>M. q\<in>P \<and> <q,p>\<in>leq \<and> q \<tturnstile> \<phi> env)"
  unfolding Forces_def using assms sats_forces_Neg' Transset_intf[OF trans_M] 
  P_in_M pair_in_M_iff by simp

lemma Forces_Nand:
  assumes
    "p\<in>P" "env \<in> list(M)" "\<phi>\<in>formula" "\<psi>\<in>formula"
  shows
    "p \<tturnstile> Nand(\<phi>,\<psi>) env \<longleftrightarrow> \<not>(\<exists>q\<in>M. q\<in>P \<and> <q,p>\<in>leq \<and> (q \<tturnstile> \<phi> env) \<and> (q \<tturnstile> \<psi> env))"
  unfolding Forces_def using assms sats_forces_Nand' Transset_intf[OF trans_M] 
  P_in_M pair_in_M_iff by simp

lemma Forces_And_aux:
  assumes
    "p\<in>P" "env \<in> list(M)" "\<phi>\<in>formula" "\<psi>\<in>formula"
  shows
    "p \<tturnstile> And(\<phi>,\<psi>) env \<longleftrightarrow> 
    (\<forall>q\<in>M. q\<in>P \<and> <q,p>\<in>leq \<longrightarrow> (\<exists>r\<in>M. r\<in>P \<and> <r,q>\<in>leq \<and> (r \<tturnstile> \<phi> env) \<and> (r \<tturnstile> \<psi> env)))"
  unfolding And_def using assms Forces_Neg Forces_Nand by (auto simp only:)

lemma Forces_And_iff_dense_below:
  assumes
    "p\<in>P" "env \<in> list(M)" "\<phi>\<in>formula" "\<psi>\<in>formula"
  shows
    "p \<tturnstile> And(\<phi>,\<psi>) env \<longleftrightarrow> dense_below({r\<in>P. (r \<tturnstile> \<phi> env) \<and> (r \<tturnstile> \<psi> env) },p)"
  unfolding dense_below_def using Forces_And_aux assms
    by (auto dest:Transset_intf[OF trans_M _ P_in_M]; rename_tac q; drule_tac x=q in bspec)+

lemma Forces_Forall:
  assumes
    "p\<in>P" "env \<in> list(M)" "\<phi>\<in>formula"
  shows
    "p \<tturnstile> Forall(\<phi>) env \<longleftrightarrow> (\<forall>x\<in>M. p \<tturnstile> \<phi> ([x] @ env))"
  unfolding Forces_def using sats_forces_Forall' assms by simp

(* Move the following to an appropriate place *)
(* "x\<in>val(G,\<pi>) \<Longrightarrow> \<exists>\<theta>. \<exists>p\<in>G.  <\<theta>,p>\<in>\<pi> \<and> val(G,\<theta>) = x" *)
bundle some_rules =  elem_of_val_pair [dest] SepReplace_iff [simp del] SepReplace_iff[iff]

context 
  includes some_rules
begin

lemma elem_of_valI: "\<exists>\<theta>. \<exists>p\<in>P. p\<in>G \<and> <\<theta>,p>\<in>\<pi> \<and> val(G,\<theta>) = x \<Longrightarrow> x\<in>val(G,\<pi>)"
  by (subst def_val, auto)

lemma M_genericD [dest]: "M_generic(G) \<Longrightarrow> x\<in>G \<Longrightarrow> x\<in>P"
  unfolding M_generic_def by (blast dest:filterD)

lemma M_generic_leqD [dest]: "M_generic(G) \<Longrightarrow> p\<in>G \<Longrightarrow> q\<in>P \<Longrightarrow> <p,q>\<in>leq \<Longrightarrow> q\<in>G"
  unfolding M_generic_def by (blast dest:filter_leqD)

lemma M_generic_compatD [dest]: "M_generic(G) \<Longrightarrow> p\<in>G \<Longrightarrow> r\<in>G \<Longrightarrow> \<exists>q\<in>G. <q,p>\<in>leq \<and> <q,r>\<in>leq"
  unfolding M_generic_def by (blast dest:low_bound_filter)

lemma M_generic_denseD [dest]: "M_generic(G) \<Longrightarrow> dense(D) \<Longrightarrow> D\<subseteq>P \<Longrightarrow> D\<in>M \<Longrightarrow> \<exists>q\<in>G. q\<in>D"
  unfolding M_generic_def by blast

lemma GenExtD: "x\<in>M[G] \<longleftrightarrow> (\<exists>\<tau>\<in>M. x = val(G,\<tau>))"
  unfolding GenExt_def by simp

lemma left_in_M : "tau\<in>M \<Longrightarrow> <a,b>\<in>tau \<Longrightarrow> a\<in>M"
  using fst_snd_closed[of "<a,b>"] Transset_intf[OF trans_M] by auto

(* Kunen 2013, Lemma IV.2.29 *)
lemma generic_inter_dense_below: "D\<in>M \<Longrightarrow> M_generic(G) \<Longrightarrow> dense_below(D,p) \<Longrightarrow> p\<in>G \<Longrightarrow> D \<inter> G \<noteq> 0"
  sorry

(* Lemma IV.2.40(a), membership *)
lemma IV240a_mem:
  assumes
    "M_generic(G)" "p\<in>G" "\<pi>\<in>M" "\<tau>\<in>M" "forces_mem(p,\<pi>,\<tau>)"
    "\<And>q \<sigma>. q\<in>P \<Longrightarrow> q\<in>G \<Longrightarrow> \<sigma>\<in>domain(\<tau>) \<Longrightarrow> forces_eq(q,\<pi>,\<sigma>) \<Longrightarrow> 
      val(G,\<pi>) = val(G,\<sigma>)" (* inductive hypothesis *)
  shows
    "val(G,\<pi>)\<in>val(G,\<tau>)"
proof (intro elem_of_valI)
  let ?D="{q\<in>P. \<exists>\<sigma>. \<exists>r. r\<in>P \<and> <\<sigma>,r> \<in> \<tau> \<and> <q,r>\<in>leq \<and> forces_eq(q,\<pi>,\<sigma>)}"
  from assms
  have "?D = {q\<in>P. \<exists>\<sigma>. \<exists>r. r\<in>P \<and> <\<sigma>,r> \<in> \<tau> \<and> <q,r>\<in>leq \<and> sats(M,forces(Equal(0,1)),[P,leq,one,q,\<pi>,\<sigma>])}"
    using sats_forces_Equal'[of _ \<pi> _ "[\<pi>, _]" 0 1]  left_in_M  by simp
  moreover from \<open>M_generic(G)\<close> \<open>p\<in>G\<close>
  have "p\<in>P" by blast
  moreover
  note \<open>\<pi>\<in>M\<close> \<open>\<tau>\<in>M\<close>
  ultimately
  have "?D \<in> M" 
    using leq_in_M one_in_M P_in_M Transset_intf[OF trans_M _ P_in_M] (* or else P_sub_M *) sorry
  moreover from assms \<open>p\<in>P\<close>
  have "dense_below(?D,p)"
    using forces_mem_iff_dense_below by simp
  moreover
  note \<open>M_generic(G)\<close> \<open>p\<in>G\<close>
  ultimately
  obtain q where "q\<in>G" "q\<in>?D" using generic_inter_dense_below by blast
  then
  obtain \<sigma> r where "r\<in>P" "<\<sigma>,r> \<in> \<tau>" "<q,r>\<in>leq" "forces_eq(q,\<pi>,\<sigma>)" by blast
  moreover from this and \<open>q\<in>G\<close> assms
  have "r \<in> G" "val(G,\<pi>) = val(G,\<sigma>)" by blast+
  ultimately
  show "\<exists> \<sigma>. \<exists>p\<in>P. p \<in> G \<and> \<langle>\<sigma>, p\<rangle> \<in> \<tau> \<and> val(G, \<sigma>) = val(G, \<pi>)" by auto
qed

(* Example IV.2.36 (next two lemmas) *)
lemma refl_forces_eq:"p\<in>P \<Longrightarrow> forces_eq(p,x,x)"
  using def_forces_eq by simp

lemma forces_memI: "<\<sigma>,r>\<in>\<tau> \<Longrightarrow> p\<in>P \<Longrightarrow> r\<in>P \<Longrightarrow> <p,r>\<in>leq \<Longrightarrow> forces_mem(p,\<sigma>,\<tau>)"
  using refl_forces_eq[of _ \<sigma>] leq_transD leq_reflI 
  by (blast intro:forces_mem_iff_dense_below[THEN iffD2])

(* 
lemma symmetry_argument: 
  assumes 
    "\<And>x y. R(x,y) \<Longrightarrow> R(y,x)"
    "\<And>x y. R(x,y) \<Longrightarrow> Q(x,y) \<longleftrightarrow> Q(y,x)"
    "\<And>x y. R(x,y) \<Longrightarrow> Q(x,y) \<Longrightarrow> S(x,y)"
    "R(x,y)" "Q(x,y)"
  shows 
    "S(x,y) \<and> S(y,x)"
  using assms by simp
*)

(* Lemma IV.2.40(a), equality, first inclusion *)
lemma IV240a_eq_1st_incl:
  assumes
    "M_generic(G)" "p\<in>G" "forces_eq(p,\<tau>,\<theta>)"
    and
    IH:"\<And>q \<sigma>. q\<in>P \<Longrightarrow> q\<in>G \<Longrightarrow> \<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>) \<Longrightarrow> 
        (forces_mem(q,\<sigma>,\<tau>) \<longrightarrow> val(G,\<sigma>) \<in> val(G,\<tau>)) \<and>
        (forces_mem(q,\<sigma>,\<theta>) \<longrightarrow> val(G,\<sigma>) \<in> val(G,\<theta>))"
(* Strong enough for this case: *)
(*  IH:"\<And>q \<sigma>. q\<in>P \<Longrightarrow> \<sigma>\<in>domain(\<tau>) \<Longrightarrow> forces_mem(q,\<sigma>,\<theta>) \<Longrightarrow> 
      val(G,\<sigma>) \<in> val(G,\<theta>)" *)
  shows
    "val(G,\<tau>) \<subseteq> val(G,\<theta>)"
proof
  fix x
  assume "x\<in>val(G,\<tau>)"
  then
  obtain \<sigma> r where "<\<sigma>,r>\<in>\<tau>" "r\<in>G" "val(G,\<sigma>)=x" by blast
  moreover from this and \<open>p\<in>G\<close> \<open>M_generic(G)\<close>
  obtain q where "q\<in>G" "<q,p>\<in>leq" "<q,r>\<in>leq" by force
  moreover from this and \<open>p\<in>G\<close> \<open>M_generic(G)\<close>
  have "q\<in>P" "p\<in>P" by blast+
  moreover from calculation
  have "forces_mem(q,\<sigma>,\<tau>)"
    using forces_memI M_genericD[OF \<open>M_generic(G)\<close>] by blast
  moreover
  note \<open>forces_eq(p,\<tau>,\<theta>)\<close>
  ultimately
  have "forces_mem(q,\<sigma>,\<theta>)"
    using def_forces_eq by blast
  with \<open>q\<in>P\<close> \<open>q\<in>G\<close> IH[of q \<sigma>] \<open><\<sigma>,r>\<in>\<tau>\<close> \<open>val(G,\<sigma>) = x\<close>
  show "x\<in>val(G,\<theta>)" by (blast)
qed

(* Lemma IV.2.40(a), equality, second inclusion--- COPY-PASTE *)
lemma IV240a_eq_2nd_incl:
  assumes
    "M_generic(G)" "p\<in>G" "forces_eq(p,\<tau>,\<theta>)"
    and
    IH:"\<And>q \<sigma>. q\<in>P \<Longrightarrow> q\<in>G \<Longrightarrow> \<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>) \<Longrightarrow> 
        (forces_mem(q,\<sigma>,\<tau>) \<longrightarrow> val(G,\<sigma>) \<in> val(G,\<tau>)) \<and>
        (forces_mem(q,\<sigma>,\<theta>) \<longrightarrow> val(G,\<sigma>) \<in> val(G,\<theta>))"
  shows
    "val(G,\<theta>) \<subseteq> val(G,\<tau>)"
proof
  fix x
  assume "x\<in>val(G,\<theta>)"
  then
  obtain \<sigma> r where "<\<sigma>,r>\<in>\<theta>" "r\<in>G" "val(G,\<sigma>)=x" by blast
  moreover from this and \<open>p\<in>G\<close> \<open>M_generic(G)\<close>
  obtain q where "q\<in>G" "<q,p>\<in>leq" "<q,r>\<in>leq" by force
  moreover from this and \<open>p\<in>G\<close> \<open>M_generic(G)\<close>
  have "q\<in>P" "p\<in>P" by blast+
  moreover from calculation
  have "forces_mem(q,\<sigma>,\<theta>)"
    using forces_memI M_genericD[OF \<open>M_generic(G)\<close>] by blast
  moreover
  note \<open>forces_eq(p,\<tau>,\<theta>)\<close>
  ultimately
  have "forces_mem(q,\<sigma>,\<tau>)"
    using def_forces_eq by blast
  with \<open>q\<in>P\<close> \<open>q\<in>G\<close> IH[of q \<sigma>] \<open><\<sigma>,r>\<in>\<theta>\<close> \<open>val(G,\<sigma>) = x\<close>
  show "x\<in>val(G,\<tau>)" by (blast)
qed

(* Lemma IV.2.40(a), equality, second inclusion--- COPY-PASTE *)
lemma IV240a_eq:
  assumes
    "M_generic(G)" "p\<in>G" "forces_eq(p,\<tau>,\<theta>)"
    and
    IH:"\<And>q \<sigma>. q\<in>P \<Longrightarrow> q\<in>G \<Longrightarrow> \<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>) \<Longrightarrow> 
        (forces_mem(q,\<sigma>,\<tau>) \<longrightarrow> val(G,\<sigma>) \<in> val(G,\<tau>)) \<and>
        (forces_mem(q,\<sigma>,\<theta>) \<longrightarrow> val(G,\<sigma>) \<in> val(G,\<theta>))"
  shows
    "val(G,\<tau>) = val(G,\<theta>)"
  using IV240a_eq_1st_incl[OF assms] IV240a_eq_2nd_incl[OF assms] IH by blast 

(*
    "forces_mem(p,\<pi>,\<tau>)"
    "\<And>q \<sigma>. q\<in>P \<Longrightarrow> \<sigma>\<in>domain(\<tau>) \<Longrightarrow> forces_eq(q,\<pi>,\<sigma>) \<Longrightarrow> val(G,\<pi>) = val(G,\<sigma>)" 
    -------------------------------
    "val(G,\<pi>) \<in> val(G,\<tau>)"

    "forces_eq(p,\<tau>,\<theta>)"
 IH:"\<And>q \<sigma>. q\<in>P \<Longrightarrow> \<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>) \<Longrightarrow> 
        (forces_mem(q,\<sigma>,\<tau>) \<longrightarrow> val(G,\<sigma>) \<in> val(G,\<tau>)) \<and>
        (forces_mem(q,\<sigma>,\<theta>) \<longrightarrow> val(G,\<sigma>) \<in> val(G,\<theta>))"
    -------------------------------
    "val(G,\<tau>) = val(G,\<theta>)"

Unfolding forces_eq and forces_mem defs,

    "frc_at(P,leq,<1,\<tau>,\<theta>,p>) = 1"
    "\<And>q \<sigma>. q\<in>P \<Longrightarrow> \<sigma>\<in>domain(\<theta>) \<Longrightarrow> frc_at(P,leq,<0,\<tau>,\<sigma>,q>) = 1 \<Longrightarrow> val(G,\<tau>) = val(G,\<sigma>)"
    -------------------------------
    "val(G,\<tau>) \<in> val(G,\<theta>)"
    
    "frc_at(P,leq,<0,\<tau>,\<theta>,p>) = 1"
 IH:"\<And>q \<sigma>. q\<in>P \<Longrightarrow> \<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>) \<Longrightarrow> 
        (frc_at(P,leq,<1,\<sigma>,\<tau>,q>) = 1 \<longrightarrow> val(G,\<sigma>) \<in> val(G,\<tau>)) \<and>
        (frc_at(P,leq,<1,\<sigma>,\<theta>,q>) = 1 \<longrightarrow> val(G,\<sigma>) \<in> val(G,\<theta>))"
    -------------------------------
    "val(G,\<tau>) = val(G,\<theta>)"


Discharging the main assumption,

    "\<And>q \<sigma>. q\<in>P \<Longrightarrow> \<sigma>\<in>domain(\<theta>) \<Longrightarrow> frc_at(P,leq,<0,\<tau>,\<sigma>,q>) = 1 \<longrightarrow> val(G,\<tau>) = val(G,\<sigma>)"
    -------------------------------
    "frc_at(P,leq,<1,\<tau>,\<theta>,p>) = 1 \<longrightarrow>  val(G,\<tau>) \<in> val(G,\<theta>)"
    
 IH:"\<And>q \<sigma>. q\<in>P \<Longrightarrow> \<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>) \<Longrightarrow> 
        (frc_at(P,leq,<1,\<sigma>,\<tau>,q>) = 1 \<longrightarrow> val(G,\<sigma>) \<in> val(G,\<tau>)) \<and>
        (frc_at(P,leq,<1,\<sigma>,\<theta>,q>) = 1 \<longrightarrow> val(G,\<sigma>) \<in> val(G,\<theta>))"
    -------------------------------
    "frc_at(P,leq,<0,\<tau>,\<theta>,p>) = 1 \<longrightarrow> val(G,\<tau>) = val(G,\<theta>)"

And abstacting,

    "\<And>q \<sigma>. q\<in>P \<Longrightarrow> \<sigma>\<in>domain(\<theta>) \<Longrightarrow> Q(0,\<tau>,\<sigma>,q)"
    -------------------------------
    "Q(1,\<tau>,\<theta>,p)"
    
 IH:"\<And>q \<sigma>. q\<in>P \<Longrightarrow> \<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>) \<Longrightarrow> Q(1,\<sigma>,\<tau>,q) \<and> Q(1,\<sigma>,\<theta>,q)"
    -------------------------------
    "Q(0,\<tau>,\<theta>,p)"

Putting altogether,
*)


lemma core_induction:
  assumes
    "\<And>\<tau> \<theta> p. p \<in> P \<Longrightarrow> \<lbrakk>\<And>q \<sigma>. \<lbrakk>q\<in>P ; \<sigma>\<in>domain(\<theta>)\<rbrakk> \<Longrightarrow> Q(0,\<tau>,\<sigma>,q)\<rbrakk> \<Longrightarrow> Q(1,\<tau>,\<theta>,p)"
    "\<And>\<tau> \<theta> p. p \<in> P \<Longrightarrow> \<lbrakk>\<And>q \<sigma>. \<lbrakk>q\<in>P ; \<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>)\<rbrakk> \<Longrightarrow> Q(1,\<sigma>,\<tau>,q) \<and> Q(1,\<sigma>,\<theta>,q)\<rbrakk> \<Longrightarrow> Q(0,\<tau>,\<theta>,p)"
    "ft \<in> 2" "p \<in> P"
  shows
    "Q(ft,\<tau>,\<theta>,p)"
proof -
  {
    fix ft p \<tau> \<theta>
    have "Transset(eclose({\<tau>,\<theta>}))" (is "Transset(?e)") 
      using Transset_eclose by simp
    have "\<tau> \<in> ?e" "\<theta> \<in> ?e" 
      using arg_into_eclose by simp_all
    moreover
    assume "ft \<in> 2" "p \<in> P"
    ultimately
    have "<ft,\<tau>,\<theta>,p>\<in> 2\<times>?e\<times>?e\<times>P" (is "?a\<in>2\<times>?e\<times>?e\<times>P") by simp
    then 
    have "Q(ftype(?a), name1(?a), name2(?a), cond_of(?a))"
      using core_induction_aux[of ?e P Q ?a,OF \<open>Transset(?e)\<close> assms(1,2) \<open>?a\<in>_\<close>] 
      by (clarify) (blast)
    then have "Q(ft,\<tau>,\<theta>,p)" by (simp add:components_simp)
  }
  then show ?thesis using assms by simp
qed

lemma forces_induction_with_conds:
  assumes
    "\<And>\<tau> \<theta> p. p \<in> P \<Longrightarrow> \<lbrakk>\<And>q \<sigma>. \<lbrakk>q\<in>P ; \<sigma>\<in>domain(\<theta>)\<rbrakk> \<Longrightarrow> Q(q,\<tau>,\<sigma>)\<rbrakk> \<Longrightarrow> R(p,\<tau>,\<theta>)"
    "\<And>\<tau> \<theta> p. p \<in> P \<Longrightarrow> \<lbrakk>\<And>q \<sigma>. \<lbrakk>q\<in>P ; \<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>)\<rbrakk> \<Longrightarrow> R(q,\<sigma>,\<tau>) \<and> R(q,\<sigma>,\<theta>)\<rbrakk> \<Longrightarrow> Q(p,\<tau>,\<theta>)"
    "p \<in> P"
  shows
    "Q(p,\<tau>,\<theta>) \<and> R(p,\<tau>,\<theta>)"
proof -
  let ?Q="\<lambda>ft \<tau> \<theta> p. (ft = 0 \<longrightarrow> Q(p,\<tau>,\<theta>)) \<and> (ft = 1 \<longrightarrow> R(p,\<tau>,\<theta>))"
  from assms(1)
  have "\<And>\<tau> \<theta> p. p \<in> P \<Longrightarrow> \<lbrakk>\<And>q \<sigma>. \<lbrakk>q\<in>P ; \<sigma>\<in>domain(\<theta>)\<rbrakk> \<Longrightarrow> ?Q(0,\<tau>,\<sigma>,q)\<rbrakk> \<Longrightarrow> ?Q(1,\<tau>,\<theta>,p)"
    by simp
  moreover from assms(2)
  have "\<And>\<tau> \<theta> p. p \<in> P \<Longrightarrow> \<lbrakk>\<And>q \<sigma>. \<lbrakk>q\<in>P ; \<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>)\<rbrakk> \<Longrightarrow> ?Q(1,\<sigma>,\<tau>,q) \<and> ?Q(1,\<sigma>,\<theta>,q)\<rbrakk> \<Longrightarrow> ?Q(0,\<tau>,\<theta>,p)"
    by simp
  moreover
  note \<open>p\<in>P\<close>
  ultimately
  have "?Q(ft,\<tau>,\<theta>,p)" if "ft\<in>2" for ft
    by (rule core_induction[OF _ _ that, of ?Q])
  then
  show ?thesis by auto
qed

lemma forces_induction:
  assumes
    "\<And>\<tau> \<theta>. \<lbrakk>\<And>\<sigma>. \<sigma>\<in>domain(\<theta>) \<Longrightarrow> Q(\<tau>,\<sigma>)\<rbrakk> \<Longrightarrow> R(\<tau>,\<theta>)"
    "\<And>\<tau> \<theta>. \<lbrakk>\<And>\<sigma>. \<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>) \<Longrightarrow> R(\<sigma>,\<tau>) \<and> R(\<sigma>,\<theta>)\<rbrakk> \<Longrightarrow> Q(\<tau>,\<theta>)"
  shows
    "Q(\<tau>,\<theta>) \<and> R(\<tau>,\<theta>)"
proof (intro forces_induction_with_conds[OF _ _ one_in_P ])
  fix \<tau> \<theta> p 
  assume "q \<in> P \<Longrightarrow> \<sigma> \<in> domain(\<theta>) \<Longrightarrow> Q(\<tau>, \<sigma>)" for q \<sigma>
  with assms(1)
  show "R(\<tau>,\<theta>)"
    using one_in_P by simp
next
  fix \<tau> \<theta> p 
    assume "q \<in> P \<Longrightarrow> \<sigma> \<in> domain(\<tau>) \<union> domain(\<theta>) \<Longrightarrow> R(\<sigma>,\<tau>) \<and> R(\<sigma>,\<theta>)" for q \<sigma>
    with assms(2)
    show "Q(\<tau>,\<theta>)"
      using one_in_P by simp
qed

(* Lemma IV.2.40(a), full *)
lemma IV240a:
  assumes
    "M_generic(G)"
  shows 
    "(\<tau>\<in>M \<longrightarrow> \<theta>\<in>M \<longrightarrow> (\<forall>p\<in>G. forces_eq(p,\<tau>,\<theta>) \<longrightarrow> val(G,\<tau>) = val(G,\<theta>))) \<and> 
     (\<tau>\<in>M \<longrightarrow> \<theta>\<in>M \<longrightarrow> (\<forall>p\<in>G. forces_mem(p,\<tau>,\<theta>) \<longrightarrow> val(G,\<tau>) \<in> val(G,\<theta>)))"
    (is "?Q(\<tau>,\<theta>) \<and> ?R(\<tau>,\<theta>)")
proof (intro forces_induction[of ?Q ?R] impI)
  fix \<tau> \<theta> 
  assume "\<tau>\<in>M" "\<theta>\<in>M"  "\<sigma>\<in>domain(\<theta>) \<Longrightarrow> ?Q(\<tau>,\<sigma>)" for \<sigma>
  moreover from this
  have "\<sigma>\<in>domain(\<theta>) \<Longrightarrow> forces_eq(q, \<tau>, \<sigma>) \<Longrightarrow> val(G, \<tau>) = val(G, \<sigma>)" 
    if "q\<in>P" "q\<in>G" for q \<sigma>
    using that domain_closed[of \<theta>] Transset_intf[OF trans_M] by auto
  moreover 
  note assms
  ultimately
  show "\<forall>p\<in>G. forces_mem(p,\<tau>,\<theta>) \<longrightarrow> val(G,\<tau>) \<in> val(G,\<theta>)"
    using IV240a_mem domain_closed Transset_intf[OF trans_M] by (simp)
next
  fix \<tau> \<theta> 
  assume "\<tau>\<in>M" "\<theta>\<in>M" "\<sigma> \<in> domain(\<tau>) \<union> domain(\<theta>) \<Longrightarrow> ?R(\<sigma>,\<tau>) \<and> ?R(\<sigma>,\<theta>)" for \<sigma>
  moreover from this
  have IH':"\<sigma> \<in> domain(\<tau>) \<union> domain(\<theta>) \<Longrightarrow> q\<in>G \<Longrightarrow>
            (forces_mem(q, \<sigma>, \<tau>) \<longrightarrow> val(G, \<sigma>) \<in> val(G, \<tau>)) \<and> 
            (forces_mem(q, \<sigma>, \<theta>) \<longrightarrow> val(G, \<sigma>) \<in> val(G, \<theta>))" for q \<sigma> 
    by (auto intro:  Transset_intf[OF trans_M _ domain_closed[simplified]])
  ultimately
  show "\<forall>p\<in>G. forces_eq(p,\<tau>,\<theta>) \<longrightarrow> val(G,\<tau>) = val(G,\<theta>)"
    using IV240a_eq[OF assms(1) _ _ IH'] by (simp)
qed

(* Lemma IV.2.40(b), membership *)
lemma IV240b_mem:
  assumes
    "M_generic(G)" "val(G,\<pi>)\<in>val(G,\<tau>)" "\<pi>\<in>M" "\<tau>\<in>M"
    and
    IH:"\<And>\<sigma>. \<sigma>\<in>domain(\<tau>) \<Longrightarrow> val(G,\<pi>) = val(G,\<sigma>) \<Longrightarrow> 
      \<exists>p\<in>G. forces_eq(p,\<pi>,\<sigma>)" (* inductive hypothesis *)
  shows
    "\<exists>p\<in>G. forces_mem(p,\<pi>,\<tau>)"
proof -
  from \<open>val(G,\<pi>)\<in>val(G,\<tau>)\<close>
  obtain \<sigma> r where "r\<in>G" "<\<sigma>,r>\<in>\<tau>" "val(G,\<pi>) = val(G,\<sigma>)" by auto
  moreover from this and IH
  obtain p' where "p'\<in>G" "forces_eq(p',\<pi>,\<sigma>)" by blast
  moreover
  note \<open>M_generic(G)\<close>
  ultimately
  obtain p where "<p,r>\<in>leq" "p\<in>G" "forces_eq(p,\<pi>,\<sigma>)" 
    using M_generic_compatD strengthening_eq[of p'] by blast
  moreover 
  note \<open>M_generic(G)\<close>
  moreover from calculation
  have "forces_eq(q,\<pi>,\<sigma>)" if "q\<in>P" "<q,p>\<in>leq" for q
    using that strengthening_eq by blast
  moreover 
  note \<open><\<sigma>,r>\<in>\<tau>\<close> \<open>r\<in>G\<close>
  ultimately
  have "r\<in>P \<and> \<langle>\<sigma>,r\<rangle> \<in> \<tau> \<and> \<langle>q,r\<rangle> \<in> leq \<and> forces_eq(q,\<pi>,\<sigma>)" if "q\<in>P" "<q,p>\<in>leq" for q
    using that leq_transD[of _ p r] by blast
  then
  have "dense_below({q\<in>P. \<exists>s r. r\<in>P \<and> \<langle>s,r\<rangle> \<in> \<tau> \<and> \<langle>q,r\<rangle>\<in>leq \<and> forces_eq(q,\<pi>,s)},p)"
    using leq_reflI by blast
  moreover
  note \<open>M_generic(G)\<close> \<open>p\<in>G\<close>
  moreover from calculation
  have "forces_mem(p,\<pi>,\<tau>)" 
    using forces_mem_iff_dense_below by blast
  ultimately
  show ?thesis by blast
qed

end (* includes *)

(* Lemma IV.2.40(b), equality *)
lemma IV240b_eq:
  assumes
    "M_generic(G)" "val(G,\<tau>) = val(G,\<theta>)" "\<tau>\<in>M" "\<theta>\<in>M" 
    and
    IH:"\<And>\<sigma>. \<sigma>\<in>domain(\<tau>)\<union>domain(\<theta>) \<Longrightarrow> 
      (val(G,\<sigma>)\<in>val(G,\<tau>) \<longrightarrow> (\<exists>q\<in>G. forces_mem(q,\<sigma>,\<tau>))) \<and> 
      (val(G,\<sigma>)\<in>val(G,\<theta>) \<longrightarrow> (\<exists>q\<in>G. forces_mem(q,\<sigma>,\<theta>)))"
    (* inductive hypothesis *)
  shows
    "\<exists>p\<in>G. forces_eq(p,\<tau>,\<theta>)"
proof -
  let ?D="{p\<in>P. forces_eq(p,\<tau>,\<theta>) 
     \<or> (\<exists>\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>). forces_mem(p,\<sigma>,\<tau>) \<and> forces_nmem(p,\<sigma>,\<theta>))
     \<or> (\<exists>\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>). forces_nmem(p,\<sigma>,\<tau>) \<and> forces_mem(p,\<sigma>,\<theta>))}"
  have "?D = {p\<in>P. sats(M,forces(Equal(0,1)),[P,leq,one,p,\<tau>,\<theta>]) 
    \<or> (\<exists>\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>). sats(M,forces(Member(0,1)),[P,leq,one,p,\<sigma>,\<tau>]) \<and> 
            \<not> (\<exists>q\<in>P. <q,p>\<in>leq \<and> sats(M,forces(Member(0,1)),[P,leq,one,q,\<sigma>,\<theta>])))
    \<or> (\<exists>\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>). \<not> (\<exists>q\<in>P. <q,p>\<in>leq \<and> sats(M,forces(Member(0,1)),[P,leq,one,q,\<sigma>,\<tau>]))
              \<and> sats(M,forces(Member(0,1)),[P,leq,one,p,\<sigma>,\<theta>]))}"
    (* horrible proof ahead *)
  proof -
    from assms
    have "\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>) \<Longrightarrow> \<sigma>\<in>M" for \<sigma>
      using Transset_intf[OF trans_M _ domain_closed[simplified]] by blast
    moreover from \<open>\<tau>\<in>M\<close> \<open>\<theta>\<in>M\<close>
    have "forces_mem(p,\<sigma>,\<tau>)\<longleftrightarrow>sats(M,forces(Member(0,1)),[P,leq,one,p,\<sigma>,\<tau>])"
      "forces_mem(p,\<sigma>,\<theta>)\<longleftrightarrow>sats(M,forces(Member(0,1)),[P,leq,one,p,\<sigma>,\<theta>])"
      if "p\<in>P" and "\<sigma>\<in>M" for p \<sigma> 
      using that sats_forces_Member'[OF \<open>p\<in>P\<close> \<open>\<sigma>\<in>M\<close>, of _ "[\<sigma>,_]" 0 1] by simp_all
    moreover
    note assms
    ultimately
    have "(\<exists>\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>). forces_mem(p,\<sigma>,\<tau>) \<and> forces_nmem(p,\<sigma>,\<theta>))
      \<or> (\<exists>\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>). forces_nmem(p,\<sigma>,\<tau>) \<and> forces_mem(p,\<sigma>,\<theta>))
   \<longleftrightarrow>
        (\<exists>\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>). sats(M,forces(Member(0,1)),[P,leq,one,p,\<sigma>,\<tau>]) 
             \<and> \<not> (\<exists>q\<in>P. <q,p>\<in>leq \<and> sats(M,forces(Member(0,1)),[P,leq,one,q,\<sigma>,\<theta>])))
      \<or> (\<exists>\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>). 
              \<not> (\<exists>q\<in>P. <q,p>\<in>leq \<and>  sats(M,forces(Member(0,1)),[P,leq,one,q,\<sigma>,\<tau>])) 
             \<and> sats(M,forces(Member(0,1)),[P,leq,one,p,\<sigma>,\<theta>])) " if "p\<in>P" for p
      unfolding forces_nmem_def using that sorry
    with assms
    show ?thesis
      using sats_forces_Equal'[of _ \<tau> \<theta> "[\<tau>,\<theta>]" 0 1] by auto
  qed
  with assms
  have "?D\<in>M" sorry
  moreover
  have "dense(?D)" 
    using def_forces_eq not_forces_nmem sorry
  moreover
  have "?D \<subseteq> P"
    by auto
  moreover
  note \<open>M_generic(G)\<close>
  ultimately
  obtain p where "p\<in>G" "p\<in>?D"
    unfolding M_generic_def by blast
  then 
  consider 
    (1) "forces_eq(p,\<tau>,\<theta>)" | 
    (2) "\<exists>\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>). forces_mem(p,\<sigma>,\<tau>) \<and> forces_nmem(p,\<sigma>,\<theta>)" | 
    (3) "\<exists>\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>). forces_nmem(p,\<sigma>,\<tau>) \<and> forces_mem(p,\<sigma>,\<theta>)"
    by blast
  then
  show ?thesis
  proof (cases)
    case 1
    with \<open>p\<in>G\<close> 
    show ?thesis by blast
  next
    case 2
    then 
    obtain \<sigma> where "\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>)" "forces_mem(p,\<sigma>,\<tau>)" "forces_nmem(p,\<sigma>,\<theta>)" 
      by blast
    moreover from this and \<open>p\<in>G\<close> and assms
    have "val(G,\<sigma>)\<in>val(G,\<tau>)"
      using IV240a[of G \<sigma> \<tau>] Transset_intf[OF trans_M _ domain_closed[simplified]] by blast
    moreover note IH \<open>val(G,\<tau>) = _\<close>
    ultimately
    obtain q where "q\<in>G" "forces_mem(q, \<sigma>, \<theta>)" by auto
    moreover from this and \<open>p\<in>G\<close> \<open>M_generic(G)\<close>
    obtain r where "r\<in>P" "<r,p>\<in>leq" "<r,q>\<in>leq"
      by blast
    moreover
    note \<open>M_generic(G)\<close>
    ultimately
    have "forces_mem(r, \<sigma>, \<theta>)"
      using strengthening_mem by blast
    with \<open><r,p>\<in>leq\<close> \<open>forces_nmem(p,\<sigma>,\<theta>)\<close> \<open>r\<in>P\<close>
    have "False"
      unfolding forces_nmem_def by blast
    then
    show ?thesis by simp
  next (* copy-paste from case 2 mutatis mutandis*)
    case 3
    then
    obtain \<sigma> where "\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>)" "forces_mem(p,\<sigma>,\<theta>)" "forces_nmem(p,\<sigma>,\<tau>)" 
      by blast
    moreover from this and \<open>p\<in>G\<close> and assms
    have "val(G,\<sigma>)\<in>val(G,\<theta>)"
      using IV240a[of G \<sigma> \<theta>] Transset_intf[OF trans_M _ domain_closed[simplified]] by blast
    moreover note IH \<open>val(G,\<tau>) = _\<close>
    ultimately
    obtain q where "q\<in>G" "forces_mem(q, \<sigma>, \<tau>)" by auto
    moreover from this and \<open>p\<in>G\<close> \<open>M_generic(G)\<close>
    obtain r where "r\<in>P" "<r,p>\<in>leq" "<r,q>\<in>leq"
      by blast
    moreover
    note \<open>M_generic(G)\<close>
    ultimately
    have "forces_mem(r, \<sigma>, \<tau>)"
      using strengthening_mem by blast
    with \<open><r,p>\<in>leq\<close> \<open>forces_nmem(p,\<sigma>,\<tau>)\<close> \<open>r\<in>P\<close>
    have "False"
      unfolding forces_nmem_def by blast
    then
    show ?thesis by simp
  qed
qed

(* Lemma IV.2.40(b), full *)
lemma IV240b:
  assumes
    "M_generic(G)"
  shows 
    "(\<tau>\<in>M\<longrightarrow>\<theta>\<in>M\<longrightarrow>val(G,\<tau>) = val(G,\<theta>) \<longrightarrow> (\<exists>p\<in>G. forces_eq(p,\<tau>,\<theta>))) \<and>
     (\<tau>\<in>M\<longrightarrow>\<theta>\<in>M\<longrightarrow>val(G,\<tau>) \<in> val(G,\<theta>) \<longrightarrow> (\<exists>p\<in>G. forces_mem(p,\<tau>,\<theta>)))" 
    (is "?Q(\<tau>,\<theta>) \<and> ?R(\<tau>,\<theta>)")
proof (intro forces_induction)
  fix \<tau> \<theta> p
  assume "\<sigma>\<in>domain(\<theta>) \<Longrightarrow> ?Q(\<tau>, \<sigma>)" for \<sigma>
  with assms
  show "?R(\<tau>, \<theta>)"
    using IV240b_mem domain_closed Transset_intf[OF trans_M] by (simp)
next
  fix \<tau> \<theta> p
  assume "\<sigma> \<in> domain(\<tau>) \<union> domain(\<theta>) \<Longrightarrow> ?R(\<sigma>,\<tau>) \<and> ?R(\<sigma>,\<theta>)" for \<sigma>
  moreover from this
  have IH':"\<tau>\<in>M \<Longrightarrow> \<theta>\<in>M \<Longrightarrow> \<sigma> \<in> domain(\<tau>) \<union> domain(\<theta>) \<Longrightarrow>
          (val(G, \<sigma>) \<in> val(G, \<tau>) \<longrightarrow> (\<exists>q\<in>G. forces_mem(q, \<sigma>, \<tau>))) \<and>
          (val(G, \<sigma>) \<in> val(G, \<theta>) \<longrightarrow> (\<exists>q\<in>G. forces_mem(q, \<sigma>, \<theta>)))" for \<sigma> 
    by (blast intro:left_in_M) 
  ultimately
  show "?Q(\<tau>,\<theta>)"
    using IV240b_eq[OF assms(1)] by (auto)
qed

lemma map_val_in_MG:
  assumes 
    "env\<in>list(M)"
  shows 
    "map(val(G),env)\<in>list(M[G])"
  unfolding GenExt_def using assms map_type2 by simp

lemma truth_lemma_mem:
  assumes 
    "env\<in>list(M)" "M_generic(G)"
    "n\<in>nat" "m\<in>nat" "n<length(env)" "m<length(env)"
  shows 
    "(\<exists>p\<in>G.(p \<tturnstile> Member(n,m) env)) \<longleftrightarrow> sats(M[G],Member(n,m),map(val(G),env))"
  using assms IV240a[OF assms(2), of "nth(n,env)" "nth(m,env)"] 
    IV240b[OF assms(2), of "nth(n,env)" "nth(m,env)"] 
    P_in_M leq_in_M one_in_M 
    Forces_Member[of _  "nth(n,env)" "nth(m,env)" env n m] map_val_in_MG
  by (auto)

lemma truth_lemma_eq:
  assumes 
    "env\<in>list(M)" "M_generic(G)" 
    "n\<in>nat" "m\<in>nat" "n<length(env)" "m<length(env)"
  shows 
    "(\<exists>p\<in>G. (p \<tturnstile> Equal(n,m) env)) \<longleftrightarrow> sats(M[G],Equal(n,m),map(val(G),env))"
  using assms IV240a(1)[OF assms(2), of "nth(n,env)" "nth(m,env)"] 
    IV240b(1)[OF assms(2), of "nth(n,env)" "nth(m,env)"] 
    P_in_M leq_in_M one_in_M 
    Forces_Equal[of _  "nth(n,env)" "nth(m,env)" env n m] map_val_in_MG
  by (auto)

lemma arities_at_aux:
  assumes
    "n \<in> nat" "m \<in> nat" "env \<in> list(M)" "succ(n) \<union> succ(m) \<le> length(env)"
  shows
    "n < length(env)" "m < length(env)"
  using assms succ_leE[OF Un_leD1, of n "succ(m)" "length(env)"] 
   succ_leE[OF Un_leD2, of "succ(n)" m "length(env)"] by auto

lemma strengthening_lemma:
  assumes 
    "p\<in>P" "\<phi>\<in>formula" "r\<in>P" "<r,p>\<in>leq"
  shows
    "\<And>env. env\<in>list(M) \<Longrightarrow> arity(\<phi>)\<le>length(env) \<Longrightarrow> p \<tturnstile> \<phi> env \<Longrightarrow> r \<tturnstile> \<phi> env"
  using assms(2)
proof (induct)
  case (Member n m)
  then
  have "n<length(env)" "m<length(env)"
    using arities_at_aux by simp_all
  moreover
  assume "env\<in>list(M)"
  moreover
  note assms Member
  ultimately
  show ?case 
    using Forces_Member[of _ "nth(n,env)" "nth(m,env)" env n m]
      strengthening_mem[of p r "nth(n,env)" "nth(m,env)"] by simp
next
  case (Equal n m)
  then
  have "n<length(env)" "m<length(env)"
    using arities_at_aux by simp_all
  moreover
  assume "env\<in>list(M)"
  moreover
  note assms Equal
  ultimately
  show ?case 
    using Forces_Equal[of _ "nth(n,env)" "nth(m,env)" env n m]
      strengthening_eq[of p r "nth(n,env)" "nth(m,env)"] by simp
next
  case (Nand \<phi> \<psi>)
  with assms
  show ?case 
    using Forces_Nand Transset_intf[OF trans_M _ P_in_M] pair_in_M_iff 
      Transset_intf[OF trans_M _ leq_in_M] leq_transD by auto
next
  case (Forall \<phi>)
  with assms
  have "p \<tturnstile> \<phi> ([x] @ env)" if "x\<in>M" for x
    using that Forces_Forall by simp
  with Forall 
  have "r \<tturnstile> \<phi> ([x] @ env)" if "x\<in>M" for x
    using that pred_le2 by (simp)
  with assms Forall
  show ?case 
    using Forces_Forall by simp
qed

lemma dense_below_imp_forces:
  assumes 
    "p\<in>P" "\<phi>\<in>formula"
  shows
    "\<And>env. env\<in>list(M) \<Longrightarrow> arity(\<phi>)\<le>length(env) \<Longrightarrow>
     dense_below({q\<in>P. (q \<tturnstile> \<phi> env)},p) \<Longrightarrow> (p \<tturnstile> \<phi> env)"
  using assms(2)
proof (induct)
  case (Member n m)
  then
  have "n<length(env)" "m<length(env)"
    using arities_at_aux by simp_all
  moreover
  assume "env\<in>list(M)"
  moreover
  note assms Member
  ultimately
  show ?case 
    using Forces_Member[of _ "nth(n,env)" "nth(m,env)" env n m]
      density_mem[of p "nth(n,env)" "nth(m,env)"] by simp
next
  case (Equal n m)
  then
  have "n<length(env)" "m<length(env)"
    using arities_at_aux by simp_all
  moreover
  assume "env\<in>list(M)"
  moreover
  note assms Equal
  ultimately
  show ?case 
    using Forces_Equal[of _ "nth(n,env)" "nth(m,env)" env n m]
      density_eq[of p "nth(n,env)" "nth(m,env)"] by simp
next
  case (Nand \<phi> \<psi>)
  then 
  show ?case
    using sats_forces_Nand' sorry
next
  case (Forall \<phi>)
  have "dense_below({q\<in>P. q \<tturnstile> \<phi> ([a]@env)},p)" if "a\<in>M" for a
  proof
    fix r
    assume "r\<in>P" "<r,p>\<in>leq"
    with \<open>dense_below(_,p)\<close>
    obtain q where "q\<in>P" "<q,r>\<in>leq" "q \<tturnstile> Forall(\<phi>) env"
      by blast
    moreover
    note Forall \<open>a\<in>M\<close>
    moreover from calculation
    have "q \<tturnstile> \<phi> ([a]@env)"
      using Forces_Forall by simp
    ultimately
    show "\<exists>d \<in> {q\<in>P. q \<tturnstile> \<phi> ([a]@env)}. d \<in> P \<and> \<langle>d,r\<rangle> \<in> leq"
      by auto
  qed
  moreover 
  note Forall(2)[of "Cons(_,env)"] Forall(1,3-5)
  ultimately
  have "p \<tturnstile> \<phi> ([a]@env)" if "a\<in>M" for a
    using that pred_le2 by simp
  with assms Forall
  show ?case using Forces_Forall by simp
qed

lemma density_lemma:
  assumes
    "p\<in>P" "\<phi>\<in>formula" "env\<in>list(M)" "arity(\<phi>)\<le>length(env)"
  shows
    "(p \<tturnstile> \<phi> env) \<longleftrightarrow> dense_below({q\<in>P. (q \<tturnstile> \<phi> env)},p)"
proof
  assume "dense_below({q\<in>P. (q \<tturnstile> \<phi> env)},p)"
  with assms
  show  "(p \<tturnstile> \<phi> env)"
    using dense_below_imp_forces by simp
next
  assume "p \<tturnstile> \<phi> env"
  with assms
  show "dense_below({q\<in>P. q \<tturnstile> \<phi> env},p)"
    using strengthening_lemma leq_reflI by auto
qed

lemma Forces_And:
  assumes
    "p\<in>P" "env \<in> list(M)" "\<phi>\<in>formula" "\<psi>\<in>formula" 
    "arity(\<phi>) \<le> length(env)" "arity(\<psi>) \<le> length(env)"
  shows
    "(p \<tturnstile> And(\<phi>,\<psi>) env) \<longleftrightarrow> (p \<tturnstile> \<phi> env) \<and> (p \<tturnstile> \<psi> env)"
proof
  assume "p \<tturnstile> And(\<phi>, \<psi>) env"
  with assms
  have "dense_below({r \<in> P . (r \<tturnstile> \<phi> env) \<and> (r \<tturnstile> \<psi> env)}, p)"
    using Forces_And_iff_dense_below by simp
  then
  have "dense_below({r \<in> P . (r \<tturnstile> \<phi> env)}, p)" "dense_below({r \<in> P . (r \<tturnstile> \<psi> env)}, p)"
    by blast+
  with assms
  show "(p \<tturnstile> \<phi> env) \<and> (p \<tturnstile> \<psi> env)"
    using density_lemma[symmetric] by simp
next
  assume "(p \<tturnstile> \<phi> env) \<and> (p \<tturnstile> \<psi> env)"
  have "dense_below({r \<in> P . (r \<tturnstile> \<phi> env) \<and> (r \<tturnstile> \<psi> env)}, p)"
  proof (intro dense_belowI bexI conjI, assumption)
    fix q
    assume "q\<in>P" "\<langle>q, p\<rangle> \<in> leq"
    with assms \<open>(p \<tturnstile> \<phi> env) \<and> (p \<tturnstile> \<psi> env)\<close>
    show "q\<in>{r \<in> P . (r \<tturnstile> \<phi> env) \<and> (r \<tturnstile> \<psi> env)}" "\<langle>q, q\<rangle> \<in> leq"
      using strengthening_lemma leq_reflI by auto
  qed
  with assms
  show "p \<tturnstile> And(\<phi>,\<psi>) env"
    using Forces_And_iff_dense_below by simp
qed

lemma Forces_Nand_alt:
  assumes
    "p\<in>P" "env \<in> list(M)" "\<phi>\<in>formula" "\<psi>\<in>formula" 
    "arity(\<phi>) \<le> length(env)" "arity(\<psi>) \<le> length(env)"
  shows
    "(p \<tturnstile> Nand(\<phi>,\<psi>) env) \<longleftrightarrow> \<not>(\<exists>q\<in>M. q\<in>P \<and> <q,p>\<in>leq \<and> (q \<tturnstile> And(\<phi>,\<psi>) env))"
  using assms Forces_Nand Forces_And by simp

lemma truth_lemma:
  assumes 
    "\<phi>\<in>formula" "M_generic(G)"
  shows 
     "\<And>env. env\<in>list(M) \<Longrightarrow> arity(\<phi>)\<le>length(env) \<Longrightarrow> 
      (\<exists>p\<in>G. (p \<tturnstile> \<phi> env)) \<longleftrightarrow> sats(M[G],\<phi>,map(val(G),env))"
  using assms(1)
proof (induct)
  case (Member x y)
  then
  show ?case
    using assms truth_lemma_mem[OF \<open>env\<in>list(M)\<close> assms(2) \<open>x\<in>nat\<close> \<open>y\<in>nat\<close>] 
      arities_at_aux by simp
next
  case (Equal x y)
  then
  show ?case
    using assms truth_lemma_eq[OF \<open>env\<in>list(M)\<close> assms(2) \<open>x\<in>nat\<close> \<open>y\<in>nat\<close>] 
      arities_at_aux by simp
next (* This case will probably need a density argument *)
  case (Nand p q)
  then 
  show ?case
    unfolding forces_def 
    sorry
next
  case (Forall \<phi>)
  with \<open>M_generic(G)\<close>
  show ?case
  proof (intro iffI)
    assume "\<exists>p\<in>G. (p \<tturnstile> Forall(\<phi>) env)"
    with \<open>M_generic(G)\<close>
    obtain p where "p\<in>G" "p\<in>M" "p\<in>P" "p \<tturnstile> Forall(\<phi>) env"
      using Transset_intf[OF trans_M _ P_in_M] by auto
    with \<open>env\<in>list(M)\<close> \<open>\<phi>\<in>formula\<close>
    have "p \<tturnstile> \<phi> ([x]@env)" if "x\<in>M" for x
      using that Forces_Forall by simp
    with \<open>p\<in>G\<close> \<open>\<phi>\<in>formula\<close> \<open>env\<in>_\<close> \<open>arity(Forall(\<phi>)) \<le> length(env)\<close>
      Forall(2)[of "Cons(_,env)"] 
    show "sats(M[G], Forall(\<phi>), map(val(G),env))"
      using pred_le2 map_val_in_MG
      by (auto iff:GenExtD)
  next
    assume "sats(M[G], Forall(\<phi>), map(val(G),env))"
    let ?D1="{d\<in>P. (d \<tturnstile> Forall(\<phi>) env)}"
    let ?D2="{d\<in>P. \<exists>b\<in>M. \<forall>q\<in>P. <q,d>\<in>leq \<longrightarrow> \<not>(q \<tturnstile> \<phi> ([b]@env))}"
    define D where "D \<equiv> ?D1 \<union> ?D2"
    have "D \<subseteq> P" unfolding D_def by auto
    moreover
    have "D\<in>M" sorry
    moreover
    have "dense(D)" 
    proof (standard, intro ballI)
      fix p
      assume "p\<in>P"
      show "\<exists>d\<in>D. \<langle>d, p\<rangle> \<in> leq"
      proof (cases "p \<tturnstile> Forall(\<phi>) env")
        case True
        with \<open>p\<in>P\<close> 
        show ?thesis unfolding D_def using leq_reflI by blast
      next
        case False
        with Forall \<open>p\<in>P\<close>
        obtain b where "b\<in>M" "\<not>(p \<tturnstile> \<phi> ([b]@env))"
          using Forces_Forall by blast
        moreover from this \<open>p\<in>P\<close> Forall
        have "\<not>dense_below({q\<in>P. q \<tturnstile> \<phi> ([b]@env)},p)"
          using density_lemma pred_le2  by auto
        moreover from this
        obtain d where "<d,p>\<in>leq" "\<forall>q\<in>P. <q,d>\<in>leq \<longrightarrow> \<not>(q \<tturnstile> \<phi> ([b] @ env))"
          "d\<in>P" by blast
        ultimately
        show ?thesis unfolding D_def by auto
      qed
    qed
    moreover
    note \<open>M_generic(G)\<close>
    ultimately
    obtain d where "d \<in> D"  "d \<in> G" by blast
    then
    consider (1) "d\<in>?D1" | (2) "d\<in>?D2" unfolding D_def by blast
    then
    show "\<exists>p\<in>G. (p \<tturnstile> Forall(\<phi>) env)"
    proof (cases)
      case 1
      with \<open>d\<in>G\<close>
      show ?thesis by blast
    next
      case 2
      then
      obtain b where "b\<in>M" "\<forall>q\<in>P. <q,d>\<in>leq \<longrightarrow>\<not>(q \<tturnstile> \<phi> ([b] @ env))"
        by blast
      moreover from this(1) and  \<open>sats(M[G], Forall(\<phi>),_)\<close> and 
        Forall(2)[of "Cons(b,env)"] Forall(1,3-4) \<open>M_generic(G)\<close>
      obtain p where "p\<in>G" "p\<in>P" "p \<tturnstile> \<phi> ([b] @ env)" 
        using pred_le2 using map_val_in_MG by (auto iff:GenExtD)
      moreover
      note \<open>d\<in>G\<close> \<open>M_generic(G)\<close>
      ultimately
      obtain q where "q\<in>G" "q\<in>P" "<q,d>\<in>leq" "<q,p>\<in>leq" by blast
      moreover from this and  \<open>p \<tturnstile> \<phi> ([b] @ env)\<close> 
        Forall  \<open>b\<in>M\<close> \<open>p\<in>P\<close>
      have "q \<tturnstile> \<phi> ([b] @ env)"
        using pred_le2 strengthening_lemma by simp
      moreover 
      note \<open>\<forall>q\<in>P. <q,d>\<in>leq \<longrightarrow>\<not>(q \<tturnstile> \<phi> ([b] @ env))\<close>
      ultimately
      show ?thesis by simp
    qed
  qed
qed

lemma definition_of_forces:
  assumes
    "p\<in>P" "\<phi>\<in>formula" "env\<in>list(M)" "arity(\<phi>)\<le>length(env)"
  shows
    "(p \<tturnstile> \<phi> env) \<longleftrightarrow>
     (\<forall>G.(M_generic(G)\<and> p\<in>G)\<longrightarrow>sats(M[G],\<phi>,map(val(G),env)))"
proof (intro iffI allI impI, elim conjE)
  fix G
  assume "(p \<tturnstile> \<phi> env)" "M_generic(G)" "p \<in> G"
  with assms 
  show "sats(M[G],\<phi>,map(val(G),env))"
    using truth_lemma by blast
next
  assume 1: "\<forall>G.(M_generic(G)\<and> p\<in>G)\<longrightarrow>sats(M[G],\<phi>,map(val(G),env))"
  {
    fix r 
    assume 2: "r\<in>P" "<r,p>\<in>leq"
    then 
    obtain G where "r\<in>G" "M_generic(G)"
      using generic_filter_existence by auto
    moreover from calculation 2 \<open>p\<in>P\<close> 
    have "p\<in>G" 
      unfolding M_generic_def using filter_leqD by simp
    moreover note 1
    ultimately
    have "sats(M[G],\<phi>,map(val(G),env))"
      by simp
    with assms \<open>M_generic(G)\<close> 
    obtain s where "s\<in>G" "(s \<tturnstile> \<phi> env)"
      using truth_lemma by blast
    moreover from this and  \<open>M_generic(G)\<close> \<open>r\<in>G\<close> 
    obtain q where "q\<in>G" "<q,s>\<in>leq" "<q,r>\<in>leq"
      by blast
    moreover from calculation \<open>s\<in>G\<close> \<open>M_generic(G)\<close> 
    have "s\<in>P" "q\<in>P" 
      unfolding M_generic_def filter_def by auto
    moreover 
    note assms
    ultimately 
    have "\<exists>q\<in>P. <q,r>\<in>leq \<and> (q \<tturnstile> \<phi> env)"
      using strengthening_lemma by blast
  }
  then
  have "dense_below({q\<in>P. (q \<tturnstile> \<phi> env)},p)"
    unfolding dense_below_def by blast
  with assms
  show "(p \<tturnstile> \<phi> env)"
    using density_lemma by blast
qed

lemmas definability = forces_type 
end (* forcing_data *)

end