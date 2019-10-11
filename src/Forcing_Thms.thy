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

lemma dense_iff [iff] : "dense(D) \<longleftrightarrow> (\<forall>p\<in>P. \<exists>d\<in>D. \<langle>d, p\<rangle> \<in> leq)"
  unfolding dense_def ..

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

(* Kunen 2013, Lemma IV.2.37(a) *)
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

(* Kunen 2013, Lemma IV.2.37(a) *)
lemma strengthening_mem: 
  assumes "p\<in>P" "r\<in>P" "<r,p>\<in>leq" "forces_mem(P,leq,p,t1,t2)"
  shows "forces_mem(P,leq,r,t1,t2)"
  using assms forces_mem_iff_dense_below dense_below_under by auto

(* Kunen 2013, Lemma IV.2.37(b) *)
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

lemma aux_density_eq:
  assumes 
    "dense_below(
    {q'\<in>P. \<forall>q. q\<in>P \<and> \<langle>q,q'\<rangle>\<in>leq \<longrightarrow> forces_mem(P,leq,q,s,t1) \<longleftrightarrow> forces_mem(P,leq,q,s,t2)}
    ,p)"
    "forces_mem(P,leq,q,s,t1)" "q\<in>P" "p\<in>P" "<q,p>\<in>leq"
  shows
    "dense_below({r\<in>P. forces_mem(P,leq,r,s,t2)},q)"
proof
  fix r
  assume "r\<in>P" "\<langle>r,q\<rangle> \<in> leq"
  moreover from this and \<open>p\<in>P\<close> \<open><q,p>\<in>leq\<close> \<open>q\<in>P\<close>
  have "<r,p>\<in>leq"
    using leq_transD by simp
  moreover
  note \<open>forces_mem(_,_,q,s,t1)\<close> \<open>dense_below(_,p)\<close> \<open>q\<in>P\<close>
  ultimately
  obtain q1 where "<q1,r>\<in>leq" "q1\<in>P" "forces_mem(P,leq,q1,s,t2)"
    using strengthening_mem[of q _ s t1] leq_reflI leq_transD[of _ r q] by blast
  then
  show "\<exists>d\<in>{r \<in> P . forces_mem(P, leq, r, s, t2)}. d \<in> P \<and> \<langle>d, r\<rangle> \<in> leq"
    by blast
qed

(* Kunen 2013, Lemma IV.2.37(b) *)
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
    assume "s\<in>domain(t1) \<union> domain(t2)" 
    then
    have "?D1\<subseteq>?D2" by blast
    with \<open>dense_below(_,p)\<close>
    have "dense_below({q'\<in>P. \<forall>s\<in>domain(t1) \<union> domain(t2). \<forall>q. q \<in> P \<and> \<langle>q,q'\<rangle>\<in>leq \<longrightarrow>
           forces_mem(P,leq,q,s,t1)\<longleftrightarrow>forces_mem(P,leq,q,s,t2)},p)"
      using dense_below_cong'[OF \<open>p\<in>P\<close> def_forces_eq[of _ t1 t2]] by simp
    with \<open>p\<in>P\<close> \<open>?D1\<subseteq>?D2\<close>
    have "dense_below({q'\<in>P. \<forall>q. q\<in>P \<and> \<langle>q,q'\<rangle>\<in>leq \<longrightarrow> 
            forces_mem(P,leq,q,s,t1) \<longleftrightarrow> forces_mem(P,leq,q,s,t2)},p)"
      using dense_below_mono by simp
    moreover from this (* Automatic tools can't handle this symmetry 
                          in order to apply aux_density_eq below *)
    have  "dense_below({q'\<in>P. \<forall>q. q\<in>P \<and> \<langle>q,q'\<rangle>\<in>leq \<longrightarrow> 
            forces_mem(P,leq,q,s,t2) \<longleftrightarrow> forces_mem(P,leq,q,s,t1)},p)"
      by blast
    moreover
    assume "q \<in> P" "<q,p>\<in>leq"
    moreover
    note \<open>p\<in>P\<close>
    ultimately (*We can omit the next step but it is slower *)
    have "forces_mem(P,leq,q,s,t1) \<Longrightarrow> dense_below({r\<in>P. forces_mem(P,leq,r,s,t2)},q)"
         "forces_mem(P,leq,q,s,t2) \<Longrightarrow> dense_below({r\<in>P. forces_mem(P,leq,r,s,t1)},q)" 
      using aux_density_eq by simp_all
    then
    have "forces_mem(P, leq, q, s, t1) \<longleftrightarrow> forces_mem(P, leq, q, s, t2)"
      using density_mem[OF \<open>q\<in>P\<close>] by blast
  }
  with \<open>p\<in>P\<close>
  show "forces_eq(P,leq,p,t1,t2)" using def_forces_eq by blast
qed

definition
  forces_neq :: "[i,i,i] \<Rightarrow> o" where
  "forces_neq(p,t1,t2) \<equiv> \<not> (\<exists>q\<in>P. <q,p>\<in>leq \<and> forces_eq(P,leq,q,t1,t2))"

definition
  forces_nmem :: "[i,i,i] \<Rightarrow> o" where
  "forces_nmem(p,t1,t2) \<equiv> \<not> (\<exists>q\<in>P. <q,p>\<in>leq \<and> forces_mem(P,leq,q,t1,t2))"

(* Kunen 2013, Lemma IV.2.38 *)
lemma not_forces_neq:
  assumes "p\<in>P"
  shows "forces_eq(P,leq,p,t1,t2) \<longleftrightarrow> \<not> (\<exists>q\<in>P. <q,p>\<in>leq \<and> forces_neq(q,t1,t2))"
  using assms density_eq unfolding forces_neq_def by blast

(* Kunen 2013, Lemma IV.2.38 *)
lemma not_forces_nmem:
  assumes "p\<in>P"
  shows "forces_mem(P,leq,p,t1,t2) \<longleftrightarrow> \<not> (\<exists>q\<in>P. <q,p>\<in>leq \<and> forces_nmem(q,t1,t2))"
  using assms density_mem unfolding forces_nmem_def by blast

lemma sats_forces_Equal:
  assumes
    "p\<in>P" "t1\<in>M" "t2\<in>M" "env\<in>list(M)" "nth(n,env) = t1" "nth(m,env) = t2"
  shows
    "sats(M,forces(Equal(n,m)),[P,leq,one,p] @ env) \<longleftrightarrow> forces_eq(P,leq,p,t1,t2)"
  sorry

lemma sats_forces_Member:
  assumes
    "p\<in>P" "t1\<in>M" "t2\<in>M" "env\<in>list(M)" "nth(n,env) = t1" "nth(m,env) = t2"
  shows
    "sats(M,forces(Member(n,m)),[P,leq,one,p] @ env) \<longleftrightarrow> forces_mem(P,leq,p,t1,t2)"
  sorry

(* Move the following to an appropriate place *)
(* "x\<in>val(G,\<pi>) \<Longrightarrow> \<exists>\<theta>. \<exists>p\<in>G.  <\<theta>,p>\<in>\<pi> \<and> val(G,\<theta>) = x" *)
declare elem_of_val_pair [dest] SepReplace_iff [simp del] SepReplace_iff[iff]

lemma elem_of_valI [intro!]: "\<exists>\<theta>. \<exists>p\<in>P. p\<in>G \<and> <\<theta>,p>\<in>\<pi> \<and> val(G,\<theta>) = x \<Longrightarrow> x\<in>val(G,\<pi>)"
  by (subst def_val, auto)

lemma M_genericD [dest]: "M_generic(G) \<Longrightarrow> x\<in>G \<Longrightarrow> x\<in>P"
  unfolding M_generic_def by (blast dest:filterD)

lemma M_generic_leqD [dest]: "M_generic(G) \<Longrightarrow> p\<in>G \<Longrightarrow> q\<in>P \<Longrightarrow> <p,q>\<in>leq \<Longrightarrow> q\<in>G"
  unfolding M_generic_def by (blast dest:filter_leqD)

lemma M_generic_compatD [dest]: "M_generic(G) \<Longrightarrow> p\<in>G \<Longrightarrow> r\<in>G \<Longrightarrow> \<exists>q\<in>G. <q,p>\<in>leq \<and> <q,r>\<in>leq"
  unfolding M_generic_def by (blast dest:low_bound_filter)

lemma left_in_M : "tau\<in>M \<Longrightarrow> <a,b>\<in>tau \<Longrightarrow> a\<in>M"
  using fst_snd_closed[of "<a,b>"] Transset_intf[OF trans_M] by auto

(* Kunen 2013, Lemma IV.2.29 *)
lemma generic_inter_dense_below: "D:M ==> M_generic(G) ==> dense_below(D,p) ==> p\<in>G ==> D \<inter> G \<noteq> 0"
  sorry

(* Lemma IV.2.40(a), membership *)
lemma IV240a_mem:
  assumes
    "M_generic(G)" "p\<in>G" "p\<in>P" "forces_mem(P,leq,p,\<pi>,\<tau>)" "\<pi>\<in>M" "\<tau>\<in>M"
    "\<And>q \<sigma>. q\<in>P \<Longrightarrow> \<sigma>\<in>domain(\<tau>) \<Longrightarrow> forces_eq(P,leq,q,\<pi>,\<sigma>) \<Longrightarrow> 
      val(G,\<pi>) = val(G,\<sigma>)" (* inductive hypothesis *)
  shows
    "val(G,\<pi>)\<in>val(G,\<tau>)"
proof
  let ?D="{q\<in>P. \<exists>\<sigma>. \<exists>r. r\<in>P \<and> <\<sigma>,r> \<in> \<tau> \<and> <q,r>\<in>leq \<and> forces_eq(P,leq,q,\<pi>,\<sigma>)}"
  from assms
  have "?D = {q\<in>P. \<exists>\<sigma>. \<exists>r. r\<in>P \<and> <\<sigma>,r> \<in> \<tau> \<and> <q,r>\<in>leq \<and> sats(M,forces(Equal(0,1)),[P,leq,one,q,\<pi>,\<sigma>])}"
    using sats_forces_Equal[of _ \<pi> _ "[\<pi>, _]" 0 1]  left_in_M  by simp
  moreover from \<open>M_generic(G)\<close> \<open>p\<in>P\<close>
  have "p\<in>P" by blast
  moreover
  note \<open>\<pi>\<in>M\<close> \<open>\<tau>\<in>M\<close>
  ultimately
  have "?D \<in> M" 
    using leq_in_M one_in_M P_in_M Transset_intf[OF trans_M _ P_in_M] (* or else P_sub_M *) sorry
  moreover from assms
  have "dense_below(?D,p)"
    using forces_mem_iff_dense_below by simp
  moreover
  note \<open>M_generic(G)\<close> \<open>p\<in>G\<close>
  ultimately
  obtain q where "q\<in>G" "q\<in>?D" using generic_inter_dense_below by blast
  then
  obtain \<sigma> r where "r\<in>P" "<\<sigma>,r> \<in> \<tau>" "<q,r>\<in>leq" "forces_eq(P,leq,q,\<pi>,\<sigma>)" by blast
  moreover from this and \<open>q\<in>G\<close> assms
  have "r \<in> G" "val(G,\<pi>) = val(G,\<sigma>)" by blast+
  ultimately
  show "\<exists> \<sigma>. \<exists>p\<in>P. p \<in> G \<and> \<langle>\<sigma>, p\<rangle> \<in> \<tau> \<and> val(G, \<sigma>) = val(G, \<pi>)" by auto
qed

(* Example IV.2.36 (next two lemmas) *)
lemma refl_forces_eq:"p\<in>P \<Longrightarrow> forces_eq(P,leq,p,x,x)"
  using def_forces_eq by simp

lemma forces_memI: "<\<sigma>,r>\<in>\<tau> \<Longrightarrow> p\<in>P \<Longrightarrow> r\<in>P \<Longrightarrow> <p,r>\<in>leq \<Longrightarrow> forces_mem(P,leq,p,\<sigma>,\<tau>)"
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

(* Lemma IV.2.40(a), equality *)
lemma
  assumes
    "M_generic(G)" "p\<in>G" "forces_eq(P,leq,p,\<tau>,\<theta>)" "\<pi>\<in>M" "\<tau>\<in>M"
    and
    IH:"\<And>q \<sigma>. q\<in>P \<Longrightarrow> \<sigma>\<in>domain(\<tau>) \<Longrightarrow> forces_mem(P,leq,q,\<sigma>,\<theta>) \<Longrightarrow> 
      val(G,\<sigma>) \<in> val(G,\<theta>)"
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
  have "forces_mem(P,leq,q,\<sigma>,\<tau>)"
    using forces_memI M_genericD[OF \<open>M_generic(G)\<close>] by blast
  moreover
  note \<open>forces_eq(P,leq,p,\<tau>,\<theta>)\<close>
  ultimately
  have "forces_mem(P,leq,q,\<sigma>,\<theta>)"
    using def_forces_eq by blast
  with \<open>q\<in>P\<close> IH[of q \<sigma>] \<open><\<sigma>,r>\<in>\<tau>\<close> \<open>val(G,\<sigma>) = x\<close>
  show "x\<in>val(G,\<theta>)" by (blast del:elem_of_valI)
qed

(* Lemma IV.2.40(b), membership *)
lemma
  assumes
    "M_generic(G)" "val(G,\<pi>)\<in>val(G,\<tau>)" "\<pi>\<in>M" "\<tau>\<in>M"
    and
    IH:"\<And>\<sigma>. \<sigma>\<in>domain(\<tau>) \<Longrightarrow> val(G,\<pi>) = val(G,\<sigma>) \<Longrightarrow> 
      \<exists>p\<in>G. forces_eq(P,leq,p,\<pi>,\<sigma>)" (* inductive hypothesis *)
  shows
    "\<exists>p\<in>G. forces_mem(P,leq,p,\<pi>,\<tau>)"
proof -
  from \<open>val(G,\<pi>)\<in>val(G,\<tau>)\<close>
  obtain \<sigma> r where "r\<in>G" "<\<sigma>,r>\<in>\<tau>" "val(G,\<pi>) = val(G,\<sigma>)" by auto
  moreover from this and IH
  obtain p' where "p'\<in>G" "forces_eq(P,leq,p',\<pi>,\<sigma>)" by blast
  moreover
  note \<open>M_generic(G)\<close>
  ultimately
  obtain p where "<p,r>\<in>leq" "p\<in>G" "forces_eq(P,leq,p,\<pi>,\<sigma>)" 
    using M_generic_compatD strengthening_eq[of p'] by blast
  moreover 
  note \<open>M_generic(G)\<close>
  moreover from calculation
  have "forces_eq(P,leq,q,\<pi>,\<sigma>)" if "q\<in>P" "<q,p>\<in>leq" for q
    using that strengthening_eq by blast
  moreover 
  note \<open><\<sigma>,r>\<in>\<tau>\<close> \<open>r\<in>G\<close>
  ultimately
  have "r\<in>P \<and> \<langle>\<sigma>,r\<rangle> \<in> \<tau> \<and> \<langle>q,r\<rangle> \<in> leq \<and> forces_eq(P,leq,q,\<pi>,\<sigma>)" if "q\<in>P" "<q,p>\<in>leq" for q
    using that leq_transD[of _ p r] by blast
  then
  have "dense_below({q\<in>P. \<exists>s r. r\<in>P \<and> \<langle>s,r\<rangle> \<in> \<tau> \<and> \<langle>q,r\<rangle>\<in>leq \<and> forces_eq(P,leq,q,\<pi>,s)},p)"
    using leq_reflI by blast
  moreover
  note \<open>M_generic(G)\<close> \<open>p\<in>G\<close>
  moreover from calculation
  have "forces_mem(P,leq,p,\<pi>,\<tau>)" 
    using forces_mem_iff_dense_below by blast
  ultimately
  show ?thesis by blast
qed

(* Lemma IV.2.40(b), equality *)
lemma
  assumes
    "M_generic(G)" "p\<in>G" "val(G,\<tau>) = val(G,\<theta>)" "\<tau>\<in>M" "\<theta>\<in>M" 
    and
    IH:"\<And>\<sigma> \<tau> \<theta>. \<sigma>\<in>domain(\<tau>)\<union>domain(\<theta>) \<Longrightarrow> val(G,\<sigma>)\<in>val(G,\<theta>) \<Longrightarrow> \<exists>q\<in>G. forces_mem(P,leq,q,\<sigma>,\<theta>)"
  shows
    "\<exists>p\<in>G. forces_eq(P,leq,p,\<tau>,\<theta>)"
proof -
  let ?D="{p\<in>P. forces_eq(P,leq,p,\<tau>,\<theta>) 
     \<or> (\<exists>\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>). forces_mem(P,leq,p,\<sigma>,\<tau>) \<and> forces_nmem(p,\<sigma>,\<theta>))
     \<or> (\<exists>\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>). forces_nmem(p,\<sigma>,\<tau>) \<and> forces_mem(P,leq,p,\<sigma>,\<theta>))}"
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
    have "forces_mem(P,leq,p,\<sigma>,\<tau>)\<longleftrightarrow>sats(M,forces(Member(0,1)),[P,leq,one,p,\<sigma>,\<tau>])"
      "forces_mem(P,leq,p,\<sigma>,\<theta>)\<longleftrightarrow>sats(M,forces(Member(0,1)),[P,leq,one,p,\<sigma>,\<theta>])"
      if "p\<in>P" and "\<sigma>\<in>M" for p \<sigma> 
      using that sats_forces_Member[OF \<open>p\<in>P\<close> \<open>\<sigma>\<in>M\<close>, of _ "[\<sigma>,_]" 0 1] by simp_all
    moreover
    note assms
    ultimately
    have "(\<exists>\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>). forces_mem(P,leq,p,\<sigma>,\<tau>) \<and> forces_nmem(p,\<sigma>,\<theta>))
      \<or> (\<exists>\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>). forces_nmem(p,\<sigma>,\<tau>) \<and> forces_mem(P,leq,p,\<sigma>,\<theta>))
   \<longleftrightarrow>
        (\<exists>\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>). sats(M,forces(Member(0,1)),[P,leq,one,p,\<sigma>,\<tau>]) 
             \<and> \<not> (\<exists>q\<in>P. <q,p>\<in>leq \<and> sats(M,forces(Member(0,1)),[P,leq,one,q,\<sigma>,\<theta>])))
      \<or> (\<exists>\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>). 
              \<not> (\<exists>q\<in>P. <q,p>\<in>leq \<and>  sats(M,forces(Member(0,1)),[P,leq,one,q,\<sigma>,\<tau>])) 
             \<and> sats(M,forces(Member(0,1)),[P,leq,one,p,\<sigma>,\<theta>])) " if "p\<in>P" for p
      unfolding forces_nmem_def using that sorry
    with assms
    show ?thesis
      using sats_forces_Equal[of _ \<tau> \<theta> "[\<tau>,\<theta>]" 0 1] by auto
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
    (1) "forces_eq(P,leq,p,\<tau>,\<theta>)" | 
    (2) "\<exists>\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>). forces_mem(P,leq,p,\<sigma>,\<tau>) \<and> forces_nmem(p,\<sigma>,\<theta>)" | 
    (3) "\<exists>\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>). forces_nmem(p,\<sigma>,\<tau>) \<and> forces_mem(P,leq,p,\<sigma>,\<theta>)"
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
    obtain \<sigma> where "\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>)" "forces_mem(P,leq,p,\<sigma>,\<tau>)" "forces_nmem(p,\<sigma>,\<theta>)" 
      by blast
    moreover from this and \<open>p\<in>G\<close> and assms
    have "val(G,\<sigma>)\<in>val(G,\<tau>)" sorry
    moreover note IH[of _ \<tau> \<theta>] \<open>val(G,\<tau>) = _\<close>
    ultimately
    obtain q where "q\<in>G" "forces_mem(P, leq, q, \<sigma>, \<theta>)" by auto
    moreover from this and \<open>p\<in>G\<close> \<open>M_generic(G)\<close>
    obtain r where "r\<in>P" "<r,p>\<in>leq" "<r,q>\<in>leq"
      by blast
    moreover
    note \<open>M_generic(G)\<close>
    ultimately
    have "forces_mem(P, leq, r, \<sigma>, \<theta>)"
      using strengthening_mem by blast
    with \<open><r,p>\<in>leq\<close> \<open>forces_nmem(p,\<sigma>,\<theta>)\<close> \<open>r\<in>P\<close>
    have "False"
      unfolding forces_nmem_def by blast
    then
    show ?thesis by simp
  next (* copy-paste from case 2 mutatis mutandis*)
    case 3
    then
    obtain \<sigma> where "\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>)" "forces_mem(P,leq,p,\<sigma>,\<theta>)" "forces_nmem(p,\<sigma>,\<tau>)" 
      by blast
    moreover from this and \<open>p\<in>G\<close> and assms
    have "val(G,\<sigma>)\<in>val(G,\<theta>)" sorry
    moreover note IH[of _ \<theta> \<tau>] \<open>val(G,\<tau>) = _\<close>
    ultimately
    obtain q where "q\<in>G" "forces_mem(P, leq, q, \<sigma>, \<tau>)" by auto
    moreover from this and \<open>p\<in>G\<close> \<open>M_generic(G)\<close>
    obtain r where "r\<in>P" "<r,p>\<in>leq" "<r,q>\<in>leq"
      by blast
    moreover
    note \<open>M_generic(G)\<close>
    ultimately
    have "forces_mem(P, leq, r, \<sigma>, \<tau>)"
      using strengthening_mem by blast
    with \<open><r,p>\<in>leq\<close> \<open>forces_nmem(p,\<sigma>,\<tau>)\<close> \<open>r\<in>P\<close>
    have "False"
      unfolding forces_nmem_def by blast
    then
    show ?thesis by simp
  qed
qed

end

end