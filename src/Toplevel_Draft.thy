theory Toplevel_Draft
  imports
    Cardinal_Preservation
    "../Delta_System_Lemma/Delta_System"
    Cohen_Posets

begin

definition
  Add_subs :: "[i,i] \<Rightarrow> i" where
  "Add_subs(\<kappa>,\<alpha>) \<equiv> Fn(\<omega>,\<kappa>\<times>\<alpha>,2)"

definition (* fake def *)
  Aleph_rel :: "[i\<Rightarrow>o,i] \<Rightarrow> i" where
  "Aleph_rel(M,a) \<equiv> Aleph(a)"

abbreviation
  Aleph_r :: "[i,i\<Rightarrow>o] \<Rightarrow> i" (\<open>\<aleph>\<^bsub>_\<^esub>\<^bsup>_\<^esup>\<close>) where
  "Aleph_r(a,M) \<equiv> Aleph_rel(M,a)"

abbreviation
  Aleph_r_set :: "[i,i] \<Rightarrow> i" (\<open>\<aleph>\<^bsub>_\<^esub>\<^bsup>_\<^esup>\<close>) where
  "Aleph_r_set(a,M) \<equiv> Aleph_rel(##M,a)"

definition
  cexp_rel :: "[i\<Rightarrow>o,i,i] \<Rightarrow> i" where
  def_cexp_rel:"cexp_rel(M,x,y) \<equiv> |y\<rightarrow>\<^bsup>M\<^esup> x|\<^bsup>M\<^esup>"

abbreviation
  cexp_r :: "[i,i,i\<Rightarrow>o] \<Rightarrow> i"  (\<open>'(_\<^bsup>\<up>_\<^esup>')\<^bsup>_\<^esup>\<close>) where
  "cexp_r(x,y,M) \<equiv> cexp_rel(M,x,y)"

abbreviation
  cexp_r_set :: "[i,i,i] \<Rightarrow> i"  (\<open>'(_\<^bsup>\<up>_\<^esup>')\<^bsup>_\<^esup>\<close>) where
  "cexp_r_set(x,y,M) \<equiv> cexp_rel(##M,x,y)"

abbreviation
  csucc_r :: "[i,i\<Rightarrow>o] \<Rightarrow> i"  (\<open>'(_\<^sup>+')\<^bsup>_\<^esup>\<close>) where
  "csucc_r(x,M) \<equiv> csucc_rel(M,x)"

abbreviation
  csucc_r_set :: "[i,i] \<Rightarrow> i"  (\<open>'(_\<^sup>+')\<^bsup>_\<^esup>\<close>) where
  "csucc_r_set(x,M) \<equiv> csucc_rel(##M,x)"

locale M_master = M_cardinal_AC
begin

lemma FiniteFun_closed[intro,simp]:
  assumes "M(A)" "M(B)" shows "M(A-||>B)"
  sorry

lemma Fn_nat_closed[intro,simp]:
  assumes "M(A)" "M(B)" shows "M(Fn(\<omega>,A,B))"
  using assms Fn_nat_eq_FiniteFun
  by simp

lemma csucc_rel_le: "Card\<^bsup>M\<^esup>(l) \<Longrightarrow> K < l \<Longrightarrow> (K\<^sup>+)\<^bsup>M\<^esup> \<le> l"
  sorry

lemma nat_lt_Aleph_rel1: "\<omega> < \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
  sorry

lemma Aleph_rel_closed[intro,simp]: "M(a) \<Longrightarrow> M(\<aleph>\<^bsub>a\<^esub>\<^bsup>M\<^esup>)"
  sorry

lemma Aleph_rel2_closed[intro,simp]: "M(\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>)"
  using  nat_into_M[of 2, THEN Aleph_rel_closed] by simp

lemma Card_rel_Aleph_rel[simp]: "Ord(\<alpha>) \<Longrightarrow> Card\<^bsup>M\<^esup>(\<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup>)"
  sorry

lemma Aleph_rel_zero_eq_nat: "\<aleph>\<^bsub>0\<^esub>\<^bsup>M\<^esup> =  \<omega>"
  sorry

lemma Aleph_rel_succ: "\<aleph>\<^bsub>succ(\<alpha>)\<^esub>\<^bsup>M\<^esup> = (\<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup>\<^sup>+)\<^bsup>M\<^esup>"
  sorry

lemma Aleph_rel_increasing:  "a < b  \<Longrightarrow> M(a) \<Longrightarrow> M(b) \<Longrightarrow> \<aleph>\<^bsub>a\<^esub>\<^bsup>M\<^esup> < \<aleph>\<^bsub>b\<^esub>\<^bsup>M\<^esup>"
  sorry

lemma Fnle_closed[intro,simp]:
  assumes "M(\<kappa>)" "M(I)" "M(J)"
  shows "M(Fnle(\<kappa>,I,J))"
  sorry

end (* M_master *)

locale M_master_sub = M_master + N:M_master N for N +
  assumes
    M_imp_N:"M(x) \<Longrightarrow> N(x)"
begin

lemma Aleph_rel_le_Aleph_rel: "Ord(\<alpha>) \<Longrightarrow> M(\<alpha>) \<Longrightarrow> \<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup> \<le> \<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>N\<^esup>"
  sorry

lemma cardinal_rel_le_cardinal_rel: "|X|\<^bsup>M\<^esup> \<le> |X|\<^bsup>N\<^esup>"
  sorry

end (* M_master_sub *)

sublocale M_master_sub \<subseteq> M_N_Perm
  using M_imp_N by unfold_locales

sublocale M_ZF_trans \<subseteq> M_master "##M"
  sorry

context M_ctm
begin

\<comment> \<open>FIXME: using notation as if \<^term>\<open>Add_subs\<close> were used\<close>
lemma ccc_Add_subs_Aleph_2: "ccc\<^bsup>M\<^esup>(Fn(\<omega>,\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>,2),Fnle(\<omega>,\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>,2))"
  sorry

end (* M_ctm *)

context G_generic begin

context
  includes G_generic_lemmas
begin

lemma ccc_preserves_Aleph_1:
  assumes "ccc\<^bsup>M\<^esup>(P,leq)"
  shows "Card\<^bsup>M[G]\<^esup>(\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>)"
  using Card_rel_Aleph_rel
  sorry

end (* G_generic_lemmas *)

end (* G_generic *)

context M_ctm
begin

abbreviation
  Add :: "i" where
  "Add \<equiv> Add_subs(\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>,\<omega>)"

end (* M_ctm *)

locale add_generic = G_generic "Fn(\<omega>, \<aleph>\<^bsub>2\<^esub>\<^bsup>##M\<^esup> \<times> \<omega>, 2)" "Fnle(\<omega>, \<aleph>\<^bsub>2\<^esub>\<^bsup>##M\<^esup> \<times> \<omega>, 2)" 0

\<comment> \<open>FIXME: all the unfoldings of @{thm Add_subs_def}\<close>
sublocale add_generic \<subseteq> ext:M_ZF_trans "M\<^bsup>Add\<^esup>[G]"
  using Transset_MG generic pairing_in_MG
    Union_MG extensionality_in_MG power_in_MG
    foundation_in_MG strong_replacement_in_MG
    separation_in_MG infinity_in_MG
  unfolding Add_subs_def
  by unfold_locales

sublocale add_generic \<subseteq> M_master_sub "##M" "##(M\<^bsup>Add\<^esup>[G])"
  using M_subset_MG[OF one_in_G] generic
  unfolding Add_subs_def
  by unfold_locales auto

context add_generic
begin

abbreviation
  f_G :: "i" (\<open>f\<^bsub>G\<^esub>\<close>) where
  "f\<^bsub>G\<^esub> \<equiv> \<Union>G"

definition
  h_G :: "i" (\<open>h\<^bsub>G\<^esub>\<close>) where
  "h\<^bsub>G\<^esub> \<equiv> \<lambda>\<alpha>\<in>\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>. \<lambda>n\<in>\<omega>. f\<^bsub>G\<^esub>`<\<alpha>,n>"

lemma Add_subs_preserves_Aleph_1:  "Card\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>(\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>)"
  using ccc_preserves_Aleph_1 ccc_Add_subs_Aleph_2
  by (auto simp add: Add_subs_def)

lemma Aleph_rel_MG_eq_Aleph_rel_M: "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup> = \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
proof -
  have "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<le> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>"
    using Aleph_rel_le_Aleph_rel by simp
  moreover
  have "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup> \<le> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
    using Add_subs_preserves_Aleph_1[THEN ext.csucc_rel_le, of \<omega>]
      nat_lt_Aleph_rel1 ext.Aleph_rel_succ ext.Aleph_rel_zero_eq_nat
    by simp
  ultimately
  show ?thesis using le_anti_sym by auto
qed

lemma "f\<^bsub>G\<^esub> : \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega> \<rightarrow> 2"
  sorry

lemma h_G_in_MG[simp]: "h\<^bsub>G\<^esub> \<in> M\<^bsup>Add\<^esup>[G]"
  sorry

lemma h_G_inj_Aleph_rel2_reals:"h\<^bsub>G\<^esub> \<in> inj\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>(\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>, \<omega> \<rightarrow>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup> 2)"
  sorry

lemma Aleph2_submodel_le_continuum_rel:
  includes G_generic_lemmas
  shows "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<le> (2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>\<^esup>)\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>"
proof -
  have "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<in> M\<^bsup>Add\<^esup>[G]" "Ord(\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>)"
    using Card_rel_Aleph_rel[THEN Card_rel_is_Ord, of 2]
      Aleph_rel2_closed
    unfolding Add_subs_def
    by auto
  moreover from this
  have "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>  \<lesssim>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup> \<omega> \<rightarrow>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup> 2"
    using ext.def_lepoll_rel[of "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>" "\<omega> \<rightarrow>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup> 2",
        OF _ ext.function_space_rel_closed]
      h_G_inj_Aleph_rel2_reals h_G_in_MG ext.nat_into_M ext.M_nat
    by auto
  ultimately
  have "|\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>|\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup> \<le> (2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>\<^esup>)\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>"
    using ext.lepoll_rel_imp_Card_rel_le[of "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>" "\<omega> \<rightarrow>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup> 2",
        OF _ _ ext.function_space_rel_closed] ext.nat_into_M ext.M_nat
      ext.Aleph_rel_zero_eq_nat
    unfolding def_cexp_rel by simp
  moreover
  have "|\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>|\<^bsup>M\<^esup> \<le> |\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>|\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>"
    using cardinal_rel_le_cardinal_rel .
  moreover
  have "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> = |\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>|\<^bsup>M\<^esup>"
    using Card_rel_cardinal_rel_eq[OF _ Aleph_rel2_closed] by simp
  ultimately
  show ?thesis using le_trans by simp
qed

lemma Aleph_rel_lt_continuum_rel: "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup> < (2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>\<^esup>)\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>"
  using Aleph2_submodel_le_continuum_rel
    Aleph_rel_increasing[of 1 2] Aleph_rel_MG_eq_Aleph_rel_M
    le_trans by auto

corollary not_CH: "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup> \<noteq> (2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>\<^esup>)\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>"
  using Aleph_rel_lt_continuum_rel by auto

end (* add_generic *)

notepad
begin
  fix M
  assume
    "M \<approx> \<omega>" "Transset(M)" "M \<Turnstile> ZF"
  from \<open>M \<Turnstile> ZF\<close>
  interpret M_ZF M
    using M_ZF_iff_M_satT
    by simp
  from \<open>Transset(M)\<close>
  interpret M_ZF_trans M
    using M_ZF_iff_M_satT
    by unfold_locales
  from \<open>M \<approx> \<omega>\<close>
  obtain enum where "enum \<in> bij(\<omega>,M)"
    using eqpoll_sym unfolding eqpoll_def by blast
  then
  interpret M_ctm M enum by unfold_locales
  interpret forcing_data "Fn(\<omega>,\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>,2)" "Fnle(\<omega>,\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>,2)" 0 M enum
  proof -
    interpret cohen_data \<omega> "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>" 2 by unfold_locales auto
    show "forcing_data(Fn(\<omega>, \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>, 2), Fnle(\<omega>, \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>, 2), 0, M, enum)"
      using nat_into_M[of 2] M_nat
        Fn_nat_closed[OF cartprod_closed, OF Aleph_rel_closed, of 2 \<omega> 2]
        Fnle_closed[OF _ cartprod_closed, OF _ Aleph_rel_closed, of  \<omega> 2 \<omega> 2]
      by (unfold_locales, simp_all)
  qed
  obtain G where "M_generic(G)"
    using generic_filter_existence[OF one_in_P]
    by auto
  then
  interpret add_generic M enum G by unfold_locales
  have "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup> \<noteq> (2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>\<^esup>)\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>"
    using not_CH .

end (* notepad *)

end