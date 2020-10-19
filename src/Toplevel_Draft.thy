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
  def_cexp_rel:"cexp_rel(M,x,y) \<equiv> |x\<rightarrow>\<^bsup>M\<^esup> y|\<^bsup>M\<^esup>"

abbreviation
  cexp_r :: "[i,i,i\<Rightarrow>o] \<Rightarrow> i"  (\<open>'(_\<^bsup>\<up>_\<^esup>')\<^bsup>_\<^esup>\<close>) where
  "cexp_r(x,y,M) \<equiv> cexp_rel(M,x,y)"

locale M_master = M_cardinal_AC 
begin

lemma FiniteFun_closed[intro,simp]:
  assumes "M(A)" "M(B)" shows "M(A-||>B)"
  sorry

lemma Fn_nat_closed[intro,simp]:
  assumes "M(A)" "M(B)" shows "M(Fn(\<omega>,A,B))"
  using assms Fn_nat_eq_FiniteFun
  by simp

lemma Aleph_rel_closed[intro,simp]: "M(a) \<Longrightarrow> M(Aleph_rel(M,a))"
  sorry

lemma Card_rel_Aleph_rel: "Ord(\<alpha>) \<Longrightarrow> Card_rel(M,Aleph_rel(M,\<alpha>))" sorry

lemma Fnle_closed[intro,simp]:
  assumes "M(\<kappa>)" "M(I)" "M(J)"
  shows "M(Fnle(\<kappa>,I,J))"
  sorry

end (* M_master *)

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
  shows "Card\<^bsup>M[G]\<^esup>(Aleph_rel(##M,1))"
  using Card_rel_Aleph_rel
  sorry

lemma ccc_preserves_Aleph_2:
  assumes "ccc\<^bsup>M\<^esup>(P,leq)"
  shows "Card\<^bsup>M[G]\<^esup>(Aleph_rel(##M,2))"
  sorry

end (* G_generic_lemmas *)

end (* G_generic *)

context M_ctm
begin

abbreviation
  Add :: "i" where
  "Add \<equiv> Add_subs(\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>,\<omega>)"

interpretation add:forcing_data "Fn(\<omega>,\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>,2)" "Fnle(\<omega>,\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>,2)" 0
proof -
  interpret cohen_data \<omega> "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>" 2 by unfold_locales auto
  show "forcing_data(Fn(\<omega>, \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>, 2), Fnle(\<omega>, \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>, 2), 0, M, enum)"
    using nat_into_M[of 2] M_nat
    Fn_nat_closed[OF cartprod_closed, OF Aleph_rel_closed, of 2 \<omega> 2]
    Fnle_closed[OF _ cartprod_closed, OF _ Aleph_rel_closed, of  \<omega> 2 \<omega> 2]
    by (unfold_locales, simp_all)
qed

lemma Add_subs_preserves_Aleph_1:
  assumes "add.M_generic(G)"
  shows "Card\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>(\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>)"
proof -
  from \<open>add.M_generic(G)\<close>
  interpret G_generic "Fn(\<omega>,\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>,2)" "Fnle(\<omega>,\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>\<times>\<omega>,2)" 0
    using nat_into_M[of 2] M_nat
    Fn_nat_closed[OF cartprod_closed, OF Aleph_rel_closed, of 2 \<omega> 2]
    Fnle_closed[OF _ cartprod_closed, OF _ Aleph_rel_closed, of  \<omega> 2 \<omega> 2]
    by (unfold_locales) (simp_all)
  show ?thesis
  using ccc_preserves_Aleph_1 ccc_Add_subs_Aleph_2
  by (auto simp add: Add_subs_def)
qed

lemma Aleph_rel_MG_eq_Aleph_rel_M:
  shows "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^bsup>Add\<^esup>[G]\<^esup>= \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
  sorry


end (* M_ctm *)

end