theory Kappa_Closed_Notions
  imports
    Cardinal_Preservation
    ZF_Trans_Interpretations
begin

definition
  lerel :: "i\<Rightarrow>i" where
  "lerel(\<alpha>) \<equiv> Memrel(\<alpha>) \<union> id(\<alpha>)"

lemma lerelI[intro!]: "x\<le>y \<Longrightarrow> y\<in>\<alpha> \<Longrightarrow> Ord(\<alpha>) \<Longrightarrow> \<langle>x,y\<rangle> \<in> lerel(\<alpha>)"
  using Ord_trans[of x y \<alpha>] ltD unfolding lerel_def by auto

lemma lerelD[dest]: "\<langle>x,y\<rangle> \<in> lerel(\<alpha>) \<Longrightarrow> Ord(\<alpha>) \<Longrightarrow> x\<le>y"
  using ltI[THEN leI] Ord_in_Ord unfolding lerel_def by auto

definition
  mono_seqspace :: "[i,i,i] \<Rightarrow> i" (\<open>_ \<^sub><\<rightarrow> '(_,_')\<close> [61] 60) where
  "\<alpha> \<^sub><\<rightarrow> (P,leq) \<equiv> mono_map(\<alpha>,Memrel(\<alpha>),P,leq)"

relativize functional "mono_seqspace" "mono_seqspace_rel"
relationalize "mono_seqspace_rel" "is_mono_seqspace"
synthesize "is_mono_seqspace" from_definition assuming "nonempty"

abbreviation
  mono_seqspace_r (\<open>_ \<^sub><\<rightarrow>\<^bsup>_\<^esup> '(_,_')\<close> [61] 60) where
  "\<alpha> \<^sub><\<rightarrow>\<^bsup>M\<^esup> (P,leq) \<equiv> mono_seqspace_rel(M,\<alpha>,P,leq)"

abbreviation
  mono_seqspace_r_set (\<open>_ \<^sub><\<rightarrow>\<^bsup>_\<^esup> '(_,_')\<close> [61] 60) where
  "\<alpha> \<^sub><\<rightarrow>\<^bsup>M\<^esup> (P,leq) \<equiv> mono_seqspace_rel(##M,\<alpha>,P,leq)"

lemma mono_seqspaceI[intro!]:
  includes mono_map_rules
  assumes "f: A\<rightarrow>P" "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> x<y \<Longrightarrow> \<langle>f`x, f`y\<rangle> \<in> leq" "Ord(A)"
  shows  "f: A \<^sub><\<rightarrow> (P,leq)"
  using ltI[OF _ Ord_in_Ord[of A], THEN [3] assms(2)] assms(1,3)
  unfolding mono_seqspace_def by auto

lemma mono_seqspace_is_fun[dest]:
  includes mono_map_rules
  shows "j: A \<^sub><\<rightarrow> (P,leq) \<Longrightarrow> j: A\<rightarrow> P"
  unfolding mono_seqspace_def by auto

lemma mono_map_lt_le_is_mono[dest]:
  includes mono_map_rules
  assumes "j: A \<^sub><\<rightarrow> (P,leq)" "a\<in>A" "c\<in>A" "a\<le>c" "Ord(A)" "refl(P,leq)"
  shows "\<langle>j`a,j`c\<rangle> \<in> leq"
  using assms mono_map_increasing unfolding mono_seqspace_def refl_def
  by (cases "a=c") (auto dest:ltD)

lemma (in M_ZF_library) mem_mono_seqspace_abs[absolut]:
  assumes "M(f)" "M(A)" "M(P)" "M(leq)"
  shows  "f:A \<^sub><\<rightarrow>\<^bsup>M\<^esup> (P,leq) \<longleftrightarrow>  f: A \<^sub><\<rightarrow> (P,leq)"
  using assms mono_map_rel_char unfolding mono_seqspace_def mono_seqspace_rel_def
  by (simp)

lemma (in M_ZF_library) mono_seqspace_char:
  assumes "M(A)" "M(P)" "M(leq)"
  shows  "A \<^sub><\<rightarrow>\<^bsup>M\<^esup> (P,leq) = {f: A \<^sub><\<rightarrow> (P,leq) . M(f)}"
  using assms mono_map_rel_char unfolding mono_seqspace_def mono_seqspace_rel_def
  by (simp)

definition
  mono_map_lt_le :: "[i,i] \<Rightarrow> i" (infixr \<open>\<^sub><\<rightarrow>\<^sub>\<le>\<close> 60) where
  "\<alpha> \<^sub><\<rightarrow>\<^sub>\<le> \<beta> \<equiv> \<alpha> \<^sub><\<rightarrow> (\<beta>,lerel(\<beta>))"

lemma mono_map_lt_leI[intro!]:
  includes mono_map_rules
  assumes "f: A\<rightarrow>B" "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> x<y \<Longrightarrow> f`x \<le> f`y" "Ord(A)" "Ord(B)"
  shows  "f: A \<^sub><\<rightarrow>\<^sub>\<le> B"
  using assms
  unfolding mono_map_lt_le_def by auto

\<comment> \<open>Kunen IV.7.13, with “$\kappa$” in place of ”$\lambda$”\<close>
definition
  kappa_closed :: "[i,i,i] \<Rightarrow> o" (\<open>_-closed'(_,_')\<close>) where
  "\<kappa>-closed(P,leq) \<equiv> \<forall>\<delta>. \<delta><\<kappa> \<longrightarrow> (\<forall>f\<in>\<delta> \<^sub><\<rightarrow> (P,converse(leq)). \<exists>q\<in>P. \<forall>\<alpha>\<in>\<delta>. \<langle>q,f`\<alpha>\<rangle>\<in>leq)"

relativize functional "kappa_closed" "kappa_closed_rel"
relationalize "kappa_closed_rel" "is_kappa_closed"
synthesize "is_kappa_closed" from_definition assuming "nonempty"

abbreviation
  kappa_closed_r (\<open>_-closed\<^bsup>_\<^esup>'(_,_')\<close> [61] 60) where
  "\<kappa>-closed\<^bsup>M\<^esup>(P,leq) \<equiv> kappa_closed_rel(M,\<kappa>,P,leq)"

abbreviation
  kappa_closed_r_set (\<open>_-closed\<^bsup>_\<^esup>'(_,_')\<close> [61] 60) where
  "\<kappa>-closed\<^bsup>M\<^esup>(P,leq) \<equiv> kappa_closed_rel(##M,\<kappa>,P,leq)"

sublocale forcing_data \<subseteq> M_ZF_library "##M"
  \<comment> \<open>Wasn't this already done??\<close>
  by unfold_locales
  

context forcing_data
begin

lemma kappa_closed_abs: 
  assumes "\<kappa>\<in>M" 
  shows "\<kappa>-closed\<^bsup>M\<^esup>(P,leq) \<longleftrightarrow> \<kappa>-closed(P,leq)"
  using assms P_in_M leq_in_M transM[OF ltD, of _ \<kappa>]
    mono_seqspace_char[of _ P leq]
  unfolding kappa_closed_rel_def kappa_closed_def
  apply (auto simp add:absolut)
  sorry

end (* forcing_data *)

context G_generic_AC begin

context
  includes G_generic_lemmas
begin

\<comment> \<open>Kunen IV.7.14, only for \<^term>\<open>\<aleph>\<^bsub>1\<^esub>\<close>\<close>
(* lemma kappa_closed_Fn: *)

\<comment> \<open>Kunen IV.7.15, only for sequences\<close>
lemma kappa_closed_imp_no_new_sequences:
  (* notes le_trans[trans] *)
  assumes "\<kappa>-closed\<^bsup>M\<^esup>(P,leq)" "f : \<delta> \<rightarrow> B" "\<delta><\<kappa>" "\<kappa>\<in>M" "B\<in>M" "f\<in>M[G]"
  shows "f\<in>M"
  sorry

end (* includes G_generic_lemmas *)

end (* G_generic *)

end