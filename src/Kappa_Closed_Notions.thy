theory Kappa_Closed_Notions
  imports
    Not_CH
    Pointed_DC_Relative
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

rel_closed for "mono_seqspace"
  sorry

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

lemma (in M_ZF_library) mono_seqspace_relI[intro!]:
  assumes "f: A\<rightarrow>\<^bsup>M\<^esup> P" "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> x<y \<Longrightarrow> \<langle>f`x, f`y\<rangle> \<in> leq"
    "Ord(A)" "M(A)" "M(P)" "M(leq)"
  shows  "f: A \<^sub><\<rightarrow>\<^bsup>M\<^esup> (P,leq)"
  sorry

lemma (in M_ZF_library) mono_seqspace_rel_char:
  assumes "M(A)" "M(P)" "M(leq)"
  shows "A \<^sub><\<rightarrow>\<^bsup>M\<^esup> (P,leq) = {f\<in>A \<^sub><\<rightarrow> (P,leq). M(f)}"
  using assms mono_map_rel_char 
  unfolding mono_seqspace_def mono_seqspace_rel_def by simp

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

\<comment> \<open>Kunen IV.7.13, with “$\kappa$” in place of “$\lambda$”\<close>
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

context M_ZF_library
begin

(* Is this true? *)
lemma kappa_closed_abs:
  assumes "M(\<kappa>)" "M(P)" "M(leq)"
  shows "\<kappa>-closed\<^bsup>M\<^esup>(P,leq) \<longleftrightarrow> \<kappa>-closed(P,leq)"
  using assms transM[OF ltD, of _ \<kappa>]
    mono_seqspace_char[of _ P leq]
  unfolding kappa_closed_rel_def kappa_closed_def
  oops

end (* forcing_data *)

context G_generic_AC begin

context
  includes G_generic_lemmas
begin

\<comment> \<open>Kunen IV.7.15, only for sequences\<close>
lemma kappa_closed_imp_no_new_sequences:
  (* notes le_trans[trans] *)
  assumes "\<kappa>-closed\<^bsup>M\<^esup>(P,leq)" "f : \<delta> \<rightarrow> B" "\<delta><\<kappa>" "f\<in>M[G]"
    "\<kappa>\<in>M" "B\<in>M"
  shows "f\<in>M"
  oops

(* MOVE THIS to an appropriate place *)
\<comment> \<open>Kunen IV.6.1\<close>
lemma local_maximal_principle:
  assumes "r \<tturnstile> (\<cdot>\<exists>\<cdot>\<cdot>0\<in>1\<cdot> \<and> \<phi>\<cdot>\<cdot>) [\<pi>]" "r\<in>P" "\<phi>\<in>formula" "\<pi> \<in> M"
  shows "\<exists>q\<in>P. \<exists>\<sigma> \<in> domain(\<pi>).  q \<preceq> r \<and> q \<tturnstile> \<cdot>\<cdot>0\<in>1\<cdot> \<and> \<phi>\<cdot> [\<sigma>,\<pi>]"
  sorry

lemma forcing_a_value:
  assumes "p \<tturnstile> \<cdot>0:1\<rightarrow>2\<cdot> [f_dot, A\<^sup>v, B\<^sup>v]" "a \<in> A"
    "q \<preceq> p" "q \<in> P" "p\<in>P" "f_dot \<in> M" "A\<in>M" "B\<in>M"
  shows "\<exists>d\<in>P. \<exists>b\<in>B. d \<preceq> q \<and> d \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, a\<^sup>v, b\<^sup>v]"
    \<comment> \<open>Old neater version, but harder to use
    (without the assumptions on \<^term>\<open>q\<close>):\<close>
    (* "dense_below({q \<in> P. \<exists>b\<in>B. q \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, a\<^sup>v, b\<^sup>v]}, p)" *)
proof -
  from assms
  have "q \<tturnstile> \<cdot>0:1\<rightarrow>2\<cdot> [f_dot, A\<^sup>v, B\<^sup>v]"
    using strengthening_lemma[of p "\<cdot>0:1\<rightarrow>2\<cdot>" q "[f_dot, A\<^sup>v, B\<^sup>v]"]
      typed_function_type arity_typed_function_fm
    by (auto simp: union_abs2 union_abs1)
  {
  }
  obtain d b where "d \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, a\<^sup>v, b\<^sup>v]" "d\<preceq>q" "d\<in>P" "b\<in>B"
    sorry
  then
  show ?thesis by auto
qed

\<comment> \<open>Kunen IV.7.15, only for countable sequences\<close>
lemma succ_omega_closed_imp_no_new_nat_sequences:
  (* notes le_trans[trans] *)
  notes monseq_closed =
    mono_seqspace_rel_closed[of "##M" \<omega> _ "converse(leq)", simplified, OF P_in_M]
  assumes "succ(\<omega>)-closed\<^bsup>M\<^esup>(P,leq)" "f : \<omega> \<rightarrow> B" "f\<in>M[G]"
    "B\<in>M"
  shows "f\<in>M"
    (* (* Proof using the general lemma: *)
  using assms nat_lt_Aleph_rel1 kappa_closed_imp_no_new_sequences
    Aleph_rel_closed[of 1] by simp *)
proof -
(*
proof (rule ccontr)
  note \<open>f\<in>M[G]\<close>
  with assms
  obtain f_dot where "f = val(P,G,f_dot)" "f_dot\<in>M" using GenExtD by force
  moreover
  note \<open>B \<in> M\<close>
  moreover
  assume "f \<notin> M"
  moreover from calculation
  have "f \<notin> \<omega> \<rightarrow>\<^bsup>M\<^esup> B" using function_space_rel_char by simp
  ultimately
  obtain p where "p \<tturnstile> \<cdot>\<cdot>0:1\<rightarrow>2\<cdot> \<and> \<cdot>\<not>\<cdot>0 \<in> 3\<cdot>\<cdot>\<cdot> [f_dot, \<omega>\<^sup>v, B\<^sup>v, (\<omega> \<rightarrow>\<^bsup>M\<^esup> B)\<^sup>v]" "p\<in>G" "p\<in>M"
    using transitivity[OF M_genericD P_in_M]
      generic truth_lemma[of "\<cdot>\<cdot>0:1\<rightarrow>2\<cdot> \<and> \<cdot>\<not>\<cdot>0 \<in> 3\<cdot>\<cdot>\<cdot>" G "[f_dot, \<omega>\<^sup>v, B\<^sup>v, (\<omega> \<rightarrow>\<^bsup>M\<^esup> B)\<^sup>v]"]
    by (auto simp add:ord_simp_union arity_typed_function_fm
        typed_function_type And_type)
 *)
  from \<open>f\<in>M[G]\<close>
  obtain f_dot where "f = val(P,G,f_dot)" "f_dot\<in>M" using GenExtD by force
  with assms
  obtain p where "p \<tturnstile> \<cdot>0:1\<rightarrow>2\<cdot> [f_dot, \<omega>\<^sup>v, B\<^sup>v]" "p\<in>G" "p\<in>M"
    using transitivity[OF M_genericD P_in_M]
      generic truth_lemma[of "\<cdot>0:1\<rightarrow>2\<cdot>" G "[f_dot, \<omega>\<^sup>v, B\<^sup>v]"]
    by (auto simp add:ord_simp_union arity_typed_function_fm
        typed_function_type)
  let ?subp="{q\<in>P. q \<preceq> p}"
  from \<open>p\<in>G\<close>
  have "?subp \<in> M"
    using first_section_closed[of P p "converse(leq)"] leq_in_M
      G_subset_M[OF generic] by auto
  define S where "S \<equiv> \<lambda>n\<in>nat.
    {\<langle>q,r\<rangle> \<in> ?subp\<times>?subp. r \<preceq> q \<and> (\<exists>b\<in>B. r \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, pred(n)\<^sup>v, b\<^sup>v])}"
    (is "S \<equiv> \<lambda>n\<in>nat. ?Y(n)")
  \<comment> \<open>Towards proving \<^term>\<open>S\<in>M\<close>.\<close>
  have "{r \<in> ?subp. \<exists>b\<in>B. r \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, pred(n)\<^sup>v, b\<^sup>v]} \<in> M" (is "?X(n) \<in> M")
    if "n\<in>\<omega>" for n sorry
  moreover
  have "?Y(n) = (?subp \<times> ?X(n)) \<inter> converse(leq)" for n
    by (intro equalityI) auto
  moreover
  note \<open>?subp \<in> M\<close>
  ultimately
  have "n \<in> \<omega> \<Longrightarrow> ?Y(n) \<in> M" for n using nat_into_M leq_in_M by simp
  have "S \<in> M" sorry
  from \<open>p\<in>G\<close> \<open>f_dot\<in>M\<close> \<open>p \<tturnstile> \<cdot>0:1\<rightarrow>2\<cdot> [f_dot, \<omega>\<^sup>v, B\<^sup>v]\<close> \<open>p\<in>M\<close> \<open>B\<in>M\<close>
  have exr:"\<exists>r\<in>P. r \<preceq> q \<and> (\<exists>b\<in>B. r \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, pred(n)\<^sup>v, b\<^sup>v])"
    if "q \<preceq> p" "q\<in>P" "n\<in>\<omega>" for q n
    using that forcing_a_value by (auto dest:transM)
  have "\<forall>q\<in>?subp. \<forall>n\<in>\<omega>. \<exists>r\<in>?subp. \<langle>q,r\<rangle> \<in> S`n"
  proof -
    {
      fix q n
      assume "q \<in> ?subp" "n\<in>\<omega>"
      moreover from this
      have "q \<preceq> p" "q \<in> P" by simp_all
      moreover from calculation and exr
      obtain r where "r \<preceq> q" "\<exists>b\<in>B. r \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, pred(n)\<^sup>v, b\<^sup>v]" "r\<in>P"
        by blast
      moreover from calculation \<open>q \<preceq> p\<close> \<open>p \<in> G\<close>
      have "r \<preceq> p"
        using leq_transD[of r q p] by auto
      ultimately
      have "\<exists>r\<in>?subp. r \<preceq> q \<and> (\<exists>b\<in>B. r \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, pred(n)\<^sup>v, b\<^sup>v])"
        by auto
    }
    then
    show ?thesis
      unfolding S_def by simp
  qed
  with \<open>p\<in>G\<close> \<open>?subp \<in> M\<close> \<open>S \<in> M\<close>
  obtain g where "g \<in> \<omega> \<rightarrow>\<^bsup>M\<^esup> ?subp" "g`0 = p" "\<forall>n \<in> nat. \<langle>g`n,g`succ(n)\<rangle>\<in>S`succ(n)"
    using sequence_DC[simplified] refl_leq[of p] by blast
  moreover from this and \<open>?subp \<in> M\<close>
  have "g : \<omega> \<rightarrow> P" "g \<in> M" 
    using fun_weaken_type[of g \<omega> ?subp P] function_space_rel_char by auto
  ultimately
  have "g : \<omega> \<^sub><\<rightarrow>\<^bsup>M\<^esup> (P,converse(leq))"
    using decr_succ_decr[of g] leq_preord leq_in_M P_in_M
    unfolding S_def by (auto simp:absolut intro:leI)
  moreover from \<open>succ(\<omega>)-closed\<^bsup>M\<^esup>(P,leq)\<close> and this
  have "\<exists>q\<in>M. q \<in> P \<and> (\<forall>\<alpha>\<in>M. \<alpha> \<in> \<omega> \<longrightarrow> q \<preceq> g ` \<alpha>)"
    using transM[simplified, OF _ monseq_closed, of g] leq_in_M
    unfolding kappa_closed_rel_def
    by auto
  ultimately
  obtain r where "r\<in>P" "r\<in>M" "\<forall>n\<in>\<omega>. r \<preceq> g`n"
    using nat_into_M by auto
  with \<open>g`0 = p\<close>
  have "r \<preceq> p" by blast
  let ?h="{\<langle>n,b\<rangle> \<in> \<omega> \<times> B. r \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, n\<^sup>v, b\<^sup>v]}"
  have "function(?h)"
  proof (rule_tac functionI, rule_tac ccontr, auto simp del: app_Cons)
    fix n b b'
    assume "n \<in> \<omega>" "b \<noteq> b'" "b \<in> B" "b' \<in> B"
    moreover
    assume "r \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, n\<^sup>v, b\<^sup>v]" "r \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, n\<^sup>v, b'\<^sup>v]"
    moreover
    note \<open>r \<in> P\<close>
    moreover from this
    have "\<not> r \<bottom> r" by (auto intro!:refl_leq)
    moreover
    note \<open>f_dot\<in>M\<close> \<open>B\<in>M\<close>
    ultimately
    show False
      using forces_neq_apply_imp_incompatible[of r f_dot "n\<^sup>v" b r b']
        transM[of _ B] by (auto dest:transM)
  qed
  moreover
  have "range(?h) \<subseteq> B" by auto
  moreover
  have "domain(?h) = \<omega>"
  proof -
    {
      fix n
      assume "n \<in> \<omega>"
      moreover from this and \<open>\<forall>n \<in> nat. \<langle>g`n,g`succ(n)\<rangle>\<in>S`succ(n)\<close>
      obtain b where "g`(succ(n)) \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, n\<^sup>v, b\<^sup>v]" "b\<in>B"
        unfolding S_def by auto
      moreover from \<open>B\<in>M\<close> and calculation
      have "b \<in> M" "n \<in> M" by (auto dest:transM)
      moreover
      note \<open>g : \<omega> \<rightarrow> P\<close> \<open>\<forall>n\<in>\<omega>. r \<preceq> g`n\<close> \<open>r\<in>P\<close> \<open>f_dot\<in>M\<close>
      moreover from calculation
      have "r \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, n\<^sup>v, b\<^sup>v]"
        using fun_apply_type arity_fun_apply_fm
          strengthening_lemma[of "g`succ(n)" "\<cdot>0`1 is 2\<cdot>" r "[f_dot, n\<^sup>v, b\<^sup>v]"]
        by (simp add: union_abs2 union_abs1)
      ultimately
      have "\<exists>b\<in>B. r \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, n\<^sup>v, b\<^sup>v]" by auto
    }
    then
    show ?thesis by force
  qed
  moreover
  have "relation(?h)" unfolding relation_def by simp
  moreover
  have "?h \<in> M" sorry
  moreover
  note \<open>B \<in> M\<close>
  ultimately
  have "?h: \<omega> \<rightarrow>\<^bsup>M\<^esup> B"
    using function_imp_Pi[THEN fun_weaken_type[of ?h _ "range(?h)" B]]
    function_space_rel_char by simp
  moreover
  have "?h`n = f`n" if "n\<in>\<omega>" for n sorry
  with calculation and \<open>f : \<omega> \<rightarrow> B\<close> \<open>B\<in>M\<close>
  have "?h = f"
    using function_space_rel_char
    by (rule_tac fun_extension[of ?h \<omega> "\<lambda>_.B" f]) auto
  moreover
  note \<open>B \<in> M\<close>
  ultimately
  show ?thesis using function_space_rel_char by (auto dest:transM)
(*
  note \<open>B \<in> M\<close> \<open>f \<notin> M\<close>
  ultimately
  show ?thesis using function_space_rel_char by (auto dest:transM)
 *)
qed

declare mono_seqspace_rel_closed[rule del]
  \<comment> \<open>Mysteriously breaks the end of the next proof\<close>

lemma succ_omega_closed_imp_no_new_reals:
  assumes "succ(\<omega>)-closed\<^bsup>M\<^esup>(P,leq)"
  shows "\<omega> \<rightarrow>\<^bsup>M\<^esup> 2 = \<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2"
proof -
  from assms
  have "\<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2 \<subseteq> \<omega> \<rightarrow>\<^bsup>M\<^esup> 2"
    using succ_omega_closed_imp_no_new_nat_sequences function_space_rel_char
      ext.function_space_rel_char Aleph_rel_succ Aleph_rel_zero
      nat_into_M[of 2] csucc_rel_closed
    by auto
  then
  show ?thesis
    using function_space_rel_transfer ext.nat_into_M[of 2] by force
qed

lemma succ_omega_closed_imp_Aleph_1_preserved:
  assumes "succ(\<omega>)-closed\<^bsup>M\<^esup>(P,leq)"
  shows "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> = \<aleph>\<^bsub>1\<^esub>\<^bsup>M[G]\<^esup>"
proof -
  have "\<aleph>\<^bsub>1\<^esub>\<^bsup>M[G]\<^esup> \<le> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
  proof (rule ccontr)
    assume "\<not> \<aleph>\<^bsub>1\<^esub>\<^bsup>M[G]\<^esup> \<le> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
    then
    have "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> < \<aleph>\<^bsub>1\<^esub>\<^bsup>M[G]\<^esup>"
      \<comment> \<open>Ridiculously complicated proof\<close>
      using Card_rel_Aleph_rel[THEN Card_rel_is_Ord, of 1]
        ext.Card_rel_Aleph_rel[THEN ext.Card_rel_is_Ord, of 1]
        Aleph_rel_closed ext.Aleph_rel_closed not_le_iff_lt[THEN iffD1]
      by auto
    then
    have "|\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>|\<^bsup>M[G]\<^esup> \<le> \<omega>"
      using ext.Card_rel_lt_csucc_rel_iff ext.Aleph_rel_zero ext.Aleph_rel_succ
        ext.Card_rel_nat Aleph_rel_closed
      by (auto intro!:ext.lt_csucc_rel_iff[THEN iffD1]
          intro:Card_rel_Aleph_rel[THEN Card_rel_is_Ord, of 1])
    then
    obtain f where "f \<in> inj(\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>,\<omega>)" "f \<in> M[G]"
      using ext.countable_rel_iff_cardinal_rel_le_nat[of "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>", THEN iffD2]
        Aleph_rel_closed
      unfolding countable_rel_def lepoll_rel_def
      by auto
    then
    obtain g where "g \<in> surj\<^bsup>M[G]\<^esup>(\<omega>, \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>)"
      using ext.inj_rel_imp_surj_rel[of f _ \<omega>, OF _ zero_lt_Aleph_rel1[THEN ltD]]
        Aleph_rel_closed[of 1]
      by auto
    moreover from this
    have "g : \<omega> \<rightarrow> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "g \<in> M[G]"
      using ext.surj_rel_char Aleph_rel_closed[of 1] surj_is_fun by simp_all
    moreover
    note \<open>succ(\<omega>)-closed\<^bsup>M\<^esup>(P,leq)\<close>
    ultimately
    have "g \<in> surj\<^bsup>M\<^esup>(\<omega>, \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>)" "g \<in> M"
      using succ_omega_closed_imp_no_new_nat_sequences
        Aleph_rel_closed[of 1]
        mem_surj_abs ext.mem_surj_abs by simp_all
    then
    show False
      using surj_rel_implies_cardinal_rel_le[of g \<omega> "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"]
        Aleph_rel_closed Card_rel_nat[THEN Card_rel_cardinal_rel_eq]
        not_le_iff_lt[THEN iffD2, OF _ _ nat_lt_Aleph_rel1]
        Card_rel_Aleph_rel[THEN Card_rel_is_Ord, of 1]
      by simp
  qed
  then
  show ?thesis
    using Aleph_rel_le_Aleph_rel
    by (rule_tac le_anti_sym) simp
qed

end (* includes G_generic_lemmas *)

end (* G_generic_AC *)

end