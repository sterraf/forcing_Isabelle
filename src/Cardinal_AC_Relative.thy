section\<open>Relative, Cardinal Arithmetic Using AC\<close>

theory Cardinal_AC_Relative 
  imports 
    Interface
    CardinalArith_Relative 

begin

\<comment> \<open>MOVE THIS to an appropriate place. Now it is repeated in
   \<^file>\<open>Forcing_Main.thy\<close>. But consider that ported versions follow,
   and hence perhaps we should only have the relative version.\<close>
definition
  minimum :: "i \<Rightarrow> i \<Rightarrow> i" where
  "minimum(r,B) \<equiv> THE b. first(b,B,r)"

lemma minimum_in: "\<lbrakk> well_ord(A,r); B\<subseteq>A; B\<noteq>0 \<rbrakk> \<Longrightarrow> minimum(r,B) \<in> B"
  using the_first_in unfolding minimum_def by simp

lemma well_ord_surj_imp_lepoll:
  assumes "well_ord(A,r)" "h \<in> surj(A,B)"
  shows "B \<lesssim> A"
proof -
  let ?f="\<lambda>b\<in>B. minimum(r, {a\<in>A. h`a=b})"
  have "minimum(r, {a \<in> A . h ` a = b}) \<in> {a\<in>A. h`a=b}" if "b\<in>B" for b
  proof -
    from \<open>h \<in> surj(A,B)\<close> that
    have "{a\<in>A. h`a=b} \<noteq> 0"
      unfolding surj_def by blast
    with \<open>well_ord(A,r)\<close>
    show "minimum(r,{a\<in>A. h`a=b}) \<in> {a\<in>A. h`a=b}"
      using minimum_in by blast
  qed
  moreover from this
  have "?f : B \<rightarrow> A"
      using lam_type[of B _ "\<lambda>_.A"] by simp
  moreover
  have "?f ` w = ?f ` x \<Longrightarrow> w = x" if "w\<in>B" "x\<in>B" for w x
  proof -
    from calculation that
    have "w = h ` minimum(r,{a\<in>A. h`a=w})"
         "x = h ` minimum(r,{a\<in>A. h`a=x})"
      by simp_all
    moreover
    assume "?f ` w = ?f ` x"
    moreover from this and that
    have "minimum(r, {a \<in> A . h ` a = w}) = minimum(r, {a \<in> A . h ` a = x})"
      unfolding minimum_def by simp_all
    moreover from calculation(1,2,4)
    show "w=x" by simp
    qed
  ultimately
  show ?thesis
  unfolding lepoll_def inj_def by blast
qed

\<comment> \<open>New result\<close>
lemma surj_imp_well_ord:
  assumes "well_ord(A,r)" "h \<in> surj(A,B)"
  shows "\<exists>s. well_ord(B,s)"
  using assms lepoll_well_ord[OF well_ord_surj_imp_lepoll]
  by force

context M_cardinal_arith
begin

lemma well_ord_surj_imp_lepoll_rel:
  assumes "well_ord(A,r)" "h \<in> surj(A,B)" and
    types:"M(A)" "M(r)" "M(h)" "M(B)"
  shows "B \<lesssim>\<^bsup>M\<^esup> A"
  sorry

lemma minimum_closed[intro,simp]:"M(A) \<Longrightarrow> M(r) \<Longrightarrow> M(minimum(A,r))"
  sorry

lemma surj_imp_well_ord_M:
  assumes wos: "well_ord(A,r)" "h \<in> surj(A,B)"
    and
    types: "M(A)" "M(r)" "M(h)" "M(B)"
  shows "\<exists>s[M]. well_ord(B,s)"
  using assms lepoll_rel_well_ord
    well_ord_surj_imp_lepoll_rel by fast

end (* M_ordertype *)

locale M_cardinal_AC = M_cardinal_arith +
  assumes
  choice_ax: "choice_ax(M)"
  and
  surj_imp_inj_replacement:
  "M(f) \<Longrightarrow> M(x) \<Longrightarrow> strong_replacement(M, \<lambda>y z. y \<in> f -`` {x} \<and> z = {\<langle>x, y\<rangle>})"
  "M(f) \<Longrightarrow> strong_replacement(M, \<lambda>x z. z = Sigfun(x, \<lambda>y. f -`` {y}))"
  "M(f) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = f -`` {x})"
  "M(f) \<Longrightarrow> M(r) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = \<langle>x, minimum(r, f -`` {x})\<rangle>)"
begin

lemma choice_ax_well_ord: "M(S) \<Longrightarrow> \<exists>r[M]. well_ord(S,r)"
  using choice_ax well_ord_Memrel[THEN surj_imp_well_ord_M]
  unfolding choice_ax_def by auto

end (* M_cardinal_AC *)

locale M_Pi_assumptions_choice = M_Pi_assumptions + M_cardinal_AC +
  assumes                         
    B_replacement: "strong_replacement(M, \<lambda>x y. y = B(x))"
    and
    \<comment> \<open>The next one should be derivable from (some variant)
        of B_replacement. Proving both instances each time seems
        inconvenient.\<close>
    minimum_replacement: "M(r) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = \<langle>x, minimum(r, B(x))\<rangle>)"
begin

lemma AC_M:
  assumes "a \<in> A" "\<And>x. x \<in> A \<Longrightarrow> \<exists>y. y \<in> B(x)"
  shows "\<exists>z[M]. z \<in> Pi\<^bsup>M\<^esup>(A, B)"
proof -
  have "M(\<Union>x\<in>A. B(x))" using assms family_union_closed Pi_assumptions B_replacement by simp
  then
  obtain r where "well_ord(\<Union>x\<in>A. B(x),r)" "M(r)"
    using choice_ax_well_ord by blast
  let ?f="\<lambda>x\<in>A. minimum(r,B(x))"
  from assms and \<open>M(r)\<close>
  have "M(?f)"
    using minimum_replacement Pi_assumptions
    by (rule_tac lam_closed) (auto)
  moreover from assms and calculation
  have "?f \<in> Pi\<^bsup>M\<^esup>(A,B)"
    using lam_type[OF minimum_in, OF \<open>well_ord(\<Union>x\<in>A. B(x),r)\<close>, of A B]
     Pi_rel_char by auto
  ultimately
  show ?thesis by blast
qed

lemma AC_Pi_rel: assumes "\<And>x. x \<in> A \<Longrightarrow> \<exists>y. y \<in> B(x)"
  shows "\<exists>z[M]. z \<in> Pi\<^bsup>M\<^esup>(A, B)"
proof (cases "A=0")
  interpret Pi0:M_Pi_assumptions_0
    using Pi_assumptions by unfold_locales auto
  case True
  then
  show ?thesis using assms by simp
next
  case False
  then
  obtain a where "a \<in> A" by auto
    \<comment> \<open>It is noteworthy that without obtaining an element of
        \<^term>\<open>A\<close>, the final step won't work\<close>
  with assms
  show ?thesis by (blast intro!: AC_M)
qed

end (* M_Pi_assumptions_choice *)


context M_cardinal_AC
begin

subsection\<open>Strengthened Forms of Existing Theorems on Cardinals\<close>

lemma cardinal_rel_eqpoll_rel: "M(A) \<Longrightarrow> |A|\<^bsup>M\<^esup> \<approx>\<^bsup>M\<^esup> A"
apply (rule choice_ax_well_ord [THEN rexE])
apply (auto intro:well_ord_cardinal_rel_eqpoll_rel)
done

lemmas cardinal_rel_idem = cardinal_rel_eqpoll_rel [THEN cardinal_rel_cong, simp]

lemma cardinal_rel_eqE: "|X|\<^bsup>M\<^esup> = |Y|\<^bsup>M\<^esup> ==> M(X) \<Longrightarrow> M(Y) \<Longrightarrow> X \<approx>\<^bsup>M\<^esup> Y"
apply (rule choice_ax_well_ord [THEN rexE], assumption)
   apply (rule choice_ax_well_ord [THEN rexE, of Y], assumption)
    apply (rule well_ord_cardinal_rel_eqE, assumption+)
done

lemma cardinal_rel_eqpoll_rel_iff: "M(X) \<Longrightarrow> M(Y) \<Longrightarrow> |X|\<^bsup>M\<^esup> = |Y|\<^bsup>M\<^esup> \<longleftrightarrow> X \<approx>\<^bsup>M\<^esup> Y"
by (blast intro: cardinal_rel_cong cardinal_rel_eqE)

lemma cardinal_rel_disjoint_Un:
     "[| |A|\<^bsup>M\<^esup>=|B|\<^bsup>M\<^esup>;  |C|\<^bsup>M\<^esup>=|D|\<^bsup>M\<^esup>;  A \<inter> C = 0;  B \<inter> D = 0; M(A); M(B); M(C); M(D)|]
      ==> |A \<union> C|\<^bsup>M\<^esup> = |B \<union> D|\<^bsup>M\<^esup>"
by (simp add: cardinal_rel_eqpoll_rel_iff eqpoll_rel_disjoint_Un)

lemma lepoll_rel_imp_cardinal_rel_le: "A \<lesssim>\<^bsup>M\<^esup> B ==> M(A) \<Longrightarrow> M(B) \<Longrightarrow> |A|\<^bsup>M\<^esup> \<le> |B|\<^bsup>M\<^esup>"
  apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
   apply (erule well_ord_lepoll_rel_imp_cardinal_rel_le, assumption+)
  done

lemma cadd_rel_assoc: "\<lbrakk>M(i); M(j); M(k)\<rbrakk> \<Longrightarrow> (i \<oplus>\<^bsup>M\<^esup> j) \<oplus>\<^bsup>M\<^esup> k = i \<oplus>\<^bsup>M\<^esup> (j \<oplus>\<^bsup>M\<^esup> k)"
  apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
   apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
    apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
     apply (rule well_ord_cadd_rel_assoc, assumption+)
done

lemma cmult_rel_assoc: "\<lbrakk>M(i); M(j); M(k)\<rbrakk> \<Longrightarrow> (i \<otimes>\<^bsup>M\<^esup> j) \<otimes>\<^bsup>M\<^esup> k = i \<otimes>\<^bsup>M\<^esup> (j \<otimes>\<^bsup>M\<^esup> k)"
  apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
   apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
    apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
     apply (rule well_ord_cmult_rel_assoc, assumption+)
  done

lemma cadd_cmult_distrib: "\<lbrakk>M(i); M(j); M(k)\<rbrakk> \<Longrightarrow> (i \<oplus>\<^bsup>M\<^esup> j) \<otimes>\<^bsup>M\<^esup> k = (i \<otimes>\<^bsup>M\<^esup> k) \<oplus>\<^bsup>M\<^esup> (j \<otimes>\<^bsup>M\<^esup> k)"
  apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
   apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
    apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
     apply (rule well_ord_cadd_cmult_distrib, assumption+)
  done


lemma InfCard_rel_square_eq: "InfCard\<^bsup>M\<^esup>(|A|\<^bsup>M\<^esup>) \<Longrightarrow> M(A) \<Longrightarrow> A\<times>A \<approx>\<^bsup>M\<^esup> A"
apply (rule choice_ax_well_ord [THEN rexE]) prefer 2
   apply (erule well_ord_InfCard_rel_square_eq, assumption, simp_all)
done

subsection \<open>The relationship between cardinality and le-pollence\<close>

lemma Card_rel_le_imp_lepoll_rel:
  assumes "|A|\<^bsup>M\<^esup> \<le> |B|\<^bsup>M\<^esup>"
    and types: "M(A)" "M(B)"
  shows "A \<lesssim>\<^bsup>M\<^esup> B"
proof -
  have "A \<approx>\<^bsup>M\<^esup> |A|\<^bsup>M\<^esup>"
    by (rule cardinal_rel_eqpoll_rel [THEN eqpoll_rel_sym], simp_all add:types)
  also have "... \<lesssim>\<^bsup>M\<^esup> |B|\<^bsup>M\<^esup>"
    by (rule le_imp_subset [THEN subset_imp_lepoll_rel]) (rule assms, simp_all add:types)
  also have "... \<approx>\<^bsup>M\<^esup> B"
    by (rule cardinal_rel_eqpoll_rel, simp_all add:types)
  finally show ?thesis by (simp_all add:types)
qed

lemma le_Card_rel_iff: "Card\<^bsup>M\<^esup>(K) ==> M(K) \<Longrightarrow> M(A) \<Longrightarrow> |A|\<^bsup>M\<^esup> \<le> K \<longleftrightarrow> A \<lesssim>\<^bsup>M\<^esup> K"
apply (erule Card_rel_cardinal_rel_eq [THEN subst], assumption, rule iffI,
       erule Card_rel_le_imp_lepoll_rel, assumption+)
apply (erule lepoll_rel_imp_cardinal_rel_le, assumption+)
done

lemma cardinal_rel_0_iff_0 [simp]: "M(A) \<Longrightarrow> |A|\<^bsup>M\<^esup> = 0 \<longleftrightarrow> A = 0"
  using cardinal_rel_0 eqpoll_rel_0_iff [THEN iffD1] 
    cardinal_rel_eqpoll_rel_iff [THEN iffD1, OF _ nonempty]
  by auto

lemma cardinal_rel_lt_iff_lesspoll_rel:
  assumes i: "Ord(i)" and
    types: "M(i)" "M(A)" 
  shows "i < |A|\<^bsup>M\<^esup> \<longleftrightarrow> i \<prec>\<^bsup>M\<^esup> A"
proof
  assume "i < |A|\<^bsup>M\<^esup>"
  hence  "i \<prec>\<^bsup>M\<^esup> |A|\<^bsup>M\<^esup>"
    by (blast intro: lt_Card_rel_imp_lesspoll_rel types) 
  also have "...  \<approx>\<^bsup>M\<^esup> A"
    by (rule cardinal_rel_eqpoll_rel) (simp_all add:types)
  finally show "i \<prec>\<^bsup>M\<^esup> A" by (simp_all add:types)
next
  assume "i \<prec>\<^bsup>M\<^esup> A"
  also have "...  \<approx>\<^bsup>M\<^esup> |A|\<^bsup>M\<^esup>"
    by (blast intro: cardinal_rel_eqpoll_rel eqpoll_rel_sym types) 
  finally have "i \<prec>\<^bsup>M\<^esup> |A|\<^bsup>M\<^esup>" by (simp_all add:types)
  thus  "i < |A|\<^bsup>M\<^esup>" using i types
    by (force intro: cardinal_rel_lt_imp_lt lesspoll_rel_cardinal_rel_lt)
qed

lemma cardinal_rel_le_imp_lepoll_rel: " i \<le> |A|\<^bsup>M\<^esup> ==> M(i) \<Longrightarrow> M(A) \<Longrightarrow>i \<lesssim>\<^bsup>M\<^esup> A"
  by (blast intro: lt_Ord Card_rel_le_imp_lepoll_rel Ord_cardinal_rel_le le_trans)


subsection\<open>Other Applications of AC\<close>

text\<open>We have an example of instantiating a locale involving higher
order variables inside a proof, by using the assumptions of the
first orde, active locale.\<close>

lemma surj_rel_implies_inj_rel:
  assumes f: "f \<in> surj\<^bsup>M\<^esup>(X,Y)" and
    types: "M(f)" "M(X)" "M(Y)"
  shows "\<exists>g[M]. g \<in> inj\<^bsup>M\<^esup>(Y,X)"
proof -
  from types
  interpret M_Pi_assumptions_choice _ Y "\<lambda>y. f-``{y}"
    by unfold_locales (auto intro:surj_imp_inj_replacement dest:transM)
  from f AC_Pi_rel
  obtain z where z: "z \<in> Pi\<^bsup>M\<^esup>(Y, \<lambda>y. f -`` {y})"
    \<comment> \<open>In this and the following ported result, it is not clear how
        uniformly are "_char" theorems to be used\<close>
    using surj_rel_char
    by (auto simp add: surj_def types) (fast dest: apply_Pair)
  show ?thesis
  proof
    show "z \<in> inj\<^bsup>M\<^esup>(Y, X)" "M(z)"
      using z surj_is_fun[of f X Y] f Pi_rel_char
      by (auto dest: apply_type Pi_memberD
          intro: apply_equality Pi_type f_imp_injective
          simp add:types mem_surj_abs)
  qed
qed


text\<open>Kunen's Lemma 10.20\<close>
lemma surj_rel_implies_cardinal_rel_le:
  assumes f: "f \<in> surj\<^bsup>M\<^esup>(X,Y)" and
    types:"M(f)" "M(X)" "M(Y)"
  shows "|Y|\<^bsup>M\<^esup> \<le> |X|\<^bsup>M\<^esup>"
proof (rule lepoll_rel_imp_cardinal_rel_le)
  from f [THEN surj_rel_implies_inj_rel]
  obtain g where "g \<in> inj\<^bsup>M\<^esup>(Y,X)"
    by (blast intro:types)
  then
  show "Y \<lesssim>\<^bsup>M\<^esup> X"
    using inj_rel_char
    by (auto simp add: def_lepoll_rel types)
qed (simp_all add:types)

end (* M_cardinal_AC *)

text\<open>The set-theoretic universe.\<close>

abbreviation
  Universe :: "i\<Rightarrow>o" (\<open>\<V>\<close>) where
  "\<V>(x) \<equiv> True"

lemma separation_absolute: "separation(\<V>, P)"
  unfolding separation_def
  by (rule rallI, rule_tac x="{x\<in>_ . P(x)}" in rexI) auto

lemma univalent_absolute:
  assumes "univalent(\<V>, A, P)" "P(x, b)" "x \<in> A"
  shows "P(x, y) \<Longrightarrow> y = b"
  using assms
  unfolding univalent_def by force

lemma replacement_absolute: "strong_replacement(\<V>, P)"
  unfolding strong_replacement_def
proof (intro rallI impI)
  fix A
  assume "univalent(\<V>, A, P)"
  then
  show "\<exists>Y[\<V>]. \<forall>b[\<V>]. b \<in> Y \<longleftrightarrow> (\<exists>x[\<V>]. x \<in> A \<and> P(x, b))"
    by (rule_tac x="{y. x\<in>A , P(x,y)}" in rexI)
      (auto dest:univalent_absolute[of _ P])
qed

lemma Union_ax_absolute: "Union_ax(\<V>)"
    unfolding Union_ax_def big_union_def
    by (auto intro:rexI[of _ "\<Union>_"])

lemma upair_ax_absolute: "upair_ax(\<V>)"
  unfolding upair_ax_def upair_def rall_def rex_def
    by (auto)

lemma power_ax_absolute:"power_ax(\<V>)"
proof -
  {
    fix x
    have "\<forall>y[\<V>]. y \<in> Pow(x) \<longleftrightarrow> (\<forall>z[\<V>]. z \<in> y \<longrightarrow> z \<in> x)"
      by auto
  }
  then
  show "power_ax(\<V>)"
    unfolding power_ax_def powerset_def subset_def by blast
qed

locale M_cardinal_UN =  M_Pi_assumptions_choice _ K X for K X +
  assumes
    \<comment> \<open>The next assumption is required by @{thm Least_closed}\<close>
    X_witness_in_M: "w \<in> X(x) \<Longrightarrow> M(x)"
    and
    lam_m_replacement:"M(f) \<Longrightarrow> strong_replacement(M,
      \<lambda>x y. y = \<langle>x, \<mu> i. x \<in> X(i), f ` (\<mu> i. x \<in> X(i)) ` x\<rangle>)"
    and
    inj_replacement:
    "M(x) \<Longrightarrow> strong_replacement(M, \<lambda>y z. y \<in> inj\<^bsup>M\<^esup>(X(x), K) \<and> z = {\<langle>x, y\<rangle>})"
    "strong_replacement(M, \<lambda>x y. y = inj\<^bsup>M\<^esup>(X(x), K))"
    "strong_replacement(M,
      \<lambda>x z. z = Sigfun(x, \<lambda>i. inj\<^bsup>M\<^esup>(X(i), K)))"
    "M(r) \<Longrightarrow> strong_replacement(M,
      \<lambda>x y. y = \<langle>x, minimum(r, inj\<^bsup>M\<^esup>(X(x), K))\<rangle>)"

begin

text\<open>Kunen's Lemma 10.21\<close>
lemma cardinal_UN_le:
  assumes K: "InfCard\<^bsup>M\<^esup>(K)"
  shows "(\<And>i. i\<in>K \<Longrightarrow> |X(i)|\<^bsup>M\<^esup> \<le> K) \<Longrightarrow> |\<Union>i\<in>K. X(i)|\<^bsup>M\<^esup> \<le> K"
proof (simp add: K InfCard_rel_is_Card_rel le_Card_rel_iff Pi_assumptions)
  have "M(\<Union>i\<in>K. X(i))"
    using family_union_closed B_replacement Pi_assumptions
    by (simp)
  then
  have "M(f) \<Longrightarrow> M(\<lambda>x\<in>(\<Union>x\<in>K. X(x)). \<langle>\<mu> i. x \<in> X(i), f ` (\<mu> i. x \<in> X(i)) ` x\<rangle>)" for f
    using lam_m_replacement X_witness_in_M Least_closed' Pi_assumptions
    by (rule_tac lam_closed) (auto dest:transM)
  note types = this \<open>M(\<Union>i\<in>K. X(i))\<close> Pi_assumptions
  have [intro]: "Ord(K)" by (blast intro: InfCard_rel_is_Card_rel
        Card_rel_is_Ord K types)
  interpret pii:M_Pi_assumptions_choice _ K "\<lambda>i. inj\<^bsup>M\<^esup>(X(i), K)"
    using inj_replacement Pi_assumptions transM[of _ K]
    by unfold_locales (simp_all del:mem_inj_abs)
  assume asm:"\<And>i. i\<in>K \<Longrightarrow> X(i) \<lesssim>\<^bsup>M\<^esup> K"
  then
  have "\<And>i. i\<in>K \<Longrightarrow> M(inj\<^bsup>M\<^esup>(X(i), K))"
    by (auto simp add: types)
  interpret V:M_N_Perm M "\<V>"
    using separation_absolute replacement_absolute Union_ax_absolute
      power_ax_absolute upair_ax_absolute
    by unfold_locales auto
  note bad_simps[simp del] = V.N.Forall_in_M_iff V.N.Equal_in_M_iff
    V.N.nonempty
  have abs:"inj_rel(\<V>,x,y) = inj(x,y)" for x y
    using V.N.inj_rel_char by simp
  from asm
  have "\<And>i. i\<in>K \<Longrightarrow> \<exists>f[M]. f \<in> inj\<^bsup>M\<^esup>(X(i), K)"
    by (simp add: types def_lepoll_rel)
  then
  obtain f where "f \<in> (\<Prod>i\<in>K. inj\<^bsup>M\<^esup>(X(i), K))" "M(f)"
    using pii.AC_Pi_rel pii.Pi_rel_char by auto
  with abs
  have f:"f \<in> (\<Prod>i\<in>K. inj(X(i), K))"
    using Pi_weaken_type[OF _ V.inj_rel_transfer, of f K X "\<lambda>_. K"]
      Pi_assumptions by simp
  { fix z
    assume z: "z \<in> (\<Union>i\<in>K. X(i))"
    then obtain i where i: "i \<in> K" "Ord(i)" "z \<in> X(i)"
      by (blast intro: Ord_in_Ord [of K]) 
    hence "(\<mu> i. z \<in> X(i)) \<le> i" by (fast intro: Least_le) 
    hence "(\<mu> i. z \<in> X(i)) < K" by (best intro: lt_trans1 ltI i) 
    hence "(\<mu> i. z \<in> X(i)) \<in> K" and "z \<in> X(\<mu> i. z \<in> X(i))"  
      by (auto intro: LeastI ltD i) 
  } note mems = this
  have "(\<Union>i\<in>K. X(i)) \<lesssim>\<^bsup>M\<^esup> K \<times> K"
    proof (simp add:types def_lepoll_rel)
      show "\<exists>f[M]. f \<in> inj(\<Union>x\<in>K. X(x), K \<times> K)"
        apply (rule rexI)
        apply (rule_tac c = "\<lambda>z. \<langle>\<mu> i. z \<in> X(i), f ` (\<mu> i. z \<in> X(i)) ` z\<rangle>"
                    and d = "\<lambda>\<langle>i,j\<rangle>. converse (f`i) ` j" in lam_injective) 
          apply (force intro: f inj_is_fun mems apply_type Perm.left_inverse)+
        apply (simp add:types \<open>M(f)\<close>)
        done
    qed
    also have "... \<approx>\<^bsup>M\<^esup> K"
    by (simp add: K InfCard_rel_square_eq InfCard_rel_is_Card_rel
        Card_rel_cardinal_rel_eq types)
  finally have "(\<Union>i\<in>K. X(i)) \<lesssim>\<^bsup>M\<^esup> K" by (simp_all add:types)
  then
  show ?thesis
    by (simp add: K InfCard_rel_is_Card_rel le_Card_rel_iff types)
qed

(*
text\<open>The same again, using \<^term>\<open>csucc\<close>\<close>
lemma cardinal_UN_lt_csucc:
     "[| InfCard(K);  \<And>i. i\<in>K \<Longrightarrow> |X(i)| < csucc(K) |]
      ==> |\<Union>i\<in>K. X(i)| < csucc(K)"
by (simp add: Card_lt_csucc_iff cardinal_UN_le InfCard_is_Card Card_cardinal)

text\<open>The same again, for a union of ordinals.  In use, j(i) is a bit like rank(i),
  the least ordinal j such that i:Vfrom(A,j).\<close>
lemma cardinal_UN_Ord_lt_csucc:
     "[| InfCard(K);  \<And>i. i\<in>K \<Longrightarrow> j(i) < csucc(K) |]
      ==> (\<Union>i\<in>K. j(i)) < csucc(K)"
apply (rule cardinal_UN_lt_csucc [THEN Card_lt_imp_lt], assumption)
apply (blast intro: Ord_cardinal_le [THEN lt_trans1] elim: ltE)
apply (blast intro!: Ord_UN elim: ltE)
apply (erule InfCard_is_Card [THEN Card_is_Ord, THEN Card_csucc])
done


subsection\<open>The Main Result for Infinite-Branching Datatypes\<close>

text\<open>As above, but the index set need not be a cardinal. Work
backwards along the injection from \<^term>\<open>W\<close> into \<^term>\<open>K\<close>, given
that \<^term>\<open>W\<noteq>0\<close>.\<close>

lemma inj_UN_subset:
  assumes f: "f \<in> inj(A,B)" and a: "a \<in> A"
  shows "(\<Union>x\<in>A. C(x)) \<subseteq> (\<Union>y\<in>B. C(if y \<in> range(f) then converse(f)`y else a))"
proof (rule UN_least)
  fix x
  assume x: "x \<in> A"
  hence fx: "f ` x \<in> B" by (blast intro: f inj_is_fun [THEN apply_type])
  have "C(x) \<subseteq> C(if f ` x \<in> range(f) then converse(f) ` (f ` x) else a)" 
    using f x by (simp add: inj_is_fun [THEN apply_rangeI])
  also have "... \<subseteq> (\<Union>y\<in>B. C(if y \<in> range(f) then converse(f) ` y else a))"
    by (rule UN_upper [OF fx]) 
  finally show "C(x) \<subseteq> (\<Union>y\<in>B. C(if y \<in> range(f) then converse(f)`y else a))" .
qed

theorem le_UN_Ord_lt_csucc:
  assumes IK: "InfCard(K)" and WK: "|W| \<le> K" and j: "\<And>w. w\<in>W \<Longrightarrow> j(w) < csucc(K)"
  shows "(\<Union>w\<in>W. j(w)) < csucc(K)"
proof -
  have CK: "Card(K)" 
    by (simp add: InfCard_is_Card IK)
  then obtain f where f: "f \<in> inj(W, K)" using WK
    by(auto simp add: le_Card_iff lepoll_def)
  have OU: "Ord(\<Union>w\<in>W. j(w))" using j
    by (blast elim: ltE)
  note lt_subset_trans [OF _ _ OU, trans]
  show ?thesis
    proof (cases "W=0")
      case True  \<comment> \<open>solve the easy 0 case\<close>
      thus ?thesis by (simp add: CK Card_is_Ord Card_csucc Ord_0_lt_csucc)
    next
      case False
        then obtain x where x: "x \<in> W" by blast
        have "(\<Union>x\<in>W. j(x)) \<subseteq> (\<Union>k\<in>K. j(if k \<in> range(f) then converse(f) ` k else x))"
          by (rule inj_UN_subset [OF f x]) 
        also have "... < csucc(K)" using IK
          proof (rule cardinal_UN_Ord_lt_csucc)
            fix k
            assume "k \<in> K"
            thus "j(if k \<in> range(f) then converse(f) ` k else x) < csucc(K)" using f x j
              by (simp add: inj_converse_fun [THEN apply_type])
          qed
        finally show ?thesis .
    qed
qed
*)

end (* M_cardinal_UN *)

end