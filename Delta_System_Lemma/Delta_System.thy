theory Delta_System
  imports 
    Konig

begin

no_notation oadd (infixl \<open>++\<close> 65)
no_notation sum (infixr \<open>+\<close> 65)
notation oadd (infixl \<open>+\<close> 65)

lemma nat_oadd_add[simp]:
  assumes "m \<in> nat" "n \<in> nat" shows "n + m = n #+ m"
  using assms
  by induct simp_all

notation csucc (\<open>_\<^sup>+\<close> [90])

\<comment> \<open>Copy-pasted from \<^file>\<open>../src/Cohen_Posets.thy\<close>. MOVE to an
    appropriate place\<close>
lemma eq_csucc_ord:
  "Ord(i) \<Longrightarrow> csucc(i) = csucc(|i|)"
  using Card_lt_iff Least_cong unfolding csucc_def by auto

lemma lesspoll_csucc:
  assumes "Ord(\<kappa>)"
  shows "d \<prec> csucc(\<kappa>) \<longleftrightarrow> d \<lesssim> \<kappa>"
proof
  assume "d \<prec> csucc(\<kappa>)"
  moreover
  note Card_is_Ord \<open>Ord(\<kappa>)\<close>
  moreover from calculation
  have "\<kappa> < csucc(\<kappa>)" "Card(csucc(\<kappa>))"
    using Ord_cardinal_eqpoll csucc_basic by simp_all
  moreover from calculation
  have "d \<prec> csucc(|\<kappa>|)" "Card(|\<kappa>|)" "d \<approx> |d|"
    using eq_csucc_ord[of \<kappa>] lesspoll_imp_eqpoll eqpoll_sym by simp_all
  moreover from calculation
  have "|d| < csucc(|\<kappa>|)"
    using lesspoll_cardinal_lt csucc_basic by simp
  moreover from calculation
  have "|d| \<lesssim> |\<kappa>|"
    using Card_lt_csucc_iff le_imp_lepoll by simp
  moreover from calculation
  have "|d| \<lesssim> \<kappa>"
    using lepoll_eq_trans Ord_cardinal_eqpoll by simp
  ultimately
  show "d \<lesssim> \<kappa>"
    using eq_lepoll_trans by simp
next
  from \<open>Ord(\<kappa>)\<close>
  have "\<kappa> < csucc(\<kappa>)" "Card(csucc(\<kappa>))"
    using csucc_basic by simp_all
  moreover
  assume "d \<lesssim> \<kappa>"
  ultimately
  have "d \<lesssim> csucc(\<kappa>)"
    using le_imp_lepoll leI lepoll_trans by simp
  moreover
  from \<open>d \<lesssim> \<kappa>\<close> \<open>Ord(\<kappa>)\<close>
  have "csucc(\<kappa>) \<lesssim> \<kappa>" if "d \<approx> csucc(\<kappa>)"
    using eqpoll_sym[OF that] eq_lepoll_trans[OF _ \<open>d\<lesssim>\<kappa>\<close>] by simp
  moreover from calculation \<open>Card(_)\<close>
  have "\<not> d \<approx> csucc(\<kappa>)"
    using lesspoll_irrefl lesspoll_trans1 lt_Card_imp_lesspoll[OF _ \<open>\<kappa> <_\<close>]
    by auto
  ultimately
  show "d \<prec> csucc(\<kappa>)"
    unfolding lesspoll_def by simp
qed

lemma mono_mapI: 
  assumes "f: A\<rightarrow>B" "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> <x,y>\<in>r \<Longrightarrow> <f`x,f`y>\<in>s"
  shows   "f \<in> mono_map(A,r,B,s)"
  unfolding mono_map_def using assms by simp

lemmas mono_mapD = mono_map_is_fun mono_map_increasing

lemmas Aleph_cont = Normal_imp_cont[OF Normal_Aleph]
lemmas Aleph_sup = Normal_Union[OF _ _ Normal_Aleph]

bundle Ord_dests = Limit_is_Ord[dest] Card_is_Ord[dest]
bundle Aleph_dests = Aleph_cont[dest] Aleph_sup[dest]
bundle Aleph_intros = Aleph_mono[intro!]
bundle Aleph_mem_dests = Aleph_mono[OF ltI, THEN ltD, dest]
bundle mono_map_rules =  mono_mapI[intro!] mono_map_is_fun[dest] mono_mapD[dest]

context
  includes Ord_dests Aleph_dests Aleph_intros Aleph_mem_dests mono_map_rules
begin

lemma cf_Aleph_Limit:
  assumes "Limit(\<gamma>)"
  shows "cf(\<aleph>\<^bsub>\<gamma>\<^esub>) = cf(\<gamma>)" 
proof -
  note \<open>Limit(\<gamma>)\<close>
  moreover from this
  have "(\<lambda>x\<in>\<gamma>. \<aleph>\<^bsub>x\<^esub>) : \<gamma> \<rightarrow> \<aleph>\<^bsub>\<gamma>\<^esub>" (is "?f : _ \<rightarrow> _")
    using lam_funtype[of _ Aleph] fun_weaken_type[of _ _ _ "\<aleph>\<^bsub>\<gamma>\<^esub>"] by blast
  moreover from \<open>Limit(\<gamma>)\<close>
  have "x \<in> y \<Longrightarrow> \<aleph>\<^bsub>x\<^esub> \<in> \<aleph>\<^bsub>y\<^esub>" if "x \<in> \<gamma>" "y \<in> \<gamma>" for x y
    using that Ord_in_Ord[of \<gamma>] Ord_trans[of _ _ \<gamma>] by blast
  ultimately
  have "?f \<in> mono_map(\<gamma>,Memrel(\<gamma>),\<aleph>\<^bsub>\<gamma>\<^esub>, Memrel(\<aleph>\<^bsub>\<gamma>\<^esub>))"
    by auto
  with  \<open>Limit(\<gamma>)\<close> 
  have "?f \<in> \<langle>\<gamma>, Memrel(\<gamma>)\<rangle> \<cong> \<langle>?f``\<gamma>, Memrel(\<aleph>\<^bsub>\<gamma>\<^esub>)\<rangle>"
    using mono_map_imp_ord_iso_Memrel[of \<gamma> "\<aleph>\<^bsub>\<gamma>\<^esub>" ?f] 
      Card_Aleph (* Already an intro rule, but need it explicitly *)
    by blast
  then
  have "converse(?f) \<in> \<langle>?f``\<gamma>, Memrel(\<aleph>\<^bsub>\<gamma>\<^esub>)\<rangle> \<cong> \<langle>\<gamma>, Memrel(\<gamma>)\<rangle>"
    using ord_iso_sym by simp
  with \<open>Limit(\<gamma>)\<close>
  have "ordertype(?f``\<gamma>, Memrel(\<aleph>\<^bsub>\<gamma>\<^esub>)) = \<gamma>"
    using ordertype_eq[OF _ well_ord_Memrel]
    ordertype_Memrel by auto
  moreover from \<open>Limit(\<gamma>)\<close>
  have "cofinal(?f``\<gamma>, \<aleph>\<^bsub>\<gamma>\<^esub>, Memrel(\<aleph>\<^bsub>\<gamma>\<^esub>))" 
    unfolding cofinal_def 
  proof (standard, intro ballI)
    fix a
    assume "a\<in>\<aleph>\<^bsub>\<gamma>\<^esub>" "\<aleph>\<^bsub>\<gamma>\<^esub> = (\<Union>i<\<gamma>. \<aleph>\<^bsub>i\<^esub>)"
    moreover from this
    obtain i where "i<\<gamma>" "a\<in>\<aleph>\<^bsub>i\<^esub>"
      by auto
    moreover from this and \<open>Limit(\<gamma>)\<close>
    have "Ord(i)" using ltD Ord_in_Ord by blast
    moreover from \<open>Limit(\<gamma>)\<close> and calculation
    have "succ(i) \<in> \<gamma>" using ltD by auto
    moreover from this and \<open>Ord(i)\<close>
    have "\<aleph>\<^bsub>i\<^esub> < \<aleph>\<^bsub>succ(i)\<^esub>" 
      by (auto) 
    ultimately
    have "<a,\<aleph>\<^bsub>i\<^esub>> \<in> Memrel(\<aleph>\<^bsub>\<gamma>\<^esub>)"
      using ltD by (auto dest:Aleph_mono)
    moreover from \<open>i<\<gamma>\<close>
    have "\<aleph>\<^bsub>i\<^esub> \<in> ?f``\<gamma>" 
      using ltD apply_in_image[OF \<open>?f : _ \<rightarrow> _\<close>] by auto
    ultimately
    show "\<exists>x\<in>?f `` \<gamma>. \<langle>a, x\<rangle> \<in> Memrel(\<aleph>\<^bsub>\<gamma>\<^esub>) \<or> a = x" by blast
  qed
  moreover
  note \<open>?f: \<gamma> \<rightarrow> \<aleph>\<^bsub>\<gamma>\<^esub>\<close> \<open>Limit(\<gamma>)\<close>
  ultimately
  show "cf(\<aleph>\<^bsub>\<gamma>\<^esub>) =  cf(\<gamma>)"
    using cf_ordertype_cofinal[OF Limit_Aleph Image_sub_codomain, of \<gamma> ?f \<gamma> \<gamma> ] 
      Limit_is_Ord by simp 
qed

end (* includes *)

lemma cardinal_lt_csucc_iff: "Card(K) \<Longrightarrow> |K'| < K\<^sup>+ \<longleftrightarrow> |K'| \<le> K"
  by (simp add: Card_lt_csucc_iff)

lemma cardinal_UN_le_nat:
  "(\<And>i. i\<in>nat \<Longrightarrow> |X(i)| \<le> nat) \<Longrightarrow> |\<Union>i\<in>nat. X(i)| \<le> nat"
  by (simp add: cardinal_UN_le InfCard_nat) 

lemma leqpoll_imp_cardinal_UN_le:
  notes [dest] = InfCard_is_Card Card_is_Ord
  assumes "InfCard(K)" "J \<lesssim> K" "\<And>i. i\<in>J \<Longrightarrow> |X(i)| \<le> K"
  shows "|\<Union>i\<in>J. X(i)| \<le> K"
proof -
  from \<open>J \<lesssim> K\<close>
  obtain f where "f \<in> inj(J,K)" by blast
  define Y where "Y(k) \<equiv> if k\<in>range(f) then X(converse(f)`k) else 0" for k
  have "i\<in>J \<Longrightarrow> f`i \<in> K" for i
    using inj_is_fun[OF \<open>f \<in> inj(J,K)\<close>] by auto
  have "(\<Union>i\<in>J. X(i)) \<subseteq> (\<Union>i\<in>K. Y(i))"
  proof (standard, elim UN_E)
    fix x i
    assume "i\<in>J" "x\<in>X(i)"
    with \<open>f \<in> inj(J,K)\<close> \<open>i\<in>J \<Longrightarrow> f`i \<in> K\<close>
    have "x \<in> Y(f`i)" "f`i \<in> K"
      unfolding Y_def 
      using inj_is_fun[OF \<open>f \<in> inj(J,K)\<close>] 
        right_inverse apply_rangeI by auto
    then
    show "x \<in> (\<Union>i\<in>K. Y(i))" by auto
  qed
  then
  have "|\<Union>i\<in>J. X(i)| \<le> |\<Union>i\<in>K. Y(i)|"
    unfolding Y_def using subset_imp_le_cardinal by simp
  with assms \<open>\<And>i. i\<in>J \<Longrightarrow> f`i \<in> K\<close>
  show "|\<Union>i\<in>J. X(i)| \<le> K" 
    using inj_converse_fun[OF \<open>f \<in> inj(J,K)\<close>] unfolding Y_def
    by (rule_tac le_trans[OF _ cardinal_UN_le]) (auto intro:Ord_0_le)+
qed

lemma nat_lt_Aleph1: "nat<\<aleph>\<^bsub>1\<^esub>"
  by (simp add: Aleph_def lt_csucc)

lemma zero_lt_Aleph1: "0<\<aleph>\<^bsub>1\<^esub>"
  by (rule lt_trans[of _ "nat"], auto simp add: ltI nat_lt_Aleph1)

lemma le_aleph1_nat: "Card(k) \<Longrightarrow> k<\<aleph>\<^bsub>1\<^esub> \<Longrightarrow> k \<le> nat"    
  by (simp add: Aleph_def Card_lt_csucc_iff Card_nat)

lemma Aleph_succ: "\<aleph>\<^bsub>succ(\<alpha>)\<^esub> = \<aleph>\<^bsub>\<alpha>\<^esub>\<^sup>+"
  unfolding Aleph_def by simp

lemma lesspoll_aleph_plus_one:
  assumes "Ord(\<alpha>)"
  shows "d \<prec> \<aleph>\<^bsub>succ(\<alpha>)\<^esub> \<longleftrightarrow> d \<lesssim> \<aleph>\<^bsub>\<alpha>\<^esub>"
  using assms lesspoll_csucc Aleph_succ Card_is_Ord by simp

lemma cardinal_lt_csucc_iff':
  includes Ord_dests
  assumes "Card(\<kappa>)"
  shows "\<kappa> < |X| \<longleftrightarrow> \<kappa>\<^sup>+ \<le> |X|"
  using assms cardinal_lt_csucc_iff[of \<kappa> X] Card_csucc[of \<kappa>]
    not_le_iff_lt[of "\<kappa>\<^sup>+" "|X|"] not_le_iff_lt[of "|X|" \<kappa>]
  by blast

lemma lepoll_imp_subset_bij: "X \<lesssim> Y \<longleftrightarrow> (\<exists>Z. Z \<subseteq> Y \<and> Z \<approx> X)"
proof
  assume "X \<lesssim> Y"
  then
  obtain j where  "j \<in> inj(X,Y)"
    by blast
  then
  have "range(j) \<subseteq> Y" "j \<in> bij(X,range(j))"
    using inj_bij_range inj_is_fun Cofinality.range_of_function
    by blast+
  then
  show "\<exists>Z. Z \<subseteq> Y \<and> Z \<approx> X"
    using eqpoll_sym unfolding eqpoll_def
    by force
next
  assume "\<exists>Z. Z \<subseteq> Y \<and> Z \<approx> X"
  then
  obtain Z f where "f \<in> bij(Z,X)" "Z \<subseteq> Y"
    unfolding eqpoll_def by force
  then
  have "converse(f) \<in> inj(X,Y)"
    using bij_is_inj inj_weaken_type bij_converse_bij by blast
  then
  show "X \<lesssim> Y" by blast
qed

lemma cardinal_Aleph [simp]: "Ord(\<alpha>) \<Longrightarrow> |\<aleph>\<^bsub>\<alpha>\<^esub>| = \<aleph>\<^bsub>\<alpha>\<^esub>"
  using Card_cardinal_eq by simp

lemma cardinal_Card_eqpoll_iff: "Card(\<kappa>) \<Longrightarrow> |X| = \<kappa> \<longleftrightarrow> X \<approx> \<kappa>"
  using Card_cardinal_eq[of \<kappa>] cardinal_eqpoll_iff[of X \<kappa>] by auto

\<comment> \<open>Kunen's Definition I.10.5\<close>
definition
  countable :: "i\<Rightarrow>o" where
  "countable(X) \<equiv> X \<lesssim> nat"

abbreviation
  uncountable :: "i\<Rightarrow>o" where
  "uncountable(X) \<equiv> \<not> countable(X)"

lemma uncountable_iff_nat_lt_cardinal:
  "uncountable(X) \<longleftrightarrow> nat < |X|"
  sorry

lemma uncountable_imp_subset_eqpoll_aleph1:
  includes Ord_dests
  notes Aleph_zero_eq_nat[simp] Card_nat[simp] Aleph_succ[simp]
  assumes "uncountable(X)"
  shows "\<exists>S. S \<subseteq> X \<and> S \<approx> \<aleph>\<^bsub>1\<^esub>"
proof -
  from assms
  have a:"\<aleph>\<^bsub>1\<^esub> \<lesssim> X"
    using uncountable_iff_nat_lt_cardinal cardinal_lt_csucc_iff'
      cardinal_le_imp_lepoll by force
  then
  obtain S where "S \<subseteq> X" "S \<approx> \<aleph>\<^bsub>1\<^esub>"
    using lepoll_imp_subset_bij by auto
  then
  show ?thesis
    using cardinal_cong Card_csucc[of nat] Card_cardinal_eq by auto
qed

lemma cof_aleph1_aux: "function(G) \<Longrightarrow> domain(G) \<lesssim> nat \<Longrightarrow> 
   \<forall>n\<in>domain(G). |G`n|<\<aleph>\<^bsub>1\<^esub> \<Longrightarrow> |\<Union>n\<in>domain(G). G`n|\<le>nat"
proof -
  assume "function(G)"
  let ?N="domain(G)" and ?R="\<Union>n\<in>domain(G). G`n"
  assume "?N \<lesssim> nat"
  assume Eq1: "\<forall>n\<in>?N. |G`n|<\<aleph>\<^bsub>1\<^esub>"
  {
    fix n
    assume "n\<in>?N"
    with Eq1 have "|G`n| \<le> nat"
      using le_aleph1_nat by simp
  }
  then
  have "n\<in>?N \<Longrightarrow> |G`n| \<le> nat" for n .
  with \<open>?N \<lesssim> nat\<close> 
  show ?thesis
    using InfCard_nat leqpoll_imp_cardinal_UN_le by simp
qed

lemma Pi_vimage_subset : "f \<in> Pi(A,B) \<Longrightarrow> f-``C \<subseteq> A"
  unfolding Pi_def by auto

lemma aleph1_eq_cardinal_vimage: "f:\<aleph>\<^bsub>1\<^esub>\<rightarrow>nat \<Longrightarrow> \<exists>n\<in>nat. |f-``{n}| = \<aleph>\<^bsub>1\<^esub>"
proof -
  assume "f:\<aleph>\<^bsub>1\<^esub>\<rightarrow>nat"
  then
  have "function(f)" "domain(f) = \<aleph>\<^bsub>1\<^esub>" "range(f)\<subseteq>nat"
    by (simp_all add: domain_of_fun fun_is_function range_of_function)
  let ?G="\<lambda>n\<in>range(f). f-``{n}"
  from \<open>f:\<aleph>\<^bsub>1\<^esub>\<rightarrow>nat\<close>
  have "range(f) \<subseteq> nat" by (simp add: range_of_function)
  then
  have "domain(?G) \<lesssim> nat"
    using subset_imp_lepoll by simp
  have "function(?G)" by (simp add:function_lam)
  from \<open>f:\<aleph>\<^bsub>1\<^esub>\<rightarrow>nat\<close>
  have "n\<in>nat \<Longrightarrow> f-``{n} \<subseteq> \<aleph>\<^bsub>1\<^esub>" for n
    using Pi_vimage_subset by simp
  with \<open>range(f) \<subseteq> nat\<close>
  have "\<aleph>\<^bsub>1\<^esub> = (\<Union>n\<in>range(f). f-``{n})"
  proof (intro equalityI, intro subsetI)
    fix x 
    assume "x \<in> \<aleph>\<^bsub>1\<^esub>"
    with \<open>f:\<aleph>\<^bsub>1\<^esub>\<rightarrow>nat\<close> \<open>function(f)\<close> \<open>domain(f) = \<aleph>\<^bsub>1\<^esub>\<close>
    have "x \<in> f-``{f`x}" "f`x \<in> range(f)" 
      using function_apply_Pair vimage_iff apply_rangeI by simp_all
    then 
    show "x \<in> (\<Union>n\<in>range(f). f-``{n})" by auto
  qed auto
  {
    assume "\<forall>n\<in>range(f). |f-``{n}| < \<aleph>\<^bsub>1\<^esub>"
    then 
    have "\<forall>n\<in>domain(?G). |?G`n| < \<aleph>\<^bsub>1\<^esub>" 
      using zero_lt_Aleph1 by (auto)
    with \<open>function(?G)\<close> \<open>domain(?G) \<lesssim> nat\<close> 
    have "|\<Union>n\<in>domain(?G). ?G`n|\<le>nat"
      using cof_aleph1_aux by blast
    then 
    have "|\<Union>n\<in>range(f). f-``{n}|\<le>nat" by simp
    with \<open>\<aleph>\<^bsub>1\<^esub> = _\<close>
    have "|\<aleph>\<^bsub>1\<^esub>| \<le> nat" by simp
    then 
    have "\<aleph>\<^bsub>1\<^esub> \<le> nat"
      using Card_Aleph Card_cardinal_eq
      by simp
    then 
    have "False"
      using nat_lt_Aleph1 by (blast dest:lt_trans2)
  }
  with \<open>range(f)\<subseteq>nat\<close> 
  obtain n where "n\<in>nat" "\<not>(|f -`` {n}| < \<aleph>\<^bsub>1\<^esub>)"
    by blast
  moreover from this
  have "\<aleph>\<^bsub>1\<^esub> \<le> |f-``{n}|"
    using not_lt_iff_le Card_is_Ord by auto
  moreover
  note \<open>n\<in>nat \<Longrightarrow> f-``{n} \<subseteq> \<aleph>\<^bsub>1\<^esub>\<close>
  ultimately
  show ?thesis
    using subset_imp_le_cardinal[THEN le_anti_sym, of _ "\<aleph>\<^bsub>1\<^esub>"]
      Card_Aleph Card_cardinal_eq by auto
qed

lemma range_of_subset_eqpoll:
  assumes "f \<in> inj(X,Y)" "S \<subseteq> X"
  shows "S \<approx> f `` S"
  using assms restrict_bij by blast

\<comment> \<open>FIXME: asymmetry between assumptions and conclusion
    (\<^term>\<open>(\<approx>)\<close> versus \<^term>\<open>cardinal\<close>)\<close>
lemma eqpoll_aleph1_cardinal_vimage:
  assumes "X \<approx> \<aleph>\<^bsub>1\<^esub>" "f : X \<rightarrow> nat"
  shows "\<exists>n\<in>nat. |f-``{n}| = \<aleph>\<^bsub>1\<^esub>"
proof -
  from assms
  obtain g where "g\<in>bij(\<aleph>\<^bsub>1\<^esub>,X)"
    using eqpoll_sym by blast
  with \<open>f : X \<rightarrow> nat\<close>
  have "f O g : \<aleph>\<^bsub>1\<^esub> \<rightarrow> nat" "converse(g) \<in> bij(X, \<aleph>\<^bsub>1\<^esub>)"
    using bij_is_fun comp_fun bij_converse_bij by blast+
  then
  obtain n where "n\<in>nat" "|(f O g)-``{n}| = \<aleph>\<^bsub>1\<^esub>"
    using aleph1_eq_cardinal_vimage by auto
  then
  have "\<aleph>\<^bsub>1\<^esub> = |converse(g) `` (f -``{n})|"
    using image_comp converse_comp
    unfolding vimage_def by simp
  also from \<open>converse(g) \<in> bij(X, \<aleph>\<^bsub>1\<^esub>)\<close> \<open>f: X\<rightarrow> nat\<close>
  have "\<dots> = |f -``{n}|"
    using range_of_subset_eqpoll[of "converse(g)" X  _ "f -``{n}"]
      bij_is_inj cardinal_cong bij_is_fun eqpoll_sym Pi_vimage_subset
    by fastforce
  finally
  show ?thesis using \<open>n\<in>nat\<close> by auto
qed

definition
  delta_system :: "i \<Rightarrow> o" where
  "delta_system(D) \<equiv> \<exists>r. \<forall>A\<in>D. \<forall>B\<in>D. A \<noteq> B \<longrightarrow> A \<inter> B = r"

lemma delta_systemI[intro]: 
  assumes "\<forall>A\<in>D. \<forall>B\<in>D. A \<noteq> B \<longrightarrow> A \<inter> B = r"
  shows "delta_system(D)"
  using assms unfolding delta_system_def by simp

lemma delta_systemD[dest]:
  "delta_system(D) \<Longrightarrow> \<exists>r. \<forall>A\<in>D. \<forall>B\<in>D. A \<noteq> B \<longrightarrow> A \<inter> B = r"
  unfolding delta_system_def by simp

lemma vimage_lam: "(\<lambda>x\<in>A. f(x)) -`` B = { x\<in>A . f(x) \<in> B }"
  using lam_funtype[of A f, THEN [2] domain_type]
    lam_funtype[of A f, THEN [2] apply_equality] lamI[of _ A f]
  by auto blast

lemma Int_eq_zero_imp_not_eq:
  assumes
    "\<And>x y. x\<in>D \<Longrightarrow> y \<in> D \<Longrightarrow> x \<noteq> y \<Longrightarrow> A(x) \<inter> A(y) = 0"
    "\<And>x. x\<in>D \<Longrightarrow> A(x) \<noteq> 0" "a\<in>D" "b\<in>D" "a\<noteq>b"
  shows
    "A(a) \<noteq> A(b)"
  using assms by fastforce

lemma cardinal_succ_not_0: "|A| = succ(n) \<Longrightarrow> A \<noteq> 0"
  by auto

lemma lt_neq_symmetry:
  assumes
    "\<And>\<alpha> \<beta>. \<alpha> \<in> \<gamma> \<Longrightarrow> \<beta> \<in> \<gamma> \<Longrightarrow> \<alpha> < \<beta> \<Longrightarrow> Q(\<alpha>,\<beta>)"
    "\<And>\<alpha> \<beta>. Q(\<alpha>,\<beta>) \<Longrightarrow> Q(\<beta>,\<alpha>)"
    "\<alpha> \<in> \<gamma>" "\<beta> \<in> \<gamma>" "\<alpha> \<noteq> \<beta>"
    "Ord(\<gamma>)"
  shows
    "Q(\<alpha>,\<beta>)"
proof -
  from assms
  consider "\<alpha><\<beta>" | "\<beta><\<alpha>"
    using Ord_linear_lt[of \<alpha> \<beta> thesis] Ord_in_Ord[of \<gamma>]
    by auto
  then
  show ?thesis by cases (auto simp add:assms)
qed

lemma naturals_lt_nat[intro]: "n \<in> nat \<Longrightarrow> n < nat"
  unfolding lt_def by simp

lemma cardinal_map_Un:
  assumes
    "nat \<le> |X|"
    "|b| < nat"
  shows "|{a \<union> b . a \<in> X}| = |X|"
  sorry

lemma Diff_bij:
  assumes "\<forall>A\<in>F. X \<subseteq> A" shows "(\<lambda>A\<in>F. A-X) \<in> bij(F, {A-X. A\<in>F})"
  sorry

lemma
  assumes
    "\<And>X. |X| < \<gamma> \<Longrightarrow> X \<subseteq> G \<Longrightarrow> \<exists>a\<in>G. \<forall>s\<in>X. Q(s,a)" "Card(\<gamma>)"
  obtains S where "S : \<gamma> \<rightarrow> G"
    "\<And>\<alpha> \<beta>. \<alpha> \<in> \<gamma> \<Longrightarrow> \<beta> \<in> \<gamma> \<Longrightarrow> \<alpha><\<beta> \<Longrightarrow> Q(S`\<alpha>,S`\<beta>)"
  oops

lemma Finite_cardinal_iff_AC: "Finite(|i|) \<longleftrightarrow> Finite(i)"
  using cardinal_eqpoll_iff eqpoll_imp_Finite_iff by fastforce

lemma delta_system_Aleph1:
  assumes "\<forall>A\<in>F. Finite(A)" "F \<approx> \<aleph>\<^bsub>1\<^esub>"
  shows "\<exists>D. D \<subseteq> F \<and> delta_system(D) \<and> D \<approx> \<aleph>\<^bsub>1\<^esub>"
proof -
  from \<open>\<forall>A\<in>F. Finite(A)\<close>
  have "(\<lambda>A\<in>F. |A|) : F \<rightarrow> nat" (is "?cards : _")
    by (rule_tac lam_type) simp
  moreover from this
  have a:"?cards -`` {n} = { A\<in>F . |A| = n }" for n
    using vimage_lam by auto
  moreover
  note \<open>F \<approx> \<aleph>\<^bsub>1\<^esub>\<close>
  moreover from calculation
  obtain n where "n\<in>nat" "|?cards -`` {n}| = \<aleph>\<^bsub>1\<^esub>"
    using eqpoll_aleph1_cardinal_vimage[of F ?cards] by auto
  moreover
  define G where "G \<equiv> ?cards -`` {n}"
  moreover from calculation
  have "G \<subseteq> F" by auto
  ultimately
  have "A\<in>G \<Longrightarrow> |A| = n" "G \<approx> \<aleph>\<^bsub>1\<^esub>" for A
    using cardinal_Card_eqpoll_iff by auto
  with \<open>n\<in>nat\<close>
  have "\<exists>D. D \<subseteq> G \<and> delta_system(D) \<and> D \<approx> \<aleph>\<^bsub>1\<^esub>"
  proof (induct arbitrary:G)
    case 0 \<comment> \<open>This case is impossible\<close>
    then
    have "G \<subseteq> {0}"
      using cardinal_0_iff_0 by auto
    with \<open>G \<approx> \<aleph>\<^bsub>1\<^esub>\<close>
    show ?case
      using nat_lt_Aleph1 subset_imp_le_cardinal[of G "{0}"]
        lt_trans2 cardinal_Card_eqpoll_iff by auto
  next
    case (succ n)
    then
    have "\<forall>a\<in>G. Finite(a)"
      using Finite_cardinal_iff_AC nat_into_Finite[of "succ(n)"]
      by fastforce
    show "\<exists>D. D \<subseteq> G \<and> delta_system(D) \<and> D \<approx> \<aleph>\<^bsub>1\<^esub>"
    proof (cases "\<exists>p. {A\<in>G . p \<in> A} \<approx> \<aleph>\<^bsub>1\<^esub>")
      case True
      then
      obtain p where "{A\<in>G . p \<in> A} \<approx> \<aleph>\<^bsub>1\<^esub>" by blast
      moreover from this
      have "{A-{p} . A\<in>{X\<in>G. p\<in>X}} \<approx> \<aleph>\<^bsub>1\<^esub>" (is "?F \<approx> _")
        using Diff_bij[of "{A\<in>G . p \<in> A}" "{p}"]
          comp_bij[OF bij_converse_bij, where C="\<aleph>\<^bsub>1\<^esub>"] by fast
      text\<open>Now using the inductive hypothesis:\<close>
      moreover from \<open>\<And>A. A\<in>G \<Longrightarrow> |A|=succ(n)\<close> \<open>\<forall>a\<in>G. Finite(a)\<close>
        and this
      have "p\<in>A \<Longrightarrow> A\<in>G \<Longrightarrow> |A - {p}| = n" for A
        using Finite_imp_succ_cardinal_Diff[of _ p] by force
      moreover from this and \<open>n\<in>nat\<close>
      have "\<forall>a\<in>?F. Finite(a)" using Finite_cardinal_iff_AC
          nat_into_Finite by auto
      moreover \<comment> \<open>the inductive hypothesis\<close>
      note \<open>(\<And>A. A \<in> ?F \<Longrightarrow> |A| = n) \<Longrightarrow> ?F \<approx> \<aleph>\<^bsub>1\<^esub> \<Longrightarrow> \<exists>D. D \<subseteq> ?F \<and> delta_system(D) \<and> D \<approx> \<aleph>\<^bsub>1\<^esub>\<close>
      ultimately
      obtain D where "D\<subseteq>{A-{p} . A\<in>{X\<in>G. p\<in>X}}" "delta_system(D)" "D \<approx> \<aleph>\<^bsub>1\<^esub>"
        by auto
      moreover from this
      obtain r where "\<forall>A\<in>D. \<forall>B\<in>D. A \<noteq> B \<longrightarrow> A \<inter> B = r"
        by fastforce
      then
      have "\<forall>A\<in>D. \<forall>B\<in>D. A \<union> {p} \<noteq> B \<union> {p} \<longrightarrow> (A \<union> {p}) \<inter> (B \<union> {p}) = r \<union> {p}"
        by blast
      ultimately
      have "delta_system({B \<union> {p} . B\<in>D})" (is "delta_system(?D)")
        by fastforce
      moreover
      note \<open>D \<approx> \<aleph>\<^bsub>1\<^esub>\<close>
      then
      have \<open>|D| = \<aleph>\<^bsub>1\<^esub>\<close> using cardinal_eqpoll_iff by force
      moreover from this
      have "?D \<approx> \<aleph>\<^bsub>1\<^esub>"
        using cardinal_map_Un leI naturals_lt_nat
          cardinal_eqpoll_iff[THEN iffD1] nat_lt_Aleph1
        by auto
      moreover
      note \<open>D \<subseteq> {A-{p} . A\<in>{X\<in>G. p\<in>X}}\<close>
      have "?D \<subseteq> G"
      proof -
        {
          fix A
          assume "A\<in>G" "p\<in>A"
          moreover from this
          have "A = A - {p} \<union> {p}"
            by blast
          ultimately
          have "A -{p} \<union> {p} \<in> G"
            by auto
        }
        with \<open>D \<subseteq> {A-{p} . A\<in>{X\<in>G. p\<in>X}}\<close>
        show ?thesis
          by blast
      qed
      ultimately
      show "\<exists>D. D \<subseteq> G \<and> delta_system(D) \<and> D \<approx> \<aleph>\<^bsub>1\<^esub>" by auto
    next
      case False
      note \<open>\<not> (\<exists>p. {A \<in> G . p \<in> A} \<approx> \<aleph>\<^bsub>1\<^esub>)\<close> \<comment> \<open>the inductive hypothesis\<close>
      moreover from \<open>G \<approx> \<aleph>\<^bsub>1\<^esub>\<close>
      have "{A \<in> G . p \<in> A} \<lesssim> \<aleph>\<^bsub>1\<^esub>" (is "?G(p) \<lesssim> _") for p
        by (blast intro:lepoll_eq_trans[OF subset_imp_lepoll])
      ultimately
      have "?G(p) \<prec> \<aleph>\<^bsub>1\<^esub>" for p
        unfolding lesspoll_def by simp
      then \<comment> \<open>may omit the previous step if unfolding here:\<close>
      have "?G(p) \<lesssim> nat" for p
        using lesspoll_aleph_plus_one[of 0] Aleph_zero_eq_nat by auto
      moreover
      have "{A \<in> G . S \<inter> A \<noteq> 0} = (\<Union>p\<in>S. ?G(p))" for S
        by auto
      ultimately
      have "S \<lesssim> nat \<Longrightarrow> |{A \<in> G . S \<inter> A \<noteq> 0}| \<le> nat" for S
        using leqpoll_imp_cardinal_UN_le InfCard_nat
          lepoll_cardinal_le by simp
      from \<open>n\<in>nat\<close> \<open>\<And>A. A\<in>G \<Longrightarrow> |A| = succ(n)\<close>
      have "S\<in>G \<Longrightarrow> \<exists>A\<in>G. S \<inter> A = 0" for S sorry
      then
      obtain S where "S : \<aleph>\<^bsub>1\<^esub> \<rightarrow> G" "\<alpha> \<in> \<aleph>\<^bsub>1\<^esub> \<Longrightarrow> \<beta> \<in> \<aleph>\<^bsub>1\<^esub> \<Longrightarrow> \<alpha><\<beta> \<Longrightarrow> S`\<alpha> \<inter> S`\<beta> = 0" for \<alpha> \<beta> sorry
      then
      have "\<alpha> \<in> \<aleph>\<^bsub>1\<^esub> \<Longrightarrow> \<beta> \<in> \<aleph>\<^bsub>1\<^esub> \<Longrightarrow> \<alpha>\<noteq>\<beta> \<Longrightarrow> S`\<alpha> \<inter> S`\<beta> = 0" for \<alpha> \<beta>
        using lt_neq_symmetry[of "\<aleph>\<^bsub>1\<^esub>" "\<lambda>\<alpha> \<beta>. S`\<alpha> \<inter> S`\<beta> = 0"] Card_is_Ord
        by auto blast
      moreover from this and \<open>\<And>A. A\<in>G \<Longrightarrow> |A| = succ(n)\<close> \<open>S : \<aleph>\<^bsub>1\<^esub> \<rightarrow> G\<close>
      have "S \<in> inj(\<aleph>\<^bsub>1\<^esub>, G)"
        using cardinal_succ_not_0 Int_eq_zero_imp_not_eq[of "\<aleph>\<^bsub>1\<^esub>" "\<lambda>x. S`x"]
        unfolding inj_def by fastforce
      moreover from calculation
      have "range(S) \<approx> \<aleph>\<^bsub>1\<^esub>"
        using inj_bij_range eqpoll_sym unfolding eqpoll_def by fast
      moreover from calculation
      have "range(S) \<subseteq> G"
        using inj_is_fun range_of_function by fast
      ultimately
      show "\<exists>D. D \<subseteq> G \<and> delta_system(D) \<and> D \<approx> \<aleph>\<^bsub>1\<^esub>"
        using inj_is_fun range_eq_image[of S "\<aleph>\<^bsub>1\<^esub>" G]
          image_function[OF fun_is_function, OF inj_is_fun, of S "\<aleph>\<^bsub>1\<^esub>" G]
          domain_of_fun[OF inj_is_fun, of S "\<aleph>\<^bsub>1\<^esub>" G]
        by (rule_tac x="S``\<aleph>\<^bsub>1\<^esub>" in exI) auto
    qed
  qed
  with \<open>G \<subseteq> F\<close>
  show ?thesis by blast
qed

lemma delta_system_uncountable:
  assumes "\<forall>A\<in>F. Finite(A)" "uncountable(F)"
  shows "\<exists>D. D \<subseteq> F \<and> delta_system(D) \<and> D \<approx> \<aleph>\<^bsub>1\<^esub>"
proof -
  from assms
  obtain S where "S \<subseteq> F" "S \<approx> \<aleph>\<^bsub>1\<^esub>"
    using uncountable_imp_subset_eqpoll_aleph1[of F] by auto
  moreover from \<open>\<forall>A\<in>F. Finite(A)\<close> and this
  have "\<forall>A\<in>S. Finite(A)" by auto
  ultimately
  show ?thesis using delta_system_Aleph1[of S]
    by auto
qed

end