theory Delta_System
  imports 
    Konig

begin

lemma mono_mapI: 
  assumes "f: A\<rightarrow>B" "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> <x,y>\<in>r \<Longrightarrow> <f`x,f`y>\<in>s"
  shows   "f \<in> mono_map(A,r,B,s)"
  unfolding mono_map_def using assms by simp

lemma mono_mapD: 
  assumes "f \<in> mono_map(A,r,B,s)"
  shows   "f: A\<rightarrow>B" "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> <x,y>\<in>r \<Longrightarrow> <f`x,f`y>\<in>s"
  using assms unfolding mono_map_def by simp_all

lemmas Aleph_cont = Normal_imp_cont[OF Normal_Aleph]
lemmas Aleph_sup = Normal_Union[OF _ _ Normal_Aleph]

bundle Ord_dests = Limit_is_Ord[dest] Card_is_Ord[dest]
bundle Aleph_dests = Aleph_cont[dest] Aleph_sup[dest]
bundle Aleph_intros = Aleph_mono[intro!]
bundle Aleph_mem_dests = Aleph_mono[OF ltI, THEN ltD, dest]
bundle mono_map_rules =  mono_mapI[intro!] mono_mapD[dest]

context
  includes Ord_dests Aleph_dests Aleph_intros Aleph_mem_dests mono_map_rules
begin

lemma cf_Aleph_Limit:
  assumes "Limit(\<gamma>)"
  shows "cf(\<aleph>\<gamma>) = cf(\<gamma>)" 
proof -
  note \<open>Limit(\<gamma>)\<close>
  moreover from this
  have "(\<lambda>x\<in>\<gamma>. \<aleph>x) : \<gamma> \<rightarrow> \<aleph>\<gamma>" (is "?f : _ \<rightarrow> _")
    using lam_funtype[of _ Aleph] fun_weaken_type[of _ _ _ "\<aleph>\<gamma>"] by blast
  moreover from \<open>Limit(\<gamma>)\<close>
  have "x \<in> y \<Longrightarrow> \<aleph>x \<in> \<aleph>y" if "x \<in> \<gamma>" "y \<in> \<gamma>" for x y
    using that Ord_in_Ord[of \<gamma>] Ord_trans[of _ _ \<gamma>] by blast
  ultimately
  have "?f \<in> mono_map(\<gamma>,Memrel(\<gamma>),\<aleph>\<gamma>, Memrel(\<aleph>\<gamma>))"
    by auto
  with  \<open>Limit(\<gamma>)\<close> 
  have "?f \<in> \<langle>\<gamma>, Memrel(\<gamma>)\<rangle> \<cong> \<langle>?f``\<gamma>, Memrel(\<aleph>\<gamma>)\<rangle>"
    using mono_map_imp_ord_iso_Memrel[of \<gamma> "\<aleph>\<gamma>" ?f] 
      Card_Aleph (* Already an intro rule, but need it explicitly *)
    by blast
  then
  have "converse(?f) \<in> \<langle>?f``\<gamma>, Memrel(\<aleph>\<gamma>)\<rangle> \<cong> \<langle>\<gamma>, Memrel(\<gamma>)\<rangle>"
    using ord_iso_sym by simp
  with \<open>Limit(\<gamma>)\<close>
  have "ordertype(?f``\<gamma>, Memrel(\<aleph>\<gamma>)) = \<gamma>"
    using ordertype_eq[OF _ well_ord_Memrel]
    ordertype_Memrel by auto
  moreover from \<open>Limit(\<gamma>)\<close>
  have "cofinal(?f``\<gamma>, \<aleph>\<gamma>, Memrel(\<aleph>\<gamma>))" 
    unfolding cofinal_def 
  proof (standard, intro ballI)
    fix a
    assume "a\<in>\<aleph>\<gamma>" "\<aleph>\<gamma> = (\<Union>i<\<gamma>. \<aleph>i)"
    moreover from this
    obtain i where "i<\<gamma>" "a\<in>\<aleph>i"
      by auto
    moreover from this and \<open>Limit(\<gamma>)\<close>
    have "Ord(i)" using ltD Ord_in_Ord by blast
    moreover from \<open>Limit(\<gamma>)\<close> and calculation
    have "succ(i) \<in> \<gamma>" using ltD by auto
    moreover from this and \<open>Ord(i)\<close>
    have "\<aleph>i < \<aleph>(succ(i))" 
      by (auto) 
    ultimately
    have "<a,\<aleph>i> \<in> Memrel(\<aleph>\<gamma>)"
      using ltD by (auto dest:Aleph_mono)
    moreover from \<open>i<\<gamma>\<close>
    have "\<aleph>i \<in> ?f``\<gamma>" 
      using ltD apply_in_image[OF \<open>?f : _ \<rightarrow> _\<close>] by auto
    ultimately
    show "\<exists>x\<in>?f `` \<gamma>. \<langle>a, x\<rangle> \<in> Memrel(\<aleph>\<gamma>) \<or> a = x" by blast
  qed
  moreover
  note \<open>?f: \<gamma> \<rightarrow> \<aleph>\<gamma>\<close> \<open>Limit(\<gamma>)\<close>
  ultimately
  show "cf(\<aleph>\<gamma>) =  cf(\<gamma>)"
    using cf_ordertype_cofinal[OF Limit_Aleph Image_sub_codomain, of \<gamma> ?f \<gamma> \<gamma> ] 
      Limit_is_Ord by simp 
qed

end (* includes *)

lemma cardinal_lt_csucc_iff: "Card(K) \<Longrightarrow> |K'| < csucc(K) \<longleftrightarrow> |K'| \<le> K"
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
  find_theorems converse inj
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

lemma nat_lt_aleph1: "nat<\<aleph>1"
  by (simp add: Aleph_def lt_csucc)

lemma zero_lt_aleph1: "0<\<aleph>1"
  by (rule lt_trans[of _ "nat"], auto simp add: ltI nat_lt_aleph1)

lemma le_aleph1_nat: "Card(k) \<Longrightarrow> k<\<aleph>1 \<Longrightarrow> k \<le> nat"    
  by (simp add: Aleph_def  Card_lt_csucc_iff Card_nat)

lemma cof_aleph1_aux: "function(G) \<Longrightarrow> domain(G) \<lesssim> nat \<Longrightarrow> 
   \<forall>n\<in>domain(G). |G`n|<\<aleph>1 \<Longrightarrow> |\<Union>n\<in>domain(G). G`n|\<le>nat"
proof -
  assume "function(G)"
  let ?N="domain(G)" and ?R="\<Union>n\<in>domain(G). G`n"
  assume "?N \<lesssim> nat"
  assume Eq1: "\<forall>n\<in>?N. |G`n|<\<aleph>1"
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

lemma aleph1_eq_cardinal_vimage: "f:\<aleph>1\<rightarrow>nat \<Longrightarrow> \<exists>n\<in>nat. |f-``{n}| = \<aleph>1"
proof -
  assume "f:\<aleph>1\<rightarrow>nat"
  then
  have "function(f)" "domain(f) = \<aleph>1" "range(f)\<subseteq>nat"
    by (simp_all add: domain_of_fun fun_is_function range_of_function)
  let ?G="\<lambda>n\<in>range(f). f-``{n}"
  from \<open>f:\<aleph>1\<rightarrow>nat\<close>
  have "range(f) \<subseteq> nat" by (simp add: range_of_function)
  then
  have "domain(?G) \<lesssim> nat"
    using subset_imp_lepoll by simp
  have "function(?G)" by (simp add:function_lam)
  from \<open>f:\<aleph>1\<rightarrow>nat\<close>
  have "n\<in>nat \<Longrightarrow> f-``{n} \<subseteq> \<aleph>1" for n
    using Pi_vimage_subset by simp
  with \<open>range(f) \<subseteq> nat\<close>
  have "\<aleph>1 = (\<Union>n\<in>range(f). f-``{n})"
  proof (intro equalityI, intro subsetI)
    fix x 
    assume "x \<in> \<aleph>1"
    with \<open>f:\<aleph>1\<rightarrow>nat\<close> \<open>function(f)\<close> \<open>domain(f) = \<aleph>1\<close>
    have "x \<in> f-``{f`x}" "f`x \<in> range(f)" 
      using function_apply_Pair vimage_iff apply_rangeI by simp_all
    then 
    show "x \<in> (\<Union>n\<in>range(f). f-``{n})" by auto
  qed auto
  {
    assume "\<forall>n\<in>range(f). |f-``{n}| < \<aleph>1"
    then 
    have "\<forall>n\<in>domain(?G). |?G`n| < \<aleph>1" 
      using zero_lt_aleph1 by (auto)
    with \<open>function(?G)\<close> \<open>domain(?G) \<lesssim> nat\<close> 
    have "|\<Union>n\<in>domain(?G). ?G`n|\<le>nat"
      using cof_aleph1_aux by (blast del:lepollD)  (* force/auto won't do it here *)
    then 
    have "|\<Union>n\<in>range(f). f-``{n}|\<le>nat" by simp
    with \<open>\<aleph>1 = _\<close>
    have "|\<aleph>1| \<le> nat" by simp
    then 
    have "\<aleph>1 \<le> nat"
      using Card_Aleph Card_cardinal_eq
      by simp
    then 
    have "False"
      using nat_lt_aleph1 by (blast dest:lt_trans2)
  }
  with \<open>range(f)\<subseteq>nat\<close> 
  obtain n where "n\<in>nat" "\<not>(|f -`` {n}| < \<aleph>1)"
    by blast
  moreover from this
  have "\<aleph>1 \<le> |f-``{n}|"
    using not_lt_iff_le Card_is_Ord by auto
  moreover
  note \<open>n\<in>nat \<Longrightarrow> f-``{n} \<subseteq> \<aleph>1\<close>
  ultimately
  show ?thesis
    using subset_imp_le_cardinal[THEN le_anti_sym, of _ "\<aleph>1"]
      Card_Aleph Card_cardinal_eq by auto
qed

lemma eqpoll_aleph1_cardinal_vimage:
  assumes "X \<approx> \<aleph>1" "f : X \<rightarrow> nat"
  shows "\<exists>n\<in>nat. |f-``{n}| = \<aleph>1"
  oops

definition
  delta_system :: "i \<Rightarrow> o" where
  "delta_system(D) \<equiv> \<exists>r. \<forall>A\<in>D. \<forall>B\<in>D. A \<noteq> B \<longrightarrow> A \<inter> B = r"

lemma delta_systemI[intro]: 
  assumes "\<forall>A\<in>D. \<forall>B\<in>D. A \<noteq> B \<longrightarrow> A \<inter> B = r"
  shows "delta_system(D)"
  using assms unfolding delta_system_def by simp

lemma delta_systemD[dest!]:
  "delta_system(D) \<Longrightarrow> \<exists>r. \<forall>A\<in>D. \<forall>B\<in>D. A \<noteq> B \<longrightarrow> A \<inter> B = r"
  unfolding delta_system_def by simp

lemma delta_system_aleph1:
  assumes "\<forall>A\<in>F. Finite(A)" "F \<approx> \<aleph>1"
  shows "\<exists>D. D \<subseteq> F \<and> delta_system(D)"
proof -
  obtain n G where "n\<in>nat" "G \<subseteq> F" "A\<in>F \<Longrightarrow> |A| = n" for A
    sorry
  moreover
  note assms
  ultimately
  show ?thesis
  proof (induct arbitrary:F)
    case 0
    then
    show ?case by auto
  next
    case (succ n)
    show ?case
    proof (cases "\<exists>p. {A\<in>G . p \<in> A} \<approx> \<aleph>1")
      case True
      then
      obtain p where "{A\<in>G . p \<in> A} \<approx> \<aleph>1" by blast
      from succ(1,3-5)
      have "\<forall>A\<in>G. p\<in>A \<longrightarrow> |A - {p}| = n"
        using Finite_imp_succ_cardinal_Diff[of _ p] by force
      with succ
      obtain D where "D\<subseteq>{A-{p} . A\<in>G}" "delta_system(D)"
        by auto
      then
      obtain r where "\<forall>A\<in>D. \<forall>B\<in>D. A \<noteq> B \<longrightarrow> A \<inter> B = r"
        by blast
      then
      show ?thesis by auto
    next
      case False
      moreover from \<open>G\<subseteq>F\<close> \<open>F \<approx> \<aleph>1\<close>
      have "{A \<in> G . p \<in> A} \<lesssim> \<aleph>1" for p
        by (blast intro:lepoll_eq_trans[OF subset_imp_lepoll])
      ultimately
      have "{A \<in> G . p \<in> A} \<prec> \<aleph>1" for p
        unfolding lesspoll_def by simp
      then show ?thesis sorry
    qed
  qed
qed

end