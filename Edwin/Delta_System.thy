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

lemma cardinal_UN_le_InfCard:
  assumes "InfCard(K)" "\<And>i. i\<in>K \<Longrightarrow> |X(i)| \<le> K"
  shows "|\<Union>i\<in>K. X(i)| \<le> K"
proof -
  {
    fix i
    assume "i\<in>K"
    with assms
    have "|X(i)| \<le> K" by simp
    with \<open>InfCard(K)\<close>
    have "|X(i)| < csucc(K)"
      using cardinal_lt_csucc_iff InfCard_is_Card by auto
  }
  with \<open>InfCard(K)\<close> 
  show "|\<Union>i\<in>K. X(i)| \<le> K"
    using cardinal_UN_lt_csucc  InfCard_is_Card cardinal_lt_csucc_iff 
    by (auto)
qed

lemma cardinal_UN_le_nat:
  "(\<And>i. i\<in>nat \<Longrightarrow> |X(i)| \<le> nat) \<Longrightarrow> |\<Union>i\<in>nat. X(i)| \<le> nat"
  by (simp add: cardinal_UN_le_InfCard InfCard_nat) 

lemma leqpoll_UN_le_InfCard:
  "InfCard(K) \<Longrightarrow> J \<lesssim> K \<Longrightarrow>  (\<And>i. i\<in>J \<Longrightarrow> |X(i)| \<le> K) 
  \<Longrightarrow> |\<Union>i\<in>J. X(i)| \<le> K"
  sorry

lemma nat_le_aleph1: "nat<\<aleph>1"
  by (simp add: Aleph_def lt_csucc)

lemma zero_le_aleph1: "0<\<aleph>1"
  by (rule lt_trans[of _ "nat"], auto simp add: ltI nat_le_aleph1)

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
    using InfCard_nat leqpoll_UN_le_InfCard by simp
qed

lemma "f:\<aleph>1\<rightarrow>nat \<Longrightarrow> \<exists>n\<in>nat. \<aleph>1 \<le> |f-``{n}|"
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
  have "\<aleph>1 \<subseteq> (\<Union>n\<in>range(f). f-``{n})"
  proof
    fix x 
    assume "x \<in> \<aleph>1"
    with \<open>f:\<aleph>1\<rightarrow>nat\<close> \<open>function(f)\<close> \<open>domain(f) = \<aleph>1\<close>
    have "x \<in> f-``{f`x}" "f`x \<in> range(f)" 
      using function_apply_Pair vimage_iff apply_rangeI by simp_all
    then 
    show "x \<in> (\<Union>n\<in>range(f). f-``{n})" by auto
  qed
  then
  have "\<aleph>1 \<lesssim> (\<Union>n\<in>range(f). f-``{n})"
    using subset_imp_lepoll by simp 
  then 
  have "|\<aleph>1| \<le> |\<Union>n\<in>range(f). f-``{n}|" 
    by (rule lepoll_imp_Card_le)
  {
    assume "\<forall>n\<in>range(f). |f-``{n}| < \<aleph>1"
    then 
    have "\<forall>n\<in>domain(?G). |?G`n| < \<aleph>1" 
      using zero_le_aleph1 by (auto)
    with \<open>function(?G)\<close> \<open>domain(?G) \<lesssim> nat\<close> 
    have "|\<Union>n\<in>domain(?G). ?G`n|\<le>nat"
      using cof_aleph1_aux by (blast del:lepollD)  (* force/auto won't do it here *)
    then 
    have "|\<Union>n\<in>range(f). f-``{n}|\<le>nat" by simp
    with \<open>|\<aleph>1| \<le> _\<close> 
    have "|\<aleph>1| \<le> nat" by (rule le_trans) 
    then 
    have "\<aleph>1 \<le> nat"
      using Aleph_def InfCard_is_Card Card_cardinal_eq Card_csucc by simp
    then 
    have "False"
      using nat_le_aleph1 by (blast dest:lt_trans2)
  }
  then 
  have "\<exists>n\<in>range(f). \<not>(|f -`` {n}| < \<aleph>1)"
    by auto
  with \<open>range(f)\<subseteq>nat\<close> 
  show ?thesis
    using not_lt_iff_le Card_is_Ord by auto
qed

lemma "|X|=\<aleph>1 \<Longrightarrow> f:X\<rightarrow>nat \<Longrightarrow> \<exists>n\<in>nat. |f-``{n}|=\<aleph>1" 
  oops

end