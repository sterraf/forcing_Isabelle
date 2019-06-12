theory Cofinality 
  imports 
    ZF.Cardinal_AC
    "~~/src/ZF/Constructible/Normal"
begin

definition
  cofinal :: "[i,i,i] \<Rightarrow> o" where
  "cofinal(X,A,r) == \<forall>a\<in>A. \<exists>x\<in>X. <a,x>\<in>r \<or> a = x"

definition
  cofinal_predic :: "[i,i,[i,i]\<Rightarrow>o] \<Rightarrow> o" where
  "cofinal_predic(X,A,r) == \<forall>a\<in>A. \<exists>x\<in>X. r(a,x) \<or> a = x"

definition
  f_cofinal :: "[i\<Rightarrow>i,i,i,i] \<Rightarrow> o" where
  "f_cofinal(f,C,A,r) == \<forall>a\<in>A. \<exists>x\<in>C. <a,f(x)>\<in>r \<or> a = f(x)" (* "predic" version ? *)
  
definition
  cofinal_fun :: "[i,i,i] \<Rightarrow> o" where
  "cofinal_fun(f,A,r) == \<forall>a\<in>A. \<exists>x\<in>domain(f). <a,f`x>\<in>r \<or> a = f`x"

(*
The next definition doesn't work if 0 is the top element of A.
But it works for limit ordinals.
*)

definition
  cofinal_fun' :: "[i,i,i] \<Rightarrow> o" where
  "cofinal_fun'(f,A,r) == f_cofinal(\<lambda>x. f`x,domain(f),A, r)"
  
lemma cofinal_in_cofinal:
  assumes
    "trans(r)" "cofinal(Y,X,r)" "cofinal(X,A,r)" 
  shows 
    "cofinal(Y,A,r)"
  oops

lemma Un_leD1 : "i \<union> j \<le> k \<Longrightarrow> Ord(i) \<Longrightarrow> Ord(j) \<Longrightarrow> Ord(k) \<Longrightarrow> i \<le> k"
  by (rule Un_least_lt_iff[THEN iffD1[THEN conjunct1]],simp_all)
  
lemma Un_leD2 : "i \<union> j \<le> k \<Longrightarrow> Ord(i) \<Longrightarrow> Ord(j) \<Longrightarrow> Ord(k) \<Longrightarrow> j \<le> k"
  by (rule Un_least_lt_iff[THEN iffD1[THEN conjunct2]],simp_all)

lemma Un_memD1: "i \<union> j \<in> k \<Longrightarrow> Ord(i) \<Longrightarrow> Ord(j) \<Longrightarrow> Ord(k) \<Longrightarrow> i \<le> k"
  by (drule ltI, assumption, drule leI, rule Un_least_lt_iff[THEN iffD1[THEN conjunct1]],simp_all)

lemma Un_memD2 : "i \<union> j \<in> k \<Longrightarrow> Ord(i) \<Longrightarrow> Ord(j) \<Longrightarrow> Ord(k) \<Longrightarrow> j \<le> k"
  by (drule ltI, assumption, drule leI, rule Un_least_lt_iff[THEN iffD1[THEN conjunct2]],simp_all)

lemma range_is_cofinal:
  assumes "cofinal_fun(f,A,r)" "f:C \<rightarrow> D"
  shows "cofinal(D,A,r)"
  unfolding cofinal_def
proof 
  fix b 
  assume "b \<in> A"
  moreover from assms
  have "a\<in>A \<Longrightarrow> \<exists>x\<in>domain(f). \<langle>a, f ` x\<rangle> \<in> r \<or> a = f`x" for a
    unfolding cofinal_fun_def by simp
  ultimately
  obtain x where "x\<in>domain(f)" "\<langle>b, f ` x\<rangle> \<in> r \<or> b = f`x" 
    by blast
  moreover from \<open>f:C \<rightarrow> D\<close>  \<open>x\<in>domain(f)\<close>
  have "f`x\<in>D"
    using domain_of_fun apply_rangeI by simp
  ultimately
  show  "\<exists>y\<in>D. \<langle>b, y\<rangle> \<in> r \<or> b = y" by auto
qed

lemma "Limit(A) \<Longrightarrow> cofinal_fun(f,A,Memrel(A)) \<longleftrightarrow> cofinal_fun'(f,A,Memrel(A))"
  oops

definition
  cf :: "i\<Rightarrow>i" where 
  "cf(\<gamma>) == \<mu> \<beta>.  \<exists>A. A\<subseteq>\<gamma> \<and> cofinal(A,\<gamma>,Memrel(\<gamma>)) \<and> \<beta> = ordertype(A,Memrel(\<gamma>))"

lemma Ord_cf [TC]: "Ord(cf(\<beta>))"
  unfolding cf_def using Ord_Least by simp
    
lemma gamma_cofinal_gamma:
  assumes "Ord(\<gamma>)"
  shows "cofinal(\<gamma>,\<gamma>,Memrel(\<gamma>))"
  unfolding cofinal_def by auto
    
lemma cf_is_ordertype:
  assumes "Ord(\<gamma>)"
  shows "\<exists>A. A\<subseteq>\<gamma> \<and> cofinal(A,\<gamma>,Memrel(\<gamma>)) \<and> cf(\<gamma>) = ordertype(A,Memrel(\<gamma>))" 
    (is "?P(cf(\<gamma>))")
  using gamma_cofinal_gamma LeastI[of ?P \<gamma>] ordertype_Memrel[symmetric] assms 
  unfolding cf_def by blast
(*
proof -
  from assms
  have "\<exists>A. A\<subseteq>\<gamma> \<and> cofinal(A,\<gamma>,Memrel(\<gamma>)) \<and> \<gamma> = ordertype(A,Memrel(\<gamma>))"
    using gamma_cofinal_gamma ordertype_Memrel[symmetric] assms by blast
  then
  show ?thesis 
    using LeastI[of ?P] assms unfolding cf_def by simp
qed
*)

lemma cofinal_mono_map_cf:
  assumes "Ord(\<gamma>)"
  shows "\<exists>j \<in> mono_map(cf(\<gamma>),Memrel(cf(\<gamma>)),\<gamma>,Memrel(\<gamma>)) . cofinal_fun(j,\<gamma>,Memrel(\<gamma>))"
  sorry
    
lemma cofinal_fun_succ:
  "Ord(\<beta>) \<Longrightarrow> f:1\<rightarrow>succ(\<beta>) \<Longrightarrow> f`0=\<beta> \<Longrightarrow> cofinal_fun(f,succ(\<beta>),Memrel(succ(\<beta>)))"
  using domain_of_fun unfolding cofinal_fun_def by auto
   
lemma not_0_cofinal:
  "ordertype(A,r) = 0 \<Longrightarrow> \<not>cofinal(A,X,r)"
  (* falta assumption X\<noteq>0 *)
sorry
  
lemma cf_succ:
  assumes "Ord(\<alpha>)" "f:1\<rightarrow>succ(\<alpha>)" "f`0=\<alpha>"
  shows " cf(succ(\<alpha>)) = 1"
proof -
  from assms
  have "cofinal_fun(f,succ(\<alpha>),Memrel(succ(\<alpha>)))" 
    using cofinal_fun_succ unfolding cofinal_fun_def by simp
  from \<open>f:1\<rightarrow>succ(\<alpha>)\<close>
  have "0\<in>domain(f)" using domain_of_fun by simp
  define A where "A={f`0}"
  with \<open>cofinal_fun(f,succ(\<alpha>),Memrel(succ(\<alpha>)))\<close> \<open>0\<in>domain(f)\<close> \<open>f`0=\<alpha>\<close>
  have "cofinal(A,succ(\<alpha>),Memrel(succ(\<alpha>)))" 
    unfolding cofinal_def cofinal_fun_def by simp
  moreover from  \<open>f`0=\<alpha>\<close> \<open>A={f`0}\<close>
  have "A \<subseteq> succ(\<alpha>)" unfolding succ_def  by auto
  moreover from \<open>Ord(\<alpha>)\<close> \<open>A\<subseteq> succ(\<alpha>)\<close>
  have "well_ord(A,Memrel(succ(\<alpha>)))" 
    using Ord_succ well_ord_Memrel  well_ord_subset relation_Memrel by blast
  moreover
  have "\<not>(\<exists>A. A \<subseteq> succ(\<alpha>) \<and> cofinal(A, succ(\<alpha>), Memrel(succ(\<alpha>))) \<and> 0 = ordertype(A, Memrel(succ(\<alpha>))))"
    (is "\<not>?P(0)")
    using not_0_cofinal unfolding cf_def  by auto
  moreover 
  have "1 = ordertype(A,Memrel(succ(\<alpha>)))" 
  proof - 
    from \<open>A={f`0}\<close>
    have "A\<approx>1" using singleton_eqpoll_1 by simp
    with \<open>well_ord(A,Memrel(succ(\<alpha>)))\<close>
    show ?thesis using nat_1I ordertype_eq_n by simp
  qed
  ultimately
  show "cf(succ(\<alpha>)) = 1" using Ord_1  Least_equality[of ?P 1]  
    unfolding cf_def by blast
qed 
      
      
lemma cf_zero:
  "cf(0) = 0"
  unfolding cf_def cofinal_def using 
    ordertype_0 subset_empty_iff Least_le[of _ 0] by auto

lemma mono_map_increasing: 
  "j\<in>mono_map(A,r,B,s) \<Longrightarrow> a\<in>A \<Longrightarrow> c\<in>A \<Longrightarrow> <a,c>\<in>r \<Longrightarrow> <j`a,j`c>\<in>s"
  unfolding mono_map_def by simp

lemma lt_trans [trans]: 
  "a<b \<Longrightarrow> b<c \<Longrightarrow> a<c"
  using Ord_trans unfolding lt_def by blast

lemma Least_antitone:
  assumes 
    "Ord(j)" "P(j)" "\<And>i. P(i) \<Longrightarrow> Q(i)"
  shows
    "(\<mu> i. Q(i)) \<le> (\<mu> i. P(i))"
  using assms LeastI2[of P j Q] Least_le by simp

lemma Least_set_antitone:
  "Ord(j) \<Longrightarrow> j\<in>A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> (\<mu> i. i\<in>B) \<le> (\<mu> i. i\<in>A)"
  using subset_iff by (auto intro:Least_antitone)

lemma le_neq_imp_lt:
  "x\<le>y \<Longrightarrow> x\<noteq>y \<Longrightarrow> x<y"
  using ltD ltI[of x y] le_Ord2
  unfolding succ_def by auto

lemma apply_in_range:
  assumes 
    "Ord(\<gamma>)" " \<gamma>\<noteq>0" "f: A \<rightarrow> \<gamma>"
  shows
    "f`x\<in>\<gamma>"
proof (cases "x\<in>A")
  case True
  from assms \<open>x\<in>A\<close>
  show ?thesis
    using   domain_of_fun apply_rangeI  by simp
next
  case False
  from assms \<open>x\<notin>A\<close>
  show ?thesis
    using apply_0  Ord_0_lt ltD domain_of_fun by auto
qed

lemma inj_to_codomain: 
  assumes 
    "f:A\<rightarrow>B" "f \<in> inj(A,B)"
  shows 
    "f \<in> inj(A,f``A)"
  sorry

lemma mono_map_imp_ord_iso_image:
  assumes 
    "Ord(\<alpha>)" "Ord(\<beta>)" "f\<in>mono_map(\<alpha>,Memrel(\<alpha>),\<beta>,Memrel(\<beta>))"
  shows
    "f \<in> ord_iso(\<alpha>,Memrel(\<alpha>),f``\<alpha>,Memrel(\<beta>))"
  unfolding ord_iso_def
proof (intro CollectI ballI iffI)
  (* Enough to show it's bijective and preserves two ways *)
  from assms
  have "f \<in> inj(\<alpha>,\<beta>)"
    using mono_map_is_inj wf_Memrel wf_imp_wf_on well_ord_is_linear well_ord_Memrel by blast
  moreover from \<open>f\<in>mono_map(_,_,_,_)\<close>
  have "f \<in> surj(\<alpha>,f``\<alpha>)"
    unfolding mono_map_def using surj_image by auto
  ultimately
  show "f \<in> bij(\<alpha>,f``\<alpha>)" 
    unfolding bij_def using inj_is_fun inj_to_codomain by simp
  from \<open>f\<in>mono_map(_,_,_,_)\<close>
  show preserves:"x\<in>\<alpha> \<Longrightarrow> y\<in>\<alpha> \<Longrightarrow> \<langle>x,y\<rangle>\<in>Memrel(\<alpha>) \<Longrightarrow> \<langle>f`x,f`y\<rangle>\<in>Memrel(\<beta>)" for x y    
    unfolding mono_map_def by blast
  show "x\<in>\<alpha> \<Longrightarrow> y\<in>\<alpha> \<Longrightarrow> \<langle>x,y\<rangle>\<in>Memrel(\<alpha>)" if  "\<langle>f`x,f`y\<rangle>\<in>Memrel(\<beta>)" for x y 
  proof 
    {
      assume "x\<notin>y" "x\<in>\<alpha>" "y\<in>\<alpha>"  
      moreover 
      note \<open>\<langle>f`x,f`y\<rangle>\<in>Memrel(\<beta>)\<close> and \<open>Ord(\<alpha>)\<close>
      moreover from calculation 
      have "y = x \<or> y\<in>x" 
        using well_ord_Memrel well_ord_is_linear[of _ "Memrel(\<alpha>)"] unfolding linear_def by blast
      moreover
      note preserves [of y x]
      ultimately
      have "y = x \<or> \<langle>f`y, f`x\<rangle>\<in> Memrel(\<beta>)"  by blast
      with \<open>\<langle>f`x,f`y\<rangle>\<in>Memrel(\<beta>)\<close> \<open>Ord(\<beta>)\<close>
      have "False"
        using trans_Memrel transD[of _ "f`x" "f`y" "f`x"] by (auto elim:mem_irrefl)
    }
    then
    show "x\<in>\<alpha> \<Longrightarrow> y\<in>\<alpha> \<Longrightarrow> x\<in>y" by blast
  qed 
qed

lemma Image_sub_codomain: "f:A\<rightarrow>B \<Longrightarrow> f``C \<subseteq> B"
  using image_subset fun_is_rel[of _ _ "\<lambda>_ . B"] by force

lemma mono_map_ordertype_image:
  assumes 
    "Ord(\<alpha>)" "Ord(\<beta>)" "f\<in>mono_map(\<alpha>,Memrel(\<alpha>),\<beta>,Memrel(\<beta>))"
  shows
    "ordertype(f``\<alpha>,Memrel(\<beta>)) = \<alpha>"
  using assms mono_map_is_fun mono_map_imp_ord_iso_image ordertype_Memrel 
    well_ord_subset Image_sub_codomain[of _ \<alpha>]  ordertype_eq[of f \<alpha> "Memrel(\<alpha>)"] 
    well_ord_Memrel[of \<beta>]  by auto 

lemma ordertype_in_cf_imp_not_cofinal:
  assumes
    "ordertype(A,Memrel(\<gamma>)) \<in> cf(\<gamma>)" 
    "A \<subseteq> \<gamma>" 
  shows
    "\<not> cofinal(A,\<gamma>,Memrel(\<gamma>))"
proof 
  note \<open>A \<subseteq> \<gamma>\<close>
  moreover
  assume "cofinal(A,\<gamma>,Memrel(\<gamma>))"
  ultimately
  have "\<exists>B. B \<subseteq> \<gamma> \<and> cofinal(B, \<gamma>, Memrel(\<gamma>)) \<and>  ordertype(A,Memrel(\<gamma>)) = ordertype(B, Memrel(\<gamma>))"
    (is "?P(ordertype(A,_))")
    by blast
  moreover from assms
  have "ordertype(A,Memrel(\<gamma>)) < cf(\<gamma>)"
    using Ord_cf ltI by blast
  ultimately
  show "False"
    unfolding cf_def using less_LeastE[of ?P  "ordertype(A,Memrel(\<gamma>))"]  
    by auto
qed

lemma range_eq_image: "f:A\<rightarrow>B \<Longrightarrow> range(f) = f``A"
proof
  show "f `` A \<subseteq> range(f)"
    unfolding image_def by blast
  assume "f:A\<rightarrow>B"
  {
    fix x
    assume "x\<in>range(f)"
    have "x\<in>f``A" sorry
  }
  then 
  show "range(f) \<subseteq> f `` A" ..
qed

lemma apply_in_image: "f:A\<rightarrow>B \<Longrightarrow> a\<in>A \<Longrightarrow> f`a \<in> f``A"
  using range_eq_image apply_rangeI[of f]  by simp

lemma
  notes le_imp_subset [dest]
  assumes 
    "Ord(\<delta>)" "Limit(\<gamma>)" "f: \<delta> \<rightarrow> \<gamma>" "cofinal_fun(f,\<gamma>,Memrel(\<gamma>))" 
  shows
    "\<exists>g \<in> mono_map(cf(\<gamma>),Memrel(cf(\<gamma>)),\<delta>,Memrel(\<delta>)).
     f O g \<in> mono_map(cf(\<gamma>),Memrel(cf(\<gamma>)),\<gamma>,Memrel(\<gamma>)) \<and> 
     cofinal_fun(f O g,\<gamma>,Memrel(\<gamma>))"
proof -
  from \<open>Limit(\<gamma>)\<close>
  have "Ord(\<gamma>)" using Limit_is_Ord by simp
  then
  obtain j where "j \<in> mono_map(cf(\<gamma>),Memrel(cf(\<gamma>)),\<gamma>,Memrel(\<gamma>))" "cofinal_fun(j,\<gamma>,Memrel(\<gamma>))"
    using cofinal_mono_map_cf by blast
  then
  have "domain(j) = cf(\<gamma>)" 
    using domain_of_fun mono_map_is_fun by force
  let ?A="\<lambda>\<beta> g. {\<theta> \<in> \<delta>. j`\<beta> \<le> f`\<theta> \<and> (\<forall>\<alpha><\<beta> . f`(g`\<alpha>) < f`\<theta>)} \<union> {\<delta>}"
  define H where "H \<equiv> \<lambda>\<beta> h. \<mu> x. x\<in>?A(\<beta>,h)"
  have "\<beta>\<in>cf(\<gamma>) \<Longrightarrow> \<alpha><\<beta> \<Longrightarrow> ?A(\<beta>,\<lambda>x\<in>\<beta>. G(x)) \<subseteq> ?A(\<alpha>,\<lambda>x\<in>\<alpha>. G(x))" for \<alpha> \<beta> G
  proof -
    assume "\<alpha><\<beta>"
    then 
    have "\<alpha>\<in>\<beta>" using ltD by simp 
    moreover assume "\<beta>\<in>cf(\<gamma>)" 
    moreover from calculation
    have "\<alpha>\<in>cf(\<gamma>)" using Ord_cf Ord_trans by blast
    moreover 
    note \<open>j \<in> mono_map(cf(\<gamma>),Memrel(cf(\<gamma>)),\<gamma>,Memrel(\<gamma>))\<close>
    ultimately 
    have "j`\<alpha> \<in> j`\<beta>" using mono_map_increasing by blast 
    moreover from \<open>j \<in> mono_map(cf(\<gamma>),Memrel(cf(\<gamma>)),\<gamma>,Memrel(\<gamma>))\<close> \<open>\<beta>\<in>cf(\<gamma>)\<close>
    have "j`\<beta>\<in>\<gamma>" 
      using domain_of_fun apply_rangeI mono_map_is_fun by force
    moreover from this and \<open>Limit(\<gamma>)\<close>
    have "Ord(j`\<beta>)"
      using Ord_in_Ord Limit_is_Ord by auto
    ultimately
    have "j`\<alpha> \<le> j`\<beta>"  unfolding lt_def by blast
    then
    have "j`\<beta> \<le> f`\<theta> \<Longrightarrow> j`\<alpha> \<le> f`\<theta>" for \<theta> using le_trans by blast
    moreover
    have "f`((\<lambda>w\<in>\<alpha>. G(w))`y) < f`z" if "z\<in>\<delta>" "\<forall>x<\<beta>. f`((\<lambda>w\<in>\<beta>. G(w))`x) < f`z" "y<\<alpha>" for y z
    proof -
      note \<open>y<\<alpha>\<close> 
      also
      note \<open>\<alpha><\<beta>\<close>
      finally
      have "y<\<beta>" by simp
      with \<open>\<forall>x<\<beta>. f`((\<lambda>w\<in>\<beta>. G(w))`x) < f`z\<close>
      have "f ` ((\<lambda>w\<in>\<beta>. G(w)) ` y) < f ` z" by simp
      moreover from \<open>y<\<alpha>\<close> \<open>y<\<beta>\<close>
      have "(\<lambda>w\<in>\<beta>. G(w)) ` y = (\<lambda>w\<in>\<alpha>. G(w)) ` y" 
        using beta_if  by (auto dest:ltD)
      ultimately show ?thesis by simp
    qed
    ultimately
    show ?thesis by blast
  qed
  with \<open>Ord(\<delta>)\<close>
  have H_mono: "\<beta>\<in>cf(\<gamma>) \<Longrightarrow> \<alpha><\<beta> \<Longrightarrow> H(\<alpha>,\<lambda>x\<in>\<alpha>. G(x)) \<le> H(\<beta>,\<lambda>x\<in>\<beta>. G(x))" for \<alpha> \<beta> G
    unfolding H_def using Least_set_antitone[of \<delta> "?A(\<beta>,\<lambda>x\<in>\<beta>. G(x))" "?A(\<alpha>,\<lambda>x\<in>\<alpha>. G(x))"] 
    by simp
  define G where "G \<equiv> \<lambda>\<beta>. transrec(\<beta>,H)"
  then 
  have G_def':"\<And>x. G(x) \<equiv> transrec(x,H)" using G_def by simp
  have G_rec:"G(\<alpha>) = H(\<alpha>, \<lambda>x\<in>\<alpha>. G(x))" for \<alpha>
    using def_transrec[OF G_def'] .
  have "G(\<alpha>) \<in> ?A(\<alpha>,\<lambda>x\<in>\<alpha>. G(x))" for \<alpha>
  proof -
    note \<open>G(\<alpha>) = H(\<alpha>, \<lambda>x\<in>\<alpha>. G(x))\<close>
    also from \<open>Ord(\<delta>)\<close>
    have "H(\<alpha>, \<lambda>x\<in>\<alpha>. G(x)) \<in> ?A(\<alpha>,\<lambda>x\<in>\<alpha>. G(x))"
      unfolding H_def using  LeastI[of "\<lambda>y. y\<in>?A(\<alpha>,\<lambda>x\<in>\<alpha>. G(x))" \<delta>] by simp
    finally 
    show ?thesis by simp
  qed
  with \<open>Ord(\<delta>)\<close>  
  have "Ord(G(\<alpha>))" for \<alpha>
    using Ord_in_Ord by auto
  have "G(\<alpha>) \<le> G(\<beta>)" if "\<beta>\<in>cf(\<gamma>)" "\<alpha><\<beta>" "G(\<alpha>)\<noteq>\<delta>" "G(\<beta>)\<noteq>\<delta>" for \<alpha> \<beta>
  proof -
    note \<open>G(\<alpha>) = H(\<alpha>, \<lambda>x\<in>\<alpha>. G(x))\<close> 
    also from that and H_mono
    have "H(\<alpha>, \<lambda>x\<in>\<alpha>. G(x)) \<le> H(\<beta>, \<lambda>x\<in>\<beta>. G(x))" 
      by simp
    also
    have "H(\<beta>, \<lambda>x\<in>\<beta>. G(x)) = G(\<beta>)" 
      using def_transrec[OF G_def', symmetric] .
    finally show ?thesis .
  qed
  moreover 
  have fg_monot:"f`G(\<alpha>) < f`G(\<beta>)" if "\<beta>\<in>cf(\<gamma>)" "\<alpha><\<beta>" "G(\<beta>)\<noteq>\<delta>"  for \<alpha> \<beta>
  proof -
    from \<open>G(\<beta>) = H(\<beta>, \<lambda>x\<in>\<beta>. G(x))\<close> \<open>Ord(\<delta>)\<close> and that 
    have "f ` ((\<lambda>x\<in>\<beta>. G(x)) ` \<alpha>) < f ` G(\<beta>)"
      unfolding H_def using  LeastI[of "\<lambda>y. y\<in>?A(\<beta>,\<lambda>x\<in>\<beta>. G(x))"] 
      by (auto simp del:beta_if)
    with \<open>\<alpha><\<beta>\<close>
    show ?thesis using ltD by auto
  qed
  moreover 
  note \<open>\<And>\<beta>. Ord(G(\<beta>))\<close>
  ultimately 
  have "G(\<alpha>)<G(\<beta>)" if "\<beta>\<in>cf(\<gamma>)" "\<alpha><\<beta>" "G(\<alpha>)\<noteq>\<delta>" "G(\<beta>)\<noteq>\<delta>" for \<alpha> \<beta> 
    using that by (force intro:le_neq_imp_lt)
  then
  have monot:"G(\<alpha>)\<in>G(\<beta>)" if "\<beta>\<in>cf(\<gamma>)" "\<alpha><\<beta>" "G(\<alpha>)\<noteq>\<delta>" "G(\<beta>)\<noteq>\<delta>" for \<alpha> \<beta> 
    using that and ltD by simp
  have G_not_delta: "G(\<beta>)\<noteq>\<delta>" if "\<beta> \<in> cf(\<gamma>)" for \<beta> 
  proof (induct \<beta> rule:Ord_induct[OF _ Ord_cf[of \<gamma>]])
    (* Induction on cf(\<gamma>) *)
    case 1 with that show ?case .
  next
    case (2 \<beta>)
    define h where "h \<equiv> \<lambda>x\<in>\<beta>. f`G(x)"
    then
    have "h \<in> mono_map(\<beta>,Memrel(\<beta>),\<gamma>,Memrel(\<gamma>))" sorry
    with \<open>\<beta>\<in>cf(\<gamma>)\<close> \<open>Ord(\<gamma>)\<close> 
    have "ordertype(h``\<beta>,Memrel(\<gamma>)) = \<beta>" (* Maybe should use range(h) *)
      using mono_map_ordertype_image[of \<beta>] Ord_cf Ord_in_Ord by blast
    also
    note \<open>\<beta> \<in>cf(\<gamma>)\<close>
    finally
    have "ordertype(h``\<beta>,Memrel(\<gamma>)) \<in> cf(\<gamma>)" by simp
    moreover 
    have "h``\<beta> \<subseteq> \<gamma>" sorry
    ultimately
    have "\<not> cofinal(h``\<beta>,\<gamma>,Memrel(\<gamma>))"
      using ordertype_in_cf_imp_not_cofinal by simp
    then
    obtain \<alpha>_0 where "\<alpha>_0\<in>\<gamma>" "\<forall>x\<in>h `` \<beta>. \<not> \<langle>\<alpha>_0, x\<rangle> \<in> Memrel(\<gamma>) \<and> \<alpha>_0 \<noteq> x"
      unfolding cofinal_def by auto
    with \<open>Ord(\<gamma>)\<close> \<open>h``\<beta> \<subseteq> \<gamma>\<close>
    have "\<forall>x\<in>h `` \<beta>. x \<in> \<alpha>_0"
      using well_ord_Memrel[of \<gamma>] well_ord_is_linear[of \<gamma> "Memrel(\<gamma>)"] 
      unfolding linear_def by blast
    from \<open>\<alpha>_0 \<in> \<gamma>\<close> \<open>j \<in> mono_map(_,_,\<gamma>,_)\<close> \<open>Ord(\<gamma>)\<close>
    have "j`\<beta> \<in> \<gamma>"
      using mono_map_is_fun apply_in_range by force 
    with \<open>\<alpha>_0 \<in> \<gamma>\<close> \<open>Ord(\<gamma>)\<close>
    have "\<alpha>_0 \<union> j`\<beta> \<in> \<gamma>"
      using Un_least_mem_iff Ord_in_Ord by auto
    with \<open>cofinal_fun(f,\<gamma>,_)\<close> 
    obtain \<theta> where "\<theta>\<in>domain(f)" "\<langle>\<alpha>_0 \<union> j`\<beta>, f ` \<theta>\<rangle> \<in> Memrel(\<gamma>) \<or>  \<alpha>_0 \<union> j`\<beta>= f ` \<theta>"
      unfolding cofinal_fun_def by blast
    moreover from this and \<open>f:\<delta>\<rightarrow>\<gamma>\<close>
    have "\<theta> \<in> \<delta>" using domain_of_fun by auto
    moreover
    note \<open>Ord(\<gamma>)\<close>
    moreover from this and \<open>f:\<delta>\<rightarrow>\<gamma>\<close>  \<open>\<alpha>_0 \<in> \<gamma>\<close>
    have "Ord(f`\<theta>)"
      using apply_in_range Ord_in_Ord by blast
    moreover from calculation and \<open>\<alpha>_0 \<in> \<gamma>\<close> and \<open>Ord(\<delta>)\<close> and \<open>j`\<beta> \<in> \<gamma>\<close>
    have "Ord(\<alpha>_0)" "Ord(j`\<beta>)" "Ord(\<theta>)"
      using Ord_in_Ord by auto
    moreover from  \<open>\<forall>x\<in>h `` \<beta>. x \<in> \<alpha>_0\<close> \<open>Ord(\<alpha>_0)\<close> \<open>_ \<or> (\<alpha>_0 \<union> _= f`\<theta>)\<close>
    have "x\<in>\<beta> \<Longrightarrow> h`x < f`\<theta>" for x
      using ltI lam_funtype[of h] apply (auto dest:Un_memD2 Un_leD2[OF le_eqI])
      sorry
    ultimately
    have "\<theta> \<in> ?A(\<beta>,\<lambda>x\<in>\<beta>. G(x))"
      unfolding h_def using ltD by (auto dest:Un_memD2 Un_leD2[OF le_eqI])
    with \<open>Ord(\<theta>)\<close> \<open>G(\<beta>) = H(\<beta>, \<lambda>x\<in>\<beta>. G(x))\<close>
    have "G(\<beta>) \<le> \<theta>"
      unfolding H_def using Least_le by auto
    with \<open>\<theta>\<in>\<delta>\<close> \<open>Ord(\<delta>)\<close>
    have "G(\<beta>) \<in> \<delta>" sorry
    then
    show ?case by (auto elim:mem_irrefl)
  qed 
  with \<open>Ord(\<delta>)\<close> \<open>\<And>\<alpha>. G(\<alpha>) \<in> ?A(\<alpha>,\<lambda>x\<in>\<alpha>. G(x))\<close> 
  have in_delta:"\<beta> \<in> cf(\<gamma>) \<Longrightarrow> G(\<beta>)\<in>\<delta>" for \<beta> 
    using Ord_cf by auto 
  let ?g="\<lambda>\<beta>\<in>cf(\<gamma>) . G(\<beta>)"
  from \<open>Ord(\<gamma>)\<close> \<open>Ord(\<delta>)\<close> in_delta G_not_delta
  have "?g : cf(\<gamma>) -> \<delta>"
    using ltI lam_type by simp
  then have "?g \<in> mono_map(cf(\<gamma>), Memrel(cf(\<gamma>)), \<delta>, Memrel(\<delta>))"
    unfolding mono_map_def 
  proof (intro CollectI ballI impI) 
    (* Proof that ?g respects membership *)
    fix \<alpha> \<beta> 
    assume 
      "\<alpha>\<in>cf(\<gamma>)" "\<beta>\<in>cf(\<gamma>)" 
    with G_not_delta 
    have "G(\<alpha>)\<noteq>\<delta>" "G(\<beta>)\<noteq>\<delta>" "Ord(\<beta>)" 
      using Ord_in_Ord Ord_cf by auto
    moreover
    assume "\<langle>\<alpha>, \<beta>\<rangle> \<in> Memrel(cf(\<gamma>))"
    ultimately
    show "\<langle>?g ` \<alpha>, ?g ` \<beta>\<rangle> \<in> Memrel(\<delta>)" 
      using ltI monot in_delta by auto 
  qed
  moreover from \<open>?g : cf(\<gamma>) \<rightarrow> \<delta>\<close> \<open>f: \<delta> \<rightarrow> \<gamma>\<close>
  have fg_mono_map: "f O ?g \<in> mono_map(cf(\<gamma>), Memrel(cf(\<gamma>)), \<gamma>, Memrel(\<gamma>))" 
     unfolding mono_map_def 
  proof (intro CollectI ballI impI comp_fun[of _ _ \<delta>]) 
    (* Proof that f O ?g respects membership *)
    fix \<alpha> \<beta> 
    assume "\<langle>\<alpha>, \<beta>\<rangle> \<in> Memrel(cf(\<gamma>))"
    then
    have "\<alpha><\<beta>"
      using Ord_in_Ord[of "cf(\<gamma>)"] ltI Ord_cf by blast
    assume
      "\<alpha>\<in>cf(\<gamma>)" "\<beta>\<in>cf(\<gamma>)"   
    moreover from this and G_not_delta  
    have "G(\<alpha>)\<noteq>\<delta>" "G(\<beta>)\<noteq>\<delta>" using Ord_cf by auto
    moreover
    note \<open>\<beta> \<in> cf(\<gamma>) \<Longrightarrow> \<alpha> < \<beta> \<Longrightarrow> G(\<beta>) \<noteq> \<delta> \<Longrightarrow> f ` G(\<alpha>) < f ` G(\<beta>)\<close>
    moreover 
    note \<open>f: \<delta> \<rightarrow> \<gamma>\<close> \<open>\<alpha><\<beta>\<close> \<open>Limit(\<gamma>)\<close> \<open>Ord(\<gamma>)\<close> \<open>?g : cf(\<gamma>) \<rightarrow> \<delta>\<close>
    ultimately
    show "\<langle>(f O ?g) ` \<alpha>, (f O ?g) ` \<beta>\<rangle> \<in> Memrel(\<gamma>)"
      using ltD[of "f ` G(\<alpha>)" "f ` G(\<beta>)"] apply_in_range by auto
  qed
  moreover
  have "cofinal_fun(f O ?g, \<gamma>, Memrel(\<gamma>))" 
  proof -
    {    
      fix a
      assume "a \<in> \<gamma>"
      with \<open>cofinal_fun(j,\<gamma>,Memrel(\<gamma>))\<close> \<open>domain(j) = cf(\<gamma>)\<close>
      obtain x where "x\<in>cf(\<gamma>)" "a \<in> j`x \<or> a = j`x"
        unfolding cofinal_fun_def by auto
      with fg_mono_map
      have "x \<in> domain(f O ?g)" 
        using mono_map_is_fun domain_of_fun by force
      moreover
      have "a \<in> (f O ?g) `x \<or> a = (f O ?g) `x"
      proof -
        from \<open>x\<in>cf(\<gamma>)\<close> \<open>G(x) \<in> ?A(x,\<lambda>y\<in>x. G(y))\<close> \<open>x \<in> cf(\<gamma>) \<Longrightarrow> G(x)\<in>\<delta>\<close>
        have "j ` x \<le> f ` G(x)" 
          using mem_not_refl by auto
        with \<open>a \<in> j`x \<or> a = j`x\<close>
        have "a \<in> f ` G(x) \<or> a = f ` G(x)" 
          using ltD by blast
        with \<open>x\<in>cf(\<gamma>)\<close>
        show ?thesis using lam_funtype[of "cf(\<gamma>)" G] by auto
      qed
      moreover
      note \<open>a \<in> \<gamma>\<close>
      moreover from calculation and fg_mono_map and \<open>Ord(\<gamma>)\<close> \<open>Limit(\<gamma>)\<close>
      have "(f O ?g) `x \<in> \<gamma>"
        using Limit_nonzero apply_in_range mono_map_is_fun[of "f O ?g" ] by blast
      ultimately
      have "\<exists>x \<in> domain(f O ?g). \<langle>a, (f O ?g) ` x\<rangle> \<in> Memrel(\<gamma>) \<or> a = (f O ?g) `x"
        by blast
    }
    then show ?thesis unfolding cofinal_fun_def by blast
  qed
  ultimately show ?thesis by blast
qed

lemma 
  assumes 
    "Ord(\<delta>)" "Ord(\<gamma>)" "function(f)" "domain(f) = \<delta>" "cofinal_fun(f,\<gamma>,Memrel(\<gamma>))" 
  shows
    "cf(\<gamma>)\<le>\<delta>"
    (* Perhaps consider three cases on \<gamma>, using cf_zero and cf_succ *)
  oops
    
locale cofinality =
  assumes 
    (* Better with f_cofinal(f,\<delta>,\<gamma>,Memrel(\<gamma>)) ? *)
    cota : "Ord(\<delta>) \<Longrightarrow> Ord(\<gamma>) \<Longrightarrow> function(f) \<Longrightarrow> domain(f) = \<delta> \<Longrightarrow>
            cofinal_fun(f,\<gamma>,Memrel(\<gamma>)) \<Longrightarrow> cf(\<gamma>)\<le>\<delta>"
    and idemp: "Ord(\<gamma>) \<Longrightarrow> A\<subseteq>\<gamma> \<Longrightarrow> cofinal(A,\<gamma>,Memrel(\<gamma>)) \<Longrightarrow> 
                cf(\<gamma>) = cf(ordertype(A,Memrel(\<gamma>)))"
    (* Is it better?? 
    and idemp': "Limit(\<gamma>) \<Longrightarrow> A\<subseteq>\<gamma> \<Longrightarrow> cofinal_predic(A,\<gamma>,mem) \<Longrightarrow> 
                cf(\<gamma>) = cf(ordertype(A,Memrel(\<gamma>)))" *)
    
begin
(* probar 5.12 y 5.13(1,2) *)
  
lemma cf_indemp:
  assumes "Ord(\<gamma>)"
  shows "cf(\<gamma>) = cf(cf(\<gamma>))"  
proof -
  from assms
  obtain A where "A\<subseteq>\<gamma>" "cofinal(A,\<gamma>,Memrel(\<gamma>))" "cf(\<gamma>) = ordertype(A,Memrel(\<gamma>))"
    using cf_is_ordertype by blast
  with assms
  have "cf(\<gamma>) = cf(ordertype(A,Memrel(\<gamma>)))" using idemp by simp
  also 
  have "... = cf(cf(\<gamma>))" 
    using \<open>cf(\<gamma>) = ordertype(A,Memrel(\<gamma>))\<close> by simp
  finally
  show "cf(\<gamma>) = cf(cf(\<gamma>))"  .
qed
  
lemma surjection_is_cofinal:
  assumes
    "Ord(\<gamma>)" "Ord(\<delta>)" "f \<in> surj(\<delta>,\<gamma>)"
  shows "cofinal_fun(f,\<gamma>,Memrel(\<gamma>))"
  unfolding cofinal_fun_def
proof 
  fix a
  assume "a\<in>\<gamma>"
  with assms
  obtain x where "x\<in>\<delta>" "f`x = a" 
    unfolding surj_def  by blast
  oops
   
    
lemma cf_le_cardinal:
  assumes "Limit(\<gamma>)"
  shows "cf(\<gamma>) \<le> |\<gamma>|"
  sorry

lemma regular_is_cardinal:
  notes le_imp_subset [dest]
  assumes "Limit(\<gamma>)" "\<gamma> = cf(\<gamma>)"
  shows "Card(\<gamma>)"
proof -
  from assms
  have "|\<gamma>| \<subseteq> \<gamma>" 
    using Limit_is_Ord Ord_cardinal_le by blast
  also from \<open>\<gamma> = cf(\<gamma>)\<close>
  have "\<gamma> \<subseteq> cf(\<gamma>)" by simp
  finally
  have "|\<gamma>| \<subseteq> cf(\<gamma>)" .
  with assms
  show ?thesis unfolding Card_def using cf_le_cardinal by force     
qed 
    
end (* cofinality *)
    
end