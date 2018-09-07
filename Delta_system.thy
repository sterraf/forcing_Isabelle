theory Delta_system imports Normal Cardinal_AC begin
  
lemma cardinal_lt_csucc_iff: "Card(K) ==> |K'| < csucc(K) \<longleftrightarrow> |K'| \<le> K"
  by (simp add: Card_lt_csucc_iff)
    
lemma cardinal_UN_le_InfCard:
     "[| InfCard(K);  \<And>i. i\<in>K \<Longrightarrow> |X(i)| \<le> K |]
      ==> |\<Union>i\<in>K. X(i)| \<le> K"
proof -
  assume
    "InfCard(K)"
  assume
    Eq1: "i\<in>K \<Longrightarrow> |X(i)| \<le> K" for i
  {
    fix i
    assume
      "i\<in>K"
    with Eq1 have
      "|X(i)| \<le> K" by simp
    with \<open>InfCard(K)\<close> InfCard_is_Card have
      "|X(i)| < csucc(K)"
      using  cardinal_lt_csucc_iff by auto
  }
  with \<open>InfCard(K)\<close>  InfCard_is_Card cardinal_lt_csucc_iff show 
    "|\<Union>i\<in>K. X(i)| \<le> K" 
    using  cardinal_UN_lt_csucc  by (auto)
qed

lemma nat_le_aleph1: "nat<\<aleph>1"
  by (simp add: Aleph_def lt_csucc)

lemma zero_le_aleph1: "0<\<aleph>1"
  by(rule lt_trans[of _ "nat"], auto simp add: ltI nat_le_aleph1)

lemma le_aleph1_nat: "Card(k) \<Longrightarrow> k<\<aleph>1 \<Longrightarrow> k \<le> nat"    
  by (simp add: Aleph_def  Card_lt_csucc_iff Card_nat)

(* Cosas que deberían servir "\<lesssim>" y surj_implies_inj *)
lemma card_le_imp_surj: "|Y| \<le> |X| \<Longrightarrow> \<exists>f. f \<in> surj(X,Y)"
  apply(drule Card_le_imp_lepoll, unfold lepoll_def)
  (* \<questiondown>cómo seguiría? Sea g la inyección. 
     Defino f(x) = THE y . g(y) = x. Pero, qué pasa si x no está
     en la imagen de f?
 *)
  sorry
lemma func_is_function: "f:A\<rightarrow>B \<Longrightarrow> function(f)"
  by (blast intro:fun_is_function)
  
lemma cof_aleph1_aux: "function(G) \<Longrightarrow> domain(G) \<lesssim> nat \<Longrightarrow> 
  \<forall>n\<in>domain(G). |G`n|<\<aleph>1 \<Longrightarrow> |\<Union>n\<in>domain(G). G`n|\<le>nat"
proof -
  assume
    "function(G)"
  let
    ?N="domain(G)"
    and
    ?R="\<Union>n\<in>domain(G). G`n"
  assume
    "?N \<lesssim> nat"
  assume
    Eq1: "\<forall>n\<in>?N. |G`n|<\<aleph>1"
  {
    fix n
    assume 
      "n\<in>?N"
    with Eq1 have
      "|G`n| \<le> nat"
      using le_aleph1_nat by simp
    then have
      "\<exists>F. F\<in>surj(nat,G`n)"
      using card_le_imp_surj Card_nat
      by (force simp add:Card_cardinal_eq)
  }
  then have
    "\<forall>n\<in>?N. \<exists>F. F\<in>surj(nat,G`n)" ..
  {
    with AC_ball_Pi obtain f where
      Eq2: "f\<in>Pi(?N,\<lambda>n. surj(nat,G`n))" by force
    let 
    ?H="\<lambda><n,m>\<in>?N\<times>nat. f`n`m"
    have
      Eq3: "?H:?N\<times>nat \<rightarrow> ?R"
    proof -
      {
        fix n m
        assume 
          "<n,m>\<in>?N\<times>nat"
        then have
          "n\<in>?N" "m\<in>nat" by auto
        with Eq2 have
          "f`n \<in> surj(nat,G`n)"
          using apply_type by (simp)
        with \<open>m\<in>nat\<close> have
          "f`n`m \<in> G`n"
          by (auto simp add:surj_def)
      }
      then have
        "<n,m>\<in>?N\<times>nat \<Longrightarrow> f`n`m \<in> G`n" for n m by simp
      then have 
        "<n,m>\<in>?N\<times>nat \<Longrightarrow> f`n`m \<in> ?R" for n m by auto
      then show ?thesis sorry
    qed
    {
      fix x
      assume 
        "x \<in> ?R" 
      then obtain n where
        "n\<in>?N" "x \<in> G`n"
        by auto
      with Eq2 have
        "f`n \<in> surj(nat,G`n)" by (rule_tac apply_type, simp_all)
      with \<open>x\<in>G`n\<close> \<open>n\<in>?N\<close> obtain m where
        "m\<in>nat" "f`n`m = x"
        using surj_def by auto
      with \<open>n\<in>?N\<close> have
        "\<exists><n,m>\<in>?N\<times>nat. ?H`<n,m> = x" by auto
    }
    then have
      "\<forall>x\<in>?R. \<exists><n,m>\<in>?N\<times>nat. ?H`<n,m> =x" 
      by blast  
    with Eq3 have
      "?H\<in>surj(?N\<times>nat,?R)" 
      using surj_def by auto
    then have
      "\<exists>H. H\<in>surj(?N\<times>nat,?R)"
      by auto
  }
  then have
    Eq4: "|?R| \<le> |?N\<times>nat|"
    using surj_implies_cardinal_le by auto
  from \<open>?N \<lesssim> nat\<close> have
    "?N\<times>nat \<lesssim> nat\<times>nat" 
    using prod_lepoll_mono by simp
  then have
    "|?N\<times>nat| \<le> nat" 
    using lepoll_imp_Card_le InfCard_csquare_eq 
      InfCard_nat cmult_def by force
  with Eq4 show ?thesis   
    by (rule le_trans) (* "by (simp add:le_trans)" takes 15 seconds *)
qed
    
lemma fun_sub : "f:A\<rightarrow>B \<Longrightarrow> f \<subseteq> Sigma(A,\<lambda> _ . B)"
  by(auto simp add: Pi_iff)
  
lemma range_of_function: "f:A\<rightarrow>B \<Longrightarrow> range(f) \<subseteq> B"
  by(rule range_rel_subset,erule fun_sub[of _ "A"])
    
lemma "f:\<aleph>1\<rightarrow>nat \<Longrightarrow> \<exists>n\<in>nat. \<aleph>1 \<le> |f-``{n}|"
proof -
  assume 
    "f:\<aleph>1\<rightarrow>nat"
  then have
    Eq0: "function(f)" "domain(f) = \<aleph>1" "range(f)\<subseteq>nat"
    by (simp_all add: domain_of_fun func_is_function range_of_function)
  let
    ?G="\<lambda>n\<in>range(f). f-``{n}"
  from \<open>f:\<aleph>1\<rightarrow>nat\<close> have
    "range(f) \<subseteq> nat" by (simp add: range_of_function)
  then have
    "domain(?G) \<lesssim> nat"
    using subset_imp_lepoll by simp
  have 
    Eq1: "function(?G)" by (simp add:function_lam)
  have
    "\<aleph>1 \<subseteq> (\<Union>n\<in>range(f). f-``{n})"
  proof
    fix x 
    assume
      "x \<in> \<aleph>1"
    with \<open>f:\<aleph>1\<rightarrow>nat\<close> Eq0 have
      "x \<in> f-``{f`x}" "f`x \<in> range(f)" 
      using function_apply_Pair vimage_iff apply_rangeI by simp_all
    then show
      "x \<in> (\<Union>n\<in>range(f). f-``{n})" by auto
  qed
  then have
    "\<aleph>1 \<lesssim> (\<Union>n\<in>range(f). f-``{n})" 
    using subset_imp_lepoll by simp 
  then have
    Eq2: "|\<aleph>1| \<le> |\<Union>n\<in>range(f). f-``{n}|" 
    by (rule lepoll_imp_Card_le)
  {
    assume
      "\<forall>n\<in>range(f). |f-``{n}| < \<aleph>1"
    with zero_le_aleph1  have
      "\<forall>n\<in>domain(?G). |?G`n| < \<aleph>1" by (auto)
    with Eq1 \<open>domain(?G) \<lesssim> nat\<close> have
      "|\<Union>n\<in>domain(?G). ?G`n|\<le>nat"
      using cof_aleph1_aux by blast (* force/auto won't do it here *)
    then have
      "|\<Union>n\<in>range(f). f-``{n}|\<le>nat"  by simp
    with Eq2 have
      "|\<aleph>1| \<le> nat" by (rule le_trans) 
    then have
      "\<aleph>1 \<le> nat"
      using Aleph_def InfCard_is_Card Card_cardinal_eq Card_csucc by simp
    then have 
      "False"
      using nat_le_aleph1 by (blast dest:lt_trans2)
  }
  then have
    "\<exists>n\<in>range(f). \<not>(|f -`` {n}| < \<aleph>1)"
    by auto
  with \<open>range(f)\<subseteq>nat\<close> show ?thesis
    using not_lt_iff_le Card_is_Ord by auto
qed
    
lemma "|X|=\<aleph>1 \<Longrightarrow> f:X\<rightarrow>nat \<Longrightarrow> \<exists>n\<in>nat. |f-``{n}|=\<aleph>1" 
  oops
end