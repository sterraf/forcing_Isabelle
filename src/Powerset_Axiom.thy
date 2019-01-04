theory Powerset_Axiom 
  imports Separation_Axiom Pairing_Axiom Union_Axiom 
begin
  

definition 
  perm_pow :: "i" where
  "perm_pow == {<0,3>,<1,4>,<2,5>,<3,0>,<4,1>,<5,6>}" 

lemma perm_pow_ftc : "perm_pow \<in> 6 -||> 7"
  by(unfold perm_pow_def,(rule consI,auto)+,rule emptyI)

lemma dom_perm_pow : "domain(perm_pow) = 6"     
  by(unfold perm_pow_def,auto)
  
lemma perm_pow_tc : "perm_pow \<in> 6 \<rightarrow> 7"
  by(subst dom_perm_pow[symmetric],rule FiniteFun_is_fun,rule perm_pow_ftc)

lemma perm_pow_env : 
  "{p,q,r,s,t,u,v} \<subseteq> A \<Longrightarrow> j<6 \<Longrightarrow>
  nth(j,[s,t,u,p,q,v]) = nth(perm_pow`j,[p,q,r,s,t,u,v])"
  apply(subgoal_tac "j\<in>nat")
  apply(rule natE,simp,subst apply_fun,rule perm_pow_tc,simp add:perm_pow_def,simp_all)+
  apply(subst apply_fun,rule perm_pow_tc,simp add:perm_pow_def,simp_all,drule ltD,auto)
  done
  
  
lemma (in M_trivial) powerset_subset_Pow:
  assumes 
    "powerset(M,x,y)" "\<And>z. z\<in>y \<Longrightarrow> M(z)"
  shows 
    "y \<subseteq> Pow(x)"
  using assms unfolding powerset_def
  by (auto)
    
lemma (in M_trivial) powerset_abs: 
  assumes
    "M(x)" "\<And>z. z\<in>y \<Longrightarrow> M(z)"
  shows
    "powerset(M,x,y) \<longleftrightarrow> y = {a\<in>Pow(x) . M(a)}"
proof (intro iffI equalityI)
  (* First show the converse implication by double inclusion *)
  assume 
    "powerset(M,x,y)"
  with assms have
    "y \<subseteq> Pow(x)" 
    using powerset_subset_Pow by simp
  with assms show
    "y \<subseteq> {a\<in>Pow(x) . M(a)}"
    by blast
  {
    fix a
    assume 
      "a \<subseteq> x" "M(a)"
    then have 
      "subset(M,a,x)" by simp
    with \<open>M(a)\<close> \<open>powerset(M,x,y)\<close> have
      "a \<in> y"
      unfolding powerset_def by simp
  }
  then show 
    "{a\<in>Pow(x) . M(a)} \<subseteq> y"
    by auto
next (* we show the direct implication *)
  assume 
    "y = {a \<in> Pow(x) . M(a)}"
  then show
    "powerset(M, x, y)"
    unfolding powerset_def
    by simp
qed
  
lemma Collect_inter_Transset:
  assumes 
    "Transset(M)" "b \<in> M"
  shows
    "{x\<in>b . P(x)} = {x\<in>b . P(x)} \<inter> M"
    using assms unfolding Transset_def
  by (auto)  

context G_generic begin
    
lemma name_components_in_M:
  assumes "<\<sigma>,p>\<in>\<theta>" "\<theta> \<in> M"
  shows   "\<sigma>\<in>M" "p\<in>M"
proof -
  from assms obtain a where
    "\<sigma> \<in> a" "p \<in> a" "a\<in><\<sigma>,p>"
    unfolding Pair_def by auto
  moreover from assms have
    "<\<sigma>,p>\<in>M"
    using trans_M  Transset_intf[of _ "<\<sigma>,p>"] by simp
  moreover from calculation have
    "a\<in>M" 
    using trans_M  Transset_intf[of _ _ "<\<sigma>,p>"] by simp
  ultimately show
    "\<sigma>\<in>M" "p\<in>M" 
    using trans_M  Transset_intf[of _ _ "a"] by simp_all
qed

lemma sats_fst_snd_in_M:
  assumes 
    "A\<in>M" "B\<in>M" "\<phi> \<in> formula" "p\<in>M" "l\<in>M" "o\<in>M" "\<chi>\<in>M"
    "arity(\<phi>) \<le> 6"
  shows
    "{sq \<in>A\<times>B . sats(M,\<phi>,[p,l,o,snd(sq),fst(sq),\<chi>])} \<in> M" 
    (is "?\<theta> \<in> M")
proof -
  have "6\<in>nat" "7\<in>nat" by simp_all
  define \<phi>' where "\<phi>'\<equiv>ren(\<phi>)`6`7`perm_pow"
  from \<open>A\<in>M\<close> \<open>B\<in>M\<close> have
    "A\<times>B \<in> M" 
    using cartprod_closed by simp
  from  \<open>arity(\<phi>) \<le> 6\<close> \<open>\<phi>\<in> formula\<close> have
    "\<phi>' \<in> formula" "arity(\<phi>')\<le>7" 
    using \<phi>'_def perm_pow_tc ren_arity[of \<phi> 6 7 perm_pow] nat_simp_union ren_tc by simp_all
  then have
     "arity(And(pair_fm(0,1,2),\<phi>'))\<le>7" (is "?ar \<le> _")
    unfolding pair_fm_def upair_fm_def using nat_simp_union by auto
  then have 
    "arity(Exists(And(pair_fm(0,1,2),\<phi>')))\<le>6" 
    using pred_le[OF _ _ \<open>?ar \<le>7\<close>] arity_type \<open>\<phi>' \<in> formula\<close> by auto
  then have
    1: "arity(Exists(Exists(And(pair_fm(0,1,2),\<phi>'))))\<le>5"     (is "arity(?\<psi>)\<le>5")
    using pred_le[of _ 5] arity_type \<open>\<phi>' \<in> formula\<close> by auto  
    {
    fix sp
    let ?env="[p,l,o,snd(sp),fst(sp),\<chi>]"
    let ?new_env="[fst(sp), snd(sp), sp, p, l, o, \<chi>]"
    note \<open>A\<times>B \<in> M\<close>
    moreover assume 
      "sp \<in> A\<times>B"
    moreover from calculation have
      "fst(sp) \<in> A" "snd(sp) \<in> B"
      using fst_type snd_type by simp_all
    ultimately have 
      "sp \<in> M" "fst(sp) \<in> M" "snd(sp) \<in> M" 
      using  \<open>A\<in>M\<close> \<open>B\<in>M\<close> 
      by (simp_all add: trans_M Transset_intf)    
    then have "?env \<in> list(M)" "?new_env\<in>list(M)" using assms by simp_all
    note
      inM =  \<open>A\<in>M\<close> \<open>B\<in>M\<close> \<open>p\<in>M\<close> \<open>l\<in>M\<close> \<open>o\<in>M\<close> \<open>\<chi>\<in>M\<close>
             \<open>sp\<in>M\<close> \<open>fst(sp)\<in>M\<close> \<open>snd(sp)\<in>M\<close> 
    from 1 zero_in_M assms \<open>sp \<in> M\<close> \<open>\<phi>' \<in> formula\<close> have
      "sats(M,?\<psi>,[sp,p,l,o,\<chi>]@[0]) \<longleftrightarrow> sats(M,?\<psi>,[sp,p,l,o,\<chi>])"
      by (rule_tac arity_sats_iff,simp_all)
    also from inM have 
      "... \<longleftrightarrow> (\<exists> u\<in>M. \<exists>v\<in>M . sats(M,And(pair_fm(0,1,2),\<phi>'),[v,u,sp,p,l,o,\<chi>]))" 
      by simp
    also from inM have 
      "... \<longleftrightarrow> sats(M,\<phi>',[fst(sp),snd(sp),sp,p,l,o,\<chi>]) \<and> sp=<fst(sp),snd(sp)>"
      by force
    also from inM \<open>sp \<in> A\<times>B\<close> have 
      "... \<longleftrightarrow> sats(M,\<phi>',[fst(sp),snd(sp),sp,p,l,o,\<chi>])"
      using Pair_fst_snd_eq by force
    also have
      " ... \<longleftrightarrow> sats(M,\<phi>,[p,l,o,snd(sp),fst(sp),\<chi>])" 
      using assms renSat[of \<phi> 6 7 ?env M  ?new_env perm_pow,symmetric]  
            perm_pow_tc inM
            \<open>?env\<in>list(M)\<close> \<open>?new_env\<in>list(M)\<close> 
            \<open>6\<in>nat\<close> \<open>7\<in>nat\<close>
            perm_pow_env[of "snd(sp)" "fst(sp)"  sp p l o \<chi> M] 
            unfolding \<phi>'_def
            apply auto
      sorry  (* histérica! *)
     finally have
      "sats(M,?\<psi>,[sp,p,l,o,\<chi>,0]) \<longleftrightarrow> 
       sats(M,\<phi>,[p,l,o,snd(sp),fst(sp),\<chi>])" 
      by simp
  }
  then have
    "?\<theta> = {sp\<in>A\<times>B . sats(M,?\<psi>,[sp,p,l,o,\<chi>,0])}"
    by auto
  also from assms \<open>A\<times>B\<in>M\<close> have
    " ... \<in> M"
  proof -
    from 1 have
      "arity(?\<psi>) \<le> 6" 
      by (simp add:  not_lt_iff_le leI nat_union_abs1)
    moreover from \<open>\<phi>' \<in> formula\<close> have
      "?\<psi> \<in> formula"
      by simp
    moreover note assms \<open>A\<times>B\<in>M\<close> 
    ultimately show
      "{x \<in> A\<times>B . sats(M, ?\<psi>, [x, p, l, o, \<chi>, 0])} \<in> M"
      using zero_in_M sixp_sep  Collect_abs separation_iff
      by simp
  qed
  finally show ?thesis .
qed
    
lemma Pow_inter_MG:
  assumes
    "a\<in>M[G]"
  shows
    "Pow(a) \<inter> M[G] \<in> M[G]" 
proof -
  from assms obtain \<tau> where
    "\<tau> \<in> M" "val(G, \<tau>) = a"
    using GenExtD by blast
  let
    ?Q="Pow(domain(\<tau>)\<times>P) \<inter> M"
  from \<open>\<tau>\<in>M\<close> have
    "domain(\<tau>)\<times>P \<in> M" "domain(\<tau>) \<in> M"
    using domain_closed cartprod_closed P_in_M   
    by simp_all
  then have
    "?Q \<in> M"
  proof -
    from power_ax \<open>domain(\<tau>)\<times>P \<in> M\<close> obtain Q where
      "powerset(##M,domain(\<tau>)\<times>P,Q)" "Q \<in> M"
      unfolding power_ax_def by auto
    moreover from calculation have
      "z\<in>Q  \<Longrightarrow> z\<in>M" for z
      using Transset_intf trans_M by blast
    ultimately have
      "Q = {a\<in>Pow(domain(\<tau>)\<times>P) . a\<in>M}"
      using \<open>domain(\<tau>)\<times>P \<in> M\<close> powerset_abs[of "domain(\<tau>)\<times>P" Q]     
      by (simp del:setclass_iff add:setclass_iff[symmetric])
    also have
      " ... = ?Q"
      by auto
    finally show
      "?Q \<in> M" 
      using \<open>Q\<in>M\<close> by simp
  qed
  let
    ?\<pi>="?Q\<times>{one}"
  let
    ?b="val(G,?\<pi>)"
  from \<open>?Q\<in>M\<close> have
    "?\<pi>\<in>M"
    using one_in_P P_in_M Transset_intf transM  
    by (simp del:setclass_iff add:setclass_iff[symmetric])
  from \<open>?\<pi>\<in>M\<close> have
    "?b \<in> M[G]" 
    using GenExtI by simp
  have
    "Pow(a) \<inter> M[G] \<subseteq> ?b"
  proof
    fix c
    assume 
      "c \<in> Pow(a) \<inter> M[G]"
    then obtain \<chi> where
      "c\<in>M[G]" "\<chi> \<in> M" "val(G,\<chi>) = c"
      using GenExtD by blast
    let
      ?\<theta>="{sp \<in>domain(\<tau>)\<times>P . sats(M,forces(Member(0,1)),[P,leq,one,snd(sp),fst(sp),\<chi>])}"
    have
      "arity(forces(Member(0,1))) = 6"
      using arity_forces by auto
    with \<open>domain(\<tau>) \<in> M\<close> \<open>\<chi> \<in> M\<close> have
      "?\<theta> \<in> M"
      using P_in_M one_in_M leq_in_M sats_fst_snd_in_M 
      by simp
    then have 
      "?\<theta> \<in> ?Q"
      by auto
    then have
      "val(G,?\<theta>) \<in> ?b"
      using one_in_G one_in_P generic val_of_elem [of ?\<theta> one ?\<pi> G]
      by auto
    have
      "val(G,?\<theta>) = c"
    proof
      (* val(G,?\<theta>) \<subseteq> c *)
      {
        fix x
        assume 
          "x \<in> val(G,?\<theta>)"
        then obtain \<sigma> p where
          1: "<\<sigma>,p>\<in>?\<theta>" "p\<in>G" "val(G,\<sigma>) =  x"
          using elem_of_val_pair 
          by blast
        moreover from \<open><\<sigma>,p>\<in>?\<theta>\<close> \<open>?\<theta> \<in> M\<close> have
          "\<sigma>\<in>M"
          using name_components_in_M[of _ _ ?\<theta>]  by auto
        moreover from 1 have
          "sats(M,forces(Member(0,1)),[P,leq,one,p,\<sigma>,\<chi>])" "p\<in>P" 
          by simp_all
        moreover note
          \<open>val(G,\<chi>) = c\<close>       
        ultimately have
          "sats(M[G],Member(0,1),[x,c])"
          using \<open>\<chi> \<in> M\<close> generic definition_of_forces
          by auto
        moreover have
          "x\<in>M[G]" 
          using \<open>val(G,\<sigma>) =  x\<close> \<open>\<sigma>\<in>M\<close> GenExtI by blast
        ultimately have
          "x\<in>c"
          using \<open>c\<in>M[G]\<close> by simp
      }
      then show 
        "val(G,?\<theta>) \<subseteq> c"
        by auto
    next
      (* val(G,?\<theta>) \<supseteq> c *)
      {
        fix x
        assume 
          "x \<in> c"
        with \<open>c \<in> Pow(a) \<inter> M[G]\<close> have
          "x \<in> a" "c\<in>M[G]" "x\<in>M[G]"
          by (auto simp add:Transset_intf Transset_MG)
        with \<open>val(G, \<tau>) = a\<close> obtain \<sigma> where
          "\<sigma>\<in>domain(\<tau>)" "val(G,\<sigma>) =  x"
          using elem_of_val
          by blast
        moreover note \<open>x\<in>c\<close> \<open>val(G,\<chi>) = c\<close>
        moreover from calculation have
          "val(G,\<sigma>) \<in> val(G,\<chi>)"
          by simp
        moreover note \<open>c\<in>M[G]\<close> \<open>x\<in>M[G]\<close>
        moreover from calculation have
          "sats(M[G],Member(0,1),[x,c])"
          by simp
        moreover have
          "Member(0,1)\<in>formula" by simp
        moreover have
          "\<sigma>\<in>M" 
        proof -
          from \<open>\<sigma>\<in>domain(\<tau>)\<close> obtain p where
            "<\<sigma>,p> \<in> \<tau>" 
            by auto
          with \<open>\<tau>\<in>M\<close> show ?thesis 
            using name_components_in_M by blast
        qed
        moreover note \<open>\<chi> \<in> M\<close>
        ultimately obtain p where
          "p\<in>G" "sats(M,forces(Member(0,1)),[P,leq,one,p,\<sigma>,\<chi>])"
          using generic truth_lemma[of "Member(0,1)" "[\<sigma>,\<chi>]" "G"] 
          by auto
        moreover from \<open>p\<in>G\<close> have 
          "p\<in>P" 
          using generic unfolding M_generic_def filter_def by blast
        ultimately  have 
          "<\<sigma>,p>\<in>?\<theta>"
          using \<open>\<sigma>\<in>domain(\<tau>)\<close> by simp
        with \<open>val(G,\<sigma>) =  x\<close> \<open>p\<in>G\<close> have
          "x\<in>val(G,?\<theta>)"
          using val_of_elem [of _ _ "?\<theta>"] by auto
      }
      then show
        "c \<subseteq> val(G,?\<theta>)"
        by auto
    qed
    with \<open>val(G,?\<theta>) \<in> ?b\<close> show
      "c\<in>?b"
      by simp
  qed
  then have
    "Pow(a) \<inter> M[G] = {x\<in>?b . x\<subseteq>a & x\<in>M[G]}" 
    by auto 
  also from \<open>a\<in>M[G]\<close> have
    " ... = {x\<in>?b . sats(M[G],subset_fm(0,1),[x,a]) & x\<in>M[G]}"
    using Transset_MG by force
  also have 
    " ... = {x\<in>?b . sats(M[G],subset_fm(0,1),[x,a])} \<inter> M[G]"
    by auto
  also from \<open>?b\<in>M[G]\<close> have
    " ... = {x\<in>?b . sats(M[G],subset_fm(0,1),[x,a])}"
    using Collect_inter_Transset Transset_MG 
    by simp
  also have
    " ... \<in> M[G]"
  proof -
    have
      "arity(subset_fm(0,1)) \<le> 2"
      by (simp add:  not_lt_iff_le leI nat_union_abs1)
    moreover note
      \<open>?\<pi>\<in>M\<close> \<open>\<tau>\<in>M\<close> \<open>val(G,\<tau>) = a\<close>
    ultimately show ?thesis
      using Collect_sats_in_MG by auto
  qed
  finally show ?thesis .
qed
end
  
sublocale G_generic \<subseteq> M_trivial"##M[G]"
  using generic Union_MG pairing_in_MG zero_in_MG Transset_intf Transset_MG
  unfolding M_trivial_def by simp 
 
context G_generic begin
theorem power_in_MG :
  "power_ax(##(M[G]))"
  unfolding power_ax_def
proof (intro rallI, simp only:setclass_iff rex_setclass_is_bex)
  fix a
  assume 
    "a \<in> M[G]"
  have
    "{x\<in>Pow(a) . x \<in> M[G]} = Pow(a) \<inter> M[G]"
    by auto
  also from \<open>a\<in>M[G]\<close> have
    " ... \<in> M[G]" 
    using Pow_inter_MG by simp
  finally have
    "{x\<in>Pow(a) . x \<in> M[G]} \<in> M[G]" .
  moreover from \<open>a\<in>M[G]\<close> have
    "powerset(##M[G], a, {x\<in>Pow(a) . x \<in> M[G]})"
    using powerset_abs[of a "{x\<in>Pow(a) . x \<in> M[G]}"]
    by simp
  ultimately show 
    "\<exists>x\<in>M[G] . powerset(##M[G], a, x)"
    by auto
qed
end
end