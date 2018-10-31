theory Names imports Forcing_data Interface2 Recursion_Thms begin
  
lemma transD : "Transset(M) \<Longrightarrow> y \<in> M \<Longrightarrow> y \<subseteq> M" 
  by (unfold Transset_def, blast) 
    
definition
  SepReplace :: "[i, i\<Rightarrow>i, i\<Rightarrow> o] \<Rightarrow>i" where
  "SepReplace(A,b,Q) == {y . x\<in>A, y=b(x) \<and> Q(x)}"
  
syntax
  "_SepReplace"  :: "[i, pttrn, i, o] => i"  ("(1{_ ../ _ \<in> _, _})")
translations
  "{b .. x\<in>A, Q}" => "CONST SepReplace(A, \<lambda>x. b, \<lambda>x. Q)"
  
lemma Sep_and_Replace: "{b(x) .. x\<in>A, P(x) } = {b(x) . x\<in>{y\<in>A. P(y)}}"
  by (auto simp add:SepReplace_def)
    
lemma SepReplace_subset : "A\<subseteq>A'\<Longrightarrow> {b .. x\<in>A, Q}\<subseteq>{b .. x\<in>A', Q}"
  by (auto simp add:SepReplace_def)
    
lemma SepReplace_iff [simp]: "y\<in>{b(x) .. x\<in>A, P(x)} \<longleftrightarrow> (\<exists>x\<in>A. y=b(x) & P(x))"
  by (auto simp add:SepReplace_def)
    
    (*
lemma SepReplace_cong1 : "(\<And>x. b(x) = b'(x))\<Longrightarrow> {b(x) .. x\<in>A, Q(x)}={b'(x) .. x\<in>A, Q(x)}"
  by (auto simp add:SepReplace_def)
*)
    
lemma SepReplace_dom_implies :
  "(\<And> x . x \<in>A \<Longrightarrow> b(x) = b'(x))\<Longrightarrow> {b(x) .. x\<in>A, Q(x)}={b'(x) .. x\<in>A, Q(x)}"
  by  (simp add:SepReplace_def)
    
lemma SepReplace_pred_implies :
  "\<forall>x. Q(x)\<longrightarrow> b(x) = b'(x)\<Longrightarrow> {b(x) .. x\<in>A, Q(x)}={b'(x) .. x\<in>A, Q(x)}"
  by  (force simp add:SepReplace_def)
    
section\<open>eclose properties\<close>
  
lemma eclose_sing : "x \<in> eclose(a) \<Longrightarrow> x \<in> eclose({a})"
  by(rule subsetD[OF mem_eclose_subset],simp+)  
     
lemma ecloseE : "x \<in> eclose(A) \<Longrightarrow> x \<in> A \<or> (\<exists> B \<in> A . x \<in> eclose(B))"
  apply(erule eclose_induct_down,simp,erule disjE,rule disjI2,simp add:arg_into_eclose)
   apply(subgoal_tac "z \<in> eclose(y)",blast,simp add: arg_into_eclose)
  apply(rule disjI2,erule bexE,subgoal_tac "z \<in> eclose(B)",blast,simp add:ecloseD) 
  done
    
lemma eclose_singE : "x \<in> eclose({a}) \<Longrightarrow> x = a \<or> x \<in> eclose(a)"
  by(blast dest: ecloseE)
    
lemma in_eclose_sing : "x \<in> eclose({a}) \<Longrightarrow> a \<in> eclose(z) \<Longrightarrow> x \<in> eclose({z})"
  apply(drule eclose_singE,erule disjE,simp add: eclose_sing)
  apply(rule eclose_sing,erule mem_eclose_trans,assumption)
  done
    
lemma in_dom_in_eclose : "x \<in> domain(z) \<Longrightarrow> x \<in> eclose(z)"
  apply(auto simp add:domain_def)
  apply(rule_tac A="{x}" in ecloseD)
   apply(subst (asm) Pair_def)
   apply(rule_tac A="{{x,x},{x,y}}" in ecloseD,auto simp add:arg_into_eclose)  
  done
    
text\<open>The well founded relation on which @{term val} is defined\<close>
definition
  ed :: "[i,i] \<Rightarrow> o" where
  "ed(x,y) == x \<in> domain(y)"
  
definition
  edrel :: "i \<Rightarrow> i" where
  "edrel(A) == {<x,y> \<in> A*A . x \<in> domain(y)}"
  
lemma edrel_dest [dest]: "x \<in> edrel(A) \<Longrightarrow> \<exists> a\<in> A. \<exists> b \<in> A. x =<a,b>"
  by(auto simp add:edrel_def)
    
lemma edrelD : "x \<in> edrel(A) \<Longrightarrow> \<exists> a\<in> A. \<exists> b \<in> A. x =<a,b> \<and> a \<in> domain(b)"
  by(auto simp add:edrel_def)
    
lemma edrelI [intro!]: "x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> x \<in> domain(y) \<Longrightarrow> <x,y>\<in>edrel(A)"
  by (simp add:edrel_def)
    
lemma edrel_trans: "Transset(A) \<Longrightarrow> y\<in>A \<Longrightarrow> x \<in> domain(y) \<Longrightarrow> <x,y>\<in>edrel(A)"
  by (rule edrelI, auto simp add:Transset_def domain_def Pair_def)

lemma domain_trans: "Transset(A) \<Longrightarrow> y\<in>A \<Longrightarrow> x \<in> domain(y) \<Longrightarrow> x\<in>A"
  by (auto simp add: Transset_def domain_def Pair_def)
       
lemma relation_edrel : "relation(edrel(A))"
  by(auto simp add: relation_def)
    
    
lemma edrel_sub_memrel: "edrel(A) \<subseteq> trancl(Memrel(eclose(A)))" 
proof
  fix z
  assume
    "z\<in>edrel(A)"
  then obtain x y where
    Eq1:   "x\<in>A" "y\<in>A" "z=<x,y>" "x\<in>domain(y)"
    by (auto simp add: edrel_def)
  then obtain u v where
    Eq2:   "x\<in>u" "u\<in>v" "v\<in>y"
    unfolding domain_def Pair_def by auto
  with Eq1 have
    Eq3:   "x\<in>eclose(A)" "y\<in>eclose(A)" "u\<in>eclose(A)" "v\<in>eclose(A)"
    by (auto, rule_tac [3-4] ecloseD, rule_tac [3] ecloseD, simp_all add:arg_into_eclose)
  let
    ?r="trancl(Memrel(eclose(A)))"
  from Eq2 and Eq3 have
    "<x,u>\<in>?r" "<u,v>\<in>?r" "<v,y>\<in>?r"
    by (auto simp add: r_into_trancl)
  then  have
    "<x,y>\<in>?r"
    by (rule_tac trancl_trans, rule_tac [2] trancl_trans, simp)
  with Eq1 show "z\<in>?r" by simp
qed
  
  
  
lemma wf_edrel : "wf(edrel(A))"
  apply (rule_tac wf_subset [of "trancl(Memrel(eclose(A)))"])
   apply (auto simp add:edrel_sub_memrel wf_trancl wf_Memrel)
  done
    
lemma dom_under_edrel_eclose: "edrel(eclose({x})) -`` {x}= domain(x)" 
  apply(simp add:edrel_def,rule,rule,drule underD,simp,rule,rule underI)
  apply(auto simp add:in_dom_in_eclose eclose_sing arg_into_eclose)
  done
    
lemma ed_eclose : "<y,z> \<in> edrel(A) \<Longrightarrow> y \<in> eclose(z)"
  by(drule edrelD,auto simp add:domain_def in_dom_in_eclose)
    
lemma tr_edrel_eclose : "<y,z> \<in> edrel(eclose({x}))^+ \<Longrightarrow> y \<in> eclose(z)"
  by(rule trancl_induct,(simp add: ed_eclose mem_eclose_trans)+)
    
    
lemma restrict_edrel_eq : 
  assumes "z \<in> domain(x)"
  shows "rel_restrict(edrel(eclose({x})), eclose({z})) = edrel(eclose({z}))"
proof -
  let ?ec="\<lambda> y . edrel(eclose({y}))"
  let ?ez="eclose({z})"
  let ?rr="rel_restrict(?ec(x), ?ez)"  
  { fix y
    assume yr:"y \<in> ?rr"
    with yr obtain a b where 1:"<a,b> \<in> rel_restrict(?rr,?ez)" 
      "a \<in> ?ez" "b \<in> ?ez" "<a,b> \<in> ?ec(x)" "y=<a,b>"
      unfolding rel_restrict_def Ord_induct by blast
    then have "a \<in> domain(b)" using edrelD by blast
    with 1 have "y \<in> edrel(eclose({z}))" by blast
  }
  then have A:"rel_restrict(edrel(eclose({x})), eclose({z})) \<subseteq> edrel(eclose({z}))" by blast
  let ?ec="\<lambda> y . edrel(eclose({y}))"
  let ?ez="eclose({z})"
  let ?rr="rel_restrict(?ec(x), ?ez)"  
  { fix y
    assume yr:"y \<in> edrel(?ez)"
    then obtain a b where 1: "a \<in> ?ez" "b \<in> ?ez" "y=<a,b>" "a \<in> domain(b)"
      using edrelD by blast 
    with assms have "z \<in> eclose(x)" using in_dom_in_eclose by simp
    with assms 1 have "a \<in> eclose({x})" "b \<in> eclose({x})" using in_eclose_sing by simp+
    with \<open>a\<in>domain(b)\<close> have "<a,b> \<in> edrel(eclose({x}))" by blast
    with 1 have "<a,b> \<in> rel_restrict(edrel(eclose({x})),eclose({z}))" using rel_restrictI by simp
    with 1 have "y \<in> rel_restrict(edrel(eclose({x})),eclose({z}))" by simp 
  }
  then have B: "edrel(eclose({z})) \<subseteq> rel_restrict(edrel(eclose({x})), eclose({z}))" by blast
  with A show ?thesis by auto
qed
  
lemma tr_edrel_subset :
  assumes "z \<in> domain(x)"
  shows   "tr_down(edrel(eclose({x})),z) \<subseteq> eclose({z})"
proof -
  let ?r="\<lambda> x . edrel(eclose({x}))"
  {fix y
    assume  "y \<in> tr_down(?r(x),z)" 
    then have "<y,z> \<in> ?r(x)^+" using tr_downD by simp
    with assms have "y \<in> eclose({z})" using tr_edrel_eclose eclose_sing by simp
  } 
  then show ?thesis  by blast  
qed
  
  
  (* KEEP? *)    
lemma eq_sub_trans :  "x=y \<Longrightarrow> y\<subseteq>z \<Longrightarrow> x\<subseteq>z"
  "x\<subseteq>y \<Longrightarrow> y=z \<Longrightarrow> x\<subseteq>z"
  by simp_all
    
context forcing_data
begin  (*************** CONTEXT: forcing_data *****************)
  
lemma upairM : "x \<in> M \<Longrightarrow> y \<in> M \<Longrightarrow> {x,y} \<in> M"
  by(insert upair_ax, auto simp add: upair_ax_def)
    
lemma pairM : "x \<in>  M \<Longrightarrow> y \<in> M \<Longrightarrow> <x,y> \<in> M"
  by(unfold Pair_def, rule upairM,(rule upairM,simp+)+)
    
lemma P_sub_M : "P \<subseteq> M"
  by (simp add: P_in_M trans_M transD)
    
lemma Rep_simp : "Replace(u,\<lambda> y z . z = f(y)) = { f(y) . y \<in> u}"
  by(auto)
    
definition 
  Hcheck :: "[i,i] \<Rightarrow> i" where
  "Hcheck(z,f)  == { <f`y,one> . y \<in> z}"
  
definition
  check :: "i \<Rightarrow> i" where
  "check(x) == wfrec(Memrel(eclose({x})), x , Hcheck)"
  
lemma  aux_def_check: "x \<in> y \<Longrightarrow>
  wfrec(Memrel(eclose({y})), x, Hcheck) = 
  wfrec(Memrel(eclose({x})), x, Hcheck)"
  by (rule wfrec_eclose_eq,auto simp add: arg_into_eclose eclose_sing)
    
lemma def_check : "check(y) = { <check(w),one> . w \<in> y}"
proof -
  let 
    ?r="\<lambda>y. Memrel(eclose({y}))"
  from wf_Memrel have
    wfr:   "\<forall>w . wf(?r(w))" ..
  with wfrec [of "?r(y)" y "Hcheck"] have
    "check(y)= Hcheck( y, \<lambda>x\<in>?r(y) -`` {y}. wfrec(?r(y), x, Hcheck))"
    using check_def by simp 
  also have 
    " ... = Hcheck( y, \<lambda>x\<in>y. wfrec(?r(y), x, Hcheck))"
    using under_Memrel_eclose arg_into_eclose by simp
  also have 
    " ... = Hcheck( y, \<lambda>x\<in>y. check(x))"
    using aux_def_check check_def by simp
  finally show ?thesis using Hcheck_def by simp
qed
  
lemma checkin_M : "x \<in> M \<Longrightarrow> check(x) \<in> M"
  sorry
    
lemma field_Memrel : "x \<in> M \<Longrightarrow> field(Memrel(eclose({x}))) \<subseteq> M"
  apply(rule subset_trans,rule field_rel_subset,rule Ordinal.Memrel_type)
  apply(rule eclose_least,rule trans_M,auto)
  done
    
definition
  Hv :: "i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>i" where
  "Hv(G,x,f) == { f`y .. y\<in> domain(x), \<exists>p\<in>P. <y,p> \<in> x \<and> p \<in> G }"

definition
  val :: "i\<Rightarrow>i\<Rightarrow>i" where
  "val(G,\<tau>) == wfrec(edrel(eclose({\<tau>})), \<tau> ,Hv(G))"

lemma aux_def_val: 
  assumes "z \<in> domain(x)"
  shows "wfrec(edrel(eclose({x})),z,Hv(G)) = wfrec(edrel(eclose({z})),z,Hv(G))"
proof -
  let ?r="\<lambda>x . edrel(eclose({x}))"
  have "z\<in>eclose({z})" using arg_in_eclose_sing .
  moreover have "relation(?r(x))" using relation_edrel .
  moreover have "wf(?r(x))" using wf_edrel .    
  moreover from assms have "tr_down(?r(x),z) \<subseteq> eclose({z})" using tr_edrel_subset by simp
  ultimately have 
    "wfrec(?r(x),z,Hv(G)) = wfrec(rel_restrict(?r(x),eclose({z})),z,Hv(G))"
    using wfrec_restr by simp
  also with assms have "... = wfrec(?r(z),z,Hv(G))" using restrict_edrel_eq by simp
  finally show ?thesis .
qed  
lemma def_val:  "val(G,x) = {val(G,t) .. t\<in>domain(x) , \<exists>p\<in>P .  <t,p>\<in>x \<and> p \<in> G }"
proof -
  let
    ?r="\<lambda>\<tau> . edrel(eclose({\<tau>}))"
  let
    ?f="\<lambda>z\<in>?r(x)-``{x}. wfrec(?r(x),z,Hv(G))"
  have "\<forall>\<tau>. wf(?r(\<tau>))" using wf_edrel by simp
  with wfrec [of _ x] have
    "val(G,x) = Hv(G,x,?f)" using val_def by simp
  also have
    " ... = Hv(G,x,\<lambda>z\<in>domain(x). wfrec(?r(x),z,Hv(G)))"
    using dom_under_edrel_eclose by simp
  also have
    " ... = Hv(G,x,\<lambda>z\<in>domain(x). val(G,z))"
    using aux_def_val val_def by simp
  finally show ?thesis using Hv_def SepReplace_def by simp
qed
  
lemma val_mono : "x\<subseteq>y \<Longrightarrow> val(G,x) \<subseteq> val(G,y)"
  by (subst (1 2) def_val, force)
    
lemma valcheck : "one \<in> G \<Longrightarrow>  one \<in> P \<Longrightarrow> val(G,check(y))  = y"
proof (induct rule:eps_induct)
  case (1 y)
  then show ?case
  proof -
    from def_check have
      Eq1: "check(y) = { \<langle>check(w), one\<rangle> . w \<in> y}"  (is "_ = ?C") .
    from Eq1 have
      "val(G,check(y)) = val(G, {\<langle>check(w), one\<rangle> . w \<in> y})"
      by simp
    also have
      " ...  = {val(G,t) .. t\<in>domain(?C) , \<exists>p\<in>P .  \<langle>t, p\<rangle>\<in>?C \<and> p \<in> G }"
      using def_val by blast
    also have
      " ... =  {val(G,t) .. t\<in>domain(?C) , \<exists>w\<in>y. t=check(w) }"
      using 1 by simp
    also have
      " ... = {val(G,check(w)) . w\<in>y }"
      by force
    finally show 
      "val(G,check(y)) = y" 
      using 1  by simp
  qed
qed
  
lemma val_of_name : 
  "val(G,{x\<in>A\<times>P. Q(x)}) = {val(G,t) .. t\<in>A , \<exists>p\<in>P .  Q(<t,p>) \<and> p \<in> G }"
proof -
  let
    ?n="{x\<in>A\<times>P. Q(x)}" and
    ?r="\<lambda>\<tau> . edrel(eclose({\<tau>}))"
  let
    ?f="\<lambda>z\<in>?r(?n)-``{?n}. val(G,z)"
  have
    wfR : "wf(?r(\<tau>))" for \<tau>
    by (simp add: wf_edrel)
  have "domain(?n) \<subseteq> A" by auto
  { fix t
    assume H:"t \<in> domain({x \<in> A \<times> P . Q(x)})"
    then have "(\<lambda>z\<in>edrel(eclose({{x \<in> A \<times> P . Q(x)}})) -`` {{x \<in> A \<times> P . Q(x)}}. val(G, z)) ` t = 
          (if t \<in> edrel(eclose({{x \<in> A \<times> P . Q(x)}})) -`` {{x \<in> A \<times> P . Q(x)}} then val(G,t) else 0)"
      by simp
    moreover have "... = val(G,t)"
      using dom_under_edrel_eclose H if_P by auto
  }
  then have Eq1: "t \<in> domain({x \<in> A \<times> P . Q(x)}) \<Longrightarrow> 
    val(G,t) = (\<lambda>z\<in>edrel(eclose({{x \<in> A \<times> P . Q(x)}})) -`` {{x \<in> A \<times> P . Q(x)}}. val(G, z)) ` t"  for t 
    by simp
  have
    "val(G,?n) = {val(G,t) .. t\<in>domain(?n), \<exists>p \<in> P . <t,p> \<in> ?n \<and> p \<in> G}"
    by (subst def_val,simp) 
  also have
    "... = {?f`t .. t\<in>domain(?n), \<exists>p\<in>P . <t,p>\<in>?n \<and> p\<in>G}"
    unfolding Hv_def
    by (subst SepReplace_dom_implies,auto simp add:Eq1)
  also have
    "... = { (if t\<in>?r(?n)-``{?n} then val(G,t) else 0) .. t\<in>domain(?n), \<exists>p\<in>P . <t,p>\<in>?n \<and> p\<in>G}"
    by (simp)
  also have
    Eq2:  "... = { val(G,t) .. t\<in>domain(?n), \<exists>p\<in>P . <t,p>\<in>?n \<and> p\<in>G}"
  proof -
    from dom_under_edrel_eclose have
      "domain(?n) \<subseteq> ?r(?n)-``{?n}"                     
      by simp
    then have
      "\<forall>t\<in>domain(?n). (if t\<in>?r(?n)-``{?n} then val(G,t) else 0) = val(G,t)"
      by auto
    then show 
      "{ (if t\<in>?r(?n)-``{?n} then val(G,t) else 0) .. t\<in>domain(?n), \<exists>p\<in>P . <t,p>\<in>?n \<and> p\<in>G} =
               { val(G,t) .. t\<in>domain(?n), \<exists>p\<in>P . <t,p>\<in>?n \<and> p\<in>G}"
      by auto
  qed
  also have
    " ... = { val(G,t) .. t\<in>A, \<exists>p\<in>P . <t,p>\<in>?n \<and> p\<in>G}"
    by force 
  finally show
    " val(G,?n)  = { val(G,t) .. t\<in>A, \<exists>p\<in>P . Q(<t,p>) \<and> p\<in>G}"
    by auto
qed
  
definition
  GenExt :: "i\<Rightarrow>i"     ("M[_]")
  where "GenExt(G)== {val(G,\<tau>). \<tau> \<in> M}"
    

lemma val_of_elem: "<\<theta>,p> \<in> \<pi> \<Longrightarrow> p\<in>G \<Longrightarrow> p\<in>P \<Longrightarrow> val(G,\<theta>) \<in> val(G,\<pi>)"
proof -
  assume
    "<\<theta>,p> \<in> \<pi>" 
  then have "\<theta>\<in>domain(\<pi>)" by auto
  assume
    "p\<in>G" "p\<in>P"
  with \<open>\<theta>\<in>domain(\<pi>)\<close> \<open><\<theta>,p> \<in> \<pi>\<close> have
    "val(G,\<theta>) \<in> {val(G,t) .. t\<in>domain(\<pi>) , \<exists>p\<in>P .  \<langle>t, p\<rangle>\<in>\<pi> \<and> p \<in> G }"
    by auto
  then show ?thesis by (subst def_val)
qed
  
lemma elem_of_val: "x\<in>val(G,\<pi>) \<Longrightarrow> \<exists>\<theta>\<in>domain(\<pi>). val(G,\<theta>) = x"
  by (subst (asm) def_val,auto)
    
lemma elem_of_val_pair: "x\<in>val(G,\<pi>) \<Longrightarrow> \<exists>\<theta>. \<exists>p\<in>G.  <\<theta>,p>\<in>\<pi> \<and> val(G,\<theta>) = x"
  by (subst (asm) def_val,auto)
  
lemma GenExtD [dest]: 
  "x \<in> M[G] \<Longrightarrow> \<exists>\<tau>\<in>M. x = val(G,\<tau>)"
  by (simp add:GenExt_def)
    
lemma GenExtI [intro]: 
  "x \<in> M \<Longrightarrow> val(G,x) \<in> M[G]"
  by (auto simp add: GenExt_def)
    
lemma trans_Gen_Ext' :
  assumes "vc \<in> M[G]"
    "y \<in> vc" 
  shows
    "y \<in> M[G]" 
proof -
  from \<open>vc\<in>M[G]\<close> have
    "\<exists>c\<in>M. vc = val(G,c)"
    by blast
  then obtain c where
    "c\<in>M" "vc = val(G,c)" by auto
  with \<open>vc \<in> M[G]\<close> have
    "val(G,c)\<in>M[G]" by simp
  from \<open>y \<in> vc\<close> and \<open>vc = val(G,c)\<close> have
    "y \<in> val(G,c)" by simp
  with \<open>c\<in>M\<close> and elem_of_val have
    "\<exists>\<theta>\<in>domain(c). val(G,\<theta>) = y" by simp
  then obtain \<theta> where
    "\<theta>\<in>domain(c)" "val(G,\<theta>) = y" by auto
  from \<open>\<theta>\<in>domain(c)\<close> trans_M \<open>c\<in>M\<close> domain_trans have
    "\<theta>\<in>M" by simp
  then have
    "val(G,\<theta>) \<in> M[G]" 
    by blast
  with \<open>val(G,\<theta>) = y\<close> show ?thesis by simp
qed
  
lemma trans_Gen_Ext:
  "Transset(M[G])"
  by (auto simp add: Transset_def trans_Gen_Ext')
    
    
definition
  G_dot :: "i" where
  "G_dot == {<check(p),p> . p\<in>P}"
  
lemma G_dot_in_M :
  "G_dot \<in> M" 
proof -
  have 0:"G_dot = { y . p\<in>P , y = <check(p),p> }"
    unfolding G_dot_def by auto
  from P_in_M checkin_M pairM P_sub_M have "\<And> p . p\<in>P \<Longrightarrow> <check(p),p> \<in> M" 
    by auto
  then have
    1:"\<And>x y. \<lbrakk> x\<in>P ; y = <check(x),x> \<rbrakk> \<Longrightarrow> y\<in>M"
    by simp
  have 2:"strong_replacement(##M,\<lambda>p y. y =<check(p),p>)"
    sorry
  then have
    "\<forall>A\<in>M.(\<exists>Y\<in>M. \<forall>b\<in>M. b \<in> Y \<longleftrightarrow> (\<exists>x\<in>M. x\<in>A & b = <check(x),x>))"
    unfolding strong_replacement_def by simp
  then have
    "(\<exists>Y\<in>M. \<forall>b\<in>M. b \<in> Y \<longleftrightarrow> (\<exists>x\<in>M. x\<in>P & b = <check(x),x>))"
    using P_in_M by simp
  with 1 2 P_in_M strong_replacement_closed have
    "{ y . p\<in>P , y = <check(p),p> } \<in> M" by simp
  then show ?thesis using 0 by simp
qed
  
lemma val_G_dot :
  assumes "G \<subseteq> P"
    "one \<in> G" 
  shows "val(G,G_dot) = G"
proof (intro equalityI subsetI) 
  fix x
  assume "x\<in>val(G,G_dot)"
  then have 
      "\<exists>\<theta>. \<exists>p\<in>G.  <\<theta>,p>\<in>G_dot \<and> val(G,\<theta>) = x"
    using elem_of_val_pair G_dot_in_M by simp
  then obtain r p where 
    "p\<in>G" "<r,p> \<in> G_dot" "val(G,r) = x" 
    by auto
  then have
    "r = check(p)" 
    unfolding G_dot_def by simp
  with \<open>one\<in>G\<close> \<open>G\<subseteq>P\<close> \<open>p\<in>G\<close> \<open>val(G,r) = x\<close> show
      "x \<in> G" 
    using valcheck P_sub_M  checkin_M by auto
next
  fix p
  assume "p\<in>G" 
  have "\<forall>q\<in>P. <check(q),q> \<in> G_dot" 
    unfolding G_dot_def by simp
  with \<open>p\<in>G\<close> \<open>G\<subseteq>P\<close> have
    "val(G,check(p)) \<in> val(G,G_dot)"
    using val_of_elem G_dot_in_M by blast
  with \<open>p\<in>G\<close> \<open>G\<subseteq>P\<close> \<open>one\<in>G\<close> show
    "p \<in> val(G,G_dot)" 
    using P_sub_M checkin_M valcheck by auto
qed
  
  
lemma G_in_Gen_Ext :
  assumes "G \<subseteq> P"
    "one \<in> G"
  shows   "G \<in> M[G]" 
proof -
  from G_dot_in_M have
    "val(G,G_dot) \<in> M[G]" 
    by auto
  with assms val_G_dot 
  show ?thesis by simp
qed

end    (*************** CONTEXT: forcing_data *****************)
  
end
