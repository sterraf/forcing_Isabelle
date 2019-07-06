theory Names imports Forcing_Data Interface Recursion_Thms begin
  
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
  shows "edrel(eclose({x}))\<inter> eclose({z})*eclose({z}) = edrel(eclose({z}))"
proof 
  let ?ec="\<lambda> y . edrel(eclose({y}))"
  let ?ez="eclose({z})"
  let ?rr="?ec(x)\<inter>?ez*?ez"  
  { fix y
    assume yr:"y \<in> ?rr"
    with yr obtain a b where 1:"<a,b> \<in> ?rr\<inter>?ez*?ez" 
      "a \<in> ?ez" "b \<in> ?ez" "<a,b> \<in> ?ec(x)" "y=<a,b>" by blast
    then have "a \<in> domain(b)" using edrelD by blast
    with 1 have "y \<in> edrel(eclose({z}))" by blast
  }
  then show "?rr \<subseteq> edrel(?ez)" using subsetI by auto 
next
  let ?ec="\<lambda> y . edrel(eclose({y}))"
  let ?ez="eclose({z})"
  let ?rr="?ec(x)\<inter>?ez*?ez"  
  { fix y
    assume yr:"y \<in> edrel(?ez)"
    then obtain a b where 1: "a \<in> ?ez" "b \<in> ?ez" "y=<a,b>" "a \<in> domain(b)"
      using edrelD by blast 
    with assms have "z \<in> eclose(x)" using in_dom_in_eclose by simp
    with assms 1 have "a \<in> eclose({x})" "b \<in> eclose({x})" using in_eclose_sing by simp_all
    with \<open>a\<in>domain(b)\<close> have "<a,b> \<in> edrel(eclose({x}))" by blast
    with 1 have "y \<in> ?rr" by simp
  }
  then show "edrel(eclose({z})) \<subseteq> ?rr" by blast
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
  
  
context forcing_data
begin  (*************** CONTEXT: forcing_data *****************)
  
lemma upairM : "x \<in> M \<Longrightarrow> y \<in> M \<Longrightarrow> {x,y} \<in> M"
 by (simp del:setclass_iff  add:setclass_iff[symmetric]) 
    
lemma singletonM : "a \<in> M \<Longrightarrow> {a} \<in> M"
 by (simp del:setclass_iff  add:setclass_iff[symmetric]) 

lemma pairM : "x \<in>  M \<Longrightarrow> y \<in> M \<Longrightarrow> <x,y> \<in> M"
 by (simp del:setclass_iff  add:setclass_iff[symmetric]) 
    
lemma P_sub_M : "P \<subseteq> M"
  by (simp add: P_in_M trans_M transD)
    
lemma Rep_simp : "Replace(u,\<lambda> y z . z = f(y)) = { f(y) . y \<in> u}"
  by(auto)
    
definition 
  Hcheck :: "[i,i] \<Rightarrow> i" where
  "Hcheck(z,f)  == { <f`y,one> . y \<in> z}"
  
definition
  check :: "i \<Rightarrow> i" where
  "check(x) == transrec(x , Hcheck)"
  
lemma checkD:
  "check(x) =  wfrec(Memrel(eclose({x})), x, Hcheck)"
  unfolding check_def transrec_def ..


lemma Hcheck_trancl_aux:
  assumes "w \<in> y"
  shows "restrict(f,Memrel(eclose({x}))-``{y})`w
       = restrict(f,(Memrel(eclose({x}))^+)-``{y})`w" 
proof (cases "y\<in>eclose({x})")
  let ?r="Memrel(eclose({x}))"
  and ?s="Memrel(eclose({x}))^+"
  case True
  from \<open>w\<in>y\<close> \<open>y\<in>eclose({x})\<close>
  have "<w,y>\<in>?r" 
    using Memrel_iff  eclose_subset[OF \<open>y\<in>eclose({x})\<close>] by blast
  then 
  have "<w,y>\<in>?s" 
    using r_subset_trancl[of ?r] relation_Memrel by blast
  with \<open><w,y>\<in>?r\<close> 
  have "w\<in>?r-``{y}" "w\<in>?s-``{y}"
    using vimage_singleton_iff by simp_all
  then 
  show ?thesis by simp
next
  let ?r="Memrel(eclose({x}))"
  let ?s="?r^+"
  case False
  then 
  have "?r-``{y}=0" 
    using Memrel_iff by blast
  then 
  have "w\<notin>?r-``{y}" by simp    
  then
  have "restrict(f,?r-``{y})`w = 0"
    using restrict by simp
  have "y\<in>range(?s) \<Longrightarrow> y \<in> eclose({x})"
    by (auto,rule trancl_induct[of _ _ ?r],auto)
  with \<open>y\<notin>eclose({x})\<close> 
  have "y\<notin>range(?s)" 
    by blast
  then 
  have "w\<notin>?s-``{y}" 
    using vimage_singleton_iff by blast
  with \<open>w\<notin>?r-``{y}\<close>
  show ?thesis by simp
qed


lemma Hcheck_trancl:"Hcheck(y, restrict(f,Memrel(eclose({x}))-``{y}))
                   = Hcheck(y, restrict(f,(Memrel(eclose({x}))^+)-``{y}))"
  unfolding Hcheck_def
  using Hcheck_trancl_aux by simp

lemma check_trancl: "check(x) =  wfrec(Memrel(eclose({x}))^+, x, Hcheck)"
proof -
  have "check(x) =  wfrec(Memrel(eclose({x})), x, Hcheck)"
        (is "_ = wfrec(?r,_,_)")
    using checkD .
  also
  have " ... = wftrec(?r^+, x, \<lambda>y f. Hcheck(y, restrict(f,?r-``{y})))"
    unfolding wfrec_def ..
  also
  have " ... = wftrec(?r^+, x, \<lambda>y f. Hcheck(y, restrict(f,(?r^+)-``{y})))"
    using Hcheck_trancl by simp
  also
  have " ... =  wfrec(?r^+, x, Hcheck)"
    unfolding wfrec_def using trancl_eq_r[OF relation_trancl trans_trancl] by simp
  finally
  show ?thesis .
qed

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
    using checkD by simp 
  also have 
    " ... = Hcheck( y, \<lambda>x\<in>y. wfrec(?r(y), x, Hcheck))"
    using under_Memrel_eclose arg_into_eclose by simp
  also have 
    " ... = Hcheck( y, \<lambda>x\<in>y. check(x))"
    using aux_def_check checkD by simp
  finally show ?thesis using Hcheck_def by simp
qed


lemma def_checkS : 
  fixes n
  assumes "n \<in> nat"
  shows "check(succ(n)) = check(n) \<union> {<check(n),one>}"
proof -
  have "check(succ(n)) = {<check(i),one> . i \<in> succ(n)} " 
    using def_check by blast
  also have "... = {<check(i),one> . i \<in> n} \<union> {<check(n),one>}"
    by blast
  also have "... = check(n) \<union> {<check(n),one>}"
    using def_check[of n,symmetric] by simp
  finally show ?thesis .
qed

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
    "wfrec(?r(x),z,Hv(G)) = wfrec[eclose({z})](?r(x),z,Hv(G))"
    using wfrec_restr by simp
  also from \<open>z\<in>domain(x)\<close> have "... = wfrec(?r(z),z,Hv(G))" 
      using restrict_edrel_eq wfrec_restr_eq by simp
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
    then have "?f ` t = (if t \<in> ?r(?n)-``{?n} then val(G,t) else 0)"
      by simp
    moreover have "... = val(G,t)"
      using dom_under_edrel_eclose H if_P by auto
  }
  then have Eq1: "t \<in> domain({x \<in> A \<times> P . Q(x)}) \<Longrightarrow> 
    val(G,t) = ?f` t"  for t 
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

lemma val_of_name_alt : 
  "val(G,{x\<in>A\<times>P. Q(x)}) = {val(G,t) .. t\<in>A , \<exists>p\<in>P\<inter>G .  Q(<t,p>) }"
using val_of_name by force
  
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
  
lemma GenExtD: 
  "x \<in> M[G] \<Longrightarrow> \<exists>\<tau>\<in>M. x = val(G,\<tau>)"
  by (simp add:GenExt_def)
    
lemma GenExtI: 
  "x \<in> M \<Longrightarrow> val(G,x) \<in> M[G]"
  by (auto simp add: GenExt_def)
    
lemma Transset_MG : "Transset(M[G])"
proof -
  { fix vc y 
    assume "vc \<in> M[G]" and  "y \<in> vc" 
  from \<open>vc\<in>M[G]\<close> and \<open>y \<in> vc\<close>   obtain c where
    "c\<in>M" "val(G,c)\<in>M[G]" "y \<in> val(G,c)" 
    using  GenExtD by auto
  from \<open>y \<in> val(G,c)\<close>  obtain \<theta> where
    "\<theta>\<in>domain(c)" "val(G,\<theta>) = y" using elem_of_val by blast
  with trans_M \<open>c\<in>M\<close> 
  have "y \<in> M[G]" using domain_trans GenExtI by blast
  }
  then show ?thesis using Transset_def by auto
qed

lemma check_n_M :
  fixes n
  assumes "n \<in> nat"
  shows "check(n) \<in> M"
  using \<open>n\<in>nat\<close> proof (induct n)
  case 0
  then show ?case using zero_in_M by (subst def_check,simp)
next
  case (succ x)
  have "one \<in> M" using one_in_P P_sub_M subsetD by simp
  with \<open>check(x)\<in>M\<close> have "<check(x),one> \<in> M" using pairM by simp
  then have "{<check(x),one>} \<in> M" using singletonM by simp
  with \<open>check(x)\<in>M\<close> have "check(x) \<union> {<check(x),one>} \<in> M" using Un_closed by simp
  then show ?case using \<open>x\<in>nat\<close> def_checkS by simp
qed

end (* context forcing_data *)
  
(* Other assumptions over M. This will be removed
   when Interface is completed *)
locale M_extra_assms = forcing_data +
  assumes
        check_in_M : "\<And>x. x \<in> M \<Longrightarrow> check(x) \<in> M"
    and repl_check_pair : "strong_replacement(##M,\<lambda>p y. y =<check(p),p>)"
    
begin 
definition
  G_dot :: "i" where
  "G_dot == {<check(p),p> . p\<in>P}"
  
lemma G_dot_in_M :
  "G_dot \<in> M" 
proof -
  have 0:"G_dot = { y . p\<in>P , y = <check(p),p> }"
    unfolding G_dot_def by auto
  from P_in_M check_in_M pairM P_sub_M have 
     1: "p\<in>P \<Longrightarrow> <check(p),p> \<in> M" for p
    by auto
  with 1 repl_check_pair P_in_M strong_replacement_closed have
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
  then obtain \<theta> p where 
    "p\<in>G" "<\<theta>,p> \<in> G_dot" "val(G,\<theta>) = x" "\<theta> = check(p)" 
    unfolding G_dot_def using elem_of_val_pair G_dot_in_M 
    by force
  with \<open>one\<in>G\<close> \<open>G\<subseteq>P\<close> show
      "x \<in> G" 
    using valcheck P_sub_M by auto
next
  fix p
  assume "p\<in>G" 
  have "q\<in>P \<Longrightarrow> <check(q),q> \<in> G_dot" for q
    unfolding G_dot_def by simp
  with \<open>p\<in>G\<close> \<open>G\<subseteq>P\<close> have
    "val(G,check(p)) \<in> val(G,G_dot)"
    using val_of_elem G_dot_in_M by blast
  with \<open>p\<in>G\<close> \<open>G\<subseteq>P\<close> \<open>one\<in>G\<close> show
    "p \<in> val(G,G_dot)" 
    using P_sub_M valcheck by auto
qed
  
  
lemma G_in_Gen_Ext :
  assumes "G \<subseteq> P" and "one \<in> G"
  shows   "G \<in> M[G]" 
 using assms val_G_dot GenExtI[of _ G] G_dot_in_M 
  by force
    
end    (*************** CONTEXT: M_extra_assms *****************)
  
end
