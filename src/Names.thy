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

lemma field_trancl : "field(r^+) = field(r)"
by (blast intro: r_into_trancl dest!: trancl_type [THEN subsetD])

lemma field_Memrel : "field(Memrel(A)) \<subseteq> A"
  unfolding field_def using Ordinal.Memrel_type by blast

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
  with \<open>y\<notin>eclose({x})\<close> 
  have "y\<notin>field(?s)" 
    using field_trancl subsetD[OF field_Memrel[of "eclose({x})"]] by auto
  then 
  have "w\<notin>?s-``{y}" 
    using vimage_singleton_iff by blast
  with \<open>w\<notin>?r-``{y}\<close>
  show ?thesis by simp
qed

definition
  rcheck :: "i \<Rightarrow> i" where
  "rcheck(x) == Memrel(eclose({x}))^+" 


lemma Hcheck_trancl:"Hcheck(y, restrict(f,Memrel(eclose({x}))-``{y}))
                   = Hcheck(y, restrict(f,(Memrel(eclose({x}))^+)-``{y}))"
  unfolding Hcheck_def
  using Hcheck_trancl_aux by simp

lemma check_trancl: "check(x) =  wfrec(rcheck(x), x, Hcheck)"
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
  show ?thesis unfolding rcheck_def .
qed


(* relation of check is in M *)
lemma rcheck_in_M : 
  "x \<in> M \<Longrightarrow> rcheck(x) \<in> M" 
  unfolding rcheck_def by (simp del:setclass_iff add:setclass_iff[symmetric])


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

lemma field_Memrel2 : "x \<in> M \<Longrightarrow> field(Memrel(eclose({x}))) \<subseteq> M"
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
       "check(y) = { \<langle>check(w), one\<rangle> . w \<in> y}"  (is "_ = ?C") .
    then have
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

lemma val_only_names: "val(F,\<tau>) = val(F,{x\<in>\<tau>. \<exists>t\<in>domain(\<tau>). \<exists>p\<in>P. x=<t,p>})" 
    (is "_ = val(F,?name)")
proof -
  have "val(F,?name) = {val(F, t).. t\<in>domain(?name), \<exists>p\<in>P. \<langle>t, p\<rangle> \<in> ?name \<and> p \<in> F}"
    using def_val by blast
  also
  have " ... = {val(F, t). t\<in>{y\<in>domain(?name). \<exists>p\<in>P. \<langle>y, p\<rangle> \<in> ?name \<and> p \<in> F}}"
    using Sep_and_Replace by simp
  also
  have " ... = {val(F, t). t\<in>{y\<in>domain(\<tau>). \<exists>p\<in>P. \<langle>y, p\<rangle> \<in> \<tau> \<and> p \<in> F}}"
    by blast
  also
  have " ... = {val(F, t).. t\<in>domain(\<tau>), \<exists>p\<in>P. \<langle>t, p\<rangle> \<in> \<tau> \<and> p \<in> F}"
    using Sep_and_Replace by simp
  also
  have " ... = val(F, \<tau>)"
    using def_val[symmetric] by blast
  finally
  show ?thesis ..
qed

lemma val_only_pairs: "val(F,\<tau>) = val(F,{x\<in>\<tau>. \<exists>t p. x=<t,p>})"
proof 
  have "val(F,\<tau>) = val(F,{x\<in>\<tau>. \<exists>t\<in>domain(\<tau>). \<exists>p\<in>P. x=<t,p>})"
    (is " _ = val(F,?name)")
    using val_only_names .
  also
  have "... \<subseteq> val(F,{x\<in>\<tau>. \<exists>t p. x=<t,p>})"
    using val_mono[of ?name "{x\<in>\<tau>. \<exists>t p. x=<t,p>}"] by auto
  finally
  show "val(F,\<tau>) \<subseteq> val(F,{x\<in>\<tau>. \<exists>t p. x=<t,p>})" by simp
next
  show "val(F,{x\<in>\<tau>. \<exists>t p. x=<t,p>}) \<subseteq> val(F,\<tau>)"
    using val_mono[of "{x\<in>\<tau>. \<exists>t p. x=<t,p>}"] by auto
qed

lemma val_subset_domain_times_range: "val(F,\<tau>) \<subseteq> val(F,domain(\<tau>)\<times>range(\<tau>))"
  using val_only_pairs[THEN equalityD1] 
    val_mono[of "{x \<in> \<tau> . \<exists>t p. x = \<langle>t, p\<rangle>}" "domain(\<tau>)\<times>range(\<tau>)"] by blast

lemma val_subset_domain_times_P: "val(F,\<tau>) \<subseteq> val(F,domain(\<tau>)\<times>P)"
  using val_only_names[of F \<tau>] val_mono[of "{x\<in>\<tau>. \<exists>t\<in>domain(\<tau>). \<exists>p\<in>P. x=<t,p>}" "domain(\<tau>)\<times>P" F] 
  by auto
  
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
    then  obtain c where
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


definition 
  PHcheck :: "[i,i,i,i] \<Rightarrow> o" where
  "PHcheck(o,f,y,p) == p\<in>M \<and> (\<exists>fy[##M]. fun_apply(##M,f,y,fy) \<and> pair(##M,fy,o,p))"

definition 
  is_Hcheck :: "[i,i,i,i] \<Rightarrow> o" where
  "is_Hcheck(o,z,f,hc)  == is_Replace(##M,z,PHcheck(o,f),hc)"

(* esto está también en Separation_axiom. Remodularizar! *)
lemmas transitivity = Transset_intf trans_M
  
lemma one_in_M: "one \<in> M"
  by (insert one_in_P P_in_M, simp add: transitivity)


lemma def_PHcheck: 
  assumes
    "z\<in>M" "f\<in>M"
  shows
    "Hcheck(z,f) = Replace(z,PHcheck(one,f))"
proof -
  have "y\<in>M \<Longrightarrow> x\<in>z \<Longrightarrow> z\<in>M \<Longrightarrow> f\<in>M \<Longrightarrow>
        y = \<langle>f ` x, one\<rangle> \<longleftrightarrow> (\<exists>fy\<in>M. fun_apply(##M, f, x, fy) \<and> pair(##M, fy, one, y))"
    for y z x f
    using Transset_intf[OF trans_M]
    by ( auto simp del:setclass_iff simp add:setclass_iff[symmetric])   
  then show ?thesis
    using \<open>z\<in>M\<close> \<open>f\<in>M\<close> Transset_intf[OF trans_M] one_in_M unfolding Hcheck_def PHcheck_def RepFun_def 
    apply auto
    apply (rule equality_iffI)
    apply (simp add: Replace_iff)
    apply auto
    apply (rule tuples_in_M)
    apply (simp_all del:setclass_iff add:setclass_iff[symmetric])
    done
qed

end (* context forcing_data *)


definition 
  is_Replace_fm :: "[i,i,i] \<Rightarrow> i" where
  "is_Replace_fm(a,p,z) == Forall(Iff(Member(0,succ(z)),
                                  Exists(And(Member(0,succ(succ(a))),p))))"

lemma is_Replace_type [TC]:
     "[| x \<in> nat; y \<in> nat; p\<in>formula |] ==> is_Replace_fm(x,p,y) \<in> formula"
  by (simp add:is_Replace_fm_def)

lemma sats_is_Rep_fm :
    assumes p_iff_sats: 
      "\<And>a b . a \<in> M \<Longrightarrow> b \<in> M \<Longrightarrow> 
          P(a,b) \<longleftrightarrow> sats(M, p, Cons(a, Cons(b, env)))"
    shows
   "[| x \<in> nat; y \<in> nat; env \<in> list(M)|]
    ==> sats(M, is_Replace_fm(x,p,y), env) \<longleftrightarrow>
        is_Replace(##M, nth(x,env), P , nth(y,env))"
  by (simp add: is_Replace_def is_Replace_fm_def p_iff_sats)

lemma nth_closed :
  assumes "0\<in>A" "env\<in>list(A)"
  shows "nth(n,env)\<in>A" 
  using assms(2,1) unfolding nth_def by (induct env; simp)

context forcing_data
begin

(*
  "PHcheck(o,f,y,p) == \<exists>fy[##M]. fun_apply(##M,f,y,fy) \<and> pair(##M,fy,o,p)"
*)
definition
  PHcheck_fm :: "[i,i,i,i] \<Rightarrow> i" where
  "PHcheck_fm(o,f,y,p) == Exists(And(fun_apply_fm(succ(f),succ(y),0)
                                 ,pair_fm(0,succ(o),succ(p))))"

lemma PHcheck_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat; u \<in> nat |] ==> PHcheck_fm(x,y,z,u) \<in> formula"
  by (simp add:PHcheck_fm_def)

lemma sats_PHcheck_fm [simp]: 
  "[| x \<in> nat; y \<in> nat; z \<in> nat; u \<in> nat ; env \<in> list(M)|]
    ==> sats(M,PHcheck_fm(x,y,z,u),env) \<longleftrightarrow> 
        PHcheck(nth(x,env),nth(y,env),nth(z,env),nth(u,env))" 
  using zero_in_M Names.nth_closed by (simp add: PHcheck_def PHcheck_fm_def)

(* 
  "is_Hcheck(o,z,f,hc)  == is_Replace(##M,z,PHcheck(o,f),hc)"
*)
definition
  is_Hcheck_fm :: "[i,i,i,i] \<Rightarrow> i" where
  "is_Hcheck_fm(o,z,f,hc) == is_Replace_fm(z,PHcheck_fm(succ(succ(o)),succ(succ(f)),0,1),hc)" 

lemma is_Hcheck_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat; u \<in> nat |] ==> is_Hcheck_fm(x,y,z,u) \<in> formula"
  by (simp add:is_Hcheck_fm_def)

lemma sats_is_Hcheck_fm [simp]: 
  "[| x \<in> nat; y \<in> nat; z \<in> nat; u \<in> nat ; env \<in> list(M)|]
    ==> sats(M,is_Hcheck_fm(x,y,z,u),env) \<longleftrightarrow> 
        is_Hcheck(nth(x,env),nth(y,env),nth(z,env),nth(u,env))" 
  apply (simp add: is_Hcheck_def is_Hcheck_fm_def)
  apply (rule sats_is_Rep_fm,simp+)
  done


(* instance of replacement for hcheck *)
lemma wfrec_Hcheck : 
  assumes
      "X\<in>M" 
    shows 
      "wfrec_replacement(##M,is_Hcheck(one),rcheck(X))"
proof -
  have "is_Hcheck(one,a,b,c) \<longleftrightarrow> 
        sats(M,is_Hcheck_fm(8,2,1,0),[c,b,a,d,e,y,x,z,one,rcheck(x)])"
    if "a\<in>M" "b\<in>M" "c\<in>M" "d\<in>M" "e\<in>M" "y\<in>M" "x\<in>M" "z\<in>M" 
    for a b c d e y x z
    using that one_in_M \<open>X\<in>M\<close> rcheck_in_M by simp
  then have 1:"sats(M,is_wfrec_fm(is_Hcheck_fm(8,2,1,0),4,1,0),
                    [y,x,z,one,rcheck(X)]) \<longleftrightarrow>
            is_wfrec(##M, is_Hcheck(one),rcheck(X), x, y)"
    if "x\<in>M" "y\<in>M" "z\<in>M" for x y z
    using  that sats_is_wfrec_fm \<open>X\<in>M\<close> rcheck_in_M one_in_M by simp
  let 
    ?f="Exists(And(pair_fm(1,0,2),
               is_wfrec_fm(is_Hcheck_fm(8,2,1,0),4,1,0)))"
  have satsf:"sats(M, ?f, [x,z,one,rcheck(X)]) \<longleftrightarrow>
              (\<exists>y\<in>M. pair(##M,x,y,z) & is_wfrec(##M, is_Hcheck(one),rcheck(X), x, y))" 
    if "x\<in>M" "z\<in>M" for x z
    using that 1 \<open>X\<in>M\<close> rcheck_in_M one_in_M by (simp del:pair_abs)
  have artyf:"arity(?f) = 4" 
    unfolding is_wfrec_fm_def is_Hcheck_fm_def is_Replace_fm_def PHcheck_fm_def
              pair_fm_def upair_fm_def is_recfun_fm_def fun_apply_fm_def big_union_fm_def
              pre_image_fm_def restriction_fm_def image_fm_def
    by (simp add:nat_simp_union)
  then
  have 3:"sats(M,?f,[x,z,one,rcheck(X),one]) \<longleftrightarrow> sats(M,?f,[x,z,one,rcheck(X)])"
    if "x\<in>M" "z\<in>M" for x z    
    using that 1 \<open>X\<in>M\<close> one_in_M rcheck_in_M arity_sats1_iff[of ?f "[z,one,rcheck(X)]" x M "[one]"] 
          by simp
  have "strong_replacement(##M,\<lambda>x z. sats(M,?f,[x,z,one,rcheck(X),one]))"
    using replacement_ax 1 artyf \<open>X\<in>M\<close> rcheck_in_M one_in_M by simp
  then 
  have "strong_replacement(##M,\<lambda>x z. sats(M,?f,[x,z,one,rcheck(X)]))"
    using  strong_replacement_cong[of "##M" "\<lambda>x z. sats(M,?f,[x,z,one,rcheck(X),one])" 
                                            "\<lambda>x z. sats(M,?f,[x,z,one,rcheck(X)])"] 3 by simp
  then
  have "strong_replacement(##M,\<lambda>x z.
          \<exists>y\<in>M. pair(##M,x,y,z) & is_wfrec(##M, is_Hcheck(one),rcheck(X), x, y))"
    using repl_sats[of M ?f "[one,rcheck(X)]"]  satsf by (simp del:pair_abs)
  then 
  show ?thesis unfolding wfrec_replacement_def by simp
qed

lemma repl_PHcheck :
  assumes
    "f\<in>M" 
  shows
    "strong_replacement(##M,PHcheck(one,f))" 
proof -
  have "arity(PHcheck_fm(2,3,0,1)) = 4" 
    unfolding PHcheck_fm_def fun_apply_fm_def big_union_fm_def pair_fm_def image_fm_def 
              upair_fm_def
    by (simp add:nat_simp_union)
  with \<open>f\<in>M\<close>
  have "strong_replacement(##M,\<lambda>x y. sats(M,PHcheck_fm(2,3,0,1),[x,y,one,f]))"
    using replacement_ax one_in_M by simp
  with \<open>f\<in>M\<close>
  show ?thesis using one_in_M unfolding strong_replacement_def univalent_def by simp
qed

lemma univ_PHcheck : "\<lbrakk> z\<in>M ; f\<in>M \<rbrakk> \<Longrightarrow> univalent(##M,z,PHcheck(one,f))" 
  unfolding univalent_def PHcheck_def by simp

lemma relation2_Hcheck : 
  "relation2(##M,is_Hcheck(one),Hcheck)"
proof -
  have 1:"\<lbrakk>x\<in>z; PHcheck(one,f,x,y) \<rbrakk> \<Longrightarrow> (##M)(y)"
    if "z\<in>M" "f\<in>M" for z f x y
    using that unfolding PHcheck_def by simp
  have "is_Replace(##M,z,PHcheck(one,f),hc) \<longleftrightarrow> hc = Replace(z,PHcheck(one,f))" 
    if "z\<in>M" "f\<in>M" "hc\<in>M" for z f hc
    using that Replace_abs[OF _ _ univ_PHcheck 1] by simp
  with def_PHcheck
  show ?thesis 
    unfolding relation2_def is_Hcheck_def Hcheck_def by simp
qed

lemma PHcheck_closed : 
  "\<lbrakk>z\<in>M ; f\<in>M ; x\<in>z; PHcheck(one,f,x,y) \<rbrakk> \<Longrightarrow> (##M)(y)"
  unfolding PHcheck_def by simp

lemma Hcheck_closed :
  "\<forall>y\<in>M. \<forall>g\<in>M. function(g) \<longrightarrow> Hcheck(y,g)\<in>M"
proof -
  have "Replace(y,PHcheck(one,f))\<in>M"
    if "f\<in>M" "y\<in>M" for f y
    using that repl_PHcheck  PHcheck_closed[of y f] univ_PHcheck
          strong_replacement_closed
    by (simp del:setclass_iff add:setclass_iff[symmetric])
  then show ?thesis using def_PHcheck by auto
qed

lemma wf_rcheck : "x\<in>M \<Longrightarrow> wf(rcheck(x))" 
  unfolding rcheck_def using wf_trancl[OF wf_Memrel] .

lemma trans_rcheck : "x\<in>M \<Longrightarrow> trans(rcheck(x))"
  unfolding rcheck_def using trans_trancl .

lemma relation_rcheck : "x\<in>M \<Longrightarrow> relation(rcheck(x))" 
  unfolding rcheck_def using relation_trancl .

lemma check_in_M : "x\<in>M \<Longrightarrow> check(x) \<in> M"
  unfolding transrec_def 
  using wfrec_Hcheck[of x] check_trancl wf_rcheck trans_rcheck relation_rcheck rcheck_in_M
        Hcheck_closed relation2_Hcheck trans_wfrec_closed[of "rcheck(x)" x "is_Hcheck(one)" Hcheck] 
  by (simp del:setclass_iff add:setclass_iff[symmetric])

lemma check_abs :
    "\<lbrakk> x\<in>M ; z\<in>M \<rbrakk> \<Longrightarrow> is_wfrec(##M,is_Hcheck(one),rcheck(x),x,z) \<longleftrightarrow> z = check(x)"
  unfolding check_trancl 
  using wfrec_Hcheck[of x] check_trancl wf_rcheck trans_rcheck relation_rcheck rcheck_in_M
        Hcheck_closed relation2_Hcheck trans_wfrec_abs[of "rcheck(x)" x z "is_Hcheck(one)" Hcheck]
  by (simp del:setclass_iff  add:setclass_iff[symmetric])


lemma M_subset_MG :  "one \<in> G \<Longrightarrow> M \<subseteq> M[G]"
  using check_in_M one_in_P GenExtI
  by (intro subsetI, subst valcheck [of G,symmetric], auto)


(* Internalization of check *)

end (* forcing_data *)


(* Other assumptions over M. This will be removed
   when Interface is completed 


  assumes 
    f_abs: "\<And>x y. \<lbrakk> x\<in>M; y\<in>M \<rbrakk> \<Longrightarrow> is_F(##M,x,y) \<longleftrightarrow> y = f(x)"
    and
    f_sats: "\<And>x y. \<lbrakk>x\<in>M ; y\<in>M \<rbrakk> \<Longrightarrow> 
             sats(M,f_fm,Cons(x,Cons(y,env))) \<longleftrightarrow> is_F(##M,x,y)"
    and
    f_form: "f_fm \<in> formula" 
    and 
    f_arty: "arity(f_fm) = 2" 
    and
    "env\<in>list(M)"
  shows
    "strong_replacement(##M, \<lambda>x y. y = f(x))"

*)
locale M_extra_assms = forcing_data +
  assumes
    repl_check_pair : "strong_replacement(##M,\<lambda>p y. y =<check(p),p>)"
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