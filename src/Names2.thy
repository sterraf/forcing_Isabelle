theory Names2 imports Forcing_data Interface2 Recursion_Thms begin

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
   
text\<open>The well founded relation on which @{term val} is defined\<close>

definition
  ed :: "[i,i] \<Rightarrow> o" where
  "ed(x,y) == x \<in> domain(y)"
  
definition
  edrel :: "i \<Rightarrow> i" where
  "edrel(A) == {<x,y> \<in> A*A . x \<in> domain(y)}"

lemma edrel_dest [dest]: "x \<in> edrel(A) \<Longrightarrow> \<exists> a\<in> A. \<exists> b \<in> A. x =<a,b>"
  by(auto simp add:edrel_def)
    
lemma edrelI [intro!]: "x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> x \<in> domain(y) \<Longrightarrow> <x,y>\<in>edrel(A)"
  by (simp add:edrel_def)
    
lemma edrel_trans: "Transset(A) \<Longrightarrow> y\<in>A \<Longrightarrow> x \<in> domain(y) \<Longrightarrow> <x,y>\<in>edrel(A)"
   by (rule edrelI, auto simp add:Transset_def domain_def Pair_def)

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
    
lemma eq_sub_trans :  "x=y \<Longrightarrow> y\<subseteq>z \<Longrightarrow> x\<subseteq>z"
                "x\<subseteq>y \<Longrightarrow> y=z \<Longrightarrow> x\<subseteq>z"
  by simp_all
    
    
lemma SepReplace_iff [simp]: "y\<in>{b(x) .. x\<in>A, P(x)} \<longleftrightarrow> (\<exists>x\<in>A. y=b(x) & P(x))"
   by (auto simp add:SepReplace_def)

    
context forcing_data
begin  (*************** CONTEXT: forcing_data *****************)

definition 
  Hcheck :: "[i,i] \<Rightarrow> i" where
  "Hcheck(z,f)  == { <f`y,one> . y \<in> z}"

definition
  check :: "i \<Rightarrow> i" where
  "check(x) == wfrec(Memrel(eclose({x})), x , Hcheck)"

lemma  aux_def_check:
  "(\<lambda>x\<in>y. wfrec(Memrel(eclose({y})), x, Hcheck)) = 
   (\<lambda>x\<in>y. wfrec(Memrel(eclose({x})), x, Hcheck))"
  apply (rule lam_cong)
   defer 1 apply (rule wfrec_eclose_eq)
    defer 1 apply (rule ecloseD, auto simp add: arg_into_eclose)
  done
    
lemma def_check : "check(y) = { <check(w),one> . w \<in> y}"
proof -
  let 
              ?r="\<lambda>y. Memrel(eclose({y}))"
  from wf_Memrel have
       wfr:   "\<forall>w . wf(?r(w))" ..
  with wfrec [of "?r(y)" y "Hcheck"] have
              "check(y)= 
               Hcheck( y, \<lambda>x\<in>?r(y) -`` {y}. wfrec(?r(y), x, Hcheck))"
    by (simp add:check_def)
  also have 
              " ... = Hcheck( y, \<lambda>x\<in>y. wfrec(?r(y), x, Hcheck))"
    by (simp add:under_Memrel_eclose arg_into_eclose)
  also have 
              " ... = Hcheck( y, \<lambda>x\<in>y. check(x))"
    using aux_def_check by (simp add:check_def)
  finally show ?thesis by (simp add:Hcheck_def)
qed

definition
  Hv :: "i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>i" where
  "Hv(G,x,f) == { f`y .. y\<in> domain(x), \<exists>p\<in>P. <y,p> \<in> x \<and> p \<in> G }"

definition
  val :: "i\<Rightarrow>i\<Rightarrow>i" where
  "val(G,\<tau>) == wfrec(edrel(eclose({\<tau>})), \<tau> ,Hv(G))"

definition
  GenExt :: "i\<Rightarrow>i"     ("M[_]" 90)
  where "GenExt(G)== {val(G,\<tau>). \<tau> \<in> M}"
   
    
lemma dom_under_edrel_eclose: "edrel(eclose({x})) -`` {x}= domain(x)" 
  apply(simp add:edrel_def,rule,rule,drule underD,simp,rule,rule underI,auto)
  apply(rule_tac A="{xa}" in ecloseD)
  apply(subst (asm) Pair_def)
  apply(rule_tac A="{{xa,xa},{xa,y}}" in ecloseD)
  apply(rule_tac A="x" in ecloseD,auto simp add:arg_into_eclose)
done

lemma edrel_prop :
  assumes "z \<in> domain(x)"
  shows   "tr_down(edrel(eclose({x})),z) \<subseteq> eclose({z})"
          "rel_restrict(edrel(eclose({x})),eclose({z})) = edrel(eclose({z}))"
 sorry
  
lemma aux_def_val: 
  assumes "z \<in> domain(x)"
  shows "wfrec(edrel(eclose({x})),z,Hv(G)) = wfrec(edrel(eclose({z})),z,Hv(G))"
proof -
  let ?r="\<lambda>x . edrel(eclose({x}))"
  have "z\<in>eclose({z})" using arg_in_eclose_sing .
  moreover have "relation(?r(x))" using relation_edrel .
  moreover have "wf(?r(x))" using wf_edrel .    
  moreover have "tr_down(?r(x),z) \<subseteq> eclose({z})" using assms edrel_prop by simp
  ultimately   have 
    "wfrec(?r(x),z,Hv(G)) = wfrec(rel_restrict(?r(x),eclose({z})),z,Hv(G))"
    using wfrec_restr by simp
  also have "... = wfrec(?r(z),z,Hv(G))" using assms edrel_prop by simp
  finally  show ?thesis .
qed  
  
lemma def_val:  "val(G,x) = {val(G,t) .. t\<in>domain(x) , \<exists>p\<in>P .  <t,p>\<in>x \<and> p \<in> G }"
proof -
  let
            ?r="\<lambda>\<tau> . edrel(eclose({\<tau>}))"
  let
            ?f="\<lambda>z\<in>?r(x)-``{x}. wfrec(?r(x),z,Hv(G))"
  have
            "\<forall>\<tau>. wf(?r(\<tau>))"
    by (simp add: wf_edrel)
  with wfrec [of "?r(x)" x "Hv(G)"] have
            "val(G,x) = Hv(G,x,?f)"
    by (simp add:val_def)
  also have
            " ... = Hv(G,x,\<lambda>z\<in>domain(x). wfrec(?r(x),z,Hv(G)))"
    by (simp add:dom_under_edrel_eclose)
  also have
            " ... = Hv(G,x,\<lambda>z\<in>domain(x). val(G,z))"
    using aux_def_val by (simp add:val_def)
  finally show ?thesis by (simp add:Hv_def SepReplace_def)
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

lemma dom_edrel : "domain(A) \<subseteq> edrel(eclose({A}))-``{A}"
  sorry
    
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
  have Eq1 : "t \<in> domain({x \<in> A \<times> P . Q(x)}) \<Longrightarrow> 
    val(G,t) = (\<lambda>z\<in>edrel(eclose({{x \<in> A \<times> P . Q(x)}})) -`` {{x \<in> A \<times> P . Q(x)}}. val(G, z)) ` t"  for t
    using dom_edrel  sorry
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
    from dom_edrel have
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
      
end    (*************** CONTEXT: forcing_data *****************)



end
