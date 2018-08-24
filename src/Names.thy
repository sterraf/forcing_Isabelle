theory Names imports Forcing_data  begin

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

    
lemma SepReplace_dom_implies :
   "\<forall>x\<in>A. b(x) = b'(x)\<Longrightarrow> {b(x) .. x\<in>A, Q(x)}={b'(x) .. x\<in>A, Q(x)}"
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

lemma edrelI [intro!]: "x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> x \<in> domain(y) \<Longrightarrow> <x,y>\<in>edrel(A)"
  by (simp add:edrel_def)
    
lemma edrelD [dest] : "<x,y>\<in>edrel(A)\<Longrightarrow> x \<in> domain(y)"
  by (simp add:edrel_def)
    
lemma edrel_trans: "Transset(A) \<Longrightarrow> y\<in>A \<Longrightarrow> x \<in> domain(y) \<Longrightarrow> <x,y>\<in>edrel(A)"
   by (rule edrelI, auto simp add:Transset_def domain_def Pair_def)

lemma edrel_trans_iff: "Transset(A) \<Longrightarrow> y\<in>A \<Longrightarrow> x \<in> domain(y) \<longleftrightarrow> <x,y>\<in>edrel(A)"
  by (auto simp add: edrel_trans, auto simp add:Transset_def Pair_def)

lemma edrel_domain: "x\<in> M \<Longrightarrow> edrel(eclose(M)) -`` {x} = domain(x)"
  apply (rule equalityI, auto , subgoal_tac "Transset(eclose(M))", rule vimageI)
    apply (auto simp add: edrelI Transset_eclose)
   apply (rename_tac y z)
   apply (rule_tac A="{y}" in ecloseD)
    apply (rule_tac A="\<langle>y, z\<rangle>" in ecloseD)
    apply (rule_tac A="x" in ecloseD)
     apply (tactic {* distinct_subgoals_tac *})
    apply (auto simp add: Pair_def arg_into_eclose)
  done

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

lemma upairM : "x \<in> M \<Longrightarrow> y \<in> M \<Longrightarrow> {x,y} \<in> M"
   by(insert upair_ax, auto simp add: upair_ax_def)

lemma pairM : "x \<in>  M \<Longrightarrow> y \<in> M \<Longrightarrow> <x,y> \<in> M"
  by(unfold Pair_def, rule upairM,(rule upairM,simp+)+)

lemma funApp : "(\<And>x . x \<in> u \<Longrightarrow> f(x) \<in> M) \<Longrightarrow> a \<in> M \<Longrightarrow> u \<in> M \<Longrightarrow>
  (##M)(Replace(u, \<lambda> y z . z = <f(y),a>))"
 apply(rule_tac P="\<lambda> y z . z = <f(y),a>" in strong_replacement_closed)
 prefer 2 apply(simp)
 prefer 3 apply(simp_all,rule pairM)
 apply((simp add: trans_M Transset_M)+)
 apply(insert replacement)
  apply(unfold strong_replacement_def,simp,clarsimp)
  sorry

lemma funApp2 : "Replace(u,\<lambda> y z . z = <f(y),a>) = { <f(y),a> . y \<in> u}"
  by(auto)
    
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

  
lemma checkin : "x \<in> M \<Longrightarrow> (\<forall> y  \<in> x . check(y) \<in> M) \<Longrightarrow> (##M)(check(x))"
  apply(subst def_check)
  apply(subst funApp2[symmetric])
  apply(rule funApp,auto)
  apply(insert one_in_P P_in_M transM,simp)
done
    
lemma check_M_aux : "(##M)(x) \<longrightarrow> (##M)(check(x))"
  apply(rule_tac P="\<lambda> z . (##M)(z) \<longrightarrow> (##M)(check(z))" and a="x" in eps_induct)
  apply(rule impI,rule checkin,simp+)
  apply(subgoal_tac "\<forall> y \<in> x . y \<in> M",simp)
  apply(insert one_in_P P_in_M transM,simp)
done  

theorem check_M : "x \<in> M \<Longrightarrow> check(x) \<in> M"
  by(insert check_M_aux,simp)
    
definition
  Hv :: "i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>i" where
  "Hv(G,x,f) == { f`y .. y\<in> domain(x), \<exists>p\<in>P. <y,p> \<in> x \<and> p \<in> G }"

definition
  val :: "i\<Rightarrow>i\<Rightarrow>i" where
  "val(G,\<tau>) == wfrec(edrel(eclose(M)), \<tau> ,Hv(G))"

definition
  GenExt :: "i\<Rightarrow>i"     ("M[_]")
  where "GenExt(G)== {val(G,\<tau>). \<tau> \<in> M}"
  
lemma def_val:  "x\<in>M \<Longrightarrow> val(G,x) = {val(G,t) .. t\<in>domain(x) , \<exists>p\<in>P .  \<langle>t, p\<rangle>\<in>x \<and> p \<in> G }"
proof -
  assume
      asm:  "x\<in>M"
  let
            ?r="edrel(eclose(M))"
  let
            ?f="\<lambda>z\<in>?r-``{x}. wfrec(?r,z,Hv(G))"
  have
            "\<forall>\<tau>. wf(?r)"
    by (simp add: wf_edrel)
  with wfrec [of "?r" x "Hv(G)"] have
            "val(G,x) = Hv(G,x,?f)"
    by (simp add:val_def)
  also have
            " ... = Hv(G,x,\<lambda>z\<in>domain(x). wfrec(?r,z,Hv(G)))"
    using asm and edrel_domain by (simp) 
  also have
            " ... = Hv(G,x,\<lambda>z\<in>domain(x). val(G,z))"
    by (simp add:val_def)
  finally show ?thesis by (simp add:Hv_def SepReplace_def)
qed

lemma elem_of_val: "\<pi> \<in> M \<Longrightarrow> x\<in>val(G,\<pi>) \<longrightarrow> (\<exists>\<theta>\<in>domain(\<pi>). val(G,\<theta>) = x)"
  by (auto simp add:def_val)

lemma val_mono : "x\<in>M \<Longrightarrow> y\<in>M \<Longrightarrow> x\<subseteq>y \<Longrightarrow> val(G,x) \<subseteq> val(G,y)"
  by (force simp add: def_val)
  
lemma def_GenExt1 : 
  "x \<in> M[G] \<Longrightarrow> \<exists>\<tau>\<in>M. x = val(G,\<tau>)"
  apply (unfold GenExt_def)
  apply (rule RepFun_iff [THEN iffD1],assumption)
  done
    
lemma def_GenExt2 : 
  "x \<in> M \<Longrightarrow> val(G,x) \<in> M[G]"
  apply (simp add: GenExt_def)
  apply auto
done
  
lemma val_of_name : 
  "{x\<in>A\<times>P. Q(x)} \<in> M \<Longrightarrow>
   val(G,{x\<in>A\<times>P. Q(x)}) = {val(G,t) .. t\<in>A , \<exists>p\<in>P .  Q(<t,p>) \<and> p \<in> G }"
proof -
  let
              ?n="{x\<in>A\<times>P. Q(x)}" and
              ?r="edrel(eclose(M))"
  assume
        asm:  "?n \<in> M"
  let
              ?f="\<lambda>z\<in>?r-``{?n}. val(G,z)"
  have
              "\<forall>\<tau>. wf(?r)"
    by (simp add: wf_edrel)
  with val_def have
              "val(G,?n) = Hv(G,?n,?f)"
    by (rule_tac def_wfrec [of _ "?r" "Hv(G)"], simp_all)
  also have
              "... = {?f`t .. t\<in>domain(?n), \<exists>p\<in>P . <t,p>\<in>?n \<and> p\<in>G}"
    unfolding Hv_def by simp
  also have
              "... = { (if t\<in>?r-``{?n} then val(G,t) else 0) .. t\<in>domain(?n), \<exists>p\<in>P . <t,p>\<in>?n \<and> p\<in>G}"
    by (simp)
  also have
        Eq1:  "... = { val(G,t) .. t\<in>domain(?n), \<exists>p\<in>P . <t,p>\<in>?n \<and> p\<in>G}"
  proof -
    from edrel_domain and asm have
              "domain(?n) \<subseteq> ?r-``{?n}" 
      by simp
    then have
              "\<forall>t\<in>domain(?n). (if t\<in>?r-``{?n} then val(G,t) else 0) = val(G,t)"
      by auto
    then show 
              "{ (if t\<in>?r-``{?n} then val(G,t) else 0) .. t\<in>domain(?n), \<exists>p\<in>P . <t,p>\<in>?n \<and> p\<in>G} =
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

lemma valcheck : "y \<in> M \<Longrightarrow> one \<in> G \<Longrightarrow> \<forall>x\<in>M. check(x) \<in> M \<Longrightarrow> val(G,check(y))  = y"
proof (induct rule:eps_induct)
  case (1 y)
  then show ?case
  proof -
    from def_check have
          Eq1: "check(y) = { \<langle>check(w), one\<rangle> . w \<in> y}"  (is "_ = ?C") .
    with 1 have
          Eq2: "?C\<in>M" 
      by auto
    with 1 transD subsetD trans_M have 
        w_in_M : "\<forall> w \<in> y . w \<in> M" by force
    from Eq1 have
               "val(G,check(y)) = val(G, {\<langle>check(w), one\<rangle> . w \<in> y})"
      by simp
    also have
                " ...  = {val(G,t) .. t\<in>domain(?C) , \<exists>p\<in>P .  \<langle>t, p\<rangle>\<in>?C \<and> p \<in> G }"
      using def_val and Eq2 by simp
    also have
                " ... =  {val(G,t) .. t\<in>domain(?C) , \<exists>w\<in>y. t=check(w) }"
      using 1 and one_in_P by simp
    also have
                " ... = {val(G,check(w)) . w\<in>y }"
      by force
    also have
                " ... = y"
      using 1 and w_in_M by simp        
    finally show "val(G,check(y)) = y" 
      using 1 by simp
  qed
qed
  
end    (*************** CONTEXT: forcing_data *****************)

end