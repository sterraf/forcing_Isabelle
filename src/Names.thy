theory Names imports Forcing_data Interface2  begin

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
   "(\<And>x. Q(x) \<Longrightarrow> b(x) = b'(x))\<Longrightarrow> {b(x) .. x\<in>A, Q(x)}={b'(x) .. x\<in>A, Q(x)}"
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

lemma Rep_simp : "Replace(u,\<lambda> y z . z = f(y)) = { f(y) . y \<in> u}"
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

    
lemma field_Memrel : "x \<in> M \<Longrightarrow> field(Memrel(eclose({x}))) \<subseteq> M"
apply(rule subset_trans,rule field_rel_subset,rule Ordinal.Memrel_type)
apply(rule eclose_least,rule trans_M,auto)
  done
    
definition Hc_body_fm :: "i" where
  "Hc_body_fm == 
  Exists(Exists(
    And(pair_fm(1,0,4),
     Exists(And(fun_apply_fm(2,3,0),Exists(And(pair_fm(1,2,0),Equal(5,0))))))))" 
  
lemma [TC] : "Hc_body_fm \<in> formula"
  by (simp add: Hc_body_fm_def)
  
lemma [simp] : "arity(Hc_body_fm) = 3"
  by (simp add: Hc_body_fm_def pair_fm_def big_union_fm_def image_fm_def
        fun_apply_fm_def upair_fm_def Un_commute nat_union_abs1)

lemma pair_D1 : "<x,y> \<in> M \<Longrightarrow> x \<in> M"
  apply(subgoal_tac "{x} \<in> <x,y>")
   apply(rule subsetD,rule transD,rule trans_M)
    apply(rule subsetD,rule transD,rule trans_M)
  apply(auto simp add:Pair_def)
done

lemma one_in_M : "one \<in> M"
 by(rule subsetD,rule transD, rule trans_M, rule P_in_M,rule one_in_P)

lemma Hc_fm_sat : 
"f \<in> M \<Longrightarrow> (\<And> z y . \<lbrakk> (##M)(z) ;  (##M)(y) \<rbrakk> \<Longrightarrow>
  sats(M,Hc_body_fm,[z,y,<f,one>]) \<longleftrightarrow> y = <f`z, one>)"
  apply(rule iffI)
  apply(subgoal_tac "[z,y,<f,one>] \<in> list(M)", simp add: Hc_body_fm_def)
   apply(insert one_in_M, simp add:  pairM)
  apply(auto, auto simp add: one_in_M pair_D1)
  apply(subgoal_tac "[z,<f`z,one>,<f,one>] \<in> list(M)", simp add: Hc_body_fm_def)
   apply(simp add: one_in_M pairM)
  apply(auto, simp add:  pair_D1)
  apply(simp add: one_in_M pairM)
done

lemma Hc_type : 
    assumes "f\<in>M"
    and     "z\<in>M"    
    shows   "strong_replacement(##M, \<lambda> z y. y = <f`z,one>)"
proof -
  from pairM and one_in_M and assms have
    \<open><f,one> \<in> M\<close>
    by simp
  from replacement_ax have
    "\<forall> a\<in> M . strong_replacement(##M, \<lambda> z y . sats(M,Hc_body_fm,[z,y,a]))"
    by simp  
  with \<open><f,one> \<in> M\<close> have  
   A : "strong_replacement(##M, \<lambda> z y . sats(M,Hc_body_fm,[z,y,<f,one>]))" 
    by simp
  with \<open>f\<in>M\<close> show ?thesis 
    by(subst strong_replacement_cong[symmetric],simp add:Hc_fm_sat[symmetric],simp)
qed

(* Se puede borrar.
 
lemma Mem_ecloseI : 
  assumes "z \<in> x"
    and   "u \<in> z"
  shows "u \<in> Memrel(eclose({x})) -`` {z}"
proof -
   let ?ex = "eclose({x})"
    from \<open>z \<in> x\<close> and \<open>u \<in> z\<close>
    have "x \<in> ?ex"
      by (simp add: arg_into_eclose)
    then have \<open>z \<in> ?ex\<close> using \<open>z \<in> x\<close>
      by (rule ecloseD)
    then have \<open>u \<in> ?ex\<close> using \<open>u \<in> z\<close>
      by (rule ecloseD)
    then have \<open><u,z> \<in> Memrel(?ex)\<close> using \<open>u \<in> z\<close> and \<open>z \<in> ?ex\<close>
      by simp
    then show ?thesis by (simp add: underI)
qed
*)

lemma Hc_col_tc : "f \<in> M \<Longrightarrow> z \<in> M \<Longrightarrow>
     f \<in> Memrel(eclose({x})) -`` {z} -> M \<Longrightarrow> 
        (##M)(Replace(z,\<lambda> u y . y= <f`u,one>))"
  apply(rule strong_replacement_closed,simp add:Hc_type,simp+)
  apply(rule pairM)
  prefer 2 apply(simp add:one_in_M) 
  apply(case_tac "xa \<in> Memrel(eclose({x}))-``{z}",erule apply_type,simp)
  apply(subst apply_0,subst domain_of_fun,assumption+,rule zero_in_M)
  done

lemma Hc_col_tc' : "f \<in> M \<Longrightarrow> z \<in> M \<Longrightarrow>
     f \<in> Memrel(eclose({x})) -`` {z} -> M \<Longrightarrow> 
        (Replace(z,\<lambda> u y . y= <f`u,one>)) \<in> M" 
  by(insert Hc_col_tc,auto)
    
lemma checkin_M : "x \<in> M \<Longrightarrow> check(x) \<in> M"
  apply(unfold check_def,rule wfrec_type)
  apply(rule wf_Memrel,assumption)
  apply(erule field_Memrel)
  apply(rename_tac z f)
  apply(unfold Hcheck_def,subgoal_tac "f \<in> M")
  apply(subst Rep_simp[symmetric],simp add: Hc_col_tc')
  oops
    
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

lemma val_of_elem: "\<pi> \<in> M \<Longrightarrow> <\<theta>,p> \<in> \<pi> \<Longrightarrow> p\<in>G \<Longrightarrow> p\<in>P \<Longrightarrow> val(G,\<theta>) \<in> val(G,\<pi>)"
proof -
  assume
    "<\<theta>,p> \<in> \<pi>" 
  then have "\<theta>\<in>domain(\<pi>)" by auto
  assume
      "p\<in>G" "p\<in>P" "\<pi> \<in> M"
  with \<open>\<theta>\<in>domain(\<pi>)\<close> \<open><\<theta>,p> \<in> \<pi>\<close> have
    "val(G,\<theta>) \<in> {val(G,t) .. t\<in>domain(\<pi>) , \<exists>p\<in>P .  \<langle>t, p\<rangle>\<in>\<pi> \<and> p \<in> G }"
    by auto
  with \<open>\<pi>\<in>M\<close> show ?thesis
    using def_val by simp
qed
  
lemma elem_of_val: "\<pi> \<in> M \<Longrightarrow> x\<in>val(G,\<pi>) \<Longrightarrow> \<exists>\<theta>\<in>domain(\<pi>). val(G,\<theta>) = x"
  by (auto simp add:def_val)

lemma elem_of_val_pair: "\<pi> \<in> M \<Longrightarrow> x\<in>val(G,\<pi>) \<Longrightarrow> \<exists>\<theta>. \<exists>p\<in>G.  <\<theta>,p>\<in>\<pi> \<and> val(G,\<theta>) = x"
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