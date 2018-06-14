theory Names2 imports Forcing_data ZFCAxioms_formula begin

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
    
lemma edrel_trans: "Transset(A) \<Longrightarrow> y\<in>A \<Longrightarrow> x \<in> domain(y) \<Longrightarrow> <x,y>\<in>edrel(A)"
   by (rule edrelI, auto simp add:Transset_def domain_def Pair_def)

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
  "Hcheck(z,f)  == { <f`y,uno> . y \<in> z}"

definition
  check :: "i \<Rightarrow> i" where
  "check(x) == wfrec(Memrel(eclose({x})), x , Hcheck)"

lemma  aux_check_simp:
  "(\<lambda>x\<in>y. wfrec(Memrel(eclose({y})), x, Hcheck)) = 
   (\<lambda>x\<in>y. wfrec(Memrel(eclose({x})), x, Hcheck))"
  apply (rule lam_cong)
   defer 1 apply (rule wfrec_eclose_eq)
    defer 1 apply (rule ecloseD, auto simp add: arg_into_eclose)
  done
    
lemma check_simp : "check(y) = { <check(w),uno> . w \<in> y}"
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
    using aux_check_simp by (simp add:check_def)
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
    
    
lemma val_of_name : 
       "val(G,{x\<in>A\<times>P. Q(x)}) = {val(G,t) .. t\<in>A , \<exists>p\<in>P .  Q(<t,p>) \<and> p \<in> G }"
proof -
  let
              ?n="{x\<in>A\<times>P. Q(x)}" and
              ?r="\<lambda>\<tau> . edrel(eclose({\<tau>}))"
  let
              ?f="\<lambda>z\<in>?r(?n)-``{?n}. val(G,z)"
  have
              "\<forall>\<tau>. wf(?r(\<tau>))"
    by (simp add: wf_edrel)
  with val_def have
              "val(G,?n) = Hv(G,?n,?f)"
    apply (simp)
      apply (rule def_wfrec [of _ "?r(?n)" "Hv(G)"], simp_all)
  also have
              "... = {?f`t .. t\<in>domain(?n), \<exists>p\<in>P . <t,p>\<in>?n \<and> p\<in>G}"
    unfolding Hv_def by simp
  also have
              "... = { (if t\<in>?r-``{?n} then val(G,t) else 0) .. t\<in>domain(?n), \<exists>p\<in>P . <t,p>\<in>?n \<and> p\<in>G}"
    by (simp)
  also have
        Eq1:  "... = { val(G,t) .. t\<in>domain(?n), \<exists>p\<in>P . <t,p>\<in>?n \<and> p\<in>G}"
  proof -
    from aux_VoN have
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
   (* by force *)
  finally show
              " val(G,?n)  = { val(G,t) .. t\<in>A, \<exists>p\<in>P . Q(<t,p>) \<and> p\<in>G}"
    by auto
qed

lemma val_check : "val(G,check(y)) = y"
proof -
  have
              "val(G,check(y)) = val"
    oops
      
end    (*************** CONTEXT: forcing_data *****************)



end