theory Arities 
  imports FrecR
    "../Constructible/Formula"
    "../Constructible/L_axioms"
begin

lemma upair_fm_arity : "\<lbrakk>  t1\<in>nat ; t2\<in>nat ; up\<in>nat  \<rbrakk> \<Longrightarrow> 
  arity(upair_fm(t1,t2,up)) = \<Union> {succ(t1),succ(t2),succ(up)}"
  unfolding  upair_fm_def
  using nat_union_abs1 nat_union_abs2 pred_Un   
  by auto


lemma pair_fm_arity : "\<lbrakk>  t1\<in>nat ; t2\<in>nat ; p\<in>nat  \<rbrakk> \<Longrightarrow> 
  arity(pair_fm(t1,t2,p)) = \<Union> {succ(t1),succ(t2),succ(p)}"
  unfolding pair_fm_def 
  using upair_fm_arity nat_union_abs1 nat_union_abs2 pred_Un
  by auto

lemma composition_fm_arity :
  "\<lbrakk> r\<in>nat ; s\<in>nat ; t\<in>nat \<rbrakk> \<Longrightarrow> arity(composition_fm(r,s,t)) = \<Union> {succ(r), succ(s), succ(t)}"
  unfolding composition_fm_def    
  using pair_fm_arity nat_union_abs1 nat_union_abs2 pred_Un_distrib
  by auto

lemma domain_fm_arity : 
    "\<lbrakk> r\<in>nat ; z\<in>nat \<rbrakk> \<Longrightarrow> arity(domain_fm(r,z)) = succ(r) \<union> succ(z)"
  unfolding domain_fm_def 
  using pair_fm_arity nat_union_abs1 nat_union_abs2 pred_Un_distrib
  by auto

lemma range_fm_arity : 
    "\<lbrakk> r\<in>nat ; z\<in>nat \<rbrakk> \<Longrightarrow> arity(range_fm(r,z)) = succ(r) \<union> succ(z)"
  unfolding range_fm_def 
  using pair_fm_arity nat_union_abs1 nat_union_abs2 pred_Un_distrib
  by auto

lemma union_fm_arity : 
  "\<lbrakk> x\<in>nat ; y\<in>nat ; z\<in>nat \<rbrakk> \<Longrightarrow> arity(union_fm(x,y,z)) = \<Union> {succ(x), succ(y), succ(z)}"
  unfolding union_fm_def
  using  nat_union_abs1 nat_union_abs2 pred_Un_distrib
  by auto

lemma image_fm_arity : 
  "\<lbrakk> x\<in>nat ; y\<in>nat ; z\<in>nat \<rbrakk> \<Longrightarrow> arity(image_fm(x,y,z)) = \<Union> {succ(x), succ(y), succ(z)}"
  unfolding image_fm_def
  using pair_fm_arity  nat_union_abs1 nat_union_abs2 pred_Un_distrib
  by auto

lemma pre_image_fm_arity : 
  "\<lbrakk> x\<in>nat ; y\<in>nat ; z\<in>nat \<rbrakk> \<Longrightarrow> arity(pre_image_fm(x,y,z)) = \<Union> {succ(x), succ(y), succ(z)}"
  unfolding pre_image_fm_def
  using pair_fm_arity  nat_union_abs1 nat_union_abs2 pred_Un_distrib
  by auto


lemma big_union_fm_arity : 
  "\<lbrakk> x\<in>nat ; y\<in>nat \<rbrakk> \<Longrightarrow> arity(big_union_fm(x,y)) = succ(x) \<union> succ(y)"
  unfolding big_union_fm_def
  using nat_union_abs1 nat_union_abs2 pred_Un_distrib
  by auto

lemma fun_apply_fm_arity : 
  "\<lbrakk> x\<in>nat ; y\<in>nat ; f\<in>nat \<rbrakk> \<Longrightarrow> 
    arity(fun_apply_fm(f,x,y)) =  succ(f) \<union> succ(x) \<union> succ(y)"
  unfolding fun_apply_fm_def
  using upair_fm_arity image_fm_arity big_union_fm_arity nat_union_abs2 pred_Un_distrib
  by auto

lemma field_fm_arity : 
    "\<lbrakk> r\<in>nat ; z\<in>nat \<rbrakk> \<Longrightarrow> arity(field_fm(r,z)) = succ(r) \<union> succ(z)"
  unfolding field_fm_def 
  using pair_fm_arity domain_fm_arity range_fm_arity union_fm_arity 
    nat_union_abs1 nat_union_abs2 pred_Un_distrib
  by auto

lemma empty_fm_arity : 
    "\<lbrakk> r\<in>nat \<rbrakk> \<Longrightarrow> arity(empty_fm(r)) = succ(r)"
  unfolding empty_fm_def 
  using nat_union_abs1 nat_union_abs2 pred_Un_distrib
  by simp

lemma function_fm_arity : 
    "\<lbrakk> r\<in>nat \<rbrakk> \<Longrightarrow> arity(function_fm(r)) = succ(r)"
  unfolding function_fm_def 
  using pair_fm_arity nat_union_abs1 nat_union_abs2 pred_Un_distrib
  by simp

lemma relation_fm_arity : 
    "\<lbrakk> r\<in>nat \<rbrakk> \<Longrightarrow> arity(relation_fm(r)) = succ(r)"
  unfolding relation_fm_def 
  using pair_fm_arity nat_union_abs1 nat_union_abs2 pred_Un_distrib
  by simp

lemma restriction_fm_arity : 
    "\<lbrakk> r\<in>nat ; z\<in>nat ; A\<in>nat \<rbrakk> \<Longrightarrow> arity(restriction_fm(A,z,r)) = succ(A) \<union> succ(r) \<union> succ(z)"
  unfolding restriction_fm_def 
  using pair_fm_arity nat_union_abs2 pred_Un_distrib
  by auto

lemma typed_function_fm_arity : 
  "\<lbrakk> x\<in>nat ; y\<in>nat ; f\<in>nat \<rbrakk> \<Longrightarrow> 
    arity(typed_function_fm(f,x,y)) = \<Union> {succ(f), succ(x), succ(y)}"
  unfolding typed_function_fm_def
  using pair_fm_arity relation_fm_arity function_fm_arity domain_fm_arity 
    nat_union_abs2 pred_Un_distrib
  by auto

lemma succ_fm_arity :
  "\<lbrakk>x\<in>nat;y\<in>nat\<rbrakk> \<Longrightarrow> arity(succ_fm(x,y)) = succ(x) \<union> succ(y)"
  unfolding succ_fm_def cons_fm_def 
  using upair_fm_arity union_fm_arity
    nat_union_abs2 pred_Un_distrib
  by auto

lemma subset_fm_arity : 
  "\<lbrakk>x\<in>nat ; y\<in>nat\<rbrakk> \<Longrightarrow> arity(subset_fm(x,y)) = succ(x) \<union> succ(y)"
  unfolding subset_fm_def 
  using nat_union_abs2 pred_Un_distrib
  by auto

lemma transset_fm_arity :
  "\<lbrakk>x\<in>nat\<rbrakk> \<Longrightarrow> arity(transset_fm(x)) = succ(x)"
  unfolding transset_fm_def 
  using subset_fm_arity nat_union_abs2 pred_Un_distrib
  by auto

lemma ordinal_fm_arity :
  "\<lbrakk>x\<in>nat\<rbrakk> \<Longrightarrow> arity(ordinal_fm(x)) = succ(x)"
  unfolding ordinal_fm_def 
  using transset_fm_arity nat_union_abs2 pred_Un_distrib
  by auto

lemma limit_ordinal_fm_arity :
  "\<lbrakk>x\<in>nat\<rbrakk> \<Longrightarrow> arity(limit_ordinal_fm(x)) = succ(x)"
  unfolding limit_ordinal_fm_def 
  using ordinal_fm_arity succ_fm_arity empty_fm_arity nat_union_abs2 pred_Un_distrib
  by auto

lemma finite_ordinal_fm_arity :
  "\<lbrakk>x\<in>nat\<rbrakk> \<Longrightarrow> arity(finite_ordinal_fm(x)) = succ(x)"
  unfolding finite_ordinal_fm_def 
  using ordinal_fm_arity limit_ordinal_fm_arity succ_fm_arity empty_fm_arity 
    nat_union_abs2 pred_Un_distrib
  by auto

lemma omega_fm_arity :
  "\<lbrakk>x\<in>nat\<rbrakk> \<Longrightarrow> arity(omega_fm(x)) = succ(x)"
  unfolding omega_fm_def 
  using limit_ordinal_fm_arity nat_union_abs2 pred_Un_distrib
  by auto

lemma fst_fm_arity :
  "\<lbrakk>x\<in>nat ; t\<in>nat\<rbrakk> \<Longrightarrow> arity(fst_fm(x,t)) = succ(x) \<union> succ(t)"
  unfolding fst_fm_def
  using pair_fm_arity empty_fm_arity nat_union_abs2 pred_Un_distrib
  by auto

lemma snd_fm_arity :
  "\<lbrakk>x\<in>nat ; t\<in>nat\<rbrakk> \<Longrightarrow> arity(snd_fm(x,t)) = succ(x) \<union> succ(t)"
  unfolding snd_fm_def
  using pair_fm_arity empty_fm_arity nat_union_abs2 pred_Un_distrib
  by auto

lemma snd_snd_fm_arity :
  "\<lbrakk>x\<in>nat ; t\<in>nat\<rbrakk> \<Longrightarrow> arity(snd_snd_fm(x,t)) = succ(x) \<union> succ(t)"
  unfolding snd_snd_fm_def hcomp_fm_def
  using snd_fm_arity empty_fm_arity nat_union_abs2 pred_Un_distrib
  by auto

lemma ftype_fm_arity :
  "\<lbrakk>x\<in>nat ; t\<in>nat\<rbrakk> \<Longrightarrow> arity(ftype_fm(x,t)) = succ(x) \<union> succ(t)"
  unfolding ftype_fm_def
  using fst_fm_arity 
  by auto

lemma name1_fm_arity :
  "\<lbrakk>x\<in>nat ; t\<in>nat\<rbrakk> \<Longrightarrow> arity(name1_fm(x,t)) = succ(x) \<union> succ(t)"
  unfolding name1_fm_def hcomp_fm_def
  using fst_fm_arity snd_fm_arity nat_union_abs2 pred_Un_distrib
  by auto

lemma name2_fm_arity :
  "\<lbrakk>x\<in>nat ; t\<in>nat\<rbrakk> \<Longrightarrow> arity(name2_fm(x,t)) = succ(x) \<union> succ(t)"
  unfolding name2_fm_def hcomp_fm_def
  using fst_fm_arity snd_snd_fm_arity nat_union_abs2 pred_Un_distrib
  by auto

lemma cond_of_fm_arity :
  "\<lbrakk>x\<in>nat ; t\<in>nat\<rbrakk> \<Longrightarrow> arity(cond_of_fm(x,t)) = succ(x) \<union> succ(t)"
  unfolding cond_of_fm_def hcomp_fm_def
  using snd_fm_arity snd_snd_fm_arity nat_union_abs2 pred_Un_distrib
  by auto

lemma singleton_fm_arity :
  "\<lbrakk>x\<in>nat ; t\<in>nat\<rbrakk> \<Longrightarrow> arity(singleton_fm(x,t)) = succ(x) \<union> succ(t)"
  unfolding singleton_fm_def cons_fm_def
  using union_fm_arity upair_fm_arity empty_fm_arity nat_union_abs2 pred_Un_distrib
  by auto

lemma Memrel_fm_arity :
  "\<lbrakk>x\<in>nat ; t\<in>nat\<rbrakk> \<Longrightarrow> arity(Memrel_fm(x,t)) = succ(x) \<union> succ(t)"
  unfolding Memrel_fm_def 
  using  pair_fm_arity nat_union_abs2 pred_Un_distrib
  by auto

lemma quasinat_fm_arity :
  "\<lbrakk>x\<in>nat\<rbrakk> \<Longrightarrow> arity(quasinat_fm(x)) = succ(x)"
  unfolding quasinat_fm_def cons_fm_def 
  using succ_fm_arity empty_fm_arity
    nat_union_abs2 pred_Un_distrib
  by auto

lemma is_recfun_fm_arity :
  "\<lbrakk>p\<in>formula ; v\<in>nat ; n\<in>nat; Z\<in>nat;i\<in>nat\<rbrakk> \<Longrightarrow>  arity(p) = i \<Longrightarrow> 
  arity(is_recfun_fm(p,v,n,Z)) = succ(v) \<union> succ(n) \<union> succ(Z) \<union> pred(pred(pred(pred(i))))"
  unfolding is_recfun_fm_def
  using upair_fm_arity pair_fm_arity pre_image_fm_arity restriction_fm_arity
    nat_union_abs2 pred_Un_distrib
  by auto

lemma is_wfrec_fm_arity :
  "\<lbrakk>p\<in>formula ; v\<in>nat ; n\<in>nat; Z\<in>nat ; i\<in>nat\<rbrakk> \<Longrightarrow> arity(p) = i \<Longrightarrow> 
    arity(is_wfrec_fm(p,v,n,Z)) = succ(v) \<union> succ(n) \<union> succ(Z) \<union> pred(pred(pred(pred(pred(i)))))"
  unfolding is_wfrec_fm_def
  using succ_fm_arity  is_recfun_fm_arity 
     nat_union_abs2 pred_Un_distrib
  by auto

lemma is_nat_case_fm_arity :
  "\<lbrakk>p\<in>formula ; v\<in>nat ; n\<in>nat; Z\<in>nat; i\<in>nat\<rbrakk> \<Longrightarrow> arity(p) = i \<Longrightarrow> 
    arity(is_nat_case_fm(v,p,n,Z)) = succ(v) \<union> succ(n) \<union> succ(Z) \<union> pred(pred(i))"
  unfolding is_nat_case_fm_def
  using succ_fm_arity empty_fm_arity quasinat_fm_arity 
    nat_union_abs2 pred_Un_distrib
  by auto

lemma iterates_MH_fm_arity :
  assumes "isF\<in>formula" "v\<in>nat" "n\<in>nat" "g\<in>nat" "z\<in>nat" "i\<in>nat" 
      "arity(isF) = i"
    shows "arity(iterates_MH_fm(isF,v,n,g,z)) = 
           succ(v) \<union> succ(n) \<union> succ(g) \<union> succ(z) \<union> pred(pred(pred(pred(i))))"
proof -
  let ?\<phi> = "Exists(And(fun_apply_fm(succ(succ(succ(g))), 2, 0), Forall(Implies(Equal(0, 2), isF))))"
  let ?ar = "succ(succ(succ(g))) \<union> pred(pred(i))"
  from assms
  have "arity(?\<phi>) =?ar" "?\<phi>\<in>formula" 
    using fun_apply_fm_arity
    nat_union_abs1 nat_union_abs2 pred_Un_distrib succ_Un_distrib Un_assoc[symmetric]
    by simp_all
  then
  show ?thesis
    unfolding iterates_MH_fm_def
    using is_nat_case_fm_arity[OF \<open>?\<phi>\<in>_\<close> _ _ _ _ \<open>arity(?\<phi>) = _\<close>] assms pred_succ_eq pred_Un_distrib
    by auto
qed

lemma is_iterates_fm_arity :
  assumes "p\<in>formula" "v\<in>nat" "n\<in>nat" "Z\<in>nat" "i\<in>nat" 
    "arity(p) = i"
  shows "arity(is_iterates_fm(p,v,n,Z)) = succ(v) \<union> succ(n) \<union> succ(Z) \<union> 
          pred(pred(pred(pred(pred(pred(pred(pred(pred(pred(pred(i)))))))))))"
proof -
  let ?\<phi> = "iterates_MH_fm(p, 7#+v, 2, 1, 0)"
  let ?\<psi> = "is_wfrec_fm(?\<phi>, 0, succ(succ(n)),succ(succ(Z)))"
  from \<open>v\<in>_\<close>
  have "arity(?\<phi>) = (8#+v) \<union> pred(pred(pred(pred(i))))" "?\<phi>\<in>formula"
    using assms iterates_MH_fm_arity nat_union_abs2
    by simp_all
  then
  have "arity(?\<psi>) = succ(succ(succ(n))) \<union> succ(succ(succ(Z))) \<union> (3#+v) \<union> 
      pred(pred(pred(pred(pred(pred(pred(pred(pred(i)))))))))"
    using assms is_wfrec_fm_arity[OF \<open>?\<phi>\<in>_\<close> _ _ _ _ \<open>arity(?\<phi>) = _\<close>] nat_union_abs1 pred_Un_distrib
    by auto
  then
  show ?thesis
    unfolding is_iterates_fm_def 
    using Memrel_fm_arity succ_fm_arity assms nat_union_abs1 pred_Un_distrib
    by auto
qed

lemma eclose_n_fm_arity :
  assumes "A\<in>nat" "x\<in>nat" "t\<in>nat" 
  shows "arity(eclose_n_fm(A,x,t)) = succ(A) \<union> succ(x) \<union> succ(t)"
proof -
  let ?\<phi> = "big_union_fm(1,0)"
  have "arity(?\<phi>) = 2" "?\<phi>\<in>formula" 
    using big_union_fm_arity nat_union_abs2
    by simp_all
  with assms
  show ?thesis
    unfolding eclose_n_fm_def
    using is_iterates_fm_arity[OF \<open>?\<phi>\<in>_\<close> _ _ _,of _ _ _ 2] 
    by auto
qed

lemma mem_eclose_fm_arity :
  assumes "x\<in>nat" "t\<in>nat"
  shows "arity(mem_eclose_fm(x,t)) = succ(x) \<union> succ(t)"
proof -  
  let ?\<phi>="eclose_n_fm(x #+ 2, 1, 0)"
  from \<open>x\<in>nat\<close>
  have "arity(?\<phi>) = x#+3" 
    using eclose_n_fm_arity nat_union_abs2 
    by simp
  with assms
  show ?thesis
    unfolding mem_eclose_fm_def 
    using finite_ordinal_fm_arity nat_union_abs2 pred_Un_distrib
    by simp
qed

lemma is_eclose_fm_arity :
  "\<lbrakk>x\<in>nat ; t\<in>nat\<rbrakk> \<Longrightarrow> arity(is_eclose_fm(x,t)) = succ(x) \<union> succ(t)"
  unfolding is_eclose_fm_def 
  using mem_eclose_fm_arity nat_union_abs2 pred_Un_distrib
  by auto

end