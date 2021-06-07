theory FrecR_Arities
  imports Arities FrecR
begin
lemma arity_fst_fm [arity] :
  "\<lbrakk>x\<in>nat ; t\<in>nat\<rbrakk> \<Longrightarrow> arity(fst_fm(x,t)) = succ(x) \<union> succ(t)"
  unfolding fst_fm_def
  using arity_pair_fm arity_empty_fm nat_union_abs2 pred_Un_distrib
  by auto

lemma arity_snd_fm [arity] :
  "\<lbrakk>x\<in>nat ; t\<in>nat\<rbrakk> \<Longrightarrow> arity(snd_fm(x,t)) = succ(x) \<union> succ(t)"
  unfolding snd_fm_def
  using arity_pair_fm arity_empty_fm nat_union_abs2 pred_Un_distrib
  by auto

lemma arity_snd_snd_fm [arity] :
  "\<lbrakk>x\<in>nat ; t\<in>nat\<rbrakk> \<Longrightarrow> arity(snd_snd_fm(x,t)) = succ(x) \<union> succ(t)"
  unfolding snd_snd_fm_def hcomp_fm_def
  using arity_snd_fm arity_empty_fm nat_union_abs2 pred_Un_distrib
  by auto

lemma arity_ftype_fm [arity] :
  "\<lbrakk>x\<in>nat ; t\<in>nat\<rbrakk> \<Longrightarrow> arity(ftype_fm(x,t)) = succ(x) \<union> succ(t)"
  unfolding ftype_fm_def
  using arity_fst_fm 
  by auto

lemma arity_name1_fm [arity] :
  "\<lbrakk>x\<in>nat ; t\<in>nat\<rbrakk> \<Longrightarrow> arity(name1_fm(x,t)) = succ(x) \<union> succ(t)"
  unfolding name1_fm_def hcomp_fm_def
  using arity_fst_fm arity_snd_fm nat_union_abs2 pred_Un_distrib
  by auto

lemma arity_name2_fm [arity] :
  "\<lbrakk>x\<in>nat ; t\<in>nat\<rbrakk> \<Longrightarrow> arity(name2_fm(x,t)) = succ(x) \<union> succ(t)"
  unfolding name2_fm_def hcomp_fm_def
  using arity_fst_fm arity_snd_snd_fm nat_union_abs2 pred_Un_distrib
  by auto

lemma arity_cond_of_fm [arity] :
  "\<lbrakk>x\<in>nat ; t\<in>nat\<rbrakk> \<Longrightarrow> arity(cond_of_fm(x,t)) = succ(x) \<union> succ(t)"
  unfolding cond_of_fm_def hcomp_fm_def
  using arity_snd_fm arity_snd_snd_fm nat_union_abs2 pred_Un_distrib
  by auto

lemma arity_eclose_n1_fm [arity] :
  "\<lbrakk>x\<in>nat ; t\<in>nat\<rbrakk> \<Longrightarrow> arity(eclose_n1_fm(x,t)) = succ(x) \<union> succ(t)"
  unfolding eclose_n1_fm_def 
  using arity_is_eclose_fm arity_singleton_fm arity_name1_fm nat_union_abs2 pred_Un_distrib
  by auto

lemma arity_eclose_n2_fm [arity] :
  "\<lbrakk>x\<in>nat ; t\<in>nat\<rbrakk> \<Longrightarrow> arity(eclose_n2_fm(x,t)) = succ(x) \<union> succ(t)"
  unfolding eclose_n2_fm_def 
  using arity_is_eclose_fm arity_singleton_fm arity_name2_fm nat_union_abs2 pred_Un_distrib
  by auto

lemma arity_ecloseN_fm [arity] :
  "\<lbrakk>x\<in>nat ; t\<in>nat\<rbrakk> \<Longrightarrow> arity(ecloseN_fm(x,t)) = succ(x) \<union> succ(t)"
  unfolding ecloseN_fm_def 
  using arity_eclose_n1_fm arity_eclose_n2_fm arity_union_fm nat_union_abs2 pred_Un_distrib
  by auto

lemma arity_frecR_fm [arity]:
  "\<lbrakk>a\<in>nat;b\<in>nat\<rbrakk> \<Longrightarrow> arity(frecR_fm(a,b)) = succ(a) \<union> succ(b)"
  unfolding frecR_fm_def
  using arity_ftype_fm arity_name1_fm arity_name2_fm arity_domain_fm 
      arity_empty_fm arity_union_fm pred_Un_distrib arity_succ_fm
  by auto
end