section\<open>Aids to internalize formulas\<close>
theory Internalizations
  imports 
    "ZF-Constructible.DPow_absolute"
    Synthetic_Definition
begin

text\<open>We found it useful to have slightly different versions of some 
results in ZF-Constructible:\<close>
lemma nth_closed :
  assumes "env\<in>list(A)" "0\<in>A"
  shows "nth(n,env)\<in>A" 
  using assms unfolding nth_def by (induct env; simp)

lemma mem_model_iff_sats [iff_sats]:
      "[| 0 \<in> A; nth(i,env) = x; env \<in> list(A)|]
       ==> (x\<in>A) \<longleftrightarrow> sats(A, Exists(Equal(0,0)), env)"
  using nth_closed[of env A i]
  by auto

lemma not_mem_model_iff_sats [iff_sats]:
      "[| 0 \<in> A; nth(i,env) = x; env \<in> list(A)|]
       ==> (\<forall> x . x \<notin> A) \<longleftrightarrow> sats(A, Neg(Exists(Equal(0,0))), env)"
  by auto

lemma top_iff_sats [iff_sats]:
  "env \<in> list(A) \<Longrightarrow> 0 \<in> A \<Longrightarrow> sats(A, Exists(Equal(0,0)), env)"
  by auto

lemma prefix1_iff_sats[iff_sats]:
  assumes
    "x \<in> nat" "env \<in> list(A)" "0 \<in> A" "a \<in> A"
  shows
    "a = nth(x,env) \<longleftrightarrow> sats(A, Equal(0,x#+1), Cons(a,env))"
    "nth(x,env) = a \<longleftrightarrow> sats(A, Equal(x#+1,0), Cons(a,env))"
    "a \<in> nth(x,env) \<longleftrightarrow> sats(A, Member(0,x#+1), Cons(a,env))"
    "nth(x,env) \<in> a \<longleftrightarrow> sats(A, Member(x#+1,0), Cons(a,env))"
  using assms nth_closed
  by simp_all

lemma prefix2_iff_sats[iff_sats]:
  assumes
    "x \<in> nat" "env \<in> list(A)" "0 \<in> A" "a \<in> A" "b \<in> A"
  shows
    "b = nth(x,env) \<longleftrightarrow> sats(A, Equal(1,x#+2), Cons(a,Cons(b,env)))"
    "nth(x,env) = b \<longleftrightarrow> sats(A, Equal(x#+2,1), Cons(a,Cons(b,env)))"
    "b \<in> nth(x,env) \<longleftrightarrow> sats(A, Member(1,x#+2), Cons(a,Cons(b,env)))"
    "nth(x,env) \<in> b \<longleftrightarrow> sats(A, Member(x#+2,1), Cons(a,Cons(b,env)))"
  using assms nth_closed
  by simp_all

lemma prefix3_iff_sats[iff_sats]:
  assumes
    "x \<in> nat" "env \<in> list(A)" "0 \<in> A" "a \<in> A" "b \<in> A" "c \<in> A"
  shows
    "c = nth(x,env) \<longleftrightarrow> sats(A, Equal(2,x#+3), Cons(a,Cons(b,Cons(c,env))))"
    "nth(x,env) = c \<longleftrightarrow> sats(A, Equal(x#+3,2), Cons(a,Cons(b,Cons(c,env))))"
    "c \<in> nth(x,env) \<longleftrightarrow> sats(A, Member(2,x#+3), Cons(a,Cons(b,Cons(c,env))))"
    "nth(x,env) \<in> c \<longleftrightarrow> sats(A, Member(x#+3,2), Cons(a,Cons(b,Cons(c,env))))"
  using assms nth_closed
  by simp_all

lemmas FOL_sats_iff = sats_Nand_iff sats_Forall_iff sats_Neg_iff sats_And_iff
  sats_Or_iff sats_Implies_iff sats_Iff_iff sats_Exists_iff 

lemma nth_ConsI: "\<lbrakk>nth(n,l) = x; n \<in> nat\<rbrakk> \<Longrightarrow> nth(succ(n), Cons(a,l)) = x"
by simp

lemmas nth_rules = nth_0 nth_ConsI nat_0I nat_succI
lemmas sep_rules = nth_0 nth_ConsI FOL_iff_sats function_iff_sats
                   fun_plus_iff_sats successor_iff_sats
                    omega_iff_sats FOL_sats_iff Replace_iff_sats

text\<open>Also a different compilation of lemmas (term\<open>sep_rules\<close>) used in formula
 synthesis\<close>
lemmas fm_defs = 
  omega_fm_def limit_ordinal_fm_def empty_fm_def typed_function_fm_def
  pair_fm_def upair_fm_def domain_fm_def function_fm_def succ_fm_def
  cons_fm_def fun_apply_fm_def image_fm_def big_union_fm_def union_fm_def
  relation_fm_def composition_fm_def field_fm_def ordinal_fm_def range_fm_def
  transset_fm_def subset_fm_def Replace_fm_def

lemmas formulas_def [fm_definitions] = fm_defs
  is_iterates_fm_def iterates_MH_fm_def is_wfrec_fm_def is_recfun_fm_def is_transrec_fm_def
  is_nat_case_fm_def quasinat_fm_def number1_fm_def ordinal_fm_def finite_ordinal_fm_def
  cartprod_fm_def sum_fm_def Inr_fm_def Inl_fm_def
  formula_functor_fm_def 
  Memrel_fm_def transset_fm_def subset_fm_def pre_image_fm_def restriction_fm_def
  list_functor_fm_def tl_fm_def quasilist_fm_def Cons_fm_def Nil_fm_def

lemmas sep_rules' [iff_sats]  = nth_0 nth_ConsI FOL_iff_sats function_iff_sats
  fun_plus_iff_sats omega_iff_sats FOL_sats_iff (* NOTE: why FOL_sats_iff? *)

end
