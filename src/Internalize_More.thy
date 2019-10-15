theory Internalize_More 
  imports 
    (* Internalizations *)
    "~~/src/ZF/Constructible/Separation"
    "~~/src/ZF/Constructible/Formula"
begin

(*  "dense_below(D,q) == \<forall>p\<in>P. \<langle>p,q\<rangle>\<in>leq \<longrightarrow> (\<exists>d\<in>D . \<langle>d,p\<rangle>\<in>leq)" *)
definition
  dense_below :: "[i,i,i,i] \<Rightarrow> o" where
  "dense_below(P,leq,D,q) == \<forall>p\<in>P. \<langle>p,q\<rangle>\<in>leq \<longrightarrow> (\<exists>d\<in>D . \<langle>d,p\<rangle>\<in>leq)"
  
definition
  is_dense_below :: "[i\<Rightarrow>o,i,i,i,i] \<Rightarrow> o" where
  "is_dense_below(M,P,leq,D,q) == 
    \<forall>p[M]. p\<in>P \<longrightarrow> (\<forall>z[M]. pair(M,p,q,z) \<and> z\<in>leq \<longrightarrow> 
        (\<exists>d[M]. \<exists>w[M]. d\<in>D \<and> pair(M,d,p,w) \<and> w\<in>leq))"

definition
  is_dense_below_fm :: "[i,i,i,i] \<Rightarrow> i" where
  "is_dense_below_fm(P,leq,D,q) == 
    Forall(Implies(Member(0,P#+1),Forall(Implies(And(pair_fm(1,q#+2,0),Member(0,leq#+2)), 
        Exists(Exists(And(Member(1,D#+4),And(pair_fm(1,3,0),Member(0,leq#+4)))))))))"
    
lemma is_dense_below_fm_type [TC]:
  "\<lbrakk> P\<in>nat ; leq\<in>nat ; D\<in>nat ; q\<in>nat \<rbrakk> \<Longrightarrow> is_dense_below_fm(P,leq,D,q) \<in>formula"
  unfolding is_dense_below_fm_def
  by (simp)
    
lemma sats_is_dense_below_fm :
  "\<lbrakk> P\<in>nat ; leq\<in>nat ; D\<in>nat ; q\<in>nat ; env\<in>list(A) \<rbrakk> \<Longrightarrow>
     sats(A,is_dense_below_fm(P,leq,D,q),env) \<longleftrightarrow> 
     is_dense_below(##A,nth(P, env), nth(leq, env), nth(D, env),nth(q, env))"
  unfolding is_dense_below_fm_def  is_dense_below_def
  by (simp)

schematic_goal sats_idbf_automatic:
  assumes 
    "P\<in>nat" "leq\<in>nat" "D\<in>nat" "q\<in>nat" "env\<in>list(A)"
  shows
    "is_dense_below(##A,nth(P, env), nth(leq, env), nth(D, env),nth(q, env))
    \<longleftrightarrow> sats(A,?idbf(P,leq,D,q),env)"
    and
    "(?idbf(P,leq,D,q) \<in> formula)"
   unfolding is_dense_below_def  
   by (insert assms ; (rule sep_rules | simp))+

(* The next line compiles, but it doesn't make sense to put it *)     
(* declare sats_idbf_automatic(2) [TC] *)
     
lemmas FOL_sats_iff = sats_Nand_iff sats_Forall_iff sats_Neg_iff sats_And_iff
  sats_Or_iff sats_Implies_iff sats_Iff_iff sats_Exists_iff 
  (* arity_Neg arity_And arity_Or arity_Implies arity_Iff arity_Exists *)
  
notepad begin
  fix P leq D q env A
  assume
    "P\<in>nat" "leq\<in>nat" "D\<in>nat" "q\<in>nat" "env\<in>list(A)"
  then obtain idbf where
    "is_dense_below(##A,nth(P, env), nth(leq, env), nth(D, env),nth(q, env))
    \<longleftrightarrow> sats(A,idbf(P,leq,D,q),env)"
    "idbf(P,leq,D,q) \<in> formula"
    using sats_idbf_automatic by (simp_all del:FOL_sats_iff)
end

notepad begin
  fix P leq D q A
  define env where "env == [P,leq,D,q]"
  assume
    "P\<in>A" "leq\<in>A" "D\<in>A" "q\<in>A"
  then
  obtain idbf where
    "is_dense_below(##A,nth(0,env),nth(1,env),nth(2,env),nth(3,env))
    \<longleftrightarrow> sats(A,idbf(0,1,2,3),env)"
    "idbf(0,1,2,3) \<in> formula"
    using sats_idbf_automatic[of 0 1 2 3 "env"] unfolding env_def 
    by (simp_all del:FOL_sats_iff)
  then 
  have "is_dense_below(##A,P,leq,D,q)
        \<longleftrightarrow> sats(A,idbf(0,1,2,3),[P,leq,D,q])"
    unfolding env_def by simp
end

context M_trivial 
begin  (************** CONTEXT: M_trivial ***************)
  
lemma is_dense_below_abs :
  "\<lbrakk> M(P); M(leq); M(D); M(q) \<rbrakk> \<Longrightarrow> 
   is_dense_below(M,P,leq,D,q) \<longleftrightarrow> dense_below(P,leq,D,q)"
  unfolding is_dense_below_def dense_below_def
  by (simp)


end    (************** CONTEXT: M_trivial ***************)
  
end
