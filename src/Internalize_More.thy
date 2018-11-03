theory Internalize_More imports Internalize_no_repl Formula begin

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
  "\<lbrakk> P\<in>nat ; leq\<in>nat ; leq\<in>nat ; D\<in>nat ; q\<in>nat \<rbrakk> \<Longrightarrow> is_dense_below_fm(P,leq,D,q) \<in>formula"
  unfolding is_dense_below_fm_def
  by (simp)
    
lemma sats_is_dense_below_fm :
  "\<lbrakk> P\<in>nat ; leq\<in>nat ; leq\<in>nat ; D\<in>nat ; q\<in>nat ; env\<in>list(A) \<rbrakk> \<Longrightarrow>
     sats(A,is_dense_below_fm(P,leq,D,q),env) \<longleftrightarrow> 
     is_dense_below(##A,nth(P, env), nth(leq, env), nth(D, env),nth(q, env))"
  unfolding is_dense_below_fm_def  is_dense_below_def
  by (simp)

context M_trivial_no_repl 
begin  (************** CONTEXT: M_trivial_no_repl ***************)
  
lemma is_dense_below_abs :
  "\<lbrakk> M(P); M(leq); M(leq); M(D); M(q) \<rbrakk> \<Longrightarrow> 
   is_dense_below(M,P,leq,D,q) \<longleftrightarrow> dense_below(P,leq,D,q)"
  unfolding is_dense_below_def dense_below_def
  by (simp)


end    (************** CONTEXT: M_trivial_no_repl ***************)
  
end
