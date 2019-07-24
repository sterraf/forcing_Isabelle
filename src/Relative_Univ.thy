theory Relative_Univ
  imports
    Datatype_absolute

begin

(* "Vfrom(A,i) == transrec(i, %x f. A \<union> (\<Union>y\<in>x. Pow(f`y)))" *)
definition
  HVfrom :: "[i,i,i] \<Rightarrow> i" where
  "HVfrom(A,x,f) \<equiv> A \<union> (\<Union>y\<in>x. Pow(f`y))"

(* z = Pow(f`y) *)
definition
  is_powapply :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_powapply(M,f,y,z) \<equiv> \<exists>fy[M]. fun_apply(M,f,y,fy) \<and> powerset(M,fy,z)"

(* is_Replace(M,A,P,z) == \<forall>u[M]. u \<in> z \<longleftrightarrow> (\<exists>x[M]. x\<in>A & P(x,u)) *)
definition
  is_HVfrom :: "[i\<Rightarrow>o,i,i,i,i] \<Rightarrow> o" where
  "is_HVfrom(M,A,x,f,h) \<equiv> \<exists>U[M]. \<exists>R[M]. \<exists>P[M]. union(M,A,U,h) 
        \<and> big_union(M,R,U) \<and> is_Replace(M,x,is_powapply(M,f),R)" 

definition
  is_Vfrom :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_Vfrom(M,A,i,V) == is_transrec(M,is_HVfrom(M,A),i,V)"

context M_basic
begin

lemma is_powapply_abs: "\<lbrakk>M(f); M(y); M(z) \<rbrakk> \<Longrightarrow> is_powapply(M,f,y,z) \<longleftrightarrow> powerset(M, f ` y, z)"
  unfolding is_powapply_def by simp

lemma "\<lbrakk>M(A); M(x); M(f); M(h) \<rbrakk> \<Longrightarrow> 
      is_HVfrom(M,A,x,f,h) \<longleftrightarrow> (\<exists>R[M]. h =A \<union> \<Union>R \<and> Ex(M) \<and> is_Replace(M, x, \<lambda>x y. powerset(M, f ` x, y), R))"
  using is_powapply_abs unfolding is_HVfrom_def by auto

end

end