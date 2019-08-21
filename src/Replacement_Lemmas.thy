theory Replacement_Lemmas
  imports
    Relative

begin

context M_basic begin

lemma 
  assumes 
    "strong_replacement(M,\<lambda>x y. y = <x,F(x)>)"
    "strong_replacement(M,\<lambda>x y. y = <x,G(x)>)"
  shows
    "strong_replacement(M,\<lambda>x y. y = <x,F(G(x))>)"
  unfolding strong_replacement_def
proof
  fix A
  have "\<And>B H. univalent(M, B, \<lambda>x y. y = H(x))" 
    by simp
  assume "M(A)"
  moreover 
  note assms
  ultimately 
  obtain Y where "M(Y)" "\<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> b = \<langle>x, G(x)\<rangle>)"
    unfolding strong_replacement_def by force
  then 
  oops
    
lemma 
  assumes 
    "strong_replacement(M,\<lambda>p y. y = <p,F(p)>)"
    "strong_replacement(M,\<lambda>p y. y = <p,G(p)>)"
  shows
    "strong_replacement(M,\<lambda>p y. y = <p,<F(p),G(p)>>)"
  unfolding strong_replacement_def
proof 
  fix A
  have unv:"\<And>B H. univalent(M, B, \<lambda>x y. y = \<langle>x, H(x)\<rangle>)" 
    by simp
  moreover 
  assume "M(A)"
  moreover 
  note assms
  ultimately 
  obtain X Y where "M(X)" "\<forall>b[M]. b \<in> X \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> b = \<langle>x, F(x)\<rangle>)"
    "M(Y)" "\<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> b = \<langle>x, G(x)\<rangle>)"
    using unv[of A F] unv[of A G] unfolding strong_replacement_def sorry
  then
  have "M(X\<times>Y)" by simp
  oops
    
end (* M_basic *)
  
end