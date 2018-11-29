theory Cofinality imports Normal Cardinal_AC begin

definition
  cofinal :: "[i,i,i] \<Rightarrow> o" where
  "cofinal(X,A,r) == \<forall>a\<in>A. \<exists>x\<in>X. <a,x>\<in>r"

definition
  f_cofinal :: "[i\<Rightarrow>i,i,i] \<Rightarrow> o" where
  "f_cofinal(f,A,r) == \<forall>a\<in>A. \<exists>x. <a,f(x)>\<in>r"
  
definition
  cofinal_fun :: "[i,i,i] \<Rightarrow> o" where
  "cofinal_fun(f,A,r) == \<forall>a\<in>A. \<exists>x\<in>domain(f). <a,f`x>\<in>r"

(*
The next definition doesn't work if 0 is the top element of A.
But it works for limit ordinals.
*)

definition
  cofinal_fun' :: "[i,i,i] \<Rightarrow> o" where
  "cofinal_fun'(f,A,r) == f_cofinal(\<lambda>x. f`x, A, r)"

lemma range_is_cofinal: 
  assumes "cofinal_fun(f,A,r)"
  shows "cofinal(range(f),A,r)"
proof -
  from assms have 
    "a\<in>A \<Longrightarrow> \<exists>x\<in>domain(f). \<langle>a, f ` x\<rangle> \<in> r" for a
    unfolding  cofinal_fun_def by simp
    {  
      fix b 
      assume  "b \<in> A"
      have  "\<exists>y\<in>range(f). \<langle>b, y\<rangle> \<in> r" sorry
    }
    then show ?thesis 
      unfolding cofinal_def by simp
  qed

lemma "Limit(A) \<Longrightarrow> cofinal_fun(f,A,Memrel(A)) \<longleftrightarrow> cofinal_fun'(f,A,Memrel(A))"
  oops
    
locale cofinality =
  fixes cf::"i\<Rightarrow>i"
  assumes 
    cota : "Ord(\<delta>) \<Longrightarrow> Limit(\<gamma>) \<Longrightarrow> function(f) \<Longrightarrow> domain(f) = \<delta> \<Longrightarrow>
            cofinal_fun(f,\<gamma>,Memrel(\<gamma>)) \<Longrightarrow> cf(\<gamma>)\<le>\<delta>"
    and idemp: "Limit(\<gamma>) \<Longrightarrow> A\<subseteq>\<gamma> \<Longrightarrow> cofinal(A,\<gamma>,Memrel(\<gamma>)) \<Longrightarrow> 
                cf(\<gamma>) = cf(ordertype(A,Memrel(\<gamma>)))"
begin

end
  
    
end