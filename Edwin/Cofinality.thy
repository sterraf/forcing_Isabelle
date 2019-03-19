theory Cofinality 
  imports 
    Cardinal_AC
    "~~/src/ZF/Constructible/Normal"
begin

definition
  cofinal :: "[i,i,i] \<Rightarrow> o" where
  "cofinal(X,A,r) == \<forall>a\<in>A. \<exists>x\<in>X. <a,x>\<in>r"

definition
  cofinal_predic :: "[i,i,[i,i]\<Rightarrow>o] \<Rightarrow> o" where
  "cofinal_predic(X,A,r) == \<forall>a\<in>A. \<exists>x\<in>X. r(a,x)"

definition
  f_cofinal :: "[i\<Rightarrow>i,i,i,i] \<Rightarrow> o" where
  "f_cofinal(f,C,A,r) == \<forall>a\<in>A. \<exists>x\<in>C. <a,f(x)>\<in>r" (* "predic" version ? *)
  
definition
  cofinal_fun :: "[i,i,i] \<Rightarrow> o" where
  "cofinal_fun(f,A,r) == \<forall>a\<in>A. \<exists>x\<in>domain(f). <a,f`x>\<in>r"

(*
The next definition doesn't work if 0 is the top element of A.
But it works for limit ordinals.
*)

definition
  cofinal_fun' :: "[i,i,i] \<Rightarrow> o" where
  "cofinal_fun'(f,A,r) == f_cofinal(\<lambda>x. f`x,domain(f),A, r)"

lemma range_is_cofinal: 
  assumes "cofinal_fun(f,A,r)" "f:C \<rightarrow> D"
  shows "cofinal(D,A,r)"
  unfolding cofinal_def
proof 
  fix b 
  assume "b \<in> A"
  moreover from assms
  have "a\<in>A \<Longrightarrow> \<exists>x\<in>domain(f). \<langle>a, f ` x\<rangle> \<in> r" for a
    unfolding cofinal_fun_def by simp
  ultimately
  obtain x where "x\<in>domain(f)" "\<langle>b, f ` x\<rangle> \<in> r" 
    by blast
  from \<open>f:C \<rightarrow> D\<close>
  have "domain(f) \<subseteq> C" (* is it needed? *)
    (* using  *) sorry find_theorems "?f:Pi(?A,?B)"
  then
  show  "\<exists>y\<in>D. \<langle>b, y\<rangle> \<in> r" sorry
qed

lemma "Limit(A) \<Longrightarrow> cofinal_fun(f,A,Memrel(A)) \<longleftrightarrow> cofinal_fun'(f,A,Memrel(A))"
  oops
    
locale cofinality =
  fixes cf::"i\<Rightarrow>i"
  assumes 
    (* Better with f_cofinal(f,\<delta>,\<gamma>,Memrel(\<gamma>)) ? *)
    cota : "Ord(\<delta>) \<Longrightarrow> Limit(\<gamma>) \<Longrightarrow> function(f) \<Longrightarrow> domain(f) = \<delta> \<Longrightarrow>
            cofinal_fun(f,\<gamma>,Memrel(\<gamma>)) \<Longrightarrow> cf(\<gamma>)\<le>\<delta>"
    and idemp: "Limit(\<gamma>) \<Longrightarrow> A\<subseteq>\<gamma> \<Longrightarrow> cofinal(A,\<gamma>,Memrel(\<gamma>)) \<Longrightarrow> 
                cf(\<gamma>) = cf(ordertype(A,Memrel(\<gamma>)))"
    (* Is it better?? 
    and idemp': "Limit(\<gamma>) \<Longrightarrow> A\<subseteq>\<gamma> \<Longrightarrow> cofinal_predic(A,\<gamma>,mem) \<Longrightarrow> 
                cf(\<gamma>) = cf(ordertype(A,Memrel(\<gamma>)))" *)
begin
(* probar 5.12 y 5.13(1,2) *)
  
lemma cofinal_is_regular:
  assumes "Limit(\<gamma>)"
  shows "cf(\<gamma>) = cf(cf(\<gamma>))"  
proof
  fix A
  assume "A\<subseteq>\<gamma>" "cofinal(A,\<gamma>,Memrel(\<gamma>))" "cf(\<gamma>) = ordertype(A,Memrel(\<gamma>)) "
  with assms
  have " cf(\<gamma>) =cf(ordertype(A,Memrel(\<gamma>)))" using idemp by simp
  also have
 "... =cf(cf(\<gamma>))" using\<open>cf(\<gamma>) =ordertype(A,Memrel(\<gamma>))\<close> by simp
  with \<open>cf(\<gamma>) =cf(ordertype(A,Memrel(\<gamma>)))\<close>
  have "cf(\<gamma>) = cf(cf(\<gamma>))"  by simp
      
      then have "cf(\<gamma>) \<subseteq> cf(cf(\<gamma>))"  using equalityD1  by auto
  
      
  find_theorems "?A=?B \<Longrightarrow>?A\<subseteq>?B"
    
  
end  
end (* cofinality *)
  
    
end