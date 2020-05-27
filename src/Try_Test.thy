theory Try_Test
  imports
    "ZF-Constructible.L_axioms"
    "../Tools/Try0"
begin

(* 
  The last "force" method takes 51ms to finish, but if we flip the 
  order of the imports, it takes 3681 ms (around 4\<onehalf>s real).

  In a real test case from which this PoC was extracted, a use of 
  force that takes 43ms, won't finish after 3'30s (real) after 
  flipping.
*)

lemma univalent_is_domain:
  assumes
    ex_tr: "\<And>P d d'. M(d) \<Longrightarrow> M(d') \<Longrightarrow> \<forall>x[M]. x \<in> d \<longleftrightarrow> P(x) \<Longrightarrow> \<forall>x[M]. x \<in> d' \<longleftrightarrow> P(x) \<Longrightarrow> d = d'"
    and
    "M(r)" "M(d)" "M(d')"
    "is_domain(M,r,d)" "is_domain(M,r,d')"
  shows
    "d=d'"
  using assms 
    ex_tr[where P="\<lambda>x. \<exists>w[M]. w \<in> r \<and> (\<exists>y[M]. pair(M, x, y, w))"]
  unfolding is_domain_def
  by force

end