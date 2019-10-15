theory Forcing_Corollaries imports Interface Names begin
   
(* A thinner locale *)
locale forcing_thms = forcing_data +
  fixes forces :: "i \<Rightarrow> i"
  assumes definition_of_forces: "p\<in>P \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> env\<in>list(M) \<Longrightarrow>
                  sats(M,forces(\<phi>), [P,leq,one,p] @ env) \<longleftrightarrow>
                  (\<forall>G.(M_generic(G)\<and> p\<in>G)\<longrightarrow>sats(M[G],\<phi>,map(val(G),env)))"
      and  definability[TC]: "\<phi>\<in>formula \<Longrightarrow> forces(\<phi>) \<in> formula"
      and  arity_forces:     "\<phi>\<in>formula \<Longrightarrow> arity(forces(\<phi>)) = arity(\<phi>) #+ 4"
      and   truth_lemma:     "\<phi>\<in>formula \<Longrightarrow> env\<in>list(M) \<Longrightarrow> M_generic(G) \<Longrightarrow>
                  (\<exists>p\<in>G.(sats(M,forces(\<phi>), [P,leq,one,p] @ env))) \<longleftrightarrow>
                  sats(M[G],\<phi>,map(val(G),env))"

context forcing_thms begin

lemma generic_inter_dense_below:
  assumes
    "M_generic(G)" "p\<in>G" "dense_below(D,p)" 
  shows
    "\<exists>q. q \<in> G \<and> q \<in> D"
  sorry   
        
lemma strengthening_lemma : 
  assumes
    "p\<in>P" "\<phi>\<in>formula" "env\<in>list(M)" "q\<in>P" "<q,p>\<in>leq"
    "sats(M,forces(\<phi>), [P,leq,one,p] @ env)"
  shows
    "sats(M,forces(\<phi>), [P,leq,one,q] @ env)"
proof -
  from assms have
    1: "(\<forall>G.(M_generic(G)\<and> p\<in>G)\<longrightarrow>sats(M[G],\<phi>,map(val(G),env)))"
    using definition_of_forces by simp
  {
    fix G
    assume 
      "M_generic(G)" "q\<in>G"
    moreover from calculation assms have
      "p\<in>G"
      unfolding M_generic_def using filter_leqD by simp
    moreover note 1
    ultimately have
      "sats(M[G],\<phi>,map(val(G),env))"
      by simp
  }
  then have
    "(\<forall>G.(M_generic(G)\<and> q\<in>G)\<longrightarrow>sats(M[G],\<phi>,map(val(G),env)))"
    by simp
  with assms show ?thesis using definition_of_forces by simp
qed
    
(* To Do: change next lemma's name when the locale is modified*)   
lemma density_lem :
  assumes
    "p\<in>P" "\<phi>\<in>formula" "env\<in>list(M)" 
  shows
    "sats(M,forces(\<phi>), [P,leq,one,p] @ env) \<longleftrightarrow> 
     dense_below({q\<in>P. sats(M,forces(\<phi>), [P,leq,one,q] @ env)},p)"
proof 
  assume
    1: "dense_below({q\<in>P. sats(M,forces(\<phi>), [P,leq,one,q] @ env)},p)"
  {
    fix G
    assume 
      "M_generic(G)" "p\<in>G"
    with 1 obtain q where
      "q\<in>G" "sats(M,forces(\<phi>), [P,leq,one,q] @ env)" "q\<in>P"
      using generic_inter_dense_below by blast
    with assms \<open>M_generic(G)\<close> have
      "sats(M[G],\<phi>,map(val(G),env))" 
      using truth_lemma by auto
  }
  with assms show
    "sats(M,forces(\<phi>), [P,leq,one,p] @ env)"
    using definition_of_forces by simp
next
  assume
    2: "sats(M,forces(\<phi>), [P,leq,one,p] @ env)"
  {
    fix r
    assume 
      "r\<in>P" "<r,p> \<in> leq"
    moreover from calculation 2 assms have
      "sats(M,forces(\<phi>), [P,leq,one,r] @ env)"
      using strengthening_lemma by simp
    ultimately have
      "r\<in>{q \<in> P . sats(M, forces(\<phi>), [P, leq, one, q] @ env)}" "\<langle>r, r\<rangle> \<in> leq"
      using refl_leq by simp_all
  }
  then show
    "dense_below({q\<in>P. sats(M,forces(\<phi>), [P,leq,one,q] @ env)},p)"
    unfolding dense_below_def by auto
qed 
end (* forcing_thms *)
  
(* An alternative locale *)
locale forcing_thms_alt = forcing_data +
  fixes forces :: "i \<Rightarrow> i"
  assumes  definability[TC]: "\<phi>\<in>formula \<Longrightarrow> forces(\<phi>) \<in> formula"
      and  arity_forces:     "\<phi>\<in>formula \<Longrightarrow> arity(forces(\<phi>)) = arity(\<phi>) #+ 4"
      and   truth_lemma:     "\<phi>\<in>formula \<Longrightarrow> env\<in>list(M) \<Longrightarrow> M_generic(G) \<Longrightarrow>
                  (\<exists>p\<in>G.(sats(M,forces(\<phi>), [P,leq,one,p] @ env))) \<longleftrightarrow>
                  sats(M[G],\<phi>,map(val(G),env))"
      and  strengthening:     "p\<in>P \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> env\<in>list(M) \<Longrightarrow> q\<in>P \<Longrightarrow> <q,p>\<in>leq \<Longrightarrow>
                               sats(M,forces(\<phi>), [P,leq,one,p] @ env) \<Longrightarrow>
                               sats(M,forces(\<phi>), [P,leq,one,q] @ env)"
      and density_lemma:     "p\<in>P \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> env\<in>list(M) \<Longrightarrow>
                    sats(M,forces(\<phi>), [P,leq,one,p] @ env) \<longleftrightarrow> 
                    dense_below({q\<in>P. sats(M,forces(\<phi>), [P,leq,one,q] @ env)},p)"
begin
lemma def_of_forces:
  assumes
    "p\<in>P" "\<phi>\<in>formula" "env\<in>list(M)" 
  shows
    "sats(M,forces(\<phi>), [P,leq,one,p] @ env) \<longleftrightarrow>
     (\<forall>G.(M_generic(G)\<and> p\<in>G)\<longrightarrow>sats(M[G],\<phi>,map(val(G),env)))"
proof (intro iffI allI impI, elim conjE)
  fix G
  assume
    "sats(M, forces(\<phi>), [P,leq,one,p] @ env)" "M_generic(G)" "p \<in> G"
  with assms show
    "sats(M[G],\<phi>,map(val(G),env))"
    using truth_lemma by auto
next
  assume
    1: "\<forall>G.(M_generic(G)\<and> p\<in>G)\<longrightarrow>sats(M[G],\<phi>,map(val(G),env))"
  {
    fix r 
    assume 
      2: "r\<in>P" "<r,p>\<in>leq"
    then obtain G where
      "r\<in>G" "M_generic(G)"
      using generic_filter_existence by auto
    moreover from calculation 2 \<open>p\<in>P\<close> have
      "p\<in>G" 
      unfolding M_generic_def using filter_leqD by simp
    moreover note 1
    ultimately have
      "sats(M[G],\<phi>,map(val(G),env))"
      by simp
    with assms \<open>M_generic(G)\<close> obtain s where
      3:"s\<in>G" "sats(M,forces(\<phi>), [P,leq,one,s] @ env)"
      using truth_lemma by blast
    with \<open>M_generic(G)\<close> \<open>r\<in>G\<close> obtain q where
      "q\<in>G" "<q,s>\<in>leq" "<q,r>\<in>leq"
      unfolding M_generic_def using low_bound_filter by blast
    moreover from calculation \<open>s\<in>G\<close> \<open>M_generic(G)\<close> have
      "s\<in>P" "q\<in>P" 
      unfolding M_generic_def filter_def by auto
    moreover note assms 3 
    ultimately have
      "\<exists>q\<in>P. <q,r>\<in>leq \<and> sats(M,forces(\<phi>), [P,leq,one,q] @ env)"
      using strengthening by blast
  }
  then have
    "dense_below({q\<in>P. sats(M,forces(\<phi>), [P,leq,one,q] @ env)},p)"
    unfolding dense_below_def by blast
  with assms show
    "sats(M,forces(\<phi>), [P,leq,one,p] @ env)"
    using density_lemma by blast
qed
end (* forcing_thms_alt *)
  
end