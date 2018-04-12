theory my_playground imports Formula ZFCaxioms L_axioms Cardinal begin

section\<open>Training in Isabelle proofs\<close>  
text\<open>The next lemma is just an experiment to have a proof of a proposition P==>P\<close>
lemma trivial_FO_implication:
  assumes "\<exists>x\<in>Z .  \<forall>y. P(x,y,Z) \<longrightarrow> Q(x,y,Z)"
  shows "\<exists>x\<in>Z .  \<forall>y. P(x,y,Z) \<longrightarrow> Q(x,y,Z)"
proof -
  show ?thesis using assms .
  text\<open>Otra opción es usar 
  show ?thesis using assms by simp\<close>
qed
  
(* A true result of FO logic *)    
lemma reinforce_antecedent:
  assumes p:"\<exists>x\<in>Z .  \<forall>y. P(x,y,Z) \<longrightarrow> Q(x,y,Z)"
  shows "\<exists>x\<in>Z .  \<forall>y. R(x,y) \<and> P(x,y,Z) \<longrightarrow> Q(x,y,Z)"
proof -
  show ?thesis using p by blast
qed

lemma reinforce_antecedent_no_vars:
  assumes p:"\<exists>x\<in>Z .  \<forall>y. (P \<longrightarrow> Q)"
  shows "\<exists>x\<in>Z .  \<forall>y. (R \<and> P \<longrightarrow> Q)"
proof -
  show ?thesis using p by blast
qed
  
section\<open>Experiments with type formula\<close>
definition 
  pedro :: "i" where
  "pedro == Exists(Exists(Neg(Equal(0,1))))"

definition 
  a :: "i" where
  "a == {0,1}"

lemma choto: "1 \<union> 2 = 2" 
  by auto

lemma arityp: "arity(pedro) = 0"
  apply (unfold pedro_def)
  apply (simp add: choto)
  done
    
lemma pedroempty: "sats(a,pedro,[])"
  apply(unfold a_def)
  apply(unfold pedro_def)
  apply(auto)
  done

lemma "env \<in> list(a) \<Longrightarrow> sats(a,pedro,env)"
  apply(unfold a_def)
  apply(unfold pedro_def)
  apply(auto)
  done

lemma "[] \<in> list(0)"
  apply (auto)
  done

subsection\<open>Absoluteness of transitivity\<close>
(* transitividad *)
definition 
  ZFtrans :: "i" where
  "ZFtrans == Forall(Forall(Implies(And(Member(0,1),
                            Member(1,2)),Member(0,2))))"

definition
  M1 :: "i" where
  "M1 == {0 , 2 , {2 , 0}}"

definition
  M2 :: "i" where
  "M2 == {0 , 1 , 2 , {2 , 0}}"


lemma l1 :
  "2 \<notin> 1"
  apply auto
  done

lemma l2 :
  "{2,0} \<noteq> 1"
  apply (unfold extension)
  apply (simp add: l1)
  done

lemma l1' :
  "2 \<notin> 2"
  apply auto
  done

lemma l2' :
  "{2,0} \<noteq> 2"
  apply (unfold extension)
  apply (simp add: l1')
  done


lemma absolute_fail : 
  "sats(M1,ZFtrans,[{2,0}])"
  apply (unfold ZFtrans_def)
  apply (unfold M1_def)
  apply (simp)
  apply (auto)
  apply (simp add: l2, simp add: l2')
  done

lemma absolute_hold : 
  "sats(M2,Neg(ZFtrans),[{2,0}])"
  apply (unfold ZFtrans_def)
  apply (unfold M2_def)
  apply (simp)
  done

section\<open>Well founded relations\<close>
definition
  eee :: "[i,i] \<Rightarrow> o" where
  "eee(x,y) == \<exists>z . z \<in> y \<and> (\<exists>w . w \<in> z \<and> x \<in> w)"
  
(* lemma eee_eclose : "eee(x,y) \<Longrightarrow> x\<in>eclose(y)"
  apply (simp add:eee_def)
  apply clarify
sorry

lemma eee_to_rank : "eee(x,y) \<Longrightarrow> rank(x)<rank(y)"
  by (simp add:eee_eclose add:eclose_rank_lt)
 
definition 
  minimal_in_class :: "[i,[i,i] \<Rightarrow> o, i\<Rightarrow>o] \<Rightarrow> o" where
  "minimal_in_class(y,R,M) == \<forall>z[M]. \<not>R(z,y)"
   
lemma eee_wf : "\<exists>x. M(x) \<Longrightarrow>  \<exists>y[M].minimal_in_class(y,eee,M)"
  apply clarify
  apply (case_tac "minimal_in_class(x,eee,M)")
proof -
  assume "M(x)"
oops

definition
  relSet :: "i \<Rightarrow> i" where
  "relSet(M) == { z \<in> M*M . eee(fst(z),snd(z)) }"
 
lemma relSet_coord : "<x,y>\<in>relSet(M) \<Longrightarrow> \<exists>z . z \<in> y \<and> (\<exists>w . w \<in> z \<and> x \<in> w)"
by (simp add:relSet_def eee_def )

lemma fld_rel_sub_eclose : "\<lbrakk>xa \<in> M; y \<in> M ; z \<in> y ; w \<in> z; xa \<in> w\<rbrakk> \<Longrightarrow> 
                            z \<in> eclose(M) \<and> w \<in> eclose(M)"
  apply (simp add:ecloseD)
proof - 
  assume p:"y\<in>M"
  assume q: "z\<in>y"
  show "z\<in>eclose(M)"
  proof - 
  have r:"M\<subseteq>eclose(M)" by (rule arg_subset_eclose)
  from p and r  have "y\<in>eclose(M)" by (simp add:subsetD)
  then show ?thesis using q  by (simp add:ecloseD)
  qed
qed
  
lemma dom_memrel : "domain(Memrel(A))\<subseteq>A"
  by clarify

lemma ran_memrel : "range(Memrel(A))\<subseteq>A"
  by clarify

lemma dom_mem_eclo :"domain(Memrel(eclose(M)))=eclose(M)"
(*proof
  show "domain(Memrel(eclose(M)))\<subseteq>eclose(M)" by (rule_tac A="eclose(M)" in dom_memrel)
  (* rule_tac se puede eliminar en favor de             *
   *   (simp add:dom_memrel)                            *)
*)
  apply standard             
  apply (rule_tac A="eclose(M)" in dom_memrel)
  apply (unfold eclose_def)
  apply (unfold domain_def)
  apply clarify
  (* apply (rule_tac nat_induct) *)
oops

lemma rel_sub_memcomp : "relSet(M) \<subseteq> Memrel(eclose(M)) O Memrel(eclose(M)) O Memrel(eclose(M))"
  apply (unfold relSet_def)
  apply (unfold rel_def)
  apply (simp add:comp_def)
  apply clarify
  apply (simp add:snd_def)
  (* relevant fact? comp_def *)
sorry
  
lemma memcomp_sub_trmem : "Memrel(eclose(M)) O Memrel(eclose(M))O Memrel(eclose(M))
                          \<subseteq> trancl(Memrel(eclose(M)))"
  apply clarify
  apply simp
  apply (unfold trancl_def)
(* proof -
  assume p:"xb\<in>ya" and q:"xb\<in>eclose(M)" and r:"ya\<in>eclose(M)"
  from p and q and r    
  have s:"<xb,ya>\<in>Memrel(eclose(M))".. *)
sorry
  
lemma wf_trmem : "wf(trancl(Memrel(eclose(M))))"
(*  apply (simp add:wf_trancl) no anda aquí *)
  apply (rule wf_trancl)
  apply (simp add:wf_Memrel)
done

lemma wf_memcomp : "wf(Memrel(eclose(M)) O Memrel(eclose(M)) O Memrel(eclose(M)))"
  apply (rule wf_subset)
  apply (rule wf_trmem)
  apply (rule memcomp_sub_trmem)
done

lemma wf_relSet : "wf(relSet(M))"
  apply (rule wf_subset)
  apply (rule wf_memcomp)
  apply (rule rel_sub_memcomp)
done

  
(*
lemma WFrel : "wf(relSet(M))"
  apply(unfold wf_def)
  apply(rule allI)
  apply(case_tac "Z=0")
  apply(rule disjI1;auto)
  apply(rule disjI2)
  apply(simp add:relSet_def add:rel_def add:WFrel_auxM)
  done
*)
*)
section\<open>Posets\<close>  
text\<open>Reflexivity in three forms\<close>

definition 
  reflexivity_abs :: "[i,i] \<Rightarrow> o" where
  "reflexivity_abs(P,r) == \<forall>p . p\<in>P \<longrightarrow> <p,p>\<in>r"

definition  
  reflexivity_rel :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "reflexivity_rel(M,P,r) == \<forall>p[M].  p\<in>P \<longrightarrow> (\<exists>x[M]. pair(M,p,p,x) \<and> x\<in>r)"

definition
  reflexivity_fm :: "[i,i]\<Rightarrow>i" where
  "reflexivity_fm(x,y) == Forall(Implies(Member(0,succ(x)),
                     Exists(And(pair_fm(1,1,0),Member(0,succ(succ(y)))))))"

lemma reflexivity_type : "\<lbrakk>x\<in>nat ; y\<in>nat\<rbrakk> \<Longrightarrow> reflexivity_fm(x,y)\<in>formula"
  by (simp add:reflexivity_fm_def)

  
section\<open>Anomalous calculations\<close>
text\<open>Here I put some anomalous lemmata, showing the typelessness of set theory.\<close>

lemma emptylist_is_pair :
  "Nil = {{0}}"
  apply (unfold Nil_def)
  apply (unfold Inl_def)
  apply (unfold Pair_def)
  apply (auto)
  done

lemma formula_is_set :
  "Member(0,0) \<noteq> 0"
  apply (unfold Member_def)
  apply (unfold Inl_def)
  apply (auto)
  done    

(*
lemma card_of_pair :
  "cardinal(Pair(x,y)) = 2"
  sorry
    
lemma card_of_formula :
  "cardinal(Member(1,2)) = 2"
  apply (unfold Member_def)
  apply (unfold Inl_def)
  apply (simp add:card_of_pair)
  done
*)
end

