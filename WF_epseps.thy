theory WF_epseps imports Formula L_axioms Cardinal begin

section\<open>Well founded relations\<close>
text\<open>To Do: find a better name for rel.\<close>
definition
  rel :: "[i,i] \<Rightarrow> o" where
  "rel(x,y) == \<exists>z . z \<in> y \<and> (\<exists>w . w \<in> z \<and> x \<in> w)"

definition
  relSet :: "i \<Rightarrow> i" where
  "relSet(M) == { z \<in> M*M . rel(fst(z),snd(z)) }"

lemma relSet_coord : 
  "<x,y>\<in>relSet(M) \<Longrightarrow> \<exists>z . z \<in> y \<and> (\<exists>w . w \<in> z \<and> x \<in> w)"
by (simp add:relSet_def rel_def )

lemma fld_rel_sub_eclose : 
 "\<lbrakk>xa \<in> M; y \<in> M ; z \<in> y ; w \<in> z; xa \<in> w\<rbrakk> \<Longrightarrow> 
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

lemma rel_sub_memcomp : 
  "relSet(M) \<subseteq> Memrel(eclose(M)) O Memrel(eclose(M)) O Memrel(eclose(M))"
text\<open>To Do: esta prueba está feísima! Una forma de mejorarla 
es utilizar a structured Isar proof (el otro estilo). \<close>
  apply (unfold relSet_def, unfold rel_def)
  apply clarsimp
  apply (rule_tac b=z in compI)
  apply (rule_tac b=w in compI)
  apply (rule MemrelI, assumption)
   apply (rule arg_into_eclose,assumption)
  apply (simp add:fld_rel_sub_eclose)
  apply (rule MemrelI, assumption)   
  apply (simp add:fld_rel_sub_eclose)
  apply (simp add:fld_rel_sub_eclose)
  apply (rule MemrelI, assumption) 
  apply (simp add:fld_rel_sub_eclose)
  apply (rule arg_into_eclose, assumption)
done
    
lemma memcomp_sub_trmem : "Memrel(eclose(M)) O Memrel(eclose(M))O Memrel(eclose(M))
                          \<subseteq> trancl(Memrel(eclose(M)))"
  apply auto
  apply (unfold trancl_def)
  apply (rule_tac b=za in compI )
  apply (rule_tac b=ya in rtrancl_into_rtrancl)
  apply (rule r_into_rtrancl)
  apply (rule MemrelI)
  apply auto
done
    
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
end

