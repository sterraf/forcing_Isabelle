theory WF_e3 imports Formula L_axioms Cardinal begin

section\<open>Relative composition of \<in>.\<close>
text\<open>Names are defined by using well-founded recursion on the relation \<in>³ given
by ``x\<in>³y if \<exists>z . z \<in> y \<and> (\<exists>w . w \<in> z \<and> x \<in> w)''\<close>
definition
  e3 :: "[i,i] \<Rightarrow> o" where
  "e3(x,y) == \<exists>z . z \<in> y \<and> (\<exists>w . w \<in> z \<and> x \<in> w)"

definition
  e3_set :: "i \<Rightarrow> i" where
  "e3_set(M) == { z \<in> M*M . e3(fst(z),snd(z)) }"

(* z \<in> M*M . e3(fst(z),snd(z)) *)

(* \<questiondown>Es útil? *)
lemma e3_set_coord : 
  "<x,y>\<in>e3_set(M) \<Longrightarrow> \<exists>z . z \<in> y \<and> (\<exists>w . w \<in> z \<and> x \<in> w)"
by (simp add:e3_set_def e3_def )

(*\<questiondown>Qué significa fld?*)
lemma fld_e3_sub_eclose : 
 "\<lbrakk>y \<in> M ; z \<in> y ; w \<in> z\<rbrakk> \<Longrightarrow> 
                           z \<in> eclose(M) \<and> w \<in> eclose(M)"
proof (simp add:ecloseD) 
  assume p:"y\<in>M"
     and q: "z\<in>y"
  show "z\<in>eclose(M)"
  proof - 
  have r:"M\<subseteq>eclose(M)" by (rule arg_subset_eclose)
  from p and r  have "y\<in>eclose(M)" by (simp add:subsetD)
  then show ?thesis using q  by (simp add:ecloseD)
  qed
qed

lemma fld_memrel:"\<lbrakk> y \<in> M ; z \<in> y ; w \<in> z\<rbrakk> \<Longrightarrow> 
                           <w,z> \<in> Memrel(eclose(M))"
  by  (rule MemrelI,assumption,simp add:fld_e3_sub_eclose,simp add:fld_e3_sub_eclose)

(* Una cosa para mejorar de esta prueba es que no debería ser
  necesario nombrar las hipótesis; no funciona si no las nombro 
  o no explicito cuáles se usan en cada have.
*)
lemma rel_sub_memcomp : 
  "e3_set(M) \<subseteq> Memrel(eclose(M)) O Memrel(eclose(M)) O Memrel(eclose(M))"
proof (unfold e3_set_def, unfold e3_def,clarsimp)
  fix x y z w
  assume a:"x \<in> M"
   and b:"y \<in> M"
   and c:"z \<in> y"
   and d:"w \<in> z"
   and e:"x \<in> w"
  from a b c d e have p : "<x,w> \<in> Memrel(eclose(M))" 
    by (simp add:fld_memrel fld_e3_sub_eclose arg_into_eclose)
   from b c d have q : "<w,z> \<in> Memrel(eclose(M))"
    by (simp add:MemrelI fld_e3_sub_eclose)
  from b c d have r : "<z,y> \<in> Memrel(eclose(M))"
    by (simp add:MemrelI fld_e3_sub_eclose arg_into_eclose)
  from p q r 
    show "<x,y> \<in> Memrel(eclose(M)) O Memrel(eclose(M)) O Memrel(eclose(M))"
     by (rule_tac b=z in compI, rule_tac b=w in compI)
qed

  
lemma memcomp_sub_trmem : 
  "Memrel(eclose(M)) O Memrel(eclose(M)) O Memrel(eclose(M))
         \<subseteq> trancl(Memrel(eclose(M)))"
proof (auto,unfold trancl_def)
  let ?M'="Memrel(eclose(M))"
  fix y x w z
  assume m: "y \<in> eclose(M)"
    and n: "z \<in> y"
    and a: "x \<in> eclose(M)"
    and b: "x \<in> w"
    and c: "w \<in> eclose(M)"
    and o: "z \<in> eclose(M)"
    and d: "w \<in> z"
  from a b c have p:"<x,w> \<in> ?M'" by (simp add:MemrelI)
  from m n o have q: "<z,y> \<in> ?M'" by (simp add:MemrelI)
  from c d o have r:"<w,z> \<in> ?M'" by (simp add:MemrelI)
  from p have s: "<x,w> \<in> ?M'^*" by (rule r_into_rtrancl)
  from s r have t:"\<langle>x, z\<rangle> \<in> ?M'^*"  by
    (rule_tac b=w in rtrancl_into_rtrancl)
  from q t show "\<langle>x, y\<rangle> \<in> ?M' O ?M'^*" by (rule_tac b=z in compI)
qed
  
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

lemma wf_e3_set : "wf(e3_set(M))"
  apply (rule wf_subset)
  apply (rule wf_memcomp)
  apply (rule rel_sub_memcomp)
done


definition 
  Hcheck :: "[i,i,i] \<Rightarrow> i" where
  "Hcheck(uno,z,f)  == { <f`y,uno> . y \<in> z}"

definition
  checkR :: "[i,i,i] \<Rightarrow> i" where
  "checkR(M,uno,x) == wfrec(trancl(Memrel(eclose(M))), x , Hcheck(uno))"

(* Ejercicios preliminares para check *)

lemma check0 : "checkR(M,1,0) =  0"
  apply (unfold checkR_def)
  apply (unfold Hcheck_def)
  apply (unfold wfrec_def)
  apply (unfold wftrec_def)
  apply (auto)
  done

lemma vimage_sing : "a\<in>M \<Longrightarrow> Memrel(eclose(M))^+ -`` {a} = 
                             domain(Memrel(eclose(M))^+) \<inter> a"
  sorry

lemma aux_check0' : "{a}\<in>M \<Longrightarrow> {a}\<in>eclose(M)"
  apply (rule_tac A="M" in subsetD)
   apply (rule arg_subset_eclose)
  apply simp
  done

lemma aux_check0'' : "\<lbrakk> a\<in>A ; b\<in>a \<rbrakk> \<Longrightarrow> b\<in>domain(Memrel(eclose(A)))"
  apply (unfold domain_def)
  sorry

lemma aux_check0''' : "r \<subseteq> r' \<Longrightarrow> domain(r) \<subseteq> domain(r')"
  apply (rule subsetI)
  apply (unfold domain_def)
  
  sorry

lemma aux_check0 : "{a} \<in> M \<Longrightarrow> a \<in> domain(Memrel(eclose(M))^+)"
  apply (rule_tac A="domain(Memrel(eclose(M)))" in subsetD)
   apply (rule aux_check0''')
   apply (rule r_subset_trancl)
   apply (rule relation_Memrel)
  apply (rule_tac a="{a}" in aux_check0'')
   apply auto
  done
  
lemma aux_check1 : 
  "{0}\<in>M \<Longrightarrow> Memrel(eclose(M))^+ -`` {{0}} = {0}"
  apply (subst vimage_sing) 
  apply (simp)
  apply (rule equalityI)
   apply (auto)
  apply (rule aux_check0)
  apply (simp)
  done

lemma check1 : "{0}\<in>M \<Longrightarrow> checkR(M,1,{0}) =  {<0,1>}"
  apply (rule trans)
  apply (rule_tac h="checkR(M,1)" and r="trancl(Memrel(eclose(M)))" in
  def_wfrec)
    apply (simp add: checkR_def)
   apply (rule wf_trancl)
   apply (rule wf_Memrel)
  apply (subst aux_check1)
   apply (simp)
  apply (unfold Hcheck_def)
  apply (simp)
  apply (rule check0)
  done


(* Val *)
definition
  Hval :: "[i,i,i,i] \<Rightarrow> i" where
  "Hval(P,G,x,f) == { f`y .y\<in>{w \<in> domain(x).(\<exists>p\<in>P. <w,p> \<in> x \<and> p \<in> G) }}"

definition
  valR :: "[i,i,i,i] \<Rightarrow> i" where
  "valR(M,P,G,\<tau>) == wfrec(trancl(Memrel(eclose(M))), \<tau> ,Hval(P,G))"

(* Ejercicios preliminares para val *)
lemma val0: "valR(M,P,G,0) = 0"
  apply (unfold valR_def)
  apply (unfold Hval_def)
  apply (unfold wfrec_def)
  apply (unfold wftrec_def)
  apply simp
  done

lemma "uno \<in> P \<Longrightarrow> uno \<in> G \<Longrightarrow> valR(M,P,G,checkR(M,uno,x)) = x"
  apply (rule_tac r="trancl(Memrel(M))" in wf_induct)
   apply (rule wf_trancl)
   apply (rule wf_Memrel)
  apply (rule trans)
   apply (rule_tac h="valR(M,P,G)" and r="trancl(Memrel(eclose(M)))" in def_wfrec)
   apply (simp add: valR_def)
   apply (rule wf_trancl)
   apply (rule wf_Memrel)
  apply (unfold Hval_def) 
  
  

end

