theory val_check imports Formula L_axioms Cardinal begin

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

text\<open>Some properties about the transitive closure of Memrel.\<close>
lemma "M\<noteq>0 \<Longrightarrow> 0 \<in> (eclose(M)) "
  apply (rule_tac j="rank(eclose(M))" in ltE)
   apply (rule Ord_0_lt,auto)
   apply (ssubsts rank_eclose)
  find_theorems "rank(eclose(?x))" 
    
lemma "M\<noteq>0 \<Longrightarrow> 0 \<in> domain(Memrel(eclose(M))^+)"
  apply (rule domainI,rule r_into_trancl)
  find_theorems "?x \<in> eclose(?a)"
 apply (rule_tac b="{0}" in MemrelI,simp)
 apply (rule_tac B="{0}" in mem_eclose_trans)
 apply (rule arg_in_eclose_sing,(rule arg_into_eclose, assumption)+)
  
definition ed :: "[i,i] \<Rightarrow> o" where
  "ed(x,y) == x \<in> domain(y)"  
  
  
definition 
  Hcheck :: "[i,i,i] \<Rightarrow> i" where
  "Hcheck(uno,z,f)  == { <f`y,uno> . y \<in> z}"

definition
  checkR :: "[i,i,i] \<Rightarrow> i" where
  "checkR(M,uno,x) == wfrec(trancl(Memrel(eclose(M))), x , Hcheck(uno))"

(*
 (\<Union>x\<in>w. Lambda(Memrel(eclose(M))^+ -`` {checkR(M, uno, w)}, valR(M, P, G)) `
                 checkR(M, uno, x)) =

checkR(M, uno, w) = {<checkR(M,uno,y),uno> . y \<in> w}

checkR(M,uno,x) = {<checkR(M,uno,z),uno> . z \<in> x}
*)

(* Ejercicios preliminares para check *)

lemma check0 : "checkR(M,1,0) =  0"
  apply (unfold checkR_def)
  apply (unfold Hcheck_def)
  apply (unfold wfrec_def)
  apply (unfold wftrec_def)
  apply (auto)
  done

lemma vimage_sing_char : "r -`` {a} = {x \<in> domain(r) . <x,a> \<in> r }"
  by blast
    
    
lemma vimage_sing : "a\<in>M \<Longrightarrow> Memrel(eclose(M))^+ -`` {a} = 
           {x \<in> domain(Memrel(eclose(M))^+) . <x,a> \<in> Memrel(eclose(M))^+}"
  by (rule vimage_sing_char)

  
lemma in_dom : " relation(r) \<Longrightarrow> <a,b> \<in> r \<Longrightarrow> a\<in>domain(r)"
  by blast
    
lemma aux_check0'' : "\<lbrakk> a\<in>A ; b\<in>a \<rbrakk> \<Longrightarrow> b\<in>domain(Memrel(eclose(A)))"
  apply (rule in_dom) 
  apply (rule relation_Memrel)
  apply (auto)
  apply (rule_tac A="a" in ecloseD)
  apply (rule arg_into_eclose,assumption+)+
done 
  

lemma dom_monotone : "r \<subseteq> r' \<Longrightarrow> domain(r) \<subseteq> domain(r')"
  by blast
    
  
lemma aux_check0 : "{a} \<in> M \<Longrightarrow> a \<in> domain(Memrel(eclose(M))^+)"
  apply (rule_tac A="domain(Memrel(eclose(M)))" in subsetD)
   apply (rule dom_monotone)
   apply (rule r_subset_trancl)
   apply (rule relation_Memrel)
  apply (rule_tac a="{a}" in aux_check0'')
   apply auto
  done

lemma empty_not_in_memrel : "<x,0> \<notin> (Memrel(eclose(M)))^+"
  apply clarsimp
  apply (frule_tac P="False" in tranclE)
  apply blast
   apply clarsimp
  apply blast  
done
  
(* TODO: find a nicer way to use a false hypothesis. *)
lemma img_sing_memrel : "<x,{0}> \<in> (Memrel(eclose(M)))^+ \<Longrightarrow> x = 0"
  apply(rule_tac r="Memrel(eclose(M))" in tranclE)
  apply assumption
  apply blast
  apply clarsimp
  apply (rule_tac P="<x,0> \<in> Memrel(eclose(M))^+" in notE)
  apply (rule empty_not_in_memrel)
  apply assumption
done
    
lemma aux_check1 : 
  "{0}\<in>M \<Longrightarrow> Memrel(eclose(M))^+ -`` {{0}} = {0}"
  apply(subst vimage_sing, assumption)
  apply (rule equalityI)
  apply (clarsimp)
  apply (rule img_sing_memrel)
  apply blast
  apply clarsimp
  apply (rule conjI) 
 (*TODO: state {0}\<in>M \<Longrightarrow> <0,{0}>\<in>Memrel(eclose(M))^+, the proof follows.
  More interesting: do we need {0}\<in>M? *)
 apply (rule domainI,rule r_into_trancl)
 apply (rule_tac b="{0}" in MemrelI,simp)
 apply (rule_tac B="{0}" in mem_eclose_trans)
 apply (rule arg_in_eclose_sing,(rule arg_into_eclose, assumption)+)
 apply(rule r_into_trancl)
 apply (rule_tac b="{0}" in MemrelI,simp)
 apply (rule_tac B="{0}" in mem_eclose_trans)
 apply (rule arg_in_eclose_sing,(rule arg_into_eclose, assumption)+)
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

text\<open>The idea of the following theorem is as follows. We 
assume y\<in>M, uno \<in>P\<inter>G

val(check(y)) 
={ definition of val }
{val(x) . \<exists> p <x,p> \<in> check(y) \<and> p \<in> G}
={ characterization of dom . check }
{val(x) . x\<in>dom(check(y)) }
={ definition of check }
{val(x) . x \<in> {check(w) . w \<in> y}}
={ lemma? }
\<union>_{w \<in> y} {val(check(w)}
={ hi }
\<union>_{w \<in> y} {w}
= { UN_singleton }
y
\<close>

lemma domain_check : "y \<in> M \<Longrightarrow> uno \<in> P \<Longrightarrow> uno \<in> G \<Longrightarrow> 
   {x \<in> domain(checkR(M, uno, y)) .  \<exists>p\<in>P. \<langle>x, p\<rangle> \<in> checkR(M, uno, y) \<and> p \<in> G}
    = domain(checkR(M,uno,y))" 
  sorry

lemma sub_e : "y \<subseteq> Memrel(eclose(M))^+ -`` {y}"
  sorry

lemma lam_dom : "A\<subseteq>B \<Longrightarrow> {Lambda(B,f)`y . y\<in>A } = {f(y) . y\<in>A}"
  sorry

(*esto no es cierto: *)
lemma lam_cons : "A\<subseteq>B \<Longrightarrow> {<Lambda(B,f)`y,a> . y\<in>A} = 
                  {Lambda(B,\<lambda>x.<f(x),a>)`y . y\<in>A}"
  sorry

lemma check_simp : "y \<in> M \<Longrightarrow> checkR(M,uno,y) = { <checkR(M,uno,w),uno> . w \<in> y}"
  apply (rule trans)
  apply (rule_tac h="checkR(M,uno)" and H="Hcheck(uno)" 
          in def_wfrec)
    apply (unfold checkR_def,simp)
   apply (rule wf_Memrel [THEN wf_trancl])
  apply (unfold Hcheck_def)
  sorry
(*  apply (rule lam_cons [THEN trans],rule lam_dom)
  apply (rule subsetI)
  apply (rule_tac b="y" in vimageI,rule r_into_trancl)
   apply (rule MemrelI,simp)
    apply (rule_tac A="y" in ecloseD)
     apply (rule arg_into_eclose,assumption+)
   apply (rule arg_into_eclose,assumption)
  apply (rule singletonI)
  done
*)
lemma dom_check : "y \<in> M \<Longrightarrow> domain(checkR(M,uno,y)) = { checkR(M,uno,w) . w \<in> y }"
  apply (subst check_simp)
  apply auto
  done
  
lemma apply2_repfun : "RepFun(RepFun(B,g),f) = Union({{f(g(x))}. x\<in>B})"
  by auto
  

lemma lam_apply : "a\<in>B \<Longrightarrow> Lambda(B,f)`a = f(a)"
  by simp

lemma pair_in2 : "{<f(z),b>.z\<in>x} \<in> M \<Longrightarrow> a \<in> x \<Longrightarrow> f(a) \<in> eclose(M)"
  apply (rule_tac A="{f(a)}" in ecloseD)
   apply (rule_tac A="<f(a),b>" in ecloseD)
    apply (rule_tac A="{\<langle>f(z), b\<rangle> . z \<in> x}" in ecloseD)
  apply (rule arg_into_eclose,assumption)
  apply (auto)
  apply (unfold Pair_def,simp)
  done

(* para check_in: primero probar check(x) \<in>3 check(w), luego
usar que \<in>3 \<subseteq> Memrel(eclose(M))+ *)

lemma check_in : "checkR(M,uno,w) \<in> M \<Longrightarrow>  w \<in> M \<Longrightarrow> x \<in> w \<Longrightarrow>
                   checkR(M, uno, x) \<in> Memrel(eclose(M))^+ -`` {checkR(M, uno, w)}"
  apply (rule_tac b="checkR(M,uno,w)" in vimageI)
   apply (rule_tac b="{checkR(M,uno,x)}" in trancl_trans)
    apply (rule r_into_trancl,rule MemrelI)
      apply simp
     apply (subst (asm) check_simp,assumption)
     apply (rule_tac f="checkR(M,uno)" and b="uno" and x="w" in pair_in2)
  apply(assumption+)
    apply (subst (asm) check_simp,assumption)
    apply (rule_tac A="<checkR(M,uno,x),uno>" in ecloseD)
    apply (rule_tac A="{\<langle>checkR(M, uno, w), uno\<rangle> . w \<in> w}" in ecloseD)
     apply (rule arg_into_eclose,assumption,auto)
   apply (unfold Pair_def,simp)
  apply (fold Pair_def)
  apply (subst (asm) check_simp,assumption,subst check_simp,assumption)
  apply (rule r_into_trancl)
  apply (rule MemrelI)
  sorry
  
lemma check_in_M : "Transset(M) \<Longrightarrow> y \<in> w \<Longrightarrow> checkR(M,uno,w) \<in> M \<Longrightarrow>
                    checkR(M,uno,y) \<in> M"
  sorry
   

lemma valcheck : "y \<in> M \<Longrightarrow> Transset(M) \<Longrightarrow> uno \<in> P \<Longrightarrow> uno \<in> G \<Longrightarrow> 
       checkR(M,uno,y) \<in> M \<longrightarrow> valR(M,P,G,checkR(M,uno,y))  = y"
  apply (rule_tac r="trancl(Memrel(eclose(M)))" and a="y" and A="M" in wf_on_induct)
   apply (rule wf_imp_wf_on,rule wf_trancl)
    apply (rule wf_Memrel,assumption)
  apply (rule impI)
  apply (rule trans)
   apply (rule_tac h="valR(M,P,G)" and r="trancl(Memrel(eclose(M)))" in def_wfrec)
   apply (simp add: valR_def)
   apply (rule wf_Memrel [THEN wf_trancl],rename_tac "w")
  apply (unfold Hval_def)
  apply (subst domain_check,assumption+)
  apply (subst dom_check,assumption)
  apply (subst apply2_repfun)
  apply (rule trans)
  apply (rule_tac  A="w" and B="w" and D="\<lambda>x . {valR(M,P,G,checkR(M,uno,x))}" in UN_cong,simp)
  apply (subst lam_apply,auto)
   apply (rule check_in,assumption+)
  apply (rule trans)
  apply (rule_tac A="w" and B="w" and C="\<lambda>x . {valR(M,P,G,checkR(M,uno,x))}" and
         D="\<lambda>x. {x}" in UN_cong,simp)
   apply (rule iffD2)
  apply (rule singleton_eq_iff)
   apply (rule_tac P="x \<in> M \<and> \<langle>x, w\<rangle> \<in> Memrel(eclose(M))^+ \<and> checkR(M,uno,x) \<in> M" in mp)
    apply simp
   apply (rule conjI)
    apply (rule_tac A="w" in subsetD)
     apply (unfold Transset_def,simp,assumption)
   apply (rule conjI)
    apply (rule r_into_trancl,rule MemrelI,assumption)
  apply (rule_tac A="w" in ecloseD,(rule arg_into_eclose,assumption+)+)
  apply (rule_tac w="w" in check_in_M,fold Transset_def,assumption+)
  apply (rule UN_singleton)
  done
  
end
