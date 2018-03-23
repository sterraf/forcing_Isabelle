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


lemma e3I [intro] : "x \<in> a \<Longrightarrow> a \<in> b \<Longrightarrow> b \<in> y \<Longrightarrow>
            e3(x,y)"
  by (simp add: e3_def,blast)


lemma e3_Memrel : "Transset(M) \<Longrightarrow> y \<in> M \<Longrightarrow> e3(x,y) \<Longrightarrow> <x,y> \<in> Memrel(eclose(M))^+"
  sorry

lemma e3_transM : "Transset(M) \<Longrightarrow> y \<in> M \<Longrightarrow> e3(x,y) \<Longrightarrow> x \<in> M"
  sorry

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
  sorry 
    
lemma "M\<noteq>0 \<Longrightarrow> 0 \<in> domain(Memrel(eclose(M))^+)"
  apply (rule domainI,rule r_into_trancl)
  find_theorems "?x \<in> eclose(?a)"
 apply (rule_tac b="{0}" in MemrelI,simp)
 apply (rule_tac B="{0}" in mem_eclose_trans)
  sorry

definition ed :: "[i,i] \<Rightarrow> o" where
  "ed(x,y) == x \<in> domain(y)"  
  
  
definition 
  Hcheck :: "[i,i,i] \<Rightarrow> i" where
  "Hcheck(uno,z,f)  == { <f`y,uno> . y \<in> z}"

definition
  checkR :: "[i,i,i] \<Rightarrow> i" where
  "checkR(M,uno,x) == wfrec(trancl(Memrel(eclose(M))), x , Hcheck(uno))"


(* Val *)
definition
  Hval :: "[i,i,i,i] \<Rightarrow> i" where
  "Hval(P,G,x,f) == { f`y .y\<in>{w \<in> domain(x).(\<exists>p\<in>P. <w,p> \<in> x \<and> p \<in> G) }}"

definition
  valR :: "[i,i,i,i] \<Rightarrow> i" where
  "valR(M,P,G,\<tau>) == wfrec(trancl(Memrel(eclose(M))), \<tau> ,Hval(P,G))"

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

lemma sub_e : "y \<in> M \<Longrightarrow> y \<subseteq> Memrel(eclose(M))^+ -`` {y}"
  apply clarsimp
  apply (rule_tac b="y" in vimageI)
   apply (rule MemrelI [THEN r_into_trancl],assumption)
    apply (rule_tac A="y" in ecloseD)
     apply ((rule arg_into_eclose,assumption+)+)
  apply simp
  done
  

lemma lam_dom : "A\<subseteq>B \<Longrightarrow> {Lambda(B,f)`y . y\<in>A } = {f(y) . y\<in>A}"
  apply (rule RepFun_cong)
   apply auto
  done

(*esto no es cierto: *)
lemma lam_cons : "A\<subseteq>B \<Longrightarrow> {<Lambda(B,f)`y,a> . y\<in>A} = 
                  {Lambda(B,\<lambda>x.<f(x),a>)`y . y\<in>A}"
  apply (rule RepFun_cong)
   apply auto
  done

lemma check_simp : "y \<in> M \<Longrightarrow> checkR(M,uno,y) = { <checkR(M,uno,w),uno> . w \<in> y}"
  apply (rule trans)
  apply (rule_tac h="checkR(M,uno)" and H="Hcheck(uno)" 
          in def_wfrec)
    apply (unfold checkR_def,simp)
   apply (rule wf_Memrel [THEN wf_trancl])
  apply (fold checkR_def)
  apply (unfold Hcheck_def)
  apply (rule trans,rule lam_cons)
   apply (rule sub_e,assumption)
  apply (rule lam_dom,rule sub_e,assumption)
  done
lemma dom_check : "y \<in> M \<Longrightarrow> domain(checkR(M,uno,y)) = { checkR(M,uno,w) . w \<in> y }"
  apply (subst check_simp)
  apply auto
  done


lemma check_uno : "y \<in> M \<Longrightarrow> uno \<in> P \<Longrightarrow> uno \<in> G \<Longrightarrow> 
                  x \<in> domain(checkR(M,uno,y)) \<Longrightarrow>
                  \<exists>p\<in>P . <x,p> \<in> checkR(M,uno,y) \<and> p \<in> G"
  apply (rule_tac x="uno" in bexI)
   apply (rule conjI)
    apply (subst check_simp,assumption)
    apply simp
    apply (subst (asm) dom_check,assumption)
    apply (rule_tac b="x" and f="checkR(M,uno)" and A="y" in RepFunE,assumption)
    apply (rule_tac x="xa" in bexI,assumption+)
  done
      
  
lemma domain_check : "y \<in> M \<Longrightarrow> uno \<in> P \<Longrightarrow> uno \<in> G \<Longrightarrow> 
   {x \<in> domain(checkR(M, uno, y)) .  \<exists>p\<in>P. \<langle>x, p\<rangle> \<in> checkR(M, uno, y) \<and> p \<in> G}
    = domain(checkR(M,uno,y))" 
  apply (rule trans)
   apply (rule_tac B="domain(checkR(M,uno,y))" and Q="\<lambda>x. True" in Collect_cong,simp)
   apply simp
   apply (rule check_uno,assumption+)
  apply (simp)
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

lemma check_e3 : "w\<in>M \<Longrightarrow> x \<in> w \<Longrightarrow> e3(checkR(M,uno,x),checkR(M,uno,w))"
   apply (rule_tac a="{checkR(M,uno,x)}" and b="<checkR(M,uno,x),uno>" in e3I)
     apply simp
    apply (unfold Pair_def,simp,fold Pair_def)
   apply (subst (2) check_simp,assumption,simp)
   apply (rule_tac x="x" in bexI,simp,assumption)
  done

lemma check_in : "Transset(M) \<Longrightarrow> checkR(M,uno,w) \<in> M \<Longrightarrow>  w \<in> M \<Longrightarrow> x \<in> w \<Longrightarrow>
                   checkR(M, uno, x) \<in> Memrel(eclose(M))^+ -`` {checkR(M, uno, w)}"
  apply (rule_tac b="checkR(M,uno,w)" in vimageI)
   apply (rule e3_Memrel,assumption+)
  apply (rule check_e3,assumption+,simp)
  done

lemma check_in_M : "Transset(M) \<Longrightarrow> w \<in> M \<Longrightarrow> y \<in> w \<Longrightarrow> checkR(M,uno,w) \<in> M \<Longrightarrow>
                    checkR(M,uno,y) \<in> M"
  apply (rule_tac y="checkR(M,uno,w)" in e3_transM,assumption+)
  apply (rule check_e3,assumption+)
  done  

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
