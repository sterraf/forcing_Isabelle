theory Names imports Formula begin

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

lemma e3E [elim] : "e3(x,y) \<Longrightarrow> (\<And> a b . x \<in> a \<Longrightarrow> a \<in> b \<Longrightarrow> b \<in> y \<Longrightarrow> P) \<Longrightarrow> P"
  by (simp add:e3_def,blast)
    
    
(* \<questiondown>Es útil? *)
lemma e3_set_coord : 
  "<x,y>\<in>e3_set(M) \<Longrightarrow> \<exists>z . z \<in> y \<and> (\<exists>w . w \<in> z \<and> x \<in> w)"
by (simp add:e3_set_def e3_def )

(*\<questiondown>Qué significa fld?*)
lemma fld_e3_sub_eclose : 
 "\<lbrakk>y \<in> M ; z \<in> y ; w \<in> z\<rbrakk> \<Longrightarrow> z \<in> eclose(M) \<and> w \<in> eclose(M)"
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


lemma rel_sub_memcomp : 
  "e3_set(M) \<subseteq> Memrel(eclose(M)) O Memrel(eclose(M)) O Memrel(eclose(M))"
proof (unfold e3_set_def, unfold e3_def,clarsimp)
  fix x y z w
  assume 
          a:  "x \<in> M" "y \<in> M" "z \<in> y" "w \<in> z" "x \<in> w"
  then have 
          p:  "<x,w> \<in> Memrel(eclose(M))" 
              "<w,z> \<in> Memrel(eclose(M))" 
              "<z,y> \<in> Memrel(eclose(M))"
    by (simp_all add:fld_memrel fld_e3_sub_eclose arg_into_eclose)
  then show     
    "<x,y> \<in> Memrel(eclose(M)) O Memrel(eclose(M)) O Memrel(eclose(M))"
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

lemma transD : "Transset(M) \<Longrightarrow> y \<in> M \<Longrightarrow> y \<subseteq> M" 
  by (unfold Transset_def, blast) 
    
lemma transM_e3 : "Transset(M) \<Longrightarrow> y \<in> M \<Longrightarrow> e3(x,y) \<Longrightarrow> x \<in> M"
  apply (unfold e3_def, clarsimp)
  apply (subgoal_tac "w \<subseteq> M",rule_tac A="w" in subsetD,assumption+)
  apply (rule transD,assumption)
  apply (subgoal_tac "z \<subseteq> M",rule_tac A="z" in subsetD,assumption+)
  apply (rule transD,assumption)
  apply (rule_tac A="y" in subsetD,erule transD,assumption+) 
  done
    
lemma e3_trans : "Transset(M) \<Longrightarrow> y \<in> M \<Longrightarrow> e3(x,y) \<Longrightarrow> <x,y> \<in> e3_set(M)"
  apply (unfold e3_def e3_set_def)
  apply (clarsimp)
  apply (erule transM_e3,assumption,blast)
done

lemma e3_Memrel : "Transset(M) \<Longrightarrow> y \<in> M \<Longrightarrow> e3(x,y) \<Longrightarrow> <x,y> \<in> Memrel(eclose(M))^+"
  apply (rule memcomp_sub_trmem [THEN subsetD])
  apply (rule rel_sub_memcomp [THEN subsetD])
  apply (rule e3_trans,assumption+)
  done  

lemma in_domain_e3 : "x \<in> domain(r) \<Longrightarrow> e3(x,r)"
  apply (rule_tac a="x" and r="r" in domainE,assumption)
  apply (rule_tac a="{x}" and b="<x,y>" in e3I,simp)
  apply (unfold Pair_def,simp,assumption)
  done


definition 
  Hcheck :: "[i,i,i] \<Rightarrow> i" where
  "Hcheck(uno,z,f)  == { <f`y,uno> . y \<in> z}"

definition
  checkR :: "[i,i] \<Rightarrow> i" where
  "checkR(uno,x) == wfrec(trancl(Memrel(eclose({x}))), x , Hcheck(uno))"


(* Val *)
definition
  Hval :: "[i,i,i,i] \<Rightarrow> i" where
  "Hval(P,G,x,f) == { f`y .y\<in>{w \<in> domain(x).(\<exists>p\<in>P. <w,p> \<in> x \<and> p \<in> G) }}"

definition
  valR :: "[i,i,i,i] \<Rightarrow> i" where
  "valR(M,P,G,\<tau>) == wfrec(trancl(Memrel(eclose(M))), \<tau> ,Hval(P,G))"

text\<open>The idea of the "valcheck" theorem is as follows. We 
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

lemma sub_e : "y \<subseteq> Memrel(eclose({y}))^+-`` {y}"
  apply clarsimp
  apply (rule_tac b="y" in vimageI)
   apply (rule MemrelI [THEN r_into_trancl],assumption)
    apply (rule_tac A="y" in ecloseD)
     apply (tactic {* distinct_subgoals_tac *})
     apply (rule arg_into_eclose)
  apply simp_all
  done
    
lemma lam_dom : "A\<subseteq>B \<Longrightarrow> {Lambda(B,f)`y . y\<in>A } = {f(y) . y\<in>A}"
  apply (rule RepFun_cong)
   apply auto
  done

lemma lam_cons : "A\<subseteq>B \<Longrightarrow> y \<in> A \<Longrightarrow> <Lambda(B,f)`y,a> = 
                  Lambda(B,\<lambda>x.<f(x),a>)`y "
  apply clarsimp
  apply (erule_tac P="y\<in>B" in notE)
  apply (erule subsetD,assumption)
done

lemma singleton_eqI : "a = b \<Longrightarrow> {a} = {b}" 
  by (erule singleton_eq_iff [THEN iffD2])

lemma equal_segm_wfrec : 
  "wf(r) \<Longrightarrow> wf(s) \<Longrightarrow> trans(r) \<Longrightarrow> trans(s) \<Longrightarrow>
  \<forall>y\<in>A. \<forall>z. <z,y>\<in>r \<longrightarrow> z\<in>A \<Longrightarrow> 
   \<forall>y\<in>A.  r-``{y} = s-``{y} \<Longrightarrow>
   \<forall>y . y\<in>A \<longrightarrow>  wfrec(r, y, H)=wfrec(s, y, H)"
proof (intro allI, rule_tac r="r" and a="y" in wf_induct_raw, assumption)
  fix y x
  assume
        asm:  "wf(r)" "wf(s)" "trans(s)" 
              "  \<forall>y\<in>A. \<forall>z. <z,y>\<in>r \<longrightarrow> z\<in>A"
              "\<forall>t\<in>A. r-``{t} = s-``{t}"
     and
        trr:  "trans(r)" 
     and               
        IH:   "\<forall>w. \<langle>w, y\<rangle> \<in> r \<longrightarrow> w\<in>A \<longrightarrow>
                 wfrec(r, w, \<lambda>a b. H(a, b)) = wfrec(s, w, \<lambda>a b. H(a, b))"
  have
       pr_eq: "y\<in> A \<longrightarrow> (\<lambda>w\<in>r-``{y}. wfrec(r, w, H)) = (\<lambda>w\<in>s-``{y}. wfrec(s, w, H))"
  proof (intro impI, rule lam_cong)
    assume 
         yrx: "y\<in> A"
    with asm show 
        rs:   "r -`` {y} = s -`` {y}"
      by simp
    fix z
    assume
              "z\<in> s -`` {y}"
    with rs have
        zry: "<z,y>\<in>r"
      by (simp add:underD)
    with asm and yrx have
              "z\<in>A"
      unfolding trans_def by blast
    with IH and zry show
              "wfrec(r, z, H) = wfrec(s, z, H)"
      by simp
  qed
  show
              "y \<in> A \<longrightarrow> wfrec(r, y, \<lambda>a b. H(a, b)) = wfrec(s, y, \<lambda>a b. H(a, b))"
  proof (intro impI)
    assume 
         yrx:  "y \<in> A"
    from asm have
              "wfrec(r, y, \<lambda>a b. H(a, b)) = H(y, \<lambda>w\<in>r-``{y}. wfrec(r, w, H))"
      by (simp add: wfrec)
    also have
              "... = H(y, \<lambda>w\<in>s-``{y}. wfrec(s, w, H))"
      using yrx and pr_eq by simp
    also with asm have
              "... =  wfrec(s, y, \<lambda>a b. H(a, b))"   
      by (simp add: wfrec)
    finally show
              "wfrec(r, y, \<lambda>a b. H(a, b)) = wfrec(s, y, \<lambda>a b. H(a, b))".
  qed
qed  
  
lemmas equal_segm_wfrec_rule =  equal_segm_wfrec [THEN spec, THEN mp]

lemma vimage_mono : "s\<subseteq>r\<Longrightarrow>s-``A \<subseteq> r-``A"
  by auto
    
lemma segment_vimage : "\<forall>y\<in>A. \<forall>z. <z,y>\<in>r \<longrightarrow> z\<in>A \<Longrightarrow> B\<subseteq>A \<Longrightarrow>
       restrict(r,A)-`` B  = r-``B " 
  by (rule equalityI, simp add: restrict_subset vimage_mono, force simp add:restrict_iff)
    
lemma trans_restrict_down :
  "trans(r) \<Longrightarrow> <x,a>\<in>r \<Longrightarrow> r-``{x} = restrict(r,{a}\<union>r-``{a})-``{x}"
  by (rule segment_vimage [symmetric], auto simp:trans_def)

lemma restrict_with_root :
  "restrict(r,{a}\<union>r-``{a})-``{a} = r-``{a}"
  by (rule equalityI, simp add: restrict_subset vimage_mono, force simp add:restrict_iff )
    
declare iff_trans [trans]

lemma is_recfun_segment :
  "trans(r) \<Longrightarrow> is_recfun(r,a,H,f) \<longleftrightarrow> is_recfun(restrict(r,{a}\<union>r-``{a}),a,H,f)"
proof -
  assume
      asm:    "trans(r)"
  let
              ?rr="restrict(r,{a}\<union>r-``{a})"
  have
              "is_recfun(r,a,H,f) \<longleftrightarrow> f = (\<lambda>x\<in>r-``{a}. H(x, restrict(f, r-``{x})))"
    unfolding is_recfun_def ..
  also have
              "... \<longleftrightarrow> f = (\<lambda>x\<in>r-``{a}. H(x, restrict(f, ?rr-``{x})))"
  proof -
    have 
              "\<forall>x. x\<in>r-``{a}\<longrightarrow> H(x, restrict(f, r -`` {x})) = H(x, restrict(f, ?rr -`` {x}))"
      using asm and trans_restrict_down  by auto
    with lam_cong have
              "(\<lambda>x\<in>r-``{a}. H(x, restrict(f, r-``{x}))) =
                (\<lambda>x\<in>r-``{a}. H(x, restrict(f, ?rr-``{x})))"  
      by simp
    then show
              "f = (\<lambda>x\<in>r -`` {a}. H(x, restrict(f, r -`` {x}))) \<longleftrightarrow>
                f = (\<lambda>x\<in>r -`` {a}. H(x, restrict(f, ?rr -`` {x})))" 
      by simp
  qed
  also have
              "... \<longleftrightarrow> f = (\<lambda>x\<in>?rr-``{a}. H(x, restrict(f, ?rr-``{x})))"
    by (simp add: restrict_with_root)
  finally show ?thesis 
    unfolding is_recfun_def by simp
qed

lemma imp_trans : "p\<longrightarrow>q \<Longrightarrow> q\<longrightarrow>r \<Longrightarrow> p\<longrightarrow>r"
  by simp

    (* Lo siguiente debería salir con is_recfun_type *)

lemma is_recfun_f_segment :
  notes imp_trans [trans]
  shows  "trans(r) \<Longrightarrow> is_recfun(r,a,H,f) \<longrightarrow> is_recfun(r,a,H,restrict(f,r-``{a}))"
proof -
  assume
      asm:    "trans(r)"
  let
              ?rf="restrict(f,r-``{a})"
  have
              "is_recfun(r,a,H,f) \<longrightarrow> f = (\<lambda>x\<in>r-``{a}. H(x, restrict(f, r-``{x})))"
    unfolding is_recfun_def ..
  also have
              "... \<longrightarrow> ?rf = (\<lambda>x\<in>r-``{a}. H(x, restrict(?rf, r-``{x})))"
  proof 
    assume 
        ff:   "f = (\<lambda>x\<in>r-``{a}. H(x, restrict(f, r-``{x})))" (is "f = ?f")
    have
              "restrict(?f,r-``{a}) = ?f"
      by (rule  domain_restrict_idem, auto simp add: relation_lam)
    with ff show
              "restrict(f,r-``{a}) = 
               (\<lambda>x\<in>r-``{a}. H(x, restrict(restrict(f,r-``{a}), r-``{x})))" 
      by simp
  qed
  finally show ?thesis
    unfolding is_recfun_def .
qed
  
lemma the_recfun_f_segment :
  "trans(r) \<Longrightarrow> the_recfun(r,a,H) = restrict(the_recfun(r,a,H),r-``{a})"
proof ( simp add:the_recfun_def is_recfun_f_segment)
  
oops

(*
lemma the_recfun_segment :
  "trans(r) \<Longrightarrow> the_recfun(r,a,H) = the_recfun(restrict(r,{a}\<union>r-``{a}),a,H)"
  by (simp add:the_recfun_def is_recfun_segment wftrec_def )

lemma wftrec_segment :
  "trans(r) \<Longrightarrow> wftrec(r,a,H) = wftrec(restrict(r,{a}\<union>r-``{a}),a,H)"  
  by (simp add:wftrec_def the_recfun_segment)
    
*)
  
lemma wftrec_segment :
  "trans(r) \<Longrightarrow> the_recfun(r,a,H) = the_recfun(restrict(r,{a}\<union>r-``{a}),a,H)"
  "trans(r) \<Longrightarrow> wftrec(r,a,H) = wftrec(restrict(r,{a}\<union>r-``{a}),a,H)"  
  by (simp_all add:the_recfun_def is_recfun_segment wftrec_def )
  
lemma trans_restrict:
  "trans(r) \<Longrightarrow> trans(restrict(r,A))" (is "_ \<Longrightarrow> trans(?rr)")
proof (unfold trans_def, intro allI impI)
  fix x y z
  assume 
        asm:  "\<forall>x y z. \<langle>x, y\<rangle> \<in> r \<longrightarrow> \<langle>y, z\<rangle> \<in> r \<longrightarrow> \<langle>x, z\<rangle> \<in> r"
              "\<langle>y, z\<rangle> \<in> ?rr" "\<langle>x, y\<rangle> \<in> ?rr"   
  with restrict_iff have
              "x\<in>A"  "\<langle>x, z\<rangle> \<in> r"
      by auto
  with restrict_iff show 
              "\<langle>x, z\<rangle> \<in> ?rr"
    by simp 
qed
    
lemma wfrec_segment:
  "relation(r) \<Longrightarrow> trans(r) \<Longrightarrow> wfrec(r,a,H) = wfrec(restrict(r,{a}\<union>r-``{a}),a,H)"
proof (simp add:wfrec_def wftrec_segment trancl_eq_r)
  let
              ?rr="restrict(r,{a}\<union>r-``{a})"
  have
              "wftrec(?rr, a, \<lambda>x f. H(x, restrict(f, r -`` {x}))) =
               wftrec(?rr, a, \<lambda>x f. H(x, restrict(f, r -`` {x})))" ..
  oops
   
    
lemma check_simp : "checkR(uno,y) = { <checkR(uno,w),uno> . w \<in> y}"
proof -
  let 
              ?r="\<lambda>y. trancl(Memrel(eclose({y})))"
  from trans_trancl have
       trr:   "\<forall>w . trans(?r(w))" ..
  from wf_trmem have
       wfr:   "\<forall>w . wf(?r(w))" ..
  with wfrec [of "?r(y)" y "Hcheck(uno)"] have
              "checkR(uno,y)= 
               Hcheck(uno, y, \<lambda>x\<in>?r(y) -`` {y}. wfrec(?r(y), x, Hcheck(uno)))"
    by (simp add:checkR_def)
  also have 
              " ... = Hcheck(uno, y, \<lambda>x\<in>?r(y) -`` {y}. checkR(uno,x))"              
  proof (simp add:checkR_def)
    have
              "(\<lambda>x\<in>?r(y)-``{y}. wfrec(?r(y), x, Hcheck(uno))) =
               (\<lambda>x\<in>?r(y)-``{y}. wfrec(?r(x), x, Hcheck(uno)))"
      apply (insert trr wfr, rule lam_cong, simp)
      apply (rule_tac xa="y" in  equal_segm_wfrec_rule)
           prefer 5 apply (rule Memrel_segments, simp_all, blast)
      done
    then show 
              "Hcheck(uno, y, \<lambda>x\<in>?r(y) -`` {y}. wfrec(?r(y), x, Hcheck(uno))) =
               Hcheck(uno, y, \<lambda>x\<in>?r(y) -`` {y}. wfrec(?r(x), x, Hcheck(uno)))" 
      by simp
  qed
  also have
              " ... = {\<langle>if w \<in> Memrel(eclose({y}))^+ -`` {y} then checkR(uno, w) else 0, uno\<rangle> . w \<in> y}"
    by  (simp add:Hcheck_def)
  also have
              " ... = {<checkR(uno,w),uno> . w \<in> y}"
    by (auto simp add:sub_e [THEN subsetD])
  finally show ?thesis .
oops
      
lemma dom_check : "y \<in> M \<Longrightarrow> domain(checkR(uno,y)) = { checkR(uno,w) . w \<in> y }"
  by (subst check_simp,auto)


lemma check_uno : "y \<in> M \<Longrightarrow> uno \<in> P \<Longrightarrow> uno \<in> G \<Longrightarrow> 
                  x \<in> domain(checkR(uno,y)) \<Longrightarrow>
                  \<exists>p\<in>P . <x,p> \<in> checkR(uno,y) \<and> p \<in> G"
  apply (rule_tac x="uno" in bexI)
   apply (rule conjI)
    defer 1 apply assumption+
    apply (subst check_simp)
    apply simp
    apply (subst (asm) dom_check,assumption)
    apply (erule_tac b="x" and f="checkR(uno)" and A="y" in RepFunE)
    apply (erule_tac x="xa" in bexI,assumption+)
  done
      
  
lemma domain_check : "y \<in> M \<Longrightarrow> uno \<in> P \<Longrightarrow> uno \<in> G \<Longrightarrow> 
   {x \<in> domain(checkR( uno, y)) .  \<exists>p\<in>P. \<langle>x, p\<rangle> \<in> checkR( uno, y) \<and> p \<in> G}
    = domain(checkR(uno,y))" 
  apply (rule trans)
   apply (rule_tac B="domain(checkR(uno,y))" and Q="\<lambda>x. True" in Collect_cong,simp)
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
  apply (erule arg_into_eclose)
  apply (auto)
  apply (unfold Pair_def,simp)
  done


lemma check_e3 : "Transset(M) \<Longrightarrow> w\<in>M \<Longrightarrow> x \<in> w \<Longrightarrow> e3(checkR(uno,x),checkR(uno,w))"
   apply (rule_tac a="{checkR(uno,x)}" and b="<checkR(uno,x),uno>" in e3I)
     apply simp
    apply (unfold Pair_def,simp,fold Pair_def)
  apply (subst (2) check_simp)
  apply simp
   apply (rule_tac x="x" in bexI,simp,assumption+)
  done

lemma check_in : "Transset(M) \<Longrightarrow> checkR(uno,w) \<in> M \<Longrightarrow>  w \<in> M \<Longrightarrow> x \<in> w \<Longrightarrow>
                   checkR( uno, x) \<in> Memrel(eclose(M))^+ -`` {checkR( uno, w)}"
  apply (rule_tac b="checkR(uno,w)" in vimageI)
   apply (rule e3_Memrel,assumption+)
  apply (rule check_e3,assumption+,simp)
  done

lemma check_in_M : "Transset(M) \<Longrightarrow> w \<in> M \<Longrightarrow> y \<in> w \<Longrightarrow> checkR(uno,w) \<in> M \<Longrightarrow>
                    checkR(uno,y) \<in> M"
  apply (rule_tac y="checkR(uno,w)" in transM_e3,assumption+)
  apply (rule check_e3,assumption+)
  done  
    
lemma valcheck : "y \<in> M \<Longrightarrow> Transset(M) \<Longrightarrow> uno \<in> P \<Longrightarrow> uno \<in> G \<Longrightarrow> 
       checkR(uno,y) \<in> M \<longrightarrow> valR(M,P,G,checkR(uno,y))  = y"
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
  apply (rule_tac  A="w" and B="w" and D="\<lambda>x . {valR(M,P,G,checkR(uno,x))}" in UN_cong,simp)
  apply (subst lam_apply,auto)
   apply (rule check_in,assumption+)
  apply (rule trans)
  apply (rule_tac A="w" and B="w" and C="\<lambda>x . {valR(M,P,G,checkR(uno,x))}" and
         D="\<lambda>x. {x}" in UN_cong,simp)
   apply (rule singleton_eqI)
   apply (rule_tac P="x \<in> M \<and> \<langle>x, w\<rangle> \<in> Memrel(eclose(M))^+ \<and> checkR(uno,x) \<in> M" in mp)
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
