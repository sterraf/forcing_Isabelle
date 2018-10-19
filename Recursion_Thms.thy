theory Recursion_Thms imports WF begin

  
definition tdown :: "[i,i] \<Rightarrow> i"
  where "tdown(r,a) = (r^+)-``{a}"

lemma pred_down : "relation(r) \<Longrightarrow> r-``{a} \<subseteq> tdown(r,a)"
 by(simp add: tdown_def vimage_mono r_subset_trancl)

lemma rest_eq : 
  assumes "r-``{a} \<subseteq> B"
  shows "r-``{a} = restrict(r,B)-``{a}"
 sorry
 
   
lemma wfrec_restr : 
  assumes "relation(r)" "wf(r)"
  shows  "wfrec(r,a,H) = wfrec(restrict(r,tdown(r,a)),a,H)"
proof -
  have "wfrec(r,a,H) = H(a,\<lambda> x \<in> r-``{a} . wfrec(r,x,H))"
    using assms by (simp add: wfrec)
  then have "... = H(a,\<lambda> x \<in> restrict(r,tdown(r,a))-``{a} . wfrec(r,x,H))"
    using assms by (subst rest_eq[of "r" "a" "tdown(r,a)"],simp add:pred_down,simp)
  
      
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
  
lemma pavo : 
  assumes ir : "<a,b> \<in>r" "domain(r) \<subseteq> A"
  shows "<a,b> \<in> restrict(r,A)"
  proof -
    from assms ir have "a \<in> A" by auto
    then have ab: "<a,b> \<in> restrict(r,A)" using ir restrict_def
      by simp
    then  show ?thesis by auto
qed
    
lemma restrict_dom :
  assumes "relation(r)" "domain(r) \<subseteq> A"
  shows "restrict(r,A) = r"
  proof (rule equalityI[OF  restrict_subset],rule subsetI)
    fix x
    assume xr: "x \<in> r"
    from xr assms have "\<exists> a b . x = <a,b>" by (simp add: relation_def)
    then obtain a b where "<a,b> \<in> r" "<a,b> \<in> restrict(r,A)" "x \<in> restrict(r,A)" using assms xr pavo 
      by(auto)
    then show "x\<in>restrict(r,A)" by simp
qed
end
(*  
        
*)