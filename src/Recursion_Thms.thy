theory Recursion_Thms imports WF begin


(* Restrict the relation r to the domain A *)
definition rel_restrict :: "[i, i] \<Rightarrow> i"
  where "rel_restrict(r,A) == {z \<in> r. \<exists>x\<in>A. \<exists>y\<in>A. z = \<langle>x,y\<rangle>}"
  
lemma rel_restrictI : "<x,y> \<in> r \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> <x,y> \<in> rel_restrict(r,A)"
  by (simp add : rel_restrict_def)
    
lemma rel_restrictD : "x \<in> rel_restrict(r,A) \<Longrightarrow> \<exists> a \<in> A . \<exists> b \<in> A . x = <a,b>"
  by (simp add:rel_restrict_def)
    
lemma restrict_mono :
  assumes "relation(r)" and "A \<subseteq> B"
  shows  "rel_restrict(r,A) \<subseteq> rel_restrict(r,B)"
proof 
  fix x
  assume xr:"x \<in> rel_restrict(r,A)"
  from xr have "\<exists> a \<in> A . \<exists> b \<in> A . x = <a,b>" by (simp add: rel_restrict_def)
  then obtain a b where "<a,b> \<in> rel_restrict(r,A)" "a \<in> B" "b \<in> B" "x \<in> rel_restrict(r,B)" using assms xr 
      unfolding rel_restrict_def by blast
  then show "x\<in> rel_restrict(r,B)" by auto
qed     
lemma rel_restrict_subset: "rel_restrict(f,A) \<subseteq> f"
by (unfold rel_restrict_def, blast)

lemma rel_restrict_dom :
  assumes "relation(r)" "domain(r) \<subseteq> A" "range(r)\<subseteq> A"
  shows "rel_restrict(r,A) = r"
  proof (rule equalityI[OF rel_restrict_subset],rule subsetI)
    fix x
    assume xr: "x \<in> r"
    from xr assms have "\<exists> a b . x = <a,b>" by (simp add: relation_def)
    then obtain a b where "<a,b> \<in> r" "<a,b> \<in> rel_restrict(r,A)" "x \<in> rel_restrict(r,A)" 
      using assms xr rel_restrict_def 
      by force
    then show "x\<in>rel_restrict(r,A)" by simp
qed

definition tr_down :: "[i,i] \<Rightarrow> i"
  where "tr_down(r,a) = (r^+)-``{a}"

lemma tr_downD : "x \<in> tr_down(r,a) \<Longrightarrow> <x,a> \<in> r^+"
  by (simp add: tr_down_def vimage_singleton_iff)
    
lemma pred_down : "relation(r) \<Longrightarrow> r-``{a} \<subseteq> tr_down(r,a)"
 by(simp add: tr_down_def vimage_mono r_subset_trancl)

lemma tr_down_mono : "relation(r) \<Longrightarrow> x \<in> r-``{a} \<Longrightarrow> tr_down(r,x) \<subseteq> tr_down(r,a)"
  by(rule subsetI,simp add:tr_down_def,(drule underD)+,force simp add: underI r_into_trancl trancl_trans)
    
lemma rest_eq : 
  assumes "relation(r)" and "r-``{a} \<subseteq> B" and "a \<in> B"
  shows "r-``{a} = rel_restrict(r,B)-``{a}"
proof 
  { fix x 
    assume "x \<in> r-``{a}"
    then have "x \<in> B" using assms by (simp add: subsetD)
    from \<open>x\<in> r-``{a}\<close> underD have "<x,a> \<in> r" by simp
    then have "x \<in> rel_restrict(r,B)-``{a}" using \<open>x \<in> B\<close> assms underI rel_restrict_def by force
  }
  then show "r -`` {a} \<subseteq> rel_restrict(r, B) -`` {a}" by auto
next
  from rel_restrict_subset vimage_mono assms
  show "rel_restrict(r, B) -`` {a} \<subseteq> r -`` {a}" by simp
qed
  
lemma wfrec_restr :
  assumes rr: "relation(r)" and wfr:"wf(r)" 
  shows  "a \<in> A \<Longrightarrow> tr_down(r,a) \<subseteq> A \<Longrightarrow> wfrec(r,a,H) = wfrec(rel_restrict(r,A),a,H)"
proof (induct a arbitrary:A rule:wf_induct_raw[OF wfr] )
  case (1 a)
  from wf_subset rel_restrict_subset wfr have wfRa : "wf(rel_restrict(r,A))" by simp
  from pred_down rr have "r -`` {a} \<subseteq> tr_down(r, a)"  .
  then have "r-``{a} \<subseteq> A" using 1 by (force simp add: subset_trans)
  {
    fix x
    assume x_a : "x \<in> r-``{a}"
    with \<open>r-``{a} \<subseteq> A\<close> have "x \<in> A" ..        
    from pred_down rr have b : "r -``{x} \<subseteq> tr_down(r,x)" .
    then have "tr_down(r,x) \<subseteq> tr_down(r,a)" 
      using tr_down_mono x_a rr by simp
    then have "tr_down(r,x) \<subseteq> A" using 1 subset_trans by force
    have "<x,a> \<in> r" using x_a  underD by simp
    then have "wfrec(r,x,H) = wfrec(rel_restrict(r,A),x,H)" 
      using 1 \<open>tr_down(r,x) \<subseteq> A\<close> \<open>x \<in> A\<close> by simp
  }
  then have "x\<in> r-``{a} \<Longrightarrow> wfrec(r,x,H) =  wfrec(rel_restrict(r,A),x,H)" for x  . 
  then have Eq1 :"(\<lambda> x \<in> r-``{a} . wfrec(r,x,H)) = (\<lambda> x \<in> r-``{a} . wfrec(rel_restrict(r,A),x,H))" 
    using lam_cong by simp
      
  from assms have 
    "wfrec(r,a,H) = H(a,\<lambda> x \<in> r-``{a} . wfrec(r,x,H))" by (simp add:wfrec)
  also have "... = H(a,\<lambda> x \<in> r-``{a} . wfrec(rel_restrict(r,A),x,H))"
    using assms Eq1 by simp
  also have "... = H(a,\<lambda> x \<in> rel_restrict(r,A)-``{a} . wfrec(rel_restrict(r,A),x,H))"
    using 1 assms rest_eq \<open>r-``{a} \<subseteq> A\<close> by simp
  also have "... = wfrec(rel_restrict(r,A),a,H)" using wfRa wfrec by simp
  finally have "wfrec(r,a,H) = wfrec(rel_restrict(r,A),a,H)" by simp
  then show ?case .
qed

lemmas wfrec_tr_down = wfrec_restr[OF _ _ _ subset_refl]

lemma wfrec_trans_restr : "relation(r) \<Longrightarrow> wf(r) \<Longrightarrow> trans(r) \<Longrightarrow> r-``{a}\<subseteq>A \<Longrightarrow> a \<in> A \<Longrightarrow>
  wfrec(r, a, H) = wfrec(rel_restrict(r, A), a, H)"
  by(subgoal_tac "tr_down(r,a) \<subseteq> A",auto simp add : wfrec_restr tr_down_def trancl_eq_r)  
      
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
              "f = (\<lambda>x\<in>r -`` {a}. H(x,  restrict(f, r -`` {x}))) \<longleftrightarrow>
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
  

end
