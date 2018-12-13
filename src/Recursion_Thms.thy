theory Recursion_Thms imports ZF.WF begin


(* Restrict the relation r to the field A*A *)
definition fld_restrict :: "[i, i] \<Rightarrow> i"
  where "fld_restrict(r,A) == {z \<in> r. \<exists>x\<in>A. \<exists>y\<in>A. z = \<langle>x,y\<rangle>}"
  
lemma fld_restrictI : "<x,y> \<in> r \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> <x,y> \<in> fld_restrict(r,A)"
  by (simp add : fld_restrict_def)
    
lemma fld_restrictD : "x \<in> fld_restrict(r,A) \<Longrightarrow> \<exists> a \<in> A . \<exists> b \<in> A . x = <a,b>"
  by (simp add:fld_restrict_def)
    
lemma fld_restrict_mono :
  assumes "relation(r)" and "A \<subseteq> B"
  shows  "fld_restrict(r,A) \<subseteq> fld_restrict(r,B)"
proof 
  fix x
  assume xr:"x \<in> fld_restrict(r,A)"
  from xr have "\<exists> a \<in> A . \<exists> b \<in> A . x = <a,b>" by (simp add: fld_restrict_def)
  then obtain a b where "<a,b> \<in> fld_restrict(r,A)" "a \<in> B" "b \<in> B" "x \<in> fld_restrict(r,B)" using assms xr 
      unfolding fld_restrict_def by blast
  then show "x\<in> fld_restrict(r,B)" by auto
qed     
lemma fld_restrict_subset: "fld_restrict(f,A) \<subseteq> f"
by (unfold fld_restrict_def, blast)

lemma fld_restrict_dom :
  assumes "relation(r)" "domain(r) \<subseteq> A" "range(r)\<subseteq> A"
  shows "fld_restrict(r,A) = r"
  proof (rule equalityI[OF fld_restrict_subset],rule subsetI)
    fix x
    assume xr: "x \<in> r"
    from xr assms have "\<exists> a b . x = <a,b>" by (simp add: relation_def)
    then obtain a b where "<a,b> \<in> r" "<a,b> \<in> fld_restrict(r,A)" "x \<in> fld_restrict(r,A)" 
      using assms xr fld_restrict_def 
      by force
    then show "x\<in>fld_restrict(r,A)" by simp
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
  shows "r-``{a} = fld_restrict(r,B)-``{a}"
proof 
  { fix x 
    assume "x \<in> r-``{a}"
    then have "x \<in> B" using assms by (simp add: subsetD)
    from \<open>x\<in> r-``{a}\<close> underD have "<x,a> \<in> r" by simp
    then have "x \<in> fld_restrict(r,B)-``{a}" using \<open>x \<in> B\<close> assms underI fld_restrict_def by force
  }
  then show "r -`` {a} \<subseteq> fld_restrict(r, B) -`` {a}" by auto
next
  from fld_restrict_subset vimage_mono assms
  show "fld_restrict(r, B) -`` {a} \<subseteq> r -`` {a}" by simp
qed
  
lemma wfrec_restr :
  assumes rr: "relation(r)" and wfr:"wf(r)" 
  shows  "a \<in> A \<Longrightarrow> tr_down(r,a) \<subseteq> A \<Longrightarrow> wfrec(r,a,H) = wfrec(fld_restrict(r,A),a,H)"
proof (induct a arbitrary:A rule:wf_induct_raw[OF wfr] )
  case (1 a)
  from wf_subset fld_restrict_subset wfr have wfRa : "wf(fld_restrict(r,A))" by simp
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
    then have "wfrec(r,x,H) = wfrec(fld_restrict(r,A),x,H)" 
      using 1 \<open>tr_down(r,x) \<subseteq> A\<close> \<open>x \<in> A\<close> by simp
  }
  then have "x\<in> r-``{a} \<Longrightarrow> wfrec(r,x,H) =  wfrec(fld_restrict(r,A),x,H)" for x  . 
  then have Eq1 :"(\<lambda> x \<in> r-``{a} . wfrec(r,x,H)) = (\<lambda> x \<in> r-``{a} . wfrec(fld_restrict(r,A),x,H))" 
    using lam_cong by simp
      
  from assms have 
    "wfrec(r,a,H) = H(a,\<lambda> x \<in> r-``{a} . wfrec(r,x,H))" by (simp add:wfrec)
  also have "... = H(a,\<lambda> x \<in> r-``{a} . wfrec(fld_restrict(r,A),x,H))"
    using assms Eq1 by simp
  also have "... = H(a,\<lambda> x \<in> fld_restrict(r,A)-``{a} . wfrec(fld_restrict(r,A),x,H))"
    using 1 assms rest_eq \<open>r-``{a} \<subseteq> A\<close> by simp
  also have "... = wfrec(fld_restrict(r,A),a,H)" using wfRa wfrec by simp
  finally have "wfrec(r,a,H) = wfrec(fld_restrict(r,A),a,H)" by simp
  then show ?case .
qed

lemmas wfrec_tr_down = wfrec_restr[OF _ _ _ subset_refl]

lemma wfrec_trans_restr : "relation(r) \<Longrightarrow> wf(r) \<Longrightarrow> trans(r) \<Longrightarrow> r-``{a}\<subseteq>A \<Longrightarrow> a \<in> A \<Longrightarrow>
  wfrec(r, a, H) = wfrec(fld_restrict(r, A), a, H)"
  by(subgoal_tac "tr_down(r,a) \<subseteq> A",auto simp add : wfrec_restr tr_down_def trancl_eq_r)  
      
end
