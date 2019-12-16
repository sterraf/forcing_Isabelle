theory Recursion_Thms imports ZF.Epsilon begin

(* Restrict the relation r to the field A*A *)
    
lemma fld_restrict_eq : "a \<in> A \<Longrightarrow> (r\<inter>A*A)-``{a} = (r-``{a} \<inter> A)"
  by(force)

lemma fld_restrict_mono : "relation(r) \<Longrightarrow> A \<subseteq> B \<Longrightarrow> r\<inter>A*A \<subseteq> r\<inter>B*B"
  by(auto)

lemma fld_restrict_dom : 
  assumes "relation(r)" "domain(r) \<subseteq> A" "range(r)\<subseteq> A"
  shows "r\<inter>A*A = r"
  proof (rule equalityI,blast,rule subsetI)
    { fix x
    assume xr: "x \<in> r"
    from xr assms have "\<exists> a b . x = <a,b>" by (simp add: relation_def)
    then obtain a b where "<a,b> \<in> r" "<a,b> \<in> r\<inter>A*A" "x \<in> r\<inter>A*A" 
      using assms xr 
      by force
    then have "x\<in> r \<inter> A*A" by simp
  }
  then show "x \<in> r \<Longrightarrow> x\<in> r\<inter>A*A" for x .
qed

definition tr_down :: "[i,i] \<Rightarrow> i"
  where "tr_down(r,a) = (r^+)-``{a}"

lemma tr_downD : "x \<in> tr_down(r,a) \<Longrightarrow> <x,a> \<in> r^+"
  by (simp add: tr_down_def vimage_singleton_iff)
    
lemma pred_down : "relation(r) \<Longrightarrow> r-``{a} \<subseteq> tr_down(r,a)"
 by(simp add: tr_down_def vimage_mono r_subset_trancl)

lemma tr_down_mono : "relation(r) \<Longrightarrow> x \<in> r-``{a} \<Longrightarrow> tr_down(r,x) \<subseteq> tr_down(r,a)"
  by(rule subsetI,simp add:tr_down_def,auto dest: underD,force simp add: underI r_into_trancl trancl_trans)
    
lemma rest_eq : 
  assumes "relation(r)" and "r-``{a} \<subseteq> B" and "a \<in> B"
  shows "r-``{a} = (r\<inter>B*B)-``{a}"
proof 
  { fix x 
    assume "x \<in> r-``{a}"
    then have "x \<in> B" using assms by (simp add: subsetD)
    from \<open>x\<in> r-``{a}\<close> underD have "<x,a> \<in> r" by simp
    then have "x \<in> (r\<inter>B*B)-``{a}" using \<open>x \<in> B\<close> \<open>a\<in>B\<close> underI by simp
  }
  then show "r -`` {a} \<subseteq> (r\<inter>B*B)-`` {a}" by auto
next
  from vimage_mono assms
  show "(r\<inter>B*B) -`` {a} \<subseteq> r -`` {a}" by auto
qed

lemma wfrec_restr_eq : "r' = r \<inter> A*A \<Longrightarrow> wfrec[A](r,a,H) = wfrec(r',a,H)"
  by(simp add:wfrec_on_def)
    
lemma wfrec_restr :
  assumes rr: "relation(r)" and wfr:"wf(r)" 
  shows  "a \<in> A \<Longrightarrow> tr_down(r,a) \<subseteq> A \<Longrightarrow> wfrec(r,a,H) = wfrec[A](r,a,H)"
proof (induct a arbitrary:A rule:wf_induct_raw[OF wfr] )
  case (1 a)
  from wf_subset wfr wf_on_def Int_lower1 have wfRa : "wf[A](r)" by simp
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
    then have "wfrec(r,x,H) = wfrec[A](r,x,H)" 
      using 1 \<open>tr_down(r,x) \<subseteq> A\<close> \<open>x \<in> A\<close> by simp
  }
  then have "x\<in> r-``{a} \<Longrightarrow> wfrec(r,x,H) =  wfrec[A](r,x,H)" for x  . 
  then have Eq1 :"(\<lambda> x \<in> r-``{a} . wfrec(r,x,H)) = (\<lambda> x \<in> r-``{a} . wfrec[A](r,x,H))" 
    using lam_cong by simp
      
  from assms have 
    "wfrec(r,a,H) = H(a,\<lambda> x \<in> r-``{a} . wfrec(r,x,H))" by (simp add:wfrec)
  also have "... = H(a,\<lambda> x \<in> r-``{a} . wfrec[A](r,x,H))"
    using assms Eq1 by simp
  also have "... = H(a,\<lambda> x \<in> (r\<inter>A*A)-``{a} . wfrec[A](r,x,H))"
    using 1 assms rest_eq \<open>r-``{a} \<subseteq> A\<close> by simp
  also have "... = H(a,\<lambda> x \<in> (r-``{a})\<inter>A . wfrec[A](r,x,H))"
    using \<open>a\<in>A\<close> fld_restrict_eq by simp
  also have "... = wfrec[A](r,a,H)" using \<open>wf[A](r)\<close> \<open>a\<in>A\<close> wfrec_on by simp 
  finally show ?case .
qed
  
lemmas wfrec_tr_down = wfrec_restr[OF _ _ _ subset_refl]

lemma wfrec_trans_restr : "relation(r) \<Longrightarrow> wf(r) \<Longrightarrow> trans(r) \<Longrightarrow> r-``{a}\<subseteq>A \<Longrightarrow> a \<in> A \<Longrightarrow>
  wfrec(r, a, H) = wfrec[A](r, a, H)"
  by(subgoal_tac "tr_down(r,a) \<subseteq> A",auto simp add : wfrec_restr tr_down_def trancl_eq_r)  


lemma field_trancl : "field(r^+) = field(r)"
by (blast intro: r_into_trancl dest!: trancl_type [THEN subsetD])

definition
  Rrel :: "[i\<Rightarrow>i\<Rightarrow>o,i] \<Rightarrow> i" where
  "Rrel(R,A) \<equiv> {z\<in>A\<times>A. \<exists>x y. z = \<langle>x, y\<rangle> \<and> R(x,y)}"

lemma RrelI : "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> R(x,y) \<Longrightarrow> \<langle>x,y\<rangle> \<in> Rrel(R,A)"
  unfolding Rrel_def by simp

lemma Rrel_mem: "Rrel(mem,x) = Memrel(x)"
  unfolding Rrel_def Memrel_def ..

lemma relation_Rrel: "relation(Rrel(R,d))"
  unfolding Rrel_def relation_def by simp

lemma field_Rrel: "field(Rrel(R,d)) \<subseteq>  d"
  unfolding Rrel_def by auto

lemma Rrel_mono : "A \<subseteq> B \<Longrightarrow> Rrel(R,A) \<subseteq> Rrel(R,B)"
  unfolding Rrel_def by blast

lemma Rrel_restr_eq : "Rrel(R,A) \<inter> B\<times>B = Rrel(R,A\<inter>B)"
  unfolding Rrel_def by blast

(* now a consequence of the previous lemmas *)
lemma field_Memrel : "field(Memrel(A)) \<subseteq> A"
  (* unfolding field_def using Ordinal.Memrel_type by blast *)
  using Rrel_mem field_Rrel by blast


lemma restrict_trancl_Rrel:
  assumes "R(w,y)" 
  shows "restrict(f,Rrel(R,d)-``{y})`w
       = restrict(f,(Rrel(R,d)^+)-``{y})`w" 
proof (cases "y\<in>d")
  let ?r="Rrel(R,d)"
  and ?s="(Rrel(R,d))^+"
  case True
  show ?thesis
  proof (cases "w\<in>d")
    case True
    with \<open>y\<in>d\<close> assms
    have "<w,y>\<in>?r" 
      unfolding Rrel_def by blast
    then 
    have "<w,y>\<in>?s" 
      using r_subset_trancl[of ?r] relation_Rrel[of R d] by blast
    with \<open><w,y>\<in>?r\<close> 
    have "w\<in>?r-``{y}" "w\<in>?s-``{y}"
      using vimage_singleton_iff by simp_all
    then 
    show ?thesis by simp
  next
    case False
    then
    have "w\<notin>domain(restrict(f,?r-``{y}))"
      using subsetD[OF field_Rrel[of R d]] by auto
    moreover from \<open>w\<notin>d\<close>
    have "w\<notin>domain(restrict(f,?s-``{y}))"
      using subsetD[OF field_Rrel[of R d], of w] field_trancl[of ?r] 
        fieldI1[of w y ?s] by auto
    ultimately
    have "restrict(f,?r-``{y})`w = 0" "restrict(f,?s-``{y})`w = 0" 
      unfolding apply_def by auto
    then show ?thesis by simp
  qed
next
  let ?r="Rrel(R,d)"
  let ?s="?r^+"
  case False
  then 
  have "?r-``{y}=0" 
    unfolding Rrel_def by blast
  then
  have "w\<notin>?r-``{y}" by simp    
  with \<open>y\<notin>d\<close> assms
  have "y\<notin>field(?s)" 
    using field_trancl subsetD[OF field_Rrel[of R d]] by force
  then 
  have "w\<notin>?s-``{y}" 
    using vimage_singleton_iff by blast
  with \<open>w\<notin>?r-``{y}\<close>
  show ?thesis by simp
qed

lemma restrict_trans_eq:
  assumes "w \<in> y"
  shows "restrict(f,Memrel(eclose({x}))-``{y})`w
       = restrict(f,(Memrel(eclose({x}))^+)-``{y})`w" 
  using assms restrict_trancl_Rrel[of mem ] Rrel_mem by (simp)

end
