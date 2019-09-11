theory Relative_Univ
  imports
    Names Rank

begin

lemma (in M_trivial) powerset_subset_Pow:
  assumes 
    "powerset(M,x,y)" "\<And>z. z\<in>y \<Longrightarrow> M(z)"
  shows 
    "y \<subseteq> Pow(x)"
  using assms unfolding powerset_def
  by (auto)
    
lemma (in M_trivial) powerset_abs: 
  assumes
    "M(x)" "\<And>z. z\<in>y \<Longrightarrow> M(z)"
  shows
    "powerset(M,x,y) \<longleftrightarrow> y = {a\<in>Pow(x) . M(a)}"
proof (intro iffI equalityI)
  (* First show the converse implication by double inclusion *)
  assume 
    "powerset(M,x,y)"
  with assms have
    "y \<subseteq> Pow(x)" 
    using powerset_subset_Pow by simp
  with assms show
    "y \<subseteq> {a\<in>Pow(x) . M(a)}"
    by blast
  {
    fix a
    assume 
      "a \<subseteq> x" "M(a)"
    then have 
      "subset(M,a,x)" by simp
    with \<open>M(a)\<close> \<open>powerset(M,x,y)\<close> have
      "a \<in> y"
      unfolding powerset_def by simp
  }
  then show 
    "{a\<in>Pow(x) . M(a)} \<subseteq> y"
    by auto
next (* we show the direct implication *)
  assume 
    "y = {a \<in> Pow(x) . M(a)}"
  then show
    "powerset(M, x, y)"
    unfolding powerset_def
    by simp
qed

lemma (in M_trivial) powerset_abs' [simp]: 
  assumes
    "M(x)" "M(y)"
  shows
    "powerset(M,x,y) \<longleftrightarrow> y = {a\<in>Pow(x) . M(a)}"
  using powerset_abs[OF _ transM] assms by simp

lemma Collect_inter_Transset:
  assumes 
    "Transset(M)" "b \<in> M"
  shows
    "{x\<in>b . P(x)} = {x\<in>b . P(x)} \<inter> M"
    using assms unfolding Transset_def
  by (auto)  

lemma (in M_trivial) family_union_closed: "\<lbrakk>strong_replacement(M, \<lambda>x y. y = f(x)); M(A); \<forall>x\<in>A. M(f(x))\<rbrakk>
      \<Longrightarrow> M(\<Union>x\<in>A. f(x))"
  using RepFun_closed ..

(* "Vfrom(A,i) == transrec(i, %x f. A \<union> (\<Union>y\<in>x. Pow(f`y)))" *)
(* HVfrom is *not* the recursive step for Vfrom. It is the
   relativized version *)
definition
  HVfrom :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> i" where
  "HVfrom(M,A,x,f) \<equiv> A \<union> (\<Union>y\<in>x. {a\<in>Pow(f`y). M(a)})"

(* z = Pow(f`y) *)
definition
  is_powapply :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_powapply(M,f,y,z) \<equiv> M(z) \<and> (\<exists>fy[M]. fun_apply(M,f,y,fy) \<and> powerset(M,fy,z))"

(* Trivial lemma *)
lemma is_powapply_closed: "is_powapply(M,f,y,z) \<Longrightarrow> M(z)"
  unfolding is_powapply_def by simp

(* is_Replace(M,A,P,z) == \<forall>u[M]. u \<in> z \<longleftrightarrow> (\<exists>x[M]. x\<in>A & P(x,u)) *)
definition
  is_HVfrom :: "[i\<Rightarrow>o,i,i,i,i] \<Rightarrow> o" where
  "is_HVfrom(M,A,x,f,h) \<equiv> \<exists>U[M]. \<exists>R[M]. \<exists>P[M]. union(M,A,U,h) 
        \<and> big_union(M,R,U) \<and> is_Replace(M,x,is_powapply(M,f),R)" 


definition
  is_Vfrom :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_Vfrom(M,A,i,V) == is_transrec(M,is_HVfrom(M,A),i,V)"

definition
  is_Vset :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "is_Vset(M,i,V) == \<exists>z[M]. empty(M,z) \<and> is_Vfrom(M,z,i,V)"


subsection\<open>Formula synthesis\<close>

(* Copied from DPow_absolute --- check Names! *)
lemma Replace_iff_sats:
  assumes is_P_iff_sats: 
      "!!a b. [|a \<in> A; b \<in> A|] 
              ==> is_P(a,b) \<longleftrightarrow> sats(A, p, Cons(a,Cons(b,env)))"
  shows 
  "[| nth(i,env) = x; nth(j,env) = y;
      i \<in> nat; j \<in> nat; env \<in> list(A)|]
   ==> is_Replace(##A, x, is_P, y) \<longleftrightarrow> sats(A, is_Replace_fm(i,p,j), env)"
by (simp add: sats_is_Rep_fm [OF is_P_iff_sats])


schematic_goal sats_is_powapply_fm_auto:
  assumes
    "f\<in>nat" "y\<in>nat" "z\<in>nat" "env\<in>list(A)" "0\<in>A"
  shows
    "is_powapply(##A,nth(f, env),nth(y, env),nth(z, env))
    \<longleftrightarrow> sats(A,?ipa_fm(f,y,z),env)"
  unfolding is_powapply_def is_Collect_def powerset_def subset_def
  using nth_closed assms
   by (simp) (rule sep_rules  | simp)+

schematic_goal is_powapply_iff_sats:
  assumes
    "nth(f,env) = ff" "nth(y,env) = yy" "nth(z,env) = zz" "0\<in>A"
    "f \<in> nat"  "y \<in> nat" "z \<in> nat" "env \<in> list(A)"
  shows
       "is_powapply(##A,ff,yy,zz) \<longleftrightarrow> sats(A, ?is_one_fm(a,r), env)"
  unfolding \<open>nth(f,env) = ff\<close>[symmetric] \<open>nth(y,env) = yy\<close>[symmetric]
    \<open>nth(z,env) = zz\<close>[symmetric]
  by (rule sats_is_powapply_fm_auto(1); simp add:assms)

lemma trivial_fm:
  assumes
    "A\<noteq>0" "env\<in>list(A)"
  shows
    "(\<exists>P. P \<in> A) \<longleftrightarrow> sats(A, Equal(0,0), env)"
  using assms by auto

schematic_goal sats_is_HVfrom_fm_auto:
  assumes
    "a\<in>nat" "x\<in>nat" "f\<in>nat" "h\<in>nat" "env\<in>list(A)" "0\<in>A"
  shows
    "is_HVfrom(##A,nth(a, env),nth(x, env),nth(f, env),nth(h, env))
    \<longleftrightarrow> sats(A,?ihvf_fm(a,x,f,h),env)"
  unfolding is_HVfrom_def using assms
  by (simp) (rule sep_rules is_powapply_iff_sats Replace_iff_sats trivial_fm not_emptyI | simp)+

schematic_goal is_HVfrom_iff_sats:
  assumes
    "nth(a,env) = aa" "nth(x,env) = xx" "nth(f,env) = ff" "nth(h,env) = hh"
    "a\<in>nat" "x\<in>nat" "f\<in>nat" "h\<in>nat" "env\<in>list(A)" "0\<in>A"
  shows
       "is_HVfrom(##A,aa,xx,ff,hh) \<longleftrightarrow> sats(A, ?ihvf_fm(a,x,f,h), env)"
  unfolding \<open>nth(a,env) = aa\<close>[symmetric] \<open>nth(x,env) = xx\<close>[symmetric]
    \<open>nth(f,env) = ff\<close>[symmetric] \<open>nth(h,env) = hh\<close>[symmetric]
  by (rule sats_is_HVfrom_fm_auto(1); simp add:assms)

(* Next two are not needed *)
schematic_goal sats_is_Vfrom_fm_auto:
  assumes
    "a\<in>nat" "i\<in>nat" "v\<in>nat" "env\<in>list(A)" "0\<in>A"
    "i < length(env)" "v < length(env)"
  shows
    "is_Vfrom(##A,nth(a, env),nth(i, env),nth(v, env))
    \<longleftrightarrow> sats(A,?ivf_fm(a,i,v),env)"
  unfolding is_Vfrom_def
  by (insert assms; (rule sep_rules is_HVfrom_iff_sats is_transrec_iff_sats | simp)+)

schematic_goal is_Vfrom_iff_sats:
  assumes
    "nth(a,env) = aa" "nth(i,env) = ii" "nth(v,env) = vv"
    "a\<in>nat" "i\<in>nat" "v\<in>nat" "env\<in>list(A)" "0\<in>A"
    "i < length(env)" "v < length(env)"
  shows
    "is_Vfrom(##A,aa,ii,vv) \<longleftrightarrow> sats(A, ?ivf_fm(a,i,v), env)"
  unfolding \<open>nth(a,env) = aa\<close>[symmetric] \<open>nth(i,env) = ii\<close>[symmetric]
    \<open>nth(v,env) = vv\<close>[symmetric]
  by (rule sats_is_Vfrom_fm_auto(1); simp add:assms)

schematic_goal sats_is_Vset_fm_auto:
  assumes
    "i\<in>nat" "v\<in>nat" "env\<in>list(A)" "0\<in>A"
    "i < length(env)" "v < length(env)"
  shows
    "is_Vset(##A,nth(i, env),nth(v, env))
    \<longleftrightarrow> sats(A,?ivs_fm(i,v),env)"
  unfolding is_Vset_def is_Vfrom_def
  by (insert assms; (rule sep_rules is_HVfrom_iff_sats is_transrec_iff_sats | simp)+)

schematic_goal is_Vset_iff_sats:
  assumes
    "nth(i,env) = ii" "nth(v,env) = vv"
    "i\<in>nat" "v\<in>nat" "env\<in>list(A)" "0\<in>A"
    "i < length(env)" "v < length(env)"
  shows
    "is_Vset(##A,ii,vv) \<longleftrightarrow> sats(A, ?ivs_fm(i,v), env)"
  unfolding \<open>nth(i,env) = ii\<close>[symmetric] \<open>nth(v,env) = vv\<close>[symmetric]
  by (rule sats_is_Vset_fm_auto(1); simp add:assms)

section\<open>Absoluteness results\<close>

locale M_eclose_pow = M_eclose + 
  assumes
    power_ax : "power_ax(M)" and
    powapply_replacement : "M(f) \<Longrightarrow> strong_replacement(M,is_powapply(M,f))" and
    HVfrom_replacement : "\<lbrakk> M(i) ; Ord(i) ; M(A) \<rbrakk> \<Longrightarrow> 
                          transrec_replacement(M,is_HVfrom(M,A),i)"

begin

lemma is_powapply_abs: "\<lbrakk>M(f); M(y)\<rbrakk> \<Longrightarrow> is_powapply(M,f,y,z) \<longleftrightarrow> M(z) \<and> z = {x\<in>Pow(f`y). M(x)}"
  unfolding is_powapply_def by simp

lemma "\<lbrakk>M(A); M(x); M(f); M(h) \<rbrakk> \<Longrightarrow> 
      is_HVfrom(M,A,x,f,h) \<longleftrightarrow> 
      (\<exists>R[M]. h = A \<union> \<Union>R \<and> is_Replace(M, x,\<lambda>x y. y = {x \<in> Pow(f ` x) . M(x)}, R))"
  using is_powapply_abs unfolding is_HVfrom_def by auto

lemma Replace_is_powapply:
  assumes
    "M(R)" "M(A)" "M(f)" 
  shows
  "is_Replace(M, A, is_powapply(M, f), R) \<longleftrightarrow> R = Replace(A,is_powapply(M,f))"
proof -
  have "univalent(M,A,is_powapply(M,f))" 
    using \<open>M(A)\<close> \<open>M(f)\<close> unfolding univalent_def is_powapply_def by simp
  moreover
  have "\<And>x y. \<lbrakk> x\<in>A; is_powapply(M,f,x,y) \<rbrakk> \<Longrightarrow> M(y)"
    using \<open>M(A)\<close> \<open>M(f)\<close> unfolding is_powapply_def by simp
  ultimately
  show ?thesis using \<open>M(A)\<close> \<open>M(R)\<close> Replace_abs by simp
qed

lemma powapply_closed:
  "\<lbrakk> M(y) ; M(f) \<rbrakk> \<Longrightarrow> M({x \<in> Pow(f ` y) . M(x)})"
  using apply_closed power_ax unfolding power_ax_def by simp

lemma RepFun_is_powapply:
  assumes
    "M(R)" "M(A)" "M(f)" 
  shows
  "Replace(A,is_powapply(M,f)) = RepFun(A,\<lambda>y.{x\<in>Pow(f`y). M(x)})"
proof -
  have "{y . x \<in> A, M(y) \<and> y = {x \<in> Pow(f ` x) . M(x)}} = {y . x \<in> A, y = {x \<in> Pow(f ` x) . M(x)}}"
    using assms powapply_closed transM[of _ A] by blast
  also
  have " ... = {{x \<in> Pow(f ` y) . M(x)} . y \<in> A}" by auto
  finally 
  show ?thesis using assms is_powapply_abs transM[of _ A] by simp
qed

lemma RepFun_powapply_closed:
  assumes 
    "M(f)" "M(A)"
  shows 
    "M(Replace(A,is_powapply(M,f)))"
proof -
  have "univalent(M,A,is_powapply(M,f))" 
    using \<open>M(A)\<close> \<open>M(f)\<close> unfolding univalent_def is_powapply_def by simp
  moreover
  have "\<lbrakk> x\<in>A ; is_powapply(M,f,x,y) \<rbrakk> \<Longrightarrow> M(y)" for x y
    using assms unfolding is_powapply_def by simp
  ultimately
  show ?thesis using assms powapply_replacement by simp
qed

lemma Union_powapply_closed:
  assumes 
    "M(x)" "M(f)"
  shows 
    "M(\<Union>y\<in>x. {a\<in>Pow(f`y). M(a)})"
proof -
  have "M({a\<in>Pow(f`y). M(a)})" if "y\<in>x" for y
    using that assms transM[of _ x] powapply_closed by simp
  then
  have "M({{a\<in>Pow(f`y). M(a)}. y\<in>x})"
    using assms transM[of _ x]  RepFun_powapply_closed RepFun_is_powapply by simp
  then show ?thesis using assms by simp
qed

lemma relation2_HVfrom: "M(A) \<Longrightarrow> relation2(M,is_HVfrom(M,A),HVfrom(M,A))"
    unfolding is_HVfrom_def HVfrom_def relation2_def
    using Replace_is_powapply RepFun_is_powapply 
          Union_powapply_closed RepFun_powapply_closed by auto

lemma HVfrom_closed : 
  "M(A) \<Longrightarrow> \<forall>x[M]. \<forall>g[M]. function(g) \<longrightarrow> M(HVfrom(M,A,x,g))"
  unfolding HVfrom_def using Union_powapply_closed by simp

lemma transrec_HVfrom:
  assumes "M(A)"
  shows "Ord(i) \<Longrightarrow> {x\<in>Vfrom(A,i). M(x)} = transrec(i,HVfrom(M,A))"
proof (induct rule:trans_induct)
  case (step i)
  have "Vfrom(A,i) = A \<union> (\<Union>y\<in>i. Pow((\<lambda>x\<in>i. Vfrom(A, x)) ` y))"
    using def_transrec[OF Vfrom_def, of A i] by simp
  then 
  have "Vfrom(A,i) = A \<union> (\<Union>y\<in>i. Pow(Vfrom(A, y)))"
    by simp
  then
  have "{x\<in>Vfrom(A,i). M(x)} = {x\<in>A. M(x)} \<union> (\<Union>y\<in>i. {x\<in>Pow(Vfrom(A, y)). M(x)})"
    by auto
  with \<open>M(A)\<close>
  have "{x\<in>Vfrom(A,i). M(x)} = A \<union> (\<Union>y\<in>i. {x\<in>Pow(Vfrom(A, y)). M(x)})" 
    by (auto intro:transM)
  also
  have "... = A \<union> (\<Union>y\<in>i. {x\<in>Pow({z\<in>Vfrom(A,y). M(z)}). M(x)})" 
  proof -
    have "{x\<in>Pow(Vfrom(A, y)). M(x)} = {x\<in>Pow({z\<in>Vfrom(A,y). M(z)}). M(x)}"
      if "y\<in>i" for y by (auto intro:transM)
    then
    show ?thesis by simp
  qed
  also from step 
  have " ... = A \<union> (\<Union>y\<in>i. {x\<in>Pow(transrec(y, HVfrom(M, A))). M(x)})" by auto
  also
  have " ... = transrec(i, HVfrom(M, A))"
    using def_transrec[of "\<lambda>y. transrec(y, HVfrom(M, A))" "HVfrom(M, A)" i,symmetric] 
    unfolding HVfrom_def by simp
  finally
  show ?case .
qed

lemma Vfrom_abs: "\<lbrakk> M(A); M(i); M(V); Ord(i) \<rbrakk> \<Longrightarrow> is_Vfrom(M,A,i,V) \<longleftrightarrow> V = {x\<in>Vfrom(A,i). M(x)}"
  unfolding is_Vfrom_def
  using relation2_HVfrom HVfrom_closed HVfrom_replacement 
    transrec_abs[of "is_HVfrom(M,A)" i "HVfrom(M,A)"] transrec_HVfrom by simp

lemma Vfrom_closed: "\<lbrakk> M(A); M(i); Ord(i) \<rbrakk> \<Longrightarrow> M({x\<in>Vfrom(A,i). M(x)})"
  unfolding is_Vfrom_def
  using relation2_HVfrom HVfrom_closed HVfrom_replacement 
    transrec_closed[of "is_HVfrom(M,A)" i "HVfrom(M,A)"] transrec_HVfrom by simp

lemma Vset_abs: "\<lbrakk> M(i); M(V); Ord(i) \<rbrakk> \<Longrightarrow> is_Vset(M,i,V) \<longleftrightarrow> V = {x\<in>Vset(i). M(x)}"
  using Vfrom_abs unfolding is_Vset_def by simp

lemma Vset_closed: "\<lbrakk> M(i); Ord(i) \<rbrakk> \<Longrightarrow> M({x\<in>Vset(i). M(x)})"
  using Vfrom_closed unfolding is_Vset_def by simp

(*

(* Results to be implemented later *)

(* hint ? *)
lemma rank_eq_wfrank: "rank(a) = wfrank(Memrel(eclose({a})),a)"
  unfolding rank_def transrec_def wfrank_def wfrec_def oops

lemma rank_closed: "M(a) \<Longrightarrow> M(rank(a))"
  sorry

lemma M_into_Vset:
  assumes "M(a)"
  shows "\<exists>i[M]. \<exists>V[M]. ordinal(M,i) \<and> is_Vfrom(M,0,i,V) \<and> a\<in>V"
proof -
  let ?i="succ(rank(a))"
  from assms
  have "a\<in>{x\<in>Vfrom(0,?i). M(x)}" (is "a\<in>?V")
    using Vset_Ord_rank_iff by simp
  moreover from assms
  have "M(?i)"
    using rank_closed by simp
  moreover 
  note \<open>M(a)\<close>
  moreover from calculation
  have "M(?V)"
    using Vfrom_closed by simp
  moreover from calculation
  have "ordinal(M,?i) \<and> is_Vfrom(M, 0, ?i, ?V) \<and> a \<in> ?V"
    using Ord_rank Vfrom_abs by simp 
  ultimately
  show ?thesis by blast
qed

*)
end (* context M_eclose_pow *)

end