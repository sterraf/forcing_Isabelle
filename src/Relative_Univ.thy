theory Relative_Univ
  imports
    Names Rank

begin

lemma rank_eq_wfrank: "rank(a) = wfrank(Memrel(eclose({a})),a)"
  unfolding rank_def transrec_def wfrank_def wfrec_def sorry

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

(*
(*   "is_powapply(M,f,y,z) \<equiv> M(z) \<and> (\<exists>fy[M]. fun_apply(M,f,y,fy) \<and> powerset(M,fy,z))" *)

definition
  powerset_fm :: "[i,i] \<Rightarrow> i" where
  "powerset_fm(y,z) \<equiv> Forall(Iff(Member(0,succ(z)),subset_fm(0,succ(y))))"

lemma sats_powerset_fm [simp]:
  assumes
    "y\<in>nat" "z\<in>nat" "env\<in>list(A)"
  shows
    "powerset(##A,nth(y, env),nth(z, env))
    \<longleftrightarrow> sats(A,powerset_fm(y,z),env)"
  unfolding powerset_fm_def powerset_def 
  using assms sats_subset_fm' by simp

definition
  is_powapply_fm :: "[i,i,i] \<Rightarrow> i" where
  "is_powapply_fm(f,y,z) \<equiv> Exists(And(fun_apply_fm(1,2,0),powerset_fm(0,3)))"

lemma sats_is_powapply_fm_auto:
  assumes
    "f\<in>nat" "y\<in>nat" "z\<in>nat" "env\<in>list(A)" "z<length(env)"
  shows
    "is_powapply(##A,nth(f, env),nth(y, env),nth(z, env))
    \<longleftrightarrow> sats(A,is_powapply_fm(f,y,z),env)"
  using assms
  unfolding is_powapply_def is_powapply_fm_def
  apply simp
*)

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

context M_basic
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

lemma 
  assumes "M(A)"
  shows "relation2(M,is_HVfrom(M,A),HVfrom(M,A))"
proof -
  have 1:"M(f) \<Longrightarrow> M(C) \<Longrightarrow> univalent(M,C,is_powapply(M,f))"  for f C
    unfolding univalent_def is_powapply_def by simp
  show ?thesis
    unfolding is_HVfrom_def HVfrom_def relation2_def
    using assms Replace_is_powapply is_powapply_abs
    sorry
qed

end (* context M_basic *)

context M_trancl
begin

lemma Vfrom_abs: "\<lbrakk> M(A); M(i); M(V); Ord(i) \<rbrakk> \<Longrightarrow> is_Vfrom(M,A,i,V) \<longleftrightarrow> V = {x\<in>Vfrom(A,i). M(x)}"
  sorry

lemma Vfrom_closed: "\<lbrakk> M(A); M(i); Ord(i) \<rbrakk> \<Longrightarrow> M({x\<in>Vfrom(A,i). M(x)})"
  sorry

lemma rank_closed: "M(a) \<Longrightarrow> M(rank(a))"
  sorry

lemma Vset_abs: "\<lbrakk> M(i); M(V); Ord(i) \<rbrakk> \<Longrightarrow> is_Vset(M,i,V) \<longleftrightarrow> V = {x\<in>Vset(i). M(x)}"
  using Vfrom_abs unfolding is_Vset_def by simp

lemma Vset_closed: "\<lbrakk> M(i); Ord(i) \<rbrakk> \<Longrightarrow> M({x\<in>Vset(i). M(x)})"
  using Vfrom_closed unfolding is_Vset_def by simp

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
end (* context M_trancl *)

context M_wfrank
begin

end (* M_wfrank *)

end