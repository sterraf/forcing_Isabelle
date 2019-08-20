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
definition
  HVfrom :: "[i,i,i] \<Rightarrow> i" where
  "HVfrom(A,x,f) \<equiv> A \<union> (\<Union>y\<in>x. Pow(f`y))"

definition
  MHVfrom :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> i" where
  "MHVfrom(M,A,x,f) \<equiv> A \<union> (\<Union>y\<in>x. {a\<in>Pow(f`y). M(a)})"

(* z = Pow(f`y) *)
definition
  is_powapply :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_powapply(M,f,y,z) \<equiv> \<exists>fy[M]. fun_apply(M,f,y,fy) \<and> powerset(M,fy,z)"

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

definition
  least :: "[i\<Rightarrow>o,i\<Rightarrow>o,i] \<Rightarrow> o" where
  "least(M,Q,i) \<equiv> ordinal(M,i) \<and> (
         (empty(M,i) \<and> (\<forall>b[M]. ordinal(M,b) \<longrightarrow> \<not>Q(b)))
       \<or> (Q(i) \<and> (\<forall>b[M]. ordinal(M,b) \<and> b\<in>i\<longrightarrow> \<not>Q(b))))"

definition
  least_fm :: "[i,i] \<Rightarrow> i" where
  "least_fm(q,i) \<equiv> And(ordinal_fm(i),
   Or(And(empty_fm(i),Forall(Implies(ordinal_fm(0),Neg(q)))), 
      And(Exists(And(q,Equal(0,succ(i)))),
          Forall(Implies(And(ordinal_fm(0),Member(0,succ(i))),Neg(q))))))"

lemma least_fm_type[TC] :"i \<in> nat \<Longrightarrow> q\<in>formula \<Longrightarrow> least_fm(q,i) \<in> formula"
  unfolding least_fm_def
  by simp

(* Refactorize Formula and Relative to include the following three lemmas *)
lemma sats_subset_fm':
   "\<lbrakk> x\<in> nat; y \<in> nat;env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, subset_fm(x,y), env) \<longleftrightarrow> subset(##A,nth(x,env),nth(y,env))"
  unfolding subset_fm_def subset_def
  by (simp)

lemma sats_transset_fm':
   "\<lbrakk>env \<in> list(A); x\<in>nat\<rbrakk>
    \<Longrightarrow> sats(A, transset_fm(x), env) \<longleftrightarrow> transitive_set(##A,nth(x,env))"
  unfolding transset_fm_def transitive_set_def 
  by (simp add:sats_subset_fm')

lemma sats_ordinal_fm':
   "\<lbrakk>x\<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, ordinal_fm(x), env) \<longleftrightarrow> ordinal(##A,nth(x,env))"
  unfolding ordinal_fm_def ordinal_def
  by (simp add:sats_subset_fm' sats_transset_fm')

lemmas basic_fm_simps = sats_subset_fm' sats_transset_fm' sats_ordinal_fm'

lemma sats_least_fm :
  assumes p_iff_sats: 
    "\<And>a. a \<in> A \<Longrightarrow> P(a) \<longleftrightarrow> sats(A, p, Cons(a, env))"
  shows
    "\<lbrakk>y \<in> nat; env \<in> list(A) ; 0\<in>A\<rbrakk>
    \<Longrightarrow> sats(A, least_fm(p,y), env) \<longleftrightarrow>
        least(##A, P, nth(y,env))"
  using nth_closed p_iff_sats unfolding least_def least_fm_def
  by (simp add:basic_fm_simps)

lemma least_iff_sats:
  assumes is_Q_iff_sats: 
      "\<And>a. a \<in> A \<Longrightarrow> is_Q(a) \<longleftrightarrow> sats(A, q, Cons(a,env))"
  shows 
  "\<lbrakk>nth(j,env) = y; j \<in> nat; env \<in> list(A); 0\<in>A\<rbrakk>
   \<Longrightarrow> least(##A, is_Q, y) \<longleftrightarrow> sats(A, least_fm(q,j), env)"
  using sats_least_fm [OF is_Q_iff_sats, of j , symmetric]
  by simp

lemma least_conj: "a\<in>M \<Longrightarrow> least(##M, \<lambda>x. x\<in>M \<and> Q(x),a) \<longleftrightarrow> least(##M,Q,a)"
  unfolding least_def by simp

(* Better to have this in M_basic or similar *)
lemma (in forcing_data) unique_least: "a\<in>M \<Longrightarrow> b\<in>M \<Longrightarrow> least(##M,Q,a) \<Longrightarrow> least(##M,Q,b) \<Longrightarrow> a=b"
  unfolding least_def
  by (auto, erule_tac i=a and j=b in Ord_linear_lt; (drule ltD | simp); auto intro:Ord_in_Ord)

context M_trivial
begin

lemma least_abs: 
  assumes "\<And>x. Q(x) \<Longrightarrow> M(x)" "M(a)" 
  shows "least(M,Q,a) \<longleftrightarrow> a = (\<mu> x. Q(x))"
  unfolding least_def
proof (cases "\<forall>b[M]. Ord(b) \<longrightarrow> \<not> Q(b)"; intro iffI; simp add:assms)
  case True
  with \<open>\<And>x. Q(x) \<Longrightarrow> M(x)\<close>
  have "\<not> (\<exists>i. Ord(i) \<and> Q(i)) " by blast
  then
  show "0 =(\<mu> x. Q(x))" using Least_0 by simp
  then
  show "ordinal(M, \<mu> x. Q(x)) \<and> (empty(M, Least(Q)) \<or> Q(Least(Q)))"
    by simp 
next
  assume "\<exists>b[M]. Ord(b) \<and> Q(b)"
  then 
  obtain i where "M(i)" "Ord(i)" "Q(i)" by blast
  assume "a = (\<mu> x. Q(x))"
  moreover
  note \<open>M(a)\<close>
  moreover from  \<open>Q(i)\<close> \<open>Ord(i)\<close>
  have "Q(\<mu> x. Q(x))" (is ?G)
    by (blast intro:LeastI)
  moreover
  have "(\<forall>b[M]. Ord(b) \<and> b \<in> (\<mu> x. Q(x)) \<longrightarrow> \<not> Q(b))" (is "?H")
    using less_LeastE[of Q _ False]
    by (auto, drule_tac ltI, simp, blast)
  ultimately
  show "ordinal(M, \<mu> x. Q(x)) \<and> (empty(M, \<mu> x. Q(x)) \<and> (\<forall>b[M]. Ord(b) \<longrightarrow> \<not> Q(b)) \<or> ?G \<and> ?H)"
    by simp
next
  assume 1:"\<exists>b[M]. Ord(b) \<and> Q(b)"
  then 
  obtain i where "M(i)" "Ord(i)" "Q(i)" by blast
  assume "Ord(a) \<and> (a = 0 \<and> (\<forall>b[M]. Ord(b) \<longrightarrow> \<not> Q(b)) \<or> Q(a) \<and> (\<forall>b[M]. Ord(b) \<and> b \<in> a \<longrightarrow> \<not> Q(b)))"
  with 1
  have "Ord(a)" "Q(a)" "\<forall>b[M]. Ord(b) \<and> b \<in> a \<longrightarrow> \<not> Q(b)"
    by blast+
  moreover from this and \<open>\<And>x. Q(x) \<Longrightarrow> M(x)\<close>
  have "Ord(b) \<Longrightarrow> b \<in> a \<Longrightarrow> \<not> Q(b)" for b
    by blast
  moreover from this and \<open>Ord(a)\<close>
  have "b < a \<Longrightarrow> \<not> Q(b)" for b
    unfolding lt_def using Ord_in_Ord by blast
  ultimately
  show "a = (\<mu> x. Q(x))"
    using Least_equality by simp
qed

lemma Least_closed:
  assumes "\<And>x. Q(x) \<Longrightarrow> M(x)"
  shows "M(\<mu> x. Q(x))"
  using assms LeastI[of Q] Least_0 by (cases "(\<exists>i. Ord(i) \<and> Q(i))", auto)

end (* context M_trivial *)

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
    "f\<in>nat" "y\<in>nat" "z\<in>nat" "env\<in>list(A)"
  shows
    "is_powapply(##A,nth(f, env),nth(y, env),nth(z, env))
    \<longleftrightarrow> sats(A,?ipa_fm(f,y,z),env)"
    and
    "?ipa_fm(f,y,z) \<in> formula"
  unfolding is_powapply_def is_Collect_def powerset_def subset_def
   by (insert assms ; (rule sep_rules  | simp))+

schematic_goal is_powapply_iff_sats:
  assumes
    "nth(f,env) = ff" "nth(y,env) = yy" "nth(z,env) = zz"
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
    "a\<in>nat" "x\<in>nat" "f\<in>nat" "h\<in>nat" "env\<in>list(A)" "A\<noteq>0"
  shows
    "is_HVfrom(##A,nth(a, env),nth(x, env),nth(f, env),nth(h, env))
    \<longleftrightarrow> sats(A,?ihvf_fm(a,x,f,h),env)"
    and
    "?ihvf_fm(a,x,f,h) \<in> formula"
  unfolding is_HVfrom_def
   by (insert assms; (rule sep_rules is_powapply_iff_sats Replace_iff_sats trivial_fm | simp))+

schematic_goal is_HVfrom_iff_sats:
  assumes
    "nth(a,env) = aa" "nth(x,env) = xx" "nth(f,env) = ff" "nth(h,env) = hh"
    "a\<in>nat" "x\<in>nat" "f\<in>nat" "h\<in>nat" "env\<in>list(A)" "A\<noteq>0"
  shows
       "is_HVfrom(##A,aa,xx,ff,hh) \<longleftrightarrow> sats(A, ?ihvf_fm(a,x,f,h), env)"
  unfolding \<open>nth(a,env) = aa\<close>[symmetric] \<open>nth(x,env) = xx\<close>[symmetric]
    \<open>nth(f,env) = ff\<close>[symmetric] \<open>nth(h,env) = hh\<close>[symmetric]
  by (rule sats_is_HVfrom_fm_auto(1); simp add:assms)

(* Next two are not needed *)
schematic_goal sats_is_Vfrom_fm_auto:
  assumes
    "a\<in>nat" "i\<in>nat" "v\<in>nat" "env\<in>list(A)" "A\<noteq>0"
    "i < length(env)" "v < length(env)"
  shows
    "is_Vfrom(##A,nth(a, env),nth(i, env),nth(v, env))
    \<longleftrightarrow> sats(A,?ivf_fm(a,i,v),env)"
    and
    "?ivf_fm(a,i,v) \<in> formula"
  unfolding is_Vfrom_def
  by (insert assms; (rule sep_rules is_HVfrom_iff_sats is_transrec_iff_sats | simp))+

schematic_goal is_Vfrom_iff_sats:
  assumes
    "nth(a,env) = aa" "nth(i,env) = ii" "nth(v,env) = vv"
    "a\<in>nat" "i\<in>nat" "v\<in>nat" "env\<in>list(A)" "A\<noteq>0"
    "i < length(env)" "v < length(env)"
  shows
    "is_Vfrom(##A,aa,ii,vv) \<longleftrightarrow> sats(A, ?ivf_fm(a,i,v), env)"
  unfolding \<open>nth(a,env) = aa\<close>[symmetric] \<open>nth(i,env) = ii\<close>[symmetric]
    \<open>nth(v,env) = vv\<close>[symmetric]
  by (rule sats_is_Vfrom_fm_auto(1); simp add:assms)

schematic_goal sats_is_Vset_fm_auto:
  assumes
    "i\<in>nat" "v\<in>nat" "env\<in>list(A)" "A\<noteq>0"
    "i < length(env)" "v < length(env)"
  shows
    "is_Vset(##A,nth(i, env),nth(v, env))
    \<longleftrightarrow> sats(A,?ivs_fm(i,v),env)"
    and
    "?ivs_fm(i,v) \<in> formula"
  unfolding is_Vset_def is_Vfrom_def
  by (insert assms; (rule sep_rules is_HVfrom_iff_sats is_transrec_iff_sats | simp))+

schematic_goal is_Vset_iff_sats:
  assumes
    "nth(i,env) = ii" "nth(v,env) = vv"
    "i\<in>nat" "v\<in>nat" "env\<in>list(A)" "A\<noteq>0"
    "i < length(env)" "v < length(env)"
  shows
    "is_Vset(##A,ii,vv) \<longleftrightarrow> sats(A, ?ivs_fm(i,v), env)"
  unfolding \<open>nth(i,env) = ii\<close>[symmetric] \<open>nth(v,env) = vv\<close>[symmetric]
  by (rule sats_is_Vset_fm_auto(1); simp add:assms)

section\<open>Absoluteness results\<close>

context M_basic
begin

lemma is_powapply_abs: "\<lbrakk>M(f); M(y); M(z) \<rbrakk> \<Longrightarrow> is_powapply(M,f,y,z) \<longleftrightarrow> z = {x\<in>Pow(f`y). M(x)}"
  unfolding is_powapply_def by simp

lemma "\<lbrakk>M(A); M(x); M(f); M(h) \<rbrakk> \<Longrightarrow> 
      is_HVfrom(M,A,x,f,h) \<longleftrightarrow> 
      (\<exists>R[M]. h = A \<union> \<Union>R \<and> is_Replace(M, x,\<lambda>x y. y = {x \<in> Pow(f ` x) . M(x)}, R))"
  using is_powapply_abs unfolding is_HVfrom_def by auto

lemma "relation2(M,is_HVfrom(M,A),MHVfrom(M,A))"
  unfolding is_HVfrom_def MHVfrom_def relation2_def
  oops
end (* context M_basic *)

context M_trancl
begin

lemma Vfrom_abs: "\<lbrakk> M(A); M(i); M(V) \<rbrakk> \<Longrightarrow> is_Vfrom(M,A,i,V) \<longleftrightarrow> V = {x\<in>Vfrom(A,i). M(x)}"
  sorry

lemma Vfrom_closed: "\<lbrakk> M(A); M(i) \<rbrakk> \<Longrightarrow> M({x\<in>Vfrom(A,i). M(x)})"
  sorry

lemma rank_closed: "M(a) \<Longrightarrow> M(rank(a))"
  sorry

lemma Vset_abs: "\<lbrakk> M(i); M(V) \<rbrakk> \<Longrightarrow> is_Vset(M,i,V) \<longleftrightarrow> V = {x\<in>Vset(i). M(x)}"
  using Vfrom_abs unfolding is_Vset_def by simp

lemma Vset_closed: "\<lbrakk> M(i) \<rbrakk> \<Longrightarrow> M({x\<in>Vset(i). M(x)})"
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