section\<open>Transitive set models of ZF\<close>
text\<open>This theory defines the locale \<^term>\<open>M_ZF_trans\<close> for
transitive models of ZF, and the associated \<^term>\<open>forcing_data\<close>
 that adds a forcing notion\<close>
theory Forcing_Data
  imports  
    Forcing_Notions 
    Interface
    Arities
    Renaming_Auto
begin

locale M_ctm = M_ZF_trans +
  fixes enum
  assumes M_countable:      "enum\<in>bij(nat,M)"
begin

subsection\<open>\<^term>\<open>Collects\<close> in $M$\<close>
lemma Collect_in_M_0p :
  assumes
    Qfm : "Q_fm \<in> formula" and
    Qarty : "arity(Q_fm) = 1" and
    Qsats : "\<And>x. x\<in>M \<Longrightarrow> sats(M,Q_fm,[x]) \<longleftrightarrow> is_Q(##M,x)" and
    Qabs  : "\<And>x. x\<in>M \<Longrightarrow> is_Q(##M,x) \<longleftrightarrow> Q(x)" and
    "A\<in>M"
  shows
    "Collect(A,Q)\<in>M" 
proof -
  have "z\<in>A \<Longrightarrow> z\<in>M" for z
    using \<open>A\<in>M\<close> transitivity by simp
  then
  have 1:"Collect(A,is_Q(##M)) = Collect(A,Q)" 
    using Qabs Collect_cong[of "A" "A" "is_Q(##M)" "Q"] by simp
  have "separation(##M,is_Q(##M))"
    using separation_ax Qsats Qarty Qfm
      separation_cong[of "##M" "\<lambda>y. sats(M,Q_fm,[y])" "is_Q(##M)"]
    by simp
  then 
  have "Collect(A,is_Q(##M))\<in>M"
    using separation_closed \<open>A\<in>M\<close> by simp 
  then
  show ?thesis using 1 by simp
qed

lemma Collect_in_M_2p :
  assumes
    Qfm : "Q_fm \<in> formula" and
    Qarty : "arity(Q_fm) = 3" and
    params_M : "y\<in>M" "z\<in>M" and
    Qsats : "\<And>x. x\<in>M \<Longrightarrow> sats(M,Q_fm,[x,y,z]) \<longleftrightarrow> is_Q(##M,x,y,z)" and
    Qabs  : "\<And>x. x\<in>M \<Longrightarrow> is_Q(##M,x,y,z) \<longleftrightarrow> Q(x,y,z)" and
    "A\<in>M"
  shows
    "Collect(A,\<lambda>x. Q(x,y,z))\<in>M" 
proof -
  have "z\<in>A \<Longrightarrow> z\<in>M" for z
    using \<open>A\<in>M\<close> transitivity by simp
  then
  have 1:"Collect(A,\<lambda>x. is_Q(##M,x,y,z)) = Collect(A,\<lambda>x. Q(x,y,z))" 
    using Qabs Collect_cong[of "A" "A" "\<lambda>x. is_Q(##M,x,y,z)" "\<lambda>x. Q(x,y,z)"] by simp
  have "separation(##M,\<lambda>x. is_Q(##M,x,y,z))"
    using separation_ax Qsats Qarty Qfm params_M
      separation_cong[of "##M" "\<lambda>x. sats(M,Q_fm,[x,y,z])" "\<lambda>x. is_Q(##M,x,y,z)"]
    by simp
  then 
  have "Collect(A,\<lambda>x. is_Q(##M,x,y,z))\<in>M"
    using separation_closed \<open>A\<in>M\<close> by simp 
  then
  show ?thesis using 1 by simp
qed

lemma Collect_in_M_4p :
  assumes
    Qfm : "Q_fm \<in> formula" and
    Qarty : "arity(Q_fm) = 5" and
    params_M : "a1\<in>M" "a2\<in>M" "a3\<in>M" "a4\<in>M" and
    Qsats : "\<And>x. x\<in>M \<Longrightarrow> sats(M,Q_fm,[x,a1,a2,a3,a4]) \<longleftrightarrow> is_Q(##M,x,a1,a2,a3,a4)" and
    Qabs  : "\<And>x. x\<in>M \<Longrightarrow> is_Q(##M,x,a1,a2,a3,a4) \<longleftrightarrow> Q(x,a1,a2,a3,a4)" and
    "A\<in>M"
  shows
    "Collect(A,\<lambda>x. Q(x,a1,a2,a3,a4))\<in>M" 
proof -
  have "z\<in>A \<Longrightarrow> z\<in>M" for z
    using \<open>A\<in>M\<close> transitivity by simp
  then
  have 1:"Collect(A,\<lambda>x. is_Q(##M,x,a1,a2,a3,a4)) = Collect(A,\<lambda>x. Q(x,a1,a2,a3,a4))" 
    using Qabs Collect_cong[of "A" "A" "\<lambda>x. is_Q(##M,x,a1,a2,a3,a4)" "\<lambda>x. Q(x,a1,a2,a3,a4)"] 
    by simp
  have "separation(##M,\<lambda>x. is_Q(##M,x,a1,a2,a3,a4))"
    using separation_ax Qsats Qarty Qfm params_M
      separation_cong[of "##M" "\<lambda>x. sats(M,Q_fm,[x,a1,a2,a3,a4])" 
        "\<lambda>x. is_Q(##M,x,a1,a2,a3,a4)"]
    by simp
  then 
  have "Collect(A,\<lambda>x. is_Q(##M,x,a1,a2,a3,a4))\<in>M"
    using separation_closed \<open>A\<in>M\<close> by simp 
  then
  show ?thesis using 1 by simp
qed

(* FIXME: rename: Replace_in_M *)
lemma Replacement_in_M :
  assumes
    f_fm:  "\<phi> \<in> formula" and
    f_ar:  "arity(\<phi>)\<le> 2 #+ length(env)" and
    fsats: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>M \<Longrightarrow> M,[x,y]@env \<Turnstile> \<phi> \<longleftrightarrow> y = f(x)" and
    fclosed: "\<And>x. x\<in>A \<Longrightarrow> f(x) \<in> M"  and
    "A\<in>M" "env\<in>list(M)" 
  shows "{f(x) . x\<in>A}\<in>M"
proof -
  let ?\<phi>' = "And(\<phi>,Member(0,length(env)#+2))"
  have "arity(?\<phi>') \<le> 2 #+ length(env@[A])"
    using assms Un_le
      le_trans[of "arity(\<phi>)" "succ(succ(length(env)))" "succ(succ(succ(length(env))))"]
    by force
  moreover from assms
  have "?\<phi>'\<in>formula" "nth(length(env), env @ [A]) = A" 
    using assms nth_append by auto
  moreover from calculation
  have "\<And> x y. x \<in> M \<Longrightarrow> y\<in>M \<Longrightarrow> M,[x,y]@env@[A]\<Turnstile>?\<phi>' \<longleftrightarrow> y=f(x) \<and>x\<in>A"
    using arity_sats_iff[of _ "[A]" _ "[_,_]@env"] assms
    by auto
  moreover from calculation
  have "strong_replacement(##M, \<lambda>x y. M,[x,y]@env@[A] \<Turnstile> ?\<phi>')"
    using replacement_ax \<open>env\<in>list(M)\<close> assms by simp
  ultimately 
  have 4:"strong_replacement(##M, \<lambda>x y. y = f(x) \<and> x\<in>A)"
    using 
      strong_replacement_cong[of "##M" "\<lambda>x y. M,[x,y]@env@[A]\<Turnstile>?\<phi>'" "\<lambda>x y. y = f(x) \<and> x\<in>A"]
    by simp
  then
  have "{y . x\<in>A , y = f(x)} \<in> M" 
    using \<open>A\<in>M\<close> strong_replacement_closed[OF 4,of A] fclosed by simp
  moreover
  have "{f(x). x\<in>A} = { y . x\<in>A , y = f(x)}"
    by auto
  ultimately show ?thesis by simp
qed

lemma Replacement_alt_in_M :
  assumes
    f_fm:  "\<phi> \<in> formula" and
    f_ar:  "arity(\<phi>)\<le> 2 #+ length(env)" and
    fsats: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>M \<Longrightarrow> M,[x,y]@env \<Turnstile> \<phi> \<longleftrightarrow> is_f(x,y)" and
    fabs:  "\<And>x y. x\<in>A \<Longrightarrow> y\<in>M \<Longrightarrow> is_f(x,y) \<longleftrightarrow> y = f(x)" and
    fclosed: "\<And>x. x\<in>A \<Longrightarrow> f(x) \<in> M"  and
    "A\<in>M" "env\<in>list(M)"
  shows "{f(x) . x\<in>A}\<in>M"
  using assms Replacement_in_M by auto

definition \<rho>_repl :: "i\<Rightarrow>i" where
  "\<rho>_repl(l) \<equiv> rsum({\<langle>0, 1\<rangle>, \<langle>1, 0\<rangle>}, id(l), 2, 3, l)"

lemma f_type : "{\<langle>0, 1\<rangle>, \<langle>1, 0\<rangle>} \<in> 2 \<rightarrow> 3"
  using Pi_iff unfolding function_def by auto

lemma ren_type :
  assumes "l\<in>nat"
  shows "\<rho>_repl(l) : 2#+l \<rightarrow> 3#+l"
  using sum_type[of 2 3 l l "{\<langle>0, 1\<rangle>, \<langle>1, 0\<rangle>}" "id(l)"] f_type assms id_type
  unfolding \<rho>_repl_def by auto

lemma ren_action :
  assumes
    "env\<in>list(M)" "x\<in>M" "y\<in>M" "z\<in>M"
  shows "\<forall> i . i < 2#+length(env) \<longrightarrow>
          nth(i,[x,z]@env) = nth(\<rho>_repl(length(env))`i,[z,x,y]@env)"
proof -
  let ?f="{\<langle>0, 1\<rangle>, \<langle>1, 0\<rangle>}"
  have 1:"(\<And>j. j < length(env) \<Longrightarrow> nth(j, env) = nth(id(length(env)) ` j, env))"
    using assms ltD by simp
  have 2:"nth(j, [x,z]) = nth(?f ` j, [z,x,y])" if "j<2" for j
  proof -
    consider "j=0" | "j=1" using  ltD[OF \<open>j<2\<close>] by auto
    then show ?thesis
    proof(cases)
      case 1
      then show ?thesis using apply_equality f_type by simp
    next
      case 2
      then show ?thesis using apply_equality f_type by simp
    qed
  qed
  show ?thesis
    using sum_action[OF _ _ _ _ f_type id_type _ _ _ _ _ _ _ 2 1,simplified] assms
    unfolding \<rho>_repl_def by simp
qed

(* FIXME: this should be to Lambda_in_M and remove the next. *)
lemma Fun_in_M :
  assumes
    f_fm:  "\<phi> \<in> formula" and
    f_ar:  "arity(\<phi>)\<le> 2 #+ length(env)" and
    fsats: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>M \<Longrightarrow> M,[x,y]@env \<Turnstile> \<phi> \<longleftrightarrow> is_f(x,y)" and
    fabs:  "\<And>x y. x\<in>A \<Longrightarrow> y\<in>M \<Longrightarrow> is_f(x,y) \<longleftrightarrow> y = f(x)" and
    fclosed: "\<And>x. x\<in>A \<Longrightarrow> f(x) \<in> M"  and
    "A\<in>M" "env\<in>list(M)" 
  shows "{<x,f(x)> . x\<in>A}\<in>M"
proof -
  let ?ren="\<rho>_repl(length(env))"
  let ?j="2#+length(env)"
  let ?k="3#+length(env)"
  let ?\<psi>="ren(\<phi>)`?j`?k`?ren"
  let ?\<phi>'="Exists(And(pair_fm(1,0,2),?\<psi>))"
  let ?p="\<lambda>x y. \<exists>z\<in>M. pair(##M,x,z,y) \<and> is_f(x,z)"
  have "?\<phi>'\<in>formula" "?\<psi>\<in>formula"
    using \<open>env\<in>_\<close> length_type f_fm ren_type ren_tc[of \<phi> "2#+length(env)" "3#+length(env)" ?ren]
    by simp_all
  moreover from this
  have "arity(?\<psi>)\<le>3#+(length(env))" "arity(?\<psi>)\<in>nat"
    using assms arity_ren[OF f_fm _ _ ren_type,of "length(env)"] by simp_all
  then
  have "arity(?\<phi>') \<le> 2#+(length(env))"
    using arity_pair_fm Un_le pred_Un_distrib assms pred_le
    by simp
  moreover from this calculation
  have "x\<in>A \<Longrightarrow> y\<in>M \<Longrightarrow> M,[x,y]@env \<Turnstile> ?\<phi>' \<longleftrightarrow> ?p(x,y)" for x y
    using \<open>env\<in>_\<close> length_type[OF \<open>env\<in>_\<close>] assms transitivity[OF _ \<open>A\<in>M\<close>]
      sats_iff_sats_ren[OF f_fm _ _ _ _ ren_type f_ar ren_action[rule_format,of _ x y],of _ M ]
    by auto
  moreover
  have "x\<in>A \<Longrightarrow> y\<in>M \<Longrightarrow> ?p(x,y) \<longleftrightarrow> y = <x,f(x)>" for x y
    using assms transitivity[OF _ \<open>A\<in>_\<close>] fclosed
    by simp
  moreover
  have "\<And> x . x\<in>A \<Longrightarrow> <x,f(x)> \<in> M"
    using transitivity[OF _ \<open>A\<in>M\<close>] pair_in_M_iff fclosed by simp
  ultimately
  show ?thesis
    using Replacement_in_M \<open>A\<in>M\<close> \<open>env\<in>_\<close>
    by simp
qed

lemma Lambda_in_M :
  assumes
    f_fm:  "\<phi> \<in> formula" and
    f_ar:  "arity(\<phi>)\<le> 2 #+ length(env)" and
    fsats: "\<And>x y. x\<in>A \<Longrightarrow> y\<in>M \<Longrightarrow> M,[x,y]@env \<Turnstile> \<phi> \<longleftrightarrow> is_f(x,y)" and
    fabs:  "\<And>x y. x\<in>A \<Longrightarrow> y\<in>M \<Longrightarrow> is_f(x,y) \<longleftrightarrow> y = f(x)" and
    fclosed: "\<And>x. x\<in>A \<Longrightarrow> f(x) \<in> M"  and
    "A\<in>M" "env\<in>list(M)" 
  shows "(\<lambda>x\<in>A . f(x)) \<in>M"
  unfolding lam_def using assms Fun_in_M by simp

lemma Repl_in_M :
  assumes
    f_fm:  "f_fm \<in> formula" and
    f_ar:  "arity(f_fm)\<le> 2 #+ length(env)" and
    fsats: "\<And>x y. x\<in>M \<Longrightarrow> y\<in>M \<Longrightarrow> sats(M,f_fm,[x,y]@env) \<longleftrightarrow> is_f(x,y)" and
    fabs:  "\<And>x y. x\<in>M \<Longrightarrow> y\<in>M \<Longrightarrow> is_f(x,y) \<longleftrightarrow> y = f(x)" and
    fclosed: "\<And>x. x\<in>A \<Longrightarrow> f(x) \<in> M"  and
    "A\<in>M" "env\<in>list(M)"
  shows "{f(x). x\<in>A}\<in>M"
  using assms Replacement_in_M transitivity[OF _ \<open>A\<in>M\<close>] by auto

end (* M_ctm *)

subsection\<open>A forcing locale and generic filters\<close>
locale forcing_data = forcing_notion + M_ctm +
  assumes P_in_M:           "P \<in> M"
    and leq_in_M:         "leq \<in> M"

begin

(* P \<subseteq> M *)
lemma P_sub_M : "P\<subseteq>M"
  using transitivity[OF _ P_in_M] by auto

definition
  M_generic :: "i\<Rightarrow>o" where
  "M_generic(G) \<equiv> filter(G) \<and> (\<forall>D\<in>M. D\<subseteq>P \<and> dense(D)\<longrightarrow>D\<inter>G\<noteq>0)"

lemma M_genericD [dest]: "M_generic(G) \<Longrightarrow> x\<in>G \<Longrightarrow> x\<in>P"
  unfolding M_generic_def by (blast dest:filterD)

lemma M_generic_leqD [dest]: "M_generic(G) \<Longrightarrow> p\<in>G \<Longrightarrow> q\<in>P \<Longrightarrow> p\<preceq>q \<Longrightarrow> q\<in>G"
  unfolding M_generic_def by (blast dest:filter_leqD)

lemma M_generic_compatD [dest]: "M_generic(G) \<Longrightarrow> p\<in>G \<Longrightarrow> r\<in>G \<Longrightarrow> \<exists>q\<in>G. q\<preceq>p \<and> q\<preceq>r"
  unfolding M_generic_def by (blast dest:low_bound_filter)

lemma M_generic_denseD [dest]: "M_generic(G) \<Longrightarrow> dense(D) \<Longrightarrow> D\<subseteq>P \<Longrightarrow> D\<in>M \<Longrightarrow> \<exists>q\<in>G. q\<in>D"
  unfolding M_generic_def by blast

lemma G_nonempty: "M_generic(G) \<Longrightarrow> G\<noteq>0"
proof -
  have "P\<subseteq>P" ..
  assume
    "M_generic(G)"
  with P_in_M P_dense \<open>P\<subseteq>P\<close> show
    "G \<noteq> 0"
    unfolding M_generic_def by auto
qed

lemma one_in_G : 
  assumes "M_generic(G)"
  shows  "one \<in> G" 
proof -
  from assms have "G\<subseteq>P" 
    unfolding M_generic_def and filter_def by simp
  from \<open>M_generic(G)\<close> have "increasing(G)" 
    unfolding M_generic_def and filter_def by simp
  with \<open>G\<subseteq>P\<close> and \<open>M_generic(G)\<close> 
  show ?thesis 
    using G_nonempty and one_in_P and one_max 
    unfolding increasing_def by blast
qed

lemma G_subset_M: "M_generic(G) \<Longrightarrow> G \<subseteq> M"
  using transitivity[OF _ P_in_M] by auto

declare iff_trans [trans]

lemma generic_filter_existence: 
  "p\<in>P \<Longrightarrow> \<exists>G. p\<in>G \<and> M_generic(G)"
proof -
  assume "p\<in>P"
  let ?D="\<lambda>n\<in>nat. (if (enum`n\<subseteq>P \<and> dense(enum`n))  then enum`n else P)"
  have "\<forall>n\<in>nat. ?D`n \<in> Pow(P)"
    by auto
  then 
  have "?D:nat\<rightarrow>Pow(P)"
    using lam_type by auto
  have Eq4: "\<forall>n\<in>nat. dense(?D`n)"
  proof(intro ballI)
    fix n
    assume "n\<in>nat"
    then
    have "dense(?D`n) \<longleftrightarrow> dense(if enum`n \<subseteq> P \<and> dense(enum`n) then enum`n else P)"
      by simp
    also 
    have "... \<longleftrightarrow>  (\<not>(enum`n \<subseteq> P \<and> dense(enum`n)) \<longrightarrow> dense(P)) "
      using split_if by simp
    finally
    show "dense(?D`n)"
      using P_dense \<open>n\<in>nat\<close> by auto
  qed
  from \<open>?D\<in>_\<close> and Eq4 
  interpret cg: countable_generic P leq one ?D 
    by (unfold_locales, auto)
  from \<open>p\<in>P\<close> 
  obtain G where Eq6: "p\<in>G \<and> filter(G) \<and> (\<forall>n\<in>nat.(?D`n)\<inter>G\<noteq>0)"
    using cg.countable_rasiowa_sikorski[where M="\<lambda>_. M"]  P_sub_M
      M_countable[THEN bij_is_fun] M_countable[THEN bij_is_surj, THEN surj_range] 
    unfolding cg.D_generic_def by blast
  then 
  have Eq7: "(\<forall>D\<in>M. D\<subseteq>P \<and> dense(D)\<longrightarrow>D\<inter>G\<noteq>0)"
  proof (intro ballI impI)
    fix D
    assume "D\<in>M" and Eq9: "D \<subseteq> P \<and> dense(D) " 
    have "\<forall>y\<in>M. \<exists>x\<in>nat. enum`x= y"
      using M_countable and  bij_is_surj unfolding surj_def by (simp)
    with \<open>D\<in>M\<close> obtain n where Eq10: "n\<in>nat \<and> enum`n = D" 
      by auto
    with Eq9 and if_P
    have "?D`n = D" by (simp)
    with Eq6 and Eq10 
    show "D\<inter>G\<noteq>0" by auto
  qed
  with Eq6 
  show ?thesis unfolding M_generic_def by auto
qed

lemma one_in_M: "one \<in> M"
  by (insert one_in_P P_in_M, simp add: transitivity)

end (* forcing_data *)

(* Compatibility lemmas *)
lemma (in M_trivial) compat_in_abs :
  assumes
    "M(A)" "M(r)" "M(p)" "M(q)" 
  shows
    "is_compat_in(M,A,r,p,q) \<longleftrightarrow> compat_in(A,r,p,q)"
  using assms unfolding is_compat_in_def compat_in_def by simp

context forcing_data begin

definition
  compat_in_fm :: "[i,i,i,i] \<Rightarrow> i" where
  "compat_in_fm(A,r,p,q) \<equiv> 
    Exists(And(Member(0,succ(A)),Exists(And(pair_fm(1,p#+2,0),
                                        And(Member(0,r#+2),
                                 Exists(And(pair_fm(2,q#+3,0),Member(0,r#+3))))))))" 

lemma compat_in_fm_type[TC] : 
  "\<lbrakk> A\<in>nat;r\<in>nat;p\<in>nat;q\<in>nat\<rbrakk> \<Longrightarrow> compat_in_fm(A,r,p,q)\<in>formula" 
  unfolding compat_in_fm_def by simp

lemma sats_compat_in_fm:
  assumes
    "A\<in>nat" "r\<in>nat"  "p\<in>nat" "q\<in>nat" "env\<in>list(M)"  
  shows
    "sats(M,compat_in_fm(A,r,p,q),env) \<longleftrightarrow> 
            is_compat_in(##M,nth(A, env),nth(r, env),nth(p, env),nth(q, env))"
  unfolding compat_in_fm_def is_compat_in_def using assms by simp

end (* forcing_data *)

end
