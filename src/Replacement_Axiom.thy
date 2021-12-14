section\<open>The Axiom of Replacement in $M[G]$\<close>
theory Replacement_Axiom
  imports
    Least Relative_Univ Separation_Axiom Renaming_Auto
begin

context G_generic
begin

definition rename_split_fm where 
  "rename_split_fm(\<phi>) \<equiv> (\<cdot>\<exists>(\<cdot>\<exists>(\<cdot>\<exists>(\<cdot>\<exists>(\<cdot>\<exists>(\<cdot>\<exists>\<cdot>\<cdot>snd(9) is 0\<cdot> \<and> \<cdot>\<cdot>fst(9) is 4\<cdot> \<and> \<cdot>\<cdot>1=11\<cdot> \<and>
    \<cdot>\<cdot>2=12\<cdot> \<and> \<cdot>\<cdot>3=13\<cdot> \<and> \<cdot>\<cdot>5=7\<cdot> \<and>
    (\<lambda>p. incr_bv(p)`6)^8(forces(\<phi>)) \<cdot>\<cdot>\<cdot>\<cdot>\<cdot>\<cdot>\<cdot>)\<cdot>)\<cdot>)\<cdot>)\<cdot>)\<cdot>)"

lemma rename_split_fm_type[TC]: "\<phi>\<in>formula \<Longrightarrow> rename_split_fm(\<phi>)\<in>formula"
  unfolding rename_split_fm_def by simp

schematic_goal arity_rename_split_fm: "\<phi>\<in>formula \<Longrightarrow> arity(rename_split_fm(\<phi>)) = ?m"
  using arity_forces[of \<phi>] forces_type unfolding rename_split_fm_def
  by (simp add:arity Un_assoc[symmetric] union_abs1)

lemma arity_rename_split_fm_le: 
  assumes "\<phi>\<in>formula"
  shows "arity(rename_split_fm(\<phi>)) \<le> 8 \<union> (arity(\<phi>) #+ 6)"
proof -
  from assms
  have arity_forces_6: "\<not> 1 < arity(\<phi>) \<Longrightarrow> 6 \<le> n \<Longrightarrow> arity(forces(\<phi>)) \<le> n" for n
    using le_trans lt_trans[of _ 5 n] not_lt_iff_le[of 1 "arity(\<phi>)"]
    by (auto intro!:le_trans[OF arity_forces])
  have pred1_arity_forces: "\<not> 1 < arity(\<phi>) \<Longrightarrow> Arith.pred^n(arity(forces(\<phi>))) \<le> 8" if "n\<in>nat" for n
    using that pred_le[of 7] le_succ[THEN [2] le_trans] arity_forces_6
    by (induct rule:nat_induct) auto
  have arity_forces_le_succ6: "Arith.pred^n(arity(forces(\<phi>))) \<le> succ(succ(succ(succ(succ(succ(arity(\<phi>)))))))"
    if "n\<in>nat" for n
    using that assms arity_forces[of \<phi>, THEN le_trans,
        OF _ le_succ, THEN le_trans, OF _ _ le_succ] le_trans[OF pred_le[OF _ le_succ]]
    by (induct rule:nat_induct) auto
  note trivial_arities = arity_forces_6
    arity_forces_le_succ6[of 1, simplified] arity_forces_le_succ6[of 2, simplified]
    arity_forces_le_succ6[of 3, simplified] arity_forces_le_succ6[of 4, simplified]
    arity_forces_le_succ6[of 5, simplified] arity_forces_le_succ6[of 6, simplified]
    pred1_arity_forces[of 1, simplified] pred1_arity_forces[of 2, simplified]
    pred1_arity_forces[of 3, simplified] pred1_arity_forces[of 4, simplified]
    pred1_arity_forces[of 5, simplified] pred1_arity_forces[of 6, simplified]
  show ?thesis
    using assms arity_forces[of \<phi>] arity_forces[of \<phi>, THEN le_trans, OF _ le_succ]
      arity_forces[of \<phi>, THEN le_trans, OF _ le_succ, THEN le_trans, OF _ _ le_succ]
    unfolding rename_split_fm_def
    by (simp add:arity Un_assoc[symmetric] union_abs1 arity_forces[of \<phi>] forces_type)
      (subst arity_incr_bv_lemma; auto simp: arity ord_simp_union forces_type trivial_arities)+
qed

bundle sharp_simps1 = snd_abs[simp] fst_abs[simp] fst_closed[simp del, simplified, simp]
    snd_closed[simp del, simplified, simp] M_inhabited[simplified, simp]
    pair_in_M_iff[simp del, simplified, simp]

lemma sats_forces_iff_sats_rename_split_fm:
  includes sharp_simps1
  assumes
    "[\<alpha>,m,p,P,leq,one,t,\<tau>] @ nenv \<in>list(M)" "V \<in> M"
    "\<phi>\<in>formula"
  shows
    "(M, [p, P, leq, one, t, \<tau>] @ nenv \<Turnstile> forces(\<phi>)) \<longleftrightarrow>
      M, [V, \<tau>, \<alpha>, \<langle>t,p\<rangle>, m, P, leq, one] @ nenv \<Turnstile> rename_split_fm(\<phi>)"
  using assms unfolding rename_split_fm_def
  by (simp add:sats_incr_bv_iff[where bvs="[_,_,_,_,_,_]", simplified])

definition body_ground_repl_fm where 
  "body_ground_repl_fm(\<phi>) \<equiv> (\<cdot>\<exists>(\<cdot>\<exists>\<cdot>is_Vset_fm(2, 0) \<and> \<cdot>\<cdot>1 \<in> 0\<cdot> \<and> rename_split_fm(\<phi>) \<cdot>\<cdot>\<cdot>)\<cdot>)"

lemma body_ground_repl_fm_type[TC]: "\<phi>\<in>formula \<Longrightarrow> body_ground_repl_fm(\<phi>)\<in>formula"
  unfolding body_ground_repl_fm_def by simp

arity_theorem for "is_powapply_fm"

lemma arity_body_ground_repl_fm_le: 
  notes le_trans[trans]
  assumes "\<phi>\<in>formula"
  shows "arity(body_ground_repl_fm(\<phi>)) \<le> 6 \<union> (arity(\<phi>) #+ 4)"
proof -
  from \<open>\<phi>\<in>formula\<close>
  have ineq: "n \<union> Arith.pred(Arith.pred(arity(rename_split_fm(\<phi>)))) 
    \<le> m \<union> Arith.pred(Arith.pred(8 \<union> (arity(\<phi>) #+6 )))" if "n \<le> m" "n\<in>nat" "m\<in>nat" for n m
  using that arity_rename_split_fm_le[of \<phi>, THEN [2] pred_mono, THEN [2] pred_mono,
      THEN [2] Un_mono[THEN subset_imp_le, OF _ le_imp_subset]] le_imp_subset 
    by auto
  moreover
  have "Arith.pred(Arith.pred(Arith.pred(4 \<union> 2 \<union> Arith.pred(Arith.pred(Arith.pred(
    Arith.pred(Arith.pred(Arith.pred(Arith.pred(Arith.pred(9 \<union> 1 \<union> 3 \<union> 2))))))))))) = 1"
    by (auto simp:pred_Un_distrib)
  ultimately
  have "Arith.pred(Arith.pred(Arith.pred(4 \<union> 2 \<union> Arith.pred(Arith.pred(Arith.pred(
    Arith.pred(Arith.pred(Arith.pred(Arith.pred(Arith.pred(9 \<union> 1 \<union> 3 \<union> 2))))))))))) \<union>
    Arith.pred(Arith.pred(arity(rename_split_fm(\<phi>)))) \<le>
    1 \<union> Arith.pred(Arith.pred(8 \<union> (arity(\<phi>) #+6 )))"
    by auto
  also from \<open>\<phi>\<in>formula\<close>
  have "1 \<union> Arith.pred(Arith.pred(8 \<union> (arity(\<phi>) #+6 ))) \<le> 6 \<union> (succ(succ(succ(succ(arity(\<phi>))))))"
    by (auto simp:pred_Un_distrib Un_assoc[symmetric] ord_simp_union)
  finally
  show ?thesis
    using \<open>\<phi>\<in>formula\<close> unfolding body_ground_repl_fm_def
    by (simp add:arity pred_Un_distrib, subst arity_transrec_fm[of "is_HVfrom_fm(8,2,1,0)" 3 1])
      (simp_all add: arity,
        subst arity_Replace_fm[of "is_powapply_fm(5, 0, 1)" 4 0], auto simp add:arity ord_simp_union)
qed

lemma sats_body_ground_repl_fm:
  includes sharp_simps1
  assumes
    "\<exists>t p. x=\<langle>t,p\<rangle>" "[x,\<alpha>,m,P,leq,one] @ nenv \<in>list(M)"
    "\<phi>\<in>formula"
  shows
    "(\<exists>\<tau>\<in>M. \<exists>V\<in>M. is_Vset(\<lambda>a. (##M)(a),\<alpha>,V) \<and> \<tau> \<in> V \<and> (snd(x) \<tturnstile> \<phi> ([fst(x),\<tau>]@nenv)))
    \<longleftrightarrow> M, [\<alpha>, x, m, P, leq, one] @ nenv \<Turnstile> body_ground_repl_fm(\<phi>)"
proof -
  {
    fix \<tau> V t p 
    assume "\<tau> \<in> M" "V \<in> M" "x = \<langle>t, p\<rangle>" "t \<in> M" "p \<in> M"
    with assms
    have "\<tau> \<in> V \<and> (M, [p,P,leq,one,t,\<tau>] @ nenv \<Turnstile> forces(\<phi>)) \<longleftrightarrow>
      \<tau> \<in> V \<and> (M, [V,\<tau>,\<alpha>,\<langle>t, p\<rangle>,m,P, leq, one] @ nenv \<Turnstile> rename_split_fm(\<phi>))"
      using sats_forces_iff_sats_rename_split_fm[of \<alpha> m p t \<tau>, where nenv=nenv and \<phi>=\<phi>]
      by auto
  }
  note eq = this
  then
  show ?thesis
    unfolding body_ground_repl_fm_def
    apply (insert assms)
    apply (rule iff_sats | simp add:nonempty[simplified])+
    using eq
    by (auto del: iffI)
qed 

definition ground_repl_fm where
  "ground_repl_fm(\<phi>) \<equiv> least_fm(body_ground_repl_fm(\<phi>), 1)"

lemma ground_repl_fm_type[TC]:
  "\<phi>\<in>formula \<Longrightarrow> ground_repl_fm(\<phi>) \<in> formula"
  unfolding ground_repl_fm_def by simp

lemma arity_ground_repl_fm:
  assumes "\<phi>\<in>formula"
  shows "arity(ground_repl_fm(\<phi>)) \<le> 5 \<union> (3 #+ arity(\<phi>))"
proof -
  from assms
  have "Arith.pred(arity(body_ground_repl_fm(\<phi>))) \<le> 5 \<union> (3 #+ arity(\<phi>))"
    using arity_body_ground_repl_fm_le pred_mono succ_Un_distrib
    by (rule_tac pred_le) auto
  with assms
  have "2 \<union> Arith.pred(arity(body_ground_repl_fm(\<phi>))) \<le> 5 \<union> (3 #+ arity(\<phi>))"
    using Un_le le_Un_iff by auto
  then
  show ?thesis
    using assms arity_forces arity_body_ground_repl_fm_le
    unfolding least_fm_def ground_repl_fm_def
    apply (auto simp add:arity Un_assoc[symmetric])
    apply (simp add: pred_Un Un_assoc, simp add: Un_assoc[symmetric] union_abs1 pred_Un)
    by (simp only: Un_commute, subst Un_commute, simp only: Un_assoc[symmetric])
      (auto simp add: ord_simp_union) (* FIXME: slow *)
qed

lemma Replace_sats_in_MG:
  assumes
    "c\<in>M[G]" "env \<in> list(M[G])"
    "\<phi> \<in> formula" "arity(\<phi>) \<le> 2 #+ length(env)"
    "univalent(##M[G], c, \<lambda>x v. (M[G] , [x,v]@env \<Turnstile> \<phi>) )"
    and
    ground_replacement:
    "\<And>nenv. nenv\<in>list(M) \<Longrightarrow> ground_repl_fm(\<phi>) \<in> formula \<Longrightarrow> [P,leq,one] @ nenv \<in> list(M) \<Longrightarrow>
      arity(ground_repl_fm(\<phi>)) \<le> 2 #+ length([P,leq,one] @ nenv) \<Longrightarrow>
      strong_replacement(##M,\<lambda>x y. sats(M,ground_repl_fm(\<phi>),[x,y] @ [P,leq,one] @ nenv))"
  shows
    "{v. x\<in>c, v\<in>M[G] \<and> (M[G] , [x,v]@env \<Turnstile> \<phi>)} \<in> M[G]"
proof -
  let ?R = "\<lambda> x v . v\<in>M[G] \<and> (M[G] , [x,v]@env \<Turnstile> \<phi>)"
  from \<open>c\<in>M[G]\<close>
  obtain \<pi>' where "val(P,G, \<pi>') = c" "\<pi>' \<in> M"
    using GenExt_def by auto
  then
  have "domain(\<pi>')\<times>P\<in>M" (is "?\<pi>\<in>M")
    using cartprod_closed P_in_M domain_closed by simp
  from \<open>val(P,G, \<pi>') = c\<close>
  have "c \<subseteq> val(P,G,?\<pi>)"
    using def_val[of G ?\<pi>] one_in_P one_in_G[OF generic] elem_of_val
      domain_of_prod[OF one_in_P, of "domain(\<pi>')"] by force
  from \<open>env \<in> _\<close>
  obtain nenv where "nenv\<in>list(M)" "env = map(val(P,G),nenv)"
    using map_val by auto
  then
  have "length(nenv) = length(env)" by simp
  define f where "f(\<rho>p) \<equiv> \<mu> \<alpha>. \<alpha>\<in>M \<and> (\<exists>\<tau>\<in>M. \<tau> \<in> Vset(\<alpha>) \<and>
        (snd(\<rho>p) \<tturnstile> \<phi> ([fst(\<rho>p),\<tau>] @ nenv)))" (is "_ \<equiv> \<mu> \<alpha>. ?P(\<rho>p,\<alpha>)") for \<rho>p
  have "f(\<rho>p) = (\<mu> \<alpha>. \<alpha>\<in>M \<and> (\<exists>\<tau>\<in>M. \<exists>V\<in>M. is_Vset(##M,\<alpha>,V) \<and> \<tau>\<in>V \<and>
        (snd(\<rho>p) \<tturnstile> \<phi> ([fst(\<rho>p),\<tau>] @ nenv))))" (is "_ = (\<mu> \<alpha>. \<alpha>\<in>M \<and> ?Q(\<rho>p,\<alpha>))") for \<rho>p
    unfolding f_def using Vset_abs Vset_closed Ord_Least_cong[of "?P(\<rho>p)" "\<lambda> \<alpha>. \<alpha>\<in>M \<and> ?Q(\<rho>p,\<alpha>)"]
    by (simp, simp del:setclass_iff)
  moreover
  have "f(\<rho>p) \<in> M" for \<rho>p
    unfolding f_def using Least_closed'[of "?P(\<rho>p)"] by simp
  ultimately
  have 1:"least(##M,\<lambda>\<alpha>. ?Q(\<rho>p,\<alpha>),f(\<rho>p))" for \<rho>p
    using least_abs'[of "\<lambda>\<alpha>. \<alpha>\<in>M \<and> ?Q(\<rho>p,\<alpha>)" "f(\<rho>p)"] least_conj
    by (simp flip: setclass_iff)
  have "Ord(f(\<rho>p))" for \<rho>p unfolding f_def by simp
  define QQ where "QQ\<equiv>?Q"
  from 1
  have "least(##M,\<lambda>\<alpha>. QQ(\<rho>p,\<alpha>),f(\<rho>p))" for \<rho>p
    unfolding QQ_def .
  from \<open>arity(\<phi>) \<le> _\<close> \<open>length(nenv) = _\<close>
  have "arity(\<phi>) \<le> 2 #+ length(nenv)"
    by simp
  moreover
  note assms \<open>nenv\<in>list(M)\<close> \<open>?\<pi>\<in>M\<close>
  moreover
  have "\<rho>p\<in>?\<pi> \<Longrightarrow> \<exists>t p. \<rho>p=\<langle>t,p\<rangle>" for \<rho>p
    by auto
  ultimately
  have body:"(M , [\<alpha>,\<rho>p,m,P,leq,one] @ nenv \<Turnstile> body_ground_repl_fm(\<phi>)) \<longleftrightarrow> ?Q(\<rho>p,\<alpha>)"
    if "\<rho>p\<in>?\<pi>" "\<rho>p\<in>M" "m\<in>M" "\<alpha>\<in>M" for \<alpha> \<rho>p m
    using that P_in_M leq_in_M one_in_M sats_body_ground_repl_fm[of \<rho>p \<alpha> m nenv \<phi>] by simp
  {
    fix \<rho>p m
    assume asm: "\<rho>p\<in>M" "\<rho>p\<in>?\<pi>" "m\<in>M"
    note inM = this P_in_M leq_in_M one_in_M \<open>nenv\<in>list(M)\<close>
    with body
    have body':"\<And>\<alpha>. \<alpha> \<in> M \<Longrightarrow> (\<exists>\<tau>\<in>M. \<exists>V\<in>M. is_Vset(\<lambda>a. (##M)(a), \<alpha>, V) \<and> \<tau> \<in> V \<and>
          (snd(\<rho>p) \<tturnstile> \<phi> ([fst(\<rho>p),\<tau>] @ nenv))) \<longleftrightarrow>
          M, Cons(\<alpha>, [\<rho>p, m, P, leq, one] @ nenv) \<Turnstile> body_ground_repl_fm(\<phi>)" by simp
    from inM
    have "(M , [\<rho>p,m,P,leq,one] @ nenv \<Turnstile> ground_repl_fm(\<phi>)) \<longleftrightarrow> least(##M, QQ(\<rho>p), m)"
      using sats_least_fm[OF body', of 1] unfolding QQ_def ground_repl_fm_def
      by (simp, simp flip: setclass_iff)
  }
  then
  have "(M, [\<rho>p,m,P,leq,one] @ nenv \<Turnstile> ground_repl_fm(\<phi>)) \<longleftrightarrow> least(##M, QQ(\<rho>p), m)"
    if "\<rho>p\<in>M" "\<rho>p\<in>?\<pi>" "m\<in>M" for \<rho>p m using that by simp
  then
  have "univalent(##M, ?\<pi>, \<lambda>\<rho>p m. M , [\<rho>p,m] @ ([P,leq,one] @ nenv) \<Turnstile> ground_repl_fm(\<phi>))"
    unfolding univalent_def by (auto intro:unique_least)
  moreover from \<open>length(_) = _\<close> \<open>env \<in> _\<close>
  have "length([P,leq,one] @ nenv) = 3 #+ length(env)" by simp
  moreover from \<open>arity(\<phi>) \<le> 2 #+ length(nenv)\<close>
    \<open>length(_) = length(_)\<close>[symmetric] \<open>nenv\<in>_\<close> \<open>\<phi>\<in>_\<close>
  have "arity(ground_repl_fm(\<phi>)) \<le> 5 #+ length(env)"
    using arity_ground_repl_fm[of \<phi>] le_trans Un_le by auto
  moreover from \<open>\<phi>\<in>formula\<close>
  have "ground_repl_fm(\<phi>)\<in>formula" by simp
  moreover
  note inM = P_in_M leq_in_M one_in_M \<open>nenv\<in>list(M)\<close> \<open>?\<pi>\<in>M\<close>
  moreover
  note \<open>length(nenv) = length(env)\<close>
  ultimately
  obtain Y where "Y\<in>M"
    "\<forall>m\<in>M. m \<in> Y \<longleftrightarrow> (\<exists>\<rho>p\<in>M. \<rho>p \<in> ?\<pi> \<and> (M, [\<rho>p,m] @ ([P,leq,one] @ nenv) \<Turnstile> ground_repl_fm(\<phi>)))"
    using ground_replacement[of nenv]
    unfolding strong_replacement_def by auto
  with \<open>least(_,QQ(_),f(_))\<close> \<open>f(_) \<in> M\<close> \<open>?\<pi>\<in>M\<close>
    \<open>_ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> (M,_ \<Turnstile> ground_repl_fm(\<phi>)) \<longleftrightarrow> least(_,_,_)\<close>
  have "f(\<rho>p)\<in>Y" if "\<rho>p\<in>?\<pi>" for \<rho>p
    using that transitivity[OF _ \<open>?\<pi>\<in>M\<close>]
    by (clarsimp, rule_tac x="\<langle>x,y\<rangle>" in bexI, auto)
  moreover
  have "{y\<in>Y. Ord(y)} \<in> M"
    using \<open>Y\<in>M\<close> separation_ax sats_ordinal_fm trans_M
      separation_cong[of "##M" "\<lambda>y. sats(M,ordinal_fm(0),[y])" "Ord"]
      separation_closed by (simp add:arity)
  then
  have "\<Union> {y\<in>Y. Ord(y)} \<in> M" (is "?sup \<in> M")
    using Union_closed by simp
  then
  have "{x\<in>Vset(?sup). x \<in> M} \<in> M"
    using Vset_closed by simp
  moreover
  have "{one} \<in> M"
    using one_in_M singleton_closed by simp
  ultimately
  have "{x\<in>Vset(?sup). x \<in> M} \<times> {one} \<in> M" (is "?big_name \<in> M")
    using cartprod_closed by simp
  then
  have "val(P,G,?big_name) \<in> M[G]"
    by (blast intro:GenExtI)
  {
    fix v x
    assume "x\<in>c"
    moreover
    note \<open>val(P,G,\<pi>')=c\<close> \<open>\<pi>'\<in>M\<close>
    moreover
    from calculation
    obtain \<rho> p where "\<langle>\<rho>,p\<rangle>\<in>\<pi>'"  "val(P,G,\<rho>) = x" "p\<in>G" "\<rho>\<in>M"
      using elem_of_val_pair'[of \<pi>' x G] by blast
    moreover
    assume "v\<in>M[G]"
    then
    obtain \<sigma> where "val(P,G,\<sigma>) = v" "\<sigma>\<in>M"
      using GenExtD by auto
    moreover
    assume "sats(M[G], \<phi>, [x,v] @ env)"
    moreover
    note \<open>\<phi>\<in>_\<close> \<open>nenv\<in>_\<close> \<open>env = _\<close> \<open>arity(\<phi>)\<le> 2 #+ length(env)\<close>
    ultimately
    obtain q where "q\<in>G" "q \<tturnstile> \<phi> ([\<rho>,\<sigma>]@nenv)"
      using truth_lemma[OF \<open>\<phi>\<in>_\<close> generic, symmetric, of "[\<rho>,\<sigma>] @ nenv"]
      by auto
    with \<open>\<langle>\<rho>,p\<rangle>\<in>\<pi>'\<close> \<open>\<langle>\<rho>,q\<rangle>\<in>?\<pi> \<Longrightarrow> f(\<langle>\<rho>,q\<rangle>)\<in>Y\<close>
    have "f(\<langle>\<rho>,q\<rangle>)\<in>Y"
      using generic unfolding M_generic_def filter_def by blast
    let ?\<alpha>="succ(rank(\<sigma>))"
    note \<open>\<sigma>\<in>M\<close>
    moreover from this
    have "?\<alpha> \<in> M"
      using rank_closed cons_closed by (simp flip: setclass_iff)
    moreover
    have "\<sigma> \<in> Vset(?\<alpha>)"
      using Vset_Ord_rank_iff by auto
    moreover
    note \<open>q \<tturnstile> \<phi> ([\<rho>,\<sigma>] @ nenv)\<close>
    ultimately
    have "?P(\<langle>\<rho>,q\<rangle>,?\<alpha>)" by (auto simp del: Vset_rank_iff)
    moreover
    have "(\<mu> \<alpha>. ?P(\<langle>\<rho>,q\<rangle>,\<alpha>)) = f(\<langle>\<rho>,q\<rangle>)"
      unfolding f_def by simp
    ultimately
    obtain \<tau> where "\<tau>\<in>M" "\<tau> \<in> Vset(f(\<langle>\<rho>,q\<rangle>))" "q \<tturnstile> \<phi> ([\<rho>,\<tau>] @ nenv)"
      using LeastI[of "\<lambda> \<alpha>. ?P(\<langle>\<rho>,q\<rangle>,\<alpha>)" ?\<alpha>] by auto
    with \<open>q\<in>G\<close> \<open>\<rho>\<in>M\<close> \<open>nenv\<in>_\<close> \<open>arity(\<phi>)\<le> 2 #+ length(nenv)\<close>
    have "M[G], map(val(P,G),[\<rho>,\<tau>] @ nenv) \<Turnstile> \<phi>"
      using truth_lemma[OF \<open>\<phi>\<in>_\<close> generic, of "[\<rho>,\<tau>] @ nenv"] by auto
    moreover from \<open>x\<in>c\<close> \<open>c\<in>M[G]\<close>
    have "x\<in>M[G]" using transitivity_MG by simp
    moreover
    note \<open>M[G],[x,v] @ env\<Turnstile> \<phi>\<close> \<open>env = map(val(P,G),nenv)\<close> \<open>\<tau>\<in>M\<close> \<open>val(P,G,\<rho>)=x\<close>
      \<open>univalent(##M[G],_,_)\<close> \<open>x\<in>c\<close> \<open>v\<in>M[G]\<close>
    ultimately
    have "v=val(P,G,\<tau>)"
      using GenExtI[of \<tau> G] unfolding univalent_def by (auto)
    from \<open>\<tau> \<in> Vset(f(\<langle>\<rho>,q\<rangle>))\<close> \<open>Ord(f(_))\<close>  \<open>f(\<langle>\<rho>,q\<rangle>)\<in>Y\<close>
    have "\<tau> \<in> Vset(?sup)"
      using Vset_Ord_rank_iff lt_Union_iff[of _ "rank(\<tau>)"] by auto
    with \<open>\<tau>\<in>M\<close>
    have "val(P,G,\<tau>) \<in> val(P,G,?big_name)"
      using domain_of_prod[of one "{one}" "{x\<in>Vset(?sup). x \<in> M}" ] def_val[of G ?big_name]
        one_in_G[OF generic] one_in_P  by (auto simp del: Vset_rank_iff)
    with \<open>v=val(P,G,\<tau>)\<close>
    have "v \<in> val(P,G,{x\<in>Vset(?sup). x \<in> M} \<times> {one})"
      by simp
  }
  then
  have "{v. x\<in>c, ?R(x,v)} \<subseteq> val(P,G,?big_name)" (is "?repl\<subseteq>?big")
    by blast
  with \<open>?big_name\<in>M\<close>
  have "?repl = {v\<in>?big. \<exists>x\<in>c. sats(M[G], \<phi>, [x,v] @ env )}" (is "_ = ?rhs")
  proof(intro equalityI subsetI)
    fix v
    assume "v\<in>?repl"
    with \<open>?repl\<subseteq>?big\<close>
    obtain x where "x\<in>c" "M[G], [x, v] @ env \<Turnstile> \<phi>" "v\<in>?big"
      using subsetD by auto
    with \<open>univalent(##M[G],_,_)\<close> \<open>c\<in>M[G]\<close>
    show "v \<in> ?rhs"
      unfolding univalent_def
      using transitivity_MG ReplaceI[of "\<lambda> x v. \<exists>x\<in>c. M[G], [x, v] @ env \<Turnstile> \<phi>"] by blast
  next
    fix v
    assume "v\<in>?rhs"
    then
    obtain x where
      "v\<in>val(P,G, ?big_name)" "M[G], [x, v] @ env \<Turnstile> \<phi>" "x\<in>c"
      by blast
    moreover from this \<open>c\<in>M[G]\<close>
    have "v\<in>M[G]" "x\<in>M[G]"
      using transitivity_MG GenExtI[OF \<open>?big_name\<in>_\<close>,of G] by auto
    moreover from calculation \<open>univalent(##M[G],_,_)\<close>
    have "?R(x,y) \<Longrightarrow> y = v" for y
      unfolding univalent_def by auto
    ultimately
    show "v\<in>?repl"
      using ReplaceI[of ?R x v c]
      by blast
  qed
  moreover
  let ?\<psi> = "Exists(And(Member(0,2#+length(env)),\<phi>))"
  have "v\<in>M[G] \<Longrightarrow> (\<exists>x\<in>c. M[G], [x,v] @ env \<Turnstile> \<phi>) \<longleftrightarrow> M[G], [v] @ env @ [c] \<Turnstile> ?\<psi>"
    "arity(?\<psi>) \<le> 2 #+ length(env)" "?\<psi>\<in>formula"
    for v
  proof -
    fix v
    assume "v\<in>M[G]"
    with \<open>c\<in>M[G]\<close>
    have "nth(length(env)#+1,[v]@env@[c]) = c"
      using  \<open>env\<in>_\<close>nth_concat[of v c "M[G]" env]
      by auto
    note inMG= \<open>nth(length(env)#+1,[v]@env@[c]) = c\<close> \<open>c\<in>M[G]\<close> \<open>v\<in>M[G]\<close> \<open>env\<in>_\<close>
    show "(\<exists>x\<in>c. M[G], [x,v] @ env \<Turnstile> \<phi>) \<longleftrightarrow> M[G], [v] @ env @ [c] \<Turnstile> ?\<psi>"
    proof
      assume "\<exists>x\<in>c. M[G], [x, v] @ env \<Turnstile> \<phi>"
      then obtain x where
        "x\<in>c" "M[G], [x, v] @ env \<Turnstile> \<phi>" "x\<in>M[G]"
        using transitivity_MG[OF _ \<open>c\<in>M[G]\<close>]
        by auto
      with \<open>\<phi>\<in>_\<close> \<open>arity(\<phi>)\<le>2#+length(env)\<close> inMG
      show "M[G], [v] @ env @ [c] \<Turnstile> Exists(And(Member(0, 2 #+ length(env)), \<phi>))"
        using arity_sats_iff[of \<phi> "[c]" _ "[x,v]@env"]
        by auto
    next
      assume "M[G], [v] @ env @ [c] \<Turnstile> Exists(And(Member(0, 2 #+ length(env)), \<phi>))"
      with inMG
      obtain x where
        "x\<in>M[G]" "x\<in>c" "M[G], [x,v]@env@[c] \<Turnstile> \<phi>"
        by auto
      with \<open>\<phi>\<in>_\<close> \<open>arity(\<phi>)\<le>2#+length(env)\<close> inMG
      show "\<exists>x\<in>c. M[G], [x, v] @ env\<Turnstile> \<phi>"
        using arity_sats_iff[of \<phi> "[c]" _ "[x,v]@env"]
        by auto
    qed
  next
    from \<open>env\<in>_\<close> \<open>\<phi>\<in>_\<close>
    show "arity(?\<psi>)\<le>2#+length(env)"
      using pred_mono[OF _ \<open>arity(\<phi>)\<le>2#+length(env)\<close>] lt_trans[OF _ le_refl]
      by (auto simp add:ord_simp_union arity)
  next
    from \<open>\<phi>\<in>_\<close>
    show "?\<psi>\<in>formula" by simp
  qed
  moreover from this
  have "{v\<in>?big. \<exists>x\<in>c. M[G], [x,v] @ env \<Turnstile> \<phi>} = {v\<in>?big. M[G], [v] @ env @ [c] \<Turnstile>  ?\<psi>}"
    using transitivity_MG[OF _ GenExtI, OF _ \<open>?big_name\<in>M\<close>]
    by simp
  moreover from calculation and \<open>env\<in>_\<close> \<open>c\<in>_\<close> \<open>?big\<in>M[G]\<close>
  have "{v\<in>?big. M[G] , [v] @ env @ [c] \<Turnstile> ?\<psi>} \<in> M[G]"
    using Collect_sats_in_MG by auto
  ultimately
  show ?thesis by simp
qed

theorem strong_replacement_in_MG:
  assumes
    "\<phi>\<in>formula" and "arity(\<phi>) \<le> 2 #+ length(env)" "env \<in> list(M[G])"
    (*
    and
    ground_replacement:
    "\<And>nenv. nenv\<in>list(M) \<Longrightarrow> ground_repl_fm(\<phi>) \<in> formula \<Longrightarrow> [P,leq,one] @ nenv \<in> list(M) \<Longrightarrow>
      arity(ground_repl_fm(\<phi>)) \<le> 2 #+ length([P,leq,one] @ nenv) \<Longrightarrow>
      strong_replacement(##M,\<lambda>x y. sats(M,ground_repl_fm(\<phi>),[x,y] @ [P,leq,one] @ nenv))"
  *)
  shows
    "strong_replacement(##M[G],\<lambda>x v. sats(M[G],\<phi>,[x,v] @ env))"
proof -
  let ?R="\<lambda>x y . M[G], [x, y] @ env \<Turnstile> \<phi>"
  {
    fix A
    let ?Y="{v . x \<in> A, v\<in>M[G] \<and> ?R(x,v)}"
    assume 1: "(##M[G])(A)"
      "\<forall>x[##M[G]]. x \<in> A \<longrightarrow> (\<forall>y[##M[G]]. \<forall>z[##M[G]]. ?R(x,y) \<and> ?R(x,z) \<longrightarrow> y = z)"
    then
    have "univalent(##M[G], A, ?R)" "A\<in>M[G]"
      unfolding univalent_def by simp_all
    with assms \<open>A\<in>_\<close>
    have "(##M[G])(?Y)"
      using Replace_sats_in_MG replacement_ax (* only ground_replacement here *) by auto
    have "b \<in> ?Y \<longleftrightarrow> (\<exists>x[##M[G]]. x \<in> A \<and> ?R(x,b))" if "(##M[G])(b)" for b
    proof(rule)
      from \<open>A\<in>_\<close>
      show "\<exists>x[##M[G]]. x \<in> A \<and> ?R(x,b)" if "b \<in> ?Y"
        using that transitivity_MG by auto
    next
      show "b \<in> ?Y" if "\<exists>x[##M[G]]. x \<in> A \<and> ?R(x,b)"
      proof -
        from \<open>(##M[G])(b)\<close>
        have "b\<in>M[G]" by simp
        with that
        obtain x where "(##M[G])(x)" "x\<in>A" "b\<in>M[G] \<and> ?R(x,b)"
          by blast
        moreover from this 1 \<open>(##M[G])(b)\<close>
        have "x\<in>M[G]" "z\<in>M[G] \<and> ?R(x,z) \<Longrightarrow> b = z" for z
          by auto
        ultimately
        show ?thesis
          using ReplaceI[of "\<lambda> x y. y\<in>M[G] \<and> ?R(x,y)"] by blast
      qed
    qed
    then
    have "\<forall>b[##M[G]]. b \<in> ?Y \<longleftrightarrow> (\<exists>x[##M[G]]. x \<in> A \<and> ?R(x,b))"
      by simp
    with \<open>(##M[G])(?Y)\<close>
    have " (\<exists>Y[##M[G]]. \<forall>b[##M[G]]. b \<in> Y \<longleftrightarrow> (\<exists>x[##M[G]]. x \<in> A \<and> ?R(x,b)))"
      by auto
  }
  then show ?thesis unfolding strong_replacement_def univalent_def
    by auto
qed

end \<comment> \<open>\<^locale>\<open>G_generic\<close>\<close>

end