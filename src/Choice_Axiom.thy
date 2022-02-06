section\<open>The Axiom of Choice in $M[G]$\<close>

theory Choice_Axiom
  imports
    Powerset_Axiom
    Extensionality_Axiom
    Foundation_Axiom
    Replacement_Axiom
    Infinity_Axiom
begin

definition
  induced_surj :: "i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>i" where
  "induced_surj(f,a,e) \<equiv> f-``(range(f)-a)\<times>{e} \<union> restrict(f,f-``a)"

lemma domain_induced_surj: "domain(induced_surj(f,a,e)) = domain(f)"
  unfolding induced_surj_def using domain_restrict domain_of_prod by auto

lemma range_restrict_vimage:
  assumes "function(f)"
  shows "range(restrict(f,f-``a)) \<subseteq> a"
proof
  from assms
  have "function(restrict(f,f-``a))"
    using function_restrictI by simp
  fix y
  assume "y \<in> range(restrict(f,f-``a))"
  then
  obtain x where "\<langle>x,y\<rangle> \<in> restrict(f,f-``a)"  "x \<in> f-``a" "x\<in>domain(f)"
    using domain_restrict domainI[of _ _ "restrict(f,f-``a)"] by auto
  moreover
  note \<open>function(restrict(f,f-``a))\<close>
  ultimately
  have "y = restrict(f,f-``a)`x"
    using function_apply_equality by blast
  also from \<open>x \<in> f-``a\<close>
  have "restrict(f,f-``a)`x = f`x"
    by simp
  finally
  have "y=f`x" .
  moreover from assms \<open>x\<in>domain(f)\<close>
  have "\<langle>x,f`x\<rangle> \<in> f"
    using function_apply_Pair by auto
  moreover
  note assms \<open>x \<in> f-``a\<close>
  ultimately
  show "y\<in>a"
    using function_image_vimage[of f a] by auto
qed

lemma induced_surj_type:
  assumes
    "function(f)" (* "relation(f)" (* a function can contain nonpairs *) *)
  shows
    "induced_surj(f,a,e): domain(f) \<rightarrow> {e} \<union> a"
    and
    "x \<in> f-``a \<Longrightarrow> induced_surj(f,a,e)`x = f`x"
proof -
  let ?f1="f-``(range(f)-a) \<times> {e}" and ?f2="restrict(f, f-``a)"
  have "domain(?f2) = domain(f) \<inter> f-``a"
    using domain_restrict by simp
  moreover from assms
  have 1: "domain(?f1) = f-``(range(f))-f-``a"
    using domain_of_prod function_vimage_Diff by simp
  ultimately
  have "domain(?f1) \<inter> domain(?f2) = 0"
    by auto
  moreover
  have "function(?f1)" "relation(?f1)" "range(?f1) \<subseteq> {e}"
    unfolding function_def relation_def range_def by auto
  moreover from this and assms
  have "?f1: domain(?f1) \<rightarrow> range(?f1)"
    using function_imp_Pi by simp
  moreover from assms
  have "?f2: domain(?f2) \<rightarrow> range(?f2)"
    using function_imp_Pi[of "restrict(f, f -`` a)"] function_restrictI by simp
  moreover from assms
  have "range(?f2) \<subseteq> a"
    using range_restrict_vimage by simp
  ultimately
  have "induced_surj(f,a,e): domain(?f1) \<union> domain(?f2) \<rightarrow> {e} \<union> a"
    unfolding induced_surj_def using fun_is_function fun_disjoint_Un fun_weaken_type by simp
  moreover
  have "domain(?f1) \<union> domain(?f2) = domain(f)"
    using domain_restrict domain_of_prod by auto
  ultimately
  show "induced_surj(f,a,e): domain(f) \<rightarrow> {e} \<union> a"
    by simp
  assume "x \<in> f-``a"
  then
  have "?f2`x = f`x"
    using restrict by simp
  moreover from \<open>x \<in> f-``a\<close> and 1
  have "x \<notin> domain(?f1)"
    by simp
  ultimately
  show "induced_surj(f,a,e)`x = f`x"
    unfolding induced_surj_def using fun_disjoint_apply2[of x ?f1 ?f2] by simp
qed

lemma induced_surj_is_surj :
  assumes
    "e\<in>a" "function(f)" "domain(f) = \<alpha>" "\<And>y. y \<in> a \<Longrightarrow> \<exists>x\<in>\<alpha>. f ` x = y"
  shows
    "induced_surj(f,a,e) \<in> surj(\<alpha>,a)"
  unfolding surj_def
proof (intro CollectI ballI)
  from assms
  show "induced_surj(f,a,e): \<alpha> \<rightarrow> a"
    using induced_surj_type[of f a e] cons_eq cons_absorb by simp
  fix y
  assume "y \<in> a"
  with assms
  have "\<exists>x\<in>\<alpha>. f ` x = y"
    by simp
  then
  obtain x where "x\<in>\<alpha>" "f ` x = y" by auto
  with \<open>y\<in>a\<close> assms
  have "x\<in>f-``a"
    using vimage_iff function_apply_Pair[of f x] by auto
  with \<open>f ` x = y\<close> assms
  have "induced_surj(f, a, e) ` x = y"
    using induced_surj_type by simp
  with \<open>x\<in>\<alpha>\<close> show
    "\<exists>x\<in>\<alpha>. induced_surj(f, a, e) ` x = y" by auto
qed

definition
  upair_name' :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where
  "upair_name'(\<tau>,\<rho>,on) \<equiv> Upair(\<langle>\<tau>,on\<rangle>,\<langle>\<rho>,on\<rangle>)"

relativize "upair_name'" "is_upair_name"
synthesize "upair_name" from_definition "is_upair_name"
definition
  opair_name' :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where
  "opair_name'(\<tau>,\<rho>,on) \<equiv> upair_name'(upair_name'(\<tau>,\<tau>,on),upair_name'(\<tau>,\<rho>,on),on)"

relativize "opair_name'" "is_opair_name"
synthesize "opair_name" from_definition "is_opair_name"

context G_generic
begin

abbreviation upair_name where
  "upair_name(\<tau>,\<rho>) \<equiv> upair_name'(\<tau>,\<rho>,\<one>)"

abbreviation opair_name where
  "opair_name(\<tau>,\<rho>) \<equiv> opair_name'(\<tau>,\<rho>,\<one>)"

lemma Upair_simp : "Upair(a,b) = {a,b}"
  by auto

lemma upair_name_abs :
  assumes "x\<in>M" "y\<in>M" "z\<in>M"
  shows "is_upair_name(##M,x,y,\<one>,z) \<longleftrightarrow> z = upair_name(x,y)"
  unfolding is_upair_name_def upair_name'_def
  using assms zero_in_M one_in_M  empty_abs pair_abs pair_in_M_iff upair_in_M_iff upair_abs
  Upair_simp
  by simp

lemma upair_name_closed :
  "\<lbrakk> x\<in>M; y\<in>M \<rbrakk> \<Longrightarrow> upair_name(x,y)\<in>M"
  unfolding upair_name'_def using upair_in_M_iff pair_in_M_iff one_in_M upair_in_M_iff Upair_simp
  by simp

lemma sats_upair_name_fm' :
  assumes "x\<in>nat" "y\<in>nat" "z\<in>nat" "o\<in>nat" "env\<in>list(M)""nth(o,env)=\<one>"
  shows
    "sats(M,upair_name_fm(x,y,o,z),env) \<longleftrightarrow> is_upair_name(##M,nth(x,env),nth(y,env),nth(o,env),nth(z,env))"
  unfolding upair_name_fm_def is_upair_name_def
  using assms sats_upair_name_fm
  by auto

lemma opair_name_abs :
  assumes "x\<in>M" "y\<in>M" "z\<in>M"
  shows "is_opair_name(##M,x,y,\<one>,z) \<longleftrightarrow> z = opair_name(x,y)"
  unfolding is_opair_name_def opair_name'_def
  using assms upair_name_abs upair_name_closed by simp

lemma opair_name_closed :
  "\<lbrakk> x\<in>M; y\<in>M \<rbrakk> \<Longrightarrow> opair_name(x,y)\<in>M"
  unfolding opair_name'_def
  using upair_name_closed by simp

lemma sats_opair_name_fm :
  assumes "x\<in>nat" "y\<in>nat" "z\<in>nat" "o\<in>nat" "env\<in>list(M)" "nth(o,env)=\<one>"
  shows
    "sats(M,opair_name_fm(x,y,o,z),env) \<longleftrightarrow> is_opair_name(##M,nth(x,env),nth(y,env),nth(o,env),nth(z,env))"
  using assms sats_opair_name_fm
  by auto

lemma val_upair_name : "val(P,G,upair_name(\<tau>,\<rho>)) = {val(P,G,\<tau>),val(P,G,\<rho>)}"
  unfolding upair_name'_def using val_Upair Upair_simp generic one_in_G one_in_P by simp

lemma val_opair_name : "val(P,G,opair_name(\<tau>,\<rho>)) = \<langle>val(P,G,\<tau>),val(P,G,\<rho>)\<rangle>"
  unfolding opair_name'_def Pair_def using val_upair_name by simp

lemma val_RepFun_one: "val(P,G,{\<langle>f(x),\<one>\<rangle> . x\<in>a}) = {val(P,G,f(x)) . x\<in>a}"
proof -
  let ?A = "{f(x) . x \<in> a}"
  let ?Q = "\<lambda>\<langle>x,p\<rangle> . p = \<one>"
  have "\<one> \<in> P\<inter>G" using generic one_in_G one_in_P by simp
  have "{\<langle>f(x),\<one>\<rangle> . x \<in> a} = {t \<in> ?A \<times> P . ?Q(t)}"
    using one_in_P by force
  then
  have "val(P,G,{\<langle>f(x),\<one>\<rangle>  . x \<in> a}) = val(P,G,{t \<in> ?A \<times> P . ?Q(t)})"
    by simp
  also
  have "... = {val(P,G,t) .. t \<in> ?A , \<exists>p\<in>P\<inter>G . ?Q(\<langle>t,p\<rangle>)}"
    using val_of_name_alt by simp
  also
  have "... = {val(P,G,t) . t \<in> ?A }"
    using \<open>\<one>\<in>P\<inter>G\<close> by force
  also
  have "... = {val(P,G,f(x)) . x \<in> a}"
    by auto
  finally show ?thesis by simp
qed

subsection\<open>$M[G]$ is a transitive model of ZF\<close>

interpretation mgzf: M_ZF_trans "M[G]"
  using Transset_MG generic pairing_in_MG Union_MG
    extensionality_in_MG power_in_MG foundation_in_MG
    strong_replacement_in_MG separation_in_MG infinity_in_MG
  by unfold_locales simp_all

(* FIXME: we could have this synthesized if is_check were parameterised by the class.
*)
definition
  is_opname_check :: "[i,i,i] \<Rightarrow> o" where
  "is_opname_check(s,x,y) \<equiv> \<exists>chx\<in>M. \<exists>sx\<in>M. is_check(x,chx) \<and> fun_apply(##M,s,x,sx) \<and>
                             is_opair_name(##M,chx,sx,\<one>,y)"

definition
  opname_check_fm :: "[i,i,i,i] \<Rightarrow> i" where
  "opname_check_fm(o,s,x,y) \<equiv> Exists(Exists(And(check_fm(2#+x,2#+o,1),
                              And(fun_apply_fm(2#+s,2#+x,0),opair_name_fm(1,0,2#+o,2#+y)))))"

lemma opname_check_fm_type[TC] :
  "\<lbrakk> s\<in>nat;x\<in>nat;y\<in>nat;o\<in>nat\<rbrakk> \<Longrightarrow> opname_check_fm(o,s,x,y)\<in>formula"
  unfolding opname_check_fm_def by simp

lemma sats_opname_check_fm:
  assumes "x\<in>nat" "y\<in>nat" "z\<in>nat" "o\<in>nat" "env\<in>list(M)" "nth(o,env)=\<one>"
          "y<length(env)"
  shows
    "sats(M,opname_check_fm(o,x,y,z),env) \<longleftrightarrow> is_opname_check(nth(x,env),nth(y,env),nth(z,env))"
  unfolding opname_check_fm_def is_opname_check_def
  using assms sats_check_fm sats_opair_name_fm one_in_M
  by simp

lemma opname_check_abs :
  assumes "s\<in>M" "x\<in>M" "y\<in>M"
  shows "is_opname_check(s,x,y) \<longleftrightarrow> y = opair_name(check(x),s`x)"
  unfolding is_opname_check_def
  using assms check_abs check_in_M opair_name_abs apply_abs apply_closed by simp

lemma repl_opname_check :
  assumes
    "A\<in>M" "f\<in>M"
  shows
   "{opair_name(check(x),f`x). x\<in>A}\<in>M"
proof -
  have "arity(opname_check_fm(3,2,0,1))= 4"
    unfolding fm_definitions opname_check_fm_def
    by (simp add:ord_simp_union arity)
  moreover
  have "x\<in>A \<Longrightarrow> opair_name(check(x), f ` x)\<in>M" for x
    using assms opair_name_closed apply_closed transitivity check_in_M
    by simp
  ultimately
  show ?thesis
    using assms opname_check_abs[of f] sats_opname_check_fm
        one_in_M transitivity
    Replace_relativized_in_M[of "opname_check_fm(3,2,0,1)" "[f,\<one>]" A "is_opname_check(f)"
                    "\<lambda>x. opair_name(check(x),f`x)"]
    by simp
qed

theorem choice_in_MG:
  assumes "choice_ax(##M)"
  shows "choice_ax(##M[G])"
proof -
  {
    fix a
    assume "a\<in>M[G]"
    then
    obtain \<tau> where "\<tau>\<in>M" "val(P,G,\<tau>) = a"
      using GenExt_def by auto
    with \<open>\<tau>\<in>M\<close>
    have "domain(\<tau>)\<in>M"
      using domain_closed by simp
    then
    obtain s \<alpha> where "s\<in>surj(\<alpha>,domain(\<tau>))" "Ord(\<alpha>)" "s\<in>M" "\<alpha>\<in>M"
      using assms choice_ax_abs by auto
    then
    have "\<alpha>\<in>M[G]"
      using M_subset_MG generic one_in_G subsetD by blast
    let ?A="domain(\<tau>)\<times>P"
    let ?g = "{opair_name(check(\<beta>),s`\<beta>). \<beta>\<in>\<alpha>}"
    have "?g \<in> M" using \<open>s\<in>M\<close> \<open>\<alpha>\<in>M\<close> repl_opname_check by simp
    let ?f_dot="{\<langle>opair_name(check(\<beta>),s`\<beta>),\<one>\<rangle>. \<beta>\<in>\<alpha>}"
    have "?f_dot = ?g \<times> {\<one>}" by blast
    from one_in_M have "{\<one>} \<in> M" using singleton_closed by simp
    define f where
      "f \<equiv> val(P,G,?f_dot)"
    from \<open>{\<one>}\<in>M\<close> \<open>?g\<in>M\<close> \<open>?f_dot = ?g\<times>{\<one>}\<close>
    have "?f_dot\<in>M"
      using cartprod_closed by simp
    then
    have "f \<in> M[G]"
      unfolding f_def by (blast intro:GenExtI)
    have "f = {val(P,G,opair_name(check(\<beta>),s`\<beta>)) . \<beta>\<in>\<alpha>}"
      unfolding f_def using val_RepFun_one by simp
    also
    have "... = {\<langle>\<beta>,val(P,G,s`\<beta>)\<rangle> . \<beta>\<in>\<alpha>}"
      using val_opair_name valcheck generic one_in_G one_in_P by simp
    finally
    have "f = {\<langle>\<beta>,val(P,G,s`\<beta>)\<rangle> . \<beta>\<in>\<alpha>}" .
    then
    have 1: "domain(f) = \<alpha>" "function(f)"
      unfolding function_def by auto
    have 2: "y \<in> a \<Longrightarrow> \<exists>x\<in>\<alpha>. f ` x = y" for y
    proof -
      fix y
      assume
        "y \<in> a"
      with \<open>val(P,G,\<tau>) = a\<close>
      obtain \<sigma> where  "\<sigma>\<in>domain(\<tau>)" "val(P,G,\<sigma>) = y"
        using elem_of_val[of y _ \<tau>] by blast
      with \<open>s\<in>surj(\<alpha>,domain(\<tau>))\<close>
      obtain \<beta> where "\<beta>\<in>\<alpha>" "s`\<beta> = \<sigma>"
        unfolding surj_def by auto
      with \<open>val(P,G,\<sigma>) = y\<close>
      have "val(P,G,s`\<beta>) = y"
        by simp
      with \<open>f = {\<langle>\<beta>,val(P,G,s`\<beta>)\<rangle> . \<beta>\<in>\<alpha>}\<close> \<open>\<beta>\<in>\<alpha>\<close>
      have "\<langle>\<beta>,y\<rangle>\<in>f"
        by auto
      with \<open>function(f)\<close>
      have "f`\<beta> = y"
        using function_apply_equality by simp
      with \<open>\<beta>\<in>\<alpha>\<close> show
        "\<exists>\<beta>\<in>\<alpha>. f ` \<beta> = y"
        by auto
    qed
    then
    have "\<exists>\<alpha>\<in>(M[G]). \<exists>f'\<in>(M[G]). Ord(\<alpha>) \<and> f' \<in> surj(\<alpha>,a)"
    proof (cases "a=0")
      case True
      then
      show ?thesis
        unfolding surj_def using zero_in_MG by auto
    next
      case False
      with \<open>a\<in>M[G]\<close>
      obtain e where "e\<in>a" "e\<in>M[G]"
        using transitivity_MG by blast
      with 1 and 2
      have "induced_surj(f,a,e) \<in> surj(\<alpha>,a)"
        using induced_surj_is_surj by simp
      moreover from \<open>f\<in>M[G]\<close> \<open>a\<in>M[G]\<close> \<open>e\<in>M[G]\<close>
      have "induced_surj(f,a,e) \<in> M[G]"
        unfolding induced_surj_def
        by (simp flip: setclass_iff)
      moreover note
        \<open>\<alpha>\<in>M[G]\<close> \<open>Ord(\<alpha>)\<close>
      ultimately show ?thesis by auto
    qed
  }
  then
  show ?thesis using mgzf.choice_ax_abs by simp
qed

end \<comment> \<open>\<^locale>\<open>G_generic\<close>\<close>

end