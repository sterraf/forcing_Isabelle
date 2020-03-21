section\<open>Relative, Choice-less Cardinal Numbers\<close>

theory Cardinal_Relative 
  imports 
    Least "../Tools/Try0"
begin

hide_const (open) L

locale M_cardinals = M_ordertype +
  assumes
  id_separation: "M(A) \<Longrightarrow> separation(M, \<lambda>z. \<exists>x\<in>A. z = \<langle>x, x\<rangle>)"
  and
  if_then_replacement: "M(f) \<Longrightarrow> M(g) \<Longrightarrow> 
     strong_replacement(M, \<lambda>x y. y = <x,if x \<in> A then f`x else g`x>)"
begin

definition
  is_eqpoll   :: "[i,i] => o"     (infixl \<open>\<approx>r\<close> 50)  where
  "A \<approx>r B \<equiv> \<exists>f[M]. bijection(M,A,B,f)"

definition
  is_lepoll   :: "[i,i] => o"     (infixl \<open>\<lesssim>r\<close> 50)  where
  "A \<lesssim>r B \<equiv> \<exists>f[M]. injection(M,A,B,f)"

definition
  is_lesspoll :: "[i,i] => o"     (infixl \<open>\<prec>r\<close> 50)  where
  "A \<prec>r B \<equiv> A \<lesssim>r B & ~(A \<approx>r B)"

definition
  is_cardinal :: "i\<Rightarrow>i\<Rightarrow>o"  (\<open>|_|r= _\<close> [0,51] 50) where
  "|A|r= \<kappa> \<equiv> least(M, \<lambda>i. M(i) \<and> i \<approx>r A, \<kappa>)"

definition
  is_Finite   :: "i=>o"  where
  "is_Finite(A) \<equiv> \<exists>om[M]. \<exists>n[M]. omega(M,om) \<and> n\<in>om \<and> A \<approx>r n"

definition
  is_Card     :: "i=>o"  where
  "is_Card(i) \<equiv> |i|r= i"

lemma is_cardinal_imp_Least:
  assumes "M(A)" "M(\<kappa>)" "|A|r= \<kappa>"
  shows "\<kappa> = (\<mu> i. M(i) \<and> i \<approx>r A)"
  using assms unfolding is_cardinal_def
  by (drule_tac least_abs[THEN iffD1, rule_format, rotated 2, of "\<lambda>x. M(x) \<and> x \<approx>r A"])
    simp_all

(* TO DO: Write a more general version, "least_Least" in Least.thy *)
lemma is_cardinal_iff_Least:
  assumes "M(A)" "M(\<kappa>)" 
  shows "|A|r= \<kappa> \<longleftrightarrow> \<kappa> = (\<mu> i. M(i) \<and> i \<approx>r A)"
  using assms is_cardinal_imp_Least[of A \<kappa>]
    least_abs[symmetric, of "\<lambda>x. M(x) \<and> x \<approx>r A" "(\<mu> i. M(i) \<and> i \<approx>r A)"]
  unfolding is_cardinal_def by auto

subsection\<open>The Schroeder-Bernstein Theorem\<close>
text\<open>See Davey and Priestly, page 106\<close>

(** Lemma: Banach's Decomposition Theorem **)

definition
  banach_functor :: "[i,i,i,i,i] \<Rightarrow> i" where
  "banach_functor(X,Y,f,g,W) \<equiv> X - g``(Y - f``W)"

lemma bnd_mono_banach_functor: "bnd_mono(X, banach_functor(X,Y,f,g))"
  unfolding bnd_mono_def banach_functor_def
  by blast

lemma inj_Inter: 
  assumes "g \<in> inj(Y,X)" "A\<noteq>0"
  shows "g``(\<Inter>A) = (\<Inter>a\<in>A. g``a)"
proof (intro equalityI subsetI)
  fix x
  from assms
  obtain a where "a\<in>A" by auto
  moreover
  assume "x \<in> (\<Inter>a\<in>A. g `` a)"
  ultimately
  have "x \<in> g``a" (* if "a\<in>A" for a *)
    (* using that *) by auto
  obtain y where "a\<in>A \<Longrightarrow> y\<in>a" "x=g`y" for a
  proof -
    {
      fix y
      have "a \<in> A \<Longrightarrow> y \<in> a" for a
        sorry
      moreover
      have "x = g ` y"
        sorry
      moreover
      note calculation
    }
    with that
    show ?thesis
      by simp
  qed
  with assms
  have "y\<in>\<Inter>A" by auto 
  with assms
  show "x \<in> g `` (\<Inter>A)"
  proof (cases "y\<in>Y", intro imageI[of y])
    case True
    with assms \<open>x = g`y\<close>
    show "\<langle>y, x\<rangle> \<in> g"
      using inj_is_fun[THEN funcI, of g] by simp 
  next
    case False
    with assms \<open>x = g`y\<close> 
    show "x \<in> g `` (\<Inter>A)" sorry
  qed
qed auto

lemma contin_banach_functor: 
  assumes "g \<in> inj(Y,X)" 
  shows "contin(banach_functor(X,Y,f,g))"
  unfolding contin_def
proof (intro allI impI)
  fix A
  assume "directed(A)"
  then
  have "A \<noteq> 0"
    unfolding directed_def ..
  have "banach_functor(X, Y, f, g, \<Union>A) = X - g``(Y - f``(\<Union>A))"
    unfolding banach_functor_def ..
  also
  have " \<dots> = X - g``(Y - (\<Union>a\<in>A. f``a))"
    by auto
  also from \<open>A\<noteq>0\<close>
  have " \<dots> = X - g``(\<Inter>a\<in>A. Y-f``a)"
    by auto
  also from \<open>A\<noteq>0\<close> and assms
  have " \<dots> = X - (\<Inter>a\<in>A. g``(Y-f``a))"
    using inj_Inter[of g Y X "{Y-f``a. a\<in>A}" ] by simp
  also from \<open>A\<noteq>0\<close>
  have " \<dots> = (\<Union>a\<in>A. X - g``(Y-f``a))" by simp
  also
  have " \<dots> = (\<Union>a\<in>A. banach_functor(X, Y, f, g, a))"
    unfolding banach_functor_def ..
  finally
  show "banach_functor(X,Y,f,g,\<Union>A) = (\<Union>a\<in>A. banach_functor(X,Y,f,g,a))" .
qed 

lemma lfp_banach_functor: 
  assumes "g\<in>inj(Y,X)"
  shows "lfp(X, banach_functor(X,Y,f,g)) = 
       (\<Union>n\<in>nat. banach_functor(X,Y,f,g)^n (0))"
  using assms lfp_eq_Union bnd_mono_banach_functor contin_banach_functor
  by simp

(* This is the biggest hole today *)
lemma lfp_banach_functor_closed: 
  assumes "M(g)" "M(X)" "M(Y)" "M(f)" "g\<in>inj(Y,X)"
  shows "M(lfp(X, banach_functor(X,Y,f,g)))" 
  sorry

lemma banach_decomposition_rel:
  "[| M(f); M(g); M(X); M(Y); f \<in> X->Y;  g \<in> inj(Y,X) |] ==>
      \<exists>XA[M]. \<exists>XB[M]. \<exists>YA[M]. \<exists>YB[M]. 
         (XA \<inter> XB = 0) & (XA \<union> XB = X) &
         (YA \<inter> YB = 0) & (YA \<union> YB = Y) &
         f``XA=YA & g``YB=XB"
  apply (intro rexI conjI)
           apply (rule_tac [6] Banach_last_equation)
           apply (rule_tac [5] refl)
          apply (assumption |
      rule inj_is_fun Diff_disjoint Diff_partition fun_is_rel 
      image_subset lfp_subset)+
  using lfp_banach_functor_closed[of g X Y f] 
  unfolding banach_functor_def by simp_all

lemma schroeder_bernstein_closed:
  "[| M(f); M(g); M(X); M(Y); f \<in> inj(X,Y);  g \<in> inj(Y,X) |] ==> \<exists>h[M]. h \<in> bij(X,Y)"
  apply (insert banach_decomposition_rel [of f g X Y])
  apply (simp add: inj_is_fun)
  apply (auto)
  apply (rule_tac x="restrict(f,XA) \<union> converse(restrict(g,YB))" in rexI)
   apply (auto intro!: restrict_bij bij_disjoint_Un intro: bij_converse_bij)
  done


(** Equipollence is an equivalence relation **)

lemma bij_imp_is_eqpoll: 
  assumes "M(f)" "M(A)" "M(B)" "f \<in> bij(A,B)"
  shows "A \<approx>r B"
  using assms unfolding is_eqpoll_def by auto

lemma id_closed: "M(A) \<Longrightarrow> M(id(A))"
proof -
  assume "M(A)"
  have "id(A) = {z\<in> A\<times>A. \<exists>x\<in>A. z=<x,x>}"
    unfolding id_def lam_def by auto
  moreover
  assume "M(A)"
  moreover from this
  have "M({z\<in> A\<times>A. \<exists>x\<in>A. z=<x,x>})" 
    using id_separation by simp
  ultimately
  show ?thesis by simp
qed

lemma is_eqpoll_refl: "M(A) \<Longrightarrow> A \<approx>r A"
  using bij_imp_is_eqpoll[OF _ _ _ id_bij, OF id_closed] .

lemma is_eqpoll_sym: "M(X) \<Longrightarrow> M(Y) \<Longrightarrow> X \<approx>r Y \<Longrightarrow> Y \<approx>r X"
  unfolding is_eqpoll_def using converse_closed
  by (auto intro: bij_converse_bij)

lemma is_eqpoll_trans [trans]:
  "[|X \<approx>r Y;  Y \<approx>r Z;  M(X); M(Y) ; M(Z) |] ==> X \<approx>r Z"
  unfolding is_eqpoll_def by (auto intro: comp_bij)

(** Le-pollence is a partial ordering **)

lemma subset_imp_is_lepoll: "M(X) \<Longrightarrow> M(Y) \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> X \<lesssim>r Y"
  unfolding is_lepoll_def using id_subset_inj id_closed
  by simp blast

lemmas is_lepoll_refl = subset_refl [THEN [3] subset_imp_is_lepoll, simp]

lemmas le_imp_is_lepoll = le_imp_subset [THEN [3] subset_imp_is_lepoll]

lemma is_eqpoll_imp_is_lepoll: "M(X) \<Longrightarrow> M(Y) \<Longrightarrow> X \<approx>r Y ==> X \<lesssim>r Y"
  unfolding is_eqpoll_def bij_def is_lepoll_def using bij_is_inj
  by (auto) 

lemma is_lepoll_trans [trans]: 
  assumes 
    "X \<lesssim>r Y" "Y \<lesssim>r Z" "M(X)" "M(Y)" "M(Z)"
  shows
    "X \<lesssim>r Z"
  using assms unfolding is_lepoll_def
  by (auto intro: comp_inj)

lemma eq_is_lepoll_trans [trans]: 
  assumes 
    "X \<approx>r Y"  "Y \<lesssim>r Z" "M(X)" "M(Y)" "M(Z)" 
  shows
    "X \<lesssim>r Z"
  using assms
  by (blast intro: is_eqpoll_imp_is_lepoll is_lepoll_trans)

lemma is_lepoll_eq_trans [trans]: 
  assumes "X \<lesssim>r Y"  "Y \<approx>r Z" "M(X)" "M(Y)" "M(Z)" 
  shows "X \<lesssim>r Z"
  using assms 
  is_eqpoll_imp_is_lepoll[of Y Z] is_lepoll_trans[of X Y Z]
  by simp

(*Antisymmetry law*)
lemma is_eqpollI: "\<lbrakk> M(X) ; M(Y); X \<lesssim>r Y; Y \<lesssim>r X \<rbrakk> \<Longrightarrow> X \<approx>r Y"
  unfolding is_lepoll_def is_eqpoll_def using schroeder_bernstein_closed
  by auto

lemma is_eqpollE:
  "[|  M(X) ; M(Y) ; X \<approx>r Y; [| X \<lesssim>r Y; Y \<lesssim>r X |] ==> P |] ==> P"
  by (blast intro: is_eqpoll_imp_is_lepoll is_eqpoll_sym)

lemma is_eqpoll_iff: "M(X) \<Longrightarrow> M(Y) \<Longrightarrow> X \<approx>r Y \<longleftrightarrow> X \<lesssim>r Y & Y \<lesssim>r X"
  by (blast intro: is_eqpollI elim: is_eqpollE)

lemma is_lepoll_0_is_0: "M(A) \<Longrightarrow> A \<lesssim>r 0 \<Longrightarrow> A = 0"
  unfolding is_lepoll_def
  by (cases "A=0") (auto simp add: inj_def)

(* \<^term>\<open>M(Y) \<Longrightarrow> 0 \<lesssim>r Y\<close> *)
lemmas empty_is_lepollI = empty_subsetI [THEN [3] subset_imp_is_lepoll, OF nonempty]

lemma is_lepoll_0_iff: "M(A) \<Longrightarrow> A \<lesssim>r 0 \<longleftrightarrow> A=0"
  by (blast intro: is_lepoll_0_is_0 is_lepoll_refl)

lemma Un_is_lepoll_Un:
  "[| M(A); M(B); M(C); M(D); A \<lesssim>r B; C \<lesssim>r D; B \<inter> D = 0 |] ==> A \<union> C \<lesssim>r B \<union> D"
  unfolding is_lepoll_def using inj_disjoint_Un[of _ A B _ C D] if_then_replacement
  apply (auto)
  apply (rule, assumption)
  apply (auto intro!:lam_closed elim:transM)+
  done

lemma is_eqpoll_0_is_0: "M(A) \<Longrightarrow> A \<approx>r 0 \<Longrightarrow> A = 0" 
  using is_eqpoll_imp_is_lepoll is_lepoll_0_is_0 nonempty
  by blast

lemma is_eqpoll_0_iff: "M(A) \<Longrightarrow> A \<approx>r 0 \<longleftrightarrow> A=0"
  by (blast intro: is_eqpoll_0_is_0 is_eqpoll_refl)

lemma is_eqpoll_disjoint_Un:
  "[| M(A); M(B); M(C) ; M(D) ; A \<approx>r B;  C \<approx>r D;  A \<inter> C = 0;  B \<inter> D = 0 |]
     ==> A \<union> C \<approx>r B \<union> D"
  unfolding is_eqpoll_def by (auto intro: bij_disjoint_Un)

subsection\<open>is_lesspoll: contributions by Krzysztof Grabczewski\<close>

lemma is_lesspoll_not_refl: "M(i) \<Longrightarrow> ~ (i \<prec>r i)"
  by (simp add: is_lesspoll_def is_eqpoll_refl)

lemma is_lesspoll_irrefl: "M(i) \<Longrightarrow> i \<prec>r i ==> P"
  by (simp add: is_lesspoll_def is_eqpoll_refl)

lemma is_lesspoll_imp_is_lepoll: "A \<prec>r B ==> A \<lesssim>r B"
  by (unfold is_lesspoll_def, blast)

lemma is_lepoll_well_ord: "[| M(A); M(B); M(r); A \<lesssim>r B; well_ord(B,r) |] ==> \<exists>s. well_ord(A,s)"
  apply (unfold is_lepoll_def)
  apply (auto intro: well_ord_rvimage)
  done

lemma is_lepoll_iff_lis_eqpoll: "\<lbrakk>M(A); M(B)\<rbrakk> \<Longrightarrow> A \<lesssim>r B \<longleftrightarrow> A \<prec>r B | A \<approx>r B"
  apply (unfold is_lesspoll_def)
  apply (blast intro: is_eqpollI elim: is_eqpollE)
  done

(** Variations on transitivity **)

lemma is_lesspoll_trans [trans]:
  "[| X \<prec>r Y; Y \<prec>r Z; M(X); M(Y) ; M(Z) |] ==> X \<prec>r Z"
  apply (unfold is_lesspoll_def)
  apply (blast elim: is_eqpollE intro: is_eqpollI is_lepoll_trans)
  done

lemma is_lesspoll_trans1 [trans]:
  "[| X \<lesssim>r Y; Y \<prec>r Z; M(X); M(Y) ; M(Z) |] ==> X \<prec>r Z"
  apply (unfold is_lesspoll_def)
  apply (blast elim: is_eqpollE intro: is_eqpollI is_lepoll_trans)
  done

lemma is_lesspoll_trans2 [trans]:
  "[|  X \<prec>r Y; Y \<lesssim>r Z; M(X); M(Y) ; M(Z)|] ==> X \<prec>r Z"
  apply (unfold is_lesspoll_def)
  apply (blast elim: is_eqpollE intro: is_eqpollI is_lepoll_trans)
  done

lemma eq_is_lesspoll_trans [trans]:
  "[| X \<approx>r Y; Y \<prec>r Z; M(X); M(Y) ; M(Z) |] ==> X \<prec>r Z"
  by (blast intro: is_eqpoll_imp_is_lepoll is_lesspoll_trans1)

lemma is_lesspoll_eq_trans [trans]:
  "[| X \<prec>r Y; Y \<approx>r Z; M(X); M(Y) ; M(Z) |] ==> X \<prec>r Z"
  by (blast intro: is_eqpoll_imp_is_lepoll is_lesspoll_trans2)

lemma is_cardinal_cong: 
  assumes "M(X)" "M(Y)" "X \<approx>r Y"
  shows "\<exists>\<kappa>[M]. |X|r= \<kappa> \<and> |Y|r= \<kappa>"
proof -
  from assms
  have "(\<mu> i. M(i) \<and> i \<approx>r X) = (\<mu> i. M(i) \<and> i \<approx>r Y)"
    unfolding is_eqpoll_def
    by (intro Least_cong) (auto intro: comp_bij bij_converse_bij)
  moreover from assms
  have "M(\<mu> i. M(i) \<and> i \<approx>r X)"
    using Least_closed by fastforce
  moreover
  note assms
  ultimately
  show ?thesis
    using is_cardinal_iff_Least
    by auto
qed 

lemma well_ord_cardinal_is_eqpoll:
  assumes "well_ord(A,r)" shows "M(A) \<Longrightarrow> M(\<kappa>) \<Longrightarrow> |A|r= \<kappa> \<Longrightarrow> \<kappa> \<approx>r A"  
proof (subst is_cardinal_imp_Least[of A \<kappa>])
  assume "M(A)" "M(\<kappa>)" "|A|r= \<kappa>"
  moreover \<comment> \<open>not sure if this is the way\<close>
  have "M(ordertype(A, r))" "M(ordermap(A, r))" sorry
  moreover
  have "M(\<mu> i. M(i) \<and> i \<approx>r A)"
    using Least_closed by fastforce
  ultimately
  show "(\<mu> i. M(i) \<and> i \<approx>r A) \<approx>r A"
  using assms[THEN well_ord_imp_relativized]
    LeastI[of "\<lambda>i. M(i) \<and> i \<approx>r A" "ordertype(A, r)"] Ord_ordertype[OF assms] 
    ordermap_bij[OF assms, THEN bij_converse_bij, THEN [4] bij_imp_is_eqpoll]
  by simp
qed

(* @{term"Ord(A) \<Longrightarrow> M(A) \<Longrightarrow> M(\<kappa>) \<Longrightarrow> |A|r= \<kappa> \<Longrightarrow> \<kappa> \<approx>r A *)
lemmas Ord_cardinal_is_eqpoll = well_ord_Memrel[THEN well_ord_cardinal_is_eqpoll]

lemma is_cardinal_univalent: 
  assumes "M(A)" "M(\<kappa>)" "M(\<kappa>')" "|A|r= \<kappa>" "|A|r= \<kappa>'"
  shows "\<kappa> = \<kappa>'"
  using assms is_cardinal_imp_Least by auto

lemma Ord_is_cardinal_idem:
  assumes "Ord(A)" "M(A)" "M(\<kappa>)" "M(\<kappa>')" "|A|r= \<kappa>" "|\<kappa>|r= \<kappa>'"
  shows "|A|r= \<kappa>'"
  using assms is_cardinal_univalent
    Ord_cardinal_is_eqpoll[THEN [3] is_cardinal_cong, of \<kappa> A]
  by auto
 
lemma well_ord_is_cardinal_eqE:
  assumes 
    "M(X)" "M(Y)" "M(\<kappa>)"
    and
    woX: "well_ord(X,r)" and woY: "well_ord(Y,s)" and 
    eq: "|X|r=\<kappa> \<and> |Y|r=\<kappa>"
  shows "X \<approx>r Y"
proof -
  from assms
  have "X \<approx>r \<kappa>" by (blast intro: well_ord_cardinal_is_eqpoll [OF woX] is_eqpoll_sym)
  also from assms
  have "... \<approx>r Y" by (blast intro: well_ord_cardinal_is_eqpoll [OF woY])
  finally
  show ?thesis by (simp add:assms)
qed

lemma well_ord_is_cardinal_is_eqpoll_iff:
  assumes 
    "M(X)" "M(Y)" "M(\<kappa>)"
    and
    woX: "well_ord(X,r)" and woY: "well_ord(Y,s)" 
  shows "(\<exists>\<kappa>[M]. |X|r=\<kappa> \<and> |Y|r=\<kappa>) \<longleftrightarrow> X \<approx>r Y"
  using assms
proof (intro iffI)
  assume "X \<approx>r Y"
  with assms
  show "\<exists>\<kappa>[M]. |X|r= \<kappa> \<and> |Y|r= \<kappa>"
    using is_cardinal_cong by simp
qed (auto intro: well_ord_is_cardinal_eqE)


(** Observations from Kunen, page 28 **)

lemma Ord_is_cardinal_le: "M(i) \<Longrightarrow> M(\<kappa>) \<Longrightarrow> Ord(i) \<Longrightarrow> |i|r= \<kappa> \<Longrightarrow> \<kappa> \<le> i"
  by (auto intro:Least_le[of "\<lambda>i. M(i) \<and> i \<approx>r _", of i i] 
      simp add:is_eqpoll_refl is_cardinal_iff_Least)

lemma is_Card_is_cardinal_eq: "is_Card(K) \<Longrightarrow> |K|r= K"
  unfolding is_Card_def .

lemma is_CardI: "\<lbrakk> M(i); Ord(i);  \<And>j. j<i \<Longrightarrow> ~(j \<approx>r i) \<rbrakk> \<Longrightarrow> is_Card(i)"
  unfolding is_Card_def
  apply (rule is_cardinal_iff_Least[THEN iffD2, rule_format], simp_all)
  apply (subst Least_equality)
  apply (blast intro: is_eqpoll_refl)+
  done

lemma is_Card_is_Ord: "M(i) \<Longrightarrow> is_Card(i) \<Longrightarrow> Ord(i)"
  using is_cardinal_imp_Least[of i i] Ord_Least
  unfolding is_Card_def 
  by (simp) (erule ssubst, blast)

lemma is_Card_cardinal_le: "M(K) \<Longrightarrow> M(\<kappa>) \<Longrightarrow> is_Card(K) \<Longrightarrow> |K|r=\<kappa> \<Longrightarrow> K \<le> \<kappa>"
  using is_Card_is_Ord is_Card_is_cardinal_eq is_cardinal_univalent
  by blast

lemma Ord_is_cardinal [simp,intro!]: "M(A) \<Longrightarrow> M(\<kappa>) \<Longrightarrow> |A|r= \<kappa> \<Longrightarrow> Ord(\<kappa>)"
  using is_cardinal_imp_Least by auto

text\<open>The cardinals are the initial ordinals.\<close>
lemma is_Card_iff_initial: "M(K) \<Longrightarrow> is_Card(K) \<longleftrightarrow> Ord(K) & (\<forall>j. j<K \<longrightarrow> ~ j \<approx>r K)"
proof -
  { 
    fix j
    assume K: "M(K)" "is_Card(K)" "j \<approx>r K"
    assume "j < K"
    also have "... = (\<mu> i. M(i) \<and> i \<approx>r K)" (is "_ = Least(?P)")
      using K is_cardinal_imp_Least by (simp add: is_Card_def)
    finally have "j < (\<mu> i. M(i) \<and> i \<approx>r K)" (is "_ < ?x") .
    then
    have "False" 
      using K less_LeastE[of "?P" j] transM[of j ?x, OF ltD] 
        Least_closed[of ?P] by simp
  }
  moreover
  assume "M(K)"
  ultimately
  show ?thesis
    using is_CardI[of K] is_Card_is_Ord[of K]
    by (intro iffI) auto
qed

lemma lt_is_Card_imp_is_lesspoll: "\<lbrakk> M(a); is_Card(a); i<a \<rbrakk> \<Longrightarrow> i \<prec>r a"
  apply (unfold is_lesspoll_def)
  apply (frule is_Card_iff_initial [THEN iffD1])
   apply (auto intro!: leI [THEN [3] le_imp_is_lepoll])
  apply (blast dest!: ltD[THEN transM])
  done

lemma is_Card_0: "is_Card(0)"
  apply (rule Ord_0 [THEN [2] is_CardI])
  apply (blast elim!: ltE)+
  done

lemma is_Card_Un: "[| M(K); M(L); is_Card(K);  is_Card(L) |] ==> is_Card(K \<union> L)"
  apply (rule Ord_linear_le [of K L])
  apply (simp_all add: subset_Un_iff [THEN iffD1]  is_Card_is_Ord le_imp_subset
      subset_Un_iff2 [THEN iffD1])
  done

(*Infinite unions of cardinals?  See Devlin, Lemma 6.7, page 98*)

lemma is_cardinal_imp_is_Card [iff]: 
  assumes "M(A)" "M(\<kappa>)" "|A|r=\<kappa>"
  shows "is_Card(\<kappa>)"
  using assms
proof (frule_tac is_cardinal_imp_Least, simp_all, simp)
   show "is_Card(\<mu> i. M(i) \<and> i \<approx>r A)" (is "is_Card(Least(?P))")
  proof (cases "\<exists>i. Ord (i) \<and> M(i) \<and> i \<approx>r A")
    case False 
    with assms
    show ?thesis           \<comment> \<open>degenerate case\<close>
      using Least_0[of ?P] is_Card_0 by simp
  next
    case True                         \<comment> \<open>real case: \<^term>\<open>A\<close> is isomorphic to some ordinal\<close>
    then obtain i where i: "M(i)" "Ord(i)" "i \<approx>r A" by blast
    show ?thesis
    proof (rule is_CardI[OF _ Ord_Least], rule_tac [2] notI)
      show "M(\<mu> i. M(i) \<and> i \<approx>r A)" 
        using \<open>M(A)\<close> Least_closed[of ?P] by simp
      fix j
      assume j: "j < (\<mu> i. M(i) \<and> i \<approx>r A)"
      then
      have "M(j)" using j[THEN ltD, THEN transM] Least_closed
        by fastforce
      assume "j \<approx>r (\<mu> i. M(i) \<and> i \<approx>r A)"
      also
      have "... \<approx>r A" using i using LeastI[of ?P] by simp
      finally 
      have "j \<approx>r A" using \<open>M(j)\<close> \<open>M(A)\<close> \<open>M(\<mu> i. M(i) \<and> i \<approx>r A)\<close>
        by simp
      with \<open>M(j)\<close>
      show "False" using less_LeastE [OF _ j] by simp
    qed 
  qed
qed

(*Kunen's Lemma 10.5*)
lemma cardinal_eq_lemma:
  assumes i:"|i| \<le> j" and j: "j \<le> i" shows "|j| = |i|"
proof (rule is_eqpollI [THEN cardinal_cong])
  show "j \<lesssim>r i" by (rule le_imp_is_lepoll [OF j])
next
  have Oi: "Ord(i)" using j by (rule le_Ord2)
  hence "i \<approx>r |i|"
    by (blast intro: Ord_cardinal_is_eqpoll is_eqpoll_sym)
  also have "... \<lesssim>r j"
    by (blast intro: le_imp_is_lepoll i)
  finally show "i \<lesssim>r j" .
qed

lemma cardinal_mono:
  assumes ij: "i \<le> j" shows "|i| \<le> |j|"
  using Ord_is_cardinal [of i] Ord_is_cardinal [of j]
proof (cases rule: Ord_linear_le)
  case le thus ?thesis .
next
  case ge
  have i: "Ord(i)" using ij
    by (simp add: lt_Ord)
  have ci: "|i| \<le> j"
    by (blast intro: Ord_cardinal_le ij le_trans i)
  have "|i| = ||i||"
    by (auto simp add: Ord_cardinal_idem i)
  also have "... = |j|"
    by (rule cardinal_eq_lemma [OF ge ci])
  finally have "|i| = |j|" .
  thus ?thesis by simp
qed

text\<open>Since we have \<^term>\<open>|succ(nat)| \<le> |nat|\<close>, the converse of \<open>cardinal_mono\<close> fails!\<close>
lemma cardinal_lt_imp_lt: "[| |i| < |j|;  Ord(i);  Ord(j) |] ==> i < j"
  apply (rule Ord_linear2 [of i j], assumption+)
  apply (erule lt_trans2 [THEN lt_irrefl])
  apply (erule cardinal_mono)
  done

lemma is_Card_lt_imp_lt: "[| M(\<kappa>); |i|r= \<kappa> ; \<kappa> < K;  Ord(i);  is_Card(K) |] ==> i < K"
  by (simp (no_asm_simp) add: cardinal_lt_imp_lt is_Card_is_Ord is_Card_is_cardinal_eq)

lemma is_Card_lt_iff: "[| Ord(i);  is_Card(K) |] ==> (|i| < K) \<longleftrightarrow> (i < K)"
  by (blast intro: is_Card_lt_imp_lt Ord_cardinal_le [THEN lt_trans1]

lemma is_Card_le_iff: "[| Ord(i);  is_Card(K) |] ==> (K \<le> |i|) \<longleftrightarrow> (K \<le> i)"
  by (simp add: is_Card_lt_iff is_Card_is_Ord Ord_is_cardinal not_lt_iff_le [THEN iff_sym])

(*Can use AC or finiteness to discharge first premise*)
lemma well_ord_is_lepoll_imp_is_Card_le:
  assumes wB: "well_ord(B,r)" and AB: "A \<lesssim>r B"
  shows "|A| \<le> |B|"
  using Ord_is_cardinal [of A] Ord_is_cardinal [of B]
proof (cases rule: Ord_linear_le)
  case le thus ?thesis .
next
  case ge
  from is_lepoll_well_ord [OF AB wB]
  obtain s where s: "well_ord(A, s)" by blast
  have "B  \<approx>r |B|" by (blast intro: wB is_eqpoll_sym well_ord_cardinal_is_eqpoll)
  also have "... \<lesssim>r |A|" by (rule le_imp_is_lepoll [OF ge])
  also have "... \<approx>r A" by (rule well_ord_cardinal_is_eqpoll [OF s])
  finally have "B \<lesssim>r A" .
  hence "A \<approx>r B" by (blast intro: is_eqpollI AB)
  hence "|A| = |B|" by (rule cardinal_cong)
  thus ?thesis by simp
qed

lemma is_lepoll_cardinal_le: "[| A \<lesssim>r i; Ord(i) |] ==> |A| \<le> i"
  apply (rule le_trans)
  apply (erule well_ord_Memrel [THEN well_ord_is_lepoll_imp_is_Card_le], assumption)
  apply (erule Ord_cardinal_le)
  done

lemma is_lepoll_Ord_imp_is_eqpoll: "[| A \<lesssim>r i; Ord(i) |] ==> |A| \<approx>r A"
  by (blast intro: is_lepoll_cardinal_le well_ord_Memrel well_ord_cardinal_is_eqpoll dest!: is_lepoll_well_ord)

lemma is_lesspoll_imp_is_eqpoll: "[| A \<prec>r i; Ord(i) |] ==> |A| \<approx>r A"
  apply (unfold is_lesspoll_def)
  apply (blast intro: is_lepoll_Ord_imp_is_eqpoll)
  done

lemma cardinal_subset_Ord: "[|A<=i; Ord(i)|] ==> |A| \<subseteq> i"
  apply (drule subset_imp_is_lepoll [THEN is_lepoll_cardinal_le])
  apply (auto simp add: lt_def)
  apply (blast intro: Ord_trans)
  done

subsection\<open>The finite cardinals\<close>

lemma cons_is_lepoll_consD:
  "[| cons(u,A) \<lesssim>r cons(v,B);  u\<notin>A;  v\<notin>B |] ==> A \<lesssim>r B"
  apply (unfold is_lepoll_def inj_def, safe)
  apply (rule_tac x = "\<lambda>x\<in>A. if f`x=v then f`u else f`x" in exI)
  apply (rule CollectI)
    (*Proving it's in the function space A->B*)
  apply (rule if_type [THEN lam_type])
  apply (blast dest: apply_funtype)
  apply (blast elim!: mem_irrefl dest: apply_funtype)
    (*Proving it's injective*)
  apply (simp (no_asm_simp))
  apply blast
  done

lemma cons_is_eqpoll_consD: "[| cons(u,A) \<approx>r cons(v,B);  u\<notin>A;  v\<notin>B |] ==> A \<approx>r B"
  apply (simp add: is_eqpoll_iff)
  apply (blast intro: cons_is_lepoll_consD)
  done

(*Lemma suggested by Mike Fourman*)
lemma succ_is_lepoll_succD: "succ(m) \<lesssim>r succ(n) ==> m \<lesssim>r n"
  apply (unfold succ_def)
  apply (erule cons_is_lepoll_consD)
  apply (rule mem_not_refl)+
  done


lemma nat_is_lepoll_imp_le:
  "m \<in> nat ==> n \<in> nat \<Longrightarrow> m \<lesssim>r n \<Longrightarrow> m \<le> n"
proof (induct m arbitrary: n rule: nat_induct)
  case 0 thus ?case by (blast intro!: nat_0_le)
next
  case (succ m)
  show ?case  using \<open>n \<in> nat\<close>
  proof (cases rule: natE)
    case 0 thus ?thesis using succ
      by (simp add: is_lepoll_def inj_def)
  next
    case (succ n') thus ?thesis using succ.hyps \<open> succ(m) \<lesssim>r n\<close>
      by (blast intro!: succ_leI dest!: succ_is_lepoll_succD)
  qed
qed

lemma nat_is_eqpoll_iff: "[| m \<in> nat; n \<in> nat |] ==> m \<approx>r n \<longleftrightarrow> m = n"
  apply (rule iffI)
  apply (blast intro: nat_is_lepoll_imp_le le_anti_sym elim!: is_eqpollE)
  apply (simp add: is_eqpoll_refl)
  done

(*The object of all this work: every natural number is a (finite) cardinal*)
lemma nat_into_is_Card:
  assumes n: "n \<in> nat" shows "is_Card(n)"
proof (unfold is_Card_def cardinal_def, rule sym)
  have "Ord(n)" using n  by auto
  moreover
  { fix i
    assume "i < n" "i \<approx>r n"
    hence False using n
      by (auto simp add: lt_nat_in_nat [THEN nat_is_eqpoll_iff])
  }
  ultimately show "(\<mu> i. i \<approx>r n) = n" by (auto intro!: Least_equality) 
qed

lemmas cardinal_0 = nat_0I [THEN nat_into_is_Card, THEN is_Card_cardinal_eq, iff]
lemmas cardinal_1 = nat_1I [THEN nat_into_is_Card, THEN is_Card_cardinal_eq, iff]


(*Part of Kunen's Lemma 10.6*)
lemma succ_is_lepoll_natE: "[| succ(n) \<lesssim>r n;  n \<in> nat |] ==> P"
  by (rule nat_is_lepoll_imp_le [THEN lt_irrefl], auto)

lemma nat_is_lepoll_imp_ex_is_eqpoll_n:
  "[| n \<in> nat;  nat \<lesssim>r X |] ==> \<exists>Y. Y \<subseteq> X & n \<approx>r Y"
  apply (unfold is_lepoll_def is_eqpoll_def)
  apply (fast del: subsetI subsetCE
      intro!: subset_SIs
      dest!: Ord_nat [THEN [2] OrdmemD, THEN [2] restrict_inj]
      elim!: restrict_bij
      inj_is_fun [THEN fun_is_rel, THEN image_subset])
  done


(** \<lesssim>r, \<prec>r and natural numbers **)

lemma is_lepoll_succ: "i \<lesssim>r succ(i)"
  by (blast intro: subset_imp_is_lepoll)

lemma is_lepoll_imp_is_lesspoll_succ:
  assumes A: "A \<lesssim>r m" and m: "m \<in> nat"
  shows "A \<prec>r succ(m)"
proof -
  { assume "A \<approx>r succ(m)"
    hence "succ(m) \<approx>r A" by (rule is_eqpoll_sym)
    also have "... \<lesssim>r m" by (rule A)
    finally have "succ(m) \<lesssim>r m" .
    hence False by (rule succ_is_lepoll_natE) (rule m) }
  moreover have "A \<lesssim>r succ(m)" by (blast intro: is_lepoll_trans A is_lepoll_succ)
  ultimately show ?thesis by (auto simp add: is_lesspoll_def)
qed

lemma is_lesspoll_succ_imp_is_lepoll:
  "[| A \<prec>r succ(m); m \<in> nat |] ==> A \<lesssim>r m"
  apply (unfold is_lesspoll_def is_lepoll_def is_eqpoll_def bij_def)
  apply (auto dest: inj_not_surj_succ)
  done

lemma is_lesspoll_succ_iff: "m \<in> nat ==> A \<prec>r succ(m) \<longleftrightarrow> A \<lesssim>r m"
  by (blast intro!: is_lepoll_imp_is_lesspoll_succ is_lesspoll_succ_imp_is_lepoll)

lemma is_lepoll_succ_disj: "[| A \<lesssim>r succ(m);  m \<in> nat |] ==> A \<lesssim>r m | A \<approx>r succ(m)"
  apply (rule disjCI)
  apply (rule is_lesspoll_succ_imp_is_lepoll)
  prefer 2 apply assumption
  apply (simp (no_asm_simp) add: is_lesspoll_def)
  done

lemma is_lesspoll_cardinal_lt: "[| A \<prec>r i; Ord(i) |] ==> |A| < i"
  apply (unfold is_lesspoll_def, clarify)
  apply (frule is_lepoll_cardinal_le, assumption)
  apply (blast intro: well_ord_Memrel well_ord_cardinal_is_eqpoll [THEN is_eqpoll_sym]
      dest: is_lepoll_well_ord  elim!: leE)
  done


subsection\<open>The first infinite cardinal: Omega, or nat\<close>

(*This implies Kunen's Lemma 10.6*)
lemma lt_not_is_lepoll:
  assumes n: "n<i" "n \<in> nat" shows "~ i \<lesssim>r n"
proof -
  { assume i: "i \<lesssim>r n"
    have "succ(n) \<lesssim>r i" using n
      by (elim ltE, blast intro: Ord_succ_subsetI [THEN subset_imp_is_lepoll])
    also have "... \<lesssim>r n" by (rule i)
    finally have "succ(n) \<lesssim>r n" .
    hence False  by (rule succ_is_lepoll_natE) (rule n) }
  thus ?thesis by auto
qed

text\<open>A slightly weaker version of \<open>nat_is_eqpoll_iff\<close>\<close>
lemma Ord_nat_is_eqpoll_iff:
  assumes i: "Ord(i)" and n: "n \<in> nat" shows "i \<approx>r n \<longleftrightarrow> i=n"
  using i nat_into_Ord [OF n]
proof (cases rule: Ord_linear_lt)
  case lt
  hence  "i \<in> nat" by (rule lt_nat_in_nat) (rule n)
  thus ?thesis by (simp add: nat_is_eqpoll_iff n)
next
  case eq
  thus ?thesis by (simp add: is_eqpoll_refl)
next
  case gt
  hence  "~ i \<lesssim>r n" using n  by (rule lt_not_is_lepoll)
  hence  "~ i \<approx>r n" using n  by (blast intro: is_eqpoll_imp_is_lepoll)
  moreover have "i \<noteq> n" using \<open>n<i\<close> by auto
  ultimately show ?thesis by blast
qed

lemma is_Card_nat: "is_Card(nat)"
proof -
  { fix i
    assume i: "i < nat" "i \<approx>r nat"
    hence "~ nat \<lesssim>r i"
      by (simp add: lt_def lt_not_is_lepoll)
    hence False using i
      by (simp add: is_eqpoll_iff)
  }
  hence "(\<mu> i. i \<approx>r nat) = nat" by (blast intro: Least_equality is_eqpoll_refl)
  thus ?thesis
    by (auto simp add: is_Card_def cardinal_def)
qed

(*Allows showing that |i| is a limit cardinal*)
lemma nat_le_cardinal: "nat \<le> i ==> nat \<le> |i|"
  apply (rule is_Card_nat [THEN is_Card_cardinal_eq, THEN subst])
  apply (erule cardinal_mono)
  done

lemma n_is_lesspoll_nat: "n \<in> nat ==> n \<prec>r nat"
  by (blast intro: Ord_nat is_Card_nat ltI lt_is_Card_imp_is_lesspoll)


subsection\<open>Towards is_Cardinal Arithmetic\<close>
  (** Congruence laws for successor, cardinal addition and multiplication **)

(*Congruence law for  cons  under equipollence*)
lemma cons_is_lepoll_cong:
  "[| A \<lesssim>r B;  b \<notin> B |] ==> cons(a,A) \<lesssim>r cons(b,B)"
  apply (unfold is_lepoll_def, safe)
  apply (rule_tac x = "\<lambda>y\<in>cons (a,A) . if y=a then b else f`y" in exI)
  apply (rule_tac d = "%z. if z \<in> B then converse (f) `z else a" in lam_injective)
  apply (safe elim!: consE')
  apply simp_all
  apply (blast intro: inj_is_fun [THEN apply_type])+
  done

lemma cons_is_eqpoll_cong:
  "[| A \<approx>r B;  a \<notin> A;  b \<notin> B |] ==> cons(a,A) \<approx>r cons(b,B)"
  by (simp add: is_eqpoll_iff cons_is_lepoll_cong)

lemma cons_is_lepoll_cons_iff:
  "[| a \<notin> A;  b \<notin> B |] ==> cons(a,A) \<lesssim>r cons(b,B)  \<longleftrightarrow>  A \<lesssim>r B"
  by (blast intro: cons_is_lepoll_cong cons_is_lepoll_consD)

lemma cons_is_eqpoll_cons_iff:
  "[| a \<notin> A;  b \<notin> B |] ==> cons(a,A) \<approx>r cons(b,B)  \<longleftrightarrow>  A \<approx>r B"
  by (blast intro: cons_is_eqpoll_cong cons_is_eqpoll_consD)

lemma singleton_is_eqpoll_1: "{a} \<approx>r 1"
  apply (unfold succ_def)
  apply (blast intro!: is_eqpoll_refl [THEN cons_is_eqpoll_cong])
  done

lemma cardinal_singleton: "|{a}| = 1"
  apply (rule singleton_is_eqpoll_1 [THEN cardinal_cong, THEN trans])
  apply (simp (no_asm) add: nat_into_is_Card [THEN is_Card_cardinal_eq])
  done

lemma not_0_is_is_lepoll_1: "A \<noteq> 0 ==> 1 \<lesssim>r A"
  apply (erule not_emptyE)
  apply (rule_tac a = "cons (x, A-{x}) " in subst)
  apply (rule_tac [2] a = "cons(0,0)" and P= "%y. y \<lesssim>r cons (x, A-{x})" in subst)
  prefer 3 apply (blast intro: cons_is_lepoll_cong subset_imp_is_lepoll, auto)
  done

(*Congruence law for  succ  under equipollence*)
lemma succ_is_eqpoll_cong: "A \<approx>r B ==> succ(A) \<approx>r succ(B)"
  apply (unfold succ_def)
  apply (simp add: cons_is_eqpoll_cong mem_not_refl)
  done

(*Congruence law for + under equipollence*)
lemma sum_is_eqpoll_cong: "[| A \<approx>r C;  B \<approx>r D |] ==> A+B \<approx>r C+D"
  apply (unfold is_eqpoll_def)
  apply (blast intro!: sum_bij)
  done

(*Congruence law for * under equipollence*)
lemma prod_is_eqpoll_cong:
  "[| A \<approx>r C;  B \<approx>r D |] ==> A*B \<approx>r C*D"
  apply (unfold is_eqpoll_def)
  apply (blast intro!: prod_bij)
  done

lemma inj_disjoint_is_eqpoll:
  "[| f \<in> inj(A,B);  A \<inter> B = 0 |] ==> A \<union> (B - range(f)) \<approx>r B"
  apply (unfold is_eqpoll_def)
  apply (rule exI)
  apply (rule_tac c = "%x. if x \<in> A then f`x else x"
      and d = "%y. if y \<in> range (f) then converse (f) `y else y"
      in lam_bijective)
  apply (blast intro!: if_type inj_is_fun [THEN apply_type])
  apply (simp (no_asm_simp) add: inj_converse_fun [THEN apply_funtype])
  apply (safe elim!: UnE')
  apply (simp_all add: inj_is_fun [THEN apply_rangeI])
  apply (blast intro: inj_converse_fun [THEN apply_type])+
  done


subsection\<open>Lemmas by Krzysztof Grabczewski\<close>

(*New proofs using cons_is_lepoll_cons. Could generalise from succ to cons.*)

text\<open>If \<^term>\<open>A\<close> has at most \<^term>\<open>n+1\<close> elements and \<^term>\<open>a \<in> A\<close>
      then \<^term>\<open>A-{a}\<close> has at most \<^term>\<open>n\<close>.\<close>
lemma Diff_sing_is_lepoll:
  "[| a \<in> A;  A \<lesssim>r succ(n) |] ==> A - {a} \<lesssim>r n"
  apply (unfold succ_def)
  apply (rule cons_is_lepoll_consD)
  apply (rule_tac [3] mem_not_refl)
  apply (erule cons_Diff [THEN ssubst], safe)
  done

text\<open>If \<^term>\<open>A\<close> has at least \<^term>\<open>n+1\<close> elements then \<^term>\<open>A-{a}\<close> has at least \<^term>\<open>n\<close>.\<close>
lemma is_lepoll_Diff_sing:
  assumes A: "succ(n) \<lesssim>r A" shows "n \<lesssim>r A - {a}"
proof -
  have "cons(n,n) \<lesssim>r A" using A
    by (unfold succ_def)
  also have "... \<lesssim>r cons(a, A-{a})"
    by (blast intro: subset_imp_is_lepoll)
  finally have "cons(n,n) \<lesssim>r cons(a, A-{a})" .
  thus ?thesis
    by (blast intro: cons_is_lepoll_consD mem_irrefl)
qed

lemma Diff_sing_is_eqpoll: "[| a \<in> A; A \<approx>r succ(n) |] ==> A - {a} \<approx>r n"
  by (blast intro!: is_eqpollI
      elim!: is_eqpollE
      intro: Diff_sing_is_lepoll is_lepoll_Diff_sing)

lemma is_lepoll_1_is_sing: "[| A \<lesssim>r 1; a \<in> A |] ==> A = {a}"
  apply (frule Diff_sing_is_lepoll, assumption)
  apply (drule is_lepoll_0_is_0)
  apply (blast elim: equalityE)
  done

lemma Un_is_lepoll_sum: "A \<union> B \<lesssim>r A+B"
  apply (unfold is_lepoll_def)
  apply (rule_tac x = "\<lambda>x\<in>A \<union> B. if x\<in>A then Inl (x) else Inr (x)" in exI)
  apply (rule_tac d = "%z. snd (z)" in lam_injective)
  apply force
  apply (simp add: Inl_def Inr_def)
  done

lemma well_ord_Un:
  "[| well_ord(X,R); well_ord(Y,S) |] ==> \<exists>T. well_ord(X \<union> Y, T)"
  by (erule well_ord_radd [THEN Un_is_lepoll_sum [THEN is_lepoll_well_ord]],
      assumption)

(*Krzysztof Grabczewski*)
lemma disj_Un_is_eqpoll_sum: "A \<inter> B = 0 ==> A \<union> B \<approx>r A + B"
  apply (unfold is_eqpoll_def)
  apply (rule_tac x = "\<lambda>a\<in>A \<union> B. if a \<in> A then Inl (a) else Inr (a)" in exI)
  apply (rule_tac d = "%z. case (%x. x, %x. x, z)" in lam_bijective)
  apply auto
  done


subsection \<open>is_Finite and infinite sets\<close>

lemma is_eqpoll_imp_is_Finite_iff: "A \<approx>r B ==> is_Finite(A) \<longleftrightarrow> is_Finite(B)"
  apply (unfold is_Finite_def)
  apply (blast intro: is_eqpoll_trans is_eqpoll_sym)
  done

lemma is_Finite_0 [simp]: "is_Finite(0)"
  apply (unfold is_Finite_def)
  apply (blast intro!: is_eqpoll_refl nat_0I)
  done

lemma is_Finite_cons: "is_Finite(x) ==> is_Finite(cons(y,x))"
  apply (unfold is_Finite_def)
  apply (case_tac "y \<in> x")
  apply (simp add: cons_absorb)
  apply (erule bexE)
  apply (rule bexI)
  apply (erule_tac [2] nat_succI)
  apply (simp (no_asm_simp) add: succ_def cons_is_eqpoll_cong mem_not_refl)
  done

lemma is_Finite_succ: "is_Finite(x) ==> is_Finite(succ(x))"
  apply (unfold succ_def)
  apply (erule is_Finite_cons)
  done

lemma is_lepoll_nat_imp_is_Finite:
  assumes A: "A \<lesssim>r n" and n: "n \<in> nat" shows "is_Finite(A)"
proof -
  have "A \<lesssim>r n \<Longrightarrow> is_Finite(A)" using n
  proof (induct n)
    case 0
    hence "A = 0" by (rule is_lepoll_0_is_0) 
    thus ?case by simp
  next
    case (succ n)
    hence "A \<lesssim>r n \<or> A \<approx>r succ(n)" by (blast dest: is_lepoll_succ_disj)
    thus ?case using succ by (auto simp add: is_Finite_def) 
  qed
  thus ?thesis using A .
qed

lemma is_lesspoll_nat_is_is_Finite:
  "A \<prec>r nat ==> is_Finite(A)"
  apply (unfold is_Finite_def)
  apply (blast dest: ltD is_lesspoll_cardinal_lt
      is_lesspoll_imp_is_eqpoll [THEN is_eqpoll_sym])
  done

lemma is_lepoll_is_Finite:
  assumes Y: "Y \<lesssim>r X" and X: "is_Finite(X)" shows "is_Finite(Y)"
proof -
  obtain n where n: "n \<in> nat" "X \<approx>r n" using X
    by (auto simp add: is_Finite_def)
  have "Y \<lesssim>r X"         by (rule Y)
  also have "... \<approx>r n"  by (rule n)
  finally have "Y \<lesssim>r n" .
  thus ?thesis using n by (simp add: is_lepoll_nat_imp_is_Finite)
qed

lemmas subset_is_Finite = subset_imp_is_lepoll [THEN is_lepoll_is_Finite]

lemma is_Finite_cons_iff [iff]: "is_Finite(cons(y,x)) \<longleftrightarrow> is_Finite(x)"
  by (blast intro: is_Finite_cons subset_is_Finite)

lemma is_Finite_succ_iff [iff]: "is_Finite(succ(x)) \<longleftrightarrow> is_Finite(x)"
  by (simp add: succ_def)

lemma is_Finite_Int: "is_Finite(A) | is_Finite(B) ==> is_Finite(A \<inter> B)"
  by (blast intro: subset_is_Finite)

lemmas is_Finite_Diff = Diff_subset [THEN subset_is_Finite]

lemma nat_le_infinite_Ord:
  "[| Ord(i);  ~ is_Finite(i) |] ==> nat \<le> i"
  apply (unfold is_Finite_def)
  apply (erule Ord_nat [THEN [2] Ord_linear2])
  prefer 2 apply assumption
  apply (blast intro!: is_eqpoll_refl elim!: ltE)
  done

lemma is_Finite_imp_well_ord:
  "is_Finite(A) ==> \<exists>r. well_ord(A,r)"
  apply (unfold is_Finite_def is_eqpoll_def)
  apply (blast intro: well_ord_rvimage bij_is_inj well_ord_Memrel nat_into_Ord)
  done

lemma succ_is_lepoll_imp_not_empty: "succ(x) \<lesssim>r y ==> y \<noteq> 0"
  by (fast dest!: is_lepoll_0_is_0)

lemma is_eqpoll_succ_imp_not_empty: "x \<approx>r succ(n) ==> x \<noteq> 0"
  by (fast elim!: is_eqpoll_sym [THEN is_eqpoll_0_is_0, THEN succ_neq_0])

lemma is_Finite_Fin_lemma [rule_format]:
  "n \<in> nat ==> \<forall>A. (A\<approx>rn & A \<subseteq> X) \<longrightarrow> A \<in> Fin(X)"
  apply (induct_tac n)
  apply (rule allI)
  apply (fast intro!: Fin.emptyI dest!: is_eqpoll_imp_is_lepoll [THEN is_lepoll_0_is_0])
  apply (rule allI)
  apply (rule impI)
  apply (erule conjE)
  apply (rule is_eqpoll_succ_imp_not_empty [THEN not_emptyE], assumption)
  apply (frule Diff_sing_is_eqpoll, assumption)
  apply (erule allE)
  apply (erule impE, fast)
  apply (drule subsetD, assumption)
  apply (drule Fin.consI, assumption)
  apply (simp add: cons_Diff)
  done

lemma is_Finite_Fin: "[| is_Finite(A); A \<subseteq> X |] ==> A \<in> Fin(X)"
  by (unfold is_Finite_def, blast intro: is_Finite_Fin_lemma)

lemma Fin_lemma [rule_format]: "n \<in> nat ==> \<forall>A. A \<approx>r n \<longrightarrow> A \<in> Fin(A)"
  apply (induct_tac n)
  apply (simp add: is_eqpoll_0_iff, clarify)
  apply (subgoal_tac "\<exists>u. u \<in> A")
  apply (erule exE)
  apply (rule Diff_sing_is_eqpoll [elim_format])
  prefer 2 apply assumption
  apply assumption
  apply (rule_tac b = A in cons_Diff [THEN subst], assumption)
  apply (rule Fin.consI, blast)
  apply (blast intro: subset_consI [THEN Fin_mono, THEN subsetD])
    (*Now for the lemma assumed above*)
  apply (unfold is_eqpoll_def)
  apply (blast intro: bij_converse_bij [THEN bij_is_fun, THEN apply_type])
  done

lemma is_Finite_into_Fin: "is_Finite(A) ==> A \<in> Fin(A)"
  apply (unfold is_Finite_def)
  apply (blast intro: Fin_lemma)
  done

lemma Fin_into_is_Finite: "A \<in> Fin(U) ==> is_Finite(A)"
  by (fast intro!: is_Finite_0 is_Finite_cons elim: Fin_induct)

lemma is_Finite_Fin_iff: "is_Finite(A) \<longleftrightarrow> A \<in> Fin(A)"
  by (blast intro: is_Finite_into_Fin Fin_into_is_Finite)

lemma is_Finite_Un: "[| is_Finite(A); is_Finite(B) |] ==> is_Finite(A \<union> B)"
  by (blast intro!: Fin_into_is_Finite Fin_UnI
      dest!: is_Finite_into_Fin
      intro: Un_upper1 [THEN Fin_mono, THEN subsetD]
      Un_upper2 [THEN Fin_mono, THEN subsetD])

lemma is_Finite_Un_iff [simp]: "is_Finite(A \<union> B) \<longleftrightarrow> (is_Finite(A) & is_Finite(B))"
  by (blast intro: subset_is_Finite is_Finite_Un)

text\<open>The converse must hold too.\<close>
lemma is_Finite_Union: "[| \<forall>y\<in>X. is_Finite(y);  is_Finite(X) |] ==> is_Finite(\<Union>(X))"
  apply (simp add: is_Finite_Fin_iff)
  apply (rule Fin_UnionI)
  apply (erule Fin_induct, simp)
  apply (blast intro: Fin.consI Fin_mono [THEN [2] rev_subsetD])
  done

(* Induction principle for is_Finite(A), by Sidi Ehmety *)
lemma is_Finite_induct [case_names 0 cons, induct set: is_Finite]:
  "[| is_Finite(A); P(0);
    !! x B.   [| is_Finite(B); x \<notin> B; P(B) |] ==> P(cons(x, B)) |]
 ==> P(A)"
  apply (erule is_Finite_into_Fin [THEN Fin_induct])
  apply (blast intro: Fin_into_is_Finite)+
  done

(*Sidi Ehmety.  The contrapositive says ~is_Finite(A) ==> ~is_Finite(A-{a}) *)
lemma Diff_sing_is_Finite: "is_Finite(A - {a}) ==> is_Finite(A)"
  apply (unfold is_Finite_def)
  apply (case_tac "a \<in> A")
  apply (subgoal_tac [2] "A-{a}=A", auto)
  apply (rule_tac x = "succ (n) " in bexI)
  apply (subgoal_tac "cons (a, A - {a}) = A & cons (n, n) = succ (n) ")
  apply (drule_tac a = a and b = n in cons_is_eqpoll_cong)
  apply (auto dest: mem_irrefl)
  done

(*Sidi Ehmety.  And the contrapositive of this says
   [| ~is_Finite(A); is_Finite(B) |] ==> ~is_Finite(A-B) *)
lemma Diff_is_Finite [rule_format]: "is_Finite(B) ==> is_Finite(A-B) \<longrightarrow> is_Finite(A)"
  apply (erule is_Finite_induct, auto)
  apply (case_tac "x \<in> A")
  apply (subgoal_tac [2] "A-cons (x, B) = A - B")
  apply (subgoal_tac "A - cons (x, B) = (A - B) - {x}", simp)
  apply (drule Diff_sing_is_Finite, auto)
  done

lemma is_Finite_RepFun: "is_Finite(A) ==> is_Finite(RepFun(A,f))"
  by (erule is_Finite_induct, simp_all)

lemma is_Finite_RepFun_iff_lemma [rule_format]:
  "[|is_Finite(x); !!x y. f(x)=f(y) ==> x=y|]
      ==> \<forall>A. x = RepFun(A,f) \<longrightarrow> is_Finite(A)"
  apply (erule is_Finite_induct)
  apply clarify
  apply (case_tac "A=0", simp)
  apply (blast del: allE, clarify)
  apply (subgoal_tac "\<exists>z\<in>A. x = f(z)")
  prefer 2 apply (blast del: allE elim: equalityE, clarify)
  apply (subgoal_tac "B = {f(u) . u \<in> A - {z}}")
  apply (blast intro: Diff_sing_is_Finite)
  apply (thin_tac "\<forall>A. P(A) \<longrightarrow> is_Finite(A)" for P)
  apply (rule equalityI)
  apply (blast intro: elim: equalityE)
  apply (blast intro: elim: equalityCE)
  done

text\<open>I don't know why, but if the premise is expressed using meta-connectives
then  the simplifier cannot prove it automatically in conditional rewriting.\<close>
lemma is_Finite_RepFun_iff:
  "(\<forall>x y. f(x)=f(y) \<longrightarrow> x=y) ==> is_Finite(RepFun(A,f)) \<longleftrightarrow> is_Finite(A)"
  by (blast intro: is_Finite_RepFun is_Finite_RepFun_iff_lemma [of _ f])

lemma is_Finite_Pow: "is_Finite(A) ==> is_Finite(Pow(A))"
  apply (erule is_Finite_induct)
  apply (simp_all add: Pow_insert is_Finite_Un is_Finite_RepFun)
  done

lemma is_Finite_Pow_imp_is_Finite: "is_Finite(Pow(A)) ==> is_Finite(A)"
  apply (subgoal_tac "is_Finite({{x} . x \<in> A})")
  apply (simp add: is_Finite_RepFun_iff )
  apply (blast intro: subset_is_Finite)
  done

lemma is_Finite_Pow_iff [iff]: "is_Finite(Pow(A)) \<longleftrightarrow> is_Finite(A)"
  by (blast intro: is_Finite_Pow is_Finite_Pow_imp_is_Finite)

lemma is_Finite_cardinal_iff:
  assumes i: "Ord(i)" shows "is_Finite(|i|) \<longleftrightarrow> is_Finite(i)"
  by (auto simp add: is_Finite_def) (blast intro: is_eqpoll_trans is_eqpoll_sym Ord_cardinal_is_eqpoll [OF i])+


(*Krzysztof Grabczewski's proof that the converse of a finite, well-ordered
  set is well-ordered.  Proofs simplified by lcp. *)

lemma nat_wf_on_converse_Memrel: "n \<in> nat ==> wf[n](converse(Memrel(n)))"
proof (induct n rule: nat_induct)
  case 0 thus ?case by (blast intro: wf_onI)
next
  case (succ x)
  hence wfx: "\<And>Z. Z = 0 \<or> (\<exists>z\<in>Z. \<forall>y. z \<in> y \<and> z \<in> x \<and> y \<in> x \<and> z \<in> x \<longrightarrow> y \<notin> Z)"
    by (simp add: wf_on_def wf_def)  \<comment> \<open>not easy to erase the duplicate \<^term>\<open>z \<in> x\<close>!\<close>
  show ?case
  proof (rule wf_onI)
    fix Z u
    assume Z: "u \<in> Z" "\<forall>z\<in>Z. \<exists>y\<in>Z. \<langle>y, z\<rangle> \<in> converse(Memrel(succ(x)))"
    show False 
    proof (cases "x \<in> Z")
      case True thus False using Z
        by (blast elim: mem_irrefl mem_asym)
    next
      case False thus False using wfx [of Z] Z
        by blast
    qed
  qed
qed

lemma nat_well_ord_converse_Memrel: "n \<in> nat ==> well_ord(n,converse(Memrel(n)))"
  apply (frule Ord_nat [THEN Ord_in_Ord, THEN well_ord_Memrel])
  apply (simp add: well_ord_def tot_ord_converse nat_wf_on_converse_Memrel) 
  done

lemma well_ord_converse:
  "[|well_ord(A,r);
        well_ord(ordertype(A,r), converse(Memrel(ordertype(A, r)))) |]
      ==> well_ord(A,converse(r))"
  apply (rule well_ord_Int_iff [THEN iffD1])
  apply (frule ordermap_bij [THEN bij_is_inj, THEN well_ord_rvimage], assumption)
  apply (simp add: rvimage_converse converse_Int converse_prod
      ordertype_ord_iso [THEN ord_iso_rvimage_eq])
  done

lemma ordertype_eq_n:
  assumes r: "well_ord(A,r)" and A: "A \<approx>r n" and n: "n \<in> nat"
  shows "ordertype(A,r) = n"
proof -
  have "ordertype(A,r) \<approx>r A"
    by (blast intro: bij_imp_is_eqpoll bij_converse_bij ordermap_bij r)
  also have "... \<approx>r n" by (rule A)
  finally have "ordertype(A,r) \<approx>r n" .
  thus ?thesis
    by (simp add: Ord_nat_is_eqpoll_iff Ord_ordertype n r)
qed

lemma is_Finite_well_ord_converse:
  "[| is_Finite(A);  well_ord(A,r) |] ==> well_ord(A,converse(r))"
  apply (unfold is_Finite_def)
  apply (rule well_ord_converse, assumption)
  apply (blast dest: ordertype_eq_n intro!: nat_well_ord_converse_Memrel)
  done

lemma nat_into_is_Finite: "n \<in> nat ==> is_Finite(n)"
  by (auto simp add: is_Finite_def intro: is_eqpoll_refl) 

lemma nat_not_is_Finite: "~ is_Finite(nat)"
proof -
  { fix n
    assume n: "n \<in> nat" "nat \<approx>r n"
    have "n \<in> nat"    by (rule n)
    also have "... = n" using n
      by (simp add: Ord_nat_is_eqpoll_iff Ord_nat)
    finally have "n \<in> n" .
    hence False
      by (blast elim: mem_irrefl)
  }
  thus ?thesis
    by (auto simp add: is_Finite_def)
qed

end (* M_eclose_pow *)
end
