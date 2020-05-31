section\<open>Relative, Choice-less Cardinal Numbers\<close>

theory Cardinal_Relative
  imports
    Least "../Tools/Try0"
begin

hide_const L

definition
  eqpoll_rel   :: "[i=>o,i,i] => o" where
  "eqpoll_rel(M,A,B) \<equiv> \<exists>f[M]. bijection(M,A,B,f)"

definition
  lepoll_rel   :: "[i=>o,i,i] => o" where
  "lepoll_rel(M,A,B) \<equiv> \<exists>f[M]. injection(M,A,B,f)"

definition
  lesspoll_rel :: "[i=>o,i,i] => o" where
  "lesspoll_rel(M,A,B) \<equiv> lepoll_rel(M,A,B) & ~(eqpoll_rel(M,A,B))"

definition
  is_cardinal :: "[i\<Rightarrow>o,i,i]\<Rightarrow>o"  where
  "is_cardinal(M,A,\<kappa>) \<equiv> least(M, \<lambda>i. M(i) \<and> eqpoll_rel(M,i,A), \<kappa>)"

definition
  Finite_rel   :: "[i\<Rightarrow>o,i]=>o"  where
  "Finite_rel(M,A) \<equiv> \<exists>om[M]. \<exists>n[M]. omega(M,om) \<and> n\<in>om \<and> eqpoll_rel(M,A,n)"

definition \<comment> \<open>Perhaps eliminate in favor of the Discipline\<close>
  Card_rel     :: "[i\<Rightarrow>o,i]=>o"  where
  "Card_rel(M,i) \<equiv> is_cardinal(M,i,i)"

locale M_cardinals = M_ordertype + M_trancl +
  assumes
  id_separation: "M(A) \<Longrightarrow> separation(M, \<lambda>z. \<exists>x\<in>A. z = \<langle>x, x\<rangle>)"
  and
  if_then_replacement: "M(f) \<Longrightarrow> M(g) \<Longrightarrow>
     strong_replacement(M, \<lambda>x y. y = <x,if x \<in> A then f`x else g`x>)"
begin

abbreviation
  Eqpoll_rel   :: "[i,i] => o"     (infixl \<open>\<approx>r\<close> 50)  where
  "A \<approx>r B \<equiv> eqpoll_rel(M,A,B)"

abbreviation
  Lepoll_rel   :: "[i,i] => o"     (infixl \<open>\<lesssim>r\<close> 50)  where
  "A \<lesssim>r B \<equiv> lepoll_rel(M,A,B)"

abbreviation
  Lesspoll_rel :: "[i,i] => o"     (infixl \<open>\<prec>r\<close> 50)  where
  "A \<prec>r B \<equiv> lesspoll_rel(M,A,B)"

definition \<comment> \<open>Perhaps eliminate in favor of the Discipline\<close>
  Card_rel     :: "i=>o"  where
  "Card_rel(i) \<equiv> is_cardinal(M,i,i)"

lemma is_cardinal_imp_Least:
  assumes "is_cardinal(M,A,\<kappa>)" "M(A)" "M(\<kappa>)" 
  shows "\<kappa> = (\<mu> i. M(i) \<and> i \<approx>r A)"
  using assms unfolding is_cardinal_def
  by (drule_tac least_abs[THEN iffD1, rule_format, rotated 2, of "\<lambda>x. M(x) \<and> x \<approx>r A"])
    simp_all

(* TO DO: Write a more general version, "least_Least" in Least.thy *)
lemma is_cardinal_iff_Least:
  assumes "M(A)" "M(\<kappa>)"
  shows "is_cardinal(M,A,\<kappa>) \<longleftrightarrow> \<kappa> = (\<mu> i. M(i) \<and> i \<approx>r A)"
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
  assumes "g \<in> inj(Y,X)" "A\<noteq>0" "\<forall>a\<in>A. a \<subseteq> Y"
  shows "g``(\<Inter>A) = (\<Inter>a\<in>A. g``a)"
proof (intro equalityI subsetI)
  fix x
  from assms
  obtain a where "a\<in>A" by blast
  moreover
  assume "x \<in> (\<Inter>a\<in>A. g `` a)"
  ultimately
  have x_in_im: "x \<in> g``y" if "y\<in>A" for y
    using that by auto
  have exists: "\<exists>z \<in> y. x = g`z" if "y\<in>A" for y
  proof -
    note that
    moreover from this and x_in_im
    have "x \<in> g``y" by simp
    moreover from calculation
    have "x \<in> g``y" by simp
    moreover
    note assms
    ultimately
    show ?thesis
      using image_fun[OF inj_is_fun] by auto
  qed
  with \<open>a\<in>A\<close>
  obtain z where "z \<in> a" "x = g`z" by auto
  moreover
  have "z \<in> y" if "y\<in>A" for y
  proof -
    from that and exists
    obtain w where "w \<in> y" "x = g`w" by auto
    moreover from this \<open>x = g`z\<close> assms that \<open>a\<in>A\<close> \<open>z\<in>a\<close>
    have "z = w" unfolding inj_def by blast
    ultimately
    show ?thesis by simp
  qed
  moreover
  note assms
  moreover from calculation
  have "z \<in> \<Inter>A" by auto
  moreover from calculation
  have "z \<in> Y" by blast
  ultimately
  show "x \<in> g `` (\<Inter>A)"
    using inj_is_fun[THEN funcI, of g] by fast
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
    using inj_Inter[of g Y X "{Y-f``a. a\<in>A}" ] by fastforce
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

lemma bij_imp_eqpoll_rel:
  assumes "f \<in> bij(A,B)" "M(f)" "M(A)" "M(B)"
  shows "A \<approx>r B"
  using assms unfolding eqpoll_rel_def by auto

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

lemma eqpoll_rel_refl: "M(A) \<Longrightarrow> A \<approx>r A"
  using bij_imp_eqpoll_rel[OF id_bij, OF id_closed] .

lemma eqpoll_rel_sym: "X \<approx>r Y \<Longrightarrow> M(X) \<Longrightarrow> M(Y) \<Longrightarrow>  Y \<approx>r X"
  unfolding eqpoll_rel_def using converse_closed
  by (auto intro: bij_converse_bij)

lemma eqpoll_rel_trans [trans]:
  "[|X \<approx>r Y;  Y \<approx>r Z;  M(X); M(Y) ; M(Z) |] ==> X \<approx>r Z"
  unfolding eqpoll_rel_def by (auto intro: comp_bij)

(** Le-pollence is a partial ordering **)

lemma subset_imp_lepoll_rel: "X \<subseteq> Y \<Longrightarrow> M(X) \<Longrightarrow> M(Y) \<Longrightarrow> X \<lesssim>r Y"
  unfolding lepoll_rel_def using id_subset_inj id_closed
  by simp blast

lemmas lepoll_rel_refl = subset_refl [THEN subset_imp_lepoll_rel, simp]

lemmas le_imp_lepoll_rel = le_imp_subset [THEN subset_imp_lepoll_rel]

lemma eqpoll_rel_imp_lepoll_rel: "M(X) \<Longrightarrow> M(Y) \<Longrightarrow> X \<approx>r Y ==> X \<lesssim>r Y"
  unfolding eqpoll_rel_def bij_def lepoll_rel_def using bij_is_inj
  by (auto)

lemma lepoll_rel_trans [trans]:
  assumes
    "X \<lesssim>r Y" "Y \<lesssim>r Z" "M(X)" "M(Y)" "M(Z)"
  shows
    "X \<lesssim>r Z"
  using assms unfolding lepoll_rel_def
  by (auto intro: comp_inj)

lemma eq_lepoll_rel_trans [trans]:
  assumes
    "X \<approx>r Y"  "Y \<lesssim>r Z" "M(X)" "M(Y)" "M(Z)"
  shows
    "X \<lesssim>r Z"
  using assms
  by (blast intro: eqpoll_rel_imp_lepoll_rel lepoll_rel_trans)

lemma lepoll_rel_eq_trans [trans]:
  assumes "X \<lesssim>r Y"  "Y \<approx>r Z" "M(X)" "M(Y)" "M(Z)"
  shows "X \<lesssim>r Z"
  using assms
  eqpoll_rel_imp_lepoll_rel[of Y Z] lepoll_rel_trans[of X Y Z]
  by simp

(*Antisymmetry law*)
lemma eqpoll_relI: "\<lbrakk> X \<lesssim>r Y; Y \<lesssim>r X; M(X) ; M(Y) \<rbrakk> \<Longrightarrow> X \<approx>r Y"
  unfolding lepoll_rel_def eqpoll_rel_def using schroeder_bernstein_closed
  by auto

lemma eqpoll_relE:
  "[| X \<approx>r Y; [| X \<lesssim>r Y; Y \<lesssim>r X |] ==> P ;  M(X) ; M(Y) |] ==> P"
  by (blast intro: eqpoll_rel_imp_lepoll_rel eqpoll_rel_sym)

lemma eqpoll_rel_iff: "M(X) \<Longrightarrow> M(Y) \<Longrightarrow> X \<approx>r Y \<longleftrightarrow> X \<lesssim>r Y & Y \<lesssim>r X"
  by (blast intro: eqpoll_relI elim: eqpoll_relE)

lemma lepoll_rel_0_is_0: "A \<lesssim>r 0 \<Longrightarrow> M(A) \<Longrightarrow> A = 0"
  unfolding lepoll_rel_def
  by (cases "A=0") (auto simp add: inj_def)

(* \<^term>\<open>M(Y) \<Longrightarrow> 0 \<lesssim>r Y\<close> *)
lemmas empty_lepoll_relI = empty_subsetI [THEN subset_imp_lepoll_rel, OF nonempty]

lemma lepoll_rel_0_iff: "M(A) \<Longrightarrow> A \<lesssim>r 0 \<longleftrightarrow> A=0"
  by (blast intro: lepoll_rel_0_is_0 lepoll_rel_refl)

lemma Un_lepoll_rel_Un:
  "[| A \<lesssim>r B; C \<lesssim>r D; B \<inter> D = 0; M(A); M(B); M(C); M(D) |] ==> A \<union> C \<lesssim>r B \<union> D"
  unfolding lepoll_rel_def using inj_disjoint_Un[of _ A B _ C D] if_then_replacement
  apply (auto)
  apply (rule, assumption)
  apply (auto intro!:lam_closed elim:transM)+
  done

lemma eqpoll_rel_0_is_0: "A \<approx>r 0 \<Longrightarrow> M(A) \<Longrightarrow> A = 0"
  using eqpoll_rel_imp_lepoll_rel lepoll_rel_0_is_0 nonempty
  by blast

lemma eqpoll_rel_0_iff: "M(A) \<Longrightarrow> A \<approx>r 0 \<longleftrightarrow> A=0"
  by (blast intro: eqpoll_rel_0_is_0 eqpoll_rel_refl)

lemma eqpoll_rel_disjoint_Un:
  "[| A \<approx>r B;  C \<approx>r D;  A \<inter> C = 0;  B \<inter> D = 0; M(A); M(B); M(C) ; M(D) |]
     ==> A \<union> C \<approx>r B \<union> D"
  unfolding eqpoll_rel_def by (auto intro: bij_disjoint_Un)

subsection\<open>lesspoll_rel: contributions by Krzysztof Grabczewski\<close>

lemma lesspoll_rel_not_refl: "M(i) \<Longrightarrow> ~ (i \<prec>r i)"
  by (simp add: lesspoll_rel_def eqpoll_rel_refl)

lemma lesspoll_rel_irrefl: "i \<prec>r i ==> M(i) \<Longrightarrow> P"
  by (simp add: lesspoll_rel_def eqpoll_rel_refl)

lemma lesspoll_rel_imp_lepoll_rel: "A \<prec>r B ==> A \<lesssim>r B"
  by (unfold lesspoll_rel_def, blast)

lemma rvimage_closed [intro,simp]:
  assumes
    "M(A)" "M(f)" "M(r)"
  shows
    "M(rvimage(A,f,r))"
  sorry

lemma lepoll_rel_well_ord: "[| A \<lesssim>r B; well_ord(B,r); M(A); M(B); M(r) |] ==> \<exists>s[M]. well_ord(A,s)"
  unfolding lepoll_rel_def by (auto intro:well_ord_rvimage)

lemma lepoll_rel_iff_leqpoll_rel: "\<lbrakk>M(A); M(B)\<rbrakk> \<Longrightarrow> A \<lesssim>r B \<longleftrightarrow> A \<prec>r B | A \<approx>r B"
  apply (unfold lesspoll_rel_def)
  apply (blast intro: eqpoll_relI elim: eqpoll_relE)
  done

(** Variations on transitivity **)

lemma lesspoll_rel_trans [trans]:
  "[| X \<prec>r Y; Y \<prec>r Z; M(X); M(Y) ; M(Z) |] ==> X \<prec>r Z"
  apply (unfold lesspoll_rel_def)
  apply (blast elim: eqpoll_relE intro: eqpoll_relI lepoll_rel_trans)
  done

lemma lesspoll_rel_trans1 [trans]:
  "[| X \<lesssim>r Y; Y \<prec>r Z; M(X); M(Y) ; M(Z) |] ==> X \<prec>r Z"
  apply (unfold lesspoll_rel_def)
  apply (blast elim: eqpoll_relE intro: eqpoll_relI lepoll_rel_trans)
  done

lemma lesspoll_rel_trans2 [trans]:
  "[|  X \<prec>r Y; Y \<lesssim>r Z; M(X); M(Y) ; M(Z)|] ==> X \<prec>r Z"
  apply (unfold lesspoll_rel_def)
  apply (blast elim: eqpoll_relE intro: eqpoll_relI lepoll_rel_trans)
  done

lemma eq_lesspoll_rel_trans [trans]:
  "[| X \<approx>r Y; Y \<prec>r Z; M(X); M(Y) ; M(Z) |] ==> X \<prec>r Z"
  by (blast intro: eqpoll_rel_imp_lepoll_rel lesspoll_rel_trans1)

lemma lesspoll_rel_eq_trans [trans]:
  "[| X \<prec>r Y; Y \<approx>r Z; M(X); M(Y) ; M(Z) |] ==> X \<prec>r Z"
  by (blast intro: eqpoll_rel_imp_lepoll_rel lesspoll_rel_trans2)

lemma is_cardinal_cong:
  assumes "X \<approx>r Y" "M(X)" "M(Y)"
  shows "\<exists>\<kappa>[M]. is_cardinal(M,X,\<kappa>) \<and> is_cardinal(M,Y,\<kappa>)"
proof -
  from assms
  have "(\<mu> i. M(i) \<and> i \<approx>r X) = (\<mu> i. M(i) \<and> i \<approx>r Y)"
    unfolding eqpoll_rel_def
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

lemma well_ord_cardinal_eqpoll_rel:
  assumes "well_ord(A,r)" shows "is_cardinal(M,A,\<kappa>) \<Longrightarrow> M(A) \<Longrightarrow> M(\<kappa>) \<Longrightarrow> M(r) \<Longrightarrow> \<kappa> \<approx>r A"
proof (subst is_cardinal_imp_Least[of A \<kappa>])
  assume "M(A)" "M(\<kappa>)" "M(r)" "is_cardinal(M,A,\<kappa>)"
  moreover from assms and calculation
  obtain f i where "M(f)" "Ord(i)" "M(i)" "f \<in> bij(A,i)"
    using ordertype_exists[of A r] ord_iso_is_bij by auto
  moreover
  have "M(\<mu> i. M(i) \<and> i \<approx>r A)"
    using Least_closed by fastforce
  ultimately
  show "(\<mu> i. M(i) \<and> i \<approx>r A) \<approx>r A"
  using assms[THEN well_ord_imp_relativized]
    LeastI[of "\<lambda>i. M(i) \<and> i \<approx>r A" i] Ord_ordertype[OF assms]
    bij_converse_bij[THEN bij_imp_eqpoll_rel, of f] by simp
qed

(* @{term"Ord(A) \<Longrightarrow> M(A) \<Longrightarrow> M(\<kappa>) \<Longrightarrow> is_cardinal(M,A,\<kappa>) \<Longrightarrow> \<kappa> \<approx>r A *)
lemmas Ord_cardinal_eqpoll_rel = well_ord_Memrel[THEN well_ord_cardinal_eqpoll_rel]

lemma is_cardinal_univalent:
  assumes "is_cardinal(M,A,\<kappa>)" "is_cardinal(M,A,\<kappa>')" "M(A)" "M(\<kappa>)" "M(\<kappa>')"
  shows "\<kappa> = \<kappa>'"
  using assms is_cardinal_imp_Least by auto

\<comment> \<open>Perhaps prove that is_cardinal is univalent?\<close>
lemma Ord_is_cardinal_idem:
  assumes "Ord(A)" "M(A)" "M(\<kappa>)" "M(\<kappa>')" "is_cardinal(M,A,\<kappa>)" "is_cardinal(M,\<kappa>,\<kappa>')"
  shows "is_cardinal(M,A,\<kappa>')"
  using assms is_cardinal_univalent
    Ord_cardinal_eqpoll_rel[THEN is_cardinal_cong, of A \<kappa>]
  by auto

lemma well_ord_is_cardinal_eqE:
  assumes
    "M(X)" "M(Y)" "M(\<kappa>)" "M(r)" "M(s)"
    and
    woX: "well_ord(X,r)" and woY: "well_ord(Y,s)" and
    eq: "is_cardinal(M,X,\<kappa>) \<and> is_cardinal(M,Y,\<kappa>)"
  shows "X \<approx>r Y"
proof -
  from assms
  have "X \<approx>r \<kappa>" by (blast intro: well_ord_cardinal_eqpoll_rel [OF woX] eqpoll_rel_sym)
  also from assms
  have "... \<approx>r Y" by (blast intro: well_ord_cardinal_eqpoll_rel [OF woY])
  finally
  show ?thesis by (simp add:assms)
qed

lemma well_ord_is_cardinal_eqpoll_rel_iff:
  assumes
    woX: "well_ord(X,r)" and woY: "well_ord(Y,s)"
    and
    "M(X)" "M(Y)" "M(\<kappa>)" "M(r)" "M(s)"
  shows "(\<exists>\<kappa>[M]. is_cardinal(M,X,\<kappa>) \<and> is_cardinal(M,Y,\<kappa>)) \<longleftrightarrow> X \<approx>r Y"
  using assms
proof (intro iffI)
  assume "X \<approx>r Y"
  with assms
  show "\<exists>\<kappa>[M]. is_cardinal(M,X,\<kappa>) \<and> is_cardinal(M,Y,\<kappa>)"
    using is_cardinal_cong by simp
qed (auto intro: well_ord_is_cardinal_eqE[of _ _ _ r s])

(** Observations from Kunen, page 28 **)

lemma Ord_is_cardinal_le: "Ord(i) \<Longrightarrow> is_cardinal(M,i,\<kappa>) \<Longrightarrow> M(i) \<Longrightarrow> M(\<kappa>) \<Longrightarrow> \<kappa> \<le> i"
  by (auto intro:Least_le[of "\<lambda>i. M(i) \<and> i \<approx>r _", of i i]
      simp add:eqpoll_rel_refl is_cardinal_iff_Least)

lemma Card_rel_is_cardinal_eq: "Card_rel(K) \<Longrightarrow> is_cardinal(M,K,K)"
  unfolding Card_rel_def .

lemma Card_relI: "\<lbrakk> Ord(i);  \<And>j. j<i \<Longrightarrow> ~(j \<approx>r i);  M(i) \<rbrakk> \<Longrightarrow> Card_rel(i)"
  unfolding Card_rel_def
  apply (rule is_cardinal_iff_Least[THEN iffD2, rule_format], simp_all)
  apply (subst Least_equality)
  apply (blast intro: eqpoll_rel_refl)+
  done

lemma Card_rel_imp_Ord: "Card_rel(i) \<Longrightarrow> M(i) \<Longrightarrow> Ord(i)"
  using is_cardinal_imp_Least[of i i] Ord_Least
  unfolding Card_rel_def
  by (simp) (erule ssubst, blast)

lemma Card_rel_cardinal_le: "Card_rel(K) \<Longrightarrow> is_cardinal(M,K,\<kappa>) \<Longrightarrow> M(K) \<Longrightarrow> M(\<kappa>) \<Longrightarrow> K \<le> \<kappa>"
  using Card_rel_imp_Ord Card_rel_is_cardinal_eq is_cardinal_univalent
  by blast

lemma Ord_is_cardinal [simp,intro!]: "is_cardinal(M,A,\<kappa>) \<Longrightarrow> M(A) \<Longrightarrow> M(\<kappa>) \<Longrightarrow> Ord(\<kappa>)"
  using is_cardinal_imp_Least by auto

text\<open>The cardinals are the initial ordinals.\<close>
lemma Card_rel_iff_initial: "M(K) \<Longrightarrow> Card_rel(K) \<longleftrightarrow> Ord(K) & (\<forall>j. j<K \<longrightarrow> ~ j \<approx>r K)"
proof -
  {
    fix j
    assume K: "M(K)" "Card_rel(K)" "j \<approx>r K"
    assume "j < K"
    also have "... = (\<mu> i. M(i) \<and> i \<approx>r K)" (is "_ = Least(?P)")
      using K is_cardinal_imp_Least by (simp add: Card_rel_def)
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
    using Card_relI[of K] Card_rel_imp_Ord[of K]
    by (intro iffI) auto
qed

lemma lt_Card_rel_imp_lesspoll_rel: "\<lbrakk> Card_rel(a); i<a; M(a) \<rbrakk> \<Longrightarrow> i \<prec>r a"
  apply (unfold lesspoll_rel_def)
  apply (frule Card_rel_iff_initial [THEN iffD1])
   apply (auto intro!: leI [THEN le_imp_lepoll_rel])
  apply (blast dest!: ltD[THEN transM])
  done

lemma Card_rel_0: "Card_rel(0)"
  apply (rule Ord_0 [THEN Card_relI])
  apply (blast elim!: ltE)+
  done

lemma Card_rel_Un: "[| Card_rel(K);  Card_rel(L); M(K); M(L) |] ==> Card_rel(K \<union> L)"
  apply (rule Ord_linear_le [of K L])
  apply (simp_all add: subset_Un_iff [THEN iffD1]  Card_rel_imp_Ord le_imp_subset
      subset_Un_iff2 [THEN iffD1])
  done

(*Infinite unions of cardinals?  See Devlin, Lemma 6.7, page 98*)

lemma is_cardinal_imp_Card_rel [simp,intro]:
  assumes "is_cardinal(M,A,\<kappa>)" "M(A)" "M(\<kappa>)"
  shows "Card_rel(\<kappa>)"
  using assms
proof (frule_tac is_cardinal_imp_Least, simp_all, simp)
   show "Card_rel(\<mu> i. M(i) \<and> i \<approx>r A)" (is "Card_rel(Least(?P))")
  proof (cases "\<exists>i. Ord (i) \<and> M(i) \<and> i \<approx>r A")
    case False
    with assms
    show ?thesis           \<comment> \<open>degenerate case\<close>
      using Least_0[of ?P] Card_rel_0 by simp
  next
    case True                         \<comment> \<open>real case: \<^term>\<open>A\<close> is isomorphic to some ordinal\<close>
    then obtain i where i: "M(i)" "Ord(i)" "i \<approx>r A" by blast
    show ?thesis
    proof (rule Card_relI[OF Ord_Least], rule_tac notI)
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
lemma is_cardinal_eq_lemma:
  assumes
    "is_cardinal(M,i,\<kappa>)" "is_cardinal(M,j,\<kappa>')"
    and
    i:"\<kappa> \<le> j" and j: "j \<le> i" 
    and
    types: "M(i)" "M(j)" "M(\<kappa>)" "M(\<kappa>')"
  shows "\<kappa>' = \<kappa>"
proof -
  from assms
  have "j \<lesssim>r i" by (rule_tac le_imp_lepoll_rel [OF j])
  moreover
  have "i \<lesssim>r j"
  proof -
    have Oi: "Ord(i)" using j by (rule le_Ord2)
    with assms
    have "i \<approx>r \<kappa>"
      using Ord_cardinal_eqpoll_rel[THEN eqpoll_rel_sym]
      by simp
    also from assms
    have "... \<lesssim>r j"
      by (blast intro: le_imp_lepoll_rel i)
    finally show "i \<lesssim>r j" using assms by simp
  qed
  moreover
  note assms(1,2) types
  moreover from calculation
  obtain \<delta> where "M(\<delta>)" "is_cardinal(M,i,\<delta>)" "is_cardinal(M,j,\<delta>)"
    using eqpoll_relI[THEN is_cardinal_cong] by auto
  ultimately
  have "\<kappa> = \<delta>" "\<kappa>'=\<delta>"
    using is_cardinal_univalent by blast+
  then
  show ?thesis by simp
qed

lemma is_cardinal_mono:
  assumes
    "is_cardinal(M,i,\<kappa>)" "is_cardinal(M,j,\<kappa>')"
    and
    ij: "i \<le> j" 
    and
    "M(i)" "M(j)" "M(\<kappa>)" "M(\<kappa>')"
shows "\<kappa> \<le> \<kappa>'"
  using Ord_is_cardinal[OF \<open> is_cardinal(M,i,\<kappa>)\<close> \<open>M(i)\<close> \<open>M(\<kappa>)\<close>]
    Ord_is_cardinal[OF \<open> is_cardinal(M,j,\<kappa>')\<close> \<open>M(j)\<close> \<open>M(\<kappa>')\<close>]
proof (cases rule: Ord_linear_le[of \<kappa> \<kappa>'])
  case le
  then
  show ?thesis by simp
next
  case ge
  have i: "Ord(i)" using ij
    by (simp add: lt_Ord)
  with assms
  have ci: "\<kappa> \<le> j"
    using Ord_is_cardinal_le[of i] ij le_trans[of \<kappa> i j]
    by simp
  from \<open>M(i)\<close> \<open>M(\<kappa>)\<close> \<open> is_cardinal(M,i,\<kappa>)\<close>
  have "is_cardinal(M,\<kappa>,\<kappa>)"
    using is_cardinal_imp_Card_rel Card_rel_is_cardinal_eq by simp
  with assms
  have "... = \<kappa>'"
    by (rule_tac is_cardinal_eq_lemma [OF _ _ ge ci])
  then
  show ?thesis
    using Ord_is_cardinal[OF \<open> is_cardinal(M,j,\<kappa>')\<close> \<open>M(j)\<close> \<open>M(\<kappa>')\<close>] by simp
qed

text\<open>Since we have \<^term>\<open>|succ(nat)| \<le> |nat|\<close>, the converse of \<open>cardinal_mono\<close> fails!\<close>
lemma cardinal_lt_imp_lt:
  assumes
    "is_cardinal(M,i,\<kappa>)" "is_cardinal(M,j,\<kappa>')"
    "\<kappa><\<kappa>'"  "Ord(i)"  "Ord(j)"
    "M(i)" "M(j)" "M(\<kappa>)" "M(\<kappa>')"
  shows
    "i < j"
  using assms
  apply (rule_tac Ord_linear2 [of i j])
  apply assumption+
  apply (erule lt_trans2 [THEN lt_irrefl])
  apply (force elim:is_cardinal_mono)
  done

lemma Card_rel_lt_imp_lt: "[| is_cardinal(M,i,\<kappa>); \<kappa> < K;  Ord(i);  Card_rel(K); M(i); M(\<kappa>); M(K) |] ==> i < K"
  using cardinal_lt_imp_lt Card_rel_imp_Ord Card_rel_is_cardinal_eq
  by blast

lemma Card_rel_lt_iff: "[| M(i); M(\<kappa>); M(K); is_cardinal(M,i,\<kappa>); Ord(i);  Card_rel(K) |] ==> (\<kappa> < K) \<longleftrightarrow> (i < K)"
  by (blast intro: Card_rel_lt_imp_lt Ord_is_cardinal_le [THEN lt_trans1])

lemma Card_rel_le_iff: "[| M(i); M(\<kappa>); M(K); is_cardinal(M,i,\<kappa>); Ord(i);  Card_rel(K) |] ==> (K \<le> \<kappa>) \<longleftrightarrow> (K \<le> i)"
  by (simp add: Card_rel_lt_iff Card_rel_imp_Ord not_lt_iff_le [THEN iff_sym])

(*Can use AC or finiteness to discharge first premise*)
lemma well_ord_lepoll_rel_imp_Card_rel_le:
  assumes
    "is_cardinal(M,A,\<kappa>)"  "is_cardinal(M,B,\<kappa>')"
    and
    wB: "well_ord(B,r)" and AB: "A \<lesssim>r B"
    and
    "M(A)" "M(B)" "M(\<kappa>)" "M(\<kappa>')" "M(r)"
  shows "\<kappa> \<le> \<kappa>'"
  using Ord_is_cardinal[OF \<open> is_cardinal(M,A,\<kappa>)\<close> \<open>M(A)\<close> \<open>M(\<kappa>)\<close>]
    Ord_is_cardinal[OF \<open> is_cardinal(M,B,\<kappa>')\<close> \<open>M(B)\<close> \<open>M(\<kappa>')\<close>]
proof (cases rule: Ord_linear_le[of \<kappa> \<kappa>'])
  case le
  then
  show ?thesis .
next
  case ge
  from lepoll_rel_well_ord [OF AB wB assms(5,6,9)]
  obtain s where s: "well_ord(A, s)" "M(s)" by auto
  from assms
  have "B  \<approx>r \<kappa>'" by (blast intro: wB eqpoll_rel_sym well_ord_cardinal_eqpoll_rel)
  also from assms
  have "... \<lesssim>r \<kappa>" by (rule_tac le_imp_lepoll_rel [OF ge])
  also from assms
  have "... \<approx>r A" by (rule_tac well_ord_cardinal_eqpoll_rel [OF s(1) _ _ _ s(2)])
  finally
  have "B \<lesssim>r A" using assms by simp
  with assms
  have "A \<approx>r B" by (blast intro: eqpoll_relI AB)
  with assms
  obtain \<delta> where "M(\<delta>)" "is_cardinal(M,A,\<delta>)" "is_cardinal(M,B,\<delta>)"
   using is_cardinal_cong[of A B] by auto
  with assms
  have "\<kappa> = \<delta>" "\<kappa>'=\<delta>"
    using is_cardinal_univalent by blast+
  then
  show ?thesis
    using Ord_is_cardinal[OF \<open> is_cardinal(M,A,\<kappa>)\<close> \<open>M(A)\<close> \<open>M(\<kappa>)\<close>] by simp
qed

(* Too many assumptions in next result
This is because of the relational form of \<open>is_cardinal\<close>,
in arguments that involve iterated cardinals (i.e. \<open>||A||\<close>).
*)
lemma lepoll_rel_is_cardinal_le: "[| A \<lesssim>r i; Ord(i) ; is_cardinal(M,A,\<kappa>);  is_cardinal(M,i,\<kappa>'); M(A); M(i); M(\<kappa>); M(\<kappa>') |] ==> \<kappa> \<le> i"
  apply (rule le_trans)
   apply (erule well_ord_Memrel[THEN [3] well_ord_lepoll_rel_imp_Card_rel_le], assumption+)
       apply (rule Memrel_closed, simp_all)
  apply (erule Ord_is_cardinal_le, simp_all)
  done

\<comment> \<open>Define a function cardinalr :: i => i, assume M(cardinalr(A)), etc.\<close>
lemma lepoll_rel_Ord_imp_eqpoll_rel: "[| A \<lesssim>r i; Ord(i) ; is_cardinal(M,A,\<kappa>);  is_cardinal(M,i,\<kappa>'); M(A); M(i); M(\<kappa>); M(\<kappa>') |] ==> \<kappa> \<approx>r A"
  using well_ord_Memrel[of i] lepoll_rel_well_ord[of A i "Memrel(i)"]
     well_ord_cardinal_eqpoll_rel[of A]
  by auto

lemma lesspoll_rel_imp_eqpoll_rel: "[| is_cardinal(M,A,\<kappa>);  is_cardinal(M,i,\<kappa>'); A \<prec>r i; Ord(i); M(A); M(i); M(\<kappa>); M(\<kappa>') |] ==> \<kappa> \<approx>r A"
  apply (unfold lesspoll_rel_def)
  apply (blast intro: lepoll_rel_Ord_imp_eqpoll_rel)
  done

lemma is_cardinal_subset_Ord: "[| is_cardinal(M,A,\<kappa>);  is_cardinal(M,i,\<kappa>'); A \<subseteq> i; Ord(i); M(A); M(i); M(\<kappa>); M(\<kappa>')|] ==> \<kappa> \<subseteq> i"
  apply (frule subset_imp_lepoll_rel [THEN lepoll_rel_is_cardinal_le])
           apply assumption+
  apply (auto intro: Ord_trans dest:ltD)
  done

lemma Finite_abs: assumes "M(A)" shows "Finite_rel(M,A) \<longleftrightarrow> Finite(A)"
  unfolding Finite_rel_def Finite_def
proof (simp, intro iffI)
  assume "\<exists>n\<in>nat. A \<approx>r n"
  then
  obtain n where "A \<approx>r n" "n\<in>nat" by blast
  with assms
  show "\<exists>n\<in>nat. A \<approx> n"
    unfolding eqpoll_def eqpoll_rel_def using nat_into_M by auto
next
  fix n
  assume "\<exists>n\<in>nat. A \<approx> n"
  then
  obtain n where "A \<approx> n" "n\<in>nat" by blast
  moreover from this
  obtain f where "f \<in> bij(A,n)" unfolding eqpoll_def by auto
  moreover
  note assms
  moreover from calculation
  have "converse(f) \<in> n\<rightarrow>A"  using bij_is_fun by simp
  moreover from calculation
  have "M(converse(f))" using transM[of _ "n\<rightarrow>A"] by simp
  moreover from calculation
  have "M(f)" using bij_is_fun
      fun_is_rel[of "f" A "\<lambda>_. n", THEN converse_converse]
      converse_closed[of "converse(f)"] by simp
  ultimately
  show "\<exists>n\<in>nat. A \<approx>r n"
    unfolding eqpoll_rel_def by (force dest:nat_into_M)
qed

end (* M_cardinals *)
end
