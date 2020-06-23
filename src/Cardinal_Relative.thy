section\<open>Relative, Choice-less Cardinal Numbers\<close>

theory Cardinal_Relative
  imports
    Least "../Tools/Try0"
begin

hide_const L

definition
  eqpoll_rel   :: "[i=>o,i,i] => o" where
  "eqpoll_rel(M,A,B) \<equiv> \<exists>f[M]. bijection(M,A,B,f)"
  \<comment> \<open> \<^term>\<open>eqpoll_rel(M,A,B) \<equiv> \<exists>f[M]. f \<in> bij_rel(M,A,B)\<close> ?? \<close>

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
  and
  lam_if_then_replacement: "M(b) \<Longrightarrow> M(a) \<Longrightarrow> M(f) \<Longrightarrow> 
     strong_replacement(M, \<lambda>y ya. ya = \<langle>y, if y = a then b else f ` y\<rangle>)"
  and
  lam_if_then_apply_replacement: "M(f) \<Longrightarrow> M(v) \<Longrightarrow> M(u) \<Longrightarrow>
     strong_replacement(M, \<lambda>x y. y = \<langle>x,  if f ` x = v then f ` u else f ` x\<rangle>)"

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

(************* Discipline for cardinal ****************)
\<comment> \<open>Note addition to the Simpset and Claset below\<close>

lemma is_cardinal_uniqueness:
  assumes
    "M(r)" "M(d)" "M(d')"
    "is_cardinal(M,r,d)" "is_cardinal(M,r,d')"
  shows
    "d=d'"
  using assms least_abs \<comment> \<open>is using abs legit?\<close>
  unfolding is_cardinal_def
  by force \<comment> \<open>non automatic\<close>

lemma is_cardinal_witness: "M(r) \<Longrightarrow> \<exists>d[M]. is_cardinal(M,r,d)"
  using Least_closed least_abs unfolding is_cardinal_def
  by fastforce \<comment> \<open>We have to do this by hand, using axioms\<close>

definition
  cardinal_rel :: "i \<Rightarrow> i" (\<open>|_|r\<close>) where
  "|x|r \<equiv> THE d. M(d) \<and> is_cardinal(M,x,d)"

\<comment> \<open>adding closure to simpset and claset\<close>
lemma cardinal_rel_closed[intro,simp]: "M(x) \<Longrightarrow> M(|x|r)"
  unfolding cardinal_rel_def
  using theI[OF ex1I[of "\<lambda>d. M(d) \<and> is_cardinal(M,x,d)"], OF _ is_cardinal_uniqueness[of x]]
    is_cardinal_witness by auto

lemma cardinal_rel_iff:
  assumes "M(x)"  "M(d)"
  shows "is_cardinal(M,x,d) \<longleftrightarrow> d = |x|r"
proof (intro iffI)
  assume "d = |x|r"
  with assms
  show "is_cardinal(M, x, d)"
    using is_cardinal_uniqueness[of x] is_cardinal_witness
    theI[OF ex1I[of "\<lambda>d. M(d) \<and> is_cardinal(M,x,d)"], OF _ is_cardinal_uniqueness[of x]]
    unfolding cardinal_rel_def
    by auto
next
  assume "is_cardinal(M, x, d)"
  with assms
  show "d = |x|r"
    using is_cardinal_uniqueness unfolding cardinal_rel_def
    by (auto del:the_equality intro:the_equality[symmetric])
qed

lemma def_cardinal_rel: "M(x) \<Longrightarrow> |x|r = (\<mu> i. M(i) \<and> i \<approx>r x)"
  using  least_abs cardinal_rel_closed cardinal_rel_iff
  unfolding is_cardinal_def by fastforce

(***************  end Discipline  *********************)

abbreviation \<comment> \<open>Perhaps eliminate in favor of the Discipline\<close>
  Card_rel     :: "i=>o"  where
  "Card_rel(i) \<equiv> Cardinal_Relative.Card_rel(M,i)"

\<comment> \<open>same comment as the previous def\<close>
lemma def_Card_rel: "M(i) \<Longrightarrow> Card_rel(i) \<longleftrightarrow> i = |i|r"
  using cardinal_rel_iff unfolding Card_rel_def
  by simp

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

\<comment> \<open>ported from Cardinal\<close>
lemma cardinal_rel_cong: "X \<approx>r Y \<Longrightarrow> M(X) \<Longrightarrow> M(Y) \<Longrightarrow> |X|r = |Y|r"
  apply (unfold eqpoll_rel_def def_cardinal_rel)
  apply (rule Least_cong)
  apply (auto intro: comp_bij bij_converse_bij)
  done

lemma well_ord_is_cardinal_eqpoll_rel:
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
lemmas Ord_is_cardinal_eqpoll_rel = well_ord_Memrel[THEN well_ord_is_cardinal_eqpoll_rel]


(**********************************************************************)
(****************** Results imported from Cardinal.thy ****************)
(**********************************************************************)

section\<open>Porting from \<^theory>\<open>ZF.Cardinal\<close>\<close>

txt\<open>The following results were ported more or less directly from \<^theory>\<open>ZF.Cardinal\<close>\<close>

\<comment> \<open>This result relies on various closure properties and
   thus cannot be translated directly\<close>
lemma well_ord_cardinal_rel_eqpoll_rel:
  assumes r: "well_ord(A,r)" and "M(A)" "M(r)" shows "|A|r \<approx>r A"
  using assms well_ord_is_cardinal_eqpoll_rel cardinal_rel_iff
  by simp

lemmas Ord_cardinal_rel_eqpoll_rel = well_ord_Memrel[THEN well_ord_cardinal_rel_eqpoll_rel]

lemma Ord_cardinal_rel_idem: "Ord(A) \<Longrightarrow> M(A) \<Longrightarrow> ||A|r|r = |A|r"
  using cardinal_rel_closed
  by (rule_tac Ord_cardinal_rel_eqpoll_rel [THEN cardinal_rel_cong]) auto

lemma well_ord_cardinal_rel_eqE:
  assumes woX: "well_ord(X,r)" and woY: "well_ord(Y,s)" and eq: "|X|r = |Y|r"
    and types: "M(X)" "M(r)" "M(Y)" "M(s)"
  shows "X \<approx>r Y"
proof -
  from types
  have "X \<approx>r |X|r" by (blast intro: well_ord_cardinal_rel_eqpoll_rel [OF woX] eqpoll_rel_sym)
  also
  have "... = |Y|r" by (rule eq)
  also from types
  have "... \<approx>r Y" by (rule_tac well_ord_cardinal_rel_eqpoll_rel [OF woY])
  finally show ?thesis  by (simp add:types)
qed

lemma well_ord_cardinal_rel_eqpoll_rel_iff:
  "[| well_ord(X,r);  well_ord(Y,s); M(X); M(r); M(Y); M(s) |] ==> |X|r = |Y|r \<longleftrightarrow> X \<approx>r Y"
  by (blast intro: cardinal_rel_cong well_ord_cardinal_rel_eqE)

lemma Ord_cardinal_rel_le: "Ord(i) \<Longrightarrow> M(i) ==> |i|r \<le> i"
  unfolding def_cardinal_rel
  using eqpoll_rel_refl Least_le by simp

lemma Card_rel_cardinal_rel_eq: "Card_rel(K) ==> M(K) \<Longrightarrow> |K|r = K"
  apply (unfold def_Card_rel)
  apply (erule sym)
  done

lemma Card_relI: "[| Ord(i);  !!j. j<i \<Longrightarrow> M(j) ==> ~(j \<approx>r i); M(i) |] ==> Card_rel(i)"
  apply (unfold def_Card_rel def_cardinal_rel)
  apply (subst Least_equality)
     apply (blast intro: eqpoll_rel_refl)+
  done

lemma Card_rel_is_Ord: "Card_rel(i) ==> M(i) \<Longrightarrow> Ord(i)"
  apply (unfold def_Card_rel def_cardinal_rel)
  apply (erule ssubst)
  apply (rule Ord_Least)
  done

lemma Card_rel_cardinal_le: "Card_rel(K) ==> M(K) \<Longrightarrow> K \<le> |K|r"
  apply (simp (no_asm_simp) add: Card_rel_is_Ord Card_rel_cardinal_rel_eq)
  done

lemma Ord_cardinal_rel [simp,intro!]: "M(A) \<Longrightarrow> Ord(|A|r)"
  apply (unfold def_cardinal_rel)
  apply (rule Ord_Least)
  done

lemma Card_rel_iff_initial: assumes types:"M(K)"
  shows "Card_rel(K) \<longleftrightarrow> Ord(K) & (\<forall>j[M]. j<K \<longrightarrow> ~ (j \<approx>r K))"
proof -
  { fix j
    assume K: "Card_rel(K)" "M(j) \<and> j \<approx>r K"
    assume "j < K"
    also have "... = (\<mu> i. M(i) \<and> i \<approx>r K)" using K
      by (simp add: def_Card_rel def_cardinal_rel types)
    finally have "j < (\<mu> i. M(i) \<and> i \<approx>r K)" .
    then have "False" using K
      by (best intro: less_LeastE[of "\<lambda>j. M(j) \<and> j \<approx>r K"])
  }
  with types
  show ?thesis
    by (blast intro: Card_relI Card_rel_is_Ord)
qed

lemma lt_Card_rel_imp_lesspoll_rel: "[| Card_rel(a); i<a; M(a); M(i) |] ==> i \<prec>r a"
  apply (unfold lesspoll_rel_def)
  apply (frule Card_rel_iff_initial [THEN iffD1], assumption)
  apply (blast intro!: leI [THEN le_imp_lepoll_rel])
  done

lemma Card_rel_0: "Card_rel(0)"
  apply (rule Ord_0 [THEN Card_relI])
   apply (auto elim!: ltE)
  done

lemma Card_rel_Un: "[| Card_rel(K);  Card_rel(L); M(K); M(L) |] ==> Card_rel(K \<union> L)"
  apply (rule Ord_linear_le [of K L])
     apply (simp_all add: subset_Un_iff [THEN iffD1]  Card_rel_is_Ord le_imp_subset
      subset_Un_iff2 [THEN iffD1])
  done

lemma Card_rel_cardinal_rel [iff]: assumes types:"M(A)" shows "Card_rel(|A|r)"
  using assms
proof (unfold def_cardinal_rel)
  show "Card_rel(\<mu> i. M(i) \<and> i \<approx>r A)"
  proof (cases "\<exists>i[M]. Ord (i) \<and> i \<approx>r A")
    case False thus ?thesis           \<comment> \<open>degenerate case\<close>
      using Least_0[of "\<lambda>i. M(i) \<and> i \<approx>r A"] Card_rel_0
      by fastforce
  next
    case True                         \<comment> \<open>real case: \<^term>\<open>A\<close> is isomorphic to some ordinal\<close>
    then obtain i where i: "Ord(i)" "i \<approx>r A" "M(i)" by blast
    show ?thesis
    proof (rule Card_relI [OF Ord_Least], rule notI)
      fix j
      assume j: "j < (\<mu> i. M(i) \<and> i \<approx>r A)" and "M(j)"
      assume "j \<approx>r (\<mu> i. M(i) \<and> i \<approx>r A)"
      also have "... \<approx>r A" using i LeastI[of "\<lambda>i. M(i) \<and> i \<approx>r A"] by (auto)
      finally have "j \<approx>r A"
        using Least_closed[of "\<lambda>i. M(i) \<and> i \<approx>r A"] by (simp add: \<open>M(j)\<close> types)
      thus False
        using \<open>M(j)\<close> by (blast intro:less_LeastE [OF _ j])
    qed (auto intro:Least_closed)
  qed
qed

lemma cardinal_rel_eq_lemma:
  assumes i:"|i|r \<le> j" and j: "j \<le> i" and types: "M(i)" "M(j)"
  shows "|j|r = |i|r"
proof (rule eqpoll_relI [THEN cardinal_rel_cong])
  show "j \<lesssim>r i" by (rule le_imp_lepoll_rel [OF j]) (simp_all add:types)
next
  have Oi: "Ord(i)" using j by (rule le_Ord2)
  with types
  have "i \<approx>r |i|r"
    by (blast intro: Ord_cardinal_rel_eqpoll_rel eqpoll_rel_sym)
  also from types
  have "... \<lesssim>r j"
    by (blast intro: le_imp_lepoll_rel i)
  finally show "i \<lesssim>r j" by (simp_all add:types)
qed (simp_all add:types)

lemma cardinal_rel_mono:
  assumes ij: "i \<le> j" and types:"M(i)" "M(j)" shows "|i|r \<le> |j|r"
  using Ord_cardinal_rel [OF \<open>M(i)\<close>] Ord_cardinal_rel [OF \<open>M(j)\<close>]
proof (cases rule: Ord_linear_le)
  case le then show ?thesis .
next
  case ge
  have i: "Ord(i)" using ij
    by (simp add: lt_Ord)
  have ci: "|i|r \<le> j"
    by (blast intro: Ord_cardinal_rel_le ij le_trans i types)
  have "|i|r = ||i|r|r"
    by (auto simp add: Ord_cardinal_rel_idem i types)
  also have "... = |j|r"
    by (rule cardinal_rel_eq_lemma [OF ge ci]) (simp_all add:types)
  finally have "|i|r = |j|r" .
  thus ?thesis by (simp add:types)
qed

lemma cardinal_rel_lt_imp_lt: "[| |i|r < |j|r;  Ord(i);  Ord(j); M(i); M(j) |] ==> i < j"
  apply (rule Ord_linear2 [of i j], assumption+)
  apply (erule lt_trans2 [THEN lt_irrefl])
  apply (erule cardinal_rel_mono, assumption+)
  done

lemma Card_rel_lt_imp_lt: "[| |i|r < K;  Ord(i);  Card_rel(K); M(i); M(K)|] ==> i < K"
  by (simp (no_asm_simp) add: cardinal_rel_lt_imp_lt Card_rel_is_Ord Card_rel_cardinal_rel_eq)

lemma Card_rel_lt_iff: "[| Ord(i);  Card_rel(K); M(i); M(K) |] ==> (|i|r < K) \<longleftrightarrow> (i < K)"
  by (blast intro: Card_rel_lt_imp_lt Ord_cardinal_rel_le [THEN lt_trans1])

lemma Card_rel_le_iff: "[| Ord(i);  Card_rel(K); M(i); M(K) |] ==> (K \<le> |i|r) \<longleftrightarrow> (K \<le> i)"
  by (simp add: Card_rel_lt_iff Card_rel_is_Ord not_lt_iff_le [THEN iff_sym])

lemma well_ord_lepoll_rel_imp_Card_rel_le:
  assumes wB: "well_ord(B,r)" and AB: "A \<lesssim>r B"
    and
    types: "M(B)" "M(r)" "M(A)"
  shows "|A|r \<le> |B|r"
  using Ord_cardinal_rel [OF \<open>M(A)\<close>] Ord_cardinal_rel [OF \<open>M(B)\<close>]
proof (cases rule: Ord_linear_le)
  case le thus ?thesis .
next
  case ge
  from lepoll_rel_well_ord [OF AB wB]
  obtain s where s: "well_ord(A, s)" "M(s)" by (blast intro:types)
  have "B \<approx>r |B|r" by (blast intro: wB eqpoll_rel_sym well_ord_cardinal_rel_eqpoll_rel types)
  also have "... \<lesssim>r |A|r" by (rule le_imp_lepoll_rel [OF ge]) (simp_all add:types)
  also have "... \<approx>r A" by (rule well_ord_cardinal_rel_eqpoll_rel [OF s(1) _ s(2)]) (simp_all add:types)
  finally have "B \<lesssim>r A" by (simp_all add:types)
  hence "A \<approx>r B" by (blast intro: eqpoll_relI AB types)
  hence "|A|r = |B|r" by (rule cardinal_rel_cong) (simp_all add:types)
  thus ?thesis by (simp_all add:types)
qed

lemma lepoll_rel_cardinal_rel_le: "[| A \<lesssim>r i; Ord(i); M(A); M(i) |] ==> |A|r \<le> i"
  using Memrel_closed
  apply (rule_tac le_trans)
   apply (erule well_ord_Memrel [THEN well_ord_lepoll_rel_imp_Card_rel_le], assumption+)
  apply (erule Ord_cardinal_rel_le, assumption)
  done

lemma lepoll_rel_Ord_imp_eqpoll_rel: "[| A \<lesssim>r i; Ord(i); M(A); M(i) |] ==> |A|r \<approx>r A"
  by (blast intro: lepoll_rel_cardinal_rel_le well_ord_Memrel well_ord_cardinal_rel_eqpoll_rel dest!: lepoll_rel_well_ord)

lemma lesspoll_rel_imp_eqpoll_rel: "[| A \<prec>r i; Ord(i); M(A); M(i) |] ==> |A|r \<approx>r A"
  apply (unfold lesspoll_rel_def)
  apply (blast intro: lepoll_rel_Ord_imp_eqpoll_rel)
  done

lemma cardinal_rel_subset_Ord: "[|A<=i; Ord(i); M(A); M(i)|] ==> |A|r \<subseteq> i"
  apply (drule subset_imp_lepoll_rel [THEN lepoll_rel_cardinal_rel_le])
       apply (auto simp add: lt_def)
  apply (blast intro: Ord_trans)
  done

\<comment> \<open>The next lemma is the first with several porting issues\<close>
lemma cons_lepoll_rel_consD:
  "[| cons(u,A) \<lesssim>r cons(v,B);  u\<notin>A;  v\<notin>B; M(u); M(A); M(v); M(B) |] ==> A \<lesssim>r B"
apply (simp add: lepoll_rel_def, unfold inj_def, safe)
apply (rule_tac x = "\<lambda>x\<in>A. if f`x=v then f`u else f`x" in rexI)
apply (rule CollectI)
(*Proving it's in the function space A->B*)
apply (rule if_type [THEN lam_type])
apply (blast dest: apply_funtype)
apply (blast elim!: mem_irrefl dest: apply_funtype)
(*Proving it's injective*)
   apply (simp (no_asm_simp))
  using lam_if_then_apply_replacement[THEN lam_closed]
   apply (blast)
  sorry \<comment> \<open>This will work with transitivity\<close>

lemma cons_eqpoll_rel_consD: "[| cons(u,A) \<approx>r cons(v,B);  u\<notin>A;  v\<notin>B; M(u); M(A); M(v); M(B) |] ==> A \<approx>r B"
  apply (simp add: eqpoll_rel_iff)
  apply (blast intro: cons_lepoll_rel_consD)
  done

lemma succ_lepoll_rel_succD: "succ(m) \<lesssim>r succ(n) \<Longrightarrow> M(m) \<Longrightarrow> M(n) ==> m \<lesssim>r n"
  apply (unfold succ_def)
  apply (erule cons_lepoll_rel_consD)
       apply (rule mem_not_refl)+
     apply assumption+
  done

lemma nat_lepoll_rel_imp_le:
  "m \<in> nat ==> n \<in> nat \<Longrightarrow> m \<lesssim>r n \<Longrightarrow> M(m) \<Longrightarrow> M(n) \<Longrightarrow> m \<le> n"
proof (induct m arbitrary: n rule: nat_induct)
  case 0 thus ?case by (blast intro!: nat_0_le)
next
  case (succ m)
  show ?case  using \<open>n \<in> nat\<close>
  proof (cases rule: natE)
    case 0 thus ?thesis using succ
      by (simp add: lepoll_rel_def inj_def)
  next
    case (succ n') thus ?thesis using succ.hyps \<open> succ(m) \<lesssim>r n\<close>
      by (blast dest!: succ_lepoll_rel_succD)
  qed
qed

lemma nat_eqpoll_rel_iff: "[| m \<in> nat; n \<in> nat; M(m); M(n) |] ==> m \<approx>r n \<longleftrightarrow> m = n"
  apply (rule iffI)
   apply (blast intro: nat_lepoll_rel_imp_le le_anti_sym elim!: eqpoll_relE)
  apply (simp add: eqpoll_rel_refl)
  done

lemma nat_into_Card_rel:
  assumes n: "n \<in> nat" and types: "M(n)" shows "Card_rel(n)"
  using types
  apply (subst def_Card_rel, assumption)
proof (unfold def_cardinal_rel, rule sym)
  have "Ord(n)" using n  by auto
  moreover
  { fix i
    assume "i < n" "M(i)" "i \<approx>r n"
    hence False using n
      by (auto simp add: lt_nat_in_nat [THEN nat_eqpoll_rel_iff] types)
  }
  ultimately show "(\<mu> i. M(i) \<and> i \<approx>r n) = n" by (auto intro!: Least_equality types eqpoll_rel_refl)
qed

lemmas cardinal_rel_0 = nat_0I [THEN nat_into_Card_rel, THEN Card_rel_cardinal_rel_eq, simplified, iff]
lemmas cardinal_rel_1 = nat_1I [THEN nat_into_Card_rel, THEN Card_rel_cardinal_rel_eq, simplified, iff]

lemma succ_lepoll_rel_natE: "[| succ(n) \<lesssim>r n;  n \<in> nat |] ==> P"
  by (rule nat_lepoll_rel_imp_le [THEN lt_irrefl], auto)

lemma nat_lepoll_rel_imp_ex_eqpoll_rel_n:
  "[| n \<in> nat;  nat \<lesssim>r X ; M(n); M(X)|] ==> \<exists>Y[M]. Y \<subseteq> X & n \<approx>r Y"
  apply (unfold lepoll_rel_def eqpoll_rel_def, simp)
  apply (fast del: subsetI subsetCE
      intro!: subset_SIs
      dest!: Ord_nat [THEN [2] OrdmemD, THEN [2] restrict_inj]
      elim!: restrict_bij
      inj_is_fun [THEN fun_is_rel, THEN image_subset])
  done

lemma lepoll_rel_succ: "M(i) \<Longrightarrow> i \<lesssim>r succ(i)"
  by (blast intro: subset_imp_lepoll_rel)

lemma lepoll_rel_imp_lesspoll_rel_succ:
  assumes A: "A \<lesssim>r m" and m: "m \<in> nat"
    and types: "M(A)" "M(m)"
  shows "A \<prec>r succ(m)"
proof -
  { assume "A \<approx>r succ(m)"
    hence "succ(m) \<approx>r A" by (rule eqpoll_rel_sym) (auto simp add:types)
    also have "... \<lesssim>r m" by (rule A)
    finally have "succ(m) \<lesssim>r m" by (auto simp add:types)
    hence False by (rule succ_lepoll_rel_natE) (rule m) }
  moreover have "A \<lesssim>r succ(m)" by (blast intro: lepoll_rel_trans A lepoll_rel_succ types)
  ultimately show ?thesis by (auto simp add: lesspoll_rel_def)
qed

lemma lesspoll_rel_succ_imp_lepoll_rel:
  "[| A \<prec>r succ(m); m \<in> nat; M(A); M(m) |] ==> A \<lesssim>r m"
  apply (unfold lesspoll_rel_def lepoll_rel_def eqpoll_rel_def, simp, unfold bij_def)
  apply (auto dest: inj_not_surj_succ)
  sorry \<comment> \<open>the last step does not use the destruction rule\<close>
(*
\<And>f. m \<in> nat \<Longrightarrow>
         M(A) \<Longrightarrow>
         M(m) \<Longrightarrow>
         \<forall>f[M]. f \<notin> inj(A, succ(m)) \<or> f \<notin> surj(A, succ(m)) \<Longrightarrow> M(f) \<Longrightarrow> f \<in> inj(A, succ(m)) \<Longrightarrow> \<exists>f[M]. f \<in> inj(A, m)
*)
lemma lesspoll_rel_succ_iff: "m \<in> nat \<Longrightarrow> M(A) ==> A \<prec>r succ(m) \<longleftrightarrow> A \<lesssim>r m"
  by (blast intro!: lepoll_rel_imp_lesspoll_rel_succ lesspoll_rel_succ_imp_lepoll_rel)

lemma lepoll_rel_succ_disj: "[| A \<lesssim>r succ(m);  m \<in> nat; M(A) ; M(m)|] ==> A \<lesssim>r m | A \<approx>r succ(m)"
  apply (rule disjCI)
  apply (rule lesspoll_rel_succ_imp_lepoll_rel)
   prefer 2 apply assumption
  apply (simp (no_asm_simp) add: lesspoll_rel_def, assumption+)
  done

lemma lesspoll_rel_cardinal_rel_lt: "[| A \<prec>r i; Ord(i); M(A); M(i) |] ==> |A|r < i"
  apply (unfold lesspoll_rel_def, clarify)
  apply (frule lepoll_rel_cardinal_rel_le, assumption+) \<comment> \<open>because of types\<close>
  apply (blast intro: well_ord_Memrel well_ord_cardinal_rel_eqpoll_rel [THEN eqpoll_rel_sym]
      dest: lepoll_rel_well_ord  elim!: leE)
  done


lemma lt_not_lepoll_rel:
  assumes n: "n<i" "n \<in> nat"
  and types:"M(n)" "M(i)" shows "~ i \<lesssim>r n"
proof -
  { assume i: "i \<lesssim>r n"
    have "succ(n) \<lesssim>r i" using n
      by (elim ltE, blast intro: Ord_succ_subsetI [THEN subset_imp_lepoll_rel] types)
    also have "... \<lesssim>r n" by (rule i)
    finally have "succ(n) \<lesssim>r n" by (simp add:types)
    hence False  by (rule succ_lepoll_rel_natE) (rule n) }
  thus ?thesis by auto
qed

text\<open>A slightly weaker version of \<open>nat_eqpoll_rel_iff\<close>\<close>
lemma Ord_nat_eqpoll_rel_iff:
  assumes i: "Ord(i)" and n: "n \<in> nat"
    and types: "M(i)" "M(n)"
  shows "i \<approx>r n \<longleftrightarrow> i=n"
  using i nat_into_Ord [OF n]
proof (cases rule: Ord_linear_lt)
  case lt
  hence  "i \<in> nat" by (rule lt_nat_in_nat) (rule n)
  thus ?thesis by (simp add: nat_eqpoll_rel_iff n types)
next
  case eq
  thus ?thesis by (simp add: eqpoll_rel_refl types)
next
  case gt
  hence  "~ i \<lesssim>r n" using n  by (rule lt_not_lepoll_rel) (simp_all add: types)
  hence  "~ i \<approx>r n" using n  by (blast intro: eqpoll_rel_imp_lepoll_rel types)
  moreover have "i \<noteq> n" using \<open>n<i\<close> by auto
  ultimately show ?thesis by blast
qed

lemma Card_rel_nat: "Card_rel(nat)"
proof -
  { fix i
    assume i: "i < nat" "i \<approx>r nat" "M(i)"
    hence "~ nat \<lesssim>r i"
      by (simp add: lt_def lt_not_lepoll_rel)
    hence False using i
      by (simp add: eqpoll_rel_iff)
  }
  hence "(\<mu> i. M(i) \<and> i \<approx>r nat) = nat" by (blast intro: Least_equality eqpoll_rel_refl)
  thus ?thesis
    by (auto simp add: def_Card_rel def_cardinal_rel)
qed

lemma nat_le_cardinal_rel: "nat \<le> i \<Longrightarrow> M(i) ==> nat \<le> |i|r"
  apply (rule Card_rel_nat [THEN Card_rel_cardinal_rel_eq, THEN subst], simp_all)
  apply (erule cardinal_rel_mono, simp_all)
  done

lemma n_lesspoll_rel_nat: "n \<in> nat ==> n \<prec>r nat"
  by (blast intro: Card_rel_nat ltI lt_Card_rel_imp_lesspoll_rel)

lemma cons_lepoll_rel_cong:
  "[| A \<lesssim>r B;  b \<notin> B; M(A); M(B); M(b); M(a) |] ==> cons(a,A) \<lesssim>r cons(b,B)"
  apply (unfold lepoll_rel_def, safe, simp)
  apply (rule_tac x = "\<lambda>y\<in>cons (a,A) . if y=a then b else f`y" in rexI)
   apply (rule_tac d = "%z. if z \<in> B then converse (f) `z else a" in lam_injective)
    apply (safe elim!: consE')
      apply simp_all
    apply (blast intro: inj_is_fun [THEN apply_type])+
  apply (auto intro:lam_closed lam_if_then_replacement simp add:transM[of _ A])
  done

lemma cons_eqpoll_rel_cong:
  "[| A \<approx>r B;  a \<notin> A;  b \<notin> B;  M(A); M(B); M(a) ; M(b) |] ==> cons(a,A) \<approx>r cons(b,B)"
  by (simp add: eqpoll_rel_iff cons_lepoll_rel_cong)

lemma cons_lepoll_rel_cons_iff:
  "[| a \<notin> A;  b \<notin> B; M(a); M(A); M(b); M(B) |] ==> cons(a,A) \<lesssim>r cons(b,B)  \<longleftrightarrow>  A \<lesssim>r B"
  by (blast intro: cons_lepoll_rel_cong cons_lepoll_rel_consD)

lemma cons_eqpoll_rel_cons_iff:
  "[| a \<notin> A;  b \<notin> B; M(a); M(A); M(b); M(B) |] ==> cons(a,A) \<approx>r cons(b,B)  \<longleftrightarrow>  A \<approx>r B"
  by (blast intro: cons_eqpoll_rel_cong cons_eqpoll_rel_consD)

lemma singleton_eqpoll_rel_1: "M(a) \<Longrightarrow> {a} \<approx>r 1"
  apply (unfold succ_def)
  apply (blast intro!: eqpoll_rel_refl [THEN cons_eqpoll_rel_cong])
  done

lemma cardinal_rel_singleton: "M(a) \<Longrightarrow> |{a}|r = 1"
  apply (rule singleton_eqpoll_rel_1 [THEN cardinal_rel_cong, THEN trans])
     apply (simp (no_asm) add: nat_into_Card_rel [THEN Card_rel_cardinal_rel_eq])
  apply auto
  done

\<comment> \<open>From here on, problems pile up\<close>

(*

lemma not_0_is_lepoll_rel_1: "A \<noteq> 0 ==> M(A) \<Longrightarrow> 1 \<lesssim>r A"
  apply (erule not_emptyE)
  apply (rule_tac a = "cons (x, A-{x}) " in subst)
   apply (rule_tac [2] a = "cons(0,0)" and P= "%y. y \<lesssim>r cons (x, A-{x})" in subst)
    prefer 3 apply (blast intro: cons_lepoll_rel_cong subset_imp_lepoll_rel, auto)
  done

lemma succ_eqpoll_rel_cong: "A \<approx>r B \<Longrightarrow> M(A) \<Longrightarrow> M(B) ==> succ(A) \<approx>r succ(B)"
  apply (unfold succ_def)
  apply (simp add: cons_eqpoll_rel_cong mem_not_refl)
  done

lemma sum_eqpoll_rel_cong: "[| A \<approx>r C;  B \<approx>r D; M(A); M(C); M(B); M(D) |] ==> A+B \<approx>r C+D"
  apply (unfold eqpoll_rel_def)
  apply (auto intro!: sum_bij)
  done

lemma prod_eqpoll_rel_cong:
  "[| A \<approx>r C;  B \<approx>r D |] ==> A*B \<approx>r C*D"
  apply (unfold eqpoll_rel_def)
  apply (blast intro!: prod_bij)
  done

lemma inj_disjoint_eqpoll_rel:
  "[| f \<in> inj(A,B);  A \<inter> B = 0 |] ==> A \<union> (B - range(f)) \<approx>r B"
  apply (unfold eqpoll_rel_def)
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


lemma Diff_sing_lepoll_rel:
  "[| a \<in> A;  A \<lesssim>r succ(n) |] ==> A - {a} \<lesssim>r n"
  apply (unfold succ_def)
  apply (rule cons_lepoll_rel_consD)
    apply (rule_tac [3] mem_not_refl)
   apply (erule cons_Diff [THEN ssubst], safe)
  done

lemma lepoll_rel_Diff_sing:
  assumes A: "succ(n) \<lesssim>r A" shows "n \<lesssim>r A - {a}"
proof -
  have "cons(n,n) \<lesssim>r A" using A
    by (unfold succ_def)
  also have "... \<lesssim>r cons(a, A-{a})"
    by (blast intro: subset_imp_lepoll_rel)
  finally have "cons(n,n) \<lesssim>r cons(a, A-{a})" .
  thus ?thesis
    by (blast intro: cons_lepoll_rel_consD mem_irrefl)
qed

lemma Diff_sing_eqpoll_rel: "[| a \<in> A; A \<approx>r succ(n) |] ==> A - {a} \<approx>r n"
  by (blast intro!: eqpoll_relI
      elim!: eqpoll_relE
      intro: Diff_sing_lepoll_rel lepoll_rel_Diff_sing)

lemma lepoll_rel_1_is_sing: "[| A \<lesssim>r 1; a \<in> A |] ==> A = {a}"
  apply (frule Diff_sing_lepoll_rel, assumption)
  apply (drule lepoll_rel_0_is_0)
  apply (blast elim: equalityE)
  done

lemma Un_lepoll_rel_sum: "A \<union> B \<lesssim>r A+B"
  apply (unfold lepoll_rel_def)
  apply (rule_tac x = "\<lambda>x\<in>A \<union> B. if x\<in>A then Inl (x) else Inr (x)" in exI)
  apply (rule_tac d = "%z. snd (z)" in lam_injective)
   apply force
  apply (simp add: Inl_def Inr_def)
  done

lemma well_ord_Un:
  "[| well_ord(X,R); well_ord(Y,S) |] ==> \<exists>T. well_ord(X \<union> Y, T)"
  by (erule well_ord_radd [THEN Un_lepoll_rel_sum [THEN lepoll_rel_well_ord]],
      assumption)

lemma disj_Un_eqpoll_rel_sum: "A \<inter> B = 0 ==> A \<union> B \<approx>r A + B"
  apply (unfold eqpoll_rel_def)
  apply (rule_tac x = "\<lambda>a\<in>A \<union> B. if a \<in> A then Inl (a) else Inr (a)" in exI)
  apply (rule_tac d = "%z. case (%x. x, %x. x, z)" in lam_bijective)
     apply auto
  done
*)

lemma eqpoll_rel_imp_Finite_rel_iff: "A \<approx>r B ==> M(A) \<Longrightarrow> M(B) \<Longrightarrow> Finite_rel(M,A) \<longleftrightarrow> Finite_rel(M,B)"
  apply (unfold Finite_rel_def)
  apply (blast intro: eqpoll_rel_trans eqpoll_rel_sym)
  done

\<comment> \<open>It seems reasonable to have the absoluteness of \<^term>\<open>Finite\<close> here,
and deduce the rest of the results from this.

Perhaps modularize that proof to have absoluteness of injections and
bijections of finite sets (cf. @{thm lesspoll_rel_succ_imp_lepoll_rel}.\<close>

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

\<comment> \<open>In the following, I'm leaving results that involve the other
relativized cardinality notions.\<close>

(*

lemma lepoll_rel_nat_imp_Finite_rel:
  assumes A: "A \<lesssim>r n" and n: "n \<in> nat"
  and types: "M(A)" "M(n)"
  shows "Finite_rel(M,A)"
  oops

lemma lesspoll_rel_nat_is_Finite_rel:
  "A \<prec>r nat ==> M(A) \<Longrightarrow> Finite_rel(M,A)"
  oops

lemma lepoll_rel_Finite_rel:
  assumes Y: "Y \<lesssim>r X" and X: "Finite_rel(M,X)"
    and types:"M(Y)" "M(X)"
  shows "Finite_rel(M,Y)"
  oops

lemma succ_lepoll_rel_imp_not_empty: "succ(x) \<lesssim>r y ==> M(x) \<Longrightarrow> M(y) \<Longrightarrow> y \<noteq> 0"
  oops

lemma eqpoll_rel_succ_imp_not_empty: "x \<approx>r succ(n) ==> M(x) \<Longrightarrow> M(n) \<Longrightarrow> x \<noteq> 0"
  oops

lemma Finite_rel_Fin_lemma [rule_format]:
  "n \<in> nat ==> M(n) \<Longrightarrow> M(X) \<Longrightarrow> \<forall>A[M]. (A\<approx>r n & A \<subseteq> X) \<longrightarrow> A \<in> Fin(X)"
  oops

lemma Fin_lemma [rule_format]: "n \<in> nat ==> \<forall>A. A \<approx>r n \<longrightarrow> A \<in> Fin(A)"
  oops

*)

(**********************************************************************)
(**********************************************************************)

\<comment> \<open>Old ported results (using \<^term>\<open>is_cardinal\<close> instead of
\<^term>\<open>cardinal_rel\<close> now follow immediately.\<close>

lemma Ord_is_cardinal_idem:
  assumes "Ord(A)" "M(A)" "M(\<kappa>)" "M(\<kappa>')" "is_cardinal(M,A,\<kappa>)" "is_cardinal(M,\<kappa>,\<kappa>')"
  shows "is_cardinal(M,A,\<kappa>')"
  using assms Ord_cardinal_rel_idem cardinal_rel_iff by simp

lemma well_ord_is_cardinal_eqE:
  assumes
    woX: "well_ord(X,r)" and woY: "well_ord(Y,s)" and
    eq: "is_cardinal(M,X,\<kappa>) \<and> is_cardinal(M,Y,\<kappa>)"
    and
    "M(X)" "M(r)" "M(Y)" "M(s)" "M(\<kappa>)"
  shows "X \<approx>r Y"
  using assms well_ord_cardinal_rel_eqE cardinal_rel_iff by simp

lemma Ord_is_cardinal_le: "Ord(i) \<Longrightarrow> is_cardinal(M,i,\<kappa>) \<Longrightarrow> M(i) \<Longrightarrow> M(\<kappa>) \<Longrightarrow> \<kappa> \<le> i"
  using Ord_cardinal_rel_le cardinal_rel_iff by simp

lemma Ord_is_cardinal: "is_cardinal(M,A,\<kappa>) \<Longrightarrow> M(A) \<Longrightarrow> M(\<kappa>) \<Longrightarrow> Ord(\<kappa>)"
  using Ord_cardinal_rel cardinal_rel_iff by simp

lemma is_cardinal_imp_Card_rel:
  assumes "is_cardinal(M,A,\<kappa>)" "M(A)" "M(\<kappa>)"
  shows "Card_rel(\<kappa>)"
  using assms Card_rel_cardinal_rel cardinal_rel_iff by simp

lemma is_cardinal_eq_lemma:
  assumes
    "is_cardinal(M,i,\<kappa>)" "is_cardinal(M,j,\<kappa>')"
    and
    i:"\<kappa> \<le> j" and j: "j \<le> i"
    and
    types: "M(i)" "M(j)" "M(\<kappa>)" "M(\<kappa>')"
  shows "\<kappa>' = \<kappa>"
  using assms cardinal_rel_eq_lemma cardinal_rel_iff by simp

lemma is_cardinal_mono:
  assumes
    "is_cardinal(M,i,\<kappa>)" "is_cardinal(M,j,\<kappa>')"
    and
    ij: "i \<le> j"
    and
    "M(i)" "M(\<kappa>)" "M(j)" "M(\<kappa>')"
  shows "\<kappa> \<le> \<kappa>'"
  using assms cardinal_rel_mono cardinal_rel_iff by simp

lemma is_cardinal_lt_imp_lt:
  assumes
    "is_cardinal(M,i,\<kappa>)" "is_cardinal(M,j,\<kappa>')"
    "\<kappa><\<kappa>'"  "Ord(i)"  "Ord(j)"
    "M(i)" "M(\<kappa>)" "M(j)" "M(\<kappa>')"
  shows
    "i < j"
  using assms cardinal_rel_lt_imp_lt cardinal_rel_iff by simp

\<comment> \<open>This oldly ported result involves some first order reasoning
and doesn't follow as simply as the previous ones.\<close>
lemma well_ord_is_cardinal_eqpoll_rel_iff:
  assumes
    woX: "well_ord(X,r)" and woY: "well_ord(Y,s)"
    and
    "M(X)" "M(r)" "M(Y)" "M(s)" "M(\<kappa>)"
  shows "(\<exists>\<kappa>[M]. is_cardinal(M,X,\<kappa>) \<and> is_cardinal(M,Y,\<kappa>)) \<longleftrightarrow> X \<approx>r Y"
  using assms
proof (intro iffI)
  assume "X \<approx>r Y"
  with assms
  show "\<exists>\<kappa>[M]. is_cardinal(M,X,\<kappa>) \<and> is_cardinal(M,Y,\<kappa>)"
    using is_cardinal_cong by simp
qed (auto intro: well_ord_is_cardinal_eqE[of _ r _ s])

end (* M_cardinals *)

end
