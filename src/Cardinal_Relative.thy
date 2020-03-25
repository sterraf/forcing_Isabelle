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

lemma rvimage_closed [intro,simp]: 
  assumes 
    "M(A)" "M(f)" "M(r)"
  shows
    "M(rvimage(A,f,r))"
  sorry

lemma is_lepoll_well_ord: "[| M(A); M(B); M(r); A \<lesssim>r B; well_ord(B,r) |] ==> \<exists>s[M]. well_ord(A,s)"
  unfolding is_lepoll_def by (auto intro:well_ord_rvimage)

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
  assumes "well_ord(A,r)" shows "M(A) \<Longrightarrow> M(\<kappa>) \<Longrightarrow> M(r) \<Longrightarrow> |A|r= \<kappa> \<Longrightarrow> \<kappa> \<approx>r A"  
proof (subst is_cardinal_imp_Least[of A \<kappa>])
  assume "M(A)" "M(\<kappa>)" "M(r)" "|A|r= \<kappa>"
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
    bij_converse_bij[THEN [4] bij_imp_is_eqpoll, of f] by simp
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
    "M(X)" "M(Y)" "M(\<kappa>)" "M(r)" "M(s)"
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
    "M(X)" "M(Y)" "M(\<kappa>)" "M(r)" "M(s)"
    and
    woX: "well_ord(X,r)" and woY: "well_ord(Y,s)" 
  shows "(\<exists>\<kappa>[M]. |X|r=\<kappa> \<and> |Y|r=\<kappa>) \<longleftrightarrow> X \<approx>r Y"
  using assms
proof (intro iffI)
  assume "X \<approx>r Y"
  with assms
  show "\<exists>\<kappa>[M]. |X|r= \<kappa> \<and> |Y|r= \<kappa>"
    using is_cardinal_cong by simp
qed (auto intro: well_ord_is_cardinal_eqE[of _ _ _ r s])

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

lemma is_Card_imp_Ord: "M(i) \<Longrightarrow> is_Card(i) \<Longrightarrow> Ord(i)"
  using is_cardinal_imp_Least[of i i] Ord_Least
  unfolding is_Card_def 
  by (simp) (erule ssubst, blast)

lemma is_Card_cardinal_le: "M(K) \<Longrightarrow> M(\<kappa>) \<Longrightarrow> is_Card(K) \<Longrightarrow> |K|r=\<kappa> \<Longrightarrow> K \<le> \<kappa>"
  using is_Card_imp_Ord is_Card_is_cardinal_eq is_cardinal_univalent
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
    using is_CardI[of K] is_Card_imp_Ord[of K]
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
  apply (simp_all add: subset_Un_iff [THEN iffD1]  is_Card_imp_Ord le_imp_subset
      subset_Un_iff2 [THEN iffD1])
  done

(*Infinite unions of cardinals?  See Devlin, Lemma 6.7, page 98*)

lemma is_cardinal_imp_is_Card [simp,intro]: 
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
lemma is_cardinal_eq_lemma:
  assumes 
    "M(i)" "M(j)" "M(\<kappa>)" "M(\<kappa>')"
    and
    "|i|r=\<kappa>" "|j|r=\<kappa>'"
    and
    i:"\<kappa> \<le> j" and j: "j \<le> i" shows "\<kappa>' = \<kappa>"
proof -
  from assms
  have "j \<lesssim>r i" by (rule_tac le_imp_is_lepoll [OF _ _ j])
  moreover
  have "i \<lesssim>r j"
  proof -
    have Oi: "Ord(i)" using j by (rule le_Ord2)
    with assms
    have "i \<approx>r \<kappa>"
      using Ord_cardinal_is_eqpoll[THEN [3] is_eqpoll_sym]
      by simp
    also from assms
    have "... \<lesssim>r j"
      by (blast intro: le_imp_is_lepoll i)
    finally show "i \<lesssim>r j" using assms by simp
  qed
  moreover
  note assms(1-6)
  moreover from calculation
  obtain \<delta> where "M(\<delta>)" "|i|r= \<delta>" "|j|r= \<delta>"
    using is_eqpollI[THEN [3] is_cardinal_cong] by auto
  ultimately
  have "\<kappa> = \<delta>" "\<kappa>'=\<delta>"
    using is_cardinal_univalent by blast+
  then
  show ?thesis by simp
qed

lemma is_cardinal_mono:
  assumes 
    "M(i)" "M(j)" "M(\<kappa>)" "M(\<kappa>')"
    and
    "|i|r= \<kappa>" "|j|r= \<kappa>'"
    and
    ij: "i \<le> j" 
  shows "\<kappa> \<le> \<kappa>'"
  using Ord_is_cardinal[OF \<open>M(i)\<close> \<open>M(\<kappa>)\<close> \<open>|i|r= \<kappa>\<close>]
    Ord_is_cardinal[OF \<open>M(j)\<close> \<open>M(\<kappa>')\<close> \<open>|j|r= \<kappa>'\<close>]
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
  from \<open>M(i)\<close> \<open>M(\<kappa>)\<close> \<open>|i|r= \<kappa>\<close> 
  have "|\<kappa>|r= \<kappa>"
    using is_cardinal_imp_is_Card is_Card_is_cardinal_eq by simp 
  with assms
  have "... = \<kappa>'"
    by (rule_tac is_cardinal_eq_lemma [OF _ _ _ _ _ _ ge ci])
  then 
  show ?thesis 
    using Ord_is_cardinal[OF \<open>M(j)\<close> \<open>M(\<kappa>')\<close> \<open>|j|r= \<kappa>'\<close>] by simp
qed

text\<open>Since we have \<^term>\<open>|succ(nat)| \<le> |nat|\<close>, the converse of \<open>cardinal_mono\<close> fails!\<close>
lemma cardinal_lt_imp_lt: 
  assumes 
    "M(i)" "M(j)" "M(\<kappa>)" "M(\<kappa>')" "|i|r=\<kappa>" "|j|r=\<kappa>'"
    "\<kappa><\<kappa>'"  "Ord(i)"  "Ord(j)"
  shows 
    "i < j"
  using assms
  apply (rule_tac Ord_linear2 [of i j])
  apply assumption+
  apply (erule lt_trans2 [THEN lt_irrefl])
  apply (force elim:is_cardinal_mono)
  done

lemma is_Card_lt_imp_lt: "[| M(i); M(\<kappa>); M(K); |i|r= \<kappa>; \<kappa> < K;  Ord(i);  is_Card(K) |] ==> i < K"
  by (simp (no_asm_simp) add: cardinal_lt_imp_lt is_Card_imp_Ord is_Card_is_cardinal_eq)

lemma is_Card_lt_iff: "[| M(i); M(\<kappa>); M(K); |i|r= \<kappa>; Ord(i);  is_Card(K) |] ==> (\<kappa> < K) \<longleftrightarrow> (i < K)"
  by (blast intro: is_Card_lt_imp_lt Ord_is_cardinal_le [THEN lt_trans1])

lemma is_Card_le_iff: "[| M(i); M(\<kappa>); M(K); |i|r= \<kappa>; Ord(i);  is_Card(K) |] ==> (K \<le> \<kappa>) \<longleftrightarrow> (K \<le> i)"
  by (simp add: is_Card_lt_iff is_Card_imp_Ord not_lt_iff_le [THEN iff_sym])

(*Can use AC or finiteness to discharge first premise*)
lemma well_ord_is_lepoll_imp_is_Card_le:
  assumes 
    "M(A)" "M(B)" "M(\<kappa>)" "M(\<kappa>')" "M(r)"
    and 
    "|A|r= \<kappa>"  "|B|r= \<kappa>'"
    and
    wB: "well_ord(B,r)" and AB: "A \<lesssim>r B"
  shows "\<kappa> \<le> \<kappa>'"
  using Ord_is_cardinal[OF \<open>M(A)\<close> \<open>M(\<kappa>)\<close> \<open>|A|r= \<kappa>\<close>]
    Ord_is_cardinal[OF \<open>M(B)\<close> \<open>M(\<kappa>')\<close> \<open>|B|r= \<kappa>'\<close>]
proof (cases rule: Ord_linear_le[of \<kappa> \<kappa>'])
  case le 
  then 
  show ?thesis .
next
  case ge
  from is_lepoll_well_ord [OF assms(1,2,5) AB wB]
  obtain s where s: "well_ord(A, s)" "M(s)" by auto
  from assms
  have "B  \<approx>r \<kappa>'" by (blast intro: wB is_eqpoll_sym well_ord_cardinal_is_eqpoll)
  also from assms 
  have "... \<lesssim>r \<kappa>" by (rule_tac le_imp_is_lepoll [OF _ _ ge])
  also from assms
  have "... \<approx>r A" by (rule_tac well_ord_cardinal_is_eqpoll [OF s(1) _ _ s(2)])
  finally 
  have "B \<lesssim>r A" using assms by simp
  with assms
  have "A \<approx>r B" by (blast intro: is_eqpollI AB)
  with assms
  obtain \<delta> where "M(\<delta>)" "|A|r= \<delta>" "|B|r= \<delta>"
   using is_cardinal_cong[of A B] by auto
  with assms
  have "\<kappa> = \<delta>" "\<kappa>'=\<delta>"
    using is_cardinal_univalent by blast+
  then
  show ?thesis 
    using Ord_is_cardinal[OF \<open>M(A)\<close> \<open>M(\<kappa>)\<close> \<open>|A|r= \<kappa>\<close>] by simp
qed 

(* Two many assumptions in next result 
This is because of the relational form of \<open>is_cardinal\<close>,
in arguments that involve iterated cardinals (i.e. \<open>||A||\<close>).
*)
lemma is_lepoll_is_cardinal_le: "[| M(A); M(i); M(\<kappa>); M(\<kappa>'); A \<lesssim>r i; Ord(i) ; |A|r=\<kappa>; |i|r= \<kappa>' |] ==> \<kappa> \<le> i"
  apply (rule le_trans)
   apply (erule well_ord_Memrel[THEN [8] well_ord_is_lepoll_imp_is_Card_le, of A i _ \<kappa>'], assumption+)
       apply (rule Memrel_closed, simp_all)
  apply (erule Ord_is_cardinal_le, simp_all)
  done

lemma is_lepoll_Ord_imp_is_eqpoll: "[| M(A); M(i); M(\<kappa>); M(\<kappa>'); A \<lesssim>r i; Ord(i) ; |A|r=\<kappa>; |i|r= \<kappa>' |] ==> \<kappa> \<approx>r A"
  using well_ord_Memrel[of i] is_lepoll_well_ord[of A i "Memrel(i)"]
     well_ord_cardinal_is_eqpoll[of A] 
  by auto

lemma is_lesspoll_imp_is_eqpoll: "[| M(A); M(i); M(\<kappa>); M(\<kappa>'); |A|r=\<kappa>; |i|r= \<kappa>'; A \<prec>r i; Ord(i) |] ==> \<kappa> \<approx>r A"
  apply (unfold is_lesspoll_def)
  apply (blast intro: is_lepoll_Ord_imp_is_eqpoll)
  done

lemma is_cardinal_subset_Ord: "[|M(A); M(i); M(\<kappa>); M(\<kappa>'); |A|r=\<kappa>; |i|r= \<kappa>'; A \<subseteq> i; Ord(i)|] ==> \<kappa> \<subseteq> i"
  apply (frule subset_imp_is_lepoll [THEN [5] is_lepoll_is_cardinal_le])
  prefer 8 prefer 9 prefer 9 apply assumption+
  apply (auto intro: Ord_trans dest:ltD)
  done

end (* M_cardinals *)
end
