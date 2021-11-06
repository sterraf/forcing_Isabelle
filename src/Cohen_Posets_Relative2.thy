section\<open>Cohen forcing notions\<close>

theory Cohen_Posets_Relative2
  imports
    Forcing_Notions
    Names \<comment> \<open>only for \<^term>\<open>SepReplace\<close>\<close>
    Recursion_Thms \<comment> \<open>only for the definition of \<^term>\<open>Rrel\<close>\<close>
    Cardinal_Library_Relative
    ZF_Library_Relative2
    Cardinal_Preservation \<comment> \<open>only for \<^locale>\<open>M_cohen\<close>\<close>
begin

lemmas app_fun = apply_iff[THEN iffD1]

(* todo: use the discipline, don't be lazy! *)
definition PFun_Space_Rel :: "[i,i\<Rightarrow>o, i] \<Rightarrow> i"  ("_\<rightharpoonup>\<^bsup>_\<^esup>_")
  where "A \<rightharpoonup>\<^bsup>M\<^esup> B == {f \<in> Pow(A\<times>B) . M(f) \<and> function(f)}"

lemma Un_filter_fun_space_closed:
  assumes "G \<subseteq> I \<rightarrow> J" "\<And> f g . f\<in>G \<Longrightarrow> g\<in>G \<Longrightarrow> \<exists>d\<in>I\<rightarrow> J . d\<supseteq>f \<and> d\<supseteq>g"
  shows "\<Union>G \<in> Pow(I\<times>J)" "function(\<Union>G)"
proof -
  from assms
  show "\<Union>G \<in> Pow(I\<times>J)"
    using Union_Pow_iff
    unfolding Pi_def
    by auto
next
  show "function(\<Union>G)"
    unfolding function_def
  proof(auto)
    fix B B' x y y'
    assume "B \<in> G" "\<langle>x, y\<rangle> \<in> B" "B' \<in> G" "\<langle>x, y'\<rangle> \<in> B'"
    moreover from assms this
    have "B \<in> I \<rightarrow> J" "B' \<in> I \<rightarrow> J"
    by auto
    moreover from calculation assms(2)[of B B']
    obtain d where "d \<supseteq> B"  "d \<supseteq> B'" "d\<in>I \<rightarrow> J"  "\<langle>x, y\<rangle> \<in> d" "\<langle>x, y'\<rangle> \<in> d"
      using subsetD[OF \<open>G\<subseteq>_\<close>]
      by auto
    then
    show "y=y'"
      using fun_is_function[OF \<open>d\<in>_\<close>]
      unfolding function_def
      by force
  qed
qed

lemma Un_filter_is_fun :
  assumes "G \<subseteq> I \<rightarrow> J" "\<And> f g . f\<in>G \<Longrightarrow> g\<in>G \<Longrightarrow> \<exists>d\<in>I\<rightarrow> J . d\<supseteq>f \<and> d\<supseteq>g" "G\<noteq>0"
  shows "\<Union>G \<in> I \<rightarrow> J"
  using assms Un_filter_fun_space_closed Pi_iff
proof(simp_all)
  show "I\<subseteq>domain(\<Union>G)"
  proof -
    from \<open>G\<noteq>0\<close>
    obtain f where "f\<subseteq>\<Union>G" "f\<in>G"
      by auto
    with \<open>G\<subseteq>_\<close>
    have "f\<in>I\<rightarrow>J" by auto
    then
    show ?thesis
      using subset_trans[OF _ domain_mono[OF \<open>f\<subseteq>\<Union>G\<close>],of I]
      unfolding Pi_def by auto
  qed
qed


context M_cardinals
begin

lemma mem_function_space_relD:
  assumes "f \<in> function_space_rel(M,A,y)" "M(A)" "M(y)"
  shows "f \<in> A \<rightarrow> y" and "M(f)"
  using assms function_space_rel_char by simp_all


(*todo*)
lemma pfunI :
  assumes "C\<subseteq>A" "f \<in> C \<rightarrow>\<^bsup>M\<^esup> B" "M(C)" "M(B)"
  shows "f\<in> A \<rightharpoonup>\<^bsup>M\<^esup> B"
proof -
  from assms
  have "f \<in> C\<rightarrow>B" "M(f)"
    using mem_function_space_relD
    by simp_all
  with assms
  show ?thesis
    using Pi_iff
  unfolding PFun_Space_Rel_def
  by auto
qed

lemma zero_in_PFun_rel:
  assumes "M(I)" "M(J)"
  shows "0 \<in> I \<rightharpoonup>\<^bsup>M\<^esup> J"
  using pfunI[of 0] nonempty mem_function_space_rel_abs assms
  by simp

lemma function_subset:
  "function(f) \<Longrightarrow> g\<subseteq>f \<Longrightarrow> function(g)"
  unfolding function_def subset_def by auto

lemma pfun_subsetI :
  assumes "f \<in> A \<rightharpoonup>\<^bsup>M\<^esup> B" "g\<subseteq>f" "M(g)"
  shows "g\<in> A \<rightharpoonup>\<^bsup>M\<^esup> B"
using assms function_subset
  unfolding PFun_Space_Rel_def
  by auto

lemma pfun_is_function :
  "f \<in> A\<rightharpoonup>\<^bsup>M\<^esup> B \<Longrightarrow> function(f)"
  unfolding PFun_Space_Rel_def by simp

lemma pfun_Un_filter_closed:
  assumes "G \<subseteq>I\<rightharpoonup>\<^bsup>M\<^esup> J" "\<And> f g . f\<in>G \<Longrightarrow> g\<in>G \<Longrightarrow> \<exists>d\<in>I\<rightharpoonup>\<^bsup>M\<^esup> J . d\<supseteq>f \<and> d\<supseteq>g"
  shows "\<Union>G \<in> Pow(I\<times>J)" "function(\<Union>G)"
proof -
  from assms
  show "\<Union>G \<in> Pow(I\<times>J)"
    using Union_Pow_iff
    unfolding PFun_Space_Rel_def
    by auto
next
  show "function(\<Union>G)"
    unfolding function_def
  proof(auto)
    fix B B' x y y'
    assume "B \<in> G" "\<langle>x, y\<rangle> \<in> B" "B' \<in> G" "\<langle>x, y'\<rangle> \<in> B'"
    moreover from calculation assms
    obtain d where "d \<in> I \<rightharpoonup>\<^bsup>M\<^esup> J" "function(d)" "\<langle>x, y\<rangle> \<in> d"  "\<langle>x, y'\<rangle> \<in> d"
      using pfun_is_function
      by force
    ultimately
    show "y=y'"
      unfolding function_def
      by auto
  qed
qed

lemma pfun_Un_filter_closed'':
  assumes "G \<subseteq>I\<rightharpoonup>\<^bsup>M\<^esup> J" "\<And> f g . f\<in>G \<Longrightarrow> g\<in>G \<Longrightarrow> \<exists>d\<in>G . d\<supseteq>f \<and> d\<supseteq>g"
  shows "\<Union>G \<in> Pow(I\<times>J)" "function(\<Union>G)"
proof -
  from assms
  have "\<And> f g . f\<in>G \<Longrightarrow> g\<in>G \<Longrightarrow> \<exists>d\<in>I\<rightharpoonup>\<^bsup>M\<^esup> J . d\<supseteq>f \<and> d\<supseteq>g"
    using subsetD[OF assms(1),THEN [2] bexI]
    by force
  then
  show "\<Union>G \<in> Pow(I\<times>J)"  "function(\<Union>G)"
      using assms pfun_Un_filter_closed
    unfolding PFun_Space_Rel_def
    by auto
qed

lemma pfun_Un_filter_closed':
  assumes "G \<subseteq>I\<rightharpoonup>\<^bsup>M\<^esup> J" "\<And> f g . f\<in>G \<Longrightarrow> g\<in>G \<Longrightarrow> \<exists>d\<in>G . d\<supseteq>f \<and> d\<supseteq>g" "M(G)"
  shows "\<Union>G \<in> I\<rightharpoonup>\<^bsup>M\<^esup> J"
  using assms pfun_Un_filter_closed''
  unfolding PFun_Space_Rel_def
  by auto

lemma pfunD :
  assumes "f \<in> A\<rightharpoonup>\<^bsup>M\<^esup> B"
  shows "\<exists>C[M]. C\<subseteq>A \<and> f \<in> C\<rightarrow>B"
proof -
  note assms
  moreover from this
  have "f\<in>Pow(A\<times>B)" "function(f)" "M(f)"
  unfolding PFun_Space_Rel_def
  by simp_all
  moreover from this
  have "domain(f) \<subseteq> A" "f \<in> domain(f) \<rightarrow> B" "M(domain(f))"
    using assms Pow_iff[of f "A\<times>B"] domain_subset Pi_iff
    by auto
  ultimately
  show ?thesis by auto
qed

lemma pfunD_closed :
  assumes "f \<in> A\<rightharpoonup>\<^bsup>M\<^esup> B"
  shows "M(f)"
  using assms
  unfolding PFun_Space_Rel_def by simp

lemma pfun_singletonI :
  assumes "x \<in> A" "b \<in> B" "M(A)" "M(B)"
  shows "{\<langle>x,b\<rangle>} \<in> A\<rightharpoonup>\<^bsup>M\<^esup> B"
  using assms transM[of x A] transM[of b B]
  unfolding PFun_Space_Rel_def function_def
  by auto

lemma pfun_unionI :
  assumes "f \<in> A\<rightharpoonup>\<^bsup>M\<^esup> B" "g \<in> A\<rightharpoonup>\<^bsup>M\<^esup> B" "domain(f)\<inter>domain(g)=0"
  shows "f\<union>g \<in> A\<rightharpoonup>\<^bsup>M\<^esup> B"
  using assms
  unfolding PFun_Space_Rel_def function_def
  by blast

lemma FiniteFun_pfunI :
  assumes "f \<in> A-||> B" "M(A)" "M(B)"
  shows "f \<in> A \<rightharpoonup>\<^bsup>M\<^esup> B"
  using assms(1)
proof(induct)
case emptyI
  then
  show ?case
    using assms nonempty mem_function_space_rel_abs pfunI[OF empty_subsetI, of 0]
    by simp
next
  case (consI a b h)
  note consI
  moreover from this
  have "M(a)" "M(b)" "M(h)" "domain(h) \<subseteq> A"
    using transM[OF _ \<open>M(A)\<close>] transM[OF _ \<open>M(B)\<close>]
      FinD
      FiniteFun_domain_Fin
      pfunD_closed
    by simp_all
  moreover from calculation
  have "{a}\<union>domain(h)\<subseteq>A" "M({a}\<union>domain(h))" "M(cons(<a,b>,h))" "domain(cons(<a,b>,h)) = {a}\<union>domain(h)"
    by auto
  moreover from calculation
  have "cons(<a,b>,h) \<in> {a}\<union>domain(h) \<rightarrow> B"
    using FiniteFun_is_fun[OF FiniteFun.consI, of a A b B h]
    by auto
  ultimately
  show "cons(<a,b>,h) \<in> A \<rightharpoonup>\<^bsup>M\<^esup> B"
    using assms  mem_function_space_rel_abs pfunI
    by simp_all
qed

(* FIXME: move this lemma to FiniteFun. *)
lemma FiniteFunI :
  assumes  "f\<in>Fin(A\<times>B)" "function(f)"
  shows "f \<in> A -||> B"
  using assms
proof(induct)
  case 0
  then show ?case using emptyI by simp
next
  case (cons p f)
  moreover
  from assms this
  have "fst(p)\<in>A" "snd(p)\<in>B" "function(f)"
    using snd_type[OF \<open>p\<in>_\<close>] function_subset
    by auto
  moreover
  from \<open>function(cons(p,f))\<close> \<open>p\<notin>f\<close> \<open>p\<in>_\<close>
  have "fst(p)\<notin>domain(f)"
    unfolding function_def
    by force
  ultimately
  show ?case
    using consI[of "fst(p)" _ "snd(p)"]
    by auto
qed

lemma PFun_FiniteFunI :
  assumes "f \<in> A \<rightharpoonup>\<^bsup>M\<^esup> B" "Finite(f)"
  shows  "f \<in> A-||> B"
proof -
  from assms
  have "f\<in>Fin(A\<times>B)" "function(f)"
    using Finite_Fin Pow_iff
    unfolding PFun_Space_Rel_def
    by auto
  then
  show ?thesis
    using FiniteFunI by simp
qed

end

(* Fn_rel should be the relativization *)
definition
  Fn_rel :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> i" (\<open>Fn\<^bsup>_\<^esup>'(_,_,_')\<close>) where
  "Fn_rel(M,\<kappa>,I,J) \<equiv> {f \<in> I\<rightharpoonup>\<^bsup>M\<^esup> J . |f|\<^bsup>M\<^esup> \<prec>\<^bsup>M\<^esup> \<kappa>}"

context  M_library
begin

lemma Fn_rel_subset_PFun_rel : "Fn\<^bsup>M\<^esup>(\<kappa>,I,J) \<subseteq> I\<rightharpoonup>\<^bsup>M\<^esup> J"
  unfolding Fn_rel_def by auto

lemma Fn_relI[intro]:
  assumes "f : d \<rightarrow> J" "d \<subseteq> I" "|f|\<^bsup>M\<^esup> \<prec>\<^bsup>M\<^esup> \<kappa>" "M(d)" "M(J)" "M(f)"
  shows "f \<in> Fn_rel(M,\<kappa>,I,J)"
  using assms pfunI mem_function_space_rel_abs
  unfolding Fn_rel_def
  by auto

lemma Fn_relD[dest]:
  assumes "p \<in> Fn_rel(M,\<kappa>,I,J)"
  shows "\<exists>C[M]. C\<subseteq>I \<and> p : C \<rightarrow> J \<and> |p|\<^bsup>M\<^esup> \<prec>\<^bsup>M\<^esup> \<kappa>"
  using assms pfunD
  unfolding Fn_rel_def
  by simp

lemma Fn_rel_is_function:
  assumes "p \<in> Fn_rel(M,\<kappa>,I,J)"
  shows "function(p)" "M(p)" "|p|\<^bsup>M\<^esup> \<prec>\<^bsup>M\<^esup> \<kappa>" "p\<in> I\<rightharpoonup>\<^bsup>M\<^esup> J"
  using assms
  unfolding Fn_rel_def PFun_Space_Rel_def by simp_all

lemma Fn_rel_mono:
  assumes "p \<in> Fn_rel(M,\<kappa>,I,J)" "\<kappa> \<prec>\<^bsup>M\<^esup> \<kappa>'" "M(\<kappa>)" "M(\<kappa>')"
  shows "p \<in> Fn_rel(M,\<kappa>',I,J)"
  using assms lesspoll_rel_trans[OF _ assms(2)] cardinal_rel_closed
    Fn_rel_is_function(2)[OF assms(1)]
  unfolding Fn_rel_def
  by simp

lemma Fn_rel_mono':
  assumes "p \<in> Fn_rel(M,\<kappa>,I,J)" "\<kappa> \<lesssim>\<^bsup>M\<^esup> \<kappa>'" "M(\<kappa>)" "M(\<kappa>')"
  shows "p \<in> Fn_rel(M,\<kappa>',I,J)"
proof -
  note assms
  then
  consider "\<kappa> \<prec>\<^bsup>M\<^esup> \<kappa>'"  | "\<kappa> \<approx>\<^bsup>M\<^esup> \<kappa>'"
    using lepoll_rel_iff_leqpoll_rel
    by auto
  then
  show ?thesis
  proof(cases)
    case 1
    with assms show ?thesis using Fn_rel_mono by simp
  next
    case 2
    then show ?thesis
      using assms cardinal_rel_closed Fn_rel_is_function[OF assms(1)]
        lesspoll_rel_eq_trans
  unfolding Fn_rel_def
  by simp
  qed
qed

lemma Fn_csucc:
  assumes "Ord(\<kappa>)" "M(\<kappa>)"
  shows "Fn_rel(M,(\<kappa>\<^sup>+)\<^bsup>M\<^esup>,I,J) = {p\<in> I\<rightharpoonup>\<^bsup>M\<^esup> J . |p|\<^bsup>M\<^esup>  \<lesssim>\<^bsup>M\<^esup> \<kappa>}"   (is "?L=?R")
  using assms
proof(intro equalityI)
  show "?L \<subseteq> ?R"
  proof(intro subsetI)
    fix p
    assume "p\<in>?L"
    then
    have "|p|\<^bsup>M\<^esup> \<prec>\<^bsup>M\<^esup> csucc_rel(M,\<kappa>)" "M(p)" "p\<in> I\<rightharpoonup>\<^bsup>M\<^esup> J"
      using Fn_rel_is_function by simp_all
    then
    show "p\<in>?R"
      using  assms lesspoll_rel_csucc_rel by simp
  qed
next
  show "?R\<subseteq>?L"
  proof(intro subsetI)
    fix p
    assume "p\<in>?R"
    then
    have  "p\<in> I\<rightharpoonup>\<^bsup>M\<^esup> J" " |p|\<^bsup>M\<^esup>  \<lesssim>\<^bsup>M\<^esup> \<kappa>"
      using assms lesspoll_rel_csucc_rel by simp_all
    then
    show "p\<in>?L"
      using  assms lesspoll_rel_csucc_rel pfunD_closed
      unfolding Fn_rel_def
      by simp
  qed
qed


lemma Finite_imp_lesspoll_nat:
  assumes "Finite(A)"
  shows "A \<prec> nat"
  using assms subset_imp_lepoll[OF naturals_subset_nat] eq_lepoll_trans
    n_lesspoll_nat eq_lesspoll_trans
  unfolding Finite_def lesspoll_def by auto

lemma FinD_Finite :
  assumes "a\<in>Fin(A)"
  shows "Finite(a)"
  using assms
  by(induct,simp_all)

lemma Fn_rel_nat_eq_FiniteFun:
  assumes "M(I)" "M(J)"
  shows "I -||> J = Fn_rel(M,\<omega>,I,J)"
proof(intro equalityI subsetI)
  fix p
  assume "p\<in>I -||> J"
  with assms
  have "p\<in> I \<rightharpoonup>\<^bsup>M\<^esup> J" "Finite(p)"
    using FiniteFun_pfunI FinD_Finite[OF subsetD[OF FiniteFun.dom_subset,OF \<open>p\<in>_\<close>]]
    by auto
  moreover from this
  have "|p|\<^bsup>M\<^esup> \<prec>\<^bsup>M\<^esup> \<omega>"
    using Finite_cardinal_rel_Finite
      Finite_cardinal_rel_in_nat pfunD_closed[of p] n_lesspoll_rel_nat
    by simp
  ultimately
  show "p\<in> Fn_rel(M,\<omega>,I,J)"
    unfolding Fn_rel_def by simp
next
  fix p
  assume "p\<in> Fn_rel(M,\<omega>,I,J)"
  then
  have "p\<in> I \<rightharpoonup>\<^bsup>M\<^esup> J"  "|p|\<^bsup>M\<^esup> \<prec>\<^bsup>M\<^esup> \<omega>"
    unfolding Fn_rel_def by simp_all
  moreover from this
  have "Finite(p)"
    using Finite_cardinal_rel_Finite lesspoll_rel_nat_is_Finite_rel pfunD_closed
      cardinal_rel_closed[of p]  Finite_cardinal_rel_iff'[THEN iffD1]
    by simp
  ultimately
  show "p\<in>I -||> J"
    using PFun_FiniteFunI
    by simp
qed

lemma Fn_nat_abs:
  assumes "M(I)" "M(J)"
  shows "Fn(nat,I,J) = Fn_rel(M,\<omega>,I,J)"
  using assms Fn_rel_nat_eq_FiniteFun Fn_nat_eq_FiniteFun
  by simp
end

lemma (in M_cohen) Fn_rel_unionI:
  assumes "p \<in> Fn\<^bsup>M\<^esup>(\<kappa>,I,J)" "q\<in>Fn\<^bsup>M\<^esup>(\<kappa>,I,J)"  "InfCard\<^bsup>M\<^esup>(\<kappa>)"
    "M(\<kappa>)" "M(I)" "M(J)""domain(p) \<inter> domain(q) = 0"
  shows "p\<union>q \<in> Fn\<^bsup>M\<^esup>(\<kappa>,I,J)"
proof -
  note assms
  moreover from calculation
  have "|p|\<^bsup>M\<^esup> \<prec>\<^bsup>M\<^esup> \<kappa>"  "M(p)"
    "|q|\<^bsup>M\<^esup> \<prec>\<^bsup>M\<^esup> \<kappa>" "M(q)"
    using Fn_rel_is_function by simp_all
  moreover from calculation
  have "p\<union>q \<prec>\<^bsup>M\<^esup> \<kappa>"
    using eqpoll_rel_sym cardinal_rel_eqpoll_rel
      eq_lesspoll_rel_trans[OF _ \<open>|p|\<^bsup>M\<^esup> \<prec>\<^bsup>M\<^esup> _\<close>]
      eq_lesspoll_rel_trans[OF _ \<open>|q|\<^bsup>M\<^esup> \<prec>\<^bsup>M\<^esup> _\<close>]
      InfCard_rel_lesspoll_rel_Un
    by simp_all
  ultimately
  show ?thesis
    unfolding Fn_rel_def
    using pfun_unionI cardinal_rel_eqpoll_rel
      eq_lesspoll_rel_trans[OF _ \<open>p\<union>q \<prec>\<^bsup>M\<^esup> _\<close>]
    by auto
qed

lemma (in M_library) Fn_rel_singletonI:
  assumes "x \<in> I" "j \<in> J" "InfCard\<^bsup>M\<^esup>(\<kappa>)" "M(\<kappa>)" "M(I)" "M(J)"
  shows "{\<langle>x,j\<rangle>} \<in> Fn\<^bsup>M\<^esup>(\<kappa>,I,J)"
    using assms pfun_singletonI transM[of x ] transM[of j]
      cardinal_rel_singleton
      lt_Card_rel_imp_lesspoll_rel ltI[OF nat_into_InfCard_rel]
      Card_rel_cardinal_rel Card_rel_is_Ord InfCard_rel_is_Card_rel
    unfolding Fn_rel_def
    by auto

lemma (in M_cohen) cons_in_Fn_rel:
  assumes "x \<notin> domain(p)" "p \<in> Fn\<^bsup>M\<^esup>(\<kappa>,I,J)" "x \<in> I" "j \<in> J" "InfCard\<^bsup>M\<^esup>(\<kappa>)"
    "M(\<kappa>)" "M(I)" "M(J)"
  shows "cons(\<langle>x,j\<rangle>, p) \<in> Fn\<^bsup>M\<^esup>(\<kappa>,I,J)"
    using assms cons_eq Fn_rel_unionI[OF Fn_rel_singletonI[of x I j J] \<open>p\<in>_\<close>]
  by auto

definition
  Fnle_rel :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> i" (\<open>Fnle\<^bsup>_\<^esup>'(_,_,_')\<close>) where
  "Fnle_rel(M,\<kappa>,I,J) \<equiv> Fnlerel(Fn\<^bsup>M\<^esup>(\<kappa>,I,J))"

abbreviation
  Fn_r_set ::  "[i,i,i,i] \<Rightarrow> i" (\<open>Fn\<^bsup>_\<^esup>'(_,_,_')\<close>) where
  "Fn_r_set(M) \<equiv> Fn_rel(##M)"

abbreviation
  Fnle_r_set ::  "[i,i,i,i] \<Rightarrow> i" (\<open>Fnle\<^bsup>_\<^esup>'(_,_,_')\<close>) where
  "Fnle_r_set(M) \<equiv> Fnle_rel(##M)"


context M_library
begin

lemma Fnle_relI[intro]:
  assumes "p \<in> Fn_rel(M,\<kappa>,I,J)" "q \<in> Fn_rel(M,\<kappa>,I,J)" "p \<supseteq> q"
  shows "<p,q> \<in> Fnle_rel(M,\<kappa>,I,J)"
  using assms unfolding Fnlerel_def Fnle_rel_def FnleR_def Rrel_def
  by auto

lemma Fnle_relD[dest]:
  assumes "<p,q> \<in> Fnle_rel(M,\<kappa>,I,J)"
  shows "p \<in> Fn_rel(M,\<kappa>,I,J)" "q \<in> Fn_rel(M,\<kappa>,I,J)" "p \<supseteq> q"
  using assms unfolding Fnlerel_def Fnle_rel_def FnleR_def Rrel_def
  by auto

end


context M_library
begin
(* FIXME: The results in this context are to be obtain through porting
  Cohen_Posets.thy *)

lemma Fn_rel_closed[intro,simp]:
  assumes "M(\<kappa>)" "M(I)" "M(J)"
  shows "M(Fn\<^bsup>M\<^esup>(\<kappa>,I,J))"
  sorry

lemma Fn_rel_subset_Pow:
  assumes "M(\<kappa>)" "M(I)" "M(J)"
  shows "Fn\<^bsup>M\<^esup>(\<kappa>,I,J) \<subseteq> Pow(I\<times>J)"
  unfolding Fn_rel_def PFun_Space_Rel_def
  by auto

lemma Fnle_rel_closed[intro,simp]:
  assumes "M(\<kappa>)" "M(I)" "M(J)"
  shows "M(Fnle\<^bsup>M\<^esup>(\<kappa>,I,J))"
  unfolding Fnle_rel_def Fnlerel_def Rrel_def FnleR_def
  using assms supset_separation Fn_rel_closed
  by auto

lemma Fnle_rel_Aleph_rel1_closed[intro,simp]: "M(Fnle\<^bsup>M\<^esup>(\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<omega> \<rightarrow>\<^bsup>M\<^esup> 2))"
  by simp

lemma zero_in_Fn_rel:
  assumes "0<\<kappa>" "M(\<kappa>)" "M(I)" "M(J)"
  shows "0 \<in> Fn\<^bsup>M\<^esup>(\<kappa>, I, J)"
  unfolding Fn_rel_def
  using zero_in_PFun_rel zero_lesspoll_rel assms
  by simp

lemma zero_top_Fn_rel:
  assumes "p\<in>Fn\<^bsup>M\<^esup>(\<kappa>, I, J)" "0<\<kappa>" "M(\<kappa>)" "M(I)" "M(J)"
  shows "\<langle>p, 0\<rangle> \<in> Fnle\<^bsup>M\<^esup>(\<kappa>, I, J)"
  using assms zero_in_Fn_rel unfolding preorder_on_def refl_def trans_on_def
  by auto

lemma preorder_on_Fnle_rel:
  assumes "M(\<kappa>)" "M(I)" "M(J)"
  shows "preorder_on(Fn\<^bsup>M\<^esup>(\<kappa>, I, J), Fnle\<^bsup>M\<^esup>(\<kappa>, I, J))"
  unfolding preorder_on_def refl_def trans_on_def
  by blast


end (* M_master *)

end