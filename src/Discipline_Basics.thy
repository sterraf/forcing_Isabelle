theory Discipline_Basics
  imports
    "ZF-Constructible.Rank"
    Relativization
    "HOL-Eisbach.Eisbach_Old_Appl_Syntax"\<comment> \<open>if put before, it breaks some simps\<close>
    "../Tools/Try0"
begin

lemma (in M_trivial) extensionality_trans:
  assumes
    "M(d)" "M(d')"
    "\<forall>x[M]. x\<in>d  \<longleftrightarrow> P(x)"
    "\<forall>x[M]. x\<in>d' \<longleftrightarrow> P(x)"
  shows
    "d=d'"
proof -
  from assms
  have "\<forall>x. x\<in>d \<longleftrightarrow> P(x) \<and> M(x)"
    using transM[of _ d, OF _ \<open>M(d)\<close>] by auto
  moreover from assms
  have  "\<forall>x. x\<in>d' \<longleftrightarrow> P(x) \<and> M(x)"
    using transM[of _ d', OF _ \<open>M(d')\<close>] by auto
  ultimately
  show ?thesis by auto
qed

definition
  is_hcomp :: "[i\<Rightarrow>o,[i\<Rightarrow>o,i,i]\<Rightarrow>o,[i\<Rightarrow>o,i,i]\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "is_hcomp(M,is_f,is_g,a,w) \<equiv> \<exists>z[M]. is_g(M,a,z) \<and> is_f(M,z,w)"

definition
  is_hcomp2_2 :: "[i\<Rightarrow>o,[i\<Rightarrow>o,i,i,i]\<Rightarrow>o,[i\<Rightarrow>o,i,i,i]\<Rightarrow>o,[i\<Rightarrow>o,i,i,i]\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_hcomp2_2(M,is_f,is_g1,is_g2,a,b,w) \<equiv> \<exists>g1ab[M]. \<exists>g2ab[M].
       is_g1(M,a,b,g1ab) \<and> is_g2(M,a,b,g2ab) \<and> is_f(M,g1ab,g2ab,w)"

lemma (in M_trivial) hcomp_abs:
  assumes
    is_f_abs:"\<And>a z. M(a) \<Longrightarrow> M(z) \<Longrightarrow> is_f(M,a,z) \<longleftrightarrow> z = f(a)" and
    is_g_abs:"\<And>a z. M(a) \<Longrightarrow> M(z) \<Longrightarrow> is_g(M,a,z) \<longleftrightarrow> z = g(a)" and
    g_closed:"\<And>a. M(a) \<Longrightarrow> M(g(a))"
    "M(a)" "M(w)"
  shows
    "is_hcomp(M,is_f,is_g,a,w) \<longleftrightarrow> w = f(g(a))"
  unfolding is_hcomp_def using assms by simp

lemma hcomp_uniqueness:
  assumes
    uniq_is_f:
    "\<And>r d d'. M(r) \<Longrightarrow> M(d) \<Longrightarrow> M(d') \<Longrightarrow> is_f(M, r, d) \<Longrightarrow> is_f(M, r, d') \<Longrightarrow>
               d = d'"
    and
    uniq_is_g:
    "\<And>r d d'. M(r) \<Longrightarrow> M(d) \<Longrightarrow> M(d') \<Longrightarrow> is_g(M, r, d) \<Longrightarrow> is_g(M, r, d') \<Longrightarrow>
               d = d'"
    and
    "M(a)" "M(w)" "M(w')"
    "is_hcomp(M,is_f,is_g,a,w)"
    "is_hcomp(M,is_f,is_g,a,w')"
  shows
    "w=w'"
proof -
  from assms
  obtain z z' where "is_g(M, a, z)" "is_g(M, a, z')"
    "is_f(M,z,w)" "is_f(M,z',w')"
    "M(z)" "M(z')"
    unfolding is_hcomp_def by blast
  moreover from this and uniq_is_g and \<open>M(a)\<close>
  have "z=z'" by blast
  moreover note uniq_is_f and \<open>M(w)\<close> \<open>M(w')\<close>
  ultimately
  show ?thesis by blast
qed

lemma hcomp_witness:
  assumes
    wit_is_f: "\<And>r. M(r) \<Longrightarrow> \<exists>d[M]. is_f(M,r,d)" and
    wit_is_g: "\<And>r. M(r) \<Longrightarrow> \<exists>d[M]. is_g(M,r,d)" and
    "M(a)"
  shows
    "\<exists>w[M]. is_hcomp(M,is_f,is_g,a,w)"
proof -
  from \<open>M(a)\<close> and wit_is_g
  obtain z where "is_g(M,a,z)" "M(z)" by blast
  moreover from this and wit_is_f
  obtain w where "is_f(M,z,w)" "M(w)" by blast
  ultimately
  show ?thesis
    using assms unfolding is_hcomp_def by auto
qed

lemma (in M_trivial) hcomp2_2_abs:
  assumes
    is_f_abs:"\<And>r1 r2 z. M(r1) \<Longrightarrow> M(r2) \<Longrightarrow>  M(z) \<Longrightarrow> is_f(M,r1,r2,z) \<longleftrightarrow> z = f(r1,r2)" and
    is_g1_abs:"\<And>r1 r2 z. M(r1) \<Longrightarrow> M(r2) \<Longrightarrow>  M(z) \<Longrightarrow> is_g1(M,r1,r2,z) \<longleftrightarrow> z = g1(r1,r2)" and
    is_g2_abs:"\<And>r1 r2 z. M(r1) \<Longrightarrow> M(r2) \<Longrightarrow>  M(z) \<Longrightarrow> is_g2(M,r1,r2,z) \<longleftrightarrow> z = g2(r1,r2)" and
    types: "M(a)" "M(b)" "M(w)" "M(g1(a,b))" "M(g2(a,b))"
  shows
    "is_hcomp2_2(M,is_f,is_g1,is_g2,a,b,w) \<longleftrightarrow> w = f(g1(a,b),g2(a,b))"
  unfolding is_hcomp2_2_def using assms
    \<comment> \<open>We only need some particular cases of the abs assumptions\<close>
    (* is_f_abs types is_g1_abs[of a b] is_g2_abs[of a b] *)
  by simp

lemma hcomp2_2_uniqueness:
  assumes
    uniq_is_f:
    "\<And>r1 r2 d d'. M(r1) \<Longrightarrow> M(r2) \<Longrightarrow> M(d) \<Longrightarrow> M(d') \<Longrightarrow>
        is_f(M, r1, r2 , d) \<Longrightarrow> is_f(M, r1, r2, d') \<Longrightarrow>  d = d'"
    and
    uniq_is_g1:
    "\<And>r1 r2 d d'. M(r1) \<Longrightarrow> M(r2)\<Longrightarrow> M(d) \<Longrightarrow> M(d') \<Longrightarrow> is_g1(M, r1,r2, d) \<Longrightarrow> is_g1(M, r1,r2, d') \<Longrightarrow>
               d = d'"
    and
    uniq_is_g2:
    "\<And>r1 r2 d d'. M(r1) \<Longrightarrow> M(r2)\<Longrightarrow> M(d) \<Longrightarrow> M(d') \<Longrightarrow> is_g2(M, r1,r2, d) \<Longrightarrow> is_g2(M, r1,r2, d') \<Longrightarrow>
               d = d'"
    and
    "M(a)" "M(b)" "M(w)" "M(w')"
    "is_hcomp2_2(M,is_f,is_g1,is_g2,a,b,w)"
    "is_hcomp2_2(M,is_f,is_g1,is_g2,a,b,w')"
  shows
    "w=w'"
proof -
  from assms
  obtain z z' y y' where "is_g1(M, a,b, z)" "is_g1(M, a,b, z')"
    "is_g2(M, a,b, y)" "is_g2(M, a,b, y')"
    "is_f(M,z,y,w)" "is_f(M,z',y',w')"
    "M(z)" "M(z')" "M(y)" "M(y')"
    unfolding is_hcomp2_2_def by force
  moreover from this and uniq_is_g1 uniq_is_g2 and \<open>M(a)\<close> \<open>M(b)\<close>
  have "z=z'" "y=y'" by blast+
  moreover note uniq_is_f and \<open>M(w)\<close> \<open>M(w')\<close>
  ultimately
  show ?thesis by blast
qed

lemma hcomp2_2_witness:
  assumes
    wit_is_f: "\<And>r1 r2. M(r1) \<Longrightarrow> M(r2) \<Longrightarrow> \<exists>d[M]. is_f(M,r1,r2,d)" and
    wit_is_g1: "\<And>r1 r2. M(r1) \<Longrightarrow> M(r2) \<Longrightarrow> \<exists>d[M]. is_g1(M,r1,r2,d)" and
    wit_is_g2: "\<And>r1 r2. M(r1) \<Longrightarrow> M(r2) \<Longrightarrow> \<exists>d[M]. is_g2(M,r1,r2,d)" and
    "M(a)" "M(b)"
  shows
    "\<exists>w[M]. is_hcomp2_2(M,is_f,is_g1,is_g2,a,b,w)"
proof -
  from \<open>M(a)\<close> \<open>M(b)\<close> and wit_is_g1
  obtain g1a where "is_g1(M,a,b,g1a)" "M(g1a)" by blast
  moreover from \<open>M(a)\<close> \<open>M(b)\<close> and wit_is_g2
  obtain g2a where "is_g2(M,a,b,g2a)" "M(g2a)" by blast
  moreover from calculation and wit_is_f
  obtain w where "is_f(M,g1a,g2a,w)" "M(w)" by blast
  ultimately
  show ?thesis
    using assms unfolding is_hcomp2_2_def by auto
qed

text\<open>The following named theorems gather instances of transitivity
that arise from closure theorems\<close>
named_theorems trans_closed

(******************************************************)
subsection\<open>Discipline for \<^term>\<open>Pow\<close>\<close>

definition
  is_Pow :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "is_Pow(N,A,z) \<equiv> \<forall>x[N]. x \<in> z \<longleftrightarrow> subset(N,x,A)"

reldb_add "Pow" "is_Pow"

context M_basic
begin

lemma is_Pow_uniqueness:
  assumes
    "M(r)" "M(d)" "M(d')"
    "is_Pow(M,r,d)" "is_Pow(M,r,d')"
  shows
    "d=d'"
  using assms extensionality_trans
  unfolding is_Pow_def
  by simp

lemma is_Pow_witness: "M(r) \<Longrightarrow> \<exists>d[M]. is_Pow(M,r,d)"
  using power_ax unfolding power_ax_def powerset_def is_Pow_def
  by simp \<comment> \<open>We have to do this by hand, using axioms\<close>

definition
  Pow_rel :: "i \<Rightarrow> i" where
  "Pow_rel(r) \<equiv> THE d. M(d) \<and> is_Pow(M,r,d)"

lemma Pow_rel_closed[intro,simp]: "M(r) \<Longrightarrow> M(Pow_rel(r))"
  unfolding Pow_rel_def
  using theI[OF ex1I[of "\<lambda>d. M(d) \<and> is_Pow(M,r,d)"], OF _ is_Pow_uniqueness[of r]]
    is_Pow_witness by auto

(* New element of Discipline: declaring transitivity rules*)
lemmas trans_Pow_rel_closed[trans_closed] = transM[OF _ Pow_rel_closed]

lemma Pow_rel_iff:
  assumes "M(r)"  "M(d)"
  shows "is_Pow(M,r,d) \<longleftrightarrow> d = Pow_rel(r)"
proof (intro iffI)
  assume "d = Pow_rel(r)"
  with assms
  show "is_Pow(M, r, d)"
    using is_Pow_uniqueness[of r] is_Pow_witness
      theI[OF ex1I[of "\<lambda>d. M(d) \<and> is_Pow(M,r,d)"], OF _ is_Pow_uniqueness[of r]]
    unfolding Pow_rel_def
    by auto
next
  assume "is_Pow(M, r, d)"
  with assms
  show "d = Pow_rel(r)"
    using is_Pow_uniqueness unfolding Pow_rel_def
    by (auto del:the_equality intro:the_equality[symmetric])
qed

text\<open>The next "def_" result really corresponds to @{thm Pow_iff}\<close>
lemma def_Pow_rel: "M(A) \<Longrightarrow> M(r) \<Longrightarrow> A\<in>Pow_rel(r) \<longleftrightarrow> A \<subseteq> r"
  using Pow_rel_iff[OF _ Pow_rel_closed, of r r]
  unfolding is_Pow_def by simp

(* New element of Discipline: a characterization result using as much
  absoluteness as possible  *)
lemma Pow_rel_char: "M(r) \<Longrightarrow> Pow_rel(r) = {A\<in>Pow(r). M(A)}"
proof -
  assume "M(r)"
  moreover from this
  have "x \<in> Pow_rel(r) \<Longrightarrow> x\<subseteq>r" "M(x) \<Longrightarrow> x \<subseteq> r \<Longrightarrow> x \<in> Pow_rel(r)" for x
    using def_Pow_rel by (auto intro!:trans_closed)
  ultimately
  show ?thesis
    using trans_closed by blast
qed

lemma mem_Pow_rel_abs: "M(a) \<Longrightarrow> M(r) \<Longrightarrow> a \<in> Pow_rel(r) \<longleftrightarrow> a \<in> Pow(r)"
  using Pow_rel_char by simp

end (* M_basic *)

(******************  end Discipline  **********************)


(**********************************************************)
subsection\<open>Discipline for \<^term>\<open>PiP\<close>\<close>

definition
  PiP_rel:: "[i\<Rightarrow>o,i,i]\<Rightarrow>o" where
  "PiP_rel(M,A,f) \<equiv> \<exists>df[M]. is_domain(M,f,df) \<and> subset(M,A,df) \<and>
                             is_function(M,f)"

context M_basic
begin

lemma def_PiP_rel:
  assumes
    "M(A)" "M(f)"
  shows
    "PiP_rel(M,A,f) \<longleftrightarrow> A \<subseteq> domain(f) \<and> function(f)"
  using assms unfolding PiP_rel_def by simp

end (* M_basic *)

(******************  end Discipline  **********************)

text\<open>A "Discipline" for terms involving \<^term>\<open>Replace\<close> is yet to
be established.\<close>
  (*
Sigma(A,B) == \<Union>x\<in>A. \<Union>y\<in>B(x). {\<langle>x,y\<rangle>}
           == \<Union> {  (\<Union>y\<in>B(x). {\<langle>x,y\<rangle>})  . x\<in>A}
           == \<Union> {  (\<Union>y\<in>B(x). {\<langle>x,y\<rangle>})  . x\<in>A}
           == \<Union> {  ( \<Union> { {\<langle>x,y\<rangle>} . y\<in>B(x)} )  . x\<in>A}
                     ----------------------
                           Sigfun(x,B)
*)

definition \<comment> \<open>FIX THIS: not completely relational. Can it be?\<close>
  Sigfun :: "[i,i\<Rightarrow>i]\<Rightarrow>i"  where
  "Sigfun(x,B) \<equiv> \<Union>y\<in>B(x). {\<langle>x,y\<rangle>}"

lemma Sigma_Sigfun: "Sigma(A,B) = \<Union> {Sigfun(x,B) . x\<in>A}"
  unfolding Sigma_def Sigfun_def ..

definition \<comment> \<open>FIX THIS: not completely relational. Can it be?\<close>
  is_Sigfun :: "[i\<Rightarrow>o,i,i\<Rightarrow>i,i]\<Rightarrow>o"  where
  "is_Sigfun(M,x,B,Sd) \<equiv> \<exists>RB[M]. is_Replace(M,B(x),\<lambda>y z. z={\<langle>x,y\<rangle>},RB)
                         \<and> big_union(M,RB,Sd)"

context M_trivial
begin

lemma is_Sigfun_abs:
  assumes
    "strong_replacement(M,\<lambda>y z. z={\<langle>x,y\<rangle>})"
    "M(x)" "M(B(x))" "M(Sd)"
  shows
    "is_Sigfun(M,x,B,Sd) \<longleftrightarrow> Sd = Sigfun(x,B)"
proof -
  have "\<Union>{z . y \<in> B(x), z = {\<langle>x, y\<rangle>}} = (\<Union>y\<in>B(x). {\<langle>x, y\<rangle>})" by auto
  then
  show ?thesis
    using assms transM[OF _ \<open>M(B(x))\<close>] Replace_abs
    unfolding is_Sigfun_def Sigfun_def by auto
qed

lemma Sigfun_closed:
  assumes
    "strong_replacement(M, \<lambda>y z. y \<in> B(x) \<and> z = {\<langle>x, y\<rangle>})"
    "M(x)" "M(B(x))"
  shows
    "M(Sigfun(x,B))"
  using assms transM[OF _ \<open>M(B(x))\<close>] RepFun_closed2
  unfolding Sigfun_def by simp

lemmas trans_Sigfun_closed[trans_closed] = transM[OF _ Sigfun_closed]

end (* M_trivial *)

definition
  is_Sigma :: "[i\<Rightarrow>o,i,i\<Rightarrow>i,i]\<Rightarrow>o"  where
  "is_Sigma(M,A,B,S) \<equiv> \<exists>RSf[M].
      is_Replace(M,A,\<lambda>x z. z=Sigfun(x,B),RSf) \<and> big_union(M,RSf,S)"

locale M_Pi = M_basic +
  assumes
    Pi_separation: "M(A) \<Longrightarrow> separation(M, \<lambda>f. \<exists>df[M].
           is_domain(M, f, df) \<and> subset(M,A,df) \<and> is_function(M, f))"
    and
    Pi_replacement:
    "M(A) \<Longrightarrow> M(y) \<Longrightarrow>
      \<forall>x\<in>A. strong_replacement(M, \<lambda>ya z. ya \<in> y \<and> z = {\<langle>x, ya\<rangle>})"
    "M(A) \<Longrightarrow> M(y) \<Longrightarrow>
      strong_replacement(M, \<lambda>x z. z = (\<Union>xa\<in>y. {\<langle>x, xa\<rangle>}))"

locale M_Pi_assumptions = M_Pi +
  fixes A B
  assumes
    Pi_assumptions:
    "\<forall>x\<in>A. strong_replacement(M, \<lambda>y z. y \<in> B(x) \<and> z = {\<langle>x, y\<rangle>})"
    "strong_replacement(M,\<lambda>x z. z=Sigfun(x,B))"
    "M(A)"
    "\<And>x. x\<in>A \<Longrightarrow>  M(B(x))"
begin

lemma Sigma_abs[simp]:
  assumes
    "M(S)"
  shows
    "is_Sigma(M,A,B,S) \<longleftrightarrow> S = Sigma(A,B)"
proof -
  have "\<Union>{z . x \<in> A, z = Sigfun(x, B)} = (\<Union>x\<in>A. Sigfun(x, B))"
    by auto
  with assms
  show ?thesis
    using Replace_abs[of A _ "\<lambda>x z. z=Sigfun(x,B)"]
      Sigfun_closed Sigma_Sigfun[of A B] transM[of _ A]
      Pi_assumptions
    unfolding is_Sigma_def by simp
qed

lemma Sigma_closed[intro,simp]: "M(Sigma(A,B))"
proof -
  have "(\<Union>x\<in>A. Sigfun(x, B)) = \<Union>{z . x \<in> A, z = Sigfun(x, B)}"
    by auto
  then
  show ?thesis
    using Sigma_Sigfun[of A B] transM[of _ A]
      Sigfun_closed Pi_assumptions
    by simp
qed

lemmas trans_Sigma_closed[trans_closed] = transM[OF _ Sigma_closed]

end (* M_Pi_assumptions *)

(**********************************************************)
subsection\<open>Discipline for \<^term>\<open>Pi\<close>\<close>

definition (* completely relational *)
  is_Pi :: "[i\<Rightarrow>o,i,i\<Rightarrow>i,i]\<Rightarrow>o"  where
  "is_Pi(M,A,B,I) \<equiv> \<exists>S[M]. \<exists>PS[M]. is_Sigma(M,A,B,S) \<and>
       is_Pow(M,S,PS) \<and>
       is_Collect(M,PS,PiP_rel(M,A),I)"

context M_Pi_assumptions
begin

lemma is_Pi_uniqueness:
  assumes
    "M(d)" "M(d')"
    "is_Pi(M,A,B,d)" "is_Pi(M,A,B,d')"
  shows
    "d=d'"
  using assms extensionality_trans Pi_assumptions
    Pow_rel_iff
  unfolding is_Pi_def by simp

lemma is_Pi_witness: "\<exists>d[M]. is_Pi(M,A,B,d)"
  using Pi_assumptions Pow_rel_iff
    Pi_assumptions Pi_separation
  unfolding is_Pi_def PiP_rel_def by simp

end (* M_Pi_assumptions *)

definition (in M_basic)
  Pi_rel :: "i \<Rightarrow> (i\<Rightarrow>i) \<Rightarrow> i"  where
  "Pi_rel(A,B) \<equiv> THE d. M(d) \<and> is_Pi(M,A,B,d)"

context M_Pi_assumptions
begin
  \<comment> \<open>From this point on, the higher order variable \<^term>\<open>y\<close> must be
explicitly instantiated, and proof methods are slower\<close>
lemma Pi_rel_closed[intro,simp]: "M(Pi_rel(A,B))"
  unfolding Pi_rel_def
  using theI[OF ex1I[of "\<lambda>d. M(d) \<and> is_Pi(M,A,B,d)"], OF _ is_Pi_uniqueness]
    is_Pi_witness by auto

lemmas trans_Pi_rel_closed[trans_closed] = transM[OF _ Pi_rel_closed]

lemma Pi_rel_iff:
  assumes "M(d)"
  shows "is_Pi(M,A,B,d) \<longleftrightarrow> d = Pi_rel(A,B)"
proof (intro iffI)
  assume "d = Pi_rel(A,B)"
  moreover
  note assms
  moreover from this
  obtain e where "M(e)" "is_Pi(M,A,B,e)"
    using is_Pi_witness by blast
  ultimately
  show "is_Pi(M, A, B, d)"
    using is_Pi_uniqueness is_Pi_witness
      theI[OF ex1I[of "\<lambda>d. M(d) \<and> is_Pi(M,A,B,d)"], OF _ is_Pi_uniqueness, of e]
    unfolding Pi_rel_def
    by auto
next
  assume "is_Pi(M, A, B, d)"
  with assms
  show "d = Pi_rel(A,B)"
    using is_Pi_uniqueness unfolding Pi_rel_def
    by (blast del:the_equality intro:the_equality[symmetric])
qed

lemma def_Pi_rel:
  "Pi_rel(A,B) = {f\<in>Pow_rel(Sigma(A,B)). A\<subseteq>domain(f) \<and> function(f)}"
proof -
  have "Pi_rel(A, B) \<subseteq> Pow_rel(Sigma(A,B))"
    using Pi_rel_iff[of "Pi_rel(A,B)"] Pi_assumptions Pow_rel_iff
    unfolding is_Pi_def by auto
  moreover
  have "f \<in> Pi_rel(A, B) \<Longrightarrow> A\<subseteq>domain(f) \<and> function(f)" for f
    using Pi_rel_iff[of "Pi_rel(A,B)"]
      Pi_assumptions def_PiP_rel[of A f] trans_closed Pow_rel_iff
    unfolding is_Pi_def by simp
  moreover
  have "f \<in> Pow_rel(Sigma(A,B)) \<Longrightarrow> A\<subseteq>domain(f) \<and> function(f) \<Longrightarrow> f \<in> Pi_rel(A, B)" for f
    using Pi_rel_iff[of "Pi_rel(A,B)"]
      Pi_assumptions def_PiP_rel[of A f] trans_closed Pow_rel_iff
    unfolding is_Pi_def by simp
  ultimately
  show ?thesis by force
qed

lemma Pi_rel_char: "Pi_rel(A,B) = {f\<in>Pi(A,B). M(f)}"
  using def_Pi_rel Pow_rel_char[OF Sigma_closed] unfolding Pi_def
  by fastforce

lemma mem_Pi_rel_abs: "M(f) \<Longrightarrow> f \<in> Pi_rel(A,B) \<longleftrightarrow> f \<in> Pi(A,B)"
  using Pi_rel_char by simp

end (* M_Pi_assumptions *)

text\<open>The next locale (and similar ones below) are used to
show the relationship between versions of simple (i.e. 
$\Sigma_1^{\mathit{ZF}}$, $\Pi_1^{\mathit{ZF}}$) concepts in two
different transitive models.\<close>
locale M_N_Pi_assumptions = M:M_Pi_assumptions + N:M_Pi_assumptions N for N +
  assumes
    M_imp_N:"M(x) \<Longrightarrow> N(x)"
begin

lemma Pi_rel_transfer: "M.Pi_rel(A,B) \<subseteq> N.Pi_rel(A,B)"
  using M.Pi_rel_char N.Pi_rel_char M_imp_N by auto

end (* M_N_Pi_assumptions *)


(******************  end Discipline  **********************)

locale M_Pi_assumptions_0 = M_Pi_assumptions _ 0
begin

text\<open>This is used in the proof of AC_Pi_rel\<close>
lemma Pi_rel_empty1[simp]: "Pi_rel(0,B) = {0}"
  using Pi_assumptions Pow_rel_char
  by (unfold def_Pi_rel function_def) (auto)

end (* M_Pi_assumptions_0 *)

context M_Pi_assumptions
begin

subsection\<open>Auxiliary ported results on \<^term>\<open>Pi_rel\<close>, now unused\<close>

lemma Pi_rel_iff':
  assumes types:"M(f)" "M(A)"
  shows
    "f \<in> Pi_rel(A,B) \<longleftrightarrow> function(f) \<and> f \<subseteq> Sigma(A,B) \<and> A \<subseteq> domain(f)"
  using assms Pow_rel_char
  by (simp add:def_Pi_rel, blast)

lemma (in M_Pi_assumptions) lam_type_M:
  assumes "\<And>x. x \<in> A \<Longrightarrow> b(x)\<in>B(x)" "strong_replacement(M,\<lambda>x y. y=\<langle>x, b(x)\<rangle>) "
  shows "(\<lambda>x\<in>A. b(x)) \<in> Pi_rel(A,B)"
proof (auto simp add: lam_def def_Pi_rel function_def)
  from assms
  have "M({\<langle>x, b(x)\<rangle> . x \<in> A})"
    using Pi_assumptions transM[OF _ Pi_assumptions(3)]
    by (rule_tac RepFun_closed, auto intro!:transM[OF _ Pi_assumptions(4)])
  with assms
  show "{\<langle>x, b(x)\<rangle> . x \<in> A} \<in> Pow_rel(Sigma(A, B))"
    using Pow_rel_char by auto
qed

end (* M_Pi_assumptions *)

locale M_Pi_assumptions2 = M_Pi_assumptions +
  PiC: M_Pi_assumptions _ _ C for C
begin

lemma Pi_rel_type:
  assumes "f \<in> Pi_rel(A,C)" "\<And>x. x \<in> A \<Longrightarrow> f`x \<in> B(x)"
    and types: "M(f)"
  shows "f \<in> Pi_rel(A,B)"
  using assms Pi_assumptions
  by (simp only: Pi_rel_iff' PiC.Pi_rel_iff')
    (blast dest: function_apply_equality)

lemma Pi_rel_weaken_type:
  assumes "f \<in> Pi_rel(A,B)" "\<And>x. x \<in> A \<Longrightarrow> B(x) \<subseteq> C(x)"
    and types: "M(f)"
  shows "f \<in> Pi_rel(A,C)"
  using assms Pi_assumptions
  by (simp only: Pi_rel_iff' PiC.Pi_rel_iff')
    (blast intro: Pi_rel_type  dest: apply_type)

end (* M_Pi_assumptions2 *)

(**********************************************************)
subsection\<open>Discipline for \<^term>\<open>function_space\<close>\<close>

abbreviation
  "is_function_space \<equiv> is_funspace"

context M_Pi
begin

lemma is_function_space_uniqueness:
  assumes
    "M(r)" "M(B)" "M(d)" "M(d')"
    "is_function_space(M,r,B,d)" "is_function_space(M,r,B,d')"
  shows
    "d=d'"
  using assms extensionality_trans
  unfolding is_funspace_def
  by simp

lemma is_function_space_witness:
  assumes "M(A)" "M(B)"
  shows "\<exists>d[M]. is_function_space(M,A,B,d)"
proof -
  from assms
  interpret M_Pi_assumptions M A "\<lambda>_. B"
    using Pi_replacement Pi_separation
    by unfold_locales (simp_all add:Sigfun_def)
  from assms
  have "\<forall>f[M]. f \<in> Pi_rel(A, \<lambda>_. B) \<longleftrightarrow> f \<in> A \<rightarrow> B"
    using Pi_rel_char by simp
  with assms
  show ?thesis unfolding is_funspace_def by auto
qed

definition
  function_space_rel :: "i \<Rightarrow> i \<Rightarrow> i" (infix \<open>\<rightarrow>r\<close> 60) where
  "A \<rightarrow>r B \<equiv> THE d. M(d) \<and> is_function_space(M,A,B,d)"

\<comment> \<open>adding closure to simpset and claset\<close>
lemma function_space_rel_closed[intro,simp]: "M(x) \<Longrightarrow> M(y) \<Longrightarrow> M(x \<rightarrow>r y)"
  unfolding function_space_rel_def
  using theI[OF ex1I[of "\<lambda>d. M(d) \<and> is_function_space(M,x,y,d)"], OF _ is_function_space_uniqueness[of x y]]
    is_function_space_witness by auto

lemmas trans_function_space_rel_closed[trans_closed] = transM[OF _ function_space_rel_closed]

lemma function_space_rel_iff:
  assumes "M(x)" "M(y)" "M(d)"
  shows "is_function_space(M,x,y,d) \<longleftrightarrow> d = x \<rightarrow>r y"
proof (intro iffI)
  assume "d = x \<rightarrow>r y"
  moreover
  note assms
  moreover from this
  obtain e where "M(e)" "is_function_space(M,x,y,e)"
    using is_function_space_witness by blast
  ultimately
  show "is_function_space(M, x, y, d)"
    using is_function_space_uniqueness[of x y] is_function_space_witness
      theI[OF ex1I[of "\<lambda>d. M(d) \<and> is_function_space(M,x,y,d)"], OF _ is_function_space_uniqueness[of x y], of e]
    unfolding function_space_rel_def
    by auto
next
  assume "is_function_space(M, x, y, d)"
  with assms
  show "d = x \<rightarrow>r y"
    using is_function_space_uniqueness unfolding function_space_rel_def
    by (blast del:the_equality intro:the_equality[symmetric])
qed

lemma def_function_space_rel:
  assumes "M(A)" "M(y)"
  shows "A \<rightarrow>r y = Pi_rel(A,\<lambda>_. y)"
proof -
  from assms
  interpret M_Pi_assumptions M A "\<lambda>_. y"
    using Pi_replacement Pi_separation
    by unfold_locales (simp_all add:Sigfun_def)
  from assms
  have "x\<in>A \<rightarrow>r y \<longleftrightarrow> x\<in>Pi_rel(A,\<lambda>_. y)" if "M(x)" for x
    using that
      function_space_rel_iff[of A y, OF _ _ function_space_rel_closed, of A y]
      def_Pi_rel Pi_rel_char Pow_rel_char
    unfolding is_funspace_def by (simp add:Pi_def)
  with assms
  show ?thesis \<comment> \<open>At this point, quoting "trans_rules" doesn't work\<close>
    using transM[OF _ function_space_rel_closed, OF _ \<open>M(A)\<close> \<open>M(y)\<close>]
      transM[OF _ Pi_rel_closed] by blast
qed

lemma function_space_rel_char:
  assumes "M(A)" "M(y)"
  shows "A \<rightarrow>r y = {f \<in> A \<rightarrow> y. M(f)}"
proof -
  from assms
  interpret M_Pi_assumptions M A "\<lambda>_. y"
    using Pi_replacement Pi_separation
    by unfold_locales (simp_all add:Sigfun_def)
  show ?thesis
    using assms def_function_space_rel Pi_rel_char
    by simp
qed

lemma mem_function_space_rel_abs:
  assumes "M(A)" "M(y)" "M(f)"
  shows "f \<in> A \<rightarrow>r y  \<longleftrightarrow>  f \<in> A \<rightarrow> y"
  using assms function_space_rel_char by simp

end (* M_Pi *)

locale M_N_Pi = M:M_Pi + N:M_Pi N for N +
  assumes
    M_imp_N:"M(x) \<Longrightarrow> N(x)"
begin
notation M.function_space_rel (infix \<open>\<rightarrow>\<^sup>M\<close> 60)
notation N.function_space_rel (infix \<open>\<rightarrow>\<^sup>N\<close> 60)

lemma function_space_rel_transfer: "M(A) \<Longrightarrow> M(B) \<Longrightarrow> A \<rightarrow>\<^sup>M B \<subseteq> A\<rightarrow>\<^sup>N B"
  using M.function_space_rel_char N.function_space_rel_char 
  by (auto dest!:M_imp_N)

end (* M_N_Pi *)

(*****************  end Discipline  ***********************)

abbreviation
  "is_apply \<equiv> fun_apply"
  \<comment> \<open>It is not necessary to perform the Discipline for \<^term>\<open>is_apply\<close>
  since it is absolute in this context\<close>

subsection\<open>Discipline for \<^term>\<open>Collect\<close> terms.\<close>

text\<open>We have to isolate the predicate involved and apply the
Discipline to it.\<close>

(*************** Discipline for injP ******************)

definition (* completely relational *)
  injP_rel:: "[i\<Rightarrow>o,i,i]\<Rightarrow>o" where
  "injP_rel(M,A,f) \<equiv> \<forall>w[M]. \<forall>x[M]. \<forall>fw[M]. \<forall>fx[M]. w\<in>A \<and> x\<in>A \<and>
            is_apply(M,f,w,fw) \<and> is_apply(M,f,x,fx) \<and> fw=fx\<longrightarrow> w=x"

context M_basic
begin

\<comment> \<open>I'm undecided on keeping the relative quantifiers here.
    Same with \<^term>\<open>surjP\<close> below. It might relieve from changing
    @{thm exI allI} to @{thm rexI rallI} in some proofs.
    I wonder if this escalates well. Assuming that all terms
    appearing in the "def_" theorem are in \<^term>\<open>M\<close> and using
    @{thm transM}, it might do.\<close>
lemma def_injP_rel:
  assumes
    "M(A)" "M(f)"
  shows
    "injP_rel(M,A,f) \<longleftrightarrow> (\<forall>w[M]. \<forall>x[M]. w\<in>A \<and> x\<in>A \<and> f`w=f`x \<longrightarrow> w=x)"
  using assms unfolding injP_rel_def by simp

end (* M_basic *)

(******************  end Discipline  **********************)

(**********************************************************)
subsection\<open>Discipline for \<^term>\<open>inj\<close>\<close>

definition (* completely relational *)
  is_inj   :: "[i\<Rightarrow>o,i,i,i]\<Rightarrow>o"  where
  "is_inj(M,A,B,I) \<equiv> \<exists>F[M]. is_function_space(M,A,B,F) \<and>
       is_Collect(M,F,injP_rel(M,A),I)"


locale M_inj = M_Pi +
  assumes
    injP_separation: "M(r) \<Longrightarrow> separation(M,\<lambda>x. injP_rel(M, r, x))"
begin

lemma is_inj_uniqueness:
  assumes
    "M(r)" "M(B)" "M(d)" "M(d')"
    "is_inj(M,r,B,d)" "is_inj(M,r,B,d')"
  shows
    "d=d'"
  using assms function_space_rel_iff extensionality_trans
  unfolding is_inj_def by simp

lemma is_inj_witness: "M(r) \<Longrightarrow> M(B)\<Longrightarrow> \<exists>d[M]. is_inj(M,r,B,d)"
  using injP_separation function_space_rel_iff
  unfolding is_inj_def by simp

definition
  inj_rel :: "i \<Rightarrow> i \<Rightarrow> i"  where
  "inj_rel(A,B) \<equiv> THE d. M(d) \<and> is_inj(M,A,B,d)"

lemma inj_rel_closed[intro,simp]: "M(x) \<Longrightarrow> M(y) \<Longrightarrow> M(inj_rel(x,y))"
  unfolding inj_rel_def
  using theI[OF ex1I[of "\<lambda>d. M(d) \<and> is_inj(M,x,y,d)"], OF _ is_inj_uniqueness[of x y]]
    is_inj_witness by auto

lemmas trans_inj_rel_closed[trans_closed] = transM[OF _ inj_rel_closed]

lemma inj_rel_iff:
  assumes "M(x)" "M(y)" "M(d)"
  shows "is_inj(M,x,y,d) \<longleftrightarrow> d = inj_rel(x,y)"
proof (intro iffI)
  assume "d = inj_rel(x,y)"
  moreover
  note assms
  moreover from this
  obtain e where "M(e)" "is_inj(M,x,y,e)"
    using is_inj_witness by blast
  ultimately
  show "is_inj(M, x, y, d)"
    using is_inj_uniqueness[of x y] is_inj_witness
      theI[OF ex1I[of "\<lambda>d. M(d) \<and> is_inj(M,x,y,d)"], OF _ is_inj_uniqueness[of x y], of e]
    unfolding inj_rel_def
    by auto
next
  assume "is_inj(M, x, y, d)"
  with assms
  show "d = inj_rel(x,y)"
    using is_inj_uniqueness unfolding inj_rel_def
    by (blast del:the_equality intro:the_equality[symmetric])
qed

lemma def_inj_rel:
  assumes "M(A)" "M(B)"
  shows "inj_rel(A,B) =
         {f \<in> A \<rightarrow>r B.  \<forall>w[M]. \<forall>x[M]. w\<in>A \<and> x\<in>A \<and> f`w = f`x \<longrightarrow> w=x}"
    (is "_ = Collect(_,?P)")
proof -
  from assms
  have "inj_rel(A, B) \<subseteq> A \<rightarrow>r B"
    using inj_rel_iff[of A B "inj_rel(A,B)"] function_space_rel_iff
    unfolding is_inj_def by auto
  moreover from assms
  have "f \<in> inj_rel(A, B) \<Longrightarrow> ?P(f)" for f
    using inj_rel_iff[of A B "inj_rel(A,B)"] function_space_rel_iff
      def_injP_rel transM[OF _ function_space_rel_closed, OF _ \<open>M(A)\<close> \<open>M(B)\<close>]
    unfolding is_inj_def by auto
  moreover from assms
  have "f \<in> A \<rightarrow>r B \<Longrightarrow> ?P(f) \<Longrightarrow> f \<in> inj_rel(A, B)" for f
    using inj_rel_iff[of A B "inj_rel(A,B)"] function_space_rel_iff
      def_injP_rel transM[OF _ function_space_rel_closed, OF _ \<open>M(A)\<close> \<open>M(B)\<close>]
    unfolding is_inj_def by auto
  ultimately
  show ?thesis by force
qed

lemma inj_rel_char:
  assumes "M(A)" "M(B)"
  shows "inj_rel(A,B) = {f \<in> inj(A,B). M(f)}"
proof -
  from assms
  interpret M_Pi_assumptions M A "\<lambda>_. B"
    using Pi_replacement Pi_separation
    by unfold_locales (simp_all add:Sigfun_def)
  from assms
  show ?thesis
    using def_inj_rel[OF assms] def_function_space_rel[OF assms]
      transM[OF _ \<open>M(A)\<close>] Pi_rel_char
    unfolding inj_def
    by auto
qed

end (* M_inj *)

locale M_N_inj = M:M_inj + N:M_inj N for N +
  assumes
    M_imp_N:"M(x) \<Longrightarrow> N(x)"
begin
notation M.inj_rel (\<open>inj\<^sup>M\<close>)
notation N.inj_rel (\<open>inj\<^sup>N\<close>)

lemma inj_rel_transfer: "M(A) \<Longrightarrow> M(B) \<Longrightarrow> inj\<^sup>M(A,B) \<subseteq> inj\<^sup>N(A,B)"
  using M.inj_rel_char N.inj_rel_char 
  by (auto dest!:M_imp_N)

end (* M_N_inj *)


(***************  end Discipline  *********************)

(*************** Discipline for surjP ******************)

definition
  surjP_rel:: "[i\<Rightarrow>o,i,i,i]\<Rightarrow>o" where
  "surjP_rel(M,A,B,f) \<equiv> \<forall>y[M]. \<exists>x[M]. \<exists>fx[M]. y\<in>B \<longrightarrow> x\<in>A \<and> is_apply(M,f,x,fx) \<and> fx=y"

context M_basic
begin

lemma def_surjP_rel:
  assumes
    "M(A)" "M(B)" "M(f)"
  shows
    "surjP_rel(M,A,B,f) \<longleftrightarrow> (\<forall>y[M]. \<exists>x[M]. y\<in>B \<longrightarrow> x\<in>A \<and> f`x=y)"
  using assms unfolding surjP_rel_def by auto

end (* M_basic *)

(******************  end Discipline  **********************)

(**********************************************************)
subsection\<open>Discipline for \<^term>\<open>surj\<close>\<close>

definition (* completely relational *)
  is_surj   :: "[i\<Rightarrow>o,i,i,i]\<Rightarrow>o"  where
  "is_surj(M,A,B,I) \<equiv> \<exists>F[M]. is_function_space(M,A,B,F) \<and>
       is_Collect(M,F,surjP_rel(M,A,B),I)"


locale M_surj = M_Pi +
  assumes
    surjP_separation: "M(A)\<Longrightarrow>M(B)\<Longrightarrow>separation(M,\<lambda>x. surjP_rel(M,A,B,x))"
begin

lemma is_surj_uniqueness:
  assumes
    "M(r)" "M(B)" "M(d)" "M(d')"
    "is_surj(M,r,B,d)" "is_surj(M,r,B,d')"
  shows
    "d=d'"
  using assms function_space_rel_iff extensionality_trans
  unfolding is_surj_def by simp

lemma is_surj_witness: "M(r) \<Longrightarrow> M(B)\<Longrightarrow> \<exists>d[M]. is_surj(M,r,B,d)"
  using surjP_separation function_space_rel_iff
  unfolding is_surj_def by simp

definition
  surj_rel :: "i \<Rightarrow> i \<Rightarrow> i"  where
  "surj_rel(A,B) \<equiv> THE d. M(d) \<and> is_surj(M,A,B,d)"

lemma surj_rel_closed[intro,simp]: "M(x) \<Longrightarrow> M(y) \<Longrightarrow> M(surj_rel(x,y))"
  unfolding surj_rel_def
  using theI[OF ex1I[of "\<lambda>d. M(d) \<and> is_surj(M,x,y,d)"], OF _ is_surj_uniqueness[of x y]]
    is_surj_witness by auto

lemmas trans_surj_rel_closed[trans_closed] = transM[OF _ surj_rel_closed]

lemma surj_rel_iff:
  assumes "M(x)" "M(y)" "M(d)"
  shows "is_surj(M,x,y,d) \<longleftrightarrow> d = surj_rel(x,y)"
proof (intro iffI)
  assume "d = surj_rel(x,y)"
  moreover
  note assms
  moreover from this
  obtain e where "M(e)" "is_surj(M,x,y,e)"
    using is_surj_witness by blast
  ultimately
  show "is_surj(M, x, y, d)"
    using is_surj_uniqueness[of x y] is_surj_witness
      theI[OF ex1I[of "\<lambda>d. M(d) \<and> is_surj(M,x,y,d)"], OF _ is_surj_uniqueness[of x y], of e]
    unfolding surj_rel_def
    by auto
next
  assume "is_surj(M, x, y, d)"
  with assms
  show "d = surj_rel(x,y)"
    using is_surj_uniqueness unfolding surj_rel_def
    by (blast del:the_equality intro:the_equality[symmetric])
qed

lemma def_surj_rel:
  assumes "M(A)" "M(B)"
  shows "surj_rel(A,B) =
         {f \<in> A \<rightarrow>r B. \<forall>y[M]. \<exists>x[M]. y\<in>B \<longrightarrow> x\<in>A \<and> f`x=y }"
    (is "_ = Collect(_,?P)")
proof -
  from assms
  have "surj_rel(A, B) \<subseteq> A \<rightarrow>r B"
    using surj_rel_iff[of A B "surj_rel(A,B)"] function_space_rel_iff
    unfolding is_surj_def by auto
  moreover from assms
  have "f \<in> surj_rel(A, B) \<Longrightarrow> ?P(f)" for f
    using surj_rel_iff[of A B "surj_rel(A,B)"] function_space_rel_iff
      def_surjP_rel transM[OF _ function_space_rel_closed, OF _ \<open>M(A)\<close> \<open>M(B)\<close>]
    unfolding is_surj_def by auto
  moreover from assms
  have "f \<in> A \<rightarrow>r B \<Longrightarrow> ?P(f) \<Longrightarrow> f \<in> surj_rel(A, B)" for f
    using surj_rel_iff[of A B "surj_rel(A,B)"] function_space_rel_iff
      def_surjP_rel transM[OF _ function_space_rel_closed, OF _ \<open>M(A)\<close> \<open>M(B)\<close>]
    unfolding is_surj_def by auto
  ultimately
  show ?thesis by force
qed

lemma surj_rel_char:
  assumes "M(A)" "M(B)"
  shows "surj_rel(A,B) = {f \<in> surj(A,B). M(f)}"
proof -
  from assms
  interpret M_Pi_assumptions M A "\<lambda>_. B"
    using Pi_replacement Pi_separation
    by unfold_locales (simp_all add:Sigfun_def)
  from assms
  show ?thesis
    using def_surj_rel[OF assms] def_function_space_rel[OF assms]
      transM[OF _ \<open>M(A)\<close>] transM[OF _ \<open>M(B)\<close>] Pi_rel_char
    unfolding surj_def
    by auto
qed

end (* M_surj *)

locale M_N_surj = M:M_surj + N:M_surj N for N +
  assumes
    M_imp_N:"M(x) \<Longrightarrow> N(x)"
begin
notation M.surj_rel (\<open>surj\<^sup>M\<close>)
notation N.surj_rel (\<open>surj\<^sup>N\<close>)

lemma surj_rel_transfer: "M(A) \<Longrightarrow> M(B) \<Longrightarrow> surj\<^sup>M(A,B) \<subseteq> surj\<^sup>N(A,B)"
  using M.surj_rel_char N.surj_rel_char 
  by (auto dest!:M_imp_N)

end (* M_N_surj *)

(***************  end Discipline  *********************)

definition
  is_Int :: "[i\<Rightarrow>o,i,i,i]\<Rightarrow>o"  where
  "is_Int(M,A,B,I) \<equiv> \<forall>x[M]. x \<in> I \<longleftrightarrow> x \<in> A \<and> x \<in> B"

context M_basic
begin

lemma is_Int_abs:
  assumes
    "M(A)" "M(B)" "M(I)"
  shows
    "is_Int(M,A,B,I) \<longleftrightarrow> I = A \<inter> B"
  using assms transM[OF _ \<open>M(B)\<close>] transM[OF _ \<open>M(I)\<close>]
  unfolding is_Int_def by blast

lemma is_Int_uniqueness:
  assumes
    "M(r)" "M(B)" "M(d)" "M(d')"
    "is_Int(M,r,B,d)" "is_Int(M,r,B,d')"
  shows
    "d=d'"
  using assms is_Int_abs by simp

text\<open>Note: @{thm Int_closed} already in \<^theory>\<open>ZF-Constructible.Relative\<close>.\<close>

end (* M_trivial *)

(**********************************************************)
subsection\<open>Discipline for \<^term>\<open>bij\<close>\<close>

definition (* completely relational *)
  is_bij   :: "[i\<Rightarrow>o,i,i,i]\<Rightarrow>o"  where
  "is_bij(M,A,B,bj) \<equiv> is_hcomp2_2(M,is_Int,is_inj,is_surj,A,B,bj)"
  (* Old def: "is_bij(M,A,B,bj) \<equiv> \<exists>I[M]. \<exists>S[M].
      is_inj(M,A,B,I) \<and> is_surj(M,A,B,S) \<and> is_Int(M,I,S,bj)" *)

locale M_Perm = M_Pi + M_inj + M_surj
begin

lemma is_bij_uniqueness:
  assumes
    "M(A)" "M(B)" "M(d)" "M(d')"
    "is_bij(M,A,B,d)" "is_bij(M,A,B,d')"
  shows
    "d=d'"
  using assms hcomp2_2_uniqueness[of M is_Int is_inj is_surj A B]
    is_Int_uniqueness is_inj_uniqueness is_surj_uniqueness
  unfolding is_bij_def
  by auto

lemma is_bij_witness: "M(A) \<Longrightarrow> M(B)\<Longrightarrow> \<exists>d[M]. is_bij(M,A,B,d)"
  using hcomp2_2_witness[of M is_Int is_inj is_surj A B]
    is_inj_witness is_surj_witness is_Int_abs
  unfolding is_bij_def by simp

definition
  bij_rel :: "i \<Rightarrow> i \<Rightarrow> i"  where
  "bij_rel(A,B) \<equiv> THE d. M(d) \<and> is_bij(M,A,B,d)"

lemma bij_rel_closed[intro,simp]: "M(x) \<Longrightarrow> M(y) \<Longrightarrow> M(bij_rel(x,y))"
  unfolding bij_rel_def
  using theI[OF ex1I[of "\<lambda>d. M(d) \<and> is_bij(M,x,y,d)"], OF _ is_bij_uniqueness[of x y]]
    is_bij_witness by auto

lemmas trans_bij_rel_closed[trans_closed] = transM[OF _ bij_rel_closed]

lemma bij_rel_iff:
  assumes "M(x)" "M(y)" "M(d)"
  shows "is_bij(M,x,y,d) \<longleftrightarrow> d = bij_rel(x,y)"
proof (intro iffI)
  assume "d = bij_rel(x,y)"
  moreover
  note assms
  moreover from this
  obtain e where "M(e)" "is_bij(M,x,y,e)"
    using is_bij_witness by blast
  ultimately
  show "is_bij(M, x, y, d)"
    using is_bij_uniqueness[of x y] is_bij_witness
      theI[OF ex1I[of "\<lambda>d. M(d) \<and> is_bij(M,x,y,d)"], OF _ is_bij_uniqueness[of x y], of e]
    unfolding bij_rel_def
    by auto
next
  assume "is_bij(M, x, y, d)"
  with assms
  show "d = bij_rel(x,y)"
    using is_bij_uniqueness unfolding bij_rel_def
    by (blast del:the_equality intro:the_equality[symmetric])
qed

lemma def_bij_rel:
  assumes "M(A)" "M(B)"
  shows "bij_rel(A,B) = inj_rel(A,B) \<inter> surj_rel(A,B)"
  using assms bij_rel_iff inj_rel_iff surj_rel_iff
    is_Int_abs\<comment> \<open>For absolute terms, "_abs" replaces "_iff".
                 Also, in this case "_closed" is in the simpset.\<close>
    hcomp2_2_abs
  unfolding is_bij_def by simp

lemma bij_rel_char:
  assumes "M(A)" "M(B)"
  shows "bij_rel(A,B) = {f \<in> bij(A,B). M(f)}"
  using assms def_bij_rel inj_rel_char surj_rel_char
  unfolding bij_def\<comment> \<open>Unfolding this might be a pattern already\<close>
  by auto

end (* M_Perm *)

locale M_N_Perm = M_N_Pi + M_N_inj + M_N_surj + M:M_Perm + N:M_Perm N

begin
notation M.bij_rel (\<open>bij\<^sup>M\<close>)
notation N.bij_rel (\<open>bij\<^sup>N\<close>)

lemma bij_rel_transfer: "M(A) \<Longrightarrow> M(B) \<Longrightarrow> bij\<^sup>M(A,B) \<subseteq> bij\<^sup>N(A,B)"
  using M.bij_rel_char N.bij_rel_char 
  by (auto dest!:M_imp_N)

end (* M_N_Perm *)

(***************  end Discipline  *********************)

(******************************************************)
subsection\<open>Discipline for \<^term>\<open>eqpoll\<close>\<close>

definition (* completely relational *)
  eqpoll_rel   :: "[i=>o,i,i] => o" where
  "eqpoll_rel(M,A,B) \<equiv> \<exists>bi[M]. \<exists>f[M]. is_bij(M,A,B,bi) \<and> f\<in>bi"

context M_Perm
begin

abbreviation
  Eqpoll_rel   :: "[i,i] => o"     (infixl \<open>\<approx>r\<close> 50)  where
  "A \<approx>r B \<equiv> eqpoll_rel(M,A,B)"

lemma def_eqpoll_rel:
  assumes
    "M(A)" "M(B)"
  shows
    "A \<approx>r B \<longleftrightarrow> (\<exists>f[M]. f \<in> bij_rel(A,B))"
  using assms bij_rel_iff
  unfolding eqpoll_rel_def by simp

end (* M_Perm *)

context M_N_Perm
begin

notation M.Eqpoll_rel (infixl \<open>\<approx>\<^sup>M\<close> 50)
notation N.Eqpoll_rel (infixl \<open>\<approx>\<^sup>N\<close> 50)

lemma eqpoll_rel_transfer: assumes "A \<approx>\<^sup>M B" "M(A)" "M(B)" 
  shows "A \<approx>\<^sup>N B"
proof -
  note assms
  moreover from this
  obtain f where "f \<in> bij\<^sup>M(A,B)" "N(f)"
    using M.def_eqpoll_rel by (auto dest!:M_imp_N)
  moreover from calculation
  have "f \<in> bij\<^sup>N(A,B)"
    using bij_rel_transfer by (auto)
  ultimately
  show ?thesis
    using N.def_eqpoll_rel by (blast dest!:M_imp_N)
qed

end (* M_N_Perm *)

(******************  end Discipline  ******************)

(******************************************************)
subsection\<open>Discipline for \<^term>\<open>lepoll\<close>\<close>

definition (* completely relational *)
  lepoll_rel   :: "[i=>o,i,i] => o" where
  "lepoll_rel(M,A,B) \<equiv> \<exists>bi[M]. \<exists>f[M]. is_inj(M,A,B,bi) \<and> f\<in>bi"

context M_Perm
begin

abbreviation
  Lepoll_rel   :: "[i,i] => o"     (infixl \<open>\<lesssim>r\<close> 50)  where
  "A \<lesssim>r B \<equiv> lepoll_rel(M,A,B)"

lemma def_lepoll_rel:
  assumes
    "M(A)" "M(B)"
  shows
    "A \<lesssim>r B \<longleftrightarrow> (\<exists>f[M]. f \<in> inj_rel(A,B))"
  using assms inj_rel_iff
  unfolding lepoll_rel_def by simp

end (* M_Perm *)

context M_N_Perm
begin

notation M.Lepoll_rel (infixl \<open>\<lesssim>\<^sup>M\<close> 50)
notation N.Lepoll_rel (infixl \<open>\<lesssim>\<^sup>N\<close> 50)

lemma lepoll_rel_transfer: assumes "A \<lesssim>\<^sup>M B" "M(A)" "M(B)" 
  shows "A \<lesssim>\<^sup>N B"
proof -
  note assms
  moreover from this
  obtain f where "f \<in> inj\<^sup>M(A,B)" "N(f)"
    using M.def_lepoll_rel by (auto dest!:M_imp_N)
  moreover from calculation
  have "f \<in> inj\<^sup>N(A,B)"
    using inj_rel_transfer by (auto)
  ultimately
  show ?thesis
    using N.def_lepoll_rel by (blast dest!:M_imp_N)
qed

end (* M_N_Perm *)

(******************  end Discipline  ******************)

(******************************************************)
subsection\<open>Discipline for \<^term>\<open>lesspoll\<close>\<close>

definition
  lesspoll_rel :: "[i=>o,i,i] => o" where
  "lesspoll_rel(M,A,B) \<equiv> lepoll_rel(M,A,B) \<and> \<not>(eqpoll_rel(M,A,B))"

context M_Perm
begin

abbreviation
  Lesspoll_rel   :: "[i,i] => o"     (infixl \<open>\<prec>r\<close> 50)  where
  "A \<prec>r B \<equiv> lesspoll_rel(M,A,B)"

lemma def_lesspoll_rel:
  assumes
    "M(A)" "M(B)"
  shows
    "A \<prec>r B \<longleftrightarrow> A \<lesssim>r B \<and> \<not>(A \<approx>r B)"
  using assms unfolding lesspoll_rel_def by simp

text\<open>Note that \<^term>\<open>(\<lesssim>r)\<close> is neither $\Sigma_1^{\mathit{ZF}}$ nor
 $\Pi_1^{\mathit{ZF}}$, so there is no “transfer” theorem for it.\<close>

end (* M_Perm *)

(******************  end Discipline  ******************)

end