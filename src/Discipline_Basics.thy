theory Discipline_Basics
  imports
    Least
    "HOL-Eisbach.Eisbach_Old_Appl_Syntax"\<comment> \<open>if put before, it breaks some simps\<close>
    "../Tools/Try0"
begin

lemma (in M_basic) extensionality_trans: \<comment> \<open>General preliminary result\<close>
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

(**********************************************************)
subsection\<open>Discipline for \<^term>\<open>function_space\<close>\<close>

abbreviation
  "is_function_space \<equiv> is_funspace"

context M_basic
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

lemma is_function_space_witness: "M(r) \<Longrightarrow> M(B)\<Longrightarrow> \<exists>d[M]. is_function_space(M,r,B,d)"
  unfolding is_funspace_def
  sorry \<comment> \<open>We have to do this by hand, assuming axiom instance for \<^term>\<open>M\<close>\<close>

definition
  function_space_rel :: "i \<Rightarrow> i \<Rightarrow> i" (infix \<open>\<rightarrow>r\<close> 60) where
  "A \<rightarrow>r B \<equiv> THE d. M(d) \<and> is_function_space(M,A,B,d)"

\<comment> \<open>adding closure to simpset and claset\<close>
lemma function_space_rel_closed[intro,simp]: "M(x) \<Longrightarrow> M(y) \<Longrightarrow> M(x \<rightarrow>r y)"
  unfolding function_space_rel_def
  using theI[OF ex1I[of "\<lambda>d. M(d) \<and> is_function_space(M,x,y,d)"], OF _ is_function_space_uniqueness[of x y]]
    is_function_space_witness by auto

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

(*
lemma def_function_space_rel: "M(x) \<Longrightarrow> M(y) \<Longrightarrow> x \<rightarrow>r y = \<dots>"
  using  least_abs function_space_rel_closed function_space_rel_iff
  unfolding is_function_space_def by fastforce
*)
end (* M_basic *)

(*****************  end Discipline  ***********************)

abbreviation
  "is_apply \<equiv> fun_apply"
  \<comment> \<open>It is not necessary to perform the Discipline for \<^term>\<open>is_apply\<close>
  since it is absolute in this context\<close>

subsection\<open>Discipline for \<^term>\<open>Collect\<close> terms.\<close>

text\<open>We have to isolate the predicate involved and apply the
Discipline to it.\<close>

definition
  injP_rel:: "[i\<Rightarrow>o,i,i]\<Rightarrow>o" where
  "injP_rel(M,A,f) \<equiv> \<forall>w[M]. \<forall>x[M]. \<forall>fw[M]. \<forall>fx[M]. w\<in>A \<and> x\<in>A \<and>
            is_apply(M,f,w,fw) \<and> is_apply(M,f,x,fx) \<and> fw=fx\<longrightarrow> w=x"

context M_basic
begin

(*************** Discipline for injP_rel ******************)

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

context M_basic
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
  unfolding is_inj_def injP_rel_def
  sorry \<comment> \<open>We have to do this by hand, assuming axiom instance for \<^term>\<open>M\<close>\<close>

definition
  inj_rel :: "i \<Rightarrow> i \<Rightarrow> i"  where
  "inj_rel(A,B) \<equiv> THE d. M(d) \<and> is_inj(M,A,B,d)"

lemma inj_rel_closed: "M(x) \<Longrightarrow> M(y) \<Longrightarrow> M(inj_rel(x,y))"
  unfolding inj_rel_def
  using theI[OF ex1I[of "\<lambda>d. M(d) \<and> is_inj(M,x,y,d)"], OF _ is_inj_uniqueness[of x y]]
    is_inj_witness by auto

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
    using inj_rel_iff[of A B "inj_rel(A,B)"] inj_rel_closed function_space_rel_iff
    unfolding is_inj_def by auto
  moreover from assms
  have "f \<in> inj_rel(A, B) \<Longrightarrow> ?P(f)" for f
    using inj_rel_iff[of A B "inj_rel(A,B)"] inj_rel_closed function_space_rel_iff
      def_injP_rel transM[OF _ function_space_rel_closed, OF _ \<open>M(A)\<close> \<open>M(B)\<close>]
    unfolding is_inj_def by auto
  moreover from assms
  have "f \<in> A \<rightarrow>r B \<Longrightarrow> ?P(f) \<Longrightarrow> f \<in> inj_rel(A, B)" for f
    using inj_rel_iff[of A B "inj_rel(A,B)"] inj_rel_closed function_space_rel_iff
      def_injP_rel transM[OF _ function_space_rel_closed, OF _ \<open>M(A)\<close> \<open>M(B)\<close>]
    unfolding is_inj_def by auto
  ultimately
  show ?thesis by force
qed

end (* M_basic *)

(***************  end Discipline  *********************)

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

lemma Pow_rel_closed: "M(r) \<Longrightarrow> M(Pow_rel(r))"
  unfolding Pow_rel_def
  using theI[OF ex1I[of "\<lambda>d. M(d) \<and> is_Pow(M,r,d)"], OF _ is_Pow_uniqueness[of r]]
    is_Pow_witness by auto

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

(**********************************************************)
subsection\<open>Discipline for \<^term>\<open>Sigma\<close>\<close>

definition (* FAKE *)
  is_Sigma   :: "[i\<Rightarrow>o,i,i\<Rightarrow>i,i]\<Rightarrow>o"  where
  "is_Sigma(M,A,B,I) \<equiv> I = Sigma(A,B)"

context M_basic
begin

lemma is_Sigma_uniqueness:
  assumes
    "M(r)" "\<And>i. M(i) \<Longrightarrow> M(y(i))" "M(d)" "M(d')"
    "is_Sigma(M,r,y,d)" "is_Sigma(M,r,y,d')"
  shows
    "d=d'"
  using assms extensionality_trans
  unfolding is_Sigma_def by simp

lemma is_Sigma_witness: "M(r) \<Longrightarrow> (\<And>i. M(i) \<Longrightarrow> M(B(i))) \<Longrightarrow> \<exists>d[M]. is_Sigma(M,r,B,d)"
  unfolding is_Sigma_def
  sorry \<comment> \<open>We have to do this by hand, assuming axiom instance for \<^term>\<open>M\<close>\<close>

definition
  Sigma_rel :: "i \<Rightarrow> (i\<Rightarrow>i) \<Rightarrow> i"  where
  "Sigma_rel(A,B) \<equiv> THE d. M(d) \<and> is_Sigma(M,A,B,d)"

\<comment> \<open>From this point on, the higher order variable \<^term>\<open>y\<close> must be
explicitly instantiated, and proof methods are slower\<close>
lemma Sigma_rel_closed:
  "M(x) \<Longrightarrow> (\<And>i. M(i) \<Longrightarrow> M(y(i))) \<Longrightarrow> M(Sigma_rel(x,y))"
  unfolding Sigma_rel_def
  using theI[OF ex1I[of "\<lambda>d. M(d) \<and> is_Sigma(M,x,y,d)"], OF _ is_Sigma_uniqueness[of x y]]
    is_Sigma_witness[of _ y] by fastforce

lemma Sigma_rel_iff:
  assumes "M(x)" "(\<And>i. M(i) \<Longrightarrow> M(y(i)))" "M(d)"
  shows "is_Sigma(M,x,y,d) \<longleftrightarrow> d = Sigma_rel(x,y)"
proof (intro iffI)
  assume "d = Sigma_rel(x,y)"
  moreover
  note assms
  moreover from this
  obtain e where "M(e)" "is_Sigma(M,x,y,e)"
    using is_Sigma_witness[of _ y] by blast
  ultimately
  show "is_Sigma(M, x, y, d)"
    using is_Sigma_uniqueness[of x y] is_Sigma_witness
      theI[OF ex1I[of "\<lambda>d. M(d) \<and> is_Sigma(M,x,y,d)"], OF _ is_Sigma_uniqueness[of x y], of e]
    unfolding Sigma_rel_def
    by auto
next
  assume "is_Sigma(M, x, y, d)"
  with assms
  show "d = Sigma_rel(x,y)"
    using is_Sigma_uniqueness[of _ y] unfolding Sigma_rel_def
    by (blast del:the_equality intro:the_equality[symmetric])
qed


lemma def_Sigma_rel: \<comment> \<open>FAKE!\<close>
  assumes "M(A)" "(\<And>i. M(i) \<Longrightarrow> M(B(i)))"
  shows "Sigma_rel(A,B) = Sigma(A,B)"
  using assms Sigma_rel_iff Sigma_rel_closed
  unfolding is_Sigma_def by simp

end (* M_basic *)

(******************  end Discipline  **********************)

(**********************************************************)
subsection\<open>Discipline for \<^term>\<open>Pi\<close>\<close>

definition (* completely relational *)
  is_Pi   :: "[i\<Rightarrow>o,i,i\<Rightarrow>i,i]\<Rightarrow>o"  where
  "is_Pi(M,A,B,I) \<equiv> \<exists>F[M]. is_Sigma(M,A,B,F) \<and>
       is_Collect(M,F,PiP_rel(M,A),I)"

context M_basic
begin

lemma is_Pi_uniqueness:
  assumes
    "M(r)" "(\<And>i. M(i) \<Longrightarrow> M(B(i)))" "M(d)" "M(d')"
    "is_Pi(M,r,B,d)" "is_Pi(M,r,B,d')"
  shows
    "d=d'"
  using assms Sigma_rel_iff extensionality_trans
  unfolding is_Pi_def by simp

lemma is_Pi_witness: "M(r) \<Longrightarrow> (\<And>i. M(i) \<Longrightarrow> M(B(i))) \<Longrightarrow> \<exists>d[M]. is_Pi(M,r,B,d)"
  unfolding is_Pi_def PiP_rel_def
  sorry \<comment> \<open>We have to do this by hand, assuming axiom instance for \<^term>\<open>M\<close>\<close>

definition
  Pi_rel :: "i \<Rightarrow> (i\<Rightarrow>i) \<Rightarrow> i"  where
  "Pi_rel(A,B) \<equiv> THE d. M(d) \<and> is_Pi(M,A,B,d)"

lemma Pi_rel_closed: "M(x) \<Longrightarrow> (\<And>i. M(i) \<Longrightarrow> M(y(i))) \<Longrightarrow> M(Pi_rel(x,y))"
  unfolding Pi_rel_def
  using theI[OF ex1I[of "\<lambda>d. M(d) \<and> is_Pi(M,x,y,d)"], OF _ is_Pi_uniqueness[of x y]]
    is_Pi_witness[of _ y] by fastforce

lemma Pi_rel_iff:
  assumes "M(x)" "(\<And>i. M(i) \<Longrightarrow> M(y(i)))" "M(d)"
  shows "is_Pi(M,x,y,d) \<longleftrightarrow> d = Pi_rel(x,y)"
proof (intro iffI)
  assume "d = Pi_rel(x,y)"
  moreover
  note assms
  moreover from this
  obtain e where "M(e)" "is_Pi(M,x,y,e)"
    using is_Pi_witness[of _ y] by blast
  ultimately
  show "is_Pi(M, x, y, d)"
    using is_Pi_uniqueness[of x y] is_Pi_witness
      theI[OF ex1I[of "\<lambda>d. M(d) \<and> is_Pi(M,x,y,d)"], OF _ is_Pi_uniqueness[of x y], of e]
    unfolding Pi_rel_def
    by auto
next
  assume "is_Pi(M, x, y, d)"
  with assms
  show "d = Pi_rel(x,y)"
    using is_Pi_uniqueness[of _ y] unfolding Pi_rel_def
    by (blast del:the_equality intro:the_equality[symmetric])
qed

lemma def_Pi_rel:
  assumes "M(A)" "(\<And>i. M(i) \<Longrightarrow> M(B(i)))"
  shows "Pi_rel(A,B) =
         {f \<in> Sigma_rel(A,B).  A \<subseteq> domain(f) \<and> function(f)}"
         (is "_ = Collect(_,?P)")
proof -
  from assms
  have "Pi_rel(A, B) \<subseteq> Sigma_rel(A,B)"
    using Pi_rel_iff[of A B "Pi_rel(A,B)"] Pi_rel_closed Sigma_rel_iff
    unfolding is_Pi_def by auto
  moreover from assms
  have "f \<in> Pi_rel(A, B) \<Longrightarrow> ?P(f)" for f
    using Pi_rel_iff[of A B "Pi_rel(A,B)"] Pi_rel_closed Sigma_rel_iff
      def_PiP_rel transM[OF _ Sigma_rel_closed, OF _ \<open>M(A)\<close>]
    unfolding is_Pi_def by auto
  moreover from assms
  have "f \<in> Sigma_rel(A,B) \<Longrightarrow> ?P(f) \<Longrightarrow> f \<in> Pi_rel(A, B)" for f
    using Pi_rel_iff[of A B "Pi_rel(A,B)"] Pi_rel_closed Sigma_rel_iff
      def_PiP_rel transM[OF _ Sigma_rel_closed, OF _ \<open>M(A)\<close>]
    unfolding is_Pi_def by auto
  ultimately
  show ?thesis by force
qed
end (* M_basic *)

(******************  end Discipline  **********************)


end