theory Discipline_Basics
  imports
    Least
    "HOL-Eisbach.Eisbach_Old_Appl_Syntax"
    "../Tools/Try0"
begin

abbreviation
  "is_function_space \<equiv> is_funspace"

context M_basic
begin
lemma extensionality_trans: \<comment> \<open>General preliminary result\<close>
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

(************* Discipline for is_function_space ****************)

lemma is_function_space_uniqueness:
  assumes
    "M(r)" "M(B)" "M(d)" "M(d')"
    "is_function_space(M,r,B,d)" "is_function_space(M,r,B,d')"
  shows
    "d=d'"
  using assms
    extensionality_trans [where P="\<lambda>f. typed_function(M, r, B, f)"]
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

(***************  end Discipline  *********************)

end (* M_basic *)

abbreviation
  "is_apply \<equiv> fun_apply"

\<comment> \<open>It is not necessary to perform the Discipline for \<^term>\<open>is_apply\<close>
  since it is absolute in this context\<close>

definition (* completely relational *)
  is_inj   :: "[i\<Rightarrow>o,i,i,i]\<Rightarrow>o"  where
  "is_inj(M,A,B,I) \<equiv> \<exists>F[M]. is_function_space(M,A,B,F) \<and>
       is_Collect(M,F,
        \<lambda>f. \<forall>w[M]. \<forall>x[M]. \<forall>fw[M]. w\<in>A \<and> x\<in>A \<and>
            is_apply(M,f,w,fw) \<and> is_apply(M,f,x,fw) \<longrightarrow> w=x,
        I)"

context M_basic
begin

(************* Discipline for is_inj ****************)

lemma is_inj_uniqueness:
  assumes
    "M(r)" "M(B)" "M(d)" "M(d')"
    "is_inj(M,r,B,d)" "is_inj(M,r,B,d')"
  shows
    "d=d'"
  using assms is_function_space_uniqueness
    extensionality_trans [where P="\<lambda>f. typed_function(M, r, B, f)"]
  unfolding is_inj_def is_Collect_def
  sorry \<comment> \<open>This was not trivial\<close>

lemma is_inj_witness: "M(r) \<Longrightarrow> M(B)\<Longrightarrow> \<exists>d[M]. is_inj(M,r,B,d)"
  unfolding is_inj_def
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

\<comment> \<open>This is not the "def_" version we intended: we expected to have
  the absolute apply operator\<close>
lemma def_inj_rel: "M(A) \<Longrightarrow> M(B) \<Longrightarrow>
    inj_rel(A,B) = { f \<in> A \<rightarrow>r B.  \<forall>w[M]. \<forall>x[M]. \<forall>fw[M].
        w\<in>A \<and> x\<in>A \<and>
            is_apply(M,f,w,fw) \<and> is_apply(M,f,x,fw) \<longrightarrow> w=x}"
  using  inj_rel_closed inj_rel_iff function_space_rel_iff
  unfolding is_inj_def by simp (* by fastforce *)

(***************  end Discipline  *********************)


(* lemma def_inj_rel : "M(A) ==> M(B) ==>
  inj_rel(M,A,B) =  Collect_rel(M, A ->r B,
     %f. \<forall>w[M]. w\<in>A --> (\<forall>x[M] . x\<in>A --> f `r w = f `r x \<longrightarrow> w=x))" *)

end (* M_basic *)

end