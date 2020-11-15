theory Discipline_Function
  imports
    "ZF-Constructible.Rank"
    "Relativization"
    "HOL-Eisbach.Eisbach_Old_Appl_Syntax"\<comment> \<open>if put before, it breaks some simps\<close>
    "../Tools/Try0"
    "Discipline_Base" 
begin

(**********************************************************)
subsection\<open>Discipline for \<^term>\<open>function_space\<close>\<close>

definition
  is_function_space :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o"  where 
  "is_function_space(M,A,B,fs) \<equiv> M(fs) \<and> is_funspace(M,A,B,fs)" 

definition
  function_space_rel :: "[i\<Rightarrow>o,i,i] \<Rightarrow> i"  where
  "function_space_rel(M,A,B) \<equiv> THE d. is_function_space(M,A,B,d)"

abbreviation
  function_space_r :: "[i,i\<Rightarrow>o,i] \<Rightarrow> i" (\<open>_ \<rightarrow>\<^bsup>_\<^esup> _\<close> [61,1,61] 60) where
  "A \<rightarrow>\<^bsup>M\<^esup> B \<equiv> function_space_rel(M,A,B)"

abbreviation
  function_space_r_set ::  "[i,i,i] \<Rightarrow> i" (\<open>_ \<rightarrow>\<^bsup>_\<^esup> _\<close> [61,1,61] 60) where
  "function_space_r_set(A,M) \<equiv> function_space_rel(##M,A)"

context M_Pi
begin

lemma is_function_space_uniqueness:
  assumes
    "M(r)" "M(B)"
    "is_function_space(M,r,B,d)" "is_function_space(M,r,B,d')"
  shows
    "d=d'"
  using assms extensionality_trans
  unfolding is_function_space_def is_funspace_def
  by simp

lemma is_function_space_witness:
  assumes "M(A)" "M(B)"
  shows "\<exists>d[M]. is_function_space(M,A,B,d)"
proof -
  from assms
  interpret M_Pi_assumptions M A "\<lambda>_. B"
    using Pi_replacement Pi_separation
    by unfold_locales (simp_all add:Sigfun_def)
  have "\<forall>f[M]. f \<in> Pi_rel(M,A, \<lambda>_. B) \<longleftrightarrow> f \<in> A \<rightarrow> B"
    using Pi_rel_char by simp
  with assms
  show ?thesis unfolding is_funspace_def is_function_space_def by auto
qed

lemma is_function_space_closed :
 "is_function_space(M,A,B,d) \<Longrightarrow> M(d)"
  unfolding is_function_space_def by simp

\<comment> \<open>adding closure to simpset and claset\<close>
lemma function_space_rel_closed[intro,simp]: 
  assumes    "M(x)" "M(y)"
  shows "M(function_space_rel(M,x,y))"
proof -
  have "is_function_space(M, x, y, THE xa. is_function_space(M, x, y, xa))" 
    using assms 
          theI[OF ex1I[of "is_function_space(M,x,y)"], OF _ is_function_space_uniqueness[of x y]]
          is_function_space_witness
    by auto
  then show ?thesis 
    using assms is_function_space_closed
    unfolding function_space_rel_def
    by blast
qed

lemmas trans_function_space_rel_closed[trans_closed] = transM[OF _ function_space_rel_closed]

lemma function_space_rel_iff:
  assumes "M(x)" "M(y)" "M(d)"
  shows "is_function_space(M,x,y,d) \<longleftrightarrow> d = function_space_rel(M,x,y)"
proof (intro iffI)
  assume "d = function_space_rel(M,x,y)"
  moreover
  note assms
  moreover from this
  obtain e where "M(e)" "is_function_space(M,x,y,e)"
    using is_function_space_witness by blast
  ultimately
  show "is_function_space(M, x, y, d)"
    using is_function_space_uniqueness[of x y] is_function_space_witness
      theI[OF ex1I[of "is_function_space(M,x,y)"], OF _ is_function_space_uniqueness[of x y], of e]
    unfolding function_space_rel_def
    by auto
next
  assume "is_function_space(M, x, y, d)"
  with assms
  show "d = function_space_rel(M,x,y)"
    using is_function_space_uniqueness unfolding function_space_rel_def
    by (blast del:the_equality intro:the_equality[symmetric])
qed


lemma def_function_space_rel:
  assumes "M(A)" "M(y)"
  shows "function_space_rel(M,A,y) = Pi_rel(M,A,\<lambda>_. y)"
proof -
  from assms
  interpret M_Pi_assumptions M A "\<lambda>_. y"
    using Pi_replacement Pi_separation
    by unfold_locales (simp_all add:Sigfun_def)
  from assms
  have "x\<in>function_space_rel(M,A,y) \<longleftrightarrow> x\<in>Pi_rel(M,A,\<lambda>_. y)" if "M(x)" for x
    using that
      function_space_rel_iff[of A y, OF _ _ function_space_rel_closed, of A y]
      def_Pi_rel Pi_rel_char Pow_rel_char
    unfolding is_function_space_def is_funspace_def by (simp add:Pi_def)
  with assms
  show ?thesis \<comment> \<open>At this point, quoting "trans_rules" doesn't work\<close>
    using transM[OF _ function_space_rel_closed, OF _ \<open>M(A)\<close> \<open>M(y)\<close>]
      transM[OF _ Pi_rel_closed] by blast
qed

lemma function_space_rel_char:
  assumes "M(A)" "M(y)"
  shows "function_space_rel(M,A,y) = {f \<in> A \<rightarrow> y. M(f)}"
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
  shows "f \<in> function_space_rel(M,A,y) \<longleftrightarrow>  f \<in> A \<rightarrow> y"
  using assms function_space_rel_char by simp

end (* M_Pi_assumptions *)



(*
definition
  is_function_space :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o"  where
  "is_function_space(M,A,B,fs) \<equiv> is_Pi(M,A,\<lambda>_. B,fs)"
  
definition
  function_space_rel :: "[i\<Rightarrow>o,i,i] \<Rightarrow> i"  where
  "function_space_rel(M,A,B) \<equiv> Pi_rel(M,A,\<lambda>_. B)"

abbreviation
  function_space_r :: "[i,i\<Rightarrow>o,i] \<Rightarrow> i" (\<open>_ \<rightarrow>\<^bsup>_\<^esup> _\<close> [61,1,61] 60) where
  "A \<rightarrow>\<^bsup>M\<^esup> B \<equiv> function_space_rel(M,A,B)"

abbreviation
  function_space_r_set ::  "[i,i,i] \<Rightarrow> i" (\<open>_ \<rightarrow>\<^bsup>_\<^esup> _\<close> [61,1,61] 60) where
  "function_space_r_set(A,M) \<equiv> function_space_rel(##M,A)"

context M_Pi
begin

lemma is_function_space_uniqueness:
  assumes
    "M(r)" "M(B)"
    "is_function_space(M,r,B,d)" "is_function_space(M,r,B,d')"
  shows
    "d=d'"
  using is_Pi_uniqueness[of r "\<lambda>_. B"] assms
  unfolding is_function_space_def
  by blast

lemma is_function_space_witness:
  assumes "M(A)" "M(B)"
  shows "\<exists>d[M]. is_function_space(M,A,B,d)"
  using is_Pi_witness[of A "\<lambda>_. B"] assms
  unfolding is_function_space_def
  by simp

\<comment> \<open>adding closure to simpset and claset\<close>
lemma function_space_rel_closed[intro,simp]: 
  "M(x) \<Longrightarrow> M(y) \<Longrightarrow> M(function_space_rel(M,x,y))"
  unfolding function_space_rel_def
  by simp

lemmas trans_function_space_rel_closed[trans_closed] = transM[OF _ function_space_rel_closed]

lemma function_space_rel_iff:
  assumes "M(x)" "M(y)" "M(d)"
  shows "is_function_space(M,x,y,d) \<longleftrightarrow> d = function_space_rel(M,x,y)"
  using Pi_rel_iff[of x "\<lambda>_. y"] assms
  unfolding is_function_space_def function_space_rel_def
  by simp

lemma def_function_space_rel:
  assumes "M(A)" "M(y)"
  shows "A \<rightarrow>\<^bsup>M\<^esup> y = Pi\<^bsup>M\<^esup>(A,\<lambda>_. y)"
proof -
  from assms
  interpret M_Pi_assumptions M A "\<lambda>_. y"
    using Pi_replacement Pi_separation
    by unfold_locales (simp_all add:Sigfun_def)
  from assms
  have "x\<in>A \<rightarrow>\<^bsup>M\<^esup> y \<longleftrightarrow> x\<in>Pi\<^bsup>M\<^esup>(A,\<lambda>_. y)" if "M(x)" for x
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
  shows "A \<rightarrow>\<^bsup>M\<^esup> y = {f \<in> A \<rightarrow> y. M(f)}"
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
  shows "f \<in> A \<rightarrow>\<^bsup>M\<^esup> y  \<longleftrightarrow>  f \<in> A \<rightarrow> y"
  using assms function_space_rel_char by simp

end (* M_Pi *)
*)

locale M_N_Pi = M:M_Pi + N:M_Pi N for N +
  assumes
    M_imp_N:"M(x) \<Longrightarrow> N(x)"
begin

lemma function_space_rel_transfer: "M(A) \<Longrightarrow> M(B) \<Longrightarrow> 
                          function_space_rel(M,A,B) \<subseteq> function_space_rel(N,A,B)"
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
  "is_inj(M,A,B,I) \<equiv> M(I) \<and> (\<exists>F[M]. is_function_space(M,A,B,F) \<and>
       is_Collect(M,F,injP_rel(M,A),I))"

definition
  inj_rel :: "[i\<Rightarrow>o,i,i] \<Rightarrow> i" (\<open>inj\<^bsup>_\<^esup>'(_,_')\<close>) where
  "inj_rel(M,A,B) \<equiv> THE d. is_inj(M,A,B,d)"

abbreviation
  inj_r_set ::  "[i,i,i] \<Rightarrow> i" (\<open>inj\<^bsup>_\<^esup>'(_,_')\<close>) where
  "inj_r_set(M) \<equiv> inj_rel(##M)"

locale M_inj = M_Pi +
  assumes
    injP_separation: "M(r) \<Longrightarrow> separation(M,injP_rel(M, r))"
begin

lemma is_inj_uniqueness:
  assumes
    "M(r)" "M(B)"
    "is_inj(M,r,B,d)" "is_inj(M,r,B,d')"
  shows
    "d=d'"
  using assms function_space_rel_iff extensionality_trans
  unfolding is_inj_def by simp

lemma is_inj_witness: "M(r) \<Longrightarrow> M(B)\<Longrightarrow> \<exists>d[M]. is_inj(M,r,B,d)"
  using injP_separation function_space_rel_iff
  unfolding is_inj_def by simp

lemma is_inj_closed :
 "is_inj(M,x,y,d) \<Longrightarrow> M(d)"
  unfolding is_inj_def by simp

lemma inj_rel_closed[intro,simp]: 
  assumes "M(x)" "M(y)"
  shows "M(inj_rel(M,x,y))"
proof -
  have "is_inj(M, x, y, THE xa. is_inj(M, x, y, xa))" 
    using assms 
          theI[OF ex1I[of "is_inj(M,x,y)"], OF _ is_inj_uniqueness[of x y]]
          is_inj_witness
    by auto
  then show ?thesis 
    using assms is_inj_closed
    unfolding inj_rel_def
    by blast
qed

lemmas trans_inj_rel_closed[trans_closed] = transM[OF _ inj_rel_closed]

lemma inj_rel_iff:
  assumes "M(x)" "M(y)" "M(d)"
  shows "is_inj(M,x,y,d) \<longleftrightarrow> d = inj_rel(M,x,y)"
proof (intro iffI)
  assume "d = inj_rel(M,x,y)"
  moreover
  note assms
  moreover from this
  obtain e where "M(e)" "is_inj(M,x,y,e)"
    using is_inj_witness by blast
  ultimately
  show "is_inj(M, x, y, d)"
    using is_inj_uniqueness[of x y] is_inj_witness
      theI[OF ex1I[of "is_inj(M,x,y)"], OF _ is_inj_uniqueness[of x y], of e]
    unfolding inj_rel_def
    by auto
next
  assume "is_inj(M, x, y, d)"
  with assms
  show "d = inj_rel(M,x,y)"
    using is_inj_uniqueness unfolding inj_rel_def
    by (blast del:the_equality intro:the_equality[symmetric])
qed

lemma def_inj_rel:
  assumes "M(A)" "M(B)"
  shows "inj_rel(M,A,B) =
         {f \<in> function_space_rel(M,A,B).  \<forall>w[M]. \<forall>x[M]. w\<in>A \<and> x\<in>A \<and> f`w = f`x \<longrightarrow> w=x}"
    (is "_ = Collect(_,?P)")
proof -
  from assms
  have "inj_rel(M,A,B) \<subseteq> function_space_rel(M,A,B)"
    using inj_rel_iff[of A B "inj_rel(M,A,B)"] function_space_rel_iff
    unfolding is_inj_def by auto
  moreover from assms
  have "f \<in> inj_rel(M,A,B) \<Longrightarrow> ?P(f)" for f
    using inj_rel_iff[of A B "inj_rel(M,A,B)"] function_space_rel_iff
      def_injP_rel transM[OF _ function_space_rel_closed, OF _ \<open>M(A)\<close> \<open>M(B)\<close>]
    unfolding is_inj_def by auto
  moreover from assms
  have "f \<in> function_space_rel(M,A,B) \<Longrightarrow> ?P(f) \<Longrightarrow> f \<in> inj_rel(M,A,B)" for f
    using inj_rel_iff[of A B "inj_rel(M,A,B)"] function_space_rel_iff
      def_injP_rel transM[OF _ function_space_rel_closed, OF _ \<open>M(A)\<close> \<open>M(B)\<close>]
    unfolding is_inj_def by auto
  ultimately
  show ?thesis by force
qed

lemma inj_rel_char:
  assumes "M(A)" "M(B)"
  shows "inj_rel(M,A,B) = {f \<in> inj(A,B). M(f)}"
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

lemma inj_rel_transfer: "M(A) \<Longrightarrow> M(B) \<Longrightarrow> inj_rel(M,A,B) \<subseteq> inj_rel(N,A,B)"
  using M.inj_rel_char N.inj_rel_char 
  by (auto dest!:M_imp_N)

end (* M_N_inj *)


(***************  end Discipline  *********************)

(*************** Discipline for surjP ******************)

definition
  surjP_rel:: "[i\<Rightarrow>o,i,i,i]\<Rightarrow>o" where
  "surjP_rel(M,A,B,f) \<equiv> 
    \<forall>y[M]. \<exists>x[M]. \<exists>fx[M]. y\<in>B \<longrightarrow> x\<in>A \<and> is_apply(M,f,x,fx) \<and> fx=y"

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
  "is_surj(M,A,B,I) \<equiv> M(I) \<and> (\<exists>F[M]. is_function_space(M,A,B,F) \<and>
       is_Collect(M,F,surjP_rel(M,A,B),I))"

definition
  surj_rel :: "[i\<Rightarrow>o,i,i] \<Rightarrow> i" (\<open>surj\<^bsup>_\<^esup>'(_,_')\<close>) where
  "surj_rel(M,A,B) \<equiv> THE d. is_surj(M,A,B,d)"

abbreviation
  surj_r_set ::  "[i,i,i] \<Rightarrow> i" (\<open>surj\<^bsup>_\<^esup>'(_,_')\<close>) where
  "surj_r_set(M) \<equiv> surj_rel(##M)"

locale M_surj = M_Pi +
  assumes
    surjP_separation: "M(A)\<Longrightarrow>M(B)\<Longrightarrow>separation(M,\<lambda>x. surjP_rel(M,A,B,x))"
begin

lemma is_surj_uniqueness:
  assumes
    "M(r)" "M(B)"
    "is_surj(M,r,B,d)" "is_surj(M,r,B,d')"
  shows
    "d=d'"
  using assms function_space_rel_iff extensionality_trans
  unfolding is_surj_def by simp

lemma is_surj_witness: "M(r) \<Longrightarrow> M(B)\<Longrightarrow> \<exists>d[M]. is_surj(M,r,B,d)"
  using surjP_separation function_space_rel_iff
  unfolding is_surj_def by simp

lemma is_surj_closed :
 "is_surj(M,x,y,d) \<Longrightarrow> M(d)"
  unfolding is_surj_def by simp

lemma surj_rel_closed[intro,simp]: 
  assumes "M(x)" "M(y)"
  shows "M(surj_rel(M,x,y))"
proof -
  have "is_surj(M, x, y, THE xa. is_surj(M, x, y, xa))" 
    using assms 
          theI[OF ex1I[of "is_surj(M,x,y)"], OF _ is_surj_uniqueness[of x y]]
          is_surj_witness
    by auto
  then show ?thesis 
    using assms is_surj_closed
    unfolding surj_rel_def
    by blast
qed

lemmas trans_surj_rel_closed[trans_closed] = transM[OF _ surj_rel_closed]

lemma surj_rel_iff:
  assumes "M(x)" "M(y)" "M(d)"
  shows "is_surj(M,x,y,d) \<longleftrightarrow> d = surj_rel(M,x,y)"
proof (intro iffI)
  assume "d = surj_rel(M,x,y)"
  moreover
  note assms
  moreover from this
  obtain e where "M(e)" "is_surj(M,x,y,e)"
    using is_surj_witness by blast
  ultimately
  show "is_surj(M, x, y, d)"
    using is_surj_uniqueness[of x y] is_surj_witness
      theI[OF ex1I[of "is_surj(M,x,y)"], OF _ is_surj_uniqueness[of x y], of e]
    unfolding surj_rel_def
    by auto
next
  assume "is_surj(M, x, y, d)"
  with assms
  show "d = surj_rel(M,x,y)"
    using is_surj_uniqueness unfolding surj_rel_def
    by (blast del:the_equality intro:the_equality[symmetric])
qed

lemma def_surj_rel:
  assumes "M(A)" "M(B)"
  shows "surj_rel(M,A,B) =
         {f \<in> function_space_rel(M,A,B). \<forall>y[M]. \<exists>x[M]. y\<in>B \<longrightarrow> x\<in>A \<and> f`x=y }"
    (is "_ = Collect(_,?P)")
proof -
  from assms
  have "surj_rel(M,A,B) \<subseteq> function_space_rel(M,A,B)"
    using surj_rel_iff[of A B "surj_rel(M,A,B)"] function_space_rel_iff
    unfolding is_surj_def by auto
  moreover from assms
  have "f \<in> surj_rel(M,A,B) \<Longrightarrow> ?P(f)" for f
    using surj_rel_iff[of A B "surj_rel(M,A,B)"] function_space_rel_iff
      def_surjP_rel transM[OF _ function_space_rel_closed, OF _ \<open>M(A)\<close> \<open>M(B)\<close>]
    unfolding is_surj_def by auto
  moreover from assms
  have "f \<in> function_space_rel(M,A,B) \<Longrightarrow> ?P(f) \<Longrightarrow> f \<in> surj_rel(M,A,B)" for f
    using surj_rel_iff[of A B "surj_rel(M,A,B)"] function_space_rel_iff
      def_surjP_rel transM[OF _ function_space_rel_closed, OF _ \<open>M(A)\<close> \<open>M(B)\<close>]
    unfolding is_surj_def by auto
  ultimately
  show ?thesis by force
qed

lemma surj_rel_char:
  assumes "M(A)" "M(B)"
  shows "surj_rel(M,A,B) = {f \<in> surj(A,B). M(f)}"
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

lemma surj_rel_transfer: "M(A) \<Longrightarrow> M(B) \<Longrightarrow> surj_rel(M,A,B) \<subseteq> surj_rel(N,A,B)"
  using M.surj_rel_char N.surj_rel_char 
  by (auto dest!:M_imp_N)

end (* M_N_surj *)

(***************  end Discipline  *********************)

definition
  is_Int :: "[i\<Rightarrow>o,i,i,i]\<Rightarrow>o"  where
  "is_Int(M,A,B,I) \<equiv> M(I) \<and> (\<forall>x[M]. x \<in> I \<longleftrightarrow> x \<in> A \<and> x \<in> B)"

context M_basic
begin

lemma is_Int_closed :
 "is_Int(M,A,B,I) \<Longrightarrow> M(I)"
  unfolding is_Int_def by simp

lemma is_Int_abs:
  assumes
    "M(A)" "M(B)" "M(I)"
  shows
    "is_Int(M,A,B,I) \<longleftrightarrow> I = A \<inter> B"
  using assms transM[OF _ \<open>M(B)\<close>] transM[OF _ \<open>M(I)\<close>]
  unfolding is_Int_def by blast

lemma is_Int_uniqueness:
  assumes
    "M(r)" "M(B)"
    "is_Int(M,r,B,d)" "is_Int(M,r,B,d')"
  shows
    "d=d'"
proof -
  have "M(d)" and "M(d')" 
    using assms is_Int_closed by simp+
  then show ?thesis
    using assms is_Int_abs by simp
qed

text\<open>Note: @{thm Int_closed} already in \<^theory>\<open>ZF-Constructible.Relative\<close>.\<close>

end (* M_trivial *)

(**********************************************************)
subsection\<open>Discipline for \<^term>\<open>bij\<close>\<close>

definition (* completely relational *)
  is_bij   :: "[i\<Rightarrow>o,i,i,i]\<Rightarrow>o"  where
  "is_bij(M,A,B,bj) \<equiv> M(bj) \<and> is_hcomp2_2(M,is_Int,is_inj,is_surj,A,B,bj)"

definition
  bij_rel :: "[i\<Rightarrow>o,i,i] \<Rightarrow> i" (\<open>bij\<^bsup>_\<^esup>'(_,_')\<close>) where
  "bij_rel(M,A,B) \<equiv> THE d. is_bij(M,A,B,d)"

abbreviation
  bij_r_set ::  "[i,i,i] \<Rightarrow> i" (\<open>bij\<^bsup>_\<^esup>'(_,_')\<close>) where
  "bij_r_set(M) \<equiv> bij_rel(##M)"

locale M_Perm = M_Pi + M_inj + M_surj
begin

lemma is_bij_uniqueness:
  assumes
    "M(A)" "M(B)"
    "is_bij(M,A,B,d)" "is_bij(M,A,B,d')"
  shows
    "d=d'"
  using assms hcomp2_2_uniqueness[of M is_Int is_inj is_surj A B d d']
    is_Int_uniqueness is_inj_uniqueness is_surj_uniqueness
    is_Int_closed is_inj_closed is_surj_closed
  unfolding is_bij_def
  by auto

lemma is_bij_witness: "M(A) \<Longrightarrow> M(B)\<Longrightarrow> \<exists>d[M]. is_bij(M,A,B,d)"
  using hcomp2_2_witness[of M is_Int is_inj is_surj A B]
    is_inj_witness is_surj_witness is_Int_abs
  unfolding is_bij_def by simp

lemma is_bij_closed : "is_bij(M,f,y,d) \<Longrightarrow> M(d)" 
  unfolding is_bij_def by simp

lemma bij_rel_closed[intro,simp]: 
  assumes "M(x)" "M(y)"
  shows "M(bij_rel(M,x,y))"
proof -
  have "is_bij(M, x, y, THE xa. is_bij(M, x, y, xa))" 
    using assms 
          theI[OF ex1I[of "\<lambda>d. is_bij(M,x,y,d)"], OF _ is_bij_uniqueness[of x y]]
          is_bij_witness
    by auto
  then show ?thesis 
    using assms is_bij_closed
    unfolding bij_rel_def
    by blast
qed

lemmas trans_bij_rel_closed[trans_closed] = transM[OF _ bij_rel_closed]

lemma bij_rel_iff:
  assumes "M(x)" "M(y)" "M(d)"
  shows "is_bij(M,x,y,d) \<longleftrightarrow> d = bij_rel(M,x,y)"
proof (intro iffI)
  assume "d = bij_rel(M,x,y)"
  moreover
  note assms
  moreover from this
  obtain e where "M(e)" "is_bij(M,x,y,e)"
    using is_bij_witness by blast
  ultimately
  show "is_bij(M, x, y, d)"
    using is_bij_uniqueness[of x y] is_bij_witness
      theI[OF ex1I[of "is_bij(M,x,y)"], OF _ is_bij_uniqueness[of x y], of e]
    unfolding bij_rel_def
    by auto
next
  assume "is_bij(M, x, y, d)"
  with assms
  show "d = bij_rel(M,x,y)"
    using is_bij_uniqueness unfolding bij_rel_def
    by (blast del:the_equality intro:the_equality[symmetric])
qed

lemma def_bij_rel:
  assumes "M(A)" "M(B)"
  shows "bij_rel(M,A,B) = inj_rel(M,A,B) \<inter> surj_rel(M,A,B)"
  using assms bij_rel_iff inj_rel_iff surj_rel_iff
    is_Int_abs\<comment> \<open>For absolute terms, "_abs" replaces "_iff".
                 Also, in this case "_closed" is in the simpset.\<close>
    hcomp2_2_abs
  unfolding is_bij_def by simp

lemma bij_rel_char:
  assumes "M(A)" "M(B)"
  shows "bij_rel(M,A,B) = {f \<in> bij(A,B). M(f)}"
  using assms def_bij_rel inj_rel_char surj_rel_char
  unfolding bij_def\<comment> \<open>Unfolding this might be a pattern already\<close>
  by auto

end (* M_Perm *)

locale M_N_Perm = M_N_Pi + M_N_inj + M_N_surj + M:M_Perm + N:M_Perm N

begin

lemma bij_rel_transfer: "M(A) \<Longrightarrow> M(B) \<Longrightarrow> bij_rel(M,A,B) \<subseteq> bij_rel(N,A,B)"
  using M.bij_rel_char N.bij_rel_char 
  by (auto dest!:M_imp_N)

end (* M_N_Perm *)

(***************  end Discipline  *********************)

(******************************************************)
subsection\<open>Discipline for \<^term>\<open>eqpoll\<close>\<close>

definition (* completely relational *)
  eqpoll_rel   :: "[i\<Rightarrow>o,i,i] => o" where
  "eqpoll_rel(M,A,B) \<equiv> \<exists>bi[M]. \<exists>f[M]. is_bij(M,A,B,bi) \<and> f\<in>bi"

abbreviation
  eqpoll_r :: "[i,i\<Rightarrow>o,i] => o" (\<open>_ \<approx>\<^bsup>_\<^esup> _\<close> [51,1,51] 50) where
  "A \<approx>\<^bsup>M\<^esup> B \<equiv> eqpoll_rel(M,A,B)"

abbreviation
  eqpoll_r_set ::  "[i,i,i] \<Rightarrow> o" (\<open>_ \<approx>\<^bsup>_\<^esup> _\<close> [51,1,51] 50) where
  "eqpoll_r_set(A,M) \<equiv> eqpoll_rel(##M,A)"

context M_Perm
begin

lemma def_eqpoll_rel:
  assumes
    "M(A)" "M(B)"
  shows
    "eqpoll_rel(M,A,B) \<longleftrightarrow> (\<exists>f[M]. f \<in> bij_rel(M,A,B))"
  using assms bij_rel_iff
  unfolding eqpoll_rel_def by simp

end (* M_Perm *)

context M_N_Perm
begin

(* the next lemma is not part of the discipline *)
lemma eqpoll_rel_transfer: assumes "A \<approx>\<^bsup>M\<^esup> B" "M(A)" "M(B)"
  shows "A \<approx>\<^bsup>N\<^esup> B"
proof -
  note assms
  moreover from this
  obtain f where "f \<in> bij\<^bsup>M\<^esup>(A,B)" "N(f)"
    using M.def_eqpoll_rel by (auto dest!:M_imp_N)
  moreover from calculation
  have "f \<in> bij\<^bsup>N\<^esup>(A,B)"
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
  lepoll_rel   :: "[i\<Rightarrow>o,i,i] => o" where
  "lepoll_rel(M,A,B) \<equiv> \<exists>bi[M]. \<exists>f[M]. is_inj(M,A,B,bi) \<and> f\<in>bi"

abbreviation
  lepoll_r :: "[i,i\<Rightarrow>o,i] => o" (\<open>_ \<lesssim>\<^bsup>_\<^esup> _\<close> [51,1,51] 50) where
  "A \<lesssim>\<^bsup>M\<^esup> B \<equiv> lepoll_rel(M,A,B)"

abbreviation
  lepoll_r_set ::  "[i,i,i] \<Rightarrow> o" (\<open>_ \<lesssim>\<^bsup>_\<^esup> _\<close> [51,1,51] 50) where
  "lepoll_r_set(A,M) \<equiv> lepoll_rel(##M,A)"

context M_Perm
begin

lemma def_lepoll_rel:
  assumes
    "M(A)" "M(B)"
  shows
    "lepoll_rel(M,A,B) \<longleftrightarrow> (\<exists>f[M]. f \<in> inj_rel(M,A,B))"
  using assms inj_rel_iff
  unfolding lepoll_rel_def by simp

end (* M_Perm *)

context M_N_Perm
begin

(* the next lemma is not part of the discipline *)
lemma lepoll_rel_transfer: assumes "A \<lesssim>\<^bsup>M\<^esup> B" "M(A)" "M(B)"
  shows "A \<lesssim>\<^bsup>N\<^esup> B"
proof -
  note assms
  moreover from this
  obtain f where "f \<in> inj\<^bsup>M\<^esup>(A,B)" "N(f)"
    using M.def_lepoll_rel by (auto dest!:M_imp_N)
  moreover from calculation
  have "f \<in> inj\<^bsup>N\<^esup>(A,B)"
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
  lesspoll_rel :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o"  where
  "lesspoll_rel(M,A,B) \<equiv> lepoll_rel(M,A,B) \<and> \<not>(eqpoll_rel(M,A,B))"

abbreviation
  lesspoll_r :: "[i,i\<Rightarrow>o,i] => o" (\<open>_ \<prec>\<^bsup>_\<^esup> _\<close> [51,1,51] 50) where
  "A \<prec>\<^bsup>M\<^esup> B \<equiv> lesspoll_rel(M,A,B)"

abbreviation
  lesspoll_r_set ::  "[i,i,i] \<Rightarrow> o" (\<open>_ \<prec>\<^bsup>_\<^esup> _\<close> [51,1,51] 50) where
  "lesspoll_r_set(A,M) \<equiv> lesspoll_rel(##M,A)"

text\<open>Since \<^term>\<open>lesspoll_rel\<close> is defined as a propositional
combination of older terms, there is no need for a separate “def”
theorem for it.\<close>

text\<open>Note that \<^term>\<open>lesspoll_rel\<close> is neither $\Sigma_1^{\mathit{ZF}}$ nor
 $\Pi_1^{\mathit{ZF}}$, so there is no “transfer” theorem for it.\<close>



end