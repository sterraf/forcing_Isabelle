theory Discipline_Univ
  imports
    "ZF-Constructible.Rank"
    "Relativization"
    "HOL-Eisbach.Eisbach_Old_Appl_Syntax"\<comment> \<open>if put before, it breaks some simps\<close>
    "../Tools/Try0"
    "Discipline_Base"
begin


definition
  Powapply :: "[i,i] \<Rightarrow> i"  where
  "Powapply(f,y) \<equiv> Pow(f`y)"

subsection\<open>Discipline for \<^term>\<open>Powapply\<close>\<close>

text\<open>Powapply is the composition of application and Pow function. We use
     the term\<open>is_hcomp2_2\<close> which allows define composition of two binary functions
     in a completely relational way.\<close>

definition
  is_Powapply :: "[i\<Rightarrow>o,i,i,i]\<Rightarrow>o"  where
  "is_Powapply(M,f,y,pa) \<equiv>  M(pa) \<and> 
   is_hcomp2_2(M,\<lambda>M _. is_Pow(M),\<lambda>_ _. (=),fun_apply,f,y,pa)"

definition
  Powapply_rel :: "[i\<Rightarrow>o,i,i] \<Rightarrow> i" (\<open>Powapply\<^bsup>_\<^esup>'(_')\<close>) where
  "Powapply_rel(M,f,y) \<equiv> THE d. is_Powapply(M,f,y,d)"

abbreviation
  Powapply_r_set ::  "[i,i,i] \<Rightarrow> i" (\<open>Powapply\<^bsup>_\<^esup>'(_')\<close>) where
  "Powapply_r_set(M) \<equiv> Powapply_rel(##M)"

context M_basic
begin

lemma is_Powapply_closed : "is_Powapply(M,f,y,d) \<Longrightarrow> M(d)" 
  unfolding is_Powapply_def by simp

lemma is_Powapply_uniqueness:
  assumes
    "M(A)" "M(B)"
    "is_Powapply(M,A,B,d)" "is_Powapply(M,A,B,d')"
  shows
    "d=d'"
proof -
  have "M(d)" and "M(d')" 
    using assms is_Powapply_closed by simp+
  then show ?thesis
    using assms \<comment> \<open>using projections (\<^term>\<open>\<lambda>_ _. (=)\<close>)
                  requires more instantiations\<close>
      is_Pow_uniqueness hcomp2_2_uniqueness[of
        M "\<lambda>M _. is_Pow(M)" "\<lambda>_ _. (=)" fun_apply A B d d']
    unfolding is_Powapply_def
    by auto
qed

lemma is_Powapply_witness: "M(A) \<Longrightarrow> M(B)\<Longrightarrow> \<exists>d[M]. is_Powapply(M,A,B,d)"
  using hcomp2_2_witness[of M "\<lambda>M _. is_Pow(M)" "\<lambda>_ _. (=)" fun_apply A B]
    is_Pow_witness
  unfolding is_Powapply_def by simp


lemma Powapply_rel_closed[intro,simp]: 
  assumes "M(x)" "M(y)"
  shows "M(Powapply_rel(M,x,y))"
proof -
  have "is_Powapply(M, x, y, THE xa. is_Powapply(M, x, y, xa))" 
    using assms 
          theI[OF ex1I[of "\<lambda>d. is_Powapply(M,x,y,d)"], OF _ is_Powapply_uniqueness[of x y]]
          is_Powapply_witness
    by auto
  then show ?thesis 
    using assms is_Powapply_closed
    unfolding Powapply_rel_def
    by blast
qed

lemma Powapply_rel_iff:
  assumes "M(x)" "M(y)" "M(d)"
  shows "is_Powapply(M,x,y,d) \<longleftrightarrow> d = Powapply_rel(M,x,y)"
proof (intro iffI)
  assume "d = Powapply_rel(M,x,y)"
  moreover
  note assms
  moreover from this
  obtain e where "M(e)" "is_Powapply(M,x,y,e)"
    using is_Powapply_witness by blast
  ultimately
  show "is_Powapply(M, x, y, d)"
    using is_Powapply_uniqueness[of x y] is_Powapply_witness
      theI[OF ex1I[of "is_Powapply(M,x,y)"], OF _ is_Powapply_uniqueness[of x y], of e]
    unfolding Powapply_rel_def
    by auto
next
  assume "is_Powapply(M, x, y, d)"
  with assms
  show "d = Powapply_rel(M,x,y)"
    using is_Powapply_uniqueness unfolding Powapply_rel_def
    by (blast del:the_equality intro:the_equality[symmetric])
qed

text\<open>The last step relating relative version of Powapply with the
     original defintion, where each non-abosolute concept is relativized.\<close>

lemma def_Powapply_rel:
  assumes "M(f)" "M(y)"
  shows "Powapply_rel(M,f,y) = Pow_rel(M,f`y)"
  using assms Powapply_rel_iff
    Pow_rel_iff
    hcomp2_2_abs[of "\<lambda>M _ . is_Pow(M)" "\<lambda>_. Pow_rel(M)"
      "\<lambda>_ _. (=)" "\<lambda>x y. y" fun_apply "(`)" f y "Powapply_rel(M,f,y)"]
  unfolding is_Powapply_def by force

end (* context M_basic *)

(*** end Discipline for Powapply ***)

subsection\<open>Discipline for \<^term>\<open>Vfrom\<close>\<close>

(* wfrec(Memrel(eclose({a})), a, %x f. A \<union> (\<Union>y\<in>x. Powapply(f,y)) *)




