theory Discipline_Cardinal
  imports
    Discipline_Base
    Discipline_Function
    Least
    FrecR
    Arities
    FrecR_Arities
begin

declare [[syntax_ambiguity_warning = false]]

relativize functional "cardinal" "cardinal_rel" external
relationalize "cardinal_rel" "is_cardinal"
synthesize "is_cardinal" from_definition assuming "nonempty"

notation is_cardinal_fm (\<open>cardinal'(_') is _\<close>)

abbreviation
  cardinal_r :: "[i,i\<Rightarrow>o] \<Rightarrow> i" (\<open>|_|\<^bsup>_\<^esup>\<close>) where
  "|x|\<^bsup>M\<^esup> \<equiv> cardinal_rel(M,x)"

abbreviation
  cardinal_r_set :: "[i,i]\<Rightarrow>i"  (\<open>|_|\<^bsup>_\<^esup>\<close>) where
  "|x|\<^bsup>M\<^esup> \<equiv> cardinal_rel(##M,x)"

context M_trivial begin
rel_closed for "cardinal"
  using Least_closed'[of "\<lambda>i. M(i) \<and> i \<approx>\<^bsup>M\<^esup> A"]
  unfolding cardinal_rel_def
  by simp
end

manual_arity intermediate for "is_Int_fm"
  unfolding is_Int_fm_def
  using arity pred_Un_distrib
  by (simp)

arity_theorem for "is_Int_fm"

arity_theorem for "is_funspace_fm"

arity_theorem for "is_function_space_fm"

arity_theorem for "surjP_rel_fm"

arity_theorem intermediate for "is_surj_fm"

lemma arity_is_surj_fm [arity] :
  "A \<in> nat \<Longrightarrow> B \<in> nat \<Longrightarrow> I \<in> nat \<Longrightarrow> arity(is_surj_fm(A, B, I)) = succ(A) \<union> succ(B) \<union> succ(I)"
  using arity_is_surj_fm' pred_Un_distrib
  by auto

arity_theorem for "injP_rel_fm"

arity_theorem intermediate for "is_inj_fm"

lemma arity_is_inj_fm [arity]:
  "A \<in> nat \<Longrightarrow> B \<in> nat \<Longrightarrow> I \<in> nat \<Longrightarrow> arity(is_inj_fm(A, B, I)) = succ(A) \<union> succ(B) \<union> succ(I)"
  using arity_is_inj_fm' pred_Un_distrib
  by auto

arity_theorem for "is_bij_fm"

arity_theorem for "is_eqpoll_fm"

arity_theorem for "is_cardinal_fm"

context M_Perm begin

is_iff_rel for "cardinal"
  using least_abs'[of "\<lambda>i. M(i) \<and> i \<approx>\<^bsup>M\<^esup> A"]
    is_eqpoll_iff
  unfolding is_cardinal_def cardinal_rel_def
  by simp
end

reldb_add relational "Ord" "ordinal"
reldb_add functional "lt" "lt"
reldb_add relational "lt" "lt_rel"
synthesize "lt_rel" from_definition
notation lt_rel_fm (\<open>\<cdot>_ < _\<cdot>\<close>)
arity_theorem intermediate for "lt_rel_fm"

lemma arity_lt_rel_fm[arity]: "a \<in> nat \<Longrightarrow> b \<in> nat \<Longrightarrow> arity(lt_rel_fm(a, b)) = succ(a) \<union> succ(b)"
  using arity_lt_rel_fm'
  by auto

relativize functional "Card" "Card_rel" external
relationalize "Card_rel" "is_Card"
synthesize "is_Card" from_definition assuming "nonempty"
notation is_Card_fm (\<open>\<cdot>Card'(_')\<cdot>\<close>)
arity_theorem for "is_Card_fm"

notation Card_rel (\<open>Card\<^bsup>_\<^esup>'(_')\<close>)

lemma (in M_Perm) is_Card_iff: "M(A) \<Longrightarrow> is_Card(M, A) \<longleftrightarrow> Card\<^bsup>M\<^esup>(A)"
  using is_cardinal_iff
  unfolding is_Card_def Card_rel_def by simp

abbreviation
  Card_r_set  :: "[i,i]\<Rightarrow>o"  (\<open>Card\<^bsup>_\<^esup>'(_')\<close>) where
  "Card\<^bsup>M\<^esup>(i) \<equiv> Card_rel(##M,i)"

relativize functional "InfCard" "InfCard_rel" external
relationalize "InfCard_rel" "is_InfCard"
synthesize "is_InfCard" from_definition assuming "nonempty"
notation is_InfCard_fm (\<open>\<cdot>InfCard'(_')\<cdot>\<close>)
arity_theorem for "is_InfCard_fm"

notation InfCard_rel (\<open>InfCard\<^bsup>_\<^esup>'(_')\<close>)

abbreviation
  InfCard_r_set  :: "[i,i]\<Rightarrow>o"  (\<open>InfCard\<^bsup>_\<^esup>'(_')\<close>) where
  "InfCard\<^bsup>M\<^esup>(i) \<equiv> InfCard_rel(##M,i)"

relativize functional "cadd" "cadd_rel" external

abbreviation
  cadd_r :: "[i,i\<Rightarrow>o,i] \<Rightarrow> i" (\<open>_ \<oplus>\<^bsup>_\<^esup> _\<close> [66,1,66] 65) where
  "A \<oplus>\<^bsup>M\<^esup> B \<equiv> cadd_rel(M,A,B)"

context M_basic begin
rel_closed for "cadd"
  using cardinal_rel_closed
  unfolding cadd_rel_def
  by simp
end

(* relativization *)

relationalize "cadd_rel" "is_cadd"

manual_schematic for "is_cadd" assuming "nonempty"
  unfolding is_cadd_def
  by (rule iff_sats sum_iff_sats | simp)+
synthesize "is_cadd" from_schematic

arity_theorem for "sum_fm"

arity_theorem for "is_cadd_fm"

context M_Perm begin
is_iff_rel for "cadd"
  using is_cardinal_iff
  unfolding is_cadd_def cadd_rel_def
  by simp
end

relativize functional "cmult" "cmult_rel" external

abbreviation
  cmult_r :: "[i,i\<Rightarrow>o,i] \<Rightarrow> i" (\<open>_ \<otimes>\<^bsup>_\<^esup> _\<close> [66,1,66] 65) where
  "A \<otimes>\<^bsup>M\<^esup> B \<equiv> cmult_rel(M,A,B)"

(* relativization *)
relationalize "cmult_rel" "is_cmult"

declare cartprod_iff_sats [iff_sats]

synthesize "is_cmult" from_definition assuming "nonempty"

arity_theorem for "is_cmult_fm"

context M_Perm begin

rel_closed for "cmult"
  using cardinal_rel_closed
  unfolding cmult_rel_def
  by simp

is_iff_rel for "cmult"
  using is_cardinal_iff 
  unfolding is_cmult_def cmult_rel_def
  by simp

end

definition
  Powapply :: "[i,i] \<Rightarrow> i"  where
  "Powapply(f,y) \<equiv> Pow(f`y)"

reldb_add functional "Pow" "Pow_rel"
reldb_add relational "Pow" "is_Pow"

lemma subset_iff_sats[iff_sats]:
  "nth(i, env) = x \<Longrightarrow> nth(j, env) = y \<Longrightarrow> i\<in>nat \<Longrightarrow> j\<in>nat \<Longrightarrow>
   env \<in> list(A) \<Longrightarrow> subset(##A, x, y) \<longleftrightarrow> A, env \<Turnstile> subset_fm(i, j)"
  using sats_subset_fm' by simp

declare Replace_iff_sats[iff_sats]

synthesize "is_Pow" from_definition assuming "nonempty"
arity_theorem for "is_Pow_fm"

relativize functional "Powapply" "Powapply_rel"
relationalize "Powapply_rel" "is_Powapply"
synthesize "is_Powapply" from_definition assuming "nonempty"
arity_theorem for "is_Powapply_fm"

notation Powapply_rel (\<open>Powapply\<^bsup>_\<^esup>'(_,_')\<close>)

context M_basic
begin

rel_closed for "Powapply"
  unfolding Powapply_rel_def
  by simp

is_iff_rel for "Powapply"
  using Pow_rel_iff
  unfolding is_Powapply_def Powapply_rel_def
  by simp

univalent for "Powapply"
  using is_Powapply_iff
  unfolding univalent_def
  by simp

end

(* definition
  HVfrom_rel :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> i" (\<open>HVfrom\<^bsup>_\<^esup>'(_,_,_')\<close>) where
  "HVfrom\<^bsup>M\<^esup>(A,x,f) \<equiv> A \<union> (\<Union>y\<in>x. Powapply\<^bsup>M\<^esup>(f,y))" *)

definition
  HVfrom :: "[i,i,i] \<Rightarrow> i" where
  "HVfrom(A,x,f) \<equiv> A \<union> (\<Union>y\<in>x. Powapply(f,y))"

relativize functional "HVfrom" "HVfrom_rel"
relationalize "HVfrom_rel" "is_HVfrom"
synthesize "is_HVfrom" from_definition assuming "nonempty"
arity_theorem for "is_HVfrom_fm"

notation HVfrom_rel (\<open>HVfrom\<^bsup>_\<^esup>'(_,_,_')\<close>)

locale M_HVfrom = M_eclose +
  assumes
    Powapply_replacement:
      "M(K) \<Longrightarrow> strong_replacement(M,\<lambda>y z. z = Powapply\<^bsup>M\<^esup>(f,y))"
begin

is_iff_rel for "HVfrom"
proof -
  assume assms:"M(A)" "M(x)" "M(f)" "M(res)"
  then
  have "is_Replace(M,x,\<lambda>y z. z = Powapply\<^bsup>M\<^esup>(f,y),r) \<longleftrightarrow> r = {z . y\<in>x, z = Powapply\<^bsup>M\<^esup>(f,y)}"
    if "M(r)" for r
    using that Powapply_rel_closed
          Replace_abs[of x r "\<lambda>y z. z = Powapply\<^bsup>M\<^esup>(f,y)"] transM[of _ x]
    by simp
  moreover
  have "is_Replace(M,x,is_Powapply(M,f),r) \<longleftrightarrow> 
        is_Replace(M,x,\<lambda>y z. z = Powapply\<^bsup>M\<^esup>(f,y),r)" if "M(r)" for r
    using assms that is_Powapply_iff is_Replace_cong 
    by simp
  ultimately
  have "is_Replace(M,x,is_Powapply(M,f),r) \<longleftrightarrow> r = {z . y\<in>x, z = Powapply\<^bsup>M\<^esup>(f,y)}"
    if "M(r)" for r
    using that assms 
    by simp
  moreover
  have "M({z . y \<in> x, z = Powapply\<^bsup>M\<^esup>(f,y)})" 
    using assms strong_replacement_closed[OF Powapply_replacement] 
          Powapply_rel_closed transM[of _ x]
    by simp
  moreover from assms
  \<comment> \<open>intermediate step for body of Replace\<close>
  have "{z . y \<in> x, z = Powapply\<^bsup>M\<^esup>(f,y)} = {y . w \<in> x, M(y) \<and> M(w) \<and> y = Powapply\<^bsup>M\<^esup>(f,w)}" 
    by (auto dest:transM)
  ultimately
  show ?thesis
    using assms
  unfolding is_HVfrom_def HVfrom_rel_def
    by (auto dest:transM)
qed

univalent for "HVfrom"
  using is_HVfrom_iff
  unfolding univalent_def
  by simp

rel_closed for "HVfrom"
proof -
  assume assms:"M(A)" "M(x)" "M(f)"
  have "M({z . y \<in> x, z = Powapply\<^bsup>M\<^esup>(f,y)})" 
    using assms strong_replacement_closed[OF Powapply_replacement] 
          Powapply_rel_closed transM[of _ x]
    by simp
  then 
  have "M(A \<union> \<Union>({z . y\<in>x, z = Powapply\<^bsup>M\<^esup>(f,y)}))"
    using assms
    by simp
  moreover from assms
  \<comment> \<open>intermediate step for body of Replace\<close>
  have "{z . y \<in> x, z = Powapply\<^bsup>M\<^esup>(f,y)} = {y . w \<in> x, M(y) \<and> M(w) \<and> y = Powapply\<^bsup>M\<^esup>(f,w)}" 
    by (auto dest:transM)
  ultimately
  show ?thesis
    using assms
    unfolding HVfrom_rel_def 
    by simp    
qed

end \<comment> \<open>\<^locale>\<open>M_HVfrom\<close>\<close>

(*
relativize functional "Vfrom" "Vfrom_rel" external
relationalize "Vfrom_rel" "is_Vfrom"
synthesize "is_Vfrom" from_definition assuming "nonempty"
arity_theorem for "is_Vfrom_fm"

notation Vfrom_rel (\<open>Vfrom\<^bsup>_\<^esup>'(_,_')\<close>)

context M_basic
begin

is_iff_rel for "Vfrom"
  using Pow_rel_iff
  unfolding is_Vfrom_def Vfrom_rel_def
  by simp

univalent for "Vfrom"
  using is_Vfrom_iff
  unfolding univalent_def
  by simp

rel_closed for "Vfrom"
  unfolding Vfrom_rel_def
  by simp

*)

definition
  Vfrom_rel :: "[i\<Rightarrow>o,i,i] \<Rightarrow> i" (\<open>Vfrom\<^bsup>_\<^esup>'(_,_')\<close>) where
  "Vfrom\<^bsup>M\<^esup>(A,i) = transrec(i, HVfrom_rel(M,A))"

(* relativization *)
definition
  is_Vfrom :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_Vfrom(M,A,i,z) \<equiv> is_transrec(M,is_HVfrom(M,A),i,z)"

locale M_Vfrom = M_HVfrom +
  assumes
    trepl_HVfrom : "\<lbrakk> M(A);M(i) \<rbrakk> \<Longrightarrow> transrec_replacement(M,is_HVfrom(M,A),i)"

begin

lemma  Vfrom_rel_iff : 
  assumes "M(A)" "M(i)" "M(z)" "Ord(i)"
  shows "is_Vfrom(M,A,i,z) \<longleftrightarrow> z = Vfrom\<^bsup>M\<^esup>(A,i)"
proof -
  have "relation2(M, is_HVfrom(M, A), HVfrom_rel(M, A))"
    using assms is_HVfrom_iff
    unfolding relation2_def
    by simp
  then
  show ?thesis
  using assms HVfrom_rel_closed trepl_HVfrom 
              transrec_abs[of "is_HVfrom(M,A)" i "HVfrom_rel(M,A)" z]
  unfolding is_Vfrom_def Vfrom_rel_def
  by simp
qed

end \<comment> \<open>\<^locale>\<open>M_Vfrom\<close>\<close>

end