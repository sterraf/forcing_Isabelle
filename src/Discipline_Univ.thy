theory Discipline_Univ
  imports
    "ZF-Constructible.Rank"
    "Relativization"
    "Discipline_Base"
    "Recursion_Thms"
    "Delta_System_Lemma.Cofinality"
    Least
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
  Powapply_rel :: "[i\<Rightarrow>o,i,i] \<Rightarrow> i" (\<open>Powapply\<^bsup>_\<^esup>'(_,_')\<close>) where
  "Powapply_rel(M,f,y) \<equiv> THE d. is_Powapply(M,f,y,d)"

abbreviation
  Powapply_r_set ::  "[i,i,i] \<Rightarrow> i" (\<open>Powapply\<^bsup>_\<^esup>'(_,_')\<close>) where
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

lemmas trans_Powapply_rel_closed[trans_closed] = transM[OF _ Powapply_rel_closed]

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
text\<open>First step: discipline for relation Memrel(eclose({a}))\<close>

subsubsection\<open>Discipline for relation Memrel(eclose({a}))\<close>

(* Discipline for term singleton. Duplicate in Names.thy. *)
definition
  is_singleton :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "is_singleton(A,x,z) \<equiv> \<exists>c[A]. empty(A,c) \<and> is_cons(A,x,c,z)"

lemma (in M_trivial) singleton_abs[simp] : 
    "\<lbrakk> M(x) ; M(s) \<rbrakk> \<Longrightarrow> is_singleton(M,x,s) \<longleftrightarrow> s = {x}"
  unfolding is_singleton_def using nonempty by simp

lemma (in M_trivial) singleton_closed[intro,simp] : 
    "M(x)  \<Longrightarrow> M({x})"
  unfolding is_singleton_def by simp

(*** end Discipline ***)

definition
  is_memclose_sing :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "is_memclose_sing(M,a,z) \<equiv> \<exists>s[M]. \<exists>ec[M]. is_singleton(M,a,s) \<and> is_eclose(M,s,ec) \<and>
                              membership(M,ec,z)"

lemma (in M_eclose) memclose_sing_abs[simp] : 
    "\<lbrakk> M(a) ; M(z) \<rbrakk> \<Longrightarrow> is_memclose_sing(M,a,z) \<longleftrightarrow> z = Memrel(eclose({a}))"
  unfolding is_memclose_sing_def by simp

lemma (in M_eclose) memclose_sing_closed[intro,simp] : 
    "M(x)  \<Longrightarrow> M(Memrel(eclose({x})))"
  unfolding is_memclose_sing_def by simp



text\<open>Second step: discipline for function %x f. A \<union> (\<Union>y\<in>x. Powapply(f,y))\<close>

definition
  HVfrom :: "[i,i,i] \<Rightarrow> i" where
  "HVfrom(A,f,x) \<equiv> A \<union> (\<Union>y\<in>x. Powapply(f,y))"


subsubsection\<open>Discipline for \<^term>\<open>HVfrom\<close>\<close>

text\<open>The function involves an instance of replacement. We apply discipline for it.\<close>

definition
  HVfrom_Repl :: "[i,i,i] \<Rightarrow> i" where
  "HVfrom_Repl(A,f,x) \<equiv> {z . y\<in>x, z = Powapply(f,y)}"

definition
  is_HVfrom_Repl :: "[i\<Rightarrow>o,i,i,i,i] \<Rightarrow> o" where
  "is_HVfrom_Repl(M,A,f,x,z) \<equiv> M(z) \<and> is_Replace(M,x,is_Powapply(M,f),z)"

definition
  HVfrom_Repl_rel :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> i" where
  "HVfrom_Repl_rel(M,A,f,x) \<equiv> THE d. is_HVfrom_Repl(M,A,f,x,d)"


locale M_HVfrom = M_eclose + 
  assumes 
    is_Powapply_replacement : 
      "M(K) \<Longrightarrow> strong_replacement(M,is_Powapply(M,K))"

begin

lemma univalent_is_Powapply:
  assumes "M(A)" "M(K)"
  shows "univalent(M,A,is_Powapply(M,K))"
  using assms is_Powapply_uniqueness transM[of _ A] unfolding univalent_def
  by blast

lemma is_HVfrom_Repl_uniqueness:
  assumes
    "M(A)" "M(f)" "M(x)"
    "is_HVfrom_Repl(M,A,f,x,d)" "is_HVfrom_Repl(M,A,f,x,d')"
  shows
    "d=d'"
  using assms Replace_abs[OF _ _ univalent_is_Powapply is_Powapply_closed]
    is_Pow_uniqueness
  unfolding is_HVfrom_Repl_def
  by force

lemma is_HVfrom_Repl_witness: "\<lbrakk> M(A);M(f);M(x)\<rbrakk> \<Longrightarrow> \<exists>d[M]. is_HVfrom_Repl(M,A,f,x,d)"
  using strong_replacementD[OF is_Powapply_replacement _ univalent_is_Powapply]
  unfolding is_HVfrom_Repl_def is_Replace_def
  by auto

lemma is_HVfrom_Repl_closed: "is_HVfrom_Repl(M,A,f,x,d) \<Longrightarrow> M(d)"
  unfolding is_HVfrom_Repl_def by simp

lemma HVfrom_Repl_rel_closed[intro,simp]:
  assumes "M(A)" "M(f)" "M(x)"
  shows "M(HVfrom_Repl_rel(M,A,f,x))"
proof -
  have "is_HVfrom_Repl(M, A, f, x, THE xa. is_HVfrom_Repl(M, A, f, x, xa))"
    using assms
      theI[OF ex1I[of "\<lambda>d. is_HVfrom_Repl(M,A,f,x,d)"], 
                            OF _ is_HVfrom_Repl_uniqueness[of A f x]]
      is_HVfrom_Repl_witness[of A f x]
    by auto
  then show ?thesis
    using assms is_HVfrom_Repl_closed
    unfolding HVfrom_Repl_rel_def
    by blast
qed

lemma HVfrom_Repl_rel_iff:
  assumes "M(A)" "M(f)" "M(x)" "M(d)"
  shows "is_HVfrom_Repl(M,A,f,x,d) \<longleftrightarrow> d = HVfrom_Repl_rel(M,A,f,x)"
proof (intro iffI)
  assume "d = HVfrom_Repl_rel(M,A,f,x)"
  moreover
  note assms
  moreover from this
  obtain e where "M(e)" "is_HVfrom_Repl(M,A,f,x,e)"
    using is_HVfrom_Repl_witness[of A f x] by blast
  ultimately
  show "is_HVfrom_Repl(M, A, f, x, d)"
    using is_HVfrom_Repl_uniqueness[of A] is_HVfrom_Repl_witness
      theI[OF ex1I[of "is_HVfrom_Repl(M,A,f,x)"], 
              OF _ is_HVfrom_Repl_uniqueness[of A], of e]
    unfolding HVfrom_Repl_rel_def
    by auto
next
  assume "is_HVfrom_Repl(M, A, f, x, d)"
  with assms
  show "d = HVfrom_Repl_rel(M,A,f,x)"
    using is_HVfrom_Repl_uniqueness unfolding HVfrom_Repl_rel_def
    by (blast del:the_equality intro:the_equality[symmetric])
qed

lemma def_HVfrom_Repl_rel:
  assumes "M(A)" "M(f)" "M(x)"
  shows
    (* "jc_Repl_rel(M,K) = {z . X\<in>Pow_rel(M,K), z = {z. r \<in> Pow_rel(M,K*K), well_ord(X,r) & z = ordertype(X,r)}}" *)
    "HVfrom_Repl_rel(M,A,f,x) = {z . y\<in>x, z = Powapply_rel(M,f,y)}"
    (is "_ = Replace(x,?P(f))")
proof -
  from assms
  have "X \<in> x \<Longrightarrow> is_Powapply(M, f, X, z) \<Longrightarrow> ?P(f,X,z)" for X z
    using is_Powapply_closed[of f X z] Powapply_rel_iff[of f X z]
    by (auto dest!:transM)
  with assms
  show ?thesis
    using Replace_abs[OF _ _ univalent_is_Powapply is_Powapply_closed]
       HVfrom_Repl_rel_iff[of A f x "HVfrom_Repl_rel(M, A, f, x)"]
      Powapply_rel_iff
    unfolding is_HVfrom_Repl_def
    apply (intro equalityI) 
    by (auto intro!:ReplaceI simp add:absolut dest:transM)
qed

(* end Discipline for HVfrom_Repl *)

end (* context M_HVfrom *)

definition
  is_HVfrom :: "[i\<Rightarrow>o,i,i,i,i] \<Rightarrow> o" where
  "is_HVfrom(M,A,x,f,z) \<equiv> M(z) \<and> (\<exists>u[M]. \<exists>hr[M]. is_HVfrom_Repl(M,A,f,x,hr) \<and> 
                          big_union(M,hr,u) \<and> union(M,A,u,z))"

definition
  HVfrom_rel :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> i" where
  "HVfrom_rel(M,A,x,f) \<equiv> THE d. is_HVfrom(M,A,x,f,d)"


context M_HVfrom
begin

lemma is_HVfrom_closed : "\<lbrakk> M(A);M(f);M(x);is_HVfrom(M,A,x,f,d) \<rbrakk> \<Longrightarrow> M(d)" 
  unfolding is_HVfrom_def by simp


lemma is_HVfrom_uniqueness:
  assumes
    "M(A)" "M(x)" "M(f)" 
    "is_HVfrom(M,A,x,f,d)" "is_HVfrom(M,A,x,f,d')"
  shows
    "d=d'"
  using assms is_HVfrom_Repl_uniqueness[of A f x]
  unfolding is_HVfrom_def
  by auto  
  

(* VER por que no sale igual que el witness anterior *)
lemma is_HVfrom_witness: 
  assumes "M(A)" "M(x)" "M(f)" 
  shows "\<exists>d[M]. is_HVfrom(M,A,x,f,d)"
  using assms is_HVfrom_Repl_witness[of A f x] unfolding is_HVfrom_def
  by auto


lemma HVfrom_rel_closed[intro,simp]: 
  assumes "M(A)" "M(f)" "M(x)" 
  shows "M(HVfrom_rel(M,A,x,f))"
proof -
  have "is_HVfrom(M, A, x, f, THE xa. is_HVfrom(M, A, x, f, xa))" 
    using assms 
          theI[OF ex1I[of "\<lambda>d. is_HVfrom(M,A,x,f,d)"], 
                                    OF _ is_HVfrom_uniqueness[of A x f]]
          is_HVfrom_witness[of A x f]
    by auto
  then show ?thesis 
    using assms is_HVfrom_closed
    unfolding HVfrom_rel_def
    by blast
qed

lemma HVfrom_rel_iff:
  assumes "M(A)" "M(x)" "M(f)"  "M(d)"
  shows "is_HVfrom(M,A,x,f,d) \<longleftrightarrow> d = HVfrom_rel(M,A,x,f)"
proof (intro iffI)
  assume "d = HVfrom_rel(M,A,x,f)"
  moreover
  note assms
  moreover from this
  obtain e where "M(e)" "is_HVfrom(M,A,x,f,e)"
    using is_HVfrom_witness[of A x f] by blast
  ultimately
  show "is_HVfrom(M,A,x,f,d)"
    using is_HVfrom_uniqueness[of A x f] is_HVfrom_witness[of A x f]
      theI[OF ex1I[of "is_HVfrom(M,A,x,f)"], 
                          OF _ is_HVfrom_uniqueness[of A x], of e]
    unfolding HVfrom_rel_def
    by auto
next
  assume "is_HVfrom(M,A,x,f,d)"
  with assms
  show "d = HVfrom_rel(M,A,x,f)"
    using is_HVfrom_uniqueness unfolding HVfrom_rel_def
    by (blast del:the_equality intro:the_equality[symmetric])
qed


lemma def_HVfrom_rel: 
  assumes "M(A)" "M(f)" "M(x)"
  shows "HVfrom_rel(M,A,x,f) = 
         A \<union> (\<Union>y\<in>x. Powapply_rel(M,f,y))"
proof -
  from assms
  have "HVfrom_rel(M,A,x,f) = A \<union> \<Union>(HVfrom_Repl_rel(M,A,f,x))"
    using HVfrom_rel_iff HVfrom_Repl_rel_iff
    unfolding is_HVfrom_def
    by simp
  also from assms have "... = A \<union> \<Union>({z . y\<in>x, z = Powapply_rel(M,f,y)})"
  using def_HVfrom_Repl_rel
  by simp
  finally show ?thesis by auto
qed

lemma relation2_HVfrom : 
  "M(A) \<Longrightarrow> relation2(M,is_HVfrom(M,A),HVfrom_rel(M,A))"
  using HVfrom_rel_iff
  unfolding relation2_def
  by simp

end (* context HVfrom *)


subsection\<open>Discipline for \<^term>\<open>Vfrom\<close>\<close>
(*
    "Vfrom(A,i) == transrec(i, %x f. A \<union> (\<Union>y\<in>x. Pow(f`y)))" 
*)
definition
  is_Vfrom :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_Vfrom(M,A,i,z) \<equiv> is_transrec(M,is_HVfrom(M,A),i,z)"
  
definition
  Vfrom_rel :: "[i\<Rightarrow>o,i,i] \<Rightarrow> i" where
  "Vfrom_rel(M,A,i) \<equiv> transrec(i,HVfrom_rel(M,A))"


locale M_Vfrom = M_HVfrom +
  assumes
    trepl_HVfrom : "\<lbrakk> M(A);M(i) \<rbrakk> \<Longrightarrow> transrec_replacement(M,is_HVfrom(M,A),i)"
    and 
    repl_trec_HVfrom : 
       "M(A) \<Longrightarrow> 
            strong_replacement(M, \<lambda>x y. y = \<langle>x, transrec(x, HVfrom_rel(M, A))\<rangle>)"

begin 

lemma Vfrom_rel_iff : 
  assumes "M(A)" "M(i)" "M(z)" "Ord(i)"
  shows "is_Vfrom(M,A,i,z) \<longleftrightarrow> z = Vfrom_rel(M,A,i)"
  using assms transrec_abs[OF trepl_HVfrom relation2_HVfrom]
  unfolding is_Vfrom_def Vfrom_rel_def
  by simp

(* It's not possible to apply def_HVfrom_rel because is necessary that
   x and f belong to M *)
lemma def_Vfrom_rel :
  assumes "M(A)" "M(i)" "Ord(i)"
  shows
    " Vfrom_rel(M,A,i) = transrec(i, %x f. A \<union> (\<Union>y\<in>x. Powapply_rel(M,f,y)))" 
  using assms 
        transrec_equal_on_M[OF def_HVfrom_rel trepl_HVfrom 
                               relation2_HVfrom repl_trec_HVfrom]  
  unfolding Vfrom_rel_def
  by simp

end (* context M_Vfrom *)

context cofinal_factor
begin

subsection \<open>Discipline for \<^term>\<open>factor\<close>\<close>

text\<open>Discipline for \<^term>\<open>factor_rec\<close>\<close>

(* Discipline for factor_body 

  "factor_body(\<beta>,h,x) \<equiv> (x\<in>\<delta> \<and> j`\<beta> \<le> f`x \<and> (\<forall>\<alpha><\<beta> . f`(h`\<alpha>) < f`x)) \<or> x=\<delta>" 
*)
definition 
  is_factor_body :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_factor_body(M,\<beta>,h,x) \<equiv> M(x) \<and>
    (\<exists>j\<beta>[M]. \<exists>fx[M]. fun_apply(M,j,\<beta>,j\<beta>) \<and> fun_apply(M,f,x,fx) \<and>
    (x\<in>\<delta> \<and> le_rel(M,j\<beta>,fx) \<and> (\<forall>\<alpha>[M]. lt_rel(M,\<alpha>,\<beta>) \<longrightarrow> 
          (\<exists>h\<alpha>[M]. \<exists>fh\<alpha>[M]. fun_apply(M,h,\<alpha>,h\<alpha>) \<and> fun_apply(M,f,h\<alpha>,fh\<alpha>) \<and>
                                    lt_rel(M,fh\<alpha>,fx))) \<or> x=\<delta>))"

end
                                
locale M_cofinal_factor = cofinal_factor + M_eclose +
  assumes 
    types : "M(j)"  "M(\<delta>)"  "M(\<xi>)"  "M(\<gamma>)"  "M(f)"


begin

lemma is_factor_body_closed : "is_factor_body(M,\<beta>,h,x) \<Longrightarrow> M(x)"
  unfolding is_factor_body_def by simp

lemma factor_body_closed : 
    "\<lbrakk> M(\<beta>);M(h) \<rbrakk> \<Longrightarrow> factor_body(\<beta>,h,x) \<Longrightarrow> M(x)" 
  using types unfolding factor_body_def 
  by (auto dest:transM)

lemma factor_body_abs[absolut] :
  assumes "M(\<beta>)" "M(h)"
  shows "is_factor_body(M,\<beta>,h,x ) \<longleftrightarrow> factor_body(\<beta>,h,x)"
  oops
(* proof -
  from assms
  have "is_factor_body(M,\<beta>,h,x) \<longleftrightarrow> 
       (x \<in> \<delta> \<and> j ` \<beta> \<le> f ` x \<and> (\<forall>\<alpha>[M]. \<alpha> < \<beta> \<longrightarrow> f ` (h ` \<alpha>) < f ` x) \<or> x = \<delta>)"
    for x
    using types assms
    unfolding is_factor_body_def apply (auto dest:transM)
  with assms
  show ?thesis
  using assms factor_body_closed[of \<beta> h] transM[of _ \<beta>]
  unfolding factor_body_def oall_def using types ltD 
  by force
qed
 *)
end

(* end Discipline for factor_body *)

(* Discipline for factor_rec *)

context cofinal_factor
begin

definition
  is_factor_rec :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_factor_rec(M,\<beta>,h,fr) \<equiv>  M(fr) \<and> least(M,\<lambda>x. M(x) \<and> is_factor_body(M,\<beta>,h,x),fr)"

end

locale cofinal_factor_rel = M_cofinal_factor +
  assumes
    trepl_factor : "M(\<beta>) \<Longrightarrow> transrec_replacement(M,is_factor_rec(M),\<beta>)"

begin

lemma is_factor_rec_closed : "is_factor_rec(M,\<beta>,h,fr) \<Longrightarrow> M(fr)"
  unfolding is_factor_rec_def by simp

lemma factor_rec_closed : "\<lbrakk> M(\<beta>);M(h) \<rbrakk> \<Longrightarrow> M(factor_rec(\<beta>,h))"
  using factor_body_closed Least_closed'[of "factor_body(\<beta>,h)"] 
  unfolding factor_rec_def by blast

lemma factor_rec_abs[absolut] :
  assumes "M(\<beta>)" "M(h)" "M(fr)"
  shows "is_factor_rec(M,\<beta>,h,fr) \<longleftrightarrow> fr = factor_rec(\<beta>,h)"
proof -
  from assms
  have "M(x) \<and> is_factor_body(M, \<beta>, h, x) \<longleftrightarrow> is_factor_body(M, \<beta>, h, x)" for x
    using is_factor_body_closed by auto
  with assms
  have "(\<mu> x. factor_body(\<beta>, h, x)) = (\<mu> x. M(x) \<and> is_factor_body(M, \<beta>, h, x))" 
    using factor_body_abs[of \<beta> h] Least_cong is_factor_body_closed by simp 
  with assms
  show ?thesis
    using least_abs'[of "\<lambda>x. M(x) \<and> is_factor_body(M, \<beta>, h, x)"]
    unfolding is_factor_rec_def factor_rec_def
    by simp
qed


lemma relation2_factor_rec : 
  "relation2(M,is_factor_rec(M),factor_rec)"
  unfolding relation2_def
  by (simp add:absolut)

(* end Discipline for factor_rec *)

end (* context cofinal_factor_rel *)

context cofinal_factor
begin

text\<open>Discipline for \<^term>\<open>factor\<close>\<close>

definition
  is_factor :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "is_factor(M,\<beta>,z) \<equiv> is_transrec(M,is_factor_rec(M),\<beta>,z)"
  
end

context cofinal_factor_rel
begin

lemma factor_abs[absolut] : 
  assumes "M(\<beta>)" "M(z)" "Ord(\<beta>)"
  shows "is_factor(M,\<beta>,z) \<longleftrightarrow> z = factor(\<beta>)"
  using assms transrec_abs[OF trepl_factor relation2_factor_rec] factor_rec_closed
  unfolding is_factor_def factor_def
  by simp

lemma factor_closed:
  assumes "M(\<beta>)" "Ord(\<beta>)"
  shows "M(factor(\<beta>))"
  using assms transrec_closed[OF trepl_factor relation2_factor_rec] factor_rec_closed
  unfolding is_factor_def factor_def
  by simp


end

end