theory Discipline_Univ
  imports
    "ZF-Constructible.Rank"
    "Relativization"
    "HOL-Eisbach.Eisbach_Old_Appl_Syntax"\<comment> \<open>if put before, it breaks some simps\<close>
    "../Tools/Try0"
    "Discipline_Base"
    "Recursion_Thms"
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
    by (auto dest!:transM[OF _ \<open>M(x)\<close>])
  with assms
  show ?thesis
    using Replace_abs[OF _ _ univalent_is_Powapply is_Powapply_closed]
       HVfrom_Repl_rel_iff[of A f x "HVfrom_Repl_rel(M, A, f, x)"]
      Powapply_rel_iff
    unfolding is_HVfrom_Repl_def
    apply (intro equalityI) 
    by (auto intro!:ReplaceI simp add:absolut transM[OF _ \<open>M(x)\<close>])
qed

(* end Discipline for HVfrom_Repl *)

end (* context M_HVfrom *)

definition
  is_HVfrom :: "[i\<Rightarrow>o,i,i,i,i] \<Rightarrow> o" where
  "is_HVfrom(M,A,f,x,z) \<equiv> M(z) \<and> (\<exists>u[M]. \<exists>hr[M]. is_HVfrom_Repl(M,A,f,x,hr) \<and> 
                          big_union(M,hr,u) \<and> union(M,A,u,z))"

definition
  HVfrom_rel :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> i" where
  "HVfrom_rel(M,A,f,x) \<equiv> THE d. is_HVfrom(M,A,f,x,d)"


context M_HVfrom
begin

lemma is_HVfrom_closed : "\<lbrakk> M(A);M(f);M(x);is_HVfrom(M,A,f,x,d) \<rbrakk> \<Longrightarrow> M(d)" 
  unfolding is_HVfrom_def by simp


lemma is_HVfrom_uniqueness:
  assumes
    "M(A)" "M(f)" "M(x)"
    "is_HVfrom(M,A,f,x,d)" "is_HVfrom(M,A,f,x,d')"
  shows
    "d=d'"
  using assms is_HVfrom_Repl_uniqueness[of A f x]
  unfolding is_HVfrom_def
  by auto  
  

(* VER por que no sale igual que el witness anterior *)
lemma is_HVfrom_witness: 
  assumes "M(A)" "M(f)" "M(x)"
  shows "\<exists>d[M]. is_HVfrom(M,A,f,x,d)"
  using assms is_HVfrom_Repl_witness[of A f x] unfolding is_HVfrom_def
  by auto


lemma HVfrom_rel_closed[intro,simp]: 
  assumes "M(A)" "M(f)" "M(x)" 
  shows "M(HVfrom_rel(M,A,f,x))"
proof -
  have "is_HVfrom(M, A, f, x, THE xa. is_HVfrom(M, A, f, x, xa))" 
    using assms 
          theI[OF ex1I[of "\<lambda>d. is_HVfrom(M,A,f,x,d)"], 
                                    OF _ is_HVfrom_uniqueness[of A f x]]
          is_HVfrom_witness[of A f x]
    by auto
  then show ?thesis 
    using assms is_HVfrom_closed
    unfolding HVfrom_rel_def
    by blast
qed

lemma HVfrom_rel_iff:
  assumes "M(A)" "M(f)" "M(x)" "M(d)"
  shows "is_HVfrom(M,A,f,x,d) \<longleftrightarrow> d = HVfrom_rel(M,A,f,x)"
proof (intro iffI)
  assume "d = HVfrom_rel(M,A,f,x)"
  moreover
  note assms
  moreover from this
  obtain e where "M(e)" "is_HVfrom(M,A,f,x,e)"
    using is_HVfrom_witness[of A f x] by blast
  ultimately
  show "is_HVfrom(M,A,f,x, d)"
    using is_HVfrom_uniqueness[of A f x] is_HVfrom_witness[of A f x]
      theI[OF ex1I[of "is_HVfrom(M,A,f,x)"], 
                          OF _ is_HVfrom_uniqueness[of A f x], of e]
    unfolding HVfrom_rel_def
    by auto
next
  assume "is_HVfrom(M,A,f,x, d)"
  with assms
  show "d = HVfrom_rel(M,A,f,x)"
    using is_HVfrom_uniqueness unfolding HVfrom_rel_def
    by (blast del:the_equality intro:the_equality[symmetric])
qed


lemma def_HVfrom_rel: 
  assumes "M(A)" "M(f)" "M(x)"
  shows "HVfrom_rel(M,A,f,x) = 
         A \<union> (\<Union>y\<in>x. Powapply_rel(M,f,y))"
proof -
  from assms
  have "HVfrom_rel(M,A,f,x) = A \<union> \<Union>(HVfrom_Repl_rel(M,A,f,x))"
    using HVfrom_rel_iff HVfrom_Repl_rel_iff
    unfolding is_HVfrom_def
    by simp
  also from assms have "... = A \<union> \<Union>({z . y\<in>x, z = Powapply_rel(M,f,y)})"
  using def_HVfrom_Repl_rel
  by simp
  finally show ?thesis by auto
qed

end (* context M_Hvfrom *)

(*** end Discipline for HVfrom ***)


text\<open>The third step is prove some results for the relative versions of the relation 
and the function HVfrom\<close>

text\<open>We define a term for the transitive closure of relation\<close>
definition
  rvfrom :: "i \<Rightarrow> i" where
  "rvfrom(a) \<equiv> Memrel(eclose({a}))^+"


context M_eclose
begin 

lemma wf_rvfrom : "M(x) \<Longrightarrow> wf(rvfrom(x))" 
  unfolding rvfrom_def using wf_trancl[OF wf_Memrel] .

lemma trans_rvfrom : "M(x) \<Longrightarrow> trans(rvfrom(x))"
  unfolding rvfrom_def using trans_trancl .

lemma relation_rvfrom : "M(x) \<Longrightarrow> relation(rvfrom(x))" 
  unfolding rvfrom_def using relation_trancl .

lemma rvfrom_in_M : "M(x) \<Longrightarrow> M(rvfrom(x))" 
  unfolding rvfrom_def by simp

lemmas rvfrom_thms = wf_rvfrom trans_rvfrom relation_rvfrom rvfrom_in_M

end

context M_HVfrom
begin

lemma relation2_HVfrom : 
  "M(A) \<Longrightarrow> relation2(M,is_HVfrom(M,A),HVfrom_rel(M,A))"
  using HVfrom_rel_iff
  unfolding relation2_def
  by simp

end


subsection\<open>Discipline for \<^term>\<open>Vfrom\<close>\<close>
(*
    "Vfrom(A,i) == transrec(i, %x f. A \<union> (\<Union>y\<in>x. Pow(f`y)))" 
*)
definition
  is_Vfrom :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_Vfrom(M,A,i,z) \<equiv> is_wfrec(M,is_HVfrom(M,A),rvfrom(i),i,z)"
  
definition
  Vfrom_rel :: "[i\<Rightarrow>o,i,i] \<Rightarrow> i" where
  "Vfrom_rel(M,A,i) \<equiv> wfrec(Memrel(eclose({i})),i,HVfrom_rel(M,A))"


locale M_Vfrom = M_HVfrom +
  assumes
    wfrepl_HVfrom : "\<lbrakk> M(A);M(a) \<rbrakk> \<Longrightarrow> wfrec_replacement(M,is_HVfrom(M,A),rvfrom(a))"

begin 

lemma HVfrom_rel_trancl:
      "HVfrom_rel(M,A,y, restrict(f,Memrel(eclose({x}))-``{y}))
              = HVfrom_rel(M,A,y, restrict(f,(Memrel(eclose({x}))^+)-``{y}))"
  sorry

lemma Vfrom_rel_trancl: "Vfrom_rel(M,A,x) = wfrec(rvfrom(x), x, HVfrom_rel(M,A))"
proof -
  have "Vfrom_rel(M,A,x) =  wfrec(Memrel(eclose({x})), x, HVfrom_rel(M,A))"
    (is "_ = wfrec(?r,_,_)")
    unfolding Vfrom_rel_def by simp
  also
  have " ... = wftrec(?r^+, x, \<lambda>y f. HVfrom_rel(M,A,y, restrict(f,?r-``{y})))"
    unfolding wfrec_def ..
  also
  have " ... = wftrec(?r^+, x, \<lambda>y f. HVfrom_rel(M,A,y, restrict(f,(?r^+)-``{y})))"
    using HVfrom_rel_trancl by simp
  also
  have " ... =  wfrec(?r^+, x, HVfrom_rel(M,A))"
    unfolding wfrec_def using trancl_eq_r[OF relation_trancl trans_trancl] by simp
  finally
  show ?thesis unfolding rvfrom_def .
qed

lemma Vfrom_rel_iff : 
  assumes "M(A)" "M(i)" "M(z)"
  shows "is_Vfrom(M,A,i,z) \<longleftrightarrow> z = Vfrom_rel(M,A,i)"
proof -
  from assms
  have "is_Vfrom(M,A,i,z) \<longleftrightarrow> z = wfrec(rvfrom(i),i,HVfrom_rel(M,A))" 
    using rvfrom_thms wfrepl_HVfrom relation2_HVfrom 
          trans_wfrec_abs[of "rvfrom(i)" i z "is_HVfrom(M,A)" "HVfrom_rel(M,A)"]
    unfolding is_Vfrom_def
    by simp
  then show ?thesis
    using Vfrom_rel_trancl
    by simp
qed

(* Observación: No podemos aplicar def_HVfrom_rel 
   ya que necesito que f esté en M*)
lemma def_Vfrom_rel :
  "\<lbrakk> M(A);M(x) \<rbrakk> \<Longrightarrow> 
    Vfrom_rel(M,A,x) = transrec(i, %x f. A \<union> (\<Union>y\<in>x. Powapply_rel(M,f,y)))"
  unfolding Vfrom_rel_def transrec_def
  using def_HVfrom_rel
  apply simp
  sorry



(*
Varias observaciones para la reunión:


(*

theorem (in M_trancl) trans_wfrec_abs:
  "[|wf(r);  trans(r);  relation(r);  M(r);  M(a);  M(z);
     wfrec_replacement(M,MH,r);  relation2(M,MH,H);
     \<forall>x[M]. \<forall>g[M]. function(g) \<longrightarrow> M(H(x,g))|] 
   ==> is_wfrec(M,MH,r,a,z) \<longleftrightarrow> z=wfrec(r,a,H)" 
by (simp add: trans_wfrec_relativize [THEN iff_sym] is_wfrec_abs, blast)  
*)
