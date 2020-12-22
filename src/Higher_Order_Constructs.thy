section\<open>Fully relational versions of higher order construct \<close>
theory Higher_Order_Constructs
  imports 
    "ZF-Constructible.Relative"
    "ZF-Constructible.Datatype_absolute"
    Least

begin

definition
  is_If :: "[i\<Rightarrow>o,o,i,i,i] \<Rightarrow> o" where
  "is_If(M,b,t,f,r) \<equiv> (b \<and> r=t) \<or> (\<not>b \<and> r=f)"

lemma (in M_trans) If_abs:
     "M(t) \<Longrightarrow> M(f) \<Longrightarrow> M(r) \<Longrightarrow> is_If(M,b,t,f,r) \<longleftrightarrow> r = If(b,t,f)"
by (simp add: is_If_def)

definition
  is_The :: "[i\<Rightarrow>o,i\<Rightarrow>o,i] \<Rightarrow> o" where
  "is_The(M,Q,i) \<equiv> (Q(i) \<and> (\<exists>x[M]. Q(x) \<and> (\<forall>y[M]. Q(y) \<longrightarrow> y = x))) \<or>
                   (\<not>(\<exists>x[M]. Q(x) \<and> (\<forall>y[M]. Q(y) \<longrightarrow> y = x))) \<and> empty(M,i) "

lemma (in M_trans) The_abs:
  assumes "\<And>x. Q(x) \<Longrightarrow> M(x)" "M(a)"
  shows "is_The(M,Q,a) \<longleftrightarrow> a = (THE x. Q(x))"
proof (cases "\<exists>x[M]. Q(x) \<and> (\<forall>y[M]. Q(y) \<longrightarrow> y = x)")
  case True
  with assms
  show ?thesis 
    unfolding is_The_def 
    by (intro iffI the_equality[symmetric]) 
      (auto, blast intro:theI)
next
  case False
  with \<open>\<And>x. Q(x) \<Longrightarrow> M(x)\<close>
  have " \<not> (\<exists>x. Q(x) \<and> (\<forall>y. Q(y) \<longrightarrow> y = x))"
    by auto
  then
  have "The(Q) = 0"
    by (intro the_0) auto 
  with assms and False
  show ?thesis
    unfolding is_The_def 
     by auto
qed

(*
definition
  recursor  :: "[i, [i,i]=>i, i]=>i"  where
    "recursor(a,b,k) \<equiv>  transrec(k, \<lambda>n f. nat_case(a, \<lambda>m. b(m, f`m), n))"
*)

definition
  is_recursor :: "[i\<Rightarrow>o,i,[i,i,i]\<Rightarrow>o,i,i] \<Rightarrow>o" where
  "is_recursor(M,a,is_b,k,r) \<equiv> is_transrec(M, \<lambda>n f ntc. is_nat_case(M,a,
      \<lambda>m bmfm.
      \<exists>fm[M]. fun_apply(M,f,m,fm) \<and> is_b(m,fm,bmfm),n,ntc),k,r)"

lemma (in M_eclose) recursor_abs:
  assumes "Ord(k)" and
    types: "M(a)" "M(k)" "M(r)" and
    b_iff: "\<And>m f bmf. M(m) \<Longrightarrow> M(f) \<Longrightarrow> M(bmf) \<Longrightarrow> is_b(m,f,bmf)  \<longleftrightarrow> bmf = b(m,f)" and
    b_closed: "\<And>m f bmf. M(m) \<Longrightarrow> M(f) \<Longrightarrow> M(b(m,f))" and
    repl: "transrec_replacement(M, \<lambda>n f ntc. is_nat_case(M, a,
        \<lambda>m bmfm. \<exists>fm[M]. fun_apply(M, f, m, fm) \<and> is_b( m, fm, bmfm), n, ntc), k)"
  shows
    "is_recursor(M,a,is_b,k,r) \<longleftrightarrow> r = recursor(a,b,k)"
  unfolding is_recursor_def recursor_def
  using assms
  apply (rule_tac transrec_abs)
  apply (auto simp:relation2_def)
  apply (rule nat_case_abs[THEN iffD1, where is_b1="\<lambda>m bmfm.
      \<exists>fm[M]. fun_apply(M,_,m,fm) \<and> is_b(m,fm,bmfm)"])
  apply (auto simp:relation1_def)
  apply (rule nat_case_abs[THEN iffD2, where is_b1="\<lambda>m bmfm.
      \<exists>fm[M]. fun_apply(M,_,m,fm) \<and> is_b(m,fm,bmfm)"])
  apply (auto simp:relation1_def)
  done

definition
  is_wfrec_on :: "[i=>o,[i,i,i]=>o,i,i,i, i] => o" where
  "is_wfrec_on(M,MH,A,r,a,z) == is_wfrec(M,MH,r,a,z)"

lemma (in M_trancl) trans_wfrec_on_abs:
  "[|wf(r);  trans(r);  relation(r);  M(r);  M(a);  M(z);
     wfrec_replacement(M,MH,r);  relation2(M,MH,H);
     \<forall>x[M]. \<forall>g[M]. function(g) \<longrightarrow> M(H(x,g));
     r-``{a}\<subseteq>A; a \<in> A|]
   ==> is_wfrec_on(M,MH,A,r,a,z) \<longleftrightarrow> z=wfrec[A](r,a,H)"
  using trans_wfrec_abs wfrec_trans_restr
  unfolding is_wfrec_on_def by simp

end