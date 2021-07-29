section\<open>Cardinal Arithmetic under Choice\label{sec:cardinal-lib-rel}\<close>

theory Replacement_Lepoll
  imports
    ZF_Library_Relative
    "Delta_System_Lemma.Cardinal_Library"
    Lambda_Replacement
begin

definition
  lepoll_assumptions1 :: "[i\<Rightarrow>o,i,[i,i]\<Rightarrow>i,i,i,i,i,i,i] \<Rightarrow> o" where
  "lepoll_assumptions1(M,A,F,S,fa,K,x,f,r) \<equiv> \<forall>x\<in>S. strong_replacement(M, \<lambda>y z. y \<in> F(A, x) \<and> z = {\<langle>x, y\<rangle>})"

definition
  lepoll_assumptions2 :: "[i\<Rightarrow>o,i,[i,i]\<Rightarrow>i,i,i,i,i,i,i] \<Rightarrow> o" where
  "lepoll_assumptions2(M,A,F,S,fa,K,x,f,r) \<equiv> strong_replacement(M, \<lambda>x z. z = Sigfun(x, F(A)))"

definition
  lepoll_assumptions3 :: "[i\<Rightarrow>o,i,[i,i]\<Rightarrow>i,i,i,i,i,i,i] \<Rightarrow> o" where
  "lepoll_assumptions3(M,A,F,S,fa,K,x,f,r) \<equiv> strong_replacement(M, \<lambda>x y. y = F(A, x))"

definition
  lepoll_assumptions4 :: "[i\<Rightarrow>o,i,[i,i]\<Rightarrow>i,i,i,i,i,i,i] \<Rightarrow> o" where
  "lepoll_assumptions4(M,A,F,S,fa,K,x,f,r) \<equiv> strong_replacement(M, \<lambda>x y. y = \<langle>x, minimum(r, F(A, x))\<rangle>)"

definition
  lepoll_assumptions5 :: "[i\<Rightarrow>o,i,[i,i]\<Rightarrow>i,i,i,i,i,i,i] \<Rightarrow> o" where
  "lepoll_assumptions5(M,A,F,S,fa,K,x,f,r) \<equiv> strong_replacement(M, \<lambda>x y. y = \<langle>x, \<mu> i. x \<in> F(A, i), f ` (\<mu> i. x \<in> F(A, i)) ` x\<rangle>)"

definition
  lepoll_assumptions6 :: "[i\<Rightarrow>o,i,[i,i]\<Rightarrow>i,i,i,i,i,i,i] \<Rightarrow> o" where
  "lepoll_assumptions6(M,A,F,S,fa,K,x,f,r) \<equiv> strong_replacement(M, \<lambda>y z. y \<in> inj\<^bsup>M\<^esup>(F(A, x),S) \<and> z = {\<langle>x, y\<rangle>})"

definition
  lepoll_assumptions7 :: "[i\<Rightarrow>o,i,[i,i]\<Rightarrow>i,i,i,i,i,i,i] \<Rightarrow> o" where
  "lepoll_assumptions7(M,A,F,S,fa,K,x,f,r) \<equiv> strong_replacement(M, \<lambda>x y. y = inj\<^bsup>M\<^esup>(F(A, x),S))"

definition
  lepoll_assumptions8 :: "[i\<Rightarrow>o,i,[i,i]\<Rightarrow>i,i,i,i,i,i,i] \<Rightarrow> o" where
  "lepoll_assumptions8(M,A,F,S,fa,K,x,f,r) \<equiv> strong_replacement(M, \<lambda>x z. z = Sigfun(x, \<lambda>i. inj\<^bsup>M\<^esup>(F(A, i),S)))"

definition
  lepoll_assumptions9 :: "[i\<Rightarrow>o,i,[i,i]\<Rightarrow>i,i,i,i,i,i,i] \<Rightarrow> o" where
  "lepoll_assumptions9(M,A,F,S,fa,K,x,f,r) \<equiv> strong_replacement(M, \<lambda>x y. y = \<langle>x, minimum(r, inj\<^bsup>M\<^esup>(F(A, x),S))\<rangle>)"

definition
  lepoll_assumptions10 :: "[i\<Rightarrow>o,i,[i,i]\<Rightarrow>i,i,i,i,i,i,i] \<Rightarrow> o" where
  "lepoll_assumptions10(M,A,F,S,fa,K,x,f,r) \<equiv> strong_replacement
           (M, \<lambda>x z. z = Sigfun(x, \<lambda>k. if k \<in> range(f) then F(A, converse(f) ` k) else 0))"

definition
  lepoll_assumptions11 :: "[i\<Rightarrow>o,i,[i,i]\<Rightarrow>i,i,i,i,i,i,i] \<Rightarrow> o" where
  "lepoll_assumptions11(M,A,F,S,fa,K,x,f,r) \<equiv> strong_replacement(M, \<lambda>x y. y = (if x \<in> range(f) then F(A, converse(f) ` x) else 0))"

definition
  lepoll_assumptions12 :: "[i\<Rightarrow>o,i,[i,i]\<Rightarrow>i,i,i,i,i,i,i] \<Rightarrow> o" where
  "lepoll_assumptions12(M,A,F,S,fa,K,x,f,r) \<equiv> strong_replacement(M, \<lambda>y z. y \<in> F(A, converse(f) ` x) \<and> z = {\<langle>x, y\<rangle>})"

definition
  lepoll_assumptions13 :: "[i\<Rightarrow>o,i,[i,i]\<Rightarrow>i,i,i,i,i,i,i] \<Rightarrow> o" where
  "lepoll_assumptions13(M,A,F,S,fa,K,x,f,r) \<equiv> strong_replacement
         (M, \<lambda>x y. y = \<langle>x, minimum(r, if x \<in> range(f) then F(A, converse(f) ` x) else 0)\<rangle>)"

definition
  lepoll_assumptions14 :: "[i\<Rightarrow>o,i,[i,i]\<Rightarrow>i,i,i,i,i,i,i] \<Rightarrow> o" where
  "lepoll_assumptions14(M,A,F,S,fa,K,x,f,r) \<equiv> strong_replacement
         (M, \<lambda>x y. y = \<langle>x, \<mu> i. x \<in> (if i \<in> range(f) then F(A, converse(f) ` i) else 0),
                        fa ` (\<mu> i. x \<in> (if i \<in> range(f) then F(A, converse(f) ` i) else 0)) ` x\<rangle>)"

definition
  lepoll_assumptions15 :: "[i\<Rightarrow>o,i,[i,i]\<Rightarrow>i,i,i,i,i,i,i] \<Rightarrow> o" where
  "lepoll_assumptions15(M,A,F,S,fa,K,x,f,r) \<equiv> strong_replacement
         (M, \<lambda>y z. y \<in> inj\<^bsup>M\<^esup>(if x \<in> range(f) then F(A, converse(f) ` x) else 0,K) \<and> z = {\<langle>x, y\<rangle>})"

definition
  lepoll_assumptions16 :: "[i\<Rightarrow>o,i,[i,i]\<Rightarrow>i,i,i,i,i,i,i] \<Rightarrow> o" where
  "lepoll_assumptions16(M,A,F,S,fa,K,x,f,r) \<equiv> strong_replacement(M, \<lambda>x y. y = inj\<^bsup>M\<^esup>(if x \<in> range(f) then F(A, converse(f) ` x) else 0,K))"

definition
  lepoll_assumptions17 :: "[i\<Rightarrow>o,i,[i,i]\<Rightarrow>i,i,i,i,i,i,i] \<Rightarrow> o" where
  "lepoll_assumptions17(M,A,F,S,fa,K,x,f,r) \<equiv> strong_replacement
             (M, \<lambda>x z. z = Sigfun(x, \<lambda>i. inj\<^bsup>M\<^esup>(if i \<in> range(f) then F(A, converse(f) ` i) else 0,K)))"

definition
  lepoll_assumptions18 :: "[i\<Rightarrow>o,i,[i,i]\<Rightarrow>i,i,i,i,i,i,i] \<Rightarrow> o" where
  "lepoll_assumptions18(M,A,F,S,fa,K,x,f,r) \<equiv> strong_replacement
         (M, \<lambda>x y. y = \<langle>x, minimum(r, inj\<^bsup>M\<^esup>(if x \<in> range(f) then F(A, converse(f) ` x) else 0,K))\<rangle>)"

lemmas lepoll_assumptions_defs[simp] = lepoll_assumptions1_def
  lepoll_assumptions2_def lepoll_assumptions3_def lepoll_assumptions4_def
  lepoll_assumptions5_def lepoll_assumptions6_def lepoll_assumptions7_def
  lepoll_assumptions8_def lepoll_assumptions9_def lepoll_assumptions10_def
  lepoll_assumptions11_def lepoll_assumptions12_def lepoll_assumptions13_def
  lepoll_assumptions14_def lepoll_assumptions15_def lepoll_assumptions16_def
  lepoll_assumptions17_def lepoll_assumptions18_def

locale M_replacement_lepoll = M_replacement + M_inj +
  fixes F
  assumes
    F_type[simp]: "M(A) \<Longrightarrow> \<forall>x[M]. M(F(A,x))"
    (* and
    types[simp]:"M(A)" "M(S)" "M(fa)" "M(K)" "M(x)" "M(f)" "M(r)" *)
    and
    lam_lepoll_assumption_F:"M(A) \<Longrightarrow> lam_replacement(M,F(A))"
    and
    lam_replacement_inj_rel:"lam_replacement(M, \<lambda>p. inj\<^bsup>M\<^esup>(fst(p),snd(p)))"
begin

lemma lepoll_assumptions1:
  assumes types[simp]:"M(A)" "M(S)"
  shows "lepoll_assumptions1(M,A,F,S,fa,K,x,f,r)"
  unfolding lepoll_assumptions1_def
  using strong_replacement_separation[OF lam_replacement_surj_imp_inj1 separation_in]
    transM[of _ S] 
  by simp

lemma lepoll_assumptions3:
  assumes types[simp]:"M(A)"
  shows "lepoll_assumptions3(M,A,F,S,fa,K,x,f,r)"
  using lam_lepoll_assumption_F[THEN lam_replacement_imp_strong_replacement]
  unfolding lepoll_assumptions_defs by simp

lemma lepoll_assumptions4:
  assumes types[simp]:"M(A)" "M(r)"
  shows "lepoll_assumptions4(M,A,F,S,fa,K,x,f,r)"
  using lam_replacement_minimum lam_replacement_constant lam_lepoll_assumption_F
  unfolding lepoll_assumptions_defs
    lam_replacement_def[symmetric]
  by (rule_tac lam_replacement_hcomp2[of _ _ minimum])
    (force intro: lam_replacement_identity)+

lemma lepoll_assumptions6:  
  assumes types[simp]:"M(A)" "M(S)" "M(x)"
  shows "lepoll_assumptions6(M,A,F,S,fa,K,x,f,r)"
  using strong_replacement_separation[OF lam_replacement_surj_imp_inj1 separation_in]
    transM[of _ S] lam_replacement_inj_rel
  unfolding lepoll_assumptions6_def
  by simp

lemma lepoll_assumptions9:
  assumes types[simp]:"M(A)" "M(S)" "M(r)"
  shows "lepoll_assumptions9(M,A,F,S,fa,K,x,f,r)"
  using lam_replacement_minimum lam_replacement_constant lam_lepoll_assumption_F
    lam_replacement_hcomp2[of _ _ "inj_rel(M)"] lam_replacement_inj_rel lepoll_assumptions4
  unfolding lepoll_assumptions_defs lam_replacement_def[symmetric]
  by (rule_tac lam_replacement_hcomp2[of _ _ minimum])
    (force intro: lam_replacement_identity)+

lemma lepoll_assumptions11:
  assumes types[simp]:"M(A)" "M(f)"
  shows "lepoll_assumptions11(M, A, F, S, fa, K, x, f, r)"
  using lam_replacement_imp_strong_replacement
    lam_replacement_if[OF _ _ separation_in[of "range(f)"]]
    lam_replacement_constant
    lam_replacement_hcomp lam_replacement_apply
    lam_lepoll_assumption_F
  unfolding lepoll_assumptions11_def
  by simp

lemma lepoll_assumptions12:
  assumes types[simp]:"M(A)" "M(x)" "M(f)"
  shows "lepoll_assumptions12(M,A,F,S,fa,K,x,f,r)"
  using strong_replacement_separation[OF lam_replacement_surj_imp_inj1 separation_in]
    transM[of _ S] 
  unfolding lepoll_assumptions12_def
  by simp

lemmas lepoll_assumptions = lepoll_assumptions1 lepoll_assumptions3
  lepoll_assumptions4 lepoll_assumptions6 lepoll_assumptions9 
  lepoll_assumptions11 lepoll_assumptions12

find_theorems name:lepoll_assumptions name:def -name:defs
-name:"assumptions1_" -name:assumptions6 -name:assumptions3 -name:assumptions4 -name:assumptions9
-name:"assumptions11_" -name:"assumptions12_"
end (* M_replacement_lepoll *)

end