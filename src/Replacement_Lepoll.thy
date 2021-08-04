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
  "lepoll_assumptions5(M,A,F,S,fa,K,x,f,r) \<equiv> 
strong_replacement(M, \<lambda>x y. y = \<langle>x, \<mu> i. x \<in> F(A, i), f ` (\<mu> i. x \<in> F(A, i)) ` x\<rangle>)"

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

definition if_range_F where
 [simp]: "if_range_F(F,A,f,i) \<equiv> 
  if i \<in> range(f) then F(A, converse(f) ` i) else 0"

definition if_range_F_else_F where
 [simp]: "if_range_F_else_F(F,b,A,f,i) \<equiv> if b=0 then if_range_F(F,A,f,i) else F(A,i)"

locale M_replacement_lepoll = M_replacement + M_inj +
  fixes F
  assumes
    F_type[simp]: "M(A) \<Longrightarrow> \<forall>x[M]. M(F(A,x))"
    and
    lam_lepoll_assumption_F:"M(A) \<Longrightarrow> lam_replacement(M,F(A))"
    and
    \<comment> \<open>Here b is a Boolean.\<close>
    lam_Least_assumption:"M(A) \<Longrightarrow> M(b) \<Longrightarrow> M(f) \<Longrightarrow> 
        lam_replacement(M,\<lambda>x . \<mu> i. x \<in> if_range_F_else_F(F,b,A,f,i))"
    and
    (* FIXME: Remove the closure of least. *)
    lam_Least_closed : "M(A) \<Longrightarrow> M(b) \<Longrightarrow> M(f) \<Longrightarrow>
        \<forall>x[M]. M(\<mu> i. x \<in> if_range_F_else_F(F,b,A,f,i))"
    and
    lam_replacement_inj_rel:"lam_replacement(M, \<lambda>p. inj\<^bsup>M\<^esup>(fst(p),snd(p)))"
begin

lemma lepoll_assumptions1:
  assumes types[simp]:"M(A)" "M(S)"
  shows "lepoll_assumptions1(M,A,F,S,fa,K,x,f,r)"
  using strong_replacement_separation[OF lam_replacement_surj_imp_inj1 separation_in]
    transM[of _ S]
  by simp

lemma lepoll_assumptions2:
  assumes types[simp]:"M(A)" "M(S)"
  shows "lepoll_assumptions2(M,A,F,S,fa,K,x,f,r)"
  using lam_replacement_Sigfun lam_replacement_imp_strong_replacement
    assms lam_lepoll_assumption_F
  by simp

lemma lepoll_assumptions3:
  assumes types[simp]:"M(A)"
  shows "lepoll_assumptions3(M,A,F,S,fa,K,x,f,r)"
  using lam_lepoll_assumption_F[THEN lam_replacement_imp_strong_replacement]
  by simp

lemma lepoll_assumptions4:
  assumes types[simp]:"M(A)" "M(r)"
  shows "lepoll_assumptions4(M,A,F,S,fa,K,x,f,r)"
  using lam_replacement_minimum lam_replacement_constant lam_lepoll_assumption_F
  unfolding lepoll_assumptions_defs
    lam_replacement_def[symmetric]
  by (rule_tac lam_replacement_hcomp2[of _ _ minimum])
    (force intro: lam_replacement_identity)+

lemma lepoll_assumptions5:
   assumes
    types[simp]:"M(A)" "M(f)"
  shows "lepoll_assumptions5(M,A,F,S,fa,K,x,f,r)"
  using 
    lam_replacement_apply2[THEN [5] lam_replacement_hcomp2]
    lam_replacement_hcomp[OF _ lam_replacement_apply[of f]]
    lam_replacement_identity
    lam_replacement_pullback lam_Least_closed[where b=1]
    assms lam_Least_assumption[where b=1,OF \<open>M(A)\<close> _ \<open>M(f)\<close>]
  unfolding lepoll_assumptions_defs
    lam_replacement_def[symmetric]
  by simp

lemma lepoll_assumptions6:
  assumes types[simp]:"M(A)" "M(S)" "M(x)"
  shows "lepoll_assumptions6(M,A,F,S,fa,K,x,f,r)"
  using strong_replacement_separation[OF lam_replacement_surj_imp_inj1 separation_in]
     lam_replacement_inj_rel
  by simp

lemma lepoll_assumptions7:
  assumes types[simp]:"M(A)" "M(S)" "M(x)"
  shows "lepoll_assumptions7(M,A,F,S,fa,K,x,f,r)"
  using lam_replacement_constant lam_lepoll_assumption_F lam_replacement_inj_rel
  unfolding lepoll_assumptions_defs
  by (rule_tac lam_replacement_imp_strong_replacement)
    (rule_tac lam_replacement_hcomp2[of _ _ "inj_rel(M)"], simp_all)

lemma lepoll_assumptions8:
  assumes types[simp]:"M(A)" "M(S)"
  shows "lepoll_assumptions8(M,A,F,S,fa,K,x,f,r)"
  using lam_replacement_Sigfun lam_replacement_imp_strong_replacement
    lam_replacement_inj_rel lam_replacement_constant
    lam_replacement_hcomp2[of _ _ "inj_rel(M)",OF lam_lepoll_assumption_F[of A]]
  by simp

lemma lepoll_assumptions9:
  assumes types[simp]:"M(A)" "M(S)" "M(r)"
  shows "lepoll_assumptions9(M,A,F,S,fa,K,x,f,r)"
  using lam_replacement_minimum lam_replacement_constant lam_lepoll_assumption_F
    lam_replacement_hcomp2[of _ _ "inj_rel(M)"] lam_replacement_inj_rel lepoll_assumptions4
  unfolding lepoll_assumptions_defs lam_replacement_def[symmetric]
  by (rule_tac lam_replacement_hcomp2[of _ _ minimum])
    (force intro: lam_replacement_identity)+

lemma lepoll_assumptions10:
  assumes types[simp]:"M(A)" "M(f)"
  shows "lepoll_assumptions10(M,A,F,S,fa,K,x,f,r)"
  using lam_replacement_Sigfun lam_replacement_imp_strong_replacement
    lam_replacement_constant[OF nonempty]
    lam_replacement_if[OF _ _ separation_in]
    lam_replacement_hcomp
       lam_replacement_apply[OF converse_closed[OF \<open>M(f)\<close>]]
       lam_lepoll_assumption_F[of A]
  by simp

lemma lepoll_assumptions11:
  assumes types[simp]:"M(A)" "M(f)"
  shows "lepoll_assumptions11(M, A, F, S, fa, K, x, f, r)"
  using lam_replacement_imp_strong_replacement
    lam_replacement_if[OF _ _ separation_in[of "range(f)"]]
    lam_replacement_constant
    lam_replacement_hcomp lam_replacement_apply
    lam_lepoll_assumption_F
  by simp

lemma lepoll_assumptions12:
  assumes types[simp]:"M(A)" "M(x)" "M(f)"
  shows "lepoll_assumptions12(M,A,F,S,fa,K,x,f,r)"
  using strong_replacement_separation[OF lam_replacement_surj_imp_inj1 separation_in]
  by simp

lemma lepoll_assumptions13:
  assumes types[simp]:"M(A)" "M(r)" "M(f)"
  shows "lepoll_assumptions13(M,A,F,S,fa,K,x,f,r)"
  using  lam_replacement_constant[OF nonempty] lam_lepoll_assumption_F
    lam_replacement_hcomp lam_replacement_converse lam_replacement_apply
    lam_replacement_hcomp2[OF lam_replacement_constant[OF \<open>M(r)\<close>]
        lam_replacement_if[OF _ _ separation_in[of "range(f)"]] _ _
        lam_replacement_minimum] assms
  unfolding lepoll_assumptions_defs
    lam_replacement_def[symmetric]
  by simp

lemma lepoll_assumptions14:
  assumes types[simp]:"M(A)" "M(f)" "M(fa)"
  shows "lepoll_assumptions14(M,A,F,S,fa,K,x,f,r)"
  using 
    lam_replacement_apply2[THEN [5] lam_replacement_hcomp2]
    lam_replacement_hcomp[OF _ lam_replacement_apply[of fa]]
    lam_replacement_identity
    lam_replacement_pullback  lam_Least_closed[where b=0]
    assms lam_Least_assumption[where b=0,OF \<open>M(A)\<close> _ \<open>M(f)\<close>]
  unfolding lepoll_assumptions_defs
    lam_replacement_def[symmetric]
 by simp

lemma lepoll_assumptions15:
  assumes types[simp]:"M(A)" "M(x)" "M(f)" "M(K)"
  shows "lepoll_assumptions15(M,A,F,S,fa,K,x,f,r)"
  using strong_replacement_separation[OF lam_replacement_surj_imp_inj1 separation_in]
  by simp

lemma lepoll_assumptions16:
  assumes types[simp]:"M(A)" "M(f)" "M(K)"
  shows "lepoll_assumptions16(M,A,F,S,fa,K,x,f,r)"
  using lam_replacement_imp_strong_replacement
    lam_replacement_inj_rel lam_replacement_constant
    lam_replacement_hcomp2[of _ _ "inj_rel(M)"]
    lam_replacement_constant[OF nonempty]
    lam_replacement_if[OF _ _ separation_in]
    lam_replacement_hcomp
       lam_replacement_apply[OF converse_closed[OF \<open>M(f)\<close>]]
       lam_lepoll_assumption_F[of A]
  by simp

lemma lepoll_assumptions17:
  assumes types[simp]:"M(A)" "M(f)" "M(K)"
  shows "lepoll_assumptions17(M,A,F,S,fa,K,x,f,r)"
  using lam_replacement_Sigfun lam_replacement_imp_strong_replacement
    lam_replacement_inj_rel lam_replacement_constant
    lam_replacement_hcomp2[of _ _ "inj_rel(M)"]
    lam_replacement_constant[OF nonempty]
    lam_replacement_if[OF _ _ separation_in]
    lam_replacement_hcomp
       lam_replacement_apply[OF converse_closed[OF \<open>M(f)\<close>]]
       lam_lepoll_assumption_F[of A]
  by simp

lemma lepoll_assumptions18:
  assumes types[simp]:"M(A)" "M(K)" "M(f)" "M(r)"
  shows "lepoll_assumptions18(M,A,F,S,fa,K,x,f,r)"
  using lam_replacement_constant lam_replacement_inj_rel lam_lepoll_assumption_F
    lam_replacement_minimum lam_replacement_identity lam_replacement_apply2 separation_in
  unfolding lepoll_assumptions18_def lam_replacement_def[symmetric]
  apply (rule_tac lam_replacement_hcomp2[of _ _ minimum], simp_all)
  by (rule_tac lam_replacement_hcomp2[of _ _ "inj_rel(M)"], simp_all)
    (rule_tac lam_replacement_if, rule_tac lam_replacement_hcomp[of _ "F(A)"],
      rule_tac lam_replacement_hcomp2[of _ _ "(`)"], simp_all)

lemmas lepoll_assumptions = lepoll_assumptions1 lepoll_assumptions2
  lepoll_assumptions3 lepoll_assumptions4 lepoll_assumptions5
  lepoll_assumptions6 lepoll_assumptions7 lepoll_assumptions8
  lepoll_assumptions9 lepoll_assumptions10 lepoll_assumptions11 
  lepoll_assumptions12 lepoll_assumptions13 lepoll_assumptions14
  lepoll_assumptions15 lepoll_assumptions16
  lepoll_assumptions17 lepoll_assumptions18

end (* M_replacement_lepoll *)

end