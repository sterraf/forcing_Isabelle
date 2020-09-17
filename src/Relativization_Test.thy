section\<open>Automatic relativization of terms.\<close>
theory Relativization_Test
  imports Relativization
begin

definition test1 :: "i \<Rightarrow> o" where
  "test1(a) \<equiv> \<forall> x . x \<subseteq> Pi(x, (\<lambda> y . x \<inter> y))"

(* relativize "test1" "is_test1" *) (* this should always fail *)

definition test2 :: "i \<Rightarrow> o" where
  "test2(a) \<equiv> \<forall> x . x \<subseteq> x \<rightarrow> x \<inter> x"

relativize "test2" "is_test2"

lemma test2_ok:
  "(\<forall>x[N]. \<exists>b[N]. \<exists>c[N]. subset(N, x, c) \<and> is_funspace(N, x, b, c) \<and> inter(N, x, x, b)) \<longleftrightarrow> is_test2(N)"
  unfolding is_test2_def
  by simp

definition test3 :: "i \<Rightarrow> i" where
  "test3(a) \<equiv> (a \<inter> a) \<union> (a \<inter> a)"

relativize "test3" "is_test3"

definition test4 :: "i \<Rightarrow> i \<Rightarrow> o" where
  "test4(a,b) \<equiv> a = (a \<inter> b) \<union> (a \<inter> b) \<and> a = (a \<inter> b)"

relativize "test4" "is_test4"

lemma (in M_trans) test4_ok:
  assumes "M(a)" "M(b)"
  shows "(\<exists>c[M]. inter(M, a, b, c) \<and> (\<exists>d[M]. a = d \<and> union(M, c, c, d) \<and> a = c)) \<longleftrightarrow> is_test4(M,a,b)"
  using assms inter_abs
  unfolding is_test4_def
  by auto

definition test4_closed :: "o" where
  "test4_closed \<equiv> \<forall> a b . a = (a \<inter> b) \<union> (a \<inter> b) \<and> a = (a \<inter> b)"

relativize "test4_closed" "is_test4_closed"

lemma (in M_trans) test4_closed_ok:
  "(\<forall> a[M]. \<forall> b[M]. \<exists>c[M]. inter(M, a, b, c) \<and> (\<exists>d[M]. a = d \<and> union(M, c, c, d) \<and> a = c)) \<longleftrightarrow> is_test4_closed(M)"
  using inter_abs
  unfolding is_test4_closed_def
  by auto

definition test5 :: "o" where
  "test5 \<equiv> \<forall> a b . a = a \<inter> b"

relativize "test5" "is_test5"

relativize_tm "<0,a>" "test6"

(* Specific context should not be required *)
context M_trans
begin

definition "test7" :: "i \<Rightarrow> o" where
  "test7(a) \<equiv> a \<in> a"

relativize "test7" "is_test7"

definition "test8" :: "o" where
  "test8 \<equiv> \<forall> a . test7(a)"

relativize "test8" "is_test8"

end (* M_trans *)

definition "test9" :: "o" where
  "test9 \<equiv> \<forall> a . a = a \<inter> a \<and> (\<exists> b . a = a \<inter> a \<or> a = b)"

relativize "test9" "is_test9"

definition "test10" :: "o" where
  "test10 \<equiv> \<forall> a b c . a = b \<inter> c \<longrightarrow> (\<forall> b d . d \<subseteq> a \<rightarrow> b \<inter> c)"

relativize "test10" "is_test10"

definition "test11" :: "o" where
  "test11 \<equiv> \<forall> a b c . a = (b \<inter> c) \<longrightarrow> (\<forall> d . a \<subseteq> d \<rightarrow> (b \<inter> c))"

relativize "test11" "is_test11"

lemma (in M_basic) test11_ok:
  "(\<forall>a[M]. \<forall>b[M]. \<forall>c[M]. \<exists>e[M]. (a = e \<longrightarrow> (\<forall>d[M]. \<exists>f[M]. subset(M, a, f) \<and> is_funspace(M, d, e, f))) \<and> inter(M, b, c, e)) \<longleftrightarrow> is_test11(M)"
  unfolding is_test11_def
  using inter_abs Int_closed
  by simp

definition "test12" :: "o" where
  "test12 \<equiv> \<forall> a b c . (\<forall> d . a \<subseteq> d \<rightarrow> (b \<inter> c)) \<longrightarrow> a = b \<inter> c"

relativize "test12" "is_test12"

relativize_tm "\<forall> b . b = a \<rightarrow> a \<inter> b" "test13"

relativize_tm "\<forall> a . a = 0" "test14"

lemma (in M_trans) test14_ok:
  "(\<forall>a[M]. \<exists>b[M]. a = b \<and> empty(M,b)) \<longleftrightarrow> test14(M)"
  unfolding test14_def
  using empty_abs nonempty
  by blast

relativize_tm "\<forall> a . 0 \<subseteq> a" "test15"

relativize_tm "\<forall> a . a = <a,0>" "test16"

(* collect { a \<in> 0 . a=a} *)
(* rep_fun { a. <a,b>\<in>0 } *)
(* replace { a. a\<in>0, a=a } *)
(*         { b. a\<in>0, b=a\<times>a } *)
(* RepFun { a\<times>a. a\<in>0 } *)

end