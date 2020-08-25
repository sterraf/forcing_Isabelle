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

relativize_tm "<0,a>" "test_6"

(* Specific context should not be required *)
(* context M_trans
begin *)

definition "test7" :: "i \<Rightarrow> o" where
  "test7(a) \<equiv> a \<in> a"

relativize "test7" "is_test7"

definition "test8" :: "o" where
  "test8 \<equiv> \<forall> a . test7(a)"

relativize "test8" "is_test8"

(* end *) (* M_trans *)

end