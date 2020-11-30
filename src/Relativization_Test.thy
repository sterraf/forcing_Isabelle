section\<open>Automatic relativization of terms.\<close>
theory Relativization_Test
  imports Relativization
begin

declare [[ML_print_depth = 50]]

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

relativize_tm "test7(0)" "is_testt7"

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

definition "between" :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o" where
  "between(x, a, b) \<equiv> a \<subseteq> x \<and> x \<subseteq> b"

relativize "between" "is_between"

lemma (in M_trans) "between_ok":
  "\<forall> a b x . M(a) \<and> M(b) \<and> M(c) \<Longrightarrow> between(x, a, b) \<longleftrightarrow> is_between(M, x, a, b)"
  unfolding between_def is_between_def
  using subset_abs
  by simp

definition "covered_by" :: "i \<Rightarrow> i \<Rightarrow> o" where
  "covered_by(a, b) \<equiv> a \<subseteq> b \<and> (\<forall> x . between(x, a, b) \<longrightarrow> x = a \<or> x = b)"

relativize "covered_by" "is_covered_by"

lemma (in M_trans) "covered_by_ok":
  "\<forall> a b . M(a) \<and> M(b) \<Longrightarrow> covered_by(a, b) \<longleftrightarrow> is_covered_by(M, a, b)"
  unfolding covered_by_def is_covered_by_def
  using between_ok
  by auto

definition "min_elem" :: "i \<Rightarrow> i \<Rightarrow> o" where
  "min_elem(u, m) \<equiv> m \<in> u \<and> (\<forall> x . x \<in> u \<longrightarrow> m \<subseteq> x)"

relativize "min_elem" "is_min_elem"

lemma (in M_trans) "min_elem_ok":
  "\<forall> u m . M(u) \<and> M(m) \<Longrightarrow> min_elem(u, m) \<longleftrightarrow> is_min_elem(M, u, m)"
  unfolding min_elem_def is_min_elem_def
  using subset_abs
  by auto

definition "atoms" :: "i \<Rightarrow> i" where
  "atoms(u) \<equiv> { a \<in> u . \<exists> m . min_elem(u, m) \<and> covered_by(m, a) }"

relativize "atoms" "is_atoms"

lemma (in M_trans) "unique_atoms":
  "\<forall> u a b . M(u) \<and> M(a) \<and> M(b) \<Longrightarrow> is_atoms(M, u, a) \<and> is_atoms(M, u, b) \<longrightarrow> a = b"
  unfolding is_atoms_def
  using covered_by_ok min_elem_ok
  by simp

lemma (in M_trans) "atoms_ok":
  "\<forall> u . M(u) \<Longrightarrow> is_atoms(M, u, atoms(u))"
  unfolding atoms_def is_atoms_def
  using covered_by_ok min_elem_ok
  by auto

lemma (in M_trans) "atoms_abs":
  "\<forall> u a . M(u) \<and> M(a) \<Longrightarrow> a = atoms(u) \<longleftrightarrow> is_atoms(M, u, a)"
  using unique_atoms atoms_ok
  by blast

relativize_tm "{ a : u . <0,0> \<in> a } \<inter> { b : u . 0 \<in> b }" "test17"

relativize_tm "{ b . f \<in> x \<rightarrow> y, \<forall> x . \<exists> a . f ` (f ` x) = f ` x \<and>  f ` a = b }" "test18"

relativize_tm "{ a \<rightarrow> a . a \<in> u }" "test19"

relativize_tm "{ a . a \<in> f ` <x,y> }" "test20"

relativize_tm "\<forall> a b . { x \<rightarrow> b . x \<in> a } = { x \<rightarrow> b . x \<in> a }" "test21"

relativize_tm "\<forall> a . {x \<inter> a . x \<in> a} \<subseteq> a" "test22"

relativize_tm "\<forall> a . {y . x \<in> <0,0> , y \<inter> a \<subseteq> x} \<subseteq> a" "test23"

(* collect { a \<in> 0 . a=a} *)
(* rep_fun { a. <a,b>\<in>0 } *)
(* replace { a. a\<in>0, a=a } *)
(*         { b. a\<in>0, b=a\<times>a } *)
(* RepFun { a\<times>a. a\<in>0 } *)

(*
ML\<open>
Local_Theory.target I @{context}
\<close>
*)

definition bla :: "i => o" where
 "bla(x) \<equiv> x = 0"
relativize "bla" "is_bla"

relativize_tm "x = <0,0> \<and> bla(x)" "test24"
relativize_tm "bla(x)" "test25"

relativize_tm functional "x = <0,0>" "test26"
relativize_tm functional "\<forall> x y . x \<subseteq> y \<longrightarrow> 0 \<in> x \<inter> y" "test27"

definition test28 :: "i \<Rightarrow> i \<Rightarrow> i" where
  "test28(x, y) \<equiv> <x \<inter> y, x \<union> y>"
relativize functional "test28" "test28_rel"
relationalize "test28_rel" "is_test28"

definition test29 :: "i \<Rightarrow> i" where
  "test29(x) \<equiv> test28(x,x)"
relativize functional "test29" "test29_rel"
relationalize "test29_rel" "is_test29"

definition test30 :: "i" where
  "test30 \<equiv> 0 \<times> test29(0)"

relativize functional "test30" "test30_rel"
relationalize "test30_rel" "is_test30"

context M_trans
begin
ML\<open>
Local_Theory.target I @{context}
\<close>
end

end