section\<open>Main definitions of the development\<close>

theory Definitions_Main
  imports Forcing_Main

begin

text\<open>This theory gathers the main definitions of the Forcing session.

It might be considered as the bare minimum reading requisite to
trust that our development indeed formalizes the theory of
forcing. This should be mathematically clear since this is the
only known method for obtaining proper extensions of ctms while
preserving the ordinals.

The main theorem of this session and all of its relevant definitions
appear in Section~\ref{sec:def-main-forcing}. The reader trusting
all the libraries in which our development is based, might jump
directly there. But in case one wants to dive deeper, the following
sections treat some basic concepts in the ZF logic
(Section~\ref{sec:def-main-ZF})  and in the
ZF-Constructible library (Section~\ref{sec:def-main-constructible})
on which our definitions are built.
\<close>

declare [[show_question_marks=false]]

subsection\<open>ZF\label{sec:def-main-ZF}\<close>

text\<open>For the basic logic ZF we restrict ourselves to just a few
concepts.\<close>

thm bij_def[unfolded inj_def surj_def]
text\<open>@{thm [display] bij_def[unfolded inj_def surj_def]}\<close>
(*
  bij(A, B) \<equiv> {f \<in> A \<rightarrow> B . \<forall>w\<in>A. \<forall>x\<in>A. f ` w = f ` x \<longrightarrow> w = x}
               \<inter> {f \<in> A \<rightarrow> B . \<forall>y\<in>B. \<exists>x\<in>A. f ` x = y}
*)

thm eqpoll_def
text\<open>@{thm [display] eqpoll_def}\<close>
(*
  A \<approx> B \<equiv> \<exists>f. f \<in> bij(A, B)
*)

thm Transset_def
text\<open>@{thm [display] Transset_def}\<close>
(*
  Transset(i) \<equiv> \<forall>x\<in>i. x \<subseteq> i
*)

thm Ord_def
text\<open>@{thm [display] Ord_def}\<close>
(*
  Ord(i) \<equiv> Transset(i) \<and> (\<forall>x\<in>i. Transset(x))
*)

thm lt_def
text\<open>@{thm [display] lt_def}\<close>
(*
  i < j \<equiv> i \<in> j \<and> Ord(j)
*)

text\<open>The set of natural numbers \<^term>\<open>nat\<close> is defined as a
fixpoint, but here we just write its characterization as the
first limit ordinal.\<close>
thm Limit_nat[unfolded Limit_def] nat_le_Limit[unfolded Limit_def]
text\<open>@{thm [display] Limit_nat[unfolded Limit_def]
 nat_le_Limit[unfolded Limit_def]}\<close>
(*
  Ord(nat) \<and> 0 < nat \<and> (\<forall>y. y < nat \<longrightarrow> succ(y) < nat)
  Ord(i) \<and> 0 < i \<and> (\<forall>y. y < i \<longrightarrow> succ(y) < i) \<Longrightarrow> nat \<le> i
*)

hide_const (open) Order.pred
thm add_0_right add_succ_right pred_0 pred_succ_eq
text\<open>@{thm [display] add_succ_right add_0_right pred_0 pred_succ_eq}\<close>
(*
  m \<in> nat \<Longrightarrow> m #+ 0 = m
  m #+ succ(n) = succ(m #+ n)

  pred(0) = 0
  pred(succ(y)) = y
*)

text\<open>Lists\<close>

thm Nil Cons list.induct
text\<open>@{thm [display] Nil Cons list.induct }\<close>
(*
  [] \<in> list(A)
  a \<in> A \<Longrightarrow> l \<in> list(A) \<Longrightarrow> Cons(a, l) \<in> list(A)
  x \<in> list(A) \<Longrightarrow> P([]) \<Longrightarrow> (\<And>a l. a \<in> A \<Longrightarrow> l \<in> list(A) \<Longrightarrow> P(l) \<Longrightarrow> P(Cons(a, l))) \<Longrightarrow> P(x)
*)
thm length.simps app.simps nth_0 nth_Cons
text\<open>@{thm [display] length.simps app.simps nth_0 nth_Cons}\<close>
(*
  length([]) = 0
  length(Cons(a, l)) = succ(length(l))

  [] @ ys = ys
  Cons(a, l) @ ys = Cons(a, l @ ys)

  nth(0, Cons(a, l)) = a
  n \<in> nat \<Longrightarrow> nth(succ(n), Cons(a, l)) = nth(n, l)
*)

txt\<open>Relative quantifications\<close>

lemma "\<forall>x[M]. P(x) \<equiv> \<forall>x. M(x) \<longrightarrow> P(x)"
      "\<exists>x[M]. P(x) \<equiv> \<exists>x. M(x) \<and> P(x)"
  unfolding rall_def rex_def .

thm setclass_iff
text\<open>@{thm [display] setclass_iff}\<close>
(*
  (##A)(x) \<longleftrightarrow> x \<in> A
*)

subsection\<open>ZF-Constructible\label{sec:def-main-constructible}\<close>

thm big_union_def
text\<open>@{thm [display] big_union_def}\<close>
(*
  big_union(M, A, z) \<equiv> \<forall>x[M]. x \<in> z \<longleftrightarrow> (\<exists>y[M]. y \<in> A \<and> x \<in> y)
*)


thm Union_ax_def
text\<open>@{thm [display] Union_ax_def}\<close>
(*
  Union_ax(M) \<equiv> \<forall>x[M]. \<exists>z[M]. \<forall>xa[M]. xa \<in> z \<longleftrightarrow> (\<exists>y[M]. y \<in> x \<and> xa \<in> y)
*)

thm power_ax_def[unfolded powerset_def subset_def]
text\<open>@{thm [display] power_ax_def[unfolded powerset_def subset_def]}\<close>
(*
  power_ax(M) \<equiv> \<forall>x[M]. \<exists>z[M]. \<forall>xa[M]. xa \<in> z \<longleftrightarrow> (\<forall>xb[M]. xb \<in> xa \<longrightarrow> xb \<in> x)
*)

thm upair_def
text\<open>@{thm [display] upair_def}\<close>
(*
  upair(M, a, b, z) \<equiv> a \<in> z \<and> b \<in> z \<and> (\<forall>x[M]. x \<in> z \<longrightarrow> x = a \<or> x = b)
*)

thm pair_def
text\<open>@{thm [display] pair_def}\<close>
(*
  pair(M, a, b, z) \<equiv> \<exists>x[M]. upair(M, a, a, x) \<and>
                        (\<exists>y[M]. upair(M, a, b, y) \<and> upair(M, x, y, z))
*)

thm successor_def[unfolded is_cons_def union_def]
text\<open>@{thm [display] successor_def[unfolded is_cons_def union_def]}\<close>
(*
  successor(M, a, z) \<equiv> \<exists>x[M]. upair(M, a, a, x) \<and> (\<forall>xa[M]. xa \<in> z \<longleftrightarrow> xa \<in> x \<or> xa \<in> a)
*)

thm upair_ax_def
text\<open>@{thm [display] upair_ax_def}\<close>
(*
  upair_ax(M) \<equiv> \<forall>x[M]. \<forall>y[M]. \<exists>z[M]. upair(M, x, y, z)
*)

thm foundation_ax_def
text\<open>@{thm [display] foundation_ax_def}\<close>
(*
  foundation_ax(M) \<equiv> \<forall>x[M]. (\<exists>y[M]. y \<in> x) \<longrightarrow> (\<exists>y[M]. y \<in> x \<and> \<not> (\<exists>z[M]. z \<in> x \<and> z \<in> y))
*)

thm extensionality_def
text\<open>@{thm [display] extensionality_def}\<close>
(*
  extensionality(M) \<equiv> \<forall>x[M]. \<forall>y[M]. (\<forall>z[M]. z \<in> x \<longleftrightarrow> z \<in> y) \<longrightarrow> x = y
*)

thm separation_def
text\<open>@{thm [display] separation_def}\<close>
(*
  separation(M, P) \<equiv> \<forall>z[M]. \<exists>y[M]. \<forall>x[M]. x \<in> y \<longleftrightarrow> x \<in> z \<and> P(x)
*)

thm univalent_def
text\<open>@{thm [display] univalent_def}\<close>
(*
  univalent(M, A, P) \<equiv> \<forall>x[M]. x \<in> A \<longrightarrow>
                          (\<forall>y[M]. \<forall>z[M]. P(x, y) \<and> P(x, z) \<longrightarrow> y = z)
*)

thm strong_replacement_def
text\<open>@{thm [display] strong_replacement_def}\<close>
(*
  strong_replacement(M, P) \<equiv> \<forall>A[M]. univalent(M, A, P) \<longrightarrow>
       (\<exists>Y[M]. \<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> P(x, b)))
*)

thm empty_def
text\<open>@{thm [display] empty_def}\<close>
(*
  empty(M, z) \<equiv> \<forall>x[M]. x \<notin> z
*)

thm transitive_set_def[unfolded subset_def]
text\<open>@{thm [display] transitive_set_def[unfolded subset_def]}\<close>
(*
  transitive_set(M, a) \<equiv> \<forall>x[M]. x \<in> a \<longrightarrow> (\<forall>xa[M]. xa \<in> x \<longrightarrow> xa \<in> a)
*)


thm ordinal_def
text\<open>@{thm [display] ordinal_def}\<close>
(*
  ordinal(M, a) \<equiv> transitive_set(M, a) \<and> (\<forall>x[M]. x \<in> a \<longrightarrow>
                                              transitive_set(M, x))
*)

thm image_def
text\<open>@{thm [display] image_def}\<close>
(*
  image(M, r, A, z) \<equiv> \<forall>y[M]. y \<in> z \<longleftrightarrow>
                (\<exists>w[M]. w \<in> r \<and> (\<exists>x[M]. x \<in> A \<and> pair(M, x, y, w)))
*)

thm fun_apply_def
text\<open>@{thm [display] fun_apply_def}\<close>
(*
  fun_apply(M, f, x, y) \<equiv> \<exists>xs[M]. \<exists>fxs[M]. upair(M, x, x, xs) \<and>
                       image(M, f, xs, fxs) \<and> big_union(M, fxs, y)
*)

thm is_function_def
text\<open>@{thm [display] is_function_def}\<close>
(*
  is_function(M, r) \<equiv> \<forall>x[M]. \<forall>y[M]. \<forall>y'[M]. \<forall>p[M]. \<forall>p'[M].
       pair(M, x, y, p) \<longrightarrow> pair(M, x, y', p') \<longrightarrow> p \<in> r \<longrightarrow> p' \<in> r \<longrightarrow> y = y'
*)

thm is_relation_def
text\<open>@{thm [display] is_relation_def}\<close>
(*
  is_relation(M, r) \<equiv> \<forall>z[M]. z \<in> r \<longrightarrow> (\<exists>x[M]. \<exists>y[M]. pair(M, x, y, z))
*)

thm is_domain_def
text\<open>@{thm [display] is_domain_def}\<close>
(*
  is_domain(M, r, z) \<equiv> \<forall>x[M]. x \<in> z \<longleftrightarrow>
                        (\<exists>w[M]. w \<in> r \<and> (\<exists>y[M]. pair(M, x, y, w)))
*)

thm typed_function_def
text\<open>@{thm [display] typed_function_def}\<close>
(*
  typed_function(M, A, B, r) \<equiv> is_function(M, r) \<and> is_relation(M, r) \<and>
                                is_domain(M, r, A) \<and>
            (\<forall>u[M]. u \<in> r \<longrightarrow> (\<forall>x[M]. \<forall>y[M]. pair(M, x, y, u) \<longrightarrow> y \<in> B))
*)

thm surjection_def
text\<open>@{thm [display] surjection_def}\<close>
(*
  surjection(M, A, B, f) \<equiv> typed_function(M, A, B, f) \<and> (\<forall>y[M]. y \<in> B \<longrightarrow>
                              (\<exists>x[M]. x \<in> A \<and> fun_apply(M, f, x, y)))
*)

text\<open>Internalized formulas\<close>

thm Member Equal Nand Forall formula.induct
text\<open>@{thm [display] Member Equal Nand Forall formula.induct}\<close>
(*
  x \<in> nat \<Longrightarrow> y \<in> nat \<Longrightarrow> Member(x, y) \<in> formula
  x \<in> nat \<Longrightarrow> y \<in> nat \<Longrightarrow> Equal(x, y) \<in> formula
  p \<in> formula \<Longrightarrow> Forall(p) \<in> formula
  p \<in> formula \<Longrightarrow> q \<in> formula \<Longrightarrow> Nand(p, q) \<in> formula

  x \<in> formula \<Longrightarrow>
  (\<And>x y. x \<in> nat \<Longrightarrow> y \<in> nat \<Longrightarrow> P(Member(x, y))) \<Longrightarrow>
  (\<And>x y. x \<in> nat \<Longrightarrow> y \<in> nat \<Longrightarrow> P(Equal(x, y))) \<Longrightarrow>
  (\<And>p q. p \<in> formula \<Longrightarrow> P(p) \<Longrightarrow> q \<in> formula \<Longrightarrow> P(q) \<Longrightarrow> P(Nand(p, q))) \<Longrightarrow>
  (\<And>p. p \<in> formula \<Longrightarrow> P(p) \<Longrightarrow> P(Forall(p))) \<Longrightarrow> P(x)
*)

thm arity.simps
text\<open>@{thm [display] arity.simps}\<close>
(*
  arity(Member(x, y)) = succ(x) \<union> succ(y)
  arity(Equal(x, y)) = succ(x) \<union> succ(y)
  arity(Nand(p, q)) = arity(p) \<union> arity(q)
  arity(Forall(p)) = pred(arity(p))
*)

thm mem_iff_sats equal_iff_sats sats_Nand_iff sats_Forall_iff
text\<open>@{thm [display] mem_iff_sats equal_iff_sats sats_Nand_iff sats_Forall_iff}\<close>
(*
  nth(i, env) = x \<Longrightarrow> nth(j, env) = y \<Longrightarrow> env \<in> list(A) \<Longrightarrow> x \<in> y \<longleftrightarrow> A, env \<Turnstile> Member(i, j)
  nth(i, env) = x \<Longrightarrow> nth(j, env) = y \<Longrightarrow> env \<in> list(A) \<Longrightarrow> x = y \<longleftrightarrow> A, env \<Turnstile> Equal(i, j)
  env \<in> list(A) \<Longrightarrow> A, env \<Turnstile> Nand(p, q) \<longleftrightarrow> \<not> (A, env \<Turnstile> p \<and> A, env \<Turnstile> q)
  env \<in> list(A) \<Longrightarrow> A, env \<Turnstile> Forall(p) \<longleftrightarrow> (\<forall>x\<in>A. A, Cons(x, env) \<Turnstile> p
*)

subsection\<open>Forcing \label{sec:def-main-forcing}\<close>

thm infinity_ax_def
text\<open>@{thm [display] infinity_ax_def}\<close>
(*
  infinity_ax(M) \<equiv> \<exists>I[M]. (\<exists>z[M]. empty(M, z) \<and> z \<in> I) \<and> (\<forall>y[M]. y \<in> I \<longrightarrow>
                        (\<exists>sy[M]. successor(M, y, sy) \<and> sy \<in> I))
*)

thm choice_ax_def
text\<open>@{thm [display] choice_ax_def}\<close>
(*
  choice_ax(M) \<equiv> \<forall>x[M]. \<exists>a[M]. \<exists>f[M]. ordinal(M, a) \<and> surjection(M, a, x, f)
*)

thm ZF_union_fm_iff_sats ZF_power_fm_iff_sats ZF_pairing_fm_iff_sats
  ZF_foundation_fm_iff_sats ZF_extensionality_fm_iff_sats
  ZF_infinity_fm_iff_sats sats_ZF_separation_fm_iff
  sats_ZF_replacement_fm_iff ZF_choice_fm_iff_sats
text\<open>@{thm [display] ZF_union_fm_iff_sats ZF_power_fm_iff_sats
  ZF_pairing_fm_iff_sats
  ZF_foundation_fm_iff_sats ZF_extensionality_fm_iff_sats
  ZF_infinity_fm_iff_sats sats_ZF_separation_fm_iff
  sats_ZF_replacement_fm_iff ZF_choice_fm_iff_sats}\<close>
(*
  Union_ax(##A) \<longleftrightarrow> A, [] \<Turnstile> ZF_union_fm

  power_ax(##A) \<longleftrightarrow> A, [] \<Turnstile> ZF_power_fm

  upair_ax(##A) \<longleftrightarrow> A, [] \<Turnstile> ZF_pairing_fm

  foundation_ax(##A) \<longleftrightarrow> A, [] \<Turnstile> ZF_foundation_fm

  extensionality(##A) \<longleftrightarrow> A, [] \<Turnstile> ZF_extensionality_fm

  infinity_ax(##A) \<longleftrightarrow> A, [] \<Turnstile> ZF_infinity_fm

  \<phi> \<in> formula \<Longrightarrow>
    M, [] \<Turnstile> ZF_separation_fm(\<phi>) \<longleftrightarrow>
    (\<forall>env\<in>list(M). arity(\<phi>) \<le> 1 #+ length(env) \<longrightarrow> separation(##M, \<lambda>x. M, [x] @ env \<Turnstile> \<phi>))

  \<phi> \<in> formula \<Longrightarrow>
    M, [] \<Turnstile> ZF_replacement_fm(\<phi>) \<longleftrightarrow>
    (\<forall>env\<in>list(M). arity(\<phi>) \<le> 2 #+ length(env) \<longrightarrow> strong_replacement(##M, \<lambda>x y. M, [x, y] @ env \<Turnstile> \<phi>))

  choice_ax(##A) \<longleftrightarrow> A, [] \<Turnstile> ZF_choice_fm
*)

thm ZF_fin_def ZF_inf_def ZF_def ZFC_fin_def ZFC_def
text\<open>@{thm [display] ZF_fin_def ZF_inf_def ZF_def ZFC_fin_def
  ZFC_def}\<close>
(*
  ZF_fin \<equiv> {ZF_extensionality_fm, ZF_foundation_fm, ZF_pairing_fm,
             ZF_union_fm, ZF_infinity_fm, ZF_power_fm}
  ZF_inf \<equiv> {ZF_separation_fm(p) . p \<in> formula} \<union> {ZF_replacement_fm(p) . p \<in> formula}
  ZF \<equiv> ZF_inf \<union> ZF_fin
  ZFC_fin \<equiv> ZF_fin \<union> {ZF_choice_fm}
  ZFC \<equiv> ZF_inf \<union> ZFC_fin
*)

thm satT_def
text\<open>@{thm [display] satT_def}\<close>
(*
  A \<Turnstile> \<Phi>  \<equiv>  \<forall>\<phi>\<in>\<Phi>. A, [] \<Turnstile> \<phi>
*)

thm extensions_of_ctms
text\<open>@{thm [display] extensions_of_ctms}\<close>
(*
  M \<approx> nat \<Longrightarrow>
  Transset(M) \<Longrightarrow>
  M \<Turnstile> ZF \<Longrightarrow>
  \<exists>N. M \<subseteq> N \<and>
      N \<approx> nat \<and>
      Transset(N) \<and> N \<Turnstile> ZF \<and> M \<noteq> N \<and> (\<forall>\<alpha>. Ord(\<alpha>) \<longrightarrow> \<alpha> \<in> M \<longleftrightarrow> \<alpha> \<in> N)
        \<and> (M, [] \<Turnstile> ZF_choice_fm \<longrightarrow> N \<Turnstile> ZFC)
*)

end