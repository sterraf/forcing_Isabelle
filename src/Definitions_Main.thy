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

thm Limit_nat[unfolded Limit_def]
text\<open>@{thm [display] Limit_nat[unfolded Limit_def]}\<close>
(*
Ord(nat) \<and> 0 < nat \<and> (\<forall>y. y < nat \<longrightarrow> succ(y) < nat)
*)

thm nat_le_Limit[unfolded Limit_def]
text\<open>@{thm [display] nat_le_Limit[unfolded Limit_def]}\<close>
(*
Ord(nat) \<and> 0 < nat \<and> (\<forall>y. y < nat \<longrightarrow> succ(y) < nat)
*)

txt\<open>The relative quantifications, \<^term>\<open>\<forall>x[M]. P(x)\<close> and
\<^term>\<open>\<exists>x[M]. P(x)\<close> correspond to the ZF terms \<^term>\<open>rall\<close>
and \<^term>\<open>rex\<close>, respectively:\<close>

thm rall_def
text\<open>@{thm [display] rall_def}\<close>
(*
rall(M, P) \<equiv> \<forall>x. M(x) \<longrightarrow> P(x)
*)

thm rex_def
text\<open>@{thm [display] rex_def}\<close>
(*
rex(M, P) \<equiv> \<exists>x. M(x) \<and> P(x)
*)

subsection\<open>ZF-Constructible\label{sec:def-main-constructible}\<close>

thm Union_ax_def[unfolded big_union_def]
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

thm successor_def[unfolded is_cons_def union_def]
text\<open>@{thm [display] successor_def}\<close>
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

thm surjection_def
text\<open>@{thm [display] surjection_def}\<close>
(*
surjection(M, A, B, f) \<equiv> typed_function(M, A, B, f) \<and> (\<forall>y[M]. y \<in> B \<longrightarrow>
                            (\<exists>x[M]. x \<in> A \<and> fun_apply(M, f, x, y)))
*)
txt\<open>The definitions of \<^term>\<open>typed_function\<close> and
 \<^term>\<open>fun_apply\<close> rely on the previously defined terms
\<^term>\<open>is_function\<close>, \<^term>\<open>is_relation\<close>, \<^term>\<open>is_domain\<close>,
\<^term>\<open>pair\<close>, \<^term>\<open>image\<close>, and \<^term>\<open>union\<close>, which use in
turn use concepts presented here.\<close>


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

thm ZF_fin_def
text\<open>@{thm [display] ZF_fin_def}\<close>
(*
ZF_fin \<equiv> {ZF_extensionality_fm, ZF_foundation_fm, ZF_pairing_fm,
           ZF_union_fm, ZF_infinity_fm, ZF_power_fm}
*)

thm ZF_inf_def
text\<open>@{thm [display] ZF_inf_def}\<close>
(*
ZF_inf \<equiv> {ZF_separation_fm(p) . p \<in> formula} \<union> {ZF_replacement_fm(p) . p \<in> formula}
*)

thm ZF_def
text\<open>@{thm [display] ZF_def}\<close>
(*
ZF \<equiv> ZF_inf \<union> ZF_fin
*)

thm ZFC_fin_def
text\<open>@{thm [display] ZFC_fin_def}\<close>
(*
"ZFC_fin \<equiv> ZF_fin \<union> {ZF_choice_fm}"
*)

thm ZFC_def
text\<open>@{thm [display] ZFC_def}\<close>
(*
"ZFC \<equiv> ZF_inf \<union> ZFC_fin"
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