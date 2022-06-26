
theory Roadmap
  imports
    Independence_CH.Definitions_Main
begin

section\<open>Introduction\<close>
text\<open>\<^theory>\<open>Pure\<close>\<close>

ML\<open>
let 
  val axs = Theory.all_axioms_of @{theory}
  val defs = (map #2 o Defs.dest_constdefs []) (Theory.defs_of @{theory})
  fun notInts ax = List.exists (fn ax' => ax' = (#1 ax)) defs
  val onlyAxs = filter_out notInts axs
in
 map (fn ax => (writeln o String.concat) [#1 ax,": ",Syntax.string_of_term @{context} ( #2 ax)]) onlyAxs
end
\<close>
text\<open>We present in this theory a high-level presentation of the
main proofs; it is intended to help navigating the whole development
by pointing out explicitly the main lemmas. It can be seen as a
complement for
\<^theory>\<open>Independence_CH.Definitions_Main\<close>, where we
present the definitions and axioms one should trust to get confidence
that our mechanization is faithful to the mathematics. We refer to
\cite{2007arXiv0712.1320C} for a more informed introduction to
forcing.

We want to show that the Continuum Hypothesis is independent of the
axioms of set theory: we will show that $\mathit{Con}(\ZFC)$ implies
$\ZFC \vdash \neg \CH$ and $\mathit{Con}(\ZFC)$ implies $\ZFC \vdash
CH$.

The assumption that $\ZFC$ is consistent amounts to assume that there
is a model, say $M$, of $\ZFC$. To refute $\ZFC \vdash \CH$ it is
enough to construct another model $M'$ (to be precise $M' \models
\ZFC$) such that $M' \models \neg \CH$. Dually, we will construct yet
another model $M''$ that validates $\CH$ to refute $\ZFC \vdash
\neg\CH$.

Forcing is \textbf{the} tool for constructing new models from
a given \emph{ground} model.\<close>

subsection\<open>Relative Consistency of the negation of CH\<close>

context add_generic4
begin

text\<open>Let us call $M[G]$ the extended model. To prove $M[G] \models
\neg \CH$ we show @{thm
[display=false,names_short=true,names_unique=false]
Aleph2_extension_le_continuum_rel}. Notice that this is an absolute
affirmation about the relative concepts. That result is a direct
consequence of having a relative injection @{thm
[display=false,names_short=true,names_unique=false]
h_G_inj_Aleph_rel2_reals} defined by currying $\bigcup G$.\<close>

text\<open>$G$ is a filter on the poset \<^term>\<open>Fn(\<omega>, \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>, 2)\<close> of
finite partial functions from \<^term>\<open>\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>\<close> to \<^term>\<open>2\<close>.
Since $G$ is a filter we know that $\bigcup G$ is functional. $G$ is
generic, which means that it intersects any dense subset of
\<^term>\<open>Add\<close>. We use twice the genericity of $G$: first to deduce
that $\bigcup G$ is defined for any \<^term>\<open>t \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>\<close>, then to
deduce that $h_G$ is injective.

It is easy to see that \<^term>\<open>{q \<in> Add . t \<in> domain(q)}\<close> is dense
(basically, take $q$ in that set, if \<^term>\<open>t\<in>domain(q)\<close> we are done;
if not, consider \<^term>\<open>cons(q,\<langle>t,1\<rangle>) \<in> Add\<close> and it extends $q$).
This proves that $\bigcup G$ is defined for any \<^term>\<open>t\<in>Add\<close>.

Now we turn to the injectivity of $h_G$; assume \<^term>\<open>w\<noteq>x\<close> for
\<^term>\<open>{w,x} \<subseteq> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>\<close>. Consider \<^term>\<open>I(w,x) = {q \<in> Add . \<exists>n\<in>\<omega>.
q`\<langle>w,n\<rangle>\<noteq>q`\<langle>x,n\<rangle>}\<close> and take \<^term>\<open>q\<in>I(w,x)\<close>; since $q$ is finite,
\<^term>\<open>q`\<langle>w,n\<rangle>\<close> and \<^term>\<open>q`\<langle>w,n\<rangle>\<close> should be undefined for some
$n$. Then one can extend $q$ to
\<^term>\<open>cons(cons(q,\<langle>\<langle>w,n\<rangle>,0\<rangle>),\<langle>\<langle>x,n\<rangle>,1\<rangle>)\<close>.\<close>

text\<open>We have an injection in \<^term>\<open>M[G]\<close> from  \<^term>\<open>\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>\<close> to
\<^term>\<open>2\<close>, but we want an injection from \<^term>\<open>\<aleph>\<^bsub>2\<^esub>\<^bsup>M[G]\<^esup> \<times> \<omega>\<close> to
\<^term>\<open>2\<close>; it can be proved that \<^term>\<open>\<aleph>\<^bsub>n\<^esub>\<^bsup>M[G]\<^esup> = \<aleph>\<^bsub>n\<^esub>\<^bsup>M\<^esup>\<close> for 
\<^term>\<open>n\<in>\<omega>\<close>. Here we resort to the result of ccc forcing.\<close>

text\<open>Now we should explain what is $G$, why does it exist, and
prove that it is in \<^term>\<open>M[G]\<close>; by the way, what is $M[G]$?\<close>

text\<open>We said that $G$ is a filter on the poset \<^term>\<open>Add=Fn(\<omega>,
\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>, 2)\<close>. First, let us note that \<^term>\<open>Add \<in> M\<close>; our proof
consists in showing the absoluteness of the space of partial finite
functions and closure of \<^term>\<open>Fn\<^bsup>M\<^esup>(\<kappa>,I,J)\<close>. Since $M$ is
countable, we can get a generic filter using @{thm [source]
generic_filter_existence}.\<^footnote>\<open>Let us remark that in our current locale
\<^locale>\<open>add_generic4\<close> we assume that $G$ is a generic filter. Only
in our top-level result we use the lemma of existence of generic
filters.\<close> To prove \<^term>\<open>G \<in> M[G]\<close> one must provide a \<^emph>\<open>name\<close> for
\<^term>\<open>G\<close>; if \<^term>\<open>G \<in> M\<close>, then its canonical name is \<^term>\<open>check(G)\<close>.
In general, one can prove that \<^term>\<open>G_dot = {\<langle>check(p),p\<rangle> . p\<in>P}\<close>
is a name for \<^term>\<open>G\<close>.\<close>

end

context forcing_data1
begin
subsection\<open>The model \<^term>\<open>M[G]\<close>\<close>


text\<open>The new model \<^term>\<open>M[G]\<close> is defined as the image of the
\<^term>\<open>val(P,G)\<close> function on \<^term>\<open>M\<close>: \<^term>\<open>M[G] =
{val(P,G,\<tau>) . \<tau> \<in> M}\<close>. Notice that we are in a more general context;
the poset \<^term>\<open>Add\<close> is one example (the suitable poset to satisfy
\<^term>\<open>\<not> CH\<close>). By definition, if \<^term>\<open>x\<in>M[G]\<close>, then there exists
some \<^term>\<open>\<tau>\<in>M\<close> such that \<^term>\<open>x=val(P,G,\<tau>)\<close>; one says that
\<^term>\<open>\<tau>\<close> is the name of \<^term>\<open>x\<close>.\<close>

text\<open>It should be clear that to prove that some set \<^term>\<open>X\<close> is in
\<^term>\<open>M[G]\<close> one has to propose a name, say \<^term>\<open>\<tau>\<close> and prove
\<^term>\<open>X = val(P,G,\<tau>)\<close>. \<^term>\<open>val\<close> is defined by recursion:\<close>

lemma def_val' : "val(P,G,x) = {val(P,G,t) . t \<in> x-``(P\<inter>G)}"
  using def_val[of G x] by auto

text\<open>Every element of $M$ has a canonical name given by 
@{thm
[display=false,names_short=true,names_unique=false] def_check};
therefore we have \<^term>\<open>M\<subseteq>M[G]\<close>.\<close>

end

context G_generic1 
begin 

text\<open>Next we have to show that \<^term>\<open>M[G]\<close> is a model of $\ZFC$. It
is straightforward to show the satisfaction of some of the axioms; for
instance, infinity is direct from the inclusion of models.\<close>

lemma infinity_in_MG : "infinity_ax(##M[G])"
proof -
  have "\<omega>\<in>M[G]" 
    using M_subset_MG one_in_G generic nat_in_M by auto
  moreover from this 
  have "succ(y) \<in> \<omega> \<inter> M[G]" if "y \<in> \<omega>" for y
    using that transitivity_MG by blast
  ultimately
  show ?thesis
    using transitivity_MG[of 0 \<omega>]
    unfolding infinity_ax_def
    by auto
qed

end

end