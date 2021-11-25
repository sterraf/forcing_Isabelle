theory Separation_Instances
  imports
    Discipline_Function
    Forcing_Data
    FiniteFun_Relative
    Cardinal_Relative
    Replacement_Lepoll
begin

subsection\<open>More Instances of Separation\<close>
text\<open>The following instances are mostly the same repetitive task; and we just
copied and pasted, tweaking some lemmas if needed (for example, we might have
needed to use some closedness results).
\<close>

(* FIXME: move these declarations and lemmas where they belong.*)
declare Inl_iff_sats [iff_sats]
declare Inr_iff_sats [iff_sats]
arity_theorem for "Inl_fm"
arity_theorem for "Inr_fm"

arity_theorem for "injection_fm"
arity_theorem for "surjection_fm"
arity_theorem for "bijection_fm"
arity_theorem for "order_isomorphism_fm"
arity_theorem for "pred_set_fm"

(* FIXME: do we need this? does this exists somewhere? *)
lemma iff_sym : "P(x,a) \<longleftrightarrow> a = f(x) \<Longrightarrow> P(x,a) \<longleftrightarrow> f(x) = a"
  by auto


lemma subset_iff_sats [iff_sats]:
      "[| nth(i,env) = x; nth(k,env) = z;
          i \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> subset(##A, x, z) \<longleftrightarrow> sats(A, subset_fm(i,k), env)"
  unfolding subset_def subset_fm_def
  by simp


definition radd_body :: "[i,i,i] \<Rightarrow> o" where
  "radd_body(R,S) \<equiv> \<lambda>z. (\<exists>x y. z = \<langle>Inl(x), Inr(y)\<rangle>) \<or>
                  (\<exists>x' x. z = \<langle>Inl(x'), Inl(x)\<rangle> \<and> \<langle>x', x\<rangle> \<in> R) \<or>
                  (\<exists>y' y. z = \<langle>Inr(y'), Inr(y)\<rangle> \<and> \<langle>y', y\<rangle> \<in> S)"

relativize functional "radd_body" "radd_body_rel"
relationalize "radd_body_rel" "is_radd_body"

synthesize "is_radd_body" from_definition
arity_theorem for "is_radd_body_fm"

lemma (in M_ZF_trans) separation_is_radd_body:
 "(##M)(r) \<Longrightarrow> (##M)(A) \<Longrightarrow> separation(##M, is_radd_body(##M,A,r))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x,A,r] \<Turnstile> is_radd_body_fm(1,2,0)",THEN iffD1])
   apply(rule_tac is_radd_body_iff_sats[where env="[_,A,r]",symmetric])
  apply(simp_all)
  apply(rule_tac separation_ax[where env="[A,r]",simplified])
    apply(simp_all add:arity_is_radd_body_fm ord_simp_union is_radd_body_fm_type)
  done

lemma (in M_ZF_trans) radd_body_abs:
  assumes "(##M)(R)" "(##M)(S)" "(##M)(x)"
  shows "is_radd_body(##M,R,S,x) \<longleftrightarrow> radd_body(R,S,x)"
  using assms pair_in_M_iff Inl_in_M_iff Inr_in_M_iff
  unfolding radd_body_def is_radd_body_def
  by (auto)

lemma (in M_ZF_trans) separation_radd_body:
 "(##M)(R) \<Longrightarrow> (##M)(S) \<Longrightarrow> separation
        (##M, \<lambda>z. (\<exists>x y. z = \<langle>Inl(x), Inr(y)\<rangle>) \<or>
                  (\<exists>x' x. z = \<langle>Inl(x'), Inl(x)\<rangle> \<and> \<langle>x', x\<rangle> \<in> R) \<or>
                  (\<exists>y' y. z = \<langle>Inr(y'), Inr(y)\<rangle> \<and> \<langle>y', y\<rangle> \<in> S))"
  using separation_is_radd_body radd_body_abs
  unfolding radd_body_def
  by (rule_tac separation_cong[
        where P="is_radd_body(##M,R,S)",THEN iffD1])


definition well_ord_body :: "[i\<Rightarrow>o,i,i,i,i] \<Rightarrow> o" where
  "well_ord_body(N,A,f,r,x) \<equiv> x \<in> A \<longrightarrow> (\<exists>y[N]. \<exists>p[N]. is_apply(N, f, x, y) \<and> pair(N, y, x, p) \<and> p \<in> r)"

synthesize "well_ord_body" from_definition
arity_theorem for "well_ord_body_fm"

lemma (in M_ZF_trans) separation_well_ord_body:
 "(##M)(f) \<Longrightarrow> (##M)(r) \<Longrightarrow> (##M)(A) \<Longrightarrow> separation(##M, well_ord_body(##M,A,f,r))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x,A,f,r] \<Turnstile> well_ord_body_fm(1,2,3,0)",THEN iffD1])
   apply(rule_tac well_ord_body_iff_sats[where env="[_,A,f,r]",symmetric])
  apply(simp_all)
  apply(rule_tac separation_ax[where env="[A,f,r]",simplified])
    apply(simp_all add:arity_well_ord_body_fm ord_simp_union well_ord_body_fm_type)
  done

lemma (in M_ZF_trans) separation_well_ord:
 "(##M)(f) \<Longrightarrow> (##M)(r) \<Longrightarrow> (##M)(A) \<Longrightarrow> separation
        (##M, \<lambda>x. x \<in> A \<longrightarrow> (\<exists>y[##M]. \<exists>p[##M]. is_apply(##M, f, x, y) \<and> pair(##M, y, x, p) \<and> p \<in> r))"
  using separation_well_ord_body well_ord_body_def by simp

definition is_obase_body :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_obase_body(N,A,r,x) \<equiv> x \<in> A \<longrightarrow>
                  \<not> (\<exists>y[N].
                         \<exists>g[N].
                            ordinal(N, y) \<and>
                            (\<exists>my[N].
                                \<exists>pxr[N].
                                   membership(N, y, my) \<and>
                                   pred_set(N, A, x, r, pxr) \<and>
                                   order_isomorphism(N, pxr, r, y, my, g)))"

synthesize "is_obase_body" from_definition
arity_theorem for "is_obase_body_fm"

lemma (in M_ZF_trans) separation_is_obase_body:
 "(##M)(r) \<Longrightarrow> (##M)(A) \<Longrightarrow> separation(##M, is_obase_body(##M,A,r))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x,A,r] \<Turnstile> is_obase_body_fm(1,2,0)",THEN iffD1])
   apply(rule_tac is_obase_body_iff_sats[where env="[_,A,r]",symmetric])
  apply(simp_all)
  apply(rule_tac separation_ax[where env="[A,r]",simplified])
    apply(simp_all add:arity_is_obase_body_fm ord_simp_union is_obase_body_fm_type)
  done

lemma (in M_ZF_trans) separation_is_obase:
 "(##M)(f) \<Longrightarrow> (##M)(r) \<Longrightarrow> (##M)(A) \<Longrightarrow> separation
        (##M, \<lambda>x. x \<in> A \<longrightarrow>
                  \<not> (\<exists>y[##M].
                         \<exists>g[##M].
                            ordinal(##M, y) \<and>
                            (\<exists>my[##M].
                                \<exists>pxr[##M].
                                   membership(##M, y, my) \<and>
                                   pred_set(##M, A, x, r, pxr) \<and>
                                   order_isomorphism(##M, pxr, r, y, my, g))))"
  using separation_is_obase_body is_obase_body_def by simp

definition is_obase_equals :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_obase_equals(N,A,r,a) \<equiv> \<exists>x[N].
                     \<exists>g[N].
                        \<exists>mx[N].
                           \<exists>par[N].
                              ordinal(N, x) \<and>
                              membership(N, x, mx) \<and>
                              pred_set(N, A, a, r, par) \<and> order_isomorphism(N, par, r, x, mx, g)"

synthesize "is_obase_equals" from_definition
arity_theorem for "is_obase_equals_fm"

lemma (in M_ZF_trans) separation_obase_equals_aux:
 "(##M)(r) \<Longrightarrow> (##M)(A) \<Longrightarrow> separation(##M, is_obase_equals(##M,A,r))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x,A,r] \<Turnstile> is_obase_equals_fm(1,2,0)",THEN iffD1])
   apply(rule_tac is_obase_equals_iff_sats[where env="[_,A,r]",symmetric])
  apply(simp_all)
  apply(rule_tac separation_ax[where env="[A,r]",simplified])
    apply(simp_all add:arity_is_obase_equals_fm ord_simp_union is_obase_equals_fm_type)
  done

lemma (in M_ZF_trans) separation_obase_equals:
 "(##M)(f) \<Longrightarrow> (##M)(r) \<Longrightarrow> (##M)(A) \<Longrightarrow> separation
        (##M, \<lambda>a. \<exists>x[##M].
                     \<exists>g[##M].
                        \<exists>mx[##M].
                           \<exists>par[##M].
                              ordinal(##M, x) \<and>
                              membership(##M, x, mx) \<and>
                              pred_set(##M, A, a, r, par) \<and> order_isomorphism(##M, par, r, x, mx, g))"
  using separation_obase_equals_aux is_obase_equals_def by (simp)


definition id_body :: "[i,i] \<Rightarrow> o" where
  "id_body(A) \<equiv> \<lambda>z. \<exists>x\<in>A. z = \<langle>x, x\<rangle>"
relativize "id_body" "is_id_body"
synthesize "is_id_body" from_definition assuming "nonempty"
arity_theorem for "is_id_body_fm"

lemma (in M_ZF_trans) separation_is_id_body:
 "(##M)(A) \<Longrightarrow> separation(##M, is_id_body(##M,A))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x,A] \<Turnstile> is_id_body_fm(1,0)",THEN iffD1])
   apply(rule_tac is_id_body_iff_sats[where env="[_,A]",symmetric])
  apply(simp_all add:zero_in_M)
  apply(rule_tac separation_ax[where env="[A]",simplified])
    apply(simp_all add:arity_is_id_body_fm ord_simp_union is_id_body_fm_type)
  done

lemma (in M_ZF_trans) id_body_abs:
  assumes "(##M)(A)" "(##M)(x)"
  shows "is_id_body(##M,A,x) \<longleftrightarrow> id_body(A,x)"
  using assms zero_in_M pair_in_M_iff unfolding id_body_def is_id_body_def
  by auto

lemma (in M_ZF_trans) separation_id_body:
 "(##M)(A) \<Longrightarrow> separation
        (##M, \<lambda>z. \<exists>x\<in>A. z = \<langle>x, x\<rangle>)"
  using id_body_abs separation_is_id_body
  unfolding id_body_def
  by (rule_tac separation_cong[where P="is_id_body(##M,A)",THEN iffD1])

definition rvimage_body :: "[i,i,i] \<Rightarrow> o" where
  "rvimage_body(f,r) \<equiv> \<lambda>z. \<exists>x y. z = \<langle>x, y\<rangle> \<and> \<langle>f ` x, f ` y\<rangle> \<in> r"

relativize functional "rvimage_body" "rvimage_body_rel"
relationalize "rvimage_body_rel" "is_rvimage_body"

synthesize "is_rvimage_body" from_definition
arity_theorem for "is_rvimage_body_fm"

lemma (in M_ZF_trans) separation_is_rvimage_body:
 "(##M)(f) \<Longrightarrow> (##M)(r) \<Longrightarrow> separation(##M, is_rvimage_body(##M,f,r))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x,f,r] \<Turnstile> is_rvimage_body_fm(1,2,0)",THEN iffD1])
   apply(rule_tac is_rvimage_body_iff_sats[where env="[_,f,r]",symmetric])
  apply(simp_all)
  apply(rule_tac separation_ax[where env="[f,r]",simplified])
    apply(simp_all add:arity_is_rvimage_body_fm ord_simp_union is_rvimage_body_fm_type)
  done

lemma (in M_ZF_trans) rvimage_body_abs:
  assumes "(##M)(R)" "(##M)(S)" "(##M)(x)"
  shows "is_rvimage_body(##M,R,S,x) \<longleftrightarrow> rvimage_body(R,S,x)"
  using assms pair_in_M_iff apply_closed
  unfolding rvimage_body_def is_rvimage_body_def
  by (auto)

lemma (in M_ZF_trans) separation_rvimage_body:
 "(##M)(f) \<Longrightarrow> (##M)(r) \<Longrightarrow> separation
        (##M, \<lambda>z. \<exists>x y. z = \<langle>x, y\<rangle> \<and> \<langle>f ` x, f ` y\<rangle> \<in> r)"
  using separation_is_rvimage_body rvimage_body_abs
  unfolding rvimage_body_def
  by (rule_tac separation_cong[
        where P="is_rvimage_body(##M,f,r)",THEN iffD1])

(* rmult_separation *)

definition rmult_body :: "[i,i,i] \<Rightarrow> o" where
  "rmult_body(b,d) \<equiv> \<lambda>z. \<exists>x' y' x y. z = \<langle>\<langle>x', y'\<rangle>, x, y\<rangle> \<and> (\<langle>x', x\<rangle> \<in> b \<or> x' = x \<and> \<langle>y', y\<rangle> \<in> d)"

relativize functional "rmult_body" "rmult_body_rel"
relationalize "rmult_body_rel" "is_rmult_body"

synthesize "is_rmult_body" from_definition
arity_theorem for "is_rmult_body_fm"

lemma (in M_ZF_trans) separation_is_rmult_body:
 "(##M)(b) \<Longrightarrow> (##M)(d) \<Longrightarrow> separation(##M, is_rmult_body(##M,b,d))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x,b,d] \<Turnstile> is_rmult_body_fm(1,2,0)",THEN iffD1])
   apply(rule_tac is_rmult_body_iff_sats[where env="[_,b,d]",symmetric])
  apply(simp_all)
  apply(rule_tac separation_ax[where env="[b,d]",simplified])
    apply(simp_all add:arity_is_rmult_body_fm ord_simp_union is_rmult_body_fm_type)
  done

lemma (in M_ZF_trans) rmult_body_abs:
  assumes "(##M)(b)" "(##M)(d)" "(##M)(x)"
  shows "is_rmult_body(##M,b,d,x) \<longleftrightarrow> rmult_body(b,d,x)"
  using assms pair_in_M_iff apply_closed
  unfolding rmult_body_def is_rmult_body_def
  by (auto)

lemma (in M_ZF_trans) separation_rmult_body:
 "(##M)(b) \<Longrightarrow> (##M)(d) \<Longrightarrow> separation
        (##M, \<lambda>z. \<exists>x' y' x y. z = \<langle>\<langle>x', y'\<rangle>, x, y\<rangle> \<and> (\<langle>x', x\<rangle> \<in> b \<or> x' = x \<and> \<langle>y', y\<rangle> \<in> d))"
  using separation_is_rmult_body rmult_body_abs
    separation_cong[where P="is_rmult_body(##M,b,d)" and M="##M",THEN iffD1]
  unfolding rmult_body_def
  by simp

definition ord_iso_body :: "[i,i,i,i] \<Rightarrow> o" where
  "ord_iso_body(A,r,s) \<equiv> \<lambda>f. \<forall>x\<in>A. \<forall>y\<in>A. \<langle>x, y\<rangle> \<in> r \<longleftrightarrow> \<langle>f ` x, f ` y\<rangle> \<in> s"

relativize functional "ord_iso_body" "ord_iso_body_rel"
relationalize "ord_iso_body_rel" "is_ord_iso_body"

synthesize "is_ord_iso_body" from_definition assuming "nonempty"
arity_theorem for "is_ord_iso_body_fm"

lemma (in M_ZF_trans) ord_iso_body_abs:
  assumes "(##M)(A)" "(##M)(r)" "(##M)(s)" "(##M)(x)"
  shows "is_ord_iso_body(##M,A,r,s,x) \<longleftrightarrow> ord_iso_body(A,r,s,x)"
  using assms pair_in_M_iff apply_closed zero_in_M transitivity[of _ A]
  unfolding ord_iso_body_def is_ord_iso_body_def
  by auto

lemma (in M_ZF_trans) separation_ord_iso_body:
 "(##M)(A) \<Longrightarrow> (##M)(r) \<Longrightarrow> (##M)(s) \<Longrightarrow> separation(##M, \<lambda>f. \<forall>x\<in>A. \<forall>y\<in>A. \<langle>x, y\<rangle> \<in> r \<longleftrightarrow> \<langle>f ` x, f ` y\<rangle> \<in> s)"
  using separation_in_ctm[where env="[A,r,s]" and \<phi>="is_ord_iso_body_fm(1,2,3,0)",
      OF _ _ _ iff_trans[OF is_ord_iso_body_iff_sats[symmetric] ord_iso_body_abs]]
    nonempty arity_is_ord_iso_body_fm is_ord_iso_body_fm_type
  unfolding ord_iso_body_def
  by(simp_all add: ord_simp_union)

synthesize "PiP_rel" from_definition assuming "nonempty"
arity_theorem for "PiP_rel_fm"

lemma (in M_ZF_trans) separation_PiP_rel:
 "(##M)(A) \<Longrightarrow> separation(##M, PiP_rel(##M,A))"
  using separation_in_ctm[where env="[A]" and \<phi>="PiP_rel_fm(1,0)"]
    nonempty PiP_rel_iff_sats[symmetric] arity_PiP_rel_fm PiP_rel_fm_type
  by(simp_all add: ord_simp_union)

synthesize "injP_rel" from_definition assuming "nonempty"
arity_theorem for "injP_rel_fm"

lemma (in M_ZF_trans) separation_injP_rel:
 "(##M)(A) \<Longrightarrow> separation(##M, injP_rel(##M,A))"
  using separation_in_ctm[where env="[A]" and \<phi>="injP_rel_fm(1,0)"]
    nonempty injP_rel_iff_sats[symmetric] arity_injP_rel_fm injP_rel_fm_type
  by(simp_all add: ord_simp_union)

synthesize "surjP_rel" from_definition assuming "nonempty"
arity_theorem for "surjP_rel_fm"

lemma (in M_ZF_trans) separation_surjP_rel:
 "(##M)(A) \<Longrightarrow> (##M)(B) \<Longrightarrow> separation(##M, surjP_rel(##M,A,B))"
  using separation_in_ctm[where env="[A,B]" and \<phi>="surjP_rel_fm(1,2,0)"]
    nonempty surjP_rel_iff_sats[symmetric] arity_surjP_rel_fm surjP_rel_fm_type
  by(simp_all add: ord_simp_union)

synthesize "cons_like_rel" from_definition assuming "nonempty"
arity_theorem for "cons_like_rel_fm"

lemma (in M_ZF_trans) separation_cons_like_rel:
 "separation(##M, cons_like_rel(##M))"
  using separation_in_ctm[where env="[]" and \<phi>="cons_like_rel_fm(0)"]
    nonempty cons_like_rel_iff_sats[symmetric] arity_cons_like_rel_fm cons_like_rel_fm_type
  by simp

definition supset_body :: "[i] \<Rightarrow> o" where
  "supset_body \<equiv> \<lambda> x. \<exists>a. \<exists>b. x = \<langle>a,b\<rangle> \<and> b \<subseteq> a"

relativize functional "supset_body" "supset_body_rel"
relationalize "supset_body_rel" "is_supset_body"

synthesize "is_supset_body" from_definition
arity_theorem for "is_supset_body_fm"

lemma (in M_ZF_trans) separation_is_supset_body:
 "separation(##M, is_supset_body(##M))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x] \<Turnstile> is_supset_body_fm(0)",THEN iffD1])
   apply(rule_tac is_supset_body_iff_sats[where env="[_]",symmetric])
  apply(simp_all)
  apply(rule_tac separation_ax[where env="[]",simplified])
    apply(simp_all add:arity_is_supset_body_fm ord_simp_union is_supset_body_fm_type)
  done

lemma (in M_ZF_trans) supset_body_abs:
  assumes "(##M)(x)"
  shows "is_supset_body(##M,x) \<longleftrightarrow> supset_body(x)"
  using assms pair_in_M_iff apply_closed
  unfolding supset_body_def is_supset_body_def
  by (auto)

lemma (in M_ZF_trans) separation_supset_body:
 "separation(##M, \<lambda> x. \<exists>a. \<exists>b. x = \<langle>a,b\<rangle> \<and> b \<subseteq> a)"
  using separation_is_supset_body supset_body_abs
    separation_cong[where P="is_supset_body(##M)" and M="##M",THEN iffD1]
  unfolding supset_body_def
  by simp


lemma (in M_ZF_trans) separation_is_function:
 "separation(##M, is_function(##M))"
  using separation_in_ctm[where env="[]" and \<phi>="function_fm(0)"] arity_function_fm
  by simp

(* Instances in M_replacement*)

(* *)
definition id_rel :: "[i\<Rightarrow>o,i] \<Rightarrow> o" where
  "id_rel(A) \<equiv> \<lambda>z. \<exists>x[A]. z = \<langle>x, x\<rangle>"
relativize "id_rel" "is_id_rel"
synthesize "is_id_rel" from_definition assuming "nonempty"
arity_theorem for "is_id_rel_fm"

lemma (in M_ZF_trans) separation_is_id_rel:
 "separation(##M, is_id_rel(##M))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x] \<Turnstile> is_id_rel_fm(0)",THEN iffD1])
   apply(rule_tac is_id_rel_iff_sats[where env="[_]",symmetric])
  apply(simp_all add:zero_in_M)
  apply(rule_tac separation_ax[where env="[]",simplified])
    apply(simp_all add:arity_is_id_rel_fm ord_simp_union is_id_rel_fm_type)
  done

lemma (in M_ZF_trans) id_rel_abs:
  assumes "(##M)(x)"
  shows "is_id_rel(##M,x) \<longleftrightarrow> id_rel(##M,x)"
  using assms zero_in_M pair_in_M_iff unfolding id_rel_def is_id_rel_def
  by auto

lemma (in M_ZF_trans) separation_id_rel:
 "separation(##M, \<lambda>z. \<exists>x[##M]. z = \<langle>x, x\<rangle>)"
  using id_rel_abs separation_is_id_rel
  unfolding id_rel_def
  by (rule_tac separation_cong[where P="is_id_rel(##M)",THEN iffD1])

definition fstsnd_in_sndsnd :: "[i] \<Rightarrow> o" where
  "fstsnd_in_sndsnd \<equiv> \<lambda>x. fst(snd(x)) \<in> snd(snd(x))"
relativize "fstsnd_in_sndsnd" "is_fstsnd_in_sndsnd"
synthesize "is_fstsnd_in_sndsnd" from_definition assuming "nonempty"
arity_theorem for "is_fstsnd_in_sndsnd_fm"

lemma (in M_ZF_trans) separation_is_fstsnd_in_sndsnd:
 "separation(##M, is_fstsnd_in_sndsnd(##M))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x] \<Turnstile> is_fstsnd_in_sndsnd_fm(0)",THEN iffD1])
   apply(rule_tac is_fstsnd_in_sndsnd_iff_sats[where env="[_]",symmetric])
  apply(simp_all add:zero_in_M)
  apply(rule_tac separation_ax[where env="[]",simplified])
    apply(simp_all add:arity_is_fstsnd_in_sndsnd_fm ord_simp_union is_fstsnd_in_sndsnd_fm_type)
  done

lemma (in M_ZF_trans) fstsnd_in_sndsnd_abs:
  assumes "(##M)(x)"
  shows "is_fstsnd_in_sndsnd(##M,x) \<longleftrightarrow> fstsnd_in_sndsnd(x)"
  using assms pair_in_M_iff fst_abs snd_abs fst_snd_closed
  unfolding fstsnd_in_sndsnd_def is_fstsnd_in_sndsnd_def
  by auto

lemma (in M_ZF_trans) separation_fstsnd_in_sndsnd:
 "separation(##M, \<lambda>x. fst(snd(x)) \<in> snd(snd(x)))"
  using fstsnd_in_sndsnd_abs separation_is_fstsnd_in_sndsnd
  unfolding fstsnd_in_sndsnd_def
  by (rule_tac separation_cong[where P="is_fstsnd_in_sndsnd(##M)",THEN iffD1])

definition sndfst_eq_fstsnd :: "[i] \<Rightarrow> o" where
  "sndfst_eq_fstsnd \<equiv> \<lambda>x. snd(fst(x)) = fst(snd(x))"
relativize "sndfst_eq_fstsnd" "is_sndfst_eq_fstsnd"
synthesize "is_sndfst_eq_fstsnd" from_definition assuming "nonempty"
arity_theorem for "is_sndfst_eq_fstsnd_fm"

lemma (in M_ZF_trans) separation_is_sndfst_eq_fstsnd:
 "separation(##M, is_sndfst_eq_fstsnd(##M))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x] \<Turnstile> is_sndfst_eq_fstsnd_fm(0)",THEN iffD1])
   apply(rule_tac is_sndfst_eq_fstsnd_iff_sats[where env="[_]",symmetric])
  apply(simp_all add:zero_in_M)
  apply(rule_tac separation_ax[where env="[]",simplified])
    apply(simp_all add:arity_is_sndfst_eq_fstsnd_fm ord_simp_union is_sndfst_eq_fstsnd_fm_type)
  done

lemma (in M_ZF_trans) sndfst_eq_fstsnd_abs:
  assumes "(##M)(x)"
  shows "is_sndfst_eq_fstsnd(##M,x) \<longleftrightarrow> sndfst_eq_fstsnd(x)"
  using assms pair_in_M_iff fst_abs snd_abs fst_snd_closed
  unfolding sndfst_eq_fstsnd_def is_sndfst_eq_fstsnd_def
  by auto

lemma (in M_ZF_trans) separation_sndfst_eq_fstsnd:
 "separation(##M, \<lambda>x. snd(fst(x)) = fst(snd(x)))"
  using sndfst_eq_fstsnd_abs separation_is_sndfst_eq_fstsnd
  unfolding sndfst_eq_fstsnd_def
  by (rule_tac separation_cong[where P="is_sndfst_eq_fstsnd(##M)",THEN iffD1])



 (* 3. separation(##M, \<lambda>x. fst(fst(x)) = fst(snd(x))) *)
definition fstfst_eq_fstsnd :: "[i] \<Rightarrow> o" where
  "fstfst_eq_fstsnd \<equiv> \<lambda>x. fst(fst(x)) = fst(snd(x))"
relativize "fstfst_eq_fstsnd" "is_fstfst_eq_fstsnd"
synthesize "is_fstfst_eq_fstsnd" from_definition assuming "nonempty"
arity_theorem for "is_fstfst_eq_fstsnd_fm"

lemma (in M_ZF_trans) separation_is_fstfst_eq_fstsnd:
 "separation(##M, is_fstfst_eq_fstsnd(##M))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x] \<Turnstile> is_fstfst_eq_fstsnd_fm(0)",THEN iffD1])
   apply(rule_tac is_fstfst_eq_fstsnd_iff_sats[where env="[_]",symmetric])
  apply(simp_all add:zero_in_M)
  apply(rule_tac separation_ax[where env="[]",simplified])
    apply(simp_all add:arity_is_fstfst_eq_fstsnd_fm ord_simp_union is_fstfst_eq_fstsnd_fm_type)
  done

lemma (in M_ZF_trans) fstfst_eq_fstsnd_abs:
  assumes "(##M)(x)"
  shows "is_fstfst_eq_fstsnd(##M,x) \<longleftrightarrow> fstfst_eq_fstsnd(x)"
  using assms pair_in_M_iff fst_abs snd_abs fst_snd_closed
  unfolding fstfst_eq_fstsnd_def is_fstfst_eq_fstsnd_def
  by auto

lemma (in M_ZF_trans) separation_fstfst_eq_fstsnd:
 "separation(##M, \<lambda>x. fst(fst(x)) = fst(snd(x)))"
  using fstfst_eq_fstsnd_abs separation_is_fstfst_eq_fstsnd
  unfolding fstfst_eq_fstsnd_def
  by (rule_tac separation_cong[where P="is_fstfst_eq_fstsnd(##M)",THEN iffD1])


(*\<And>B. (##M)(B) \<Longrightarrow> \<forall>A\<in>M. separation(##M, \<lambda>y. \<exists>x\<in>A. y = \<langle>x, restrict(x, B)\<rangle>)*)
definition restrict_elem :: "[i,i,i] \<Rightarrow> o" where
  "restrict_elem(B,A) \<equiv> \<lambda>y. \<exists>x\<in>A. y = \<langle>x, restrict(x, B)\<rangle>"

relativize "restrict_elem" "is_restrict_elem"
synthesize "is_restrict_elem" from_definition assuming "nonempty"
arity_theorem for "is_restrict_elem_fm"

lemma (in M_ZF_trans) separation_is_restrict_elem:
 "(##M)(B) \<Longrightarrow> (##M)(A) \<Longrightarrow> separation(##M, is_restrict_elem(##M,B,A))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x,A,B] \<Turnstile> is_restrict_elem_fm(2,1,0)",THEN iffD1])
   apply(rule_tac is_restrict_elem_iff_sats[where env="[_,A,B]",symmetric])
  apply(simp_all add:zero_in_M)
  apply(rule_tac separation_ax[where env="[A,B]",simplified])
    apply(simp_all add:arity_is_restrict_elem_fm ord_simp_union is_restrict_elem_fm_type)
  done

lemma (in M_ZF_trans) restrict_elem_abs:
  assumes "(##M)(B)" "(##M)(A)" "(##M)(x)"
  shows "is_restrict_elem(##M,B,A,x) \<longleftrightarrow> restrict_elem(B,A,x)"
  using assms pair_in_M_iff fst_abs snd_abs fst_snd_closed
  unfolding restrict_elem_def is_restrict_elem_def
  by auto

lemma (in M_ZF_trans) separation_restrict_elem_aux:
 "(##M)(B) \<Longrightarrow> (##M)(A) \<Longrightarrow> separation(##M, \<lambda>y. \<exists>x\<in>A. y = \<langle>x, restrict(x, B)\<rangle>)"
  using restrict_elem_abs separation_is_restrict_elem
  unfolding restrict_elem_def
  by (rule_tac separation_cong[where P="is_restrict_elem(##M,B,_)",THEN iffD1])

lemma (in M_ZF_trans) separation_restrict_elem:
 "(##M)(B) \<Longrightarrow> \<forall>A[##M]. separation(##M, \<lambda>y. \<exists>x\<in>A. y = \<langle>x, restrict(x, B)\<rangle>)"
  using separation_restrict_elem_aux by simp

lemma (in M_ZF_trans) separation_ordinal:
 "separation(##M, ordinal(##M))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x] \<Turnstile> ordinal_fm(0)",THEN iffD1])
   apply(rule_tac ordinal_iff_sats[where env="[_]",symmetric])
  apply(simp_all)
  apply(rule_tac separation_ax[where env="[]",simplified])
    apply(simp_all add:ord_simp_union )
  done

lemma (in M_ZF_trans) separation_Ord:
 "separation(##M, Ord)"
  using separation_ordinal ordinal_abs
    separation_cong[where P="ordinal(##M)" and M="##M",THEN iffD1]
  unfolding Ord_def
  by simp

(*  "M(G) \<Longrightarrow> M(Q) \<Longrightarrow> separation(M, \<lambda>p. \<forall>x\<in>G. x \<in> snd(p) \<longleftrightarrow> (\<forall>s\<in>fst(p). \<langle>s, x\<rangle> \<in> Q))" *)
definition insnd_ballPair :: "[i,i,i] \<Rightarrow> o" where
  "insnd_ballPair(B,A) \<equiv> \<lambda>p. \<forall>x\<in>B. x \<in> snd(p) \<longleftrightarrow> (\<forall>s\<in>fst(p). \<langle>s, x\<rangle> \<in> A)"

relativize "insnd_ballPair" "is_insnd_ballPair"
synthesize "is_insnd_ballPair" from_definition assuming "nonempty"
arity_theorem for "is_insnd_ballPair_fm"

lemma (in M_ZF_trans) separation_is_insnd_ballPair:
 "(##M)(B) \<Longrightarrow> (##M)(A) \<Longrightarrow> separation(##M, is_insnd_ballPair(##M,B,A))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x,A,B] \<Turnstile> is_insnd_ballPair_fm(2,1,0)",THEN iffD1])
   apply(rule_tac is_insnd_ballPair_iff_sats[where env="[_,A,B]",symmetric])
  apply(simp_all add:zero_in_M)
  apply(rule_tac separation_ax[where env="[A,B]",simplified])
    apply(simp_all add:arity_is_insnd_ballPair_fm ord_simp_union is_insnd_ballPair_fm_type)
  done

lemma (in M_ZF_trans) insnd_ballPair_abs:
  assumes "(##M)(B)" "(##M)(A)" "(##M)(x)"
  shows "is_insnd_ballPair(##M,B,A,x) \<longleftrightarrow> insnd_ballPair(B,A,x)"
  using assms pair_in_M_iff fst_abs snd_abs fst_snd_closed
    transM[of _ B] transM[of _ "snd(x)"] transM[of _ "fst(x)"]
  unfolding insnd_ballPair_def is_insnd_ballPair_def
  by (auto)

lemma (in M_ZF_trans) separation_insnd_ballPair_aux:
 "(##M)(B) \<Longrightarrow> (##M)(A) \<Longrightarrow> separation(##M, \<lambda>p. \<forall>x\<in>B. x \<in> snd(p) \<longleftrightarrow> (\<forall>s\<in>fst(p). \<langle>s, x\<rangle> \<in> A))"
  using insnd_ballPair_abs separation_is_insnd_ballPair
  unfolding insnd_ballPair_def
  by (rule_tac separation_cong[where P="is_insnd_ballPair(##M,B,_)",THEN iffD1])

lemma (in M_ZF_trans) separation_insnd_ballPair:
 "(##M)(B) \<Longrightarrow> \<forall>A[##M]. separation(##M, \<lambda>p. \<forall>x\<in>B. x \<in> snd(p) \<longleftrightarrow> (\<forall>s\<in>fst(p). \<langle>s, x\<rangle> \<in> A))"
  using separation_insnd_ballPair_aux by simp

(* *)
definition bex_restrict_eq_dom :: "[i,i,i,i] \<Rightarrow> o" where
  "bex_restrict_eq_dom(B,A,x) \<equiv> \<lambda>dr. \<exists>r\<in>A . restrict(r,B) = x \<and> dr=domain(r)"

relativize "bex_restrict_eq_dom" "is_bex_restrict_eq_dom"
synthesize "is_bex_restrict_eq_dom" from_definition assuming "nonempty"
arity_theorem for "is_bex_restrict_eq_dom_fm"

lemma (in M_ZF_trans) separation_is_bex_restrict_eq_dom:
 "(##M)(B) \<Longrightarrow> (##M)(A) \<Longrightarrow> (##M)(x) \<Longrightarrow> separation(##M, is_bex_restrict_eq_dom(##M,B,A,x))"
  apply(rule_tac separation_cong[
        where P="\<lambda> dr . M,[dr,x,A,B] \<Turnstile> is_bex_restrict_eq_dom_fm(3,2,1,0)",THEN iffD1])
   apply(rule_tac is_bex_restrict_eq_dom_iff_sats[where env="[_,x,A,B]",symmetric])
  apply(simp_all add:zero_in_M)
  apply(rule_tac separation_ax[where env="[x,A,B]",simplified])
    apply(simp_all add:arity_is_bex_restrict_eq_dom_fm ord_simp_union is_bex_restrict_eq_dom_fm_type)
  done
lemma (in M_ZF_trans) bex_restrict_eq_dom_abs:
  assumes "(##M)(B)" "(##M)(A)" "(##M)(x)" "(##M)(dr)"
  shows "is_bex_restrict_eq_dom(##M,B,A,x,dr) \<longleftrightarrow> bex_restrict_eq_dom(B,A,x,dr)"
  using assms transM[of _ B] transM[of _ A]
  unfolding bex_restrict_eq_dom_def is_bex_restrict_eq_dom_def 
  by (auto)

lemma (in M_ZF_trans) separation_restrict_eq_dom_eq_aux: 
    "(##M)(A) \<Longrightarrow> (##M)(B) \<Longrightarrow> (##M)(x) \<Longrightarrow> separation(##M, \<lambda>dr. \<exists>r\<in>A . restrict(r,B) = x \<and> dr=domain(r))" 
  using bex_restrict_eq_dom_abs separation_is_bex_restrict_eq_dom
  unfolding bex_restrict_eq_dom_def
  by (rule_tac separation_cong[where P="is_bex_restrict_eq_dom(##M,B,A,x)",THEN iffD1])

lemma (in M_ZF_trans) separation_restrict_eq_dom_eq: 
    "(##M)(A) \<Longrightarrow> (##M)(B) \<Longrightarrow> \<forall>x[##M]. separation(##M, \<lambda>dr. \<exists>r\<in>A . restrict(r,B) = x \<and> dr=domain(r))" 
  using separation_restrict_eq_dom_eq_aux by simp

definition insnd_restrict_eq_dom :: "[i,i,i,i] \<Rightarrow> o" where
  "insnd_restrict_eq_dom(B,A,D) \<equiv> \<lambda>p. \<forall>x\<in>D. x \<in> snd(p) \<longleftrightarrow> (\<exists>r\<in>A. restrict(r, B) = fst(p) \<and> x = domain(r))"

definition is_insnd_restrict_eq_dom :: "[i\<Rightarrow>o,i,i,i,i] \<Rightarrow> o" where
  "is_insnd_restrict_eq_dom(N,B,A,D,p) \<equiv>
       \<exists>c[N].
          \<exists>a[N].
             (\<forall>x[N]. x \<in> D \<longrightarrow> x \<in> a \<longleftrightarrow> (\<exists>r[N]. \<exists>b[N]. (r \<in> A \<and>restriction(N, r, B, b)) \<and> b=c \<and> is_domain(N, r, x))) \<and>
             is_snd(N, p, a) \<and> is_fst(N, p, c)"

synthesize "is_insnd_restrict_eq_dom" from_definition assuming "nonempty"
arity_theorem for "is_insnd_restrict_eq_dom_fm"

lemma (in M_ZF_trans) separation_is_insnd_restrict_eq_dom:
 "(##M)(B) \<Longrightarrow> (##M)(A) \<Longrightarrow> (##M)(D) \<Longrightarrow> separation(##M, is_insnd_restrict_eq_dom(##M,B,A,D))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x,D,A,B] \<Turnstile> is_insnd_restrict_eq_dom_fm(3,2,1,0)",THEN iffD1])
   apply(rule_tac is_insnd_restrict_eq_dom_iff_sats[where env="[_,D,A,B]",symmetric])
  apply(simp_all add:zero_in_M)
  apply(rule_tac separation_ax[where env="[D,A,B]",simplified])
    apply(simp_all add:arity_is_insnd_restrict_eq_dom_fm ord_simp_union is_insnd_restrict_eq_dom_fm_type)
  done

lemma (in M_basic) insnd_restrict_eq_dom_abs:
  assumes "(M)(B)" "(M)(A)" "(M)(D)" "(M)(x)"
  shows "is_insnd_restrict_eq_dom(M,B,A,D,x) \<longleftrightarrow> insnd_restrict_eq_dom(B,A,D,x)"
  using assms pair_in_M_iff fst_abs snd_abs fst_snd_closed domain_closed
    transM[of _ B] transM[of _ D] transM[of _ A]  transM[of _ "snd(x)"] transM[of _ "fst(x)"]
  unfolding insnd_restrict_eq_dom_def is_insnd_restrict_eq_dom_def
  by simp

lemma (in M_ZF_trans) separation_restrict_eq_dom_eq_pair_aux:
    "(##M)(A) \<Longrightarrow> (##M)(B) \<Longrightarrow> (##M)(D) \<Longrightarrow>
      separation(##M, \<lambda>p. \<forall>x\<in>D. x \<in> snd(p) \<longleftrightarrow> (\<exists>r\<in>A. restrict(r, B) = fst(p) \<and> x = domain(r)))"
  using separation_is_insnd_restrict_eq_dom insnd_restrict_eq_dom_abs
  unfolding insnd_restrict_eq_dom_def
  by (rule_tac separation_cong[where P="is_insnd_restrict_eq_dom(##M,B,A,D)",THEN iffD1])

lemma (in M_ZF_trans) separation_restrict_eq_dom_eq_pair:
    "(##M)(A) \<Longrightarrow> (##M)(B) \<Longrightarrow> 
  \<forall>D[##M]. separation(##M, \<lambda>p. \<forall>x\<in>D. x \<in> snd(p) \<longleftrightarrow> (\<exists>r\<in>A. restrict(r, B) = fst(p) \<and> x = domain(r)))" 
  using separation_restrict_eq_dom_eq_pair_aux by simp

(* (##M)(A) \<Longrightarrow> (##M)(b) \<Longrightarrow> (##M)(f) \<Longrightarrow>
separation(##M, \<lambda>y. \<exists>x\<in>A. y = \<langle>x, \<mu> i. x \<in> if_range_F_else_F(\<lambda>x. if (##M)(x) then x else 0, b, f, i)\<rangle>) *)

(* MOVE THIS to an appropriate place *)
synthesize "is_converse" from_definition assuming "nonempty"
arity_theorem for "is_converse_fm"

definition ifrFb_body where
  "ifrFb_body(M,b,f,x,i) \<equiv> x \<in>
  (if b = 0 then if i \<in> range(f) then
  if M(converse(f) ` i) then converse(f) ` i else 0 else 0 else if M(i) then i else 0)"

relativize functional "ifrFb_body" "ifrFb_body_rel"
relationalize "ifrFb_body_rel" "is_ifrFb_body"

synthesize "is_ifrFb_body" from_definition assuming "nonempty"
arity_theorem for "is_ifrFb_body_fm"

definition ifrangeF_body :: "[i\<Rightarrow>o,i,i,i,i] \<Rightarrow> o" where
  "ifrangeF_body(M,A,b,f) \<equiv> \<lambda>y. \<exists>x\<in>A. y = \<langle>x,\<mu> i. ifrFb_body(M,b,f,x,i)\<rangle>"

relativize functional "ifrangeF_body" "ifrangeF_body_rel"
relationalize "ifrangeF_body_rel" "is_ifrangeF_body"

synthesize "is_ifrangeF_body" from_definition assuming "nonempty"
arity_theorem for "is_ifrangeF_body_fm"

lemma (in M_ZF_trans) separation_is_ifrangeF_body:
  "(##M)(A) \<Longrightarrow> (##M)(r) \<Longrightarrow> (##M)(s) \<Longrightarrow> separation(##M, is_ifrangeF_body(##M,A,r,s))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x,A,r,s] \<Turnstile> is_ifrangeF_body_fm(1,2,3,0)",THEN iffD1])
   apply(rule_tac is_ifrangeF_body_iff_sats[where env="[_,A,r,s]",symmetric])
            apply(simp_all add:zero_in_M)
  apply(rule_tac separation_ax[where env="[A,r,s]",simplified])
    apply(simp_all add:arity_is_ifrangeF_body_fm ord_simp_union is_ifrangeF_body_fm_type)
  done

lemma (in M_basic) is_ifrFb_body_closed: "M(r) \<Longrightarrow> M(s) \<Longrightarrow> is_ifrFb_body(M, r, s, x, i) \<Longrightarrow> M(i)"
  unfolding ifrangeF_body_def is_ifrangeF_body_def is_ifrFb_body_def If_abs
  by (cases "i\<in>range(s)"; cases "r=0"; auto dest:transM)

lemma (in M_ZF_trans) ifrangeF_body_abs:
  assumes "(##M)(A)" "(##M)(r)" "(##M)(s)" "(##M)(x)"
  shows "is_ifrangeF_body(##M,A,r,s,x) \<longleftrightarrow> ifrangeF_body(##M,A,r,s,x)"
proof -
  {
    fix a
    assume "a\<in>M"
    with assms
    have "(\<mu> i. i\<in> M \<and> is_ifrFb_body(##M, r, s, z, i))= (\<mu> i. is_ifrFb_body(##M, r, s, z, i))" for z
      using is_ifrFb_body_closed[of r s z]
      by (rule_tac Least_cong[of "\<lambda>i. i\<in>M \<and> is_ifrFb_body(##M,r,s,z,i)"]) auto
    moreover
    have "(\<mu> i. is_ifrFb_body(##M, r, s, z, i))= (\<mu> i. ifrFb_body(##M, r, s, z, i))" for z
    proof (rule_tac Least_cong[of "\<lambda>i. is_ifrFb_body(##M,r,s,z,i)" "\<lambda>i. ifrFb_body(##M,r,s,z,i)"])
      fix y
      from assms \<open>a\<in>M\<close>
      show "is_ifrFb_body(##M, r, s, z, y) \<longleftrightarrow> ifrFb_body(##M, r, s, z, y)"
        using If_abs apply_0
        unfolding ifrFb_body_def is_ifrFb_body_def
        by (cases "y\<in>M"; cases "y\<in>range(s)"; cases "converse(s)`y \<in> M";
            auto dest:transM split del: split_if del:iffI)
          (auto simp flip:setclass_iff; (force simp only:setclass_iff))+
    qed
    moreover from \<open>a\<in>M\<close>
    have "least(##M, \<lambda>i. i \<in> M \<and> is_ifrFb_body(##M, r, s, z, i), a)
      \<longleftrightarrow> a = (\<mu> i.  i\<in> M \<and> is_ifrFb_body(##M, r, s, z,i))" for z
      using If_abs least_abs'[of "\<lambda>i. (##M)(i) \<and> is_ifrFb_body(##M,r,s,z,i)" a]
      by simp
    ultimately
    have "least(##M, \<lambda>i. i \<in> M \<and> is_ifrFb_body(##M, r, s, z, i), a)
      \<longleftrightarrow> a = (\<mu> i. ifrFb_body(##M, r, s, z,i))" for z
      by simp
  }
  with assms
  show ?thesis
    using  pair_in_M_iff apply_closed zero_in_M transitivity[of _ A]
    unfolding ifrangeF_body_def is_ifrangeF_body_def
    by (auto dest:transM)
qed

lemma (in M_ZF_trans) separation_ifrangeF_body:
  "(##M)(A) \<Longrightarrow> (##M)(b) \<Longrightarrow> (##M)(f) \<Longrightarrow> separation
        (##M, \<lambda>y.  \<exists>x\<in>A. y = \<langle>x, \<mu> i. x \<in> if_range_F_else_F(\<lambda>x. if (##M)(x) then x else 0, b, f, i)\<rangle>)"
  using separation_is_ifrangeF_body ifrangeF_body_abs
    separation_cong[where P="is_ifrangeF_body(##M,A,b,f)" and M="##M",THEN iffD1]
  unfolding ifrangeF_body_def if_range_F_def if_range_F_else_F_def ifrFb_body_def
  by simp

(* (##M)(A) \<Longrightarrow> (##M)(G) \<Longrightarrow> (##M)(b) \<Longrightarrow> (##M)(f) \<Longrightarrow>
    separation(##M,
      \<lambda>y. \<exists>x\<in>A. y = \<langle>x, \<mu> i. x \<in> if_range_F_else_F(\<lambda>a. if (##M)(a) then G`a else 0, b, f, i)\<rangle>) *)

definition ifrFb_body2 where
  "ifrFb_body2(M,G,b,f,x,i) \<equiv> x \<in>
  (if b = 0 then if i \<in> range(f) then
  if M(converse(f) ` i) then G`(converse(f) ` i) else 0 else 0 else if M(i) then G`i else 0)"

relativize functional "ifrFb_body2" "ifrFb_body2_rel"
relationalize "ifrFb_body2_rel" "is_ifrFb_body2"

synthesize "is_ifrFb_body2" from_definition assuming "nonempty"
arity_theorem for "is_ifrFb_body2_fm"

definition ifrangeF_body2 :: "[i\<Rightarrow>o,i,i,i,i,i] \<Rightarrow> o" where
  "ifrangeF_body2(M,A,G,b,f) \<equiv> \<lambda>y. \<exists>x\<in>A. y = \<langle>x,\<mu> i. ifrFb_body2(M,G,b,f,x,i)\<rangle>"

relativize functional "ifrangeF_body2" "ifrangeF_body2_rel"
relationalize "ifrangeF_body2_rel" "is_ifrangeF_body2"

synthesize "is_ifrangeF_body2" from_definition assuming "nonempty"
arity_theorem for "is_ifrangeF_body2_fm"

lemma (in M_ZF_trans) separation_is_ifrangeF_body2:
  "(##M)(A) \<Longrightarrow> (##M)(G) \<Longrightarrow> (##M)(r) \<Longrightarrow> (##M)(s) \<Longrightarrow> separation(##M, is_ifrangeF_body2(##M,A,G,r,s))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x,A,G,r,s] \<Turnstile> is_ifrangeF_body2_fm(1,2,3,4,0)",THEN iffD1])
   apply(rule_tac is_ifrangeF_body2_iff_sats[where env="[_,A,G,r,s]",symmetric])
              apply(simp_all add:zero_in_M)
  apply(rule_tac separation_ax[where env="[A,G,r,s]",simplified])
    apply(simp_all add:arity_is_ifrangeF_body2_fm ord_simp_union is_ifrangeF_body2_fm_type)
  done

lemma (in M_basic) is_ifrFb_body2_closed: "M(G) \<Longrightarrow> M(r) \<Longrightarrow> M(s) \<Longrightarrow> is_ifrFb_body2(M, G, r, s, x, i) \<Longrightarrow> M(i)"
  unfolding ifrangeF_body2_def is_ifrangeF_body2_def is_ifrFb_body2_def If_abs
  by (cases "i\<in>range(s)"; cases "r=0"; auto dest:transM)

lemma (in M_ZF_trans) ifrangeF_body2_abs:
  assumes "(##M)(A)" "(##M)(G)" "(##M)(r)" "(##M)(s)" "(##M)(x)"
  shows "is_ifrangeF_body2(##M,A,G,r,s,x) \<longleftrightarrow> ifrangeF_body2(##M,A,G,r,s,x)"
proof -
  {
    fix a
    assume "a\<in>M"
    with assms
    have "(\<mu> i. i\<in> M \<and> is_ifrFb_body2(##M, G, r, s, z, i))= (\<mu> i. is_ifrFb_body2(##M, G, r, s, z, i))" for z
      using is_ifrFb_body2_closed[of G r s z]
      by (rule_tac Least_cong[of "\<lambda>i. i\<in>M \<and> is_ifrFb_body2(##M,G,r,s,z,i)"]) auto
    moreover
    have "(\<mu> i. is_ifrFb_body2(##M, G, r, s, z, i))= (\<mu> i. ifrFb_body2(##M, G, r, s, z, i))" for z
    proof (rule_tac Least_cong[of "\<lambda>i. is_ifrFb_body2(##M,G,r,s,z,i)" "\<lambda>i. ifrFb_body2(##M,G,r,s,z,i)"])
      fix y
      from assms \<open>a\<in>M\<close>
      show "is_ifrFb_body2(##M, G, r, s, z, y) \<longleftrightarrow> ifrFb_body2(##M, G, r, s, z, y)"
        using If_abs apply_0
        unfolding ifrFb_body2_def is_ifrFb_body2_def
        by (cases "y\<in>M"; cases "y\<in>range(s)"; cases "converse(s)`y \<in> M";
            auto dest:transM split del: split_if del:iffI)
          (auto simp flip:setclass_iff; (force simp only:setclass_iff))+
    qed
    moreover from \<open>a\<in>M\<close>
    have "least(##M, \<lambda>i. i \<in> M \<and> is_ifrFb_body2(##M, G, r, s, z, i), a)
      \<longleftrightarrow> a = (\<mu> i.  i\<in> M \<and> is_ifrFb_body2(##M, G, r, s, z,i))" for z
      using If_abs least_abs'[of "\<lambda>i. (##M)(i) \<and> is_ifrFb_body2(##M,G,r,s,z,i)" a]
      by simp
    ultimately
    have "least(##M, \<lambda>i. i \<in> M \<and> is_ifrFb_body2(##M, G, r, s, z, i), a)
      \<longleftrightarrow> a = (\<mu> i. ifrFb_body2(##M, G, r, s, z,i))" for z
      by simp
  }
  with assms
  show ?thesis
    using  pair_in_M_iff apply_closed zero_in_M transitivity[of _ A]
    unfolding ifrangeF_body2_def is_ifrangeF_body2_def
    by (auto dest:transM)
qed

lemma (in M_ZF_trans) separation_ifrangeF_body2:
  "(##M)(A) \<Longrightarrow> (##M)(G) \<Longrightarrow> (##M)(b) \<Longrightarrow> (##M)(f) \<Longrightarrow>
       separation
        (##M,
         \<lambda>y. \<exists>x\<in>A.
                y =
                \<langle>x, \<mu> i. x \<in>
                         if_range_F_else_F(\<lambda>a. if (##M)(a) then G ` a else 0, b, f, i)\<rangle>)"
  using separation_is_ifrangeF_body2 ifrangeF_body2_abs
    separation_cong[where P="is_ifrangeF_body2(##M,A,G,b,f)" and M="##M",THEN iffD1]
  unfolding ifrangeF_body2_def if_range_F_def if_range_F_else_F_def ifrFb_body2_def
  by simp

(* (##M)(A) \<Longrightarrow> (##M)(b) \<Longrightarrow> (##M)(f) \<Longrightarrow> (##M)(F) \<Longrightarrow>
  separation(##M,
    \<lambda>y. \<exists>x\<in>A. y = \<langle>x, \<mu> i. x \<in> if_range_F_else_F(\<lambda>a. if (##M)(a) then F -`` {a} else 0, b, f, i)\<rangle>) *)

definition ifrFb_body3 where
  "ifrFb_body3(M,G,b,f,x,i) \<equiv> x \<in>
  (if b = 0 then if i \<in> range(f) then
  if M(converse(f) ` i) then G-``{converse(f) ` i} else 0 else 0 else if M(i) then G-``{i} else 0)"

relativize functional "ifrFb_body3" "ifrFb_body3_rel"
relationalize "ifrFb_body3_rel" "is_ifrFb_body3"

synthesize "is_ifrFb_body3" from_definition assuming "nonempty"
arity_theorem for "is_ifrFb_body3_fm"

definition ifrangeF_body3 :: "[i\<Rightarrow>o,i,i,i,i,i] \<Rightarrow> o" where
  "ifrangeF_body3(M,A,G,b,f) \<equiv> \<lambda>y. \<exists>x\<in>A. y = \<langle>x,\<mu> i. ifrFb_body3(M,G,b,f,x,i)\<rangle>"

relativize functional "ifrangeF_body3" "ifrangeF_body3_rel"
relationalize "ifrangeF_body3_rel" "is_ifrangeF_body3"

synthesize "is_ifrangeF_body3" from_definition assuming "nonempty"
arity_theorem for "is_ifrangeF_body3_fm"

lemma (in M_ZF_trans) separation_is_ifrangeF_body3:
  "(##M)(A) \<Longrightarrow> (##M)(G) \<Longrightarrow> (##M)(r) \<Longrightarrow> (##M)(s) \<Longrightarrow> separation(##M, is_ifrangeF_body3(##M,A,G,r,s))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x,A,G,r,s] \<Turnstile> is_ifrangeF_body3_fm(1,2,3,4,0)",THEN iffD1])
   apply(rule_tac is_ifrangeF_body3_iff_sats[where env="[_,A,G,r,s]",symmetric])
              apply(simp_all add:zero_in_M)
  apply(rule_tac separation_ax[where env="[A,G,r,s]",simplified])
    apply(simp_all add:arity_is_ifrangeF_body3_fm ord_simp_union is_ifrangeF_body3_fm_type)
  done

lemma (in M_basic) is_ifrFb_body3_closed: "M(G) \<Longrightarrow> M(r) \<Longrightarrow> M(s) \<Longrightarrow> is_ifrFb_body3(M, G, r, s, x, i) \<Longrightarrow> M(i)"
  unfolding ifrangeF_body3_def is_ifrangeF_body3_def is_ifrFb_body3_def If_abs
  by (cases "i\<in>range(s)"; cases "r=0"; auto dest:transM)

lemma (in M_ZF_trans) ifrangeF_body3_abs:
  assumes "(##M)(A)" "(##M)(G)" "(##M)(r)" "(##M)(s)" "(##M)(x)"
  shows "is_ifrangeF_body3(##M,A,G,r,s,x) \<longleftrightarrow> ifrangeF_body3(##M,A,G,r,s,x)"
proof -
  {
    fix a
    assume "a\<in>M"
    with assms
    have "(\<mu> i. i\<in> M \<and> is_ifrFb_body3(##M, G, r, s, z, i))= (\<mu> i. is_ifrFb_body3(##M, G, r, s, z, i))" for z
      using is_ifrFb_body3_closed[of G r s z]
      by (rule_tac Least_cong[of "\<lambda>i. i\<in>M \<and> is_ifrFb_body3(##M,G,r,s,z,i)"]) auto
    moreover
    have "(\<mu> i. is_ifrFb_body3(##M, G, r, s, z, i))= (\<mu> i. ifrFb_body3(##M, G, r, s, z, i))" for z
    proof (rule_tac Least_cong[of "\<lambda>i. is_ifrFb_body3(##M,G,r,s,z,i)" "\<lambda>i. ifrFb_body3(##M,G,r,s,z,i)"])
      fix y
      from assms \<open>a\<in>M\<close>
      show "is_ifrFb_body3(##M, G, r, s, z, y) \<longleftrightarrow> ifrFb_body3(##M, G, r, s, z, y)"
        using If_abs apply_0
        unfolding ifrFb_body3_def is_ifrFb_body3_def
        by (cases "y\<in>M"; cases "y\<in>range(s)"; cases "converse(s)`y \<in> M";
            auto dest:transM split del: split_if del:iffI)
          (auto simp flip:setclass_iff; (force simp only:setclass_iff))+
    qed
    moreover from \<open>a\<in>M\<close>
    have "least(##M, \<lambda>i. i \<in> M \<and> is_ifrFb_body3(##M, G, r, s, z, i), a)
      \<longleftrightarrow> a = (\<mu> i.  i\<in> M \<and> is_ifrFb_body3(##M, G, r, s, z,i))" for z
      using If_abs least_abs'[of "\<lambda>i. (##M)(i) \<and> is_ifrFb_body3(##M,G,r,s,z,i)" a]
      by simp
    ultimately
    have "least(##M, \<lambda>i. i \<in> M \<and> is_ifrFb_body3(##M, G, r, s, z, i), a)
      \<longleftrightarrow> a = (\<mu> i. ifrFb_body3(##M, G, r, s, z,i))" for z
      by simp
  }
  with assms
  show ?thesis
    using  pair_in_M_iff apply_closed zero_in_M transitivity[of _ A]
    unfolding ifrangeF_body3_def is_ifrangeF_body3_def
    by (auto dest:transM)
qed

lemma (in M_ZF_trans) separation_ifrangeF_body3:
  "(##M)(A) \<Longrightarrow> (##M)(G) \<Longrightarrow> (##M)(b) \<Longrightarrow> (##M)(f) \<Longrightarrow>
       separation
        (##M,
         \<lambda>y. \<exists>x\<in>A.
                y =
                \<langle>x, \<mu> i. x \<in>
                         if_range_F_else_F(\<lambda>a. if (##M)(a) then G-``{a} else 0, b, f, i)\<rangle>)"
  using separation_is_ifrangeF_body3 ifrangeF_body3_abs
    separation_cong[where P="is_ifrangeF_body3(##M,A,G,b,f)" and M="##M",THEN iffD1]
  unfolding ifrangeF_body3_def if_range_F_def if_range_F_else_F_def ifrFb_body3_def
  by simp

(* (##M)(A) \<Longrightarrow> (##M)(b) \<Longrightarrow> (##M)(f) \<Longrightarrow> (##M)(A') \<Longrightarrow>
    separation(##M, \<lambda>y. \<exists>x\<in>A'. y = \<langle>x, \<mu> i. x \<in> if_range_F_else_F((`)(A), b, f, i)\<rangle>) *)

definition ifrFb_body4 where
  "ifrFb_body4(G,b,f,x,i) \<equiv> x \<in>
  (if b = 0 then if i \<in> range(f) then G`(converse(f) ` i) else 0 else G`i)"

relativize functional "ifrFb_body4" "ifrFb_body4_rel"
relationalize "ifrFb_body4_rel" "is_ifrFb_body4"

synthesize "is_ifrFb_body4" from_definition assuming "nonempty"
arity_theorem for "is_ifrFb_body4_fm"

definition ifrangeF_body4 :: "[i\<Rightarrow>o,i,i,i,i,i] \<Rightarrow> o" where
  "ifrangeF_body4(M,A,G,b,f) \<equiv> \<lambda>y. \<exists>x\<in>A. y = \<langle>x,\<mu> i. ifrFb_body4(G,b,f,x,i)\<rangle>"

relativize functional "ifrangeF_body4" "ifrangeF_body4_rel"
relationalize "ifrangeF_body4_rel" "is_ifrangeF_body4"

synthesize "is_ifrangeF_body4" from_definition assuming "nonempty"
arity_theorem for "is_ifrangeF_body4_fm"

lemma (in M_ZF_trans) separation_is_ifrangeF_body4:
  "(##M)(A) \<Longrightarrow> (##M)(G) \<Longrightarrow> (##M)(r) \<Longrightarrow> (##M)(s) \<Longrightarrow> separation(##M, is_ifrangeF_body4(##M,A,G,r,s))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x,A,G,r,s] \<Turnstile> is_ifrangeF_body4_fm(1,2,3,4,0)",THEN iffD1])
   apply(rule_tac is_ifrangeF_body4_iff_sats[where env="[_,A,G,r,s]",symmetric])
              apply(simp_all add:zero_in_M)
  apply(rule_tac separation_ax[where env="[A,G,r,s]",simplified])
    apply(simp_all add:arity_is_ifrangeF_body4_fm ord_simp_union is_ifrangeF_body4_fm_type)
  done

lemma (in M_basic) is_ifrFb_body4_closed: "M(G) \<Longrightarrow> M(r) \<Longrightarrow> M(s) \<Longrightarrow> is_ifrFb_body4(M, G, r, s, x, i) \<Longrightarrow> M(i)"
  using If_abs
  unfolding ifrangeF_body4_def is_ifrangeF_body4_def is_ifrFb_body4_def fun_apply_def
  by (cases "i\<in>range(s)"; cases "r=0"; auto dest:transM)

lemma (in M_ZF_trans) ifrangeF_body4_abs:
  assumes "(##M)(A)" "(##M)(G)" "(##M)(r)" "(##M)(s)" "(##M)(x)"
  shows "is_ifrangeF_body4(##M,A,G,r,s,x) \<longleftrightarrow> ifrangeF_body4(##M,A,G,r,s,x)"
proof -
  {
    fix a
    assume "a\<in>M"
    with assms
    have "(\<mu> i. i\<in> M \<and> is_ifrFb_body4(##M, G, r, s, z, i))= (\<mu> i. is_ifrFb_body4(##M, G, r, s, z, i))" for z
      using is_ifrFb_body4_closed[of G r s z]
      by (rule_tac Least_cong[of "\<lambda>i. i\<in>M \<and> is_ifrFb_body4(##M,G,r,s,z,i)"]) auto
    moreover
    have "(\<mu> i. is_ifrFb_body4(##M, G, r, s, z, i))= (\<mu> i. ifrFb_body4(G, r, s, z, i))" if "z\<in>M" for z
    proof (rule_tac Least_cong[of "\<lambda>i. is_ifrFb_body4(##M,G,r,s,z,i)" "\<lambda>i. ifrFb_body4(G,r,s,z,i)"])
      fix y
      from assms \<open>a\<in>M\<close> \<open>z\<in>M\<close>
      show "is_ifrFb_body4(##M, G, r, s, z, y) \<longleftrightarrow> ifrFb_body4(G, r, s, z, y)"
        using If_abs apply_0
        unfolding ifrFb_body4_def is_ifrFb_body4_def
        apply (cases "y\<in>M"; cases "y\<in>range(s)"; cases "r=0"; cases "y\<in>domain(G)";
            auto dest:transM split del: split_if del:iffI)
        by (auto simp flip:setclass_iff; (force simp only: fun_apply_def setclass_iff))
          (auto simp flip:setclass_iff simp: fun_apply_def )
    qed
    moreover from \<open>a\<in>M\<close>
    have "least(##M, \<lambda>i. i \<in> M \<and> is_ifrFb_body4(##M, G, r, s, z, i), a)
      \<longleftrightarrow> a = (\<mu> i.  i\<in> M \<and> is_ifrFb_body4(##M, G, r, s, z,i))" for z
      using If_abs least_abs'[of "\<lambda>i. (##M)(i) \<and> is_ifrFb_body4(##M,G,r,s,z,i)" a]
      by simp
    ultimately
    have "z\<in>M \<Longrightarrow> least(##M, \<lambda>i. i \<in> M \<and> is_ifrFb_body4(##M, G, r, s, z, i), a)
      \<longleftrightarrow> a = (\<mu> i. ifrFb_body4(G, r, s, z,i))" for z
      by simp
  }
  with assms
  show ?thesis
    using  pair_in_M_iff apply_closed zero_in_M transitivity[of _ A]
    unfolding ifrangeF_body4_def is_ifrangeF_body4_def
    by (auto dest:transM)
qed

lemma (in M_ZF_trans) separation_ifrangeF_body4:
  "(##M)(A) \<Longrightarrow> (##M)(G) \<Longrightarrow> (##M)(b) \<Longrightarrow> (##M)(f) \<Longrightarrow>
       separation(##M, \<lambda>y. \<exists>x\<in>A. y = \<langle>x, \<mu> i. x \<in> if_range_F_else_F((`)(G), b, f, i)\<rangle>)"
  using separation_is_ifrangeF_body4 ifrangeF_body4_abs
    separation_cong[where P="is_ifrangeF_body4(##M,A,G,b,f)" and M="##M",THEN iffD1]
  unfolding ifrangeF_body4_def if_range_F_def if_range_F_else_F_def ifrFb_body4_def
  by simp

(* (##M)(G) \<Longrightarrow> (##M)(A) \<Longrightarrow>
    separation(##M,
      \<lambda>y. \<exists>x\<in>A. y = \<langle>x, \<mu> i. x \<in> if_range_F_else_F(\<lambda>x. {xa \<in> G . x \<in> xa}, b, f, i)\<rangle>) *)

definition ifrFb_body5 where
  "ifrFb_body5(G,b,f,x,i) \<equiv> x \<in>
  (if b = 0 then if i \<in> range(f) then {xa \<in> G . converse(f) ` i \<in> xa} else 0 else {xa \<in> G . i \<in> xa})"

relativize functional "ifrFb_body5" "ifrFb_body5_rel"
relationalize "ifrFb_body5_rel" "is_ifrFb_body5"

synthesize "is_ifrFb_body5" from_definition assuming "nonempty"
arity_theorem for "is_ifrFb_body5_fm"

definition ifrangeF_body5 :: "[i\<Rightarrow>o,i,i,i,i,i] \<Rightarrow> o" where
  "ifrangeF_body5(M,A,G,b,f) \<equiv> \<lambda>y. \<exists>x\<in>A. y = \<langle>x,\<mu> i. ifrFb_body5(G,b,f,x,i)\<rangle>"

relativize functional "ifrangeF_body5" "ifrangeF_body5_rel"
relationalize "ifrangeF_body5_rel" "is_ifrangeF_body5"

synthesize "is_ifrangeF_body5" from_definition assuming "nonempty"
arity_theorem for "is_ifrangeF_body5_fm"

lemma (in M_ZF_trans) separation_is_ifrangeF_body5:
  "(##M)(A) \<Longrightarrow> (##M)(G) \<Longrightarrow> (##M)(r) \<Longrightarrow> (##M)(s) \<Longrightarrow> separation(##M, is_ifrangeF_body5(##M,A,G,r,s))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x,A,G,r,s] \<Turnstile> is_ifrangeF_body5_fm(1,2,3,4,0)",THEN iffD1])
   apply(rule_tac is_ifrangeF_body5_iff_sats[where env="[_,A,G,r,s]",symmetric])
              apply(simp_all add:zero_in_M)
  apply(rule_tac separation_ax[where env="[A,G,r,s]",simplified])
    apply(simp_all add:arity_is_ifrangeF_body5_fm ord_simp_union is_ifrangeF_body5_fm_type)
  done

lemma (in M_basic) is_ifrFb_body5_closed: "M(G) \<Longrightarrow> M(r) \<Longrightarrow> M(s) \<Longrightarrow> is_ifrFb_body5(M, G, r, s, x, i) \<Longrightarrow> M(i)"
  using If_abs
  unfolding ifrangeF_body5_def is_ifrangeF_body5_def is_ifrFb_body5_def fun_apply_def
  by (cases "i\<in>range(s)"; cases "r=0"; auto dest:transM)

(* FIXME: this has been proved in M_replacement, we should move the next instances after
making the instance of M_replacement.
*)
definition separation_domain_eq :: "[i,i] \<Rightarrow> o" where
  "separation_domain_eq(R) \<equiv> \<lambda>x. domain(x) = R"

relativize functional "separation_domain_eq" "separation_domain_eq_rel"
relationalize "separation_domain_eq_rel" "is_separation_domain_eq"

synthesize "is_separation_domain_eq" from_definition assuming "nonempty"
arity_theorem for "is_separation_domain_eq_fm"

lemma (in M_ZF_trans) separation_is_separation_domain_eq:
 "(##M)(A) \<Longrightarrow> separation(##M, is_separation_domain_eq(##M,A))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x,A] \<Turnstile> is_separation_domain_eq_fm(1,0)",THEN iffD1])
   apply(rule_tac is_separation_domain_eq_iff_sats[where env="[_,A]",symmetric])
  apply(simp_all add:nonempty[simplified])
  apply(rule_tac separation_ax[where env="[A]",simplified])
    apply(simp_all add:arity_is_separation_domain_eq_fm ord_simp_union is_separation_domain_eq_fm_type)
  done

lemma (in M_ZF_trans) separation_domain_eq_abs:
  assumes "(##M)(R)" "(##M)(x)"
  shows "is_separation_domain_eq(##M,R,x) \<longleftrightarrow> separation_domain_eq(R,x)"
  using assms pair_in_M_iff is_Int_abs
  unfolding separation_domain_eq_def is_separation_domain_eq_def
  by (auto simp:domain_closed[simplified])

lemma (in M_ZF_trans) separation_separation_domain_eq:
 "(##M)(R) \<Longrightarrow> separation
        (##M, \<lambda>x. domain(x) = R)"
  using separation_is_separation_domain_eq separation_domain_eq_abs
  unfolding separation_domain_eq_def
  by (rule_tac separation_cong[where P="is_separation_domain_eq(##M,R)",THEN iffD1])

lemma (in M_ZF_trans) ifrangeF_body5_abs:
  assumes "(##M)(A)" "(##M)(G)" "(##M)(r)" "(##M)(s)" "(##M)(x)"
  shows "is_ifrangeF_body5(##M,A,G,r,s,x) \<longleftrightarrow> ifrangeF_body5(##M,A,G,r,s,x)"
proof -
  {
    fix a
    assume "a\<in>M"
    with assms
    have "(\<mu> i. i\<in> M \<and> is_ifrFb_body5(##M, G, r, s, z, i))= (\<mu> i. is_ifrFb_body5(##M, G, r, s, z, i))" for z
      using is_ifrFb_body5_closed[of G r s z]
      by (rule_tac Least_cong[of "\<lambda>i. i\<in>M \<and> is_ifrFb_body5(##M,G,r,s,z,i)"]) auto
    moreover
    have "(\<mu> i. is_ifrFb_body5(##M, G, r, s, z, i))= (\<mu> i. ifrFb_body5(G, r, s, z, i))" if "z\<in>M" for z
    proof (rule_tac Least_cong[of "\<lambda>i. is_ifrFb_body5(##M,G,r,s,z,i)" "\<lambda>i. ifrFb_body5(G,r,s,z,i)"])
      fix y
      from assms \<open>a\<in>M\<close> \<open>z\<in>M\<close>
      show "is_ifrFb_body5(##M, G, r, s, z, y) \<longleftrightarrow> ifrFb_body5(G, r, s, z, y)"
        using If_abs apply_0 separation_in_constant separation_in_rev
        unfolding ifrFb_body5_def is_ifrFb_body5_def
        apply (cases "y\<in>M"; cases "y\<in>range(s)"; cases "r=0"; cases "y\<in>domain(G)";
            auto dest:transM split del: split_if del:iffI)
        apply (auto simp flip:setclass_iff; (force simp only: fun_apply_def setclass_iff))
        apply (auto simp flip:setclass_iff simp: fun_apply_def)
        apply (auto dest:transM)
        done
    qed
    moreover from \<open>a\<in>M\<close>
    have "least(##M, \<lambda>i. i \<in> M \<and> is_ifrFb_body5(##M, G, r, s, z, i), a)
      \<longleftrightarrow> a = (\<mu> i.  i\<in> M \<and> is_ifrFb_body5(##M, G, r, s, z,i))" for z
      using If_abs least_abs'[of "\<lambda>i. (##M)(i) \<and> is_ifrFb_body5(##M,G,r,s,z,i)" a]
      by simp
    ultimately
    have "z\<in>M \<Longrightarrow> least(##M, \<lambda>i. i \<in> M \<and> is_ifrFb_body5(##M, G, r, s, z, i), a)
      \<longleftrightarrow> a = (\<mu> i. ifrFb_body5(G, r, s, z,i))" for z
      by simp
  }
  with assms
  show ?thesis
    using  pair_in_M_iff apply_closed zero_in_M transitivity[of _ A]
    unfolding ifrangeF_body5_def is_ifrangeF_body5_def
    by (auto dest:transM)
qed

lemma (in M_ZF_trans) separation_ifrangeF_body5:
  "(##M)(A) \<Longrightarrow> (##M)(G) \<Longrightarrow> (##M)(b) \<Longrightarrow> (##M)(f) \<Longrightarrow>
       separation(##M, \<lambda>y. \<exists>x\<in>A. y = \<langle>x, \<mu> i. x \<in> if_range_F_else_F(\<lambda>x. {xa \<in> G . x \<in> xa}, b, f, i)\<rangle>)"
  using separation_is_ifrangeF_body5 ifrangeF_body5_abs
    separation_cong[where P="is_ifrangeF_body5(##M,A,G,b,f)" and M="##M",THEN iffD1]
  unfolding ifrangeF_body5_def if_range_F_def if_range_F_else_F_def ifrFb_body5_def
  by simp

(* (##M)(A) \<Longrightarrow> (##M)(b) \<Longrightarrow> (##M)(f) \<Longrightarrow>
    separation(##M,
      \<lambda>y. \<exists>x\<in>A'. y = \<langle>x, \<mu> i. x \<in> if_range_F_else_F(\<lambda>a. {p \<in> A . domain(p) = a}, b, f, i)\<rangle>) *)

definition ifrFb_body6 where
  "ifrFb_body6(G,b,f,x,i) \<equiv> x \<in>
  (if b = 0 then if i \<in> range(f) then {p\<in>G . domain(p) = converse(f) ` i} else 0 else {p\<in>G . domain(p) = i})"

relativize functional "ifrFb_body6" "ifrFb_body6_rel"
relationalize "ifrFb_body6_rel" "is_ifrFb_body6"

synthesize "is_ifrFb_body6" from_definition assuming "nonempty"
arity_theorem for "is_ifrFb_body6_fm"

definition ifrangeF_body6 :: "[i\<Rightarrow>o,i,i,i,i,i] \<Rightarrow> o" where
  "ifrangeF_body6(M,A,G,b,f) \<equiv> \<lambda>y. \<exists>x\<in>A. y = \<langle>x,\<mu> i. ifrFb_body6(G,b,f,x,i)\<rangle>"

relativize functional "ifrangeF_body6" "ifrangeF_body6_rel"
relationalize "ifrangeF_body6_rel" "is_ifrangeF_body6"

synthesize "is_ifrangeF_body6" from_definition assuming "nonempty"
arity_theorem for "is_ifrangeF_body6_fm"

lemma (in M_ZF_trans) separation_is_ifrangeF_body6:
  "(##M)(A) \<Longrightarrow> (##M)(G) \<Longrightarrow> (##M)(r) \<Longrightarrow> (##M)(s) \<Longrightarrow> separation(##M, is_ifrangeF_body6(##M,A,G,r,s))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x,A,G,r,s] \<Turnstile> is_ifrangeF_body6_fm(1,2,3,4,0)",THEN iffD1])
   apply(rule_tac is_ifrangeF_body6_iff_sats[where env="[_,A,G,r,s]",symmetric])
              apply(simp_all add:zero_in_M)
  apply(rule_tac separation_ax[where env="[A,G,r,s]",simplified])
    apply(simp_all add:arity_is_ifrangeF_body6_fm ord_simp_union is_ifrangeF_body6_fm_type)
  done

lemma (in M_basic) ifrFb_body6_closed: "M(G) \<Longrightarrow> M(r) \<Longrightarrow> M(s) \<Longrightarrow> ifrFb_body6(G, r, s, x, i) \<longleftrightarrow>  M(i) \<and> ifrFb_body6(G, r, s, x, i)"
  using If_abs
  unfolding ifrangeF_body6_def is_ifrangeF_body6_def ifrFb_body6_def fun_apply_def
  by (cases "i\<in>range(s)"; cases "r=0"; auto dest:transM)

lemma (in M_basic) is_ifrFb_body6_closed: "M(G) \<Longrightarrow> M(r) \<Longrightarrow> M(s) \<Longrightarrow> is_ifrFb_body6(M, G, r, s, x, i) \<Longrightarrow> M(i)"
  using If_abs
  unfolding ifrangeF_body6_def is_ifrangeF_body6_def is_ifrFb_body6_def fun_apply_def
  by (cases "i\<in>range(s)"; cases "r=0"; auto dest:transM)

lemma (in M_ZF_trans) ifrangeF_body6_abs:
  assumes "(##M)(A)" "(##M)(G)" "(##M)(r)" "(##M)(s)" "(##M)(x)"
  shows "is_ifrangeF_body6(##M,A,G,r,s,x) \<longleftrightarrow> ifrangeF_body6(##M,A,G,r,s,x)"
proof -
  {
    fix a
    assume "a\<in>M"
    with assms
    have "(\<mu> i. i\<in> M \<and> is_ifrFb_body6(##M, G, r, s, z, i))= (\<mu> i. is_ifrFb_body6(##M, G, r, s, z, i))" for z
      using is_ifrFb_body6_closed[of G r s z]
      by (rule_tac Least_cong[of "\<lambda>i. i\<in>M \<and> is_ifrFb_body6(##M,G,r,s,z,i)"]) auto
    moreover
    have "(\<mu> i. i\<in>M \<and> is_ifrFb_body6(##M, G, r, s, z, i))= (\<mu> i. i\<in>M \<and>  ifrFb_body6(G, r, s, z, i))" if "z\<in>M" for z
    proof (rule_tac Least_cong[of "\<lambda>i. i\<in>M \<and> is_ifrFb_body6(##M,G,r,s,z,i)" "\<lambda>i. i\<in>M \<and> ifrFb_body6(G,r,s,z,i)"])
      fix y
      from assms \<open>a\<in>M\<close> \<open>z\<in>M\<close>
      show "y\<in>M \<and> is_ifrFb_body6(##M, G, r, s, z, y) \<longleftrightarrow> y\<in>M \<and> ifrFb_body6(G, r, s, z, y)"
        using If_abs apply_0 separation_in_constant transitivity[of _ G]
          separation_closed converse_closed apply_closed range_closed zero_in_M
          separation_cong[OF eq_commute,THEN iffD1,OF separation_separation_domain_eq]
        unfolding ifrFb_body6_def is_ifrFb_body6_def
        by auto
    qed
    moreover from \<open>a\<in>M\<close>
    have "least(##M, \<lambda>i. i \<in> M \<and> is_ifrFb_body6(##M, G, r, s, z, i), a)
      \<longleftrightarrow> a = (\<mu> i.  i\<in> M \<and> is_ifrFb_body6(##M, G, r, s, z,i))" for z
      using If_abs least_abs'[of "\<lambda>i. (##M)(i) \<and> is_ifrFb_body6(##M,G,r,s,z,i)" a]
      by simp
    ultimately
    have "z\<in>M \<Longrightarrow> least(##M, \<lambda>i. i \<in> M \<and> is_ifrFb_body6(##M, G, r, s, z, i), a)
      \<longleftrightarrow> a = (\<mu> i. ifrFb_body6(G, r, s, z,i))" for z
      using Least_cong[OF ifrFb_body6_closed[of G r s]] assms
      by simp
  }
  with assms
  show ?thesis
    using  pair_in_M_iff apply_closed zero_in_M transitivity[of _ A]
    unfolding ifrangeF_body6_def is_ifrangeF_body6_def
    by (auto dest:transM)
qed

lemma (in M_ZF_trans) separation_ifrangeF_body6:
  "(##M)(A) \<Longrightarrow> (##M)(G) \<Longrightarrow> (##M)(b) \<Longrightarrow> (##M)(f) \<Longrightarrow>
       separation(##M,
      \<lambda>y. \<exists>x\<in>A. y = \<langle>x, \<mu> i. x \<in> if_range_F_else_F(\<lambda>a. {p \<in> G . domain(p) = a}, b, f, i)\<rangle>)"
  using separation_is_ifrangeF_body6 ifrangeF_body6_abs
    separation_cong[where P="is_ifrangeF_body6(##M,A,G,b,f)" and M="##M",THEN iffD1]
  unfolding ifrangeF_body6_def if_range_F_def if_range_F_else_F_def ifrFb_body6_def
  by simp

(* (##M)(A) \<Longrightarrow> (##M)(f) \<Longrightarrow> (##M)(b) \<Longrightarrow> (##M)(D) \<Longrightarrow> (##M)(r') \<Longrightarrow> (##M)(A') \<Longrightarrow>
    separation(##M,
      \<lambda>y. \<exists>x\<in>A'. y = \<langle>x, \<mu> i. x \<in> if_range_F_else_F(drSR_Y(r', D, A), b, f, i)\<rangle>) *)

definition ifrFb_body7 where
  "ifrFb_body7(B,D,A,b,f,x,i) \<equiv> x \<in>
    (if b = 0 then if i \<in> range(f) then
        {d \<in> D . \<exists>r\<in>A. restrict(r, B) = converse(f) ` i \<and> d = domain(r)} else 0
       else {d \<in> D . \<exists>r\<in>A. restrict(r, B) = i \<and> d = domain(r)})"

relativize functional "ifrFb_body7" "ifrFb_body7_rel"
relationalize "ifrFb_body7_rel" "is_ifrFb_body7"

synthesize "is_ifrFb_body7" from_definition assuming "nonempty"
arity_theorem for "is_ifrFb_body7_fm"

definition ifrangeF_body7 :: "[i\<Rightarrow>o,i,i,i,i,i,i,i] \<Rightarrow> o" where
  "ifrangeF_body7(M,A,B,D,G,b,f) \<equiv> \<lambda>y. \<exists>x\<in>A. y = \<langle>x,\<mu> i. ifrFb_body7(B,D,G,b,f,x,i)\<rangle>"

relativize functional "ifrangeF_body7" "ifrangeF_body7_rel"
relationalize "ifrangeF_body7_rel" "is_ifrangeF_body7"

synthesize "is_ifrangeF_body7" from_definition assuming "nonempty"
arity_theorem for "is_ifrangeF_body7_fm"

lemma (in M_ZF_trans) separation_is_ifrangeF_body7:
  "(##M)(A) \<Longrightarrow> (##M)(B) \<Longrightarrow> (##M)(D) \<Longrightarrow> (##M)(G) \<Longrightarrow> (##M)(r) \<Longrightarrow> (##M)(s) \<Longrightarrow> separation(##M, is_ifrangeF_body7(##M,A,B,D,G,r,s))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x,A,B,D,G,r,s] \<Turnstile> is_ifrangeF_body7_fm(1,2,3,4,5,6,0)",THEN iffD1])
   apply(rule_tac is_ifrangeF_body7_iff_sats[where env="[_,A,B,D,G,r,s]",symmetric])
                  apply(simp_all add:zero_in_M)
  apply(rule_tac separation_ax[where env="[A,B,D,G,r,s]",simplified])
    apply(simp_all add:arity_is_ifrangeF_body7_fm ord_simp_union is_ifrangeF_body7_fm_type)
  done

lemma (in M_basic) ifrFb_body7_closed: "M(B) \<Longrightarrow> M(D) \<Longrightarrow> M(G) \<Longrightarrow> M(r) \<Longrightarrow> M(s) \<Longrightarrow>
  ifrFb_body7(B,D,G, r, s, x, i) \<longleftrightarrow>  M(i) \<and> ifrFb_body7(B,D,G, r, s, x, i)"
  using If_abs
  unfolding ifrangeF_body7_def is_ifrangeF_body7_def ifrFb_body7_def fun_apply_def
  by (cases "i\<in>range(s)"; cases "r=0"; auto dest:transM)

lemma (in M_basic) is_ifrFb_body7_closed: "M(B) \<Longrightarrow> M(D) \<Longrightarrow> M(G) \<Longrightarrow> M(r) \<Longrightarrow> M(s) \<Longrightarrow> 
  is_ifrFb_body7(M, B,D,G, r, s, x, i) \<Longrightarrow> M(i)"
  using If_abs
  unfolding ifrangeF_body7_def is_ifrangeF_body7_def is_ifrFb_body7_def fun_apply_def
  by (cases "i\<in>range(s)"; cases "r=0"; auto dest:transM)

lemma (in M_ZF_trans) ifrangeF_body7_abs:
  assumes "(##M)(A)"  "(##M)(B)" "(##M)(D)" "(##M)(G)" "(##M)(r)" "(##M)(s)" "(##M)(x)"
  shows "is_ifrangeF_body7(##M,A,B,D,G,r,s,x) \<longleftrightarrow> ifrangeF_body7(##M,A,B,D,G,r,s,x)"
proof -
  from assms
  have sep_dr: "y\<in>M \<Longrightarrow> separation(##M, \<lambda>d . \<exists>r\<in>M . r\<in>G\<and> y = restrict(r, B) \<and> d = domain(r))" for y
    by(rule_tac separation_cong[where P'="\<lambda>d . \<exists>r\<in> M . r\<in>G \<and> y = restrict(r, B) \<and> d = domain(r)",THEN iffD1,OF _ 
        separation_restrict_eq_dom_eq[rule_format,of G B y]],auto simp:transitivity[of _ G])

  from assms
  have sep_dr'': "y\<in>M \<Longrightarrow> separation(##M, \<lambda>d . \<exists>r\<in>M. r \<in> G \<and> d = domain(r) \<and> converse(s) ` y = restrict(r, B))" for y
    apply(rule_tac separation_cong[where P'="\<lambda>d . \<exists>r\<in> M . r\<in>G \<and> d = domain(r) \<and> converse(s) ` y = restrict(r, B)",THEN iffD1,OF _ separation_restrict_eq_dom_eq[rule_format,of G B "converse(s) ` y "]])
    by(auto simp:transitivity[of _ G] apply_closed[simplified] converse_closed[simplified])
  from assms
  have sep_dr':"separation(##M, \<lambda>x. \<exists>r\<in>M. r \<in> G \<and> x = domain(r) \<and> 0 = restrict(r, B))"
    apply(rule_tac separation_cong[where P'="\<lambda>d . \<exists>r\<in> M . r\<in>G \<and> d = domain(r) \<and> 0 = restrict(r, B)",THEN iffD1,OF _ separation_restrict_eq_dom_eq[rule_format,of G B 0]])
    by(auto simp:transitivity[of _ G] zero_in_M)
  {
    fix a
    assume "a\<in>M"
    with assms
    have "(\<mu> i. i\<in> M \<and> is_ifrFb_body7(##M, B,D,G, r, s, z, i))= (\<mu> i. is_ifrFb_body7(##M,B,D, G, r, s, z, i))" for z
      using is_ifrFb_body7_closed[of B D G r s z]
      by (rule_tac Least_cong[of "\<lambda>i. i\<in>M \<and> is_ifrFb_body7(##M,B,D,G,r,s,z,i)"]) auto
    moreover from this
    have "(\<mu> i. i\<in>M \<and> is_ifrFb_body7(##M, B,D,G, r, s, z, i))= (\<mu> i. i\<in>M \<and>  ifrFb_body7(B,D,G, r, s, z, i))" if "z\<in>M" for z
    proof (rule_tac Least_cong[of "\<lambda>i. i\<in>M \<and> is_ifrFb_body7(##M,B,D,G,r,s,z,i)" "\<lambda>i. i\<in>M \<and> ifrFb_body7(B,D,G,r,s,z,i)"])
      from assms \<open>a\<in>M\<close> \<open>z\<in>M\<close>
      have "is_ifrFb_body7(##M, B,D,G, r, s, z, y) \<longleftrightarrow> ifrFb_body7(B,D,G, r, s, z, y)" if "y\<in>M" for y 
        using If_abs apply_0 
          separation_closed converse_closed apply_closed range_closed zero_in_M 
          separation_restrict_eq_dom_eq[of G,rule_format]
          transitivity[of _ D] transitivity[of _ G]  that sep_dr sep_dr' sep_dr''
         unfolding ifrFb_body7_def is_ifrFb_body7_def
         by auto
       then 
       show " y \<in> M \<and> is_ifrFb_body7(##M, B, D, G, r, s, z, y) \<longleftrightarrow> y \<in> M \<and> ifrFb_body7(B, D, G, r, s, z, y)" for y
         using conj_cong 
         by simp
       qed
    moreover from \<open>a\<in>M\<close>
    have "least(##M, \<lambda>i. i \<in> M \<and> is_ifrFb_body7(##M, B,D,G, r, s, z, i), a)
      \<longleftrightarrow> a = (\<mu> i.  i\<in> M \<and> is_ifrFb_body7(##M,B,D,G, r, s, z,i))" for z
      using If_abs least_abs'[of "\<lambda>i. (##M)(i) \<and> is_ifrFb_body7(##M,B,D,G,r,s,z,i)" a]
      by simp
    ultimately
    have "z\<in>M \<Longrightarrow> least(##M, \<lambda>i. i \<in> M \<and> is_ifrFb_body7(##M,B,D,G, r, s, z, i), a)
      \<longleftrightarrow> a = (\<mu> i. ifrFb_body7(B,D,G, r, s, z,i))" for z
      using Least_cong[OF ifrFb_body7_closed[of B D G r s]] assms
      by simp
  }
  with assms
  show ?thesis
    using  pair_in_M_iff apply_closed zero_in_M transitivity[of _ A]
    unfolding ifrangeF_body7_def is_ifrangeF_body7_def
    by (auto dest:transM)
qed

lemma (in M_ZF_trans) separation_ifrangeF_body7:
  "(##M)(A) \<Longrightarrow> (##M)(B) \<Longrightarrow> (##M)(D) \<Longrightarrow> (##M)(G) \<Longrightarrow> (##M)(b) \<Longrightarrow> (##M)(f) \<Longrightarrow>
    separation(##M,
      \<lambda>y. \<exists>x\<in>A. y = \<langle>x, \<mu> i. x \<in> if_range_F_else_F(drSR_Y(B, D, G), b, f, i)\<rangle>)"
  using separation_is_ifrangeF_body7 ifrangeF_body7_abs drSR_Y_equality
    separation_cong[where P="is_ifrangeF_body7(##M,A,B,D,G,b,f)" and M="##M",THEN iffD1]
  unfolding ifrangeF_body7_def if_range_F_def if_range_F_else_F_def ifrFb_body7_def
  by simp

end