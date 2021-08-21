theory Separation_Instances
  imports
    Discipline_Function
    Forcing_Data
    FiniteFun_Relative
    Cardinal_Relative
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
    apply(simp_all add:arity_is_radd_body_fm nat_simp_union is_radd_body_fm_type)
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
    apply(simp_all add:arity_well_ord_body_fm nat_simp_union well_ord_body_fm_type)
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
    apply(simp_all add:arity_is_obase_body_fm nat_simp_union is_obase_body_fm_type)
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
    apply(simp_all add:arity_is_obase_equals_fm nat_simp_union is_obase_equals_fm_type)
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
    apply(simp_all add:arity_is_id_body_fm nat_simp_union is_id_body_fm_type)
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
    apply(simp_all add:arity_is_rvimage_body_fm nat_simp_union is_rvimage_body_fm_type)
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
    apply(simp_all add:arity_is_rmult_body_fm nat_simp_union is_rmult_body_fm_type)
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

lemma (in M_ZF_trans) separation_is_ord_iso_body:
 "(##M)(A) \<Longrightarrow> (##M)(r) \<Longrightarrow> (##M)(s) \<Longrightarrow> separation(##M, is_ord_iso_body(##M,A,r,s))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x,A,r,s] \<Turnstile> is_ord_iso_body_fm(1,2,3,0)",THEN iffD1])
   apply(rule_tac is_ord_iso_body_iff_sats[where env="[_,A,r,s]",symmetric])
  apply(simp_all add:zero_in_M)
  apply(rule_tac separation_ax[where env="[A,r,s]",simplified])
    apply(simp_all add:arity_is_ord_iso_body_fm nat_simp_union is_ord_iso_body_fm_type)
  done

lemma (in M_ZF_trans) ord_iso_body_abs:
  assumes "(##M)(A)" "(##M)(r)" "(##M)(s)" "(##M)(x)"
  shows "is_ord_iso_body(##M,A,r,s,x) \<longleftrightarrow> ord_iso_body(A,r,s,x)"
  using assms pair_in_M_iff apply_closed zero_in_M transitivity[of _ A]
  unfolding ord_iso_body_def is_ord_iso_body_def
  by auto

lemma (in M_ZF_trans) separation_ord_iso_body:
 "(##M)(A) \<Longrightarrow> (##M)(r) \<Longrightarrow> (##M)(s) \<Longrightarrow> separation
        (##M, \<lambda>f. \<forall>x\<in>A. \<forall>y\<in>A. \<langle>x, y\<rangle> \<in> r \<longleftrightarrow> \<langle>f ` x, f ` y\<rangle> \<in> s)"
  using separation_is_ord_iso_body ord_iso_body_abs
    separation_cong[where P="is_ord_iso_body(##M,A,r,s)" and M="##M",THEN iffD1]
  unfolding ord_iso_body_def
  by simp


synthesize "PiP_rel" from_definition assuming "nonempty"
arity_theorem for "PiP_rel_fm"

lemma (in M_ZF_trans) separation_PiP_rel:
 "(##M)(A) \<Longrightarrow> separation(##M, PiP_rel(##M,A))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x,A] \<Turnstile> PiP_rel_fm(1,0)",THEN iffD1])
   apply(rule_tac PiP_rel_iff_sats[where env="[_,A]",symmetric])
  apply(simp_all add:zero_in_M)
  apply(rule_tac separation_ax[where env="[A]",simplified])
    apply(simp_all add:arity_PiP_rel_fm nat_simp_union PiP_rel_fm_type)
  done

synthesize "injP_rel" from_definition assuming "nonempty"
arity_theorem for "injP_rel_fm"

lemma (in M_ZF_trans) separation_injP_rel:
 "(##M)(A) \<Longrightarrow> separation(##M, injP_rel(##M,A))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x,A] \<Turnstile> injP_rel_fm(1,0)",THEN iffD1])
   apply(rule_tac injP_rel_iff_sats[where env="[_,A]",symmetric])
  apply(simp_all add:zero_in_M)
  apply(rule_tac separation_ax[where env="[A]",simplified])
    apply(simp_all add:arity_injP_rel_fm nat_simp_union injP_rel_fm_type)
  done

synthesize "surjP_rel" from_definition assuming "nonempty"
arity_theorem for "surjP_rel_fm"

lemma (in M_ZF_trans) separation_surjP_rel:
 "(##M)(A) \<Longrightarrow> (##M)(B) \<Longrightarrow> separation(##M, surjP_rel(##M,A,B))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x,A,B] \<Turnstile> surjP_rel_fm(1,2,0)",THEN iffD1])
   apply(rule_tac surjP_rel_iff_sats[where env="[_,A,B]",symmetric])
  apply(simp_all add:zero_in_M)
  apply(rule_tac separation_ax[where env="[A,B]",simplified])
    apply(simp_all add:arity_surjP_rel_fm nat_simp_union surjP_rel_fm_type)
  done

synthesize "cons_like_rel" from_definition assuming "nonempty"
arity_theorem for "cons_like_rel_fm"

lemma (in M_ZF_trans) separation_cons_like_rel:
 "separation(##M, cons_like_rel(##M))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x] \<Turnstile> cons_like_rel_fm(0)",THEN iffD1])
   apply(rule_tac cons_like_rel_iff_sats[where env="[_]",symmetric])
  apply(simp_all add:zero_in_M)
  apply(rule_tac separation_ax[where env="[]",simplified])
    apply(simp_all add:arity_cons_like_rel_fm nat_simp_union cons_like_rel_fm_type)
  done

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
    apply(simp_all add:arity_is_supset_body_fm nat_simp_union is_supset_body_fm_type)
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

lemma (in M_ZF_trans) separation_is_fst:
 "(##M)(a) \<Longrightarrow> separation(##M, \<lambda>x . is_fst(##M,x,a))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x,a] \<Turnstile> fst_fm(0,1)",THEN iffD1])
   apply(rule_tac fst_iff_sats[where env="[_,a]",symmetric])
  apply(simp_all)
  apply(rule_tac separation_ax[where env="[a]",simplified])
    apply(simp_all add:arity_fst_fm nat_simp_union fst_fm_type)
  done

lemma (in M_ZF_trans) separation_fst_equal:
 "(##M)(a) \<Longrightarrow> separation(##M, \<lambda>x. fst(x) = a)"
  using separation_cong[THEN iffD1,OF _ separation_is_fst[of a]]
     iff_sym[of "is_fst(##M)" _ a "fst", OF fst_abs]
  by auto

lemma (in M_ZF_trans) separation_is_apply:
 "(##M)(f) \<Longrightarrow> (##M)(a) \<Longrightarrow> separation(##M, \<lambda>x . is_apply(##M,f,x,a))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x,f,a] \<Turnstile> fun_apply_fm(1,0,2)",THEN iffD1])
   apply(rule_tac fun_apply_iff_sats[where env="[_,f,a]",symmetric])
  apply(simp_all)
  apply(rule_tac separation_ax[where env="[f,a]",simplified])
    apply(simp_all add:arity_fun_apply_fm nat_simp_union)
  done

lemma (in M_ZF_trans) separation_equal_apply:
 "(##M)(f) \<Longrightarrow> (##M)(a) \<Longrightarrow> separation(##M, \<lambda>x. f`x = a)"
  using separation_cong[THEN iffD1,OF _ separation_is_apply[of f a]] apply_abs
  by force
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
    apply(simp_all add:arity_is_id_rel_fm nat_simp_union is_id_rel_fm_type)
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


 (* 2. separation(##M, \<lambda>x. snd(fst(x)) = fst(snd(x))) *)
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
    apply(simp_all add:arity_is_sndfst_eq_fstsnd_fm nat_simp_union is_sndfst_eq_fstsnd_fm_type)
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
    apply(simp_all add:arity_is_fstfst_eq_fstsnd_fm nat_simp_union is_fstfst_eq_fstsnd_fm_type)
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


 (* 5. \<And>a. (##M)(a) \<Longrightarrow> separation(##M, \<lambda>x. fst(fst(x)) = a) *)
definition fstfst_eq :: "[i,i] \<Rightarrow> o" where
  "fstfst_eq(a) \<equiv> \<lambda>x. fst(fst(x)) = a"

relativize "fstfst_eq" "is_fstfst_eq"
synthesize "is_fstfst_eq" from_definition assuming "nonempty"
arity_theorem for "is_fstfst_eq_fm"

lemma (in M_ZF_trans) separation_is_fstfst_eq:
 "(##M)(a) \<Longrightarrow> separation(##M, is_fstfst_eq(##M,a))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x,a] \<Turnstile> is_fstfst_eq_fm(1,0)",THEN iffD1])
   apply(rule_tac is_fstfst_eq_iff_sats[where env="[_,a]",symmetric])
  apply(simp_all add:zero_in_M)
  apply(rule_tac separation_ax[where env="[a]",simplified])
    apply(simp_all add:arity_is_fstfst_eq_fm nat_simp_union is_fstfst_eq_fm_type)
  done

lemma (in M_ZF_trans) fstfst_eq_abs:
  assumes "(##M)(a)" "(##M)(x)"
  shows "is_fstfst_eq(##M,a,x) \<longleftrightarrow> fstfst_eq(a,x)"
  using assms pair_in_M_iff fst_abs snd_abs fst_snd_closed
  unfolding fstfst_eq_def is_fstfst_eq_def
  by auto

lemma (in M_ZF_trans) separation_fstfst_eq:
 "(##M)(a) \<Longrightarrow> separation(##M, \<lambda>x. fst(fst(x)) = a)"
  using fstfst_eq_abs separation_is_fstfst_eq
  unfolding fstfst_eq_def
  by (rule_tac separation_cong[where P="is_fstfst_eq(##M,a)",THEN iffD1])


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
    apply(simp_all add:arity_is_restrict_elem_fm nat_simp_union is_restrict_elem_fm_type)
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
    apply(simp_all add:nat_simp_union )
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
    apply(simp_all add:arity_is_insnd_ballPair_fm nat_simp_union is_insnd_ballPair_fm_type)
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
    apply(simp_all add:arity_is_bex_restrict_eq_dom_fm nat_simp_union is_bex_restrict_eq_dom_fm_type)
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
    apply(simp_all add:arity_is_insnd_restrict_eq_dom_fm nat_simp_union is_insnd_restrict_eq_dom_fm_type)
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

end