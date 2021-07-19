theory Draft_Automatic_Satisfaction
  imports
    Discipline_Function
    Forcing_Data
begin

(* Proof of concept of the proposal to automatize *)
definition body :: "[i,i,i,i] \<Rightarrow> o" where
  "body(u,w,x,y) \<equiv> x \<in> u \<and> y = {\<langle>w, x\<rangle>}"

relativize functional "body" "body_rel"
relationalize "body_rel" "is_body"

(* Do we have a reasonable order of arguments in is_body' ? *)
(* relativize_tm "x \<in> u \<and> y = {\<langle>w, x\<rangle>}" "is_body'"
 *)

lemma (in M_ZF_trans) body_abs:
  assumes "(##M)(ya)" "(##M)(z)" "(##M)(y)" "(##M)(x)"
  shows "is_body(##M,ya,z,y,x) \<longleftrightarrow> body(ya,z,y,x)"
  using assms unfolding body_def is_body_def 
  by (simp flip:setclass_iff)

synthesize "is_body" from_definition
arity_theorem for "cons_fm"
arity_theorem for "is_body_fm"

lemma (in M_ZF_trans) proof_of_concept_aux:
 "(##M)(u) \<Longrightarrow> (##M)(w) \<Longrightarrow> strong_replacement(##M, body(u,w))"
  apply(rule_tac strong_replacement_cong[
        where P="\<lambda> x y . M,[x,y,u,w] \<Turnstile> is_body_fm(2,3,0,1)",THEN iffD1])
   apply(rule_tac iff_trans[OF body_abs[symmetric,of  u w]
                              is_body_iff_sats[where env="[_,_,u,w]"],simplified,symmetric])
  apply(simp_all)
  apply(rule_tac replacement_ax[where env="[u,w]",simplified])
    apply(simp_all add:arity_is_body_fm nat_simp_union is_body_fm_type body_def  )
  done 

lemma (in M_ZF_trans) proof_of_concept:
 "(##M)(u) \<Longrightarrow> (##M)(w) \<Longrightarrow> strong_replacement(##M, \<lambda>x y. x \<in> u \<and> y = {\<langle>w, x\<rangle>})"
  using proof_of_concept_aux body_def by simp

(*

 (##M)(f) \<Longrightarrow> (##M)(x) \<Longrightarrow> 
  
  strong_replacement(##M, \<lambda>y z. y \<in> f -`` {x} \<and> z = {\<langle>x, y\<rangle>})


*)

definition body_2 :: "[i,i,i,i] \<Rightarrow> o" where
  "body_2(f,x,y,z) \<equiv> y \<in> f -`` {x} \<and> z = {\<langle>x, y\<rangle>}"

relativize functional "body_2" "body_2_rel"
relationalize "body_2_rel" "is_body_2"

(* Do we have a reasonable order of arguments in is_body_2' ? *)
(* relativize_tm "x \<in> u \<and> y = {\<langle>w, x\<rangle>}" "is_body_2'"
 *)

lemma (in M_ZF_trans) body_2_abs:
  assumes "(##M)(ya)" "(##M)(z)" "(##M)(y)" "(##M)(x)"
  shows "is_body_2(##M,ya,z,y,x) \<longleftrightarrow> body_2(ya,z,y,x)"
  using assms unfolding body_2_def is_body_2_def 
  by (simp flip:setclass_iff)

synthesize "is_body_2" from_definition
arity_theorem for "is_body_2_fm"

lemma (in M_ZF_trans) proof_of_concept_aux2:
 "(##M)(u) \<Longrightarrow> (##M)(w) \<Longrightarrow> strong_replacement(##M, body_2(u,w))"
  apply(rule_tac strong_replacement_cong[
        where P="\<lambda> x y . M,[x,y,u,w] \<Turnstile> is_body_2_fm(2,3,0,1)",THEN iffD1])
   apply(rule_tac iff_trans[OF body_2_abs[symmetric,of  u w]
                              is_body_2_iff_sats[where env="[_,_,u,w]"],simplified,symmetric])
  apply(simp_all)
  apply(rule_tac replacement_ax[where env="[u,w]",simplified])
    apply(simp_all add:arity_is_body_2_fm nat_simp_union is_body_2_fm_type body_2_def  )
  done 

lemma (in M_ZF_trans) proof_of_concept2:
 "(##M)(f) \<Longrightarrow> (##M)(x) \<Longrightarrow> strong_replacement(##M, \<lambda> y z. y \<in> f -`` {x} \<and> z = {\<langle>x, y\<rangle>})"
  using proof_of_concept_aux2 body_2_def by simp


(* Separation *)

definition is_body_3 :: "[i\<Rightarrow>o,i,i,i,i] \<Rightarrow> o" where
  "is_body_3(N,A,f,r,x) \<equiv> x \<in> A \<longrightarrow> (\<exists>y[N]. \<exists>p[N]. is_apply(N, f, x, y) \<and> pair(N, y, x, p) \<and> p \<in> r)"

synthesize "is_body_3" from_definition
arity_theorem for "is_body_3_fm"

lemma (in M_ZF_trans) proof_of_concept_aux3:
 "(##M)(f) \<Longrightarrow> (##M)(r) \<Longrightarrow> (##M)(A) \<Longrightarrow> separation(##M, is_body_3(##M,A,f,r))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x,A,f,r] \<Turnstile> is_body_3_fm(1,2,3,0)",THEN iffD1])
   apply(rule_tac is_body_3_iff_sats[where env="[_,A,f,r]",symmetric])
  apply(simp_all)
  apply(rule_tac separation_ax[where env="[A,f,r]",simplified])
    apply(simp_all add:arity_is_body_3_fm nat_simp_union is_body_3_fm_type)
  done 

lemma (in M_ZF_trans) proof_of_concept3:
 "(##M)(f) \<Longrightarrow> (##M)(r) \<Longrightarrow> (##M)(A) \<Longrightarrow> separation
        (##M, \<lambda>x. x \<in> A \<longrightarrow> (\<exists>y[##M]. \<exists>p[##M]. is_apply(##M, f, x, y) \<and> pair(##M, y, x, p) \<and> p \<in> r))"
  using proof_of_concept_aux3 is_body_3_def by simp


(*. \<And>A r. (##M)(A) \<Longrightarrow>
           (##M)(r) \<Longrightarrow>
           separation
            (##M,
             \<lambda>x. x \<in> A \<longrightarrow>
                  \<not> (\<exists>y[##M].
                         \<exists>g[##M].
                            ordinal(##M, y) \<and>
                            (\<exists>my[##M].
                                \<exists>pxr[##M].
                                   membership(##M, y, my) \<and>
                                   pred_set(##M, A, x, r, pxr) \<and>
                                   order_isomorphism(##M, pxr, r, y, my, g))))
*)


definition is_body_4 :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_body_4(N,A,r,x) \<equiv> x \<in> A \<longrightarrow>
                  \<not> (\<exists>y[N].
                         \<exists>g[N].
                            ordinal(N, y) \<and>
                            (\<exists>my[N].
                                \<exists>pxr[N].
                                   membership(N, y, my) \<and>
                                   pred_set(N, A, x, r, pxr) \<and>
                                   order_isomorphism(N, pxr, r, y, my, g)))"

synthesize "is_body_4" from_definition
arity_theorem for "injection_fm"
arity_theorem for "surjection_fm"
arity_theorem for "bijection_fm"
arity_theorem for "order_isomorphism_fm"
arity_theorem for "pred_set_fm"
arity_theorem for "is_body_4_fm"

lemma (in M_ZF_trans) proof_of_concept_aux4:
 "(##M)(r) \<Longrightarrow> (##M)(A) \<Longrightarrow> separation(##M, is_body_4(##M,A,r))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x,A,r] \<Turnstile> is_body_4_fm(1,2,0)",THEN iffD1])
   apply(rule_tac is_body_4_iff_sats[where env="[_,A,r]",symmetric])
  apply(simp_all)
  apply(rule_tac separation_ax[where env="[A,r]",simplified])
    apply(simp_all add:arity_is_body_4_fm nat_simp_union is_body_4_fm_type)
  done 

lemma (in M_ZF_trans) proof_of_concept4:
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
  using proof_of_concept_aux4 is_body_4_def by simp



definition is_body_5 :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_body_5(N,A,r,a) \<equiv> \<exists>x[N].
                     \<exists>g[N].
                        \<exists>mx[N].
                           \<exists>par[N].
                              ordinal(N, x) \<and>
                              membership(N, x, mx) \<and>
                              pred_set(N, A, a, r, par) \<and> order_isomorphism(N, par, r, x, mx, g)"

synthesize "is_body_5" from_definition
arity_theorem for "is_body_5_fm"

lemma (in M_ZF_trans) proof_of_concept_aux5:
 "(##M)(r) \<Longrightarrow> (##M)(A) \<Longrightarrow> separation(##M, is_body_5(##M,A,r))"
  apply(rule_tac separation_cong[
        where P="\<lambda> x . M,[x,A,r] \<Turnstile> is_body_5_fm(1,2,0)",THEN iffD1])
   apply(rule_tac is_body_5_iff_sats[where env="[_,A,r]",symmetric])
  apply(simp_all)
  apply(rule_tac separation_ax[where env="[A,r]",simplified])
    apply(simp_all add:arity_is_body_5_fm nat_simp_union is_body_5_fm_type)
  done 

lemma (in M_ZF_trans) proof_of_concept5:
 "(##M)(f) \<Longrightarrow> (##M)(r) \<Longrightarrow> (##M)(A) \<Longrightarrow> separation
        (##M, \<lambda>a. \<exists>x[##M].
                     \<exists>g[##M].
                        \<exists>mx[##M].
                           \<exists>par[##M].
                              ordinal(##M, x) \<and>
                              membership(##M, x, mx) \<and>
                              pred_set(##M, A, a, r, par) \<and> order_isomorphism(##M, par, r, x, mx, g))"
  using proof_of_concept_aux5 is_body_5_def by simp

end