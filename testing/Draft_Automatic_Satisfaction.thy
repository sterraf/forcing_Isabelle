theory Draft_Automatic_Satisfaction
  imports
    "../src/Discipline_Function"
    "../src/Forcing_Data"
begin

(* Proof of concept of the proposal to automatize *)
definition body :: "[i,i,i,i] \<Rightarrow> o" where
  "body(u,w,x,y) \<equiv> x \<in> u \<and> y = {\<langle>w, x\<rangle>}"

relativize functional "body" "body_rel"
relationalize "body_rel" "is_body"

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

 (##M)(f) \<Longrightarrow> (##M)(x) \<Longrightarrow> strong_replacement(##M, \<lambda>y z. y \<in> f -`` {x} \<and> z = {\<langle>x, y\<rangle>})

*)

definition body_2 :: "[i,i,i,i] \<Rightarrow> o" where
  "body_2(f,x,y,z) \<equiv> y \<in> f -`` {x} \<and> z = {\<langle>x, y\<rangle>}"

relativize functional "body_2" "body_2_rel"
relationalize "body_2_rel" "is_body_2"

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
   apply(rule_tac iff_trans[OF body_2_abs[symmetric]
                              is_body_2_iff_sats[where env="[_,_,u,w]"],simplified,symmetric])
  apply(simp_all)
  apply(rule_tac replacement_ax[where env="[u,w]",simplified])
    apply(simp_all add:arity_is_body_2_fm nat_simp_union is_body_2_fm_type body_2_def  )
  done 

lemma (in M_ZF_trans) proof_of_concept2:
 "(##M)(f) \<Longrightarrow> (##M)(x) \<Longrightarrow> strong_replacement(##M, \<lambda> y z. y \<in> f -`` {x} \<and> z = {\<langle>x, y\<rangle>})"
  using proof_of_concept_aux2 body_2_def by simp


end