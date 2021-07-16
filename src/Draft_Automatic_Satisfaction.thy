theory Draft_Automatic_Satisfaction
  imports
    Cohen_Posets_Relative
begin

(* Proof of concept of the proposal to automatize *)
definition body :: "[i,i,i,i] \<Rightarrow> o" where
  "body(ya,z,y,x) \<equiv> ya \<in> y \<and> z = {\<langle>x, ya\<rangle>}"

relativize relational "body" "is_body"

lemma (in G_generic) body_abs:
  assumes "(##M)(ya)" "(##M)(z)" "(##M)(y)" "(##M)(x)"
  shows "is_body(##M,ya,z,y,x) \<longleftrightarrow> body(ya,z,y,x)"
  using assms unfolding body_def is_body_def 
  by simp

synthesize "is_body" from_definition
arity_theorem for "cons_fm"
arity_theorem for "is_body_fm"


lemma (in G_generic) proof_of_concept:
 "(##M)(u) \<Longrightarrow> (##M)(w) \<Longrightarrow> strong_replacement(##M, \<lambda>x y. x \<in> u \<and> y = {\<langle>w, x\<rangle>})"
  using iff_trans[OF body_abs[symmetric] is_body_iff_sats[of 0 "[_,_,u,w]" _ 1 _ 2 _ 3],simplified]
    replacement_ax[of "is_body_fm(0,1,2,3)" "[u,w]",simplified]
    strong_replacement_cong[THEN iffD1]
  apply (simp add:arity_is_body_fm nat_simp_union is_body_fm_type )
  oops
