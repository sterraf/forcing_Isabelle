(*  
    This file is completely based on L_axioms.thy and Internalize.thy 
    by Lawrence C Paulson.
*)

theory Internalizations 
  imports 
    "~~/src/ZF/Constructible/Formula"
    Relative  Datatype_absolute 
begin

subsection\<open>Internalized Formulas for some Set-Theoretic Concepts\<close>

subsubsection\<open>Some numbers to help write de Bruijn indices\<close>

abbreviation
  digit3 :: i   ("3") where "3 == succ(2)"

abbreviation
  digit4 :: i   ("4") where "4 == succ(3)"

abbreviation
  digit5 :: i   ("5") where "5 == succ(4)"

abbreviation
  digit6 :: i   ("6") where "6 == succ(5)"

abbreviation
  digit7 :: i   ("7") where "7 == succ(6)"

abbreviation
  digit8 :: i   ("8") where "8 == succ(7)"

abbreviation
  digit9 :: i   ("9") where "9 == succ(8)"


subsubsection\<open>The Empty Set, Internalized\<close>

definition
  empty_fm :: "i=>i" where
    "empty_fm(x) == Forall(Neg(Member(0,succ(x))))"

lemma empty_type [TC]:
     "x \<in> nat ==> empty_fm(x) \<in> formula"
by (simp add: empty_fm_def)

lemma sats_empty_fm [simp]:
   "[| x \<in> nat; env \<in> list(A)|]
    ==> sats(A, empty_fm(x), env) \<longleftrightarrow> empty(##A, nth(x,env))"
by (simp add: empty_fm_def empty_def)

lemma empty_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; env \<in> list(A)|]
       ==> empty(##A, x) \<longleftrightarrow> sats(A, empty_fm(i), env)"
by simp

text\<open>Not used.  But maybe useful?\<close>
lemma Transset_sats_empty_fm_eq_0:
   "[| n \<in> nat; env \<in> list(A); Transset(A)|]
    ==> sats(A, empty_fm(n), env) \<longleftrightarrow> nth(n,env) = 0"
apply (simp add: empty_fm_def empty_def Transset_def, auto)
apply (case_tac "n < length(env)")
apply (frule nth_type, assumption+, blast)
apply (simp_all add: not_lt_iff_le nth_eq_0)
done


subsubsection\<open>Unordered Pairs, Internalized\<close>

definition
  upair_fm :: "[i,i,i]=>i" where
    "upair_fm(x,y,z) ==
       And(Member(x,z),
           And(Member(y,z),
               Forall(Implies(Member(0,succ(z)),
                              Or(Equal(0,succ(x)), Equal(0,succ(y)))))))"

lemma upair_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> upair_fm(x,y,z) \<in> formula"
by (simp add: upair_fm_def)

lemma sats_upair_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, upair_fm(x,y,z), env) \<longleftrightarrow>
            upair(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: upair_fm_def upair_def)

lemma upair_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> upair(##A, x, y, z) \<longleftrightarrow> sats(A, upair_fm(i,j,k), env)"
by (simp)

text\<open>Useful? At least it refers to "real" unordered pairs\<close>
lemma sats_upair_fm2 [simp]:
   "[| x \<in> nat; y \<in> nat; z < length(env); env \<in> list(A); Transset(A)|]
    ==> sats(A, upair_fm(x,y,z), env) \<longleftrightarrow>
        nth(z,env) = {nth(x,env), nth(y,env)}"
apply (frule lt_length_in_nat, assumption)
apply (simp add: upair_fm_def Transset_def, auto)
apply (blast intro: nth_type)
done

subsubsection\<open>Ordered pairs, Internalized\<close>

definition
  pair_fm :: "[i,i,i]=>i" where
    "pair_fm(x,y,z) ==
       Exists(And(upair_fm(succ(x),succ(x),0),
              Exists(And(upair_fm(succ(succ(x)),succ(succ(y)),0),
                         upair_fm(1,0,succ(succ(z)))))))"

lemma pair_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> pair_fm(x,y,z) \<in> formula"
by (simp add: pair_fm_def)

lemma sats_pair_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, pair_fm(x,y,z), env) \<longleftrightarrow>
        pair(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: pair_fm_def pair_def)

lemma pair_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> pair(##A, x, y, z) \<longleftrightarrow> sats(A, pair_fm(i,j,k), env)"
by simp


subsubsection\<open>Binary Unions, Internalized\<close>

definition
  union_fm :: "[i,i,i]=>i" where
    "union_fm(x,y,z) ==
       Forall(Iff(Member(0,succ(z)),
                  Or(Member(0,succ(x)),Member(0,succ(y)))))"

lemma union_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> union_fm(x,y,z) \<in> formula"
by (simp add: union_fm_def)

lemma sats_union_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, union_fm(x,y,z), env) \<longleftrightarrow>
        union(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: union_fm_def union_def)

lemma union_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> union(##A, x, y, z) \<longleftrightarrow> sats(A, union_fm(i,j,k), env)"
by (simp)


subsubsection\<open>Set ``Cons,'' Internalized\<close>

definition
  cons_fm :: "[i,i,i]=>i" where
    "cons_fm(x,y,z) ==
       Exists(And(upair_fm(succ(x),succ(x),0),
                  union_fm(0,succ(y),succ(z))))"


lemma cons_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> cons_fm(x,y,z) \<in> formula"
by (simp add: cons_fm_def)

lemma sats_cons_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, cons_fm(x,y,z), env) \<longleftrightarrow>
        is_cons(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: cons_fm_def is_cons_def)

lemma cons_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> is_cons(##A, x, y, z) \<longleftrightarrow> sats(A, cons_fm(i,j,k), env)"
by simp


subsubsection\<open>Successor Function, Internalized\<close>

definition
  succ_fm :: "[i,i]=>i" where
    "succ_fm(x,y) == cons_fm(x,x,y)"

lemma succ_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> succ_fm(x,y) \<in> formula"
by (simp add: succ_fm_def)

lemma sats_succ_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, succ_fm(x,y), env) \<longleftrightarrow>
        successor(##A, nth(x,env), nth(y,env))"
by (simp add: succ_fm_def successor_def)

lemma successor_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> successor(##A, x, y) \<longleftrightarrow> sats(A, succ_fm(i,j), env)"
by simp


subsubsection\<open>The Number 1, Internalized\<close>

(* "number1(M,a) == (\<exists>x[M]. empty(M,x) & successor(M,x,a))" *)
definition
  number1_fm :: "i=>i" where
    "number1_fm(a) == Exists(And(empty_fm(0), succ_fm(0,succ(a))))"

lemma number1_type [TC]:
     "x \<in> nat ==> number1_fm(x) \<in> formula"
by (simp add: number1_fm_def)

lemma sats_number1_fm [simp]:
   "[| x \<in> nat; env \<in> list(A)|]
    ==> sats(A, number1_fm(x), env) \<longleftrightarrow> number1(##A, nth(x,env))"
by (simp add: number1_fm_def number1_def)

lemma number1_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; env \<in> list(A)|]
       ==> number1(##A, x) \<longleftrightarrow> sats(A, number1_fm(i), env)"
by simp


subsubsection\<open>Big Union, Internalized\<close>

(*  "big_union(M,A,z) == \<forall>x[M]. x \<in> z \<longleftrightarrow> (\<exists>y[M]. y\<in>A & x \<in> y)" *)
definition
  big_union_fm :: "[i,i]=>i" where
    "big_union_fm(A,z) ==
       Forall(Iff(Member(0,succ(z)),
                  Exists(And(Member(0,succ(succ(A))), Member(1,0)))))"

lemma big_union_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> big_union_fm(x,y) \<in> formula"
by (simp add: big_union_fm_def)

lemma sats_big_union_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, big_union_fm(x,y), env) \<longleftrightarrow>
        big_union(##A, nth(x,env), nth(y,env))"
by (simp add: big_union_fm_def big_union_def)

lemma big_union_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> big_union(##A, x, y) \<longleftrightarrow> sats(A, big_union_fm(i,j), env)"
by simp

subsubsection\<open>Variants of Satisfaction Definitions for Ordinals, etc.\<close>

text\<open>The \<open>sats\<close> theorems below are standard versions of the ones proved
in theory \<open>Formula\<close>.  They relate elements of type @{term formula} to
relativized concepts such as @{term subset} or @{term ordinal} rather than to
real concepts such as @{term Ord}.  Now that we have instantiated the locale
\<open>M_trivial\<close>, we no longer require the earlier versions.\<close>

lemma sats_subset_fm':
   "[|x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, subset_fm(x,y), env) \<longleftrightarrow> subset(##A, nth(x,env), nth(y,env))"
by (simp add: subset_fm_def Relative.subset_def)

lemma sats_transset_fm':
   "[|x \<in> nat; env \<in> list(A)|]
    ==> sats(A, transset_fm(x), env) \<longleftrightarrow> transitive_set(##A, nth(x,env))"
by (simp add: sats_subset_fm' transset_fm_def transitive_set_def)

lemma sats_ordinal_fm':
   "[|x \<in> nat; env \<in> list(A)|]
    ==> sats(A, ordinal_fm(x), env) \<longleftrightarrow> ordinal(##A,nth(x,env))"
by (simp add: sats_transset_fm' ordinal_fm_def ordinal_def)

lemma ordinal_iff_sats:
      "[| nth(i,env) = x;  i \<in> nat; env \<in> list(A)|]
       ==> ordinal(##A, x) \<longleftrightarrow> sats(A, ordinal_fm(i), env)"
by (simp add: sats_ordinal_fm')


subsubsection\<open>Membership Relation, Internalized\<close>

definition
  Memrel_fm :: "[i,i]=>i" where
    "Memrel_fm(A,r) ==
       Forall(Iff(Member(0,succ(r)),
                  Exists(And(Member(0,succ(succ(A))),
                             Exists(And(Member(0,succ(succ(succ(A)))),
                                        And(Member(1,0),
                                            pair_fm(1,0,2))))))))"

lemma Memrel_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> Memrel_fm(x,y) \<in> formula"
by (simp add: Memrel_fm_def)

lemma sats_Memrel_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, Memrel_fm(x,y), env) \<longleftrightarrow>
        membership(##A, nth(x,env), nth(y,env))"
by (simp add: Memrel_fm_def membership_def)

lemma Memrel_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> membership(##A, x, y) \<longleftrightarrow> sats(A, Memrel_fm(i,j), env)"
by simp

subsubsection\<open>Predecessor Set, Internalized\<close>

definition
  pred_set_fm :: "[i,i,i,i]=>i" where
    "pred_set_fm(A,x,r,B) ==
       Forall(Iff(Member(0,succ(B)),
                  Exists(And(Member(0,succ(succ(r))),
                             And(Member(1,succ(succ(A))),
                                 pair_fm(1,succ(succ(x)),0))))))"


lemma pred_set_type [TC]:
     "[| A \<in> nat; x \<in> nat; r \<in> nat; B \<in> nat |]
      ==> pred_set_fm(A,x,r,B) \<in> formula"
by (simp add: pred_set_fm_def)

lemma sats_pred_set_fm [simp]:
   "[| U \<in> nat; x \<in> nat; r \<in> nat; B \<in> nat; env \<in> list(A)|]
    ==> sats(A, pred_set_fm(U,x,r,B), env) \<longleftrightarrow>
        pred_set(##A, nth(U,env), nth(x,env), nth(r,env), nth(B,env))"
by (simp add: pred_set_fm_def pred_set_def)

lemma pred_set_iff_sats:
      "[| nth(i,env) = U; nth(j,env) = x; nth(k,env) = r; nth(l,env) = B;
          i \<in> nat; j \<in> nat; k \<in> nat; l \<in> nat; env \<in> list(A)|]
       ==> pred_set(##A,U,x,r,B) \<longleftrightarrow> sats(A, pred_set_fm(i,j,k,l), env)"
by (simp) 



subsubsection\<open>Domain of a Relation, Internalized\<close>

(* "is_domain(M,r,z) ==
        \<forall>x[M]. (x \<in> z \<longleftrightarrow> (\<exists>w[M]. w\<in>r & (\<exists>y[M]. pair(M,x,y,w))))" *)
definition
  domain_fm :: "[i,i]=>i" where
    "domain_fm(r,z) ==
       Forall(Iff(Member(0,succ(z)),
                  Exists(And(Member(0,succ(succ(r))),
                             Exists(pair_fm(2,0,1))))))"

lemma domain_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> domain_fm(x,y) \<in> formula"
by (simp add: domain_fm_def)

lemma sats_domain_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, domain_fm(x,y), env) \<longleftrightarrow>
        is_domain(##A, nth(x,env), nth(y,env))"
by (simp add: domain_fm_def is_domain_def)

lemma domain_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> is_domain(##A, x, y) \<longleftrightarrow> sats(A, domain_fm(i,j), env)"
by simp


subsubsection\<open>Range of a Relation, Internalized\<close>

(* "is_range(M,r,z) ==
        \<forall>y[M]. (y \<in> z \<longleftrightarrow> (\<exists>w[M]. w\<in>r & (\<exists>x[M]. pair(M,x,y,w))))" *)
definition
  range_fm :: "[i,i]=>i" where
    "range_fm(r,z) ==
       Forall(Iff(Member(0,succ(z)),
                  Exists(And(Member(0,succ(succ(r))),
                             Exists(pair_fm(0,2,1))))))"

lemma range_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> range_fm(x,y) \<in> formula"
by (simp add: range_fm_def)

lemma sats_range_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, range_fm(x,y), env) \<longleftrightarrow>
        is_range(##A, nth(x,env), nth(y,env))"
by (simp add: range_fm_def is_range_def)

lemma range_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> is_range(##A, x, y) \<longleftrightarrow> sats(A, range_fm(i,j), env)"
by simp


subsubsection\<open>Field of a Relation, Internalized\<close>

(* "is_field(M,r,z) ==
        \<exists>dr[M]. is_domain(M,r,dr) &
            (\<exists>rr[M]. is_range(M,r,rr) & union(M,dr,rr,z))" *)
definition
  field_fm :: "[i,i]=>i" where
    "field_fm(r,z) ==
       Exists(And(domain_fm(succ(r),0),
              Exists(And(range_fm(succ(succ(r)),0),
                         union_fm(1,0,succ(succ(z)))))))"

lemma field_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> field_fm(x,y) \<in> formula"
by (simp add: field_fm_def)

lemma sats_field_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, field_fm(x,y), env) \<longleftrightarrow>
        is_field(##A, nth(x,env), nth(y,env))"
by (simp add: field_fm_def is_field_def)

lemma field_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> is_field(##A, x, y) \<longleftrightarrow> sats(A, field_fm(i,j), env)"
by simp


subsubsection\<open>Image under a Relation, Internalized\<close>

(* "image(M,r,A,z) ==
        \<forall>y[M]. (y \<in> z \<longleftrightarrow> (\<exists>w[M]. w\<in>r & (\<exists>x[M]. x\<in>A & pair(M,x,y,w))))" *)
definition
  image_fm :: "[i,i,i]=>i" where
    "image_fm(r,A,z) ==
       Forall(Iff(Member(0,succ(z)),
                  Exists(And(Member(0,succ(succ(r))),
                             Exists(And(Member(0,succ(succ(succ(A)))),
                                        pair_fm(0,2,1)))))))"

lemma image_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> image_fm(x,y,z) \<in> formula"
by (simp add: image_fm_def)

lemma sats_image_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, image_fm(x,y,z), env) \<longleftrightarrow>
        image(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: image_fm_def Relative.image_def)

lemma image_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> image(##A, x, y, z) \<longleftrightarrow> sats(A, image_fm(i,j,k), env)"
by (simp) 


subsubsection\<open>Pre-Image under a Relation, Internalized\<close>

(* "pre_image(M,r,A,z) ==
        \<forall>x[M]. x \<in> z \<longleftrightarrow> (\<exists>w[M]. w\<in>r & (\<exists>y[M]. y\<in>A & pair(M,x,y,w)))" *)
definition
  pre_image_fm :: "[i,i,i]=>i" where
    "pre_image_fm(r,A,z) ==
       Forall(Iff(Member(0,succ(z)),
                  Exists(And(Member(0,succ(succ(r))),
                             Exists(And(Member(0,succ(succ(succ(A)))),
                                        pair_fm(2,0,1)))))))"

lemma pre_image_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> pre_image_fm(x,y,z) \<in> formula"
by (simp add: pre_image_fm_def)

lemma sats_pre_image_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, pre_image_fm(x,y,z), env) \<longleftrightarrow>
        pre_image(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: pre_image_fm_def Relative.pre_image_def)

lemma pre_image_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> pre_image(##A, x, y, z) \<longleftrightarrow> sats(A, pre_image_fm(i,j,k), env)"
by (simp)


subsubsection\<open>Function Application, Internalized\<close>

(* "fun_apply(M,f,x,y) ==
        (\<exists>xs[M]. \<exists>fxs[M].
         upair(M,x,x,xs) & image(M,f,xs,fxs) & big_union(M,fxs,y))" *)
definition
  fun_apply_fm :: "[i,i,i]=>i" where
    "fun_apply_fm(f,x,y) ==
       Exists(Exists(And(upair_fm(succ(succ(x)), succ(succ(x)), 1),
                         And(image_fm(succ(succ(f)), 1, 0),
                             big_union_fm(0,succ(succ(y)))))))"

lemma fun_apply_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> fun_apply_fm(x,y,z) \<in> formula"
by (simp add: fun_apply_fm_def)

lemma sats_fun_apply_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, fun_apply_fm(x,y,z), env) \<longleftrightarrow>
        fun_apply(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: fun_apply_fm_def fun_apply_def)

lemma fun_apply_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> fun_apply(##A, x, y, z) \<longleftrightarrow> sats(A, fun_apply_fm(i,j,k), env)"
by simp


subsubsection\<open>The Concept of Relation, Internalized\<close>

(* "is_relation(M,r) ==
        (\<forall>z[M]. z\<in>r \<longrightarrow> (\<exists>x[M]. \<exists>y[M]. pair(M,x,y,z)))" *)
definition
  relation_fm :: "i=>i" where
    "relation_fm(r) ==
       Forall(Implies(Member(0,succ(r)), Exists(Exists(pair_fm(1,0,2)))))"

lemma relation_type [TC]:
     "[| x \<in> nat |] ==> relation_fm(x) \<in> formula"
by (simp add: relation_fm_def)

lemma sats_relation_fm [simp]:
   "[| x \<in> nat; env \<in> list(A)|]
    ==> sats(A, relation_fm(x), env) \<longleftrightarrow> is_relation(##A, nth(x,env))"
by (simp add: relation_fm_def is_relation_def)

lemma relation_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; env \<in> list(A)|]
       ==> is_relation(##A, x) \<longleftrightarrow> sats(A, relation_fm(i), env)"
by simp


subsubsection\<open>The Concept of Function, Internalized\<close>

(* "is_function(M,r) ==
        \<forall>x[M]. \<forall>y[M]. \<forall>y'[M]. \<forall>p[M]. \<forall>p'[M].
           pair(M,x,y,p) \<longrightarrow> pair(M,x,y',p') \<longrightarrow> p\<in>r \<longrightarrow> p'\<in>r \<longrightarrow> y=y'" *)
definition
  function_fm :: "i=>i" where
    "function_fm(r) ==
       Forall(Forall(Forall(Forall(Forall(
         Implies(pair_fm(4,3,1),
                 Implies(pair_fm(4,2,0),
                         Implies(Member(1,r#+5),
                                 Implies(Member(0,r#+5), Equal(3,2))))))))))"

lemma function_type [TC]:
     "[| x \<in> nat |] ==> function_fm(x) \<in> formula"
by (simp add: function_fm_def)

lemma sats_function_fm [simp]:
   "[| x \<in> nat; env \<in> list(A)|]
    ==> sats(A, function_fm(x), env) \<longleftrightarrow> is_function(##A, nth(x,env))"
by (simp add: function_fm_def is_function_def)

lemma is_function_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; env \<in> list(A)|]
       ==> is_function(##A, x) \<longleftrightarrow> sats(A, function_fm(i), env)"
by simp


subsubsection\<open>Typed Functions, Internalized\<close>

(* "typed_function(M,A,B,r) ==
        is_function(M,r) & is_relation(M,r) & is_domain(M,r,A) &
        (\<forall>u[M]. u\<in>r \<longrightarrow> (\<forall>x[M]. \<forall>y[M]. pair(M,x,y,u) \<longrightarrow> y\<in>B))" *)

definition
  typed_function_fm :: "[i,i,i]=>i" where
    "typed_function_fm(A,B,r) ==
       And(function_fm(r),
         And(relation_fm(r),
           And(domain_fm(r,A),
             Forall(Implies(Member(0,succ(r)),
                  Forall(Forall(Implies(pair_fm(1,0,2),Member(0,B#+3)))))))))"

lemma typed_function_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> typed_function_fm(x,y,z) \<in> formula"
by (simp add: typed_function_fm_def)

lemma sats_typed_function_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, typed_function_fm(x,y,z), env) \<longleftrightarrow>
        typed_function(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: typed_function_fm_def typed_function_def)

lemma typed_function_iff_sats:
  "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
      i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
   ==> typed_function(##A, x, y, z) \<longleftrightarrow> sats(A, typed_function_fm(i,j,k), env)"
by simp

lemmas function_iff_sats =
        empty_iff_sats number1_iff_sats
        upair_iff_sats pair_iff_sats union_iff_sats
        big_union_iff_sats cons_iff_sats successor_iff_sats
        fun_apply_iff_sats  Memrel_iff_sats
        pred_set_iff_sats domain_iff_sats range_iff_sats field_iff_sats
        image_iff_sats pre_image_iff_sats
        relation_iff_sats is_function_iff_sats


subsubsection\<open>Composition of Relations, Internalized\<close>

(* "composition(M,r,s,t) ==
        \<forall>p[M]. p \<in> t \<longleftrightarrow>
               (\<exists>x[M]. \<exists>y[M]. \<exists>z[M]. \<exists>xy[M]. \<exists>yz[M].
                pair(M,x,z,p) & pair(M,x,y,xy) & pair(M,y,z,yz) &
                xy \<in> s & yz \<in> r)" *)
definition
  composition_fm :: "[i,i,i]=>i" where
  "composition_fm(r,s,t) ==
     Forall(Iff(Member(0,succ(t)),
             Exists(Exists(Exists(Exists(Exists(
              And(pair_fm(4,2,5),
               And(pair_fm(4,3,1),
                And(pair_fm(3,2,0),
                 And(Member(1,s#+6), Member(0,r#+6))))))))))))"

lemma composition_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> composition_fm(x,y,z) \<in> formula"
by (simp add: composition_fm_def)

lemma sats_composition_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, composition_fm(x,y,z), env) \<longleftrightarrow>
        composition(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: composition_fm_def composition_def)

lemma composition_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> composition(##A, x, y, z) \<longleftrightarrow> sats(A, composition_fm(i,j,k), env)"
by simp


subsubsection\<open>Injections, Internalized\<close>

(* "injection(M,A,B,f) ==
        typed_function(M,A,B,f) &
        (\<forall>x[M]. \<forall>x'[M]. \<forall>y[M]. \<forall>p[M]. \<forall>p'[M].
          pair(M,x,y,p) \<longrightarrow> pair(M,x',y,p') \<longrightarrow> p\<in>f \<longrightarrow> p'\<in>f \<longrightarrow> x=x')" *)
definition
  injection_fm :: "[i,i,i]=>i" where
  "injection_fm(A,B,f) ==
    And(typed_function_fm(A,B,f),
       Forall(Forall(Forall(Forall(Forall(
         Implies(pair_fm(4,2,1),
                 Implies(pair_fm(3,2,0),
                         Implies(Member(1,f#+5),
                                 Implies(Member(0,f#+5), Equal(4,3)))))))))))"


lemma injection_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> injection_fm(x,y,z) \<in> formula"
by (simp add: injection_fm_def)

lemma sats_injection_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, injection_fm(x,y,z), env) \<longleftrightarrow>
        injection(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: injection_fm_def injection_def)

lemma injection_iff_sats:
  "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
      i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
   ==> injection(##A, x, y, z) \<longleftrightarrow> sats(A, injection_fm(i,j,k), env)"
by simp


subsubsection\<open>Surjections, Internalized\<close>

(*  surjection :: "[i=>o,i,i,i] => o"
    "surjection(M,A,B,f) ==
        typed_function(M,A,B,f) &
        (\<forall>y[M]. y\<in>B \<longrightarrow> (\<exists>x[M]. x\<in>A & fun_apply(M,f,x,y)))" *)
definition
  surjection_fm :: "[i,i,i]=>i" where
  "surjection_fm(A,B,f) ==
    And(typed_function_fm(A,B,f),
       Forall(Implies(Member(0,succ(B)),
                      Exists(And(Member(0,succ(succ(A))),
                                 fun_apply_fm(succ(succ(f)),0,1))))))"

lemma surjection_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> surjection_fm(x,y,z) \<in> formula"
by (simp add: surjection_fm_def)

lemma sats_surjection_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, surjection_fm(x,y,z), env) \<longleftrightarrow>
        surjection(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: surjection_fm_def surjection_def)

lemma surjection_iff_sats:
  "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
      i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
   ==> surjection(##A, x, y, z) \<longleftrightarrow> sats(A, surjection_fm(i,j,k), env)"
by simp


subsubsection\<open>Bijections, Internalized\<close>

(*   bijection :: "[i=>o,i,i,i] => o"
    "bijection(M,A,B,f) == injection(M,A,B,f) & surjection(M,A,B,f)" *)
definition
  bijection_fm :: "[i,i,i]=>i" where
  "bijection_fm(A,B,f) == And(injection_fm(A,B,f), surjection_fm(A,B,f))"

lemma bijection_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> bijection_fm(x,y,z) \<in> formula"
by (simp add: bijection_fm_def)

lemma sats_bijection_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, bijection_fm(x,y,z), env) \<longleftrightarrow>
        bijection(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: bijection_fm_def bijection_def)

lemma bijection_iff_sats:
  "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
      i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
   ==> bijection(##A, x, y, z) \<longleftrightarrow> sats(A, bijection_fm(i,j,k), env)"
by simp


subsubsection\<open>Restriction of a Relation, Internalized\<close>


(* "restriction(M,r,A,z) ==
        \<forall>x[M]. x \<in> z \<longleftrightarrow> (x \<in> r & (\<exists>u[M]. u\<in>A & (\<exists>v[M]. pair(M,u,v,x))))" *)
definition
  restriction_fm :: "[i,i,i]=>i" where
    "restriction_fm(r,A,z) ==
       Forall(Iff(Member(0,succ(z)),
                  And(Member(0,succ(r)),
                      Exists(And(Member(0,succ(succ(A))),
                                 Exists(pair_fm(1,0,2)))))))"

lemma restriction_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> restriction_fm(x,y,z) \<in> formula"
by (simp add: restriction_fm_def)

lemma sats_restriction_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, restriction_fm(x,y,z), env) \<longleftrightarrow>
        restriction(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: restriction_fm_def restriction_def)

lemma restriction_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> restriction(##A, x, y, z) \<longleftrightarrow> sats(A, restriction_fm(i,j,k), env)"
by simp

subsubsection\<open>Order-Isomorphisms, Internalized\<close>

(*  order_isomorphism :: "[i=>o,i,i,i,i,i] => o"
   "order_isomorphism(M,A,r,B,s,f) ==
        bijection(M,A,B,f) &
        (\<forall>x[M]. x\<in>A \<longrightarrow> (\<forall>y[M]. y\<in>A \<longrightarrow>
          (\<forall>p[M]. \<forall>fx[M]. \<forall>fy[M]. \<forall>q[M].
            pair(M,x,y,p) \<longrightarrow> fun_apply(M,f,x,fx) \<longrightarrow> fun_apply(M,f,y,fy) \<longrightarrow>
            pair(M,fx,fy,q) \<longrightarrow> (p\<in>r \<longleftrightarrow> q\<in>s))))"
  *)

definition
  order_isomorphism_fm :: "[i,i,i,i,i]=>i" where
 "order_isomorphism_fm(A,r,B,s,f) ==
   And(bijection_fm(A,B,f),
     Forall(Implies(Member(0,succ(A)),
       Forall(Implies(Member(0,succ(succ(A))),
         Forall(Forall(Forall(Forall(
           Implies(pair_fm(5,4,3),
             Implies(fun_apply_fm(f#+6,5,2),
               Implies(fun_apply_fm(f#+6,4,1),
                 Implies(pair_fm(2,1,0),
                   Iff(Member(3,r#+6), Member(0,s#+6)))))))))))))))"

lemma order_isomorphism_type [TC]:
     "[| A \<in> nat; r \<in> nat; B \<in> nat; s \<in> nat; f \<in> nat |]
      ==> order_isomorphism_fm(A,r,B,s,f) \<in> formula"
by (simp add: order_isomorphism_fm_def)

lemma sats_order_isomorphism_fm [simp]:
   "[| U \<in> nat; r \<in> nat; B \<in> nat; s \<in> nat; f \<in> nat; env \<in> list(A)|]
    ==> sats(A, order_isomorphism_fm(U,r,B,s,f), env) \<longleftrightarrow>
        order_isomorphism(##A, nth(U,env), nth(r,env), nth(B,env),
                               nth(s,env), nth(f,env))"
by (simp add: order_isomorphism_fm_def order_isomorphism_def)

lemma order_isomorphism_iff_sats:
  "[| nth(i,env) = U; nth(j,env) = r; nth(k,env) = B; nth(j',env) = s;
      nth(k',env) = f;
      i \<in> nat; j \<in> nat; k \<in> nat; j' \<in> nat; k' \<in> nat; env \<in> list(A)|]
   ==> order_isomorphism(##A,U,r,B,s,f) \<longleftrightarrow>
       sats(A, order_isomorphism_fm(i,j,k,j',k'), env)"
by simp

subsubsection\<open>Limit Ordinals, Internalized\<close>

text\<open>A limit ordinal is a non-empty, successor-closed ordinal\<close>

(* "limit_ordinal(M,a) ==
        ordinal(M,a) & ~ empty(M,a) &
        (\<forall>x[M]. x\<in>a \<longrightarrow> (\<exists>y[M]. y\<in>a & successor(M,x,y)))" *)

definition
  limit_ordinal_fm :: "i=>i" where
    "limit_ordinal_fm(x) ==
        And(ordinal_fm(x),
            And(Neg(empty_fm(x)),
                Forall(Implies(Member(0,succ(x)),
                               Exists(And(Member(0,succ(succ(x))),
                                          succ_fm(1,0)))))))"

lemma limit_ordinal_type [TC]:
     "x \<in> nat ==> limit_ordinal_fm(x) \<in> formula"
by (simp add: limit_ordinal_fm_def)

lemma sats_limit_ordinal_fm [simp]:
   "[| x \<in> nat; env \<in> list(A)|]
    ==> sats(A, limit_ordinal_fm(x), env) \<longleftrightarrow> limit_ordinal(##A, nth(x,env))"
by (simp add: limit_ordinal_fm_def limit_ordinal_def sats_ordinal_fm')

lemma limit_ordinal_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; env \<in> list(A)|]
       ==> limit_ordinal(##A, x) \<longleftrightarrow> sats(A, limit_ordinal_fm(i), env)"
by simp

subsubsection\<open>Finite Ordinals: The Predicate ``Is A Natural Number''\<close>

(*     "finite_ordinal(M,a) == 
        ordinal(M,a) & ~ limit_ordinal(M,a) & 
        (\<forall>x[M]. x\<in>a \<longrightarrow> ~ limit_ordinal(M,x))" *)
definition
  finite_ordinal_fm :: "i=>i" where
    "finite_ordinal_fm(x) ==
       And(ordinal_fm(x),
          And(Neg(limit_ordinal_fm(x)),
           Forall(Implies(Member(0,succ(x)),
                          Neg(limit_ordinal_fm(0))))))"

lemma finite_ordinal_type [TC]:
     "x \<in> nat ==> finite_ordinal_fm(x) \<in> formula"
by (simp add: finite_ordinal_fm_def)

lemma sats_finite_ordinal_fm [simp]:
   "[| x \<in> nat; env \<in> list(A)|]
    ==> sats(A, finite_ordinal_fm(x), env) \<longleftrightarrow> finite_ordinal(##A, nth(x,env))"
by (simp add: finite_ordinal_fm_def sats_ordinal_fm' finite_ordinal_def)

lemma finite_ordinal_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; env \<in> list(A)|]
       ==> finite_ordinal(##A, x) \<longleftrightarrow> sats(A, finite_ordinal_fm(i), env)"
by simp


subsubsection\<open>Omega: The Set of Natural Numbers\<close>

(* omega(M,a) == limit_ordinal(M,a) & (\<forall>x[M]. x\<in>a \<longrightarrow> ~ limit_ordinal(M,x)) *)
definition
  omega_fm :: "i=>i" where
    "omega_fm(x) ==
       And(limit_ordinal_fm(x),
           Forall(Implies(Member(0,succ(x)),
                          Neg(limit_ordinal_fm(0)))))"

lemma omega_type [TC]:
     "x \<in> nat ==> omega_fm(x) \<in> formula"
by (simp add: omega_fm_def)

lemma sats_omega_fm [simp]:
   "[| x \<in> nat; env \<in> list(A)|]
    ==> sats(A, omega_fm(x), env) \<longleftrightarrow> omega(##A, nth(x,env))"
by (simp add: omega_fm_def omega_def)

lemma omega_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; env \<in> list(A)|]
       ==> omega(##A, x) \<longleftrightarrow> sats(A, omega_fm(i), env)"
by simp

lemmas fun_plus_iff_sats =
        typed_function_iff_sats composition_iff_sats
        injection_iff_sats surjection_iff_sats
        bijection_iff_sats restriction_iff_sats
        order_isomorphism_iff_sats finite_ordinal_iff_sats
        ordinal_iff_sats limit_ordinal_iff_sats omega_iff_sats

(*  
    Here starts the fraction from Internalize.thy
*)

subsection\<open>Internalized Forms of Data Structuring Operators\<close>

subsubsection\<open>The Formula @{term is_Inl}, Internalized\<close>

(*  is_Inl(M,a,z) == \<exists>zero[M]. empty(M,zero) & pair(M,zero,a,z) *)
definition
  Inl_fm :: "[i,i]=>i" where
    "Inl_fm(a,z) == Exists(And(empty_fm(0), pair_fm(0,succ(a),succ(z))))"

lemma Inl_type [TC]:
     "[| x \<in> nat; z \<in> nat |] ==> Inl_fm(x,z) \<in> formula"
by (simp add: Inl_fm_def)

lemma sats_Inl_fm [simp]:
   "[| x \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, Inl_fm(x,z), env) \<longleftrightarrow> is_Inl(##A, nth(x,env), nth(z,env))"
   
by (simp add: Inl_fm_def is_Inl_def)

lemma Inl_iff_sats:
      "[| nth(i,env) = x; nth(k,env) = z;
          i \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> is_Inl(##A, x, z) \<longleftrightarrow> sats(A, Inl_fm(i,k), env)"
by simp


subsubsection\<open>The Formula @{term is_Inr}, Internalized\<close>

(*  is_Inr(M,a,z) == \<exists>n1[M]. number1(M,n1) & pair(M,n1,a,z) *)
definition
  Inr_fm :: "[i,i]=>i" where
    "Inr_fm(a,z) == Exists(And(number1_fm(0), pair_fm(0,succ(a),succ(z))))"

lemma Inr_type [TC]:
     "[| x \<in> nat; z \<in> nat |] ==> Inr_fm(x,z) \<in> formula"
by (simp add: Inr_fm_def)

lemma sats_Inr_fm [simp]:
   "[| x \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, Inr_fm(x,z), env) \<longleftrightarrow> is_Inr(##A, nth(x,env), nth(z,env))"
by (simp add: Inr_fm_def is_Inr_def)

lemma Inr_iff_sats:
      "[| nth(i,env) = x; nth(k,env) = z;
          i \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> is_Inr(##A, x, z) \<longleftrightarrow> sats(A, Inr_fm(i,k), env)"
by simp


subsubsection\<open>The Formula @{term is_Nil}, Internalized\<close>

(* is_Nil(M,xs) == \<exists>zero[M]. empty(M,zero) & is_Inl(M,zero,xs) *)

definition
  Nil_fm :: "i=>i" where
    "Nil_fm(x) == Exists(And(empty_fm(0), Inl_fm(0,succ(x))))"

lemma Nil_type [TC]: "x \<in> nat ==> Nil_fm(x) \<in> formula"
by (simp add: Nil_fm_def)

lemma sats_Nil_fm [simp]:
   "[| x \<in> nat; env \<in> list(A)|]
    ==> sats(A, Nil_fm(x), env) \<longleftrightarrow> is_Nil(##A, nth(x,env))"
by (simp add: Nil_fm_def is_Nil_def)

lemma Nil_iff_sats:
      "[| nth(i,env) = x; i \<in> nat; env \<in> list(A)|]
       ==> is_Nil(##A, x) \<longleftrightarrow> sats(A, Nil_fm(i), env)"
by simp


subsubsection\<open>The Formula @{term is_Cons}, Internalized\<close>


(*  "is_Cons(M,a,l,Z) == \<exists>p[M]. pair(M,a,l,p) & is_Inr(M,p,Z)" *)
definition
  Cons_fm :: "[i,i,i]=>i" where
    "Cons_fm(a,l,Z) ==
       Exists(And(pair_fm(succ(a),succ(l),0), Inr_fm(0,succ(Z))))"

lemma Cons_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> Cons_fm(x,y,z) \<in> formula"
by (simp add: Cons_fm_def)

lemma sats_Cons_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, Cons_fm(x,y,z), env) \<longleftrightarrow>
       is_Cons(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: Cons_fm_def is_Cons_def)

lemma Cons_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==>is_Cons(##A, x, y, z) \<longleftrightarrow> sats(A, Cons_fm(i,j,k), env)"
by simp

subsubsection\<open>The Formula @{term is_quasilist}, Internalized\<close>

(* is_quasilist(M,xs) == is_Nil(M,z) | (\<exists>x[M]. \<exists>l[M]. is_Cons(M,x,l,z))" *)

definition
  quasilist_fm :: "i=>i" where
    "quasilist_fm(x) ==
       Or(Nil_fm(x), Exists(Exists(Cons_fm(1,0,succ(succ(x))))))"

lemma quasilist_type [TC]: "x \<in> nat ==> quasilist_fm(x) \<in> formula"
by (simp add: quasilist_fm_def)

lemma sats_quasilist_fm [simp]:
   "[| x \<in> nat; env \<in> list(A)|]
    ==> sats(A, quasilist_fm(x), env) \<longleftrightarrow> is_quasilist(##A, nth(x,env))"
by (simp add: quasilist_fm_def is_quasilist_def)

lemma quasilist_iff_sats:
      "[| nth(i,env) = x; i \<in> nat; env \<in> list(A)|]
       ==> is_quasilist(##A, x) \<longleftrightarrow> sats(A, quasilist_fm(i), env)"
by simp


subsection\<open>Absoluteness for the Function @{term nth}\<close>


subsubsection\<open>The Formula @{term is_hd}, Internalized\<close>

(*   "is_hd(M,xs,H) == 
       (is_Nil(M,xs) \<longrightarrow> empty(M,H)) &
       (\<forall>x[M]. \<forall>l[M]. ~ is_Cons(M,x,l,xs) | H=x) &
       (is_quasilist(M,xs) | empty(M,H))" *)
definition
  hd_fm :: "[i,i]=>i" where
    "hd_fm(xs,H) == 
       And(Implies(Nil_fm(xs), empty_fm(H)),
           And(Forall(Forall(Or(Neg(Cons_fm(1,0,xs#+2)), Equal(H#+2,1)))),
               Or(quasilist_fm(xs), empty_fm(H))))"

lemma hd_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> hd_fm(x,y) \<in> formula"
by (simp add: hd_fm_def) 

lemma sats_hd_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, hd_fm(x,y), env) \<longleftrightarrow> is_hd(##A, nth(x,env), nth(y,env))"
by (simp add: hd_fm_def is_hd_def)

lemma hd_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> is_hd(##A, x, y) \<longleftrightarrow> sats(A, hd_fm(i,j), env)"
by simp


subsubsection\<open>The Formula @{term is_tl}, Internalized\<close>

(*     "is_tl(M,xs,T) ==
       (is_Nil(M,xs) \<longrightarrow> T=xs) &
       (\<forall>x[M]. \<forall>l[M]. ~ is_Cons(M,x,l,xs) | T=l) &
       (is_quasilist(M,xs) | empty(M,T))" *)
definition
  tl_fm :: "[i,i]=>i" where
    "tl_fm(xs,T) ==
       And(Implies(Nil_fm(xs), Equal(T,xs)),
           And(Forall(Forall(Or(Neg(Cons_fm(1,0,xs#+2)), Equal(T#+2,0)))),
               Or(quasilist_fm(xs), empty_fm(T))))"

lemma tl_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> tl_fm(x,y) \<in> formula"
by (simp add: tl_fm_def)

lemma sats_tl_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, tl_fm(x,y), env) \<longleftrightarrow> is_tl(##A, nth(x,env), nth(y,env))"
by (simp add: tl_fm_def is_tl_def)

lemma tl_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> is_tl(##A, x, y) \<longleftrightarrow> sats(A, tl_fm(i,j), env)"
by simp


subsubsection\<open>The Operator @{term is_bool_of_o}\<close>

(*   is_bool_of_o :: "[i=>o, o, i] => o"
   "is_bool_of_o(M,P,z) == (P & number1(M,z)) | (~P & empty(M,z))" *)

text\<open>The formula @{term p} has no free variables.\<close>
definition
  bool_of_o_fm :: "[i, i]=>i" where
  "bool_of_o_fm(p,z) == 
    Or(And(p,number1_fm(z)),
       And(Neg(p),empty_fm(z)))"

lemma is_bool_of_o_type [TC]:
     "[| p \<in> formula; z \<in> nat |] ==> bool_of_o_fm(p,z) \<in> formula"
by (simp add: bool_of_o_fm_def)

lemma sats_bool_of_o_fm:
  assumes p_iff_sats: "P \<longleftrightarrow> sats(A, p, env)"
  shows 
      "[|z \<in> nat; env \<in> list(A)|]
       ==> sats(A, bool_of_o_fm(p,z), env) \<longleftrightarrow>
           is_bool_of_o(##A, P, nth(z,env))"
by (simp add: bool_of_o_fm_def is_bool_of_o_def p_iff_sats [THEN iff_sym])

lemma is_bool_of_o_iff_sats:
  "[| P \<longleftrightarrow> sats(A, p, env); nth(k,env) = z; k \<in> nat; env \<in> list(A)|]
   ==> is_bool_of_o(##A, P, z) \<longleftrightarrow> sats(A, bool_of_o_fm(p,k), env)"
by (simp add: sats_bool_of_o_fm)


subsection\<open>More Internalizations\<close>

subsubsection\<open>The Operator @{term is_lambda}\<close>

text\<open>The two arguments of @{term p} are always 1, 0. Remember that
 @{term p} will be enclosed by three quantifiers.\<close>

(* is_lambda :: "[i=>o, i, [i,i]=>o, i] => o"
    "is_lambda(M, A, is_b, z) == 
       \<forall>p[M]. p \<in> z \<longleftrightarrow>
        (\<exists>u[M]. \<exists>v[M]. u\<in>A & pair(M,u,v,p) & is_b(u,v))" *)
definition
  lambda_fm :: "[i, i, i]=>i" where
  "lambda_fm(p,A,z) == 
    Forall(Iff(Member(0,succ(z)),
            Exists(Exists(And(Member(1,A#+3),
                           And(pair_fm(1,0,2), p))))))"

text\<open>We call @{term p} with arguments x, y by equating them with 
  the corresponding quantified variables with de Bruijn indices 1, 0.\<close>

lemma is_lambda_type [TC]:
     "[| p \<in> formula; x \<in> nat; y \<in> nat |] 
      ==> lambda_fm(p,x,y) \<in> formula"
by (simp add: lambda_fm_def) 

lemma sats_lambda_fm:
  assumes is_b_iff_sats: 
      "!!a0 a1 a2. 
        [|a0\<in>A; a1\<in>A; a2\<in>A|] 
        ==> is_b(a1, a0) \<longleftrightarrow> sats(A, p, Cons(a0,Cons(a1,Cons(a2,env))))"
  shows 
      "[|x \<in> nat; y \<in> nat; env \<in> list(A)|]
       ==> sats(A, lambda_fm(p,x,y), env) \<longleftrightarrow> 
           is_lambda(##A, nth(x,env), is_b, nth(y,env))"
by (simp add: lambda_fm_def is_lambda_def is_b_iff_sats [THEN iff_sym]) 

subsubsection\<open>The Operator @{term is_Member}, Internalized\<close>

(*    "is_Member(M,x,y,Z) ==
        \<exists>p[M]. \<exists>u[M]. pair(M,x,y,p) & is_Inl(M,p,u) & is_Inl(M,u,Z)" *)
definition
  Member_fm :: "[i,i,i]=>i" where
    "Member_fm(x,y,Z) ==
       Exists(Exists(And(pair_fm(x#+2,y#+2,1), 
                      And(Inl_fm(1,0), Inl_fm(0,Z#+2)))))"

lemma is_Member_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> Member_fm(x,y,z) \<in> formula"
by (simp add: Member_fm_def)

lemma sats_Member_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, Member_fm(x,y,z), env) \<longleftrightarrow>
        is_Member(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: Member_fm_def is_Member_def)

lemma Member_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> is_Member(##A, x, y, z) \<longleftrightarrow> sats(A, Member_fm(i,j,k), env)"
by (simp add: sats_Member_fm)

subsubsection\<open>The Operator @{term is_Equal}, Internalized\<close>

(*    "is_Equal(M,x,y,Z) ==
        \<exists>p[M]. \<exists>u[M]. pair(M,x,y,p) & is_Inr(M,p,u) & is_Inl(M,u,Z)" *)
definition
  Equal_fm :: "[i,i,i]=>i" where
    "Equal_fm(x,y,Z) ==
       Exists(Exists(And(pair_fm(x#+2,y#+2,1), 
                      And(Inr_fm(1,0), Inl_fm(0,Z#+2)))))"

lemma is_Equal_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> Equal_fm(x,y,z) \<in> formula"
by (simp add: Equal_fm_def)

lemma sats_Equal_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, Equal_fm(x,y,z), env) \<longleftrightarrow>
        is_Equal(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: Equal_fm_def is_Equal_def)

lemma Equal_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> is_Equal(##A, x, y, z) \<longleftrightarrow> sats(A, Equal_fm(i,j,k), env)"
by (simp add: sats_Equal_fm)

subsubsection\<open>The Operator @{term is_Nand}, Internalized\<close>

(*    "is_Nand(M,x,y,Z) ==
        \<exists>p[M]. \<exists>u[M]. pair(M,x,y,p) & is_Inl(M,p,u) & is_Inr(M,u,Z)" *)
definition
  Nand_fm :: "[i,i,i]=>i" where
    "Nand_fm(x,y,Z) ==
       Exists(Exists(And(pair_fm(x#+2,y#+2,1), 
                      And(Inl_fm(1,0), Inr_fm(0,Z#+2)))))"

lemma is_Nand_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> Nand_fm(x,y,z) \<in> formula"
by (simp add: Nand_fm_def)

lemma sats_Nand_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, Nand_fm(x,y,z), env) \<longleftrightarrow>
        is_Nand(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: Nand_fm_def is_Nand_def)

lemma Nand_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> is_Nand(##A, x, y, z) \<longleftrightarrow> sats(A, Nand_fm(i,j,k), env)"
by (simp add: sats_Nand_fm)

subsubsection\<open>The Operator @{term is_Forall}, Internalized\<close>

(* "is_Forall(M,p,Z) == \<exists>u[M]. is_Inr(M,p,u) & is_Inr(M,u,Z)" *)
definition
  Forall_fm :: "[i,i]=>i" where
    "Forall_fm(x,Z) ==
       Exists(And(Inr_fm(succ(x),0), Inr_fm(0,succ(Z))))"

lemma is_Forall_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> Forall_fm(x,y) \<in> formula"
by (simp add: Forall_fm_def)

lemma sats_Forall_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, Forall_fm(x,y), env) \<longleftrightarrow>
        is_Forall(##A, nth(x,env), nth(y,env))"
by (simp add: Forall_fm_def is_Forall_def)

lemma Forall_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; 
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> is_Forall(##A, x, y) \<longleftrightarrow> sats(A, Forall_fm(i,j), env)"
by (simp add: sats_Forall_fm)


subsubsection\<open>The Operator @{term is_and}, Internalized\<close>

(* is_and(M,a,b,z) == (number1(M,a)  & z=b) | 
                       (~number1(M,a) & empty(M,z)) *)
definition
  and_fm :: "[i,i,i]=>i" where
    "and_fm(a,b,z) ==
       Or(And(number1_fm(a), Equal(z,b)),
          And(Neg(number1_fm(a)),empty_fm(z)))"

lemma is_and_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> and_fm(x,y,z) \<in> formula"
by (simp add: and_fm_def)

lemma sats_and_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, and_fm(x,y,z), env) \<longleftrightarrow>
        is_and(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: and_fm_def is_and_def)

lemma is_and_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> is_and(##A, x, y, z) \<longleftrightarrow> sats(A, and_fm(i,j,k), env)"
by simp


subsubsection\<open>The Operator @{term is_or}, Internalized\<close>

(* is_or(M,a,b,z) == (number1(M,a)  & number1(M,z)) | 
                     (~number1(M,a) & z=b) *)

definition
  or_fm :: "[i,i,i]=>i" where
    "or_fm(a,b,z) ==
       Or(And(number1_fm(a), number1_fm(z)),
          And(Neg(number1_fm(a)), Equal(z,b)))"

lemma is_or_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> or_fm(x,y,z) \<in> formula"
by (simp add: or_fm_def)

lemma sats_or_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, or_fm(x,y,z), env) \<longleftrightarrow>
        is_or(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: or_fm_def is_or_def)

lemma is_or_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> is_or(##A, x, y, z) \<longleftrightarrow> sats(A, or_fm(i,j,k), env)"
by simp



subsubsection\<open>The Operator @{term is_not}, Internalized\<close>

(* is_not(M,a,z) == (number1(M,a)  & empty(M,z)) | 
                     (~number1(M,a) & number1(M,z)) *)
definition
  not_fm :: "[i,i]=>i" where
    "not_fm(a,z) ==
       Or(And(number1_fm(a), empty_fm(z)),
          And(Neg(number1_fm(a)), number1_fm(z)))"

lemma is_not_type [TC]:
     "[| x \<in> nat; z \<in> nat |] ==> not_fm(x,z) \<in> formula"
by (simp add: not_fm_def)

lemma sats_is_not_fm [simp]:
   "[| x \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, not_fm(x,z), env) \<longleftrightarrow> is_not(##A, nth(x,env), nth(z,env))"
by (simp add: not_fm_def is_not_def)

lemma is_not_iff_sats:
      "[| nth(i,env) = x; nth(k,env) = z;
          i \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> is_not(##A, x, z) \<longleftrightarrow> sats(A, not_fm(i,k), env)"
by simp

subsection\<open>Well-Founded Recursion!\<close>

subsubsection\<open>The Operator @{term M_is_recfun}\<close>

text\<open>Alternative definition, minimizing nesting of quantifiers around MH\<close>
lemma M_is_recfun_iff:
   "M_is_recfun(M,MH,r,a,f) \<longleftrightarrow>
    (\<forall>z[M]. z \<in> f \<longleftrightarrow> 
     (\<exists>x[M]. \<exists>f_r_sx[M]. \<exists>y[M]. 
             MH(x, f_r_sx, y) & pair(M,x,y,z) &
             (\<exists>xa[M]. \<exists>sx[M]. \<exists>r_sx[M]. 
                pair(M,x,a,xa) & upair(M,x,x,sx) &
               pre_image(M,r,sx,r_sx) & restriction(M,f,r_sx,f_r_sx) &
               xa \<in> r)))"
apply (simp add: M_is_recfun_def)
apply (rule rall_cong, blast) 
done


(* M_is_recfun :: "[i=>o, [i,i,i]=>o, i, i, i] => o"
   "M_is_recfun(M,MH,r,a,f) ==
     \<forall>z[M]. z \<in> f \<longleftrightarrow>
               2      1           0
new def     (\<exists>x[M]. \<exists>f_r_sx[M]. \<exists>y[M]. 
             MH(x, f_r_sx, y) & pair(M,x,y,z) &
             (\<exists>xa[M]. \<exists>sx[M]. \<exists>r_sx[M]. 
                pair(M,x,a,xa) & upair(M,x,x,sx) &
               pre_image(M,r,sx,r_sx) & restriction(M,f,r_sx,f_r_sx) &
               xa \<in> r)"
*)

text\<open>The three arguments of @{term p} are always 2, 1, 0 and z\<close>
definition
  is_recfun_fm :: "[i, i, i, i]=>i" where
  "is_recfun_fm(p,r,a,f) == 
   Forall(Iff(Member(0,succ(f)),
    Exists(Exists(Exists(
     And(p, 
      And(pair_fm(2,0,3),
       Exists(Exists(Exists(
        And(pair_fm(5,a#+7,2),
         And(upair_fm(5,5,1),
          And(pre_image_fm(r#+7,1,0),
           And(restriction_fm(f#+7,0,4), Member(2,r#+7)))))))))))))))"

lemma is_recfun_type [TC]:
     "[| p \<in> formula; x \<in> nat; y \<in> nat; z \<in> nat |] 
      ==> is_recfun_fm(p,x,y,z) \<in> formula"
by (simp add: is_recfun_fm_def)


lemma sats_is_recfun_fm:
  assumes MH_iff_sats: 
      "!!a0 a1 a2 a3. 
        [|a0\<in>A; a1\<in>A; a2\<in>A; a3\<in>A|] 
        ==> MH(a2, a1, a0) \<longleftrightarrow> sats(A, p, Cons(a0,Cons(a1,Cons(a2,Cons(a3,env)))))"
  shows 
      "[|x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
       ==> sats(A, is_recfun_fm(p,x,y,z), env) \<longleftrightarrow>
           M_is_recfun(##A, MH, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: is_recfun_fm_def M_is_recfun_iff MH_iff_sats [THEN iff_sym])

lemma is_recfun_iff_sats:
  assumes MH_iff_sats: 
      "!!a0 a1 a2 a3. 
        [|a0\<in>A; a1\<in>A; a2\<in>A; a3\<in>A|] 
        ==> MH(a2, a1, a0) \<longleftrightarrow> sats(A, p, Cons(a0,Cons(a1,Cons(a2,Cons(a3,env)))))"
  shows
  "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
      i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
   ==> M_is_recfun(##A, MH, x, y, z) \<longleftrightarrow> sats(A, is_recfun_fm(p,i,j,k), env)"
by (simp add: sats_is_recfun_fm [OF MH_iff_sats]) 

text\<open>The additional variable in the premise, namely @{term f'}, is essential.
It lets @{term MH} depend upon @{term x}, which seems often necessary.
The same thing occurs in \<open>is_wfrec_reflection\<close>.\<close>

subsubsection\<open>The Operator @{term is_wfrec}\<close>

text\<open>The three arguments of @{term p} are always 2, 1, 0;
      @{term p} is enclosed by 5 quantifiers.\<close>

(* is_wfrec :: "[i=>o, i, [i,i,i]=>o, i, i] => o"
    "is_wfrec(M,MH,r,a,z) == 
      \<exists>f[M]. M_is_recfun(M,MH,r,a,f) & MH(a,f,z)" *)
definition
  is_wfrec_fm :: "[i, i, i, i]=>i" where
  "is_wfrec_fm(p,r,a,z) == 
    Exists(And(is_recfun_fm(p, succ(r), succ(a), 0),
           Exists(Exists(Exists(Exists(
             And(Equal(2,a#+5), And(Equal(1,4), And(Equal(0,z#+5), p)))))))))"

text\<open>We call @{term p} with arguments a, f, z by equating them with 
  the corresponding quantified variables with de Bruijn indices 2, 1, 0.\<close>

text\<open>There's an additional existential quantifier to ensure that the
      environments in both calls to MH have the same length.\<close>

lemma is_wfrec_type [TC]:
     "[| p \<in> formula; x \<in> nat; y \<in> nat; z \<in> nat |] 
      ==> is_wfrec_fm(p,x,y,z) \<in> formula"
by (simp add: is_wfrec_fm_def) 

lemma sats_is_wfrec_fm:
  assumes MH_iff_sats: 
      "!!a0 a1 a2 a3 a4. 
        [|a0\<in>A; a1\<in>A; a2\<in>A; a3\<in>A; a4\<in>A|] 
        ==> MH(a2, a1, a0) \<longleftrightarrow> sats(A, p, Cons(a0,Cons(a1,Cons(a2,Cons(a3,Cons(a4,env))))))"
  shows 
      "[|x \<in> nat; y < length(env); z < length(env); env \<in> list(A)|]
       ==> sats(A, is_wfrec_fm(p,x,y,z), env) \<longleftrightarrow> 
           is_wfrec(##A, MH, nth(x,env), nth(y,env), nth(z,env))"
apply (frule_tac x=z in lt_length_in_nat, assumption)  
apply (frule lt_length_in_nat, assumption)  
apply (simp add: is_wfrec_fm_def sats_is_recfun_fm is_wfrec_def MH_iff_sats [THEN iff_sym], blast) 
done


lemma is_wfrec_iff_sats:
  assumes MH_iff_sats: 
      "!!a0 a1 a2 a3 a4. 
        [|a0\<in>A; a1\<in>A; a2\<in>A; a3\<in>A; a4\<in>A|] 
        ==> MH(a2, a1, a0) \<longleftrightarrow> sats(A, p, Cons(a0,Cons(a1,Cons(a2,Cons(a3,Cons(a4,env))))))"
  shows
  "[|nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
      i \<in> nat; j < length(env); k < length(env); env \<in> list(A)|]
   ==> is_wfrec(##A, MH, x, y, z) \<longleftrightarrow> sats(A, is_wfrec_fm(p,i,j,k), env)" 
by (simp add: sats_is_wfrec_fm [OF MH_iff_sats])


subsection\<open>For Datatypes\<close>

subsubsection\<open>Binary Products, Internalized\<close>

definition
  cartprod_fm :: "[i,i,i]=>i" where
(* "cartprod(M,A,B,z) ==
        \<forall>u[M]. u \<in> z \<longleftrightarrow> (\<exists>x[M]. x\<in>A & (\<exists>y[M]. y\<in>B & pair(M,x,y,u)))" *)
    "cartprod_fm(A,B,z) ==
       Forall(Iff(Member(0,succ(z)),
                  Exists(And(Member(0,succ(succ(A))),
                         Exists(And(Member(0,succ(succ(succ(B)))),
                                    pair_fm(1,0,2)))))))"

lemma cartprod_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> cartprod_fm(x,y,z) \<in> formula"
by (simp add: cartprod_fm_def)

lemma sats_cartprod_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, cartprod_fm(x,y,z), env) \<longleftrightarrow>
        cartprod(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: cartprod_fm_def cartprod_def)

lemma cartprod_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> cartprod(##A, x, y, z) \<longleftrightarrow> sats(A, cartprod_fm(i,j,k), env)"
by (simp add: sats_cartprod_fm)


subsubsection\<open>Binary Sums, Internalized\<close>

(* "is_sum(M,A,B,Z) ==
       \<exists>A0[M]. \<exists>n1[M]. \<exists>s1[M]. \<exists>B1[M].
         3      2       1        0
       number1(M,n1) & cartprod(M,n1,A,A0) & upair(M,n1,n1,s1) &
       cartprod(M,s1,B,B1) & union(M,A0,B1,Z)"  *)
definition
  sum_fm :: "[i,i,i]=>i" where
    "sum_fm(A,B,Z) ==
       Exists(Exists(Exists(Exists(
        And(number1_fm(2),
            And(cartprod_fm(2,A#+4,3),
                And(upair_fm(2,2,1),
                    And(cartprod_fm(1,B#+4,0), union_fm(3,0,Z#+4)))))))))"

lemma sum_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> sum_fm(x,y,z) \<in> formula"
by (simp add: sum_fm_def)

lemma sats_sum_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, sum_fm(x,y,z), env) \<longleftrightarrow>
        is_sum(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: sum_fm_def is_sum_def)

lemma sum_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> is_sum(##A, x, y, z) \<longleftrightarrow> sats(A, sum_fm(i,j,k), env)"
by simp


subsubsection\<open>The Operator @{term quasinat}\<close>

(* "is_quasinat(M,z) == empty(M,z) | (\<exists>m[M]. successor(M,m,z))" *)
definition
  quasinat_fm :: "i=>i" where
    "quasinat_fm(z) == Or(empty_fm(z), Exists(succ_fm(0,succ(z))))"

lemma quasinat_type [TC]:
     "x \<in> nat ==> quasinat_fm(x) \<in> formula"
by (simp add: quasinat_fm_def)

lemma sats_quasinat_fm [simp]:
   "[| x \<in> nat; env \<in> list(A)|]
    ==> sats(A, quasinat_fm(x), env) \<longleftrightarrow> is_quasinat(##A, nth(x,env))"
by (simp add: quasinat_fm_def is_quasinat_def)

lemma quasinat_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; env \<in> list(A)|]
       ==> is_quasinat(##A, x) \<longleftrightarrow> sats(A, quasinat_fm(i), env)"
by simp


subsubsection\<open>The Operator @{term is_nat_case}\<close>
text\<open>I could not get it to work with the more natural assumption that 
 @{term is_b} takes two arguments.  Instead it must be a formula where 1 and 0
 stand for @{term m} and @{term b}, respectively.\<close>

(* is_nat_case :: "[i=>o, i, [i,i]=>o, i, i] => o"
    "is_nat_case(M, a, is_b, k, z) ==
       (empty(M,k) \<longrightarrow> z=a) &
       (\<forall>m[M]. successor(M,m,k) \<longrightarrow> is_b(m,z)) &
       (is_quasinat(M,k) | empty(M,z))" *)
text\<open>The formula @{term is_b} has free variables 1 and 0.\<close>
definition
  is_nat_case_fm :: "[i, i, i, i]=>i" where
 "is_nat_case_fm(a,is_b,k,z) == 
    And(Implies(empty_fm(k), Equal(z,a)),
        And(Forall(Implies(succ_fm(0,succ(k)), 
                   Forall(Implies(Equal(0,succ(succ(z))), is_b)))),
            Or(quasinat_fm(k), empty_fm(z))))"

lemma is_nat_case_type [TC]:
     "[| is_b \<in> formula;  
         x \<in> nat; y \<in> nat; z \<in> nat |] 
      ==> is_nat_case_fm(x,is_b,y,z) \<in> formula"
by (simp add: is_nat_case_fm_def)

lemma sats_is_nat_case_fm:
  assumes is_b_iff_sats: 
      "!!a. a \<in> A ==> is_b(a,nth(z, env)) \<longleftrightarrow> 
                      sats(A, p, Cons(nth(z,env), Cons(a, env)))"
  shows 
      "[|x \<in> nat; y \<in> nat; z < length(env); env \<in> list(A)|]
       ==> sats(A, is_nat_case_fm(x,p,y,z), env) \<longleftrightarrow>
           is_nat_case(##A, nth(x,env), is_b, nth(y,env), nth(z,env))"
apply (frule lt_length_in_nat, assumption)
apply (simp add: is_nat_case_fm_def is_nat_case_def is_b_iff_sats [THEN iff_sym])
done

lemma is_nat_case_iff_sats:
  "[| (!!a. a \<in> A ==> is_b(a,z) \<longleftrightarrow>
                      sats(A, p, Cons(z, Cons(a,env))));
      nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
      i \<in> nat; j \<in> nat; k < length(env); env \<in> list(A)|]
   ==> is_nat_case(##A, x, is_b, y, z) \<longleftrightarrow> sats(A, is_nat_case_fm(i,p,j,k), env)"
by (simp add: sats_is_nat_case_fm [of A is_b])


text\<open>The second argument of @{term is_b} gives it direct access to @{term x},
  which is essential for handling free variable references.  Without this
  argument, we cannot prove reflection for @{term iterates_MH}.\<close>

subsection\<open>The Operator @{term iterates_MH}, Needed for Iteration\<close>

(*  iterates_MH :: "[i=>o, [i,i]=>o, i, i, i, i] => o"
   "iterates_MH(M,isF,v,n,g,z) ==
        is_nat_case(M, v, \<lambda>m u. \<exists>gm[M]. fun_apply(M,g,m,gm) & isF(gm,u),
                    n, z)" *)
definition
  iterates_MH_fm :: "[i, i, i, i, i]=>i" where
 "iterates_MH_fm(isF,v,n,g,z) == 
    is_nat_case_fm(v, 
      Exists(And(fun_apply_fm(succ(succ(succ(g))),2,0), 
                     Forall(Implies(Equal(0,2), isF)))), 
      n, z)"

lemma iterates_MH_type [TC]:
     "[| p \<in> formula;  
         v \<in> nat; x \<in> nat; y \<in> nat; z \<in> nat |] 
      ==> iterates_MH_fm(p,v,x,y,z) \<in> formula"
by (simp add: iterates_MH_fm_def)

lemma sats_iterates_MH_fm:
  assumes is_F_iff_sats:
      "!!a b c d. [| a \<in> A; b \<in> A; c \<in> A; d \<in> A|]
              ==> is_F(a,b) \<longleftrightarrow>
                  sats(A, p, Cons(b, Cons(a, Cons(c, Cons(d,env)))))"
  shows 
      "[|v \<in> nat; x \<in> nat; y \<in> nat; z < length(env); env \<in> list(A)|]
       ==> sats(A, iterates_MH_fm(p,v,x,y,z), env) \<longleftrightarrow>
           iterates_MH(##A, is_F, nth(v,env), nth(x,env), nth(y,env), nth(z,env))"
apply (frule lt_length_in_nat, assumption)  
apply (simp add: iterates_MH_fm_def iterates_MH_def sats_is_nat_case_fm 
              is_F_iff_sats [symmetric])
apply (rule is_nat_case_cong) 
apply (simp_all add: setclass_def)
done

lemma iterates_MH_iff_sats:
  assumes is_F_iff_sats:
      "!!a b c d. [| a \<in> A; b \<in> A; c \<in> A; d \<in> A|]
              ==> is_F(a,b) \<longleftrightarrow>
                  sats(A, p, Cons(b, Cons(a, Cons(c, Cons(d,env)))))"
  shows 
  "[| nth(i',env) = v; nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
      i' \<in> nat; i \<in> nat; j \<in> nat; k < length(env); env \<in> list(A)|]
   ==> iterates_MH(##A, is_F, v, x, y, z) \<longleftrightarrow>
       sats(A, iterates_MH_fm(p,i',i,j,k), env)"
by (simp add: sats_iterates_MH_fm [OF is_F_iff_sats]) 

text\<open>The second argument of @{term p} gives it direct access to @{term x},
  which is essential for handling free variable references.  Without this
  argument, we cannot prove reflection for @{term list_N}.\<close>

subsubsection\<open>The Operator @{term is_iterates}\<close>

text\<open>The three arguments of @{term p} are always 2, 1, 0;
      @{term p} is enclosed by 9 (??) quantifiers.\<close>

(*    "is_iterates(M,isF,v,n,Z) == 
      \<exists>sn[M]. \<exists>msn[M]. successor(M,n,sn) & membership(M,sn,msn) &
       1       0       is_wfrec(M, iterates_MH(M,isF,v), msn, n, Z)"*)

definition
  is_iterates_fm :: "[i, i, i, i]=>i" where
  "is_iterates_fm(p,v,n,Z) == 
     Exists(Exists(
      And(succ_fm(n#+2,1),
       And(Memrel_fm(1,0),
              is_wfrec_fm(iterates_MH_fm(p, v#+7, 2, 1, 0), 
                          0, n#+2, Z#+2)))))"

text\<open>We call @{term p} with arguments a, f, z by equating them with 
  the corresponding quantified variables with de Bruijn indices 2, 1, 0.\<close>


lemma is_iterates_type [TC]:
     "[| p \<in> formula; x \<in> nat; y \<in> nat; z \<in> nat |] 
      ==> is_iterates_fm(p,x,y,z) \<in> formula"
by (simp add: is_iterates_fm_def) 

lemma sats_is_iterates_fm:
  assumes is_F_iff_sats:
      "!!a b c d e f g h i j k. 
              [| a \<in> A; b \<in> A; c \<in> A; d \<in> A; e \<in> A; f \<in> A; 
                 g \<in> A; h \<in> A; i \<in> A; j \<in> A; k \<in> A|]
              ==> is_F(a,b) \<longleftrightarrow>
                  sats(A, p, Cons(b, Cons(a, Cons(c, Cons(d, Cons(e, Cons(f, 
                      Cons(g, Cons(h, Cons(i, Cons(j, Cons(k, env))))))))))))"
  shows 
      "[|x \<in> nat; y < length(env); z < length(env); env \<in> list(A)|]
       ==> sats(A, is_iterates_fm(p,x,y,z), env) \<longleftrightarrow>
           is_iterates(##A, is_F, nth(x,env), nth(y,env), nth(z,env))"
apply (frule_tac x=z in lt_length_in_nat, assumption)  
apply (frule lt_length_in_nat, assumption)  
apply (simp add: is_iterates_fm_def is_iterates_def sats_is_nat_case_fm 
              is_F_iff_sats [symmetric] sats_is_wfrec_fm sats_iterates_MH_fm)
done


lemma is_iterates_iff_sats:
  assumes is_F_iff_sats:
      "!!a b c d e f g h i j k. 
              [| a \<in> A; b \<in> A; c \<in> A; d \<in> A; e \<in> A; f \<in> A; 
                 g \<in> A; h \<in> A; i \<in> A; j \<in> A; k \<in> A|]
              ==> is_F(a,b) \<longleftrightarrow>
                  sats(A, p, Cons(b, Cons(a, Cons(c, Cons(d, Cons(e, Cons(f, 
                      Cons(g, Cons(h, Cons(i, Cons(j, Cons(k, env))))))))))))"
  shows 
  "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
      i \<in> nat; j < length(env); k < length(env); env \<in> list(A)|]
   ==> is_iterates(##A, is_F, x, y, z) \<longleftrightarrow>
       sats(A, is_iterates_fm(p,i,j,k), env)"
by (simp add: sats_is_iterates_fm [OF is_F_iff_sats]) 

text\<open>The second argument of @{term p} gives it direct access to @{term x},
  which is essential for handling free variable references.  Without this
  argument, we cannot prove reflection for @{term list_N}.\<close>

subsubsection\<open>The Formula @{term is_eclose_n}, Internalized\<close>

(* is_eclose_n(M,A,n,Z) == is_iterates(M, big_union(M), A, n, Z) *)

definition
  eclose_n_fm :: "[i,i,i]=>i" where
  "eclose_n_fm(A,n,Z) == is_iterates_fm(big_union_fm(1,0), A, n, Z)"

lemma eclose_n_fm_type [TC]:
 "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> eclose_n_fm(x,y,z) \<in> formula"
by (simp add: eclose_n_fm_def)

lemma sats_eclose_n_fm [simp]:
   "[| x \<in> nat; y < length(env); z < length(env); env \<in> list(A)|]
    ==> sats(A, eclose_n_fm(x,y,z), env) \<longleftrightarrow>
        is_eclose_n(##A, nth(x,env), nth(y,env), nth(z,env))"
apply (frule_tac x=z in lt_length_in_nat, assumption)  
apply (frule_tac x=y in lt_length_in_nat, assumption)  
apply (simp add: eclose_n_fm_def is_eclose_n_def 
                 sats_is_iterates_fm) 
done

lemma eclose_n_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j < length(env); k < length(env); env \<in> list(A)|]
       ==> is_eclose_n(##A, x, y, z) \<longleftrightarrow> sats(A, eclose_n_fm(i,j,k), env)"
by (simp add: sats_eclose_n_fm)


subsubsection\<open>Membership in @{term "eclose(A)"}\<close>

(* mem_eclose(M,A,l) == 
      \<exists>n[M]. \<exists>eclosen[M]. 
       finite_ordinal(M,n) & is_eclose_n(M,A,n,eclosen) & l \<in> eclosen *)
definition
  mem_eclose_fm :: "[i,i]=>i" where
    "mem_eclose_fm(x,y) ==
       Exists(Exists(
         And(finite_ordinal_fm(1),
           And(eclose_n_fm(x#+2,1,0), Member(y#+2,0)))))"

lemma mem_eclose_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> mem_eclose_fm(x,y) \<in> formula"
by (simp add: mem_eclose_fm_def)

lemma sats_mem_eclose_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, mem_eclose_fm(x,y), env) \<longleftrightarrow> mem_eclose(##A, nth(x,env), nth(y,env))"
by (simp add: mem_eclose_fm_def mem_eclose_def)

lemma mem_eclose_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> mem_eclose(##A, x, y) \<longleftrightarrow> sats(A, mem_eclose_fm(i,j), env)"
by simp


subsubsection\<open>The Predicate ``Is @{term "eclose(A)"}''\<close>

(* is_eclose(M,A,Z) == \<forall>l[M]. l \<in> Z \<longleftrightarrow> mem_eclose(M,A,l) *)
definition
  is_eclose_fm :: "[i,i]=>i" where
    "is_eclose_fm(A,Z) ==
       Forall(Iff(Member(0,succ(Z)), mem_eclose_fm(succ(A),0)))"

lemma is_eclose_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> is_eclose_fm(x,y) \<in> formula"
by (simp add: is_eclose_fm_def)

lemma sats_is_eclose_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, is_eclose_fm(x,y), env) \<longleftrightarrow> is_eclose(##A, nth(x,env), nth(y,env))"
by (simp add: is_eclose_fm_def is_eclose_def)

lemma is_eclose_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> is_eclose(##A, x, y) \<longleftrightarrow> sats(A, is_eclose_fm(i,j), env)"
by simp


subsubsection\<open>The List Functor, Internalized\<close>

definition
  list_functor_fm :: "[i,i,i]=>i" where
(* "is_list_functor(M,A,X,Z) ==
        \<exists>n1[M]. \<exists>AX[M].
         number1(M,n1) & cartprod(M,A,X,AX) & is_sum(M,n1,AX,Z)" *)
    "list_functor_fm(A,X,Z) ==
       Exists(Exists(
        And(number1_fm(1),
            And(cartprod_fm(A#+2,X#+2,0), sum_fm(1,0,Z#+2)))))"

lemma list_functor_type [TC]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> list_functor_fm(x,y,z) \<in> formula"
by (simp add: list_functor_fm_def)

lemma sats_list_functor_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, list_functor_fm(x,y,z), env) \<longleftrightarrow>
        is_list_functor(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: list_functor_fm_def is_list_functor_def)

lemma list_functor_iff_sats:
  "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
      i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
   ==> is_list_functor(##A, x, y, z) \<longleftrightarrow> sats(A, list_functor_fm(i,j,k), env)"
by simp


subsubsection\<open>The Formula @{term is_list_N}, Internalized\<close>

(* "is_list_N(M,A,n,Z) == 
      \<exists>zero[M]. empty(M,zero) & 
                is_iterates(M, is_list_functor(M,A), zero, n, Z)" *)

definition
  list_N_fm :: "[i,i,i]=>i" where
  "list_N_fm(A,n,Z) == 
     Exists(
       And(empty_fm(0),
           is_iterates_fm(list_functor_fm(A#+9#+3,1,0), 0, n#+1, Z#+1)))"

lemma list_N_fm_type [TC]:
 "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> list_N_fm(x,y,z) \<in> formula"
by (simp add: list_N_fm_def)

lemma sats_list_N_fm [simp]:
   "[| x \<in> nat; y < length(env); z < length(env); env \<in> list(A)|]
    ==> sats(A, list_N_fm(x,y,z), env) \<longleftrightarrow>
        is_list_N(##A, nth(x,env), nth(y,env), nth(z,env))"
apply (frule_tac x=z in lt_length_in_nat, assumption)  
apply (frule_tac x=y in lt_length_in_nat, assumption)  
apply (simp add: list_N_fm_def is_list_N_def sats_is_iterates_fm) 
done

lemma list_N_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j < length(env); k < length(env); env \<in> list(A)|]
       ==> is_list_N(##A, x, y, z) \<longleftrightarrow> sats(A, list_N_fm(i,j,k), env)"
by (simp add: sats_list_N_fm)



subsubsection\<open>The Predicate ``Is A List''\<close>

(* mem_list(M,A,l) == 
      \<exists>n[M]. \<exists>listn[M]. 
       finite_ordinal(M,n) & is_list_N(M,A,n,listn) & l \<in> listn *)
definition
  mem_list_fm :: "[i,i]=>i" where
    "mem_list_fm(x,y) ==
       Exists(Exists(
         And(finite_ordinal_fm(1),
           And(list_N_fm(x#+2,1,0), Member(y#+2,0)))))"

lemma mem_list_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> mem_list_fm(x,y) \<in> formula"
by (simp add: mem_list_fm_def)

lemma sats_mem_list_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, mem_list_fm(x,y), env) \<longleftrightarrow> mem_list(##A, nth(x,env), nth(y,env))"
by (simp add: mem_list_fm_def mem_list_def)

lemma mem_list_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> mem_list(##A, x, y) \<longleftrightarrow> sats(A, mem_list_fm(i,j), env)"
by simp


subsubsection\<open>The Predicate ``Is @{term "list(A)"}''\<close>

(* is_list(M,A,Z) == \<forall>l[M]. l \<in> Z \<longleftrightarrow> mem_list(M,A,l) *)
definition
  is_list_fm :: "[i,i]=>i" where
    "is_list_fm(A,Z) ==
       Forall(Iff(Member(0,succ(Z)), mem_list_fm(succ(A),0)))"

lemma is_list_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> is_list_fm(x,y) \<in> formula"
by (simp add: is_list_fm_def)

lemma sats_is_list_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, is_list_fm(x,y), env) \<longleftrightarrow> is_list(##A, nth(x,env), nth(y,env))"
by (simp add: is_list_fm_def is_list_def)

lemma is_list_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> is_list(##A, x, y) \<longleftrightarrow> sats(A, is_list_fm(i,j), env)"
by simp


subsubsection\<open>The Formula Functor, Internalized\<close>

definition formula_functor_fm :: "[i,i]=>i" where
(*     "is_formula_functor(M,X,Z) ==
        \<exists>nat'[M]. \<exists>natnat[M]. \<exists>natnatsum[M]. \<exists>XX[M]. \<exists>X3[M].
           4           3               2       1       0
          omega(M,nat') & cartprod(M,nat',nat',natnat) &
          is_sum(M,natnat,natnat,natnatsum) &
          cartprod(M,X,X,XX) & is_sum(M,XX,X,X3) &
          is_sum(M,natnatsum,X3,Z)" *)
    "formula_functor_fm(X,Z) ==
       Exists(Exists(Exists(Exists(Exists(
        And(omega_fm(4),
         And(cartprod_fm(4,4,3),
          And(sum_fm(3,3,2),
           And(cartprod_fm(X#+5,X#+5,1),
            And(sum_fm(1,X#+5,0), sum_fm(2,0,Z#+5)))))))))))"

lemma formula_functor_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> formula_functor_fm(x,y) \<in> formula"
by (simp add: formula_functor_fm_def)

lemma sats_formula_functor_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, formula_functor_fm(x,y), env) \<longleftrightarrow>
        is_formula_functor(##A, nth(x,env), nth(y,env))"
by (simp add: formula_functor_fm_def is_formula_functor_def)

lemma formula_functor_iff_sats:
  "[| nth(i,env) = x; nth(j,env) = y;
      i \<in> nat; j \<in> nat; env \<in> list(A)|]
   ==> is_formula_functor(##A, x, y) \<longleftrightarrow> sats(A, formula_functor_fm(i,j), env)"
by simp


subsubsection\<open>The Formula @{term is_formula_N}, Internalized\<close>

(*  "is_formula_N(M,n,Z) == 
      \<exists>zero[M]. empty(M,zero) & 
                is_iterates(M, is_formula_functor(M), zero, n, Z)" *) 
definition
  formula_N_fm :: "[i,i]=>i" where
  "formula_N_fm(n,Z) == 
     Exists(
       And(empty_fm(0),
           is_iterates_fm(formula_functor_fm(1,0), 0, n#+1, Z#+1)))"

lemma formula_N_fm_type [TC]:
 "[| x \<in> nat; y \<in> nat |] ==> formula_N_fm(x,y) \<in> formula"
by (simp add: formula_N_fm_def)

lemma sats_formula_N_fm [simp]:
   "[| x < length(env); y < length(env); env \<in> list(A)|]
    ==> sats(A, formula_N_fm(x,y), env) \<longleftrightarrow>
        is_formula_N(##A, nth(x,env), nth(y,env))"
apply (frule_tac x=y in lt_length_in_nat, assumption)  
apply (frule lt_length_in_nat, assumption)  
apply (simp add: formula_N_fm_def is_formula_N_def sats_is_iterates_fm) 
done

lemma formula_N_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; 
          i < length(env); j < length(env); env \<in> list(A)|]
       ==> is_formula_N(##A, x, y) \<longleftrightarrow> sats(A, formula_N_fm(i,j), env)"
by (simp add: sats_formula_N_fm)



subsubsection\<open>The Predicate ``Is A Formula''\<close>

(*  mem_formula(M,p) == 
      \<exists>n[M]. \<exists>formn[M]. 
       finite_ordinal(M,n) & is_formula_N(M,n,formn) & p \<in> formn *)
definition
  mem_formula_fm :: "i=>i" where
    "mem_formula_fm(x) ==
       Exists(Exists(
         And(finite_ordinal_fm(1),
           And(formula_N_fm(1,0), Member(x#+2,0)))))"

lemma mem_formula_type [TC]:
     "x \<in> nat ==> mem_formula_fm(x) \<in> formula"
by (simp add: mem_formula_fm_def)

lemma sats_mem_formula_fm [simp]:
   "[| x \<in> nat; env \<in> list(A)|]
    ==> sats(A, mem_formula_fm(x), env) \<longleftrightarrow> mem_formula(##A, nth(x,env))"
by (simp add: mem_formula_fm_def mem_formula_def)

lemma mem_formula_iff_sats:
      "[| nth(i,env) = x; i \<in> nat; env \<in> list(A)|]
       ==> mem_formula(##A, x) \<longleftrightarrow> sats(A, mem_formula_fm(i), env)"
by simp



subsubsection\<open>The Predicate ``Is @{term "formula"}''\<close>

(* is_formula(M,Z) == \<forall>p[M]. p \<in> Z \<longleftrightarrow> mem_formula(M,p) *)
definition
  is_formula_fm :: "i=>i" where
    "is_formula_fm(Z) == Forall(Iff(Member(0,succ(Z)), mem_formula_fm(0)))"

lemma is_formula_type [TC]:
     "x \<in> nat ==> is_formula_fm(x) \<in> formula"
by (simp add: is_formula_fm_def)

lemma sats_is_formula_fm [simp]:
   "[| x \<in> nat; env \<in> list(A)|]
    ==> sats(A, is_formula_fm(x), env) \<longleftrightarrow> is_formula(##A, nth(x,env))"
by (simp add: is_formula_fm_def is_formula_def)

lemma is_formula_iff_sats:
      "[| nth(i,env) = x; i \<in> nat; env \<in> list(A)|]
       ==> is_formula(##A, x) \<longleftrightarrow> sats(A, is_formula_fm(i), env)"
by simp


subsubsection\<open>The Operator @{term is_transrec}\<close>

text\<open>The three arguments of @{term p} are always 2, 1, 0.  It is buried
   within eight quantifiers!
   We call @{term p} with arguments a, f, z by equating them with 
  the corresponding quantified variables with de Bruijn indices 2, 1, 0.\<close>

(* is_transrec :: "[i=>o, [i,i,i]=>o, i, i] => o"
   "is_transrec(M,MH,a,z) == 
      \<exists>sa[M]. \<exists>esa[M]. \<exists>mesa[M]. 
       2       1         0
       upair(M,a,a,sa) & is_eclose(M,sa,esa) & membership(M,esa,mesa) &
       is_wfrec(M,MH,mesa,a,z)" *)
definition
  is_transrec_fm :: "[i, i, i]=>i" where
 "is_transrec_fm(p,a,z) == 
    Exists(Exists(Exists(
      And(upair_fm(a#+3,a#+3,2),
       And(is_eclose_fm(2,1),
        And(Memrel_fm(1,0), is_wfrec_fm(p,0,a#+3,z#+3)))))))"


lemma is_transrec_type [TC]:
     "[| p \<in> formula; x \<in> nat; z \<in> nat |] 
      ==> is_transrec_fm(p,x,z) \<in> formula"
by (simp add: is_transrec_fm_def) 

lemma sats_is_transrec_fm:
  assumes MH_iff_sats: 
      "!!a0 a1 a2 a3 a4 a5 a6 a7. 
        [|a0\<in>A; a1\<in>A; a2\<in>A; a3\<in>A; a4\<in>A; a5\<in>A; a6\<in>A; a7\<in>A|] 
        ==> MH(a2, a1, a0) \<longleftrightarrow> 
            sats(A, p, Cons(a0,Cons(a1,Cons(a2,Cons(a3,
                          Cons(a4,Cons(a5,Cons(a6,Cons(a7,env)))))))))"
  shows 
      "[|x < length(env); z < length(env); env \<in> list(A)|]
       ==> sats(A, is_transrec_fm(p,x,z), env) \<longleftrightarrow> 
           is_transrec(##A, MH, nth(x,env), nth(z,env))"
apply (frule_tac x=z in lt_length_in_nat, assumption)  
apply (frule_tac x=x in lt_length_in_nat, assumption)  
apply (simp add: is_transrec_fm_def sats_is_wfrec_fm is_transrec_def MH_iff_sats [THEN iff_sym]) 
done


lemma is_transrec_iff_sats:
  assumes MH_iff_sats: 
      "!!a0 a1 a2 a3 a4 a5 a6 a7. 
        [|a0\<in>A; a1\<in>A; a2\<in>A; a3\<in>A; a4\<in>A; a5\<in>A; a6\<in>A; a7\<in>A|] 
        ==> MH(a2, a1, a0) \<longleftrightarrow> 
            sats(A, p, Cons(a0,Cons(a1,Cons(a2,Cons(a3,
                          Cons(a4,Cons(a5,Cons(a6,Cons(a7,env)))))))))"
  shows
  "[|nth(i,env) = x; nth(k,env) = z; 
      i < length(env); k < length(env); env \<in> list(A)|]
   ==> is_transrec(##A, MH, x, z) \<longleftrightarrow> sats(A, is_transrec_fm(p,i,k), env)" 
by (simp add: sats_is_transrec_fm [OF MH_iff_sats])


definition 
  is_Replace_fm :: "[i,i,i] \<Rightarrow> i" where
  "is_Replace_fm(a,p,z) == Forall(Iff(Member(0,succ(z)),
                                  Exists(And(Member(0,succ(succ(a))),p))))"

lemma is_Replace_type [TC]:
     "[| x \<in> nat; y \<in> nat; p\<in>formula |] ==> is_Replace_fm(x,p,y) \<in> formula"
  by (simp add:is_Replace_fm_def)

lemma sats_is_Rep_fm :
    assumes p_iff_sats: 
      "\<And>a b . a \<in> M \<Longrightarrow> b \<in> M \<Longrightarrow> 
          P(a,b) \<longleftrightarrow> sats(M, p, Cons(a, Cons(b, env)))"
    shows
   "[| x \<in> nat; y \<in> nat; env \<in> list(M)|]
    ==> sats(M, is_Replace_fm(x,p,y), env) \<longleftrightarrow>
        is_Replace(##M, nth(x,env), P , nth(y,env))"
  by (simp add: is_Replace_def is_Replace_fm_def p_iff_sats)

lemma Replace_iff_sats:
  assumes is_P_iff_sats: 
      "!!a b. [|a \<in> A; b \<in> A|] 
              ==> is_P(a,b) \<longleftrightarrow> sats(A, p, Cons(a,Cons(b,env)))"
  shows 
  "[| nth(i,env) = x; nth(j,env) = y;
      i \<in> nat; j \<in> nat; env \<in> list(A)|]
   ==> is_Replace(##A, x, is_P, y) \<longleftrightarrow> sats(A, is_Replace_fm(i,p,j), env)"
by (simp add: sats_is_Rep_fm [OF is_P_iff_sats])

(* "is_Collect(M,A,P,z) == \<forall>x[M]. x \<in> z \<longleftrightarrow> x \<in> A & P(x)" *)
definition 
  is_Collect_fm :: "[i,i,i] \<Rightarrow> i" where
  "is_Collect_fm(a,p,z) == Forall(Iff(Member(0,succ(z)),And(Member(0,succ(a)),p)))"

lemma is_Collect_type [TC]:
     "[| x \<in> nat; y \<in> nat; p\<in>formula |] ==> is_Collect_fm(x,p,y) \<in> formula"
  by (simp add:is_Collect_fm_def)

lemma sats_is_Collect_fm :
    assumes p_iff_sats: 
      "\<And>a. a \<in> M \<Longrightarrow>  
          P(a) \<longleftrightarrow> sats(M, p, Cons(a, env))"
    shows
   "[| x \<in> nat; y \<in> nat; env \<in> list(M)|]
    ==> sats(M, is_Collect_fm(x,p,y), env) \<longleftrightarrow>
        is_Collect(##M, nth(x,env), P , nth(y,env))"
  by (simp add: is_Collect_def is_Collect_fm_def p_iff_sats)

lemma Collect_iff_sats:
  assumes is_P_iff_sats: 
      "\<And>a b. a \<in> A 
              \<Longrightarrow> is_P(a) \<longleftrightarrow> sats(A, p, Cons(a,env))"
  shows 
  "[| nth(i,env) = x; nth(j,env) = y;
      i \<in> nat; j \<in> nat; env \<in> list(A)|]
   ==> is_Collect(##A, x, is_P, y) \<longleftrightarrow> sats(A, is_Collect_fm(i,p,j), env)"
by (simp add: sats_is_Collect_fm [OF is_P_iff_sats])

(* 
  This final segment must be preserved, perhaps in a file named like 
  this one.

  Note: sep_rules already appears in Constructible/Separation.thy, and
  this new  version is needed in Interface and Relative_Univ 
*)

lemma nth_closed :
  assumes "0\<in>A" "env\<in>list(A)"
  shows "nth(n,env)\<in>A" 
  using assms(2,1) unfolding nth_def by (induct env; simp)

lemmas FOL_sats_iff = sats_Nand_iff sats_Forall_iff sats_Neg_iff sats_And_iff
  sats_Or_iff sats_Implies_iff sats_Iff_iff sats_Exists_iff 

lemma nth_ConsI: "[|nth(n,l) = x; n \<in> nat|] ==> nth(succ(n), Cons(a,l)) = x"
by simp

lemmas nth_rules = nth_0 nth_ConsI nat_0I nat_succI
lemmas sep_rules = nth_0 nth_ConsI FOL_iff_sats function_iff_sats
                   fun_plus_iff_sats successor_iff_sats
                    omega_iff_sats FOL_sats_iff Replace_iff_sats

lemmas fm_defs = omega_fm_def limit_ordinal_fm_def empty_fm_def typed_function_fm_def
                 pair_fm_def upair_fm_def domain_fm_def function_fm_def succ_fm_def
                 cons_fm_def fun_apply_fm_def image_fm_def big_union_fm_def union_fm_def
                 relation_fm_def composition_fm_def field_fm_def ordinal_fm_def range_fm_def
                 transset_fm_def subset_fm_def is_Replace_fm_def


end
