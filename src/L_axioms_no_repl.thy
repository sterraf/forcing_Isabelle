(*  Title:      ZF/Constructible/L_axioms.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
*)

section \<open>The ZF Axioms (Except Separation) in L\<close>

theory L_axioms_no_repl 
  imports 
    "~~/src/ZF/Constructible/Formula"
    Relative_no_repl   
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
by (simp add: subset_fm_def Relative_no_repl.subset_def)

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
by (simp add: image_fm_def Relative_no_repl.image_def)

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
by (simp add: pre_image_fm_def Relative_no_repl.pre_image_def)

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

end
