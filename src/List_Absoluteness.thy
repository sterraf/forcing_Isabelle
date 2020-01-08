theory List_Absoluteness
  imports
    "../Constructible/Datatype_absolute"
    Internalizations
    Recursion_Thms

begin

lemma (in M_datatypes) length_abs [simp]:
     "[|M(A); l \<in> list(A); n \<in> nat|] ==> is_length(M,A,l,n) \<longleftrightarrow> n = length(l)"
  oops

lemma (in M_trivial) length_closed [intro,simp]:
     "l \<in> list(A) ==> M(length(l))"
  oops

lemma (in M_trivial) list_case_abs [simp]:
     "[| relation2(M,is_b,b); M(k); M(z) |]
      ==> is_list_case(M,a,is_b,k,z) \<longleftrightarrow> z = list_case'(a,b,k)"
  oops

lemma (in M_basic) list_case'_closed [intro,simp]:
  "[|M(k); M(a); \<forall>x[M]. \<forall>y[M]. M(b(x,y))|] ==> M(list_case'(a,b,k))"
  oops

theorem (in M_eclose) transrec_abs:
  "[|transrec_replacement(M,MH,i);  relation2(M,MH,H);
     Ord(i);  M(i);  M(z);
     \<forall>x[M]. \<forall>g[M]. function(g) \<longrightarrow> M(H(x,g))|]
   ==> is_transrec(M,MH,i,z) \<longleftrightarrow> z = transrec(i,H)"
  oops

lemma (in M_trivial) list_rec_eq:
  "l \<in> list(A) \<Longrightarrow>
   list_rec(a,g,l) = 
   transrec (succ(length(l)),
      \<lambda>x h. Lambda (list(A),
                    list_case' (a, 
                           \<lambda>a l. g(a, l, h ` succ(length(l)) ` l)))) ` l"
  oops

definition
  app_lr :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where
  "app_lr(A,xs,ys) \<equiv> list_rec(\<lambda>l\<in>list(A). ys,
                            \<lambda>u us H. \<lambda>l\<in>list(A). Cons(u,H`ys),
                            xs
                           )`ys"

lemma "xs\<in> list(A) \<Longrightarrow> ys\<in>list(A) \<Longrightarrow> app_lr(A,xs,ys) = xs @ ys"
  unfolding app_lr_def 
  by (induct xs set:"list", simp_all)

definition
  is_blr :: "[i\<Rightarrow>o,i,[i,i,i] \<Rightarrow> i,i,i,i,i,i] \<Rightarrow> o" where
  "is_blr(M,aa,g,x,h,a,l,z) \<equiv> z = g(a,l,h`succ(length(l))`l)" 

definition
  is_Hlr :: "[i\<Rightarrow>o,i,i,[i,i,i] \<Rightarrow> i,i,i,i] \<Rightarrow> o" where 
  "is_Hlr(M,lA,a,g,x,h,z) \<equiv> is_lambda(M,lA,is_list_case(M,a,is_blr(M,a,g,x,h)),z)"

end