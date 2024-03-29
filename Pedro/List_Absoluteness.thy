theory List_Absoluteness
  imports
    "../src/FrecR"

begin
(* Sólo para referencia *)
theorem (in M_eclose) transrec_abs:
  "[|transrec_replacement(M,MH,i);  relation2(M,MH,H);
     Ord(i);  M(i);  M(z);
     \<forall>x[M]. \<forall>g[M]. function(g) \<longrightarrow> M(H(x,g))|]
   ==> is_transrec(M,MH,i,z) \<longleftrightarrow> z = transrec(i,H)"
  oops

definition
  app_lr :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where
  "app_lr(A,xs,ys) \<equiv> list_rec(\<lambda>l\<in>list(A). ys,
                            \<lambda>u us H. \<lambda>l\<in>list(A). Cons(u,H`ys),
                            xs
                           )`ys"

lemma app_lr_eq_app: "xs\<in> list(A) \<Longrightarrow> ys\<in>list(A) \<Longrightarrow> app_lr(A,xs,ys) = xs @ ys"
  unfolding app_lr_def 
  by (induct xs set:"list", simp_all)

txt\<open>list_rec es el recursor de listas. El teorema @{thm app_lr_eq_app} muestra cómo 
se expresa app (@) usándolo.

El teorema que sigue expresa list_rec con términos absolutos.\<close>
(*
lemma (in M_trivial) list_rec_eq: "ll \<in> list(A) \<Longrightarrow>
  list_rec(aa,g,ll) 
  = 
  transrec
    (succ(length(ll)),
     \<lambda>x h. Lambda(list(A),
                 list_case' (aa,
                             \<lambda>a l. g(a, l, h ` succ(length(l)) ` l)
                            )
                )
    ) ` ll"
*)

txt\<open>A continuación trato de escribir la versión relativa de list_rec.
La siguiente función toma is_g del "g" de arriba, y me da el "is" de
la expresión lambda que necesito como argumento de list_case'\<close>

definition
  change_args :: "[i\<Rightarrow>o,i,[i,i,i,i]\<Rightarrow>o,i] \<Rightarrow> ([i,i,i]\<Rightarrow>o)" where
  "change_args(M,A,is_g,h,a,l,z) \<equiv> \<exists>ln[M]. \<exists>sl[M]. \<exists>aphsl[M]. \<exists>apapl[M].
   \<exists>lA[M]. \<exists>om[M]. is_list(M,A,lA) \<and> omega(M,om) \<and> l \<in> lA \<and> ln \<in> om \<and> 
   is_length(M,A,l,ln) \<and> successor(M,ln,sl) \<and> fun_apply(M,h,sl,aphsl) 
   \<and> fun_apply(M,aphsl,l,apapl) \<and> is_g(a,l,apapl,z)"

context M_datatypes
begin

lemma Relation2_change_args:
  assumes "relation3(M,is_g,g)" "M(A)" "M(h)"
  shows "Relation2(M,B,list(A),change_args(M,A,is_g,h),\<lambda>a l. g(a,l, h ` succ(length(l)) ` l))"
  using assms length_type
  unfolding relation3_def Relation2_def change_args_def
  by simp

txt\<open>No puedo probar "relation2", sino la versión tipada, @{term Relation2},
porque necesito la assms de que las cosas son listas.
@{thm Relation2_change_args} muestra que @{term change_args} hace lo que debe\<close>

end (* M_datatypes *)

definition
  is_blc :: "[i\<Rightarrow>o,i,i,[i,i,i,i]\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_blc(M,A,aa,is_g,h,xs,z) \<equiv> is_list_case(M,aa,change_args(M,A,is_g,h),xs,z)"

definition
  Lam_list_case :: "[i, i,[i,i,i]\<Rightarrow>i,i,i] \<Rightarrow> i" where
  "Lam_list_case(A,aa,g,x,h) \<equiv>
          Lambda(list(A), 
                 list_case'(aa,
                           \<lambda>a l. g(a, l, h ` succ(length(l)) ` l)
                           )
                 )"

definition
  (* x is dumb           M   A aa       is_g   x *)
  is_Lam_list_case :: "[i\<Rightarrow>o,i, i,[i,i,i,i]\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_Lam_list_case(M,A,aa,is_g,x,h,z) \<equiv> \<exists>lA[M].
   is_list(M,A,lA) \<and> is_lambda(M,lA,is_blc(M,A,aa,is_g,h),z)"

definition
  is_list_rec :: "[i\<Rightarrow>o,i,i,[i,i,i,i]\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "is_list_rec(M,A,aa,is_g,ll,z)\<equiv> \<exists>ln[M]. \<exists>sl[M]. \<exists>tr[M].
    is_length(M,A,ll,ln) \<and> successor(M,ln,sl) \<and> 
    is_transrec(M,is_Lam_list_case(M,A,aa,is_g),sl,tr) \<and>
    fun_apply(M,tr,ll,z)"
(*  "is_list_rec(M,A,aa,is_g,ll,z)\<equiv> \<exists>om[M]. \<exists>ln[M]. \<exists>sl[M]. \<exists>tr[M]. \<exists>lA[M].
    is_list(M,A,lA) \<and> ll \<in> lA \<and> is_length(M,A,ll,ln) \<and> omega(M,om) \<and>
    ln \<in> om \<and> successor(M,ln,sl) \<and> 
    is_transrec(M,is_Lam_list_case(M,A,aa,is_g),sl,tr) \<and>
    fun_apply(M,tr,ll,z)"*)

context M_datatypes
begin

lemma relation2_change_args:
  assumes "relation3(M,is_g,g)" "M(A)" "M(h)"
  shows "relation2(M,change_args(M,A,is_g,h),\<lambda>a l. g(a,l, h ` succ(length(l)) ` l))"
  oops

txt\<open>Si tuviera relation2 (oops arriba), podría probar que is_blc
(abreviatura de "is_b con list_case'") se corresponde al
"is_b" que va a consumir is_lambda más abajo.\<close>

lemma Relation1_is_blc:
  assumes "relation3(M,is_g,g)" "M(A)"  "M(h)" "M(aa)"
  shows "Relation1(M,list(A),is_blc(M,A,aa,is_g,h),
                 list_case'(aa, \<lambda>a l. g(a, l, h ` succ(length(l)) ` l)))"
  unfolding Relation1_def is_blc_def using 
    list_case_abs[OF relation2_change_args, OF assms(1-3)]
  by (simp del:list_case'_eq_list_case)

lemma relation2_is_Lam_list_case:
  assumes 
    "relation3(M,is_g,g)" "M(A)" "M(aa)"
    "\<And>h a l. M(h) \<Longrightarrow> M(a) \<Longrightarrow> M(l) \<Longrightarrow>
        M(g(a, l, h ` succ(length(l)) ` l))"
    (* (* These two would suffice, but the second might not be true *)
    "\<And>h a l. M(h) \<Longrightarrow> M(a) \<Longrightarrow> M(l) \<Longrightarrow> M(g(a, l, h))"
    "\<And>l. M(l) \<Longrightarrow> M(length(l))"
    *)  
  shows
    "relation2(M,is_Lam_list_case(M,A,aa,is_g),Lam_list_case(A,aa,g))"
  using assms lambda_abs2[OF Relation1_is_blc[OF assms(1,2) _ assms(3)] list_closed[OF \<open>M(A)\<close>]]
  unfolding relation3_def relation2_def is_Lam_list_case_def Lam_list_case_def
  by (simp del:list_case'_eq_list_case)

end (* M_datatypes *)

context M_eclose
begin

lemma transrec_Lam_list_case_abs:
  assumes   
    "relation3(M,is_g,g)" "M(A)" "M(aa)" 
    "\<And>h a l. M(h) \<Longrightarrow> M(a) \<Longrightarrow> M(l) \<Longrightarrow> M(g(a,l,h`succ(length(l))`l))"
    "transrec_replacement(M,is_Lam_list_case(M,A,aa,is_g),i)"
    "Ord(i)" "M(i)" "M(z)"
    "\<forall>x[M]. \<forall>gg[M]. function(gg) \<longrightarrow> M(Lam_list_case(A,aa,g,x,gg))"
  shows 
    "is_transrec(M,is_Lam_list_case(M,A,aa,is_g),i,z) \<longleftrightarrow> z = transrec(i,Lam_list_case(A,aa,g))"
    using transrec_abs[OF assms(5) relation2_is_Lam_list_case[OF assms(1-4)] assms(6-9)]
    by simp

lemma list_rec_abs:
  assumes   
    "relation3(M,is_g,g)" "M(A)" "M(aa)" 
    "\<And>h a l. M(h) \<Longrightarrow> M(a) \<Longrightarrow> M(l) \<Longrightarrow> M(g(a,l,h`succ(length(l))`l))"
    "\<And>i. M(i) \<Longrightarrow> transrec_replacement(M,is_Lam_list_case(M,A,aa,is_g),i)"
    "M(z)"
    "\<forall>x[M]. \<forall>gg[M]. function(gg) \<longrightarrow> M(Lam_list_case(A,aa,g,x,gg))"
    "ll\<in>list(A)"
  shows 
    "is_list_rec(M,A,aa,is_g,ll,z) \<longleftrightarrow> z = list_rec(aa,g,ll)"
proof -
  from assms
  have "M(ll)" using transM[of _ "list(A)"] by simp
  with assms
  show ?thesis
    using transrec_Lam_list_case_abs[OF assms(1-5) _ _ assms(6,7)] 
    unfolding is_list_rec_def
    apply (simp add:list_rec_eq)
  oops

end (* M_eclose *)
end