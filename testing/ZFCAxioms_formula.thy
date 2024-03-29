(* internalización de los axiomas de ZFC dentro de la teoría ZF *)

theory ZFCAxioms_formula imports Formula L_axioms_no_repl Swap_vars begin

(* 
   Extensionalidad 
   \<forall>x\<forall>y. \<forall>z(z\<in>x \<leftrightarrow> z\<in>y) \<rightarrow> x=y 
*)
definition
  extension_ax_fm :: "i" where
  "extension_ax_fm == 
      Forall(Forall(
             Implies(Forall(Iff(Member(0,2),Member(0,1))),
             Equal(1,0))))"

lemma ext_type [TC]: "extension_ax_fm \<in> formula"
  by (simp add: extension_ax_fm_def)

(*
  Fundación 
  \<forall>x. \<exists>y(y\<in>x) \<rightarrow> \<exists>y(y\<in>x \<and> \<not>\<exists>z(z\<in>x \<and> z\<in>y))
*)
definition 
  foundation_ax_fm :: "i" where
  "foundation_ax_fm == 
        Forall(Implies(
              Exists(Member(0,1)),
              Exists(And(Member(0,1),
                     Neg(Exists(And(Member(0,2),Member(0,1))))))))"

lemma found_type [TC]: "foundation_ax_fm \<in> formula"
  by (simp add: foundation_ax_fm_def)

(*
  Pares
  \<forall>a\<forall>b\<exists>z. a \<in> z & b \<in> z & (\<forall>x. x\<in>z \<longrightarrow> x = a | x = b)
*)
definition
  pairing_ax_fm :: "i" where
  "pairing_ax_fm == Forall(Forall(Exists(upair_fm(2,1,0))))"

lemma ZFpair_type [TC]: "pairing_ax_fm \<in> formula"
  by (simp add: pairing_ax_fm_def)

(*
  Union
  \<forall>A\<exists>z\<forall>x. x \<in> z \<longleftrightarrow> (\<exists>y. y\<in>A & x \<in> y)
*)
definition
  union_ax_fm :: "i" where
  "union_ax_fm == Forall(Exists(big_union_fm(1,0)))"

lemma union_type [TC]: "union_ax_fm \<in> formula"
  by (simp add: union_ax_fm_def)

(* Infinito
   \<exists>x. \<emptyset>\<in>x \<and> \<forall>y(y\<in>x \<rightarrow> y U {y} \<in> x)
*)
definition
  infinity_ax_fm :: "i" where
  "infinity_ax_fm == 
      Exists(And(Exists(And(empty_fm(0),Member(0,1))),
             Forall(Implies(Member(0,1),
                    Exists(And(succ_fm(1,0),Member(0,2)))))))"

lemma inf_type [TC]: "infinity_ax_fm \<in> formula"
  by (simp add: infinity_ax_fm_def)

(* Powerset 
  \<forall>x\<exists>y\<forall>z. z\<in>y \<longleftrightarrow> z\<subseteq>x
*)
definition 
  powerset_ax_fm :: "i" where
  "powerset_ax_fm == Forall(Exists(Forall(
                 Iff(Member(0,1),subset_fm(0,2)))))"

lemma ZFpower_type [TC]: "powerset_ax_fm \<in> formula"
  by (simp add: powerset_ax_fm_def)


definition
  ZF_fin :: "i" where
  "ZF_fin == {extension_ax_fm,foundation_ax_fm,pairing_ax_fm,
              union_ax_fm,infinity_ax_fm,powerset_ax_fm}"

(* Elección *)
(* Intersección internalizada *)
definition
  inter_fm :: "[i,i,i] \<Rightarrow> i" where
  "inter_fm(x,y,z) == Forall(Iff(Member(0,z),
                             And(Member(0,x),Member(0,y))))"
lemma inter_type [TC]: 
      "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> inter_fm(x,y,z) \<in> formula"
  by (simp add: inter_fm_def)

(* Existe único *)
definition
  ExistsU :: "i \<Rightarrow> i" where
  "ExistsU(p) == Exists(And(p,Forall(Implies(Neg
                       (Equal(0,1)),Neg(incr_bv1(p))))))"

lemma ExistsU_type [TC]: "p \<in> formula \<Longrightarrow> ExistsU(p) \<in> formula"
  by (simp add: ExistsU_def)


(* Abreviación para \<forall>x\<in>C.F *)
definition
  ForallIn :: "[i,i] \<Rightarrow> i" where
  "ForallIn(x,p) = Forall(Implies(Member(0,succ(x)),p))"

lemma ForallIn_type [TC]: 
      "[| x \<in> nat; p \<in> formula |] ==> ForallIn(x,p) \<in> formula"
  by (simp add: ForallIn_def)

(* Elección
  \<forall>F. \<emptyset>\<notin>F \<and> \<forall>x\<in>F\<forall>y\<in>F (x\<noteq>y \<rightarrow> x\<inter>y=\<emptyset>))) \<rightarrow> \<exists>C\<forall>x\<in>F (\<exists>!y (y\<in>x \<and> y\<in>C))
*)
definition
  choice_ax_fm :: "i" where
  "choice_ax_fm == 
      Forall(Implies(
         Exists(And(empty_fm(0),And(Neg(Member(0,1)), 
                    ForallIn(1,ForallIn(2,Implies(Neg(Equal(1,0)),inter_fm(1,0,2))))))),
         Exists(ForallIn(1,ExistsU(And(Member(0,1),Member(0,2)))))))
            "
lemma choice_type [TC]: "choice_ax_fm \<in> formula"
  by (simp add: choice_ax_fm_def)

(* Esquemas *)

(* fórmula compuesta por n veces Forall *)
consts 
  nForall :: "[i,i] \<Rightarrow> i"
primrec
  "nForall(0,p) = p"
  "nForall(succ(n),p) = Forall(nForall(n,p))" 

lemma nForall_type [TC]: 
      "[| n \<in> nat; p \<in> formula |] ==> nForall(n,p) \<in> formula"
  by (induct_tac "n",auto)

(*
  Esquema de separación
  Sea \<Phi> fórmula, donde 'y' no es libre.
  \<forall>a1...an\<forall>v\<exists>y\<forall>x. x\<in>y \<leftrightarrow> x\<in>v \<and> \<Phi>(x,v,a1,...,an)

  Ejemplo: Si \<Phi> = x=a \<or> x=b entonces
              p debe ser 0=2 \<or> 0=3
*)
definition
  separation_ax_fm :: "i \<Rightarrow> i" where
  "separation_ax_fm(\<phi>) == nForall(pred(pred(arity(\<phi>))),
                              Forall(Exists(Forall(
                              Iff(Member(0,1),And(Member(0,2),
                                              incr_bv1(\<phi>)))))))"
                                                
lemma sep_type [TC]: "p \<in> formula \<Longrightarrow> separation_ax_fm(p) \<in> formula"
  by (simp add: separation_ax_fm_def)

(* Esquema de reemplazo (strong)
   Sea \<Phi> fórmula, donde B no es libre.
   \<forall>A. \<forall>x(x\<in>A \<longrightarrow> \<exists>!y \<Phi>(y,x)) \<longleftrightarrow> \<exists>B \<forall>y(y\<in>B \<longleftrightarrow> \<exists>x(x\<in>A \<and> \<Phi>(y,x)))
*)

  (*  
    "univalent(M,A,P) ==
        \<forall>x[M]. x\<in>A \<longrightarrow> (\<forall>y[M]. `\<forall>z[M]. P(x,y) & P(x,z) \<longrightarrow> y=z)" 
    En la fórmula \<phi> la correspondencia entre las variables nombradas
    es 0 \<longrightarrow> x
       1 \<longrightarrow> y
       2 \<longrightarrow> A
       resto \<longrightarrow> params   *)
definition
  univalent_fm :: "i \<Rightarrow> i" where
  "univalent_fm(\<phi>) == 
      Forall(Implies(Member(0,1),
      Forall(Forall(Implies(And(incr_bv(swap_0_1(\<phi>))`0,incr_bv1(swap_0_1(\<phi>))),Equal(1,0))))))"

lemma univalent_fm_type [TC] : 
  "\<lbrakk> \<phi> \<in> formula \<rbrakk> \<Longrightarrow> univalent_fm(\<phi>) \<in> formula"
  by (simp add: univalent_fm_def)
  

(*
"strong_replacement(M,P) ==
      \<forall>A[M]. univalent(M,A,P) \<longrightarrow>
      (\<exists>Y[M]. \<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x\<in>A & P(x,b)))"

  \<phi> es de la forma \<phi>(x,y,A,p1..pn)
*)
definition
  strong_replacement_ax_fm :: "i \<Rightarrow> i" where
  "strong_replacement_ax_fm(p) == 
      nForall(pred(pred(pred(arity(p)))),
      Forall(Implies(univalent_fm(p),
        Exists(Forall(Iff(Member(0,1),Exists(And(Member(0,3),
                      incr_bv(p)`2))))))))"

lemma rep_type [TC]: "p \<in> formula \<Longrightarrow> strong_replacement_ax_fm(p) \<in> formula"
  by (simp add: strong_replacement_ax_fm_def)

definition
  ZF_inf :: "i" where
  "ZF_inf == {separation_ax_fm(p) . p \<in> formula } \<union> {strong_replacement_ax_fm(p) . p \<in> formula }"
              
lemma unions : "A\<subseteq>formula \<and> B\<subseteq>formula \<Longrightarrow> A\<union>B \<subseteq> formula"
  by auto
  
lemma ZF_inf_type : "ZF_inf \<subseteq> formula"
  apply(unfold ZF_inf_def)
  apply(auto)
  done
    
(* Teoría ZF *)
definition
  ZFTh :: "i" where
  "ZFTh == ZF_inf \<union> ZF_fin"

(* Teoría ZFC *)
definition
  ZFCTh :: "i" where
  "ZFCTh == ZFTh \<union> {choice_ax_fm}"

  
(* satisfacción de un conjunto de fórmulas *)
definition
  satT :: "[i,i,i] => o" where
  "satT(A,\<Phi>,env) == \<forall> p \<in> \<Phi>. sats(A,p,env)"

lemma satT_sats : 
  "\<lbrakk> satT(M,\<Phi>,env) ; \<phi> \<in> \<Phi> \<rbrakk> \<Longrightarrow> sats(M,\<phi>,env)"
  by (simp add: satT_def)

lemma sep_spec : 
  "\<lbrakk> satT(M,ZFTh,env) ; \<phi> \<in> formula \<rbrakk> \<Longrightarrow>
    sats(M,separation_ax_fm(\<phi>),env)"
  apply (rule satT_sats,assumption)
  apply (simp add: ZFTh_def ZF_inf_def)
  apply auto
  done

lemma repl_spec :
  "\<lbrakk> satT(M,ZFTh,env) ; \<phi> \<in> formula \<rbrakk> \<Longrightarrow>
    sats(M,strong_replacement_ax_fm(\<phi>),env)"
  apply (rule satT_sats,assumption)
  apply (simp add: ZFTh_def ZF_inf_def)
  apply auto
  done
    


end
