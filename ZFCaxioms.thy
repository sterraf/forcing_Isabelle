(* internalización de los axiomas de ZFC dentro de la teoría ZF *)

theory ZFCaxioms imports Formula L_axioms begin

(* 
   Extensionalidad 
   \<forall>x\<forall>y. \<forall>z(z\<in>x \<leftrightarrow> z\<in>y) \<rightarrow> x=y 
*)
definition
  ZFextension :: "i" where
  "ZFextension == 
      Forall(Forall(
             Implies(Forall(Iff(Member(0,2),Member(0,1))),
             Equal(0,1))))"

lemma ZFext_type [TC]: "ZFextension \<in> formula"
  by (simp add: ZFextension_def)

(*
  Fundación 
  \<forall>x. \<exists>y(y\<in>x) \<rightarrow> \<exists>y(y\<in>x \<and> \<not>\<exists>z(z\<in>x \<and> z\<in>y))
*)
definition 
  ZFfoundation :: "i" where
  "ZFfoundation == 
        Forall(Implies(
              Exists(Member(0,1)),
              Exists(And(Member(0,1),
                     Neg(Exists(And(Member(0,2),Member(0,1))))))))"

lemma ZFfound_type [TC]: "ZFfoundation \<in> formula"
  by (simp add: ZFfoundation_def)

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
  \<forall>v\<exists>y\<forall>x. x\<in>y \<leftrightarrow> x\<in>v \<and> \<Phi>
*)
definition
  ZFseparation :: "i \<Rightarrow> i" where
  "ZFseparation(p) == nForall(pred(pred(arity(p))), 
                              Forall(Exists(Forall(
                              Iff(Member(0,1),And(Member(0,2),
                                              incr_bv(p)`1))))))"

lemma ZFsep_type [TC]: "p \<in> formula \<Longrightarrow> ZFseparation(p) \<in> formula"
  by (simp add: ZFseparation_def)

(*
  Pares
  \<forall>x\<forall>y\<exists>z. x\<in>z \<and> y\<in>z
*)
definition
  ZFpairing :: "i" where
  "ZFpairing == Forall(Forall(Exists(
                And(Member(2,0),Member(1,0)))))"

lemma ZFpair_type [TC]: "ZFpairing \<in> formula"
  by (simp add: ZFpairing_def)

(*
  Union
  \<forall>F\<exists>A\<forall>Y\<forall>x. (x\<in>Y \<and> Y\<in>F) \<rightarrow> x\<in>A
*)
definition
  ZFunion :: "i" where
  "ZFunion == Forall(Exists(Forall(Forall(
              Implies(And(Member(0,1),Member(1,3)),Member(0,2))))))"

lemma ZFunion_type [TC]: "ZFunion \<in> formula"
  by (simp add: ZFunion_def)


(* Existe único *)
definition
  ExistsU :: "i \<Rightarrow> i" where
  "ExistsU(p) == Exists(And(p,Forall(Implies(Neg(Equal(0,1)),Neg(p)))))"

lemma ZFExistsU_type [TC]: "p \<in> formula \<Longrightarrow> ExistsU(p) \<in> formula"
  by (simp add: ExistsU_def)

(* Esquema de reemplazo
   Sea \<Phi> fórmula, donde B no es libre.
   \<forall>A. \<forall>x(x\<in>A \<longrightarrow> \<exists>!y \<Phi>) \<longrightarrow> \<exists>B \<forall>x(x\<in>A \<longrightarrow> \<exists>y(y\<in>B \<and> \<Phi>))
*)
definition
  ZFreplacement :: "i \<Rightarrow> i" where
  "ZFreplacement(p) == 
      nForall(pred(pred(pred(arity(p)))),
      Forall(Implies(
        Forall(Implies(Member(0,1),ExistsU(incr_bv(p)`2))),
        Exists(Forall(Implies(Member(0,2),
                      Exists(And(Member(0,2),incr_bv(p)`2))))))))"

lemma ZFrep_type [TC]: "p \<in> formula \<Longrightarrow> ZFreplacement(p) \<in> formula"
  by (simp add: ZFreplacement_def)

(* Infinito
   \<exists>x. \<emptyset>\<in>x \<and> \<forall>y(y\<in>x \<rightarrow> y U {y} \<in> x)
*)
definition
  ZFinfinity :: "i" where
  "ZFinfinity == 
      Exists(And(Exists(And(empty_fm(0),Member(0,1))),
             Forall(Implies(Member(0,1),
                    Exists(And(succ_fm(1,0),Member(0,2)))))))"

lemma ZFinf_type [TC]: "ZFinfinity \<in> formula"
  by (simp add: ZFinfinity_def)

(* Powerset 
  \<forall>x\<exists>y\<forall>z. z\<subseteq>x \<rightarrow> z\<in>y 
*)
definition 
  ZFpowerset :: "i" where
  "ZFpowerset == Forall(Exists(Forall(
                 Implies(subset_fm(0,2),Member(0,1)))))"

lemma ZFpower_type [TC]: "ZFpowerset \<in> formula"
  by (simp add: ZFpowerset_def)

(* Intersección internalizada *)
definition
  inter_fm :: "[i,i,i] \<Rightarrow> i" where
  "inter_fm(x,y,z) == Forall(Iff(Member(0,z),
                             And(Member(0,x),Member(0,y))))"
lemma inter_type [TC]: 
      "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> inter_fm(x,y,z) \<in> formula"
  by (simp add: inter_fm_def)

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
  ZFchoice :: "i" where
  "ZFchoice == 
      Forall(Implies(
         Exists(And(empty_fm(0),And(Neg(Member(0,1)), 
                    ForallIn(1,ForallIn(2,Implies(Neg(Equal(1,0)),inter_fm(1,0,2))))))),
         Exists(ForallIn(1,ExistsU(And(Member(0,1),Member(0,2)))))))
            "
lemma ZFchoice_type [TC]: "ZFchoice \<in> formula"
  by (simp add: ZFchoice_def)

definition
  ZFC_fin :: "i" where
  "ZFC_fin == {ZFextension,ZFfoundation,ZFpairing,
              ZFunion,ZFinfinity,ZFpowerset,ZFchoice}"

definition
  ZFC_inf :: "i" where
  "ZFC_inf == (\<lambda>p \<in> formula. ZFseparation(p)) \<union>
              (\<lambda>p \<in> formula. ZFreplacement(p))"

(* Teoría ZFC internalizada *)
definition
  ZFCTh :: "i" where
  "ZFCTh == ZFC_fin \<union> ZFC_inf"

(* satisfacción de un conjunto de fórmulas *)
definition
  satT :: "[i,i,i] => o" where
  "satT(A,\<Phi>,env) == \<forall> p \<in> \<Phi>. sats(A,p,env)"



(*
lemma "sats(A,Forall(transset_fm(0)),[]) \<and> 
       satT(A,ZFCTh,[])  
       \<Longrightarrow> PROP M_trivial(##A)"
*)

definition
  rel :: "[i,i] \<Rightarrow> o" where
  "rel(x,y) == \<exists>z . z \<in> y \<longrightarrow> (\<exists>w . w \<in> z \<longrightarrow> x \<in> w)"

definition
  relSet :: "i \<Rightarrow> i" where
  "relSet(M) == {z\<in>M. \<exists>x. \<exists>y. z=\<langle>x,y\<rangle> \<and> rel(x,y)}"

lemma WFrel : "wf(relSet(M))"
  apply(unfold relSet_def)
  apply(unfold wf_def)
  apply(rule allI)
  
  


