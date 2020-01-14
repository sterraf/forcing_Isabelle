(* internalización de los axiomas de ZFC dentro de la teoría ZF *)

theory ZFCaxioms 
  imports 
  "Constructible/Formula" 
  "Constructible/L_axioms" 
  "src/Forcing_Data"

begin

(* 
   Extensionalidad 
   \<forall>x\<forall>y. \<forall>z(z\<in>x \<leftrightarrow> z\<in>y) \<rightarrow> x=y 
*)
definition
  ZF_extension_fm :: "i" where
  "ZF_extension_fm == 
      Forall(Forall(
             Implies(Forall(Iff(Member(0,2),Member(0,1))),
             Equal(0,1))))"

lemma ZF_extension_fm_type [TC]: "ZF_extension_fm \<in> formula"
  by (simp add: ZF_extension_fm_def)

lemma sats_ZF_extension_fm: "(A, [] \<Turnstile> ZF_extension_fm) \<longleftrightarrow> extensionality(##A)"
  unfolding extensionality_def ZF_extension_fm_def by auto

(*
  Fundación 
  \<forall>x. \<exists>y(y\<in>x) \<rightarrow> \<exists>y(y\<in>x \<and> \<not>\<exists>z(z\<in>x \<and> z\<in>y))
*)
definition 
  ZF_foundation_fm :: "i" where
  "ZF_foundation_fm == 
        Forall(Implies(
              Exists(Member(0,1)),
              Exists(And(Member(0,1),
                     Neg(Exists(And(Member(0,2),Member(0,1))))))))"

lemma ZF_foundation_fm_type [TC]: "ZF_foundation_fm \<in> formula"
  by (simp add: ZF_foundation_fm_def)

lemma sats_ZF_foundation_fm: "(A, [] \<Turnstile> ZF_foundation_fm) \<longleftrightarrow> foundation_ax(##A)"
  unfolding foundation_ax_def ZF_foundation_fm_def by auto

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
  ZF_separation_fm :: "i \<Rightarrow> i" where
  "ZF_separation_fm(p) == nForall(pred(arity(p)), 
                              Forall(Exists(Forall(
                              Iff(Member(0,1),And(Member(0,2),
                                              incr_bv(p)`1))))))"
                                                
lemma ZF_separation_fm_type [TC]: "p \<in> formula \<Longrightarrow> ZF_separation_fm(p) \<in> formula"
  by (simp add: ZF_separation_fm_def)

(*
  Pares
  \<forall>x\<forall>y\<exists>z. x\<in>z \<and> y\<in>z
*)
definition
  ZF_pairing_fm :: "i" where
  "ZF_pairing_fm == Forall(Forall(Exists(
                And(Member(2,0),Member(1,0)))))"

lemma ZF_pair_fm_type [TC]: "ZF_pairing_fm \<in> formula"
  by (simp add: ZF_pairing_fm_def)

(*
  Union
  \<forall>F\<exists>A\<forall>Y\<forall>x. (x\<in>Y \<and> Y\<in>F) \<rightarrow> x\<in>A
*)
definition
  ZF_union_fm :: "i" where
  "ZF_union_fm == Forall(Exists(Forall(Forall(
              Implies(And(Member(0,1),Member(1,3)),Member(0,2))))))"

lemma ZF_union_fm_type [TC]: "ZF_union_fm \<in> formula"
  by (simp add: ZF_union_fm_def)


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
  ZF_replacement_fm :: "i \<Rightarrow> i" where
  "ZF_replacement_fm(p) == 
      nForall(pred(pred(pred(arity(p)))),
      Forall(Implies(
        Forall(Implies(Member(0,1),ExistsU(incr_bv(p)`2))),
        Exists(Forall(Implies(Member(0,2),
                      Exists(And(Member(0,2),incr_bv(p)`2))))))))"

lemma ZF_replacement_fm_type [TC]: "p \<in> formula \<Longrightarrow> ZF_replacement_fm(p) \<in> formula"
  by (simp add: ZF_replacement_fm_def)

(* Infinito
   \<exists>x. \<emptyset>\<in>x \<and> \<forall>y(y\<in>x \<rightarrow> y U {y} \<in> x)
*)
definition
  ZF_infinity_fm :: "i" where
  "ZF_infinity_fm == 
      Exists(And(Exists(And(empty_fm(0),Member(0,1))),
             Forall(Implies(Member(0,1),
                    Exists(And(succ_fm(1,0),Member(0,2)))))))"

lemma ZF_infinity_fm_type [TC]: "ZF_infinity_fm \<in> formula"
  by (simp add: ZF_infinity_fm_def)

(* Powerset 
  \<forall>x\<exists>y\<forall>z. z\<subseteq>x \<rightarrow> z\<in>y 
*)
definition 
  ZF_powerset_fm :: "i" where
  "ZF_powerset_fm == Forall(Exists(Forall(
                 Implies(subset_fm(0,2),Member(0,1)))))"

lemma ZF_powerset_fm_type [TC]: "ZF_powerset_fm \<in> formula"
  by (simp add: ZF_powerset_fm_def)

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
  ZF_choice_fm :: "i" where
  "ZF_choice_fm == 
      Forall(Implies(
         Exists(And(empty_fm(0),And(Neg(Member(0,1)), 
                    ForallIn(1,ForallIn(2,Implies(Neg(Equal(1,0)),inter_fm(1,0,2))))))),
         Exists(ForallIn(1,ExistsU(And(Member(0,1),Member(0,2)))))))
            "
lemma ZF_choice_fm_type [TC]: "ZF_choice_fm \<in> formula"
  by (simp add: ZF_choice_fm_def)

definition
  ZF_fin :: "i" where
  "ZF_fin == {ZF_extension_fm,ZF_foundation_fm,ZF_pairing_fm,
              ZF_union_fm,ZF_infinity_fm,ZF_powerset_fm}"

definition
  ZFC_fin :: "i" where
  "ZFC_fin == {ZF_extension_fm,ZF_foundation_fm,ZF_pairing_fm,
              ZF_union_fm,ZF_infinity_fm,ZF_powerset_fm,ZF_choice_fm}"

lemma ZFC_fin_type : "ZFC_fin \<subseteq> formula"
  by (simp add:ZFC_fin_def)
  
definition
  ZFC_inf :: "i" where
  "ZFC_inf == {ZF_separation_fm(p) . p \<in> formula } \<union> {ZF_replacement_fm(p) . p \<in> formula }"
              
lemma unions : "A\<subseteq>formula \<and> B\<subseteq>formula \<Longrightarrow> A\<union>B \<subseteq> formula"
  by auto
  
lemma ZFC_inf_subset_formula : "ZFC_inf \<subseteq> formula"
  unfolding ZFC_inf_def by auto
    
definition
  ZFC :: "i" where
  "ZFC == ZFC_inf \<union> ZFC_fin"

definition
  ZF :: "i" where
  "ZF == ZFC_inf \<union> ZF_fin"

definition 
  ZF_minus_P :: "i" where
  "ZF_minus_P == {ZF_extension_fm,ZF_foundation_fm,ZF_pairing_fm,
              ZF_union_fm,ZF_infinity_fm,ZF_powerset_fm} \<union> ZFC_inf"

lemma ZFC_subset_formula: "ZFC \<subseteq> formula"
  by (simp add:ZFC_def unions ZFC_inf_subset_formula ZFC_fin_type)
  
txt\<open>Satisfaction of a set of sentences\<close>
definition
  satT :: "[i,i] => o"  ("_ \<Turnstile> _" 60) where
  "satT(A,\<Phi>) == \<forall> p \<in> \<Phi>. sats(A,p,[])"

lemma ACyZF_impZFC:
  assumes "sats(A,ZF_choice_fm,[])" "satT(A,ZF)"
  shows  "satT(A,ZFC)"
  using assms unfolding satT_def ZFC_def
    ZF_def ZF_fin_def ZFC_fin_def by blast

end