theory my_playground imports Formula L_axioms Cardinal begin

section\<open>Training in Isabelle proofs\<close>  
text\<open>The next lemma is just an experiment to have a proof of a proposition P==>P\<close>
lemma trivial_FO_implication:
  assumes "\<exists>x\<in>Z .  \<forall>y. P(x,y,Z) \<longrightarrow> Q(x,y,Z)"
  shows "\<exists>x\<in>Z .  \<forall>y. P(x,y,Z) \<longrightarrow> Q(x,y,Z)"
proof -
  show ?thesis using assms .
  text\<open>Otra opción es usar 
  show ?thesis using assms by simp\<close>
qed
  
(* A true result of FO logic *)    
lemma reinforce_antecedent:
  assumes p:"\<exists>x\<in>Z .  \<forall>y. P(x,y,Z) \<longrightarrow> Q(x,y,Z)"
  shows "\<exists>x\<in>Z .  \<forall>y. R(x,y) \<and> P(x,y,Z) \<longrightarrow> Q(x,y,Z)"
proof -
  show ?thesis using p by blast
qed

lemma reinforce_antecedent_no_vars:
  assumes p:"\<exists>x\<in>Z .  \<forall>y. (P \<longrightarrow> Q)"
  shows "\<exists>x\<in>Z .  \<forall>y. (R \<and> P \<longrightarrow> Q)"
proof -
  show ?thesis using p by blast
qed
  
section\<open>Experiments with type formula\<close>
definition 
  pedro :: "i" where
  "pedro == Exists(Exists(Neg(Equal(0,1))))"

definition 
  a :: "i" where
  "a == {0,1}"

lemma choto: "1 \<union> 2 = 2" 
  by auto

lemma arityp: "arity(pedro) = 0"
  apply (unfold pedro_def)
  apply (simp add: choto)
  done
    
lemma pedroempty: "sats(a,pedro,[])"
  apply(unfold a_def)
  apply(unfold pedro_def)
  apply(auto)
  done

lemma "env \<in> list(a) \<Longrightarrow> sats(a,pedro,env)"
  apply(unfold a_def)
  apply(unfold pedro_def)
  apply(auto)
  done

lemma "[] \<in> list(0)"
  apply (auto)
  done


section\<open>Internalized ZFC Axioms\<close>

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

lemma ZFC_fin_type : "ZFC_fin \<subseteq> formula"
  by (simp add:ZFC_fin_def)
  
definition
  ZFC_inf :: "i" where
  "ZFC_inf == {ZFseparation(p) . p \<in> formula } \<union> {ZFreplacement(p) . p \<in> formula }"
              
lemma unions : "A\<subseteq>formula \<and> B\<subseteq>formula \<Longrightarrow> A\<union>B \<subseteq> formula"
  by auto
  
lemma ZFC_inf_type : "ZFC_inf \<subseteq> formula"
  apply(unfold ZFC_inf_def)
  (* apply(auto) (*aquí lo finiquita*) *)
  apply(rule unions)
  apply(rule conjI)    
proof -
  show "{ZFseparation(p) . p \<in> formula }\<subseteq>formula" by auto  
                         (* no sé cómo decir "by simp using ZFsep_type" *)
next
  show "{ZFreplacement(p) . p \<in> formula }\<subseteq>formula" by auto
qed
  
(* Teoría ZFC internalizada *)
definition
  ZFCTh :: "i" where
  "ZFCTh == ZFC_fin \<union> ZFC_inf"

lemma "ZFCTh \<subseteq> formula"
  by (simp add:ZFCTh_def add:unions add:ZFC_inf_type add:ZFC_fin_type)
  
(* satisfacción de un conjunto de fórmulas *)
definition
  satT :: "[i,i,i] => o" where
  "satT(A,\<Phi>,env) == \<forall> p \<in> \<Phi>. sats(A,p,env)"



subsection\<open>Absoluteness of transitivity\<close>
(* transitividad *)
definition 
  ZFtrans :: "i" where
  "ZFtrans == Forall(Forall(Implies(And(Member(0,1),
                            Member(1,2)),Member(0,2))))"

definition
  M1 :: "i" where
  "M1 == {0 , 2 , {2 , 0}}"

definition
  M2 :: "i" where
  "M2 == {0 , 1 , 2 , {2 , 0}}"


lemma l1 :
  "2 \<notin> 1"
  apply auto
  done

lemma l2 :
  "{2,0} \<noteq> 1"
  apply (unfold extension)
  apply (simp add: l1)
  done

lemma l1' :
  "2 \<notin> 2"
  apply auto
  done

lemma l2' :
  "{2,0} \<noteq> 2"
  apply (unfold extension)
  apply (simp add: l1')
  done


lemma absolute_fail : 
  "sats(M1,ZFtrans,[{2,0}])"
  apply (unfold ZFtrans_def)
  apply (unfold M1_def)
  apply (simp)
  apply (auto)
  apply (simp add: l2, simp add: l2')
  done

lemma absolute_hold : 
  "sats(M2,Neg(ZFtrans),[{2,0}])"
  apply (unfold ZFtrans_def)
  apply (unfold M2_def)
  apply (simp)
  done

section\<open>Well founded relations\<close>
definition
  rel :: "[i,i] \<Rightarrow> o" where
  "rel(x,y) == \<exists>z . z \<in> y \<and> (\<exists>w . w \<in> z \<and> x \<in> w)"

definition
  relSet :: "i \<Rightarrow> i" where
  "relSet(M) == { z \<in> M*M . rel(fst(z),snd(z)) }"

lemma relSet_coord : "<x,y>\<in>relSet(M) \<Longrightarrow> \<exists>z . z \<in> y \<and> (\<exists>w . w \<in> z \<and> x \<in> w)"
by (simp add:relSet_def rel_def )

lemma fld_rel_sub_eclose : "\<lbrakk>xa \<in> M; y \<in> M ; z \<in> y ; w \<in> z; xa \<in> w\<rbrakk> \<Longrightarrow> 
                            z \<in> eclose(M) \<and> w \<in> eclose(M)"
  apply (simp add:ecloseD)
proof - 
  assume p:"y\<in>M"
  assume q: "z\<in>y"
  show "z\<in>eclose(M)"
  proof - 
  have r:"M\<subseteq>eclose(M)" by (rule arg_subset_eclose)
  from p and r  have "y\<in>eclose(M)" by (simp add:subsetD)
  then show ?thesis using q  by (simp add:ecloseD)
  qed
qed
  
lemma dom_memrel : "domain(Memrel(A))\<subseteq>A"
  by clarify

lemma ran_memrel : "range(Memrel(A))\<subseteq>A"
  by clarify

lemma dom_mem_eclo :"domain(Memrel(eclose(M)))=eclose(M)"
(*proof
  show "domain(Memrel(eclose(M)))\<subseteq>eclose(M)" by (rule_tac A="eclose(M)" in dom_memrel)
  (* rule_tac se puede eliminar en favor de             *
   *   (simp add:dom_memrel)                            *)
*)
  apply standard             
  apply (rule_tac A="eclose(M)" in dom_memrel)
  apply (unfold eclose_def)
  apply (unfold domain_def)
  apply clarify
  (* apply (rule_tac nat_induct) *)
oops

lemma rel_sub_memcomp : "relSet(M) \<subseteq> Memrel(eclose(M)) O Memrel(eclose(M)) O Memrel(eclose(M))"
  apply (unfold relSet_def)
  apply (unfold rel_def)
  apply (simp add:comp_def)
  apply clarify
  apply (simp add:snd_def)
  (* relevant fact? comp_def *)
sorry
  
lemma memcomp_sub_trmem : "Memrel(eclose(M)) O Memrel(eclose(M))O Memrel(eclose(M))
                          \<subseteq> trancl(Memrel(eclose(M)))"
  apply clarify
  apply simp
  apply (unfold trancl_def)
(* proof -
  assume p:"xb\<in>ya" and q:"xb\<in>eclose(M)" and r:"ya\<in>eclose(M)"
  from p and q and r    
  have s:"<xb,ya>\<in>Memrel(eclose(M))".. *)
sorry
  
lemma wf_trmem : "wf(trancl(Memrel(eclose(M))))"
(*  apply (simp add:wf_trancl) no anda aquí *)
  apply (rule wf_trancl)
  apply (simp add:wf_Memrel)
done

lemma wf_memcomp : "wf(Memrel(eclose(M)) O Memrel(eclose(M)) O Memrel(eclose(M)))"
  apply (rule wf_subset)
  apply (rule wf_trmem)
  apply (rule memcomp_sub_trmem)
done

lemma wf_relSet : "wf(relSet(M))"
  apply (rule wf_subset)
  apply (rule wf_memcomp)
  apply (rule rel_sub_memcomp)
done

  
(*
lemma WFrel : "wf(relSet(M))"
  apply(unfold wf_def)
  apply(rule allI)
  apply(case_tac "Z=0")
  apply(rule disjI1;auto)
  apply(rule disjI2)
  apply(simp add:relSet_def add:rel_def add:WFrel_auxM)
  done
*)

section\<open>Posets\<close>  
text\<open>Reflexivity in three forms\<close>

definition 
  reflexivity_abs :: "[i,i] \<Rightarrow> o" where
  "reflexivity_abs(P,r) == \<forall>p . p\<in>P \<longrightarrow> <p,p>\<in>r"

definition  
  reflexivity_rel :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "reflexivity_rel(M,P,r) == \<forall>p[M].  p\<in>P \<longrightarrow> (\<exists>x[M]. pair(M,p,p,x) \<and> x\<in>r)"

definition
  reflexivity_fm :: "[i,i]\<Rightarrow>i" where
  "reflexivity_fm(x,y) == Forall(Implies(Member(0,succ(x)),
                     Exists(And(pair_fm(1,1,0),Member(0,succ(succ(y)))))))"

lemma reflexivity_type : "\<lbrakk>x\<in>nat ; y\<in>nat\<rbrakk> \<Longrightarrow> reflexivity_fm(x,y)\<in>formula"
  by (simp add:reflexivity_fm_def)

  
section\<open>Anomalous calculations\<close>
text\<open>Here I put some anomalous lemmata, showing the typelessness of set theory.\<close>

lemma emptylist_is_pair :
  "Nil = {{0}}"
  apply (unfold Nil_def)
  apply (unfold Inl_def)
  apply (unfold Pair_def)
  apply (auto)
  done

lemma formula_is_set :
  "Member(0,0) \<noteq> 0"
  apply (unfold Member_def)
  apply (unfold Inl_def)
  apply (auto)
  done    

(*
lemma card_of_pair :
  "cardinal(Pair(x,y)) = 2"
  sorry
    
lemma card_of_formula :
  "cardinal(Member(1,2)) = 2"
  apply (unfold Member_def)
  apply (unfold Inl_def)
  apply (simp add:card_of_pair)
  done
*)
end

