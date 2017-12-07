theory my_playground imports Formula L_axioms Cardinal begin

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


(* satisfacción de un conjunto de fórmulas *)
definition
  satT :: "[i,i,i] => o" where
  "satT(A,\<Phi>,env) == \<forall> p \<in> \<Phi>. sats(A,p,env)"

section\<open>ZFC axioms in type formula\<close>
(* Axiomas ZF internalizados en ZF *)

(* extension "A = B \<longleftrightarrow> A \<subseteq> B \<and> B \<subseteq> A" *)
definition 
  ZFextension :: "i" where
  "ZFextension == Forall(Forall(
                 Iff(Equal(1,0) , 
                 And(subset_fm(1,0),subset_fm(0,1)))))"

(* extension "\<forall>x\<forall>y(\<forall>z.(z\<in>x \<longleftrightarrow> z\<in>y) \<rightarrow> x = y)" *)
definition
  ZFextension2 :: "i" where
  "ZFextension2 == Forall(Forall(Implies(
                      Forall(Iff(Member(0,2),Member(0,1))),
                      Equal(1,0))))"


(* foundation "A = 0 \<or> (\<exists>x\<in>A. \<forall>y\<in>x. y\<notin>A)" *)
definition
  ZFfoundation :: "i" where
  "ZFfoundation == Forall(Or(empty_fm(0),
                   Exists(Implies(Member(0,1),
                   Forall(Implies(Member(0,1),Neg(Member(0,2))))))))"

(* foundation "\<forall>x(\<exists>a(a\<in>x) \<rightarrow> \<exists>y(y\<in>x \<and> \<not>\<exists>z(z\<in>y \<and> z\<in>x)))" *)
definition 
  ZFfoundation2 :: "i" where
  "ZFfoundation2 == Forall(Implies(
                            Exists(Member(0,1)),
                            Exists(And(Member(0,1),
                                       Neg(Exists(And(Member(0,1),Member(0,2))))))))"

(* pairing "\<forall>x\<forall>y\<exists>z(x\<in>z \<and> y\<in>z)" *)
definition
  ZFpairing :: "i" where
  "ZFpairing == Forall(Forall(Exists(And(Member(2,0),Member(1,0)))))"

(* union "\<forall>F\<exists>A\<forall>Y\<forall>x((x\<in>Y \<and> Y\<in>F) \<rightarrow> x\<in>A)" *)
definition
  ZFunion :: "i" where
  "ZFunion == Forall(Exists(Forall(Forall(
              Implies(And(Member(0,1),Member(1,3)),Member(0,2))))))"


(* powerset: "\<forall>x\<exists>y\<forall>z(z\<subseteq>x \<rightarrow> z\<in>y)" *)
definition 
  ZFpowerset :: "i" where
  "ZFpowerset == Forall(Exists(Forall(
                 Implies(subset_fm(0,2),Member(0,1)))))"

(* fórmula compuesta por n veces Forall *)
consts 
  nForall :: "[i,i] \<Rightarrow> i"
primrec
  "nForall(0,\<Phi>) = \<Phi>"
  "nForall(succ(n),\<Phi>) = Forall(nForall(n,\<Phi>))" 

(* nForall está bien tipada *)
lemma nForall_type [TC]: 
      "[| n \<in> nat; \<Phi> \<in> formula |] ==> nForall(n,\<Phi>) \<in> formula"
by (induct_tac "n",auto)

(* specification: Para cada \<Phi> con variables libres entre x,z,w1,...,wn. 
                  "\<forall>z \<forall>w1...wn \<exists>y\<forall>x(x\<in>y \<longleftrightarrow> (x\<in>z \<and> \<Phi>)" *)


(* infinity "\<exists>X(\<emptyset>\<in>X \<and> \<forall>y(y\<in>X \<rightarrow> succ(y)\<in>X))" *)


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
  "relSet(M) == {z\<in>M. \<exists>x. \<exists>y. z=\<langle>x,y\<rangle> \<and> rel(x,y)}"

text\<open>The next lemma is just an experiment to have a proof of a proposition P==>P\<close>
lemma trivial_FO_implication:
  assumes "\<exists>x\<in>Z .  \<forall>y. P(x,y,Z) \<longrightarrow> Q(x,y,Z)"
  shows "\<exists>x\<in>Z .  \<forall>y. P(x,y,Z) \<longrightarrow> Q(x,y,Z)"
proof -
  show ?thesis using assms .
  text\<open>Otra opción es usar 
  show ?thesis using assms by simp\<close>
qed
  
(* Fake lemma to follow our arguments *)
lemma WFrel_aux :
  assumes "Z\<noteq>0" 
  shows "\<exists>x\<in>Z .  \<forall>y. (\<exists>z. z \<in> x \<and> (\<exists>w. w \<in> z \<and> y \<in> w)) \<longrightarrow> y \<notin> Z "
  sorry

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
  
(* Auxiliary result for showing rel well founded *)
lemma WFrel_auxM :
  assumes p:"Z\<noteq>0" 
  shows q:"\<exists>x\<in>Z. \<forall>y. \<langle>y, x\<rangle> \<in> M \<and> (\<exists>z. z \<in> x \<and> (\<exists>w. w \<in> z \<and> y \<in> w)) \<longrightarrow> y \<notin> Z"
    (* I plan to use reinforce_antecedent *)
  apply(rule_tac 
      Q="\<exists>x\<in>Z. \<forall>y. \<langle>y, x\<rangle> \<in> M \<and> (\<exists>z. z \<in> x \<and> (\<exists>w. w \<in> z \<and> y \<in> w)) \<longrightarrow> y \<notin> Z"
      and
      P="\<exists>x\<in>Z .  \<forall>y. (\<exists>z. z \<in> x \<and> (\<exists>w. w \<in> z \<and> y \<in> w)) \<longrightarrow> y \<notin> Z" in mp) 
proof -
  from p
  show "\<exists>x\<in>Z .  \<forall>y. (\<exists>z. z \<in> x \<and> (\<exists>w. w \<in> z \<and> y \<in> w)) \<longrightarrow> y \<notin> Z" by(rule WFrel_aux)
qed auto
(*
next
  show 
    "(\<exists>x\<in>Z. \<forall>y. (\<exists>z. z \<in> x \<and> (\<exists>w. w \<in> z \<and> y \<in> w)) \<longrightarrow> y \<notin> Z) \<longrightarrow>
    (\<exists>x\<in>Z. \<forall>y. \<langle>y, x\<rangle> \<in> M \<and> (\<exists>z. z \<in> x \<and> (\<exists>w. w \<in> z \<and> y \<in> w)) \<longrightarrow> y \<notin> Z)"
    by (rule_tac
        Z="Z"
        and
        R="\<lambda> x y . \<langle>y, x\<rangle> \<in> M"
        and
        P="\<lambda> x y Z . (\<exists>z. z \<in> x \<and> (\<exists>w. w \<in> z \<and> y \<in> w))"
        and
        Q="\<lambda> x y Z . y \<notin> Z"
        for Z and R and P and Q
        in reinforce_antecedent)
qed *)

definition
  bool_fun :: "[i,i] \<Rightarrow> o" where
  "bool_fun == \<lambda> x y . \<exists>z . z \<in> y \<longrightarrow> (\<exists>w . w \<in> z \<longrightarrow> x \<in> w)"

  
lemma WFrel : "wf(relSet(M))"
  apply(unfold wf_def)
  apply(rule allI)
  apply(case_tac "Z=0")
  apply(rule disjI1;auto)
  apply(rule disjI2)
  apply(simp add:relSet_def add:rel_def add:WFrel_auxM)
  done

section\<open>Anomalous calculations\<close>
text\<open>Here I put some anomalous lemmata, showing the typelessness of set theory.\<close>
lemma card_of_pair :
  "cardinal(Pair(x,y)) = 2"
  sorry
    
lemma card_of_formula :
  "cardinal(Member(1,2)) = 2"
  apply (unfold Member_def)
  apply (unfold Inl_def)
  apply (simp add:card_of_pair)
  done
            
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

end