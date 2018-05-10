theory my_playground imports Formula ZFCaxioms L_axioms  Pointed_DC Cardinal begin

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
  
lemma monotone_bex : "\<forall>y w. P(y,w)\<longrightarrow>Q(y,w) \<Longrightarrow> \<exists>x\<in>Z. P(x,Z) \<Longrightarrow> \<exists>x\<in>Z. Q(x,Z)" 
  apply (drule_tac Q="\<exists>x\<in>Z. Q(x,Z)" in bexE)
  prefer 2 apply assumption
  apply (rule_tac x="x" in bexI)
   apply (thin_tac "x\<in>Z")
    apply (drule_tac x="x" in spec)
    apply (drule_tac x="Z" in spec)
    apply (rotate_tac 1)
  apply (drule mp)
 apply ( assumption+)
  done

(* Prueba  más corta, sacando los \<exists> primero y después los \<forall> *)
lemma monotone_bex' : "\<forall>y w. P(y,w)\<longrightarrow>Q(y,w) \<Longrightarrow> \<exists>x\<in>Z. P(x,Z) \<Longrightarrow> \<exists>x\<in>Z. Q(x,Z)" 
  apply (erule bexE)
  apply (rule bexI)
  apply (drule spec)+
  apply (drule mp)
    apply assumption+
  done
    

lemma "(EX y. ALL x. Q(x,y)) --> (ALL x. EX y. Q(x,y))"
  by (tactic "IntPr.fast_tac  @{context} 1")
    
lemma monotone_all : "\<forall>x. P(x)\<longrightarrow>Q(x) \<Longrightarrow> \<forall>x. P(x) \<Longrightarrow> \<forall>x. Q(x)" 
  apply (rule allI)
    apply (rename_tac w)
    apply (drule_tac x="w" in spec)
  apply (drule_tac x="w" in spec)
  apply (tactic "mp_tac  @{context} 1")
    apply assumption
(* El anterior reemplaza las dos siguientes líneas más manuales *)
(*
  apply (rotate_tac,frule mp)
  apply (assumption+)
*)
  done
    
  
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

(* 
lemma l1 :
  "2 \<notin> 1"
  apply auto
  done
 *)
lemma l2 :
  "{2,0} \<noteq> 1"
  apply (subst extension)
  apply auto
 (* antes requería l1 para simplificar *)  
 (*  apply (simp add: l1) *)
  done

lemma l1' :
  "2 \<notin> 2"
  apply auto
  done

lemma l2' :
  "{2,0} \<noteq> 2"
  apply (rule notI)
  apply (drule extension [THEN iffD1])
    apply auto
 (*  Otra opción, con un hint:
  apply (subgoal_tac "2\<notin>2")
    apply auto
 *) 
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
  eee :: "[i,i] \<Rightarrow> o" where
  "eee(x,y) == \<exists>z . z \<in> y \<and> (\<exists>w . w \<in> z \<and> x \<in> w)"
  
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

section\<open>Isar training\<close>

notepad begin
(* Trying to re-do the proof of  lemma monotone_bexi' : 
"\<forall>y w. P(y,w)\<longrightarrow>Q(y,w) \<Longrightarrow> \<exists>x\<in>Z. P(x,Z) \<Longrightarrow> \<exists>x\<in>Z. Q(x,Z)"  *)
  
fix P::"i\<Rightarrow>i\<Rightarrow>o" and Q::"i\<Rightarrow>i\<Rightarrow>o"
  assume a:"\<forall>y w. P(y,w)\<longrightarrow>Q(y,w)"   (* w,y instead y,w to make it easier *)
  (* Apparently, this is the same as the next line 
  assume "\<forall>y w. P(y,w)\<longrightarrow>Q(y,w)" for P::"i\<Rightarrow>i\<Rightarrow>o" and Q::"i\<Rightarrow>i\<Rightarrow>o" *)

    (* Don't know if I can "open a new sub-block" using another "assume."
       Otherwise I have to use "and":
  and "\<exists>x\<in>Z. P(x,Z)" for Z *)
  then have p: "\<forall>w y. P(y,w)\<longrightarrow>Q(y,w)" by (auto)
  have "\<exists>x\<in>Z. P(x,Z) \<Longrightarrow> \<exists>x\<in>Z. Q(x,Z)" for Z
  proof -
    assume q: "\<exists>x\<in>Z. P(x, Z)"
    obtain x where s:"P(x,Z)" and t:"x\<in>Z" using q by (rule bexE) (* or by blast *)
    from p have r:"\<forall>y . P(y,Z)\<longrightarrow>Q(y,Z)" by (rule spec)
    then have "P(x,Z)\<longrightarrow>Q(x,Z)" by (rule spec)
    with s have "Q(x,Z)"  by (auto) (*  "by (rule mp)" doesn't work *)
    then show  "\<exists>x\<in>Z. Q(x,Z)" using  t by (rule bexI)
  qed

end
  

end

