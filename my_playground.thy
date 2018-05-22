theory my_playground imports Formula ZFCaxioms L_axioms Cardinal begin

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
  
fix P and Q::"i\<Rightarrow>i\<Rightarrow>o"
  assume a:"\<forall>y w. P(y,w)\<longrightarrow>Q(y,w)"  
  (* Apparently, this is the same as the next line 
  assume "\<forall>y w. P(y,w)\<longrightarrow>Q(y,w)" for P::"i\<Rightarrow>i\<Rightarrow>o" and Q::"i\<Rightarrow>i\<Rightarrow>o" *)

    (* Don't know if I can "open a new sub-block" using another "assume."
       Otherwise I have to use "and":
  and "\<exists>x\<in>Z. P(x,Z)" for Z *)
  then have p: "\<forall>w y. P(y,w)\<longrightarrow>Q(y,w)" by (auto)
  have "\<exists>x\<in>Z. Q(x,Z)" when q:"\<exists>x\<in>Z. P(x,Z)" for Z
  proof -
    (* Alternative: say 'have "\<exists>x\<in>Z. P(x,Z) \<Longrightarrow> \<exists>x\<in>Z. Q(x,Z)"'
       and then use: 
    assume q: "\<exists>x\<in>Z. P(x, Z)" *)
    obtain x where s:"P(x,Z)" and t:"x\<in>Z" using q by (rule bexE) (* or by blast *)
    from p have r:"\<forall>y . P(y,Z)\<longrightarrow>Q(y,Z)" by (rule spec)
    then have "P(x,Z)\<longrightarrow>Q(x,Z)" by (rule spec)
    with s have "Q(x,Z)"  by (auto) (*  "by (rule mp)" doesn't work *)
    then show  "\<exists>x\<in>Z. Q(x,Z)" using  t by (rule bexI)
  qed
end

(* Another try, minimizing references and labels *)
lemma "\<forall>y w. P(y,w)\<longrightarrow>Q(y,w) \<Longrightarrow> \<exists>x\<in>Z. P(x,Z) \<Longrightarrow> \<exists>x\<in>Z. Q(x,Z)"
proof -
  assume 
                  "\<forall>y w. P(y,w)\<longrightarrow>Q(y,w)"  
  then have 
              1:  "\<forall>w y. P(y,w)\<longrightarrow>Q(y,w)" 
    by (auto)
  assume
                  "\<exists>x\<in>Z. P(x,Z)" 
  then obtain x where 
              2:  "P(x,Z)" 
  and 
              3:  "x\<in>Z" 
    by (rule bexE)
  with 1 have "\<forall>y . P(y,Z)\<longrightarrow>Q(y,Z)" by (auto) (* rule spec doesn't work *)
  then have "P(x,Z)\<longrightarrow>Q(x,Z)" by (rule spec)
  with 2 have "Q(x,Z)"  by (auto)
  then show  "\<exists>x\<in>Z. Q(x,Z)" using 3 by (rule bexI)
qed
  
lemma nat_included_inductive : "0 \<in> I \<and> (\<forall>y\<in>I. succ(y) \<in> I) \<Longrightarrow> nat \<subseteq> I"
  apply (rule subsetI, rename_tac n)
  apply (induct_tac n, auto) 
  done

(* trying to understand calculational reasoning *)
(* (Actually, the next proof does not need 'also', since the last step is trivial) *)
notepad begin
  fix f g
  assume 
     f_invol: "\<forall>n. f`(f`n) = n"
  and 
     g_idemp: "\<forall>n. g`(g`n) = g`n"
  have
              "\<forall>n. g`(g`(f`(f`n))) = g`n"
  proof 
    show
              "g`(g`(f`(f`n))) = g`n" for n 
    proof -
      have 
              "g`(g`(f`(f`n))) = g`(g`n)"
        by (simp add:f_invol)
      also have    
              " ... = g`n"
        by (simp add: g_idemp)
      finally show ?thesis
        by assumption
    qed
  qed
end
  
(* Now with ball instead of all *)  
notepad begin
  fix f g
  assume 
     f_invol: "\<forall>n\<in>nat. f`(f`n) = n"
  and 
     g_idemp: "\<forall>n\<in>nat. g`(g`n) = g`n"
  have
              "\<forall>n\<in>nat. g`(g`(f`(f`(f`(f`n))))) = g`n"
  proof 
    show
              "n\<in>nat \<Longrightarrow> g`(g`(f`(f`(f`(f`n))))) = g`n" for n
    proof -
      assume 
          1:  "n\<in>nat" 
      then have 
              "g`(g`(f`(f`(f`(f`n))))) = g`(g`(f`(f`n)))"
        by (simp add:f_invol)
      also have    
              " ... = g`(g`n)"
        using 1 by (simp add:f_invol)
      finally show ?thesis
        using 1 by (simp add:g_idemp)
    qed
  qed
end

(* Variant eliminating the "\<Longrightarrow>", and alternatives to "using" *)  
notepad begin
  fix f g
  assume 
     f_invol: "\<forall>n\<in>nat. f`(f`n) = n"
  and 
     g_idemp: "\<forall>n\<in>nat. g`(g`n) = g`n"
  have
              "\<forall>n\<in>nat. g`(g`(f`(f`(f`(f`n))))) = g`n"
  proof 
    show
              "g`(g`(f`(f`(f`(f`n))))) = g`n" if 1:"n\<in>nat" for n
    proof -
      from 1 and f_invol have 
              "g`(g`(f`(f`(f`(f`n))))) = g`(g`(f`(f`n)))"
        by (simp)
      also with 1 and f_invol have    
              " ... = g`(g`n)"
        by (simp)
      finally show ?thesis                   (* can't use "with" here *)
        using g_idemp by (simp add:1)             (* Note the "1" in the simp set *) 
    qed
  qed
end

    
(* 
theorem (in countable_generic) rasiowa_sikorski:
  "p\<in>P \<Longrightarrow> \<exists>G. p\<in>G \<and> D_generic(G)"
proof -
  assume 
        0:  "p\<in>P"
  let
            ?S="(\<lambda>m\<in>nat. {<x,y>\<in>P*P. <y,x>\<in>leq \<and> y\<in>\<D>`(pred(m))})"
  have 
            "\<forall>x\<in>P. \<forall>n\<in>nat. \<exists>y\<in>P. <x,y> \<in> ?S`n"
  proof (intro ballI)
    fix x n
    assume 
        1:  "x\<in>P"
            and
        2:  "n\<in>nat"
    then show 
            "\<exists>y\<in>P. <x,y> \<in> ?S`n"
    proof (simp)
      from seq_of_denses and 2 have "dense(\<D> ` pred(n))" by (simp)
      with 1 have
            "\<exists>d\<in>\<D> ` Arith.pred(n). \<langle>d, x\<rangle> \<in> leq"
        unfolding dense_def by (simp)
      then obtain d where
        3:  "d \<in> \<D> ` Arith.pred(n) \<and> \<langle>d, x\<rangle> \<in> leq"
        by (rule bexE, simp)
      from countable_subs_of_P have
            "\<D> ` Arith.pred(n) \<in> Pow(P)"
        using 2 by (blast dest:apply_funtype intro:pred_type) (* (rule apply_funtype [OF _ pred_type]) *)
      then have
            "\<D> ` Arith.pred(n) \<subseteq> P" 
        by (rule PowD)
      then have
            "d \<in> P \<and> \<langle>d, x\<rangle> \<in> leq \<and> d \<in> \<D> ` Arith.pred(n)"
        using 3 by auto
      then show 
            "\<exists>y\<in>P. \<langle>y, x\<rangle> \<in> leq \<and> y \<in> \<D> ` Arith.pred(n)"
        using 1 and 2 by (auto) 
    qed
  qed
  with sequence_DC have
            "\<forall>a\<in>P. (\<exists>f \<in> nat->P. f`0 = a \<and> (\<forall>n \<in> nat. <f`n,f`succ(n)>\<in>?S`succ(n)))"
    by (blast)
  then obtain f where
        8:  "f : nat\<rightarrow>P"
    and
        4:  "f ` 0 = p \<and>
             (\<forall>n\<in>nat.
              f ` n \<in> P \<and> f ` succ(n) \<in> P \<and> \<langle>f ` succ(n), f ` n\<rangle> \<in> leq \<and> 
              f ` succ(n) \<in> \<D> ` n)"
    using 0 by (auto)
  then have   
       7:   "f``nat  \<subseteq> P"
    by (simp add:subset_fun_image)
  with leq_preord have 
       5:   "refl(f``nat, leq) \<and> trans[P](leq)"
    unfolding preorder_on_def  by (blast intro:refl_monot_domain)
  from 4 have
            "\<forall>n\<in>nat.  \<langle>f ` succ(n), f ` n\<rangle> \<in> leq"
    by (simp)
  with 8 and 5 and leq_preord and decr_seq_linear have
       6:   "linear(f``nat, leq)"
    unfolding preorder_on_def by (blast)
  with 5 and chain_compat have 
            "(\<forall>p\<in>f``nat.\<forall>q\<in>f``nat. compat_in(f``nat,leq,p,q))"             
    by (auto)
  then have
     fil:   "filter(upclosure(f``nat))"
   (is "filter(?G)")
    using closure_compat_filter and 7 by simp
  have
    gen:   "\<forall>n\<in>nat. \<D> ` n \<inter> ?G \<noteq> 0"
  proof
    fix n
    assume  
           "n\<in>nat"
    with 8 and 4 have
            "f`succ(n) \<in> ?G \<and> f`succ(n) \<in> \<D> ` n"
      using aux_RS1 by simp
    then show 
       9:   "\<D> ` n \<inter> ?G \<noteq> 0"
      by blast
  qed
  from 4 and 8 have 
            "p \<in> ?G"
    using aux_RS1 by auto
  with gen and fil show ?thesis  
    unfolding D_generic_def by auto
qed *)

definition
  e3 :: "[i,i] \<Rightarrow> o" where
  "e3(x,y) == \<exists>z . z \<in> y \<and> (\<exists>w . w \<in> z \<and> x \<in> w)"

definition
  e3_set :: "i \<Rightarrow> i" where
  "e3_set(M) == { z \<in> M*M . e3(fst(z),snd(z)) }"


lemma e3I [intro] : "x \<in> a \<Longrightarrow> a \<in> b \<Longrightarrow> b \<in> y \<Longrightarrow>
            e3(x,y)"
  by (simp add: e3_def,blast)

lemma e3E [elim] : "e3(x,y) \<Longrightarrow> (\<And> a b . x \<in> a \<Longrightarrow> a \<in> b \<Longrightarrow> b \<in> y \<Longrightarrow> P) \<Longrightarrow> P"
  by (simp add:e3_def,blast)
    
    
(* \<questiondown>Es útil? *)
lemma e3_set_coord : 
  "<x,y>\<in>e3_set(M) \<Longrightarrow> \<exists>z . z \<in> y \<and> (\<exists>w . w \<in> z \<and> x \<in> w)"
by (simp add:e3_set_def e3_def )

(*\<questiondown>Qué significa fld?*)
lemma fld_e3_sub_eclose : 
 "\<lbrakk>y \<in> M ; z \<in> y ; w \<in> z\<rbrakk> \<Longrightarrow> z \<in> eclose(M) \<and> w \<in> eclose(M)"
proof (simp add:ecloseD) 
  assume p:"y\<in>M"
     and q: "z\<in>y"
  show "z\<in>eclose(M)"
  proof - 
  have r:"M\<subseteq>eclose(M)" by (rule arg_subset_eclose)
  from p and r  have "y\<in>eclose(M)" by (simp add:subsetD)
  then show ?thesis using q  by (simp add:ecloseD)
  qed
qed

lemma fld_memrel:"\<lbrakk> y \<in> M ; z \<in> y ; w \<in> z\<rbrakk> \<Longrightarrow> 
                           <w,z> \<in> Memrel(eclose(M))"
  by  (rule MemrelI,assumption,simp add:fld_e3_sub_eclose,simp add:fld_e3_sub_eclose)


lemma
  "e3_set(M) \<subseteq> Memrel(eclose(M)) O Memrel(eclose(M)) O Memrel(eclose(M))"
proof (unfold e3_set_def, unfold e3_def,clarsimp)
  fix x y z w
  assume a:"x \<in> M" "y \<in> M" "z \<in> y" "w \<in> z" "x \<in> w"
  then have p : "<x,w> \<in> Memrel(eclose(M))" 
    by (simp add:fld_memrel fld_e3_sub_eclose arg_into_eclose)
  from a have q : "<w,z> \<in> Memrel(eclose(M))"
    by (simp add:MemrelI fld_e3_sub_eclose)
  from a have r: "<z,y> \<in> Memrel(eclose(M))"
    by (simp add:MemrelI fld_e3_sub_eclose arg_into_eclose)
  with p q 
    show "<x,y> \<in> Memrel(eclose(M)) O Memrel(eclose(M)) O Memrel(eclose(M))"
     by (rule_tac b=z in compI, rule_tac b=w in compI)
qed

lemma rel_sub_memcomp : 
  "e3_set(M) \<subseteq> Memrel(eclose(M)) O Memrel(eclose(M)) O Memrel(eclose(M))"
proof (unfold e3_set_def, unfold e3_def,clarsimp)
  fix x y z w
  assume 
          a:  "x \<in> M" "y \<in> M" "z \<in> y" "w \<in> z" "x \<in> w"
  then have 
          p:  "<x,w> \<in> Memrel(eclose(M))" 
              "<w,z> \<in> Memrel(eclose(M))" 
              "<z,y> \<in> Memrel(eclose(M))"
    by (simp_all add:fld_memrel fld_e3_sub_eclose arg_into_eclose)
  then show     
    "<x,y> \<in> Memrel(eclose(M)) O Memrel(eclose(M)) O Memrel(eclose(M))"
    by (rule_tac b=z in compI, rule_tac b=w in compI)
qed

end

