theory Separation_Lemmas imports Forces_locale Renaming Eisbach_Old_Appl_Syntax begin

lemma pred_mono : "m \<in> nat \<Longrightarrow> n \<le> m \<Longrightarrow> pred(n) \<le> pred(m)"
  by(rule_tac n="n" in natE,auto simp add:le_in_nat,erule_tac n="m" in natE,auto)
    
lemma pred2_Un: assumes "j \<in> nat" "m \<le> j" "n \<le> j" 
  shows "pred(pred(m \<union> n)) \<le> pred(pred(j))" 
proof -
  from assms assms show ?thesis 
    using pred_mono[of "j"] le_in_nat un_leI' pred_mono by simp
qed

definition 
  perm_sep_forces :: "i" where
  "perm_sep_forces == {<3,0>,<4,1>,<5,2>,<1,3>,<0,4>,<6,5>,<7,6>,<2,7>}"

lemma perm_sep_ftc : "perm_sep_forces \<in> 8 -||> 8"
  by(unfold perm_sep_forces_def,(rule consI,auto)+,rule emptyI)

lemma dom_perm_sep : "domain(perm_sep_forces) = 8"     
  by(unfold perm_sep_forces_def,auto)
  
lemma perm_sep_tc : "perm_sep_forces \<in> 8 \<rightarrow> 8"
  by(subst dom_perm_sep[symmetric],rule FiniteFun_is_fun,rule perm_sep_ftc)

lemma apply_fun: "f \<in> Pi(A,B) ==> <a,b>: f \<Longrightarrow> f`a = b"
  by(auto simp add: apply_iff)
    
lemma perm_sep_inj: "perm_sep_forces \<in> inj(8,8)"   
  apply(auto simp add:apply_fun inj_def  perm_sep_forces_def)
  apply(fold perm_sep_forces_def, simp add:  perm_sep_tc)
  done
    
lemma perm_sep_surj: "perm_sep_forces \<in> surj(8,8)" 
  apply(auto simp add:apply_fun perm_sep_forces_def surj_def)
  apply(fold perm_sep_forces_def, simp add: perm_sep_tc)
  done

lemma perm_sep_bij: "perm_sep_forces \<in> bij(8,8)" 
  by(simp add: bij_def perm_sep_inj perm_sep_surj)
    
lemma conv_perm_sep_bij: "converse(perm_sep_forces) \<in> bij(8,8)" 
  by (rule perm_sep_bij [THEN bij_converse_bij])


lemma perm_sep_env_aux : "
  {p,q,r,s,t,u,v,w} \<subseteq> A \<Longrightarrow>                           
perm_list(perm_sep_forces,[t,s,w,p,q,r,u,v]) = [q,p,v,t,s,w,r,u]"
  apply(rule nth_equalityI)
  apply(auto simp add: perm_list_tc perm_sep_bij  perm_list_length)
  apply(subst nth_perm,simp,simp add:perm_sep_bij,simp,erule ltD)
  apply(rule_tac natE,simp+,subst apply_fun,rule perm_sep_tc,simp add:perm_sep_forces_def,simp)+
  apply(auto,subst apply_fun,rule perm_sep_tc,simp add:perm_sep_forces_def,simp)
  done

lemma perm_sep_env: 
  "perm_list(perm_sep_forces,[t,s,w,p,q,r,u,v]) = [q,p,v,t,s,w,r,u]"
  by (auto simp add: perm_sep_env_aux [of _ _ _ _ _ _ _ _ "{p,q,r,s,t,u,v,w}"])

    
locale six_param_separation = forcing_thms +
  assumes
    sixp_sep: "\<lbrakk> \<phi> \<in> formula ; arity(\<phi>)\<le>6 \<rbrakk> \<Longrightarrow> 
                  (\<forall>a1\<in>M. \<forall>a2\<in>M. \<forall>a3\<in>M. \<forall>a4\<in>M. \<forall>a5\<in>M. 
                    separation(##M,\<lambda>x. sats(M,\<phi>,[x,a1,a2,a3,a4,a5])))" 
  
    
context six_param_separation begin (*********** CONTEXT: six_param_separation ************)

lemmas transitivity = Transset_intf trans_M
  
lemma one_in_M: "one \<in> M"
  by (insert one_in_P P_in_M, simp add: transitivity)

lemma six_sep_aux: 
  assumes
    "b \<in> M" "[\<sigma>, \<pi>] \<in> list(M)" "\<psi>\<in>formula" "arity(\<psi>) \<le> 6"
  shows
    "{u \<in> b. sats(M,\<psi>,[u] @ [P, leq, one] @ [\<sigma>, \<pi>])} \<in> M" 
proof -
  from assms P_in_M leq_in_M one_in_M  have
    "(\<forall>u\<in>M. separation(##M,\<lambda>x. sats(M,\<psi>,[x] @ [P, leq, one] @ [\<sigma>, \<pi>])))" 
    using sixp_sep by simp  
  with \<open>b \<in> M\<close> show ?thesis
    using separation_iff by auto
qed
      
lemma G_nonempty: "M_generic(G) \<Longrightarrow> G\<noteq>0"
proof -
  have "P\<subseteq>P" ..
  assume
    "M_generic(G)"
  with P_in_M P_dense \<open>P\<subseteq>P\<close> show
    "G \<noteq> 0"
    unfolding M_generic_def by auto
qed
  
lemma iff_impl_trans: "Q\<longleftrightarrow>R \<Longrightarrow> R\<longrightarrow>S \<Longrightarrow> Q \<longrightarrow>S"
  "Q\<longrightarrow>R \<Longrightarrow> R\<longleftrightarrow>S \<Longrightarrow> Q \<longrightarrow>S"
  "Q\<longrightarrow>R \<Longrightarrow> R\<longrightarrow> S \<Longrightarrow> Q\<longrightarrow> S"
  by simp_all  


named_theorems fstpass
named_theorems sndpass
    
method simp_altnt declares fstpass sndpass = (simp add:fstpass ; simp add:sndpass)+
method abs_simp = (simp_altnt fstpass:nat_union_abs1 sndpass: nat_union_abs2)
    
lemma separation_aux :
  "M_generic(G) \<Longrightarrow> \<pi> \<in> M \<Longrightarrow> \<sigma> \<in> M \<Longrightarrow>
    val(G, \<pi>) = c \<Longrightarrow> val(G, \<sigma>) = w \<Longrightarrow>
    \<phi> \<in> formula \<Longrightarrow> arity(\<phi>) \<le> 2 \<Longrightarrow>
    {x\<in>c. sats(M[G], \<phi>, [x, w, c])}\<in> M[G]" for G \<pi> c w \<sigma> \<phi>
proof -
  assume
    "M_generic(G)" 
  with G_nonempty have 
    "G\<noteq>0" .
  from \<open>M_generic(G)\<close> have 
    "filter(G)" "G\<subseteq>P" 
    unfolding M_generic_def filter_def by simp_all
  assume
    phi: "\<phi>\<in>formula" "arity(\<phi>) \<le> 2"
  let
    ?\<chi>="And(Member(0,2),\<phi>)"
    and   
    ?Pl1="[P,leq,one]"
  let
    ?new_form="rename(forces(?\<chi>))`8`converse(perm_sep_forces)"
  let
    ?\<psi>="Exists(Exists(And(pair_fm(0,1,2),?new_form)))"
  from phi have 
    "arity(?\<chi>) \<le> 3" 
    by (simp add:nat_union_abs1,subst nat_union_abs2,(simp add: leI)+)
  with phi have
    "arity(forces(?\<chi>)) \<le> 8"
    using arity_forces 
    by(simp add:nat_union_abs1,subst nat_union_abs2,(simp add: leI)+)
  with phi definability[of "?\<chi>"] arity_forces  have
    nf_form : "?new_form \<in> formula"
    using ren_lib_tc[of "forces(?\<chi>)" _ "converse(perm_sep_forces)"] conv_perm_sep_bij 
    by(simp)
  then have
    "?\<psi> \<in> formula"
    by simp
  from \<open>\<phi>\<in>formula\<close> have
    "forces(?\<chi>) \<in> formula"
    using definability by simp
  with \<open>arity(forces(?\<chi>)) \<le> 8\<close> have
    "arity(?new_form) \<le> 8"
    using ren_arity conv_perm_sep_bij definability by simp
  then have
    "arity(?\<psi>) \<le> 6" 
  proof -
    have "n \<le> 8 \<Longrightarrow> pred(pred(3 \<union> n)) \<le> 6" for n
      using pred2_Un[of "8"]
      by simp        
    with \<open>arity(?new_form)  \<le> 8\<close> \<open>?new_form \<in> formula\<close> have
      "pred(pred(3 \<union> arity(?new_form))) \<le> 6"
      by (simp add:arity_type)
    moreover have 
      "arity(pair_fm(0,1,2)) = 3" 
      unfolding pair_fm_def upair_fm_def 
      by abs_simp
    ultimately  show ?thesis 
      using \<open>arity(?new_form) \<le> 8\<close> by simp
  qed
  assume
    "\<pi>\<in>M" "\<sigma>\<in>M" 
  with P_in_M have
    "domain(\<pi>)\<in>M" "domain(\<pi>) \<times> P \<in> M"
    by (simp_all del:setclass_iff add:setclass_iff[symmetric])
  note in_M1 = \<open>\<pi>\<in>M\<close> \<open>\<sigma>\<in>M\<close> \<open>domain(\<pi>) \<times> P \<in> M\<close>  P_in_M one_in_M leq_in_M
  {
    fix u
    assume
      "u \<in> domain(\<pi>) \<times> P" "u \<in> M"
    with in_M1 \<open>?new_form \<in> formula\<close> \<open>?\<psi>\<in>formula\<close> have
      Eq1: "sats(M,?\<psi>,[u] @ ?Pl1 @ [\<sigma>,\<pi>]) \<longleftrightarrow> 
                        (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
                          sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<sigma>,\<pi>]))"
      by (auto simp add: transitivity)
    {
      fix p \<theta> 
      assume 
        "\<theta> \<in> M" "p\<in>P"
      with P_in_M have "p\<in>M" by (simp add: transitivity)
      note
        in_M = in_M1 \<open>\<theta> \<in> M\<close> \<open>p\<in>M\<close> \<open>\<pi>\<in>M\<close> \<open>u \<in> domain(\<pi>) \<times> P\<close> \<open>u \<in> M\<close>
      then have
        "[\<theta>,\<sigma>,u] \<in> list(M)" by simp
      let
        ?env="?Pl1@[p,\<theta>,\<sigma>,\<pi>,u]"
      let
        ?new_env="perm_list(perm_sep_forces,?env)"
      let
        ?\<psi>="Exists(Exists(And(pair_fm(0,1,2),?new_form)))"
      have  
        "1 \<union> 3 = 3" using nat_union_abs2 leI by auto
      then have
         "?\<chi> \<in> formula" "arity(?\<chi>) \<le> 3" "forces(?\<chi>)\<in> formula"  
        using phi  nat_union_abs2[of _ "3"] leI by auto
      with arity_forces have
        "arity(forces(?\<chi>)) \<le> 7" 
        by simp     
      then have "arity(forces(?\<chi>)) \<le> 8" using le_trans by simp
      from in_M have
        "?Pl1 \<in> list(M)" by simp
      from in_M have "?env \<in> list(M)" by simp
      have
        Eq1': "?new_env = [\<theta>,p,u,P,leq,one,\<sigma>,\<pi>]"
        using in_M perm_sep_env
        by simp 
      then have
        "sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<sigma>,\<pi>]) \<longleftrightarrow> sats(M,?new_form,?new_env)"
        by simp
      also have
        "sats(M,?new_form,?new_env) \<longleftrightarrow> 
           sats(M,rename(forces(?\<chi>))`length(?env)`converse(perm_sep_forces),?new_env)"           
        by simp
      also from \<open>arity(forces(?\<chi>)) \<le> 8\<close> and \<open>forces(?\<chi>) \<in> formula\<close> and in_M have
        "... \<longleftrightarrow> sats(M,forces(?\<chi>),?env)"
        using  perm_sep_bij ren_Sat_leq by auto
      also have
        "... \<longleftrightarrow> sats(M,forces(?\<chi>), [P, leq, one,p,\<theta>,\<sigma>,\<pi>]@[u])" by simp
      also from \<open>arity(forces(?\<chi>)) \<le> 7\<close> \<open>forces(?\<chi>)\<in>formula\<close> in_M  phi have
        "... \<longleftrightarrow> sats(M,forces(?\<chi>), [P, leq, one,p,\<theta>,\<sigma>,\<pi>])"        
        by (rule_tac arity_sats_iff,auto)
      also from \<open>arity(forces(?\<chi>)) \<le> 7\<close> \<open>forces(?\<chi>)\<in>formula\<close> in_M  phi have
        " ... \<longleftrightarrow> (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> 
                           sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<sigma>), val(F, \<pi>)]))"
        using  definition_of_forces 
      proof (intro iffI)
        assume
          a1: "sats(M, forces(?\<chi>), [P, leq, one,p,\<theta>,\<sigma>,\<pi>])"
        note definition_of_forces [THEN iffD1] 
        then have
          "p \<in> P \<Longrightarrow> ?\<chi>\<in>formula \<Longrightarrow> [\<theta>,\<sigma>,\<pi>] \<in> list(M) \<Longrightarrow>
                  sats(M, forces(?\<chi>), [P, leq, one, p] @ [\<theta>,\<sigma>,\<pi>]) \<Longrightarrow> 
              \<forall>G. M_generic(G) \<and> p \<in> G \<longrightarrow> sats(M[G], ?\<chi>, map(val(G), [\<theta>,\<sigma>,\<pi>]))" .
        then show
          "\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> 
                  sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<sigma>), val(F, \<pi>)])"
          using  \<open>?\<chi>\<in>formula\<close> \<open>p\<in>P\<close> a1 \<open>\<theta>\<in>M\<close> \<open>\<sigma>\<in>M\<close> \<open>\<pi>\<in>M\<close> by auto
      next
        assume
          "\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> 
                   sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<sigma>), val(F, \<pi>)])"
        with definition_of_forces [THEN iffD2] show
          "sats(M, forces(?\<chi>), [P, leq, one,p,\<theta>,\<sigma>,\<pi>])"
          using  \<open>?\<chi>\<in>formula\<close> \<open>p\<in>P\<close> in_M by auto
      qed
      finally have
        "sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<sigma>,\<pi>]) \<longleftrightarrow> (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> 
                           sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<sigma>), val(F, \<pi>)]))" by simp
    }
    then have
      Eq3: "\<theta>\<in>M \<Longrightarrow> p\<in>P \<Longrightarrow>
      sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<sigma>,\<pi>]) \<longleftrightarrow>
      (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<sigma>), val(F, \<pi>)]))" 
      for \<theta> p by simp
    with Eq1 have
      "sats(M,?\<psi>,[u] @ ?Pl1 @ [\<sigma>,\<pi>]) \<longleftrightarrow> 
            (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
                           (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<sigma>), val(F, \<pi>)])))"
      "\<theta>\<in>M \<Longrightarrow> p\<in>P \<Longrightarrow>
      sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<sigma>,\<pi>]) \<longleftrightarrow>
      (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<sigma>), val(F, \<pi>)]))"  for \<theta> p
      by auto
  }
  with in_M1 \<open>?new_form \<in> formula\<close> \<open>?\<psi>\<in>formula\<close> have
    Equivalence: "u\<in> domain(\<pi>) \<times> P \<Longrightarrow> u \<in> M \<Longrightarrow> 
            sats(M,?\<psi>,[u] @ ?Pl1 @ [\<sigma>,\<pi>]) \<longleftrightarrow> 
            (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
               (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<sigma>), val(F, \<pi>)])))" 
    for u 
    by simp
  from Equivalence  [THEN iffD1]  \<open>M_generic(G)\<close> have
    "u \<in> domain(\<pi>) \<times> P \<Longrightarrow> u \<in> M \<Longrightarrow>
        sats(M,?\<psi>,[u, P, leq, one,\<sigma>, \<pi>]) \<Longrightarrow>
          (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
                (p \<in> G \<longrightarrow> 
                sats(M[G], ?\<chi>, [val(G, \<theta>), val(G, \<sigma>), val(G, \<pi>)])))" for u
    by force
  moreover have
    "val(G,\<sigma>)\<in>M[G]" and "\<theta>\<in>M \<Longrightarrow> val(G,\<theta>)\<in>M[G]" for \<theta>
    using GenExt_def \<open>\<sigma>\<in>M\<close> by auto
  ultimately have
    "u \<in> domain(\<pi>) \<times> P \<Longrightarrow> u \<in> M \<Longrightarrow>
        sats(M,?\<psi>,[u, P, leq, one,\<sigma>, \<pi>]) \<Longrightarrow>
          (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
                (p \<in> G \<longrightarrow> 
                val(G,\<theta>) \<in> val(G,\<pi>) \<and> sats(M[G], \<phi>, [val(G, \<theta>), val(G, \<sigma>), val(G, \<pi>)])))" for u
    using \<open>\<pi>\<in>M\<close> by auto
  with \<open>domain(\<pi>)*P\<in>M\<close> have
    "\<forall>u\<in>domain(\<pi>)*P . sats(M,?\<psi>,[u] @ ?Pl1 @ [\<sigma>,\<pi>])  \<longrightarrow>
      (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
        (p \<in> G \<longrightarrow> val(G, \<theta>)\<in>val(G, \<pi>) \<and> sats(M[G], \<phi>, [val(G, \<theta>), val(G, \<sigma>), val(G, \<pi>)])))"
    by (simp add:transitivity)
  then have
    "{u\<in>domain(\<pi>)*P . sats(M,?\<psi>,[u] @ ?Pl1 @ [\<sigma>,\<pi>]) } \<subseteq>
     {u\<in>domain(\<pi>)*P . \<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
       (p \<in> G \<longrightarrow> val(G, \<theta>)\<in>val(G, \<pi>) \<and> sats(M[G], \<phi>, [val(G, \<theta>), val(G, \<sigma>), val(G, \<pi>)]))}"
    (is "?n\<subseteq>?m") 
    by auto
  with val_mono have
    first_incl: "val(G,?n) \<subseteq> val(G,?m)" 
    by simp
  fix c w
  assume 
    "val(G,\<pi>) = c" "val(G,\<sigma>) = w"
  with \<open>?\<psi>\<in>formula\<close> \<open>arity(?\<psi>) \<le> 6\<close> in_M1 have 
    "?n\<in>M" 
    using six_sep_aux by simp
  have
    in_val_n: "<\<theta>,p>\<in>domain(\<pi>)*P \<Longrightarrow> <\<theta>,p>\<in>M \<Longrightarrow> p\<in>G \<Longrightarrow> p\<in>P \<Longrightarrow> 
      sats(M,?\<psi>,[<\<theta>,p>] @ ?Pl1 @ [\<sigma>,\<pi>]) \<Longrightarrow> val(G,\<theta>)\<in>val(G,?n)" for \<theta> p
    using val_of_elem by simp
  from val_of_name and \<open>val(G,\<pi>) = c\<close> \<open>val(G,\<sigma>) = w\<close> have
    "val(G,?m) =
               {val(G,t) .. t\<in>domain(\<pi>) , \<exists>q\<in>P .  
                    (\<exists>\<theta>\<in>M. \<exists>p\<in>P. <t,q> = \<langle>\<theta>, p\<rangle> \<and> 
            (p \<in> G \<longrightarrow> val(G, \<theta>) \<in> c \<and> sats(M[G], \<phi>, [val(G, \<theta>), w, c])) \<and> q \<in> G)}"
    by auto
  also have
    "... =  {val(G,t) .. t\<in>domain(\<pi>) , \<exists>q\<in>P. 
                   val(G, t) \<in> c \<and> sats(M[G], \<phi>, [val(G, t), w, c]) \<and> q \<in> G}" 
  proof -
    have
      "t\<in>M \<Longrightarrow>
      (\<exists>q\<in>P. (\<exists>\<theta>\<in>M. \<exists>p\<in>P. <t,q> = \<langle>\<theta>, p\<rangle> \<and> 
              (p \<in> G \<longrightarrow> val(G, \<theta>) \<in> c \<and> sats(M[G], \<phi>, [val(G, \<theta>), w, c])) \<and> q \<in> G)) 
      \<longleftrightarrow> 
      (\<exists>q\<in>P. val(G, t) \<in> c \<and> sats(M[G], \<phi>, [val(G, t), w, c]) \<and> q \<in> G)" for t
      by auto
    then show ?thesis using \<open>domain(\<pi>)\<in>M\<close> by (auto simp add:transitivity)
  qed
  also have
    "... =  {x .. x\<in>c , \<exists>q\<in>P. x \<in> c \<and> sats(M[G], \<phi>, [x, w, c]) \<and> q \<in> G}"
  proof
    show 
      "... \<subseteq> {x .. x\<in>c , \<exists>q\<in>P. x \<in> c \<and> sats(M[G], \<phi>, [x, w, c]) \<and> q \<in> G}"
      by auto
  next 
    (* 
      {x .. x\<in>c , \<exists>q\<in>P. x \<in> c \<and> sats(M[G], \<phi>, [x, w, c]) \<and> q \<in> G}
      \<subseteq>
      {val(G,t)..t\<in>domain(\<pi>),\<exists>q\<in>P.val(G,t)\<in>c\<and>sats(M[G],\<phi>,[val(G,t),w])\<and>q\<in>G}
    *)
    {
      fix x
      assume
        "x\<in>{x .. x\<in>c , \<exists>q\<in>P. x \<in> c \<and> sats(M[G], \<phi>, [x, w, c]) \<and> q \<in> G}"
      then have
        "\<exists>q\<in>P. x \<in> c \<and> sats(M[G], \<phi>, [x, w, c]) \<and> q \<in> G"
        by simp
      with \<open>val(G,\<pi>) = c\<close>  have 
        "\<exists>q\<in>P. \<exists>t\<in>domain(\<pi>). val(G,t) =x \<and> sats(M[G], \<phi>, [val(G,t), w, c]) \<and> q \<in> G" 
        using Sep_and_Replace def_val sorry
    }
    then show 
      " {x .. x\<in>c , \<exists>q\<in>P. x \<in> c \<and> sats(M[G], \<phi>, [x, w, c]) \<and> q \<in> G} \<subseteq> ..."
      by (force simp add: SepReplace_iff [THEN iffD2])
  qed
  also have
    " ... = {x\<in>c. sats(M[G], \<phi>, [x, w, c])}"
    using \<open>G\<subseteq>P\<close> \<open>G\<noteq>0\<close> by force
  finally have
    val_m: "val(G,?m) = {x\<in>c. sats(M[G], \<phi>, [x, w, c])}" by simp
  {
    fix x
    assume
      Eq4: "x \<in> {x\<in>c. sats(M[G], \<phi>, [x, w, c])}"
    with \<open>val(G,\<pi>) = c\<close> have 
      "x \<in> val(G,\<pi>)" by simp
    then have
      "\<exists>\<theta>. \<exists>q\<in>G. <\<theta>,q>\<in>\<pi> \<and> val(G,\<theta>) =x" 
      using elem_of_val_pair by auto
    then obtain \<theta> q where
      "<\<theta>,q>\<in>\<pi>" "q\<in>G" "val(G,\<theta>)=x" by auto
    from \<open><\<theta>,q>\<in>\<pi>\<close> \<open>\<pi>\<in>M\<close> trans_M have 
      "\<theta>\<in>M"
      unfolding Pair_def Transset_def by auto 
    with \<open>\<pi>\<in>M\<close> \<open>\<sigma>\<in>M\<close> have
      "[val(G,\<theta>), val(G,\<sigma>), val(G,\<pi>)]\<in>list(M[G])" 
      using GenExt_def by auto
    with  Eq4 \<open>val(G,\<theta>)=x\<close> \<open>val(G,\<pi>) = c\<close> \<open>val(G,\<sigma>) = w\<close> \<open>x \<in> val(G,\<pi>)\<close> have
      Eq5: "sats(M[G], And(Member(0,2),\<phi>), [val(G,\<theta>), val(G,\<sigma>), val(G,\<pi>)])" 
      by auto
        (* Recall ?\<chi> = And(Member(0,2),\<phi>) *)
    with \<open>\<theta>\<in>M\<close> \<open>\<pi>\<in>M\<close>  \<open>\<sigma>\<in>M\<close> and truth_lemma and Eq5 have
      "(\<exists>r\<in>G. sats(M,forces(?\<chi>), [P,leq,one,r,\<theta>,\<sigma>,\<pi>]))"
      using \<open>M_generic(G)\<close> \<open>\<phi>\<in>formula\<close> by auto
    then obtain r where      (* I can't "obtain" this directly *)
      "r\<in>G" "sats(M,forces(?\<chi>), [P,leq,one,r,\<theta>,\<sigma>,\<pi>])" by auto
    with \<open>filter(G)\<close> and \<open>q\<in>G\<close> obtain p where
      "p\<in>G" "<p,q>\<in>leq" "<p,r>\<in>leq" 
      unfolding filter_def compat_in_def by force
    with \<open>r\<in>G\<close>  \<open>q\<in>G\<close> P_in_M have
      "p\<in>P" "r\<in>P" "q\<in>P" "p\<in>M"
      using \<open>G\<subseteq>P\<close>  by (auto simp add:transitivity)
    with \<open>\<phi>\<in>formula\<close> \<open>\<theta>\<in>M\<close> \<open>\<pi>\<in>M\<close> \<open>\<sigma>\<in>M\<close> \<open>sats(M,forces(And(Member(0,2),\<phi>)), [P,leq,one,r,\<theta>,\<sigma>,\<pi>])\<close> have
      "sats(M,forces(?\<chi>), [P,leq,one,p,\<theta>,\<sigma>,\<pi>])"
      using \<open><p,r>\<in>leq\<close> streghtening by simp
    with \<open>p\<in>P\<close> \<open>\<phi>\<in>formula\<close> \<open>\<theta>\<in>M\<close> \<open>\<pi>\<in>M\<close> \<open>\<sigma>\<in>M\<close> have
      "\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> 
                 sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<sigma>), val(F,\<pi>)])"
      using definition_of_forces by simp
    with \<open>p\<in>P\<close> \<open>\<theta>\<in>M\<close>  have
      Eq6: "\<exists>\<theta>'\<in>M. \<exists>p'\<in>P.  <\<theta>,p> = <\<theta>',p'> \<and> (\<forall>F. M_generic(F) \<and> p' \<in> F \<longrightarrow> 
                 sats(M[F], ?\<chi>, [val(F, \<theta>'), val(F, \<sigma>), val(F,\<pi>)]))" by auto
    from \<open>\<pi>\<in>M\<close> \<open><\<theta>,q>\<in>\<pi>\<close> have
      "<\<theta>,q> \<in> M" by (simp add:transitivity)
    from \<open><\<theta>,q>\<in>\<pi>\<close> \<open>\<theta>\<in>M\<close> \<open>p\<in>P\<close>  \<open>p\<in>M\<close> have
      "<\<theta>,p>\<in>M" "<\<theta>,p>\<in>domain(\<pi>)\<times>P" 
      using pairM by auto
    with \<open>\<theta>\<in>M\<close> Eq6 \<open>p\<in>P\<close> have
      "sats(M,?\<psi>,[<\<theta>,p>] @ ?Pl1 @ [\<sigma>,\<pi>])"
      using Equivalence [THEN iffD2]  by auto
        (* with \<open><\<theta>,p>\<in>domain(\<pi>)\<times>P\<close> have
      "\<exists>u\<in>domain(\<pi>)\<times>P. sats(M,?\<psi>,[u] @ ?Pl1 @ [\<pi>]@?params)" by auto *)
    with \<open><\<theta>,p>\<in>domain(\<pi>)\<times>P\<close>  \<open><\<theta>,p>\<in>M\<close> \<open>p\<in>G\<close> \<open>val(G,\<theta>)=x\<close> have
      "x\<in>val(G,?n)"   
      using in_val_n by auto
  }
  with val_m  have 
    "val(G,?m) \<subseteq> val(G,?n)" by auto
  with  val_m first_incl have
    "val(G,?n) = {x\<in>c. sats(M[G], \<phi>, [x, w, c])}" by auto
  with \<open>?n\<in>M\<close> GenExt_def show
    "{x\<in>c. sats(M[G], \<phi>, [x, w, c])}\<in> M[G]" by force
qed

end   (*********** CONTEXT: six_param_separation ************)
end