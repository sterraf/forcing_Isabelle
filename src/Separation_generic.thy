theory Separation_generic imports Forces_locale begin

definition 
  perm_sep_forces :: "i" where
  "perm_sep_forces == {\<langle>0, 4\<rangle>, \<langle>1, 3\<rangle>, \<langle>2, 7\<rangle>, \<langle>3, 0\<rangle>, \<langle>4, 1\<rangle>, \<langle>5, 2\<rangle>, \<langle>6, 5\<rangle>, \<langle>7, 6\<rangle>}"

lemma perm_sep_ftc : "perm_sep_forces \<in> 8 -||> 8"
  apply(unfold perm_sep_forces_def)
  apply(rule consI,auto)+
  apply(rule emptyI)
  done

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
perm_list(perm_sep_forces,[p,q,r,s,t,u,v,w]) = [t,s,w,p,q,r,u,v]"
  apply(rule nth_equalityI)
  apply(auto simp add: perm_list_tc perm_sep_bij  perm_list_length)
  apply(subst nth_perm,simp,simp add:perm_sep_bij,simp,erule ltD)
  apply(rule_tac natE,simp+,subst apply_fun,rule perm_sep_tc,simp add:perm_sep_forces_def,simp)+
  apply(auto,subst apply_fun,rule perm_sep_tc,simp add:perm_sep_forces_def,simp)
  done

lemma perm_sep_env: 
  "perm_list(perm_sep_forces,[p,q,r,s,t,u,v,w]) = [t,s,w,p,q,r,u,v]"
  by (auto simp add: perm_sep_env_aux [of _ _ _ _ _ _ _ _ "{p,q,r,s,t,u,v,w}"])
    
(*
lemma small_arity: "[pp,l,o,p,\<theta>,\<pi>,\<sigma>,u]\<in>list(M) \<Longrightarrow> \<chi>\<in>formula \<Longrightarrow> arity(\<chi>) = 2 \<Longrightarrow> 
            sats(M,forces(\<chi>),[pp,l,o,p,\<theta>,\<pi>,\<sigma>]@[u]) \<longleftrightarrow>
            sats(M,forces(\<chi>),[pp,l,o,p,\<theta>,\<pi>,\<sigma>])"
  apply (insert arity_forces definability)
  apply (rule arity_sats_iff, simp_all)
  done
*)
    
context forcing_thms begin  

lemmas transitivity = Transset_intf trans_M

lemma one_in_M: "one \<in> M"
  by (insert one_in_P P_in_M, simp add: transitivity)

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

  
    
theorem separation_in_genext:
  notes iff_impl_trans [trans] 
 (* assumes "\<phi>\<in>formula"  and "arity(\<phi>) = 1 \<or> arity(\<phi>)=2" 
  shows  "sats(M[G],separation_ax_fm(\<phi>),[])" *)
  shows
  "M_generic(G) \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> arity(\<phi>) = 1 \<or> arity(\<phi>)=2 \<Longrightarrow> 
    sats(M[G],separation_ax_fm(\<phi>),[])"
proof -
  assume 
      "arity(\<phi>) = 1 \<or> arity(\<phi>)=2" (is "?P \<or> ?Q")
  then consider (1) ?P | (2) ?Q ..
  then show ?thesis
  proof cases
    case (1)
    then show ?thesis sorry
  next
    case (2)
    fix G c w 
    assume
         asm: "c\<in>M[G]" "w\<in>M[G]" "\<phi>\<in>formula" "M_generic(G)"
    then have
              "{x\<in>c. sats(M[G],\<phi>,[x,w])}\<in>M[G]"  (is "?S\<in>_")
    proof -
      from asm obtain \<pi> \<sigma> where
         Eq1: "\<pi>\<in>M" "\<sigma>\<in>M" "val(G,\<pi>) = c" "val(G,\<sigma>) = w" 
        by (auto simp add: GenExt_def)
      with P_in_M have
         Eq2: "domain(\<pi>)*P\<in>M"
        by (simp del:setclass_iff add:setclass_iff [symmetric])
      let
              ?\<chi>="And(Member(0,1),\<phi>)"
        and   ?Pl1="[P,leq,one]"
      let
              ?new_form="rename(forces(?\<chi>))`8`converse(perm_sep_forces)"
      let
              ?\<psi>="Exists(Exists(And(pair_fm(0,1,2),forces(?\<chi>))))"
      from asm P_in_M leq_in_M one_in_P 2 have
         Eq3: "?\<chi>\<in>formula" "?\<psi>\<in>formula" "\<phi>\<in>formula" "?Pl1\<in>list(M)" "arity(?\<chi>) =2"
        by (auto simp add: transitivity)
      then have
        chi: "?\<chi> \<in> formula" "arity(?\<chi>) = 2" "forces(?\<chi>)\<in> formula" by auto
      with arity_forces have
        "arity(forces(?\<chi>)) \<le> 6" 
        by simp
      have
        "\<forall>u\<in>domain(\<pi>)*P . sats(M,?\<psi>,[u] @ ?Pl1 @ [\<pi>,\<sigma>])  \<longrightarrow>
          (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
                            p \<in> G \<longrightarrow> 
                           val(G, \<theta>)\<in>c \<and> sats(M[G], \<phi>, [val(G, \<theta>), c]))"
      proof (intro ballI)
        fix u
        assume 
         Eq4: "u \<in> domain(\<pi>) \<times> P"
        with Eq2  trans_M transD have
         Eq5: "u \<in> M"
             unfolding Transset_def by auto
        from Eq4 Eq1 and Eq2 and Eq3 have
         Eq6: "sats(M,?\<psi>,[u] @ ?Pl1 @ [\<pi>,\<sigma>]) \<longleftrightarrow> 
                        (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
                          sats(M,forces(?\<chi>),[\<theta>,p,u]@?Pl1@[\<pi>,\<sigma>]))"
          by (auto simp add: transitivity)
        have
         Eq7: "(\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
                    sats(M,forces(?\<chi>),[\<theta>,p,u]@?Pl1@[\<pi>,\<sigma>]))
               \<longrightarrow> 
               (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
                    p \<in> G \<longrightarrow> val(G, \<theta>)\<in>c \<and> sats(M[G], \<phi>, [val(G, \<theta>), c]))"
        proof -
          {
            fix \<theta> p
            let
                ?new_form="rename(forces(?\<chi>))`length(?Pl1@[p,\<theta>,\<pi>,\<sigma>,u])`converse(perm_sep_forces)"
                and
                ?new_env="perm_list(perm_sep_forces,?Pl1@[p,\<theta>,\<pi>,\<sigma>,u])"
            assume
               a: "\<theta>\<in>M" "p\<in>P" "u = <\<theta>,p>"
            with P_in_M have
                  "p\<in>M"
              by (simp add:transitivity)
            note
              in_M = P_in_M one_in_M leq_in_M \<open>\<pi>\<in>M\<close>  \<open>\<sigma>\<in>M\<close> \<open>\<theta> \<in> M\<close> \<open>p\<in>M\<close> \<open>u\<in>M\<close>
            from \<open>p\<in>M\<close> have
                  " sats(M,forces(?\<chi>),[\<theta>,p,u]@?Pl1@[\<pi>,\<sigma>])
                   \<longleftrightarrow> sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<pi>,\<sigma>])"
              (* using Eq4 P_in_M by (auto simp add:transitivity)*) sorry
            also have
                  " ... \<longleftrightarrow> sats(M,?new_form,?new_env)" 
              by (auto simp add: perm_sep_env)
            also have
                  " ... \<longleftrightarrow> sats(M,forces(?\<chi>),?Pl1@[p,\<theta>,\<pi>,\<sigma>,u])"
              using  \<open>\<phi> \<in> formula\<close> in_M 2 transD trans_M
              apply(rule_tac ren_Sat_leq [symmetric])
                 apply(auto simp add: perm_sep_bij arity_forces nat_union_abs1)
              done
            also have
              "... \<longleftrightarrow> sats(M,forces(?\<chi>), [P, leq, one,p,\<theta>,\<pi>]@[\<sigma>,u])" by auto
            also have
              "... \<longleftrightarrow> sats(M,forces(?\<chi>), [P, leq, one,p,\<theta>,\<pi>])"
              using  in_M \<open>arity(forces(?\<chi>)) \<le> 6\<close> \<open>forces(?\<chi>)\<in>formula\<close>
              by (rule_tac arity_sats_iff, auto)
            also have
              " ... \<longleftrightarrow> (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> 
                           sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<pi>)]))"
              using Eq1 Eq3 Eq4 Eq5 a and definition_of_forces 
            proof (intro iffI)
              assume
                a1: "sats(M, forces(?\<chi>), [P, leq, one,p,\<theta>,\<pi>])"
              note definition_of_forces [THEN iffD1] 
              then have
                "p \<in> P \<Longrightarrow> ?\<chi>\<in>formula \<Longrightarrow> [\<theta>,\<pi>] \<in> list(M) \<Longrightarrow>
                  sats(M, forces(?\<chi>), [P, leq, one, p] @ [\<theta>,\<pi>]) \<Longrightarrow> 
              \<forall>G. M_generic(G) \<and> p \<in> G \<longrightarrow> sats(M[G], ?\<chi>, map(val(G), [\<theta>,\<pi>]))" .
              then show
                "\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> 
                  sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<pi>)])"
                using  \<open>?\<chi>\<in>formula\<close> \<open>p\<in>P\<close> a1 \<open>\<theta>\<in>M\<close> \<open>\<pi>\<in>M\<close> by auto
            next
              assume
                "\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> 
                   sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<pi>)])"
              with definition_of_forces [THEN iffD2] show
                "sats(M, forces(?\<chi>), [P, leq, one,p,\<theta>,\<pi>])"
                using  \<open>?\<chi>\<in>formula\<close> \<open>p\<in>P\<close> in_M by auto
            qed              
              also have
                  " ... \<longrightarrow> M_generic(G) \<and> p \<in> G \<longrightarrow> 
                                sats(M[G], ?\<chi>, [val(G, \<theta>), c])"
              using Eq1 by auto
            also have
                  " ... \<longrightarrow> M_generic(G) \<and> p \<in> G \<longrightarrow> 
                               val(G, \<theta>)\<in>c \<and> sats(M[G], \<phi>, [val(G, \<theta>), c ])"
            proof (intro impI)
              assume
                  "M_generic(G) \<and> p \<in> G \<longrightarrow> sats(M[G], And(Member(0, 1), \<phi>), [val(G, \<theta>), c])"
                  "M_generic(G) \<and> p \<in> G"
              then have
                  sat_and: "sats(M[G], And(Member(0, 1), \<phi>), [val(G, \<theta>), c])"  "p\<in>G" 
                by simp_all
              from a have
                  "val(G, \<theta>) \<in> M[G]"
                unfolding GenExt_def by(auto)
              with asm sat_and show  
                "val(G, \<theta>) \<in> c \<and> sats(M[G], \<phi>, [val(G, \<theta>), c])"
                by auto
            qed
            finally have
                  " sats(M,forces(?\<chi>),[\<theta>,p,u]@?Pl1@[\<pi>,\<sigma>])
                   \<longrightarrow> M_generic(G) \<and> p \<in> G \<longrightarrow> 
                               val(G, \<theta>)\<in>c \<and> sats(M[G], \<phi>, [val(G, \<theta>), c ])" .
          }
          then have
            "\<theta>\<in>M \<Longrightarrow> p\<in>P \<Longrightarrow>
             u = \<langle>\<theta>, p\<rangle> \<and> sats(M, forces(And(Member(0, 1), \<phi>)), [\<theta>, p, u] @ [P, leq, one] @ [\<pi>, \<sigma>]) \<longrightarrow>
             u = \<langle>\<theta>, p\<rangle> \<and> p \<in> G \<longrightarrow> val(G, \<theta>) \<in> c \<and> sats(M[G], \<phi>, [val(G, \<theta>), c])" for \<theta> p
            using asm by simp
          then show ?thesis by auto
        qed
        from Eq6 Eq7 show
        Eq8: "sats(M,?\<psi>,[u] @ ?Pl1 @ [\<pi>,\<sigma>]) \<longrightarrow>
               (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
                           p \<in> G \<longrightarrow> 
                           val(G, \<theta>)\<in>c \<and> sats(M[G], \<phi>, [val(G, \<theta>), c ]))" 
          by simp
      qed
      then have
              "{u\<in>domain(\<pi>)*P . sats(M,?\<psi>,[u] @ ?Pl1 @ [\<pi>,\<sigma>]) } \<subseteq>
               {u\<in>domain(\<pi>)*P . \<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
                            p \<in> G \<longrightarrow> 
                           val(G, \<theta>)\<in>c \<and> sats(M[G], \<phi>, [val(G, \<theta>), c ])}"
                  (is "?n\<subseteq>?m") 
        by auto
      with val_mono have
         Eq7: "?n\<in>M \<Longrightarrow> ?m\<in>M \<Longrightarrow> val(G,?n) \<subseteq> val(G,?m)" 
        by simp
      assume 
              "?n \<in> M"  "?m \<in> M"
      with val_of_name and Eq7 have
              "val(G,?n) \<subseteq>
               {val(G,t) .. t\<in>domain(\<pi>) , \<exists>q\<in>P .  
                    (\<exists>\<theta>\<in>M. \<exists>p\<in>P. <t,q> = \<langle>\<theta>, p\<rangle> \<and> p \<in> G \<longrightarrow> 
                      val(G, \<theta>) \<in> c \<and> sats(M[G], \<phi>, [val(G, \<theta>), c])) \<and> q \<in> G }"
             by auto
            then show ?thesis sorry 
                qed
   oops

notepad begin   (************** notepad **************)
  fix G \<phi> 
  assume
    "M_generic(G)" 
  with G_nonempty have 
    "G\<noteq>0" .
  assume
    "Transset(M[G])"
  from \<open>M_generic(G)\<close> have 
    "filter(G)" "G\<subseteq>P" 
      unfolding M_generic_def filter_def by simp_all
  assume
    phi: "\<phi>\<in>formula" "arity(\<phi>) = 2"
  let
    ?\<chi>="And(Member(0,1),\<phi>)"
    and   
    ?Pl1="[P,leq,one]"
  let
    ?new_form="rename(forces(?\<chi>))`8`converse(perm_sep_forces)"
  let
    ?\<psi>="Exists(Exists(And(pair_fm(0,1,2),?new_form)))"
  have "1 \<union> 2 \<union> 2 = 2" by auto    
  then have "1 \<union> 2 \<union> 2 \<le> 4" by auto
  with phi conv_perm_sep_bij arity_forces  have
    "?new_form \<in> formula"
    using ren_tc by (simp)
  then have
    "?\<psi> \<in> formula"
    by simp
  fix \<pi> \<sigma> 
  assume
    "\<pi>\<in>M" "\<sigma>\<in>M"  "domain(\<pi>) \<times> P \<in> M"
  note in_M1 = \<open>\<pi>\<in>M\<close> \<open>\<sigma>\<in>M\<close> \<open>domain(\<pi>) \<times> P \<in> M\<close>  P_in_M one_in_M leq_in_M
  {
    fix u
    assume
      "u \<in> domain(\<pi>) \<times> P" "u \<in> M"
    with in_M1 \<open>?new_form \<in> formula\<close> \<open>?\<psi>\<in>formula\<close> have
      Eq1: "sats(M,?\<psi>,[u] @ ?Pl1 @ [\<pi>,\<sigma>]) \<longleftrightarrow> 
                        (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
                          sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<pi>,\<sigma>]))"
      by (auto simp add: transitivity)
    {
      fix p \<theta> 
      assume 
        "\<theta> \<in> M" "p\<in>P"
      with P_in_M have "p\<in>M" by (simp add: transitivity)
      note
        in_M = in_M1 \<open>\<theta> \<in> M\<close> \<open>p\<in>M\<close> \<open>u \<in> domain(\<pi>) \<times> P\<close> \<open>u \<in> M\<close>
      then have
        "[\<theta>,\<pi>,\<sigma>,u] \<in> list(M)" by simp
      let
        ?new_env="perm_list(perm_sep_forces,?Pl1@[p,\<theta>,\<pi>,\<sigma>,u])"
      let
        ?\<psi>="Exists(Exists(And(pair_fm(0,1,2),?new_form)))"
      from phi  have
        chi: "?\<chi> \<in> formula" "arity(?\<chi>) = 2" "forces(?\<chi>)\<in> formula" by auto
      with arity_forces have
        "arity(forces(?\<chi>)) \<le> 6" 
        by simp
      from in_M have
        "?Pl1 \<in> list(M)" by simp
      have
        "[\<theta>,p,u]@?Pl1@[\<pi>,\<sigma>] = ?new_env"
        by (auto simp add: perm_sep_env)
      have
        len : "8 = length(?Pl1@[p,\<theta>,\<pi>,\<sigma>,u])" 
        by simp
      assume
        "sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<pi>,\<sigma>])"
      with perm_sep_env have
        "sats(M,?new_form,perm_list(perm_sep_forces,?Pl1@[p,\<theta>,\<pi>,\<sigma>,u]))" 
        by simp
      then have
        "sats(M,forces(?\<chi>),?Pl1@[p,\<theta>,\<pi>,\<sigma>,u])"
        using phi in_M transD trans_M  ren_Sat_leq [THEN iffD2]  perm_sep_bij
        by (auto simp add: arity_forces nat_union_abs1) 
      with in_M \<open>arity(forces(?\<chi>)) \<le> 6\<close> \<open>forces(?\<chi>)\<in>formula\<close> have
        Eq2: "sats(M,forces(?\<chi>), [P, leq, one,p]@[\<theta>,\<pi>])"
        by (rule_tac arity_sats_iff [THEN iffD1], auto) (* Enhance this ! *)
      from in_M have
        th_pi: "[\<theta>,\<pi>] \<in> list(M)" by simp
      have
        "\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<pi>)])"
      proof -
        note definition_of_forces [THEN iffD1] 
        then have
          "p \<in> P \<Longrightarrow> ?\<chi>\<in>formula \<Longrightarrow> [\<theta>,\<pi>] \<in> list(M) \<Longrightarrow>
           sats(M, forces(?\<chi>), [P, leq, one, p] @ [\<theta>,\<pi>]) \<Longrightarrow> 
          \<forall>G. M_generic(G) \<and> p \<in> G \<longrightarrow> sats(M[G], ?\<chi>, map(val(G), [\<theta>,\<pi>]))" .
        then show ?thesis using  phi chi \<open>p\<in>P\<close> Eq2 th_pi by simp
      qed
    }
    then have
      Eq3: "\<theta>\<in>M \<Longrightarrow> p\<in>P \<Longrightarrow>
      sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<pi>,\<sigma>]) \<Longrightarrow>
      \<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<pi>)])" 
      for \<theta> p 
      by simp
    have
        "\<theta>\<in>M \<Longrightarrow> sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<pi>,\<sigma>]) \<Longrightarrow> p \<in> G \<longrightarrow> 
          val(G, \<theta>) \<in>  val(G, \<pi>) \<and> sats(M[G], \<phi>, [val(G, \<theta>), val(G, \<pi>)])" for \<theta> p
    proof (intro impI)
      assume 
        "p \<in> G"
      with \<open>G\<subseteq>P\<close> have "p\<in>P" by auto 
      assume
        "sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<pi>,\<sigma>])"
        "\<theta> \<in> M"   
      with Eq3  \<open>p\<in>P\<close> have
        "\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> 
                 sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<pi>)])" by simp
      with \<open>M_generic(G)\<close> \<open>p\<in>G\<close> have
        sat_chi: "sats(M[G], ?\<chi>, [val(G, \<theta>), val(G, \<pi>)])"
        by simp
      from in_M1 \<open>\<theta>\<in>M\<close> have
        "val(G, \<theta>) \<in> M[G]" "val(G, \<pi>) \<in> M[G]" 
        unfolding GenExt_def by(auto)
      with sat_chi show
        "val(G, \<theta>)\<in>val(G, \<pi>) \<and> sats(M[G], \<phi>, [val(G, \<theta>), val(G, \<pi>)])"
        by simp
    qed
    with \<open>M_generic(G)\<close> have
      Eq3: "\<theta>\<in>M \<Longrightarrow> p\<in>P \<Longrightarrow>
      sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<pi>,\<sigma>]) \<Longrightarrow>
      p \<in> G \<Longrightarrow> 
      val(G, \<theta>) \<in> val(G, \<pi>) \<and> sats(M[G], \<phi>, [val(G, \<theta>),val(G, \<pi>)])" 
      for \<theta> p 
      by auto
    with \<open>u\<in>M\<close> have
      "(\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
          sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<pi>,\<sigma>]))
       \<Longrightarrow>
        (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
                (p \<in> G \<longrightarrow> 
               val(G, \<theta>)\<in> val(G, \<pi>) \<and> sats(M[G], \<phi>, [val(G, \<theta>), val(G, \<pi>)])))"
    proof -
      assume
        "\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
          sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<pi>,\<sigma>])"
      then obtain \<theta> p where
        obt: "\<theta>\<in>M" "p\<in>P" "u =<\<theta>,p> \<and> sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<pi>,\<sigma>])"
        by (auto)
      from \<open>P\<in>M\<close> \<open>p\<in>P\<close> have "p\<in>M" 
        by (simp add:transitivity)
      with obt Eq3 have
        "u =<\<theta>,p> \<and> (p \<in> G \<longrightarrow> 
          val(G, \<theta>)\<in> val(G, \<pi>) \<and> sats(M[G], \<phi>, [val(G, \<theta>), val(G, \<pi>)]))"
        by simp
      with \<open>\<theta>\<in>M\<close> \<open>p\<in>P\<close> show ?thesis by simp
    qed
    with Eq1  [THEN iffD1] in_M1 have
      "sats(M,?\<psi>,[u, P, leq, one, \<pi>,\<sigma>]) \<Longrightarrow>
          (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
                (p \<in> G \<longrightarrow> 
               val(G, \<theta>)\<in> val(G, \<pi>) \<and> sats(M[G], \<phi>, [val(G, \<theta>), val(G, \<pi>)])))"
      by simp
  }
  with \<open>domain(\<pi>)*P\<in>M\<close> have
    "\<forall>u\<in>domain(\<pi>)*P . sats(M,?\<psi>,[u] @ ?Pl1 @ [\<pi>,\<sigma>])  \<longrightarrow>
      (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
        (p \<in> G \<longrightarrow> val(G, \<theta>)\<in>val(G, \<pi>) \<and> sats(M[G], \<phi>, [val(G, \<theta>), val(G, \<pi>)])))"
    by (simp add:transitivity)
  then have
    "{u\<in>domain(\<pi>)*P . sats(M,?\<psi>,[u] @ ?Pl1 @ [\<pi>,\<sigma>]) } \<subseteq>
     {u\<in>domain(\<pi>)*P . \<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
       (p \<in> G \<longrightarrow> val(G, \<theta>)\<in>val(G, \<pi>) \<and> sats(M[G], \<phi>, [val(G, \<theta>), val(G, \<pi>)]))}"
    (is "?n\<subseteq>?m") 
    by auto
  with val_mono have
    first_incl: "?n\<in>M \<Longrightarrow> ?m\<in>M \<Longrightarrow> val(G,?n) \<subseteq> val(G,?m)" 
    by simp
  fix c w
  assume 
    "val(G,\<pi>) = c" "val(G,\<sigma>) = w"
  assume
    "domain(\<pi>)\<in>M"
  assume 
    "?n \<in> M"  "?m \<in> M" 
  with val_of_name and \<open>val(G,\<pi>) = c\<close> have
    "val(G,?m) =
               {val(G,t) .. t\<in>domain(\<pi>) , \<exists>q\<in>P .  
                    (\<exists>\<theta>\<in>M. \<exists>p\<in>P. <t,q> = \<langle>\<theta>, p\<rangle> \<and> 
            (p \<in> G \<longrightarrow> val(G, \<theta>) \<in> c \<and> sats(M[G], \<phi>, [val(G, \<theta>), c])) \<and> q \<in> G)}"
    by auto
  also have
    "... =  {val(G,t) .. t\<in>domain(\<pi>) , \<exists>q\<in>P. 
                   val(G, t) \<in> c \<and> sats(M[G], \<phi>, [val(G, t), c]) \<and> q \<in> G}" 
  proof -
    have
      "t\<in>M \<Longrightarrow>
      (\<exists>q\<in>P. (\<exists>\<theta>\<in>M. \<exists>p\<in>P. <t,q> = \<langle>\<theta>, p\<rangle> \<and> 
              (p \<in> G \<longrightarrow> val(G, \<theta>) \<in> c \<and> sats(M[G], \<phi>, [val(G, \<theta>), c])) \<and> q \<in> G)) 
      \<longleftrightarrow> 
      (\<exists>q\<in>P. val(G, t) \<in> c \<and> sats(M[G], \<phi>, [val(G, t), c]) \<and> q \<in> G)" for t
      by auto
    then show ?thesis using \<open>domain(\<pi>)\<in>M\<close> by (auto simp add:transitivity)
  qed
  also have
    "... =  {x .. x\<in>c , \<exists>q\<in>P. x \<in> c \<and> sats(M[G], \<phi>, [x, c]) \<and> q \<in> G}"
  proof
    show 
      "... \<subseteq> {x .. x\<in>c , \<exists>q\<in>P. x \<in> c \<and> sats(M[G], \<phi>, [x, c]) \<and> q \<in> G}"
      by auto
  next 
    (* 
      {x .. x\<in>c , \<exists>q\<in>P. x \<in> c \<and> sats(M[G], \<phi>, [x, c]) \<and> q \<in> G}
      \<subseteq>
      {val(G,t)..t\<in>domain(\<pi>),\<exists>q\<in>P.val(G,t)\<in>c\<and>sats(M[G],\<phi>,[val(G,t),c])\<and>q\<in>G}
    *)
    {
      fix x
      assume
        "x\<in>{x .. x\<in>c , \<exists>q\<in>P. x \<in> c \<and> sats(M[G], \<phi>, [x, c]) \<and> q \<in> G}"
      then have
        "\<exists>q\<in>P. x \<in> c \<and> sats(M[G], \<phi>, [x, c]) \<and> q \<in> G"
        by simp
      with \<open>val(G,\<pi>) = c\<close> \<open>\<pi>\<in>M\<close> have 
        "\<exists>q\<in>P. \<exists>t\<in>domain(\<pi>). val(G,t) =x \<and> sats(M[G], \<phi>, [val(G,t), c]) \<and> q \<in> G" 
        using Sep_and_Replace def_val by auto
    }
    then show 
      " {x .. x\<in>c , \<exists>q\<in>P. x \<in> c \<and> sats(M[G], \<phi>, [x, c]) \<and> q \<in> G} \<subseteq> ..."
      by (force simp add: SepReplace_iff [THEN iffD2])
  qed
  also have
    " ... = {x\<in>c. sats(M[G], \<phi>, [x, c])}"
    using \<open>G\<subseteq>P\<close> \<open>G\<noteq>0\<close> by force
  finally have
    "val(G,?m) = {x\<in>c. sats(M[G], \<phi>, [x, c])}" by simp
  {
(*    fix x
    assume
      Eq4: "x \<in> {x\<in>c. sats(M[G], \<phi>, [x, c])}"
    with \<open>val(G,\<pi>) = c\<close> have 
      "x \<in> val(G,\<pi>)" by simp
    with \<open>\<pi>\<in>M\<close> have
       "\<exists>\<theta>. \<exists>q\<in>G. <\<theta>,q>\<in>\<pi> \<and> val(G,\<theta>) =x" 
      using elem_of_val_pair by auto
    then obtain \<theta> q where
      "<\<theta>,q>\<in>\<pi>" "q\<in>G" "val(G,\<theta>)=x" by auto
    with  Eq4 \<open>val(G,\<pi>) = c\<close>  have
      Eq5: "sats(M[G], \<phi>, [val(G,\<theta>), val(G,\<pi>)])" 
      by simp
    from \<open><\<theta>,q>\<in>\<pi>\<close> \<open>\<pi>\<in>M\<close> transD trans_M have 
        "\<theta>\<in>M" 
      unfolding Pair_def  sorry
    with \<open>\<pi>\<in>M\<close> and truth_lemma and Eq5 have
      "(\<exists>r\<in>G. sats(M,forces(\<phi>), [P,leq,one,r,\<theta>,\<pi>]))"
      using \<open>M_generic(G)\<close> \<open>\<phi>\<in>formula\<close> by auto
    then obtain r where      (* I can't "obtain" this directly *)
      "r\<in>G" "sats(M,forces(\<phi>), [P,leq,one,r,\<theta>,\<pi>])" by auto
    with \<open>filter(G)\<close> and \<open>q\<in>G\<close> obtain p where
      "p\<in>G" "<p,q>\<in>leq" "<p,r>\<in>leq" 
      unfolding filter_def compat_in_def by force
    with \<open>r\<in>G\<close> P_in_M have
      "p\<in>P" "r\<in>P"
      using \<open>G\<subseteq>P\<close>  by auto
    with \<open>\<phi>\<in>formula\<close> \<open>\<theta>\<in>M\<close> \<open>\<pi>\<in>M\<close> \<open>sats(M,forces(\<phi>), [P,leq,one,r,\<theta>,\<pi>])\<close> have
      "sats(M,forces(\<phi>), [P,leq,one,p,\<theta>,\<pi>])"
      using \<open><p,r>\<in>leq\<close> streghtening by simp
    with \<open>p\<in>P\<close> \<open>\<phi>\<in>formula\<close> \<open>\<theta>\<in>M\<close> \<open>\<pi>\<in>M\<close> have
      "\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> 
                 sats(M[F], \<phi>, [val(F, \<theta>), val(F, \<pi>)])"
      using definition_of_forces by simp *)

    (*********** The same as before but  for And(Member(0,1),\<phi>) ***************)
    fix x
    assume
      Eq4: "x \<in> {x\<in>c. sats(M[G], \<phi>, [x, c])}"
    with \<open>val(G,\<pi>) = c\<close> have 
      "x \<in> val(G,\<pi>)" by simp
    with \<open>\<pi>\<in>M\<close> have
       "\<exists>\<theta>. \<exists>q\<in>G. <\<theta>,q>\<in>\<pi> \<and> val(G,\<theta>) =x" 
      using elem_of_val_pair by auto
    then obtain \<theta> q where
      "<\<theta>,q>\<in>\<pi>" "q\<in>G" "val(G,\<theta>)=x" by auto
    from \<open><\<theta>,q>\<in>\<pi>\<close> \<open>\<pi>\<in>M\<close> transD trans_M have 
        "\<theta>\<in>M" 
      unfolding Pair_def  sorry
    with \<open>\<pi>\<in>M\<close> have
      "[val(G,\<theta>), val(G,\<pi>)]\<in>list(M[G])" 
      using GenExt_def by auto
    with  Eq4 \<open>val(G,\<theta>)=x\<close> \<open>val(G,\<pi>) = c\<close> \<open>x \<in> val(G,\<pi>)\<close> have
      Eq5: "sats(M[G], And(Member(0,1),\<phi>), [val(G,\<theta>), val(G,\<pi>)])" 
      by simp
        (* Recall ?\<chi> = And(Member(0,1),\<phi>) *)
    with \<open>\<theta>\<in>M\<close> \<open>\<pi>\<in>M\<close> and truth_lemma and Eq5 have
      "(\<exists>r\<in>G. sats(M,forces(?\<chi>), [P,leq,one,r,\<theta>,\<pi>]))"
      using \<open>M_generic(G)\<close> \<open>\<phi>\<in>formula\<close> by auto
    then obtain r where      (* I can't "obtain" this directly *)
      "r\<in>G" "sats(M,forces(?\<chi>), [P,leq,one,r,\<theta>,\<pi>])" by auto
    with \<open>filter(G)\<close> and \<open>q\<in>G\<close> obtain p where
      "p\<in>G" "<p,q>\<in>leq" "<p,r>\<in>leq" 
      unfolding filter_def compat_in_def by force
    with \<open>r\<in>G\<close> P_in_M have
      "p\<in>P" "r\<in>P"
      using \<open>G\<subseteq>P\<close>  by auto
    with \<open>\<phi>\<in>formula\<close> \<open>\<theta>\<in>M\<close> \<open>\<pi>\<in>M\<close> \<open>sats(M,forces(And(Member(0,1),\<phi>)), [P,leq,one,r,\<theta>,\<pi>])\<close> have
      "sats(M,forces(?\<chi>), [P,leq,one,p,\<theta>,\<pi>])"
      using \<open><p,r>\<in>leq\<close> streghtening by simp
    with \<open>p\<in>P\<close> \<open>\<phi>\<in>formula\<close> \<open>\<theta>\<in>M\<close> \<open>\<pi>\<in>M\<close> have
      "\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> 
                 sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<pi>)])"
      using definition_of_forces by simp
  }
    
end  (************** notepad **************)
end