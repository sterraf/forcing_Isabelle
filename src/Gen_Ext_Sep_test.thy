theory Gen_Ext_Sep_test imports Forces_locale begin

definition 
  perm_sep_forces :: "i\<Rightarrow>i" where
  "perm_sep_forces(n) == {\<langle>0, 4\<rangle>, \<langle>1, 3\<rangle>, \<langle>2, 7\<rangle>, \<langle>3, 0\<rangle>, \<langle>4, 1\<rangle>, \<langle>5, 2\<rangle>, \<langle>6, 5\<rangle>, \<langle>7, 6\<rangle>}"

lemma perm_sep_bij: "perm_sep_forces(n) \<in> bij(n,n)" 
  sorry
    
lemma conv_perm_sep_bij: "converse(perm_sep_forces(n)) \<in> bij(n,n)" 
  by (rule perm_sep_bij [THEN bij_converse_bij])

lemma perm_sep_env: 
  "perm_list(perm_sep_forces(length(env)#+7),[p,q,r,s,t,u]@env@[w]) = [t,s,w,p,q,r,u]@env"
  sorry
    
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

(* theorem separation_in_genext: *)
(* lemma    *) 

notepad begin   (************** notepad **************)
  {
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
      phi: "\<phi>\<in>formula" "arity(\<phi>) \<le> 2"
    let
      ?\<chi>="And(Member(0,1),\<phi>)"
      and   
      ?Pl1="[P,leq,one]"
    fix params
    assume
      "params\<in>list(M)"
    let 
      ?lenenv="length(params)#+7"    
    let
      ?new_form="rename(forces(?\<chi>))`?lenenv`converse(perm_sep_forces(?lenenv))"
    let
      ?\<psi>="Exists(Exists(And(pair_fm(0,1,2),?new_form)))"
    from \<open>params\<in>list(M)\<close> have
      "?lenenv \<in> nat" (*"length(params) \<in> nat"*) by simp_all
    with phi have 
      "arity(?\<chi>) \<le> length(params)#+3" 
      by (simp add:nat_union_abs1, simp add:nat_union_abs2)
    with phi have
      "arity(forces(?\<chi>)) \<le> ?lenenv"
      using arity_forces by simp
    with phi conv_perm_sep_bij arity_forces \<open>?lenenv \<in> nat\<close> have
      "?new_form \<in> formula"
      using ren_tc by simp
    then have
      "?\<psi> \<in> formula"
      by simp
    fix \<pi>
    assume
      "\<pi>\<in>M" "domain(\<pi>) \<times> P \<in> M"
    note in_M1 = \<open>\<pi>\<in>M\<close> \<open>params\<in>list(M)\<close> \<open>domain(\<pi>) \<times> P \<in> M\<close>  P_in_M one_in_M leq_in_M
    {
      fix u
      assume
        "u \<in> domain(\<pi>) \<times> P" "u \<in> M"
      with in_M1 \<open>?new_form \<in> formula\<close> \<open>?\<psi>\<in>formula\<close> have
        Eq1: "sats(M,?\<psi>,[u] @ ?Pl1 @ [\<pi>]@params) \<longleftrightarrow> 
                        (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
                          sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<pi>]@params))"
        by (auto simp add: transitivity)
      {
        fix p \<theta> 
        assume 
          "\<theta> \<in> M" "p\<in>P"
        with P_in_M have "p\<in>M" by (simp add: transitivity)
        note
          in_M = in_M1 \<open>\<theta> \<in> M\<close> \<open>p\<in>M\<close> \<open>u \<in> domain(\<pi>) \<times> P\<close> \<open>u \<in> M\<close>
        then have
          "[\<theta>,\<pi>]@params@[u] \<in> list(M)" by simp
        let
          ?new_env="perm_list(perm_sep_forces(?lenenv),?Pl1@[p,\<theta>,\<pi>]@params@[u])"
        let
          ?\<psi>="Exists(Exists(And(pair_fm(0,1,2),?new_form)))"
        have
          arit_fact: "n\<in>nat \<Longrightarrow> n\<le>2 \<Longrightarrow> 2 \<union> n = 2" "1 \<union> 2 = 2" for n
           by (auto simp add:nat_union_abs2)
        with phi  have
          chi: "?\<chi> \<in> formula" "arity(?\<chi>) \<le> 2" "forces(?\<chi>)\<in> formula" 
          by (auto)
        with arity_forces have
          "arity(forces(?\<chi>)) \<le> 6" 
          by simp
        from in_M have
          "?Pl1 \<in> list(M)" by simp
        from in_M have
          len : "?lenenv = length(?Pl1@[p,\<theta>,\<pi>]@params@[u])" 
          using \<open>?lenenv\<in>nat\<close> length_app by simp 
        have
          Eq1': "?new_env = [\<theta>,p,u]@?Pl1@[\<pi>]@params"
          using perm_sep_env  by simp
        then have
          "sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<pi>]@params) \<longleftrightarrow> sats(M,?new_form,?new_env)"
          by simp
        also have
          "sats(M,?new_form,?new_env) \<longleftrightarrow> 
        sats(M,rename(forces(?\<chi>))`length(?Pl1@[p,\<theta>,\<pi>]@params@[u])`converse(perm_sep_forces(length(params)#+7)),?new_env)" 
          using len
          by simp
        also have
          "... \<longleftrightarrow> sats(M,forces(?\<chi>),?Pl1@[p,\<theta>,\<pi>]@params@[u])"
          using  phi in_M  transD trans_M arit_fact
          apply(rule_tac ren_Sat_leq [symmetric])
             apply(auto simp add: perm_sep_bij arity_forces nat_union_abs1)
          done
        also have
          "... \<longleftrightarrow> sats(M,forces(?\<chi>), [P, leq, one,p,\<theta>,\<pi>]@(params@[u]))" by simp
        also have
          "... \<longleftrightarrow> sats(M,forces(?\<chi>), [P, leq, one,p,\<theta>,\<pi>])"
          using  in_M \<open>arity(forces(?\<chi>)) \<le> 6\<close> \<open>forces(?\<chi>)\<in>formula\<close>
          by (rule_tac arity_sats_iff, auto)
        also have
          " ... \<longleftrightarrow> (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> 
                           sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<pi>)]))"
          using in_M phi chi and definition_of_forces 
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
        finally have
          "sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<pi>]@params) \<longleftrightarrow> (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> 
                           sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<pi>)]))" by simp
      }
      then have
        Eq3: "\<theta>\<in>M \<Longrightarrow> p\<in>P \<Longrightarrow>
      sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<pi>]@params) \<longleftrightarrow>
      (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<pi>)]))" 
        for \<theta> p by simp
      with Eq1 have
        "sats(M,?\<psi>,[u] @ ?Pl1 @ [\<pi>]@params) \<longleftrightarrow> 
            (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
                           (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<pi>)])))"
        "\<theta>\<in>M \<Longrightarrow> p\<in>P \<Longrightarrow>
      sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<pi>]@params) \<longleftrightarrow>
      (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<pi>)]))"  for \<theta> p
        by auto
    }
    with in_M1 \<open>?new_form \<in> formula\<close> \<open>?\<psi>\<in>formula\<close> have
      Equivalence: "u\<in> domain(\<pi>) \<times> P \<Longrightarrow> u \<in> M \<Longrightarrow> 
            sats(M,?\<psi>,[u] @ ?Pl1 @ [\<pi>]@params) \<longleftrightarrow> 
            (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
               (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<pi>)])))" 
      and 
      Eq3': "u\<in> domain(\<pi>) \<times> P \<Longrightarrow> u \<in> M \<Longrightarrow> \<theta>\<in>M \<Longrightarrow> p\<in>P \<Longrightarrow>
      sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<pi>]@params) \<longleftrightarrow>
      (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<pi>)]))"  for u \<theta> p
      by auto
    from Equivalence  [THEN iffD1]  \<open>M_generic(G)\<close> have
      Eq3'': "u \<in> domain(\<pi>) \<times> P \<Longrightarrow> u \<in> M \<Longrightarrow>
        sats(M,?\<psi>,[u, P, leq, one, \<pi>]@params) \<Longrightarrow>
          (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
                (p \<in> G \<longrightarrow> 
                sats(M[G], ?\<chi>, [val(G, \<theta>), val(G, \<pi>)])))" for u
      by force
    from GenExt_def have
      "val(G,\<pi>)\<in>M[G]" and "\<theta>\<in>M \<Longrightarrow> val(G,\<theta>)\<in>M[G]" for \<theta>
      using \<open>\<pi>\<in>M\<close> by auto
    with Eq3'' have
      "u \<in> domain(\<pi>) \<times> P \<Longrightarrow> u \<in> M \<Longrightarrow>
        sats(M,?\<psi>,[u, P, leq, one, \<pi>]@params) \<Longrightarrow>
          (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
                (p \<in> G \<longrightarrow> 
                val(G,\<theta>) \<in> val(G,\<pi>) \<and> sats(M[G], \<phi>, [val(G, \<theta>), val(G, \<pi>)])))" for u
      by auto
    with \<open>domain(\<pi>)*P\<in>M\<close> have
      "\<forall>u\<in>domain(\<pi>)*P . sats(M,?\<psi>,[u] @ ?Pl1 @ [\<pi>]@params)  \<longrightarrow>
      (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
        (p \<in> G \<longrightarrow> val(G, \<theta>)\<in>val(G, \<pi>) \<and> sats(M[G], \<phi>, [val(G, \<theta>), val(G, \<pi>)])))"
      by (simp add:transitivity)
    then have
      "{u\<in>domain(\<pi>)*P . sats(M,?\<psi>,[u] @ ?Pl1 @ [\<pi>]@params) } \<subseteq>
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
    then have
      in_val_n: "<\<theta>,p>\<in>domain(\<pi>)*P \<Longrightarrow> <\<theta>,p>\<in>M \<Longrightarrow> p\<in>G \<Longrightarrow> p\<in>P \<Longrightarrow> 
      sats(M,?\<psi>,[<\<theta>,p>] @ ?Pl1 @ [\<pi>]@params) \<Longrightarrow> val(G,\<theta>)\<in>val(G,?n)" for \<theta> p
      using val_of_elem by simp
    from \<open>?m\<in>M\<close> val_of_name and \<open>val(G,\<pi>) = c\<close> have
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
      val_m: "val(G,?m) = {x\<in>c. sats(M[G], \<phi>, [x, c])}" by simp
    {
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
      from \<open><\<theta>,q>\<in>\<pi>\<close> \<open>\<pi>\<in>M\<close> trans_M have 
        "\<theta>\<in>M"
        unfolding Pair_def Transset_def by auto 
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
      with \<open>r\<in>G\<close>  \<open>q\<in>G\<close> P_in_M have
        "p\<in>P" "r\<in>P" "q\<in>P" "p\<in>M"
        using \<open>G\<subseteq>P\<close>  by (auto simp add:transitivity)
      with \<open>\<phi>\<in>formula\<close> \<open>\<theta>\<in>M\<close> \<open>\<pi>\<in>M\<close> \<open>sats(M,forces(And(Member(0,1),\<phi>)), [P,leq,one,r,\<theta>,\<pi>])\<close> have
        "sats(M,forces(?\<chi>), [P,leq,one,p,\<theta>,\<pi>])"
        using \<open><p,r>\<in>leq\<close> streghtening by simp
      with \<open>p\<in>P\<close> \<open>\<phi>\<in>formula\<close> \<open>\<theta>\<in>M\<close> \<open>\<pi>\<in>M\<close> have
        "\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> 
                 sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<pi>)])"
        using definition_of_forces by simp
      with \<open>p\<in>P\<close> \<open>\<theta>\<in>M\<close>  have
        Eq6: "\<exists>\<theta>'\<in>M. \<exists>p'\<in>P.  <\<theta>,p> = <\<theta>',p'> \<and> (\<forall>F. M_generic(F) \<and> p' \<in> F \<longrightarrow> 
                 sats(M[F], ?\<chi>, [val(F, \<theta>'), val(F, \<pi>)]))" by auto
      from \<open>\<pi>\<in>M\<close> \<open><\<theta>,q>\<in>\<pi>\<close> have
        "<\<theta>,q> \<in> M" by (simp add:transitivity)
      from \<open><\<theta>,q>\<in>\<pi>\<close> \<open>\<theta>\<in>M\<close> \<open>p\<in>P\<close>  \<open>p\<in>M\<close> have
        "<\<theta>,p>\<in>M" "<\<theta>,p>\<in>domain(\<pi>)\<times>P" 
        using pairM by auto
      with \<open>\<theta>\<in>M\<close> Eq6 \<open>p\<in>P\<close> have
        "sats(M,?\<psi>,[<\<theta>,p>] @ ?Pl1 @ [\<pi>]@params)"
        using Equivalence [THEN iffD2]  by auto
          (* with \<open><\<theta>,p>\<in>domain(\<pi>)\<times>P\<close> have
      "\<exists>u\<in>domain(\<pi>)\<times>P. sats(M,?\<psi>,[u] @ ?Pl1 @ [\<pi>]@params)" by auto *)
      with \<open><\<theta>,p>\<in>domain(\<pi>)\<times>P\<close>  \<open><\<theta>,p>\<in>M\<close> \<open>p\<in>G\<close> \<open>val(G,\<theta>)=x\<close> have
        "x\<in>val(G,?n)"   
        using in_val_n by auto
    }
    with val_m  have 
      "val(G,?m) \<subseteq> val(G,?n)" by auto
    with \<open>?n\<in>M\<close> \<open>?m\<in>M\<close> val_m first_incl have
      "val(G,?n) = {x\<in>c. sats(M[G], \<phi>, [x, c])}" by auto
    with \<open>?n\<in>M\<close> GenExt_def have
      "{x\<in>c. sats(M[G], \<phi>, [x, c])}\<in> M[G]" by force
  }
  then have
    sep_aux: "M_generic(G) \<Longrightarrow> Transset(M[G]) \<Longrightarrow>
     \<phi> \<in> formula \<Longrightarrow> arity(\<phi>) \<le> 2 \<Longrightarrow> val(G, \<pi>) = c \<Longrightarrow> params \<in> list(M) \<Longrightarrow> 
     \<pi> \<in> M \<Longrightarrow> \<sigma> \<in> M \<Longrightarrow> domain(\<pi>) \<times> P \<in> M \<Longrightarrow>  domain(\<pi>) \<in> M \<Longrightarrow>
     {u \<in> domain(\<pi>) \<times> P .
        sats(M, Exists(Exists(And(pair_fm(0, 1, 2), rename(forces(And(Member(0, 1), \<phi>))) ` 
          (length(params)#+7) ` converse(perm_sep_forces(length(params)#+7))))),
         [u] @ [P, leq, one] @ [\<pi>] @ params)} \<in>  M \<Longrightarrow>
     {u \<in> domain(\<pi>) \<times> P .
       \<exists>\<theta>\<in>M. \<exists>p\<in>P. u = \<langle>\<theta>, p\<rangle> \<and> (p \<in> G \<longrightarrow> val(G, \<theta>) \<in> val(G, \<pi>) \<and> sats(M[G], \<phi>, [val(G, \<theta>), val(G, \<pi>)]))} \<in> M 
      \<Longrightarrow>
      {x\<in>c. sats(M[G], \<phi>, [x, c])}\<in> M[G]" for G \<pi> c \<sigma> \<phi> params by simp
  fix \<phi> G \<pi> c \<sigma> params   
  assume 
    asm: "arity(\<phi>)= 1" "M_generic(G)" "Transset(M[G])" "
     \<phi> \<in> formula " "val(G, \<pi>) = c" "params \<in> list(M)" "
     \<pi> \<in> M" "\<sigma> \<in> M" "domain(\<pi>) \<times> P \<in> M" " domain(\<pi>) \<in> M" "
     {u \<in> domain(\<pi>) \<times> P .
        sats(M, Exists(Exists(And(pair_fm(0, 1, 2), rename(forces(And(Member(0, 1), \<phi>))) ` 
          (length(params)#+7) ` converse(perm_sep_forces(length(params)#+7))))),
         [u] @ [P, leq, one] @ [\<pi>] @ params)} \<in>  M" "
     {u \<in> domain(\<pi>) \<times> P .
       \<exists>\<theta>\<in>M. \<exists>p\<in>P. u = \<langle>\<theta>, p\<rangle> \<and> (p \<in> G \<longrightarrow> val(G, \<theta>) \<in> val(G, \<pi>) \<and> sats(M[G], \<phi>, [val(G, \<theta>), val(G, \<pi>)]))} \<in> M"
    "c\<in>M[G]"
  then have
    "arity(\<phi>)\<le> 2"  by simp_all
  with asm sep_aux have
    S_in_MG: "{x\<in>c. sats(M[G], \<phi>, [x,c])}\<in> M[G]"  by simp
  {
    fix x
    assume 
      "x\<in>c"
    with asm have
      "x\<in>M[G]"
      by (simp add:\<open>Transset(M[G])\<close> Transset_intf)
    with \<open>arity(\<phi>) = 1\<close> \<open>\<phi> \<in> formula\<close> \<open>c\<in>M[G]\<close> have
      "sats(M[G], \<phi>, [x]@[c]) \<longleftrightarrow> sats(M[G], \<phi>, [x])" 
      by (rule_tac arity_sats_iff, simp_all)   (* Enhance this *)
  }
  with S_in_MG have
   "{x\<in>c. sats(M[G], \<phi>, [x])}\<in> M[G]"  by simp   
end
end