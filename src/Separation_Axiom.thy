theory Separation_Axiom 
  imports Forcing_Theorems Renaming 
begin

lemma apply_fun: "f \<in> Pi(A,B) ==> <a,b>: f \<Longrightarrow> f`a = b"
  by(auto simp add: apply_iff)

definition 
  perm_sep_forces :: "i" where
  "perm_sep_forces == {<0,3>,<1,4>,<2,5>,<3,1>,<4,0>,<5,6>,<6,7>,<7,2>}" 

lemma perm_sep_ftc : "perm_sep_forces \<in> 8 -||> 8"
  by(unfold perm_sep_forces_def,(rule consI,auto)+,rule emptyI)

lemma dom_perm_sep : "domain(perm_sep_forces) = 8"     
  by(unfold perm_sep_forces_def,auto)
  
lemma perm_sep_tc : "perm_sep_forces \<in> 8 \<rightarrow> 8"
  by(subst dom_perm_sep[symmetric],rule FiniteFun_is_fun,rule perm_sep_ftc)

lemma perm_sep_env : 
  "{p,q,r,s,t,u,v,w} \<subseteq> A \<Longrightarrow> j<8 \<Longrightarrow>
  nth(j,[t,s,w,p,q,r,u,v]) = nth(perm_sep_forces`j,[q,p,v,t,s,w,r,u])"
  apply(subgoal_tac "j\<in>nat")
  apply(rule natE,simp,subst apply_fun,rule perm_sep_tc,simp add:perm_sep_forces_def,simp_all)+
  apply(subst apply_fun,rule perm_sep_tc,simp add:perm_sep_forces_def,simp_all,drule ltD,auto)
  done
  
context G_generic begin

lemmas transitivity = Transset_intf trans_M
  
lemma one_in_M: "one \<in> M"
  by (insert one_in_P P_in_M, simp add: transitivity)

lemma six_sep_aux: 
  assumes
    "b \<in> M" "[\<sigma>, \<pi>] \<in> list(M)" "\<psi>\<in>formula" "arity(\<psi>) \<le> 6"
  shows
    "{u \<in> b. sats(M,\<psi>,[u] @ [P, leq, one] @ [\<sigma>, \<pi>])} \<in> M" 
proof -
  from assms P_in_M leq_in_M one_in_M  
  have "(\<forall>u\<in>M. separation(##M,\<lambda>x. sats(M,\<psi>,[x] @ [P, leq, one] @ [\<sigma>, \<pi>])))" 
    using sixp_sep by simp  
  with \<open>b \<in> M\<close> show ?thesis
    using separation_iff by auto
qed
  
lemma Collect_sats_in_MG :
  assumes
    "\<pi> \<in> M" "\<sigma> \<in> M" "val(G, \<pi>) = c" "val(G, \<sigma>) = w"
    "\<phi> \<in> formula" "arity(\<phi>) \<le> 2"
  shows    
    "{x\<in>c. sats(M[G], \<phi>, [x, w])}\<in> M[G]"
proof -  
  let ?\<chi>="And(Member(0,2),\<phi>)" and ?Pl1="[P,leq,one]"
  let ?new_form="ren(forces(?\<chi>))`8`8`perm_sep_forces"
  let ?\<psi>="Exists(Exists(And(pair_fm(0,1,2),?new_form)))"
  have "8\<in>nat" by simp
  note phi = \<open>\<phi>\<in>formula\<close> \<open>arity(\<phi>) \<le> 2\<close> 
  then
  have "arity(?\<chi>) \<le> 3" 
    using nat_simp_union leI by simp
  with phi
  have "arity(forces(?\<chi>)) \<le> 8"
    using nat_simp_union arity_forces leI by simp
  with phi definability[of "?\<chi>"] arity_forces
  have "?new_form \<in> formula"
    using ren_tc[of "forces(?\<chi>)" 8 8 "perm_sep_forces"] perm_sep_tc by simp
  then
  have "?\<psi> \<in> formula"
    by simp
  from \<open>\<phi>\<in>formula\<close>
  have "forces(?\<chi>) \<in> formula"
    using definability by simp
  with \<open>arity(forces(?\<chi>)) \<le> 8\<close> 
  have "arity(?new_form) \<le> 8"
    using ren_arity perm_sep_tc definability by simp
  then 
  have "arity(?\<psi>) \<le> 6" 
    unfolding pair_fm_def upair_fm_def 
    using  nat_simp_union pred2_Un[of "8"] by simp
  from \<open>\<pi>\<in>M\<close> \<open>\<sigma>\<in>M\<close> P_in_M 
  have "domain(\<pi>)\<in>M" "domain(\<pi>) \<times> P \<in> M"
    by (simp_all del:setclass_iff add:setclass_iff[symmetric])
  note in_M = \<open>\<pi>\<in>M\<close> \<open>\<sigma>\<in>M\<close> \<open>domain(\<pi>) \<times> P \<in> M\<close>  P_in_M one_in_M leq_in_M
  {
    fix u
    assume "u \<in> domain(\<pi>) \<times> P" "u \<in> M"
    with in_M \<open>?new_form \<in> formula\<close> \<open>?\<psi>\<in>formula\<close> 
    have Eq1: "sats(M,?\<psi>,[u] @ ?Pl1 @ [\<sigma>,\<pi>]) \<longleftrightarrow> 
                        (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =\<langle>\<theta>,p\<rangle> \<and> 
                          sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<sigma>,\<pi>]))"
      by (auto simp add: transitivity)
    have Eq3: "\<theta>\<in>M \<Longrightarrow> p\<in>P \<Longrightarrow>
       sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<sigma>,\<pi>]) \<longleftrightarrow>
          (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<sigma>), val(F, \<pi>)]))" 
      for \<theta> p 
    proof -
      fix p \<theta> 
      assume "\<theta> \<in> M" "p\<in>P"
      with P_in_M have "p\<in>M" by (simp add: transitivity)

      note in_M' = in_M \<open>\<theta> \<in> M\<close> \<open>p\<in>M\<close> \<open>u \<in> domain(\<pi>) \<times> P\<close> \<open>u \<in> M\<close>
      then 
      have "[\<theta>,\<sigma>,u] \<in> list(M)" by simp
      let ?env="?Pl1@[p,\<theta>,\<sigma>,\<pi>,u]"
      let ?new_env=" [\<theta>,p,u,P,leq,one,\<sigma>,\<pi>]"
      let ?\<psi>="Exists(Exists(And(pair_fm(0,1,2),?new_form)))"

      have "?\<chi> \<in> formula" "arity(?\<chi>) \<le> 3" "forces(?\<chi>)\<in> formula"  
        using phi nat_simp_union leI by auto
      with arity_forces 
      have "arity(forces(?\<chi>)) \<le> 7" 
        by simp     
      then have "arity(forces(?\<chi>)) \<le> 8" using le_trans by simp
      from in_M' 
      have "?Pl1 \<in> list(M)" by simp
      from in_M' have "?env \<in> list(M)" by simp

      have Eq1': "?new_env \<in> list(M)" using in_M'  by simp 
      then 
      have "sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<sigma>,\<pi>]) \<longleftrightarrow> sats(M,?new_form,?new_env)"
        by simp
      also from \<open>forces(?\<chi>)\<in>formula\<close> \<open>8\<in>nat\<close>  \<open>?env\<in>list(M)\<close> 
        \<open>?new_env\<in>list(M)\<close> perm_sep_tc \<open>arity(forces(?\<chi>)) \<le> 8\<close>

      have "... \<longleftrightarrow> sats(M,forces(?\<chi>),?env)"
        using sats_iff_sats_ren[of _ 8 8 ?env M ?new_env] perm_sep_env
        by auto
      also 
      have "... \<longleftrightarrow> sats(M,forces(?\<chi>), [P, leq, one,p,\<theta>,\<sigma>,\<pi>]@[u])" by simp
      also from \<open>arity(forces(?\<chi>)) \<le> 7\<close> \<open>forces(?\<chi>)\<in>formula\<close> in_M'  phi 
      have "... \<longleftrightarrow> sats(M,forces(?\<chi>), [P, leq, one,p,\<theta>,\<sigma>,\<pi>])"        
        by (rule_tac arity_sats_iff,auto)
      also from \<open>arity(forces(?\<chi>)) \<le> 7\<close> \<open>forces(?\<chi>)\<in>formula\<close> in_M' phi 
      have " ... \<longleftrightarrow> (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> 
                           sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<sigma>), val(F, \<pi>)]))"
        using  definition_of_forces 
      proof (intro iffI)
        assume a1: "sats(M, forces(?\<chi>), [P, leq, one,p,\<theta>,\<sigma>,\<pi>])"
        note definition_of_forces
        then 
        have "p \<in> P \<Longrightarrow> ?\<chi>\<in>formula \<Longrightarrow> [\<theta>,\<sigma>,\<pi>] \<in> list(M) \<Longrightarrow>
                  sats(M, forces(?\<chi>), [P, leq, one, p] @ [\<theta>,\<sigma>,\<pi>]) \<Longrightarrow> 
              \<forall>G. M_generic(G) \<and> p \<in> G \<longrightarrow> sats(M[G], ?\<chi>, map(val(G), [\<theta>,\<sigma>,\<pi>]))" ..
        then 
        show "\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> 
                  sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<sigma>), val(F, \<pi>)])"
          using  \<open>?\<chi>\<in>formula\<close> \<open>p\<in>P\<close> a1 \<open>\<theta>\<in>M\<close> \<open>\<sigma>\<in>M\<close> \<open>\<pi>\<in>M\<close> by auto
      next
        assume "\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> 
                   sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<sigma>), val(F, \<pi>)])"
        with definition_of_forces [THEN iffD2] 
        show "sats(M, forces(?\<chi>), [P, leq, one,p,\<theta>,\<sigma>,\<pi>])"
          using  \<open>?\<chi>\<in>formula\<close> \<open>p\<in>P\<close> in_M' by auto
      qed
      finally 
      show "sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<sigma>,\<pi>]) \<longleftrightarrow> (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> 
                           sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<sigma>), val(F, \<pi>)]))" by simp
    qed
    with Eq1 
    have "sats(M,?\<psi>,[u] @ ?Pl1 @ [\<sigma>,\<pi>]) \<longleftrightarrow> 
         (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =\<langle>\<theta>,p\<rangle> \<and> 
          (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<sigma>), val(F, \<pi>)])))"
      by auto 
  }
  then 
  have Equivalence: "u\<in> domain(\<pi>) \<times> P \<Longrightarrow> u \<in> M \<Longrightarrow> 
       sats(M,?\<psi>,[u] @ ?Pl1 @ [\<sigma>,\<pi>]) \<longleftrightarrow> 
         (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =\<langle>\<theta>,p\<rangle> \<and> 
          (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<sigma>), val(F, \<pi>)])))" 
    for u 
    by simp
  with generic 
  have "(\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =\<langle>\<theta>,p\<rangle> \<and> (p\<in>G \<longrightarrow> sats(M[G],?\<chi>,[val(G,\<theta>), val(G,\<sigma>), val(G,\<pi>)])))" 
   (is "(\<exists>\<theta>\<in>M. \<exists>p\<in>P. _ \<and> ( _ \<longrightarrow> sats(_,_,?vals(\<theta>))))")
    if "u \<in> domain(\<pi>) \<times> P" "u \<in> M"  "sats(M,?\<psi>,[u, P, leq, one,\<sigma>, \<pi>])" for u
    using that
    by force
  moreover 
  have "val(G,\<sigma>)\<in>M[G]" and "\<theta>\<in>M \<Longrightarrow> val(G,\<theta>)\<in>M[G]" for \<theta>
    using GenExt_def \<open>\<sigma>\<in>M\<close> by auto
  ultimately 
  have "(\<exists>\<theta>\<in>M. \<exists>p\<in>P. u=\<langle>\<theta>,p\<rangle> \<and> (p\<in>G \<longrightarrow> val(G,\<theta>)\<in>val(G,\<pi>) \<and> sats(M[G], \<phi>, ?vals(\<theta>))))"
    if "u \<in> domain(\<pi>) \<times> P" "u \<in> M"  "sats(M,?\<psi>,[u, P, leq, one,\<sigma>, \<pi>])" for u
    using that \<open>\<pi>\<in>M\<close> by auto
  with \<open>domain(\<pi>)\<times>P\<in>M\<close> 
  have "\<forall>u\<in>domain(\<pi>)\<times>P . sats(M,?\<psi>,[u] @ ?Pl1 @ [\<sigma>,\<pi>]) \<longrightarrow> (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =\<langle>\<theta>,p\<rangle> \<and>
        (p \<in> G \<longrightarrow> val(G, \<theta>)\<in>val(G, \<pi>) \<and> sats(M[G], \<phi>, ?vals(\<theta>))))"
    by (simp add:transitivity)
  then 
  have "{u\<in>domain(\<pi>)\<times>P . sats(M,?\<psi>,[u] @ ?Pl1 @ [\<sigma>,\<pi>]) } \<subseteq>
     {u\<in>domain(\<pi>)\<times>P . \<exists>\<theta>\<in>M. \<exists>p\<in>P. u =\<langle>\<theta>,p\<rangle> \<and> 
       (p \<in> G \<longrightarrow> val(G, \<theta>)\<in>val(G, \<pi>) \<and> sats(M[G], \<phi>, ?vals(\<theta>)))}"
    (is "?n\<subseteq>?m") 
    by auto
  with val_mono 
  have first_incl: "val(G,?n) \<subseteq> val(G,?m)" 
    by simp
  note  \<open>val(G,\<pi>) = c\<close> \<open>val(G,\<sigma>) = w\<close> (* from the assumptions *)
  with \<open>?\<psi>\<in>formula\<close> \<open>arity(?\<psi>) \<le> 6\<close> in_M 
  have "?n\<in>M" 
    using six_sep_aux by simp
  from generic 
  have "filter(G)" "G\<subseteq>P" 
    unfolding M_generic_def filter_def by simp_all
  from \<open>val(G,\<pi>) = c\<close> \<open>val(G,\<sigma>) = w\<close> 
  have "val(G,?m) =
               {val(G,t) .. t\<in>domain(\<pi>) , \<exists>q\<in>P .  
                    (\<exists>\<theta>\<in>M. \<exists>p\<in>P. <t,q> = \<langle>\<theta>, p\<rangle> \<and> 
            (p \<in> G \<longrightarrow> val(G, \<theta>) \<in> c \<and> sats(M[G], \<phi>, [val(G, \<theta>), w, c])) \<and> q \<in> G)}"
    using val_of_name by auto
  also 
  have "... =  {val(G,t) .. t\<in>domain(\<pi>) , \<exists>q\<in>P. 
                   val(G, t) \<in> c \<and> sats(M[G], \<phi>, [val(G, t), w, c]) \<and> q \<in> G}" 
  proof -

    have "t\<in>M \<Longrightarrow>
      (\<exists>q\<in>P. (\<exists>\<theta>\<in>M. \<exists>p\<in>P. <t,q> = \<langle>\<theta>, p\<rangle> \<and> 
              (p \<in> G \<longrightarrow> val(G, \<theta>) \<in> c \<and> sats(M[G], \<phi>, [val(G, \<theta>), w, c])) \<and> q \<in> G)) 
      \<longleftrightarrow> 
      (\<exists>q\<in>P. val(G, t) \<in> c \<and> sats(M[G], \<phi>, [val(G, t), w, c]) \<and> q \<in> G)" for t
      by auto
    then show ?thesis using \<open>domain(\<pi>)\<in>M\<close> by (auto simp add:transitivity)
  qed
  also 
  have "... =  {x .. x\<in>c , \<exists>q\<in>P. x \<in> c \<and> sats(M[G], \<phi>, [x, w, c]) \<and> q \<in> G}"
  proof

    show "... \<subseteq> {x .. x\<in>c , \<exists>q\<in>P. x \<in> c \<and> sats(M[G], \<phi>, [x, w, c]) \<and> q \<in> G}"
      by auto
  next 
    (* Now we show the other inclusion:
      {x .. x\<in>c , \<exists>q\<in>P. x \<in> c \<and> sats(M[G], \<phi>, [x, w, c]) \<and> q \<in> G}
      \<subseteq>
      {val(G,t)..t\<in>domain(\<pi>),\<exists>q\<in>P.val(G,t)\<in>c\<and>sats(M[G],\<phi>,[val(G,t),w])\<and>q\<in>G}
    *)
    {
      fix x
      assume "x\<in>{x .. x\<in>c , \<exists>q\<in>P. x \<in> c \<and> sats(M[G], \<phi>, [x, w, c]) \<and> q \<in> G}"
      then 
      have "\<exists>q\<in>P. x \<in> c \<and> sats(M[G], \<phi>, [x, w, c]) \<and> q \<in> G"
        by simp
      with \<open>val(G,\<pi>) = c\<close>  
      have "\<exists>q\<in>P. \<exists>t\<in>domain(\<pi>). val(G,t) =x \<and> sats(M[G], \<phi>, [val(G,t), w, c]) \<and> q \<in> G" 
        using Sep_and_Replace elem_of_val by auto
    }
    then 
    show " {x .. x\<in>c , \<exists>q\<in>P. x \<in> c \<and> sats(M[G], \<phi>, [x, w, c]) \<and> q \<in> G} \<subseteq> ..."
      using SepReplace_iff by force
  qed
  also 
  have " ... = {x\<in>c. sats(M[G], \<phi>, [x, w, c])}"
    using \<open>G\<subseteq>P\<close> G_nonempty by force
  finally 
  have val_m: "val(G,?m) = {x\<in>c. sats(M[G], \<phi>, [x, w, c])}" by simp
  have "val(G,?m) \<subseteq> val(G,?n)" 
  proof
    fix x
    assume "x \<in> val(G,?m)"
    with val_m 
    have Eq4: "x \<in> {x\<in>c. sats(M[G], \<phi>, [x, w, c])}" by simp
    with \<open>val(G,\<pi>) = c\<close> 
    have "x \<in> val(G,\<pi>)" by simp
    then 
    have "\<exists>\<theta>. \<exists>q\<in>G. \<langle>\<theta>,q\<rangle>\<in>\<pi> \<and> val(G,\<theta>) =x" 
      using elem_of_val_pair by auto
    then obtain \<theta> q where
      "\<langle>\<theta>,q\<rangle>\<in>\<pi>" "q\<in>G" "val(G,\<theta>)=x" by auto
    from \<open>\<langle>\<theta>,q\<rangle>\<in>\<pi>\<close> \<open>\<pi>\<in>M\<close> trans_M 
    have "\<theta>\<in>M"
      unfolding Pair_def Transset_def by auto 
    with \<open>\<pi>\<in>M\<close> \<open>\<sigma>\<in>M\<close> 
    have "[val(G,\<theta>), val(G,\<sigma>), val(G,\<pi>)]\<in>list(M[G])" 
      using GenExt_def by auto
    with  Eq4 \<open>val(G,\<theta>)=x\<close> \<open>val(G,\<pi>) = c\<close> \<open>val(G,\<sigma>) = w\<close> \<open>x \<in> val(G,\<pi>)\<close> 
    have Eq5: "sats(M[G], And(Member(0,2),\<phi>), [val(G,\<theta>), val(G,\<sigma>), val(G,\<pi>)])" 
      by auto
        (* Recall ?\<chi> = And(Member(0,2),\<phi>) *)
    with \<open>\<theta>\<in>M\<close> \<open>\<pi>\<in>M\<close>  \<open>\<sigma>\<in>M\<close> Eq5 \<open>M_generic(G)\<close> \<open>\<phi>\<in>formula\<close> 
    have "(\<exists>r\<in>G. sats(M,forces(?\<chi>), [P,leq,one,r,\<theta>,\<sigma>,\<pi>]))"
      using truth_lemma  by auto
    then obtain r where      (* I can't "obtain" this directly *)
      "r\<in>G" "sats(M,forces(?\<chi>), [P,leq,one,r,\<theta>,\<sigma>,\<pi>])" by auto
    with \<open>filter(G)\<close> and \<open>q\<in>G\<close> obtain p where
      "p\<in>G" "<p,q>\<in>leq" "<p,r>\<in>leq" 
      unfolding filter_def compat_in_def by force
    with \<open>r\<in>G\<close>  \<open>q\<in>G\<close> \<open>G\<subseteq>P\<close> 
    have "p\<in>P" "r\<in>P" "q\<in>P" "p\<in>M"
      using  P_in_M  by (auto simp add:transitivity)
    with \<open>\<phi>\<in>formula\<close> \<open>\<theta>\<in>M\<close> \<open>\<pi>\<in>M\<close> \<open>\<sigma>\<in>M\<close>  \<open><p,r>\<in>leq\<close> 
      \<open>sats(M,forces(?\<chi>), [P,leq,one,r,\<theta>,\<sigma>,\<pi>])\<close> 
    have "sats(M,forces(?\<chi>), [P,leq,one,p,\<theta>,\<sigma>,\<pi>])"
      using strengthening by simp
    with \<open>p\<in>P\<close> \<open>\<phi>\<in>formula\<close> \<open>\<theta>\<in>M\<close> \<open>\<pi>\<in>M\<close> \<open>\<sigma>\<in>M\<close> 
    have "\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> 
                 sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<sigma>), val(F,\<pi>)])"
      using definition_of_forces by simp
    with \<open>p\<in>P\<close> \<open>\<theta>\<in>M\<close>  
    have Eq6: "\<exists>\<theta>'\<in>M. \<exists>p'\<in>P.  \<langle>\<theta>,p\<rangle> = <\<theta>',p'> \<and> (\<forall>F. M_generic(F) \<and> p' \<in> F \<longrightarrow> 
                 sats(M[F], ?\<chi>, [val(F, \<theta>'), val(F, \<sigma>), val(F,\<pi>)]))" by auto
    from \<open>\<pi>\<in>M\<close> \<open>\<langle>\<theta>,q\<rangle>\<in>\<pi>\<close> 
    have "\<langle>\<theta>,q\<rangle> \<in> M" by (simp add:transitivity)
    from \<open>\<langle>\<theta>,q\<rangle>\<in>\<pi>\<close> \<open>\<theta>\<in>M\<close> \<open>p\<in>P\<close>  \<open>p\<in>M\<close> 
    have "\<langle>\<theta>,p\<rangle>\<in>M" "\<langle>\<theta>,p\<rangle>\<in>domain(\<pi>)\<times>P" 
      using pairM by auto
    with \<open>\<theta>\<in>M\<close> Eq6 \<open>p\<in>P\<close> 
    have "sats(M,?\<psi>,[\<langle>\<theta>,p\<rangle>] @ ?Pl1 @ [\<sigma>,\<pi>])"
      using Equivalence  by auto
    with \<open>\<langle>\<theta>,p\<rangle>\<in>domain(\<pi>)\<times>P\<close> 
    have "\<langle>\<theta>,p\<rangle>\<in>?n" by simp
    with \<open>p\<in>G\<close> \<open>p\<in>P\<close> 
    have "val(G,\<theta>)\<in>val(G,?n)" 
      using  val_of_elem[of \<theta> p] by simp
    with \<open>val(G,\<theta>)=x\<close> 
    show "x\<in>val(G,?n)" by simp
  qed (* proof of "val(G,?m) \<subseteq> val(G,?n)" *)
  with val_m first_incl 
  have "val(G,?n) = {x\<in>c. sats(M[G], \<phi>, [x, w, c])}" by auto
  also 
  have " ... = {x\<in>c. sats(M[G], \<phi>, [x, w])}"
  proof -
    {
      fix x
      assume "x\<in>c"
      moreover from assms 
      have "c\<in>M[G]" "w\<in>M[G]"
        unfolding GenExt_def by auto
      moreover with \<open>x\<in>c\<close> 
      have "x\<in>M[G]"
        by (simp add:Transset_MG Transset_intf)
      ultimately 
      have "sats(M[G], \<phi>, [x,w]@[c]) \<longleftrightarrow> sats(M[G], \<phi>, [x,w])" 
        using phi by (rule_tac arity_sats_iff, simp_all)   (* Enhance this *)
    }
    then show ?thesis by auto
  qed      
  finally 
  show "{x\<in>c. sats(M[G], \<phi>, [x, w])}\<in> M[G]" 
    using \<open>?n\<in>M\<close> GenExt_def by force
qed

theorem separation_in_MG:
  assumes 
    "\<phi>\<in>formula" and "arity(\<phi>) = 1 \<or> arity(\<phi>)=2"
  shows  
    "(\<forall>a\<in>(M[G]). separation(##M[G],\<lambda>x. sats(M[G],\<phi>,[x,a])))"
proof -
  { 
    fix c w 
    assume "c\<in>M[G]" "w\<in>M[G]"
    then 
    obtain \<pi> \<sigma> where "val(G, \<pi>) = c" "val(G, \<sigma>) = w" "\<pi> \<in> M" "\<sigma> \<in> M" 
      using GenExt_def by auto
    with assms 
    have Eq1: "{x\<in>c. sats(M[G], \<phi>, [x,w])} \<in> M[G]"
      using Collect_sats_in_MG  by auto
  }
  then 
  show ?thesis 
    using separation_iff rev_bexI unfolding is_Collect_def by force
qed
end   (* context: G_generic *)
end