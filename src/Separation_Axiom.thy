theory Separation_Axiom 
  imports Forcing_Theorems Separation_Rename
begin

context G_generic
begin

lemma map_val :
  assumes "env\<in>list(M[G])"
  shows "\<exists>nenv\<in>list(M). env = map(val(G),nenv)"
  using assms
  proof(induct env)
    case Nil
    have "map(val(G),Nil) = Nil" by simp
    then show ?case by force
  next
    case (Cons a l)
    then obtain a' l' where
      "l' \<in> list(M)" "l=map(val(G),l')" "a = val(G,a')"
      "Cons(a,l) = map(val(G),Cons(a',l'))" "Cons(a',l') \<in> list(M)"
      using \<open>a\<in>M[G]\<close> GenExtD
      by force
    then show ?case by force
qed


lemma Collect_sats_in_MG :
  assumes
    "c\<in>M[G]"
    "\<phi> \<in> formula" "env\<in>list(M[G])" "arity(\<phi>) \<le> 1 #+ length(env)"
  shows    
    "{x\<in>c. sats(M[G], \<phi>, [x] @ env)}\<in> M[G]"
proof -  
  from \<open>c\<in>M[G]\<close>
  obtain \<pi> where "\<pi> \<in> M" "val(G, \<pi>) = c"
    using GenExt_def by auto
  let ?\<chi>="And(Member(0,1 #+ length(env)),\<phi>)" and ?Pl1="[P,leq,one]"
  let ?new_form="sep_ren(length(env),forces(?\<chi>))"
  let ?\<psi>="Exists(Exists(And(pair_fm(0,1,2),?new_form)))"
  note phi = \<open>\<phi>\<in>formula\<close> \<open>arity(\<phi>) \<le> 1 #+ length(env)\<close>
  with \<open>env\<in>list(_)\<close>
  have "arity(forces(?\<chi>)) \<le> 6 #+ length(env)"
    using nat_simp_union arity_forces leI by simp
  then
  have "arity(forces(?\<chi>)) \<le> 7 #+ length(env)"
    using nat_simp_union arity_forces leI by simp
  with \<open>arity(forces(?\<chi>)) \<le>7 #+ _\<close> \<open>env \<in> _\<close> \<open>\<phi> \<in> formula\<close>
  have "arity(?new_form) \<le> 7 #+ length(env)" "?new_form \<in> formula"
    using arity_rensep[OF definability[of "?\<chi>"]]  definability[of "?\<chi>"] type_rensep 
    by auto
  then
  have "pred(pred(arity(?new_form))) \<le> 5 #+ length(env)" "?\<psi>\<in>formula"
    unfolding pair_fm_def upair_fm_def 
    using nat_simp_union length_type[OF \<open>env\<in>list(M[G])\<close>] 
        pred_mono[OF _ pred_mono[OF _ \<open>arity(?new_form) \<le> _\<close>]]
    by auto
  with \<open>arity(?new_form) \<le> _\<close> \<open>?new_form \<in> formula\<close>
  have "arity(?\<psi>) \<le> 5 #+ length(env)"
    unfolding pair_fm_def upair_fm_def 
    using nat_simp_union arity_forces 
    by auto
  from \<open>\<phi>\<in>formula\<close>
  have "forces(?\<chi>) \<in> formula"
    using definability by simp
  from \<open>\<pi>\<in>M\<close> P_in_M 
  have "domain(\<pi>)\<in>M" "domain(\<pi>) \<times> P \<in> M"
    by (simp_all del:setclass_iff add:setclass_iff[symmetric])
  from \<open>env \<in> _\<close>
  obtain nenv where "nenv\<in>list(M)" "env = map(val(G),nenv)"
    using map_val by auto
  then
  have "length(nenv) = length(env)" "1\<le>2" by simp_all
  from \<open>arity(\<phi>) \<le> _\<close> 
  have "arity(\<phi>) \<le> 2#+ length(env)" 
    using length_type[OF \<open>env\<in>_\<close>] le_trans[OF \<open>arity(\<phi>)\<le>_\<close>]
      add_le_mono[OF \<open>1\<le>2\<close> le_refl[of "length(env)"]] by auto
  with \<open>nenv\<in>_\<close> \<open>env\<in>_\<close> \<open>\<pi>\<in>M\<close>
  have "arity(?\<chi>) \<le> length([\<theta>] @ nenv @ [\<pi>])" for \<theta> 
    using  
   nat_union_abs2[OF nat_into_Ord[OF arity_type[OF \<open>\<phi>\<in>_\<close>]] add_type[THEN nat_into_Ord] \<open>arity(\<phi>) \<le> 2#+ _\<close>]
   \<open>length(nenv) = length(env)\<close> arity_type length_type 
      nat_simp_union 
      length_app
    by simp    
  note in_M = \<open>\<pi>\<in>M\<close> \<open>domain(\<pi>) \<times> P \<in> M\<close>  P_in_M one_in_M leq_in_M
  {
    fix u
    assume "u \<in> domain(\<pi>) \<times> P" "u \<in> M"
    with in_M \<open>?new_form \<in> formula\<close> \<open>?\<psi>\<in>formula\<close> \<open>nenv \<in> _\<close>
    have Eq1: "sats(M,?\<psi>,[u] @ ?Pl1 @ [\<pi>] @ nenv) \<longleftrightarrow> 
                        (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =\<langle>\<theta>,p\<rangle> \<and> 
                          sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<pi>] @ nenv))"
      by (auto simp add: transitivity)
    have Eq3: "\<theta>\<in>M \<Longrightarrow> p\<in>P \<Longrightarrow>
       sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<pi>]@nenv) \<longleftrightarrow>
          (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> sats(M[F], ?\<chi>, map(val(F), [\<theta>] @ nenv@[\<pi>])))" 
      for \<theta> p 
    proof -
      fix p \<theta> 
      assume "\<theta> \<in> M" "p\<in>P"
      then 
      have "p\<in>M" using P_in_M by (simp add: transitivity)
      note in_M' = in_M \<open>\<theta> \<in> M\<close> \<open>p\<in>M\<close> \<open>u \<in> domain(\<pi>) \<times> P\<close> \<open>u \<in> M\<close> \<open>nenv\<in>_\<close>
      then 
      have "[\<theta>,u] \<in> list(M)" by simp
      let ?env="?Pl1@[p,\<theta>] @ nenv @ [\<pi>,u]"
      let ?new_env=" [\<theta>,p,u,P,leq,one,\<pi>] @ nenv"
      let ?\<psi>="Exists(Exists(And(pair_fm(0,1,2),?new_form)))"
      have "[\<theta>, p, u, \<pi>, leq, one, \<pi>] \<in> list(M)" 
        using in_M' by simp
      have "?\<chi> \<in> formula" "forces(?\<chi>)\<in> formula"  
        using phi by simp_all
      from in_M' 
      have "?Pl1 \<in> list(M)" by simp
      from in_M' have "?env \<in> list(M)" by simp
      have Eq1': "?new_env \<in> list(M)" using in_M'  by simp 
      then 
      have "sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<pi>] @ nenv) \<longleftrightarrow> sats(M,?new_form,?new_env)"
        by simp
      from in_M' \<open>env \<in> _\<close> Eq1' \<open>length(nenv) = length(env)\<close> 
        \<open>arity(forces(?\<chi>)) \<le> 7 #+ length(env)\<close> \<open>forces(?\<chi>)\<in> formula\<close>
        \<open>[\<theta>, p, u, \<pi>, leq, one, \<pi>] \<in> list(M)\<close> 
      have "... \<longleftrightarrow> sats(M,forces(?\<chi>),?env)"
        using sepren_action[of "forces(?\<chi>)"  "nenv",OF _ _ \<open>nenv\<in>list(M)\<close>] 
        by simp
      also from in_M'
      have "... \<longleftrightarrow> sats(M,forces(?\<chi>), ([P, leq, one,p,\<theta>]@nenv@ [\<pi>])@[u])" 
        using app_assoc by simp
      also 
      from in_M' \<open>env\<in>_\<close>  phi \<open>length(nenv) = length(env)\<close>
        \<open>arity(forces(?\<chi>)) \<le> 6 #+ length(env)\<close> \<open>forces(?\<chi>)\<in>formula\<close>
      have "... \<longleftrightarrow> sats(M,forces(?\<chi>), [P, leq, one,p,\<theta>]@ nenv @ [\<pi>])"        
        by (rule_tac arity_sats_iff,auto)
      also 
      from \<open>arity(forces(?\<chi>)) \<le> 6 #+ length(env)\<close> \<open>forces(?\<chi>)\<in>formula\<close> in_M' phi 
      have " ... \<longleftrightarrow> (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> 
                           sats(M[F], ?\<chi>, map(val(F), [\<theta>] @ nenv @ [\<pi>])))"
        using  definition_of_forces 
      proof (intro iffI)
        assume a1: "sats(M, forces(?\<chi>), [P, leq, one,p,\<theta>] @ nenv @ [\<pi>])"
        note definition_of_forces \<open>arity(\<phi>)\<le> 1#+_\<close>
        with \<open>nenv\<in>_\<close> \<open>arity(?\<chi>) \<le> length([\<theta>] @ nenv @ [\<pi>])\<close>
        have "p \<in> P \<Longrightarrow> ?\<chi>\<in>formula \<Longrightarrow> [\<theta>,\<pi>] \<in> list(M) \<Longrightarrow>
                  sats(M, forces(?\<chi>), [P, leq, one, p] @ [\<theta>]@ nenv@[\<pi>]) \<Longrightarrow> 
              \<forall>G. M_generic(G) \<and> p \<in> G \<longrightarrow> sats(M[G], ?\<chi>, map(val(G), [\<theta>] @ nenv @[\<pi>]))" by auto
        then
        show "\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> 
                  sats(M[F], ?\<chi>, map(val(F), [\<theta>] @ nenv @ [\<pi>]))"
          using  \<open>?\<chi>\<in>formula\<close> \<open>p\<in>P\<close> a1 \<open>\<theta>\<in>M\<close> \<open>\<pi>\<in>M\<close> by simp
      next
        assume "\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> 
                   sats(M[F], ?\<chi>, map(val(F), [\<theta>] @ nenv @[\<pi>]))"
        with definition_of_forces [THEN iffD2] \<open>arity(?\<chi>) \<le> length([\<theta>] @ nenv @ [\<pi>])\<close>
        show "sats(M, forces(?\<chi>), [P, leq, one,p,\<theta>] @ nenv @ [\<pi>])"
          using  \<open>?\<chi>\<in>formula\<close> \<open>p\<in>P\<close> in_M' by auto
      qed
      finally 
      show "sats(M,?new_form,[\<theta>,p,u]@?Pl1@[\<pi>]@nenv) \<longleftrightarrow> (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> 
                           sats(M[F], ?\<chi>, map(val(F), [\<theta>] @ nenv @ [\<pi>])))" 
        by simp
    qed
    with Eq1 
    have "sats(M,?\<psi>,[u] @ ?Pl1 @ [\<pi>] @ nenv) \<longleftrightarrow> 
         (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =\<langle>\<theta>,p\<rangle> \<and> 
          (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> sats(M[F], ?\<chi>, map(val(F), [\<theta>] @ nenv @ [\<pi>]))))"
      by auto 
  }
  then 
  have Equivalence: "u\<in> domain(\<pi>) \<times> P \<Longrightarrow> u \<in> M \<Longrightarrow> 
       sats(M,?\<psi>,[u] @ ?Pl1 @ [\<pi>] @ nenv) \<longleftrightarrow> 
         (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =\<langle>\<theta>,p\<rangle> \<and> 
          (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> sats(M[F], ?\<chi>,  map(val(F), [\<theta>] @ nenv @[\<pi>]))))" 
    for u 
    by simp
  moreover from \<open>env = _\<close> \<open>\<pi>\<in>M\<close> \<open>nenv\<in>list(M)\<close>
  have map_nenv:"map(val(G), nenv@[\<pi>]) = env @ [val(G,\<pi>)]"
    using map_app_distrib append1_eq_iff by auto
  ultimately
  have aux:"(\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =\<langle>\<theta>,p\<rangle> \<and> (p\<in>G \<longrightarrow> sats(M[G],?\<chi>,[val(G,\<theta>)] @ env @ [val(G,\<pi>)])))" 
   (is "(\<exists>\<theta>\<in>M. \<exists>p\<in>P. _ ( _ \<longrightarrow> sats(_,_,?vals(\<theta>))))")
   if "u \<in> domain(\<pi>) \<times> P" "u \<in> M"  "sats(M,?\<psi>,[u]@ ?Pl1 @[\<pi>] @ nenv)" for u
    using Equivalence[THEN iffD1, OF that] generic by force
  moreover 
  have "\<theta>\<in>M \<Longrightarrow> val(G,\<theta>)\<in>M[G]" for \<theta>
    using GenExt_def by auto
  moreover
  have "\<theta>\<in> M \<Longrightarrow> [val(G, \<theta>)] @ env @ [val(G, \<pi>)] \<in> list(M[G])" for \<theta>
  proof -
    from \<open>\<pi>\<in>M\<close>
    have "val(G,\<pi>)\<in> M[G]" using GenExtI by simp
    moreover
    assume "\<theta> \<in> M"
    moreover
    note \<open>env \<in> list(M[G])\<close>
    ultimately
    show ?thesis 
      using GenExtI by simp
  qed
  ultimately 
  have "(\<exists>\<theta>\<in>M. \<exists>p\<in>P. u=\<langle>\<theta>,p\<rangle> \<and> (p\<in>G \<longrightarrow> val(G,\<theta>)\<in>nth(1 #+ length(env),[val(G, \<theta>)] @ env @ [val(G, \<pi>)]) 
        \<and> sats(M[G], \<phi>, ?vals(\<theta>))))"
    if "u \<in> domain(\<pi>) \<times> P" "u \<in> M"  "sats(M,?\<psi>,[u] @ ?Pl1 @[\<pi>] @ nenv)" for u
    using aux[OF that] by simp
  moreover from \<open>env \<in> _\<close> \<open>\<pi>\<in>M\<close>
  have nth:"nth(1 #+ length(env),[val(G, \<theta>)] @ env @ [val(G, \<pi>)]) = val(G,\<pi>)" 
    if "\<theta>\<in>M" for \<theta>
    using nth_concat[of "val(G,\<theta>)" "val(G,\<pi>)" "M[G]"] using that GenExtI by simp
  ultimately
  have "(\<exists>\<theta>\<in>M. \<exists>p\<in>P. u=\<langle>\<theta>,p\<rangle> \<and> (p\<in>G \<longrightarrow> val(G,\<theta>)\<in>val(G,\<pi>) \<and> sats(M[G], \<phi>, ?vals(\<theta>))))"
    if "u \<in> domain(\<pi>) \<times> P" "u \<in> M"  "sats(M,?\<psi>,[u] @ ?Pl1 @[\<pi>] @ nenv)" for u
    using that \<open>\<pi>\<in>M\<close> \<open>env \<in> _\<close> by simp
  with \<open>domain(\<pi>)\<times>P\<in>M\<close>
  have "\<forall>u\<in>domain(\<pi>)\<times>P . sats(M,?\<psi>,[u] @ ?Pl1 @[\<pi>] @ nenv) \<longrightarrow> (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =\<langle>\<theta>,p\<rangle> \<and>
        (p \<in> G \<longrightarrow> val(G, \<theta>)\<in>val(G, \<pi>) \<and> sats(M[G], \<phi>, ?vals(\<theta>))))"
    by (simp add:transitivity)
  then 
  have "{u\<in>domain(\<pi>)\<times>P . sats(M,?\<psi>,[u] @ ?Pl1 @[\<pi>] @ nenv) } \<subseteq>
     {u\<in>domain(\<pi>)\<times>P . \<exists>\<theta>\<in>M. \<exists>p\<in>P. u =\<langle>\<theta>,p\<rangle> \<and> 
       (p \<in> G \<longrightarrow> val(G, \<theta>)\<in>val(G, \<pi>) \<and> sats(M[G], \<phi>, ?vals(\<theta>)))}"
    (is "?n\<subseteq>?m") 
    by auto
  with val_mono 
  have first_incl: "val(G,?n) \<subseteq> val(G,?m)" 
    by simp
  note  \<open>val(G,\<pi>) = c\<close> (* from the assumptions *)
  with \<open>?\<psi>\<in>formula\<close>  \<open>arity(?\<psi>) \<le> _\<close> in_M \<open>nenv \<in> _\<close> \<open>env \<in> _\<close> \<open>length(nenv) = _\<close> 
  have "?n\<in>M" 
    using separation_ax leI separation_iff by auto 
  from generic 
  have "filter(G)" "G\<subseteq>P" 
    unfolding M_generic_def filter_def by simp_all
  from \<open>val(G,\<pi>) = c\<close> 
  have "val(G,?m) =
               {val(G,t) .. t\<in>domain(\<pi>) , \<exists>q\<in>P .  
                    (\<exists>\<theta>\<in>M. \<exists>p\<in>P. <t,q> = \<langle>\<theta>, p\<rangle> \<and> 
            (p \<in> G \<longrightarrow> val(G, \<theta>) \<in> c \<and> sats(M[G], \<phi>, [val(G, \<theta>)] @ env @ [c])) \<and> q \<in> G)}"
    using val_of_name by auto
  also 
  have "... =  {val(G,t) .. t\<in>domain(\<pi>) , \<exists>q\<in>P. 
                   val(G, t) \<in> c \<and> sats(M[G], \<phi>, [val(G, t)] @ env @ [c]) \<and> q \<in> G}" 
  proof -

    have "t\<in>M \<Longrightarrow>
      (\<exists>q\<in>P. (\<exists>\<theta>\<in>M. \<exists>p\<in>P. <t,q> = \<langle>\<theta>, p\<rangle> \<and> 
              (p \<in> G \<longrightarrow> val(G, \<theta>) \<in> c \<and> sats(M[G], \<phi>, [val(G, \<theta>)] @ env @ [c])) \<and> q \<in> G)) 
      \<longleftrightarrow> 
      (\<exists>q\<in>P. val(G, t) \<in> c \<and> sats(M[G], \<phi>, [val(G, t)] @ env @ [c]) \<and> q \<in> G)" for t
      by auto
    then show ?thesis using \<open>domain(\<pi>)\<in>M\<close> by (auto simp add:transitivity)
  qed
  also 
  have "... =  {x .. x\<in>c , \<exists>q\<in>P. x \<in> c \<and> sats(M[G], \<phi>, [x] @ env @ [c]) \<and> q \<in> G}"
  proof

    show "... \<subseteq> {x .. x\<in>c , \<exists>q\<in>P. x \<in> c \<and> sats(M[G], \<phi>, [x] @ env @ [c]) \<and> q \<in> G}"
      by auto
  next 
    (* Now we show the other inclusion:
      {x .. x\<in>c , \<exists>q\<in>P. x \<in> c \<and> sats(M[G], \<phi>, [x, w, c]) \<and> q \<in> G}
      \<subseteq>
      {val(G,t)..t\<in>domain(\<pi>),\<exists>q\<in>P.val(G,t)\<in>c\<and>sats(M[G],\<phi>,[val(G,t),w])\<and>q\<in>G}
    *)
    {
      fix x
      assume "x\<in>{x .. x\<in>c , \<exists>q\<in>P. x \<in> c \<and> sats(M[G], \<phi>, [x] @ env @ [c]) \<and> q \<in> G}"
      then 
      have "\<exists>q\<in>P. x \<in> c \<and> sats(M[G], \<phi>, [x] @ env @ [c]) \<and> q \<in> G"
        by simp
      with \<open>val(G,\<pi>) = c\<close>  
      have "\<exists>q\<in>P. \<exists>t\<in>domain(\<pi>). val(G,t) =x \<and> sats(M[G], \<phi>, [val(G,t)] @ env @ [c]) \<and> q \<in> G" 
        using Sep_and_Replace elem_of_val by auto
    }
    then 
    show " {x .. x\<in>c , \<exists>q\<in>P. x \<in> c \<and> sats(M[G], \<phi>, [x] @ env @ [c]) \<and> q \<in> G} \<subseteq> ..."
      using SepReplace_iff by force
  qed
  also 
  have " ... = {x\<in>c. sats(M[G], \<phi>, [x] @ env @ [c])}"
    using \<open>G\<subseteq>P\<close> G_nonempty by force
  finally 
  have val_m: "val(G,?m) = {x\<in>c. sats(M[G], \<phi>, [x] @ env @ [c])}" by simp
  have "val(G,?m) \<subseteq> val(G,?n)" 
  proof
    fix x
    assume "x \<in> val(G,?m)"
    with val_m 
    have Eq4: "x \<in> {x\<in>c. sats(M[G], \<phi>, [x] @ env @ [c] )}" by simp
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
    with \<open>\<pi>\<in>M\<close> \<open>nenv \<in> _\<close> \<open>env = _\<close>
    have "[val(G,\<theta>), val(G,\<pi>)] @ env \<in>list(M[G])" 
      using GenExt_def by auto
    with  Eq4 \<open>val(G,\<theta>)=x\<close> \<open>val(G,\<pi>) = c\<close> \<open>x \<in> val(G,\<pi>)\<close> nth \<open>\<theta>\<in>M\<close>
    have Eq5: "sats(M[G], And(Member(0,1 #+ length(env)),\<phi>), [val(G,\<theta>)] @ env @[val(G,\<pi>)] )" 
      by auto
        (* Recall ?\<chi> = And(Member(0,1 #+ length(env)),\<phi>) *)
    with \<open>\<theta>\<in>M\<close> \<open>\<pi>\<in>M\<close>  Eq5 \<open>M_generic(G)\<close> \<open>\<phi>\<in>formula\<close> \<open>nenv \<in> _ \<close> \<open>env = _ \<close> map_nenv 
      \<open>arity(?\<chi>) \<le> length([\<theta>] @ nenv @ [\<pi>])\<close>
    have "(\<exists>r\<in>G. sats(M,forces(?\<chi>), [P,leq,one,r,\<theta>] @ nenv @[\<pi>]))"
      using truth_lemma  by auto
    then obtain r where      (* I can't "obtain" this directly *)
      "r\<in>G" "sats(M,forces(?\<chi>), [P,leq,one,r,\<theta>] @ nenv @ [\<pi>])" by auto
    with \<open>filter(G)\<close> and \<open>q\<in>G\<close> obtain p where
      "p\<in>G" "<p,q>\<in>leq" "<p,r>\<in>leq" 
      unfolding filter_def compat_in_def by force
    with \<open>r\<in>G\<close>  \<open>q\<in>G\<close> \<open>G\<subseteq>P\<close> 
    have "p\<in>P" "r\<in>P" "q\<in>P" "p\<in>M"
      using  P_in_M  by (auto simp add:transitivity)
    with \<open>\<phi>\<in>formula\<close> \<open>\<theta>\<in>M\<close> \<open>\<pi>\<in>M\<close>  \<open><p,r>\<in>leq\<close> \<open>nenv \<in> _\<close> \<open>arity(?\<chi>) \<le> length([\<theta>] @ nenv @ [\<pi>])\<close>
      \<open>sats(M,forces(?\<chi>), [P,leq,one,r,\<theta>] @ nenv @ [\<pi>])\<close> \<open>env\<in>_\<close>
    have "sats(M,forces(?\<chi>), [P,leq,one,p,\<theta>] @ nenv @ [\<pi>])"
      using strengthening_lemma by simp
    with \<open>p\<in>P\<close> \<open>\<phi>\<in>formula\<close> \<open>\<theta>\<in>M\<close> \<open>\<pi>\<in>M\<close> \<open>nenv \<in> _\<close> \<open>arity(?\<chi>) \<le> length([\<theta>] @ nenv @ [\<pi>])\<close>
    have "\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> 
                 sats(M[F], ?\<chi>,  map(val(F), [\<theta>] @ nenv @[\<pi>]))"
      using definition_of_forces by simp
    with \<open>p\<in>P\<close> \<open>\<theta>\<in>M\<close>  
    have Eq6: "\<exists>\<theta>'\<in>M. \<exists>p'\<in>P.  \<langle>\<theta>,p\<rangle> = <\<theta>',p'> \<and> (\<forall>F. M_generic(F) \<and> p' \<in> F \<longrightarrow> 
                 sats(M[F], ?\<chi>,  map(val(F), [\<theta>'] @ nenv @ [\<pi>])))" by auto
    from \<open>\<pi>\<in>M\<close> \<open>\<langle>\<theta>,q\<rangle>\<in>\<pi>\<close> 
    have "\<langle>\<theta>,q\<rangle> \<in> M" by (simp add:transitivity)
    from \<open>\<langle>\<theta>,q\<rangle>\<in>\<pi>\<close> \<open>\<theta>\<in>M\<close> \<open>p\<in>P\<close>  \<open>p\<in>M\<close> 
    have "\<langle>\<theta>,p\<rangle>\<in>M" "\<langle>\<theta>,p\<rangle>\<in>domain(\<pi>)\<times>P" 
      using pairM by auto
    with \<open>\<theta>\<in>M\<close> Eq6 \<open>p\<in>P\<close>
    have "sats(M,?\<psi>,[\<langle>\<theta>,p\<rangle>] @ ?Pl1 @ [\<pi>] @ nenv)"
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
  have "val(G,?n) = {x\<in>c. sats(M[G], \<phi>, [x] @ env @ [c])}" by auto
  also 
  have " ... = {x\<in>c. sats(M[G], \<phi>, [x] @ env)}" 
  proof -
    {
      fix x
      assume "x\<in>c"
      moreover from assms 
      have "c\<in>M[G]"
        unfolding GenExt_def by auto
      moreover from this and \<open>x\<in>c\<close> 
      have "x\<in>M[G]"
        by (simp add:Transset_MG Transset_intf)
      ultimately 
      have "sats(M[G], \<phi>, ([x] @ env) @[c]) \<longleftrightarrow> sats(M[G], \<phi>, [x] @ env)" 
        using phi \<open>env \<in> _\<close> by (rule_tac arity_sats_iff, simp_all)   (* Enhance this *)
    }
    then show ?thesis by auto
  qed      
  finally 
  show "{x\<in>c. sats(M[G], \<phi>, [x] @ env)}\<in> M[G]" 
    using \<open>?n\<in>M\<close> GenExt_def by force
qed

theorem separation_in_MG:
  assumes 
    "\<phi>\<in>formula" and "arity(\<phi>) \<le> 1 #+ length(env)" and "env\<in>list(M[G])"
  shows  
    "separation(##M[G],\<lambda>x. sats(M[G],\<phi>,[x] @ env))"
proof -
  { 
    fix c
    assume "c\<in>M[G]" 
    moreover from \<open>env \<in> _\<close>
    obtain nenv where  "nenv\<in>list(M)" 
      "env = map(val(G),nenv)" "length(env) = length(nenv)"
      using GenExt_def map_val[of env] by auto
    moreover note \<open>\<phi> \<in> _\<close> \<open>arity(\<phi>) \<le> _\<close> \<open>env \<in> _\<close>
    ultimately
    have Eq1: "{x\<in>c. sats(M[G], \<phi>, [x] @ env)} \<in> M[G]"
      using Collect_sats_in_MG  by auto
  }
  then 
  show ?thesis 
    using separation_iff rev_bexI unfolding is_Collect_def by force
qed

end (* context: sep_rename *)

end