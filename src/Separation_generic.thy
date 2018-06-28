theory Separation_generic imports   Forces_locale begin

context forcing_thms begin  

lemma val_mono : "x\<subseteq>y \<Longrightarrow> val(G,x) \<subseteq> val(G,y)"
  sorry

definition 
  perm_sep_forces :: "i" where
  "perm_sep_forces == {\<langle>0, 4\<rangle>, \<langle>1, 3\<rangle>, \<langle>2, 7\<rangle>, \<langle>3, 0\<rangle>, \<langle>4, 1\<rangle>, \<langle>5, 2\<rangle>, \<langle>6, 5\<rangle>, \<langle>7, 6\<rangle>}"

lemma perm_sep_bij: "perm_sep_forces \<in> bij(8,8)" 
  sorry
    
lemma perm_sep_env : "perm_list(perm_sep_forces,[p,q,r,s,t,u,v,w]) = [t,s,w,p,q,r,u,v]"
  sorry
  
lemmas transitivity = Transset_intf trans_M

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
        and   ?env="[P,leq,uno]"
      let
              ?\<psi>="Exists(Exists(And(pair_fm(0,1,2),forces(?\<chi>))))"
      from asm P_in_M leq_in_M uno_in_P have
         Eq3: "?\<chi>\<in>formula" "?\<psi>\<in>formula" "\<phi>\<in>formula" "?env\<in>list(M)"
        by (auto simp add: transitivity)
      have
        "\<forall>u\<in>domain(\<pi>)*P . sats(M,?\<psi>,[u] @ ?env @ [\<pi>,\<sigma>])  \<longrightarrow>
          (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
                            p \<in> G \<longrightarrow> 
                           val(G, \<theta>)\<in>c \<and> sats(M[G], \<phi>, [val(G, \<theta>), c, w ]))"
      proof (intro ballI)
        fix u
        assume 
         Eq4: "u \<in> domain(\<pi>) \<times> P"
        with Eq1 and Eq2 and Eq3 have
              "sats(M,?\<psi>,[u] @ ?env @ [\<pi>,\<sigma>]) \<longleftrightarrow> 
                        (\<exists>\<theta>\<in>M. \<exists>p\<in>M. u =<\<theta>,p> \<and> 
                          sats(M,forces(?\<chi>),[\<theta>,p,u]@?env@[\<pi>,\<sigma>]))"
          by (auto simp add: transitivity)
        also have
              " ... \<longleftrightarrow> (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
                          sats(M,rename(forces(?\<chi>))`length(?env@[p,\<theta>,\<pi>,\<sigma>,u])`converse(perm_sep_forces),[\<theta>,p,u]@?env@[\<pi>,\<sigma>]))"
          (* using Eq4 P_in_M by (auto simp add:transitivity)*) sorry
         also have
              " ... \<longleftrightarrow> (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
                          sats(M,rename(forces(?\<chi>))`length(?env@[p,\<theta>,\<pi>,\<sigma>,u])`converse(perm_sep_forces),
                          perm_list(perm_sep_forces,?env@[p,\<theta>,\<pi>,\<sigma>,u])))"
           by (simp add: perm_sep_env)
         also have
              " ... \<longleftrightarrow> (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
                          sats(M,forces(?\<chi>),?env@[p,\<theta>,\<pi>,\<sigma>,u]))"
         proof 
           from Eq2 trans_M have
         Eq5: "u \<in> M"
             by (auto simp add:transD)
               
           have
              "\<And>\<theta> p u. \<theta>\<in>M \<Longrightarrow> p\<in>P \<Longrightarrow> u \<in> M \<Longrightarrow> sats(M,rename(forces(?\<chi>))`length(?env@[p,\<theta>,\<pi>,\<sigma>,u])`converse(perm_sep_forces),
                          perm_list(perm_sep_forces,?env@[p,\<theta>,\<pi>,\<sigma>,u]))
                \<longleftrightarrow>
                     sats(M,forces(?\<chi>),?env@[p,\<theta>,\<pi>,\<sigma>,u])"
             using asm P_in_M leq_in_M uno_in_P Eq1  2 transD trans_M
             apply(rule_tac ren_Sat_leq [symmetric])
                apply(auto simp add: perm_sep_bij arity_forces nat_union_abs1)
               
               
        also have
              " ... \<longleftrightarrow> (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
                          (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> 
                            sats(M[F], ?\<chi>, [val(F, \<theta>), val(F, \<pi>), val(F, \<sigma>)])))"
          using Eq1 Eq3 Eq4 and definition_of_forces by simp
        also have
              " ... \<longrightarrow> (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
                           M_generic(G) \<and> p \<in> G \<longrightarrow> 
                            sats(M[G], ?\<chi>, [val(G, \<theta>), c, w ]))"
          using Eq1 by auto
        also have
              " ... \<longrightarrow> (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
                           M_generic(G) \<and> p \<in> G \<longrightarrow> 
                           val(G, \<theta>)\<in>c \<and> sats(M[G], \<phi>, [val(G, \<theta>), c, w ]))"
        proof (intro impI, elim bexE)
          fix \<theta> p
          assume
          Eq5:"\<theta> \<in> M" "p \<in> P"
              "u = \<langle>\<theta>, p\<rangle> \<and> M_generic(G) \<and> p \<in> G \<longrightarrow>
                sats(M[G], And(Member(0, 1), \<phi>), [val(G, \<theta>), c, w])"
          then have
              "val(G, \<theta>) \<in> M[G]"
              unfolding GenExt_def by(auto)
          with asm and Eq5 have
              "u = \<langle>\<theta>, p\<rangle> \<and> M_generic(G) \<and> p \<in> G \<longrightarrow>
                        val(G, \<theta>) \<in> c \<and> sats(M[G], \<phi>, [val(G, \<theta>), c, w])"
             by simp
          with Eq5 show 
              "\<exists>\<theta>\<in>M. \<exists>p\<in>P. u = \<langle>\<theta>, p\<rangle> \<and> M_generic(G) \<and> p \<in> G \<longrightarrow>
                        val(G, \<theta>) \<in> c \<and> sats(M[G], \<phi>, [val(G, \<theta>), c, w])" 
            by auto
        qed
        finally show
         Eq6: "sats(M,?\<psi>,[u] @ ?env @ [\<pi>,\<sigma>]) \<longrightarrow>
               (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
                           p \<in> G \<longrightarrow> 
                           val(G, \<theta>)\<in>c \<and> sats(M[G], \<phi>, [val(G, \<theta>), c, w ]))" 
          using asm by simp
      qed
      then have
              "{u\<in>domain(\<pi>)*P . sats(M,?\<psi>,[u] @ ?env @ [\<pi>,\<sigma>]) } \<subseteq>
               {u\<in>domain(\<pi>)*P . \<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> 
                            p \<in> G \<longrightarrow> 
                           val(G, \<theta>)\<in>c \<and> sats(M[G], \<phi>, [val(G, \<theta>), c, w ])}"
                  (is "?n\<subseteq>?m") 
        by auto
      with val_mono have
         Eq7: "val(G,?n) \<subseteq> val(G,?m)"
        by simp
      assume 
              "?m \<in> M"
      with val_of_name and Eq7 have
              "val(G,?n) \<subseteq>
               {val(G,t) .. t\<in>domain(\<pi>) , \<exists>q\<in>P .  
                    (\<exists>\<theta>\<in>M. \<exists>p\<in>P. <t,p> = \<langle>\<theta>, p\<rangle> \<and> p \<in> G \<longrightarrow> 
                      val(G, \<theta>) \<in> c \<and> sats(M[G], \<phi>, [val(G, \<theta>), c, w])) \<and> q \<in> G }"
        apply auto
              
    then show ?thesis sorry
  qed
  
  oops
    
lemma
  "And(Member(0, 1), \<phi>) \<in> formula \<Longrightarrow>
    P \<in> M \<and> leq \<in> M \<and> uno \<in> M \<Longrightarrow>
    u \<in> domain(\<pi>) \<times> P \<Longrightarrow>
  \<pi> \<in> M \<and> \<sigma> \<in> M \<Longrightarrow>
      (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and> sats(M, forces(And(Member(0, 1), \<phi>)), [P, leq, uno] @ [p, \<theta>, \<pi>, \<sigma>])) \<longleftrightarrow>
      (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =<\<theta>,p> \<and>            (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow>
                       sats(M[F], And(Member(0, 1), \<phi>), map(val(F), [\<theta>, \<pi>, \<sigma>]))))"
apply (insert definition_of_forces)
  apply (simp_all)
proof -
  fix F
  have
        "map(val(F), [\<theta>, \<pi>, \<sigma>]) =[val(F, \<theta>), val(F, \<pi>), val(F, \<sigma>)]"
    apply simp
    oops
end  
end