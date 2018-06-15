theory Separation_generic imports   Forces_locale begin

context forcing_thms begin  

theorem separation_in_genext:
 (* assumes "\<phi>\<in>formula"  and "arity(\<phi>) = 1 \<or> arity(\<phi>)=2" 
  shows  "sats(M[G],separation_ax_fm(\<phi>),[])" *)
  shows
  "\<phi>\<in>formula \<Longrightarrow> arity(\<phi>) = 1 \<or> arity(\<phi>)=2 \<Longrightarrow> sats(M[G],separation_ax_fm(\<phi>),[])"
proof -
  assume 
      "arity(\<phi>) = 1 \<or> arity(\<phi>)=2" (is "?P \<or> ?Q")
  then consider (1) ?P | (2) ?Q ..
  then show ?thesis
  proof cases
    case 1
    then show ?thesis sorry
  next
    case 2
    fix c w
    assume
         asm: "c\<in>M[G]" "w\<in>M[G]" "\<phi>\<in>formula"
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
        by (auto simp add: Transset_intf trans_M)
      with Eq1 and Eq2 have
              "{u\<in>domain(\<pi>)*P . sats(M,?\<psi>,[u] @ ?env @ [\<pi>,\<sigma>])} = 
               {u\<in>domain(\<pi>)*P . \<exists>\<theta>\<in>M. \<exists>p\<in>M. u =<\<theta>,p> \<and> sats(M,forces(?\<chi>),[\<theta>,p,u]@?env@[\<pi>,\<sigma>])}"
        by (auto simp add: Transset_intf trans_M)
(*      also have
              " ... =  {u\<in>domain(\<pi>)*P . \<exists>\<theta> p. u =<\<theta>,p> \<and> sats(M,forces(?\<chi>),[\<theta>,p,u,\<pi>,\<sigma>])}"
        using Eq2 Pair_def apply (auto simp add:  Transset_intf trans_M) *)
      also have
              " ... =  
              {u\<in>domain(\<pi>)*P . \<exists>\<theta> p. u =<\<theta>,p> \<and> sats(M,forces(?\<chi>),?env@[\<theta>,p,u,\<pi>,\<sigma>])}"
          
  find_theorems "sats(M,?x,?y)"              
        sorry
    then show ?thesis sorry
  qed
  
oops
end  
end