theory Forcing_Theorems imports Interface Names Forcing_Thms begin
   
(* Prototyping Forcing relation and theorems as a locale*)
locale forcing_thms = forcing_data + 
  assumes  arity_forces:     "\<phi>\<in>formula \<Longrightarrow> arity(forces(\<phi>)) = arity(\<phi>) #+ 4"

locale G_generic = forcing_thms + 
  fixes G :: "i"
  assumes generic : "M_generic(G)" 
begin

lemma zero_in_MG : 
  "0 \<in> M[G]" 
proof -
  from zero_in_M and elem_of_val have 
    "0 = val(G,0)" 
    by auto
  also from GenExtI and zero_in_M have 
    "... \<in> M[G]" 
  by simp
  finally show ?thesis .
qed 

lemma G_nonempty: "G\<noteq>0"
proof -
  have "P\<subseteq>P" ..
  with P_in_M P_dense \<open>P\<subseteq>P\<close> show
    "G \<noteq> 0"
    using generic unfolding M_generic_def by auto
qed

end    (* context: G_generic *)

end