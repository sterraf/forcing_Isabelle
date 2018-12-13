theory Foundation_Axiom
imports
  Names
begin

context forcing_data
begin
  
(* Same proof by Paulson for L *)  
lemma foundation_in_MG : "foundation_ax(##(M[G]))"
  unfolding foundation_ax_def
  by (rule rallI, cut_tac A=x in foundation, auto intro: Transset_M [OF Transset_MG])

(* Same theorem as above, declarative proof *)
lemma "foundation_ax(##(M[G]))"
proof -
  {   
    fix x 
    assume
      "x\<in>M[G]" "\<exists>y\<in>M[G] . y\<in>x"
    then obtain y where
      "y\<in>x" "\<forall>z\<in>y. z \<notin> x" 
      using foundation by blast
    moreover with \<open>x\<in>M[G]\<close> have
      "y\<in>M[G]"
      using Transset_M Transset_MG by simp
    ultimately have
      "\<exists>y\<in>M[G] . y \<in> x \<and> (\<forall>z\<in>M[G] . z \<notin> x \<or> z \<notin> y)"
      by auto
  }
  then show ?thesis
    unfolding foundation_ax_def by auto
qed
    
end
end