theory Two_Separations imports FOL begin

txt\<open>Proof that 2-parameter Separation without 'z' implies 1-parameter 
    Separation using 'z'\<close>
  
notepad begin
  fix E::"'a\<Rightarrow>'a\<Rightarrow>o" and Q::"'a\<Rightarrow>'a\<Rightarrow>'a\<Rightarrow>o"
  assume
      1: "\<forall>u1 u2 z. \<exists>y. \<forall>x. E(x,y) \<longleftrightarrow> E(x,z) \<and> P(x,u1,u2)" for P::"'a\<Rightarrow>'a\<Rightarrow>'a\<Rightarrow>o"
  have
      "\<forall>v z. \<exists>y. \<forall>x. E(x,y) \<longleftrightarrow> E(x,z) \<and> Q(x,z,v)" 
  proof (intro allI)
    show 
      "\<exists>y. \<forall>x. E(x,y) \<longleftrightarrow> E(x,z) \<and> Q(x,z,v)" for v and z
    proof -
      from 1 have
      "\<exists>y. \<forall>x. E(x,y) \<longleftrightarrow> E(x,z) \<and> Q(x,z,v)" by simp
      then obtain y where
      "\<forall>x. E(x,y) \<longleftrightarrow> E(x,z) \<and> Q(x,z,v)" by auto
      then show ?thesis by auto
    qed
  qed
end
  
end 