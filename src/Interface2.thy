theory Interface2 imports Relative_no_repl  begin

lemma Transset_intf :
  "Transset(M) \<Longrightarrow>  y\<in>x \<Longrightarrow> x \<in> M \<Longrightarrow> y \<in> M"
  by (simp add: Transset_def,auto)

definition 
  infinity_ax :: "(i \<Rightarrow> o) \<Rightarrow> o" where
  "infinity_ax(M) ==  
      (\<exists>I[M]. (\<exists>z[M]. empty(M,z) \<and> z\<in>I) \<and>  (\<forall>y[M]. y\<in>I \<longrightarrow> (\<exists>sy[M]. successor(M,y,sy) \<and> sy\<in>I)))" 
    
lemma empty_intf :
  "infinity_ax(M) \<Longrightarrow>
  (\<exists>z[M]. empty(M,z))"
  by (auto simp add: empty_def infinity_ax_def)

lemma zero_in_M:  "\<lbrakk> infinity_ax(##M) ; Transset(M) \<rbrakk> \<Longrightarrow> 0 \<in> M"
proof -
  assume inf: "infinity_ax(##M)" and
         trans: "Transset(M)"
  from inf have
        "(\<exists>z[##M]. empty(##M,z))"
    by (rule empty_intf)
  then obtain z where
        zm: "empty(##M,z)"  "z\<in>M"
    by auto
  with trans have "z=0"
    by (simp  add: empty_def, blast intro: Transset_intf )
  with zm show ?thesis 
      by simp
qed

  
  
end