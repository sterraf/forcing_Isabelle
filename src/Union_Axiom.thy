theory Union_Axiom 
  imports Forcing_data Names  
begin

context forcing_data
begin

  (*
to  prove  that  whenever  a \<in> M[G),  there  is  b \<in>  M[G)  such  that  \<union> a  \<subseteq>  b. 
 Fix \<tau> \<in> M^P  such  that  a  = val(G,\<tau>),  let  \<pi> =  \<union> dom(\<tau>),  and  let  b = val(G,\<pi>). 

Note  that  \<tau>  is  a  set  of  pairs  of  the  form  (a,p),  and  dom(\<tau>)  is  just  the 
set  of  all  these  a's.  Then,  our  Definition  IV.2.5  (of  "name")  implies  that  the 
union  of  any  family  of  names  is  also  a  name,  so  \<pi> is a P-name,  and \<pi> \<in> M  by 
absoluteness  of \<union>,  so  b \<in>  M[G]. 

If  c \<in> a =  val(G,\<tau>),  then  c = val(G,\<sigma>) for  some  \<sigma> \<in> dom(\<tau>).  Then  \<sigma> \<subseteq> \<pi>,  
so,  applying Definition  IV.2.7,  c = val(G,\<sigma>) \<subseteq> val(G,\<pi>) = b.  Thus,  a \<subseteq> \<union> b. 

Alternatively: \<pi>  ==  {(\<theta>,p)  : \<exists>(\<sigma>, q) \<in> \<tau> . \<exists> r. [(\<theta>,r) \<in> \<sigma> \<and> p \<le> r \<and> p  \<le> q}
And prove \<union>a=val(G,\<pi>)
definition pi_Union :: "i \<Rightarrow> i" where
  "pi_Union(\<tau>) == {<\<theta>,p> \<in> M \<times> P . \<exists> <\<sigma>,q> \<in> \<tau> . (\<exists> r \<in> P. <\<theta>,r> \<in> \<sigma> \<and> p \<le> r \<and> p  \<le> q) }"
*)
    
lemma Union_aux : 
  assumes "a \<in> M[G]"
  shows "\<exists> b \<in> M[G] . \<Union> a \<subseteq> b"
proof - 
    from \<open>a \<in> M[G]\<close> obtain \<tau> where
    "\<tau> \<in> M" "a = val(G,\<tau>)" "domain(\<tau>) \<in> M" and "\<Union> (domain(\<tau>)) \<in> M" (is "?\<pi> \<in> M")
    using GenExtD  domain_closed Union_closed by force
  then have "val(G,?\<pi>) \<in> M[G]" using GenExtI by simp
  {
    fix x
    assume "x \<in> val(G,\<tau>)"
    then obtain \<theta> p where
      "p \<in> G" "<\<theta>,p> \<in> \<tau>" "val(G,\<theta>) = x"
      using elem_of_val_pair by blast
    then have "\<theta> \<in> domain(\<tau>)" "\<theta> \<subseteq> ?\<pi>" using Union_upper by auto
    then have "val(G,\<theta>) \<subseteq> val(G,?\<pi>)" using val_mono by simp
    with \<open>val(G,\<theta>)=x\<close> have "x \<subseteq> val(G,?\<pi>)" by simp
  }
  with \<open>a=val(G,\<tau>)\<close> have "\<Union> a \<subseteq> val(G,?\<pi>)" (is "_ \<subseteq> ?b") using Union_subset_iff by auto
  with \<open>val(G,?\<pi>) \<in> M[G]\<close> show ?thesis by auto
qed
        
lemma union_in_MG : "M_generic(G) \<Longrightarrow> Union_ax(##M[G])"
  sorry

end
end