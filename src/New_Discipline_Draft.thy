theory New_Discipline_Draft
  imports
    "Discipline_Base"
    "Discipline_Function"
    "Least"
    "FrecR"
    Arities
    FrecR_Arities
begin

declare [[syntax_ambiguity_warning = false]]


text\<open>
Disciplina de Relativización.

En la teoría de conjuntos pura no podemos construir términos, sino
que cada concepto sobre conjuntos está caracterizado por una fórmula de
primer orden. Trabajar de esa manera es por demás impráctico, por lo que
en la teoría Isabelle/ZF se definen algunos términos básicos a partir de los
cuales se pueden construir otros. Los términos "viven" en el universo "i", que
está implementado como un tipo de datos de Isabelle. 


Cuando Paulson necesitó probar resultados relativos a una clase, lo hizo
del modo full relacional, es decir, sin términos, sino que expresando cada
concepto con una fórmula de primer orden. Consideremos como ejemplo los pares
ordenados, que en Isabelle/ZF están definidos mediante

definition Pair :: "[i, i] => i"
  where "Pair(a,b) == {{a,a}, {a,b}}"

y la versión relativa definida por Paulson:

definition
  pair :: "[i=>o,i,i,i] => o" where
    "pair(M,a,b,z) == \<exists>x[M]. upair(M,a,a,x) &
                     (\<exists>y[M]. upair(M,a,b,y) & upair(M,x,y,z))"

Cuando un concepto es *absoluto*, podemos utilizar equivalentemente
la versión definida originalmente en I/ZF y la full-relacional. Por lo
tanto los resultados dentro y fuera del modelo se obtienen de la misma manera.

Sin embargo cuando tenemos conceptos que no son equivalentes dentro y 
fuera del modelo, tenemos problemas para obtener resultados. 
Consideremos f :: i => i, y alguna propiedad P(f) :: o. Si queremos obtener
la versión de P relativa a M, en el diseño de Paulson deberíamos dar la
versión full-relacional relativa de f, is_f :: [i=>o,i,i] => o, y luego
traducir la prueba de P(f), en una P'(is_f). No queremos hacer ese trabajo.

La idea de la "disciplina de relativización consiste en obtener para cada
término f :: i => i, un término f_rel :: [i=>o,i] => i que se corresponda con
f, obteniendo el mismo resultado pero restringido a una clase M :: i=>o.

Para ello, partimos de un core de relativizaciones de conceptos básicos
donde para cada concepto 

   f = t(h)

tenemos su correspondiente is_f, tal como lo
hace Paulson, y luego obtenemos f_rel a partir de este último, probando
la equivalencia

     is_f(M,x,y) <--> y = f_rel(M,x)

y un lema de definición
     f_rel(M,x) = t_rel(h_rel)

Una vez que tenemos ese core de definiciones básicas, podemos obtener
nuevos términos relativos simplemente definiendo cada nuevo término
de la misma manera en que está definido el término original, aplicando
la versión relativa de cada uno de los subtérminos. 
De esta manera podemos copiar todas las pruebas hechas para los términos
originales, reemplazando aquellos que no sean absolutos por sus
versiones _rel.

Debemos además dar la versión full-relacional de cada término ya que
en nuestro diseño de forcing tenemos que utilizar fórmulas internalizadas
y ahí no escapamos del problema. 

La nueva disciplina obtiene la versión full-relacional a partir
de la definición f_rel.
A continuación un ejemplo.
\<close>



text\<open>Consideremos el término \<^term>\<open>cardinal\<close>.


Lo que debemos hacer es definir su versión relativa simplemente
"mapeando" la _función de relativización_ sobre todos los subtérminos
que no sean absolutos:
\<close>

relativize functional "cardinal" "cardinal_rel" external
relationalize "cardinal_rel" "is_cardinal"
synthesize "is_cardinal" from_definition assuming "nonempty"


abbreviation
  cardinal_r :: "[i,i\<Rightarrow>o] \<Rightarrow> i" (\<open>|_|\<^bsup>_\<^esup>\<close>) where
  "|x|\<^bsup>M\<^esup> \<equiv> cardinal_rel(M,x)"

abbreviation
  cardinal_r_set :: "[i,i]\<Rightarrow>i"  (\<open>|_|\<^bsup>_\<^esup>\<close>) where
  "|x|\<^bsup>M\<^esup> \<equiv> cardinal_rel(##M,x)"


text\<open>Probamos el lema closed\<close>

context M_trivial begin
rel_closed for "cardinal"
  using Least_closed'[of "\<lambda>i. M(i) \<and> i \<approx>\<^bsup>M\<^esup> A"]
  unfolding cardinal_rel_def
  by simp
end

(*lemma (in M_trivial) cardinal_rel_closed: "M(x) \<Longrightarrow> M(|x|\<^bsup>M\<^esup>)"
  using Least_closed'[of "\<lambda>i. M(i) \<and> i \<approx>\<^bsup>M\<^esup> x"]
  unfolding cardinal_rel_def
  by simp*)



manual_arity intermediate for "is_Int_fm"
  unfolding is_Int_fm_def
  using arity
  by simp

arity_theorem for "is_Int_fm"

arity_theorem for "is_funspace_fm"

arity_theorem for "is_function_space_fm"

arity_theorem for "surjP_rel_fm"

arity_theorem intermediate for "is_surj_fm"

lemma arity_is_surj_fm [arity] :
  "A \<in> nat \<Longrightarrow> B \<in> nat \<Longrightarrow> I \<in> nat \<Longrightarrow> arity(is_surj_fm(A, B, I)) = succ(A) \<union> succ(B) \<union> succ(I)"
  using arity_is_surj_fm'
  by auto

arity_theorem for "injP_rel_fm"

arity_theorem intermediate for "is_inj_fm"

lemma arity_is_inj_fm [arity]:
  "A \<in> nat \<Longrightarrow> B \<in> nat \<Longrightarrow> I \<in> nat \<Longrightarrow> arity(is_inj_fm(A, B, I)) = succ(A) \<union> succ(B) \<union> succ(I)"
  using arity_is_inj_fm'
  by auto

arity_theorem for "is_bij_fm"

arity_theorem for "is_eqpoll_fm"

arity_theorem for "is_cardinal_fm"

text\<open>Y probamos la equivalencia entre la versión full-relacional
y el concepto relativo\<close>

context M_Perm begin

is_iff_rel for "cardinal"
  using least_abs'[of "\<lambda>i. M(i) \<and> i \<approx>\<^bsup>M\<^esup> A"]
    is_eqpoll_iff
  unfolding is_cardinal_def cardinal_rel_def
  by simp
end

(*lemma (in M_trivial) is_cardinal_iff :
  assumes "M(x)" "M(c)"
  shows "is_cardinal(M,x,c) \<longleftrightarrow> c = |x|\<^bsup>M\<^esup>"
  using assms least_abs'[of "\<lambda>i. M(i) \<and> i \<approx>\<^bsup>M\<^esup> x"]
  unfolding is_cardinal_def cardinal_rel_def
  by simp*)

text\<open>Esa es toda la disciplina.\<close>

reldb_add relational "Ord" "ordinal"
reldb_add functional "lt" "lt"
reldb_add relational "lt" "lt_rel"
synthesize "lt_rel" from_definition
arity_theorem intermediate for "lt_rel_fm"

lemma arity_lt_rel_fm[arity]: "a \<in> nat \<Longrightarrow> b \<in> nat \<Longrightarrow> arity(lt_rel_fm(a, b)) = succ(a) \<union> succ(b)"
  using arity_lt_rel_fm'
  by auto

relativize functional "Card" "Card_rel" external
relationalize "Card_rel" "is_Card"
synthesize "is_Card" from_definition assuming "nonempty"
arity_theorem for "is_Card_fm"

notation Card_rel (\<open>Card\<^bsup>_\<^esup>'(_')\<close>)

lemma (in M_Perm) is_Card_iff: "M(A) \<Longrightarrow> is_Card(M, A) \<longleftrightarrow> Card\<^bsup>M\<^esup>(A)"
  using is_cardinal_iff
  unfolding is_Card_def Card_rel_def by simp

abbreviation
  Card_r_set  :: "[i,i]\<Rightarrow>o"  (\<open>Card\<^bsup>_\<^esup>'(_')\<close>) where
  "Card\<^bsup>M\<^esup>(i) \<equiv> Card_rel(##M,i)"

relativize functional "InfCard" "InfCard_rel" external
relationalize "InfCard_rel" "is_InfCard"
synthesize "is_InfCard" from_definition assuming "nonempty"
arity_theorem for "is_InfCard_fm"

notation InfCard_rel (\<open>InfCard\<^bsup>_\<^esup>'(_')\<close>)

abbreviation
  InfCard_r_set  :: "[i,i]\<Rightarrow>o"  (\<open>InfCard\<^bsup>_\<^esup>'(_')\<close>) where
  "InfCard\<^bsup>M\<^esup>(i) \<equiv> InfCard_rel(##M,i)"

relativize functional "cadd" "cadd_rel" external

abbreviation
  cadd_r :: "[i,i\<Rightarrow>o,i] \<Rightarrow> i" (\<open>_ \<oplus>\<^bsup>_\<^esup> _\<close> [66,1,66] 65) where
  "A \<oplus>\<^bsup>M\<^esup> B \<equiv> cadd_rel(M,A,B)"

context M_basic begin
rel_closed for "cadd"
  using cardinal_rel_closed
  unfolding cadd_rel_def
  by simp
end

(* relativization *)

relationalize "cadd_rel" "is_cadd"

manual_schematic for "is_cadd" assuming "nonempty"
  unfolding is_cadd_def
  by (rule iff_sats sum_iff_sats | simp)+
synthesize "is_cadd" from_schematic

arity_theorem for "sum_fm"

arity_theorem for "is_cadd_fm"

context M_Perm begin
is_iff_rel for "cadd"
  using is_cardinal_iff
  unfolding is_cadd_def cadd_rel_def
  by simp
end

relativize functional "cmult" "cmult_rel" external

abbreviation
  cmult_r :: "[i,i\<Rightarrow>o,i] \<Rightarrow> i" (\<open>_ \<otimes>\<^bsup>_\<^esup> _\<close> [66,1,66] 65) where
  "A \<otimes>\<^bsup>M\<^esup> B \<equiv> cmult_rel(M,A,B)"

(* relativization *)
relationalize "cmult_rel" "is_cmult"

declare cartprod_iff_sats [iff_sats]

synthesize "is_cmult" from_definition assuming "nonempty"

arity_theorem for "is_cmult_fm"

context M_Perm begin

rel_closed for "cmult"
  using cardinal_rel_closed
  unfolding cmult_rel_def
  by simp

is_iff_rel for "cmult"
  using is_cardinal_iff 
  unfolding is_cmult_def cmult_rel_def
  by simp

end


definition
  Powapply :: "[i,i] \<Rightarrow> i"  where
  "Powapply(f,y) \<equiv> Pow(f`y)"

reldb_add functional "Pow" "Pow_rel"
reldb_add relational "Pow" "is_Pow"

lemma subset_iff_sats[iff_sats]:
  "nth(i, env) = x \<Longrightarrow> nth(j, env) = y \<Longrightarrow> i\<in>nat \<Longrightarrow> j\<in>nat \<Longrightarrow>
   env \<in> list(A) \<Longrightarrow> subset(##A, x, y) \<longleftrightarrow> A, env \<Turnstile> subset_fm(i, j)"
  using sats_subset_fm' by simp

declare Replace_iff_sats[iff_sats]

synthesize "is_Pow" from_definition assuming "nonempty"
arity_theorem for "is_Pow_fm"

relativize functional "Powapply" "Powapply_rel"
relationalize "Powapply_rel" "is_Powapply"
synthesize "is_Powapply" from_definition assuming "nonempty"
arity_theorem for "is_Powapply_fm"

notation Powapply_rel (\<open>Powapply\<^bsup>_\<^esup>'(_,_')\<close>)

context M_basic
begin

rel_closed for "Powapply"
  unfolding Powapply_rel_def
  by simp

is_iff_rel for "Powapply"
  using Pow_rel_iff
  unfolding is_Powapply_def Powapply_rel_def
  by simp

univalent for "Powapply"
  using is_Powapply_iff
  unfolding univalent_def
  by simp

end

(* definition
  HVfrom_rel :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> i" (\<open>HVfrom\<^bsup>_\<^esup>'(_,_,_')\<close>) where
  "HVfrom\<^bsup>M\<^esup>(A,x,f) \<equiv> A \<union> (\<Union>y\<in>x. Powapply\<^bsup>M\<^esup>(f,y))" *)

definition
  HVfrom :: "[i,i,i] \<Rightarrow> i" where
  "HVfrom(A,x,f) \<equiv> A \<union> (\<Union>y\<in>x. Powapply(f,y))"

relativize functional "HVfrom" "HVfrom_rel"
relationalize "HVfrom_rel" "is_HVfrom"
synthesize "is_HVfrom" from_definition assuming "nonempty"
arity_theorem for "is_HVfrom_fm"

notation HVfrom_rel (\<open>HVfrom\<^bsup>_\<^esup>'(_,_,_')\<close>)

locale M_HVfrom = M_eclose +
  assumes
    Powapply_replacement:
      "M(K) \<Longrightarrow> strong_replacement(M,\<lambda>y z. z = Powapply\<^bsup>M\<^esup>(f,y))"
begin

is_iff_rel for "HVfrom"
proof -
  assume assms:"M(A)" "M(x)" "M(f)" "M(res)"
  then
  have "is_Replace(M,x,\<lambda>y z. z = Powapply\<^bsup>M\<^esup>(f,y),r) \<longleftrightarrow> r = {z . y\<in>x, z = Powapply\<^bsup>M\<^esup>(f,y)}"
    if "M(r)" for r
    using that Powapply_rel_closed
          Replace_abs[of x r "\<lambda>y z. z = Powapply\<^bsup>M\<^esup>(f,y)"] transM[of _ x]
    by simp
  moreover
  have "is_Replace(M,x,is_Powapply(M,f),r) \<longleftrightarrow> 
        is_Replace(M,x,\<lambda>y z. z = Powapply\<^bsup>M\<^esup>(f,y),r)" if "M(r)" for r
    using assms that is_Powapply_iff is_Replace_cong 
    by simp
  ultimately
  have "is_Replace(M,x,is_Powapply(M,f),r) \<longleftrightarrow> r = {z . y\<in>x, z = Powapply\<^bsup>M\<^esup>(f,y)}"
    if "M(r)" for r
    using that assms 
    by simp
  moreover
  have "M({z . y \<in> x, z = Powapply\<^bsup>M\<^esup>(f,y)})" 
    using assms strong_replacement_closed[OF Powapply_replacement] 
          Powapply_rel_closed transM[of _ x]
    by simp
  moreover from assms
  \<comment> \<open>intermediate step for body of Replace\<close>
  have "{z . y \<in> x, z = Powapply\<^bsup>M\<^esup>(f,y)} = {y . w \<in> x, M(y) \<and> M(w) \<and> y = Powapply\<^bsup>M\<^esup>(f,w)}" 
    by (auto dest:transM)
  ultimately
  show ?thesis
    using assms
  unfolding is_HVfrom_def HVfrom_rel_def
    by (auto dest:transM)
qed

univalent for "HVfrom"
  using is_HVfrom_iff
  unfolding univalent_def
  by simp

rel_closed for "HVfrom"
proof -
  assume assms:"M(A)" "M(x)" "M(f)"
  have "M({z . y \<in> x, z = Powapply\<^bsup>M\<^esup>(f,y)})" 
    using assms strong_replacement_closed[OF Powapply_replacement] 
          Powapply_rel_closed transM[of _ x]
    by simp
  then 
  have "M(A \<union> \<Union>({z . y\<in>x, z = Powapply\<^bsup>M\<^esup>(f,y)}))"
    using assms
    by simp
  moreover from assms
  \<comment> \<open>intermediate step for body of Replace\<close>
  have "{z . y \<in> x, z = Powapply\<^bsup>M\<^esup>(f,y)} = {y . w \<in> x, M(y) \<and> M(w) \<and> y = Powapply\<^bsup>M\<^esup>(f,w)}" 
    by (auto dest:transM)
  ultimately
  show ?thesis
    using assms
    unfolding HVfrom_rel_def 
    by simp    
qed

end (*  M_HVfrom *)

(*
relativize functional "Vfrom" "Vfrom_rel" external
relationalize "Vfrom_rel" "is_Vfrom"
synthesize "is_Vfrom" from_definition assuming "nonempty"
arity_theorem for "is_Vfrom_fm"

notation Vfrom_rel (\<open>Vfrom\<^bsup>_\<^esup>'(_,_')\<close>)

context M_basic
begin

is_iff_rel for "Vfrom"
  using Pow_rel_iff
  unfolding is_Vfrom_def Vfrom_rel_def
  by simp

univalent for "Vfrom"
  using is_Vfrom_iff
  unfolding univalent_def
  by simp

rel_closed for "Vfrom"
  unfolding Vfrom_rel_def
  by simp

*)

definition
  Vfrom_rel :: "[i\<Rightarrow>o,i,i] \<Rightarrow> i" (\<open>Vfrom\<^bsup>_\<^esup>'(_,_')\<close>) where
  "Vfrom\<^bsup>M\<^esup>(A,i) = transrec(i, HVfrom_rel(M,A))"

(* relativization *)
definition
  is_Vfrom :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_Vfrom(M,A,i,z) \<equiv> is_transrec(M,is_HVfrom(M,A),i,z)"

locale M_Vfrom = M_HVfrom +
  assumes
    trepl_HVfrom : "\<lbrakk> M(A);M(i) \<rbrakk> \<Longrightarrow> transrec_replacement(M,is_HVfrom(M,A),i)"

begin

lemma  Vfrom_rel_iff : 
  assumes "M(A)" "M(i)" "M(z)" "Ord(i)"
  shows "is_Vfrom(M,A,i,z) \<longleftrightarrow> z = Vfrom\<^bsup>M\<^esup>(A,i)"
proof -
  have "relation2(M, is_HVfrom(M, A), HVfrom_rel(M, A))"
    using assms is_HVfrom_iff
    unfolding relation2_def
    by simp
  then
  show ?thesis
  using assms HVfrom_rel_closed trepl_HVfrom 
              transrec_abs[of "is_HVfrom(M,A)" i "HVfrom_rel(M,A)" z]
  unfolding is_Vfrom_def Vfrom_rel_def
  by simp
qed

end (* M_Vfrom *)

end