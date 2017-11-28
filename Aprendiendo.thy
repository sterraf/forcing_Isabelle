theory Aprendiendo
imports Pure FOL
begin
chapter\<open>Aprendiendo a usar Isar\<close>
text\<open>En este archivo mostramos cómo utilizar el estilo de prueba declarativo.
Para ello iremos refinando la prueba de la conmutatividad de la disyunción. 
La primera prueba es @{disj_comm}.\<close>


text\<open>En esta prueba enunciamos la conmutatividad como lo esperamos.
El uso de proof sin ningún parámetro implica que se usarán reglas
de introducción y,o eliminación.\<close>
lemma disj_comm: "P \<or> Q \<longrightarrow> Q \<or> P"
proof 
  assume pq : "P \<or> Q"
  show "Q \<or> P"
  proof (rule disjE[OF pq])
    assume p : "P" show "Q \<or> P"
    proof(rule disjI2) 
      show "P" by fact
    qed
    next
    assume "Q" then show "Q \<or> P" by(rule disjI1)
  qed
qed

text\<open>La prueba anterior la podemos simplificar si utilizamos la palabra clave
thus. En el segundo caso, dejamos que Isabelle complete la prueba.\<close>
lemma disj_comm': "P \<or> Q \<longrightarrow> Q \<or> P"
proof 
  assume pq : "P \<or> Q"
  show "Q \<or> P"
  proof (rule disjE[OF pq])
    assume "P" thus ?thesis by(rule disjI2)
    next
    assume "Q" then show ?thesis ..
  qed
qed
text\<open>Una forma más simple de que se active la regla de eliminación es usando
using...\<close>
lemma disj_comm'': "P \<or> Q \<longrightarrow> Q \<or> P"
proof 
  assume pq : "P \<or> Q"
  show "Q \<or> P"
  using pq
  proof 
    assume "P" thus ?thesis by(rule disjI2)
    next
    assume "Q" then show ?thesis ..
  qed
qed

text\<open>Veamos cómo hacer una prueba en la que vamos deduciendo resultados parciales.
Además introducimos las hipótesis, en vez de enunciar la implicación.\<close>
lemma or_dist_and:
  assumes pqr : "(P \<or> Q) \<and> (P \<or> R)" (is "?PQ \<and> ?PR")
  shows "P \<or> (Q \<and> R)" 
proof - (* si no pusiéramos -, usaría introducción y nos pide
         prematuramente probar P *)
  from pqr have pq:?PQ by (rule conjE)
  moreover
  from pqr have pr:?PR by (rule conjE)
  show ?thesis
  using pq (* de esta manera estamos diciendo que hacemos eliminación de \<or> *)
  proof 
    assume "P" thus ?thesis by (rule disjI1)
    next
      assume q:"Q" show ?thesis
      using pr
      proof
       assume "P" thus ?thesis ..
       next
       assume r:"R" 
        moreover from q r have qr:"Q\<and>R" by (rule conjI)
        thus ?thesis by (rule disjI2)
      qed
    qed
  qed
  