section \<open>Left distribution of sequential composition \label{S:conjunctive-sequential}\<close>

theory Distributive_Sequential
imports Sequential
begin

text \<open>
  Sequential left-distribution over non-deterministic choice 
  is not assumed in the algebra so far
  but it does hold in many models, 
  e.g.\ the relational model of sequential programs and
  the rely/guarantee algebra.
\<close>

locale seq_nondet_distrib = seq_distrib_right + 
  assumes seq_nondet_distrib: "c;(d\<^sub>0 \<squnion> d\<^sub>1) = c;d\<^sub>0 \<squnion> c;d\<^sub>1"
begin

sublocale seq_distrib_left
    by (simp add: seq_distrib_left.intro seq_distrib_left_axioms.intro 
        seq_nondet_distrib sequential_axioms) 
end


locale seq_Nondet_distrib = seq_distrib_right + (* lib
  for lib :: "'b \<Rightarrow> 'a::refinement_lattice \<Rightarrow> 'a" ("E\<^sup>C\<^sub>_ _" [999, 999] 999) + *)
  assumes seq_Nondet_distrib: "D \<noteq> {} \<Longrightarrow> c ; \<Squnion>D = (\<Squnion>d\<in>D. c ; d)"
begin

sublocale seq_distrib
proof unfold_locales
  fix c::'a and d\<^sub>0::'a and d\<^sub>1::'a
  have "{d\<^sub>0, d\<^sub>1} \<noteq> {}" by simp
  then have "c ; \<Squnion>{d\<^sub>0, d\<^sub>1} = \<Squnion>{c ; d |d. d \<in> {d\<^sub>0, d\<^sub>1}}" using seq_Nondet_distrib
    by (metis Collect_mem_eq setcompr_eq_image)
  also have "... = c ; d\<^sub>0 \<squnion> c ; d\<^sub>1" by (simp only: Nondet_to_nondet)
  finally show "c ; (d\<^sub>0 \<squnion> d\<^sub>1) \<ge> c ; d\<^sub>0 \<squnion> c ; d\<^sub>1" by simp
qed


lemma seq_NONDET_distrib: "X \<noteq> {} \<Longrightarrow> c ; (\<Squnion>x\<in>X. d x) = (\<Squnion>x\<in>X. c ; d x)"
proof -
  assume xne: "X \<noteq> {}"
  have a: "c ; (\<Squnion>x\<in>X. d x) = c ; \<Squnion>(d ` X)" by auto
  also have b: "... = (\<Squnion>d\<in>(d ` X). c ; d)" by (meson image_is_empty seq_Nondet_distrib xne)
  also have c: "... = (\<Squnion>x\<in>X. c ; d x)" by (simp add:image_image)
  finally show ?thesis by (simp add: b image_image)
qed

lemma seq_NONDET_distrib_UNIV: "c ; (\<Squnion>x. d x) = (\<Squnion>x. c ; d x)"
  by (simp add: seq_NONDET_distrib)

lemma NONDET_NONDET_seq_distrib: "Y \<noteq> {} \<Longrightarrow> (\<Squnion>x\<in>X. c x) ; (\<Squnion>y\<in>Y. d y) = (\<Squnion>x\<in>X. \<Squnion>y\<in>Y. c x ; d y)"
  by (simp add: NONDET_seq_distrib seq_NONDET_distrib)

lemma NONDET_NONDET_seq_distrib_UNIV: "(\<Squnion>x. c x) ; (\<Squnion>y. d y) = (\<Squnion>x. \<Squnion>y. c x ; d y)"
  by (simp add: NONDET_NONDET_seq_distrib)

end

end

