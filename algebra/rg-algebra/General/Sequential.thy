section \<open>Sequential composition operator \label{S:sequential}\<close>


theory Sequential
  imports 
    Refinement_Lattice
begin

subsection \<open>Basic sequential\<close>
                                 

locale seq = (* liberation_stages + *)
  fixes seq :: "'a::order_top \<Rightarrow> 'a \<Rightarrow> 'a" (infixl ";" 90)
  assumes seq_abort [simp]: "\<top> ; c = \<top>"   (* 35 *)
 (*assumes seq_first: "E\<^sup>C\<^sub>x (c ; (F\<^sup>C\<^sub>x d)) = (E\<^sup>C\<^sub>x c) ; (E\<^sup>C\<^sub>x d)" (* 59 *)
   assumes seq_last: "E\<^sup>C\<^sub>x ((L\<^sup>C\<^sub>x c) ; d) = (E\<^sup>C\<^sub>x c) ; (E\<^sup>C\<^sub>x d)" (* 60 *) *)
begin
text \<open>
  The sequential composition has abort @{term "\<top>"} as a left annihilator.
\<close>
end

locale nil =
  fixes nil :: "'a" ("nil")

locale sequential = seq + nil + seq: monoid seq nil
begin
text \<open>
  The monoid axioms imply @{term "c ; d"} is associative and 
  has identity (neutral element) @{term "nil"}.
\<close>

declare seq.assoc [algebra_simps, field_simps]

lemmas seq_assoc = seq.assoc             (* 30 *)
lemmas seq_nil_right = seq.right_neutral (* 31 *)
lemmas seq_nil_left = seq.left_neutral   (* 32 *)

end

subsection \<open>Distributed sequential\<close>

text \<open>
  Sequential composition distributes across arbitrary non-deterministic choices 
  from the right but only across the binary (finite) choice from the left
  and hence it is monotonic in both arguments. 
  We consider left distribution first.
  Note that Section \ref{S:conjunctive-sequential} considers the
  case in which the @{prop "seq_nondet_distrib_weak"} axiom is strengthened to
  an equality.
\<close>

locale seq_distrib_left = sequential +
  assumes seq_nondet_distrib_weak: 
    "(c::'a::refinement_lattice);(d\<^sub>0 \<squnion> d\<^sub>1) \<ge> (c;d\<^sub>0 \<squnion> c;d\<^sub>1)"  (* 33 *)
begin

text \<open>Left distribution implies sequential composition is monotonic is its right argument\<close>
lemma seq_mono_right: "c\<^sub>0 \<ge> c\<^sub>1 \<Longrightarrow> d ; c\<^sub>0 \<ge> d ; c\<^sub>1"
  by (metis sup.absorb_iff2 le_sup_iff seq_nondet_distrib_weak)

(* Nec? *)
lemma seq_abort_right [simp]: "c;\<top> \<ge> c"
   by (metis top.extremum seq.right_neutral seq_mono_right)

end

locale seq_distrib_right = sequential +
  assumes Nondet_seq_distrib: 
    "(\<Squnion> C) ; d = (\<Squnion>(c::'a::refinement_lattice)\<in>C. c ; d)" (* 34 *)
begin

lemma NONDET_seq_distrib: "(\<Squnion>c\<in>C. f c) ; d = (\<Squnion>c\<in>C. f c ; d)"
  by (simp add:Nondet_seq_distrib image_image)

lemma nondet_seq_distrib: "(c\<^sub>0 \<squnion> c\<^sub>1) ; d = (c\<^sub>0 ; d \<squnion> c\<^sub>1 ; d)"
proof -
  have "(c\<^sub>0 \<squnion> c\<^sub>1) ; d = (\<Squnion> {c\<^sub>0, c\<^sub>1}) ; d" by simp
  also have "... = (\<Squnion>c\<in>{c\<^sub>0, c\<^sub>1}. c ; d)" by (fact Nondet_seq_distrib)
  also have "... = (c\<^sub>0 ; d) \<squnion> (c\<^sub>1 ; d)" by simp
  finally show ?thesis .
qed

lemma seq_mono_left: "c\<^sub>0 \<ge> c\<^sub>1 \<Longrightarrow> c\<^sub>0 ; d \<ge> c\<^sub>1 ; d"
  by (metis sup.absorb_iff2 nondet_seq_distrib)

lemma seq_magic_left [simp]: "\<bottom> ; c = \<bottom>"
proof -
  have "\<bottom> ; c = (\<Squnion>a\<in>{}. a ; c)"
    by (metis Sup_empty Nondet_seq_distrib)
  thus ?thesis
    by simp
qed

primrec seq_power :: "'a \<Rightarrow> nat \<Rightarrow> 'a" (infixr "\<^sup>;^" 80) where
    seq_power_0: "a \<^sup>;^ 0 = nil"
  | seq_power_Suc: "a \<^sup>;^ Suc n = a ; (a \<^sup>;^ n)"

notation (latex output)
  seq_power ("(_\<^bsup>_\<^esup>)" [1000] 1000)

notation (HTML output)
  seq_power ("(_\<^bsup>_\<^esup>)" [1000] 1000)


lemma seq_power_front: "(a \<^sup>;^ n) ; a = a ; (a \<^sup>;^ n)"
  by (induct n, simp_all add: seq_assoc)

lemma seq_power_split_less: "i < j \<Longrightarrow> (b \<^sup>;^ j) = (b \<^sup>;^ i) ; (b \<^sup>;^ (j - i))"
proof (induct j arbitrary: i type: nat)
  case 0
  thus ?case by simp
next
  case (Suc j)
  have "b \<^sup>;^ Suc j = b ; (b \<^sup>;^ i) ; (b \<^sup>;^ (j - i))"
    using Suc.hyps Suc.prems less_Suc_eq seq_assoc by auto
  also have "... = (b \<^sup>;^ i) ; b ; (b \<^sup>;^ (j - i))" by (simp add: seq_power_front)
  also have "... = (b \<^sup>;^ i) ; (b \<^sup>;^ (Suc j - i))"
    using Suc.prems Suc_diff_le seq_assoc by force
  finally show ?case .
qed

end

locale seq_distrib = seq_distrib_right + seq_distrib_left
begin

lemma seq_mono: "c\<^sub>1 \<ge> d\<^sub>1 \<Longrightarrow> c\<^sub>2 \<ge> d\<^sub>2 \<Longrightarrow> c\<^sub>1;c\<^sub>2 \<ge> d\<^sub>1;d\<^sub>2"
  using seq_mono_left seq_mono_right by (metis inf.orderE le_infI2) 
(*
(* liberation over sequential commands *)

text_raw \<open>\DefineSnippet{seqproofs}{%\<close>
lemma seq_right: "E\<^sup>C\<^sub>x (c ; (E\<^sup>C\<^sub>x d)) = (E\<^sup>C\<^sub>x c) ; (E\<^sup>C\<^sub>x d)" (* 61 *)
text_raw \<open>}%EndSnippet\<close>
  by (metis lib_lattice.lib_idem liberation_stages.axioms(1)
      liberation_stages_axioms localising_first seq_first)

lemma seq_left: "E\<^sup>C\<^sub>x ((E\<^sup>C\<^sub>x c) ; d) = (E\<^sup>C\<^sub>x c) ; (E\<^sup>C\<^sub>x d)" (* 62 *)
  by (metis lib_lattice.lib_idem liberation_stages.axioms(1) 
      liberation_stages_axioms localising_last seq_last)
*)

end

end
