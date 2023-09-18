section \<open>Abstract view of the synchronisation operators\<close>

text \<open>The concurrency theory makes use of two synchronisation operators:
  parallel composition and weak conjunction.
  This theory provides an abstraction of the common properties of both.\<close>

theory Abstract_Sync
imports 
  Main
  "Refinement_Lattice"
begin

locale abstract_sync_pre = 
  fixes sync :: "'a::refinement_lattice \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 75)

locale abstract_sync = abstract_sync_pre + comm: abel_semigroup sync + (* liberation_stages + *)
  assumes sync_Nondet_distrib: "D \<noteq> {} \<Longrightarrow> c \<otimes> (\<Squnion>D) = (\<Squnion>d \<in> D. c \<otimes> d)"
begin
text \<open>Synchronisation operators are associative and commutative
  (i.e.\ they form and Abelian semi-group.
  Synchronisation operators distribute over arbitrary non-empty non-deterministic choices.
  Because the empty non-deterministic choice corresponds to the lattice top
  and synchronisation operators are abort strict, 
  distribution over empty choices is not valid.\<close>

lemmas [algebra_simps, field_simps] =
  comm.assoc
  comm.commute
  comm.left_commute

lemmas sync_assoc = comm.assoc
lemmas sync_commute = comm.commute

lemma Nondet_sync_distrib: "C \<noteq> {} \<Longrightarrow> (\<Squnion> C) \<otimes> d = (\<Squnion>c\<in>C. c \<otimes> d)"
  using sync_Nondet_distrib sync_commute INF_cong by simp 

lemma nondet_sync_distrib: "(c\<^sub>0 \<squnion> c\<^sub>1) \<otimes> d = (c\<^sub>0 \<otimes> d) \<squnion> (c\<^sub>1 \<otimes> d)"
proof -
  have "(c\<^sub>0 \<squnion> c\<^sub>1) \<otimes> d = (\<Squnion> {c\<^sub>0, c\<^sub>1}) \<otimes> d" by simp
  also have "... = (\<Squnion>c \<in> {c\<^sub>0, c\<^sub>1}. c \<otimes> d)" using Nondet_sync_distrib
    by (meson INF_empty INF_insert insert_not_empty)
  also have "... = c\<^sub>0 \<otimes> d \<squnion> c\<^sub>1 \<otimes> d" by simp
  finally show ?thesis .
qed

lemma sync_nondet_distrib: "d \<otimes> (c\<^sub>0 \<squnion> c\<^sub>1) = (d \<otimes> c\<^sub>0) \<squnion> (d \<otimes> c\<^sub>1)"
  using nondet_sync_distrib sync_commute by auto

lemma nondet_sync_distrib3: "(c0 \<otimes> d) \<squnion> (d \<otimes> c2) = d \<otimes> (c0 \<squnion> c2)"
    using sync_nondet_distrib by (simp add: sync_commute) 

lemma nondet_sync_distrib4: "c0  \<otimes> c1 \<squnion> (c0  \<otimes> c2 \<squnion> d) = d \<squnion> c0  \<otimes> (c1 \<squnion> c2)"
    by (simp add: sync_nondet_distrib sup.commute inf_sup_aci(7))

lemma nondet_sync_product: "(a \<squnion> b) \<otimes> (c \<squnion> d) = (a \<otimes> c) \<squnion> (a \<otimes> d) \<squnion> (b \<otimes> c) \<squnion> (b \<otimes> d)"
  by (simp add: sup_commute nondet_sync_distrib sync_nondet_distrib inf_sup_aci(7))

lemma sync_NONDET_distrib: "X \<noteq> {} \<Longrightarrow> c \<otimes> (\<Squnion>x\<in>X. d x) = (\<Squnion>x\<in>X. c \<otimes> d x)"
  by (simp add: image_image sync_Nondet_distrib)

lemma NONDET_sync_distrib: "X \<noteq> {} \<Longrightarrow> (\<Squnion>x\<in>X. d x) \<otimes> c = (\<Squnion>x\<in>X. d x \<otimes> c)"
  using sync_NONDET_distrib sync_commute by (metis (mono_tags, lifting) SUP_cong) 

lemma NONDET_sync_product: 
  "X \<noteq> {} \<Longrightarrow> Y \<noteq> {} \<Longrightarrow> (\<Squnion>x\<in>X. c x) \<otimes> (\<Squnion>y\<in>Y. d y) = (\<Squnion>x\<in>X. \<Squnion>y\<in>Y. c x \<otimes> d y)"
proof -
  assume a1: "X \<noteq> {}"
  assume "Y \<noteq> {}"
  then have "(\<Squnion>ca\<in>X. \<Squnion>da\<in>Y. c ca \<otimes> d da) = (\<Squnion>ca\<in>X. c ca \<otimes> (\<Squnion>y\<in>Y. d y))"
    by (simp add: sync_NONDET_distrib)
  then show ?thesis
    using a1 by (simp add: NONDET_sync_distrib)
qed 

lemma sync_mono: "c\<^sub>1 \<ge> d\<^sub>1 \<Longrightarrow> c\<^sub>2 \<ge> d\<^sub>2 \<Longrightarrow> c\<^sub>1 \<otimes> c\<^sub>2 \<ge> d\<^sub>1 \<otimes> d\<^sub>2"
  by (metis sup.orderE le_sup_iff order_refl nondet_sync_distrib sync_commute)

lemma sync_mono_left: "c\<^sub>0 \<ge> c\<^sub>1 \<Longrightarrow> c\<^sub>0 \<otimes> d \<ge> c\<^sub>1 \<otimes> d"
  by (simp add: sync_mono)

lemma sync_mono_right: "c\<^sub>0 \<ge> c\<^sub>1 \<Longrightarrow> d \<otimes> c\<^sub>0 \<ge> d \<otimes> c\<^sub>1"
  by (simp add: sync_mono)

end

end
