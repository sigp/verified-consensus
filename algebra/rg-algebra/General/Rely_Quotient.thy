section \<open> Rely quotient operator \label{S:rely-quotient} \<close>

text \<open>
  The rely quotient operator is used to generalise a Jones-style rely condition
  to a process \cite{jon83a}.
  It is defined in terms of the parallel operator and a process @{term "i"}
  representing interference from the environment.
\<close>

theory Rely_Quotient
imports
  CRA
  Distributive_Iteration
begin

subsection \<open> Basic rely quotient \<close>

text \<open>Remove existing notation for quotient as it interferes with the rely quotient.\<close>
no_notation (xsymbols) Equiv_Relations.quotient  (infixl "'/'/" 90)
no_notation (HTML) Equiv_Relations.quotient  (infixl "'/'/" 90)

locale rely_quotient = par_distrib + conjunction_parallel
begin

definition
  rely_quotient :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "'/'/" 85)
where
  "c // i \<equiv> \<Squnion>{ d. (c \<ge> d \<parallel> i)}"
text \<open>
  The rely quotient of a process @{term "c"} and an interference process @{term "i"}
  is the most general process @{term "d"} such that @{term "c"} is refined by 
  @{term "d \<parallel> i"}.
  This locale introduces the definition of the 
  rely quotient @{term "c // i"} as a non-deterministic choice over 
  all processes @{term "d"} such that @{term "c"} is refined by @{term "d \<parallel> i"}. 
\<close>
text \<open>
  Any process @{term "c"} is implemented by itself if the interference is @{term "skip"}.
\<close>
lemma quotient_identity: "c // skip = c"
proof -
  have "c // skip = \<Squnion>{ d. (c \<ge> d \<parallel> skip) }" by (metis rely_quotient_def)
  then have "c // skip = \<Squnion>{ d. (c \<ge> d)  }" by (metis (mono_tags, lifting) Collect_cong par_skip) 
  thus ?thesis
    by (metis cSup_eq_maximum mem_Collect_eq order_refl) 
qed

text \<open>
  Provided the interference process @{term "i"} is non-aborting 
  (i.e.\ it refines @{term "chaos"}), 
  any process @{term "c"} is refined by its rely quotient 
  with @{term "i"} in parallel with @{term "i"}.
  If interference @{term "i"} was allowed to be aborting then, 
  because @{term "(c // \<top>) \<parallel> \<top>"} equals @{term "\<top>"},
  it does not refine @{term "c"} in general. 
\<close>
theorem rely_quotient: 
  assumes nonabort_i: "chaos \<ge> i"
  shows "c \<ge> (c // i) \<parallel> i"
proof -
  define D where "D = { d \<parallel> i | d. (c \<ge> d \<parallel> i)}"
  define C where "C = {c}"
  have "(\<forall>d \<in> D. (\<exists> c \<in> C. c \<ge> d))" using D_def C_def CollectD singletonI by auto
  then have "\<Squnion> C \<ge> (\<Squnion> D)" by (simp add: Sup_mono) 
  then have "c \<ge> \<Squnion>{ d \<parallel> i | d. (c \<ge> d \<parallel> i)}" (is "_ \<ge> ?rhs") by (simp add: C_def D_def) 
  also have "?rhs = \<Squnion>{ d \<parallel> i | d. d \<in> {d. (c \<ge> d \<parallel> i)}}" (is "_ = ?rhs") by simp
  also have "?rhs = (\<Squnion>d \<in> {d. (c \<ge> d \<parallel> i)}. d \<parallel> i)" (is "_ = ?rhs")
    by (simp add: setcompr_eq_image)
  also have "?rhs = \<Squnion>{ d | d. (c \<ge> d \<parallel> i)} \<parallel> i"
  proof (cases "{ d | d. (c \<ge> d \<parallel> i)} = {}")
    assume "{ d | d. (c \<ge> d \<parallel> i)} = {}"
    then show "(\<Squnion>d \<in> {d. (c \<ge> d \<parallel> i)}. d \<parallel> i) = \<Squnion>{ d | d. (c \<ge> d \<parallel> i)} \<parallel> i"
      using nonabort_i Collect_empty_eq top_greatest
            nonaborting_par_magic par_commute by fastforce 
  next 
    assume a: "{ d | d. (c \<ge> d \<parallel> i)} \<noteq> {}"
    have b: "{d. (c \<ge> d \<parallel> i)}  \<noteq> {}" using a by blast 
    then have "(\<Squnion>d \<in> {d. (c \<ge> d \<parallel> i)}. d \<parallel> i) = \<Squnion>{ d. (c \<ge> d \<parallel> i)} \<parallel> i"
      by (metis abstract_sync.Nondet_sync_distrib par_distrib_axioms par_distrib_def)
    then show ?thesis by auto 
  qed
  also have "... = (c // i) \<parallel> i" by (metis rely_quotient_def)
  finally show ?thesis .
qed

text \<open>
  The following theorem represents the Galois connection between 
  the parallel operator (lower adjoint) and the rely quotient operator
  (upper adjoint). This basic relationship is used to prove the majority
  of the theorems about rely quotient.
\<close>

theorem rely_refinement: 
  assumes nonabort_i: "chaos \<ge> i"
  shows "c // i \<ge> d \<longleftrightarrow> c \<ge> d \<parallel> i"
proof
  assume a: "c // i \<ge> d"
  have "c \<ge> (c // i) \<parallel> i" using rely_quotient nonabort_i by simp
  thus "c \<ge> d \<parallel> i" using a
    by (meson abstract_sync.sync_mono dual_order.trans order_refl par_distrib.axioms(2) par_distrib_axioms)
next
  assume b: "c \<ge> d \<parallel> i"
  then have "\<Squnion>{ d. (c \<ge> d \<parallel> i)} \<ge> d" by (simp add: Sup_upper)
  thus "c // i \<ge> d" by (metis rely_quotient_def) 
qed

text \<open>
  Refining the ``numerator'' in a quotient, refines the quotient.
\<close>

lemma rely_mono:
  assumes c_refsto_d: "c \<ge> d"
  shows "(c // i) \<ge> (d // i)"
proof -
  have "\<And> f. ((d \<ge> f \<parallel> i) \<Longrightarrow> \<exists> e. (c \<ge> e \<parallel> i) \<and> (e \<ge> f))"
    using c_refsto_d order.trans by blast 
  then have b: "\<Squnion>{ e. (c \<ge> e \<parallel> i)} \<ge>  \<Squnion>{ f. (d \<ge> f \<parallel> i)}"
    by (metis Sup_mono mem_Collect_eq) 
  show ?thesis using rely_quotient_def b by simp
qed

text \<open>
  Refining the ``denominator'' in a quotient, gives a reverse refinement 
  for the quotients. This corresponds to weaken rely condition law of
  Jones \cite{jon83a}, 
  i.e. assuming less about the environment.
\<close>

lemma rely_weaken: 
  assumes i_refsto_j: "i \<ge> j"
  shows "(c // j) \<ge> (c // i)"
proof -
  have "\<And> f. ((c \<ge> f \<parallel> i) \<Longrightarrow> \<exists> e. (c \<ge> e \<parallel> j) \<and> (e \<ge> f))"
    using i_refsto_j order.trans
    by (metis abstract_sync.sync_mono_right order_refl par_distrib.axioms(2) par_distrib_axioms)
  then have b: "\<Squnion>{ e. (c \<ge> e \<parallel> j)} \<ge>  \<Squnion>{ f. (c \<ge> f \<parallel> i)}"
    by (metis Sup_mono mem_Collect_eq) 
  show ?thesis using rely_quotient_def b by simp
qed

lemma par_nonabort: 
  assumes nonabort_i: "chaos \<ge> i"
  assumes nonabort_j: "chaos \<ge> j"
  shows "chaos \<ge> i \<parallel> j"
  using abstract_sync.sync_mono chaos_par_chaos nonabort_i nonabort_j par_distrib.axioms(2) par_distrib_axioms by fastforce 


text \<open>
  Nesting rely quotients of @{term "j"} and @{term "i"} means the same as 
  a single quotient that is the parallel composition of @{term "i"} and @{term "j"}.
\<close>

lemma nested_rely: 
  assumes j_nonabort: "chaos \<ge> j"
  shows "((c // j) // i) = c // (i \<parallel> j)"
proof (rule antisym)
  show "((c // j) // i) \<ge> c // (i \<parallel> j)" 
  proof -
    have "\<And> f. ((c \<ge> f \<parallel> i \<parallel> j) \<Longrightarrow> \<exists> e. (c \<ge> e \<parallel> j) \<and> (e \<ge> f \<parallel> i))" by blast
    then have "\<Squnion>{ d. (\<Squnion>{ e. (c \<ge> e \<parallel> j)} \<ge> d \<parallel> i)} \<ge>  \<Squnion>{ f. (c \<ge> f \<parallel> i \<parallel> j)}"
      by (simp add: Collect_mono Sup_upper Sup_subset_mono)
    thus ?thesis using local.rely_quotient_def par_assoc by auto 
  qed
next
  show "c // (i \<parallel> j) \<ge> ((c // j) // i) "
  proof -
    have "c \<ge> \<Squnion>{ e. (c \<ge> e \<parallel> j)} \<parallel> j"
      using j_nonabort local.rely_quotient_def rely_quotient by auto 
    then have "\<And> d. \<Squnion>{ e. (c \<ge> e \<parallel> j)} \<ge> d \<parallel> i  \<Longrightarrow> (c \<ge> d \<parallel> i \<parallel> j)"
      by (meson j_nonabort order_trans rely_refinement)
    thus ?thesis
      by (simp add: Collect_mono Sup_subset_mono local.rely_quotient_def par_assoc) 
  qed
qed

end


subsection \<open> Distributed rely quotient \<close>

locale rely_distrib = rely_quotient + conjunction_sequential
begin

text \<open>
  The following is a fundamental law for introducing a parallel composition
  of process to refine a conjunction of specifications. 
  It represents an abstract view of the parallel introduction law of Jones \cite{jon83a}.
\<close>

lemma introduce_parallel: 
  assumes nonabort_i: "chaos \<ge>  i"
  assumes nonabort_j: "chaos \<ge>  j"
  shows "c \<iinter> d \<ge>  (j \<iinter> (c // i)) \<parallel> (i \<iinter> (d // j))"
proof -
  have a: "c \<ge> (c // i) \<parallel> i" using nonabort_i nonabort_j rely_quotient by auto
  have b: "d \<ge> j \<parallel> (d // j)" using rely_quotient par_commute 
    by (simp add: nonabort_j) 
  have "c \<iinter> d \<ge>  ((c // i) \<parallel> i) \<iinter> ( j \<parallel> (d // j))" using a b by (metis sync_mono) 
  also have interchange: "c \<iinter> d \<ge>  ((c // i) \<iinter> j) \<parallel> ( i \<iinter> (d // j))" 
   using par_conj_interchange refine_trans calculation by blast 
  show ?thesis using interchange by (simp add: local.conj_commute) 
qed

text \<open>
  Rely quotients satisfy a range of distribution properties with respect
  to the other operators.
\<close>

lemma distribute_rely_conjunction: 
  assumes nonabort_i: "chaos \<ge>  i"
  shows "(c \<iinter> d) // i  \<ge>  (c // i) \<iinter> (d // i)"
proof -
  have "c \<iinter> d \<ge> ((c // i) \<parallel> i) \<iinter> ((d // i) \<parallel> i)" using sync_mono rely_quotient
    by (simp add: nonabort_i) 
  then have "c \<iinter> d \<ge> ((c // i) \<iinter> (d // i)) \<parallel> (i \<iinter> i)"
    by (metis par_conj_interchange refine_trans) 
  then have "c \<iinter> d \<ge> ((c // i) \<iinter> (d // i)) \<parallel> i" by (metis conj_idem) 
  thus ?thesis using rely_refinement by (simp add: nonabort_i)
qed

lemma distribute_rely_choice: 
  assumes nonabort_i: "chaos \<ge>  i"
  shows "(c \<squnion> d) // i  \<ge>  (c // i) \<squnion> (d // i)"
proof -
  have "c \<squnion> d \<ge> ((c // i) \<parallel> i) \<squnion> ((d // i) \<parallel> i)" 
    by (metis nonabort_i sup_mono rely_quotient) 
  then have "c \<squnion> d \<ge> ((c // i) \<squnion> (d // i)) \<parallel> i"
    using nonabort_i rely_refinement
    using abstract_sync.sync_nondet_distrib par_commute par_distrib.axioms(2) par_distrib_axioms
    by fastforce
  thus ?thesis by (metis nonabort_i rely_refinement) 
qed

lemma distribute_rely_parallel1: 
  assumes nonabort_i: "chaos \<ge>  i"
  assumes nonabort_j: "chaos \<ge>  j"
  shows "(c \<parallel> d) // (i \<parallel> j)  \<ge>  (c // i) \<parallel> (d // j)"
proof -
  have "(c \<parallel> d) \<ge> ((c // i) \<parallel> i) \<parallel> ((d // j) \<parallel> j)" 
    using sync_mono rely_quotient nonabort_i nonabort_j
    by (meson abstract_sync.sync_mono par_distrib.axioms(2) par_distrib_axioms)
  then have "(c \<parallel> d) \<ge> (c // i) \<parallel> (d // j) \<parallel> j \<parallel> i" by (metis par_assoc par_commute) 
  thus ?thesis using par_assoc par_commute rely_refinement
    by (metis nonabort_i nonabort_j par_nonabort) 
qed

lemma distribute_rely_parallel2: 
  assumes nonabort_i: "chaos \<ge> i"
  assumes i_par_i: "i \<parallel> i \<ge> i"
  shows "(c \<parallel> d) // i  \<ge>  (c // i) \<parallel> (d // i)"
proof -
  have "(c \<parallel> d) // i \<ge> ((c \<parallel> d) // (i \<parallel> i))" using assms(1) using rely_weaken
    by (simp add: i_par_i par_nonabort)
  thus ?thesis by (metis distribute_rely_parallel1 refine_trans nonabort_i) 
qed

lemma distribute_rely_sequential: 
  assumes nonabort_i: "chaos \<ge> i"
  assumes "(\<forall> c. (\<forall> d. ((c \<parallel> i);(d \<parallel> i) \<ge> (c;d) \<parallel> i)))"
  shows "(c;d) // i \<ge> (c // i);(d // i)"
proof -
  have "c;d \<ge> ((c // i) \<parallel> i);((d // i) \<parallel> i)" 
    by (metis rely_quotient nonabort_i seq_mono) 
  then have "c;d \<ge> (c // i) ; (d // i) \<parallel> i" using assms(2) by (metis refine_trans)
  thus ?thesis by (metis rely_refinement nonabort_i) 
qed

lemma distribute_rely_sequential_event: 
  assumes nonabort_i: "chaos \<ge> i"
  assumes nonabort_j: "chaos \<ge> j"
  assumes nonabort_e: "chaos \<ge> e"
  assumes "(\<forall> c. (\<forall> d. ((c \<parallel> i);e;(d \<parallel> j) \<ge> (c;e;d) \<parallel> (i;e;j))))" 
  shows "(c;e;d) // (i;e;j) \<ge> (c // i);e;(d // j)"
proof -
  have "c;e;d \<ge> ((c // i) \<parallel> i);e;((d // j) \<parallel> j)" 
    by (metis order.refl rely_quotient nonabort_i nonabort_j seq_mono) 
  then have "c;e;d \<ge> ((c // i);e;(d // j)) \<parallel> (i;e;j)" using assms 
    by (metis refine_trans) 
  thus ?thesis using rely_refinement nonabort_i nonabort_j nonabort_e
    by (simp add: Sup_upper local.rely_quotient_def)
qed

lemma introduce_parallel_with_rely: 
  assumes nonabort_i: "chaos \<ge> i"
  assumes nonabort_j0: "chaos \<ge>  j\<^sub>0"
  assumes nonabort_j1: "chaos \<ge>  j\<^sub>1"
  shows "(c \<iinter> d) // i \<ge> (j\<^sub>1 \<iinter> (c // (j\<^sub>0 \<parallel> i))) \<parallel> (j\<^sub>0 \<iinter> (d // (j\<^sub>1 \<parallel> i)))"
proof -
  have "(c \<iinter> d) // i \<ge> (c // i) \<iinter> (d // i)" 
    by (metis distribute_rely_conjunction nonabort_i) 
  then have "(c \<iinter> d) // i \<ge> (j\<^sub>1 \<iinter> ((c // i) // j\<^sub>0)) \<parallel> (j\<^sub>0 \<iinter> ((d // i) // j\<^sub>1))" 
    by (metis introduce_parallel nonabort_j0 nonabort_j1 sup_assoc sup.absorb_iff1) 
  thus ?thesis by (simp add: nested_rely nonabort_i) 
qed

lemma introduce_parallel_with_rely_guarantee: 
  assumes nonabort_i: "chaos \<ge>  i"
  assumes nonabort_j0: "chaos \<ge>  j\<^sub>0"
  assumes nonabort_j1: "chaos \<ge>  j\<^sub>1"
  shows "(j\<^sub>1 \<parallel> j\<^sub>0) \<iinter> (c \<iinter> d) // i \<ge> (j\<^sub>1 \<iinter> (c // (j\<^sub>0 \<parallel> i))) \<parallel> (j\<^sub>0 \<iinter> (d // (j\<^sub>1 \<parallel> i)))"
proof -
  have "(j\<^sub>1 \<parallel> j\<^sub>0) \<iinter> (c \<iinter> d) // i \<ge> (j\<^sub>1 \<parallel> j\<^sub>0) \<iinter> ((j\<^sub>1 \<iinter> (c // (j\<^sub>0 \<parallel> i))) \<parallel> (j\<^sub>0 \<iinter> (d // (j\<^sub>1 \<parallel> i))))"
       (is "_ \<ge> ?rhs")
    by (metis introduce_parallel_with_rely nonabort_i nonabort_j0 nonabort_j1 
        sync_mono order.refl) 
  also have "?rhs \<ge> (j\<^sub>1 \<iinter> j\<^sub>1 \<iinter> (c // (j\<^sub>0 \<parallel> i))) \<parallel> (j\<^sub>0 \<iinter> j\<^sub>0 \<iinter> (d // (j\<^sub>1 \<parallel> i)))"
    using calculation dual_order.trans par_conj_interchange by fastforce 
  finally show ?thesis by (metis conj_idem)
qed

lemma wrap_rely_guar:
  assumes nonabort_rg: "chaos \<ge> rg" 
  and skippable: "rg \<ge> skip"
  shows "c \<ge> rg \<iinter> c // rg"
proof -
  have "c = c // skip" (is "_ = ?rhs") by (simp add: quotient_identity)
  also have "?rhs \<ge> c // rg" (is "_ \<ge> ?rhs") by (simp add: skippable rely_weaken nonabort_rg)
  also have "?rhs \<ge> rg \<iinter> c // rg" using conj_conjoin_non_aborting conj_commute nonabort_rg 
    by auto
  finally show "c \<ge> rg \<iinter> c // rg" .
qed

end


locale rely_distrib_iteration = rely_distrib + iteration_finite_distrib

begin

lemma distribute_rely_iteration: 
  assumes nonabort_i: "chaos \<ge> i"
  assumes "(\<forall> c. (\<forall> d. ((c \<parallel> i);(d \<parallel> i) \<ge> (c;d) \<parallel> i)))"
  shows "(c\<^sup>\<omega>;d) // i \<ge> (c // i)\<^sup>\<omega>;(d // i)"
proof -
  have "d \<squnion> c ; ((c // i)\<^sup>\<omega>;(d // i) \<parallel> i) \<ge> ((d // i) \<parallel> i) \<squnion> ((c // i) \<parallel> i);((c // i)\<^sup>\<omega>;(d // i) \<parallel> i)"
    (is "_ \<ge> ?rhs")
    by (metis sup_mono order.refl rely_quotient nonabort_i seq_mono) 
  also have "?rhs \<ge> ((d // i) \<parallel> i) \<squnion> ((c // i);(c // i)\<^sup>\<omega>;(d // i) \<parallel> i )" (is "_ \<ge> ?rhs")
    using assms(2) nondet_mono_right seq_assoc by fastforce
  also have "?rhs \<ge> ((d // i) \<squnion> (c // i);(c // i)\<^sup>\<omega>;(d // i)) \<parallel> i" (is "_ \<ge> ?rhs")
    using abstract_sync.sync_nondet_distrib par_commute par_distrib.axioms(2) par_distrib_axioms
    by fastforce
  also have "?rhs = ((c // i)\<^sup>\<omega>;(d // i)) \<parallel> i" 
    using iter_unfold nondet_seq_distrib seq_nil_left by metis
  finally show ?thesis
    by (simp add: iter_induct nonabort_i rely_refinement)
qed

end

end
