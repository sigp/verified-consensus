theory Test_Commands
imports
  Assertions
  "../General/CRA"
  "../General/Abstract_Sync"
begin

locale sync_command_with_tests = assertions + abstract_sync +
  assumes test_sync_distrib: "(\<tau> p); (c \<otimes> d) = ((\<tau> p); c) \<otimes> ((\<tau> p); d)" 
  assumes test_sync_test: "(\<tau> p) \<otimes> (\<tau> q) = (\<tau> p) \<sqinter> (\<tau> q)"
begin

lemma test_sync_to_inf: "(\<tau> p1) \<otimes> (\<tau> p2) = \<tau>(p1 \<sqinter> p2)"
  by (simp add: test_sync_test)

lemma test_sync_idem: "\<tau> p \<otimes> \<tau> p = \<tau> p "
  using test_sync_test by auto

lemma test_sync_nil: "\<tau> p \<otimes> nil = \<tau> p"
  using test_sync_test by (metis inf_top_right test_sync_to_inf test_top) 
end


(* An abort-strict sync operator, like weak conjunction or parallel. *)
locale sync_command_with_tests_aborting = sync_command_with_tests + chaos +
  assumes chaos_sync_magic: "\<bottom> \<ge> chaos \<otimes> \<bottom>"
  assumes chaos_ref_nil: "chaos \<ge> nil"
  assumes seq_conj_interchange: "(c\<^sub>0;c\<^sub>1) \<otimes> (d\<^sub>0;d\<^sub>1) \<ge> (c\<^sub>0 \<otimes> d\<^sub>0);(c\<^sub>1 \<otimes> d\<^sub>1)"
  assumes sync_abort_right: "c \<otimes> \<top> = \<top>"
begin

lemma sync_abort_left: "\<top> \<otimes> c = \<top>"
  using sync_abort_right sync_commute by fastforce

lemma nonabort_sync_top: "chaos \<ge> c \<Longrightarrow> c \<otimes> \<bottom> = \<bottom>"
  by (metis chaos_sync_magic sync_mono bot.extremum_uniqueI)

lemma chaos_ref_test: "chaos \<ge> \<tau> p" using test_top
  by (meson dual_order.trans chaos_ref_nil nil_ref_test)

lemma test_abort_sync_test_abort: 
   assumes test_commands: "t1 = \<tau>(p) \<and> t2 = \<tau>(q)"
   shows "t1;\<top> \<otimes> t2;\<top> = (t1 \<squnion> t2);\<top>" 
proof -
  have a1: "t1;\<top> \<otimes> t2;\<top> = nil;(t1;\<top> \<otimes> t2;\<top>)" by simp
  then have a2: "... = (t1 \<squnion> t2 \<squnion> test.negate(t1 \<squnion> t2));(t1;\<top> \<otimes> t2;\<top>)"
     by (metis test_commands test_nondet_compl test.hom_sup)
  then have a3: "... = t1;(t1;\<top> \<otimes> t2;\<top>) \<squnion> t2;(t1;\<top> \<otimes> t2;\<top>) 
                              \<squnion> test.negate(t1 \<squnion> t2);(t1;\<top> \<otimes> t2;\<top>)"
     by (simp add: nondet_seq_distrib)
  then have a4: "... = (t1;t1;\<top> \<otimes> t1;t2;\<top>) \<squnion> (t2;t1;\<top> \<otimes> t2;t2;\<top>) \<squnion>
                       (test.negate(t1 \<squnion> t2);t1;\<top> \<otimes> test.negate(t1 \<squnion> t2);t2;\<top>)"
      by (metis seq_assoc test_commands test.hom_not test_sync_distrib test.hom_sup)
  then have a5: "... = (t1;\<top> \<otimes> t1;t2;\<top>) \<squnion> (t2;t1;\<top> \<otimes> t2;\<top>) \<squnion>
                       (test.negate(t1 \<squnion> t2);t1;\<top> \<otimes> test.negate(t1 \<squnion> t2);t2;\<top>)"
     using test_commands test_seq_idem by auto
  then have a6: "... = t1;(\<top> \<otimes> t2;\<top>) \<squnion> t2;(t1;\<top> \<otimes> \<top>) \<squnion> 
               ((test.negate(t1) \<sqinter> test.negate(t2));t1;\<top> \<otimes> (test.negate(t1) \<sqinter> test.negate(t2));t2;\<top>)"
     using sequential.seq_assoc sequential_axioms test_commands test_de_morgan 
            test_sync_distrib by fastforce 
  then have a7: "... = t1;(\<top> \<otimes> t2;\<top>) \<squnion> t2;(t1;\<top> \<otimes> \<top>) \<squnion> 
            ((test.negate(t1) \<sqinter> test.negate(t2) \<sqinter> t1);\<top> \<otimes> (test.negate(t1) \<sqinter> test.negate(t2) \<sqinter> t2);\<top>)"
     proof -
       have f1: "\<tau> (- (p \<squnion> q)) = test.negate t1 \<sqinter> test.negate t2" by (simp add: test_commands)
       then have f2: "test.negate t1 \<sqinter> test.negate t2 \<sqinter> t1 = (test.negate t1 \<sqinter> test.negate t2) ; t1"
         by (metis (no_types) test_inf_eq_seq test_commands)
       have "test.negate t1 \<sqinter> test.negate t2 \<sqinter> t2 = (test.negate t1 \<sqinter> test.negate t2) ; t2"
         using f1 by (metis (no_types) test_inf_eq_seq test_commands) 
       then show ?thesis using f2 by presburger
     qed
  then have a8: "... = t1;(\<top> \<otimes> t2;\<top>) \<squnion> t2;(t1;\<top> \<otimes> \<top>) \<squnion> (\<bottom>;\<top> \<otimes> \<bottom>;\<top>)"      
     proof -
       have f1: "\<forall>a. t1 \<sqinter> (test.negate t1 \<sqinter> a) = \<bottom>"
         by (metis inf_commute inf_left_commute inf_bot_right test.hom_compl_sup test_commands)
       have "\<forall>a. t2 \<sqinter> (test.negate t2 \<sqinter> a) = \<bottom>"
         by (metis inf_commute inf_left_commute inf_bot_right test.hom_compl_sup test_commands)
       then show ?thesis using f1 by (metis (no_types) inf_sup_aci(1))
     qed
     then have a9: "... = t1;\<top> \<squnion> t2;\<top> \<squnion> \<bottom>" by (simp add: sync_abort_left nonabort_sync_top sync_commute)
  thus ?thesis using a1 a2 a3 a4 a5 a6 a7 a8 a9 nondet_seq_distrib inf_top.right_neutral by auto
qed

lemma nonaborting_sync_test_pre_generic: 
  assumes c_nonabort: "c \<otimes> \<bottom> = \<bottom>" (* i.e. c does not plan to abort immediately *)
  shows "c \<otimes> (\<tau> p);d = (\<tau> p);(c \<otimes> d)"
proof -
  have a1: "c \<otimes> (\<tau> p);d = (\<tau>(p) \<squnion> test.negate(\<tau>(p)));(c \<otimes> (\<tau> p);d)" using test_nondet_compl by auto   
  then have a2: "... = \<tau>(p);(c \<otimes> (\<tau> p);d) \<squnion> test.negate(\<tau>(p));(c \<otimes> (\<tau> p);d)"
     using nondet_seq_distrib by blast
  then have a3: "... = (\<tau>(p);c) \<otimes> (\<tau>(p);\<tau>(p);d)  \<squnion> \<bottom>"
    proof -
       have "test.negate (\<tau> p) ; \<tau> p = \<bottom>"
           by (metis (no_types) test_seq_compl test.hom_not test_seq_commute)
       then have "\<bottom> = \<tau> (- p) ; (c \<otimes> \<tau> p ; d)"
           by (metis (no_types) assms seq_assoc seq_magic_left test.hom_not test_sync_distrib test_seq_magic)
       then show ?thesis by (simp add: seq_assoc test_sync_distrib)
    qed 
  thus ?thesis using a1 a2 inf_top.right_neutral test_sync_distrib test_seq_idem by auto 
qed

lemma nonaborting_sync_test_pre: 
  assumes c_nonabort: "chaos \<ge> c"
  shows "c \<otimes> (\<tau> p);d = (\<tau> p);(c \<otimes> d)"
proof -
  have "c \<otimes> \<bottom> = \<bottom>"
    using nonabort_sync_top assms by simp
  then show ?thesis using nonaborting_sync_test_pre_generic by simp
qed

(* The assumptions of this lemma (with respect to non-aborting behaviour of c and d) are
   stronger than necessary. We should be able to weaken to at least 
   chaos \<ge> \<tau>(p);c and chaos \<ge> \<tau>(q);d *)
lemma test_nonaborting_sync_test_nonaborting:
  assumes c_nonabort: "chaos \<ge> c"
  assumes d_nonabort: "chaos \<ge> d"
  shows "(\<tau>(p); c) \<otimes> (\<tau>(q); d) = \<tau>(p \<sqinter> q); (c \<otimes> d)"
proof -
  have "chaos \<ge> \<tau>(p); c" using c_nonabort seq_mono_right test_seq_refine by blast
  then have "(\<tau>(p); c) \<otimes> (\<tau>(q); d) =  \<tau>(q);(\<tau>(p);c \<otimes> d)" 
    using nonaborting_sync_test_pre by simp
  also have "... = \<tau>(q);\<tau>(p);(c \<otimes> d)"
    using nonaborting_sync_test_pre d_nonabort seq_assoc sync_commute by simp
  also have "... = \<tau>(p \<sqinter> q); (c \<otimes> d)"
    using test_seq_commute test_seq_test by auto
  finally show ?thesis .
qed

lemma nonaborting_sync_test_bot:
  assumes "chaos \<ge> c"
  shows "c \<otimes> (\<tau> p);\<top> = (\<tau> p);\<top>"
  by (simp add: assms sync_abort_right nonaborting_sync_test_pre)

lemma nil_sync_test_pre: 
  "nil \<otimes> (\<tau> p);d = (\<tau> p);(nil \<otimes> d)" using nonaborting_sync_test_pre
  using chaos_ref_test by (simp add: chaos_ref_nil)

(* Lemma now available for parallel. *)
lemma nil_sync_assert: "nil \<otimes> assert(p) = assert(p)" (* formerly: nil_conj_assert*)
proof -
  have s1: "nil \<otimes> assert(p) = (nil \<otimes> \<tau> p) \<squnion> (nil \<otimes> \<tau>(-p);\<top>)"
    using nondet_sync_distrib sync_commute assert_def by (metis test.hom_not)  
  then have s2: "\<dots> = \<tau>(top \<sqinter> p) \<squnion> (\<tau>(top) \<otimes> \<tau>(-p);\<top>)"
    using test_sync_to_inf test_top by metis 
  then have s3: "\<dots> = \<tau> p \<squnion> (\<tau>(top) \<otimes> \<tau>(-p);\<top>)" by auto
  then have s4: "\<dots> = \<tau> p \<squnion> (\<tau>(p) \<otimes> \<tau>(-p);\<top>) \<squnion> (\<tau>(-p) \<otimes> \<tau>(-p);\<top>)"
    by (simp add: chaos_ref_test nonaborting_sync_test_bot)
  then have s5: "\<dots> = \<tau> p \<squnion> \<tau>(-p);\<top>"
  proof -
    have "\<tau>(p) \<otimes> \<tau>(-p);\<top> =  \<tau>(-p);\<top>"
      using chaos_ref_test nonaborting_sync_test_bot by metis
    moreover have "\<tau>(-p) \<otimes> \<tau>(-p);\<top> =  \<tau>(-p);\<top>"
      using chaos_ref_test nonaborting_sync_test_bot by metis
    ultimately show ?thesis
      by simp 
  qed
  thus ?thesis using s1 s2 s3 s4 using assert_def test.hom_not by auto 
qed

(* Here follows a nice lemma Larissa discovered early 2018.  *)
lemma test_sync_post_helper1: "c \<otimes> d;\<tau>(p) = (c \<otimes> d;\<tau>(p));\<lbrace>p\<rbrace>"
proof (rule antisym)
  show "(c \<otimes> d;\<tau>(p));\<lbrace>p\<rbrace> \<ge> c \<otimes> d;\<tau>(p)"
    using assert_nil seq_mono_right seq_nil_right by metis
next
  have "c \<otimes> d;\<tau>(p) = c;nil \<otimes> d;\<tau>(p);\<lbrace>p\<rbrace>"
    using test_seq_assert seq_assoc by simp
  also have "... \<ge> (c \<otimes> d;\<tau>(p));(nil \<otimes> \<lbrace>p\<rbrace>)"
    using seq_conj_interchange by metis
  finally show "c \<otimes> d;\<tau>(p) \<ge>  (c \<otimes> d;\<tau>(p));\<lbrace>p\<rbrace>"
    by (simp add: nil_sync_assert)
qed

lemma test_sync_post_helper2: "(c \<otimes> d;\<tau>(p)) = (c \<otimes> d;\<tau>(p));\<tau>(p)"
  by (metis test_sync_post_helper1 assert_seq_test seq_assoc) 

lemma test_sync_post: "(c \<otimes> d;\<tau>(p)) = (c \<otimes> d);\<tau>(p)"
proof (rule antisym)
  have "(c \<otimes> d;\<tau>(p)) \<ge> (c;nil \<otimes> d;\<tau>(p))"
    by simp
  also have "... \<ge> (c \<otimes> d);(nil \<otimes> \<tau>(p))"
    using seq_conj_interchange calculation order_trans by blast
  thus "(c \<otimes> d;\<tau>(p)) \<ge> (c \<otimes> d);\<tau>(p)"
    using nil_inf_test test_sync_test by (simp add: nil_def)
next
  have "(c \<otimes> d);\<tau>(p) \<ge> (c \<otimes> d;\<tau>(p));\<tau>(p)"
    by (metis sync_mono_right seq_mono_left seq_mono_right seq_nil_right nil_ref_test)
  then show "(c \<otimes> d);\<tau>(p) \<ge> (c \<otimes> d;\<tau>(p))"
    using test_sync_post_helper2 by simp
qed

lemma test_sync_post2:
  shows "c;\<tau>(p) \<otimes> d;\<tau>(q) = (c \<otimes> d);\<tau>(p \<sqinter> q)"
proof -
  have "c;\<tau>(p) \<otimes> d;\<tau>(q) = (c;\<tau>(p) \<otimes> d);\<tau>(q)"
    using test_sync_post by simp
  also have "... = (c \<otimes> d);\<tau>(p);\<tau>(q)"
    using test_sync_post sync_commute by simp
  also have "... = (c \<otimes> d);\<tau>(p \<sqinter> q)"
    using test_seq_test seq_assoc by simp
  finally show ?thesis .
qed

end

(* Here we bring together tests, strong conjunction, weak conjunction, parallel and sequential 
   composition via the CRA locale. To avoid having duplicate locale parameters, we need to
   instantiate nil (the identity of sequential composition) with \<tau>(top). This definition has already
   been given in test_sequential.  *)
locale test_commands = assertions + cra seq nil +
  assumes test_par_distrib: "(\<tau> p); (c \<parallel> d) = ((\<tau> p); c) \<parallel> ((\<tau> p); d)" 
  assumes test_conj_distrib: "(\<tau> p); (c \<iinter> d) = ((\<tau> p); c) \<iinter> ((\<tau> p); d)" 
  assumes test_par_test: "(\<tau> p) \<parallel> (\<tau> q) = (\<tau> p) \<sqinter> (\<tau> q)"
begin

lemma chaos_ref_test: "chaos \<ge> \<tau> p" using test_top
  by (meson dual_order.trans chaos_ref_nil nil_ref_test)

lemma test_conj_to_inf: "(\<tau> p) \<iinter> (\<tau> q) = (\<tau> p) \<sqinter> (\<tau> q)"
  by (simp add: chaos_ref_test conj_to_inf_nonaborting) 

(* Weak conjunction and Parallel are abort-strict, which allows a few extra lemmas 
  (in sync_command_with_tests_aborting) whereas sup gets a smaller set
  (from sync_command_with_tests) *)
sublocale conj: sync_command_with_tests_aborting  seq  test conj chaos
  using conj.assoc conj.commute sync_Nondet_distrib test_conj_distrib test_conj_to_inf
        chaos_ref_nil seq_conj_interchange conj_abort_right
  by unfold_locales auto

sublocale par: sync_command_with_tests_aborting  seq test par chaos
  using par.assoc par.commute sync_Nondet_distrib test_par_distrib test_par_test 
        chaos_ref_nil chaos_par_magic seq_par_interchange par_abort_right
  by unfold_locales auto

sublocale inf: sync_command_with_tests  seq  test inf
proof -
  have "\<And>D c. D \<noteq> {} \<Longrightarrow> (c::'a::refinement_lattice) \<sqinter> (\<Squnion>D) = (\<Squnion>d \<in> D. c \<sqinter> d)" 
    by (simp add: inf_Sup) 
  moreover have "\<And>p c d. (\<tau> p); (c \<sqinter> d) = ((\<tau> p); c) \<sqinter> ((\<tau> p); d)"
    using test_inf_interchange by auto
  ultimately show "sync_command_with_tests seq  test inf"
   by unfold_locales auto
qed

end

end
