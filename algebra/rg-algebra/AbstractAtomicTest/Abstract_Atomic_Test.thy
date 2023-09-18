section \<open>Abstract view of atomic steps and tests\<close>

theory Abstract_Atomic_Test 
imports
  "../AbstractAtomic/Assumptions"
  "../AbstractTests/Assertions"
  Abstract_Atomic_Sync_Test
begin

(* Pull in all of the locale variables from their definitions, and relate the types *)
locale atomic_test_commands_pre = assertions   _ test + abstract_atomic_commands + par_atomid + conj 
  for test :: "'test::complete_boolean_algebra \<Rightarrow> 'a::refinement_lattice" ("\<tau>") +
  constrains atomic :: "'e :: complete_boolean_algebra \<Rightarrow> 'a"
  constrains par :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  constrains atomid :: "'a"
  constrains conj :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

locale atomic_test_commands = atomic_test_commands_pre 
  + atomic_assump seq nil atomic par atomid conj 
  + conj: atomic_sync_command_with_tests_aborting seq test conj atomic chaos
  + par: atomic_sync_command_with_tests_aborting seq test par atomic chaos
  + inf: atomic_sync_command_with_tests seq test
      inf atomic +
  (* Re-assume these axioms about tests that are not included as part of the above. *)
  (*
  assumes test_par_distrib: "(\<tau> p); (c \<parallel> d) = ((\<tau> p); c) \<parallel> ((\<tau> p); d)"
  assumes test_conj_distrib: "(\<tau> p); (c \<iinter> d) = ((\<tau> p); c) \<iinter> ((\<tau> p); d)" 
  assumes test_par_test: "(\<tau> p) \<parallel> (\<tau> q) = (\<tau> p) \<sqinter> (\<tau> q)"
  *)
  (* Plus an all-new assumption for this locale *)
  assumes atomic_test_is_atomic: 
        "\<exists> q. \<tau>(p1::'c::complete_boolean_algebra);atomic(p2::'b::complete_boolean_algebra) = atomic(q)"
begin

sublocale test_commands seq  test par skip conj chaos
proof (unfold_locales)
  fix p c d
  show "(\<tau> p); (c \<parallel> d) = ((\<tau> p); c) \<parallel> ((\<tau> p); d)"
    using par.test_sync_distrib by simp
next
  fix p c d
  show "(\<tau> p); (c \<iinter> d) = ((\<tau> p); c) \<iinter> ((\<tau> p); d)"
    using conj.test_sync_distrib by simp
next
  fix p q
  show "(\<tau> p) \<parallel> (\<tau> q) = (\<tau> p) \<sqinter> (\<tau> q)"
    using par.test_sync_test by simp
qed

lemma atomic_sup_test_command:"(atomic q);c \<sqinter> (\<tau> p);d = (\<tau> p);((atomic q);c \<sqinter> d)"
    by (metis (no_types) inf_top.left_neutral seq_nil_left 
          test.hom_inf test_inf_interchange test_top) 

(* atomic and test have only top in common*)

lemma atomic_sup_nil: "Atomic \<sqinter> \<tau> top = \<bottom>" using atomic_sup_test_command
  by (metis seq_nil_right inf.atomic_pre_sync_nil inf.syncid_atomic test_top)


lemma atomic_test_negate: 
   assumes equal_t_a: "(\<tau> p) = (atomic q)"
   shows "(\<tau> p) = \<bottom> \<and> (atomic q) = \<bottom>"
      by (metis equal_t_a seq_nil_right nil_inf_test inf.nil_sync_atomic_pre)

lemma  atomic_test: "(\<tau> q) \<iinter> (atomic p);c = \<bottom>"
proof -
  have "\<bottom> \<ge> (\<tau> q) \<iinter> (atomic p);c"
    by (metis conj.nil_sync_atomic_pre conj.sync_mono_left nil_ref_test) 
  thus ?thesis by (metis sup.absorb_iff2 sup_eq_bot_iff) 
qed

lemma  atomic_test_par: "(\<tau> q) \<parallel> (atomic p);c = \<bottom>"
  by (simp add: par.test_sync_atomic_pre)

(*
lemma abstract_atomic_pre:
  assumes test_t : "t = \<tau> p" 
  assumes atomic_a: "a = atomic q"
  shows "assert t \<iinter> a; c = test_negate t ; \<bottom>" 
proof -
  have a1: "assert t \<iinter> a; c = (t \<sqinter> test_negate t ; \<bottom>)  \<iinter> a; c"
      by (simp add: assert_def test_t) 
  then have a2: "... = (t \<iinter> a; c) \<sqinter> (test_negate t ; \<bottom>  \<iinter> a; c)"
      by (simp add: inf_conj_distrib)
  then have a3: "... = t;(a;c \<iinter> nil) \<sqinter> test_negate t ;(a;c \<iinter> \<bottom>)"
      by (metis atomic_a atomic_conj_test_command local.conj_commute 
                seq_nil_right test_not test_t)
  thus ?thesis
    proof -
      have "\<tau> p \<iinter> a ; c = a ; c \<iinter> \<tau> p"
         by (simp add: abel_semigroup.commute conj.abel_semigroup_axioms)
      then have "t ; (a ; c \<iinter> nil) = \<top>"
         by (metis (no_types) atomic_a atomic_conj_test_command atomic_test 
                              seq_nil_right test_t)
      then show ?thesis using a1 a2 a3 by auto
    qed
qed 

     
lemma test_conj_atomic_inf:
  assumes a_atomic: "a = atomic(p)"
  assumes t_test: "t = \<tau>(q)"
  shows "a\<^sup>\<omega> \<iinter> t = t" using seq_nil_right atomic_conj_test_command conj.atomic_iter_sync_nil
    by (metis a_atomic conj.nil_sync_nil conj.sync_assoc nil_conj_test_command t_test)
*)
             
end

end
