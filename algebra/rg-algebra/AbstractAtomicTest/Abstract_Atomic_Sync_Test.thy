theory Abstract_Atomic_Sync_Test
imports
    "../AbstractTests/Test_Commands"
    "../AbstractAtomic/Abstract_Atomic_Sync"
begin

locale atomic_sync_command_with_tests = sync_command_with_tests + atomic_sync_pre
                                        + atomic_sync sync  seq nil atomic
begin

(* Since we 'renamed' the atomic_sync locale by instantiating it, 
   we lost all mixfix syntax of definitions inside it. Let's 
   redeclare it here.  *)
notation 
  infiter ("_\<^sup>\<infinity>" [105] 106) and
  iter  ("_\<^sup>\<omega>" [103] 102) and
  fiter ("_\<^sup>\<star>" [101] 100) and
  seq_power (infixr "\<^sup>;^" 80)

lemma test_sync_atomic_pre: "(\<tau> p) \<otimes> ((atomic r) ; c) = \<bottom>"
    by (metis sup_eq_bot_iff nondet_sync_distrib nil_sync_atomic_pre test_nondet_compl) 

lemma atomic_test_sync_iter_test:
  assumes a_atomic[simp]: "a = (atomic r)"
  shows  "(\<tau> p1) \<otimes> a\<^sup>\<omega>;(\<tau> p2) = (\<tau> (p1 \<sqinter> p2))"
proof -
  have "(\<tau> p1) \<otimes> a\<^sup>\<omega>;(\<tau> p2) = (\<tau> p1) \<otimes> (nil \<squnion> a;a\<^sup>\<omega>);(\<tau> p2)"
    using iter_unfold by simp
  also have "... = (\<tau> p1) \<otimes> ((\<tau> p2) \<squnion> a;a\<^sup>\<omega>;(\<tau> p2))"
    using nondet_seq_distrib by simp
  also have "... = ((\<tau> p1) \<otimes> (\<tau> p2)) \<squnion> ((\<tau> p1) \<otimes> a;(a\<^sup>\<omega>;(\<tau> p2)))"
    using sync_commute nondet_sync_distrib seq_assoc by simp
  also have "... = (\<tau> (p1 \<sqinter> p2))"
    using a_atomic test_sync_atomic_pre test_sync_test by simp
  finally show ?thesis .
qed

lemma atomic_test_sync_fiter_iter_test:
  assumes a_atomic[simp]: "a = (atomic r1)"
  assumes b_atomic[simp]: "b = (atomic r2)"
  shows  "(\<tau> p1) \<otimes> a\<^sup>\<star>;b\<^sup>\<omega>;(\<tau> p2) = (\<tau> (p1 \<sqinter> p2))"
proof -
  have "(\<tau> p1) \<otimes> a\<^sup>\<star>;b\<^sup>\<omega>;(\<tau> p2) = (\<tau> p1) \<otimes> (nil \<squnion> a;a\<^sup>\<star>);b\<^sup>\<omega>;(\<tau> p2)"
    using fiter_unfold by simp
  also have "... = (\<tau> p1) \<otimes> (b\<^sup>\<omega>;(\<tau> p2) \<squnion> a;a\<^sup>\<star>;b\<^sup>\<omega>;(\<tau> p2))"
    using nondet_seq_distrib by simp
  also have "... = ((\<tau> p1) \<otimes> b\<^sup>\<omega>;(\<tau> p2)) \<squnion> ((\<tau> p1) \<otimes> a;a\<^sup>\<star>;b\<^sup>\<omega>;(\<tau> p2))"
    using sync_commute nondet_sync_distrib seq_assoc by simp
  also have "... = (\<tau> (p1 \<sqinter> p2))"
    using atomic_test_sync_iter_test b_atomic
          a_atomic test_sync_atomic_pre seq_assoc by simp
  finally show ?thesis .
qed

lemma atomic_test_helper1: "a\<^sup>\<omega>;b \<squnion> b = a\<^sup>\<omega>;b"
proof -
  have "a\<^sup>\<omega>;b \<squnion> b = (nil \<squnion> a;a\<^sup>\<omega>);b \<squnion> b"
    using iter_unfold by simp
  also have "... = (nil \<squnion> a;a\<^sup>\<omega>);b"
    by (simp add: sup_commute nondet_seq_distrib)
  also have "... = a\<^sup>\<omega>;b"
    using iter_unfold by simp
  finally show ?thesis .
qed
    
(* can be reduced to a\<^sup>\<omega>;(\<tau> p1) \<otimes> b\<^sup>\<star>;d\<^sup>\<omega>  by setting a = c, p2 = \<top>
    for showing (guar g);\<tau>(p) \<iinter> term = ((guar g) \<iinter> term);\<tau>(p) *)
lemma atomic_fiter_iter_test_sync_fiter_iter_test:
  assumes a_atomic[simp]: "a = (atomic r1)"
  assumes b_atomic[simp]: "b = (atomic r2)"
  assumes c_atomic[simp]: "c = (atomic r3)"
  assumes d_atomic[simp]: "d = (atomic r4)"
  shows "a\<^sup>\<star>;c\<^sup>\<omega>;(\<tau> p1) \<otimes> b\<^sup>\<star>;d\<^sup>\<omega>;(\<tau> p2) =
          (a\<otimes>b)\<^sup>\<star>;((c\<otimes>b)\<^sup>\<star> \<squnion> (a\<otimes>d)\<^sup>\<star>);(c\<otimes>d)\<^sup>\<omega>;(\<tau> (p1 \<sqinter> p2))"
proof -
  have  "a\<^sup>\<star>;c\<^sup>\<omega>;(\<tau> p1) \<otimes> b\<^sup>\<star>;d\<^sup>\<omega>;(\<tau> p2) = (a\<otimes>b)\<^sup>\<star>;(
        (c\<otimes>b)\<^sup>\<star>;((c\<otimes>d)\<^sup>\<omega>;((\<tau> p2) \<otimes> c\<^sup>\<omega>;(\<tau> p1) \<squnion> d\<^sup>\<omega>;(\<tau> p2) \<otimes> (\<tau> p1)) \<squnion> b\<^sup>\<star>;d\<^sup>\<omega>;(\<tau> p2) \<otimes> (\<tau> p1)) \<squnion>
        (a\<otimes>d)\<^sup>\<star>;((c\<otimes>d)\<^sup>\<omega>;((\<tau> p1) \<otimes> d\<^sup>\<omega>;(\<tau> p2) \<squnion> c\<^sup>\<omega>;(\<tau> p1) \<otimes> (\<tau> p2)) \<squnion> a\<^sup>\<star>;c\<^sup>\<omega>;(\<tau> p1) \<otimes> (\<tau> p2)))"
    using atomic_fiter_iter_pre_sync_fiter_iter_pre by simp
  also have  "... = (a\<otimes>b)\<^sup>\<star>;(
        (c\<otimes>b)\<^sup>\<star>;((c\<otimes>d)\<^sup>\<omega>;(\<tau> (p1 \<sqinter> p2)) \<squnion> \<tau> (p1 \<sqinter> p2)) \<squnion>
        (a\<otimes>d)\<^sup>\<star>;((c\<otimes>d)\<^sup>\<omega>;(\<tau> (p1 \<sqinter> p2)) \<squnion> \<tau> (p1 \<sqinter> p2)))"
    using a_atomic b_atomic c_atomic d_atomic sync_commute
    by (simp add: atomic_test_sync_iter_test atomic_test_sync_fiter_iter_test inf_commute) 
  also have  "... = (a\<otimes>b)\<^sup>\<star>;((c\<otimes>b)\<^sup>\<star> \<squnion> (a\<otimes>d)\<^sup>\<star>);((c\<otimes>d)\<^sup>\<omega>;(\<tau> (p1 \<sqinter> p2)) \<squnion> \<tau> (p1 \<sqinter> p2))"
    by (simp add: nondet_seq_distrib seq_assoc)
  also have  "... = (a\<otimes>b)\<^sup>\<star>;((c\<otimes>b)\<^sup>\<star> \<squnion> (a\<otimes>d)\<^sup>\<star>);(c\<otimes>d)\<^sup>\<omega>;(\<tau> (p1 \<sqinter> p2))"
    using atomic_test_helper1 seq_assoc by simp
  finally show ?thesis .
qed

lemma atomic_iter_test_sync_fiter_iter_test:
  assumes a_atomic[simp]: "a = (atomic r1)"
  assumes b_atomic[simp]: "b = (atomic r2)"
  assumes d_atomic[simp]: "d = (atomic r4)"
  shows "a\<^sup>\<omega>;(\<tau> p1) \<otimes> b\<^sup>\<star>;d\<^sup>\<omega>;(\<tau> p2) = (a\<otimes>b)\<^sup>\<star>;(a\<otimes>d)\<^sup>\<omega>;(\<tau> (p1 \<sqinter> p2))"
proof -
  have "a\<^sup>\<omega>;(\<tau> p1) \<otimes> b\<^sup>\<star>;d\<^sup>\<omega>;(\<tau> p2) = a\<^sup>\<star>;a\<^sup>\<omega>;(\<tau> p1) \<otimes> b\<^sup>\<star>;d\<^sup>\<omega>;(\<tau> p2)"
    by (simp add: fiter_seq_iter)
  also have "... = (a\<otimes>b)\<^sup>\<star>;((a\<otimes>b)\<^sup>\<star> \<squnion> (a\<otimes>d)\<^sup>\<star>);(a\<otimes>d)\<^sup>\<omega>;(\<tau> (p1 \<sqinter> p2))"
    using atomic_fiter_iter_test_sync_fiter_iter_test by simp
  also have "... = (a\<otimes>b)\<^sup>\<star>;(a\<otimes>d)\<^sup>\<omega>;(\<tau> (p1 \<sqinter> p2))"
    by (simp add: fiter_seq_iter nondet_seq_distrib seq_assoc seq_nondet_distrib)
  finally show ?thesis . 
qed
end

locale atomic_sync_command_with_tests_aborting = atomic_sync_command_with_tests 
                                                 + sync_command_with_tests_aborting
begin

lemma atomic_pre_sync_test_pre:
  shows "(atomic r);c \<otimes> (\<tau> p);d = (\<tau> p);((atomic r);c \<otimes> d)"
proof -
  have "(atomic r);c \<otimes> \<bottom> = \<bottom>"
    by (metis sync_commute test.hom_bot test_sync_atomic_pre)
  then show ?thesis using nonaborting_sync_test_pre_generic by metis
qed

lemma assert_distrib: "\<lbrace>p\<rbrace>;(c \<otimes> d) = c \<otimes> (\<lbrace>p\<rbrace>;d)"
proof -
  have "(c \<otimes> \<lbrace>p\<rbrace>;d) = ((\<tau> p);(c \<otimes> \<lbrace>p\<rbrace>;d) \<squnion> (\<tau>(-p));(c \<otimes> \<lbrace>p\<rbrace>;d))"
    by (metis nondet_seq_distrib seq_nil_left test.hom_not test_nondet_compl)
  also have "\<dots> = ((\<tau> p);c \<otimes> (\<tau> p);\<lbrace>p\<rbrace>;d) \<squnion> (\<tau>(-p);c \<otimes> \<tau>(-p);\<lbrace>p\<rbrace>;d)"
    by (simp add: seq_assoc test_sync_distrib)
  also have "\<dots> = ((\<tau> p);c \<otimes> (\<tau> p);d) \<squnion> (\<tau>(-p);c \<otimes> \<tau>(-p);\<lbrace>-p\<rbrace>;\<lbrace>p\<rbrace>;d)"
    using test_seq_assert by simp
  also have "\<dots> = (\<tau> p);(c \<otimes> d) \<squnion> (\<tau>(-p);c \<otimes> \<tau>(-p);\<top>)"
    using assert_seq_compl assert_seq_assert seq_assoc test_sync_distrib by force
  also have "\<dots> = (\<tau> p);(c \<otimes> d) \<squnion> \<tau>(-p);\<top>"
    by (metis sync_abort_left local.sync_commute test_sync_distrib)
  also have "\<dots> = (\<tau> p);(c \<otimes> d) \<squnion> \<tau>(-p);\<top>;(c \<otimes> d)"
    by (simp add: seq_assoc)
  finally show ?thesis
    by (simp add: assert_def nondet_seq_distrib) 
qed

end

end