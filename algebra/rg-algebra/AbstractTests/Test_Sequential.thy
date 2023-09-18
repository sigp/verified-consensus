section \<open>Test operator combined with sequential composition.\<close>

theory Test_Sequential
imports                       
  "../AbstractTests/Abstract_Test"
  "../General/Sequential"
begin

locale test_sequential_pre = seq + abstract_test_commands +
  constrains test :: "'test :: complete_boolean_algebra \<Rightarrow> 'a::refinement_lattice"
  constrains seq :: "'a \<Rightarrow> 'a  \<Rightarrow> 'a"
begin

(* When we combine sequential composition and tests, we redefine nil in terms of a test. *)
definition nil :: "'a"
  where "nil \<equiv> \<tau> top"

lemma test_top:
  shows "\<tau> top = nil"
  using nil_def by simp

end

locale test_sequential =
  test_sequential_pre + seq_distrib seq nil +
  assumes test_nondet_distrib_weak: "((\<tau> p); c) \<squnion> ((\<tau> p); d) \<ge> (\<tau> p); (c \<squnion> d)" 
  assumes test_inf_interchange: "((\<tau> p); c) \<sqinter> ((\<tau> q); d) = ((\<tau> p) \<sqinter> (\<tau> q)); (c \<sqinter> d)"
begin

lemma test_nondet_compl: "(\<tau> p) \<squnion> test.negate(\<tau> p) = nil" 
  by (metis test_top sup_compl_top test.hom_not test.hom_sup)

lemma nil_ref_test: "nil \<ge> \<tau> p" using test_top test.hom_mono
  by (metis top_greatest)

lemma nil_inf_test: "nil \<sqinter> (\<tau> p) = (\<tau> p)" by (simp add: inf.absorb2 nil_ref_test)

lemma test_inf_eq_seq: 
  shows "(\<tau> p)\<sqinter>(\<tau> q) = (\<tau> p);(\<tau> q)"
proof (rule antisym)
  show "(\<tau> p)\<sqinter>(\<tau> q) \<ge> (\<tau> p);(\<tau> q)"
  proof -
    have p1: "(\<tau> p) \<ge> (\<tau> p);(\<tau> q)" using seq_nil_right seq_mono_right nil_ref_test by fastforce 
    also have p2: "(\<tau> q) = nil;(\<tau> q)" using seq_nil_right seq_nil_left by metis
    also have p3: "(\<tau> q) \<ge> (\<tau> p);(\<tau> q)" using p2 nil_ref_test by (metis seq_mono_left)
    also have p4: "(\<tau> p) \<sqinter> (\<tau> q) \<ge> (\<tau> p);(\<tau> q)" using p1 p3 by (simp add: le_sup_iff)
    thus ?thesis .
  qed
next
  show "(\<tau> p);(\<tau> q) \<ge> (\<tau> p) \<sqinter> (\<tau> q)" 
  proof -
    have a: "(\<tau> p);(\<tau> q) = ((\<tau> p) \<sqinter> (\<tau> top)); ((\<tau> q) \<sqinter> (\<tau> top))"
      by (metis inf_top.right_neutral test.hom_inf)
    then have "\<dots> = (\<tau> p) \<sqinter> (\<tau> q)" using test_inf_interchange
      by (metis inf_sup_aci(1) seq_nil_left seq_nil_right test_top)
    thus ?thesis by (simp add: a) 
  qed
qed

lemma test_seq_test:
  shows "(\<tau> p);(\<tau> q) = \<tau>(p \<sqinter> q)"
  by (simp add: test_inf_eq_seq)

(*test_par_top*)
lemma test_seq_magic: "\<tau> p; \<bottom> = \<bottom>"
  by (metis inf.absorb2 test.hom_bot bot_least test_inf_eq_seq)

lemma test_nondet_distrib: "(\<tau> p);(c \<squnion> d) = (\<tau> p); c \<squnion> (\<tau> p); d"
   using test_nondet_distrib_weak seq_nondet_distrib_weak by (simp add: eq_iff)

lemma test_seq_idem: "\<tau> p = \<tau> p ; \<tau> p" 
  using test_inf_eq_seq by (metis inf.idem)

lemma test_seq_commute: "\<tau> p ; \<tau> q = \<tau> q ; \<tau> p"
  by (metis inf_sup_aci(1) test_inf_eq_seq)

lemma test_seq_compl: "\<tau> p ; \<tau>(-p) = \<bottom>"
  by (simp add: test_seq_test)

lemma test_compl_seq: "\<tau>(-p) ; \<tau> p = \<bottom>"
  using test_seq_compl test_seq_commute by presburger 

lemma test_inf_interchange2: "(\<tau> p);d \<sqinter> c = (\<tau> p);(d \<sqinter> c)"
proof -
  have a: "(\<tau> p);d \<sqinter> c = (\<tau> p);d \<sqinter> ((\<tau> p);c \<squnion> (\<tau> (-p));c)"
    by (metis nondet_seq_distrib seq_nil_left test.hom_not test_nondet_compl)
  then have b: "\<dots> = ((\<tau> p);d \<sqinter> (\<tau> p);c) \<squnion> ((\<tau> p);d \<sqinter> (\<tau> (-p));c)"
    by (simp add: inf_sup_distrib1)
  then have c: "\<dots> = (\<tau> p);(d \<sqinter> c) \<squnion> ((\<tau> p) \<sqinter> (\<tau> (-p)));(d \<sqinter> c)"
    by (metis inf.idem test_inf_interchange)
  thus ?thesis
    by (metis a b nondet_seq_distrib sup_inf_absorb) 
qed

lemma test_absorb: 
  assumes "p \<le> q" 
  shows "\<tau> p \<squnion> \<tau> q ; \<top> = \<tau> q ; \<top>"
proof -
  have "\<tau> p ; \<tau> q = \<tau> p"
    by (metis assms le_iff_inf test_inf_eq_seq test.hom_inf)
  then show ?thesis
    by (meson assms sup_absorb2 order_trans seq_abort_right test.hom_mono)
qed

lemma test_seq_refine: "(c \<ge> \<tau> p ; d) = (\<tau> p ;c \<ge> \<tau> p ; d)"
proof -
  have "\<And>a b. nil ; a \<ge> \<tau> b ; a"
    by (meson seq_mono_left nil_ref_test)
  then show ?thesis
    by (metis dual_order.trans seq_assoc seq_mono_right seq_nil_left test_seq_idem)
qed 

end

end