section \<open>The assert command\<close>

theory Assertions
imports
  Test_Sequential
begin

term test_sequential
                             
locale assertions = test_sequential _ _
 (* for test :: "'b::complete_boolean_algebra \<Rightarrow> 'a::refinement_lattice" ("\<tau>")
  and  seq  :: "'a :: refinement_lattice \<Rightarrow> 'a \<Rightarrow> 'a" *)
begin

definition assert :: "'b::complete_boolean_algebra\<Rightarrow>'a::refinement_lattice" ("\<lbrace>_\<rbrace>" 98)
  where "assert p \<equiv> (\<tau> p) \<squnion> (test.negate (\<tau> p));\<top>"

lemma assert_inter: "\<lbrace>p\<rbrace> \<squnion> \<lbrace>q\<rbrace> = \<lbrace>p \<sqinter> q\<rbrace>"
proof -
  have p_minus_q: "p-q \<le> -(p \<sqinter> q)" by (simp add: diff_eq le_infI2) 
  have q_minus_p: "q-p \<le> -(p \<sqinter> q)" by (simp add: diff_eq le_infI2) 
  have "\<lbrace>p\<rbrace> \<squnion> \<lbrace>q\<rbrace> = (\<tau> p \<squnion> test.negate(\<tau> p);\<top>) \<squnion> (\<tau> q \<squnion> test.negate(\<tau> q);\<top>)" 
      by (simp add: assert_def)
  also have "... = (\<tau> p \<squnion> \<tau> q) \<squnion> (test.negate(\<tau> p);\<top> \<squnion> test.negate(\<tau> q);\<top>)"
      by (simp add: sup_assoc sup_left_commute) 
    also have "... = \<tau>(p \<squnion> q) \<squnion> \<tau>(-p \<squnion> -q); \<top>" 
      by (simp add: nondet_seq_distrib)
  also have "... = \<tau>(p \<sqinter> q) \<squnion> \<tau>(p-q) \<squnion> \<tau>(q-p) \<squnion> \<tau>(-(p \<sqinter> q));\<top>"
    by (metis (no_types) compl_sup diff_eq double_compl inf_compl_bot 
        inf_sup_distrib1 sup_bot.right_neutral test.hom_sup)
  also have "... = \<tau>(p \<sqinter> q) \<squnion> \<tau>(-(p \<sqinter> q));\<top>" 
      by (metis p_minus_q q_minus_p test_absorb sup_assoc)
  finally show ?thesis by (metis assert_def test.hom_not) 
qed

lemma assert_inf: "\<lbrace>p\<rbrace>;c \<sqinter> \<lbrace>q\<rbrace>;c = \<lbrace>p \<squnion> q\<rbrace>;c"
proof -
  have "\<lbrace>p\<rbrace>;c \<sqinter> \<lbrace>q\<rbrace>;c = (\<tau> p;c \<squnion> \<tau>(-p);\<top>) \<sqinter> (\<tau> q;c \<squnion> \<tau>(-q);\<top>)"
    by (simp add: assert_def nondet_seq_distrib seq_assoc)
  also have "... = (\<tau> p;c \<sqinter> \<tau> q;c) \<squnion> (\<tau>(-p);\<top> \<sqinter> \<tau> q;c) 
                    \<squnion> (\<tau> p;c \<sqinter> (\<tau>(-q));\<top>) \<squnion> (\<tau>(-p);\<top> \<sqinter> \<tau>(-q);\<top>)"
    by (simp add: sup.assoc inf_sup_distrib1 inf_sup_distrib2)
  also have "... = \<tau>(p \<sqinter> q);c \<squnion> \<tau>(-p \<sqinter> q);c \<squnion> \<tau>(p \<sqinter> -q);c \<squnion> \<tau>(-p \<sqinter> -q);\<top>"
    by (simp add: test_inf_interchange)
  also have "... = \<tau>(p \<squnion> q);c \<squnion> \<tau>(-(p \<squnion> q));\<top>"
  proof -
    have "p \<squnion> q = (p \<sqinter> q) \<squnion> (-p \<sqinter> q) \<squnion> (p \<sqinter> -q)"
      by (metis inf_sup_distrib2 inf_top.left_neutral inf_top.right_neutral sup_commute
                sup_compl_top sup_inf_distrib1) 
    then show ?thesis by (metis nondet_seq_distrib compl_sup test.hom_sup)
  qed
  finally show ?thesis by (metis assert_def test.hom_not nondet_seq_distrib seq_assoc seq_abort)
qed 

lemma assert_seq_assert: "\<lbrace>p\<rbrace>;\<lbrace>q\<rbrace> = \<lbrace>p \<sqinter> q\<rbrace>"
proof -
  have "\<lbrace>p\<rbrace>;\<lbrace>q\<rbrace> = (\<tau> p \<squnion> \<tau>(-p);\<top>);(\<tau> q \<squnion> \<tau>(-q);\<top>)" by (simp add: assert_def)
  also have "... = \<tau> p;\<tau> q \<squnion> \<tau> p;\<tau>(-q);\<top> \<squnion> (\<tau>(-p);\<top>)" 
    by (simp add: nondet_seq_distrib test_nondet_distrib seq_assoc) 
  also have "... = \<tau> (p \<sqinter> q) \<squnion> \<tau>(p \<sqinter> -q);\<top> \<squnion> (\<tau>(-p);\<top>)" using test_inf_eq_seq test.hom_inf by metis
  also have "... = \<tau> (p \<sqinter> q) \<squnion> \<tau>((p \<sqinter> -q) \<squnion> -p);\<top>" by (simp add: sup_assoc nondet_seq_distrib)
  also have "... = \<tau> (p \<sqinter> q) \<squnion> \<tau>(-(p \<sqinter> q));\<top>"  by (simp add: sup_commute sup_inf_distrib1)
  also have "... = \<lbrace>p \<sqinter> q\<rbrace>" by (metis assert_def test.hom_not)
  finally show ?thesis .
qed

lemma assert_seq_test: "\<lbrace>p\<rbrace>;(\<tau> p) = \<lbrace>p\<rbrace>" 
proof -
   have "(\<tau> p \<squnion> test.negate (\<tau> p);\<top>) ; \<tau> p = \<tau> p ; \<tau> p \<squnion> test.negate(\<tau> p);\<top>;\<tau> p" 
      by (simp add: nondet_seq_distrib)
   then show ?thesis using assert_def test_inf_eq_seq seq_assoc seq_abort by (metis test_seq_idem) 
qed

lemma test_seq_assert: "(\<tau> p);\<lbrace>p\<rbrace> = \<tau> p"
  by (metis (no_types, lifting)  test_nondet_compl assert_def  
    test_nondet_distrib semigroup.assoc seq.semigroup_axioms seq_magic_left 
    test_seq_compl test.hom_not test_seq_idem seq_nil_right)

lemma assert_seq_self: "\<lbrace>p\<rbrace>;\<lbrace>p\<rbrace> = \<lbrace>p\<rbrace>"
  using assert_seq_assert by simp

lemma assert_seq_compl: "\<lbrace>p\<rbrace>;\<lbrace>-p\<rbrace> = \<top>"
  by (metis assert_seq_assert assert_def compl_bot_eq sup_top_right inf_compl_bot
            seq_nil_left test.hom_not test_top)

lemma assert_top: "\<lbrace>\<top>\<rbrace> = nil"
   by (metis (no_types) compl_top_eq seq_magic_left assert_def 
                         test.hom_bot test.hom_not test_nondet_compl) 

lemma assert_bot: "\<lbrace>\<bottom>\<rbrace> = \<top>"
  by (metis assert_top assert_seq_compl compl_bot_eq seq.right_neutral) 

lemma assert_redundant: "\<lbrace>p\<rbrace>;c \<ge> \<lbrace>p\<rbrace>;d \<longleftrightarrow> \<lbrace>p\<rbrace>;c \<ge> d"
proof
  assume a: "\<lbrace>p\<rbrace>;c \<ge> \<lbrace>p\<rbrace>;d"
  show "\<lbrace>p\<rbrace>; c \<ge> d"
  proof -
    have "\<forall>a. nil = \<tau> a \<squnion> \<tau> (- a)" using test_nondet_compl by auto
    then show ?thesis
      by (metis a assert_inf assert_top le_infE order_refl order_trans seq_nil_left sup_top_right)
  qed
  next
    assume b: "\<lbrace>p\<rbrace>;c >= d"
    show "\<lbrace>p\<rbrace>; c \<ge> \<lbrace>p\<rbrace>;d"
    by (metis b assert_seq_self seq_assoc seq_mono_right)
qed 


lemma assert_galois_test: "(\<lbrace>p\<rbrace>;c \<ge> d) \<longleftrightarrow> (c \<ge> \<tau> p;d)" 
proof
  assume a: "\<lbrace>p\<rbrace>;c \<ge> d"
  show "c \<ge> \<tau> p;d"
  proof -
    have a1: "\<lbrace>p\<rbrace>;c = (\<tau> p \<squnion> test.negate(\<tau> p);\<top>);c" by (simp add: assert_def) 
    then have a2: "... = (\<tau> p);c \<squnion> test.negate(\<tau> p);\<top>;c" using nondet_seq_distrib by blast
    then have a3: "... = (\<tau> p);c \<squnion> test.negate(\<tau> p);\<top>" by (simp add: seq_assoc) 
    have a4: "(\<tau> p);((\<tau> p);c \<squnion> test.negate(\<tau> p);\<top>) \<ge> (\<tau> p);d" using a a1 a2 a3 seq_mono_right by auto
    have a5: "(\<tau> p);c \<squnion> \<bottom> \<ge> (\<tau> p);d"
       by (metis a4 test_nondet_distrib seq_assoc seq_magic_left test_seq_compl test.hom_not test_seq_idem) 
    have a6: "(\<tau> p);c \<ge> (\<tau> p);d" using a5 by auto
    have a7: "c \<ge> (\<tau> p);c" using seq_mono_left nil_ref_test by fastforce 
    show ?thesis using a7 a6 by (simp add: le_sup_iff sup.orderE)
  qed 
  next
  assume b: "c \<ge> \<tau> p;d"
  show "\<lbrace>p\<rbrace>;c \<ge> d" 
  proof -
    have b1: "\<lbrace>p\<rbrace>;c \<ge> \<lbrace>p\<rbrace>;\<tau> p;d" by (simp add: b seq_assoc seq_mono)
    have b2: "\<lbrace>p\<rbrace>;c \<ge> \<lbrace>p\<rbrace>;d" using assert_seq_test b1 by auto
    show ?thesis using assert_redundant b2 by blast
  qed
qed

lemma assert_nil: "\<lbrace>p\<rbrace> \<ge> nil"  
   by (metis assert_galois_test seq.right_neutral nil_ref_test) 

lemma assert_iso: "p \<le> q \<longleftrightarrow> \<lbrace>p\<rbrace> \<ge> \<lbrace>q\<rbrace>"
proof
  assume a: "\<lbrace>p\<rbrace> \<ge> \<lbrace>q\<rbrace>"
  show "p \<le> q"
  proof -
    have a1: "\<lbrace>p\<rbrace> \<squnion> \<lbrace>q\<rbrace> = \<lbrace>p\<rbrace>"
       by (metis a assert_inter sup.orderE)
    have "\<And>p q. \<tau> p \<ge> \<tau> p \<sqinter> \<tau> q" by simp
    then have "p \<le> p \<sqinter> q" 
      using a1 by (metis assert_galois_test assert_seq_test test_seq_assert inf_sup_ord(1)
                         assert_inter test.hom_iso) 
    then show ?thesis by simp  
  qed
next
  assume b: "p \<le> q"
  show "\<lbrace>p\<rbrace> \<ge> \<lbrace>q\<rbrace>" by (metis assert_inter b inf.orderE sup.order_iff) 
qed

end
end