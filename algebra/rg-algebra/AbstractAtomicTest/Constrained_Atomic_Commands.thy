section \<open>Atomic commands constrained to the algebra of sets and relations.\<close>

theory Constrained_Atomic_Commands
imports
  "../General/Relations"
  "ParallelFlip"
begin


locale constrained_atomic_pre = pgm_env_commands  +
(* Constrains atomic steps and derived commands to operate on relations of two states.
   Tests are constrained to operate only on sets of states. *)
  constrains test :: "'state :: type set \<Rightarrow> 'a"
  constrains pgm:: "'state rel \<Rightarrow> 'a" 
  constrains env:: "'state rel \<Rightarrow> 'a" 

  
locale constrained_atomic = constrained_atomic_pre  +
  (* Introduces the manner in which tests can be moved and combined with pgm/env steps. *)
  (* Based on "Reasoning about sequential code under interference from concurrent
     processes" by Ian J. Hayes. *)
  assumes pgm_test_pre: "\<tau>(p);\<pi>(r) = \<pi>(p \<triangleleft> r)"  (* Equation 3. *)
  assumes env_test_pre: "\<tau>(p);\<epsilon>(r) = \<epsilon>(p \<triangleleft> r)"  (* Equation 4. *)
  assumes pgm_test_post: "\<pi>(r \<triangleright> p);\<tau>(p) = \<pi>(r \<triangleright> p)"  (* Equation 5. *)
  assumes env_test_post: "\<epsilon>(r \<triangleright> p);\<tau>(p) = \<epsilon>(r \<triangleright> p)"  (* Equation 6. *)
  constrains test :: "'state :: type set \<Rightarrow> 'a"
  constrains pgm:: "'state rel \<Rightarrow> 'a" 
  constrains env:: "'state rel \<Rightarrow> 'a" 
begin

definition opt :: "'state rel \<Rightarrow> 'a"
  where "opt q \<equiv> \<pi>(q) \<squnion> \<tau>({\<sigma>. (\<sigma>,\<sigma>)\<in>q })"

(* Lemma 1. This is a generalisation of the version in the paper to 
   allow the final state set to be different from the initial state set. *)
lemma test_pre_post:
  assumes c_ref: "c;\<tau>(pf) \<ge> \<tau>(p);c"
  shows "\<tau>(p);c;\<tau>(pf) = \<tau>(p);c"
proof (rule antisym)
  have "\<tau>(p);c;\<tau>(pf) \<ge> \<tau>(p);\<tau>(p);c" (is "_ \<ge> ?rhs") using c_ref seq_mono_right seq_assoc by simp
  also have "?rhs = \<tau>(p);c" using test_seq_idem by simp
  finally show "\<tau>(p);c;\<tau>(pf) \<ge> \<tau>(p);c" .
next
  have "\<tau>(p);c = \<tau>(p);c;nil" by simp
  also have "... \<ge> \<tau>(p);c;\<tau>(pf)" using seq_mono_right nil_ref_test by blast
  finally show "\<tau>(p);c \<ge> \<tau>(p);c;\<tau>(pf)" .  
qed
  
(* Lemma 2 - pgm steps. *)    
lemma pgm_test_ref: 
  assumes p0_implies_p1: "(r `` p0) \<subseteq> p1"
  shows "\<pi>(r);\<tau>(p1) \<ge> \<tau>(p0);\<pi>(r)"
proof -
  have a1: "p0 \<triangleleft> r = (p0 \<triangleleft> r) \<triangleright> p1" 
    unfolding restrict_domain_def restrict_range_def
    using p0_implies_p1 by blast
  have "\<pi>(r);\<tau>(p1) = nil;\<pi>(r);\<tau>(p1)" by simp
  also have "... \<ge> \<tau>(p0);\<pi>(r);\<tau>(p1)" (is "_ \<ge> ?rhs") using seq_mono_left nil_ref_test by blast
  also have "?rhs = \<pi>(p0 \<triangleleft> r);\<tau>(p1)" using pgm_test_pre by simp
  also have "... = \<pi>((p0 \<triangleleft> r) \<triangleright> p1);\<tau>(p1)" using a1 by simp
  also have "... = \<pi>((p0 \<triangleleft> r) \<triangleright> p1)" using pgm_test_post by blast
  also have "... = \<pi>(p0 \<triangleleft> r)" using a1 by simp
  also have "... = \<tau>(p0);\<pi>(r)" using pgm_test_pre by simp
  finally show ?thesis .    
qed

(* Lemma 2 - env steps. This version is a generalisation of the version
   in the paper. *)
lemma env_test_ref: 
  assumes p0_implies_p1: "(r `` p0) \<subseteq> p1"
  shows "\<epsilon>(r);\<tau>(p1) \<ge> \<tau>(p0);\<epsilon>(r)"
proof -
  have a1: "p0 \<triangleleft> r = (p0 \<triangleleft> r) \<triangleright> p1" 
    unfolding restrict_domain_def restrict_range_def
    using p0_implies_p1 by blast
  have "\<epsilon>(r);\<tau>(p1) = nil;\<epsilon>(r);\<tau>(p1)" by simp
  also have "... \<ge> \<tau>(p0);\<epsilon>(r);\<tau>(p1)" (is "_ \<ge> ?rhs") using seq_mono_left nil_ref_test by blast
  also have "?rhs = \<epsilon>(p0 \<triangleleft> r);\<tau>(p1)" using env_test_pre by simp
  also have "... = \<epsilon>((p0 \<triangleleft> r) \<triangleright> p1);\<tau>(p1)" using a1 by simp
  also have "... = \<epsilon>((p0 \<triangleleft> r) \<triangleright> p1)" using env_test_post by blast
  also have "... = \<epsilon>(p0 \<triangleleft> r)" using a1 by simp
  also have "... = \<tau>(p0);\<epsilon>(r)" using env_test_pre by simp
  finally show ?thesis .    
qed

(* Lemma 3 - finite or infinite iteration. *)
lemma iter_test_pre:
  assumes c_ref: "c;\<tau>(p) \<ge> \<tau>(p);c"
  shows "c\<^sup>\<omega>;\<tau>(p) \<ge> \<tau>(p);c\<^sup>\<omega>"
proof -
  have "\<tau>(p) \<squnion> c;\<tau>(p);c\<^sup>\<omega> \<ge> \<tau>(p) \<squnion> \<tau>(p);c;c\<^sup>\<omega>" (is "_ \<ge> ?rhs")
    using c_ref seq_mono_left seq_assoc sup_mono by blast
  also have "?rhs = \<tau>(p);(nil \<squnion> c;c\<^sup>\<omega>)"
    by (simp add: par.seq_nondet_distrib seq_assoc)
  also have "... = \<tau>(p);c\<^sup>\<omega>"
    using iter_unfold by simp
  finally have "\<tau>(p) \<squnion> c;(\<tau>(p);c\<^sup>\<omega>) \<ge> \<tau>(p);c\<^sup>\<omega>" 
    using seq_assoc by simp
  then show ?thesis
    using par.iter_induct by blast
qed
  
(* Helper for the lemma below, but it stands well by itself. *)
lemma power_test_pre: 
  assumes c_ref: "c;\<tau>(p) \<ge> \<tau>(p);c"
  shows "(c \<^sup>;^ i);\<tau>(p) \<ge> \<tau>(p);(c \<^sup>;^ i)"
proof (induction i)
  case zero: 0
  show "(c \<^sup>;^ 0);\<tau>(p) \<ge> \<tau>(p);(c \<^sup>;^ 0)" by simp
next 
  case more: (Suc n)
  have "(c \<^sup>;^ (Suc n));\<tau>(p) = (c \<^sup>;^ n);c;\<tau>(p)"
    using seq_power_front by simp
  also have "... \<ge> (c \<^sup>;^ n);\<tau>(p);c" (is "_ \<ge> ?rhs")
    using c_ref seq_mono_right seq_assoc by simp
  also have "?rhs \<ge> \<tau>(p);(c \<^sup>;^ n);c" (is "_ \<ge> ?rhs")
    using more seq_mono_left by simp
  also have "?rhs = \<tau>(p);(c \<^sup>;^ (Suc n))"
    using seq_power_front seq_assoc by simp
  finally show ?case .
qed

(* Lemma 3 - finite iteration. *)
lemma fiter_test_pre:
  assumes c_ref: "c;\<tau>(p) \<ge> \<tau>(p);c"
  shows "c\<^sup>\<star>;\<tau>(p) \<ge> \<tau>(p);c\<^sup>\<star>"
proof -
  (* A different proof path has been used than in the paper
     due the lack of the specific finite iteration induction
     rule. *)
  have "c\<^sup>\<star>;\<tau>(p) = (\<Squnion>i::nat. (c \<^sup>;^ i);\<tau>(p))"
    using par.fiter_seq_choice Nondet_seq_distrib by (simp add:image_image)
  also have "... \<ge> (\<Squnion>i::nat. \<tau>(p);(c \<^sup>;^ i))" (is "_ \<ge> ?rhs")
    by (simp add: power_test_pre SUP_subset_mono c_ref) 
  also have "?rhs = \<tau>(p);c\<^sup>\<star>"
    using par.seq_Nondet_distrib par.fiter_seq_choice by (simp add:image_image)
  finally show ?thesis .
qed

(* Useful now that we are constrained to sets. *)
lemma Nondet_test_nil: "(\<Squnion>s. \<tau>({s})) = nil"
proof -
  have "(\<Squnion>s. \<tau>({s})) = (\<Squnion>x\<in>((\<lambda>x. {x}) ` (UNIV::'state set)). \<tau>(x))"    
    by (simp add:image_comp)
  also have "... = \<tau>(\<Squnion>((\<lambda>x. {x}) ` (UNIV::'state set)))"
    using test_Sup by metis
  also have "... = \<tau>(\<top>)"
  proof -
    have "(UNIV) = \<Squnion>((\<lambda>x. {x}) ` (UNIV))"
      by blast
    then show ?thesis by simp
  qed
  also have "... = nil"
    using test_top by simp
  finally show ?thesis .
qed

lemma test_restricts_Nondet: "\<tau>(A);(\<Squnion>s. \<tau>({s});f s) = (\<Squnion>s\<in>A. \<tau>({s});f s)"
proof -
  have "\<tau>(A);(\<Squnion>s. (\<tau>({s});f s)) = (\<Squnion>s. \<tau>(A);(\<tau>({s});f s))"
    by (simp add: par.seq_NONDET_distrib_UNIV)
  also have "... = ((\<Squnion>s\<in>A. \<tau>(A);(\<tau>({s});f s)) \<squnion> (\<Squnion>s\<in>(-A). \<tau>(A);(\<tau>({s});f s)))"
    by (metis (no_types, lifting) SUP_union sup_compl_top)
  also have "... = ((\<Squnion>s\<in>A. (\<tau>(A \<inter> {s});f s)) \<squnion>  (\<Squnion>s\<in>(-A). \<tau>(A \<inter> {s});f s))"
    using seq_assoc test_inf_eq_seq test.hom_inf by presburger
  also have "... = (\<Squnion>s\<in>A. (\<tau>({s});f s))"
    by simp
  finally show ?thesis .
qed

lemma test_Nondet_product_helper1:
  "(\<Squnion>(a::'d). ((x::'d\<Rightarrow>'d\<Rightarrow>'a) s a)) = (\<Squnion>(a::'d)\<in>(UNIV-{s}). (x s a)) \<squnion> (x s s)"
  by (metis SUP_insert UNIV_I inf_sup_aci(5) insert_Diff)
  
lemma test_Nondet_product_helper2:
  "(\<Squnion>a. (\<tau>({s} \<sqinter> {a}); (x s a))) = \<tau>({s}); (x s s)"
proof -
  (* Split supremum over all a into supremum over (all a except s) and s.*)
  have a1: "(\<Squnion>a. (\<tau>({s} \<sqinter> {a}); (x s a)))
      = (\<Squnion>a\<in>(UNIV-{s}). (\<tau>({s} \<sqinter> {a}); (x s a))) \<squnion> (\<tau>({s} \<sqinter> {s});(x s s))"
    by (meson test_Nondet_product_helper1)
  (* Show LHS is magic, because test always fails. *)
  have a2: "(\<Squnion>a\<in>(UNIV-{s}). (\<tau>({s} \<sqinter> {a}); (x s a))) = \<bottom>" by simp
  then have "(\<Squnion>a. (\<tau>({s} \<sqinter> {a}); (x s a))) = \<tau>({s});(x s s)"
    using a1 a2 by simp
  then show ?thesis by simp
qed

lemma test_Nondet_conj_product:
  assumes x_nonabort: "\<forall>s. chaos \<ge> x s"
  assumes y_nonabort: "\<forall>s. chaos \<ge> y s"    
  shows "(\<Squnion>s1. (\<tau>({s1}); (x s1))) \<iinter> (\<Squnion>s2. (\<tau>({s2}); (y s2)))
       = (\<Squnion>s.  (\<tau>({s}); ((x s) \<iinter> (y s))))"  
proof - 
  (* Distribute RHS infimum into infimum over s1. *)
  have "(\<Squnion>s1. \<tau>({s1}); x s1) \<iinter> (\<Squnion>s2. \<tau>({s2}); y s2)
      = (\<Squnion>s1. ((\<tau>({s1}); x s1) \<iinter> (\<Squnion>s2. \<tau>({s2}); y s2)))"
    using conj.Nondet_sync_distrib by (simp add:image_image)
  (* Distribute into inner infimum. *)
  also have "... = (\<Squnion>s1. (\<Squnion>s2. ((\<tau>({s1}); (x s1)) \<iinter> (\<tau>({s2}); (y s2)))))"
    using conj.sync_Nondet_distrib by (simp add:image_image)
  (* Simplify terms. *)
  also have "... = (\<Squnion>s1. (\<Squnion>s2. (\<tau>({s1} \<sqinter> {s2}); ((x s1) \<iinter> (y s2)))))"
    using x_nonabort y_nonabort conj.test_nonaborting_sync_test_nonaborting by simp
  (* Simplify using fact that inner term is magic whenever s1 is not s2. *)
  also have "... = (\<Squnion>s. (\<tau>({s}); ((x s) \<iinter> (y s))))"
    using test_Nondet_product_helper2 by meson
  finally show ?thesis by simp
qed

lemma test_Nondet_par_product:
  assumes x_nonabort: "\<forall>s. chaos \<ge> x s"
  assumes y_nonabort: "\<forall>s. chaos \<ge> y s"    
  shows "(\<Squnion>s1. (\<tau>({s1}); (x s1))) \<parallel> (\<Squnion>s2. (\<tau>({s2}); (y s2)))
       = (\<Squnion>s.  (\<tau>({s}); ((x s) \<parallel> (y s))))"  
proof - 
  (* Distribute RHS infimum into infimum over s1. *)
  have "(\<Squnion>s1. \<tau>({s1}); x s1) \<parallel> (\<Squnion>s2. \<tau>({s2}); y s2)
      = (\<Squnion>s1. ((\<tau>({s1}); x s1) \<parallel> (\<Squnion>s2. \<tau>({s2}); y s2)))"
    using par.Nondet_sync_distrib by (simp add:image_image)
  (* Distribute into inner infimum. *)
  also have "... = (\<Squnion>s1. (\<Squnion>s2. ((\<tau>({s1}); (x s1)) \<parallel> (\<tau>({s2}); (y s2)))))"
    using par.sync_Nondet_distrib by (simp add:image_image)
  (* Simplify terms. *)
  also have "... = (\<Squnion>s1. (\<Squnion>s2. (\<tau>({s1} \<sqinter> {s2}); ((x s1) \<parallel> (y s2)))))"
    using x_nonabort y_nonabort par.test_nonaborting_sync_test_nonaborting by simp
  (* Simplify using fact that inner term is magic whenever s1 is not s2. *)
  also have "... = (\<Squnion>s. (\<tau>({s}); ((x s) \<parallel> (y s))))"
    using test_Nondet_product_helper2 by meson
  finally show ?thesis by simp
qed

lemma opt_pre_internalise:
  shows "\<tau>(p);opt(q) = opt(p \<triangleleft> q)"
proof -
  have a1: "p \<inter> {\<sigma>. (\<sigma>,\<sigma>)\<in>q } = {\<sigma>. (\<sigma>,\<sigma>)\<in>(p \<triangleleft> q)}"
    unfolding restrict_domain_def by auto
  have "\<tau>(p);opt(q) = \<tau>(p);\<pi>(q) \<squnion> \<tau>(p);\<tau>({\<sigma>. (\<sigma>,\<sigma>)\<in>q })"
    unfolding opt_def using par.seq_nondet_distrib by simp
  also have "... = \<pi>(p \<triangleleft> q) \<squnion> \<tau>({\<sigma>. (\<sigma>,\<sigma>)\<in>(p \<triangleleft> q)})"
    using pgm_test_pre test_seq_test a1 by metis
  finally show ?thesis using opt_def by simp
qed

lemma opt_strengthen:
  assumes subset: "q2 \<subseteq> q1"
  shows "opt(q1) \<ge> opt(q2)"
proof -
  have a1: "{\<sigma>. (\<sigma>,\<sigma>)\<in>q2 }\<subseteq>{\<sigma>. (\<sigma>,\<sigma>)\<in>q1}" using subset by auto
  have "\<pi>(q1) \<squnion> \<tau>({\<sigma>. (\<sigma>,\<sigma>)\<in>q1 }) \<ge>  \<pi>(q2) \<squnion> \<tau>({\<sigma>. (\<sigma>,\<sigma>)\<in>q2 })"
    using subset a1 by (meson sup_mono pgm.hom_iso test.hom_iso)
  then show ?thesis unfolding opt_def by simp
qed

lemma opt_strengthen_under_pre:
  assumes subset: "p \<triangleleft> q2 \<subseteq> q1"
  shows "\<lbrace>p\<rbrace>;opt(q1) \<ge> \<lbrace>p\<rbrace>;opt(q2)"
  using opt_pre_internalise opt_strengthen assert_galois_test
        assert_redundant subset by auto 



lemma general_atomic_test_post: "\<alpha>(r \<triangleright> p) = \<alpha>(r \<triangleright> p);\<tau>(p)"
  using env_test_post pgm_test_post general_atomic_def nondet_seq_distrib by simp 

lemma atomic_pull_test: "\<tau>(p);\<alpha>(r) = \<alpha>(p \<triangleleft> UNIV \<inter> r)"
  by (metis general_atomic_def env.hom_inf env_test_pre inf_top.left_neutral par.seq_nondet_distrib pgm.hom_inf pgm_test_pre test_inf_interchange2)

end

end

