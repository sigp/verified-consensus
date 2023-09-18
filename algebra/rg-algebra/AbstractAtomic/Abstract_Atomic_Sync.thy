section \<open>Abstract view of atomic commands with a sync operator\<close>

theory Abstract_Atomic_Sync
imports
  "../General/Distributive_Iteration"
  "../General/Abstract_Sync"
  "../General/Abstract_Hom"
begin

(* Join sync and iteration commands with one axiom *)
locale sync_iteration = abstract_sync + iteration_infinite_distrib +
                          iteration_finite_distrib + 
  assumes nil_sync_nil: "nil \<otimes> nil = nil"  

locale atomic = 
  fixes atomic :: "'b::complete_boolean_algebra \<Rightarrow> 'a::refinement_lattice"

locale abstract_atomic_commands = (* liberation_stages + *) atomic + atomic: abstract_hom_commands atomic
begin

abbreviation Atomic where "Atomic \<equiv> atomic.Hom"
lemmas Atomic_def = atomic.Hom_def
end

(* Sync and atomic locales with another axiom. *)         
locale atomic_sync_pre = abstract_sync + atomic + abstract_atomic_commands +
  assumes atomic_sync: "\<forall>p q. \<exists> r . (atomic p) \<otimes> (atomic q) = (atomic r)"   

(* Now put both bits together at once. (This dance is only needed to get isabelle
   to infer the types of all locale parameters correctly.) *)
locale atomic_sync = sync_iteration + atomic_sync_pre +
  assumes atomic_pre_sync_atomic_pre:    "(atomic p);c \<otimes> (atomic q);d = ((atomic p) \<otimes> (atomic q));(c \<otimes> d)"                  
  assumes nil_sync_atomic_pre:     "nil \<otimes> ((atomic p) ; c) = \<bottom>"
  assumes atomic_infiter_sync' : "(atomic p)\<^sup>\<infinity> \<otimes> (atomic q)\<^sup>\<infinity> \<ge> (atomic p \<otimes> atomic q)\<^sup>\<infinity>"
 (* assumes sync_lib: "E\<^sup>C\<^sub>x (c \<otimes> (E\<^sup>C\<^sub>x d)) = (E\<^sup>C\<^sub>x c) \<otimes> (E\<^sup>C\<^sub>x d)" (* 65 *) 
  assumes sync_first: "F\<^sup>C\<^sub>x (c \<otimes> (F\<^sup>C\<^sub>x d)) = (F\<^sup>C\<^sub>x c) \<otimes> (F\<^sup>C\<^sub>x d)" (* 66 *) *)
begin

lemma atomic_infiter_sync [simp]: "(atomic p)\<^sup>\<infinity> \<otimes> (atomic q)\<^sup>\<infinity> = (atomic p \<otimes> atomic q)\<^sup>\<infinity>"
  apply (rule antisym)
   apply (rule infiter_induct)
  apply (metis atomic_pre_sync_atomic_pre infiter_unfold order_refl)
  apply (rule atomic_infiter_sync')
  done

lemma atomic_pre_sync_nil: "((atomic p) ; c) \<otimes> nil = \<bottom>"
  by (simp add: nil_sync_atomic_pre sync_commute)

(* All of (a\<^sup>\<star>, a\<^sup>\<star>;c, a\<^sup>\<omega>, a\<^sup>\<omega>;c, a\<^sup>\<infinity>) \<otimes> nil *)
lemma atomic_fiter_sync_nil:
  assumes a_atomic[simp]: "a = (atomic p)"
  shows "a\<^sup>\<star> \<otimes> nil = nil"
proof -
  have "a\<^sup>\<star> \<otimes> nil = (nil \<squnion> a ; a\<^sup>\<star>) \<otimes> nil" by (metis fiter_unfold)
  also have "... = (nil \<otimes> nil) \<squnion> (a ; a\<^sup>\<star> \<otimes> nil)" by (simp add: nondet_sync_distrib)
  also have "... = nil \<squnion> \<bottom>" by (simp add: nil_sync_nil nil_sync_atomic_pre sync_commute)
  also have "... = nil" by simp
  finally show ?thesis .
qed

lemma atomic_fiter_pre_sync_nil:
  assumes a_atomic[simp]: "a = (atomic p)"
  shows "a\<^sup>\<star> ; c \<otimes> nil =  c \<otimes> nil" 
proof -
  have "a\<^sup>\<star>;c \<otimes> nil = (nil \<squnion> a ; a\<^sup>\<star>);c \<otimes> nil" by (metis fiter_unfold)
  also have "... = (nil;c \<squnion> a ; a\<^sup>\<star>;c) \<otimes> nil" by (simp add: nondet_seq_distrib)
  also have "... = (nil;c \<otimes> nil) \<squnion> (a ; a\<^sup>\<star>;c \<otimes> nil)" by (simp add: nondet_sync_distrib)
  also have "... = (c \<otimes> nil) \<squnion> \<bottom>"
   by (simp add: nil_sync_atomic_pre seq_assoc sync_commute)
  also have "... = c \<otimes> nil" by simp
  finally show ?thesis .
qed

lemma atomic_iter_pre_sync_nil:
  assumes a_atomic[simp]: "a = (atomic p)"
  shows "a\<^sup>\<omega>;c \<otimes> nil = c \<otimes> nil"
proof -
  have "a\<^sup>\<omega>;c \<otimes> nil = (nil \<squnion> a ; a\<^sup>\<omega>);c \<otimes> nil" by (metis iter_unfold)
  also have "... = (nil;c \<otimes> nil) \<squnion> (a ; a\<^sup>\<omega>; c \<otimes> nil)" 
            by (simp add:nondet_seq_distrib nondet_sync_distrib)
  also have "... = (c \<otimes> nil) \<squnion> \<bottom>" by (simp add: nil_sync_atomic_pre seq_assoc sync_commute) 
  also have "... = c \<otimes> nil" by simp
  finally show ?thesis .
qed

lemma atomic_iter_sync_nil:
  assumes a_atomic[simp]: "a = (atomic p)"
  shows "a\<^sup>\<omega> \<otimes> nil = nil"
     by (metis assms atomic_iter_pre_sync_nil nil_sync_nil seq_nil_right) 

lemma atomic_infiter_sync_nil:
  assumes a_atomic[simp]: "a = (atomic p)"
  shows "a\<^sup>\<infinity> \<otimes> nil = \<bottom>"
proof -
  have "a\<^sup>\<infinity> \<otimes> nil = a ; a\<^sup>\<infinity> \<otimes> nil" by (metis infiter_unfold)
  also have "... = \<bottom>" by (simp add: nil_sync_atomic_pre sync_commute)
  finally show ?thesis .
qed

lemma atomic_power_pre_sync_power_pre:
  assumes a_atomic[simp]: "a = (atomic p)"
  assumes b_atomic[simp]: "b = (atomic q)"
  shows "(a \<^sup>;^ i) ; c \<otimes> (b \<^sup>;^ i) ; d = ((a \<otimes> b) \<^sup>;^ i) ; (c \<otimes> d)"
proof (induct i type: nat)
  case 0
  then show ?case by simp 

next
  case (Suc n)
(*then show ?case by (simp add: atomic_parallel_axiom seq_assoc) --"Can be proved without Suc.hyps?"*)
  have "(a \<^sup>;^ Suc n) ; c \<otimes> (b \<^sup>;^ Suc n) ; d = a ; (a \<^sup>;^ n) ; c \<otimes> b ; (b \<^sup>;^ n) ; d" by simp
  also have "... = (a \<otimes> b) ; ((a \<^sup>;^ n) ; c \<otimes> (b \<^sup>;^ n) ; d)" by (simp add: atomic_pre_sync_atomic_pre seq_assoc)
  also have "... = (a \<otimes> b) ; ((a \<otimes> b) \<^sup>;^ n) ; (c \<otimes> d)" by (metis Suc.hyps seq_assoc)
  also have "... = ((a \<otimes> b) \<^sup>;^ Suc n) ; (c \<otimes> d)" by simp
  finally show ?case .
qed


(* helper lemmas *)
lemma atomic_fiter_pre_sync_fiter_pre_ij:
  "(\<Squnion>j\<in>{j. i < j}. (a \<^sup>;^ i) ; c \<otimes> (b \<^sup>;^ j) ; d) =
   (\<Squnion>j\<in>{j. i < j}. (a \<^sup>;^ i) ; c \<otimes> (b \<^sup>;^ i) ; (b \<^sup>;^ (j - i)) ; d)"
     using seq_distrib_right.seq_power_split_less seq_distrib_right_axioms by fastforce
      
lemma atomic_fiter_pre_sync_fiter_pre_ji:
  "(\<Squnion>j\<in>{j. j < i}. (a \<^sup>;^ i) ; c \<otimes> (b \<^sup>;^ j) ; d) =
   (\<Squnion>j\<in>{j. j < i}. (a \<^sup>;^ j) ; (a \<^sup>;^ (i - j)) ; c \<otimes> (b \<^sup>;^ j) ; d)"
      using seq_power_split_less by auto
  
lemma atomic_fiter_pre_sync_fiter_pre:
  assumes a_atomic[simp]: "a = (atomic p)"
  assumes b_atomic[simp]: "b = (atomic q)"
  shows "a\<^sup>\<star> ; c \<otimes> b\<^sup>\<star> ; d = (a \<otimes> b)\<^sup>\<star> ; ((c \<otimes> d) \<squnion> (c \<otimes> b ; b\<^sup>\<star> ; d) \<squnion> (a ; a\<^sup>\<star> ; c \<otimes> d))"
proof -
  have "a\<^sup>\<star> ; c \<otimes> b\<^sup>\<star> ; d = (\<Squnion>i. a \<^sup>;^ i) ; c \<otimes> (\<Squnion>j. b \<^sup>;^ j) ; d"
    by (simp add: fiter_seq_choice)
  also have "... = (\<Squnion>i j. (a \<^sup>;^ i) ; c \<otimes> (b \<^sup>;^ j) ; d)" by (simp add: NONDET_sync_product NONDET_seq_distrib)
  also have "... = (\<Squnion>i. (a \<^sup>;^ i) ; c \<otimes> (b \<^sup>;^ i) ; d) \<squnion>
                   (\<Squnion>i. \<Squnion>j\<in>{j. i < j}. (a \<^sup>;^ i) ; c \<otimes> (b \<^sup>;^ j) ; d) \<squnion>
                   (\<Squnion>i. \<Squnion>j\<in>{j. j < i}. (a \<^sup>;^ i) ; c \<otimes> (b \<^sup>;^ j) ; d)"
    by (simp add: Nondet_Nondet_partition_nat3)
  also have "... = (\<Squnion>i. (a \<^sup>;^ i) ; c \<otimes> (b \<^sup>;^ i) ; d) \<squnion>
                   (\<Squnion>i. \<Squnion>j\<in>{j. i < j}. (a \<^sup>;^ i) ; c \<otimes> (b \<^sup>;^ i) ; (b \<^sup>;^ (j - i)) ; d) \<squnion>
                   (\<Squnion>i. \<Squnion>j\<in>{j. j < i}. (a \<^sup>;^ j) ; (a \<^sup>;^ (i - j)) ; c \<otimes> (b \<^sup>;^ j) ; d)"
    by (simp add: atomic_fiter_pre_sync_fiter_pre_ij atomic_fiter_pre_sync_fiter_pre_ji)
  also have "... = (\<Squnion>i. (a \<^sup>;^ i) ; c \<otimes> (b \<^sup>;^ i) ; d) \<squnion>
                   (\<Squnion>i. \<Squnion>k\<in>{k. 0 < k}. (a \<^sup>;^ i) ; c \<otimes> (b \<^sup>;^ i) ; (b \<^sup>;^ k) ; d) \<squnion>
                   (\<Squnion>i. \<Squnion>j\<in>{j. j < i}. (a \<^sup>;^ j) ; (a \<^sup>;^ (i - j)) ; c \<otimes> (b \<^sup>;^ j) ; d)"
    by (subst NONDET_nat_minus, simp)
  also have "... = (\<Squnion>i. (a \<^sup>;^ i) ; c \<otimes> (b \<^sup>;^ i) ; d) \<squnion>
                   (\<Squnion>i. \<Squnion>k\<in>{k. 0 < k}. (a \<^sup>;^ i) ; c \<otimes> (b \<^sup>;^ i) ; (b \<^sup>;^ k) ; d) \<squnion>
                   (\<Squnion>j. \<Squnion>k\<in>{k. 0 < k}. (a \<^sup>;^ j) ; (a \<^sup>;^ k) ; c \<otimes> (b \<^sup>;^ j) ; d)"
    by (subst Nondet_NONDET_guarded_switch, subst NONDET_nat_minus, simp)
  also have "... = (\<Squnion>i. ((a \<otimes> b) \<^sup>;^ i) ; (c \<otimes> d)) \<squnion>
                   (\<Squnion>i. \<Squnion>k\<in>{k. 0 < k}. ((a \<otimes> b) \<^sup>;^ i) ; (c \<otimes> (b \<^sup>;^ k) ; d)) \<squnion>
                   (\<Squnion>j. \<Squnion>k\<in>{k. 0 < k}. ((a \<otimes> b) \<^sup>;^ j) ; ((a \<^sup>;^ k) ; c \<otimes> d))"
    by (simp add: seq_assoc atomic_power_pre_sync_power_pre)
  also have "... = (\<Squnion>i. ((a \<otimes> b) \<^sup>;^ i) ; (c \<otimes> d)) \<squnion>
                   (\<Squnion>i. ((a \<otimes> b) \<^sup>;^ i) ; (\<Squnion>k\<in>{k. 0 < k}. c \<otimes> (b \<^sup>;^ k) ; d)) \<squnion>
                   (\<Squnion>j. ((a \<otimes> b) \<^sup>;^ j) ; (\<Squnion>k\<in>{k. 0 < k}. (a \<^sup>;^ k) ; c \<otimes> d))"
    apply (subst seq_NONDET_distrib[symmetric], blast)+ by blast
  also have "... = (\<Squnion>i. (a \<otimes> b) \<^sup>;^ i) ;
                     (c \<otimes> d \<squnion>
                     (\<Squnion>k\<in>{k. 0 < k}. c \<otimes> (b \<^sup>;^ k) ; d) \<squnion>
                     (\<Squnion>k\<in>{k. 0 < k}. (a \<^sup>;^ k) ; c \<otimes> d))"
    by (simp add: NONDET_seq_distrib seq_nondet_distrib)
  also have "... = (\<Squnion>i. (a \<otimes> b) \<^sup>;^ i) ; (c \<otimes> d \<squnion> c \<otimes> b ; b\<^sup>\<star> ; d \<squnion> a ; a\<^sup>\<star> ; c \<otimes> d)"
  proof -
    (*using INF_sync_distrib INF_seq_distrib fiter_seq_choice_nonempty sync_INF_distrib*)
    have "(\<Squnion>k\<in>{k. 0 < k}. c \<otimes> (b \<^sup>;^ k) ; d) = (c \<otimes>  b ; b\<^sup>\<star> ; d)"
    proof -
      { assume "Collect ((<) (0::nat)) \<noteq> {}"
        then have ?thesis
          by (simp add: NONDET_seq_distrib fiter_seq_choice_nonempty sync_NONDET_distrib) }
      then show ?thesis
        by blast
    qed
    moreover have "(\<Squnion>k\<in>{k. 0 < k}. (a \<^sup>;^ k) ; c \<otimes> d) = (a ; a\<^sup>\<star> ; c \<otimes> d)"
      by (metis Collect_empty_eq NONDET_seq_distrib NONDET_sync_distrib fiter_seq_choice_nonempty zero_less_Suc)
    ultimately show ?thesis by metis
  qed
  also have "... = (a \<otimes> b)\<^sup>\<star> ; (c \<otimes> d \<squnion> c \<otimes> b ; b\<^sup>\<star> ; d \<squnion> a ; a\<^sup>\<star> ; c \<otimes> d)"
    by (simp add: fiter_seq_choice)
  finally show ?thesis .
qed

lemma atomic_fiter_pre_sync_fiter_pre2:
  assumes a_atomic[simp]: "a = (atomic p)"
  assumes b_atomic[simp]: "b = (atomic q)"
  shows "a\<^sup>\<star> ; c \<otimes> b\<^sup>\<star> ; d = (a \<otimes> b)\<^sup>\<star> ; ((c \<otimes> b\<^sup>\<star> ; d) \<squnion> (a\<^sup>\<star> ; c \<otimes> d))"
proof -
  have  "a\<^sup>\<star> ; c \<otimes> b\<^sup>\<star> ; d = (a \<otimes> b)\<^sup>\<star> ; ((c \<otimes> d) \<squnion> (c \<otimes> b ; b\<^sup>\<star> ; d) \<squnion> (a ; a\<^sup>\<star> ; c \<otimes> d))"
    using atomic_fiter_pre_sync_fiter_pre a_atomic b_atomic by simp
  also have "... = (a \<otimes> b)\<^sup>\<star> ; ((c \<otimes> nil;d) \<squnion> (c \<otimes> b ; b\<^sup>\<star> ; d) \<squnion> (nil;c \<otimes> d) \<squnion> (a ; a\<^sup>\<star> ; c \<otimes> d))"
    by (simp add: sup_commute)
  also have "... = (a \<otimes> b)\<^sup>\<star> ; ((c \<otimes> (nil \<squnion> b ; b\<^sup>\<star>) ; d) \<squnion> ((nil \<squnion> a ; a\<^sup>\<star>) ; c \<otimes> d))"
    by (simp add: sup.semigroup_axioms nondet_seq_distrib nondet_sync_distrib sync_nondet_distrib semigroup.assoc)
  also have "... = (a \<otimes> b)\<^sup>\<star> ; ((c \<otimes> b\<^sup>\<star> ; d) \<squnion> (a\<^sup>\<star>; c \<otimes> d))"
    using fiter_unfold by auto 
  finally show ?thesis .
qed
  
lemma atomic_fiter_sync_fiter:
  assumes a_atomic[simp]: "a = (atomic p)"
  assumes b_atomic[simp]: "b = (atomic q)"
  shows "a\<^sup>\<star> \<otimes> b\<^sup>\<star> = (a \<otimes> b)\<^sup>\<star>"
  using atomic_fiter_pre_sync_fiter_pre
  by (metis a_atomic atomic_pre_sync_nil b_atomic sup_bot.right_neutral nil_sync_nil 
        nil_sync_atomic_pre seq.right_neutral) 

lemma atomic_fiter_pre_sync_infiter:
  assumes a_atomic[simp]: "a = (atomic p)"
  assumes b_atomic[simp]: "b = (atomic q)"
  shows "a\<^sup>\<star> ; c \<otimes> b\<^sup>\<infinity> = (a \<otimes> b)\<^sup>\<star> ; (c \<otimes> b\<^sup>\<infinity>)"
proof -
  have "a\<^sup>\<star> ; c \<otimes> b\<^sup>\<infinity> = (\<Squnion>i. (a \<^sup>;^ i) ; c) \<otimes> b\<^sup>\<infinity>"
   by (simp add: NONDET_seq_distrib fiter_seq_choice)
  also have "... = (\<Squnion>i. (a \<^sup>;^ i) ; c \<otimes> b\<^sup>\<infinity>)" using NONDET_sync_distrib by blast
  also have "... = (\<Squnion>i. (a \<^sup>;^ i) ; c \<otimes> (b \<^sup>;^ i) ; b\<^sup>\<infinity>)" by (metis (no_types, opaque_lifting) infiter_unfold_any)
  also have "... = (\<Squnion>i. ((a \<otimes> b) \<^sup>;^ i) ; (c \<otimes> b\<^sup>\<infinity>))" using atomic_power_pre_sync_power_pre by auto
  also have "... = (\<Squnion>i. ((a \<otimes> b) \<^sup>;^ i)) ; (c \<otimes> b\<^sup>\<infinity>)" by (simp add: NONDET_seq_distrib)
  also have "... = (a \<otimes> b)\<^sup>\<star> ; (c \<otimes> b\<^sup>\<infinity>)" 
    by (simp add: fiter_seq_choice)
  finally show ?thesis .
qed
  
lemma atomic_infiter_sync_fiter_pre:
  assumes a_atomic[simp]: "a = (atomic p)"
  assumes b_atomic[simp]: "b = (atomic q)"
  shows "a\<^sup>\<infinity> \<otimes> b\<^sup>\<star> ; c = (a \<otimes> b)\<^sup>\<star> ; (a\<^sup>\<infinity> \<otimes> c)"
  by (metis a_atomic atomic_fiter_pre_sync_infiter b_atomic sync_commute)

lemma atomic_fiter_sync_infiter: 
  assumes a_atomic[simp]: "a = (atomic p)"
  assumes b_atomic[simp]: "b = (atomic q)"
  shows "a\<^sup>\<star> \<otimes> b\<^sup>\<infinity> = (a \<otimes> b)\<^sup>\<star> ; \<bottom>"
proof -
  have "a\<^sup>\<star> \<otimes> b\<^sup>\<infinity> = a\<^sup>\<star> ; nil \<otimes> b\<^sup>\<infinity>" by simp
  thus ?thesis using atomic_fiter_pre_sync_infiter 
  by (metis a_atomic atomic_fiter_pre_sync_infiter b_atomic infiter_unfold nil_sync_atomic_pre)
qed

lemma atomic_iter_pre_sync_infiter:
  assumes a_atomic[simp]: "a = (atomic p)"
  assumes b_atomic[simp]: "b = (atomic q)"
  shows "a\<^sup>\<omega> ; c \<otimes> b\<^sup>\<infinity> = (a \<otimes> b)\<^sup>\<omega> ; (c \<otimes> b\<^sup>\<infinity>)"    
proof -
  have "a\<^sup>\<omega> ; c \<otimes> b\<^sup>\<infinity> = (a\<^sup>\<star>; c \<squnion> a\<^sup>\<infinity>) \<otimes> b\<^sup>\<infinity>" by (simp add: infiter_annil iter_isolate)
  also have "... = (a\<^sup>\<star>; c \<otimes> b\<^sup>\<infinity> \<squnion> a\<^sup>\<infinity> \<otimes> b\<^sup>\<infinity>)" by (simp add: nondet_sync_distrib)
  also have "... = (a \<otimes> b)\<^sup>\<star> ; (c \<otimes> b\<^sup>\<infinity>) \<squnion> (a \<otimes> b)\<^sup>\<infinity>"  using atomic_fiter_pre_sync_infiter atomic_infiter_sync by simp
  also have "... = (a \<otimes> b)\<^sup>\<omega> ; (c \<otimes> b\<^sup>\<infinity>)" by (simp add: iter_isolate)
  finally show ?thesis by simp
qed

lemma atomic_infiter_sync_iter_pre:
  assumes a_atomic[simp]: "a = (atomic p)"
  assumes b_atomic[simp]: "b = (atomic q)"
  shows "a\<^sup>\<infinity> \<otimes> b\<^sup>\<omega> ; c = (a \<otimes> b)\<^sup>\<omega> ; (a\<^sup>\<infinity> \<otimes> c)"
  by (metis a_atomic atomic_iter_pre_sync_infiter b_atomic sync_commute)

lemma atomic_iter_sync_infiter: 
  assumes a_atomic[simp]: "a = (atomic p)"
  assumes b_atomic[simp]: "b = (atomic q)"
  shows "a\<^sup>\<omega> \<otimes> b\<^sup>\<infinity> = (a \<otimes> b)\<^sup>\<infinity>"
proof -
  have "a\<^sup>\<omega> \<otimes> b\<^sup>\<infinity> = a\<^sup>\<omega> ; nil \<otimes> b\<^sup>\<infinity>" by simp
  also have "... = (a \<otimes> b)\<^sup>\<omega> ; \<bottom>"  by (metis a_atomic atomic_iter_pre_sync_infiter b_atomic infiter_unfold nil_sync_atomic_pre)
  also have "... = (a \<otimes> b)\<^sup>\<infinity>" by (simp add: infiter_iter_magic)
  finally show ?thesis by simp
qed
    
lemma atomic_infiter_sync_iter:
  assumes a_atomic[simp]: "a = (atomic p)"
  assumes b_atomic[simp]: "b = (atomic q)"
  shows "a\<^sup>\<infinity> \<otimes> b\<^sup>\<omega> = (a \<otimes> b)\<^sup>\<infinity>"
  by (metis a_atomic atomic_iter_sync_infiter b_atomic sync_commute)
  
lemma atomic_iter_pre_sync_fiter_pre:
  assumes a_atomic[simp]: "a = (atomic p)"
  assumes b_atomic[simp]: "b = (atomic q)"
  shows "a\<^sup>\<omega> ; c \<otimes> b\<^sup>\<star> ; d = (a \<otimes> b)\<^sup>\<star> ; ((c \<otimes> d) \<squnion> (c \<otimes> b ; b\<^sup>\<star> ; d) \<squnion> (a ; a\<^sup>\<omega> ; c \<otimes> d))"
proof -
  have "a\<^sup>\<omega> ; c \<otimes> b\<^sup>\<star> ; d = (a\<^sup>\<star> \<squnion> a\<^sup>\<infinity>) ; c \<otimes> b\<^sup>\<star> ; d"
   by (simp add: iter_isolation) 
  also have "... = (a\<^sup>\<star> ; c \<otimes> b\<^sup>\<star> ; d) \<squnion> (a\<^sup>\<infinity> \<otimes> b\<^sup>\<star> ; d)"
    using nondet_seq_distrib infiter_annil by (simp add: nondet_sync_distrib)
  also have "... = (a \<otimes> b)\<^sup>\<star> ; ((c \<otimes> d) \<squnion> (c \<otimes> b ; b\<^sup>\<star> ; d) \<squnion> (a ; a\<^sup>\<star> ; c \<otimes> d)) \<squnion>
                   (a\<^sup>\<infinity> \<otimes> b\<^sup>\<star> ; d)"
    by (simp add: atomic_fiter_pre_sync_fiter_pre)
  also have "... = (a \<otimes> b)\<^sup>\<star> ; ((c \<otimes> d) \<squnion> (c \<otimes> b ; b\<^sup>\<star> ; d) \<squnion> (a ; a\<^sup>\<star> ; c \<otimes> d)) \<squnion>
                   ((a \<otimes> b)\<^sup>\<star> ; (a\<^sup>\<infinity> \<otimes> d))"
    by (simp add: atomic_infiter_sync_fiter_pre)
  also have "... = (a \<otimes> b)\<^sup>\<star> ; ((c \<otimes> d) \<squnion>
                               ((c \<otimes> b ; b\<^sup>\<star> ; d)) \<squnion>
                               ((a ; a\<^sup>\<star> ; c \<otimes> d) \<squnion> (a\<^sup>\<infinity> \<otimes> d)))"
    by (simp add: sup.commute inf_sup_aci(7) seq_nondet_distrib)
  also have "... = (a \<otimes> b)\<^sup>\<star> ; ((c \<otimes> d) \<squnion>
                               (c \<otimes> (b ; b\<^sup>\<star> ; d)) \<squnion>
                               ((a ; a\<^sup>\<star> ; c \<squnion> a\<^sup>\<infinity>) \<otimes> d))"
    by (simp add: nondet_sync_distrib)
  also have "... = (a \<otimes> b)\<^sup>\<star> ; ((c \<otimes> d) \<squnion> (c \<otimes> b ; b\<^sup>\<star> ; d) \<squnion> (a ; a\<^sup>\<omega> ; c \<otimes> d))"
    by (simp add: iter_isolate2)
  finally show ?thesis .
qed

lemma atomic_fiter_pre_sync_iter_pre:
  assumes a_atomic[simp]: "a = (atomic p)"
  assumes b_atomic[simp]: "b = (atomic q)"
  shows "a\<^sup>\<star> ; c \<otimes> b\<^sup>\<omega> ; d =  (a \<otimes> b)\<^sup>\<star> ; ((c \<otimes> d) \<squnion> (a ; a\<^sup>\<star> ; c \<otimes> d) \<squnion> (c \<otimes> b ; b\<^sup>\<omega> ; d))"
  by (metis a_atomic atomic_iter_pre_sync_fiter_pre b_atomic sync_commute)
  
lemma atomic_iter_pre_sync_fiter_pre2:
  assumes a_atomic[simp]: "a = (atomic p)"
  assumes b_atomic[simp]: "b = (atomic q)"
  shows "a\<^sup>\<omega> ; c \<otimes> b\<^sup>\<star> ; d = (a \<otimes> b)\<^sup>\<star> ; ((c \<otimes> b\<^sup>\<star> ; d) \<squnion> (a\<^sup>\<omega>; c \<otimes> d))"
proof -
  have  "a\<^sup>\<omega> ; c \<otimes> b\<^sup>\<star> ; d = (a \<otimes> b)\<^sup>\<star> ; ((c \<otimes> d) \<squnion> (c \<otimes> b ; b\<^sup>\<star> ; d) \<squnion> (a ; a\<^sup>\<omega> ; c \<otimes> d))"
    using atomic_iter_pre_sync_fiter_pre a_atomic b_atomic by simp
  also have "... = (a \<otimes> b)\<^sup>\<star> ; ((c \<otimes> nil;d) \<squnion> (c \<otimes> b ; b\<^sup>\<star> ; d) \<squnion> (nil;c \<otimes> d) \<squnion> (a ; a\<^sup>\<omega> ; c \<otimes> d))"
    by (simp add: sup_commute)
  also have "... = (a \<otimes> b)\<^sup>\<star> ; ((c \<otimes> (nil \<squnion> b ; b\<^sup>\<star>) ; d) \<squnion> ((nil \<squnion> a ; a\<^sup>\<omega>) ; c \<otimes> d))"
    by (simp add: sup.semigroup_axioms nondet_seq_distrib nondet_sync_distrib sync_nondet_distrib semigroup.assoc)
  also have "... = (a \<otimes> b)\<^sup>\<star> ; ((c \<otimes> b\<^sup>\<star> ; d) \<squnion> (a\<^sup>\<omega>; c \<otimes> d))"
    using fiter_unfold iter_unfold by auto 
  finally show ?thesis .
qed
  
lemma atomic_fiter_pre_sync_iter_pre2:
  assumes a_atomic[simp]: "a = (atomic p)"
  assumes b_atomic[simp]: "b = (atomic q)"
  shows "a\<^sup>\<star> ; c \<otimes> b\<^sup>\<omega> ; d = (a \<otimes> b)\<^sup>\<star> ; ((c \<otimes> b\<^sup>\<omega> ; d) \<squnion> (a\<^sup>\<star> ; c \<otimes> d))"
  by (metis a_atomic atomic_iter_pre_sync_fiter_pre2 b_atomic sync_commute sup_commute)

lemma atomic_iter_pre_sync_fiter:
  assumes a_atomic[simp]: "a = (atomic p)"
  assumes b_atomic[simp]: "b = (atomic q)"
  shows "a\<^sup>\<omega> ; c \<otimes> b\<^sup>\<star> = (a \<otimes> b)\<^sup>\<star> ; (c \<otimes> b\<^sup>\<star>)"
proof -
  have "a\<^sup>\<omega> ; c \<otimes> b\<^sup>\<star> = a\<^sup>\<omega> ; c \<otimes> b\<^sup>\<star> ; nil" by simp 
  also have "...  = (a \<otimes> b)\<^sup>\<star> ; ((c \<otimes> nil) \<squnion> (c \<otimes> b ; b\<^sup>\<star> ; nil) \<squnion> (a ; a\<^sup>\<omega> ; c \<otimes> nil))"
    by (metis a_atomic atomic_iter_pre_sync_fiter_pre b_atomic)
  also have "... = (a \<otimes> b)\<^sup>\<star> ; ((c \<otimes> nil) \<squnion> (c \<otimes> b ; b\<^sup>\<star>))"
    by (simp add: nil_sync_atomic_pre nil_sync_nil sync_commute seq_assoc)
  also have "... = (a \<otimes> b)\<^sup>\<star> ; (c \<otimes> (nil \<squnion> b ; b\<^sup>\<star>))"
    by (simp add: nondet_sync_distrib sync_nondet_distrib)
  also have "... = (a \<otimes> b)\<^sup>\<star> ; (c \<otimes> b\<^sup>\<star>)"
    using fiter_unfold by simp
  finally show ?thesis .
qed

lemma atomic_fiter_sync_iter_pre:
  assumes a_atomic[simp]: "a = (atomic p)"
  assumes b_atomic[simp]: "b = (atomic q)"
  shows "a\<^sup>\<star> \<otimes> b\<^sup>\<omega> ; c= (a \<otimes> b)\<^sup>\<star> ; (a\<^sup>\<star> \<otimes> c)"
  by (metis a_atomic atomic_iter_pre_sync_fiter b_atomic sync_commute)
  
lemma atomic_fiter_pre_sync_iter:
  assumes a_atomic[simp]: "a = (atomic p)"
  assumes b_atomic[simp]: "b = (atomic q)"
  shows "a\<^sup>\<star> ; c \<otimes> b\<^sup>\<omega> = (a \<otimes> b)\<^sup>\<star> ; (c \<otimes> b\<^sup>\<omega>)"
proof -
  have "a\<^sup>\<star> ; c \<otimes> b\<^sup>\<omega> = a\<^sup>\<star> ; c \<otimes> b\<^sup>\<omega> ; nil" by simp 
  also have "...  = (a \<otimes> b)\<^sup>\<star> ; ((c \<otimes> nil) \<squnion> (a ; a\<^sup>\<star> ; c \<otimes> nil) \<squnion> (c \<otimes> b ; b\<^sup>\<omega> ; nil))"
    by (metis a_atomic atomic_fiter_pre_sync_iter_pre b_atomic)
  also have "... = (a \<otimes> b)\<^sup>\<star> ; ((c \<otimes> nil) \<squnion> (c \<otimes> b ; b\<^sup>\<omega>))"
    by (simp add: nil_sync_atomic_pre nil_sync_nil sync_commute seq_assoc)
  also have "... = (a \<otimes> b)\<^sup>\<star> ; (c \<otimes> (nil \<squnion> b ; b\<^sup>\<omega>))"
    by (simp add: nondet_sync_distrib sync_nondet_distrib)
  also have "... = (a \<otimes> b)\<^sup>\<star> ; (c \<otimes> b\<^sup>\<omega>)"
    using iter_unfold by simp
  finally show ?thesis .
qed

lemma atomic_iter_sync_fiter_pre:
  assumes a_atomic[simp]: "a = (atomic p)"
  assumes b_atomic[simp]: "b = (atomic q)"
  shows  "a\<^sup>\<omega> \<otimes> b\<^sup>\<star> ; c = (a \<otimes> b)\<^sup>\<star> ; (a\<^sup>\<omega> \<otimes> c)"
  by (metis a_atomic atomic_fiter_pre_sync_iter b_atomic sync_commute)
  
lemma atomic_iter_sync_fiter:
  assumes a_atomic[simp]: "a = (atomic p)"
  assumes b_atomic[simp]: "b = (atomic q)"
  shows "a\<^sup>\<omega> \<otimes> b\<^sup>\<star> = (a \<otimes> b)\<^sup>\<star>"
proof -
  have "a\<^sup>\<omega> \<otimes> b\<^sup>\<star> = a\<^sup>\<omega> ; nil \<otimes> b\<^sup>\<star>" by simp 
  also have "\<dots> = (a \<otimes> b)\<^sup>\<star> ; (nil \<otimes> b\<^sup>\<star>)"
    using a_atomic b_atomic atomic_iter_pre_sync_fiter by blast 
  thus ?thesis using atomic_fiter_sync_nil sync_commute by simp
qed
  
lemma atomic_fiter_sync_iter:
  assumes a_atomic[simp]: "a = (atomic p)"
  assumes b_atomic[simp]: "b = (atomic q)"
  shows "a\<^sup>\<star> \<otimes> b\<^sup>\<omega> = (a \<otimes> b)\<^sup>\<star>"
  by (metis a_atomic atomic_iter_sync_fiter b_atomic sync_commute)

    
lemma atomic_iter_pre_sync_iter_pre:
  assumes a_atomic[simp]: "a = (atomic p)"
  assumes b_atomic[simp]: "b = (atomic q)"
  shows "a\<^sup>\<omega> ; c \<otimes> b\<^sup>\<omega> ; d = (a \<otimes> b)\<^sup>\<omega> ; ((c \<otimes> d) \<squnion> (c \<otimes> b ; b\<^sup>\<omega> ; d) \<squnion> (a ; a\<^sup>\<omega> ; c \<otimes> d))"
proof -
  have "a\<^sup>\<omega> ; c \<otimes> b\<^sup>\<omega> ; d = (a\<^sup>\<star> \<squnion> a\<^sup>\<infinity>) ; c \<otimes> (b\<^sup>\<star> \<squnion> b\<^sup>\<infinity>) ; d"
   by (simp add: iter_isolation) 
 also have "... = (a\<^sup>\<star> ; c \<otimes> b\<^sup>\<star> ; d) \<squnion> (a\<^sup>\<star> ; c \<otimes> b\<^sup>\<infinity>) \<squnion> (a\<^sup>\<infinity> \<otimes> b\<^sup>\<star> ; d) \<squnion> (a\<^sup>\<infinity> \<otimes> b\<^sup>\<infinity>)"
    by (simp add: infiter_annil nondet_sync_product nondet_seq_distrib)
  also have "... = (a \<otimes> b)\<^sup>\<star> ; ((c \<otimes> d) \<squnion> (c \<otimes> b ; b\<^sup>\<star> ; d) \<squnion> (a ; a\<^sup>\<star> ; c \<otimes> d)) \<squnion>
                   (a\<^sup>\<star> ; c \<otimes> b\<^sup>\<infinity>) \<squnion> (a\<^sup>\<infinity> \<otimes> b\<^sup>\<star> ; d) \<squnion> (a\<^sup>\<infinity> \<otimes> b\<^sup>\<infinity>)"
    by (simp add: atomic_fiter_pre_sync_fiter_pre)
  also have "... = (a \<otimes> b)\<^sup>\<star> ; ((c \<otimes> d) \<squnion> (c \<otimes> b ; b\<^sup>\<star> ; d) \<squnion> (a ; a\<^sup>\<star> ; c \<otimes> d)) \<squnion>
                   ((a \<otimes> b)\<^sup>\<star> ; (c \<otimes> b\<^sup>\<infinity>)) \<squnion> ((a \<otimes> b)\<^sup>\<star> ; (a\<^sup>\<infinity> \<otimes> d)) \<squnion> (a \<otimes> b)\<^sup>\<infinity>"
    by (simp add: atomic_fiter_pre_sync_infiter atomic_infiter_sync_fiter_pre)
  also have "... = (a \<otimes> b)\<^sup>\<star> ; ((c \<otimes> d) \<squnion>
                               ((c \<otimes> b ; b\<^sup>\<star> ; d) \<squnion> (c \<otimes> b\<^sup>\<infinity>)) \<squnion>
                               ((a ; a\<^sup>\<star> ; c \<otimes> d) \<squnion> (a\<^sup>\<infinity> \<otimes> d))) \<squnion>
                   (a \<otimes> b)\<^sup>\<infinity>"
    by (simp add: sup.commute inf_sup_aci(7) seq_nondet_distrib)
  also have "... = (a \<otimes> b)\<^sup>\<star> ; ((c \<otimes> d) \<squnion>
                               (c \<otimes> (b ; b\<^sup>\<star> ; d \<squnion> b\<^sup>\<infinity>)) \<squnion>
                               ((a ; a\<^sup>\<star> ; c \<squnion> a\<^sup>\<infinity>) \<otimes> d)) \<squnion>
                   (a \<otimes> b)\<^sup>\<infinity>"
    by (simp add: nondet_sync_distrib sync_nondet_distrib)
  also have "... = (a \<otimes> b)\<^sup>\<star> ; ((c \<otimes> d) \<squnion> (c \<otimes> b ; b\<^sup>\<omega> ; d) \<squnion> (a ; a\<^sup>\<omega> ; c \<otimes> d)) \<squnion> (a \<otimes> b)\<^sup>\<infinity>"
    by (simp add: iter_isolate2)
  also have "... = (a \<otimes> b)\<^sup>\<omega> ; ((c \<otimes> d) \<squnion> (c \<otimes> b ; b\<^sup>\<omega> ; d) \<squnion> (a ; a\<^sup>\<omega> ; c \<otimes> d))"
    by (simp add: iter_isolate)
  finally show ?thesis .
qed

lemma atomic_iter_pre_sync_iter_pre2:
  assumes a_atomic[simp]: "a = (atomic p)"
  assumes b_atomic[simp]: "b = (atomic q)"
  shows "a\<^sup>\<omega> ; c \<otimes> b\<^sup>\<omega> ; d = (a \<otimes> b)\<^sup>\<omega> ; ((c \<otimes> b\<^sup>\<omega> ; d) \<squnion> (a\<^sup>\<omega> ; c \<otimes> d))"
proof -
  have  "a\<^sup>\<omega> ; c \<otimes> b\<^sup>\<omega> ; d = (a \<otimes> b)\<^sup>\<omega> ; ((c \<otimes> d) \<squnion> (c \<otimes> b ; b\<^sup>\<omega> ; d) \<squnion> (a ; a\<^sup>\<omega> ; c \<otimes> d))"
    using atomic_iter_pre_sync_iter_pre a_atomic b_atomic by simp
  also have "... = (a \<otimes> b)\<^sup>\<omega> ; ((c \<otimes> nil;d) \<squnion> (c \<otimes> b ; b\<^sup>\<omega> ; d) \<squnion> (nil;c \<otimes> d) \<squnion> (a ; a\<^sup>\<omega> ; c \<otimes> d))"
    by (simp add: sup_commute)
  also have "... = (a \<otimes> b)\<^sup>\<omega> ; ((c \<otimes> (nil \<squnion> b ; b\<^sup>\<omega>) ; d) \<squnion> ((nil \<squnion> a ; a\<^sup>\<omega>) ; c \<otimes> d))"
    by (simp add: sup.semigroup_axioms nondet_seq_distrib nondet_sync_distrib sync_nondet_distrib semigroup.assoc)
  also have "... = (a \<otimes> b)\<^sup>\<omega> ; ((c \<otimes> b\<^sup>\<omega> ; d) \<squnion> (a\<^sup>\<omega>; c \<otimes> d))"
    using iter_unfold by auto 
  finally show ?thesis .
qed

lemma atomic_iter_pre_sync_iter:
  assumes a_atomic[simp]: "a = (atomic p)"
  assumes b_atomic[simp]: "b = (atomic q)"
  shows "a\<^sup>\<omega> ; c \<otimes> b\<^sup>\<omega> = (a \<otimes> b)\<^sup>\<omega> ; (c \<otimes> b\<^sup>\<omega>)"
proof -
  have "a\<^sup>\<omega> ; c \<otimes> b\<^sup>\<omega> = (a \<otimes> b)\<^sup>\<omega> ; ((c \<otimes> nil) \<squnion> (c \<otimes> b ; b\<^sup>\<omega> ; nil) \<squnion> (a ; a\<^sup>\<omega>; c \<otimes> nil))"
    using atomic_iter_pre_sync_iter_pre by (metis a_atomic b_atomic seq_assoc seq_nil_right) 
  also have "... =  (a \<otimes> b)\<^sup>\<omega> ; ((c \<otimes> nil) \<squnion> (c \<otimes> b ; b\<^sup>\<omega>))"
    by (simp add: atomic_pre_sync_nil seq_assoc)
  also have "... = (a \<otimes> b)\<^sup>\<omega> ; (c \<otimes> (nil \<squnion> b ; b\<^sup>\<omega>))"
    by (simp add: sync_nondet_distrib)
  also have "... = (a \<otimes> b)\<^sup>\<omega> ; (c \<otimes> b\<^sup>\<omega>)"
    using iter_unfold by simp
  finally show ?thesis .
qed
  
lemma atomic_iter_sync_iter:
  assumes atomic_a[simp]: "a = (atomic p)"
  assumes atomic_b[simp]: "b = (atomic q)"
  shows "a\<^sup>\<omega> \<otimes> b\<^sup>\<omega> = (a \<otimes> b)\<^sup>\<omega>"
proof -
  have "a\<^sup>\<omega> \<otimes> b\<^sup>\<omega> = a\<^sup>\<omega> ; nil \<otimes> b\<^sup>\<omega> ; nil" by simp 
  also have "\<dots> = (a \<otimes> b)\<^sup>\<omega> ; ((nil \<otimes> nil) \<squnion> (nil \<otimes> b ; b\<^sup>\<omega> ; nil) \<squnion> (a ; a\<^sup>\<omega> ; nil \<otimes> nil))"
    using atomic_a atomic_b atomic_iter_pre_sync_iter_pre by blast 
  thus ?thesis by (simp add: nil_sync_nil nil_sync_atomic_pre sync_commute)
qed

lemma atomic_iter_sync_iter_atom_pre:
  assumes a_atomic[simp]: "a = (atomic p)"
  assumes b_atomic[simp]: "b = (atomic q)"
  assumes y_atomic[simp]: "y = (atomic r)"
  shows "a\<^sup>\<omega> \<otimes> b\<^sup>\<omega> ; y ; d = (a \<otimes> b)\<^sup>\<omega> ; (a \<otimes> y) ; (a\<^sup>\<omega> \<otimes> d)"
proof -
  have "a\<^sup>\<omega> \<otimes> b\<^sup>\<omega> ; y ; d = 
        (a \<otimes> b)\<^sup>\<omega> ; ((nil \<otimes> y ; d) \<squnion> (nil \<otimes> b ; b\<^sup>\<omega> ; y ; d) \<squnion> (a ; a\<^sup>\<omega> \<otimes> y ; d))"
    using atomic_iter_pre_sync_iter_pre by (metis a_atomic b_atomic seq_assoc seq_nil_right) 
  also have "\<dots> = (a \<otimes> b)\<^sup>\<omega> ; (a ; a\<^sup>\<omega> \<otimes> y ; d)" using nil_sync_atomic_pre
    by (simp add: seq_assoc)
  thus ?thesis using atomic_pre_sync_atomic_pre a_atomic calculation seq_assoc y_atomic by auto
qed

lemma atomic_iter_pre_sync_iter_pre_atomic:
  assumes a_atomic[simp]: "a = (atomic p)"
  assumes b_atomic[simp]: "b = (atomic q)"
  assumes x_atomic[simp]: "x = (atomic r)"
  assumes y_atomic[simp]: "y = (atomic s)"
  shows "a\<^sup>\<omega>;x;c \<otimes> b\<^sup>\<omega>;y;d = 
         (a \<otimes> b)\<^sup>\<omega>;((x \<otimes> y);(c \<otimes> d) \<squnion> (x \<otimes> b);(c \<otimes> b\<^sup>\<omega>;y;d) \<squnion> (a \<otimes> y);(a\<^sup>\<omega>;x;c \<otimes> d))"
  using atomic_iter_pre_sync_iter_pre
    by (simp add: atomic_pre_sync_atomic_pre seq_assoc)

lemma atomic_iter_pre_sync_fiter_iter_pre:
  assumes a_atomic[simp]: "a = (atomic p)"
  assumes c_atomic[simp]: "c = (atomic p1)"
  assumes d_atomic[simp]: "d = (atomic q1)"
  shows "a\<^sup>\<star>;c\<^sup>\<omega>;e \<otimes> d\<^sup>\<omega>;f = (a\<otimes>d)\<^sup>\<star>;((c\<otimes>d)\<^sup>\<omega>;(e \<otimes> d\<^sup>\<omega>;f \<squnion> c\<^sup>\<omega>;e \<otimes> f) \<squnion> a\<^sup>\<star>;c\<^sup>\<omega>;e \<otimes> f)"
proof -
  have "a\<^sup>\<star>;c\<^sup>\<omega>;e \<otimes> d\<^sup>\<omega>;f = (a\<otimes>d)\<^sup>\<star>;(c\<^sup>\<omega>;e \<otimes> d\<^sup>\<omega>;f \<squnion> a\<^sup>\<star>;c\<^sup>\<omega>;e \<otimes> f)"
    using atomic_fiter_pre_sync_iter_pre2 a_atomic d_atomic seq_assoc by simp
  also have "... = (a\<otimes>d)\<^sup>\<star>;((c\<otimes>d)\<^sup>\<omega>;(e \<otimes> d\<^sup>\<omega>;f \<squnion> c\<^sup>\<omega>;e \<otimes> f) \<squnion> a\<^sup>\<star>;c\<^sup>\<omega>;e \<otimes> f)"
    using atomic_iter_pre_sync_iter_pre2 c_atomic d_atomic by simp
  finally show ?thesis .
qed

lemma atomic_fiter_iter_pre_sync_fiter_iter_pre:
  assumes a_atomic[simp]: "a0 = (atomic p0)"
  assumes b_atomic[simp]: "b0 = (atomic q0)"
  assumes c_atomic[simp]: "a1 = (atomic p1)"
  assumes d_atomic[simp]: "b1 = (atomic q1)"
  shows "a0\<^sup>\<star>;a1\<^sup>\<omega>;c \<otimes> b0\<^sup>\<star>;b1\<^sup>\<omega>;d = (a0\<otimes>b0)\<^sup>\<star>;(
        (a1\<otimes>b0)\<^sup>\<star>;((a1\<otimes>b1)\<^sup>\<omega>;(d \<otimes> a1\<^sup>\<omega>;c \<squnion> b1\<^sup>\<omega>;d \<otimes> c) \<squnion> b0\<^sup>\<star>;b1\<^sup>\<omega>;d \<otimes> c) \<squnion>
        (a0\<otimes>b1)\<^sup>\<star>;((a1\<otimes>b1)\<^sup>\<omega>;(c \<otimes> b1\<^sup>\<omega>;d \<squnion> a1\<^sup>\<omega>;c \<otimes> d) \<squnion> a0\<^sup>\<star>;a1\<^sup>\<omega>;c \<otimes> d))"
proof -
  have "a0\<^sup>\<star>;a1\<^sup>\<omega>;c \<otimes> b0\<^sup>\<star>;b1\<^sup>\<omega>;d = (a0\<otimes>b0)\<^sup>\<star>;(a1\<^sup>\<omega>;c \<otimes> b0\<^sup>\<star>;b1\<^sup>\<omega>;d \<squnion> a0\<^sup>\<star>;a1\<^sup>\<omega>;c \<otimes> b1\<^sup>\<omega>;d)"
    using atomic_fiter_pre_sync_fiter_pre2 a_atomic b_atomic seq_assoc by simp
  also have "... = (a0\<otimes>b0)\<^sup>\<star>;(
        (a1\<otimes>b0)\<^sup>\<star>;((a1\<otimes>b1)\<^sup>\<omega>;(d \<otimes> a1\<^sup>\<omega>;c \<squnion> b1\<^sup>\<omega>;d \<otimes> c) \<squnion> b0\<^sup>\<star>;b1\<^sup>\<omega>;d \<otimes> c) \<squnion>
        (a0\<otimes>b1)\<^sup>\<star>;((a1\<otimes>b1)\<^sup>\<omega>;(c \<otimes> b1\<^sup>\<omega>;d \<squnion> a1\<^sup>\<omega>;c \<otimes> d) \<squnion> a0\<^sup>\<star>;a1\<^sup>\<omega>;c \<otimes> d))"
    using atomic_iter_pre_sync_fiter_iter_pre sync_commute by simp
  finally show ?thesis .
qed


lemma atomic_fiter_iter_sync_fiter_iter:
  assumes a_atomic[simp]: "a0 = (atomic p0)"
  assumes b_atomic[simp]: "b0 = (atomic q0)"
  assumes c_atomic[simp]: "a1 = (atomic p1)"
  assumes d_atomic[simp]: "b1 = (atomic q1)"
  shows "a0\<^sup>\<star>;a1\<^sup>\<omega> \<otimes> b0\<^sup>\<star>;b1\<^sup>\<omega> = (a0\<otimes>b0)\<^sup>\<star>;((a1\<otimes>b0)\<^sup>\<star> \<squnion> (a0\<otimes>b1)\<^sup>\<star>);(a1\<otimes>b1)\<^sup>\<omega>"
proof -
  have "a0\<^sup>\<star>;a1\<^sup>\<omega> \<otimes> b0\<^sup>\<star>;b1\<^sup>\<omega> = (a0\<otimes>b0)\<^sup>\<star>;(
        (a1\<otimes>b0)\<^sup>\<star>;((a1\<otimes>b1)\<^sup>\<omega>;(nil \<otimes> a1\<^sup>\<omega> \<squnion> b1\<^sup>\<omega> \<otimes> nil) \<squnion> b0\<^sup>\<star>;b1\<^sup>\<omega> \<otimes> nil) \<squnion>
        (a0\<otimes>b1)\<^sup>\<star>;((a1\<otimes>b1)\<^sup>\<omega>;(nil \<otimes> b1\<^sup>\<omega> \<squnion> a1\<^sup>\<omega> \<otimes> nil) \<squnion> a0\<^sup>\<star>;a1\<^sup>\<omega> \<otimes> nil))"
    using atomic_fiter_iter_pre_sync_fiter_iter_pre[where ?c = nil and ?d = nil] by simp
  also have "... = (a0\<otimes>b0)\<^sup>\<star>;(
        (a1\<otimes>b0)\<^sup>\<star>;((a1\<otimes>b1)\<^sup>\<omega> \<squnion> nil) \<squnion>
        (a0\<otimes>b1)\<^sup>\<star>;((a1\<otimes>b1)\<^sup>\<omega> \<squnion> nil))"
    using atomic_fiter_pre_sync_nil atomic_iter_sync_nil by (simp add: sync_commute)
  also have "... = (a0\<otimes>b0)\<^sup>\<star>;((a1\<otimes>b0)\<^sup>\<star>;((a1\<otimes>b1)\<^sup>\<omega>) \<squnion> (a0\<otimes>b1)\<^sup>\<star>;((a1\<otimes>b1)\<^sup>\<omega>))"
    by (simp add: sup.absorb1 iter0)
  also have "... = (a0\<otimes>b0)\<^sup>\<star>;((a1\<otimes>b0)\<^sup>\<star> \<squnion> (a0\<otimes>b1)\<^sup>\<star>);(a1\<otimes>b1)\<^sup>\<omega>"
    by (simp add: nondet_seq_distrib seq_assoc)
  finally show ?thesis .
qed


lemma atomic_fiter_iter_sync_fiter_iter_symmetric:
  assumes a_atomic[simp]: "a0 = (atomic p0)"
  assumes c_atomic[simp]: "a1 = (atomic p1)"
  shows "a0\<^sup>\<star>;a1\<^sup>\<omega> \<otimes> a0\<^sup>\<star>;a1\<^sup>\<omega> = (a0\<otimes>a0)\<^sup>\<star>;(a1\<otimes>a0)\<^sup>\<star>;(a1\<otimes>a1)\<^sup>\<omega>"
proof -
  have "a0\<^sup>\<star>;a1\<^sup>\<omega> \<otimes> a0\<^sup>\<star>;a1\<^sup>\<omega> = (a0\<otimes>a0)\<^sup>\<star>;((a1\<otimes>a0)\<^sup>\<star> \<squnion> (a0\<otimes>a1)\<^sup>\<star>);(a1\<otimes>a1)\<^sup>\<omega>"
    using atomic_fiter_iter_sync_fiter_iter by simp
  also have "... = (a0\<otimes>a0)\<^sup>\<star>;(a1\<otimes>a0)\<^sup>\<star>;(a1\<otimes>a1)\<^sup>\<omega>"
    using sync_commute by simp
  finally show ?thesis .
qed

lemma atomic_optional_sync_iter:
  assumes a_atomic[simp]: "a = (atomic p)"
  assumes b_atomic[simp]: "b = (atomic q)"
  shows "(nil \<squnion> a;c) \<otimes> b\<^sup>\<omega> = nil \<squnion> (a\<otimes>b);(c \<otimes> b\<^sup>\<omega>)"
proof -
  have "(nil \<squnion> a;c) \<otimes> b\<^sup>\<omega> = (nil \<otimes> b\<^sup>\<omega> \<squnion> a;c \<otimes> b\<^sup>\<omega>)"
    by (simp add: nondet_sync_distrib)
  also have "... = (nil \<squnion> a;c \<otimes> (nil \<squnion> b;b\<^sup>\<omega>))"
    using atomic_iter_sync_nil sync_commute iter_unfold by auto
  also have "... = (nil \<squnion> a;c \<otimes> nil \<squnion> a;c \<otimes> b;b\<^sup>\<omega>)"
    using sync_nondet_distrib sup_assoc by metis
  also have "... = (nil \<squnion> a;c \<otimes> b;b\<^sup>\<omega>)"
    using nil_sync_atomic_pre a_atomic sync_commute by simp
  also have "... = nil \<squnion> (a\<otimes>b);(c \<otimes> b\<^sup>\<omega>)"
    using atomic_pre_sync_atomic_pre a_atomic b_atomic by simp
  finally show ?thesis .
qed
(*
(* this does not hold if c=\<bottom> and sync=\<squnion>: 
     if c=\<bottom> we can show with d=\<top> that nil=\<top> and with that can prove that \<top>=\<bottom> *)
lemma atomic_inf_distrib_seq:
  assumes a_atomic[simp]: "a = (atomic p)"
  shows "a\<^sup>\<omega> \<otimes> c;d = (a\<^sup>\<omega> \<otimes> c); (a\<^sup>\<omega> \<otimes> d)" 
oops
(* proof using the canonical representation *)
*)

end

(*========================================================*)

subsection \<open>Lemmas involving syncid\<close>

locale atomic_sync_id_commands = atomic_sync +
    fixes syncid :: "'a"
    assumes syncid_atomic: "\<exists> p . syncid = (atomic p)"
    assumes atomic_sync_identity: "syncid \<otimes> (atomic p) = atomic p"
begin

lemma syncid_syncid[iff]: "syncid \<otimes> syncid  = syncid"
  using atomic_sync_identity syncid_atomic by blast

lemma syncid_fiter_atomic_fiter: "syncid\<^sup>\<star> \<otimes> (atomic p)\<^sup>\<star> = (atomic p)\<^sup>\<star>" 
  using syncid_atomic atomic_sync_identity atomic_fiter_sync_fiter by auto 

lemma syncid_syncid_iter: "syncid\<^sup>\<omega> \<otimes> syncid\<^sup>\<omega> = syncid\<^sup>\<omega>"
  using atomic_iter_sync_iter syncid_atomic syncid_syncid by force

lemma syncid_syncid_fiter: "syncid\<^sup>\<star> \<otimes> syncid\<^sup>\<star> = syncid\<^sup>\<star>"
  using syncid_fiter_atomic_fiter syncid_atomic by blast

lemma syncid_syncidt_infiter: "syncid\<^sup>\<infinity> \<otimes> syncid\<^sup>\<infinity> = syncid\<^sup>\<infinity>"
  using syncid_atomic syncid_syncid by force

lemma syncid_iter_atomic:
  assumes a_atomic[simp]: "a = (atomic p)"
  shows "syncid\<^sup>\<omega> \<otimes> a ; c = a ; (syncid\<^sup>\<omega> \<otimes> c)"
proof -
  have "syncid\<^sup>\<omega> \<otimes> a ; c = (nil \<squnion> syncid ; syncid\<^sup>\<omega>) \<otimes> a ; c" by (metis iter_unfold)
  also have "... = (nil \<otimes> a ; c) \<squnion> (syncid ; syncid\<^sup>\<omega> \<otimes> a ; c)" by (simp add: nondet_sync_distrib)
  also have "... = \<bottom> \<squnion> (syncid \<otimes> a) ; (syncid\<^sup>\<omega> \<otimes> c)"
    using atomic_pre_sync_atomic_pre nil_sync_atomic_pre syncid_atomic by force
  also have "... = a ; (syncid\<^sup>\<omega> \<otimes> c)" by (simp add: atomic_sync_identity)
  finally show ?thesis .
qed

lemma syncid_fiter_atomic:
  assumes a_atomic[simp]: "a = (atomic p)"
  shows "syncid\<^sup>\<star> \<otimes> a ; c = a ; (syncid\<^sup>\<star> \<otimes> c)" 
proof -
  have "syncid\<^sup>\<star> \<otimes> a ; c = (nil \<squnion> syncid ; syncid\<^sup>\<star>) \<otimes> a ; c" using fiter_unfold by auto 
  also have "... = (nil \<otimes> a ; c) \<squnion> (syncid ; syncid\<^sup>\<star> \<otimes> a ; c)" by (simp add: nondet_sync_distrib)
  also have "... = \<bottom> \<squnion> (syncid \<otimes> a) ; (syncid\<^sup>\<star> \<otimes> c)"
    using atomic_pre_sync_atomic_pre nil_sync_atomic_pre syncid_atomic by auto
  also have "... = a ; (syncid\<^sup>\<star> \<otimes> c)" by (simp add: atomic_sync_identity)
  finally show ?thesis .
qed


lemma syncid_iter_atomic_power:
  assumes a_atomic[simp]: "a = (atomic p)"
  shows "syncid\<^sup>\<omega> \<otimes> (a \<^sup>;^ i) ; c = (a \<^sup>;^ i) ; (syncid\<^sup>\<omega> \<otimes> c)"
proof (induct i)
  case 0
  thus ?case by simp
next
  case (Suc i)
  have "syncid\<^sup>\<omega> \<otimes> (a \<^sup>;^ Suc i) ; c = syncid\<^sup>\<omega> \<otimes> a ; (a \<^sup>;^ i) ; c" by simp
  also have "... = a ; (syncid\<^sup>\<omega> \<otimes> (a \<^sup>;^ i) ; c)" by (simp add: seq_assoc syncid_iter_atomic)
  also have "... = a ; (a \<^sup>;^ i) ; (syncid\<^sup>\<omega> \<otimes> c)" by (metis Suc.hyps seq_assoc)
  also have "... = (a \<^sup>;^ Suc i) ; (syncid\<^sup>\<omega> \<otimes> c)" by simp
  finally show ?case .
qed

lemma syncid_iter_atomic_fiter:
  assumes a_atomic[simp]: "a = (atomic p)"
  shows "syncid\<^sup>\<omega> \<otimes> a\<^sup>\<star> ; c = a\<^sup>\<star> ; (syncid\<^sup>\<omega> \<otimes> c)"
proof -
  have "syncid\<^sup>\<omega> \<otimes> a\<^sup>\<star> ; c = syncid\<^sup>\<omega> \<otimes> (\<Squnion>i. (a \<^sup>;^ i) ; c)" 
    by (simp add: NONDET_seq_distrib fiter_seq_choice)
  also have "... = (\<Squnion>i. syncid\<^sup>\<omega> \<otimes> (a \<^sup>;^ i) ; c)" by (simp add: sync_NONDET_distrib)
  also have "... = (\<Squnion>i. (a \<^sup>;^ i) ; (syncid\<^sup>\<omega> \<otimes> c))" by (simp add: syncid_iter_atomic_power)
  also have "... = (\<Squnion>i. (a \<^sup>;^ i)) ; (syncid\<^sup>\<omega> \<otimes> c)" by (simp add: NONDET_seq_distrib)
  also have "... = a\<^sup>\<star> ; (syncid\<^sup>\<omega> \<otimes> c)"
    by (simp add: fiter_seq_choice)
  finally show ?thesis .
qed

lemma syncid_fiter_atomic_infiter:
  assumes a_atomic[simp]: "a = (atomic p)"
  shows "syncid\<^sup>\<star> \<otimes> a\<^sup>\<infinity> = a\<^sup>\<star> ; \<bottom>"
proof -
  have "syncid\<^sup>\<star> \<otimes> a\<^sup>\<infinity> = syncid\<^sup>\<star> ; nil \<otimes> a\<^sup>\<infinity>" by simp
  also have "... = (syncid \<otimes> a)\<^sup>\<star> ; (nil \<otimes> a\<^sup>\<infinity>)"
    using a_atomic atomic_fiter_pre_sync_infiter syncid_atomic by blast
  also have "... = (syncid \<otimes> a)\<^sup>\<star> ; \<bottom>" by (metis assms atomic_infiter_sync_nil sync_commute)
  also have "... = a\<^sup>\<star> ; \<bottom>" by (simp add: atomic_sync_identity)
  finally show ?thesis .
qed

lemma syncid_iter_atomic_infiter:
  assumes a_atomic[simp]: "a = (atomic p)"
  shows "syncid\<^sup>\<omega> \<otimes> a\<^sup>\<infinity> = a\<^sup>\<infinity>"
proof -
  have "syncid\<^sup>\<omega> \<otimes> a\<^sup>\<infinity> = (syncid\<^sup>\<star> \<squnion> syncid\<^sup>\<infinity>) \<otimes> a\<^sup>\<infinity>" 
    by (simp add: iter_isolation) 
  also have "... = (syncid\<^sup>\<star> \<otimes> a\<^sup>\<infinity>) \<squnion> (syncid\<^sup>\<infinity> \<otimes> a\<^sup>\<infinity>)" by (simp add: nondet_sync_distrib)
  also have "... = a\<^sup>\<star> ; \<bottom> \<squnion> a\<^sup>\<infinity>"
    using atomic_sync_identity syncid_fiter_atomic_infiter syncid_atomic by auto
  also have "... = a\<^sup>\<infinity>" by (simp add: sup_absorb2 infiter_fiter_magic)
  finally show ?thesis .
qed

lemma syncid_iter_atomic_iter_prefix:
  assumes a_atomic[simp]: "a = (atomic p)"
  shows "syncid\<^sup>\<omega> \<otimes> a\<^sup>\<omega> ; c = a\<^sup>\<omega> ; (syncid\<^sup>\<omega> \<otimes> c)"
proof -
  have "syncid\<^sup>\<omega> \<otimes> a\<^sup>\<omega> ; c = syncid\<^sup>\<omega> \<otimes> (a\<^sup>\<star> ; c \<squnion> a\<^sup>\<infinity>)" 
    by (simp add: iter_isolate)
  also have "... = (syncid\<^sup>\<omega> \<otimes> a\<^sup>\<star> ; c) \<squnion> (syncid\<^sup>\<omega> \<otimes> a\<^sup>\<infinity>)" by (simp add: sync_nondet_distrib)
  also have "... = a\<^sup>\<star> ; (syncid\<^sup>\<omega> \<otimes> c) \<squnion> a\<^sup>\<infinity>" by (simp add: syncid_iter_atomic_fiter syncid_iter_atomic_infiter)
  also have "... = a\<^sup>\<omega> ; (syncid\<^sup>\<omega> \<otimes> c)" 
    by (simp add: iter_isolate)
  finally show ?thesis .
qed

lemma syncid_iter_wrap_fiter:
  assumes a_atomic[simp]: "a = (atomic p)"
  shows "syncid\<^sup>\<omega> \<otimes> syncid\<^sup>\<star> ; a ; syncid\<^sup>\<omega> = syncid\<^sup>\<star> ; a ; syncid\<^sup>\<omega>"
proof -
  have "syncid\<^sup>\<omega> \<otimes> syncid\<^sup>\<star> ; a ; syncid\<^sup>\<omega> = syncid\<^sup>\<star> ; (syncid\<^sup>\<omega> \<otimes> a ; syncid\<^sup>\<omega>)"
    by (metis seq_assoc syncid_iter_atomic_fiter syncid_atomic)
  also have "... = syncid\<^sup>\<star> ; a ; (syncid\<^sup>\<omega> \<otimes> syncid\<^sup>\<omega>)" by (simp add: seq_assoc syncid_iter_atomic)
  also have "... = syncid\<^sup>\<star> ; a ; syncid\<^sup>\<omega>" using atomic_iter_sync_iter atomic_sync_identity syncid_atomic by auto
  finally show ?thesis .
qed


lemma syncid_iter_wrap_iter:
  assumes a_atomic[simp]: "a = (atomic p)"
  shows "syncid\<^sup>\<omega> \<otimes> syncid\<^sup>\<omega> ; a ; syncid\<^sup>\<omega> = syncid\<^sup>\<omega> ; a ; syncid\<^sup>\<omega>"
proof -
  have "syncid\<^sup>\<omega> \<otimes> syncid\<^sup>\<omega> ; a ; syncid\<^sup>\<omega> = syncid\<^sup>\<omega> ; (syncid\<^sup>\<omega> \<otimes> a ; syncid\<^sup>\<omega>)"
    by (metis seq_assoc syncid_iter_atomic_iter_prefix syncid_atomic)
  also have "... = syncid\<^sup>\<omega> ; a ; (syncid\<^sup>\<omega> \<otimes> syncid\<^sup>\<omega>)" by (simp add: seq_assoc syncid_iter_atomic)
  also have "... = syncid\<^sup>\<omega> ; a ; syncid\<^sup>\<omega>" using atomic_iter_sync_iter atomic_sync_identity syncid_atomic by auto
  finally show ?thesis .
qed

lemma syncid_wrap_iter_par:
  assumes a_atomic[simp]: "a = (atomic p)"
  assumes b_atomic[simp]: "b = (atomic q)"
  shows "syncid\<^sup>\<omega> ; a ; syncid\<^sup>\<omega> \<otimes> syncid\<^sup>\<omega> ; b ; syncid\<^sup>\<omega> = 
                   syncid\<^sup>\<omega> ; (a \<otimes> b) ; syncid\<^sup>\<omega> \<squnion> 
                   syncid\<^sup>\<omega> ; a ; syncid\<^sup>\<omega> ; b ; syncid\<^sup>\<omega> \<squnion>
                   syncid\<^sup>\<omega> ; b ; syncid\<^sup>\<omega> ; a ; syncid\<^sup>\<omega>"
proof -
  obtain e where syncid_atomic[simp]: "syncid = (atomic e)" using syncid_atomic by blast
  have "syncid\<^sup>\<omega> ; a ; syncid\<^sup>\<omega> \<otimes> syncid\<^sup>\<omega> ; b ; syncid\<^sup>\<omega> = (syncid \<otimes> syncid)\<^sup>\<omega> ; ((a ; syncid\<^sup>\<omega> \<otimes> b ; syncid\<^sup>\<omega>) \<squnion>
                                              (a ; syncid\<^sup>\<omega> \<otimes> syncid ; syncid\<^sup>\<omega> ; b ; syncid\<^sup>\<omega>) \<squnion>
                                              (syncid ; syncid\<^sup>\<omega> ; a ; syncid\<^sup>\<omega> \<otimes> b ; syncid\<^sup>\<omega>))"
    by (simp add: atomic_iter_pre_sync_iter_pre seq_assoc)
  also have "... = (syncid \<otimes> syncid)\<^sup>\<omega> ; ((a \<otimes> b) ; (syncid\<^sup>\<omega> \<otimes> syncid\<^sup>\<omega>) \<squnion> (a \<otimes> syncid) ; (syncid\<^sup>\<omega> \<otimes> syncid\<^sup>\<omega> ; b ; syncid\<^sup>\<omega>) \<squnion> (syncid \<otimes> b) ; (syncid\<^sup>\<omega> ; a ; syncid\<^sup>\<omega> \<otimes> syncid\<^sup>\<omega>))"
    by (simp add: atomic_pre_sync_atomic_pre seq_assoc)
  also have "... = syncid\<^sup>\<omega> ; ((a \<otimes> b) ; (syncid\<^sup>\<omega> \<otimes> syncid\<^sup>\<omega>) \<squnion> a ; (syncid\<^sup>\<omega> \<otimes> syncid\<^sup>\<omega> ; b ; syncid\<^sup>\<omega>) \<squnion> b ; (syncid\<^sup>\<omega> ; a ; syncid\<^sup>\<omega> \<otimes> syncid\<^sup>\<omega>))"
    by (metis a_atomic atomic_sync_identity b_atomic sync_commute syncid_syncid)
  also have "... = syncid\<^sup>\<omega> ; ((a \<otimes> b) ; syncid\<^sup>\<omega> \<squnion> a ; (syncid\<^sup>\<omega> \<otimes> syncid\<^sup>\<omega> ; b ; syncid\<^sup>\<omega>) \<squnion> b ; (syncid\<^sup>\<omega> \<otimes> syncid\<^sup>\<omega> ; a ; syncid\<^sup>\<omega>))"
    by (metis sync_commute syncid_syncid_iter)
  also have "... = syncid\<^sup>\<omega> ; ((a \<otimes> b) ; syncid\<^sup>\<omega> \<squnion> a ; (syncid\<^sup>\<omega> ; b ; syncid\<^sup>\<omega>) \<squnion> b ; (syncid\<^sup>\<omega> ; a ; syncid\<^sup>\<omega>))"
    using syncid_iter_wrap_iter by auto
  also have "... = syncid\<^sup>\<omega> ; (a \<otimes> b) ; syncid\<^sup>\<omega> \<squnion> syncid\<^sup>\<omega> ; a ; syncid\<^sup>\<omega> ; b ; syncid\<^sup>\<omega> \<squnion> syncid\<^sup>\<omega> ; b ; syncid\<^sup>\<omega> ; a ; syncid\<^sup>\<omega>"
    by (simp add: seq_assoc seq_nondet_distrib)
  finally show ?thesis .
qed

(*
lemma syncid_wrap_iter_par_general:
  assumes a_atomic[simp]: "a = (atomic p)"
  assumes b_atomic[simp]: "b = (atomic q)"
  shows "syncid\<^sup>\<omega> ; a ; syncid\<^sup>\<omega>;c \<otimes> syncid\<^sup>\<omega> ; b ; syncid\<^sup>\<omega>;d = 
                               syncid\<^sup>\<omega> ; (a \<otimes> b) ; syncid\<^sup>\<omega>;(c \<otimes> d) \<squnion>
                               syncid\<^sup>\<omega> ; a ; syncid\<^sup>\<omega>;(c \<otimes> (syncid\<^sup>\<omega>; b ; syncid\<^sup>\<omega>;d)) \<squnion>
                               syncid\<^sup>\<omega> ; b ; syncid\<^sup>\<omega>;((syncid\<^sup>\<omega>; a ; syncid\<^sup>\<omega>;c) \<otimes> d)"
  *)


end

end
