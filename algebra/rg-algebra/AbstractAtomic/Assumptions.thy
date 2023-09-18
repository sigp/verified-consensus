section \<open>assumption definition\<close>

theory Assumptions
imports
  "Atomic_Commands"
begin

locale atomic_assump = atomic_commands 
begin

definition assump :: "'a \<Rightarrow> 'a"
  where "assump c \<equiv> (if c \<in> range(atomic) then 
                        (let p = (THE p. atomic p = c) in (atomic(p) \<squnion> (atomic.negate(atomic(p)));\<top>))
                     else undefined)"

lemma assump_atomic:
  assumes a_def: "a = atomic p"
  shows "assump a = a \<squnion> (atomic.negate a); \<top>"
proof -
  define P where "P \<equiv> (\<lambda>p'. atomic p' = atomic p)"
  have "P p" unfolding P_def by simp
  moreover have "\<And>p'. P p' \<Longrightarrow> p' = p"
    unfolding P_def using atomic.hom_injective unfolding inj_def by auto
  ultimately have a1: "(THE p'. P p') = p"
    using theI by blast
  have "assump (atomic p) = (let p' = (THE p'. atomic p' = (atomic p)) in (atomic(p') \<squnion> (atomic.negate(atomic(p')));\<top>))"
    unfolding assump_def by auto
  also have "... = atomic(p) \<squnion> (atomic.negate(atomic(p)));\<top>"
    using atomic.hom_injective a1 unfolding P_def by simp
  finally show ?thesis using a_def by simp
qed

lemma assump_conj_atomic: "assump(atomic p) \<iinter> atomic p = atomic p"
  proof -
    have a1: "assump(atomic p) \<iinter> atomic p = ((atomic p) \<iinter> (atomic p)) \<squnion> (atomic.negate(atomic p);\<top> \<iinter> (atomic p))"
        by (simp add: assump_atomic conj.nondet_sync_distrib)
    then have a2: "... = (atomic p) \<squnion> \<bottom>"
        by (metis atomic_conj_inf atomic.hom_inf atomic.hom_not atomic_seq_abort_conj_right 
              atomic.hom_bot conj_idem inf_compl_bot local.conj_commute seq_magic_left)
    thus ?thesis by (simp add: a1)
  qed   

lemma helper1: 
  "(atomic.negate(atomic p);\<top> \<iinter> atomic q) \<squnion> (atomic p \<iinter> (atomic.negate(atomic q));\<top>) \<squnion> ((atomic.negate(atomic p));\<top> \<iinter> (atomic.negate(atomic q));\<top>)
   = (((atomic.negate(atomic p))\<iinter> atomic q) \<squnion> (atomic p \<iinter> (atomic.negate(atomic q))) \<squnion> ((atomic.negate(atomic p)) \<iinter> (atomic.negate(atomic q))));\<top>" 
    using atomic_seq_bot_conj_inf_distrib by (metis atomic.hom_not) 
   
lemma helper2:
   "((atomic.negate(atomic p)\<iinter> atomic q) \<squnion> (atomic p \<iinter> atomic.negate(atomic q)) \<squnion> (atomic.negate(atomic p) \<iinter> atomic.negate(atomic q)))
    = atomic.negate(atomic(p \<sqinter> q))" 
proof -
  have a0: "-(p \<squnion> -q) \<squnion> -(-p \<squnion> q) \<squnion> -(p \<squnion> q) = -(p \<sqinter> q)"
     by (simp add: inf_sup_aci(7) sup_aci(1) sup_inf_distrib1)

  have a1: "(atomic.negate(atomic p)\<iinter> atomic q) \<squnion> (atomic p \<iinter> atomic.negate(atomic q)) \<squnion> (atomic.negate(atomic p) \<iinter> atomic.negate(atomic q))
             = ((atomic(-p) \<iinter> atomic(q)) \<squnion> (atomic(p) \<iinter> atomic(-q)) \<squnion> (atomic(-p) \<iinter> atomic(-q)))" by simp
  then have a2: "... = (atomic(-p \<sqinter> q) \<squnion> atomic(p \<sqinter> -q) \<squnion> atomic(-p \<sqinter> -q))"
    using atomic_conj_inf atomic.hom_inf by presburger
  thus ?thesis using a1 a2 unfolding atomic.hom_not
    using atomic.hom_inf a0 by (metis (no_types, lifting) atomic.hom_sup compl_sup double_compl)
qed


(* uses helper1 and helper2 *)

lemma assump_conj: 
  assumes a_def: "a = atomic p"
  assumes b_def: "b = atomic q"
  shows "assump(a) \<iinter> assump(b) = assump(a \<sqinter> b)"
proof -
  have a1: "assump(a) \<iinter> assump(b) = (a \<squnion> (atomic.negate a); \<top>) \<iinter> (b \<squnion> (atomic.negate b);\<top>)" 
    using a_def b_def assump_atomic by auto
  also have a2: "... = (a \<iinter> b) \<squnion> ((atomic.negate a);\<top> \<iinter> b) \<squnion> (a \<iinter> (atomic.negate b);\<top>) 
                          \<squnion> ((atomic.negate a);\<top> \<iinter> (atomic.negate b);\<top>)"
    by (metis (no_types) conj.nondet_sync_distrib4 sup.commute conj.nondet_sync_distrib) 
  also have a3: "... = (a \<iinter> b) \<squnion> (((atomic.negate a)\<iinter> b) \<squnion> (a \<iinter> (atomic.negate b))
                          \<squnion> ((atomic.negate a) \<iinter> (atomic.negate b)));\<top>"
    using a_def b_def by (metis (no_types, lifting) helper1 sup.assoc)
  also have a4: "... = (atomic(p) \<iinter> atomic(q)) \<squnion> atomic.negate(atomic(p) \<iinter> atomic(q));\<top>"
    using a_def atomic_conj_inf b_def helper2 by auto
  thus ?thesis using a1 a2 a3 a4 by (metis a_def assump_atomic atomic_conj_inf atomic.hom_inf b_def) 
qed

lemma assump_inter: "assump(atomic p) \<squnion> assump(atomic q) = assump(atomic p \<sqinter> atomic q)"
proof -
  have p_minus_q: "p-q \<le> -(p \<sqinter> q)" by (simp add: diff_eq le_infI2) 
  have q_minus_p: "q-p \<le> -(p \<sqinter> q)" by (simp add: diff_eq le_infI2) 
  then have a1: "assump(atomic p) \<squnion> assump(atomic q) = (atomic p \<squnion> atomic q) \<squnion> (atomic.negate(atomic p);\<top> \<squnion> atomic.negate(atomic q);\<top>)"
      by (simp add: assump_atomic sup_assoc sup_left_commute) 
  then have a2: "... = atomic(p \<sqinter> q) \<squnion> atomic(p-q) \<squnion> atomic(q-p) \<squnion> atomic(-(p \<sqinter> q));\<top>"       
    using compl_sup diff_eq double_compl inf_compl_bot inf_sup_distrib1 sup_bot.right_neutral atomic.hom_sup
         by (metis (no_types, lifting) atomic.hom_not nondet_seq_distrib) 
  then have a3: "... = atomic(p \<sqinter> q) \<squnion> atomic(-(p \<sqinter> q));\<top>"  using p_minus_q q_minus_p atomic_abort_absorb
       by (metis (full_types) sup.semigroup_axioms semigroup.assoc)
  thus ?thesis using a1 a2 a3 by (metis assump_atomic atomic.hom_inf atomic.hom_not) 
qed


lemma assump_mono: 
  assumes p_q_ref: "p \<le> q"  
  shows "assump(atomic p) \<ge> assump(atomic q)"
  by (metis assump_inter atomic.hom_inf inf.orderE le_iff_sup p_q_ref sup_commute)

lemma assump_mono2:
  assumes atomic_p_q_ref: "atomic q \<ge> atomic p"  
  shows "assump(atomic p) \<ge> assump(atomic q)"
     by (simp add: assump_mono atomic.hom_iso atomic_p_q_ref)

lemma assump_iter:
  assumes a_atomic[simp]: "a = atomic p"
  shows "(assump a)\<^sup>\<omega> = a\<^sup>\<omega> \<squnion> a\<^sup>\<omega>;atomic.negate a;\<top>"
proof -
  have "(assump a)\<^sup>\<omega> = a\<^sup>\<omega> ; (atomic.negate a ; \<top> ; a\<^sup>\<omega>)\<^sup>\<omega>" by (simp add: assump_atomic par.iter_decomp)  
  also have "\<dots> = a\<^sup>\<omega> \<squnion> a\<^sup>\<omega> ; atomic.negate a ; \<top> ; a\<^sup>\<omega> ; (atomic.negate a ; \<top> ; a\<^sup>\<omega>)\<^sup>\<omega>"
  proof -
    have "a\<^sup>\<omega> ; (atomic.negate a ; \<top> ; a\<^sup>\<omega>)\<^sup>\<omega> = a\<^sup>\<omega> ; nil \<squnion> a\<^sup>\<omega> ; (atomic.negate a ; \<top> ; a\<^sup>\<omega> ; (atomic.negate a ; \<top> ; a\<^sup>\<omega>)\<^sup>\<omega>)"
      by (metis (no_types) iter_unfold par.seq_nondet_distrib)
    then show ?thesis
      using sequential.seq_assoc sequential_axioms by fastforce
  qed
 thus ?thesis using calculation seq_assoc by auto 
qed

lemma assump_help1: 
  assumes a_atomic[simp]: "a = atomic p"
  assumes b_atomic[simp]: "b = atomic q"
  shows "a\<^sup>\<omega> \<iinter> b\<^sup>\<omega>;atomic.negate b;\<top> = (a \<sqinter> b)\<^sup>\<omega> ; (a \<sqinter> atomic.negate b) ; \<top>"
proof -
  have nb_atomic: "\<exists>r . atomic.negate b = atomic r" by (metis atomic.hom_not b_atomic) 
  thus ?thesis 
    using conj.atomic_iter_sync_iter_atom_pre a_atomic b_atomic nb_atomic
          atomic_conj_inf conj_abort_right by auto  
qed

lemma assump_help2: 
  assumes a_atomic[simp]: "a = atomic p"
  assumes b_atomic[simp]: "b = atomic q"
  shows "a\<^sup>\<omega>;atomic.negate a;\<top> \<iinter> b\<^sup>\<omega>;atomic.negate b;\<top> = 
         (a \<sqinter> b)\<^sup>\<omega> ; ((atomic.negate a \<sqinter> atomic.negate b) \<squnion> (atomic.negate a \<sqinter> b) \<squnion> (a \<sqinter> atomic.negate b)) ; \<top>"
proof -
  have na_atomic: "\<exists>r . atomic.negate a = atomic r" by (metis atomic.hom_not a_atomic) 
  have nb_atomic: "\<exists>r . atomic.negate b = atomic r" by (metis atomic.hom_not b_atomic)
  have "a\<^sup>\<omega>;atomic.negate a;\<top> \<iinter> b\<^sup>\<omega>;atomic.negate b;\<top> =
        (a \<sqinter> b)\<^sup>\<omega> ; ((atomic.negate a \<sqinter> atomic.negate b);\<top> \<squnion> (atomic.negate a \<sqinter> b);\<top> \<squnion> (a \<sqinter> atomic.negate b);\<top>)"
    using conj.atomic_iter_pre_sync_iter_pre_atomic a_atomic b_atomic na_atomic nb_atomic
          atomic_conj_inf conj_abort_right conj.sync_commute nondet_seq_distrib seq_assoc
    proof -
      obtain bb :: 'b where
        f1: "atomic.negate a = atomic bb"
        using na_atomic by blast
      then have "atomic.negate a \<sqinter> b = atomic bb \<iinter> atomic q"
        by (simp add: atomic_conj_inf)
      then show ?thesis
        using f1 atomic_conj_inf conj.atomic_iter_pre_sync_iter_pre_atomic nb_atomic
              a_atomic b_atomic conj_abort_left conj_abort_right by auto
    qed
  thus ?thesis by (simp add: nondet_seq_distrib seq_assoc) 
qed

lemma assump_help3:
  assumes a_atomic[simp]: "a = atomic p"
  assumes b_atomic[simp]: "b = atomic q"  
  shows "(a \<sqinter> atomic.negate b) \<squnion> (atomic.negate a \<sqinter> b) \<squnion> (atomic.negate a \<sqinter> atomic.negate b) = atomic.negate(a \<sqinter> b)"
  unfolding a_atomic b_atomic atomic.hom_not
    by (metis (full_types) atomic_conj_inf atomic.hom_inf atomic.hom_not  
      helper2 inf_sup_aci(5))

lemma assump_iter_conj:
  assumes a_atomic: "a = atomic p"
  assumes b_atomic: "b = atomic q"
  shows "(assump a)\<^sup>\<omega> \<iinter> (assump b)\<^sup>\<omega> = (assump (a \<sqinter> b))\<^sup>\<omega>"
proof -
  have "(assump a)\<^sup>\<omega> \<iinter> (assump b)\<^sup>\<omega> = (a\<^sup>\<omega> \<squnion> a\<^sup>\<omega>;atomic.negate a;\<top>) \<iinter> (b\<^sup>\<omega> \<squnion> b\<^sup>\<omega>;atomic.negate b;\<top>)"
    using assump_iter by (simp add: a_atomic b_atomic) 
  also have "\<dots> = (a\<^sup>\<omega> \<iinter> b\<^sup>\<omega>) \<squnion> (a\<^sup>\<omega> \<iinter> b\<^sup>\<omega>;atomic.negate b;\<top>) \<squnion> (a\<^sup>\<omega>;atomic.negate a;\<top> \<iinter> b\<^sup>\<omega>) \<squnion>
                  (a\<^sup>\<omega>;atomic.negate a;\<top> \<iinter> b\<^sup>\<omega>;atomic.negate b;\<top>)" using conj.nondet_sync_product by blast
  also have "\<dots> = (a \<sqinter> b)\<^sup>\<omega> \<squnion>
                  (a \<sqinter> b)\<^sup>\<omega> ; (a \<sqinter> atomic.negate b) ; \<top> \<squnion> 
                  (a \<sqinter> b)\<^sup>\<omega> ; (atomic.negate a \<sqinter> b) ; \<top> \<squnion>
                  (a\<^sup>\<omega>;atomic.negate a;\<top> \<iinter> b\<^sup>\<omega>;atomic.negate b;\<top>)" 
    using assump_help1
    by (simp add: a_atomic atomic_conj_inf b_atomic conj.atomic_iter_sync_iter conj.sync_commute 
                  inf.sync_commute) 
  also have "\<dots> = (a \<sqinter> b)\<^sup>\<omega> \<squnion> 
                  (a \<sqinter> b)\<^sup>\<omega> ; (a \<sqinter> atomic.negate b) ; \<top> \<squnion> 
                  (a \<sqinter> b)\<^sup>\<omega> ; (atomic.negate a \<sqinter> b) ; \<top> \<squnion> 
                  (a \<sqinter> b)\<^sup>\<omega> ; ((atomic.negate a \<sqinter> atomic.negate b) \<squnion> (atomic.negate a \<sqinter> b) \<squnion> (a \<sqinter> atomic.negate b)) ; \<top>"
    using assump_help2 by (simp add: a_atomic b_atomic) 
  also have "\<dots> = (a \<sqinter> b)\<^sup>\<omega> \<squnion>
                  (a \<sqinter> b)\<^sup>\<omega> ; (a \<sqinter> atomic.negate b) ; \<top> \<squnion> 
                  (a \<sqinter> b)\<^sup>\<omega> ; (atomic.negate a \<sqinter> b) ; \<top> \<squnion> 
                  (a \<sqinter> b)\<^sup>\<omega> ; (atomic.negate a \<sqinter> atomic.negate b) ; \<top>"
    by (simp add: sup_commute sup_left_commute nondet_seq_distrib par.seq_nondet_distrib)
  also have "\<dots> = (a \<sqinter> b)\<^sup>\<omega> ; 
                  (nil \<squnion> ((a \<sqinter> atomic.negate b) \<squnion> (atomic.negate a \<sqinter> b) \<squnion> (atomic.negate a \<sqinter> atomic.negate b)) ; \<top>)"
    by (simp add: sup_assoc nondet_seq_distrib par.seq_nondet_distrib seq_assoc)
  also have "\<dots> = (a \<sqinter> b)\<^sup>\<omega> ; (nil \<squnion> atomic.negate(a \<sqinter> b) ; \<top>)" using assump_help3
    by (simp add: a_atomic b_atomic)
  thus ?thesis by (metis a_atomic assump_iter atomic.hom_inf b_atomic calculation 
                         par.seq_nondet_distrib seq_assoc seq_nil_right) 
qed


(* canonical form proof:
lemma assump_distrib_seq:
  assumes a_atomic: "a = atomic p"
  shows "(assump a)\<^sup>\<omega> \<iinter> c;d = ((assump a)\<^sup>\<omega> \<iinter> c);((assump a)\<^sup>\<omega> \<iinter> d)" 
proof -
  have a1: "(assump a)\<^sup>\<omega> \<iinter> c;d = (a\<^sup>\<omega> \<sqinter> a\<^sup>\<omega>;negate a;\<bottom>) \<iinter> c;d"
    by (simp add: assms assump_iter)
  then have a2: "... = (a\<^sup>\<omega> \<iinter> c;d) \<sqinter> (a\<^sup>\<omega>;negate a;\<bottom> \<iinter> c;d)"
    using inf_conj_distrib by blast
  then have a3: "... = (a\<^sup>\<omega> \<iinter> c);(a\<^sup>\<omega> \<iinter> d) \<sqinter> (a\<^sup>\<omega>;negate a;\<bottom> \<iinter> c;d)"
    by (simp add: assms atomic_inf_conj_distrib_seq)
  thus ?thesis sorry
qed
*)

end
end
