theory Scraps
begin

lemma compile_if: "(\<Squnion>x\<in>A. \<tau> {x} ;
          (if P A x then f a x else g a x) (c x A)) = (\<Squnion>x\<in>(Collect (P A)) \<inter> A. \<tau> {x}; f a x (c x A)) \<squnion> (\<Squnion>x\<in>(-Collect (P A)) \<inter> A. \<tau> {x} ; g a x (c x A))" sorry

lemma compile_get: "(\<Squnion>x\<in>A. \<tau> {x} ;
          (if get l x = None then fail else return (the (get l x))) f) = (\<Squnion>x\<in>(dom (get l)) \<inter> A. \<tau> {x}; f (the (get l x))) \<squnion> (\<Squnion>x\<in>(-dom (get l)) \<inter> A. \<tau> {x} ; \<top>)"
  apply (subst if_distribR)
  apply (clarsimp simp: fail_def)
  apply (clarsimp simp: return_def split: if_splits)
  apply (intro antisym)
   apply (subst SUP_le_iff; clarsimp)
   apply (intro conjI impI)
  apply (rule order_trans[rotated], rule sup_ge2)
thm sup.commute
  thm SUP_upper2
    apply (rule_tac i="(a,b)" in SUP_upper2; clarsimp simp: fail_def)
  apply (rule order_trans[rotated], rule sup_ge1)
    apply (rule_tac i="(a,b)" in SUP_upper2; clarsimp simp: return_def)

  apply (clarsimp simp: SUP_le_iff)
  apply (intro conjI impI allI ballI)
   apply (clarsimp)
   apply (clarsimp simp: SUP_le_iff)
   apply (rule_tac i="(a, b)" in SUP_upper2; clarsimp)
   apply (clarsimp simp: fail_def return_def)
  apply (clarsimp)
  apply (erule contrapos_np)
  by (rule_tac i="(a, b)" in SUP_upper2; clarsimp simp: fail_def)
   apply (clarsimp simp: fail_def return_def)
   apply (intro conjI impI)
  apply (simp add: seq_mono_right)

  apply (case_tac "get(aa, ba)"
  apply (clarsimp)
  apply (clarsimp simp: fail_def)

    apply (rule_tac i="x" in SUP_upper2; clarsimp)

   apply (subst SUP_le_iff; clarsimp)

    apply (subst assert_galois_test)
    apply (clarsimp simp: test_seq_test seq.assoc[symmetric])
    apply (subst inf.test_sync_to_inf)
    apply (clarsimp simp: get_dom_inter_none)
   apply (clarsimp simp: return_def)
  apply (rule_tac i="(a,b)" in SUP_upper2; clarsimp)

   apply (subst assert_galois_test)
    apply (clarsimp simp: test_seq_test seq.assoc[symmetric])
   apply (subst inf.test_sync_to_inf)
   apply (clarsimp simp: get_dom_inter)
   apply (simp add: test_seq_refine)
  apply (subst SUP_le_iff; clarsimp)
  apply (rule_tac i="(a,b)" in SUP_upper2; clarsimp)
  apply (intro conjI impI; clarsimp?)


lemma "\<tau> {x} ; (\<Squnion>y. \<tau> {y} ; f x y) = (\<tau> {x} ; f x x)"
  by (simp add: test_restricts_Nondet)


lemma restrict_univ_singleton: "{x} \<triangleleft> (UNIV \<times> A) = ({x} \<times> A)"
  by (safe; clarsimp simp: restrict_domain_def)

lemma test_restricts_Nondet_gen: "\<tau>(B);(\<Squnion>s\<in>A. \<tau>({s});f s A B) = (\<Squnion>s\<in>(A \<inter> B). \<tau>({s});f s A B)" sorry

lemma pgm_restricts_Nondet_gen: "\<tau>(B);(\<Squnion>s\<in>A. pgm({(s, f s A B)});g s A B) = (\<Squnion>s\<in>(A \<inter> B). pgm({(s, f s A B)});g s A B)" sorry


end