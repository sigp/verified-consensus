theory Hoare_Logic
imports Translation_Test "algebra/rg-algebra/AbstractAtomicTest/Programming_Constructs"
begin

declare [[show_sorts=false]]


lemma "((converse (R \<triangleright> P)) `` Q) \<triangleleft> (R \<triangleright> P) = (R \<triangleright> (P \<inter> Q))" nitpick
  apply (safe; clarsimp simp: restrict_range_def Image_iff restrict_domain_def) 

lemma "(P \<inter> Q\<inverse> `` P') \<triangleleft> Q \<subseteq> (P \<inter> Q\<inverse> `` P') \<triangleleft> Q \<triangleright> P'" nitpick

lemma Id_on_relcomp_eq: "Id_on P O Id_on Q = Id_on (P \<inter> Q)" 
  by (safe; clarsimp simp: Id_on_def, rule relcompI, blast, blast)


locale hoare_logic = verified_con + strong_spec begin


definition "hoare_triple P f Q \<equiv>   run f \<le> assert P; spec (Q) "


notation hoare_triple ("\<lblot>_\<rblot> _ \<lblot>_\<rblot>")


lemma setState_spec: "(run (setState s)) \<le> spec (UNIV \<triangleright> {s}) "
  apply (clarsimp simp: spec_def)
  apply (rule conj_refine)
   apply (clarsimp simp: run_def setState_def)
  using  pspec_ref_pgm apply presburger
    apply (clarsimp simp: run_def setState_def)
  by (meson order_trans spec_ref_pgm spec_term)

lemma set_state_valid: "hoare_triple \<top> (setState s) (UNIV \<triangleright> {s})"
  apply (clarsimp simp: hoare_triple_def assert_top)
  apply (rule setState_spec)
  done

lemma getState_spec: "(run (getState)) \<le> spec (UNIV) "
  apply (clarsimp simp: spec_def)
  apply (rule conj_refine)
   apply (clarsimp simp: run_def getState_def)
  apply (simp add: Nondet_test_nil chaos_ref_nil pspec_univ)
  apply (clarsimp simp: run_def getState_def)
  by (simp add: Nondet_test_nil term_nil)

lemma getState_valid: "hoare_triple \<top> (getState) \<top>"
  apply (clarsimp simp: hoare_triple_def assert_top)
  by (simp add: getState_spec spec_test_restricts test_top)
  apply (rule setState_spec)
  done

definition "bind_rel P Q = (Id_on P) O Q "


lemma pgm_post_assert: "\<pi> (UNIV \<triangleright> S) = \<pi> (UNIV \<triangleright> S) ; assert S"
  by (metis pgm_test_post seq_assoc test_seq_assert)

lemma rewrite: "UNIV \<triangleright> (Q `` (P \<inter> {s})) = (UNIV \<triangleright> {s}) O (P \<triangleleft> Q)  "
  apply (safe; clarsimp simp: Image_iff restrict_range_def restrict_domain_def)
  by blast


lemma stutter_range_restriction: "a \<in> P \<Longrightarrow> (a,a) \<in> range_restriction P"
  apply (clarsimp)
  done

lemma stutter_range_restriction: "a \<in> P \<Longrightarrow> (a,a) \<in> Id_on P"
  apply (clarsimp)
  done

lemma restrict_domain_compose_Id: "(P \<triangleleft> Q) = ((Id_on P) O Q)" 
  apply (rule set_eqI)
  apply (safe)
   apply (clarsimp simp: restrict_range_def  restrict_domain_def, rule relcompI)
    apply (erule Id_onI, assumption)
  by (clarsimp simp: restrict_range_def  restrict_domain_def)


 


lemma test_smaller_assert: "p \<subseteq> q \<Longrightarrow> test p ; assert q = test p"
  apply (clarsimp simp: assert_def)
  apply (subst par.seq_nondet_distrib)
  by (metis assert_bot le_iff_inf seq_assoc sup_bot.right_neutral test.hom_bot test_seq_assert test_seq_compl test_seq_magic test_seq_test)



find_theorems "_ \<triangleright> _ = _"
lemma "\<lparr>Q\<rparr>; assert P \<le> \<lparr>Q \<triangleright> P\<rparr> ; assert P"
  find_theorems "spec _ ; assert _"

lemma hoare_chain: "(\<lbrace>P\<rbrace>;\<lparr>Q\<rparr>; \<lbrace>P'\<rbrace>;\<lparr>Q'\<rparr>) \<le> \<lbrace>P - (converse Q `` (-P'))\<rbrace>;\<lparr>(Q) O Q'\<rparr>" 
  apply (subst assert_restricts_spec) back
  apply (subst assert_galois_test)
  apply (subst domain_restrict_relcomp[symmetric])
  apply (rule order_trans[rotated], rule spec_seq_introduce[where p="P'"])
  apply (rule_tac y="(\<tau> (P - Q\<inverse> `` (- P')) ; \<lbrace>P\<rbrace> ; \<lparr>Q\<rparr>) ; (\<lbrace>P'\<rbrace> ; \<lparr>Q'\<rparr>)" in order_trans)
   apply (clarsimp simp: seq_assoc)
  apply (subst seq_assoc, rule seq_mono[rotated], rule order_refl)
  apply ( subst test_smaller_assert)
   apply (blast)
  apply (subst test_seq_refine)
  apply (subst test_restricts_spec)
  apply (rule seq_mono, rule order_refl)
  apply (rule spec_strengthen)
  apply (clarsimp simp: restrict_domain_def restrict_range_def Image_iff)
  apply (blast)
  done


lemma set_state_hoare_inner: "\<pi> (UNIV \<triangleright> {s}) \<le> \<lbrace>UNIV\<rbrace> ; spec (UNIV \<triangleright> {s})"
  by (simp add: assert_top spec_ref_pgm)

lemma univ_sub_neg: "UNIV - P = - P"
  apply (safe; clarsimp)
  done

lemma setState_seq: "hoare_triple P (g ()) Q  \<Longrightarrow>  hoare_triple (- (UNIV \<triangleright> {s})\<inverse> `` (- P)) (do {x <- setState s ; g x}) ( UNIV \<triangleright> {s} O Q) "
  apply (clarsimp simp: run_def bindCont_def setState_def hoare_triple_def) 
  apply (rule order_trans)
   apply (rule seq_mono, rule set_state_hoare_inner, assumption)
  apply (rule order_trans, subst seq_assoc[symmetric], rule hoare_chain)
  apply (clarsimp simp: univ_sub_neg)
  done

lemma setState_seq': "run (g ()) \<le> spec P \<Longrightarrow>  (run (do {x <- setState s ; g x})) \<le> spec (UNIV \<triangleright> {s} O P) "
  apply (clarsimp simp: run_def bindCont_def setState_def)
  apply (rule order_trans[rotated], rule spec_to_sequential)
  apply (rule seq_mono)
   apply (rule spec_ref_pgm)
  apply (assumption)
  done


lemma spec_ref_pspec: "spec P \<le> pspec P "
  apply (clarsimp simp: spec_def)
  by (simp add: conj_conjoin_non_aborting term_nonaborting)

lemma specI: "x \<le> term \<Longrightarrow> x \<le> pspec P \<Longrightarrow> x \<le> spec P"
  apply (clarsimp simp: spec_def)
  apply (rule conj_refine, assumption+)
  done

lemma pspec_strengthen: "p \<subseteq> q \<Longrightarrow> pspec p \<le> pspec q" by (erule pspec_strengthen)

lemma spec_strengthen: "p \<subseteq> q \<Longrightarrow> spec p \<le> spec q" by (erule spec_strengthen)


lemma "assert {(a, b)} ; \<lceil>P (a, b)\<rceil> \<le> \<lceil>{(s, s'). (s, s') \<in> P s}\<rceil>"
  apply (rule order_trans[rotated])
  thm pspec_strengthen[where p="P (a, b)"]
   apply (rule pspec_strengthen[where p="P (a, b)"])
   apply (clarsimp)

lemma restrict_dom_singleton: "restrict_domain {x} {x. P x} = {(a,b). a = x \<and> P (a, b) }"
  apply (clarsimp simp: restrict_domain_def)
  apply (safe)
  done

lemma assert_commute: "assert a ; assert b = assert b ; assert a"
  by (simp add: Int_commute assert_seq_assert)

lemma test_spec: "test {t} \<le> \<lbrace>UNIV\<rbrace> ; \<lparr>Id_on {t}\<rparr>"
  apply (clarsimp simp: assert_top)
  apply (rule spec_refine)
  using dual_order.trans nil_ref_test term_nil apply blast
  apply (clarsimp)
  using test_inf_eq_seq test_seq_commute test_seq_refine by fastforce

lemma "- {(a, b)} \<union> P (a, b) = R"
  apply (clarsimp simp: Compl_Diff_eq)

  find_theorems uminus "(\<union>)"

lemma getState_seq_gen: "(\<And>x. hoare_triple (P x) (g x) (Q x)) \<Longrightarrow>  hoare_triple (\<Squnion>x. P x \<inter> {x}) (bindCont getState g) ({(s, s'). (s, s') \<in> Q s})"
  apply (clarsimp simp: run_def bindCont_def getState_def)
  apply (clarsimp simp: hoare_triple_def run_def Sup_le_iff)

  apply (rule order_trans, rule seq_mono)
  apply (rule test_spec)

   apply (atomize)
   apply (erule_tac x="a" in allE)
   apply (erule_tac x="b" in allE)
  apply (assumption)
  apply (rule order_trans, subst seq_assoc[symmetric], rule hoare_chain)
  apply (clarsimp simp: Diff_eq)
  apply (rule seq_mono)
   apply (subst assert_iso[symmetric])
  apply (rule subsetI)
   using [[simp_trace]] apply (clarsimp)
  apply (rule spec_strengthen)
  apply (clarsimp)
  done
  

lemma getState_seq: "(\<And>x. run (g x) \<le> spec (P x)) \<Longrightarrow>  (run (do { x <- getState ; g (x)})) \<le> spec ({(s, s'). (s, s') \<in> P s}) "
  apply (clarsimp simp: run_def bindCont_def getState_def)
  apply (rule specI)
  apply (subst Sup_le_iff, clarsimp)
   apply (atomize)
   apply (erule_tac x="a" in allE)
  apply (erule_tac x="b" in allE)
  using nil_ref_test order_trans seq_mono spec_def spec_term apply fastforce
  apply (subst Sup_le_iff, clarsimp)
   apply (atomize)
  apply (erule_tac x="a" in allE)
  apply (erule_tac x="b" in allE)
  apply (drule order_trans, rule spec_ref_pspec)
  apply (rule order_trans, rule seq_mono, rule order_refl, assumption)
  apply (subst test_seq_refine)
  apply (subst test_restricts_pspec)
  apply (subst test_restricts_pspec) back

  apply (rule seq_mono, rule order_refl)
  apply (rule pspec_strengthen)
  apply (subst restrict_dom_singleton)
  apply (clarsimp simp: restrict_domain_def)
  done


lemma test_refines_id_spec: "\<tau> S \<le> spec (Id_on S) "
  apply (rule spec_refine; clarsimp?)
  using dual_order.trans nil_ref_test term_nil apply blast
  using test_inf_eq_seq test_seq_commute test_seq_refine by auto

lemma test_inf_singletons: "(\<tau> {x} \<sqinter> \<tau> {xa}) = (if x = xa then test {x} else \<bottom>)"
  by (metis Int_empty_right Int_insert_right_if0 insert_inter_insert singletonD test.hom_bot test.hom_inf)


lemma test_prefix_spec: "\<tau> {x} ; spec P \<le> spec {(a, b). a = x \<and> (a, b) \<in> P}" 
  apply (subst test_seq_refine)
   apply (subst test_restricts_spec)  
   apply (subst test_restricts_spec) 
   apply (rule seq_mono; clarsimp?)
   apply (rule spec_strengthen)
   apply (clarsimp simp: restrict_range_def restrict_domain_def restrict_dom_singleton Sup_le_iff)
  done


lemma spec_singletonI[intro!]: "x \<in> S \<Longrightarrow> \<lparr>{x}\<rparr> \<le> \<lparr>S\<rparr>"
  by (simp add: spec_strengthen)

lemma modify_spec: "(run (modifyState f)) \<le> assert UNIV ; spec ({(s, s'). s' = f s})"
  apply (clarsimp simp: modifyState_def)
  apply (rule order_trans, rule getState_seq_gen[simplified hoare_triple_def])
  thm setState_spec
   apply (rule set_state_valid[simplified hoare_triple_def])
  apply (clarsimp)
  apply (clarsimp simp:  assert_top)
  by (rule spec_strengthen, clarsimp simp: restrict_domain_def restrict_range_def)

lemma hoare_anti_mono: "hoare_triple P' f Q' \<Longrightarrow> P \<subseteq> P' \<Longrightarrow> P \<triangleleft> Q' \<subseteq> Q \<Longrightarrow> hoare_triple P f Q"
  apply (clarsimp simp: hoare_triple_def)
  by (meson assert_iso dual_order.trans seq_mono_left spec_strengthen_under_pre)


lemma restrict_range_UNIV[simp]: "UNIV \<triangleright> S = UNIV \<times> S "
  by (safe; clarsimp simp: restrict_range_def) 


lemma restrict_domain_UNIV[simp]: "UNIV \<triangleleft> R = R "
  by (safe; clarsimp simp: restrict_domain_def) 

lemma modify_spec_valid: "hoare_triple UNIV (modifyState f) {(s, s'). s' = f s}  "
  apply (clarsimp simp: modifyState_def)
  apply (rule hoare_anti_mono)
    apply (rule getState_seq_gen, rule set_state_valid)
   apply (clarsimp)
  by (clarsimp)



lemmas bind_assoc =  kcomp_assoc[simplified k_comp_def]

lemma bindCont_assoc: "bindCont f (\<lambda>a. bindCont (g a) h) = bindCont (bindCont f g) h"
  by (clarsimp simp: bindCont_def)


lemma if_seq: 
  "run (bindCont P c) \<le> assert S ; spec R \<Longrightarrow> run (bindCont Q c) \<le> assert S' ; spec R' \<Longrightarrow>
   run (do {x <- (if B then P else Q); c x}) \<le> assert (if B then S else S') ; spec (if B then R else R')"
  apply (clarsimp split: if_splits)
  done

lemma if_seq_valid: 
  "hoare_triple  S (bindCont P c) R \<Longrightarrow> hoare_triple S' (bindCont Q c) R' \<Longrightarrow>
   hoare_triple (if B then S else S') (do {x <- (if B then P else Q); c x}) (if B then R else R')"
  apply (clarsimp split: if_splits)
  done

find_theorems "bindCont _ return"

lemmas if_seq_valid' = if_seq_valid[where c=return, simplified bindCont_return]



lemma run_fail_assert: "run (bindCont fail c) \<le> assert {} ; \<lparr>{}\<rparr>"
  apply (clarsimp simp: run_def fail_def bindCont_def spec_def pspec_def assert_def)
  using assert_bot local.assert_def by force


lemma run_fail_assert_valid: "hoare_triple {} (bindCont fail c) R"
  apply (clarsimp simp: run_def fail_def bindCont_def spec_def pspec_def assert_def hoare_triple_def)
  using assert_bot local.assert_def by force


lemma assertion_spec: "run (c ()) \<le> assert Q; spec R \<Longrightarrow> run (do {x <- assertion P ; c x}) \<le> assert (Collect P \<inter> Q) ; spec R"
  apply (clarsimp)
  apply (clarsimp simp: assertion_def)
  apply (rule order_trans)
  apply (subst bindCont_assoc[symmetric])
   apply (rule getState_seq_gen[simplified hoare_triple_def])
   apply (rule if_seq)
    apply (clarsimp simp: bindCont_return', assumption)
   apply (rule run_fail_assert)
  apply (rule seq_mono, subst assert_iso[symmetric])
   apply (clarsimp)
  apply (rule spec_strengthen, clarsimp split: if_splits)
  done

declare in_dom_iff[simp]

lemma "x \<in> S \<triangleleft> R \<longleftrightarrow> fst x \<in> S \<and> x \<in> R"
  by (clarsimp simp: restrict_domain_def, safe; clarsimp)

lemma assertion_spec_valid: "hoare_triple Q (c ()) R \<Longrightarrow> hoare_triple (Collect P \<inter> Q) (do {x <- assertion P ; c x}) R"
  apply (rule hoare_anti_mono)
  apply (clarsimp simp: assertion_def)
  apply (subst bindCont_assoc[symmetric])+
   apply (rule getState_seq_gen)
   apply (rule if_seq_valid)
    apply (clarsimp simp: bindCont_return', assumption)
   apply (rule run_fail_assert_valid[where R="{}"])
   apply (clarsimp)
  apply (clarsimp simp:  split: if_splits)
  done

definition "wf_lens l \<longleftrightarrow> (\<forall>s v. get l (set l s v) = v)"


definition "maps_to l v s \<equiv> wf_lens l \<and> get l (fst s) = Some v" 

lemma "hoare_triple (Collect (maps_to l v)) (write_beacon l v') ({(s,s'). maps_to l v s \<and> maps_to l v' s'})"
  apply (rule hoare_anti_mono)
    apply (clarsimp simp: write_beacon_def bindCont_assoc[symmetric])
    apply (rule getState_seq_gen)
    apply (rule if_seq_valid')
     apply (rule run_fail_assert_valid[where c=return and R="{}", simplified bindCont_return] )
    apply (rule set_state_valid)
   apply (clarsimp simp: maps_to_def)
  apply (clarsimp split: if_splits)
  apply (clarsimp simp: maps_to_def )
  apply (clarsimp simp: wf_lens_def)
  done

lemma ifM_seq: "(run (do {x <- ifM B P Q; c x})) \<le> spec R"
  apply (clarsimp simp: ifM_def bindCont_def run_def)


end


end