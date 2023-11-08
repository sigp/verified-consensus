section \<open>Strong specification command.\<close>

theory Specification
imports
  "Constrained_Atomic_Commands"
  "Termination"
  "PartialSpecification"
begin

locale strong_spec = partial_spec + term_op (* TODO Check this *)

begin

text \<open>Given a binary relation on states q, a specification command
  started in a state $\sigma$ terminates in a state $\sigma'$, 
  such that $(\sigma,\sigma') \in q$, unless no such state $\sigma'$
  exists, in which case the command is infeasible from state $\sigma$.
\<close> 
definition spec :: "'b rel \<Rightarrow> 'a::refinement_lattice"   ( "\<lparr>_\<rparr>" 99) 
  where "spec q = (pspec q) \<iinter> term"

lemma test_conj_post:
  assumes chaos_c: "chaos \<ge> c"
  assumes chaos_d: "chaos \<ge> d"
  shows "c;\<tau>(q) \<sqinter> d = (c \<sqinter> d);\<tau>(q)"
proof -
  have "c;\<tau>(q) \<sqinter> d = c;\<tau>(q) \<iinter> d"
    using conj_to_inf_nonaborting chaos_c chaos_d nil_ref_test seq_mono seq_nil_right by metis
  also have "... = (c \<iinter> d);\<tau>(q)"
    using conj.test_sync_post conj_commute by simp
  also have "... = (c \<sqinter> d);\<tau>(q)"
    using conj_to_inf_nonaborting chaos_c chaos_d by simp
  finally show ?thesis .
qed

lemma old_spec: "\<lparr>q\<rparr> = (\<Squnion>s. (\<tau>({s});term;\<tau>(q``{s})))"
proof -
  have "\<lparr>q\<rparr> = \<lceil>q\<rceil> \<iinter> term"
    using spec_def by simp
  also have "... = \<lceil>q\<rceil> \<sqinter> term"
    using pspec_chaos conj_to_inf_nonaborting term_nonaborting by simp
  also have "... = (\<Squnion>s. (\<tau>({s});chaos;\<tau>(q``{s}))) \<sqinter> term"
    using pspec_def by simp
  also have "... = (\<Squnion>s. (\<tau>({s});chaos;\<tau>(q``{s})) \<sqinter> term)"
    by (rule Hilbert_Choice.complete_distrib_lattice_class.SUP_inf)
  also have "... = (\<Squnion>s. (((\<tau>({s});chaos) \<sqinter> term);(\<tau>(q``{s}))))"
    using test_conj_post term_nonaborting by (simp add: test_seq_refine)
  also have "... = (\<Squnion>s. (\<tau>({s});(chaos \<sqinter> term);(\<tau>(q``{s}))))"
    using test_inf_interchange2 by simp
  also have "... = (\<Squnion>s. (\<tau>({s});term;\<tau>(q``{s})))"
    using inf.sync_commute term_nonaborting by (simp add: inf.absorb1)
  finally show ?thesis .
qed

lemma spec_strengthen:
  assumes strengthen: "q2 \<subseteq> q1"
  shows "\<lparr>q1\<rparr> \<ge> \<lparr>q2\<rparr>"
  using conj.sync_mono_left pspec_strengthen spec_def strengthen
  by simp

lemma spec_univ: "\<lparr>UNIV\<rparr> = term"
  using pspec_univ spec_def
  by simp

lemma spec_term: "term \<ge> \<lparr>q\<rparr>"
proof -
  have "term = \<lparr>\<top>\<rparr>" using spec_univ by simp
  also have "... \<ge> \<lparr>q\<rparr>" using spec_strengthen by simp
  finally show ?thesis .
qed   

lemma test_restricts_spec: "\<tau>(p);\<lparr>q\<rparr> = \<tau>(p);\<lparr>p \<triangleleft> q\<rparr>"
  using spec_def test_conj_distrib test_restricts_pspec
  by force

lemma assert_restricts_spec: "\<lbrace>p\<rbrace>;\<lparr>q\<rparr> = \<lbrace>p\<rbrace>;\<lparr>p \<triangleleft> q\<rparr>"
  by (metis assert_seq_test seq_assoc test_restricts_spec)

lemma spec_strengthen_under_pre:
  assumes s: "p \<triangleleft> q2 \<subseteq> q1"
  shows  "\<lbrace>p\<rbrace>;\<lparr>q1\<rparr> \<ge> \<lbrace>p\<rbrace>;\<lparr>q2\<rparr>"
  using assert_restricts_spec spec_strengthen
  by (metis s seq_mono_right)

lemma spec_test_restricts: "\<lparr>q \<triangleright> p\<rparr> = \<lparr>q\<rparr>;\<tau>(p)"
  using conj.test_sync_post local.conj_commute pspec_test_restricts spec_def
  by simp

lemma spec_assert_restricts: "\<lparr>q \<triangleright> p\<rparr>;\<lbrace>p\<rbrace> = \<lparr>q \<triangleright> p\<rparr>"
proof -
  have "\<lparr>q \<triangleright> p\<rparr>;\<lbrace>p\<rbrace> = \<lparr>q\<rparr>;(\<tau> p);\<lbrace>p\<rbrace>" 
    by (simp add: spec_test_restricts)
  also have "... = \<lparr>q\<rparr>;(\<tau> p)"
    by (simp add: seq_assoc test_seq_assert)
  also have "... = \<lparr>q \<triangleright> p\<rparr>"
    by (simp add: spec_test_restricts)
  finally show ?thesis by simp
qed 

lemma spec_refine:
  assumes terminates: "term \<ge> c"
  assumes refine: "\<forall>s. c;\<tau>(q``{s}) \<ge> \<tau>({s});c"
  shows "\<lparr>q\<rparr> \<ge> c"
(*
  using assms conj_refine pspec_refine spec_def term_nonaborting
  by auto
*)
proof -
  have "\<lparr>q\<rparr> = \<lceil>q\<rceil> \<iinter> term"
    using spec_def by simp
  also have "... \<ge> c \<iinter> term" (is "_ \<ge> ?rhs")
    using pspec_refine assms conj.sync_mono_left term_nonaborting by simp
  also have "?rhs = c \<sqinter> term"
    using terminates conj_to_inf_nonaborting term_nonaborting by simp
  also have "... = c"
    using inf.absorb1 terminates by auto
  finally show ?thesis .
qed

lemma spec_test_post: "\<lparr>q \<triangleright> p\<rparr> = \<lparr>q \<triangleright> p\<rparr>;\<tau>(p)"
proof -
  have a1: "q \<triangleright> p = (q \<triangleright> p) \<triangleright> p"
    using restrict_range_def by auto
  have "\<lparr>q \<triangleright> p\<rparr> = \<lparr>q \<triangleright> p\<rparr>;\<tau>(p)"
    using a1 spec_test_restricts by metis
  then show ?thesis .  
qed

lemma spec_test_commute : "\<lparr>q\<rparr>;\<tau>(q``p) \<ge> \<tau>(p);\<lparr>q\<rparr>"
proof -
  have "\<lparr>q\<rparr>;\<tau>(q``p) = (\<lceil>q\<rceil> \<iinter> term);\<tau>(q``p)"
    using spec_def by simp
  also have "... = \<lceil>q\<rceil>;\<tau>(q``p) \<iinter> term"
    using conj.test_sync_post local.conj_commute by simp
  also have "... \<ge> \<tau>(p);\<lceil>q\<rceil> \<iinter> term" (is "_ \<ge> ?rhs")
    using pspec_test_commute conj.sync_mono_left by simp
  also have "?rhs = \<tau>(p);(\<lceil>q\<rceil> \<iinter> term)"
    using conj.nonaborting_sync_test_pre local.conj_commute term_nonaborting by simp
  also have "... = \<tau>(p);\<lparr>q\<rparr>"
    using spec_def by simp
  finally show ?thesis .
qed

lemma spec_to_sequential:
  shows "\<lparr>a O b\<rparr> \<ge> \<lparr>a\<rparr>;\<lparr>b\<rparr>"
proof -
  have "\<lparr>a O b\<rparr> = \<lceil>a O b\<rceil> \<iinter> term"
    using spec_def by simp
  also have "... \<ge> \<lceil>a\<rceil>;\<lceil>b\<rceil> \<iinter> term" (is "_ \<ge> ?rhs")
    using pspec_to_sequential conj.sync_mono_left by simp
  also have "?rhs = \<lceil>a\<rceil>;\<lceil>b\<rceil> \<iinter> term;term"
    using seq_term_term by simp
  also have "... \<ge> (\<lceil>a\<rceil> \<iinter> term);(\<lceil>b\<rceil> \<iinter> term)" (is "_ \<ge> ?rhs")
    using seq_conj_interchange by simp
  also have "?rhs = \<lparr>a\<rparr>;\<lparr>b\<rparr>"
    using spec_def by simp
  finally show ?thesis .
qed

lemma spec_seq_introduce: 
  shows "\<lparr>a O b\<rparr> \<ge> \<lparr>a \<triangleright> p\<rparr>;\<lbrace>p\<rbrace>;\<lparr>b\<rparr>"
proof -
  have "\<lparr>a O b\<rparr> \<ge> \<lparr>a\<rparr>;\<lparr>b\<rparr>" (is "_ \<ge> ?rhs")
    using spec_to_sequential by simp
  also have "?rhs \<ge> \<lparr>a \<triangleright> p\<rparr>;\<lparr>b\<rparr>"
    using spec_strengthen
    by (metis nil_ref_test seq_mono_left seq_mono_right seq_nil_right spec_test_restricts) 
  finally show ?thesis using spec_assert_restricts by auto
qed

lemma par_spec_spec: "\<lparr>q1\<rparr> \<parallel> \<lparr>q2\<rparr> = \<lparr>q1 \<inter> q2\<rparr>"    
proof -
  have "\<lparr>q1\<rparr> \<parallel> \<lparr>q2\<rparr> = (\<lceil>q1\<rceil> \<iinter> term) \<parallel> (\<lceil>q2\<rceil> \<iinter> term)"
    using spec_def by simp
  also have "... = \<lceil>q1\<rceil> \<iinter> \<lceil>q2\<rceil> \<iinter> (term \<parallel> term)"
    using local.conj_assoc local.conj_commute par_commute pspec_distrib_par by simp
  also have "... = \<lceil>q1\<rceil> \<iinter> \<lceil>q2\<rceil> \<iinter> term"
    using par_term_term by simp
  also have "... = \<lceil>q1 \<inter> q2\<rceil> \<iinter> term"
    using conj_pspec_pspec by simp
  also have "... = \<lparr>q1 \<inter> q2\<rparr>"
    using spec_def by simp
  finally show ?thesis .
qed

lemma conj_spec_spec: "\<lparr>q1\<rparr> \<iinter> \<lparr>q2\<rparr> = \<lparr>q1 \<inter> q2\<rparr>"
  using conj_conj_distrib_left conj_pspec_pspec local.conj_commute spec_def by auto

lemma spec_par_term: "\<lparr>q\<rparr> \<parallel> term = \<lparr>q\<rparr>"
  using par_spec_spec spec_univ by (metis inf_top.right_neutral)

lemma spec_chain: 
  assumes recomp_ab: "a O b \<subseteq> c"
  shows "\<lparr>c\<rparr> \<ge> \<lparr>a\<rparr>;\<lparr>b\<rparr>"
  using spec_strengthen spec_to_sequential recomp_ab order_trans by metis

lemma spec_conj_term: "\<lparr>q1\<rparr> = \<lparr>q1\<rparr> \<iinter> term"
proof -
  have "\<lparr>q1\<rparr> = \<lparr>q1 \<sqinter> \<top>\<rparr>"
    by simp
  also have "... = \<lparr>q1\<rparr> \<iinter> \<lparr>\<top>\<rparr>"
    using conj_spec_spec by metis
  also have "... = \<lparr>q1\<rparr> \<iinter> term"
    using spec_univ by simp
  finally show ?thesis .
qed

lemma atomic_terminating: "term \<ge> atomic(\<top>)"
proof -
  have "term = (\<pi>(\<top>) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>"
    by (rule term_def)
  also have "... \<ge> (\<pi>(\<top>) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;nil" (is "_ \<ge> ?rhs")
    using iter0 seq_mono_right by blast
  also have "?rhs = (\<pi>(\<top>) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>"
    by simp
  also have "... \<ge> \<pi>(\<top>) \<squnion> \<epsilon>(\<top>)" (is "_ \<ge> ?rhs")
    by (rule fiter1)
  also have "?rhs \<ge> atomic(\<top>)"
    using Atomic_def2 atomic.Hom_ref_hom env.Hom_def pgm.Hom_def by auto
  finally show ?thesis .
qed

lemma spec_ref_pgm:
  shows "\<lparr>q\<rparr> \<ge> \<pi>(q)"
proof -
  have "\<lparr>q\<rparr> = \<lceil>q\<rceil> \<iinter> term"
    using spec_def by simp
  also have "... \<ge> \<pi>(q) \<iinter> term" (is "_ \<ge> ?rhs")
    using conj.sync_mono_left pspec_ref_pgm by simp
  also have "?rhs \<ge> \<pi>(q) \<iinter> atomic(\<top>)" (is "_ \<ge> ?rhs")
    using atomic_terminating conj.sync_mono_right by simp
  also have "?rhs \<ge> \<pi>(q)"
    using Atomic_ref_pgm atomic.Hom_def conj_refine by auto
  finally show ?thesis .
qed

lemma spec_ref_env:
  shows "\<lparr>q\<rparr> \<ge> \<epsilon>(q)"
proof -
  have "\<lparr>q\<rparr> = \<lceil>q\<rceil> \<iinter> term"
    using spec_def by simp
  also have "... \<ge> \<epsilon>(q) \<iinter> term" (is "_ \<ge> ?rhs")
    using conj.sync_mono_left pspec_ref_env by simp
  also have "?rhs \<ge> \<epsilon>(q) \<iinter> atomic(\<top>)" (is "_ \<ge> ?rhs")
    using atomic_terminating conj.sync_mono_right by simp
  also have "?rhs \<ge> \<epsilon>(q)"
    using Atomic_ref_env atomic.Hom_def conj_refine by auto
  finally show ?thesis .
qed

lemma spec_to_test:
  shows "\<lparr>q\<rparr> \<ge> \<tau>({s. (s,s) \<in> q})"
proof -
  define p where "p \<equiv> {s. (s,s) \<in> q}"
  have "\<forall>s. {s} \<inter> p \<subseteq> p \<inter> q``{s}"
    unfolding restrict_range_def p_def by auto
  then have "\<forall>s. \<tau>(p);\<tau>(q``{s}) 
            \<ge> \<tau>({s});\<tau>(p)"
    by (simp add: test.hom_iso test_seq_test)
  moreover have "term \<ge> \<tau>(p)"
    using term_def fiter0 iter0 seq_mono nil_ref_test order_trans by fastforce 
  ultimately show ?thesis using spec_refine p_def by simp
qed

lemma spec_ref_opt:
  shows "\<lparr>q\<rparr> \<ge> opt q"
  unfolding opt_def using spec_to_test spec_ref_pgm by simp

lemma spec_id_nil: "\<lparr>Id\<rparr> \<ge> nil"
proof -
  have "{s. (s, s) \<in> Id} = UNIV" by auto
  then show ?thesis using spec_to_test by (metis test_top)
qed

lemma spec_refine_iterated_relation: "\<lparr>r\<^sup>*\<rparr> \<ge> (\<lparr>r\<rparr>)\<^sup>\<star>"
proof -
  have a0: "\<And>r. \<lparr>(Id \<union> r)\<rparr> \<ge> (nil \<squnion> \<lparr>r\<rparr>)"
    by (metis (no_types) sup.orderE inf_sup_ord(3) le_sup_iff spec_id_nil spec_strengthen sup_ge2) 
  have a1: "r\<^sup>* = Id \<union> r\<^sup>*"
    by blast
  have a2: "(Id \<union> r) O (Id \<union> r\<^sup>*) = (r)\<^sup>*"
    by (metis inf_sup_aci(8) sup.commute trancl_reflcl a1 trancl_unfold_left)
  have a3: "\<lparr>(Id \<union> r)\<rparr> \<ge> (nil \<squnion> \<lparr>r\<rparr>)"
    by (metis a0)
  have a4: "\<lparr>Id \<union> (r\<^sup>*)\<rparr> \<ge> (nil \<squnion> \<lparr>r\<^sup>*\<rparr>)"    
    by (metis a0)
  have "\<lparr>r\<^sup>*\<rparr> \<ge> \<lparr>(Id \<squnion> r)\<rparr>; \<lparr>Id \<union> r\<^sup>*\<rparr>" (is "_ \<ge> ?rhs")
    using a2 spec_chain by simp
  also have "?rhs \<ge> (nil \<squnion> \<lparr>r\<rparr>); (nil \<squnion> \<lparr>r\<^sup>*\<rparr>)" (is "_ \<ge> ?rhs")
    using a1 a3 a4 seq_mono by simp
  also have "?rhs = nil \<squnion> (\<lparr>r\<rparr> \<squnion> \<lparr>r\<^sup>*\<rparr>) \<squnion> \<lparr>r\<rparr>;\<lparr>r\<^sup>*\<rparr>"
    by (simp add: nondet_seq_distrib par.seq_nondet_distrib sup_assoc)
  also have "... \<ge> nil \<squnion> \<lparr>r\<rparr>;\<lparr>r\<^sup>*\<rparr>"
    by (meson sup_mono inf_sup_ord(3) order_refl)
  finally show ?thesis using fiter_induct_nil by simp
qed



end


(* Strong specification with preconditions  
locale strong_spec_pre = strong_spec lib_last
  for lib_last :: "'b \<Rightarrow> 'a::refinement_lattice \<Rightarrow> 'a" ("L\<^sup>C\<^sub>_ _" [999, 999] 999)
begin
  
(* If you see '\<ltort>' and '\<rtort>' as text instead of symbols, then
  make sure to add the following lines to your isabelle symbols file in 
   ~/.isabelle/IsabelleYYYY/etc/symbols
\<ltort>              code: 0x0027ec  group: operator  font: DejaVuSans
\<rtort>              code: 0x0027ed  group: operator  font: DejaVuSans
  This should not be an issue if you used the readme in the root of this repository.
*)

definition specpre :: "'c set\<Rightarrow>'c rel\<Rightarrow>'a::refinement_lattice" ("\<ltort>_,_\<rtort>" 99)
  where "specpre p q \<equiv> \<lbrace>p\<rbrace>;\<lparr>q\<rparr>"
  
lemma specpre_eq_spec:
  shows "\<lparr>q\<rparr>=\<ltort>\<top>,q\<rtort>"
  using specpre_def assert_top by simp

lemma specpre_strengthen_post: 
  assumes q2_strengthen_q1: "q2 \<subseteq> q1"
  shows "\<ltort>p,q1\<rtort> \<ge> \<ltort>p,q2\<rtort>"
proof -
  have "\<lbrace>p\<rbrace>;\<lparr>q1\<rparr> \<ge> \<lbrace>p\<rbrace>;\<lparr>q2\<rparr>"
    using spec_strengthen seq_mono_right q2_strengthen_q1 by simp
  then show ?thesis using specpre_def by simp
qed
  
lemma specpre_weaken_pre:
  assumes p2_weakens_p1: "p1 \<subseteq> p2"
  shows "\<ltort>p1,q\<rtort> \<ge> \<ltort>p2,q\<rtort>"
proof -
  have "\<lbrace>p1\<rbrace> \<ge> \<lbrace>p2\<rbrace>"
    using p2_weakens_p1 by (simp add: assert_iso)     
  then have "\<lbrace>p1\<rbrace>;\<lparr>q\<rparr> \<ge> \<lbrace>p2\<rbrace>;\<lparr>q\<rparr>"
    using seq_mono_left by simp
  then show ?thesis using specpre_def by simp
qed
  
lemma specpre_ref_spec:
  shows "\<ltort>p,q\<rtort> \<ge> \<lparr>q\<rparr>"
proof -
  have "p \<subseteq> \<top>"
    by simp
  then have "\<ltort>p,q\<rtort> \<ge> \<ltort>\<top>,q\<rtort>"
    using specpre_weaken_pre by simp
  then show ?thesis using specpre_eq_spec by simp
qed
  
lemma specpre_test_post_extract:
  shows "\<ltort>p1,q \<triangleright> p2\<rtort> = \<ltort>p1,q\<rtort>;\<tau>(p2)"
proof -  
  have "\<ltort>p1,q \<triangleright> p2\<rtort> = \<lbrace>p1\<rbrace>;\<lparr>q \<triangleright> p2\<rparr>"
    using specpre_def by simp
  also have "... = \<lbrace>p1\<rbrace>;\<lparr>q\<rparr>;\<tau>(p2)"
    using spec_test_restricts seq_assoc by simp
  also have "... = \<ltort>p1,q\<rtort>;\<tau>(p2)"
    using specpre_def by simp
  finally show ?thesis .
qed

lemma specpre_assert_post:
  shows "\<ltort>p1,q \<triangleright> p2\<rtort> = \<ltort>p1,q \<triangleright> p2\<rtort>;\<lbrace>p2\<rbrace>"
proof -  
  have "\<ltort>p1,q \<triangleright> p2\<rtort> = \<lbrace>p1\<rbrace>;\<lparr>q \<triangleright> p2\<rparr>"
    using specpre_def by simp
  also have "... = \<lbrace>p1\<rbrace>;\<lparr>q \<triangleright> p2\<rparr>;\<lbrace>p2\<rbrace>"
    using spec_assert_restricts seq_assoc by simp
  also have "... = \<ltort>p1,q \<triangleright> p2\<rtort>;\<lbrace>p2\<rbrace>"
    using specpre_def by simp
  finally show ?thesis .
qed
  
lemma specpre_assert_pre:
  shows "\<lbrace>p1\<rbrace>;\<ltort>p2,q\<rtort> = \<ltort>p1 \<inter> p2,q\<rtort>"
proof -
  have "\<lbrace>p1\<rbrace>;\<ltort>p2,q\<rtort> = \<lbrace>p1\<rbrace>;\<lbrace>p2\<rbrace>;\<lparr>q\<rparr>"
    using specpre_def seq_assoc by simp
  also have "... = \<lbrace>p1 \<inter> p2\<rbrace>;\<lparr>q\<rparr>"
    using assert_seq_assert by simp
  finally show ?thesis using specpre_def by simp
qed
  
lemma specpre_pre_internalise:
  shows "\<ltort>p,q\<rtort> = \<ltort>p,p \<triangleleft> q\<rtort>"
proof -
  have "\<ltort>p,q\<rtort>= \<lbrace>p\<rbrace>;\<lparr>q\<rparr>"
    using specpre_def by simp
  also have "... = \<lbrace>p\<rbrace>;(\<tau> p);\<lparr>q\<rparr>"
    by (simp add: assert_seq_test)
  also have "... = \<lbrace>p\<rbrace>;(\<tau> p);\<lparr>p \<triangleleft> q\<rparr>"
    using test_restricts_spec seq_assoc by simp
  also have "... = \<lbrace>p\<rbrace>;\<lparr>p \<triangleleft> q\<rparr>"
    by (simp add: assert_seq_test)
  also have "... = \<ltort>p,p \<triangleleft> q\<rtort>"
    using specpre_def by simp
  finally show ?thesis .
qed    
    
lemma specpre_ref_test:
  shows "\<ltort>p, q\<rtort> \<ge> \<tau>({s. (s,s) \<in> q})"
  using spec_to_test specpre_def assert_redundant seq_mono_right by metis

lemma specpre_id_nil:
  shows "\<ltort>p, Id \<triangleright> p\<rtort> \<ge> nil"
proof -
  have "Id \<triangleright> p = p \<triangleleft> (Id \<triangleright> UNIV)"
    unfolding restrict_domain_def restrict_range_def by auto
  then have "\<ltort>p, Id \<triangleright> p\<rtort> = \<ltort>p, Id \<triangleright> UNIV\<rtort>"
    using specpre_pre_internalise by metis
  moreover have "{s. (s,s) \<in>  Id \<triangleright> UNIV} = UNIV"
    unfolding restrict_range_def by auto
  ultimately show ?thesis using specpre_ref_test test_top by metis
qed
  
lemma specpre_sequential:
  shows "\<ltort>p0,(relcomp q1 q2)\<rtort> \<ge> \<ltort>p0,q1 \<triangleright> p1\<rtort>;\<ltort>p1,q2\<rtort>"
proof -
  have a1: "(relcomp (q1 \<triangleright> p1) (q2)) \<subseteq> ((relcomp q1 q2))"
    using restrict_range_def by auto  
  have "\<ltort>p0,(relcomp q1 q2)\<rtort> = \<lbrace>p0\<rbrace>;\<lparr>(relcomp q1 q2)\<rparr>"
    using specpre_def by simp
  also have "... \<ge> \<lbrace>p0\<rbrace>;\<lparr>(relcomp (q1 \<triangleright> p1) (q2))\<rparr>" (is "_ \<ge> ?rhs")
    using spec_strengthen seq_mono_right a1 by simp
  also have "?rhs \<ge> \<lbrace>p0\<rbrace>;\<lparr>q1 \<triangleright> p1\<rparr>;\<lparr>q2\<rparr>" (is "_ \<ge> ?rhs")
    using spec_chain seq_mono_right seq_assoc by simp
  also have "?rhs = \<lbrace>p0\<rbrace>;\<lparr>q1 \<triangleright> p1\<rparr>;\<lbrace>p1\<rbrace>;\<lparr>q2\<rparr>"
    using spec_assert_restricts seq_assoc by simp
  also have "... = \<ltort>p0,q1 \<triangleright> p1\<rtort>;\<ltort>p1,q2\<rtort>"
    using specpre_def seq_assoc by simp
  finally show ?thesis .  
qed

lemma specpre_tolerates_left:
  assumes tolerates_interference: "tolerates_interference p q r"
  shows "\<ltort>p,q\<rtort> \<ge> \<lparr>r\<^sup>*\<rparr>;\<ltort>p,q\<rtort>"
proof -   
  have a1: "p \<triangleleft> r\<^sup>* = (p \<triangleleft> r\<^sup>* ) \<triangleright> p"    
    using stable_rtrancl tolerates_interference
    unfolding tolerates_interference_def stable_def 
              restrict_range_def restrict_domain_def by auto
  have "p \<triangleleft> (relcomp (r\<^sup>* ) (q)) \<subseteq> q"
    using q_tolerates_rtrancl_left tolerates_interference by metis    
  then have "\<ltort>p,q\<rtort> \<ge> \<ltort>p,p \<triangleleft> (relcomp (r\<^sup>* ) (q))\<rtort>" (is "_ \<ge> ?rhs")
    using specpre_strengthen_post by simp
  also have "?rhs = \<ltort>p,(relcomp (r\<^sup>* ) (q))\<rtort>"
    using specpre_pre_internalise by simp
  also have "... \<ge> \<lbrace>p\<rbrace>;\<lparr>r\<^sup>*\<rparr>;\<lparr>q\<rparr>" (is "_ \<ge> ?rhs")
    using specpre_def spec_chain seq_mono_right seq_assoc by simp
  also have "?rhs = \<ltort>p, r\<^sup>*\<rtort>;\<lparr>q\<rparr>"
    using specpre_def by simp
  also have "... = \<ltort>p, (p \<triangleleft> r\<^sup>* ) \<triangleright> p\<rtort>;\<lparr>q\<rparr>"     
    using a1 specpre_pre_internalise by simp
  also have "... = \<ltort>p, (p \<triangleleft> r\<^sup>* ) \<triangleright> p\<rtort>;\<lbrace>p\<rbrace>;\<lparr>q\<rparr>"     
    using specpre_assert_post spec_def by simp
  also have "... = \<ltort>p, (p \<triangleleft> r\<^sup>* ) \<triangleright> p\<rtort>;\<ltort>p,q\<rtort>"     
    using specpre_def by (simp add: seq_assoc)
  also have "... = \<ltort>p, r\<^sup>*\<rtort>;\<ltort>p,q\<rtort>"  
    using a1 specpre_pre_internalise by simp
  also have "... \<ge> \<lparr>r\<^sup>*\<rparr>;\<ltort>p,q\<rtort>"
    using specpre_ref_spec seq_mono_left by simp
  finally show ?thesis .
qed  

lemma specpre_tolerates_right:
  assumes tolerates_interference: "tolerates_interference p q r"  
  shows "\<ltort>p,q\<rtort> \<ge> \<ltort>p,q\<rtort>;\<lparr>r\<^sup>*\<rparr>"
proof -  
  have "p \<triangleleft> (relcomp (q) (r\<^sup>* )) \<subseteq> q"
    using q_tolerates_rtrancl_right tolerates_interference by metis    
  then have "\<ltort>p,q\<rtort> \<ge> \<ltort>p,p \<triangleleft> (relcomp (q) (r\<^sup>* ))\<rtort>" (is "_ \<ge> ?rhs")
    using specpre_strengthen_post by simp
  also have "?rhs = \<ltort>p,(relcomp (q) (r\<^sup>* ))\<rtort>"
    using specpre_pre_internalise by simp
  also have "... \<ge> \<lbrace>p\<rbrace>;\<lparr>q\<rparr>;\<lparr>r\<^sup>*\<rparr>" (is "_ \<ge> ?rhs")
    using specpre_def spec_chain seq_mono_right seq_assoc by simp
  also have "?rhs = \<ltort>p,q\<rtort>;\<lparr>r\<^sup>*\<rparr>"
    using specpre_def by simp
  finally show ?thesis .
qed

end

*) 



end
