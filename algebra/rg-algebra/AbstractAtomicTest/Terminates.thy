section \<open>Terminates command.\<close>

(* Concrete semantics book *)

theory Terminates
imports
  "HOL-Library.Boolean_Algebra"
  "Constrained_Atomic_Commands"
  "Termination"
  "Specification"
  "Programming_Constructs"
  "../AbstractAtomic/Fairness"
begin

locale terminates = constrained_atomic + term_op + strong_spec + if_statement + while_loop +
  constrains \<tau> :: "'state set \<Rightarrow> 'a"
  constrains \<pi> :: "'state rel \<Rightarrow> 'a"
  constrains \<epsilon> :: "'state rel \<Rightarrow> 'a"
begin

datatype 'x Temporal =
  Initially "'x set" (\<open>\<iota>\<close>) |
  InitiallyPgm "'x rel" (\<open>\<Pi>\<^sub>t\<close>) |
  InitiallyEnv "'x rel" (\<open>\<E>\<^sub>t\<close>) |
  Eventually "'x Temporal" (\<open>\<diamond>\<close>) |
  Always "'x Temporal" (\<open>\<box>\<close>) |
  And "'x Temporal" "'x Temporal" (infixl "\<sqinter>\<^sub>t" 65) |
  Or "'x Temporal" "'x Temporal" (infixl "\<squnion>\<^sub>t" 70) |
  Not "'x Temporal" (\<open>\<not>\<^sub>t\<close>)

definition "fair\<^sub>t" :: "'x Temporal" where
  "fair\<^sub>t \<equiv> \<box> (\<diamond> (\<Pi>\<^sub>t \<top>))"

definition EventuallyUnfair :: "'x Temporal \<Rightarrow> 'x Temporal" (\<open>\<diamond>\<^sub>f\<close>) where
  "EventuallyUnfair f \<equiv> \<diamond> f \<squnion>\<^sub>t \<not>\<^sub>t fair\<^sub>t"

definition AlwaysUnfair :: "'x Temporal \<Rightarrow> 'x Temporal" (\<open>\<box>\<^sub>f\<close>) where
  "AlwaysUnfair f \<equiv> \<box> f \<sqinter>\<^sub>t fair\<^sub>t"

fun metric :: "'b Temporal \<Rightarrow> nat" where
  "metric (\<iota> p) = 2" |
  "metric (\<Pi>\<^sub>t p) = 2" |
  "metric (\<E>\<^sub>t p) = 2" |
  "metric (\<diamond> f) = 1 + metric f" |
  "metric (\<box> f) = 1 + metric f" |
  "metric (f1 \<sqinter>\<^sub>t f2) = 1 + max (metric f1) (metric f2)" |
  "metric (f1 \<squnion>\<^sub>t f2) = 1 + max (metric f1) (metric f2)" |
  "metric (\<not>\<^sub>t f) = 2 * metric f"

function encode :: "'b Temporal \<Rightarrow> 'a" where
  "encode (\<iota> p) = \<tau> p ; chaos" |
  "encode (\<Pi>\<^sub>t r) = \<pi> r ; chaos" |
  "encode (\<E>\<^sub>t r) = \<epsilon> r ; chaos" |
  "encode (\<diamond> f) = Atomic\<^sup>\<star> ; encode f" |
  "encode (\<box> f) = gfp (\<lambda>x. encode f \<iinter> (nil \<squnion> Atomic ; x))" |
  "encode (f1 \<sqinter>\<^sub>t f2) = encode f1 \<sqinter> encode f2" |
  "encode (f1 \<squnion>\<^sub>t f2) = encode f1 \<squnion> encode f2" |
  "encode (\<not>\<^sub>t (\<iota> p)) = encode (\<iota> (-p))" |
  "encode (\<not>\<^sub>t (\<Pi>\<^sub>t r)) = encode (\<Pi>\<^sub>t (-r) \<squnion>\<^sub>t \<E>\<^sub>t \<top>)" |
  "encode (\<not>\<^sub>t (\<E>\<^sub>t r)) =  encode (\<E>\<^sub>t (-r) \<squnion>\<^sub>t \<Pi>\<^sub>t \<top>)" |
  "encode (\<not>\<^sub>t (\<diamond> f)) = encode (\<box> (\<not>\<^sub>t f))" |
  "encode (\<not>\<^sub>t (\<box> f)) = encode (\<diamond> (\<not>\<^sub>t f))" |
  "encode (\<not>\<^sub>t (f1 \<sqinter>\<^sub>t f2)) = encode ((\<not>\<^sub>t f1) \<squnion>\<^sub>t (\<not>\<^sub>t f2))" |
  "encode (\<not>\<^sub>t (f1 \<squnion>\<^sub>t f2)) = encode ((\<not>\<^sub>t f1) \<sqinter>\<^sub>t (\<not>\<^sub>t f2))" |
  "encode (\<not>\<^sub>t (\<not>\<^sub>t f)) = encode f"
  by pat_completeness auto
termination
  apply (relation "measure metric")
  apply simp_all
  apply auto
proof -
  fix f
  show "0 < metric f"
    apply induct
    apply simp_all
    done
qed

lemma always_step_mono: "mono (\<lambda>x. c \<iinter> (nil \<squnion> Atomic ; x))"
  using seq_mono_right nondet_mono_right conj.sync_mono_right mono_def by (metis (mono_tags))

lemma always_atomic_infiter: "gfp (\<lambda>x. atomic p ; chaos \<iinter> (nil \<squnion> Atomic ; x)) = (atomic p)\<^sup>\<infinity>"
proof -
  have "gfp (\<lambda>x. atomic p ; chaos \<iinter> (nil \<squnion> Atomic ; x)) = gfp (\<lambda>x. atomic p ; (chaos \<iinter> x))"
  proof -
    have "gfp (\<lambda>x. atomic p ; chaos \<iinter> (nil \<squnion> Atomic ; x))
            = gfp (\<lambda>x. (atomic p ; chaos \<iinter> nil) \<squnion> (atomic p ; chaos \<iinter> Atomic ; x))"
      using conj_commute by (simp add: conj.nondet_sync_distrib)
    also have "... = gfp (\<lambda>x. atomic p ; chaos \<iinter> Atomic ; x)"
      using conj.nil_sync_atomic_pre conj_commute by simp
    also have "... = gfp (\<lambda>x. (atomic p \<iinter> Atomic) ; (chaos \<iinter> x))"
      using atomic.Hom_def conj.atomic_pre_sync_atomic_pre by simp
    also have "... = gfp (\<lambda>x. atomic p ; (chaos \<iinter> x))"
      using conj.atomic_sync_identity conj_commute by simp
    finally show ?thesis .
  qed
  also have "... = (atomic p)\<^sup>\<infinity>"
    proof -
    have "gfp (\<lambda>x. atomic p ; (chaos \<iinter> x)) \<le> (atomic p)\<^sup>\<infinity>"
    proof -
      have "\<And>Z. atomic p ; (chaos \<iinter> Z) \<le> atomic p ; Z" (is "(\<And>Z. ?Q Z)")
          using chaos_def iter_ref_infiter local.conj_commute seq_mono_right by (simp add: conj_conjoin_non_aborting)
      thus ?thesis
        using gfp_mono infiter_def by metis
    qed
    moreover have "(atomic p)\<^sup>\<infinity> \<le> gfp (\<lambda>x. atomic p ; (chaos \<iinter> x))"
    proof -
      have "mono (\<lambda>x. atomic p ; (chaos \<iinter> x))" using always_step_mono
        using chaos_def conj_chaos_left mono_def seq_mono_right by fastforce
      moreover have "(atomic p)\<^sup>\<infinity> \<le> atomic p ; (chaos \<iinter> ((atomic p)\<^sup>\<infinity> \<squnion> gfp (\<lambda>x. atomic p ; (chaos \<iinter> x))))"
      proof -
        have "atomic p ; (chaos \<iinter> ((atomic p)\<^sup>\<infinity> \<squnion> gfp (\<lambda>x. atomic p ; (chaos \<iinter> x))))
                = atomic p ; ((atomic p)\<^sup>\<infinity> \<squnion> gfp (\<lambda>x. atomic p ; (chaos \<iinter> x)))"
          using chaos_def conj_chaos_left by simp
        also have "... \<ge> atomic p ; (atomic p)\<^sup>\<infinity>" (is "_ \<ge> ?rhs")
          using seq_nondet_distrib_weak by simp
        also have "?rhs = (atomic p)\<^sup>\<infinity>"
          using infiter_unfold by simp
        finally show ?thesis .
      qed
      ultimately show ?thesis
        using always_step_mono coinduct by (simp add: coinduct)
    qed
    ultimately show ?thesis
      by simp
  qed
  finally show ?thesis .
qed

lemma unfair_eventually: "encode (\<diamond>\<^sub>f f) = term ; encode f"
proof -
  have "encode (\<diamond>\<^sub>f f) = encode (\<diamond> f \<squnion>\<^sub>t \<not>\<^sub>t fair\<^sub>t)"
    by (simp add: EventuallyUnfair_def)
  also have "... = Atomic\<^sup>\<star> ; encode f \<squnion> encode (\<not>\<^sub>t (\<box> (\<diamond> (\<Pi>\<^sub>t UNIV))))"
    by (simp add: fair\<^sub>t_def)
  also have "... = Atomic\<^sup>\<star> ; encode f \<squnion> encode (\<diamond> (\<box> (\<E>\<^sub>t UNIV)))"
    using env.Hom_def by simp
  also have "... = Atomic\<^sup>\<star> ; encode f \<squnion> Atomic\<^sup>\<star> ; Env\<^sup>\<infinity>"
  proof -
    have "encode (\<diamond> (\<box> (\<E>\<^sub>t UNIV))) = Atomic\<^sup>\<star> ; gfp (\<lambda>x. Env ; chaos \<iinter> (nil \<squnion> Atomic ; x))"
      by (simp add: env.Hom_def)
    thus ?thesis
      using always_atomic_infiter par.syncid_atomic by auto
  qed
  also have "... = Atomic\<^sup>\<star> ; Env\<^sup>\<omega> ; encode f"
  proof -
    have "Atomic\<^sup>\<star> = Atomic\<^sup>\<star> ; Env\<^sup>\<star>"
      using Atomic_def2 par.fiter_decomp par.fiter_leapfrog seq_assoc by (simp add: sup_commute)
    hence "Atomic\<^sup>\<star> ; encode f \<squnion> Atomic\<^sup>\<star> ; Env\<^sup>\<infinity> = Atomic\<^sup>\<star> ; Env\<^sup>\<star> ; encode f \<squnion> Atomic\<^sup>\<star> ; Env\<^sup>\<infinity>"
      by simp
    thus ?thesis
      using par.iter_isolate par.seq_nondet_distrib seq_assoc by metis
  qed
  also have "... = term ; encode f"
    using term_def Atomic_def2 env.Hom_def pgm.Hom_def by simp
  finally show ?thesis .
qed

(* TODO Move somewhere more appropriate *)
lemma inf_prefix_term: "Atomic\<^sup>\<infinity> \<ge> term ; Atomic\<^sup>\<infinity>"
proof -
  have "Atomic\<^sup>\<infinity> = Atomic\<^sup>\<star> ; Atomic\<^sup>\<infinity>"
    using fiter_seq_iter infiter_iter_magic seq_assoc by metis
  also have "... = Atomic\<^sup>\<star> ; Atomic\<^sup>\<omega> ; Atomic\<^sup>\<infinity>"
    using infiter_iter_magic iter_seq_iter seq_assoc by metis
  also have "... \<ge> Atomic\<^sup>\<star> ; Env\<^sup>\<omega> ; Atomic\<^sup>\<infinity>" (is "_ \<ge> ?rhs")
    using atomic.Hom_ref_hom iter_mono par.syncid_atomic seq_mono by auto
  also have "?rhs = term ; Atomic\<^sup>\<infinity>"
    using Atomic_def2 env.Hom_def pgm.Hom_def terminate_def by simp
  finally show ?thesis .
qed

lemma refine_infiter: "c \<ge> d \<Longrightarrow> c\<^sup>\<infinity> \<ge> d\<^sup>\<infinity>"
  using infiter_induct infiter_unfold seq_mono_left by metis

lemma seq_atomic_term: "Atomic ; term = term ; Atomic"
proof -
  have "Atomic ; term \<ge> term ; Atomic"
  proof -
    have "Atomic ; term = Atomic ; Atomic\<^sup>\<star> ; Env\<^sup>\<omega>"
      using term_def Atomic_def2 env.Hom_def pgm.Hom_def seq_assoc by simp
    also have "... = Atomic ; Atomic\<^sup>\<star> ; (Env\<^sup>\<star> \<squnion> Env\<^sup>\<infinity>)"
      using par.iter_isolation by simp
    also have "... \<ge> Atomic ; Atomic\<^sup>\<star> ; (nil \<squnion> Env\<^sup>\<infinity>)" (is "_ \<ge> ?rhs")
      using par.iter_isolation seq_mono_right skip_def skip_ref_nil by simp
    also have "?rhs = Atomic\<^sup>\<star> ; Atomic ; (nil \<squnion> Env\<^sup>\<infinity>)"
      using par.fiter_leapfrog seq_nil_left seq_nil_right by metis
    also have "... = Atomic\<^sup>\<star> ; Atomic \<squnion> Atomic\<^sup>\<star> ; Atomic ; Env\<^sup>\<infinity>"
      using par.seq_nondet_distrib by simp
    also have "... = Atomic\<^sup>\<star> ; Atomic\<^sup>\<star> ; Atomic \<squnion> Atomic\<^sup>\<star> ; Atomic ; Env\<^sup>\<infinity>"
      by simp
    also have "... = Atomic\<^sup>\<star> ; (Atomic\<^sup>\<star> ; Atomic \<squnion> Atomic ; Env\<^sup>\<infinity>)" 
      using par.seq_nondet_distrib seq_assoc by presburger
    also have "... \<ge> Atomic\<^sup>\<star> ; (Env\<^sup>\<star> ; Atomic \<squnion> Env ; Env\<^sup>\<infinity>)" (is "_ \<ge> ?rhs")
      using Atomic_ref_env env.Hom_def order_refl seq_mono sup.mono fiter_mono by metis
    also have "?rhs = Atomic\<^sup>\<star> ; (Env\<^sup>\<star> ; Atomic \<squnion> Env\<^sup>\<infinity>)"
      using infiter_unfold seq_assoc by simp
    also have "... = Atomic\<^sup>\<star> ; Env\<^sup>\<omega> ; Atomic"
      using par.iter_isolate seq_assoc by simp
    also have "... = term ; Atomic"
      using Atomic_def2 env.Hom_def pgm.Hom_def terminate_def by simp
    finally show ?thesis .
  qed
  moreover have "term ; Atomic \<ge> Atomic ; term"
  proof -
    have "term ; Atomic = Atomic\<^sup>\<star> ; Env\<^sup>\<omega> ; Atomic"
      using Atomic_def2 env.Hom_def pgm.Hom_def terminate_def by simp
    also have "... = Atomic\<^sup>\<star> ; Env\<^sup>\<omega> ; Atomic \<squnion> Atomic\<^sup>\<star> ; Env\<^sup>\<omega> ; Atomic"
      by simp
    also have "... = Atomic\<^sup>\<star> ; Env\<^sup>\<omega> ; Atomic \<squnion> Atomic\<^sup>\<star> ; (Env\<^sup>\<star> \<squnion> Env\<^sup>\<infinity>) ; Atomic"
      using par.iter_isolation by simp
    also have "... = Atomic\<^sup>\<star> ; Env\<^sup>\<omega> ; Atomic \<squnion> Atomic\<^sup>\<star> ; Env\<^sup>\<star> ; Atomic \<squnion> Atomic\<^sup>\<star> ; Env\<^sup>\<infinity>"
      using par.iter_isolate par.iter_isolation par.seq_nondet_distrib seq_assoc sup.assoc by (metis (no_types))
    also have "... \<ge> Atomic\<^sup>\<star> ; nil ; Atomic \<squnion> Atomic\<^sup>\<star> ; Atomic ; Env\<^sup>\<star> ; Env \<squnion> Atomic\<^sup>\<star> ; Env\<^sup>\<infinity>" (is "_ \<ge> ?rhs")
    proof -
      have "Atomic\<^sup>\<star> ; Env\<^sup>\<star> ; Atomic \<ge> Atomic\<^sup>\<star> ; nil ; Atomic"
        using fiter0 seq_mono_left seq_mono_right by presburger
      moreover have "Atomic\<^sup>\<star> ; Env\<^sup>\<star> ; Atomic \<ge> Atomic\<^sup>\<star> ; Atomic ; Env\<^sup>\<star> ; Env"
        using Atomic_ref_env env.Hom_def fiter1 fiter_seq_fiter order_refl seq_mono by metis
      ultimately show ?thesis
        using iter0 order_refl seq_mono_left seq_mono_right sup.mono by metis
    qed
    also have "?rhs = Atomic\<^sup>\<star> ; Atomic \<squnion> Atomic\<^sup>\<star> ; Atomic ; Env ; Env\<^sup>\<star> \<squnion> Atomic\<^sup>\<star> ; Env\<^sup>\<infinity>"
      using fiter0 par.fiter_leapfrog seq_assoc seq_nil_right by (metis (no_types))
    also have "... = Atomic\<^sup>\<star> ; Atomic ; Env\<^sup>\<star> \<squnion> Atomic\<^sup>\<star> ; Env\<^sup>\<infinity>"
      using fiter_unfold par.seq_nondet_distrib seq_assoc seq_nil_right by (metis (no_types))
    also have "... \<ge> Atomic\<^sup>\<star> ; Atomic ; Env\<^sup>\<star> \<squnion> Atomic\<^sup>\<star> ; Atomic ; Env\<^sup>\<infinity>" (is "_ \<ge> ?rhs")
      using fiter1 fiter_fiter fiter_unfold iter_fiter nil_iter par.fiter_decomp par.fiter_leapfrog seq_mono_left seq_nil_left seq_nil_right sup.mono by (metis (no_types))
    also have "?rhs = Atomic\<^sup>\<star> ; Atomic ; Env\<^sup>\<omega>"
      using par.iter_isolation par.seq_nondet_distrib by simp
    also have "... = Atomic ; Atomic\<^sup>\<star> ; Env\<^sup>\<omega>"
      using par.fiter_leapfrog seq_nil_left seq_nil_right by metis
    also have "... = Atomic ; term"
      using Atomic_def2 env.Hom_def pgm.Hom_def seq_assoc terminate_def by simp
    finally show ?thesis .
  qed
  ultimately show ?thesis
    by simp
qed

lemma seq_atomic_term2: "Atomic ; term = term ; Atomic ; term"
proof -
  have "Atomic ; term = Atomic ; term ; term"
    using seq_term_term seq_assoc by simp
  also have "... = term ; Atomic ; term"
    using seq_atomic_term by simp
  finally show ?thesis .
qed

lemma top_restrict_range[simp]: "\<top> \<triangleright> p = range_restriction p"
  using restrict_range_def by auto

lemma range_restriction_image: "(\<top> \<triangleright> p)``{s} = p"
   by simp

lemma NOTDET_test_seq: "(\<Squnion>s. \<tau> {s} ; c) = c"
  using NONDET_seq_distrib Nondet_test_nil seq_nil_left by metis

lemma range_restriction_pspec: "\<lceil>\<top> \<triangleright> p\<rceil> = chaos ; \<tau> p"
proof -
  have "\<lceil>\<top> \<triangleright> p\<rceil> = (\<Squnion>s. \<tau> {s} ; chaos ; \<tau> ((\<top> \<triangleright> p)``{s}))"
    by (rule pspec_def)
  also have "... = (\<Squnion>s. \<tau> {s} ; chaos ; \<tau> p)"
    using range_restriction_image by simp
  also have "... = chaos ; \<tau> p"
    using NOTDET_test_seq seq_assoc by simp
  finally show ?thesis .
qed

lemma range_restriction_spec: "\<lparr>\<top> \<triangleright> p\<rparr> = term ; \<tau> p"
proof -
  have "\<lparr>\<top> \<triangleright> p\<rparr> = \<lceil>\<top> \<triangleright> p\<rceil> \<iinter> term"
    by (rule spec_def)
  also have "... = chaos ; \<tau> p \<iinter> term"
    using range_restriction_pspec by simp
  also have "... = term ; \<tau> p"
    using conj.test_sync_post local.conj_commute by simp
  finally show ?thesis .
qed

lemma seq_term_range_restriction:"\<lparr>\<top> \<triangleright> p\<rparr> = term ; \<lparr>\<top> \<triangleright> p\<rparr>"
proof -
  have "\<lparr>\<top> \<triangleright> p\<rparr> = term ; \<tau> p"
    by (rule range_restriction_spec)
  also have "... = term ; term ; \<tau> p"
    using seq_term_term by simp
  also have "... = term ; \<lparr>\<top> \<triangleright> p\<rparr>"
    using range_restriction_spec seq_assoc by simp
  finally show ?thesis .
qed

lemma seq_term_term_conj_distrib: "term ; a \<iinter> term ; b = term ; (term ; a \<iinter> term ; b)"
proof -
  have "term ; a \<iinter> term ; b \<ge> term ; (term ; a \<iinter> term ; b)"
  proof -
    have "term ; a \<iinter> term ; b = term ; term ; a \<iinter> term ; term ; b"
      using seq_term_term by simp
    also have "... \<ge> term ; (term ; a \<iinter> term ; b)"
      using seq_assoc seq_conj_interchange spec_conj_term spec_univ by metis
    finally show ?thesis .
  qed
  moreover have "term ; (term ; a \<iinter> term ; b) \<ge> term ; a \<iinter> term ; b"
  proof -
    have "term ; (term ; a \<iinter> term ; b) \<ge> nil ; (term ; a \<iinter> term ; b)" (is "_ \<ge> ?rhs")
      using seq_mono_left term_nil by metis
    also have "?rhs = term ; a \<iinter> term ; b"
      by simp
    finally show ?thesis .
  qed
  ultimately show ?thesis
    by simp
qed

lemma nil_atomic_term: "term = nil \<squnion> Atomic ; term"
proof -
  have "term = Atomic\<^sup>\<star> ; Env\<^sup>\<omega>"
    using term_def Atomic_def2 env.Hom_def pgm.Hom_def by simp
  also have "... = (nil \<squnion> Atomic ; Atomic\<^sup>\<star>) ; Env\<^sup>\<omega>"
    using fiter_unfold by simp
  also have "... = Env\<^sup>\<omega> \<squnion> Atomic ; Atomic\<^sup>\<star> ; Env\<^sup>\<omega>"
    using nondet_seq_distrib by simp
  also have "... = nil \<squnion> Env ; Env\<^sup>\<omega> \<squnion> Atomic ; Atomic\<^sup>\<star> ; Env\<^sup>\<omega>"
    using iter_unfold by simp
  also have "... = nil \<squnion> Atomic ; Atomic\<^sup>\<star> ; Env\<^sup>\<omega>"
  proof -
    have "Env \<le> Atomic"
      using Atomic_ref_env env.Hom_def by simp

    moreover have "Env\<^sup>\<omega> \<le> Atomic\<^sup>\<star> ; Env\<^sup>\<omega>"
      using fiter0 seq_mono_left by fastforce

    ultimately have "Env ; Env\<^sup>\<omega> \<le> Atomic ; Atomic\<^sup>\<star> ; Env\<^sup>\<omega>"
      using seq_assoc seq_mono by simp
    thus ?thesis
      using le_iff_sup sup.assoc by (metis (no_types))
  qed
  also have "... = nil \<squnion> Atomic ; term"
    using term_def Atomic_def2 env.Hom_def pgm.Hom_def seq_assoc by simp
  finally show ?thesis .
qed

lemma atomic_term: "Atomic ; term = term \<iinter> Atomic ; chaos"
proof -
  have "Atomic ; term = Atomic ; (term \<iinter> chaos)"
    by simp
  also have "... = Atomic ; term \<iinter> Atomic ; chaos"
    using atomic.Hom_def conj.atomic_pre_sync_atomic_pre by simp
  also have "... = (nil \<squnion> Atomic ; term) \<iinter> Atomic ; chaos"
    using atomic.Hom_def conj.nil_sync_atomic_pre conj.nondet_sync_distrib by simp
  also have "... = term \<iinter> Atomic ; chaos"
    using nil_atomic_term by simp
  finally show ?thesis .
qed

lemma inf_encode: "chaos \<ge> encode f"
proof -
  show ?thesis
  proof (induction f rule: encode.induct)
    case (1 p)
    have "chaos \<ge> \<tau> p ; chaos" (is "_ \<ge> ?rhs")
      using test_seq_refine by auto
    also have "?rhs = encode (\<iota> p)"
      by simp
    finally show ?case .
  next
    case (2 r)
    have "chaos \<ge> Atomic ; chaos" (is "_ \<ge> ?rhs")
      by (metis Atomic_nonaborting chaos_seq_chaos seq_mono_left)
    also have "?rhs \<ge> \<pi> r ; chaos" (is "_ \<ge> ?rhs")
      using Atomic_ref_pgm seq_mono_left by simp
    also have "?rhs = encode (\<Pi>\<^sub>t r)"
      by simp
    finally show ?case .
  next
    case (3 r)
    have "chaos \<ge> Atomic ; chaos" (is "_ \<ge> ?rhs")
      by (metis Atomic_nonaborting chaos_seq_chaos seq_mono_left)
    also have "?rhs \<ge> \<epsilon> r ; chaos" (is "_ \<ge> ?rhs")
      using Atomic_ref_env seq_mono_left by simp
    also have "?rhs = encode (\<E>\<^sub>t r)"
      by simp
    finally show ?case .
  next
    case (4 f)
    have "chaos = Atomic\<^sup>\<star> ; chaos"
      using chaos_def fiter_seq_iter by simp
    also have "... \<ge> Atomic\<^sup>\<star> ; encode f" (is "_ \<ge> ?rhs")
      using "4.IH" seq_mono_right by simp
    also have "?rhs = encode (\<diamond> f)"
      by simp
    finally show ?case .
  next
    case (5 f)
    have "chaos = gfp (\<lambda>x. nil \<squnion> Atomic ; x)"
      using chaos_def iter_def by simp
    also have "... = gfp (\<lambda>x. chaos \<iinter> (nil \<squnion> Atomic ; x))"
      by simp
    also have "... \<ge> gfp (\<lambda>x. (encode f) \<iinter> (nil \<squnion> Atomic ; x))" (is "_ \<ge> ?rhs")
    proof -
      have "\<And>x. (encode f) \<iinter> (nil \<squnion> Atomic ; x) \<le> chaos \<iinter> (nil \<squnion> Atomic ; x)"
        using "5.IH" conj.sync_mono_left by presburger
      thus ?thesis
        using always_step_mono by (simp add: gfp_mono)
    qed
    also have "?rhs = encode (\<box> f)"
      by simp
    finally show ?case .
  next
    case (6 f1 f2)
    have "chaos = chaos \<sqinter> chaos"
      by simp
    also have "... \<ge> encode f1 \<sqinter> encode f2" (is "_ \<ge> ?rhs")
      using "6.IH" inf_mono by auto
    also have "?rhs = encode (f1 \<sqinter>\<^sub>t f2)"
      by simp
    finally show ?case .
  next
    case (7 f1 f2)
    have "chaos = chaos \<squnion> chaos"
      by simp
    also have "... \<ge> encode f1 \<squnion> encode f2" (is "_ \<ge> ?rhs")
      using "7.IH" inf_mono by auto
    also have "?rhs = encode (f1 \<squnion>\<^sub>t f2)"
      by simp
    finally show ?case .
  next
    case (8 p)
    thus ?case by simp
  next
    case (9 r)
    have "chaos \<ge> Atomic ; chaos" (is "_ \<ge> ?rhs")
      using chaos_def iter_unfold le_sup_iff order_refl by metis
    also have "?rhs \<ge> (\<pi> (-r) \<squnion> Env) ; chaos" (is "_ \<ge> ?rhs")
      using Atomic_ref_env Atomic_ref_pgm env.Hom_def seq_mono_left by simp
    also have "?rhs = encode (\<not>\<^sub>t (\<Pi>\<^sub>t r))"
      using env.Hom_def nondet_seq_distrib by simp
    finally show ?case .
  next
    case (10 r)
    have "chaos \<ge> Atomic ; chaos" (is "_ \<ge> ?rhs")
      using chaos_def iter_unfold le_sup_iff order_refl by metis
    also have "?rhs \<ge> (\<epsilon> (-r) \<squnion> Pgm) ; chaos" (is "_ \<ge> ?rhs")
      using Atomic_ref_pgm Atomic_ref_env pgm.Hom_def seq_mono_left by simp
    also have "?rhs = encode (\<not>\<^sub>t (\<E>\<^sub>t r))"
      using pgm.Hom_def nondet_seq_distrib by simp
    finally show ?case .
  next
    case (11 f)
    thus ?case by simp
  next
    case (12 f)
    thus ?case by simp
  next
    case (13 f1 f2)
    have "chaos = chaos \<squnion> chaos"
      by simp
    also have "... \<ge> encode (\<not>\<^sub>t f1) \<squnion> encode (\<not>\<^sub>t f2)" (is "_ \<ge> ?rhs")
      using "13.IH" inf_mono by auto
    also have "?rhs = encode (\<not>\<^sub>t (f1 \<sqinter>\<^sub>t f2))"
      by simp
    finally show ?case .
  next
    case (14 f1 f2)
    have "chaos = chaos \<sqinter> chaos"
      by simp
    also have "... \<ge> encode (\<not>\<^sub>t f1) \<sqinter> encode (\<not>\<^sub>t f2)" (is "_ \<ge> ?rhs")
      using "14.IH" inf_mono by auto
    also have "?rhs = encode (\<not>\<^sub>t (f1 \<squnion>\<^sub>t f2))"
      by simp
    finally show ?case .
  next
    case (15 f)
    thus ?case by simp
  qed
qed

(* TODO Consider moving into encode_always_eventually_spec. *)
lemma atomic_inf_range_restriction_spec_term: "Atomic\<^sup>\<infinity> \<ge> (\<lparr>\<top> \<triangleright> p\<rparr> ; term \<iinter> Atomic ; term)\<^sup>\<infinity>"
proof -
  have "Atomic\<^sup>\<infinity> = (Atomic ; term)\<^sup>\<infinity>"
  proof -
    have "Atomic\<^sup>\<infinity> \<ge> (Atomic ; term)\<^sup>\<infinity>"
    proof -
      have "Atomic\<^sup>\<infinity> = (Atomic ; Atomic\<^sup>\<omega>)\<^sup>\<infinity>"
      proof -
        have "(Atomic ; Atomic\<^sup>\<omega>)\<^sup>\<infinity> = Atomic ; Atomic\<^sup>\<omega> ; (Atomic ; Atomic\<^sup>\<omega>)\<^sup>\<infinity>"
          using infiter_unfold by simp
        also have "... = Atomic ; (nil \<squnion> Atomic ; Atomic\<^sup>\<omega>) ; (Atomic ; Atomic\<^sup>\<omega>)\<^sup>\<infinity>"
          using iter_unfold by simp
        also have "... = Atomic ; nil ; (Atomic ; Atomic\<^sup>\<omega>)\<^sup>\<infinity> \<squnion> Atomic ; Atomic ; Atomic\<^sup>\<omega> ; (Atomic ; Atomic\<^sup>\<omega>)\<^sup>\<infinity>"
          using nondet_seq_distrib par.seq_nondet_distrib seq_assoc by simp
        also have "... = Atomic ; (Atomic ; Atomic\<^sup>\<omega>)\<^sup>\<infinity> \<squnion> Atomic ; (Atomic ; Atomic\<^sup>\<omega>)\<^sup>\<infinity>"
          using infiter_unfold seq_assoc seq_nil_right by simp
        also have "... = Atomic ; (Atomic ; Atomic\<^sup>\<omega>)\<^sup>\<infinity>"
          by simp
        finally show ?thesis
          using infiter_iter_magic iter_unfold par.iter_decomp seq_assoc sup.idem by metis
      qed
      also have "... \<ge> (Atomic ; term)\<^sup>\<infinity>"
        using chaos_def refine_infiter seq_mono_right term_nonaborting by auto
      finally show ?thesis .
    qed
    moreover have "(Atomic ; term)\<^sup>\<infinity> \<ge> Atomic\<^sup>\<infinity>"
      using refine_infiter seq_mono_right seq_nil_right term_nil by metis
    ultimately show ?thesis by simp
  qed
  also have "... = (chaos \<iinter> Atomic ; term)\<^sup>\<infinity>"
    by simp
  also have "... \<ge> (term \<iinter> Atomic ; term)\<^sup>\<infinity>" (is "_ \<ge> ?rhs")
    using conj.sync_mono_left refine_infiter term_nonaborting by fastforce
  also have "?rhs \<ge> (\<lparr>\<top> \<triangleright> p\<rparr> ; term \<iinter> Atomic ; term)\<^sup>\<infinity>"
    using seq_mono_left conj.sync_mono_left seq_term_term spec_term refine_infiter by metis
  finally show ?thesis .
qed

lemma encode_always_eventually: "encode (\<box> (\<diamond>\<^sub>f (\<iota> p))) \<ge> (\<lparr>\<top> \<triangleright> p\<rparr> ; term \<iinter> Atomic ; term)\<^sup>\<infinity>"
proof -
  have "encode (\<box> (\<diamond>\<^sub>f (\<iota> p))) = gfp (\<lambda>x. term ; \<tau> p ; chaos \<iinter> (nil \<squnion> Atomic ; x))"
    using encode.simps seq_assoc unfair_eventually by simp
  also have "... = gfp (\<lambda>x. \<lparr>\<top> \<triangleright> p\<rparr> ; chaos \<iinter> (nil \<squnion> Atomic ; x))"
    using range_restriction_spec by simp
  finally have "encode (\<box> (\<diamond>\<^sub>f (\<iota> p))) = gfp (\<lambda>x. \<lparr>\<top> \<triangleright> p\<rparr> ; chaos \<iinter> (nil \<squnion> Atomic ; x))" .
  
  moreover have "\<lparr>\<top> \<triangleright> p\<rparr> ; chaos \<iinter> (nil \<squnion> Atomic ; (\<lparr>\<top> \<triangleright> p\<rparr> ; term \<iinter> Atomic ; term)\<^sup>\<infinity>)
                  \<ge> (\<lparr>\<top> \<triangleright> p\<rparr> ; term \<iinter> Atomic ; term)\<^sup>\<infinity>"
  proof -
    have "\<lparr>\<top> \<triangleright> p\<rparr> ; chaos \<iinter> (nil \<squnion> Atomic ; (\<lparr>\<top> \<triangleright> p\<rparr> ; term \<iinter> Atomic ; term)\<^sup>\<infinity>)
            \<ge> \<lparr>\<top> \<triangleright> p\<rparr> ; Atomic\<^sup>\<infinity> \<iinter> Atomic ; (\<lparr>\<top> \<triangleright> p\<rparr> ; term \<iinter> Atomic ; term)\<^sup>\<infinity>" (is "_ \<ge> ?rhs")
      using conj.sync_mono_left iter_ref_infiter seq_mono_right chaos_def conj.sync_mono by simp
    also have "?rhs = \<lparr>\<top> \<triangleright> p\<rparr> ; Atomic\<^sup>\<infinity> \<iinter> Atomic ; (term ; \<lparr>\<top> \<triangleright> p\<rparr> ; term \<iinter> term ; Atomic ; term)\<^sup>\<infinity>"
      using seq_term_range_restriction seq_atomic_term2 by simp
    also have "... = \<lparr>\<top> \<triangleright> p\<rparr> ; Atomic\<^sup>\<infinity> \<iinter> Atomic ; term ; (term ; \<lparr>\<top> \<triangleright> p\<rparr> ; term \<iinter> term ; Atomic ; term)\<^sup>\<infinity>"
    proof -
      have "(term ; \<lparr>\<top> \<triangleright> p\<rparr> ; term \<iinter> term ; Atomic ; term)\<^sup>\<infinity>
              = (term ; \<lparr>\<top> \<triangleright> p\<rparr> ; term \<iinter> term ; Atomic ; term)
                  ; (term ; \<lparr>\<top> \<triangleright> p\<rparr> ; term \<iinter> term ; Atomic ; term)\<^sup>\<infinity>"
        using infiter_unfold by simp
      also have "... = term ; (term ; \<lparr>\<top> \<triangleright> p\<rparr> ; term \<iinter> term ; Atomic ; term)
                          ; (term ; \<lparr>\<top> \<triangleright> p\<rparr> ; term \<iinter> term ; Atomic ; term)\<^sup>\<infinity>"
        using seq_assoc seq_term_term_conj_distrib by simp
      also have "... = term ; (term ; \<lparr>\<top> \<triangleright> p\<rparr> ; term \<iinter> term ; Atomic ; term)\<^sup>\<infinity>"
        using infiter_unfold seq_assoc by simp
      finally show ?thesis
        using seq_assoc by simp
    qed
    also have "... = \<lparr>\<top> \<triangleright> p\<rparr> ; Atomic\<^sup>\<infinity> \<iinter> Atomic ; term ; (\<lparr>\<top> \<triangleright> p\<rparr> ; term \<iinter> Atomic ; term)\<^sup>\<infinity>"
      using seq_term_range_restriction seq_atomic_term2 by simp
    also have "... \<ge> (\<lparr>\<top> \<triangleright> p\<rparr> ; term) ; Atomic\<^sup>\<infinity> \<iinter> (Atomic ; term) ; (\<lparr>\<top> \<triangleright> p\<rparr> ; term \<iinter> Atomic ; term)\<^sup>\<infinity>" (is "_ \<ge> ?rhs")
      using conj.sync_mono_left inf_prefix_term seq_assoc seq_mono_right by simp
    also have "?rhs \<ge> (\<lparr>\<top> \<triangleright> p\<rparr> ; term \<iinter> Atomic ; term) ; (Atomic\<^sup>\<infinity> \<iinter> (\<lparr>\<top> \<triangleright> p\<rparr> ; term \<iinter> Atomic ; term)\<^sup>\<infinity>)" (is "_ \<ge> ?rhs")
      using seq_conj_interchange by simp
    also have "?rhs \<ge> (\<lparr>\<top> \<triangleright> p\<rparr> ; term \<iinter> Atomic ; term)\<^sup>\<infinity>"
      using conj_refine infiter_unfold order_refl range_restriction_spec seq_mono_right atomic_inf_range_restriction_spec_term by metis
    finally show ?thesis .
  qed
  hence "gfp (\<lambda>x. \<lparr>\<top> \<triangleright> p\<rparr> ; chaos \<iinter> (nil \<squnion> Atomic ; x)) \<ge> (\<lparr>\<top> \<triangleright> p\<rparr> ; term \<iinter> Atomic ; term)\<^sup>\<infinity>"
    using gfp_upperbound by metis

  ultimately show ?thesis
    by simp
qed

(* TODO Find a better name. *)
lemma conj_refines_nonaborting_eq:
  assumes nonaborting_c: "chaos \<ge> c"
  assumes d_refines_c: "c \<ge> d"
  shows "c \<iinter> d = d"
  using conj_to_inf_nonaborting d_refines_c inf.absorb_iff2 nonaborting_c by auto

lemma "chaos \<ge> Atomic\<^sup>\<infinity>"
  using chaos_def iter_ref_infiter by simp

lemma
  assumes "chaos \<ge> d"
  shows "(\<tau> p ; c) \<iinter> d \<ge> \<tau> p ; (c \<iinter> d)"
  using assms conj.nonaborting_sync_test_pre local.conj_commute by force

lemma
  assumes "chaos \<ge> c"
  assumes "chaos \<ge> d"
  shows "chaos \<ge> c ; d"
  using assms by (metis chaos_seq_chaos seq_mono)

lemma
  assumes "chaos \<ge> c"
  assumes "chaos \<ge> d"
  shows "chaos \<ge> c \<squnion> d"
  using assms by simp

lemma "chaos \<ge> nil"
  by (rule chaos_ref_nil)

(* Clean this up; I don't think this matches the paper. *)
lemma encode_always: "encode (\<box> (\<iota> p)) = \<tau> p ; (Atomic ; \<tau> p)\<^sup>\<omega>"
proof -
  have "\<tau> p ; chaos \<iinter> (nil \<squnion> Atomic ; (\<tau> p ; (Atomic ; \<tau> p)\<^sup>\<omega>)) \<ge> \<tau> p ; (Atomic ; \<tau> p)\<^sup>\<omega>"
  proof -
    have "\<tau> p ; chaos \<iinter> (nil \<squnion> Atomic ; (\<tau> p ; (Atomic ; \<tau> p)\<^sup>\<omega>))
            \<ge> \<tau> p ; (chaos \<iinter> (nil \<squnion> Atomic ; (\<tau> p ; (Atomic ; \<tau> p)\<^sup>\<omega>)))" (is "_ \<ge> ?rhs")
      using conj.sync_mono_right order_refl test_conj_distrib test_seq_refine by metis
    also have "?rhs = \<tau> p ; ((nil \<squnion> Atomic ; chaos) \<iinter> (nil \<squnion> Atomic ; (\<tau> p ; (Atomic ; \<tau> p)\<^sup>\<omega>)))"
      using chaos_def iter_unfold by simp
    also have "... \<ge> \<tau> p ; (nil \<squnion> Atomic ; (\<tau> p ; (Atomic ; \<tau> p)\<^sup>\<omega>))" (is "_ \<ge> ?rhs")
      using chaos_def conj_chaos_left iter_unfold by auto
    also have "?rhs = \<tau> p ; (Atomic ; \<tau> p)\<^sup>\<omega>"
      using iter_unfold seq_assoc by metis
    finally show ?thesis .
  qed
  hence "gfp (\<lambda>x. \<tau> p ; chaos \<iinter> (nil \<squnion> Atomic ; x)) \<ge> \<tau> p ; (Atomic ; \<tau> p)\<^sup>\<omega>"
    by (simp add: gfp_upperbound)

  moreover have "\<tau> p ; (Atomic ; \<tau> p)\<^sup>\<omega> \<ge> gfp (\<lambda>x. \<tau> p ; chaos \<iinter> (nil \<squnion> Atomic ; x))"
  proof -
    have "\<tau> p ; (nil \<squnion> Atomic ; gfp (\<lambda>x. \<tau> p ; chaos \<iinter> (nil \<squnion> Atomic ; x)))
            = \<tau> p ; (chaos \<iinter> (nil \<squnion> Atomic ; gfp (\<lambda>x. \<tau> p ; chaos \<iinter> (nil \<squnion> Atomic ; x))))"
      by simp
    also have a: "... \<ge> \<tau> p ; chaos \<iinter> (nil \<squnion> Atomic ; gfp (\<lambda>x. \<tau> p ; chaos \<iinter> (nil \<squnion> Atomic ; x)))" (is "_ \<ge> ?rhs")
    proof -
      have "gfp (\<lambda>x. \<tau> p ; chaos \<iinter> (nil \<squnion> Atomic ; x)) = encode (\<box> (\<iota> p))"
        by simp
      hence "chaos \<ge> gfp (\<lambda>x. \<tau> p ; chaos \<iinter> (nil \<squnion> Atomic ; x))"
        using inf_encode by metis
      hence "chaos \<ge> nil \<squnion> Atomic ; gfp (\<lambda>x. \<tau> p ; chaos \<iinter> (nil \<squnion> Atomic ; x))"
        using chaos_seq_chaos seq_mono chaos_ref_nil Atomic_nonaborting le_sup_iff by metis
      (* TODO Make this a bit neater. *)
      thus ?thesis
        using conj.nonaborting_sync_test_pre local.conj_commute order_refl by (smt (z3))
    qed
    also have b: "?rhs = gfp (\<lambda>x. \<tau> p ; chaos \<iinter> (nil \<squnion> Atomic ; x))"
      (* TODO Speed this up. Not sure why it's so slow. *)
      using gfp_unfold always_step_mono by metis
    finally have "\<tau> p ; (nil \<squnion> Atomic ; gfp (\<lambda>x. \<tau> p ; chaos \<iinter> (nil \<squnion> Atomic ; x)))
              \<ge> gfp (\<lambda>x. \<tau> p ; chaos \<iinter> (nil \<squnion> Atomic ; x))" .
    hence "nil \<squnion> Atomic ; \<tau> p ; (nil \<squnion> Atomic ; gfp (\<lambda>x. \<tau> p ; chaos \<iinter> (nil \<squnion> Atomic ; x)))
            \<ge> nil \<squnion> Atomic ; gfp (\<lambda>x. \<tau> p ; chaos \<iinter> (nil \<squnion> Atomic ; x))"
      using nil_ref_test seq_assoc seq_mono_right sup.mono test_top by metis
    hence "(Atomic ; \<tau> p)\<^sup>\<omega> \<ge> nil \<squnion> Atomic ; gfp (\<lambda>x. \<tau> p ; chaos \<iinter> (nil \<squnion> Atomic ; x))"
      using iter_induct_nil by presburger
    hence "\<tau> p ; (Atomic ; \<tau> p)\<^sup>\<omega> \<ge> \<tau> p ; (nil \<squnion> Atomic ; gfp (\<lambda>x. \<tau> p ; chaos \<iinter> (nil \<squnion> Atomic ; x)))"
      using seq_mono_right by simp
    hence "\<tau> p ; (Atomic ; \<tau> p)\<^sup>\<omega> \<ge> \<tau> p ; chaos \<iinter> (nil \<squnion> Atomic ; gfp (\<lambda>x. \<tau> p ; chaos \<iinter> (nil \<squnion> Atomic ; x)))"
      using a by simp
    hence "\<tau> p ; (Atomic ; \<tau> p)\<^sup>\<omega> \<ge> gfp (\<lambda>x. \<tau> p ; chaos \<iinter> (nil \<squnion> Atomic ; x))"
      using b by simp
    thus ?thesis .
  qed

  ultimately show ?thesis
    by simp
qed

lemma encode_eventually_always: "encode (\<diamond>\<^sub>f (\<box> (\<iota> p))) = term ; \<tau> p ; (Atomic ; \<tau> p)\<^sup>\<omega>"
  using unfair_eventually encode_always seq_assoc by simp

(*
lemma nonterminating_spec: "\<lceil>q\<rceil> \<ge> encode f"
proof -
  have "\<lceil>q\<rceil> = (\<Squnion>s. \<tau> {s} ; Atomic\<^sup>\<omega> ; \<tau> (q``{s}))"
    using pspec_def chaos_def by simp
  also have "... \<ge> (\<Squnion>s. \<tau> {s} ; Atomic\<^sup>\<infinity>)" (is "_ \<ge> ?rhs")
  proof -
    have "(\<Squnion>s. \<tau> {s} ; Atomic\<^sup>\<omega> ; \<tau> (q``{s})) = (\<Squnion>s. \<tau> {s} ; (Atomic\<^sup>\<star> \<squnion> Atomic\<^sup>\<infinity>) ; \<tau> (q``{s}))"
      using par.iter_isolation by simp
    also have "... = (\<Squnion>s. \<tau> {s} ; Atomic\<^sup>\<star> ; \<tau> (q``{s}) \<squnion> \<tau> {s} ; Atomic\<^sup>\<infinity> ; \<tau> (q``{s}))"
      using infiter_annil par.iter_isolate par.iter_isolation par.seq_nondet_distrib seq_assoc by metis
    also have "... \<ge> (\<Squnion>s. \<tau> {s} ; Atomic\<^sup>\<infinity> ; \<tau> (q``{s}))" (is "_ \<ge> ?rhs")
    proof -
      have "\<And>s. \<tau> {s} ; Atomic\<^sup>\<star> ; \<tau> (q``{s}) \<squnion> \<tau> {s} ; Atomic\<^sup>\<infinity> ; \<tau> (q``{s}) \<ge> \<tau> {s} ; Atomic\<^sup>\<infinity> ; \<tau> (q``{s})"
        by simp
      thus ?thesis
        by (rule SUP_mono')
    qed
    also have "?rhs = (\<Squnion>s. \<tau> {s} ; Atomic\<^sup>\<infinity>)"
      using infiter_annil seq_assoc by simp
    finally show ?thesis .
  qed
  also have "?rhs = Atomic\<^sup>\<infinity>"
    by (rule NOTDET_test_seq)
  also have "... \<ge> encode f"
    using inf_encode by simp
  finally show ?thesis .
qed
*)

definition forever :: "'b Temporal \<Rightarrow> 'a" where
  "forever f \<equiv> encode f \<iinter> Atomic\<^sup>\<infinity>"

lemma forever_always_eventually: "forever (\<box> (\<diamond>\<^sub>f (\<iota> p))) \<ge> (\<lparr>\<top> \<triangleright> p\<rparr> ; term \<iinter> Atomic ; term)\<^sup>\<infinity>"
  using conj_refine encode_always_eventually forever_def atomic_inf_range_restriction_spec_term by simp

lemma infinite_leapfrog: "c ; (d ; c)\<^sup>\<infinity> = (c ; d)\<^sup>\<infinity>"
  using gfp_rolling[of "\<lambda>x. c ; x" "\<lambda>x. d ; x"] infiter_step_mono infiter_def seq_assoc by simp

lemma infinite_distribute_conj:
  assumes "\<And>c1 c2. d \<iinter> c1 ; c2 \<ge> (d \<iinter> c1) ; (d \<iinter> c2)"
  shows "d \<iinter> c\<^sup>\<infinity> \<ge> (d \<iinter> c)\<^sup>\<infinity>"
proof -
  let ?G = "(\<lambda>x. c ; x)"
  let ?H = "(\<lambda>x. (d \<iinter> c) ; x)"
  let ?F = "(\<lambda>x. d \<iinter> x)"

  have gfp_g: "gfp ?G = c\<^sup>\<infinity>"
    using infiter_def by simp
  hence f_gfp_g: "?F (gfp ?G) = d \<iinter> c\<^sup>\<infinity>"
    by simp
  hence gfp_h: "gfp ?H = (d \<iinter> c)\<^sup>\<infinity>"
    using infiter_def by simp

  have "?F \<circ> ?G \<ge> ?H \<circ> ?F"
    using assms by (simp add: le_fun_def)

  have "mono ?F"
    using conj.sync_mono_right by (simp add: mono_def)
  have "mono ?G"
    by (rule infiter_step_mono)
  have "mono ?H"
    by (rule infiter_step_mono)

  (* This axiom doesn't exist in the theory, so this is sorry'd for now. *)
  have "\<And>C. ?F (\<Sqinter> C) = (\<Sqinter>c\<in>C. ?F c)" sorry
  hence "dist_over_inf ?F"
    by simp

  have "?F (gfp ?G) \<ge> gfp ?H"
    using fusion_gfp_geq \<open>?F \<circ> ?G \<ge> ?H \<circ> ?F\<close> \<open>dist_over_inf ?F\<close> \<open>mono ?H\<close> le_fun_def by metis
  thus ?thesis
    using infiter_def by simp
qed

lemma rely_eval2:
  assumes "single_reference b r"
  assumes "stable p r"
  assumes "stable b0 r"
  assumes "expr_eq b x \<inter> p \<subseteq> b0"
  shows "rely r \<iinter> \<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> (b0 \<inter> p)\<rparr> \<ge> \<lbrakk>b\<rbrakk>x"
proof -
  have "tolerates_interference p (\<top> \<triangleright> (b0 \<inter> p)) r"
    using assms stable_inter tolerates_interference_def tolerates_interference_restict_post top_greatest by metis
  moreover have "(p \<inter> (expr_eq b x)) \<triangleleft> Id \<subseteq> \<top> \<triangleright> (b0 \<inter> p)"
    using Int_subset_iff assms id_maintains_pre inf_commute inf_le1 inf_top_left restrict_range_def by metis
  ultimately show ?thesis
    using rely_eval assms by simp
qed

lemma guar_eval:
  assumes "refl g"
  shows "guar g \<iinter> \<lbrakk>e\<rbrakk>k \<ge> \<lbrakk>e\<rbrakk>k"
  using assms eval_guar_absorb order_refl by metis

lemma rely_guar_eval:
  assumes "refl g"
  assumes "single_reference b r"
  assumes "stable p r"
  assumes "stable b0 r"
  assumes "expr_eq b x \<inter> p \<subseteq> b0"
  shows "guar g \<iinter> rely r \<iinter> \<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> (b0 \<inter> p)\<rparr> \<ge> \<lbrakk>b\<rbrakk>x"
proof -
  have "guar g \<iinter> rely r \<iinter> \<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> (b0 \<inter> p)\<rparr> \<ge> guar g \<iinter> \<lbrakk>b\<rbrakk>x" (is "_ \<ge> ?rhs")
    using rely_eval2 assms conj.sync_mono_right conj_assoc by metis
  also have "?rhs \<ge> \<lbrakk>b\<rbrakk>x"
    using guar_eval assms by simp
  finally show ?thesis .
qed

lemma spec_test_post_eq:
  assumes "p \<le> q"
  shows "\<lparr>\<top> \<triangleright> p\<rparr> = \<lparr>\<top> \<triangleright> p\<rparr> ; \<tau> q"
  using assms spec_test_post
proof -
  have "\<lparr>\<top> \<triangleright> p\<rparr> = \<lparr>\<top> \<triangleright> p\<rparr> ; \<tau> p"
    using spec_test_post by blast
  also have "... = \<lparr>\<top> \<triangleright> p\<rparr> ; \<tau> (p \<inter> q)"
  proof -
    have "p = p \<inter> q"
      using assms by blast
    thus ?thesis
      by simp
  qed
  also have "... = \<lparr>\<top> \<triangleright> p\<rparr> ; \<tau> p ; \<tau> q"
    using test_seq_test seq_assoc by simp
  also have "... = \<lparr>\<top> \<triangleright> p\<rparr> ; \<tau> q"
    using spec_test_post by metis
  finally show ?thesis .
qed

lemma terminating_iteration:
  assumes "single_reference (b::(_, 'v::has_booleans) expr) r"
  assumes "stable p r"
  assumes "stable b0 r"
  assumes "stable b1 r"
  assumes "refl g"
  assumes "p \<inter> expr_eq b true \<le> b0"
  assumes "p \<inter> expr_eq b false \<le> b1"
  shows "rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> (b1 \<inter> p)\<rparr> \<ge> (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> p\<rparr>))\<^sup>\<star> ; \<lbrakk>b\<rbrakk>false"
proof -
  have "rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> (b1 \<inter> p)\<rparr> \<ge> rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> p\<rparr> ; \<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> (b1 \<inter> p)\<rparr>" (is "_ \<ge> ?rhs")
    using spec_seq_introduce conj.sync_mono_right order_refl seq_assoc seq_mono_right seq_term_term spec_test_restricts spec_univ test_seq_assert test_seq_refine by metis
  also have "?rhs \<ge> (rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> p\<rparr>) ; (rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> (b1 \<inter> p)\<rparr>)" (is "_ \<ge> ?rhs")
    using guar_seq_idem rely_seq_distrib conj_seq_distrib seq_assoc by metis
  also have "?rhs \<ge> (rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> p\<rparr>) ; \<lbrakk>b\<rbrakk>false" (is "_ \<ge> ?rhs")
    using rely_guar_eval assms inf_commute conj_commute seq_mono_right by metis
  also have "?rhs \<ge> (rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> p\<rparr>)\<^sup>\<star> ; \<lbrakk>b\<rbrakk>false" (is "_ \<ge> ?rhs")
  proof -
    have "\<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> p\<rparr> \<ge> nil"
      using assert_galois_test range_restriction_spec seq_mono_left term_nil by fastforce
    moreover have "\<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> p\<rparr> \<ge> (\<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> p\<rparr>) ; (\<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> p\<rparr>)"
      using order_refl range_restriction_spec seq_assoc seq_mono seq_term_term test_seq_assert test_seq_refine by (metis (no_types))
    ultimately have a: "\<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> p\<rparr> \<ge> nil \<squnion> (\<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> p\<rparr>) ; (\<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> p\<rparr>)"
      by simp

    have "rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> p\<rparr> \<ge> nil \<squnion> (rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> p\<rparr>) ; (rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> p\<rparr>)"
    proof -
      have "rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> p\<rparr> \<ge> rely r \<iinter> guar g \<iinter> (nil \<squnion> (\<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> p\<rparr>) ; (\<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> p\<rparr>))" (is "_ \<ge> ?rhs")
        using a conj.sync_mono_right by simp
      also have "?rhs = (rely r \<iinter> guar g \<iinter> nil) \<squnion> (rely r \<iinter> guar g \<iinter> (\<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> p\<rparr>) ; (\<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> p\<rparr>))"
        using conj.sync_nondet_distrib by presburger
      also have "... \<ge> (rely r \<iinter> guar g \<iinter> nil) \<squnion> (rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> p\<rparr>) ; (rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> p\<rparr>)" (is "_ \<ge> ?rhs")
        using conj_seq_distrib guar_seq_idem rely_seq_distrib le_sup_iff sup.orderE sup_ge1 by (smt (z3))
      also have "?rhs = nil \<squnion> (rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> p\<rparr>) ; (rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> p\<rparr>)"
        using guar_conj_nil local.conj_assoc local.conj_commute nil_conj_rely by metis
      finally show ?thesis
        by simp
    qed
    hence "(rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<ge> (rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> p\<rparr>)\<^sup>\<star>"
      using fiter_induct by fastforce
    thus ?thesis
      using seq_mono_left by blast
  qed
  also have "?rhs \<ge> (rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> (p \<inter> b0)\<rparr> ; \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> p\<rparr>)\<^sup>\<star> ; \<lbrakk>b\<rbrakk>false" (is "_ \<ge> ?rhs")
  proof -
    have "\<lparr>\<top> \<triangleright> p\<rparr> \<ge> \<lparr>\<top> \<triangleright> (p \<inter> b0)\<rparr> ; \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> p\<rparr>"
      using spec_seq_introduce seq_mono_left seq_term_range_restriction spec_assert_restricts spec_term by metis
    thus ?thesis
      using conj.sync_mono_right fiter_mono seq_assoc seq_mono_left seq_mono_right by force
  qed
  also have "?rhs \<ge> ((rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> (p \<inter> b0)\<rparr>) ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> p\<rparr>))\<^sup>\<star> ; \<lbrakk>b\<rbrakk>false" (is "_ \<ge> ?rhs")
    using guar_seq_idem rely_seq_distrib conj_seq_distrib seq_assoc fiter_mono seq_mono_left by metis
  also have "?rhs \<ge> (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> p\<rparr>))\<^sup>\<star> ; \<lbrakk>b\<rbrakk>false" (is "_ \<ge> ?rhs")
  proof -
    have "rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> (p \<inter> b0)\<rparr> \<ge> \<lbrakk>b\<rbrakk>true"
      using rely_guar_eval assms inf_commute conj_commute by metis
    thus ?thesis
      using fiter_mono seq_mono_left by simp
  qed
  finally show ?thesis .
qed

lemma "rely r \<iinter> \<bottom> = \<bottom>"
proof -
  have "rely r \<iinter> \<bottom> = (env_assump r)\<^sup>\<omega> \<iinter> \<bottom>"
    using rely_def by simp
  also have "... = (\<epsilon> r \<squnion> Pgm \<squnion> (atomic.negate (\<epsilon> r) \<sqinter> \<E>) ; \<top>)\<^sup>\<omega> \<iinter> \<bottom>"
    using env_assump_def by simp
  also have "... = (nil \<squnion> (\<epsilon> r \<squnion> Pgm \<squnion> (atomic.negate (\<epsilon> r) \<sqinter> \<E>) ; \<top>) ; (\<epsilon> r \<squnion> Pgm \<squnion> (atomic.negate (\<epsilon> r) \<sqinter> \<E>) ; \<top>)\<^sup>\<omega>) \<iinter> \<bottom>"
    using iter_unfold by simp
  also have "... = \<bottom> \<squnion> ((\<epsilon> r \<squnion> Pgm \<squnion> (atomic.negate (\<epsilon> r) \<sqinter> \<E>) ; \<top>) ; (\<epsilon> r \<squnion> Pgm \<squnion> (atomic.negate (\<epsilon> r) \<sqinter> \<E>) ; \<top>)\<^sup>\<omega> \<iinter> \<bottom>)"
    using conj.nondet_sync_distrib conj_magic_nonaborting par.chaos_ref_nil by simp
  also have "... = (\<epsilon> r \<squnion> Pgm \<squnion> (atomic.negate (\<epsilon> r) \<sqinter> \<E>) ; \<top>) ; (\<epsilon> r \<squnion> Pgm \<squnion> (atomic.negate (\<epsilon> r) \<sqinter> \<E>) ; \<top>)\<^sup>\<omega> \<iinter> \<bottom>"
    by simp
  also have "... = (\<epsilon> r ; (\<epsilon> r \<squnion> Pgm \<squnion> (atomic.negate (\<epsilon> r) \<sqinter> \<E>) ; \<top>)\<^sup>\<omega> \<squnion>
                    Pgm ; (\<epsilon> r \<squnion> Pgm \<squnion> (atomic.negate (\<epsilon> r) \<sqinter> \<E>) ; \<top>)\<^sup>\<omega> \<squnion>
                    (atomic.negate (\<epsilon> r) \<sqinter> \<E>) ; \<top> ; (\<epsilon> r \<squnion> Pgm \<squnion> (atomic.negate (\<epsilon> r) \<sqinter> \<E>) ; \<top>)\<^sup>\<omega>) \<iinter> \<bottom>"
    by (simp add: nondet_seq_distrib)
  also have "... = (\<epsilon> r ; (\<epsilon> r \<squnion> Pgm \<squnion> (atomic.negate (\<epsilon> r) \<sqinter> \<E>) ; \<top>)\<^sup>\<omega> \<squnion>
                    Pgm ; (\<epsilon> r \<squnion> Pgm \<squnion> (atomic.negate (\<epsilon> r) \<sqinter> \<E>) ; \<top>)\<^sup>\<omega> \<squnion>
                    (atomic.negate (\<epsilon> r) \<sqinter> \<E>) ; \<top>) \<iinter> \<bottom>"
    using seq_assoc by simp
  also have "... \<le> (Atomic ; (\<epsilon> r \<squnion> Pgm \<squnion> (atomic.negate (\<epsilon> r) \<sqinter> \<E>) ; \<top>)\<^sup>\<omega> \<squnion>
                    Atomic ; (\<epsilon> r \<squnion> Pgm \<squnion> (atomic.negate (\<epsilon> r) \<sqinter> \<E>) ; \<top>)\<^sup>\<omega> \<squnion>
                    Atomic ; \<top>) \<iinter> \<bottom>"
  proof -
    have "Atomic \<ge> \<epsilon> r"
      by (rule Atomic_ref_env)
    moreover have "Atomic \<ge> Pgm"
      using Atomic_ref_pgm pgm.Hom_def by simp
    moreover have "Atomic \<ge> atomic.negate (\<epsilon> r) \<sqinter> \<E>"
      using Atomic_def2 by (simp add: sup.coboundedI2)
    ultimately show ?thesis
      by (smt (verit) conj.sync_mono_right inf_top_right le_iff_inf le_sup_iff local.conj_commute nondet_seq_distrib par.seq_nondet_distrib seq_mono sup.left_commute sup.orderE)
  qed
  also have "... = Atomic ; ((\<epsilon> r \<squnion> Pgm \<squnion> (atomic.negate (\<epsilon> r) \<sqinter> \<E>) ; \<top>)\<^sup>\<omega> \<squnion>
                    (\<epsilon> r \<squnion> Pgm \<squnion> (atomic.negate (\<epsilon> r) \<sqinter> \<E>) ; \<top>)\<^sup>\<omega> \<squnion>
                    \<top>) \<iinter> \<bottom>"
    using par.seq_nondet_distrib by presburger
  also have "... = \<bottom>"
    using Atomic_nonaborting atomic.Hom_def atomic_seq_abort_conj_left atomic_sup_nil conj.atomic_pre_sync_nil conj.syncid_syncid conj_to_inf_nonaborting local.conj_assoc par.chaos_ref_nil sup_top_right test_top by metis
  finally show ?thesis
    using le_bot by simp
qed

lemma term_magic_refines_spec: "\<lparr>q\<rparr> \<ge> term ; \<bottom>"
proof -
  have "\<lparr>q\<rparr> = (\<Squnion>s. (\<tau> {s} ; term ; \<tau> (q``{s})))"
    using old_spec by simp
  moreover have "... \<ge> (\<Squnion>s. \<tau> {s} ; term ; \<tau> (q``{s})) ; \<bottom>" (is "_ \<ge> ?rhs")
    using nil_ref_test seq_mono_right seq_nil_right test.hom_bot by (metis (lifting))
  moreover have "?rhs = (\<Squnion>s. \<tau> {s} ; term ; \<tau> (q``{s}) ; \<bottom>)"
    by (rule NONDET_seq_distrib)
  moreover have "... = (\<Squnion>s. \<tau> {s} ; term ; \<bottom>)"
    using seq_assoc test_seq_magic by simp
  moreover have "... = term ; \<bottom>"
    using NONDET_seq_distrib NOTDET_test_seq by metis
  ultimately show ?thesis
    by simp
qed

lemma seq_magic_atomic_infiter: "c ; \<bottom> = c ; \<bottom> \<iinter> Atomic\<^sup>\<infinity>"
proof -
  have "c = c \<iinter> chaos"
    by simp
  hence "c ; \<bottom> = (c \<iinter> chaos) ; \<bottom>"
    by simp
  also have "... = c ; \<bottom> \<iinter> chaos ; \<bottom>"
    using conj.test_sync_post2 test.hom_bot test_seq_idem test_seq_test by metis
  also have "... = c ; \<bottom> \<iinter> Atomic\<^sup>\<infinity>"
    using chaos_def infiter_iter_magic by simp
  finally show ?thesis .
qed

lemma nonterminating_iteration_helper_induction_1:
  assumes "p \<subseteq> expr_type b boolean"
  shows "(\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<tau> (-t) ; \<lparr>{(s, s'). (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}\<rparr>) \<iinter> Atomic ; chaos) ; c\<^sup>\<infinity> \<squnion>
         (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<tau> t ; \<lparr>{(s, s'). (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}\<rparr>) \<iinter> Atomic ; chaos) ; c\<^sup>\<infinity>
          = (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<tau> (-t) ; \<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr>) \<iinter> Atomic ; chaos) ; c\<^sup>\<infinity> \<squnion>
            (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> (expr_eq b true \<inter> p)\<rparr>) \<iinter> Atomic ; chaos) ; c\<^sup>\<infinity>"
proof -
  let ?c = c
  have "\<tau> (-t) ; \<lparr>{(s, s'). (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}\<rparr>
           = \<tau> (-t) ; \<lparr>{(s, s'). s' \<in> expr_eq b false \<and> s' \<in> p}\<rparr>"
  proof -
    have "\<tau> (-t) ; \<lparr>{(s, s'). (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}\<rparr>
            = \<tau> (-t) ; \<lparr>(-t) \<triangleleft> {(s, s'). (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}\<rparr>"
      using test_restricts_spec by simp
    also have "... = \<tau> (-t) ; \<lparr>{(s, s'). s \<in> (-t)} \<inter> {(s, s'). (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}\<rparr>"
      by (simp add: restrict_domain_def)
    also have "... = \<tau> (-t) ; \<lparr>{(s, s'). s \<in> (-t) \<and> (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}\<rparr>"
    proof -
      have "{(s, s'). s \<in> (-t)} \<inter> {(s, s'). (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}
              = {(s, s'). s \<in> (-t) \<and> (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}" by auto
      thus ?thesis
        by simp
    qed
    also have "... = \<tau> (-t) ; \<lparr>{(s, s'). s \<in> (-t) \<and> s' \<notin> expr_eq b true \<and> s' \<in> p}\<rparr>"
      using Compl_iff by metis
    also have "... = \<tau> (-t) ; \<lparr>{(s, s'). s \<in> (-t)} \<inter> {(s, s'). s' \<notin> expr_eq b true \<and> s' \<in> p}\<rparr>"
    proof -
      have "{(s, s'). s \<in> (-t)} \<inter> {(s, s'). s' \<notin> expr_eq b true \<and> s' \<in> p}
              = {(s, s'). s \<in> (-t) \<and> s' \<notin> expr_eq b true \<and> s' \<in> p}" by auto
      thus ?thesis
        by simp
    qed
    also have "... = \<tau> (-t) ; \<lparr>(-t) \<triangleleft> {(s, s'). s' \<notin> expr_eq b true \<and> s' \<in> p}\<rparr>"
      by (simp add: restrict_domain_def)
    also have "... = \<tau> (-t) ; \<lparr>{(s, s'). s' \<notin> expr_eq b true \<and> s' \<in> p}\<rparr>"
      using test_restricts_spec by simp
    also have "... = \<tau> (-t) ; \<lparr>{(s, s'). s' \<in> expr_eq b false \<and> s' \<in> p}\<rparr>"
    proof -
      have "\<And>s'. s' \<notin> expr_eq b true \<and> s' \<in> p \<Longrightarrow> s' \<in> expr_eq b false \<and> s' \<in> p" (is "\<And>s'. ?P s' \<Longrightarrow> ?Q s'")
      proof -
        fix s'
        assume "?P s'"
        have a: "s' \<in> expr_type b boolean"
          using \<open>?P s'\<close> \<open>p \<subseteq> expr_type b boolean\<close> by auto
        have "s' \<in> expr_eq b true \<union> expr_eq b false"
        proof -
          have "expr_type b boolean = expr_eq b true \<union> expr_eq b false"
            using expr_type_def by auto
          thus ?thesis
            using a by simp
        qed
        thus "?Q s'"
          using \<open>?P s'\<close> by simp
      qed
      moreover have "\<And>s'. s' \<in> expr_eq b false \<and> s' \<in> p \<Longrightarrow> s' \<notin> expr_eq b true \<and> s' \<in> p" (is "\<And>s'. ?P s' \<Longrightarrow> ?Q s'")
      proof -
        fix s'
        assume "?P s'"
        have a: "s' \<in> expr_type b boolean"
          using \<open>?P s'\<close> \<open>p \<subseteq> expr_type b boolean\<close> by auto
        have "s' \<in> expr_eq b true \<union> expr_eq b false"
        proof -
          have "expr_type b boolean = expr_eq b true \<union> expr_eq b false"
            using expr_type_def by auto
          thus ?thesis
            using a by simp
        qed
        thus "?Q s'"
          using \<open>?P s'\<close> expr_eq_distinct_true_false by auto
      qed
      ultimately show ?thesis
        by metis
    qed
    finally show ?thesis .
  qed

  moreover have "\<tau> t ; \<lparr>{(s, s'). (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}\<rparr>
           = \<tau> t ; \<lparr>{(s, s'). s' \<in> expr_eq b true \<and> s' \<in> p}\<rparr>"
  proof -
    have "\<tau> t ; \<lparr>{(s, s'). (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}\<rparr>
            = \<tau> t; \<lparr>t \<triangleleft> {(s, s'). (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}\<rparr>"
      using test_restricts_spec by simp
    also have "... = \<tau> t ; \<lparr>{(s, s'). s \<in> t} \<inter> {(s, s'). (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}\<rparr>"
      by (simp add: restrict_domain_def)
    also have "... = \<tau> t ; \<lparr>{(s, s'). s \<in> t \<and> (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}\<rparr>"
    proof -
      have "{(s, s'). s \<in> t} \<inter> {(s, s'). (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}
              = {(s, s'). s \<in> t \<and> (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}" by auto
      thus ?thesis
        by simp
    qed
    also have "... = \<tau> t ; \<lparr>{(s, s'). s \<in> t \<and> s' \<in> expr_eq b true \<and> s' \<in> p}\<rparr>"
      by metis
    also have "... = \<tau> t ; \<lparr>{(s, s'). s \<in> t} \<inter> {(s, s'). s' \<in> expr_eq b true \<and> s' \<in> p}\<rparr>"
    proof -
      have "{(s, s'). s \<in> t} \<inter> {(s, s'). s' \<in> expr_eq b true \<and> s' \<in> p}
              = {(s, s'). s \<in> t \<and> s' \<in> expr_eq b true \<and> s' \<in> p}"
        by auto
      thus ?thesis
        by simp
    qed
    also have "... = \<tau> t ; \<lparr>t \<triangleleft> {(s, s'). s' \<in> expr_eq b true \<and> s' \<in> p}\<rparr>"
      by (simp add: restrict_domain_def)
    also have "... = \<tau> t ; \<lparr>{(s, s'). s' \<in> expr_eq b true \<and> s' \<in> p}\<rparr>"
      using test_restricts_spec by simp
    finally show ?thesis .
  qed

  ultimately show  ?thesis
    unfolding expr_eq_def using range_restriction_spec seq_assoc by auto
qed

lemma nonterminating_iteration_helper_induction_2:
  assumes "single_reference b r"
  assumes "stable (expr_eq b false) r"
  shows "(\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<tau> (-t) ; \<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr>) \<iinter> Atomic ; chaos) ; \<tau> (expr_eq b false) ; (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<lparr>{(s, s'). ((s \<in> t) = (s' \<in> expr_eq b true)) \<and> (s' \<in> p)}\<rparr>) \<iinter> Atomic ; chaos)\<^sup>\<infinity> \<squnion>
         (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos) ; (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<lparr>{(s, s'). ((s \<in> t) = (s' \<in> expr_eq b true)) \<and> (s' \<in> p)}\<rparr>) \<iinter> Atomic ; chaos)\<^sup>\<infinity>
            \<le> rely r \<iinter> (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<tau> (-t) ; \<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr>) \<iinter> Atomic ; chaos) ; \<tau> (expr_eq b false) ; idle ; \<bottom> \<squnion>
                        (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos) ; (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<lparr>{(s, s'). ((s \<in> t) = (s' \<in> expr_eq b true)) \<and> (s' \<in> p)}\<rparr>) \<iinter> Atomic ; chaos)\<^sup>\<infinity>"
proof -
  let ?c = "\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<lparr>{(s, s'). ((s \<in> t) = (s' \<in> expr_eq b true)) \<and> (s' \<in> p)}\<rparr>) \<iinter> Atomic ; chaos"
  have "\<tau> (expr_eq b false) ; ?c\<^sup>\<infinity> = \<tau> (expr_eq b false) ; ?c ; ?c\<^sup>\<infinity>"
    using infiter_unfold seq_assoc by simp
  moreover have "... = \<tau> (expr_eq b false) ; (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<lparr>{(s, s'). (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}\<rparr>) \<iinter> Atomic ; chaos) ; ?c\<^sup>\<infinity>"
    by simp
  moreover have "... = (\<tau> (expr_eq b false) ; \<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<lparr>{(s, s'). (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}\<rparr>) \<iinter> Atomic ; chaos) ; ?c\<^sup>\<infinity>"
  proof -
    have "chaos \<ge> Atomic ; chaos"
      using iter_unfold chaos_def le_sup_iff order_refl by metis
    thus ?thesis
      using conj.nonaborting_sync_test_pre conj_commute seq_assoc by simp
  qed
  moreover have "... \<le> (\<tau> (expr_eq b false) ; (rely r \<iinter> idle ; \<tau> (expr_eq b true) ; idle) ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<lparr>{(s, s'). (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}\<rparr>) \<iinter> Atomic ; chaos) ; ?c\<^sup>\<infinity>" (is "_ \<le> (?a1 ; (rely r \<iinter> ?a2) ; ?a3 \<iinter> ?a4) ; ?a5")
  proof -
    have "\<lbrakk>b\<rbrakk>true \<le> rely r \<iinter> idle ; \<tau> (expr_eq b true) ; idle"
      using single_reference_eval \<open>single_reference b r\<close> by metis
    thus ?thesis
      using seq_mono conj.sync_mono_left by simp
  qed
  moreover have "... \<le> rely r \<iinter> idle ; \<bottom>"
  proof -
    have "\<tau> (expr_eq b false) ; (rely r \<iinter> idle ; \<tau> (expr_eq b true) ; idle)
            = rely r \<iinter> \<tau> (expr_eq b false) ; idle ; \<tau> (expr_eq b true) ; idle"
      using seq_assoc test_pre_rely by force
    also have "... \<le> rely r \<iinter> idle ; \<tau> (expr_eq b false) ; \<tau> (expr_eq b true) ; idle"
      using rely_idle_stable \<open>stable (expr_eq b false) r\<close> refine_within_rely_left by simp
    also have "... = rely r \<iinter> idle ; \<tau> (expr_eq b false \<inter> expr_eq b true) ; idle"
      using seq_assoc test_seq_test by simp
    also have "... = rely r \<iinter> idle ; \<bottom> ; idle"
      using expr_eq_distinct_true_false inf_commute test.hom_bot by metis
    also have "... = rely r \<iinter> idle ; \<bottom>"
      using seq_assoc by simp
    finally have "\<tau> (expr_eq b false) ; (rely r \<iinter> idle ; \<tau> (expr_eq b true) ; idle)
                    \<le> rely r \<iinter> idle ; \<bottom>" .
    hence "(?a1 ; (rely r \<iinter> ?a2) ; ?a3 \<iinter> ?a4) ; ?a5 \<le> ((rely r \<iinter> idle ; \<bottom>) ; ?a3 \<iinter> ?a4) ; ?a5"
      using conj.sync_mono_left seq_mono_left by meson
    also have "... = ((rely r \<iinter> idle) ; \<bottom> ; ?a3 \<iinter> ?a4) ; ?a5"
      by (metis (lifting) conj.test_sync_post test.hom_bot)
    also have "... = ((rely r \<iinter> idle) ; \<bottom> \<iinter> ?a4) ; ?a5"
      using seq_assoc by simp
    also have "... = (rely r \<iinter> idle \<iinter> ?a4) ; \<bottom> ; ?a5"
      by (smt (z3) conj.test_sync_post local.conj_commute test.hom_bot)
    also have "... = (rely r \<iinter> idle \<iinter> ?a4) ; \<bottom>"
      using seq_assoc by simp
    finally have "(?a1 ; (rely r \<iinter> ?a2) ; ?a3 \<iinter> ?a4) ; ?a5 \<le> (rely r \<iinter> idle \<iinter> ?a4) ; \<bottom>" .
    hence "(?a1 ; (rely r \<iinter> ?a2) ; ?a3 \<iinter> ?a4) ; ?a5 \<le> (rely r \<iinter> idle \<iinter> Atomic ; chaos) ; \<bottom>"
      by simp
    also have "... = rely r \<iinter> idle ; \<bottom> \<iinter> Atomic ; chaos ; \<bottom>"
      using conj.test_sync_post local.conj_commute seq_assoc test.hom_bot test_seq_idem by (metis (no_types))
    also have "... = rely r \<iinter> idle ; \<bottom> \<iinter> Atomic ; Atomic\<^sup>\<infinity>"
      using chaos_def infiter_iter_magic seq_assoc by simp
    also have "... = rely r \<iinter> idle ; \<bottom> \<iinter> Atomic\<^sup>\<infinity>"
      using infiter_unfold by simp
    also have "... = rely r \<iinter> (guar Id \<iinter> term) ; \<bottom> \<iinter> Atomic\<^sup>\<infinity>"
      using idle_def by simp
    also have a: "... = rely r \<iinter> (guar Id ; \<bottom> \<iinter> term ; \<bottom>) \<iinter> Atomic\<^sup>\<infinity>"
      using conj.test_sync_post local.conj_commute seq_assoc seq_magic_left test.hom_bot by (metis (no_types))
    also have b: "... = rely r \<iinter> guar Id ; \<bottom> \<iinter> term ; \<bottom> \<iinter> chaos ; \<bottom>"
      using chaos_def infiter_iter_magic conj_assoc by simp
    also have "... = rely r \<iinter> guar Id ; \<bottom> \<iinter> (term \<iinter> chaos) ; \<bottom>"
      using conj.test_sync_post conj_chaos seq_assoc seq_magic_left test.hom_bot by metis
    also have "... = rely r \<iinter> guar Id ; \<bottom> \<iinter> term ; \<bottom>"
      by simp
    also have "... = rely r \<iinter> (guar Id \<iinter> term) ; \<bottom>"
      using a b chaos_def conj.test_sync_post conj.test_sync_post_helper2 conj_id infiter_iter_magic test.hom_bot by metis
    also have "... = rely r \<iinter> idle ; \<bottom>"
      using idle_def by simp
    finally show ?thesis .
  qed
  ultimately have "\<tau> (expr_eq b false) ; ?c\<^sup>\<infinity> \<le> rely r \<iinter> idle ; \<bottom>"
    by simp
  hence "\<tau> (expr_eq b false) ; ?c\<^sup>\<infinity> \<le> \<tau> (expr_eq b false) ; (rely r \<iinter> idle ; \<bottom>)"
    using test_seq_refine by simp
  hence "(\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<tau> (-t) ; \<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr>) \<iinter> Atomic ; chaos) ; \<tau> (expr_eq b false) ; ?c\<^sup>\<infinity>
            \<le> (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<tau> (-t) ; \<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr>) \<iinter> Atomic ; chaos) ; \<tau> (expr_eq b false) ; (rely r \<iinter> idle ; \<bottom>)"
    using seq_assoc seq_mono_right by simp
  also have "... \<le> rely r \<iinter> (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<tau> (-t) ; \<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr>) \<iinter> Atomic ; chaos) ; \<tau> (expr_eq b false) ; (rely r \<iinter> idle ; \<bottom>)"
    using rely_remove refine_within_rely_right seq_assoc by simp
  finally have "(\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<tau> (-t) ; \<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr>) \<iinter> Atomic ; chaos) ; \<tau> (expr_eq b false) ; ?c\<^sup>\<infinity> \<squnion>
         (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos) ; ?c\<^sup>\<infinity>
            \<le> rely r \<iinter> (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<tau> (-t) ; \<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr>) \<iinter> Atomic ; chaos) ; \<tau> (expr_eq b false) ; (rely r \<iinter> idle ; \<bottom>) \<squnion>
               (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos) ; ?c\<^sup>\<infinity>"
    using le_iff_sup le_sup_iff order_refl by (smt (z3))
  moreover have "... = rely r \<iinter> (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<tau> (-t) ; \<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr>) \<iinter> Atomic ; chaos) ; \<tau> (expr_eq b false) ; idle ; \<bottom> \<squnion>
               (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos) ; ?c\<^sup>\<infinity>"
    using equal_within_rely_right local.conj.left_idem seq_assoc by (smt (z3))
  moreover have "... \<le> rely r \<iinter> (rely r \<iinter> (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<tau> (-t) ; \<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr>) \<iinter> Atomic ; chaos) ; \<tau> (expr_eq b false) ; idle ; \<bottom> \<squnion>
                                  (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos) ; ?c\<^sup>\<infinity>)"
    using rely_remove by simp
  moreover have "... \<le> rely r \<iinter> ((\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<tau> (-t) ; \<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr>) \<iinter> Atomic ; chaos) ; \<tau> (expr_eq b false) ; idle ; \<bottom> \<squnion>
                                  (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos) ; ?c\<^sup>\<infinity>)"
    using conj.sync_nondet_distrib by force
  ultimately show ?thesis
    by simp
qed

lemma nonterminating_iteration_helper_induction_3:
  assumes "refl g"
  shows "rely r \<iinter> (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<tau> (-t) ; \<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr>) \<iinter> Atomic ; chaos) ; \<tau> (expr_eq b false) ; idle ; \<bottom> \<squnion>
         (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos) ; (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<lparr>{(s, s'). ((s \<in> t) = (s' \<in> expr_eq b true)) \<and> (s' \<in> p)}\<rparr>) \<iinter> Atomic ; chaos)\<^sup>\<infinity>
            \<le> rely r \<iinter> \<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<bottom>) \<squnion>
               (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos) ; (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<lparr>{(s, s'). ((s \<in> t) = (s' \<in> expr_eq b true)) \<and> (s' \<in> p)}\<rparr>) \<iinter> Atomic ; chaos)\<^sup>\<infinity>"
proof -
  let ?c = "\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<lparr>{(s, s'). ((s \<in> t) = (s' \<in> expr_eq b true)) \<and> (s' \<in> p)}\<rparr>) \<iinter> Atomic ; chaos"
  have "(\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<tau> (-t) ; \<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr>) \<iinter> Atomic ; chaos) ; \<tau> (expr_eq b false) ; idle ; \<bottom>
          = (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<tau> (-t) ; \<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr>) ; \<tau> (expr_eq b false) \<iinter> Atomic ; chaos ; \<tau> (expr_eq b false)) ; idle ; \<bottom>"
    using conj.test_sync_post2 by simp
  also have "... \<le> (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<tau> (-t) ; \<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr>) ; \<tau> (expr_eq b false) ; idle \<iinter> Atomic ; chaos ; \<tau> (expr_eq b false) ; idle) ; \<bottom>"
    using conj.idem seq_conj_interchange seq_mono_left by metis
  also have "... \<le> \<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<tau> (-t) ; \<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr>) ; \<tau> (expr_eq b false) ; idle ; \<bottom> \<iinter>
                    Atomic ; chaos ; \<tau> (expr_eq b false) ; idle ; \<bottom>"
    using conj.test_sync_idem seq_conj_interchange test.hom_bot by metis
  also have "... \<le> \<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<tau> (-t) ; \<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr>) ; \<tau> (expr_eq b false) ; idle ; \<bottom>"
    using Atomic_nonaborting chaos_seq_chaos conj_conjoin_non_aborting idle_nonaborting nil_ref_test seq_mono seq_mono_left seq_nil_right test.hom_bot by (metis (no_types))
  also have "... = \<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<tau> (-t) ; \<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr>) ; idle ; \<bottom>" 
    using spec_test_post conj.test_sync_post inf_commute seq_assoc test_seq_idem test_seq_test by (smt (z3))
  also have "... \<le> \<lbrakk>b\<rbrakk>true ; (rely r \<iinter> (guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<tau> (-t) ; \<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr>) ; idle) ; \<bottom>"
  proof -
    have "\<And>x. (rely r \<iinter> x) ; idle \<le> rely r \<iinter> x ; idle"
      by (meson order_trans rely_remove rely_seq_distrib seq_mono_right)
    thus ?thesis
      using conj.sync_mono_left local.conj_assoc seq_assoc seq_mono_left seq_mono_right by (metis (no_types))
  qed
  also have "... \<le> \<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<tau> (-t) ; \<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr> ; idle) ; \<bottom>"
  proof -
    have "\<And>x. (guar g \<iinter> x) ; idle =  guar g \<iinter> x ; idle"
      using \<open>refl g\<close> guar_distrib_seq_eq guar_idle by metis
    thus ?thesis
      using conj_assoc by simp
  qed
  also have "... \<le> \<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; term ; term) ; \<bottom>"
  proof -
    have "\<tau> (-t) ; \<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr> \<le> term"
      by (meson seq_mono_right spec_term test_seq_refine)
    thus ?thesis
    proof -
      have "\<And>a aa B. \<not> a \<le> aa \<or> \<tau> B ; a \<le> aa"
        by (meson seq_mono_right test_seq_refine)
      then show ?thesis
        using conj.sync_mono_right local.conj_commute range_restriction_spec seq_assoc seq_mono_left seq_mono_right term_ref_idle by presburger
    qed
  qed
  also have "... \<le> \<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term) ; \<bottom>"
    using seq_term_term seq_assoc by simp
  also have "... = \<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<bottom>)"
    using conj.test_sync_post seq_assoc test.hom_bot by (metis (no_types))
  finally have "(\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<tau> (-t) ; \<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr>) \<iinter> Atomic ; chaos) ; \<tau> (expr_eq b false) ; idle ; \<bottom>
                  \<le> \<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<bottom>)" .
  thus ?thesis
    by (meson conj.sync_mono_right order_refl sup.mono)
qed

lemma nonterminating_iteration_helper_induction:
  assumes "single_reference (b::(_, 'v::has_booleans) expr) r"
  assumes "refl g"
  assumes "stable (expr_eq b false) r"
  assumes "p \<subseteq> expr_type b boolean"
  shows "(rely r \<iinter> \<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos)\<^sup>\<infinity>
          \<ge> (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<lparr>{(s, s'). ((s \<in> t) = (s' \<in> expr_eq b true)) \<and> (s' \<in> p)}\<rparr>) \<iinter> Atomic ; chaos)\<^sup>\<infinity>" (is "_ \<ge> ?c\<^sup>\<infinity>")
proof -
  have "?c\<^sup>\<infinity> = (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<lparr>{(s, s'). (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}\<rparr>) \<iinter> Atomic ; chaos) ; ?c\<^sup>\<infinity>"
    using infiter_unfold by simp
  moreover have "... = (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; (\<tau> (-t) \<squnion> \<tau> t) ; \<lparr>{(s, s'). (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}\<rparr>) \<iinter> Atomic ; chaos) ; ?c\<^sup>\<infinity>"
    using test.Hom_def test.hom_compl_inf test_top by simp
  moreover have "... = (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<tau> (-t) ; \<lparr>{(s, s'). (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}\<rparr>) \<iinter> Atomic ; chaos) ; ?c\<^sup>\<infinity> \<squnion>
                       (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<tau> t ; \<lparr>{(s, s'). (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}\<rparr>) \<iinter> Atomic ; chaos) ; ?c\<^sup>\<infinity>"
    using conj.sync_nondet_distrib conj_commute nondet_seq_distrib par.seq_nondet_distrib by simp
  moreover have "... = (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<tau> (-t) ; \<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr>) \<iinter> Atomic ; chaos) ; ?c\<^sup>\<infinity> \<squnion>
                       (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> (expr_eq b true \<inter> p)\<rparr>) \<iinter> Atomic ; chaos) ; ?c\<^sup>\<infinity>"
    using nonterminating_iteration_helper_induction_1 \<open>p \<subseteq> expr_type b boolean\<close> by simp
  moreover have "... \<le> (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<tau> (-t) ; \<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr>) \<iinter> Atomic ; chaos) ; \<tau> (expr_eq b false) ; ?c\<^sup>\<infinity> \<squnion>
                        (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos) ; ?c\<^sup>\<infinity>"
  proof -
    have "\<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr> = \<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr> ; \<tau> (expr_eq b false)"
      using spec_test_post_eq by blast
    hence "(\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<tau> (-t) ; \<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr>) \<iinter> Atomic ; chaos) ; ?c\<^sup>\<infinity>
            = (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<tau> (-t) ; \<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr>) \<iinter> Atomic ; chaos) ; \<tau> (expr_eq b false) ; ?c\<^sup>\<infinity>"
      using conj.test_sync_post conj_commute seq_assoc by (smt (z3))

    moreover have "\<lparr>\<top> \<triangleright> (expr_eq b true \<inter> p)\<rparr> \<le> \<lparr>\<top> \<triangleright> p\<rparr>"
    proof -
      have "\<top> \<triangleright> (expr_eq b true \<inter> p) \<le> \<top> \<triangleright> p"
        by auto
      thus ?thesis
        by (rule spec_strengthen)
    qed
    hence "\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> (expr_eq b true \<inter> p)\<rparr>) \<iinter> Atomic ; chaos
            \<le> \<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos"
      using conj.sync_mono_left conj.sync_mono_right seq_mono_right by metis
    hence "(\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> (expr_eq b true \<inter> p)\<rparr>) \<iinter> Atomic ; chaos) ; ?c\<^sup>\<infinity>
            \<le> (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos) ; ?c\<^sup>\<infinity>"
      using seq_mono_left seq_mono_right by simp

    ultimately show ?thesis
      using sup.mono by auto
  qed
  ultimately have "?c\<^sup>\<infinity> \<le> (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<tau> (-t) ; \<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr>) \<iinter> Atomic ; chaos) ; \<tau> (expr_eq b false) ; ?c\<^sup>\<infinity> \<squnion>
                          (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos) ; ?c\<^sup>\<infinity>"
    by simp
  moreover have "... \<le> rely r \<iinter> (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<tau> (-t) ; \<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr>) \<iinter> Atomic ; chaos) ; \<tau> (expr_eq b false) ; idle ; \<bottom> \<squnion>
                        (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos) ; ?c\<^sup>\<infinity>"
    using nonterminating_iteration_helper_induction_2 assms by blast
  moreover have "... \<le> rely r \<iinter> \<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<bottom>) \<squnion>
                        (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos) ; ?c\<^sup>\<infinity>"
    using nonterminating_iteration_helper_induction_3 assms by simp
  moreover have "... \<le> rely r \<iinter> \<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<bottom>) \<squnion>
                        (rely r \<iinter> \<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos) ; ?c\<^sup>\<infinity>"
    using rely_remove conj_assoc order_refl seq_mono sup.mono by (smt (z3))
  ultimately have "?c\<^sup>\<infinity> \<le> rely r \<iinter> \<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<bottom>) \<squnion>
                          (rely r \<iinter> \<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos) ; ?c\<^sup>\<infinity>"
    using order_trans by blast
  moreover have "... = (rely r \<iinter> \<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos) ; ?c\<^sup>\<infinity>"
  proof -
    have "rely r \<iinter> \<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<bottom>)
            \<le> (rely r \<iinter> \<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos) ; ?c\<^sup>\<infinity>"
    proof -
      have "\<lbrace>p \<inter> b0\<rbrace> ; term ; \<bottom> \<le> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr> ; \<bottom>"
      proof -
        have "\<lbrace>p \<inter> b0\<rbrace> ; term ; \<bottom> = \<lbrace>p \<inter> b0\<rbrace> ; term ; \<bottom> ; \<lparr>\<top> \<triangleright> p\<rparr> ; \<bottom>"
          using seq_assoc by simp
        moreover have "\<lbrace>p \<inter> b0\<rbrace> ; term ; \<bottom> \<le> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr>"
          using term_magic_refines_spec seq_mono seq_assoc by simp
        ultimately show ?thesis
          using seq_mono_left by metis
      qed
      hence "rely r \<iinter> \<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<bottom>)
              \<le> rely r \<iinter> \<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr> ; \<bottom>)"
        using conj.sync_mono_right seq_mono_right by simp
      also have "... = rely r \<iinter> \<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) ; \<bottom>"
        using conj.test_sync_post seq_assoc test.hom_bot by metis
      also have "... = rely r \<iinter> \<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) ; \<bottom> \<iinter> Atomic\<^sup>\<infinity>"
        using seq_magic_atomic_infiter conj_assoc by metis
      also have "... = rely r \<iinter> \<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) ; \<bottom> \<iinter> Atomic ; chaos ; \<bottom>"
        using infiter_unfold infiter_iter_magic seq_assoc chaos_def by simp
      also have "... = rely r \<iinter> (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos) ; \<bottom>"
        using conj.test_sync_post2 local.conj_assoc test.hom_bot test_seq_idem test_seq_test by (smt (z3))
      also have "... = (rely r \<iinter> \<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos) ; \<bottom>"
        using conj.test_sync_post test.hom_bot conj_assoc by metis
      also have "... \<le> (rely r \<iinter> \<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos) ; ?c\<^sup>\<infinity>"
        using seq_mono_right by simp
      finally show ?thesis .
    qed
    thus ?thesis
      using le_iff_sup by (metis (lifting))
  qed
  ultimately have "?c\<^sup>\<infinity> \<le> (rely r \<iinter> \<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos) ; ?c\<^sup>\<infinity>"
    by simp
  thus ?thesis
    using infiter_induct by simp
qed

lemma nonterminating_iteration:
  assumes "single_reference (b::(_, 'v::has_booleans) expr) r"
  assumes "stable p r"
  assumes "stable b0 r"
  assumes "stable (expr_eq b false) r"
  assumes "refl g"
  assumes "p \<inter> expr_eq b true \<le> b0"
  assumes "p \<subseteq> expr_type b boolean"
  shows "rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; forever (\<box> (\<diamond>\<^sub>f (\<iota> t)))
          \<ge> (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<lparr>{(s, s'). ((s \<in> t) = (s' \<in> expr_eq b true)) \<and> (s' \<in> p)}\<rparr>) \<iinter> Atomic ; chaos)\<^sup>\<infinity>"
proof -
  have "rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; forever (\<box> (\<diamond>\<^sub>f (\<iota> t)))
          \<ge> rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; (\<lparr>\<top> \<triangleright> t\<rparr> ; term \<iinter> Atomic ; term)\<^sup>\<infinity>" (is "_ \<ge> ?rhs")
    using forever_always_eventually conj.sync_mono_right seq_mono_right by simp
  also have "?rhs \<ge> rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; (\<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr> ; \<lbrace>p\<rbrace> \<iinter> Atomic ; term)\<^sup>\<infinity>" (is "_ \<ge> ?rhs")
    using spec_term conj.sync_mono_right local.conj_commute refine_infiter range_restriction_spec seq_assoc seq_mono_right test_seq_assert by metis
  also have "?rhs \<ge> rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; ((\<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr> \<iinter> Atomic ; term) ; \<lbrace>p\<rbrace>)\<^sup>\<infinity>" (is "_ \<ge> ?rhs")
    using conj.sync_mono_right conj.test_sync_post_helper1 conj_idem local.conj_commute range_restriction_spec seq_assoc seq_conj_interchange by (metis (no_types))
  also have "?rhs = rely r \<iinter> guar g \<iinter> (\<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr> \<iinter> Atomic ; term)\<^sup>\<infinity>"
    using infinite_leapfrog conj.assert_distrib local.conj_commute seq_assoc by simp
  also have "... \<ge> rely r \<iinter> guar g \<iinter> (\<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr> \<iinter> term \<iinter> Atomic ; chaos)\<^sup>\<infinity>" (is "_ \<ge> ?rhs")
    using atomic_term conj_assoc by force
  also have "?rhs \<ge> rely r \<iinter> guar g \<iinter> (\<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr> \<iinter> Atomic ; chaos)\<^sup>\<infinity>" (is "_ \<ge> ?rhs")
  proof-
    have a: "\<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr> \<le> term"
      using seq_mono spec_term seq_term_term by metis

    have "\<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr> \<iinter> term = \<lbrace>p\<rbrace> ; (\<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr> \<iinter> term)"
      using conj.assert_distrib local.conj_commute seq_assoc by simp
    also have "... = \<lbrace>p\<rbrace> ; (\<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>)"
      using a conj_refines_nonaborting_eq local.conj_commute term_nonaborting by simp
    finally show ?thesis
      using seq_assoc by auto
  qed
  also have "?rhs \<ge> rely r \<iinter> guar g \<iinter> (\<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> (p \<inter> b0)\<rparr> ; \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr> \<iinter> Atomic ; chaos)\<^sup>\<infinity>" (is "_ \<ge> ?rhs")
    using spec_seq_introduce conj.sync_mono_right local.conj_commute order_refl refine_infiter seq_assoc seq_mono_right seq_term_term spec_test_restricts spec_univ test_seq_assert test_seq_refine by (metis (no_types))
  also have "?rhs \<ge> rely r \<iinter> (rely r \<iinter> guar g \<iinter> (\<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> (p \<inter> b0)\<rparr> ; \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr> \<iinter> Atomic ; chaos)\<^sup>\<infinity>)" (is "_ \<ge> ?rhs")
    using conj_assoc by simp
  also have "?rhs \<ge> rely r \<iinter> ((rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> (p \<inter> b0)\<rparr> ; \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos)\<^sup>\<infinity>" (is "_ \<ge> ?rhs")
    using infinite_distribute_conj conj_seq_distrib guar_seq_idem conj_assoc rely_seq_distrib conj.sync_mono_right by metis
  also have "?rhs \<ge> rely r \<iinter> ((rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> (p \<inter> b0)\<rparr>) ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos)\<^sup>\<infinity>" (is "_ \<ge> ?rhs")
  proof -
    have a: "\<And>c d. rely r \<iinter> guar g \<iinter> c ; d
            \<ge> (rely r \<iinter> guar g \<iinter> c) ; (rely r \<iinter> guar g \<iinter> d)"
      using rely_seq_distrib conj_seq_distrib guar_seq_idem by metis
    have "(rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> (p \<inter> b0)\<rparr> ; \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos
              \<ge> (rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> (p \<inter> b0)\<rparr>) ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos"
      using a[of "\<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> (p \<inter> b0)\<rparr>" "\<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>"] conj.sync_mono_left seq_assoc by simp
    thus ?thesis
      using refine_infiter conj.sync_mono_right by blast
  qed
  also have "?rhs \<ge> rely r \<iinter> (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos)\<^sup>\<infinity>" (is "_ \<ge> ?rhs")
  proof -
    have "rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> (p \<inter> b0)\<rparr> \<ge> \<lbrakk>b\<rbrakk>true"
      using assms inf_commute local.conj_commute rely_guar_eval by metis
    hence "(rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> (p \<inter> b0)\<rparr>) ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos
            \<ge> \<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos"
      using conj.sync_mono_left seq_mono_left by simp
    thus ?thesis
      using refine_infiter conj.sync_mono_right by simp
  qed
  also have "?rhs \<ge> (rely r \<iinter> \<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> t\<rparr> ; \<lparr>\<top> \<triangleright> p\<rparr>) \<iinter> Atomic ; chaos)\<^sup>\<infinity>" (is "_ \<ge> ?rhs")
    using infinite_distribute_conj conj_assoc rely_seq_distrib by simp
  also have "?rhs \<ge> (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<lparr>{(s, s'). ((s \<in> t) = (s' \<in> expr_eq b true)) \<and> (s' \<in> p)}\<rparr>) \<iinter> Atomic ; chaos)\<^sup>\<infinity>" (is "_ \<ge> ?c\<^sup>\<infinity>")
    using nonterminating_iteration_helper_induction assms by simp
  finally show ?thesis .
qed

definition stepped_while_statement :: "('b,'v::has_booleans) expr \<Rightarrow> 'a::refinement_lattice \<Rightarrow> 'a" ("(SWhile_do_)" 41)
  where "(SWhile b do c) \<equiv> (\<lbrakk>b\<rbrakk>true ; c \<iinter> Atomic ; chaos)\<^sup>\<omega> ; \<lbrakk>b\<rbrakk>false"

lemma conditional_loop:
  assumes "single_reference (b::(_, 'v::has_booleans) expr) r"
  assumes "stable p r"
  assumes "stable b0 r"
  assumes "stable (expr_eq b false) r"
  assumes "refl g"
  assumes "p \<inter> expr_eq b true \<subseteq> b0"
  assumes "p \<subseteq> expr_type b boolean"
  shows "rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; (\<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr> \<squnion> forever (\<box> (\<diamond>\<^sub>f (\<iota> t))))
          \<ge> (SWhile b do rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<lparr>{(s, s'). (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}\<rparr>)"
proof -
  have "rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; (\<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr> \<squnion> forever (\<box> (\<diamond>\<^sub>f (\<iota> t))))
          = rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; \<lparr>\<top> \<triangleright> (expr_eq b false \<inter> p)\<rparr> \<squnion> rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; forever (\<box> (\<diamond>\<^sub>f (\<iota> t)))"
    using conj.sync_nondet_distrib par.seq_nondet_distrib by simp
  also have "... \<ge> (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>\<top> \<triangleright> p\<rparr>))\<^sup>\<star> ; \<lbrakk>b\<rbrakk>false \<squnion>
                    (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<lparr>{(s, s'). (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}\<rparr>) \<iinter> Atomic ; chaos)\<^sup>\<infinity>" (is "_ \<ge> ?rhs")
    using terminating_iteration nonterminating_iteration assms sup.mono by blast
  also have "?rhs \<ge> (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<lparr>{(s, s'). (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}\<rparr>))\<^sup>\<star> ; \<lbrakk>b\<rbrakk>false \<squnion>
                     (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<lparr>{(s, s'). (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}\<rparr>) \<iinter> Atomic ; chaos)\<^sup>\<infinity>" (is "_ \<ge> ?rhs")
  proof -
    have "\<lparr>\<top> \<triangleright> p\<rparr> = term ; \<lparr>\<top> \<triangleright> p\<rparr>"
      using seq_term_range_restriction by simp
    also have "... \<ge> term ; \<lparr>{(s, s'). (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}\<rparr>"
    proof -
      have "\<top> \<triangleright> p \<ge> {(s, s'). (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}"
        by auto
      thus ?thesis
        using seq_mono_right spec_strengthen by simp
    qed
    finally have "\<lparr>\<top> \<triangleright> p\<rparr> \<ge> term ; \<lparr>{(s, s'). (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}\<rparr>" .
    thus ?thesis
      using conj.sync_mono_right seq_assoc seq_mono_right fiter_mono order_refl seq_mono_left sup.mono by (metis (lifting))
  qed
  also have "?rhs \<ge> (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<lparr>{(s, s'). (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}\<rparr>) \<iinter> Atomic ; chaos)\<^sup>\<star> ; \<lbrakk>b\<rbrakk>false \<squnion>
                     (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<lparr>{(s, s'). (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}\<rparr>) \<iinter> Atomic ; chaos)\<^sup>\<infinity>" (is "_ \<ge> ?rhs")
  proof -
    have "chaos \<ge> Atomic ; chaos"
      using Atomic_nonaborting chaos_seq_chaos seq_mono_left by metis
    thus ?thesis
      by (meson conj_conjoin_non_aborting fiter_mono order_refl seq_mono_left seq_mono_right sup.mono)
  qed
  also have "?rhs = (\<lbrakk>b\<rbrakk>true ; (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<lparr>{(s, s'). (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}\<rparr>) \<iinter> Atomic ; chaos)\<^sup>\<omega> ; \<lbrakk>b\<rbrakk>false"
    using par.iter_isolate by simp
  also have "... = (SWhile b do (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; term ; \<lparr>{(s, s'). (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}\<rparr>))"
    using stepped_while_statement_def[of b] by simp
  finally show ?thesis .
qed

lemma spin_lock:
  assumes "single_reference (b::(_, 'v::has_booleans) expr) r"
  assumes "stable p r"
  assumes "stable b0 r"
  assumes "stable (expr_eq b false) r"
  assumes "refl g"
  assumes "p \<inter> expr_eq b true \<subseteq> b0"
  assumes "p \<subseteq> epxr_type b boolean"
  shows "rely r \<iinter> guar g \<iinter> \<lbrace>p\<rbrace> ; (\<lparr>\<top> \<triangleright> (eval_eq b false \<inter> p)\<rparr> \<squnion> forever (\<box> (\<diamond>\<^sub>f (\<iota> t))))
           \<ge> (SWhile b do (rely r \<iinter> guar g \<iinter> \<lbrace>p \<inter> b0\<rbrace> ; \<lparr>{(s, s'). (s \<in> t) = (s' \<in> expr_eq b true) \<and> s' \<in> p}\<rparr>))"
proof -
  show ?thesis sorry
qed

end
