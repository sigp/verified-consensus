section \<open>Concurrent Refinement Algebra \label{S:CRA}\<close>

text \<open>
  This theory brings together the three main operators:
  sequential composition,
  parallel composition and
  conjunction,
  as well as the iteration operators. 
\<close>

theory CRA
imports 
  Sequential
  Conjunction
  Parallel
begin


locale seq_par = sequential + parallel +
  assumes nil_par_nil_weak: "nil \<parallel> nil \<ge> nil" 
  and skip_ref_nil: "skip \<ge> nil"           (* 41 *)
  and skip_seq_skip_weak: "skip \<ge> skip;skip"    (* 40 *)
  and seq_par_interchange: "(c0;d0) \<parallel> (c1;d1) \<ge> (c0 \<parallel> c1);(d0 \<parallel> d1)"

locale sequential_parallel = seq_par + seq_distrib + par_distrib begin

text \<open>
  Locale @{locale "sequential_parallel"} brings together the sequential and parallel
  operators and relates their identities.
\<close>

lemma nil_par_nil: "nil \<parallel> nil = nil" using nil_par_nil_weak skip_ref_nil par_skip
  by (metis sup.absorb_iff2 sup.orderE sync_nondet_distrib)

lemma skip_seq_skip [simp]: "skip;skip = skip"
by (metis antisym seq_mono_right seq_nil_right skip_seq_skip_weak skip_ref_nil)

end


locale conjunction_parallel = conj_distrib + par_distrib + 
  assumes chaos_par_magic: "\<bottom> \<ge> chaos \<parallel> \<bottom>"
  assumes chaos_par_chaos_nonaborting: "chaos \<ge> chaos \<parallel> chaos"     (* 47 *)
  assumes par_conj_interchange: "(c\<^sub>0 \<parallel> c\<^sub>1) \<iinter> (d\<^sub>0 \<parallel> d\<^sub>1) \<ge> (c\<^sub>0 \<iinter> d\<^sub>0) \<parallel> (c\<^sub>1 \<iinter> d\<^sub>1)" (* 50 *)
begin
text \<open>
  Locale @{locale "conjunction_parallel"} brings together the weak conjunction and
  parallel operators and relates their identities.
  It also introduces the interchange axiom for conjunction and parallel.
\<close>

lemma skip_nonaborting: "chaos \<ge> skip"  (* 46 *)
proof -
  have "chaos = (chaos \<parallel> skip) \<iinter> (skip \<parallel> chaos)" by simp
  then have "\<dots> \<ge> (chaos \<iinter> skip) \<parallel> (skip \<iinter> chaos)" using par_conj_interchange by blast 
  thus ?thesis by auto
qed

lemma chaos_par_chaos: "chaos \<parallel> chaos = chaos"
  by (metis antisym chaos_par_chaos_nonaborting skip_nonaborting order_refl sync_mono par_skip)

lemma nonaborting_par_magic: "chaos \<ge> c \<Longrightarrow> c \<parallel> \<bottom> = \<bottom>"
  by (metis chaos_par_magic sync_mono bot.extremum_uniqueI)

lemma skip_conj_magic: "skip \<iinter> \<bottom> = \<bottom>"
by (simp add: skip_nonaborting conj_magic_nonaborting)

lemma conj_par_distrib: "c \<ge> c \<parallel> c \<Longrightarrow> c \<iinter> (d\<^sub>0 \<parallel> d\<^sub>1) \<ge> (c \<iinter> d\<^sub>0) \<parallel> (c \<iinter> d\<^sub>1)"
proof -
  assume "c \<ge> c \<parallel> c"
  then have "c \<iinter> (d\<^sub>0 \<parallel> d\<^sub>1) \<ge> (c \<parallel> c) \<iinter> (d\<^sub>0 \<parallel> d\<^sub>1)" 
    using abstract_sync.sync_mono_left conj_distrib.axioms(2) conj_distrib_axioms by blast 
  thus ?thesis by (metis par_conj_interchange refine_trans) 
qed

lemma conj_par_absorb: 
  shows "c \<ge> c \<parallel> c \<Longrightarrow> c \<iinter> (c \<iinter> d_0 \<parallel> c \<iinter> d_1) \<ge> c \<iinter> d_0 \<parallel> c \<iinter> d_1"
  by (metis conj_par_distrib conj_idem conj_assoc)

end


locale conjunction_sequential = conj_distrib + seq_distrib + (* iteration + *)
  assumes chaos_seq_chaos_nonaborting: "chaos \<ge> chaos;chaos"
  assumes seq_conj_interchange: "(c\<^sub>0;c\<^sub>1) \<iinter> (d\<^sub>0;d\<^sub>1) \<ge> (c\<^sub>0 \<iinter> d\<^sub>0);(c\<^sub>1 \<iinter> d\<^sub>1)"  (* 51 *)
begin
text \<open>
  Locale @{locale "conjunction_sequential"} brings together the weak conjunction and
  sequential operators.
  It also introduces the interchange axiom for conjunction and sequential.
\<close>

lemma chaos_ref_nil: "chaos \<ge> nil"
  by (metis conj_chaos local.conj_commute seq_nil_left seq_nil_right
       seq_conj_interchange)

lemma chaos_seq_chaos: "chaos;chaos = chaos" 
proof (rule antisym)
  show "chaos;chaos \<ge> chaos" using chaos_ref_nil
    using seq_mono_left seq_nil_left by fastforce 
next
  show "chaos \<ge> chaos;chaos" by (simp add: chaos_seq_chaos_nonaborting) 
qed
  
lemma seq_abort_conj: "c;\<top> \<iinter> d \<ge> (c \<iinter> d);\<top>"
   by (metis (no_types) conj_abort_left seq_nil_right seq_conj_interchange) 

lemma conj_seq_abort_right [simp]: "c;\<top> \<iinter> c =  c;\<top>"
proof (rule antisym)
  show lr: "c;\<top> \<iinter> c \<ge>  c;\<top>" by (metis seq_abort_conj conj_idem) 
next
  show rl: "c;\<top> \<ge> c;\<top> \<iinter> c" 
    by (metis conj_idem sync_mono_right seq_abort_right)
qed

lemma conj_seq_distrib: "c \<ge> c;c \<Longrightarrow> c \<iinter> (d\<^sub>0 ; d\<^sub>1) \<ge> (c \<iinter> d\<^sub>0);(c \<iinter> d\<^sub>1)"
proof -
  assume "c \<ge> c;c"
  then have "c \<iinter> (d\<^sub>0;d\<^sub>1) \<ge> (c;c) \<iinter> (d\<^sub>0;d\<^sub>1)" by (metis sync_mono order.refl) 
  thus ?thesis by (metis seq_conj_interchange refine_trans) 
qed

(*
lemma iter_conj_distrib:
  assumes nil: "c \<ge> nil"
    and repeat: "c \<ge> c ; c"
  shows "c \<iinter> d\<^sup>\<omega> \<ge> (c \<iinter> d)\<^sup>\<omega>"
proof (unfold iter_def)
  def F \<equiv> "(\<lambda> x. c \<iinter> x)"
  def G \<equiv> "(\<lambda> x. nil \<sqinter> d;x)"
  def H \<equiv> "(\<lambda> x. nil \<sqinter> ((c \<iinter> d);x))"

  have FG: "F \<circ> G = (\<lambda> x. c \<iinter> (nil \<sqinter> d;x))"  by (metis comp_def F_def G_def) 
  have HF: "H \<circ> F = (\<lambda> x. (nil \<sqinter> (c \<iinter> d);(c \<iinter> x)))" by (metis comp_def H_def F_def) 

  have "F (lfp G) \<ge> lfp H"
  proof (rule fusion_lfp_leq)
    show "mono H" by (simp add: H_def iter_step_mono)
  next
    show "dist_over_sup F" by (simp add: F_def conj_Sup_distrib)
  next
    fix x
    have "c \<iinter> (nil \<sqinter> d;x) = (c \<iinter> nil) \<sqinter> (c \<iinter> d;x)" by (metis inf_conj_distrib conj_commute)
    also have "... \<ge> nil \<sqinter> (c \<iinter> d;x)" by (metis conj_to_sup inf_mono_left le_iff_sup nil)
    also have "... \<ge> nil \<sqinter> (c;c \<iinter> d;x)" by (metis inf_conj_distrib inf.absorb_iff2 inf_mono_right repeat)
    also have "... \<ge> nil \<sqinter> (c \<iinter> d);(c \<iinter> x)" by (meson inf_mono_right seq_conj_interchange)
    finally show "(F \<circ> G) x \<ge> (H \<circ> F) x" by (simp add: FG HF)
  qed

  then show "c \<iinter> lfp(\<lambda>x. nil \<sqinter> d ; x) \<ge> lfp (\<lambda>x. nil \<sqinter> (c \<iinter> d) ; x)" using F_def G_def H_def by simp
qed

lemma iter_conj_conj_distrib_left: "c\<^sup>\<omega> \<iinter> d\<^sup>\<omega> \<ge> (c\<^sup>\<omega> \<iinter> d)\<^sup>\<omega>"
  by (simp add: iter0 iter_conj_distrib)

lemma iter_conj_par_distrib: "c\<^sup>\<omega> \<iinter> d\<^sup>\<omega> \<ge> (c \<iinter> d)\<^sup>\<omega>"
proof -
  have a: "c\<^sup>\<omega> \<ge> c" by (metis iter1)
  have b: "c\<^sup>\<omega> \<iinter> d\<^sup>\<omega> \<ge> (c\<^sup>\<omega> \<iinter> d)\<^sup>\<omega>" by (metis iter_conj_conj_distrib_left)
  have "c\<^sup>\<omega> \<iinter> d \<ge> c \<iinter> d" by (metis a conj_mono order.refl) 
  thus ?thesis using a b by (metis refine_trans iter_mono) 
qed
*)

end


locale cra = sequential_parallel + conjunction_parallel + conjunction_sequential
text \<open>
  Locale @{locale "cra"} brings together sequential, parallel and weak conjunction.
\<close>

end
