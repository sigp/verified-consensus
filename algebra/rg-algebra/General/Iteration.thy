section \<open>Iteration \label{S:iteration}\<close>

theory Iteration
imports
  Galois_Connections
  Sequential
begin

subsection \<open>Possibly infinite iteration\<close>

text \<open>
  Iteration of finite or infinite steps can be defined using a greatest fixed point.
\<close>


(* hide_fact (open) Random_Sequence.iter_def *)

locale finite_or_infinite_iteration = lower_galois_connections + seq_distrib (* lib
  for lib :: "'b \<Rightarrow> 'a::refinement_lattice \<Rightarrow> 'a" ("E\<^sup>C\<^sub>_ _" [999, 999] 999) *)
begin

definition
  iter :: "'a \<Rightarrow> 'a" ("_\<^sup>\<omega>" [103] 102) (* this can be entered as \sup\omega *)
where
  "c\<^sup>\<omega> \<equiv> gfp (\<lambda> x. nil \<squnion> c;x)"

lemma iter_step_mono: "mono (\<lambda> x. nil \<squnion> c;x)"
  by (meson sup_mono order_refl seq_mono_right mono_def)

text \<open>
  This fixed point definition leads to the two core iteration lemmas:
  folding and induction.
\<close>

theorem iter_unfold: "c\<^sup>\<omega> = nil \<squnion> c;c\<^sup>\<omega>"
  using iter_def iter_step_mono gfp_unfold by auto

lemma iter_induct_nil: "nil \<squnion> c;x \<ge> x \<Longrightarrow> c\<^sup>\<omega> \<ge> x"
  by (simp add: iter_def gfp_upperbound)

lemma iter0: "c\<^sup>\<omega> \<ge> nil"
  by (metis iter_unfold inf.orderI inf_sup_absorb)

lemma iter1: "c\<^sup>\<omega> \<ge> c"
  by (metis sup_ge2 iter0 iter_unfold order.trans seq_mono_right seq_nil_right)

lemma iter_seq_iter [simp]: "c\<^sup>\<omega>;c\<^sup>\<omega> = c\<^sup>\<omega>"
proof (rule antisym)
  show "c\<^sup>\<omega>;c\<^sup>\<omega> \<ge> c\<^sup>\<omega>" using iter0 seq_mono_right by fastforce
next
  have a: "nil \<squnion> c;c\<^sup>\<omega>;c\<^sup>\<omega> \<ge> nil \<squnion> c;c\<^sup>\<omega> \<squnion> c;c\<^sup>\<omega>;c\<^sup>\<omega>"
    by (metis sup_least sup_ge2 sup_mono iter0 order_refl seq_distrib_left.seq_mono_right seq_distrib_left_axioms seq_nil_right) 
  then have b: "\<dots> = c\<^sup>\<omega> \<squnion> c;c\<^sup>\<omega>;c\<^sup>\<omega>" by (metis iter_unfold dual_order.antisym iter0 sup.cobounded2 sup.left_idem sup_mono) 
  then have c: "\<dots> = (nil \<squnion> c;c\<^sup>\<omega>);c\<^sup>\<omega>" by (simp add: nondet_seq_distrib)
  thus "c\<^sup>\<omega> \<ge> c\<^sup>\<omega>;c\<^sup>\<omega>" using a iter_induct_nil iter_unfold seq_assoc by auto 
qed

lemma iter_mono: "c \<ge> d \<Longrightarrow> c\<^sup>\<omega> \<ge> d\<^sup>\<omega>"
proof -
  assume "c \<ge> d"
  then have "nil \<squnion> c;d\<^sup>\<omega> \<ge> d;d\<^sup>\<omega>" by (metis sup.absorb_iff2 sup_left_commute nondet_seq_distrib)
  then have "nil \<squnion> c;d\<^sup>\<omega> \<ge> d\<^sup>\<omega>" by (metis sup.bounded_iff inf_sup_ord(3) iter_unfold) 
  thus ?thesis by (simp add: iter_induct_nil)
qed

lemma iter_abort: "\<top> = nil\<^sup>\<omega>"
  by (simp add: antisym iter_induct_nil)

lemma nil_iter: "\<bottom>\<^sup>\<omega> = nil"
  by (metis (no_types) sup_bot.right_neutral iter_unfold seq_magic_left)
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



subsection \<open>Finite iteration\<close>

text \<open>
  Iteration of a finite number of steps (Kleene star) is defined
  using the least fixed point.
\<close>

locale finite_iteration = upper_galois_connections + seq_distrib (* lib
  for lib :: "'b \<Rightarrow> 'a::refinement_lattice \<Rightarrow> 'a" ("E\<^sup>C\<^sub>_ _" [999, 999] 999) *)
begin

definition
  fiter :: "'a \<Rightarrow> 'a" ("_\<^sup>\<star>" [101] 100)
where
  "c\<^sup>\<star> \<equiv> lfp (\<lambda> x. nil \<squnion> c;x)"


lemma fin_iter_step_mono: "mono (\<lambda> x. nil \<squnion> c;x)"
  by (meson sup_mono order_refl seq_mono_right mono_def)

text \<open>
  This definition leads to the two core iteration lemmas:
  folding and induction.
\<close>

lemma fiter_unfold: "c\<^sup>\<star> = nil \<squnion> c;c\<^sup>\<star>"
  using fiter_def lfp_unfold fin_iter_step_mono by auto

lemma fiter_induct_nil: "x \<ge> nil \<squnion> c;x \<Longrightarrow> x \<ge> c\<^sup>\<star>"
  by (simp add: fiter_def lfp_lowerbound)

lemma fiter0: "c\<^sup>\<star> \<ge> nil"
  by (metis fiter_unfold sup.cobounded1)

lemma fiter1: "c\<^sup>\<star> \<ge> c"
  by (metis fiter0 fiter_unfold sup_ge2 order.trans seq_mono_right seq_nil_right)

lemma fiter_induct_eq: "c\<^sup>\<star>;d = lfp (\<lambda> x. c;x \<squnion> d)"
proof -
  define F where "F = (\<lambda> x. x;d)"
  define G where "G = (\<lambda> x. nil \<squnion> c;x)"
  define H where "H = (\<lambda> x. c;x \<squnion> d)"

  have FG: "F \<circ> G = (\<lambda> x. c;x;d \<squnion> d)" by (simp add: F_def G_def comp_def sup_commute nondet_seq_distrib)
  have HF: "H \<circ> F = (\<lambda> x. c;x;d \<squnion> d)" by (metis comp_def seq_assoc H_def F_def) 

  have adjoint: "dist_over_nondet F" using Nondet_seq_distrib F_def by simp
  have monoH: "mono H"
    by (metis H_def nondet_mono_left monoI seq_distrib_left.seq_mono_right seq_distrib_left_axioms)
  have monoG: "mono G" by (metis G_def nondet_mono_right mono_def seq_mono_right) 
  have "\<forall> x. ((F \<circ> G) x = (H \<circ> F) x)" using FG HF by simp
  then have "F (lfp G) = lfp H" using adjoint monoG monoH fusion_lfp_eq by blast 
  then have "(lfp (\<lambda> x. nil \<squnion> c;x));d = lfp (\<lambda> x. c;x \<squnion> d)" using F_def G_def H_def sup_commute by simp
  thus ?thesis by (metis fiter_def) 
qed

theorem fiter_induct: "x \<ge> d \<squnion> c;x \<Longrightarrow> x \<ge> c\<^sup>\<star>;d"
proof -
  assume "x \<ge> d \<squnion> c;x"
  then have "x \<ge> c;x \<squnion> d" using sup_commute by simp
  then have "x \<ge> lfp (\<lambda> x. c;x \<squnion> d)" by (simp add: lfp_lowerbound)
  thus ?thesis by (metis (full_types) fiter_induct_eq)
qed

lemma fiter_seq_fiter [simp]: "c\<^sup>\<star>;c\<^sup>\<star> = c\<^sup>\<star>"
proof -
  have lr: "c\<^sup>\<star>;c\<^sup>\<star> \<ge> c\<^sup>\<star>" using fiter0 seq_mono_right seq_nil_right by fastforce 
  have rl: "c\<^sup>\<star> \<ge> c\<^sup>\<star>;c\<^sup>\<star>" by (metis fiter_induct fiter_unfold sup.right_idem order_refl) 
  thus ?thesis by (simp add: antisym lr) 
qed

lemma fiter_fiter [simp]: "(c\<^sup>\<star>)\<^sup>\<star> = c\<^sup>\<star>"
  by (metis dual_order.refl fiter0 fiter1 fiter_seq_fiter fiter_induct sup.commute sup_absorb1 seq_nil_right)

lemma fiter_mono: "c \<ge> d \<Longrightarrow> c\<^sup>\<star> \<ge> d\<^sup>\<star>"
proof -
  assume "c \<ge> d"
  then have "c\<^sup>\<star> \<ge> nil \<squnion> d;c\<^sup>\<star>" by (metis fiter0 fiter1 fiter_seq_fiter sup.bounded_iff refine_trans seq_mono_left)
  thus ?thesis  by (metis seq_nil_right fiter_induct)
qed

end



subsection \<open>Infinite iteration\<close>

text \<open>
  Iteration of infinite number of steps can be defined
  using a greatest fixed point.
\<close>

locale infinite_iteration = upper_galois_connections + seq_distrib (* lib
  for lib :: "'b \<Rightarrow> 'a::refinement_lattice \<Rightarrow> 'a" ("E\<^sup>C\<^sub>_ _" [999, 999] 999) *)
begin

definition
  infiter :: "'a  \<Rightarrow> 'a" ("_\<^sup>\<infinity>" [105] 106)
where
  "c\<^sup>\<infinity> \<equiv> gfp (\<lambda> x. c;x)"

lemma infiter_step_mono: "mono (\<lambda> x. c;x)"
  by (meson inf_mono order_refl seq_mono_right mono_def)

text \<open>
  This definition leads to the two core iteration lemmas:
  folding and induction.
\<close>

theorem infiter_unfold: "c\<^sup>\<infinity> = c;c\<^sup>\<infinity>"
  using infiter_def infiter_step_mono gfp_unfold by auto

lemma infiter_induct: "c;x \<ge> x \<Longrightarrow> c\<^sup>\<infinity> \<ge> x"
  by (simp add: infiter_def gfp_upperbound)

theorem infiter_unfold_any: "c\<^sup>\<infinity> = (c \<^sup>;^ i) ; c\<^sup>\<infinity>"
proof (induct i)
  case 0
  thus ?case by simp
next
  case (Suc i)
  thus ?case using infiter_unfold seq_assoc seq_power_Suc by auto
qed

lemma infiter_annil: "c\<^sup>\<infinity>;x = c\<^sup>\<infinity>"
proof -
  have "\<forall>a. (\<top>::'a) \<ge> a"
    by auto
  thus ?thesis
    by (metis (no_types) eq_iff sup.cobounded2 infiter_induct infiter_unfold inf_sup_ord(3) seq_assoc seq_abort seq_nondet_distrib_weak seq_nil_right)
qed

end



subsection \<open>Combined iteration\<close>

text \<open>
  The three different iteration operators can be combined to show that 
  finite iteration refines finite-or-infinite iteration.
\<close>

locale iteration = finite_or_infinite_iteration + finite_iteration + 
                   infinite_iteration (* +
   assumes finite_liberation: "E\<^sup>C\<^sub>x ((E\<^sup>C\<^sub>x c) \<^sup>;^ (i-1)) = (E\<^sup>C\<^sub>x c) \<^sup>;^ i" *)
begin

lemma iter_ref_fiter: "c\<^sup>\<omega> \<ge> c\<^sup>\<star>"
  by (metis seq_nil_right order.refl iter_unfold fiter_induct)

lemma iter_fiter [simp]: "(c\<^sup>\<omega>)\<^sup>\<star> = c\<^sup>\<omega>"
proof (rule antisym)
  show "(c\<^sup>\<omega>)\<^sup>\<star> \<ge> c\<^sup>\<omega>" by (metis fiter1)
next
  show "c\<^sup>\<omega> \<ge> (c\<^sup>\<omega>)\<^sup>\<star>" by (metis fiter_induct iter_seq_iter iter_unfold seq_nil_right sup.cobounded2 sup.orderE sup_commute)
qed

lemma infiter_iter_magic: "c\<^sup>\<infinity> = c\<^sup>\<omega> ; \<bottom>" 
proof -
  have lr: "c\<^sup>\<infinity> \<ge> c\<^sup>\<omega> ; \<bottom>"
  proof -
    have "c ; (c\<^sup>\<omega> ; \<bottom>) = nil ; \<bottom> \<squnion> c ; c\<^sup>\<omega> ; \<bottom>"
      using semigroup.assoc seq.semigroup_axioms by fastforce
    then show ?thesis
      by (metis (no_types) eq_refl finite_or_infinite_iteration.iter_unfold 
         finite_or_infinite_iteration_axioms infiter_induct 
         seq_distrib_right.nondet_seq_distrib seq_distrib_right_axioms)
  qed 
  have rl: "c\<^sup>\<omega> ; \<bottom> \<ge> c\<^sup>\<infinity>"
    by (metis sup_ge2 infiter_annil infiter_unfold iter_induct_nil seq_mono_left) 
  thus ?thesis using antisym_conv lr by blast 
qed

lemma infiter_fiter_magic:
  shows "c\<^sup>\<infinity> \<ge> c\<^sup>\<star> ; \<bottom>"
  by (metis eq_iff fiter_induct sup_bot_left infiter_unfold)

lemma iter_ref_infiter: "c\<^sup>\<omega> \<ge> c\<^sup>\<infinity>"
  using infiter_unfold iter_induct_nil by auto

lemma fiter_seq_iter: "c\<^sup>\<star> ; c\<^sup>\<omega> = c\<^sup>\<omega>"
proof -
  have lr: "c\<^sup>\<star> ; c\<^sup>\<omega> \<ge> c\<^sup>\<omega>" using fiter0 seq_mono_left by fastforce
  have rl: "c\<^sup>\<omega> \<ge> c\<^sup>\<star> ; c\<^sup>\<omega>" by (metis iter_seq_iter iter_ref_fiter seq_mono_left)
  thus ?thesis by (simp add: antisym lr) 
qed

(* liberation over iteration *)

(*

text_raw \<open>\DefineSnippet{iterationfixed}{%\<close>
lemma localised_fixed_iteration: "E\<^sup>C\<^sub>x ((E\<^sup>C\<^sub>x c)\<^sup>;^ i) = (E\<^sup>C\<^sub>x c)\<^sup>;^ i" (* Lemma 1 *)
  by (metis finite_liberation localising_first seq_first seq_nil_left seq_right)
text_raw \<open>}%EndSnippet\<close>

lemma localited_finite_iteration: "E\<^sup>C\<^sub>x ((E\<^sup>C\<^sub>x c)\<^sup>\<star>) = (E\<^sup>C\<^sub>x c)\<^sup>\<star>" (* Lemma 2 *)
  by (metis diff_Suc_1 finite_liberation iter_fiter nil_iter seq_nil_right 
      seq_power_0 seq_power_Suc)

lemma localised_omega_iteration: "E\<^sup>C\<^sub>x ((E\<^sup>C\<^sub>x c)\<^sup>\<omega>) = (E\<^sup>C\<^sub>x c)\<^sup>\<omega>" (* Lemma 3 *)
  by (metis abort_remove top.extremum diff_Suc_1 eq_iff finite_liberation iter0 
      last seq_nil_right seq_power_0 seq_power_Suc)

lemma localised_inf_iteration: "E\<^sup>C\<^sub>x ((E\<^sup>C\<^sub>x c)\<^sup>\<infinity>) = (E\<^sup>C\<^sub>x c)\<^sup>\<infinity>"
  by (metis antisym infiter_induct infiter_unfold lib_lattice.remove_lib 
      liberation_stages.axioms(1) liberation_stages_axioms localising_last remove_lib seq_left)

lemma localised_atomic_fixed_iteration: "((E\<^sup>C\<^sub>x a) = (L\<^sup>C\<^sub>x a)) \<Longrightarrow> ((E\<^sup>C\<^sub>x (a\<^sup>;^i)) = ((E\<^sup>C\<^sub>x a)\<^sup>;^i))" (* Lemma 4 *)
  by (metis diff_Suc_1 finite_liberation seq_nil_right seq_power_0 seq_power_Suc)

lemma localised_atomic_finite_iteration: "((E\<^sup>C\<^sub>x a) = (L\<^sup>C\<^sub>x a)) \<Longrightarrow> ((E\<^sup>C\<^sub>x (a\<^sup>\<star>)) = ((E\<^sup>C\<^sub>x a)\<^sup>\<star>))" (* Lemma 5 *)
proof -
  assume "E\<^sup>C\<^sub>x a = L\<^sup>C\<^sub>x a"
  have "\<And>a. a = nil"
    by (metis diff_Suc_1 finite_liberation iter_abort localised_fixed_iteration localised_omega_iteration 
        seq_abort seq_nil_left seq_power_0 seq_power_Suc)
  then show ?thesis
    by metis
qed

lemma localised_atomic_omega_iteration: "((E\<^sup>C\<^sub>x a) = (L\<^sup>C\<^sub>x a)) \<Longrightarrow> ((E\<^sup>C\<^sub>x (a\<^sup>\<omega>)) = ((E\<^sup>C\<^sub>x a)\<^sup>\<omega>))" (* Lemma 6 *)
  by (metis diff_Suc_1 finite_liberation localised_omega_iteration seq_nil_right seq_power_0 seq_power_Suc)

lemma localised_atomic_infinite_iteration: "((E\<^sup>C\<^sub>x a) = (L\<^sup>C\<^sub>x a)) \<Longrightarrow> ((E\<^sup>C\<^sub>x (a\<^sup>\<infinity>)) = ((E\<^sup>C\<^sub>x a)\<^sup>\<infinity>))"
  by (metis (full_types) infiter_iter_magic lib_lattice.magic_remove liberation_stages.axioms(1) 
      liberation_stages_axioms localised_atomic_omega_iteration seq_right)

*)

    
end  

end

