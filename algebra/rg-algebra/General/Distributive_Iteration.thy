section \<open>Iteration for distributive models \label{S:distributive-iteration}\<close>

theory Distributive_Iteration
imports
  Distributive_Sequential
  Iteration
  Nondet_Nat
begin

text \<open>
  Sequential left-distribution over non-deterministic choice 
  is only supported by some models. 
  The relational model is one such example, as is the rely/guarantee algebra.
\<close>

locale iteration_finite_distrib = seq_nondet_distrib + iteration
begin                                                     

lemma iter_isolation: "c\<^sup>\<omega> = c\<^sup>\<star> \<squnion> c\<^sup>\<infinity>"
proof -
  define F where "F = (\<lambda> x. c\<^sup>\<star> \<squnion> x)"
  define G where "G = (\<lambda> x. c;x)"
  define H where "H = (\<lambda> x. nil \<squnion> c;x)"

  have FG: "F \<circ> G = (\<lambda> x. c\<^sup>\<star> \<squnion> c;x)" using F_def G_def by auto
  have HF: "H \<circ> F = (\<lambda> x. nil \<squnion> c;(c\<^sup>\<star> \<squnion> x))" using F_def H_def by auto

  have adjoint: "dist_over_inf F" by (simp add: F_def sup_Inf)
  have monoH: "mono H" by (metis H_def sup_mono monoI order_refl seq_mono_right)
  have monoG: "mono G" by (metis G_def sup.absorb_iff2 monoI seq_nondet_distrib)

  have "\<forall> x. ((F \<circ> G) x = (H \<circ> F) x)" using FG HF 
    by (metis fiter_unfold inf_sup_aci(6) seq_nondet_distrib)
  then have "F (gfp G) = gfp H" using adjoint monoH monoG fusion_gfp_eq by blast
  then have "c\<^sup>\<star> \<squnion> gfp (\<lambda> x. c;x) = gfp (\<lambda> x. nil \<squnion> c;x)"
     using F_def G_def H_def by blast
  thus ?thesis by (simp add: infiter_def iter_def)
qed

lemma iter_induct_isolate: "c\<^sup>\<star>;d \<squnion> c\<^sup>\<infinity> = gfp (\<lambda> x. d \<squnion> c;x)"
proof - 
  define F where "F = (\<lambda> x. c\<^sup>\<star>;d \<squnion> x)"
  define G where "G = (\<lambda> x. c;x)"
  define H where "H = (\<lambda> x. d \<squnion> c;x)"

  have FG: "F \<circ> G = (\<lambda> x. c\<^sup>\<star>;d \<squnion> c;x)" using F_def G_def by auto
  have HF: "H \<circ> F = (\<lambda> x. d \<squnion> c;c\<^sup>\<star>;d \<squnion> c;x)" using F_def H_def seq_nondet_distrib_weak
    by (metis comp_apply sup.commute sup.left_commute seq_assoc seq_nondet_distrib)
  have unroll: "c\<^sup>\<star>;d = (nil \<squnion> c;c\<^sup>\<star>);d" using fiter_unfold by auto
  have distribute: "c\<^sup>\<star>;d = d \<squnion> c;c\<^sup>\<star>;d" by (simp add: unroll nondet_seq_distrib)
  have FGx: "\<And>x. (F \<circ> G) x = d \<squnion> c;c\<^sup>\<star>;d \<squnion> c;x" using FG distribute by simp

  have adjoint: "dist_over_inf F" by (simp add: F_def sup_Inf)
  have monoH: "mono H" by (metis H_def sup_mono monoI order_refl seq_mono_right)
  have monoG: "mono G" by (metis G_def sup.absorb_iff2 monoI seq_nondet_distrib)

  have "\<forall> x. ((F \<circ> G) x = (H \<circ> F) x)" using FGx HF by (simp add: FG distribute)
  then have "F (gfp G) = gfp H" using adjoint monoH monoG fusion_gfp_eq by blast
  then have "c\<^sup>\<star>;d \<squnion> gfp (\<lambda> x. c;x) = gfp (\<lambda> x. d \<squnion> c;x)"
     using F_def G_def H_def by blast
  thus ?thesis by (simp add: infiter_def)
qed 

lemma iter_induct_eq: "c\<^sup>\<omega>;d = gfp (\<lambda> x. d \<squnion> c;x)"
proof -
  have "c\<^sup>\<omega>;d = c\<^sup>\<star>;d \<squnion> c\<^sup>\<infinity>;d" by (simp add: iter_isolation nondet_seq_distrib)
  then have "c\<^sup>\<star>;d \<squnion> c\<^sup>\<infinity>;d = c\<^sup>\<star>;d \<squnion> c\<^sup>\<infinity>" by (simp add: infiter_annil)
  then have "c\<^sup>\<star>;d \<squnion> c\<^sup>\<infinity> = gfp (\<lambda> x. d \<squnion> c;x)" by (simp add: iter_induct_isolate)
  thus ?thesis 
    by (simp add: \<open>c\<^sup>\<omega> ; d = c\<^sup>\<star> ; d \<squnion> c\<^sup>\<infinity> ; d\<close> \<open>c\<^sup>\<star> ; d \<squnion> c\<^sup>\<infinity> ; d = c\<^sup>\<star> ; d \<squnion> c\<^sup>\<infinity>\<close>)
qed

lemma iter_induct: "d \<squnion> c;x \<ge> x \<Longrightarrow> c\<^sup>\<omega>;d \<ge> x"
  by (simp add: iter_induct_eq gfp_upperbound)

lemma iter_isolate: "c\<^sup>\<star>;d \<squnion> c\<^sup>\<infinity> = c\<^sup>\<omega>;d"
  by (simp add: iter_induct_eq iter_induct_isolate)

lemma iter_isolate2: "c;c\<^sup>\<star>;d \<squnion> c\<^sup>\<infinity> = c;c\<^sup>\<omega>;d"
  by (metis infiter_unfold iter_isolate seq_assoc seq_nondet_distrib)

  
lemma iter_leapfrog_var: "(c;d)\<^sup>\<omega>;c \<ge> c;(d;c)\<^sup>\<omega>"
proof -
  have "c \<squnion> c;d;c;(d;c)\<^sup>\<omega> \<ge> c;(d;c)\<^sup>\<omega>"
    by (metis iter_unfold order_refl seq_assoc seq_nondet_distrib seq_nil_right)
  thus ?thesis using iter_induct_eq by (metis iter_induct seq_assoc) 
qed

lemma iter_leapfrog: "c;(d;c)\<^sup>\<omega> = (c;d)\<^sup>\<omega>;c"
proof (rule antisym)
  show "(c;d)\<^sup>\<omega>;c \<ge> c;(d;c)\<^sup>\<omega>" by (metis iter_leapfrog_var)
next
  have "(d;c)\<^sup>\<omega> \<ge> ((d;c)\<^sup>\<omega>;d);c \<squnion> nil" by (metis sup.bounded_iff order.refl seq_assoc seq_mono iter_unfold iter1 iter_seq_iter) 
  then have "(d;c)\<^sup>\<omega> \<ge> (d;(c;d)\<^sup>\<omega>);c \<squnion> nil" by (metis sup.absorb_iff2 sup.boundedE sup_assoc iter_leapfrog_var nondet_seq_distrib)
  then have "c;(d;c)\<^sup>\<omega> \<ge> c;d;(c;d)\<^sup>\<omega>;c \<squnion> nil;c" using sup.bounded_iff seq_assoc seq_mono_right seq_nil_left seq_nil_right by fastforce
  thus "c;(d;c)\<^sup>\<omega> \<ge> (c;d)\<^sup>\<omega>;c" by (metis sup_commute nondet_seq_distrib iter_unfold) 
qed

lemma fiter_leapfrog: "c;(d;c)\<^sup>\<star> = (c;d)\<^sup>\<star>;c"
proof -
  have lr: "c;(d;c)\<^sup>\<star> \<ge> (c;d)\<^sup>\<star>;c"
  proof -
    have "(d ; c)\<^sup>\<star> = nil \<squnion> d ; c ; (d ; c)\<^sup>\<star>"
      by (meson finite_iteration.fiter_unfold finite_iteration_axioms)
    then show ?thesis
      by (metis fiter_induct seq_assoc seq_distrib_left.seq_nondet_distrib_weak 
          seq_distrib_left_axioms seq_nil_right)
  qed
  have rl: "(c;d)\<^sup>\<star>;c \<ge> c;(d;c)\<^sup>\<star>" 
  proof -
    have a1: "(c;d)\<^sup>\<star>;c = c \<squnion> c;d;(c;d)\<^sup>\<star>;c"
       by (metis finite_iteration.fiter_unfold finite_iteration_axioms 
           nondet_seq_distrib seq_nil_left)  
    have a2: "(c;d)\<^sup>\<star>;c \<ge> c;(d;c)\<^sup>\<star> \<longleftrightarrow> c \<squnion> c;d;(c;d)\<^sup>\<star>;c \<ge> c;(d;c)\<^sup>\<star>" by (simp add: a1)  
    then have a3: "... \<longleftrightarrow> c;( nil \<squnion> d;(c;d)\<^sup>\<star>;c) \<ge> c;(d;c)\<^sup>\<star>"
       by (metis a1 eq_iff fiter_unfold lr seq_assoc seq_nondet_distrib seq_nil_right)  
    have a4: "(nil \<squnion> d;(c;d)\<^sup>\<star>;c) \<ge> (d;c)\<^sup>\<star> \<Longrightarrow> c;( nil \<squnion> d;(c;d)\<^sup>\<star>;c) \<ge> c;(d;c)\<^sup>\<star>"
       using seq_mono_right by blast
    have a5: "(nil \<squnion> d;(c;d)\<^sup>\<star>;c) \<ge> (d;c)\<^sup>\<star>"
      proof -
        have f1: "d ; (c ; d)\<^sup>\<star> ; c \<squnion> nil = d ; ((c ; d)\<^sup>\<star> ; c) \<squnion> nil \<squnion> nil"
           by (simp add: seq_assoc)
        have "d ; c ; (d ; (c ; d)\<^sup>\<star> ; c \<squnion> nil) = d ; ((c ; d)\<^sup>\<star> ; c)"
          by (metis a1 inf_sup_aci(5) seq_assoc seq_nil_right seq_nondet_distrib)
        then show ?thesis
           using f1 by (metis (no_types) finite_iteration.fiter_induct finite_iteration_axioms 
                           sup.cobounded1 inf_sup_aci(5) seq_nil_right)
     qed
   thus ?thesis using a2 a3 a4 by blast 
  qed
  thus ?thesis by (simp add: eq_iff lr)
qed


lemma iter_decomp: "(c \<squnion> d)\<^sup>\<omega> = c\<^sup>\<omega>;(d;c\<^sup>\<omega>)\<^sup>\<omega>"
proof (rule antisym)
  have      "c;c\<^sup>\<omega>;(d;c\<^sup>\<omega>)\<^sup>\<omega> \<squnion> (d;c\<^sup>\<omega>)\<^sup>\<omega> \<ge> c\<^sup>\<omega>;(d;c\<^sup>\<omega>)\<^sup>\<omega>" by (metis sup_commute order.refl nondet_seq_distrib seq_nil_left iter_unfold)
  thus "(c \<squnion> d)\<^sup>\<omega> \<ge> c\<^sup>\<omega>;(d;c\<^sup>\<omega>)\<^sup>\<omega>" by (metis sup.left_commute iter_induct_nil iter_unfold seq_assoc nondet_seq_distrib)
next
  have "(c;(c \<squnion> d)\<^sup>\<omega> \<squnion> d;(c \<squnion> d)\<^sup>\<omega>) \<squnion> nil \<ge> (c \<squnion> d)\<^sup>\<omega>" by (metis sup_commute order.refl nondet_seq_distrib iter_unfold) 
  then have a: "c\<^sup>\<omega>;(d;(c \<squnion> d)\<^sup>\<omega> \<squnion> nil) \<ge> (c \<squnion> d)\<^sup>\<omega>" 
  proof -
    have "nil \<squnion> d;(c \<squnion> d)\<^sup>\<omega> \<squnion> c;(c \<squnion> d)\<^sup>\<omega> \<ge> (c \<squnion> d)\<^sup>\<omega>"
      by (metis eq_iff sup.semigroup_axioms sup_commute nondet_seq_distrib iter_unfold semigroup.assoc)
    thus ?thesis using iter_induct_eq by (metis inf_sup_aci(5) iter_induct) 
  qed
  then have "d;c\<^sup>\<omega>;(d;(c \<squnion> d)\<^sup>\<omega> \<squnion> nil) \<squnion> nil \<ge> d;(c \<squnion> d)\<^sup>\<omega> \<squnion> nil" by (metis sup_mono order.refl seq_assoc seq_mono) 
  then have "(d;c\<^sup>\<omega>)\<^sup>\<omega> \<ge> d;(c \<squnion> d)\<^sup>\<omega> \<squnion> nil" by (metis sup_commute iter_induct_nil) 
  then have "c\<^sup>\<omega>;(d;c\<^sup>\<omega>)\<^sup>\<omega> \<ge> c\<^sup>\<omega>;(d;(c \<squnion> d)\<^sup>\<omega> \<squnion> nil)" by (metis order.refl seq_mono) 
  thus "c\<^sup>\<omega>;(d;c\<^sup>\<omega>)\<^sup>\<omega> \<ge> (c \<squnion> d)\<^sup>\<omega>" using a refine_trans by blast
qed

lemma fiter_decomp: "(c \<squnion> d)\<^sup>\<star> = c\<^sup>\<star>;(d;c\<^sup>\<star>)\<^sup>\<star>"
proof (rule antisym)
  have "c\<^sup>\<star>;(d;c\<^sup>\<star>)\<^sup>\<star> = (nil \<squnion> c;c\<^sup>\<star>);(d;c\<^sup>\<star>)\<^sup>\<star>"
    using fiter_unfold by simp
  also have "... = ((d;c\<^sup>\<star>)\<^sup>\<star> \<squnion> c;c\<^sup>\<star>;(d;c\<^sup>\<star>)\<^sup>\<star>)"
    by (simp add: sup_assoc nondet_seq_distrib seq_nondet_distrib seq_assoc)
  also have "... = (nil \<squnion> d;c\<^sup>\<star>;(d;c\<^sup>\<star>)\<^sup>\<star> \<squnion> c;c\<^sup>\<star>;(d;c\<^sup>\<star>)\<^sup>\<star>)"
    using fiter_unfold by simp
  also have "... = (nil \<squnion> (d \<squnion> c);c\<^sup>\<star>;(d;c\<^sup>\<star>)\<^sup>\<star>)"
    by (simp add: sup_assoc nondet_seq_distrib)
  also have "... = (nil \<squnion> (d \<squnion> c);(c\<^sup>\<star>;(d;c\<^sup>\<star>)\<^sup>\<star>))"
    by (simp add: seq_assoc)
  finally have "c\<^sup>\<star>;(d;c\<^sup>\<star>)\<^sup>\<star> \<ge> (nil \<squnion> (d \<squnion> c);(c\<^sup>\<star>;(d;c\<^sup>\<star>)\<^sup>\<star>))"
    by (simp)
  then show "c\<^sup>\<star>;(d;c\<^sup>\<star>)\<^sup>\<star> \<ge> (c \<squnion> d)\<^sup>\<star>"
    by (simp add: fiter_induct_nil seq_assoc sup_commute) 
next
  have a1: "(c \<squnion> d)\<^sup>\<star> \<ge> c\<^sup>\<star>"
    by (simp add: fiter_mono)
  have a2: "(c \<squnion> d)\<^sup>\<star> \<ge> d"
    using fiter1 sup.bounded_iff by blast
  have a3: "(c \<squnion> d)\<^sup>\<star> \<ge> nil"
    using fiter0 by simp
  then have "(c \<squnion> d)\<^sup>\<star> \<ge> nil \<squnion> (c \<squnion> d)\<^sup>\<star>"
    by simp
  then have "(c \<squnion> d)\<^sup>\<star> \<ge> nil \<squnion> d;c\<^sup>\<star>;(c \<squnion> d)\<^sup>\<star>"
    using a1 a2 a3 seq_mono by (metis fiter_seq_fiter sup.absorb2 sup.boundedI)
  then have a4: "(c \<squnion> d)\<^sup>\<star> \<ge> (d;c\<^sup>\<star>)\<^sup>\<star>"
    by (simp add: fiter_induct_nil) 
  then show "(c \<squnion> d)\<^sup>\<star> \<ge> c\<^sup>\<star>;(d;c\<^sup>\<star>)\<^sup>\<star>"
    using a1 a4 fiter_seq_fiter seq_mono by metis      
qed
  
lemma fiter_decomp_iter: "(c \<squnion> d)\<^sup>\<star>;c\<^sup>\<omega> = c\<^sup>\<omega>;(d;c\<^sup>\<omega>)\<^sup>\<star>"
proof -
  have "c\<^sup>\<omega>;(d;c\<^sup>\<omega>)\<^sup>\<star> = (c\<^sup>\<omega>;d)\<^sup>\<star>;c\<^sup>\<omega>"
    by (simp add: fiter_leapfrog)
  also have "... = (c\<^sup>\<star>;d)\<^sup>\<star>;c\<^sup>\<omega>"
  proof -
    have "(c\<^sup>\<omega>;d)\<^sup>\<star>;c\<^sup>\<omega> = ((c\<^sup>\<star> \<squnion> c\<^sup>\<infinity>);d)\<^sup>\<star>;c\<^sup>\<omega>"
      by (simp add: iter_isolation)         
    also have "... = lfp (\<lambda> x. nil \<squnion> ((c\<^sup>\<star> \<squnion> c\<^sup>\<infinity>);d;x));c\<^sup>\<omega>"
      by (simp add: fiter_def)
    also have "... = lfp (\<lambda> x. nil \<squnion> ((c\<^sup>\<star>;d;x \<squnion> c\<^sup>\<infinity>;d;x)));c\<^sup>\<omega>"
      by (simp add: nondet_seq_distrib)
    also have "... = lfp (\<lambda> x. nil \<squnion> c\<^sup>\<star>;d;x \<squnion> c\<^sup>\<infinity>);c\<^sup>\<omega>"
      by (simp add: infiter_annil sup_assoc)
    also have "... = lfp (\<lambda> x. c\<^sup>\<star>;d;x \<squnion> (nil \<squnion> c\<^sup>\<infinity>));c\<^sup>\<omega>"      
      by (metis sup_commute sup_assoc)
    also have "... =(c\<^sup>\<star>;d)\<^sup>\<star>;(nil \<squnion> c\<^sup>\<infinity>);c\<^sup>\<omega>"      
      by (simp add: fiter_induct_eq)
    also have "... =(c\<^sup>\<star>;d)\<^sup>\<star>;(nil \<squnion> c\<^sup>\<infinity>);(c\<^sup>\<star> \<squnion> c\<^sup>\<infinity>)"   
      by (simp add: iter_isolation)  
    also have "... =(c\<^sup>\<star>;d)\<^sup>\<star>;(nil;(c\<^sup>\<star> \<squnion> c\<^sup>\<infinity>) \<squnion> c\<^sup>\<infinity>;(c\<^sup>\<star> \<squnion> c\<^sup>\<infinity>))"
      by (simp add: nondet_seq_distrib seq_assoc)
    also have "... =(c\<^sup>\<star>;d)\<^sup>\<star>;(c\<^sup>\<star> \<squnion> c\<^sup>\<infinity>)"
      by (simp add: infiter_annil)
    also have "... =(c\<^sup>\<star>;d)\<^sup>\<star>;(c\<^sup>\<omega>)"
      by (simp add: iter_isolation)
    finally show ?thesis by simp
  qed
  also have "... = (c\<^sup>\<star>;d)\<^sup>\<star>;c\<^sup>\<star>;c\<^sup>\<omega>"
    using fiter_seq_iter seq_assoc by simp   
  also have "... = c\<^sup>\<star>;(d;c\<^sup>\<star>)\<^sup>\<star>;c\<^sup>\<omega>"
    using fiter_leapfrog seq_assoc by simp   
  also have "... = (c \<squnion> d)\<^sup>\<star>;c\<^sup>\<omega>"
    using fiter_decomp by simp
  finally show ?thesis by simp
qed

lemma fiter_iter_seq:
  shows "(c \<squnion> d)\<^sup>\<star>;c\<^sup>\<omega> = ((c \<squnion> d)\<^sup>\<star>;c\<^sup>\<omega>);((c \<squnion> d)\<^sup>\<star>;c\<^sup>\<omega>)"
proof -
  have "c\<^sup>\<omega>;(d;c\<^sup>\<omega>)\<^sup>\<star> = c\<^sup>\<omega>;(d;c\<^sup>\<omega>)\<^sup>\<star>;(d;c\<^sup>\<omega>)\<^sup>\<star>"
    using fiter_decomp_iter by (simp add: seq_assoc)
  also have "... = (c\<^sup>\<omega>;d)\<^sup>\<star>;c\<^sup>\<omega>;(d;c\<^sup>\<omega>)\<^sup>\<star>"
    by (simp add: fiter_leapfrog)
  also have "... = (c\<^sup>\<omega>;d)\<^sup>\<star>;c\<^sup>\<omega>;c\<^sup>\<omega>;(d;c\<^sup>\<omega>)\<^sup>\<star>"
    by (simp add: seq_assoc)
  also have "... = c\<^sup>\<omega>;(d;c\<^sup>\<omega>)\<^sup>\<star>;c\<^sup>\<omega>;(d;c\<^sup>\<omega>)\<^sup>\<star>"
    by (simp add: fiter_leapfrog)
  finally show ?thesis using fiter_decomp_iter seq_assoc by metis
qed
  
end


locale iteration_infinite_distrib = seq_Nondet_distrib + iteration + nondet_nat

begin

lemma fiter_seq_choice: "c\<^sup>\<star> = (\<Squnion>i::nat. c \<^sup>;^ i)"
proof (rule antisym)
  show "c\<^sup>\<star> \<ge> (\<Squnion>i. c \<^sup>;^ i)"
  proof (rule SUP_least) 
    fix i
    show "c\<^sup>\<star> \<ge> c \<^sup>;^ i"
      proof (induct i type: nat)
        case 0
        show "c\<^sup>\<star> \<ge> c \<^sup>;^ 0" by (simp add: fiter0)
      next
        case (Suc n)
        show "c\<^sup>\<star> \<ge> c \<^sup>;^ Suc n"
          by (metis Suc.hyps fiter1 fiter_seq_fiter seq_mono seq_power_Suc)
      qed
  qed
next
  have "(\<Squnion>i. c \<^sup>;^ i) \<ge> (c \<^sup>;^ 0) \<squnion> (\<Squnion>i. c \<^sup>;^ Suc i)" (is "_ \<ge> ?rhs") by (meson SUP_least SUP_upper UNIV_I le_sup_iff)
  also have "?rhs = nil \<squnion> (\<Squnion>i. c ; (c \<^sup>;^ i))" by simp
  also have "... \<ge> nil \<squnion> c ; (\<Squnion>i. c \<^sup>;^ i)" by (simp add: seq_NONDET_distrib_UNIV)
  finally show "(\<Squnion>i. c \<^sup>;^ i) \<ge> c\<^sup>\<star>" using fiter_induct_nil by blast
qed

lemma fiter_seq_choice_nonempty: "c ; c\<^sup>\<star> = (\<Squnion>i\<in>{i. 0 < i}. c \<^sup>;^ i)"
proof -
  have "(\<Squnion>i\<in>{i. 0 < i}. c \<^sup>;^ i) = (\<Squnion>i. c \<^sup>;^ (Suc i))" by (simp add: NONDET_nat_shift)
  also have "... = (\<Squnion>i. c ; (c \<^sup>;^ i))" by simp
  also have "... = c ; (\<Squnion>i. c \<^sup>;^ i)" by (simp add: seq_NONDET_distrib_UNIV)
  also have "... = c ; c\<^sup>\<star>" by (simp add: fiter_seq_choice)
  finally  show ?thesis by simp
qed 

end
end

