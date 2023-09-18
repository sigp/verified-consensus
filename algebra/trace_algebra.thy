theory trace_algebra
imports Trace_Monads CRA_Obs
begin


instantiation term_symbols :: (type) Trace_Monads.bounded_order begin

definition "top_term_symbols = (Abort :: 'a term_symbols)"
definition "bot_term_symbols = (Incomplete :: 'a term_symbols)"

fun less_eq_term_symbols where
 "less_eq_term_symbols Incomplete r = True"|
 "less_eq_term_symbols r Abort = True" |
 "less_eq_term_symbols (Term a) (Term b) = (a = b)" |
 "less_eq_term_symbols r Incomplete = (r = Incomplete)" |
 "less_eq_term_symbols Abort r = (r = Abort)"


definition
  "(f:: ('a) term_symbols) < g \<longleftrightarrow> f \<le> g \<and> \<not> (g \<le> f)"

instance
  apply (intro_classes; (clarsimp simp: less_term_symbols_def bot_term_symbols_def top_term_symbols_def  split: term_symbols.splits)?)
    apply (case_tac x; clarsimp)
    apply (case_tac x; case_tac y; case_tac z; clarsimp)
   apply (case_tac x; case_tac y;  clarsimp)

  apply (case_tac a; clarsimp)
  done
end






instantiation  trace :: (order, Trace_Monads.bounded_order)  preorder_bot begin

definition "bot_trace = ((empty_trace bot) :: ('a, 'b) trace)"

instance
  apply (intro_classes; clarsimp simp: bot_trace_def less_eq_trace_def)
  using less_eq_sum.elims(3) by fastforce
end

term Suc


definition "last_trace t \<equiv> (case (lengthS t) of (Some (Suc n)) \<Rightarrow> dropS n t | (Some 0) \<Rightarrow> t | None \<Rightarrow> \<bottom>)"

definition "first_trace t \<equiv> (case (lengthS t) of (Some (Suc n)) \<Rightarrow> takeS 1 t | (Some 0) \<Rightarrow> t | None \<Rightarrow> \<bottom>)"


definition "test t \<equiv> constT t"

lemma trace_leI: "(\<And>n. index x n \<le> index y n) \<Longrightarrow> x \<le> y"
  apply (clarsimp simp: less_eq_trace_def)
  done
lemma trace_leD: "x \<le> y \<Longrightarrow>  index x n \<le> index y n  "
  apply (clarsimp simp: less_eq_trace_def)
  done

lemma coerce_index_mono: "x \<le> y \<Longrightarrow> n < the (lengthS x) \<Longrightarrow> n < the (lengthS y) \<Longrightarrow> (coerce (index x n) ) \<le> (coerce (index y n))"
  apply (drule trace_leD[where n=n])
  apply (case_tac "index x n"; case_tac "index y n"; clarsimp)

   apply (metis inf_all_l leD lengthS_leI no_length_no_termination sum.disc(2))
  apply (metis inf_all_l leD lengthS_leI no_length_no_termination sum.disc(2))
  done


lemma terminates_appendS[simp]: "terminates x \<Longrightarrow> appendS x y ^ n = (if n < (the (lengthS x)) then coerce (x ^ n) else y ^ (n - (the (lengthS x))))"
  by (metis index_append lengthS_def option.sel terminates_finite)

definition "compatible_trace t t' \<equiv> (case (lengthS t) of (Some (Suc n)) \<Rightarrow>
                                       (case (index t' 0) of (Inl a) \<Rightarrow> (index t n = Inl a)  |
                                                             _  \<Rightarrow> True ) | _ \<Rightarrow> True)"



definition "seq_t t t' = (if terminates t then (if compatible_trace t t' then appendS t t' else appendS t \<bottom>)
                             else fmap_trace id (coerce_sym) t) "

lemma both_terminate: "terminates y \<Longrightarrow> n < the (lengthS y) \<Longrightarrow> terminates x \<Longrightarrow>  x \<le> y \<Longrightarrow> n < the (lengthS x)"
  apply (clarsimp simp: terminates_def)
  apply (drule trace_leD[where n=n])
  apply (case_tac "index x n"; case_tac "index y n"; clarsimp)
     apply (metis inf_all_l isl_iff option.exhaust_sel sum.disc(1) sum.disc(2))
  apply (metis inf_all_l isl_iff option.exhaust_sel sum.disc(1) sum.disc(2))
   apply (metis bot_term_symbols_def index_inr_eq term_symbols.distinct(1))
  by (metis finiteS_def leD lengthS_leI sum.disc(2))

lemma le_terminating_same_length: "terminates y \<Longrightarrow>  terminates x \<Longrightarrow>  x \<le> y \<Longrightarrow> lengthS x = lengthS y"
  apply (rule lengthS_eqI; clarsimp)
  apply (drule_tac n=n in trace_leD)
   apply (case_tac "index x n"; case_tac "index y n"; clarsimp)
    apply (simp add: no_length_no_termination)
  apply (simp add: no_length_no_termination)
  apply (safe)
   apply (metis both_terminate leD lengthS_leI option.sel terminates_finite)
  apply (drule_tac n=n in trace_leD)
   apply (case_tac "index x n"; case_tac "index y n"; clarsimp simp: top_term_symbols_def bot_term_symbols_def)
     apply (metis dual_order.refl isl_iff linorder_not_less sum.disc(1))
    apply (metis fails_def finite_fail_or_term lengthS_some_finite )
  using fails_def apply auto[1]
  by (metis isl_monotone linorder_le_less_linear sum.disc(2))

  thm leD
  
  oops
     apply (metis inf_all_l isl_iff option.exhaust_sel sum.disc(1) sum.disc(2))
  apply (metis inf_all_l isl_iff option.exhaust_sel sum.disc(1) sum.disc(2))
   apply (metis bot_term_symbols_def index_inr_eq term_symbols.distinct(1))
  by (metis finiteS_def leD lengthS_leI sum.disc(2))


lemma match_terminate_append[simp]: "compatible_trace t t' \<Longrightarrow> terminates t  \<Longrightarrow> seq_t t t' = appendS t t'"
  by (clarsimp simp: seq_t_def)


lemma no_match_terminate_append[simp]: " terminates t  \<Longrightarrow> \<not>compatible_trace t t' \<Longrightarrow> seq_t t t' = appendS t \<bottom>"
  by (clarsimp simp: seq_t_def)


lemma no_terminate_append[simp]: " \<not>terminates t  \<Longrightarrow>  seq_t t t' = fmap_trace id (coerce_sym) t"
  by (clarsimp simp: seq_t_def)

lemma [simp]:"coerce_sym \<top> = \<top>" by (clarsimp simp: top_term_symbols_def)

lemma [simp]:"coerce_sym \<bottom> = \<bottom>" by (clarsimp simp: bot_term_symbols_def)

thm match_def

lemma incompatible_non_empty: "\<not> compatible_trace x y \<Longrightarrow> \<exists>s. index y 0 = Inl s"
  apply (clarsimp simp: compatible_trace_def split: option.splits)
  apply (case_tac x2; clarsimp)
  by (clarsimp split: sum.splits)


lemma incompatible_non_empty': "\<not> compatible_trace x y \<Longrightarrow> \<exists>s n. lengthS x = Some (Suc n) \<and>  index x n = Inl s"
  apply (clarsimp simp: compatible_trace_def split: option.splits)
  apply (case_tac x2; clarsimp)
  apply (clarsimp split: sum.splits)
  by (metis isl_iff lessI sum.collapse(1))


lemma index_bot_iff: "index \<bottom> n = Inr Incomplete"
  by (clarsimp simp: bot_trace_def bot_term_symbols_def)

lemma le_terminates_has_length: "x \<le> y \<Longrightarrow> terminates y \<Longrightarrow> lengthS x \<noteq> None"
  apply (rule ccontr; clarsimp)
  apply (clarsimp simp: terminates_def)
  apply (drule_tac n=n in trace_leD)
  by (metis inf_all_l isl_def less_eq_sum.simps(3) term_symbols.distinct(3) top_term_symbols_def)

lemma terminated_le:" x \<le> y \<Longrightarrow> terminates x \<Longrightarrow> terminates y \<Longrightarrow> x = y"
  apply (rule antisym, assumption)
  apply (rule trace_leI)
  apply (drule_tac n=n in trace_leD)
  apply (case_tac "index x n"; case_tac "index y n"; clarsimp?)
    apply (metis index_inr_eq term_symbols.distinct(3) terminatesD top_term_symbols_def)
   apply (metis bot_term_symbols_def fails_def finite_fail_or_term terminates_finite)
  apply (case_tac "b"; case_tac "ba"; clarsimp)
  using fails_def apply auto[1]
  using fails_def apply auto[1]
  using fails_def apply auto[1]
  done


lemma "lengthS b = Some (Suc n) \<Longrightarrow> lengthS a = None \<Longrightarrow> a \<le> b \<Longrightarrow> a \<le> \<bottom>"
  apply (clarsimp simp: bot_trace_def)
  apply (rule trace_leI)
  apply (clarsimp)
  apply (case_tac "na \<le> n")
  apply (drule_tac n=na in trace_leD)
   apply (case_tac "index b na", clarsimp)
    apply (case_tac "index a na"; clarsimp)
  oops

lemma compatible_trace_disj: "compatible_trace x a \<Longrightarrow> x \<le> y \<Longrightarrow> a \<le> b \<Longrightarrow> terminates y \<Longrightarrow> terminates x \<Longrightarrow> compatible_trace y b \<or> a \<le> \<bottom>" 
  apply (clarsimp simp: terminated_le)
  apply (frule (2) terminated_le; clarsimp)
  apply (subst compatible_trace_def)
  apply (clarsimp split: option.splits)
   apply (case_tac x2; clarsimp)
  apply (clarsimp simp: compatible_trace_def)
  apply (case_tac "index a 0"; clarsimp)
   apply (clarsimp split: sum.splits)
   apply (metis less_eq_sum.simps(1) less_eq_trace_def)
  apply (clarsimp split: sum.splits)
  by (metis bot_trace_def dual_order.refl inf_all_l le_zero_eq lengthS_leI lengthS_zero_empty_trace
 less_eq_sum.simps(2) no_length_no_termination option.exhaust_sel sum.disc(2) sum.sel(2) trace_leD)


lemma index_fmap_trace:"index (fmap_trace f g t) n = map_sum f g (index t n)" 
  by (clarsimp simp: fmap_trace_def)

lemma aborting_greatest[simp]: "x \<le> Inr Abort"
  apply (case_tac x; clarsimp simp: top_term_symbols_def)
  apply (case_tac b; clarsimp)
  done

lemma non_terminating_ge_terminating_aborts: 
  "x \<le> y \<Longrightarrow> lengthS x = Some n \<Longrightarrow> n' \<ge> n \<Longrightarrow>
        terminates x \<Longrightarrow> \<not> terminates y \<Longrightarrow> index y n' = Inr Abort"
  by (smt (verit, ccfv_SIG) antisym bot_term_symbols_def bot_trace_def fails_def 
         finite_fail_or_term index_empty index_inr_eq inf_all_l isl_def isr_iff 
         less_eq_sum.simps(2) no_length_no_termination preorder_bot_class.bot_least sumE trace_leD)


lemma non_terminating_ge_terminating_incomplete: 
  "x \<le> y \<Longrightarrow> lengthS y = Some n \<Longrightarrow> n' \<ge> n \<Longrightarrow>
        \<not>terminates x \<Longrightarrow>  terminates y \<Longrightarrow> index x n' = Inr Incomplete"
  by (smt (verit, del_insts) fails_def finite_fail_or_term index_inr_eq isr_antitone le_terminates_has_length less_eq_sum.simps(3) less_eq_sum.simps(4) less_eq_term_symbols.simps(7) less_eq_trace_def no_length_no_termination option.sel sumE term_symbols.distinct(3) terminatesD top_term_symbols_def)
  oops
  by (smt (verit, ccfv_SIG) antisym bot_term_symbols_def bot_trace_def fails_def 
         finite_fail_or_term index_empty index_inr_eq inf_all_l isl_def isr_iff 
         less_eq_sum.simps(2) no_length_no_termination preorder_bot_class.bot_least sumE trace_leD)



lemma index_bot_least[simp]: "index \<bottom> n \<le> x"
  by (case_tac x; clarsimp simp: bot_trace_def)


lemma seq_trace_mono: " x \<le> y \<Longrightarrow> a \<le> b \<Longrightarrow> (seq_t x a) \<le> (seq_t y b) "
            apply (rule trace_leI)
            apply (case_tac "compatible_trace x a \<and> terminates x"; clarsimp?)
            apply (case_tac "compatible_trace y b \<and> terminates y"; clarsimp?)
    apply (safe; clarsimp?)
       apply (erule (2) coerce_index_mono)
  using both_terminate apply blast
     apply (metis le_terminating_same_length)
    apply (metis le_terminating_same_length trace_leD)
   apply (safe)
       apply (case_tac "terminates y"; clarsimp)
        apply (intro conjI impI)
  using coerce_index_mono apply blast
        apply (metis le_terminating_same_length)
       apply (case_tac "index y n"; clarsimp simp: index_fmap_trace)
        apply (metis coerce.simps(1) lengthS_leI less_eq_sum.simps(1)
               linorder_not_less sum.collapse(1) terminates_finite trace_leD)
       apply (drule_tac n=n in trace_leD, clarsimp)
       apply (case_tac "index x n"; clarsimp)
       apply (metis leD lengthS_leI sum.disc(2) terminates_finite)
       apply (case_tac "terminates y"; clarsimp)
       apply (safe; clarsimp?)
        apply (metis le_terminating_same_length)
       apply (clarsimp simp: index_bot_iff)
       apply (frule_tac n=0 and x=a in trace_leD)
       apply (frule incompatible_non_empty, clarsimp)
  apply (frule incompatible_non_empty', clarsimp) 
       apply (metis (no_types, opaque_lifting) compatible_trace_disj dual_order.eq_iff index_bot_iff preorder_bot_class.bot_least)
      apply (subgoal_tac "index y n = Inr Abort", clarsimp simp: index_fmap_trace)

  using non_terminating_ge_terminating_aborts 
      apply (metis linorder_le_less_linear option.sel terminatesD)
     apply (clarsimp simp: index_fmap_trace)
  apply (case_tac "index y n"; clarsimp)
      apply (metis coerce.simps(1) leD lengthS_leI less_eq_sum.simps(1) less_eq_trace_def sum.collapse(1) terminates_finite)
     apply (case_tac ba; clarsimp)
  using terminates_def apply blast
     apply (meson dual_order.refl index_inr_eq no_length_no_termination 
   non_terminating_ge_terminating_aborts option.exhaust_sel term_symbols.simps(7) terminates_finite)
    apply (clarsimp)
    apply (subgoal_tac "index y n = Inr Abort", clarsimp simp: index_fmap_trace)
  using non_terminating_ge_terminating_aborts 
    apply (metis linorder_le_less_linear option.sel terminatesD)
  apply (case_tac "terminates x")
    apply (clarsimp)
    apply (safe)
     apply (case_tac "terminates y", clarsimp?)
      apply (metis dual_order.refl match_terminate_append no_match_terminate_append terminated_le terminates_appendS)
     apply (clarsimp)
    apply (case_tac "index y n = Inr Abort", clarsimp simp: index_fmap_trace)
     apply (smt (verit, best) coerce_clean_index coerce_index_mono coerce_le coerce_syms_def index_eq_finished inf_all_l isr_iff 
       lengthS_fmap linorder_le_less_linear no_length_no_termination non_terminating_ge_terminating_aborts option.exhaust_sel order_less_imp_le sum.disc(2) terminates_finite)
   apply (clarsimp)
   apply (case_tac "terminates y", clarsimp?)
    apply (clarsimp simp: seq_t_def)
    apply (safe)
      apply (clarsimp simp: index_fmap_trace)
  apply (case_tac "index x n"; clarsimp)
       apply (metis coerce.simps(1) coerce_index_mono incompatible_non_empty' isl_iff option.sel sum.disc(1))
  apply (subgoal_tac "ba = Incomplete", clarsimp)
       apply (metis index_bot_iff index_bot_least)
      apply (metis bot_term_symbols_def dual_order.strict_iff_not finiteS_def lengthS_leI less_eq_sum.simps(2) old.sum.exhaust sum.disc(2) trace_leD)
      apply (clarsimp simp: index_fmap_trace)

     apply (subgoal_tac "index x n = Inr Incomplete", clarsimp)
      apply (metis index_bot_iff index_bot_least)
using non_terminating_ge_terminating_incomplete
   apply (metis linorder_le_less_linear no_length_no_termination option.exhaust_sel terminates_finite)
      apply (clarsimp simp: index_fmap_trace)

  apply (subgoal_tac "index x n = Inr Incomplete", clarsimp)
   apply (simp add: index_bot_iff order.order_iff_strict)

using non_terminating_ge_terminating_incomplete
  apply (metis linorder_le_less_linear no_length_no_termination option.exhaust_sel terminates_finite)
  apply (clarsimp simp: index_fmap_trace)
  apply (case_tac "index x n"; clarsimp)
  apply (smt (verit, best) coerce_sym.simps(1) id_apply less_eq_sum.simps(1) less_eq_sum.simps(3) less_eq_trace_def map_sum.simps(1) map_sum.simps(2) sum.exhaust_sel top_term_symbols_def)
  apply (metis (no_types, opaque_lifting) Orderings.order_eq_iff aborting_greatest coerce_sym.simps(2) fails_def finiteS_def finite_fail_or_term index_bot_iff index_bot_least index_inr_eq map_sum.simps(2) sum.disc(2) trace_leD)
  apply (clarsimp)
 apply (case_tac "terminates y", clarsimp?)
    apply (clarsimp simp: seq_t_def)
    apply (safe)
      apply (clarsimp simp: index_fmap_trace)
   apply (case_tac "index x n"; clarsimp)
  apply (metis coerce.simps(1) coerce_index_mono isl_iff le_terminates_has_length option.exhaust_sel sum.disc(1))
  apply (subgoal_tac "ba = Incomplete", clarsimp)
       apply (metis index_bot_iff index_bot_least)
      apply (metis bot_term_symbols_def dual_order.strict_iff_not finiteS_def lengthS_leI less_eq_sum.simps(2) old.sum.exhaust sum.disc(2) trace_leD)
      apply (clarsimp simp: index_fmap_trace)

     apply (subgoal_tac "index x n = Inr Incomplete", clarsimp)
      apply (metis index_bot_iff index_bot_least)
using non_terminating_ge_terminating_incomplete
   apply (metis linorder_le_less_linear no_length_no_termination option.exhaust_sel terminates_finite)
      apply (clarsimp simp: index_fmap_trace)

  apply (subgoal_tac "index x n = Inr Incomplete", clarsimp)
   apply (simp add: index_bot_iff order.order_iff_strict)

using non_terminating_ge_terminating_incomplete
  apply (metis linorder_le_less_linear no_length_no_termination option.exhaust_sel terminates_finite)
  apply (clarsimp simp: index_fmap_trace)
  apply (case_tac "index x n"; clarsimp)
  apply (smt (verit, best) coerce_sym.simps(1) id_apply less_eq_sum.simps(1) less_eq_sum.simps(3) less_eq_trace_def map_sum.simps(1) map_sum.simps(2) sum.exhaust_sel top_term_symbols_def)
  apply (metis (no_types, opaque_lifting) Orderings.order_eq_iff aborting_greatest coerce_sym.simps(2) fails_def finiteS_def finite_fail_or_term index_bot_iff index_bot_least index_inr_eq map_sum.simps(2) sum.disc(2) trace_leD)
  done 

lemma not_terminates_tail_not_term_seq: "\<not> terminates b \<Longrightarrow> \<not> terminates (seq_t a b)"
  by (metis coerce_syms_def fails_def finite_fail_or_term index_bot_iff seq_t_def terminates_clean terminates_finite terminates_tail)


lemma not_terminates_tail_not_term_appendS: "\<not> terminates b \<Longrightarrow> \<not> terminates (appendS a b)"
  by (metis fails_appendS finiteS_append_iff finite_fail_or_term terminates_finite)

lemma compatible_coerce: "compatible_trace c b \<Longrightarrow> compatible_trace c (fmap_trace id coerce_sym b)"
  apply (clarsimp simp: compatible_trace_def index_fmap_trace split: option.splits)
  apply (case_tac x2; clarsimp)
  by (clarsimp simp: index_fmap_trace split: sum.splits)

lemma compatible_coerce': "\<not>compatible_trace c b \<Longrightarrow> \<not>compatible_trace c (fmap_trace id coerce_sym b)"
  apply (clarsimp simp: compatible_trace_def index_fmap_trace split: option.splits)
  apply (case_tac x2; clarsimp)
  by (clarsimp simp: index_fmap_trace split: sum.splits)

lemma fmap_id_coerce_tail: "fmap_trace id coerce_sym (appendS t t') = appendS t (fmap_trace id coerce_sym t')"
  apply (rule trace_eqI; clarsimp simp: index_fmap_trace)
  apply (case_tac "finiteS t")
   apply (metis (no_types, lifting) Trace_Monads.map_sum.compositionality fmap_trace_appendS fun.map_id sum.map_id trace_algebra.index_fmap_trace)
  by (metis fmap_trace_appendS sum.map_id trace_algebra.index_fmap_trace trace_eqI)
  apply (clarsimp)

lemma [simp]: "(fmap_trace id coerce_sym \<bottom>) = \<bottom>"
  by (rule trace_eqI; clarsimp simp: index_fmap_trace bot_trace_def)

lemma bot_no_term[simp]: "\<not>terminates \<bottom>"
  apply (clarsimp simp: bot_trace_def)
  apply (drule terminatesD)
  by (clarsimp simp: bot_term_symbols_def)

lemma seq_unfinished[simp]: "seq_t (appendS c \<bottom>) a = (appendS c \<bottom>)"
  apply (clarsimp simp: seq_t_def, safe; clarsimp simp: not_terminates_tail_not_term_appendS)
     apply (clarsimp simp: fmap_id_coerce_tail)
     apply (clarsimp simp: fmap_id_coerce_tail)
  done

lemma appendS_prefix: " appendS a \<bottom> \<le> appendS a d" 
  apply (rule trace_leI)
  apply (case_tac "\<exists>n. lengthS a = Some n"; clarsimp?)
  apply (clarsimp simp: index_append)
  done

lemma compatible_append_assoc: "compatible_trace c b \<Longrightarrow> compatible_trace b a \<Longrightarrow> compatible_trace c (appendS b a) \<longleftrightarrow> compatible_trace (appendS c b) a "
  apply (clarsimp simp: compatible_trace_def split: option.splits sum.splits)
   apply (case_tac "x2"; clarsimp)
   apply (safe; clarsimp?)
     apply (metis clean_idemp coerce.simps(1) index_append_inf inf_append_simp lengthS_clean no_length_easy_clean)
   apply (case_tac "x2"; clarsimp)

  apply (case_tac "\<exists>n. lengthS b = Some n"; clarsimp?)
    apply (clarsimp simp: index_append)
    apply (metis infinite_appendS_iff option.distinct(1))
  apply (metis infinite_appendS_iff option.distinct(1))
  apply (safe)
    apply (simp add: infinite_appendS_iff)
   apply (case_tac "x2"; clarsimp)
    apply (case_tac "x2b"; clarsimp)
   apply (case_tac "x2a"; clarsimp)
    apply (case_tac "x2b"; clarsimp)

    apply (simp add: Traces.lengthS_append_eq index_append)
   apply (case_tac "x2b"; clarsimp)
    apply (simp add: Traces.lengthS_append_eq index_append)
  apply (case_tac "x2"; case_tac "x2a"; case_tac "x2b"; clarsimp)
    apply (simp add: Traces.lengthS_append_eq index_append)
    apply (simp add: Traces.lengthS_append_eq index_append)
    apply (metis coerce.simps(1) coerce_coerce coerce_le lessI)
    apply (simp add: Traces.lengthS_append_eq index_append)
  apply (simp add: Traces.lengthS_append_eq index_append)
  by (metis coerce.simps(1) isl_coerce sum.collapse(1) sum.disc(1))

lemma append_terminating_still_incompatible: "terminates c \<Longrightarrow> \<not> compatible_trace b a \<Longrightarrow> \<not>compatible_trace (appendS c b) a" 
  apply (erule contrapos_nn)
  apply (clarsimp simp: compatible_trace_def split: option.splits sum.splits)
   apply (simp add: no_length_no_termination terminates_finite)
  apply (case_tac x2; case_tac x2a; clarsimp)
   apply (metis first_None_iff' first_appendS first_index_iff length_zero_append option.distinct(1))
  apply (clarsimp split: if_splits)
   apply (metis Traces.lengthS_append_eq bot_nat_0.not_eq_extremum less_add_same_cancel1 not_less_eq option.sel order_less_asym')
  by (smt (verit, ccfv_SIG) Nat.diff_add_assoc Traces.lengthS_append_eq add_diff_cancel_left' leI option.sel plus_1_eq_Suc)

lemma compatible_append_bot_still_compat: "compatible_trace c b \<Longrightarrow> compatible_trace c (appendS b \<bottom>)"
   apply (clarsimp simp: compatible_trace_def split: option.splits sum.splits)
  apply (case_tac x2; clarsimp)
  apply (case_tac "\<exists>n. lengthS b = Some n"; clarsimp?)
   apply (metis bot_trace_def coerce.simps(1) index_append index_empty isl_iff sum.collapse(1) sum.disc(1) sum.disc(2))
  by (metis coerce.simps(1) index_append_inf inf_append_simp isl_coerce isl_def)
  

lemma seq_t_assoc: "seq_t (seq_t c b) a \<le> seq_t c (seq_t b a)"
  apply (case_tac "terminates c")
   defer
   apply (clarsimp)
   apply (metis coerce_syms_def coerce_syms_idemp order_refl)
  apply (case_tac "terminates b"; clarsimp?)
   defer
  apply (clarsimp simp: not_terminates_tail_not_term_seq)
   apply (case_tac "compatible_trace c b", clarsimp)
    apply (rule trace_leI, clarsimp simp: index_fmap_trace  compatible_coerce)
    apply (smt (verit, best) coerce.simps(1) dual_order.eq_iff id_apply isl_iff map_sum.simps(1) no_length_no_termination option.exhaust_sel sum.collapse(1) terminates_finite)
   apply (clarsimp)
   apply (clarsimp simp: compatible_coerce')
   apply (clarsimp simp: fmap_id_coerce_tail)
   apply (case_tac "compatible_trace c b", clarsimp)
   defer
   apply (clarsimp)
   apply (clarsimp simp: seq_t_def)
   apply (safe; clarsimp simp: appendS_prefix)
  apply (case_tac " compatible_trace b a", clarsimp)
   apply (case_tac "compatible_trace c (appendS b a)"; clarsimp simp: compatible_append_assoc)
    apply (simp add: appendS_assoc ) 
  defer
   apply (clarsimp)
   apply (clarsimp simp: seq_t_def)
   apply (safe)
      apply (clarsimp simp: append_terminating_still_incompatible)
  using append_terminating_still_incompatible apply blast
    apply (simp add: appendS_assoc)
  using compatible_append_bot_still_compat 
   apply blast
  apply (subst appendS_assoc[symmetric])
  by (metis (no_types, lifting) Orderings.order_eq_iff appendS_prefix compatible_append_assoc compatible_append_bot_still_compat compatible_trace_disj preorder_bot_class.bot_least)

lemma compatible_left_append: "compatible_trace b a \<Longrightarrow> compatible_trace c (appendS b a) \<Longrightarrow> compatible_trace c b"
  apply (clarsimp simp: compatible_trace_def split: option.splits sum.splits)
  apply (case_tac x2; clarsimp)
   apply (metis coerce.simps(1) index_append_inf inf_append_simp)
  apply (case_tac x2; case_tac x2a; clarsimp)
   apply (metis isl_iff less_numeral_extra(3) sum.disc(1))
  by (simp add: index_append)

lemma compatible_append_bot: "compatible_trace c (appendS b \<bottom>) \<Longrightarrow> compatible_trace c b"
  apply (clarsimp simp: compatible_trace_def split: option.splits sum.splits)
  apply (case_tac x2; clarsimp)
  by (metis coerce.simps(1) index_append index_append_inf isl_iff lengthS_def sum.disc(1))

lemma seq_t_assoc': "seq_t (seq_t c b) a \<ge> seq_t c (seq_t b a)"
  apply (case_tac "terminates c")
   defer
   apply (clarsimp)
   apply (metis coerce_syms_def coerce_syms_idemp order_refl)
  apply (case_tac "terminates b"; clarsimp?)
   defer
  apply (clarsimp simp: not_terminates_tail_not_term_seq)
   apply (case_tac "compatible_trace c b", clarsimp)
    apply (rule trace_leI, clarsimp simp: index_fmap_trace  compatible_coerce)
    apply (smt (verit, best) coerce.simps(1) dual_order.eq_iff id_apply isl_iff map_sum.simps(1) no_length_no_termination option.exhaust_sel sum.collapse(1) terminates_finite)
   apply (clarsimp)
   apply (clarsimp simp: compatible_coerce')
   apply (clarsimp simp: fmap_id_coerce_tail)
   apply (case_tac "compatible_trace c b", clarsimp)
   defer
   apply (clarsimp)
  apply (case_tac " compatible_trace b a", clarsimp)

    apply (clarsimp simp: seq_t_def)
  using compatible_left_append apply blast
   apply (clarsimp)
   apply (clarsimp simp: seq_t_def)
  using compatible_append_bot apply blast
  
  apply (case_tac " compatible_trace b a", clarsimp)
   apply (case_tac "compatible_trace c (appendS b a)"; clarsimp simp: compatible_append_assoc)
    apply (simp add: appendS_assoc ) 
   apply (metis appendS_assoc appendS_prefix)
  apply (clarsimp)
  apply (clarsimp simp: seq_t_def)
  apply (safe; (clarsimp simp: appendS_prefix)?)
  using append_terminating_still_incompatible apply blast
    apply (simp add: appendS_assoc ) 
  using append_terminating_still_incompatible apply blast
  using compatible_append_bot_still_compat by blast

lemma [simp]:"lengthS \<bottom> = Some 0"
  by (clarsimp simp: bot_trace_def)

lemma compatible_first[simp]: "compatible_trace (first_trace a) a "
  apply (clarsimp simp: first_trace_def compatible_trace_def)
  apply (clarsimp split: option.splits sum.splits)
  apply (safe)
  apply (case_tac x2; clarsimp)
  apply (case_tac x2a; clarsimp)
  by (metis Suc_leI Suc_n_not_le_n index_take isr_iff lessI less_Suc0)


lemma terminates_first_iff: "terminates (first_trace a) \<longleftrightarrow> terminates a"
  apply (clarsimp simp: first_trace_def split: option.splits)
  apply (safe)
    apply (simp add: no_length_no_termination)
   apply (metis Nitpick.case_nat_unfold index_take terminatesD terminatesI)
   apply (metis Nitpick.case_nat_unfold index_take terminatesD terminatesI)
  done
sledgehammer

lemma terminates_first_length: "terminates a \<Longrightarrow> the (lengthS (first_trace a)) \<le> 1"
  apply (clarsimp simp: first_trace_def split: option.splits)
  apply (case_tac x2; clarsimp)
  by (metis finiteS_takeS index_take lengthS_leI order_less_irrefl sum.disc(2) terminatesD)

lemma "a \<le> seq_t (first_trace a) a"
  apply (clarsimp simp: seq_t_def)
  apply (safe)
   apply (rule trace_leI)
   apply (case_tac "finiteS a"; clarsimp)
    apply (safe; clarsimp simp: terminates_first_iff)
  apply (clars

lemma "b \<le> test t \<Longrightarrow> (first_trace a \<le> b) = (a \<le> seq_t b a)"
  apply (safe)
   apply (rule order_trans[rotated])
    apply (rule seq_trace_mono, assumption)
  apply (rule order_refl)


interpretation seq_elem seq_t last_trace test first_trace
  apply (standard; clarsimp?)
  apply (erule (1) seq_trace_mono)
             apply (rule seq_t_assoc)
  apply (rule seq_t_assoc')

  apply (case_tac terminates s)
  oops
             apply (metis seq_traceS_assoc)
            apply (rule trace_leI)
            apply (case_tac "terminates x"; clarsimp)
             apply (case_tac "terminates y"; clarsimp)
  apply (metis coerce_index_mono le_terminating_same_length trace_leD)
  oops

  find_theorems appendS index
  apply (intro 

end