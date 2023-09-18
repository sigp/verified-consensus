theory Trace_Monads
imports Main Traces "HOL-Library.Monad_Syntax" 
begin


datatype ('a) term_symbols = Term (res: 'a) | Incomplete | Abort

type_synonym  ('a, 'state) State =  "'state + 'a term_symbols"

abbreviation (input) "isState \<equiv> isl"


(* definition "traceDom \<equiv> {(f). \<forall> (i :: nat) j. j \<le> i \<longrightarrow> \<not>(isState (f j)) \<longrightarrow> f i = f j}"

typedef ('a, 'state) trace = "traceDom :: (nat \<Rightarrow> ('a, 'state) State) set"
  apply (rule_tac x="\<lambda>_. Term undefined" in exI)
  apply (clarsimp simp: traceDom_def)
  done

setup_lifting type_definition_trace     
(* datatype ('a, 'state) stateS =
   Empty | Next (hd : "'state") (tl: "unit \<Rightarrow> ('a, 'state) stateS") | Abort |
   Result (res : "'a") *)

lift_definition index :: " ('a, 'state) trace \<Rightarrow> nat \<Rightarrow>  ('a, 'state) State" is "\<lambda>f n. f n" done
*)

primrec iterate where
  "iterate x f 0       = x" |
  "iterate x f (Suc n) = f (iterate x f n)" 

(* definition "finiteS f \<equiv> \<exists>n. \<not>isState (index f n)" *)

(* lift_definition pred :: "((nat \<Rightarrow>  ('a, 'state) State) \<Rightarrow> 'b) \<Rightarrow> ( ('a, 'state) trace \<Rightarrow> 'b)" is "\<lambda>P f. P f"
  done

definition "terminates \<equiv> \<lambda>f. \<exists>n c . ( f n) = Term c "


definition lengthS where "lengthS \<equiv> \<lambda>f. if (\<exists>n. \<not>isState (f n)) then Some (LEAST n. \<not>isState (f n)) else None"

lift_definition liftF :: "(nat \<Rightarrow>  ('a, 'state) State) \<Rightarrow>  ('a, 'state) trace " is
 "\<lambda>f. if f \<in> traceDom then f else (\<lambda>_. Incomplete)" 
  by (clarsimp simp: traceDom_def)
*)

lemma traceDom_antimono: "g \<in> traceDom \<Longrightarrow> antimono P \<Longrightarrow> (\<And>n. P n \<longrightarrow> isState (f n)) \<Longrightarrow> (\<lambda>n. if P n then f n else g n ) \<in> traceDom"
  apply ( clarsimp simp: traceDom_def split: if_splits)
  by (metis monotoneD)

lemma traceDom_antimono': "\<not>(\<lambda>n. if P n then f n else g n ) \<in> traceDom \<Longrightarrow>  antimono P \<Longrightarrow> (\<And>n. P n \<Longrightarrow> isState (f n)) \<Longrightarrow> \<not>g \<in> traceDom "
  apply ( clarsimp simp: traceDom_def split: if_splits)
  by (metis monotoneD)

lemma traceDom_antimono': " antimono P \<Longrightarrow> (\<And>n. P n \<Longrightarrow> isState (f n)) \<Longrightarrow> (\<lambda>n. if P n then f n else g n ) \<in> traceDom  \<longleftrightarrow> g \<in> traceDom "
  apply (rule iffI)
   apply ( clarsimp simp: traceDom_def split: if_splits)
  oops


lemma antimono_less[simp, intro]: "antimono (\<lambda>n. n < x)"
  apply (clarsimp simp: antimono_def, rule monotoneI)
  by auto


lemma [simp]:"map_sum h i o (index t) \<in> traceDom"
  apply (clarsimp simp: traceDom_def isl_iff split: sum.splits)
  by (metis index_eq_finished isl_map_sum order_refl)

definition "fmap_trace f g t = liftF ( map_sum f g o index t)"


functor map_sum: "fmap_trace "
proof -
  show "fmap_trace f g \<circ> fmap_trace h i = fmap_trace (f \<circ> h) (g \<circ> i)" for f g h i
    unfolding fmap_trace_def
    apply (intro ext trace_eqI, clarsimp)
    by (subst comp_assoc[symmetric], simp add: map_sum.comp)
  show "fmap_trace id id = id"
    unfolding fmap_trace_def
    apply (intro ext trace_eqI, clarsimp)
    by (simp add: sum.map_id0)
qed




primrec coerce_sym where
  "coerce_sym Abort = Abort" |
  "coerce_sym Incomplete = Incomplete" |
  "coerce_sym (Term _) = Term undefined" 


definition "fails s = (\<exists>n. index s n = Inr Abort \<or> index s n = Inr Incomplete)"

lemma fails_finite[simp, dest]: "fails s \<Longrightarrow> finiteS s"
  apply (clarsimp simp: fails_def)
  by (metis finiteS_def sum.disc(2))

lemma index_tail_append: "lengthS s = Some m \<Longrightarrow> n = m + m' \<Longrightarrow> index (appendS s s') n = index s' m'"
  by (clarsimp simp: index_append)


lemma fails_appendS[simp]: "fails (appendS s s') \<longleftrightarrow> (finiteS s \<and> fails s')"
  apply (safe)
    apply (clarsimp simp: fails_def)
  using fails_def fails_finite finiteS_append_iff apply blast
   apply (clarsimp simp: fails_def)
   apply (metis (no_types, lifting) index_append inf_all_l infinite_appendS_iff isl_coerce isl_iff lengthS_def sum.disc(2))
  apply (clarsimp simp: fails_def)
  apply (cases "lengthS s = None"; clarsimp)
   apply (simp add: finiteS_def)
  using index_tail_append by metis


definition "terminates s = (\<exists>n a. index s n = Inr (Term a))"

lemma finite_fail_or_term[simp, dest]: "finiteS s \<Longrightarrow> terminates s \<noteq> fails s  "
  apply (clarsimp simp: fails_def terminates_def)
  apply (safe; clarsimp?)
    apply (metis isr_antitone nle_le sum.inject(2) term_symbols.distinct(3))
   apply (metis isr_antitone nle_le sum.inject(2) term_symbols.distinct(1))
  by (metis finiteS_def sum.collapse(2) term_symbols.exhaust_sel)



definition "seq_trace t t' = (if terminates t then appendS t t'
                             else fmap_trace id (coerce_sym) t) "


lemma terminates_finite[dest, simp]:"terminates t \<Longrightarrow> finiteS t"
  apply (clarsimp simp: terminates_def)
  by (metis finiteS_def sum.disc(2))

lemma terminates_index: "terminates t \<Longrightarrow> index (seq_trace t t') = index (appendS t t')"
  apply (clarsimp simp: seq_trace_def)
  done

lemma index_fmap_trace: "index (fmap_trace f g t) = map_sum f g o index t"
  by (clarsimp simp: fmap_trace_def)

lemma non_terminates_index: "\<not> terminates t \<Longrightarrow> index (seq_trace t t') = map_sum id coerce_sym o (index t)"
  by (clarsimp simp: seq_trace_def index_fmap_trace)

lemma index_inr_eq:"index t n = Inr a \<Longrightarrow> index t m = Inr b \<Longrightarrow> a = b"
  by (metis isr_antitone linorder_not_less old.sum.inject(2) order.strict_iff_not)


lemma fails_seq: "fails t \<Longrightarrow> seq_trace t t' = t"
  apply (clarsimp simp: seq_trace_def)
  apply (safe; clarsimp?)
   apply blast
  apply (rule trace_eqI, clarsimp simp: index_fmap_trace)
  apply (case_tac "index t n"; clarsimp?)
  apply (clarsimp simp: fails_def)
  using index_inr_eq 
  by fastforce

lemma traceDom_tail[simp, intro]: "s \<in> traceDom \<Longrightarrow> (\<lambda>n. s (n - i)) \<in> traceDom "
  by (clarsimp simp: traceDom_def)



lemma less_length_is_state[dest]:  "lengthS s = Some m \<Longrightarrow> n < m \<Longrightarrow> isState (index s n)"
  using isl_iff by blast


lemma isr_iff: "lengthS t = Some n \<Longrightarrow> \<not>(isl (index t m))\<longleftrightarrow> m \<ge> n"
  by (metis isl_iff verit_comp_simplify1(3))

lemma map_sum_index_l[simp]: " lengthS s = Some m \<Longrightarrow>  n < m \<Longrightarrow> map_sum f g (index s n) =  Inl (f (projl (index s n)))"
  using isl_iff 
  by (metis map_sum.simps(1) sum.collapse(1))


lemma map_sum_index_r[simp]: " lengthS s = Some m \<Longrightarrow>  n \<ge> m \<Longrightarrow> map_sum f g (index s n) =  Inr (g (projr (index s n)))"
  using isl_iff 
  by (metis isl_map_sum leD map_sum_sel(2) sum.collapse(2))


lemma map_sum_index_l'[simp]: " lengthS s = None \<Longrightarrow>   map_sum f g (index s n) =  Inl (f (projl (index s n)))"
  by (metis inf_all_l isl_map_sum map_sum_sel(1) sum.collapse(1))


lemma isState_coerce[simp]: "isState (coerce s) \<longleftrightarrow> isState s " 
  by (case_tac \<open>s\<close>; clarsimp)



lemma coerce_in_traces: "s \<in> traceDom \<Longrightarrow> coerce \<circ> s \<in> traceDom"
  by (clarsimp simp: traceDom_def)

lemma term_index_append': "\<not>finiteS s \<Longrightarrow> index (appendS s s') n = coerce (index s n)" 
  by (clarsimp simp: appendS_def)

lemma coerce_term[simp]: "coerce_sym ( s n) = Term a \<Longrightarrow> \<exists>a'. (s n) = Term a'"
  by (cases \<open>s n\<close>; clarsimp)



lemma terminatesD: "terminates s \<Longrightarrow> \<exists>n a. lengthS s = Some n \<and> index s n = Inr (Term a) "
  apply (clarsimp simp: terminates_def)
  apply (case_tac "lengthS s = None", clarsimp)
   apply (metis inf_all_l sum.disc(2))
  apply (clarsimp)
  apply (rule_tac x=a in exI)
  by (metis isl_iff isr_antitone leD nle_le sum.collapse(2))

lemma terminatesI: "\<exists>i a. index s i = Inr (Term a) \<Longrightarrow> terminates s"
  by (clarsimp simp: terminates_def)

lemma terminates_append[intro, simp]: "terminates s \<Longrightarrow> terminates s' \<Longrightarrow> terminates (appendS s s')"
  apply (rule terminatesI)
    apply (drule terminatesD, clarsimp)
    apply (drule terminatesD, clarsimp)

  apply (simp add: index_append)
  by (rule_tac x="n + na" in exI, clarsimp)
  

lemma terminates_seq[intro, simp]: " terminates (seq_trace s s') \<longleftrightarrow>  terminates s \<and>  terminates s' "
  apply (safe)
    apply (clarsimp simp: seq_trace_def split: if_splits)
    apply (clarsimp simp: terminates_def index_fmap_trace)
    apply (metis coerce_sym.simps(1) coerce_sym.simps(2) isl_map_sum map_sum_sel(2) sum.collapse(2) sum.disc(2) sum.sel(2) term_symbols.exhaust term_symbols.simps(3) term_symbols.simps(5))
   apply (clarsimp simp: seq_trace_def split: if_splits)
    apply (smt (verit, ccfv_threshold) coerce.simps(2) finiteS_def index_append isl_coerce isl_iff lengthS_def sum.collapse(2) terminates_def terminates_finite)
    apply (clarsimp simp: terminates_def index_fmap_trace)
   apply (metis coerce_sym.simps(1) coerce_sym.simps(2) isl_map_sum map_sum_sel(2) sum.collapse(2) sum.disc(2) sum.sel(2) term_symbols.exhaust_sel term_symbols.simps(3) term_symbols.simps(5))
  apply (subst terminates_def)
  apply (subst terminates_index, clarsimp)
  apply (drule terminatesD)+
  apply (clarsimp)
  apply (subst index_append, assumption)

  apply (clarsimp)
  apply (rule_tac x="na + n" in exI)
  by (clarsimp)




definition "terminated c \<longleftrightarrow> (\<exists>a. c = Inr (Term a)) "

(* 
lemma lengthS_le: "(\<And>n.  terminated (index s' n) \<Longrightarrow> terminated (index s n)) ==> terminates s' \<Longrightarrow>   the ( lengthS s) \<le> the ( lengthS s')"
  apply (transfer)
  apply (clarsimp simp:  terminated_def)
  apply (drule terminatesD, clarsimp)
  by (metis inf_all_l isr_iff lengthS_def option.sel sum.disc(2))



lemma lengthS_le': "(\<And>n.  isl (index s n) \<Longrightarrow> isl (index s' n) ) ==> finiteS s' \<Longrightarrow>   the ( lengthS s) \<le> the ( lengthS s')"
  apply (clarsimp simp:  terminated_def)
  by (metis Traces.lengthS_le lengthS_some_finite option.sel)
*)

lemma always_term: " terminated (s n) \<Longrightarrow> s \<in> traceDom \<Longrightarrow> n \<le> n' \<Longrightarrow> terminated (s n')"
  by (fastforce simp: traceDom_def terminated_def)

lemma lengthS_le_append: " terminates s \<Longrightarrow>  terminates s' \<Longrightarrow> the ( lengthS s) \<le> the ( lengthS (seq_trace s s'))"
  apply (rule lengthS_le; clarsimp?)
   apply (clarsimp simp: terminates_index index_append)
  by (metis index_append isl_coerce isl_iff terminatesD)

lemma less_sub_less_plus:"x - y < z \<Longrightarrow> x < y + (z :: nat)"
  by force



lemma lengthS_leI:" finiteS s \<Longrightarrow>  \<not>isl (index s n)   \<Longrightarrow> the ( lengthS s) \<le> n"
  by (metis inf_all_l isr_iff option.collapse)

lemma lengthS_geI:" finiteS s \<Longrightarrow> (\<And>n'. \<not>isl (index s n')  \<Longrightarrow> n' \<ge> n) \<Longrightarrow> the (lengthS s) \<ge> n"
  by (simp add: finiteS_lengthSE)

lemma terminates_at_length: "terminates s' \<Longrightarrow>terminated (index s' (the (lengthS s'))) "
  by (metis option.sel terminated_def terminatesD)

(* lemma traceDom_append_inner[simp]: "s \<in> traceDom \<Longrightarrow> s' \<in> traceDom \<Longrightarrow> (\<lambda>n. if n < the (lengthS s) then coerce (s n) else s' (n - the (lengthS s))) \<in> traceDom"
  apply (clarsimp simp: traceDom_def)
  by (meson less_length_is_state)
*)

lemma coerce_idemp[simp]: "coerce_sym (coerce_sym c) = coerce_sym c"
  by (cases c; clarsimp)

lemma lengthS_append_eq: "terminates s \<Longrightarrow>  terminates s' \<Longrightarrow> the (lengthS (seq_trace s s')) = the ( lengthS s) + the ( lengthS s')"
  by (metis (no_types, opaque_lifting) lengthS_appendI' option.sel seq_trace_def terminatesD)

find_theorems terminates

lemma terminates_coerce_sym[simp]: "terminates (fmap_trace f (coerce_sym) s) = terminates s"
  apply (rule iffI)
  apply (case_tac "lengthS s = None"; clarsimp?)
   apply (drule terminatesD, clarsimp simp: index_fmap_trace)
   apply (drule terminatesD, clarsimp simp: index_fmap_trace)

  apply (rule terminatesI)
  apply (rule_tac x=n in exI)
  apply (metis coerce_sym.simps(1) coerce_sym.simps(2) isl_map_sum map_sum.simps(2) 
            sum.collapse(2) sum.disc(2) sum.sel(2) term_symbols.exhaust_sel term_symbols.simps(3) term_symbols.simps(5))
  apply (drule terminatesD, rule terminatesI, clarsimp simp: index_fmap_trace)
  by (rule_tac x=n in exI, rule_tac x=undefined in exI, clarsimp)

lemma [simp]: "(coerce_sym \<circ> coerce_sym) = coerce_sym"
  by (rule ext; clarsimp)

lemma lengthS_fmap: "lengthS (fmap_trace f g x) = lengthS x"
  by (rule lengthS_eqI; clarsimp simp: index_fmap_trace)

lemma clean_fmap: "clean = fmap_trace id (\<lambda>x. undefined)"
  apply (intro ext trace_eqI; clarsimp simp: index_fmap_trace clean_def)
  by (case_tac "index x n"; clarsimp simp: coerce_def)

lemma fmap_trace_appendS: "fmap_trace f g (appendS x y) = appendS (map_trace f  x) (fmap_trace f g y)"
  using [[show_types]]
  apply (case_tac "lengthS x = None"; clarsimp simp: index_fmap_trace lengthS_fmap)
   apply (rule trace_eqI)
   apply (clarsimp simp: clean_fmap map_sum.compositionality index_fmap_trace index_map_sum)  
  find_theorems index map_trace
  apply (rule trace_eqI)
   apply (clarsimp simp: clean_fmap map_sum.compositionality index_fmap_trace)  
  apply (simp add: index_append lengthS_fmap index_fmap_trace index_map_sum)
  apply (safe)
  by (metis coerce.simps(1) less_length_is_state map_sum.simps(1) sum.collapse(1))

lemma map_trace_id[simp]:"(map_trace id) = id"
  apply (intro ext trace_eqI; clarsimp simp: index_map_sum)
  by (case_tac "index x n"; clarsimp)

lemma seq_traceS_assoc: "seq_trace s (seq_trace s' s'') = seq_trace (seq_trace s s') s''"
  apply (clarsimp simp: seq_trace_def; safe; (clarsimp simp: appendS_assoc)?)
     apply (subst map_sum.compositionality, clarsimp)
    apply (metis seq_trace_def terminates_seq)
  apply (clarsimp simp: fmap_trace_appendS)
  by (subst map_sum.compositionality, clarsimp)


type_synonym ('a, 'config, 'state) stateful =
    "'config \<Rightarrow> 'state \<Rightarrow> ('state , 'a term_symbols) trace"

primrec mapState where
 "mapState f (Incomplete) = Incomplete" |
 "mapState f (Term v) = Term (f v)" | 
 "mapState f (Abort) = Abort" 

definition flatTrace where
 "flatTrace n s prev = (if n = 0 then res (index s 0) prev else
                          (let final = st (index s (n - 1)) in (res (index s n)) final))"

find_consts "('a \<Rightarrow> 'b) \<Rightarrow> 'a option \<Rightarrow>  'b option"

term singleton

abbreviation "constT c == singleton c (Term ())"

term map_add
term "[0 \<mapsto> c]"

notation constT ("\<bar>_\<bar>")

notation seq_trace (infixr \<open>@@\<close> 65)

term "(@)"
term "(!)"
notation index (infixl \<open>^\<close> 100)

thm appendS_def

abbreviation "result \<equiv> res o projr"

definition "coerce_syms \<equiv> (fmap_trace id coerce_sym)"


definition state_bind ::
     "('a, 'config, 'state) stateful \<Rightarrow>
      ('a \<Rightarrow> ('b, 'config, 'state) stateful) \<Rightarrow>
      ('b, 'config, 'state) stateful"
     where
 "state_bind f g \<equiv> 
    \<lambda>config state. let s = f config state in
                           (case (lengthS s) of (Some n) \<Rightarrow>
                             (case (terminates s) of True \<Rightarrow>
                                 let r  = (result (index s n));
                                     s' = g r config (projl (index (\<bar>state\<bar> @@ s)  n)) in (s @@ s') 
                                 | False \<Rightarrow> coerce_syms s) |
                                   None \<Rightarrow> coerce_syms s) "

definition state_compose :: 
     "('a => ('b, 'config, 'state) stateful) \<Rightarrow>
      ('b \<Rightarrow> ('c, 'config, 'state) stateful) \<Rightarrow>
      ('a \<Rightarrow> ('c, 'config, 'state) stateful)"
     where
 "state_compose f g \<equiv> \<lambda>x. state_bind (f x) g" 

adhoc_overloading
 bind state_bind

declare trace_eqI[intro]


lemma nonterm_append_simp[simp]: "\<not>  terminates s \<Longrightarrow> seq_trace s s' = s"
  apply (clarsimp simp: seq_trace_def, rule trace_eqI, clarsimp simp: index_fmap_trace)
  apply (case_tac "(index s  n)"; clarsimp?)
  by (metis coerce_sym.simps(1) coerce_sym.simps(2) term_symbols.exhaust terminatesI)

thm terminates_def
lemma no_length_no_termination:" lengthS c = None \<longleftrightarrow> \<not>  finiteS c " 
  apply (safe; clarsimp?)
   apply (metis lengthS_def option.distinct(1))
  by (metis lengthS_def )

lemma finiteS_append: "finiteS c' \<Longrightarrow> finiteS (c @@ c') \<longleftrightarrow> finiteS c  " 
  apply (intro iffI)
    apply (metis finiteS_def index_fmap_trace isl_map_sum o_apply seq_trace_def terminates_finite)
  apply (clarsimp simp: seq_trace_def split:if_splits)
  apply (clarsimp simp: finiteS_def index_fmap_trace)
  using isl_map_sum by blast
  
lemma singleton_index[simp]:"index (singleton c d) 0 = Inl c"
  by (clarsimp simp: singleton_def)


lemma [simp]:"index (singleton c d) (Suc n) = Inr d"
  by (clarsimp simp: singleton_def)

lemma constT_term[simp]: " terminates (constT c) " 
  by (rule terminatesI, clarsimp, rule_tac x=1 in exI, clarsimp)

lemma constT_length[simp]:"the ( lengthS (constT c)) = 1"
  by (clarsimp simp: lengthS_singleton)

definition "empty_term = empty_trace  (Term ())"

lemma terminates_seq_appendS[simp]:"terminates x \<Longrightarrow> seq_trace x y = appendS x y"
  by (clarsimp simp: seq_trace_def)

lemma empty_append[simp]:  "seq_trace empty_term c = c" 
  apply (clarsimp simp: empty_term_def)
  by (simp add: terminatesI)

lemma state_st_inv[simp]: "isState c \<Longrightarrow> Inl (projl c) = c"
  by (clarsimp)

lemma not_terminated_yet: " lengthS x = Some n \<Longrightarrow> m < n \<Longrightarrow> \<not>terminated (x ^ m)"
  by (metis less_length_is_state sum.disc(2) terminated_def)


lemma no_length_easy_clean[simp]: " lengthS c = None \<Longrightarrow> clean c = c"
  apply (rule trace_eqI; clarsimp?)
  by (metis inf_is_clean)




lemma coerce_clean_index[simp]: "coerce (coerce_syms s ^ n) = coerce (s ^ n)"
  apply (clarsimp simp: coerce_def coerce_syms_def split: sum.splits)

  by (metis Inl_Inr_False comp_apply id_apply index_fmap_trace map_sum.simps(1) map_sum.simps(2) sum.sel(1))


lemma terminates_clean[simp]: " terminates (coerce_syms s) \<longleftrightarrow>  terminates s  "
  by (simp add: coerce_syms_def)

lemma index_coerce_syms: "index (coerce_syms s) = map_sum id coerce_sym o (index s)"
  apply (clarsimp simp: coerce_syms_def)
  by (simp add: index_fmap_trace)

lemma lengthS_coerce_syms[simp]: "lengthS (coerce_syms s) = lengthS s"
  by (rule lengthS_eqI; clarsimp simp: index_coerce_syms)

lemma [simp]: "\<not>terminates s \<Longrightarrow> s @@ s' = coerce_syms s"
  by (clarsimp simp: seq_trace_def coerce_syms_def)

lemma clean_head: "s' = s'' \<Longrightarrow> s @@ s' = (coerce_syms s) @@ s''"
  apply (clarsimp)
  apply (rule trace_eqI)
  apply (case_tac "terminates s")
   apply (clarsimp simp: index_append)
   apply (subgoal_tac "\<exists>n. lengthS s = Some n", clarsimp simp: index_append)
  using terminatesD apply blast
  apply (clarsimp)
  apply (clarsimp simp: coerce_syms_def)
  by (metis seq_traceS_assoc seq_trace_def terminates_seq)


lemma clean_distrib_seq_traceS[simp]: " coerce_syms (s @@ s') =  ( s) @@ (coerce_syms s')" 
  apply (rule trace_eqI)
  apply (case_tac "terminates s"; clarsimp simp: index_coerce_syms index_clean)
   apply (drule terminatesD; clarsimp simp: index_append index_coerce_syms)
   apply (smt (verit) coerce.simps(1) id_apply isl_iff map_sum.simps(1) sum.collapse(1))
  by (smt (verit) coerce_idemp id_apply isl_map_sum map_sum_sel(1)
                  map_sum_sel(2) sum.collapse(2) sum.disc(2) sum.exhaust_sel)


lemma clean_distrib_appendS[simp]: " terminates s \<Longrightarrow> coerce_syms (appendS s s') =  appendS ( s) (coerce_syms s')" 
  apply (rule trace_eqI)
  apply (clarsimp simp: index_coerce_syms index_clean)
   apply (drule terminatesD; clarsimp simp: index_append index_coerce_syms)
  by (smt (verit) coerce.simps(1) id_apply isl_iff map_sum.simps(1) sum.collapse(1))


lemma coerce_syms_idemp[simp]:"coerce_syms x = coerce_syms (coerce_syms x)"
  by (clarsimp simp: coerce_syms_def map_sum.compositionality)

lemma seq_trace_cong: "t = t' \<Longrightarrow> s = s' \<Longrightarrow> t @@ s = t' @@ s'" by (erule (1) arg_cong2)

lemma terminates_tail[simp] :"terminates s \<Longrightarrow> terminates (appendS s s') = terminates s'"
  apply (safe)
  apply (drule terminatesD, drule terminatesD, clarsimp, rule terminatesI)
   apply (metis index_tail_append lengthS_appendD)
  by blast


lemma state_compose_assoc:
 "state_compose f (state_compose g h) = state_compose (state_compose f g) h"
  apply (rule ext; clarsimp simp: state_compose_def) 
  apply (rule ext)+
  apply (clarsimp simp: state_bind_def Let_unfold lengthS_singleton appendS_assoc infinite_appendS_iff Traces.lengthS_append_eq split: option.splits prod.splits bool.splits)
   apply (clarsimp simp: appendS_assoc index_append lengthS_singleton Traces.lengthS_append_eq linorder_not_less)
  by (smt (verit) Suc_pred coerce.simps(1) isl_iff lessI sum.collapse(1) sum.sel(1))


definition "termS c = empty_trace (Term c)"

definition return :: "'a \<Rightarrow> ('a, 'config, 'state) stateful" where
  "return a \<equiv> \<lambda>config state. (termS a)"

lemma lengthS_emptyS[simp]: " lengthS empty_term = Some 0"
  by (clarsimp simp: empty_term_def)


lemma terminates_termS[simp]: "terminates (termS c)"
  by (rule terminatesI, clarsimp simp: termS_def)

lemma length_const[simp]: " lengthS (termS x) = Some 0" 
  by (clarsimp simp: termS_def)


lemma constS_append[simp]: "termS x @@ s = s" 
  by (rule trace_eqI, clarsimp)
  find_theorems index seq_trace
  apply (clarsimp simp: termS_def)
  apply (subst term_index_append)
   defer
   apply (clarsimp)
  apply (clarsimp simp: constS_def, transfer)
  by (simp add: terminates_def traceDom_def)

lemma constS_append'[simp]: "s @@ termS x = s"
  oops
  apply (case_tac "terminates s")

  apply (rule trace_eqI, clarsimp)
  apply (case_tac "pred terminates s")
  apply (subst term_index_append, clarsimp)
   apply (clarsimp)
  apply (clarsimp simp: constS_def, transfer)
   apply (simp add: terminates_def traceDom_def)
   apply (clarsimp)
  oops
  

lemma index_left_append_zero[simp]: "index (appendS \<bar>x\<bar> xs) 0 = Inl x"
  by (simp add: index_append lengthS_singleton)


lemma index_right_append_suc[simp]: "index (appendS \<bar>x\<bar> xs) (Suc n) = index (xs) (n)"
  by (simp add: index_append lengthS_singleton)

lemma index_constS[simp]:  "(termS x) ^ n = Inr (Term x)" 
  by (clarsimp simp: termS_def)


lemma return_left: "state_compose return f = f"
  apply (intro ext)
  apply (clarsimp simp: state_compose_def)
  apply ( clarsimp simp: state_compose_def state_bind_def  split: prod.splits option.splits)
  by (clarsimp simp: return_def Let_unfold split: option.splits)


lemma index_eq_after_finish: " lengthS s = Some i \<Longrightarrow> i \<le> m \<Longrightarrow> i \<le> n \<Longrightarrow>  (index s n) = s ^ m"
  by (metis index_eq_finished isr_iff order_refl)

lemma coerce_inf[simp]: "lengthS t = None \<Longrightarrow> coerce_syms t = t"
  by (metis coerce_syms_def is_none_code(2) is_none_simps(1) nonterm_append_simp seq_trace_def terminatesD)

lemma coerce_syms_failed[simp]: "fails t \<Longrightarrow> coerce_syms t = t"
  by (metis clean_distrib_seq_traceS fails_seq)

lemma return_right: "state_compose f return = f" 
  apply (intro ext)
  apply (clarsimp simp: state_compose_def)
  apply ( clarsimp simp: state_compose_def state_bind_def Let_unfold  split: prod.splits option.splits bool.splits)
  apply (clarsimp simp: return_def, safe) 
   apply (rule trace_eqI; clarsimp simp: index_append linorder_not_less)
   apply (metis isr_antitone option.sel sum.sel(2) term_symbols.collapse term_symbols.discI terminatesD)
  using coerce_syms_failed lengthS_some_finite by blast


lemma return_bind_l: "(return x \<bind> f) = f x"
  apply (intro ext)
  apply ( clarsimp simp: state_compose_def state_bind_def  split: prod.splits option.splits)
  by (clarsimp simp: return_def  Let_unfold split: option.splits)

lemma return_bind: "(f x \<bind> return) = f x"
  apply (insert return_right[where f=f], clarsimp simp: state_compose_def) 
  by (drule_tac x=x in fun_cong, clarsimp)

definition "abortS \<equiv> empty_trace Abort" 

lemma nonterm_aborts: "fails abortS"
  by (clarsimp simp: fails_def abortS_def)

lemma infinite_appendS: "\<not> finiteS c \<Longrightarrow> c @@ d = c"
  using nonterm_append_simp terminates_finite by blast

definition config :: "('config, 'config, 'state) stateful" where
 "config \<equiv> \<lambda>config state. return config config state"

definition getState :: "('state, 'config, 'state) stateful" where
 "getState \<equiv> \<lambda>config state. return state config state "

definition setState :: "'state \<Rightarrow> (unit, 'config, 'state) stateful" where
 "setState s \<equiv> \<lambda>config state. \<bar>s\<bar> "

definition modifyState :: "('state \<Rightarrow> 'state) \<Rightarrow> (unit, 'config, 'state) stateful" where
 "modifyState f \<equiv> do {s <- getState; setState (f s)} "

definition flag :: "bool \<Rightarrow> (unit, 'config, 'state) stateful" where
 "flag b \<equiv> \<lambda>config state. if b then empty_term else abortS "

definition assert :: "('state \<Rightarrow> bool) \<Rightarrow> (unit, 'config, 'state) stateful" where
  "assert P = do {s <- getState;
                     flag (P s)} "

definition fail :: "(unit, 'config, 'state) stateful" where
  "fail = assert (\<lambda>_. False) "


definition liftM :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'config, 'state) stateful \<Rightarrow> ('b, 'config, 'state) stateful " where
  "liftM f m = do {x <- m; return (f x)} "


definition foldrM :: "('a \<Rightarrow> 'b \<Rightarrow> ('b , 'config, 'state) stateful) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> ('b , 'config, 'state) stateful " where
  "foldrM f xs = foldr (state_compose) (map f xs) (return)"

definition mapM :: "('a \<Rightarrow> ('b , 'config, 'state) stateful) \<Rightarrow> 'a list \<Rightarrow> ('b list, 'config, 'state) stateful" where
  "mapM f xs = foldrM (\<lambda>a xs. do { x <- f a ; return (x#xs)}) xs []" 

lemma getState_bind_simp: "getState \<bind> P = (\<lambda>config state. P state config state)"
  apply (intro ext)
  apply (clarsimp simp: getState_def state_bind_def Let_unfold split: option.splits, intro conjI impI allI; clarsimp?)
   apply (clarsimp simp: return_def)
  by (clarsimp simp: return_def)

lemma fail_absorb: "fail \<bind> f = fail"
  apply (clarsimp simp: fail_def assert_def getState_bind_simp)
  apply (intro ext)
  apply (clarsimp simp: state_bind_def Let_unfold flag_def split: bool.splits option.splits)
  apply (safe; clarsimp?)
  using nonterm_aborts apply blast
  by (simp add: nonterm_aborts)


primrec iterateM :: "('a \<Rightarrow> ('a, 'config, 'state) stateful) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'config \<Rightarrow> 'state \<Rightarrow>  ('state , 'a term_symbols) trace"
  where "iterateM f 0 a cf state  = f a cf state" |
        "iterateM f (Suc n) a cf state = (state_bind (iterateM f (n) a) f) cf state"

definition "fixP (f :: (nat \<Rightarrow> ('state , 'a term_symbols) trace)) = f (SOME n. f n = f (Suc n))"

definition flatten :: "(nat \<Rightarrow> ('state , 'a term_symbols) trace) \<Rightarrow> nat \<Rightarrow> ('a, 'state) State"
  where "flatten f i \<equiv> if (\<exists>n. f n = f (Suc n)) 
             then index ( fixP f) i else
             (if (\<exists>n. isState (index (f n) i)) then  
                  index (f (SOME n. isState (index (f n) i))) i else
               Inr Incomplete) "


lemma fixP_iter_return: "fixP (\<lambda>n. iterateM return n a cf state) = return a cf state"
  apply (clarsimp simp: fixP_def)
  apply (rule someI2[where a=0])
   apply (clarsimp)
   apply (clarsimp simp: return_bind)
  apply (clarsimp simp: return_bind)
  by (induct_tac x; clarsimp simp: return_bind)

lemma someI_ex_eq: "\<exists>a. P a \<Longrightarrow> (\<And>b. (SOME a. P a) = b  \<Longrightarrow> P b \<Longrightarrow> Q b) \<Longrightarrow> Q (SOME a. P a)"
  by (simp add: verit_sko_ex)


lemma "a = a @@ b \<Longrightarrow>  terminates a \<Longrightarrow>  \<exists>c. b = termS c "
  apply (rule_tac x="(res o projr o index b) 0" in exI)
  apply (rule trace_eqI)
  apply (clarsimp)
  apply (drule terminatesD, clarsimp)
  apply (drule_tac n="na" in index_cong, clarsimp simp: index_append)
  by blast


lemma index_eq_after_term: "j \<le> i \<Longrightarrow> \<not>isState (index s j) \<Longrightarrow> index s j = index s i"
  apply (transfer)
  by (clarsimp simp: traceDom_def)


lemma flatten_wf: "flatten (\<lambda>n. iterateM f n a cf state) \<in> traceDom"
  apply (clarsimp simp: traceDom_def)
  apply (clarsimp simp: flatten_def)
  apply (intro conjI impI allI; clarsimp)
   apply (rule sym, rule index_eq_after_term, assumption, assumption)
       apply (meson some_eq_imp)
      apply (metis index_eq_after_term)
     apply (erule_tac x=n in allE)
  apply (metis index_eq_after_term)
    apply (smt (verit, best) index_eq_after_term)
   apply (meson tfl_some)
  using index_eq_after_term by fastforce

definition "fixM f a \<equiv> \<lambda>config state. liftF (flatten (\<lambda>n. iterateM f n a config state))"

lemma index_fixM: "index (fixM f a conf st) n = flatten (\<lambda>n. iterateM f n a conf st) n "
  by (clarsimp simp: fixM_def flatten_wf)

definition "whileM f P a \<equiv> fixM (\<lambda>a. do {b <- P a; if b then f a else return a}) a"

term iterateM

lemma index_iterateM_zero: "index (iterateM f 0 a cf st) n = index (f a cf st) n"
  by (clarsimp)

lemma lengthS_append_singleton[simp]: "lengthS x = Some n \<Longrightarrow> lengthS (appendS \<bar>st\<bar> x) = Some (Suc n)"
  by (simp add: lengthS_appendI' lengthS_singleton)

definition "the_result t \<equiv>  (result o index t o the o lengthS) t"

declare lengthS_singleton[simp]

lemma state_bind_is_appendS[simp]: "terminates (f cf st) \<Longrightarrow> ((state_bind f g) cf st) = appendS (f cf st) (g (the_result (f cf st)) cf (the (last (appendS \<bar>st\<bar> (f cf st)))) )  "
  apply (clarsimp simp: state_bind_def the_result_def Let_unfold split: option.splits)
  apply (safe)
   apply (drule terminatesD, clarsimp)
  apply (clarsimp simp: last_def index_append isl_iff)
  by (simp add: isl_iff sum.case_eq_if)

lemma state_bind_nonterminating: "\<not>terminates (f cf st) \<Longrightarrow> ((state_bind f g) cf st) = coerce_syms (f cf st)  "
  by (clarsimp simp: state_bind_def Let_unfold split: option.splits)

lemma index_iterateM_Suc: "index (iterateM f (Suc n) a cf st) n = index ((iterateM f n a \<bind> f) cf st) n"
  by (clarsimp)


lemma non_terminating_coerce_syms: "\<not>terminates t \<Longrightarrow> coerce_syms t = t"
  using coerce_inf coerce_syms_failed no_length_no_termination by blast

lemma induct_iterateM: "P (f a cf st) \<Longrightarrow> (\<And>n. terminates (iterateM f n a cf st) \<Longrightarrow> P (iterateM f (Suc n) a cf st)) \<Longrightarrow> (\<And>n. \<not> terminates (iterateM f n a cf st) \<Longrightarrow> P (iterateM f n a cf st)) \<Longrightarrow> P (iterateM f n a cf st)"
  apply (induct n; clarsimp)
  apply (case_tac "terminates (iterateM f n a cf st)", clarsimp)
  by (clarsimp simp: state_bind_nonterminating non_terminating_coerce_syms)

lemma one_iter_fixp:"(iterateM f n a \<bind> f) cf st = iterateM f n a cf st \<Longrightarrow> iterateM f m a cf st = (iterateM f m a \<bind> f) cf st \<Longrightarrow> iterateM f m a cf st = iterateM f n a cf st"
 apply (subgoal_tac "n \<le> m \<or> m \<le> n", elim disjE; clarsimp)
   apply (rule nat_induct_at_least, assumption)
    apply (clarsimp)
   apply (clarsimp)+
   apply (metis state_bind_is_appendS state_bind_nonterminating)
   apply (rule nat_induct_at_least, assumption)
   apply (clarsimp)
  apply (clarsimp)
  by (metis state_bind_is_appendS state_bind_nonterminating)

lemma fixP_iterateM: "(state_bind (iterateM f n a) f) cf st = (iterateM f n a cf st) \<Longrightarrow>  
     fixP (\<lambda>n. iterateM f n a cf st) = (iterateM f n a cf st) "
  apply (clarsimp simp: fixP_def)
  apply (rule someI2[where Q="\<lambda>m. iterateM f m a cf st = iterateM f n a cf st"] )
   apply (erule sym)
  apply (subgoal_tac "n \<le> na \<or> na \<le> n", elim disjE; clarsimp)
  defer
   apply (rule nat_induct_at_least, assumption)
    apply (clarsimp)
   apply (clarsimp)+
   apply (metis state_bind_is_appendS state_bind_nonterminating)
   apply (rule nat_induct_at_least, assumption)
   apply (clarsimp)
  apply (clarsimp)
  by (metis state_bind_is_appendS state_bind_nonterminating)

lemma iterateM_zero_simp[simp]: "iterateM f 0 a = f a"
  by (intro ext; clarsimp)

lemma iterateM_Suc_simp[simp]: "iterateM f (Suc n) a = (iterateM f (n) a \<bind> f)"
  by (intro ext; clarsimp)

lemma iterateM_zero_bind[simp]: "(iterateM f 0 a \<bind> f) = (f a \<bind> f)"
  by (intro ext, clarsimp simp: state_bind_def)

lemma fixM_is_iter_fixp: "(iterateM f n a \<bind> f) = iterateM f n a \<Longrightarrow> fixM f a = iterateM f n a "
  apply (intro ext)
  apply (rule trace_eqI)
  apply (clarsimp simp: index_fixM flatten_def, safe)
     apply (subst fixP_iterateM, erule sym)
     apply (metis (mono_tags, lifting) one_iter_fixp )
    apply (erule_tac x=n in allE, clarsimp)
   apply (subst fixP_iterateM, erule sym)
     apply (metis (mono_tags, lifting) one_iter_fixp )
    apply (erule_tac x=n in allE)
    apply (erule_tac x=n in allE, clarsimp)
  done

definition "measureM r f \<equiv> f = (do { assert (fst r); x <- f ; assert (snd r x); return x})" 

lemma terminates_fixP: "terminates (fixM f a cf st) \<Longrightarrow> \<exists>n. (iterateM f n a \<bind> f) cf st = (iterateM f n a) cf st"
  apply (clarsimp simp: terminates_def index_fixM flatten_def split:if_splits)
   apply (elim disjE; clarsimp)
     apply (metis (no_types, lifting) some_eq_imp sum.disc(2))
    apply (rule_tac x=nb in exI, clarsimp)
     apply (metis (no_types, lifting) some_eq_imp sum.disc(2))
  apply (elim disjE; clarsimp)
  by (rule_tac x=na in exI, clarsimp)


lemma "whileM f (\<lambda>_. return False) a = return a" 
  apply (clarsimp simp: whileM_def)
  apply (clarsimp simp: return_bind_l)
  apply (subst fixM_is_iter_fixp[where n=0], clarsimp)
   apply (simp add: return_bind_l)
  apply (clarsimp)
  done

lemma "fixM (return) a = return a"
  apply (intro ext)
  apply (clarsimp simp: return_def constS_def)
  apply (rule trace_eqI, clarsimp simp: index_fixM)
   apply (clarsimp simp: flatten_def, intro conjI impI; clarsimp?)
    apply (clarsimp simp: return_bind)
    apply (clarsimp simp: fixP_iter_return)
    apply (simp add: return_def)
     apply (clarsimp simp: return_bind)+
    apply (clarsimp simp: fixP_iter_return)
    apply (clarsimp simp: return_def)
   apply (rule_tac x=0 in exI, clarsimp)
     apply (clarsimp simp: return_bind)+
  done

datatype ('state, 'a) result = Result (st: 'state) (val: 'a) | Nonterm | Undefined

thm le_fun_def

term top


class bounded_order = order_bot + order_top +
  assumes two_points: "bot \<noteq> top"
begin

lemma top_le_bot: "top \<le> bot \<Longrightarrow> False"
  using local.bot_unique local.two_points by auto

end


instantiation sum :: (type, bounded_order) order begin

fun less_eq_sum :: "'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> bool" where
 "less_eq_sum (Inl a) (Inl b) =  (a = b)"   |
 "less_eq_sum (Inr a) (Inl b) =  (a = bot)" |
 "less_eq_sum (Inl a) (Inr b) =  (b = top)" |
 "less_eq_sum (Inr a) (Inr b) =  (a \<le> b)"


definition
  "(f:: 'a + 'b) < g \<longleftrightarrow> f \<le> g \<and> \<not> (g \<le> f)"

instance
  apply (intro_classes; (clarsimp simp: less_sum_def split: sum.splits)?)
    apply (case_tac x; clarsimp)
    apply (case_tac x; case_tac y; case_tac z; clarsimp)
       apply force
      apply (metis two_points)
     apply (simp add: top.extremum_unique bot.extremum_unique)+
  apply (case_tac x; case_tac y; clarsimp)
      apply (metis two_points)
      apply (metis two_points)
  done
end



instantiation trace :: (order, bounded_order) order begin

definition less_eq_trace :: "('a, 'b) trace \<Rightarrow> ('a, 'b) trace \<Rightarrow> bool"  where
 "less_eq_trace t t' \<equiv> \<forall>n. index t n \<le> index t' n"


definition
  "(f:: ('a, 'b) trace) < g \<longleftrightarrow> f \<le> g \<and> \<not> (g \<le> f)"


instance
  apply (intro_classes; (clarsimp simp: less_trace_def less_eq_trace_def split: sum.splits)?)
   apply (erule_tac x=n in allE)
  apply (erule_tac x=n in allE)
   apply force
  apply (rule trace_eqI)
  apply (erule_tac x=n in allE)
  apply (erule_tac x=n in allE)
  apply force
  done
end


instantiation  result :: (type, type) order begin
fun less_eq_result where
 "less_eq_result _ Undefined = True" |
 "less_eq_result Undefined r = (if r = Undefined then True else False)" |
 "less_eq_result r Nonterm = (if r = Nonterm then True else False)" |
 "less_eq_result Nonterm r = True" |
 "less_eq_result (Result s r) (Result s' r') =  (s = s' \<and> r = r')"

definition
  "(f:: ('a, 'b) result) < g \<longleftrightarrow> f \<le> g \<and> \<not> (g \<le> f)"
instance 
  apply (intro_classes; case_tac x;  clarsimp simp: less_result_def split: result.splits)
       apply (case_tac y; clarsimp)
       apply (case_tac z; clarsimp)
apply (case_tac y; clarsimp)
       apply (case_tac z; clarsimp)
      apply (case_tac z; clarsimp)
apply (case_tac y; clarsimp)
apply (case_tac y; clarsimp)
apply (case_tac y; clarsimp)
apply (case_tac y; clarsimp)
  done
end


fun trace_to_result :: "'a term_symbols \<Rightarrow> ('state, 'a) result"
  where "trace_to_result (term_symbols.Abort)      = (Undefined :: ('state, 'a) result)" |
        "trace_to_result (term_symbols.Incomplete) = (Nonterm :: ('state, 'a) result)"

definition "eval t \<equiv> (case lengthS t of Some (Suc n) \<Rightarrow> 
                       (case terminates t of True \<Rightarrow> Result (projl (index t n)) (res (projr (index t (Suc n)))) |
                             False \<Rightarrow> trace_to_result (projr (index t (Suc n)))) |
                        None \<Rightarrow> Undefined)"     


definition evaluate :: "'config \<Rightarrow> ('a, 'config, 'state) stateful \<Rightarrow>  ('state 'a result) set "
  where "evaluate cfg f  \<equiv>
           {(s, s'). s' = eval (f cfg s)}"

definition "downcl S = {x. \<exists>y\<in>S. x \<le> y}"

definition "refinement_order f g \<equiv> downcl f <= downcl g"

definition seq_result where
 "('state \<times> ('state,  'a) result)"
 "seq_result Undefined r = Undefined" |
 "seq_result Nonterm r = Nonterm" |
 "seq_result (Result v r) s = (if r = s then r' else Nonterm)"
print_theorems

lemma "seq_result Nonterm r = Nonterm"


definition "hoare_triple pre f post \<longleftrightarrow> refinement_order (pre ; f) post"dfrgcv  


end


