theory Trace_Monads
imports Main  "HOL-Library.Monad_Syntax"
begin


datatype  ('a, 'state) State =  State (st: 'state) | Term (res: 'a) | Incomplete | Abort

primrec isState where
 "isState (Term _) = False" | 
 "isState (State s) = True" |
 "isState (Abort ) = False" |
 "isState (Incomplete) = False"



definition "traceDom \<equiv> {(f). \<forall> (i :: nat) j. j \<le> i \<longrightarrow> \<not>(isState (f j)) \<longrightarrow> f i = f j}"

typedef ('a, 'state) trace = "traceDom :: (nat \<Rightarrow> ('a, 'state) State) set"
  apply (rule_tac x="\<lambda>_. Term undefined" in exI)
  apply (clarsimp simp: traceDom_def)
  done

setup_lifting type_definition_trace     
(* datatype ('a, 'state) stateS =
   Empty | Next (hd : "'state") (tl: "unit \<Rightarrow> ('a, 'state) stateS") | Abort |
   Result (res : "'a") *)

lift_definition index :: " ('a, 'state) trace \<Rightarrow> nat \<Rightarrow>  ('a, 'state) State" is "\<lambda>f n. f n" done

primrec iterate where
  "iterate x f 0       = x" |
  "iterate x f (Suc n) = f (iterate x f n)" 

definition "finiteS f \<equiv> \<exists>n. \<not>isState (index f n)"

lift_definition pred :: "((nat \<Rightarrow>  ('a, 'state) State) \<Rightarrow> 'b) \<Rightarrow> ( ('a, 'state) trace \<Rightarrow> 'b)" is "\<lambda>P f. P f"
  done

definition "terminates \<equiv> \<lambda>f. \<exists>n c . ( f n) = Term c "


definition lengthS where "lengthS \<equiv> \<lambda>f. if (\<exists>n. \<not>isState (f n)) then Some (LEAST n. \<not>isState (f n)) else None"

lift_definition liftF :: "(nat \<Rightarrow>  ('a, 'state) State) \<Rightarrow>  ('a, 'state) trace " is
 "\<lambda>f. if f \<in> traceDom then f else (\<lambda>_. Incomplete)" 
  by (clarsimp simp: traceDom_def)

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

thm traceDom_antimono[OF contrapos_np]

lemma antimono_less[simp, intro]: "antimono (\<lambda>n. n < x)"
  apply (clarsimp simp: antimono_def, rule monotoneI)
  by auto

primrec coerce where
  "coerce Abort = Abort" |
  "coerce (State s) = State s" |
  "coerce Incomplete = Incomplete" |
  "coerce (Term _) = Term undefined" 




definition appendS :: " ('a, 'state) trace \<Rightarrow>  ('b, 'state) trace \<Rightarrow>  ('b, 'state) trace"
  where "appendS s s' \<equiv> 
   if pred terminates s then
       liftF (\<lambda>n. if (n < the (pred lengthS s)) then coerce (index s n) else index s' (n - (the (pred lengthS s))))
                        else
       liftF (coerce o index s)"


lemma traceDom_tail[simp, intro]: "s \<in> traceDom \<Longrightarrow> (\<lambda>n. s (n - i)) \<in> traceDom "
  by (clarsimp simp: traceDom_def)

lemma traceDom_append[simp]: " s' \<in> traceDom \<Longrightarrow> (\<lambda>n. if (n < the ( lengthS s)) then s n else  s' (n - (the ( lengthS s)))) \<in> traceDom"
  apply (rule ccontr, drule traceDom_antimono')
    apply blast
   apply (clarsimp simp: lengthS_def)
  apply (metis (mono_tags, lifting) not_less_Least option.sel)
  apply (clarsimp)
  done


lemma less_length_is_state[dest]:  "n < the (lengthS (s' :: nat \<Rightarrow>  ('a, 'state) State)) \<Longrightarrow> isState (s' n)"
  apply (clarsimp simp: lengthS_def)
  by (metis (mono_tags, lifting) not_less_Least option.sel)


lemma trace_eqI: "(\<And>n. index s n = index s' n) \<Longrightarrow> s = s'"
  by (transfer, rule ext, clarsimp)

lemma coerce_eq[simp]: "s \<in> traceDom \<Longrightarrow> n < the (lengthS s) \<Longrightarrow> coerce (s n) = s n"
  apply (case_tac "s n"; clarsimp)
  by auto

lemma isState_coerce[simp]: "isState (coerce s) \<longleftrightarrow> isState s " 
  by (case_tac \<open>s\<close>; clarsimp)

lemma term_index_append: "pred terminates s \<Longrightarrow> index (appendS s s') n = (if (n < (the o pred lengthS) s) then coerce (index s n) else index s' (n - (the (pred lengthS s))))" 
  apply (clarsimp, intro conjI impI, clarsimp simp: appendS_def)
   apply (transfer, clarsimp)
   apply (erule contrapos_np)
   apply (clarsimp simp: traceDom_def)
  apply blast
  apply (clarsimp simp: appendS_def, transfer, clarsimp)
   apply (erule contrapos_np) back
  apply (clarsimp simp: traceDom_def split: if_splits)
  apply blast
  done


lemma coerce_in_traces: "s \<in> traceDom \<Longrightarrow> coerce \<circ> s \<in> traceDom"
  by (clarsimp simp: traceDom_def)

lemma term_index_append': "\<not>pred terminates s \<Longrightarrow> index (appendS s s') n = coerce (index s n)" 
  apply (clarsimp simp: appendS_def)
  by (transfer, clarsimp simp: coerce_in_traces)

lemma coerce_term[simp]: "coerce (s n) = Term a \<Longrightarrow> \<exists>a'. (s n) = Term a'"
  by (cases \<open>s n\<close>; clarsimp)

lemma "s \<in> traceDom \<Longrightarrow> s' \<in> traceDom \<Longrightarrow> (\<lambda>n. if n < the (lengthS s) then coerce (s n) else s' (n - the (lengthS s))) \<in> traceDom"
  apply (clarsimp simp: traceDom_def)


  

lemma terminates_append[intro, simp]: "pred terminates (appendS s s') \<longleftrightarrow> pred terminates s \<and> pred terminates s' "
  apply (clarsimp simp: appendS_def, transfer, clarsimp simp: terminates_def)
  apply (safe; clarsimp?)
             apply blast
  apply (metis coerce_term isState.simps(1) less_length_is_state)
           apply (metis coerce_term isState.simps(1) less_length_is_state)
          apply (metis add_diff_cancel_right' not_add_less2)
         apply (meson coerce_term)
  
        apply blast
  using coerce_term apply fastforce
  using coerce_term apply fastforce
  using coerce_term apply fastforce
    apply (erule notE)
    apply (clarsimp simp: traceDom_def)
    apply (smt (z3) State.exhaust coerce.simps(1) coerce.simps(2) coerce.simps(3) coerce.simps(4) isState.simps(1) less_length_is_state nle_le)
   apply (metis State.exhaust State.simps(10) State.simps(12) State.simps(4) coerce.simps(1) coerce.simps(2) coerce.simps(3))
  by (clarsimp simp: coerce_in_traces)



definition "terminated c \<longleftrightarrow> (\<exists>a. c = Term a) "


lemma lengthS_le: "(\<And>n.  terminated (index s' n) \<Longrightarrow> terminated (index s n)) ==> pred terminates s' \<Longrightarrow>   the (pred lengthS s) \<le> the (pred lengthS s')"
  apply (transfer)
  apply (clarsimp simp: lengthS_def terminated_def)
  apply (intro conjI impI; clarsimp?)
  apply (rule Least_le)
    apply (smt (z3) LeastI isState.simps(1) mem_Collect_eq nle_le terminates_def traceDom_def)
  apply (rule Least_le)
   apply (smt (z3) LeastI isState.simps(1) mem_Collect_eq nle_le terminates_def traceDom_def)
  apply (smt (z3) LeastI isState.simps(1) mem_Collect_eq nle_le terminates_def traceDom_def)
  done

lemma always_term: " terminated (s n) \<Longrightarrow> s \<in> traceDom \<Longrightarrow> n \<le> n' \<Longrightarrow> terminated (s n')"
  by (fastforce simp: traceDom_def terminated_def)

lemma lengthS_le_append: "pred terminates s \<Longrightarrow> pred terminates s' \<Longrightarrow> the (pred lengthS s) \<le> the (pred lengthS (appendS s s'))"
  apply (rule lengthS_le; clarsimp?)
  apply (subst (asm) term_index_append)
  thm term_index_append
  apply (clarsimp simp: term_index_append split: if_splits)
  apply (transfer, clarsimp)
  apply (clarsimp simp: terminates_def lengthS_def terminated_def)
  apply (clarsimp split: if_splits)
  by (smt (z3) LeastI isState.simps(1) linorder_not_less mem_Collect_eq nle_le traceDom_def)+


lemma less_sub_less_plus:"x - y < z \<Longrightarrow> x < y + (z :: nat)"
  by force
  
lemma lengthS_leI:" pred terminates s \<Longrightarrow>  terminated(index s n)   \<Longrightarrow> the (pred lengthS s) \<le> n"
  apply (transfer)
  apply (clarsimp simp: terminates_def lengthS_def terminated_def)
  by (metis Least_le isState.simps(1) linorder_le_cases)

lemma lengthS_geI:" pred terminates s \<Longrightarrow> (\<And>n'. terminated (index s n')  \<Longrightarrow> n' \<ge> n) \<Longrightarrow> the (pred lengthS s) \<ge> n"
  apply (transfer)
  apply (clarsimp simp: terminates_def lengthS_def terminated_def)
  by (metis (mono_tags, lifting) LeastI isState.simps(1) linorder_le_cases mem_Collect_eq traceDom_def)

lemma terminates_at_length: "s' \<in> traceDom \<Longrightarrow> terminates s' \<Longrightarrow>terminated (s' (the (lengthS s'))) "
  apply (clarsimp simp: lengthS_def terminated_def)
  by (smt (verit) LeastI2 isState.simps(1) mem_Collect_eq nle_le terminates_def traceDom_def)

lemma traceDom_append_inner[simp]: "s \<in> traceDom \<Longrightarrow> s' \<in> traceDom \<Longrightarrow> (\<lambda>n. if n < the (lengthS s) then coerce (s n) else s' (n - the (lengthS s))) \<in> traceDom"
  apply (clarsimp simp: traceDom_def)
  by (meson less_length_is_state)

lemma coerce_idemp[simp]: "coerce (coerce c) = coerce c"
  by (cases c; clarsimp)

lemma lengthS_append_eq: " pred terminates s \<Longrightarrow> pred terminates s' \<Longrightarrow> the (pred lengthS (appendS s s')) = the (pred lengthS s) + the (pred lengthS s')"
  apply (rule antisym)
  apply (rule lengthS_leI, clarsimp)
  apply (clarsimp simp: appendS_def, transfer)
   apply (clarsimp)
   apply (clarsimp simp: terminates_at_length)
  apply (rule lengthS_geI, clarsimp)
  apply (clarsimp simp: term_index_append split: if_splits)
   apply (transfer, clarsimp simp: lengthS_def terminated_def split: if_splits)
  apply (metis State.exhaust State.simps(10) State.simps(12) coerce.simps(1) coerce.simps(2) coerce.simps(3) isState.simps(1) isState.simps(2) not_less_Least)
   apply (transfer, clarsimp simp: lengthS_def terminated_def)
  apply (metis (no_types, lifting) isState.simps(1) terminates_def)
  by (metis le_add_diff_inverse lengthS_leI linorder_le_less_linear nat_add_left_cancel_le)

lemma appendS_assoc: "appendS s (appendS s' s'') = appendS (appendS s s') s''"
  apply (rule trace_eqI)
  apply (case_tac "pred terminates s"; case_tac "pred terminates s'"; (clarsimp simp: term_index_append)?)
     apply (intro conjI impI; (clarsimp simp: lengthS_append_eq)?)
  using lengthS_le_append  apply force
  using less_sub_less_plus lengthS_le_append 
     apply (simp add: lengthS_append_eq)
  using [[show_types]]

    apply (intro conjI impI)
  by (clarsimp simp: term_index_append' term_index_append)+

  


type_synonym ('a, 'config, 'state) stateful =
    "'config \<Rightarrow> 'state \<Rightarrow> ('a , 'state) trace"

primrec mapState where
 "mapState f (Incomplete) = Incomplete" |
 "mapState f (Term v) = Term (f v)" | 
 "mapState f (Abort) = Abort" |
 "mapState f (State s) = (State s)"

definition flatTrace where
 "flatTrace n s prev = (if n = 0 then res (index s 0) prev else
                          (let final = st (index s (n - 1)) in (res (index s n)) final))"

find_consts "('a \<Rightarrow> 'b) \<Rightarrow> 'a option \<Rightarrow>  'b option"

definition "constT c = liftF (\<lambda>n. if n = 0 then State c else Term ())"

notation constT ("[[_]]")

notation appendS (infixr \<open>@@\<close> 65)

term "(@)"
term "(!)"
notation index (infixl \<open>^\<close> 100)

thm appendS_def

definition state_bind ::
     "('a, 'config, 'state) stateful \<Rightarrow>
      ('a \<Rightarrow> ('b, 'config, 'state) stateful) \<Rightarrow>
      ('b, 'config, 'state) stateful"
     where
 "state_bind f g \<equiv> 
    \<lambda>config state. let s = f config state in
                           (case (pred lengthS s) of (Some n) \<Rightarrow>
                                 let s' = g (res (index s n)) config (st (index ([[state]] @@ s)  n)) in (s @@ s') |
                                   None \<Rightarrow> liftF (coerce \<circ> index s)) "

definition state_compose :: 
     "('a => ('b, 'config, 'state) stateful) \<Rightarrow>
      ('b \<Rightarrow> ('c, 'config, 'state) stateful) \<Rightarrow>
      ('a \<Rightarrow> ('c, 'config, 'state) stateful)"
     where
 "state_compose f g \<equiv> \<lambda>x. state_bind (f x) g" 

adhoc_overloading
 bind state_bind



lemma nonterm_append_simp[simp]: "\<not> pred terminates s \<Longrightarrow> appendS s s' = s"
  apply (simp add: appendS_def, transfer, clarsimp, safe)
   apply (rule ext)
   apply (clarsimp)
   apply (metis State.exhaust coerce.simps(1) coerce.simps(2) coerce.simps(3) terminates_def)
  by (simp add: coerce_in_traces)

thm terminates_def
lemma no_length_no_termination:"pred lengthS c = None \<longleftrightarrow> \<not>  finiteS c " 
  apply (safe; clarsimp simp: finiteS_def)
  apply (transfer)
   apply (clarsimp simp: lengthS_def terminates_def terminated_def split: if_splits)
  apply (transfer)
  by (simp add: lengthS_def)


lemma finiteS_append: "finiteS (c @@ c') \<longleftrightarrow> finiteS c \<and> finiteS c'"
  apply (clarsimp simp: finiteS_def, safe)
  
    apply (smt (verit, best) State.exhaust coerce.simps(1) coerce.simps(3) coerce.simps(4) coerce_idemp
          index.rep_eq isState.simps(1) isState.simps(2) isState.simps(3) isState.simps(4) nonterm_append_simp
           pred.rep_eq term_index_append' terminates_def)
  sorry


lemma singleton_term[simp]: "pred terminates [[c]] " sorry

lemma singleton_length[simp]:"the (pred lengthS [[c]]) = 1" sorry

lemma singleton_index[simp]:"[[c]] ^ 0 = State c" sorry

definition "emptyS = liftF (\<lambda>n. Term ())"

lemma empty_trace[simp]: "pred lengthS x = Some 0 \<longleftrightarrow> x = emptyS " sorry

lemma empty_append[simp]: "appendS c emptyS = c" "appendS emptyS c = c" sorry

lemma state_st_inv[simp]: "isState c \<Longrightarrow> State (st c) = c"
  apply (case_tac c; clarsimp)
  apply (clarsimp simp: terminated_def)+
  done

lemma not_terminated_yet: "pred lengthS x = Some n \<Longrightarrow> m < n \<Longrightarrow> \<not>terminated (x ^ m)"
  apply (transfer, clarsimp simp: terminated_def)
  by (metis isState.simps(1) less_length_is_state option.sel)

abbreviation "clean c \<equiv> liftF (coerce o index c)"

lemma clean_twice[simp]: "clean (clean c) = clean c"
  apply (transfer, clarsimp simp: , safe; clarsimp simp: comp_def)
  
   apply (simp add: coerce_in_traces traceDom_def)
  apply (simp add: coerce_in_traces traceDom_def)
  done

lemma no_length_easy_clean[simp]: "pred lengthS c = None \<Longrightarrow> clean c = c"
  apply (transfer, clarsimp, intro conjI impI)
   apply (rule ext, clarsimp)
   apply (case_tac \<open>c x\<close>; clarsimp)
  apply (metis isState.simps(1) lengthS_def option.distinct(1))

  sorry


lemma length_clean_length[simp]: "pred lengthS (clean c) = pred lengthS c"
  apply (transfer, clarsimp; safe)
  apply (clarsimp simp: lengthS_def)
  by (simp add: coerce_in_traces)

find_theorems index

lemma coerce_clean_index[simp]: "coerce (clean s ^ n) = coerce (s ^ n)  "
  by (transfer, clarsimp simp: coerce_in_traces)


lemma terminates_clean[simp]: "pred terminates (clean s) \<longleftrightarrow> pred terminates s  "
  apply (transfer, clarsimp, safe; clarsimp simp: terminates_def)
  apply (metis State.distinct(9) State.exhaust State.simps(10) State.simps(4) coerce.simps(1) coerce.simps(2) coerce.simps(3))
   apply (metis coerce.simps(4))
  by (simp add: coerce_in_traces)


lemma clean_head: "s' = s'' \<Longrightarrow> s @@ s' = clean s @@ s''"
  apply (clarsimp)
  apply (rule trace_eqI)
  apply (case_tac "pred terminates s")
   apply (clarsimp simp: term_index_append term_index_append')
  by (clarsimp simp: term_index_append')

lemma clean_index_coerce: "(clean s) ^ n = coerce (s ^ n)"
  by (transfer, clarsimp simp: coerce_in_traces)


lemma clean_distrib_appendS: "clean (s @@ s') = clean s @@ clean s'"
  apply (rule trace_eqI)
  apply (case_tac "pred terminates s")
   apply (clarsimp simp: term_index_append term_index_append' clean_index_coerce)
  by (clarsimp simp: term_index_append' clean_index_coerce)


lemma state_compose_assoc:
 "state_compose f (state_compose g h) = state_compose (state_compose f g) h"
  apply (rule ext; clarsimp simp: state_compose_def) 
  apply (rule ext)+
  apply (clarsimp simp: state_bind_def Let_unfold clean_distrib_appendS split: option.splits prod.splits)

  apply (intro conjI impI; clarsimp?)
  apply (subst clean_distrib_appendS)
    apply (rule clean_head, clarsimp)
  apply (metis finiteS_append no_length_no_termination option.distinct(1))
  apply (intro impI conjI allI | clarsimp)+
   apply (metis no_length_no_termination option.distinct(1) finiteS_append)
  by (smt (verit) One_nat_def add.commute add_cancel_left_right add_diff_cancel_left add_diff_cancel_left'
                  add_diff_cancel_right' appendS_assoc appendS_def clean_head clean_index_coerce clean_index_coerce clean_index_coerce clean_index_coerce 
                  clean_twice clean_twice coerce.simps(2) comp_apply comp_apply diff_Suc_less diff_diff_cancel diff_diff_left diff_is_0_eq diff_le_self dual_order.refl index.rep_eq index.rep_eq le_add2 le_add_diff_inverse2 le_antisym le_eq_less_or_eq le_zero_eq lengthS_append_eq lengthS_append_eq lengthS_le_append length_clean_length lessI less_diff_conv2 less_length_is_state less_sub_less_plus linorder_not_less nat_less_le not_less_eq option.sel pred.rep_eq pred.rep_eq res_def singleton_index singleton_length singleton_term st_def state_st_inv term_index_append term_index_append term_index_append terminates_append)


definition "constS c = liftF (\<lambda>n. Term c)"

definition return :: "'a \<Rightarrow> ('a, 'config, 'state) stateful" where
  "return a \<equiv> \<lambda>config state. (constS a)"

lemma lengthS_emptyS[simp]: "pred lengthS emptyS = Some 0"
  apply (transfer)
  by (clarsimp)

lemma length_const[simp]: "pred lengthS (constS x) = Some 0" 
  apply (clarsimp simp: constS_def, transfer, clarsimp simp: traceDom_def)
  by (clarsimp simp: lengthS_def)


lemma constS_append[simp]: "constS x @@ s = s" 
  apply (rule trace_eqI)
  apply (subst term_index_append)
   defer
   apply (clarsimp)
  apply (clarsimp simp: constS_def, transfer)
  by (simp add: terminates_def traceDom_def)

lemma constS_append'[simp]: "s @@ constS x = s"

  apply (rule trace_eqI)
  apply (case_tac "pred terminates s")
  apply (subst term_index_append, clarsimp)
   apply (clarsimp)
  apply (clarsimp simp: constS_def, transfer)
   apply (simp add: terminates_def traceDom_def)
   apply (clarsimp)
  oops
  


lemma index_constS[simp]:  "constS x ^ n = Term x" 
  by (clarsimp simp: constS_def, transfer, clarsimp simp: traceDom_def)


lemma return_left: "state_compose return f = f"
  apply (intro ext)
  apply (clarsimp simp: state_compose_def)
  apply ( clarsimp simp: state_compose_def state_bind_def  split: prod.splits option.splits)
  apply (clarsimp simp: return_def  Let_unfold split: option.splits)
  by (simp add: term_index_append)


lemma index_eq_after_finish: "pred lengthS s = Some i \<Longrightarrow> i \<le> m \<Longrightarrow> i \<le> n \<Longrightarrow>  (index s n) = s ^ m"
  apply (transfer, clarsimp simp: traceDom_def lengthS_def split: if_splits)
  by (metis (no_types, lifting) LeastI)


lemma return_right: "state_compose f return = f" 
  apply (intro ext)
  apply (clarsimp simp: state_compose_def)
  apply ( clarsimp simp: state_compose_def state_bind_def Let_unfold  split: prod.splits option.splits)
  apply (clarsimp simp: return_def)
  apply (case_tac "pred terminates ( f x xa xb)")
  apply (rule trace_eqI)
  apply (subst term_index_append)
    apply (clarsimp)
   apply (clarsimp, safe)
    apply (metis coerce.simps(2) index.rep_eq less_length_is_state option.sel pred.rep_eq state_st_inv)
  using index_eq_after_finish 
   apply (smt (verit, del_insts) State.sel(2) index.rep_eq isState.simps(1) less_length_is_state linorder_not_le nle_le option.sel pred.rep_eq terminates_def)
  by simp

lemma return_bind_l: "(return x \<bind> f) = f x"
  apply (intro ext)
  apply ( clarsimp simp: state_compose_def state_bind_def  split: prod.splits option.splits)
  apply (clarsimp simp: return_def  Let_unfold split: option.splits)
  by (simp add: term_index_append)

lemma return_bind: "(f x \<bind> return) = f x"
  apply (insert return_right[where f=f], clarsimp simp: state_compose_def) 
  by (drule_tac x=x in fun_cong, clarsimp)

definition "abortS \<equiv> liftF (\<lambda>_. Abort)" 

lemma nonterm_aborts: "\<not> pred terminates abortS"
  by (clarsimp simp: terminates_def abortS_def, transfer, clarsimp split: if_splits)


lemma infinite_appendS: "\<not> finiteS c \<Longrightarrow> c @@ d = c"
  by (metis finiteS_def index.rep_eq isState.simps(1) nonterm_append_simp pred.rep_eq terminates_def)

definition config :: "('config, 'config, 'state) stateful" where
 "config \<equiv> \<lambda>config state. return config config state"

definition getState :: "('state, 'config, 'state) stateful" where
 "getState \<equiv> \<lambda>config state. return state config state "

definition setState :: "'state \<Rightarrow> (unit, 'config, 'state) stateful" where
 "setState s \<equiv> \<lambda>config state. [[s]] "

definition modifyState :: "('state \<Rightarrow> 'state) \<Rightarrow> (unit, 'config, 'state) stateful" where
 "modifyState f \<equiv> do {s <- getState; setState (f s)} "

definition flag :: "bool \<Rightarrow> (unit, 'config, 'state) stateful" where
 "flag b \<equiv> \<lambda>config state. if b then emptyS else abortS "

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
  apply (clarsimp simp: return_def)
  by (simp add: term_index_append)

lemma fail_absorb: "fail \<bind> f = fail"
  apply (clarsimp simp: fail_def assert_def getState_bind_simp)
  apply (intro ext)
  apply (clarsimp simp: state_bind_def Let_unfold flag_def split: option.splits)
  by (simp add: nonterm_aborts)


primrec iterateM :: "('a \<Rightarrow> ('a, 'config, 'state) stateful) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'config \<Rightarrow> 'state \<Rightarrow>  ('a, 'state) trace"
  where "iterateM f 0 a cf state  = f a cf state" |
        "iterateM f (Suc n) a cf state = (state_bind (iterateM f (n) a) f) cf state"


definition "fixP (f :: (nat \<Rightarrow> ('a, 'state) trace)) = f (SOME n. f n = f (Suc n))"



definition flatten :: "(nat \<Rightarrow> ('a, 'state) trace) \<Rightarrow> nat \<Rightarrow> ('a, 'state) State"
  where "flatten f i \<equiv> if (\<exists>n. f n = f (Suc n)) 
             then index ( fixP f) i else
             (if (\<exists>n. isState (index (f n) i)) then  
                  index (f (SOME n. isState (index (f n) i))) i else
               Incomplete) "

lemma Term_tracedom[simp]:"(\<lambda>n. Term a) \<in> traceDom"
  by (simp add: traceDom_def)


lemma fixP_iter_return: "fixP (\<lambda>n. iterateM return n a cf state) = return a cf state"
  apply (clarsimp simp: fixP_def)
  apply (rule someI2[where a=0])
   apply (clarsimp)
   apply (clarsimp simp: return_bind)
  apply (clarsimp simp: return_bind)
  by (induct_tac x; clarsimp simp: return_bind)

lemma someI_ex_eq: "\<exists>a. P a \<Longrightarrow> (\<And>b. (SOME a. P a) = b  \<Longrightarrow> P b \<Longrightarrow> Q b) \<Longrightarrow> Q (SOME a. P a)"
  by (simp add: verit_sko_ex)


lemma same_terminated: "a \<in> traceDom \<Longrightarrow> a n = Term c \<Longrightarrow> m \<ge> the (lengthS a) \<Longrightarrow> a m = Term c"
  apply (clarsimp simp: traceDom_def)
  by (smt (verit, del_insts) LeastI isState.simps(1) lengthS_def nat_le_linear option.sel)

lemma "a = a @@ b \<Longrightarrow> pred terminates a \<Longrightarrow>  \<exists>c. b = constS c "
  apply (clarsimp simp: appendS_def constS_def)
  apply (transfer)
  apply (clarsimp)
  apply (clarsimp simp:  terminates_def)

  apply (rule_tac x="c" in exI)
  apply (intro ext)
  apply (drule_tac x="na + the (lengthS a)" in fun_cong )
  apply (clarsimp split: if_splits)
  by (frule_tac m="(na + the (lengthS a))" in same_terminated, assumption, clarsimp, clarsimp)


lemma "iterateM f b a cf state = (iterateM f b a \<bind> f) cf state"
  apply (clarsimp simp: state_bind_def Let_unfold split: option.splits)

lemma index_eq_after_term: "j \<le> i \<Longrightarrow> \<not>isState (index s j) \<Longrightarrow> index s j = index s i"
  apply (transfer)
  by (clarsimp simp: traceDom_def)

lemma "j \<le> i \<Longrightarrow> iterateM f j a cf state \<noteq> (iterateM f j a \<bind> f) cf state \<Longrightarrow>
      isState (iterateM f j a cf state ^ j)"
  apply (induct j)
   apply (clarsimp simp:  state_bind_def Let_unfold split: option.splits) 
  apply (case_tac "x2 = 0", clarsimp)
   apply (erule contrapos_np)
  apply (case_tac "pred terminates ( f a cf state)")
    apply (rule trace_eqI)
  apply (clarsimp simp: term_index_append) 
  find_theorems appendS index
  
  apply (metis State.sel(2) constS_append constS_append' index_constS)
  oops

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


definition "whileM f P a \<equiv> fixM (\<lambda>a. do {b <- P a; if b then f a else return a}) a"

lemma "whileM f (\<lambda>_. return False) a = return a"
  apply (intro ext, clarsimp simp: whileM_def return_bind_l)

lemma "flatten (\<lambda>n. iterateM return n a x xa) = return a x xa"

lemma "fixM (return) a = return a"
  apply (intro ext)
  apply (clarsimp simp: return_def fixM_def constS_def)
  apply (transfer)
  apply (clarsimp simp: flatten_wf)
   apply (intro ext)
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

definition "while_map = 





end


