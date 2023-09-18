theory operational_obs
  imports Main
          "HOL-Library.Adhoc_Overloading"
          HOL.Relation
          HOL.Transitive_Closure
          HOL.Complete_Lattices
          CRA_Obs
          Upset
          
begin


datatype label = \<pi> | \<epsilon> 

declare [[typedef_overloaded]]

datatype ('state) command = Test 'state | Pgmc "('state \<times> 'state)" | Envc "('state \<times> 'state)" | Abort 'state | Magic

datatype ('state) program = Seq    "('state) program" "('state) program" |
                          Par    "('state) program" "( 'state) program" |
                          Conj   "('state) program" "('state) program" |
                          Star   "('state) program" |
                          Prim   "('state) command"

definition "set_of_ups S = {x. x \<up>\<in> S}"

(* 
instantiation option :: (order) order begin

fun less_eq_option where
 "less_eq_option None _ = True" |
 "less_eq_option (Some v) (Some v') = (v \<le> v')" |
 "less_eq_option (Some v) None = False" 
definition "(f:: 'a option) < g \<longleftrightarrow> f \<le> g \<and> \<not> (g \<le> f)"
instance
  apply (standard; (clarsimp simp: less_option_def split:  option.splits)?)
    apply (case_tac x;clarsimp)
   apply (case_tac x; case_tac y; case_tac z; clarsimp)
  apply (metis order_trans)
  apply (case_tac x; case_tac y; clarsimp)
  done
end

instantiation option :: (type) plus
begin
fun plus_option where
 "plus_option None _ = None" |
 "plus_option _ None = None" |
 "plus_option (Some v) (Some v') = (if v = v' then Some v else None)" 
instance
  apply (standard)
  done
end

instantiation option :: (type) times
begin
fun times_option where
 "times_option None v = v" |
 "times_option v None = v" |
 "times_option (Some v) (Some v') =  Some v " 
instance
  apply (standard)
  done
end

lemma plus_option_assoc: "(x :: 'a option) + y + z = x + (y + z)" 
  by (metis plus_option.elims)


lemma times_option_assoc: "(x :: 'a option) * y * z = x * (y * z)" 
  oops
  by (metis times_option.elims)

 fun terminate and abort where
 "terminate (Seq p q) = (terminate p + terminate q) * abort p" |
 "terminate (Par p q) = (terminate p + terminate q) * abort p * abort q" | 
 "terminate (Conj p q) = (terminate p + terminate q) * abort p * abort q" |
 "terminate (Prim (Test t)) =  Some t " |
 "terminate (Star c) = (terminate c) " |
 "terminate (Prim Abort) = Some \<top> "|
 "terminate (Prim p) = None " |
 "abort (Seq p q) = abort p * (if (terminate p) = None then None else abort q)" |
 "abort (Par p q) = abort p * abort q" | 
 "abort (Conj p q) = abort p * abort q" |
 "abort (Prim (Abort)) = Some \<top> " |
 "abort (Star c) =  abort c " |
 "abort (Prim p) = None"
*)

fun terminate and abort where
 "terminate (Seq p q) = (terminate p \<sqinter> terminate q) \<squnion> abort p" |
 "terminate (Par p q) = (terminate p \<sqinter> terminate q) \<squnion> abort p \<squnion> abort q" | 
 "terminate (Conj p q) = (terminate p \<sqinter> terminate q) \<squnion> abort p \<squnion> abort q" |
 "terminate (Prim (Test t)) =  {t} " |
 "terminate (Star c) = (terminate c) " |
 "terminate (Prim (Abort t)) = {t} "|
 "terminate (Prim p) = \<bottom> " |
 "abort (Seq p q) = abort p \<squnion> (terminate p \<sqinter> abort q)" |
 "abort (Par p q) = abort p \<squnion> abort q" | 
 "abort (Conj p q) = abort p \<squnion> abort q" |
 "abort (Prim (Abort t)) = {t} " |
 "abort (Star c) =  abort c " |
 "abort (Prim p) = \<bottom> " 


text \<open>
We provide a convenient do-notation for monadic expressions well-known from Haskell.
const>\<open>Let\<close> is printed specially in do-expressions.
\<close>

consts
  bind :: "'a \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'd" (infixl "\<bind>" 54)


consts
  thend ::  "['a, 'b] \<Rightarrow> 'c" (infixl "\<then>" 54)

notation (ASCII)
  bind (infixl ">>=" 54)



abbreviation (do_notation)
  then_do :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"
  where "then_do \<equiv> thend"

abbreviation (do_notation)
  bind_do :: "'a \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'd"
  where "bind_do \<equiv> bind"

definition "set_of f = {(x, y). y = f x}"

definition match :: "('a \<times> ('state \<times> 'state \<times> 'b) set) set \<Rightarrow> (('state \<times> 'a) \<times> ('state \<times> 'b)) set "
  where "match S = {((s, a), s', b). (s, s', b) \<in> \<Union> (S  `` {a}) }"

term "set_of (f :: ('a \<Rightarrow> ('state \<times> ('state \<times> 'b)) set)) "

definition rel_bind :: "('state \<times> ('state \<times> 'a)) set \<Rightarrow> ('a \<Rightarrow> ('state \<times> ('state \<times> 'b)) set) \<Rightarrow> (('state \<times> ('state \<times> 'b)) set)"
  where "rel_bind R f = R O (match (set_of f))"


definition return :: "'a \<Rightarrow> ('state \<times> ('state \<times> 'a)) set"
  where "return a = {(x, y, b). x = y \<and> a = b}"

lemma return_iff: "(x, y, a) \<in> return b \<longleftrightarrow> (x = y \<and> a = b)"
  by (safe; clarsimp simp: return_def)


definition run :: "('state \<times> ('state \<times> 'a)) set \<Rightarrow> 'state rel"
  where "run R = {(x, (x')). (\<exists>(a :: 'a) . (x , (x', a)) \<in> R)}"


lemma return_id: "rel_bind f (return) = f"
  apply (safe; clarsimp simp: rel_bind_def return_iff set_of_def match_def)
  apply (rule relcompI, assumption, clarsimp)
  done

lemma return_id': "rel_bind (return a) f  = f a"
  apply (safe; clarsimp simp: rel_bind_def return_iff set_of_def match_def)
  apply (rule relcompI)
  apply (subst  return_iff, intro conjI, rule refl, rule refl, clarsimp)
  done

abbreviation (do_notation)
  pgm_d :: "('state \<times> ('state \<times> 'a)) set \<Rightarrow> 'state program"
  where "pgm_d \<equiv> Prim o Pgmc o run "

notation (output)
  bind_do (infixl "\<bind>" 54)

notation (ASCII output)
  bind_do (infixl ">>=" 54)




nonterminal do_binds and do_bind
syntax
  "_do_block" :: "do_binds \<Rightarrow> 'a" ("do {//(2  _)//}" [12] 62)
  "_atom_block" :: "do_binds \<Rightarrow> 'a" ("atomically {//(2  _)//}" [12] 62)
                                               
  "_do_bind"  :: "[pttrn, 'a] \<Rightarrow> do_bind" ("(2_ \<leftarrow>/ _)" 13)
  "_do_let" :: "[pttrn, 'a] \<Rightarrow> do_bind" ("(2let _ =/ _)" [1000, 13] 13)
  "_do_then" :: "'a \<Rightarrow> do_bind" ("_" [14] 13)
  "_do_final" :: "'a \<Rightarrow> do_binds" ("_")
  "_do_cons" :: "[do_bind, do_binds] \<Rightarrow> do_binds" ("_;//_" [13, 12] 12)

translations
  "_do_block (_do_cons (_do_then t) (_do_final e))"
    \<rightleftharpoons> "CONST then_do t e"
  "_atom_block (_do_cons (_do_bind p t) (_do_final e))"
    \<rightleftharpoons> "CONST pgm_d (CONST bind_do t (\<lambda>p. e))"
  "_do_block (_do_cons (_do_bind p t) (_do_final e))"
    \<rightleftharpoons> "(CONST bind_do t (\<lambda>p. e))"
  "_do_block (_do_cons (_do_let p t) bs)"
    \<rightleftharpoons> "let p = t in _do_block bs"
  "_do_block (_do_cons b (_do_cons c cs))"
    \<rightleftharpoons> "_do_block (_do_cons b (_do_final (_do_block (_do_cons c cs))))"
  "_atom_block (_do_cons b (_do_cons c cs))"
    \<rightleftharpoons> "_atom_block (_do_cons b (_do_final (_do_block (_do_cons c cs))))"
  "_do_cons (_do_let p t) (_do_final s)"
    \<rightleftharpoons> "_do_final (let p = t in s)"
  "_do_block (_do_final e)" \<rightharpoonup> "e"
  "_atom_block (_do_final e)" \<rightharpoonup> "CONST pgm_d e"




adhoc_overloading
  bind rel_bind

adhoc_overloading
  thend Seq


term "rel_bind f (\<lambda>x. rel_bind g h)"

lemma " (s \<bind> f) \<bind> g = s \<bind> (\<lambda>x. f x \<bind> g)" 
  apply (intro set_eqI iffI; clarsimp simp: rel_bind_def set_of_def match_def)
   apply (rule relcompI, assumption, clarsimp)
   apply (rule relcompI, assumption, clarsimp)
  apply (rule relcompI, rule relcompI, assumption, clarsimp, assumption, clarsimp)
  done
  


term "do { (Prim Abort);
           atomically {x \<leftarrow> (s); y \<leftarrow> f x;  g y x};
           (Prim Abort); 
           (Prim Abort)}" 


datatype 'a result = Nothing | Result 'a | Anything | Everything


instantiation result :: (type) bounded_order begin
definition "bot_result = Nothing"
definition "top_result = Everything"

fun less_eq_result where
 "less_eq_result Nothing _ = True" |
 "less_eq_result (Result a) (Result b) = (a = b)" |
 "less_eq_result (Result r) Anything  = True" |
 "less_eq_result _ Everything = True" |
 "less_eq_result r r' = (r = r')"
 

definition "(f:: 'a result) < g \<longleftrightarrow> f \<le> g \<and> \<not> (g \<le> f)"


instance
  apply (intro_classes; (clarsimp simp: bot_result_def top_result_def less_result_def split: result.splits)?)
    apply (case_tac x; clarsimp)
   apply (case_tac x; case_tac y; case_tac z; clarsimp)
  apply (case_tac a; clarsimp)
  done
end

   






lemma in_Up_iff: "x \<in> \<Up>S \<longleftrightarrow> (\<exists>y\<in>S. y \<in> \<down>x)"
  apply (safe; clarsimp simp: upset_set_def in_down_iff)
  apply (blast)
  done

lemma up_univ[simp]:"\<Up> UNIV = UNIV"
  by (safe; fastforce simp: in_Up_iff in_down_iff)

lemma up_empty[simp]: "\<Up> {} = {}"
  by (safe; fastforce simp: in_Up_iff in_down_iff)

lemma terminate_and_abort_upclosed: "\<Up>(terminate p) = (terminate p) \<and> \<Up>(abort p) = (abort p) " 
  oops
  apply (induct p; clarsimp?)
     apply (safe; clarsimp simp: in_Up_iff in_down_iff)
        apply (elim disjE; clarsimp?)
  using in_Up_iff in_down_iff apply blast
  apply (meson in_upsetI)+
  using in_Up_iff not_in_down_iff apply blast
  using in_Up_iff not_in_down_iff apply blast
  apply (meson in_upsetI)+

  using in_Up_iff not_in_down_iff apply blast
  using in_Up_iff not_in_down_iff apply blast
  apply (meson in_upsetI)+
     apply (safe; clarsimp simp: in_Up_iff in_down_iff)
  apply (meson in_upsetI)+

  using in_Up_iff not_in_down_iff apply blast
  using in_Up_iff not_in_down_iff apply blast
  using in_Up_iff not_in_down_iff apply blast

    apply (safe; clarsimp simp: in_Up_iff in_down_iff)
  apply (meson in_upsetI)+

  using in_Up_iff not_in_down_iff apply blast
  using in_Up_iff not_in_down_iff apply blast
   apply (meson in_upsetI)+
  apply (safe; clarsimp simp: in_Up_iff in_down_iff)
   apply (meson in_upsetI)+


  using in_Up_iff not_in_down_iff apply blast
  using in_Up_iff not_in_down_iff apply blast
  using in_Up_iff not_in_down_iff apply blast
  apply (safe; clarsimp simp: in_Up_iff in_down_iff)
   apply (meson in_upsetI)+

  using in_Up_iff not_in_down_iff apply blast
  using in_Up_iff not_in_down_iff apply blast
  apply (case_tac x; clarsimp)
  apply (safe; clarsimp simp: in_Up_iff in_down_iff set_of_ups_def, transfer, clarsimp)
  using in_upsetI apply blast
  using order_trans apply blast
  done

thm conjI

lemma abort_upclosed: "\<Up>(abort p) = abort p"
  oops
  by (rule terminate_and_abort_upclosed[THEN conjunct2])


lemma term_upclosed: "\<Up>(terminate p) = terminate p"
  oops
  by (rule terminate_and_abort_upclosed[THEN conjunct1])

  
  


lemma abort_term[simp]: "abort c \<subseteq> terminate c"
  apply (induct c; clarsimp?)
    apply (blast)+
  apply (case_tac x; clarsimp)
  done


abbreviation (input) "pgm r \<equiv>  (Prim (Pgmc r))"

abbreviation (input) "env r \<equiv>  (Prim (Envc r))"

abbreviation (input) "test s \<equiv> Prim (Test (s))"


notation Par (infixr "\<parallel>" 50)

notation Conj (infixr "&&" 50)

notation Seq (infixr ";" 50)



type_synonym 'state configuration = " 'state program \<times> 'state" 

type_synonym 'state transition = "label \<times> 'state configuration \<times> 'state configuration" 


instantiation prod :: (preorder, preorder) preorder begin
definition "less_eq_prod (x :: 'a \<times> 'b) y \<equiv> fst x \<le> fst y \<and> snd x \<le> snd y"
definition "(f:: 'a \<times> 'b) < g \<longleftrightarrow> f \<le> g \<and> \<not> (g \<le> f)"
instance
  apply (intro_classes; clarsimp simp: less_eq_prod_def less_prod_def)
  by (metis order_trans)
end

instantiation prod :: (preorder_top, preorder_top) preorder_top begin
definition "top_prod  \<equiv> (\<top>, \<top>)"
instance
  by (intro_classes; clarsimp simp: less_eq_prod_def top_prod_def less_prod_def)
end

instantiation upset :: (preorder) preorder_top begin
lift_definition top_upset :: "'a upset" is "UNIV"
  apply (clarsimp)
  done
instance
  by (standard; clarsimp simp: less_eq_upset_def, transfer, clarsimp)
end


abbreviation "PGM   \<equiv> Prim (Pgmc \<top>)" 

abbreviation "ENV   \<equiv> Prim (Envc \<top>)" 

abbreviation "MAGIC \<equiv> Prim (Magic)"

abbreviation "TAU   \<equiv> Prim (Test \<top>)"   

find_consts "'a set \<Rightarrow> 'a set"

term abort

term "x \<in>\<up> S"



inductive_set oper :: "(('state ) transition) set" where
  abortIntro[simp, intro]    : "s \<in> (abort c) \<Longrightarrow>  (\<beta>, (c, s ), (Prim (Abort s'), s')) \<in> oper " |
  pgmIntro[simp, intro]      :  "(s, s') = r \<Longrightarrow> (\<pi>, (pgm r, s), (Prim (Test s'), s'))  \<in> oper"     |
  envIntro[simp, intro]      :  "(s, s') = r \<Longrightarrow> (\<epsilon>, (env r, s), (Prim (Test s'), s')) \<in> oper"      |
  conjIntro[simp, intro]     : "(\<beta>, (pl, s), (pl', s')) \<in> oper \<Longrightarrow> (\<beta>, (pr, s), (pr', s')) \<in> oper
                       \<Longrightarrow>  (\<beta>, (Conj pl pr, s),  (Conj pl' pr', s')) \<in> oper"   |
  seqIntro[simp, intro]      : "(\<beta>, (pl, s), (pl', s')) \<in> oper \<Longrightarrow>
                      (\<beta>, (Seq pl pr, s), (Seq pl' pr, s')) \<in> oper"           |
  seqStep[simp, intro]      :  "s \<in> (terminate pl) \<Longrightarrow> (\<beta>, (pr, s),  (pr', s')) \<in> oper \<Longrightarrow> 
                      (\<beta>, (Seq pl pr, s),  (pr', s')) \<in> oper"                  |
  parStepPgmEnv[simp, intro]   :  "(\<pi>, (pl, s), (pl', s')) \<in> oper \<Longrightarrow> (\<epsilon>, (pr, s) , (pr', s')) \<in> oper \<Longrightarrow>
                      (\<pi>, (Par pl pr, s), (Par pl' pr', s')) \<in> oper"          |
  parStepEnvPgm[simp, intro]   :  "(\<epsilon>, (pl, s), (pl', s')) \<in> oper \<Longrightarrow> (\<pi>, (pr, s), (pr', s')) \<in> oper \<Longrightarrow>
                      (\<pi>, (Par pl pr, s), (Par pl' pr', s')) \<in> oper"          |
  parStepEnvEnv[simp, intro]   :  "(\<epsilon>, (pl, s), (pl', s')) \<in> oper \<Longrightarrow> (\<epsilon>, (pr, s), (pr', s')) \<in> oper \<Longrightarrow>
                      (\<epsilon>, (Par pl pr, s), (Par pl' pr', s')) \<in> oper"          |
  whileStep:       "(\<beta>, (p, s), (p', s')) \<in> oper \<Longrightarrow> (\<beta>, (Star p, s), (p'; Star p, s')) \<in> oper" 

(* inductive_set oper_nondet :: "(label \<times> (('state program set) \<times> 'state) \<times> (('state program set) \<times> 'state) ) set" where
  nondet: "p \<in> S \<Longrightarrow> (\<beta>, (p, s), (q, s')) \<in> oper \<Longrightarrow> (\<beta>, (S, s), ({q}, s')) \<in> oper_nondet" |
  branch: "S \<noteq> {} \<Longrightarrow> (\<forall>q\<in>S. (\<beta>, (p,s), ({q}, s')) \<in> oper_nondet) \<Longrightarrow> (\<beta>, (p, s), (S, s')) \<in> oper_nondet" 



lemmas oper_nondet_intros[intro, simp] =
                     oper.intros[THEN oper_nondet.nondet[where p = p and S="{p}" for p, simplified]]


lemma oper_nondet_nonempty[simp, dest!]: "(\<beta>, (q, s), {}, s') \<in> oper_nondet \<Longrightarrow> False"
  apply (erule oper_nondet.cases; clarsimp)
  done


lemma conj_nondet: "(\<beta>, (p,s), (p',s')) \<in> oper \<Longrightarrow> (\<beta>, (q, s), (q', s')) \<in> oper_nondet \<Longrightarrow>
       (\<beta>, (Conj p ` q , s), ((Conj p' ` q'),s')) \<in> oper_nondet" 
  apply (erule oper_nondet.inducts[where P="\<lambda>\<beta> a st b st'. (\<beta>, (p,st), (p', st')) \<in> oper \<longrightarrow> R \<beta> a st b st'" for R, THEN mp] )
    apply (clarsimp)
    apply (rule branch, clarsimp)
  apply (clarsimp)
  apply (rule_tac p="Conj p pa" in  nondet)
    apply (clarsimp simp: image_def)
    apply (erule (1) oper.conjIntro)
   apply (clarsimp)
  apply (rule oper_nondet.branch)
  apply blast
   apply (fastforce)
  apply (assumption)
  done

*)


abbreviation transition  ("(_ \<rightarrow>\<^sub>_ _)"[56,55,56] 55) where
 "transition (c :: ('a  program \<times> 'a)) (l :: label) (c' :: 'a program \<times> 'a) \<equiv> (l, c , c') \<in> oper "

notation (input) transition  ("(_ \<rightarrow>_ _)"[56,55,56] 55)



definition "simulates f \<equiv> {(p,q). (\<forall>l s s' p'. (p,s) \<rightarrow>l (p', s') \<longrightarrow> (\<exists>q'. (q,s) \<rightarrow>l (q', s')  \<and>  (p', q') \<in> f))}"

lemma mono_simulates :"mono simulates"
  apply (rule monoI, clarsimp simp: simulates_def)
  by (meson in_mono)

lemma mono_simulates' :"x \<le> y \<Longrightarrow> (p,q) \<in> simulates x \<longrightarrow> (p,q) \<in> simulates y" 
  apply (clarsimp simp: simulates_def)
  by (meson subset_eq)

definition "terms S = \<Union>(terminate ` S)"

definition "aborts S = \<Union>(abort ` S)"


coinductive_set similar where
 simStep: "\<lbrakk>  (p, q) \<in> simulates similar;
            (terminate p) \<le> (terminate q); (abort p) \<le> (abort q)  \<rbrakk> \<Longrightarrow> (p,q) \<in> similar"
monos mono_simulates'

declare terms_def[simp]
declare aborts_def[simp]


abbreviation simjudge (infixr "\<leadsto>" 40) where
  "simjudge p q \<equiv> (q,p) \<in> similar"

definition bisimulate (infixr "~" 40) where 
  "bisimulate p q \<equiv> (p,q) \<in> similar \<and> (q,p) \<in> similar" 



lemma refines_refl[simp]: " p \<leadsto> p"
  apply (rule similar.coinduct[where X="(=)"]; fastforce simp: simulates_def)
  done


lemma simulatesD[elim, dest]: "q \<leadsto> p \<Longrightarrow> (p,s) \<rightarrow>l (p', s')  \<Longrightarrow>  (terminate p) \<le> (terminate q) \<and> (abort p) \<le> (abort q) \<and>
                          (\<exists>q'. (q,s) \<rightarrow>l (q', s')  \<and>  q' \<leadsto> p')" 
  apply (erule similar.cases; fastforce simp: simulates_def)
  done

lemma refines_trans[trans, elim]: "p \<leadsto> q \<Longrightarrow>  q \<leadsto> r \<Longrightarrow>  p \<leadsto> r"
  apply (rule similar.coinduct[where X="(\<lambda>x y. (x,y) \<in> relcomp similar similar) "])
   apply (simp add: relcomp.relcompI)
  apply (clarsimp simp: simulates_def)
  apply (intro conjI)
  apply (clarsimp)
  apply (meson relcomp.relcompI simulatesD) 
   apply (metis order.trans similar.cases )
  apply (metis order.trans similar.cases )
  done

lemma [simp]: "s \<up>\<in> \<top>"
  by (transfer, clarsimp simp: in_up_iff)

lemma abort_top [simp]: "Prim Abort \<leadsto> p"
  oops
  apply (coinduction arbitrary: p; clarsimp simp: simulates_def)
  by (rule_tac x="Prim Abort" in exI, clarsimp)


lemma refines_all[elim]: " q \<leadsto> Prim Abort \<Longrightarrow>  q \<leadsto> p "
  oops
  by auto


lemma conj_abort_absorb: "Conj p (Prim Abort) ~ Prim Abort"
  oops
  apply (clarsimp simp: bisimulate_def)
  apply (coinduction arbitrary: p; clarsimp simp: simulates_def)
  apply (fastforce)
  done

lemma seq_abort_left_absorb: "Seq (Prim Abort) p ~ Prim Abort"
  oops
 apply (clarsimp simp: bisimulate_def)
  apply (coinduction arbitrary: p; clarsimp simp: simulates_def)
  apply (fastforce)
  done


lemma dsub_set_ofI: "set_of_ups t' \<subseteq> set_of_ups t \<Longrightarrow> t' \<up>\<subseteq> t"
  apply (subst Dsub_iff)
  apply (clarsimp simp: set_of_ups_def)
  apply (blast)
  done

lemma not_test_step[simp]: "\<not>(Prim (Test t'), s) \<rightarrow>\<^sub>l (p', s')"
  apply (clarsimp)
  by (erule oper.cases; clarsimp)

lemma tests_le_iff: "Prim (Test t) \<leadsto> Prim (Test t') \<longleftrightarrow> t' = t"
  apply (clarsimp simp: similar.simps)
  apply (safe)
  apply (clarsimp simp: simulates_def)
  done

(* lemma choice_abort_absorb: "{(Choice p (Prim Abort))} ~ {(Prim Abort)}"
  apply ( clarsimp simp: bisimulate_def)
  apply (coinduction arbitrary: p;  clarsimp simp: simulates_def)
  apply (fastforce)
  done *)


lemma bisim_sym: "p ~ q \<longleftrightarrow> q ~ p"
  by (fastforce simp: bisimulate_def)

lemma bisim_refl[simp]: "p ~ p"
   by (fastforce simp: bisimulate_def)


lemma bisim_trans[elim]: "p ~ q \<Longrightarrow> q ~ r \<Longrightarrow> p ~ r"
  apply (clarsimp simp: bisimulate_def)
  by auto

instantiation program :: (type) preorder_bot
begin

definition "less_eq_program (p :: 'a program) q \<equiv> q \<leadsto> p"
definition "(f:: 'a program) < g \<longleftrightarrow> f \<le> g \<and> \<not> (g \<le> f)"
definition "bot_program \<equiv> MAGIC"

instance
  apply (intro_classes; clarsimp simp: bot_program_def less_eq_program_def less_program_def)
   apply force
  apply (coinduction)
  apply (auto)
  apply (clarsimp simp: simulates_def)
  by (erule oper.cases; clarsimp?)
end

lemma distrib_union: "\<Up> (P \<union> Q) = \<Up>P \<union> \<Up>Q"
  apply (safe; clarsimp simp: in_Up_iff in_down_iff)
    apply (blast)+
  done

lemma "x \<leadsto> y \<Longrightarrow> \<Up>(terminate y) \<subseteq> \<Up>(terminate x) \<and> \<Up>(abort y) \<subseteq> \<Up>(abort x) "
  apply (clarsimp simp: similar.simps)
  using terminate_and_abort_upclosed by blast


lemma seq_mono: "y \<leadsto> x \<Longrightarrow> b \<leadsto> a \<Longrightarrow> y ; b \<leadsto> x ; a"
 apply (coinduction arbitrary: x y b a; clarsimp, safe)
                 apply (clarsimp simp: simulates_def)
                 apply (erule oper.cases; clarsimp)
  apply (elim disjE)
                    apply (rule_tac x="Prim (Abort s'a)" in exI, clarsimp)
             apply (rule abortIntro)
             apply (clarsimp simp: distrib_union)
  apply (meson in_mono similar.cases)
            apply (clarsimp)
            apply (rule_tac x=" Prim (Abort s'a)" in exI, clarsimp)
            apply (rule abortIntro; clarsimp)
  apply (meson in_mono similar.cases)

                  apply (drule (1) simulatesD, clarsimp)
                  apply (rule_tac x="q';b" in exI, clarsimp)
                  apply (drule (1) simulatesD, clarsimp)
                 apply (rule_tac x="q'" in exI, clarsimp)
                 apply (erule seqStep[rotated])
  apply (metis similar.simps subsetD )
         apply (clarsimp simp: similar.simps)
         apply (blast)
        apply (clarsimp simp: similar.simps, blast)
                apply (clarsimp simp: similar.simps, blast)
                apply (clarsimp simp: similar.simps, blast)
                apply (clarsimp simp: similar.simps, blast)
                apply (clarsimp simp: similar.simps, blast)
                apply (clarsimp simp: similar.simps, blast)
                apply (clarsimp simp: similar.simps, blast)
  done

lemma "(c, s) \<rightarrow>\<^sub>\<beta> (c', s') \<Longrightarrow> Prim (Abort s) \<leadsto> c"
  apply (coinduction arbitrary: s s' c' c \<beta>; clarsimp)
  apply (intro conjI)
    apply (clarsimp simp: simulates_def)
    apply (rule_tac x="Prim (Abort s'a)" in exI, clarsimp)

  

lemma " Prim (Abort s) \<leadsto> Prim (Abort s) \<then> c"
  apply (coinduction arbitrary: s; clarsimp)
  apply (clarsimp simp: simulates_def)
  apply (erule oper.cases; clarsimp)
    apply (rule_tac x="Prim (Abort s'a)" in exI, clarsimp)
   apply (erule oper.cases; clarsimp)
   apply (rule_tac x="Prim (Abort s')" in exI)
   apply (clarsimp)
  apply (rule_tac x="Prim (Abort s'a)" in exI)
  apply (clarsimp)
  apply (erule notE)
  apply (coinduction; clarsimp)
  apply (intro conjI)
    defer
  

lemma seq_assoc': "(a ; b ; c) \<le> ((a ; b) ; c)"
  apply (clarsimp simp: less_eq_program_def)
  apply (coinduction arbitrary: a b c; clarsimp)
  apply (intro conjI)
    apply (clarsimp simp: simulates_def)
    apply (erule oper.cases; clarsimp)
      apply (rule_tac x="Prim (Abort s'a)" in exI, clarsimp, rule abortIntro; clarsimp)
     apply (rule_tac x="(pl' ; b) ; c" in exI, clarsimp)
    apply (erule oper.cases; clarsimp)
      apply (rule_tac x="Prim (Abort s')" in exI, clarsimp, rule abortIntro; clarsimp)
     apply (rule_tac x="pl'; c" in exI)
     apply (clarsimp)
    apply (rule_tac x="pr'a" in exI, clarsimp)
   apply (safe; clarsimp simp: in_Up_iff in_down_iff)
   apply blast
   apply (safe; clarsimp simp: in_Up_iff in_down_iff)
  apply (blast)
  done

lemma seq_assoc: "(a ; b ; c) \<ge> ((a ; b) ; c)"
  apply (clarsimp simp: less_eq_program_def)
  apply (coinduction arbitrary: a b c; clarsimp)
  apply (intro conjI)
    apply (clarsimp simp: simulates_def)
    apply (erule oper.cases; clarsimp)
      apply (rule_tac x=" Prim (Abort s'a)" in exI, clarsimp, rule abortIntro; clarsimp)
      apply (blast)
     apply (erule oper.cases; clarsimp)
         apply (rule_tac x="Prim (Abort s')" in exI)
         apply (intro conjI)
  apply (rule abortIntro)
  apply (clarsimp)


      apply (rule_tac x="(pl'a ; (b ; c))" in exI, clarsimp)
     apply (rule_tac x="pr'; c" in exI, clarsimp)
    apply (elim disjE)
     apply (rule_tac x="pr'" in exI, clarsimp)
      apply (rule_tac x="Prim Abort" in exI, clarsimp)
   apply (safe; clarsimp simp: in_Up_iff in_down_iff)
   apply blast
   apply (safe; clarsimp simp: in_Up_iff in_down_iff)
  apply (blast)
  done



fun domain where
 "domain (Seq p q) = \<Up>(domain p - (terminate p - abort p)) \<union> (terminate p \<inter> domain q)" |
 "domain (Par p q) = (domain p \<inter> domain q) \<union> abort p \<union> abort q" |
 "domain (Conj p q) = (domain p \<inter> domain q) \<union> abort p \<union> abort q" |
 "domain (Prim (Test t)) = set_of_ups (t)" |
 "domain (Prim Abort)    = UNIV" |
 "domain (Prim (Pgmc r)) = (\<Up>(fst ` set_of_ups r))"|
 "domain (Prim (Envc r)) = (\<Up>(fst ` set_of_ups r))"|
 "domain (Star p) = domain p" |
 "domain (Prim Magic) = {}"


fun codomain where
 "codomain (Seq p q) = UNIV" |
 "codomain (Par p q) = UNIV" | 
 "codomain (Conj p q) = UNIV" |
 "codomain (Prim (Test t)) = set_of_ups t " |
 "codomain (Star c) = UNIV " |
 "codomain (Prim Abort) = UNIV "|
 "codomain (Prim (Pgmc r)) = UNIV"|
 "codomain (Prim (Envc r)) = UNIV" |
 "codomain (Prim (Magic)) = {}"



fun first_prog where
 "first_prog (Seq p q)  = first_prog p" |
 "first_prog (Par p q)  = Par (last_prog p) (last_prog q)" |
 "first_prog (Conj p q) = Conj (last_prog p) (last_prog q)" |
 "first_prog (Prim (Test t)) = Prim (Test (\<Up>t))"|
 "first_prog (Prim (Pgmc r)) = Prim (Test (\<Up>(fst ` r)))" |
 "first_prog (Prim (Envc r)) = Prim (Test (\<Up>(fst ` r)))" |
 "first_prog (Prim Abort) = TAU" |
 "first_prog (Star p) = first_prog p" 

lemma sim_magic[simp]: " b \<leadsto> MAGIC"
  by (coinduction; clarsimp simp: simulates_def, erule oper.cases; clarsimp)

lemma [simp]:" \<Up> (\<Up> S) = \<Up>(S)"
  by (safe; clarsimp simp: in_down_iff in_Up_iff Bex_def)
   apply (metis dual_order.trans)
  by blast


lemma in_terminate_up: "x \<in> terminate a \<Longrightarrow> x \<le> y \<Longrightarrow> y \<in> terminate a"
  by (metis in_Up_iff in_down_iff term_upclosed)


lemma in_abort_up: "x \<in> abort a \<Longrightarrow> x \<le> y \<Longrightarrow> y \<in> abort a"
  by (metis in_Up_iff in_down_iff abort_upclosed)  


  
  


lemma inf_is_inf_upc[simp]:"\<Up>P = P \<Longrightarrow> \<Up>Q = Q \<Longrightarrow>  \<Up> (P \<inter> Q) = P \<inter> Q"
  apply (safe; clarsimp simp: in_Up_iff in_down_iff)
  using in_Up_iff in_down_iff apply blast
  using in_Up_iff in_down_iff apply blast
  using in_Up_iff in_down_iff apply blast
  done

lemma abort_sub_domain: "abort a \<subseteq> domain a"
  apply (induct a; clarsimp)
   apply (safe; clarsimp?)
  apply (clarsimp simp: in_Up_iff in_down_iff)
     apply blast
  apply (clarsimp simp: in_Up_iff in_down_iff)
  apply blast
  apply blast
  apply (case_tac x; clarsimp)
  done

lemma [simp]: "\<Up> (set_of_ups S) = set_of_ups S"
  apply (clarsimp simp: set_of_ups_def, transfer, clarsimp)
  done

lemma codom_upclosed: "\<Up> (codomain a) = codomain a" 
  apply (induct a; clarsimp?)
  apply (case_tac x;clarsimp)
  done

definition "testS s = (if s = {} then MAGIC else Prim (Test (Abs_upset s)))" 

lemma testS_no_steps[simp]: "\<not>(testS S, s) \<rightarrow>\<^sub>\<beta> (x, s')"
  by (clarsimp simp: testS_def, erule oper.cases; clarsimp)

lemma seq_cod_le: "(b ; testS (codomain c)) \<le> b"
  apply (clarsimp simp: less_eq_program_def)
  apply (coinduction arbitrary: b; clarsimp)
  apply (clarsimp simp: simulates_def)
  apply (intro conjI;  clarsimp)
   apply (erule oper.cases; clarsimp)
     apply (rule_tac x="Prim Abort" in exI; clarsimp)
     apply (rule abortIntro, clarsimp)
  apply (metis abort.simps(6) abort.simps(9) empty_iff testS_def)
   apply (rule_tac x="pl'" in exI; clarsimp)
  apply (metis abort.simps(6) abort.simps(9) empty_iff testS_def)
  done

lemma can_abort_term_everywhere: "s \<in> abort c \<Longrightarrow> codomain c = UNIV " 
  apply (induct c; clarsimp?)
  apply (case_tac x; clarsimp)
  done

lemma top_to_top[simp]: "set_of_ups \<top> = UNIV "
  by (safe; clarsimp simp: set_of_ups_def)
  oops

lemma cod_const: "(b, s) \<rightarrow>\<^sub>l (p', s') \<Longrightarrow>  codomain b = codomain p'  " 
  apply (induct rule: oper.induct; clarsimp)
           apply (erule can_abort_term_everywhere)

  apply (erule oper.cases; clarsimp)
  done


lemma invert_Uprime_UNIV[simp]: "set_of_ups (Uprime UNIV) = UNIV"
  oops
  apply (safe; clarsimp simp: set_of_ups_def)
  by (transfer, clarsimp simp: in_up_iff)


lemma invert_Uprime[simp]: "set_of_ups (Uprime (set_of_ups S)) = set_of_ups S"
  apply (safe; clarsimp simp: set_of_ups_def)
   apply (transfer, clarsimp simp: in_up_iff)
   apply (meson in_upsetI)
   apply (transfer, clarsimp simp: in_up_iff)
  done


lemma invert_Uprime_iff[simp]: "\<Up>S = S \<Longrightarrow> S \<noteq> {} \<Longrightarrow>  set_of_ups (Abs_upset S) = S"
  apply (safe; clarsimp simp: set_of_ups_def)
   apply (transfer, clarsimp simp: in_up_iff)
  using Abs_upset_inverse Uin.rep_eq apply blast
  using Abs_upset_inverse Uin.rep_eq apply blast
  done


lemma terminate_testS_cod: "terminate (testS (codomain b)) = codomain b"
  apply (case_tac "codomain b = {}")
   apply (clarsimp simp: testS_def)
  apply (clarsimp simp: testS_def)
  by (simp add: codom_upclosed)

lemma terminate_le_cod: "terminate b \<subseteq> codomain b"
  apply (induct b; clarsimp)
  apply (case_tac x; clarsimp)
done

lemma seq_cod_ge: " (b ; testS (codomain b)) \<ge> b"
  apply (clarsimp simp: less_eq_program_def)
  apply (coinduction arbitrary: b ; clarsimp)
  apply (intro conjI)
   apply (clarsimp simp: simulates_def)
   apply (rule_tac x="p' ; testS (codomain b) " in exI,  clarsimp)
  apply (rule arg_cong[where f=testS])
   apply (erule cod_const)
  apply (clarsimp simp: terminate_testS_cod)
  using terminate_le_cod 
  by auto
  
 

lemma dom_upclosed: "\<Up> (domain a) = domain a" 
  apply (induct a; clarsimp?)
     apply (clarsimp simp: distrib_union abort_upclosed)
     apply (intro set_eqI iffI; clarsimp simp: abort_upclosed term_upclosed)
     apply (clarsimp simp: distrib_union abort_upclosed)
     apply (clarsimp simp: distrib_union abort_upclosed)
  apply (case_tac x;clarsimp)
  done

lemma abort_testS[simp]: "abort (testS (S)) = {}"
  by (clarsimp simp: testS_def)


lemma terminate_testS[simp]: "\<Up>S = S \<Longrightarrow> terminate (testS (S)) = S"
  by (clarsimp simp: testS_def)
  sledgehammer

lemma dom_decreasing: "(testS (domain a) ; b) \<le> b"
  apply (clarsimp simp: less_eq_program_def)
  apply (coinduction arbitrary: a b; clarsimp?)
  apply (clarsimp simp: simulates_def)
    apply (erule oper.cases; clarsimp)
   apply (rule_tac x="Prim Abort" in exI, clarsimp)
    apply (rule_tac x=pr' in exI, clarsimp)
  done

lemma terminate_domain[simp]: "terminate (testS (domain a)) = domain a"
  by (clarsimp simp: dom_upclosed)
  

lemma abort_domain': "s \<in> abort c \<Longrightarrow> s \<in> \<Up> (domain c)" 
  by (rule in_mono[THEN mp], subst dom_upclosed, rule abort_sub_domain, clarsimp )

lemma terminated_step_is_aborting:
  "(p, s) \<rightarrow>\<^sub>\<beta> (p', s') \<Longrightarrow> s \<in> (terminate p) \<Longrightarrow> s \<in> abort p" 
  by (induct rule: oper.inducts; clarsimp)

lemma not_terminated_seq_invariant: "(pl, s) \<rightarrow>\<^sub>\<beta> (pl', s') \<Longrightarrow> s \<in> \<Up> (domain pl) \<Longrightarrow> s \<notin> terminate pl \<Longrightarrow> s \<in> \<Up> (domain (pl ; pr)) "
  apply (induct rule: oper.inducts; clarsimp simp: dom_upclosed term_upclosed distrib_union abort_upclosed)
  using abort_term apply blast
       apply (clarsimp simp: in_Up_iff in_down_iff less_eq_prod_def)
       apply (metis Diff_iff Int_iff Un_iff dual_order.refl)

      apply (clarsimp simp: in_Up_iff in_down_iff less_eq_prod_def)
  apply (smt (z3) Diff_iff Downset.not_in_down_iff Int_iff Un_iff in_Up_iff order_refl)
      apply (clarsimp simp: in_Up_iff in_down_iff less_eq_prod_def)
     apply (smt (z3) Diff_iff Downset.not_in_down_iff Int_iff Un_iff in_Up_iff order_refl)
      apply (clarsimp simp: in_Up_iff in_down_iff less_eq_prod_def)


     apply (smt (verit, del_insts) Diff_iff Int_iff Un_iff dual_order.refl in_Up_iff not_in_down_iff)
     apply (clarsimp simp: in_Up_iff in_down_iff less_eq_prod_def)
    apply (metis Diff_iff Int_iff Un_iff dual_order.refl)
   apply (clarsimp simp: in_Up_iff in_down_iff less_eq_prod_def)
   apply (metis Diff_iff Int_iff Un_iff dual_order.refl)
  done





lemma all_steps_in_domain: "(a, s) \<rightarrow>\<^sub>l (p', s') \<Longrightarrow> s \<in> \<Up> (domain a)"
  apply (induct rule: oper.induct; clarsimp?)
           apply (erule abort_domain')
          apply (clarsimp)
          apply (metis Downset.not_in_down_iff fstI image_eqI in_Up_iff mem_Collect_eq order_refl set_of_ups_def)
         apply (clarsimp)
        apply (metis Downset.not_in_down_iff fstI image_eqI in_Up_iff mem_Collect_eq order_refl set_of_ups_def)
       apply (clarsimp simp: dom_upclosed term_upclosed distrib_union)
       apply (clarsimp simp: dom_upclosed term_upclosed distrib_union)
      apply (clarsimp simp: in_Up_iff in_down_iff less_eq_prod_def)
      apply (metis DiffD1 DiffD2 DiffI dual_order.refl terminated_step_is_aborting)
       apply (clarsimp simp: dom_upclosed term_upclosed distrib_union)
       apply (clarsimp simp: dom_upclosed term_upclosed distrib_union)
       apply (clarsimp simp: dom_upclosed term_upclosed distrib_union)
       apply (clarsimp simp: dom_upclosed term_upclosed distrib_union)
  done


lemma terminated_domain: "terminate a \<subseteq> domain a"
  apply (induct a; clarsimp)
  apply (intro conjI)
      apply (clarsimp simp: dom_upclosed term_upclosed abort_upclosed distrib_union)
         apply (clarsimp simp: in_Up_iff in_down_iff less_eq_prod_def)
      apply blast
     apply (clarsimp simp: in_Up_iff in_down_iff less_eq_prod_def)
  apply (metis Diff_iff abort_domain' dom_upclosed order_refl)
    apply blast
  apply blast
  apply (case_tac x; clarsimp)
  done

lemma nonempty_domain_aborting: "s \<in> abort c \<Longrightarrow> domain c = {} \<Longrightarrow> False"
  apply (induct c; clarsimp?)
   apply (elim disjE; clarsimp)
    apply (metis abort.simps(1) abort_domain' bot_eq_sup_iff domain.simps(1) ex_in_conv up_empty)
  apply (metis abort_domain' disjoint_iff_not_equal dom_upclosed)
  apply (case_tac x; clarsimp)
  done


lemma set_of_ups_nonempty: "set_of_ups r \<noteq> {}"
  apply (clarsimp simp: set_of_ups_def)
  apply (transfer)
  apply (clarsimp)
  apply (rule ccontr, clarsimp)
  done

lemma domain_nonempty: "(a, s) \<rightarrow>\<^sub>l (p', s') \<Longrightarrow> domain a \<noteq> {}"
  using all_steps_in_domain dom_upclosed by blast


lemma first_refine_refl: "a \<le> (testS (domain a) ; a)"
    apply (clarsimp simp: less_eq_program_def)
  apply (coinduction; clarsimp)
  apply (intro conjI)
    apply (clarsimp simp: simulates_def)
    apply (rule_tac x=p' in exI; clarsimp)
    apply (rule seqStep; clarsimp) 
  using all_steps_in_domain dom_upclosed apply blast
   apply (metis bot_least_trans dom_upclosed invert_Uprime_iff terminated_domain)
  by (metis abort_sub_domain bot_least_trans dom_upclosed invert_Uprime_iff)


lemma " Prim (Test t) \<leadsto> b1 ; b2 \<Longrightarrow> Prim (Test t) \<leadsto> b1" 
  apply (coinduction; clarsimp)
  apply (intro conjI)
    apply (clarsimp simp: simulates_def)
    apply (drule_tac simulatesD, erule seqIntro)
    apply (clarsimp)
    apply (erule oper.cases; clarsimp)back
   apply (clarsimp simp: similar.simps)
   apply (clarsimp simp: dom_upclosed term_upclosed abort_upclosed distrib_union terminated_domain)
  oops

declare terminate_and_abort_upclosed[simp]

lemma sub_test_is_terminates: "Prim (Test t) \<leadsto> b \<Longrightarrow>  b \<leadsto> testS (terminate b) \<and> testS (terminate b) \<leadsto> b"
  apply (case_tac "terminate b = {}")
  apply (clarsimp simp: testS_def)
   apply (coinduction; clarsimp)
  apply (intro conjI)
    apply (clarsimp simp: simulates_def)
  apply auto[1]
  apply (clarsimp simp: similar.simps)
  apply (intro conjI)
  apply (coinduction; clarsimp)
   apply (clarsimp simp: simulates_def)
  apply (coinduction; clarsimp)
  apply (clarsimp simp: simulates_def)
  apply (intro conjI)
   apply (clarsimp)
  by (auto)

lemma domain_can_step: "x \<in> domain a \<Longrightarrow> x \<notin> terminate a \<Longrightarrow> \<exists>y b l. (a, x) \<rightarrow>l (b, y)" 
  apply (case_tac "x \<in> abort a")
  apply (fastforce)
  apply (induct a arbitrary: x ; clarsimp?)
      apply (clarsimp simp: in_down_iff in_Up_iff)
      apply (elim disjE; clarsimp?)
  sorry 

lemma sim_test_iff:"(b \<leadsto> Prim (Test c)) \<longleftrightarrow> set_of_ups c \<subseteq> terminate b"
  apply (safe)
  apply (clarsimp simp: similar.simps)
   apply (metis in_Up_iff in_mono not_in_down_iff order_refl terminate_and_abort_upclosed)
  apply (coinduction; clarsimp)
  by (simp add:simulates_def)

lemma abort_nonempty_all_term: "s \<in> abort c \<Longrightarrow> terminate c - abort c = {}"
  apply (induct c; clarsimp?)
     apply (blast)
  apply (blast)
  apply (blast)
  apply (case_tac x; clarsimp)
  done

lemma abort_nonempty_no_codomain: "s \<in> abort c \<Longrightarrow> codomain c = {}"
  apply (induct c; clarsimp?)
  oops
      apply blast
  apply blast
    apply blast
   apply (clarsimp simp: abort_nonempty_all_term)
  apply (case_tac x;clarsimp)
  done

lemma in_term_not_abort_in_cod: "x \<in> \<Up> (terminate p - abort p) \<Longrightarrow> x \<in> codomain p"
  oops
  apply (induct p; (clarsimp simp: abort_nonempty_no_codomain abort_nonempty_all_term  in_Up_iff in_down_iff)?)

     apply blast
  apply blast
  apply blast
  apply (case_tac "xa";clarsimp)
  apply (clarsimp simp: in_Up_iff in_down_iff)
  by (meson order_trans)

lemma cod_step_decreasing: "(a, s) \<rightarrow>\<^sub>l (p', s') \<Longrightarrow> codomain a \<subseteq> codomain p'" 
  oops
  apply (induct arbitrary: rule:oper.inducts ; clarsimp simp: abort_nonempty_no_codomain)
        apply (safe; clarsimp?)
         apply (blast)+
  apply (drule in_term_not_abort_in_cod)
  apply (meson order_trans in_mono)
  done



lemma seq_ord_mono: "x \<le> y \<Longrightarrow> a \<le> b \<Longrightarrow> (x ; a) \<le> (y ; b)"
  by (clarsimp simp: less_eq_program_def seq_mono)



lemma in_terminate_not_in_abort_in_cod: "x \<in> terminate s \<Longrightarrow> x \<notin> abort s \<Longrightarrow> x \<in> codomain s"
  apply (induct s; clarsimp?)
  apply (case_tac "xa"; clarsimp)
  done

lemma not_sim_testD: "(Prim (Test t), b) \<notin> similar \<Longrightarrow> \<not>(terminate (Prim (Test t)) \<subseteq> terminate b  )"
  apply (clarsimp simp: similar.simps)
  apply (erule notE)
  apply (clarsimp simp: simulates_def)
  apply (erule oper.cases; clarsimp)
  done
sledgehammer

lemma le_test_no_term_magic: "b \<le> Prim (Test t) \<Longrightarrow> terminate b = {} \<Longrightarrow> b \<le> \<bottom>"
  apply (clarsimp simp: less_eq_program_def)

  apply (clarsimp simp: similar.simps)
  by (clarsimp simp: simulates_def)
  by (metis abort.simps(6) all_steps_in_domain dom_upclosed domain.simps(4) empty_iff terminate.simps(4) terminated_step_is_aborting)
)

find_theorems similar terminate

lemma "b \<le> Prim (Test t) \<Longrightarrow> b \<le> \<bottom> \<or> (\<exists>t'. t' \<le> t \<and>  b \<ge> Prim (Test t'))"
  apply (subst disj_commute)
  apply (clarsimp)
  apply (case_tac "terminate b = {}")
  apply (drule (1) le_test_no_term_magic, clarsimp)

  
  oops



    apply (metis abort.simps(6) all_steps_in_domain dom_upclosed domain.simps(4) empty_iff simulatesD terminate.simps(4) terminated_step_is_aborting)
   apply (clarsimp simp: bot_program_def)
  apply (drule not_sim_testD)
   apply (clarsimp simp: similar.simps)


lemma first_llp: "b \<le> Prim (Test t) \<Longrightarrow> (testS (domain a) \<le> b) = (a \<le> (b ; a))"
  apply (safe)
   apply (rule order_trans[rotated])
    apply (clarsimp simp: less_eq_program_def)
    apply (rule seq_mono, assumption)
    apply (rule refines_refl)
   apply (rule first_refine_refl)
  apply (clarsimp simp: less_eq_program_def)
  apply (drule sub_test_is_terminates)
  apply (clarsimp)
  apply (drule refines_trans[rotated])
 
   apply (erule seq_mono)
  apply (rule refines_refl)
  apply (coinduction arbitrary: a b t)
  apply (clarsimp)
  apply (intro conjI)
   apply (clarsimp simp: simulates_def)
  apply (clarsimp simp:   dom_upclosed term_upclosed abort_upclosed distrib_union terminated_domain)
  apply (case_tac "x \<in> terminate a")
  apply (clarsimp simp: similar.simps dom_upclosed term_upclosed abort_upclosed distrib_union terminated_domain)
   apply auto[1]
  apply (frule domain_can_step, clarsimp)
  apply (clarsimp)
  apply (frule_tac simulatesD, assumption)
  apply (clarsimp)
  apply (erule oper.cases; clarsimp) back
  done

lemma seq_tau_le: "b \<then> TAU \<le> b"
  apply (clarsimp simp: less_eq_program_def)
  apply (coinduction arbitrary: b; clarsimp)
   apply (clarsimp simp: simulates_def)
   apply (erule oper.cases ; clarsimp)
     apply (rule_tac x="Prim Abort" in exI, clarsimp)
  by (fastforce)


lemma seq_tau_ge: "b \<then> TAU \<ge> b"
  apply (clarsimp simp: less_eq_program_def)
  apply (coinduction arbitrary: b; clarsimp)
   apply (clarsimp simp: simulates_def)
  by (rule_tac x="p' ; TAU" in exI, clarsimp)


interpretation kleene: seq_elem Seq "testS o codomain" test "testS o domain"
  apply (standard; clarsimp?)
               apply (clarsimp simp: less_eq_program_def)
               apply (erule (1) seq_mono)
              apply (rule seq_assoc)
             apply (rule seq_assoc')
            apply (erule first_llp)
  apply (simp add: dom_decreasing)
      apply (simp add: first_refine_refl)
  using seq_ord_mono apply blast
             apply (rule seq_assoc')
       apply (rule seq_assoc)
     apply (rule_tac x="Prim Abort" in exI, intro conjI)
      apply (clarsimp simp: less_eq_program_def)
  apply (clarsimp simp: less_eq_program_def)
     apply (coinduction; clarsimp)
     apply (clarsimp simp: simulates_def, rule_tac x="Prim Abort" in exI; clarsimp)
    apply (clarsimp simp: less_eq_program_def)
    apply (coinduction; clarsimp simp: bot_program_def)
      apply (clarsimp simp: simulates_def)
      apply (erule oper.cases; clarsimp)
     apply (erule oper.cases; clarsimp)
    apply (simp add: seq_cod_le)
  apply (simp add: seq_cod_ge)
    apply (safe)
      apply (clarsimp simp: image_iff)
   apply (rule_tac x="testS (codomain xa)" in exI)
  apply (metis domain.simps(4) domain.simps(9) terminate.simps(4) terminate_testS_cod testS_def)
  apply (clarsimp)

  apply (clarsimp simp: image_iff) 
  apply (rule_tac x="testS (domain xa)" in exI) 
  apply (case_tac "domain xa = {}")
   apply (clarsimp simp: testS_def)
  by (metis codomain.simps(4) terminate.simps(4) terminate_domain testS_def)

declare set_of_ups_nonempty[simp]


interpretation kleene: test_seq Seq "testS o codomain" test "testS o domain"
  apply (standard; clarsimp?)
      apply (safe; clarsimp simp: image_iff)[1]
       apply (rule_tac x="test s" in exI)
        apply (clarsimp)
        apply (clarsimp simp: testS_def)
  apply (smt (verit, best) Rep_upset Rep_upset_inverse invert_Uprime_iff mem_Collect_eq)
       apply (clarsimp simp: in_down_iff)
       apply (clarsimp simp: less_eq_program_def similar.simps bot_program_def)
      apply (clarsimp simp: in_down_iff)
  apply (clarsimp simp: testS_def bot_program_def)
  apply (cl





adhoc_overloading
  thend kleene.convolute



find_consts name:assert

print_definitions



     



inductive_set choice_relation :: "('state program set \<times> 'state program set) set \<Rightarrow> ('state program set \<times> 'state program set) set"
  for R :: "('state program set \<times> 'state program set) set" where
 sim [simp, elim!]: "(P, Q) \<in> similar \<Longrightarrow> (P, Q) \<in> choice_relation R" |
 step[simp, elim!]: "(P, Q) \<in> R \<Longrightarrow> (P, Q) \<in> choice_relation R"  |
 trans: "(A, B) \<in> choice_relation R \<Longrightarrow> (B, C) \<in> choice_relation R \<Longrightarrow> (A, C) \<in> choice_relation R" |
 multi: "\<forall>v\<in>A. \<exists>B'. B' \<subseteq> B \<and> B' \<noteq> {} \<and> ({v},B') \<in> choice_relation R \<Longrightarrow> (A, B) \<in> choice_relation R" 

lemmas choice_relation_inducts = choice_relation.inducts[split_format(complete)]



lemma helperr: "\<forall>v\<in>S. P v \<and> (\<exists>S'. f v S') \<Longrightarrow> \<exists>S''. \<forall>v\<in>S''. \<exists>v'\<in>S. f v' v"
  by blast


lemma never_empty[simp]: "(q, s) \<rightarrow>\<^sub>\<beta> (q', s') \<Longrightarrow> q' \<noteq> {}"
  apply (induction rule: oper_nondet.inducts; clarsimp)
  done

lemma choose_single[simp]: "(q, s) \<rightarrow>\<^sub>\<beta> (q', s') \<Longrightarrow> v \<in> q' \<Longrightarrow> (q, s) \<rightarrow>\<^sub>\<beta> ({v}, s')"
  apply (induction rule: oper_nondet.inducts; clarsimp)
  by (simp add: oper_nondet.nondet)
  

lemma prooove: "\<lbrakk>((p, s) \<rightarrow>\<^sub>l (p', s')) \<rbrakk> \<Longrightarrow> (\<And>v v' s s' l. v \<in> p \<Longrightarrow> (l, (v, s), v', s') \<in> oper \<Longrightarrow> \<exists>q'. (q, s) \<rightarrow>\<^sub>l (q', s') \<and> ({v'}, q') \<in> choice_relation X)
 \<Longrightarrow>  \<exists>q'. (q, s) \<rightarrow>\<^sub>l (q', s')  \<and> (p', q') \<in> choice_relation (X) "
  thm oper_nondet.inducts
  thm oper_nondet.inducts[where ?x2.0=p and P="\<lambda>\<beta> S s q s'. S = p \<longrightarrow> Q \<beta> S s q s'" for p Q, simplified]
  apply (erule oper_nondet.inducts[where ?x2.0=p and P="\<lambda>\<beta> S s q s'. S = p \<longrightarrow> Q \<beta> S s q s'" for p Q, simplified])
   apply (clarsimp)
  apply (clarsimp)
  apply (frule helperr)
  apply (clarsimp)
  apply (rule_tac x="\<Union>((\<lambda>v. (SOME q'. (q, s) \<rightarrow>\<^sub>\<beta> (q', s') \<and> ({v}, q') \<in> choice_relation X)) ` S) " in exI)
  apply (rule conjI)
   apply (rule oper_nondet.branch, clarsimp)
    apply (metis (no_types, lifting) ex_in_conv never_empty verit_sko_ex_indirect)
  apply (clarsimp)
  apply (metis (no_types, lifting) choose_single verit_sko_ex')
   defer
   apply (rule choice_relation.multi)
   apply (clarsimp)
  apply (drule (1) bspec)
  apply (clarsimp)
proof -
  fix S :: "'a program set" and \<beta> :: label and sa :: 'a and s'a :: 'a and S'' :: "'a program set set" and v :: "'a program" and q' :: "'a program set"
  assume a1: "v \<in> S"
assume a2: "(q, sa) \<rightarrow>\<^sub>\<beta> (q', s'a)"
assume "({v}, q') \<in> choice_relation X"
then have "(q, sa) \<rightarrow>\<^sub>\<beta> (q', s'a) \<and> ({v}, q') \<in> choice_relation X"
  using a2 by fastforce
  then have f3: "(q, sa) \<rightarrow>\<^sub>\<beta> (SOME P. (q, sa) \<rightarrow>\<^sub>\<beta> (P, s'a) \<and> ({v}, P) \<in> choice_relation X, s'a) \<and> ({v}, SOME P. (q, sa) \<rightarrow>\<^sub>\<beta> (P, s'a) \<and> ({v}, P) \<in> choice_relation X) \<in> choice_relation X"
    
    by (metis (no_types, lifting) verit_sko_ex')
then have "{} \<noteq> (SOME P. (q, sa) \<rightarrow>\<^sub>\<beta> (P, s'a) \<and> ({v}, P) \<in> choice_relation X)"
  using never_empty by fastforce
  then have "\<exists>P. P \<in> (\<lambda>p. SOME P. (q, sa) \<rightarrow>\<^sub>\<beta> (P, s'a) \<and> ({p}, P) \<in> choice_relation X) ` S \<and> ((q, sa) \<rightarrow>\<^sub>\<beta> (P, s'a) \<and> ({v}, P) \<in> choice_relation X) \<and> {} \<noteq> P"
    using f3 a1 by blast
  then show "\<exists>P\<subseteq>\<Union>p\<in>S. SOME P. (q, sa) \<rightarrow>\<^sub>\<beta> (P, s'a) \<and> ({p}, P) \<in> choice_relation X. P \<noteq> {} \<and> ({v}, P) \<in> choice_relation X"
    by blast
qed



lemma stepChoice'[simp,intro]: "({P}, {P'}) \<in> choice_relation R \<Longrightarrow> ({Q}, {Q'}) \<in> choice_relation R \<Longrightarrow> ({P,Q}, {P', Q'}) \<in> choice_relation R"
  by (smt choice_relation.multi insert_commute insert_iff singletonD subset_insertI)


lemma [simp]: "choice_relation X \<union> similar = choice_relation X"
  by (metis choice_relation.sim subrelI sup.orderE)



lemma simulates_trans: "(A, B) \<in> simulates S \<Longrightarrow> trans S \<Longrightarrow> (B, C) \<in> simulates S \<Longrightarrow> (A, C) \<in> simulates S"
  apply (clarsimp simp: simulates_def)
  apply (erule allE, erule allE, erule allE, erule allE, drule (1) mp)
  apply (clarsimp)
  apply (erule allE, erule allE, erule allE, erule allE, drule (1) mp)
  apply (clarsimp)
  by (meson transE)

lemma simulates_helper: "(A,B) \<in> simulates S \<Longrightarrow> (A, s) \<rightarrow>l (A', s') \<Longrightarrow> \<exists>B'. (B, s) \<rightarrow>l (B', s') \<and> (A', B') \<in> S"
  apply (clarsimp simp: simulates_def)
  done

lemma choose_sub[simp]: "(q, s) \<rightarrow>\<^sub>\<beta> (q', s') \<Longrightarrow> v \<subseteq> q' \<Longrightarrow> v \<noteq> {} \<Longrightarrow> (q, s) \<rightarrow>\<^sub>\<beta> (v, s')"
  apply (induction rule: oper_nondet.inducts; clarsimp?)
   apply (simp add: oper_nondet.nondet subset_singleton_iff)
  by (meson oper_nondet.branch subset_eq)

lemma choose_sub': "(v, s) \<rightarrow>\<^sub>\<beta> (q, s') \<Longrightarrow> v \<subseteq> q'  \<Longrightarrow> (q', s) \<rightarrow>\<^sub>\<beta> (q, s')"
  apply (induction rule: oper_nondet.inducts; clarsimp?)
  
   apply (meson oper_nondet.nondet subset_iff)
  by (meson oper_nondet.branch)
 


lemma halp: assumes subs:"\<forall>v\<in>A. \<exists>B'\<subseteq>B. B' \<noteq> {} \<and> ({v}, B') \<in> choice_relation X \<and> ({v}, B') \<in> simulates (choice_relation X)" 
  shows " (A, B) \<in> simulates (choice_relation X)"
  apply (subst simulates_def, clarsimp)
  apply (erule oper_nondet.inducts[where ?x2.0=p and P="\<lambda>\<beta> S s q s'. S = p \<longrightarrow> Q \<beta> S s q s'" for p Q, simplified]; clarsimp)
  apply (insert subs)

   apply (drule (1) bspec, clarsimp)
   apply (clarsimp simp: simulates_def)
   apply (erule_tac x="\<beta>" in allE)
   apply (erule_tac x="sa" in allE)
   apply (erule_tac x="s'a" in allE)
   apply (erule_tac x="{q}" in allE)
   apply (drule mp)
    apply (simp add: oper_nondet.nondet)
   apply (clarsimp)
   apply (meson choose_sub')
apply (rule_tac x="\<Union>((\<lambda>v. (SOME q'. (B, sa) \<rightarrow>\<^sub>\<beta> (q', s'a) \<and> ({v}, q') \<in> choice_relation X)) ` S) " in exI)
  apply (rule conjI)
   apply (rule oper_nondet.branch, clarsimp)
    apply (metis (no_types, lifting) ex_in_conv never_empty verit_sko_ex_indirect)
  apply (clarsimp)
  apply (metis (no_types, lifting) choose_single verit_sko_ex')
   apply (rule choice_relation.multi)
   apply (clarsimp)
  apply (drule (1) bspec)
  apply (clarsimp)+
proof -
  fix S :: "'a program set" and \<beta> :: label and sa :: 'a and s'a :: 'a and S'' :: "'a program set set" and v :: "'a program" and q' :: "'a program set"
  assume a1: "v \<in> S"
assume a2: "(B, sa) \<rightarrow>\<^sub>\<beta> (q', s'a)"
assume "({v}, q') \<in> choice_relation X"
then have "(B, sa) \<rightarrow>\<^sub>\<beta> (q', s'a) \<and> ({v}, q') \<in> choice_relation X"
  using a2 by fastforce
  then have f3: "(B, sa) \<rightarrow>\<^sub>\<beta> (SOME P. (B, sa) \<rightarrow>\<^sub>\<beta> (P, s'a) \<and> ({v}, P) \<in> choice_relation X, s'a) \<and> ({v}, SOME P. (B, sa) \<rightarrow>\<^sub>\<beta> (P, s'a) \<and> ({v}, P) \<in> choice_relation X) \<in> choice_relation X"
    by (metis (no_types, lifting) verit_sko_ex')
  then have "{} \<noteq> (SOME P. (B, sa) \<rightarrow>\<^sub>\<beta> (P, s'a) \<and> ({v}, P) \<in> choice_relation X)"
    by (metis never_empty)
  then have "\<exists>P. P \<in> (\<lambda>p. SOME P. (B, sa) \<rightarrow>\<^sub>\<beta> (P, s'a) \<and> ({p}, P) \<in> choice_relation X) ` S \<and> ((B, sa) \<rightarrow>\<^sub>\<beta> (P, s'a) \<and> ({v}, P) \<in> choice_relation X) \<and> {} \<noteq> P"
    using f3 a1 by blast
  then show "\<exists>P\<subseteq>\<Union>p\<in>S. SOME P. (B, sa) \<rightarrow>\<^sub>\<beta> (P, s'a) \<and> ({p}, P) \<in> choice_relation X. P \<noteq> {} \<and> ({v}, P) \<in> choice_relation X"
    by blast
qed
  

lemma choice_relation_thingy: assumes 
 pgm_induct:
   "(\<And>s p q p' s' r. (p, q) \<in> X  \<Longrightarrow> (p,q) \<in> simulates (choice_relation X))"
 shows " (p, q) \<in> choice_relation X \<Longrightarrow> (p,q) \<in> simulates (choice_relation X)" 
  apply (induction rule: choice_relation.inducts; clarsimp?)
     apply (clarsimp simp: simulates_def)
  apply (drule (1) simulatesD)
     apply auto[1]
    apply (simp add: pgm_induct)
   apply (erule simulates_trans)
 apply (rule transI)
  using choice_relation.trans apply blast
   apply (assumption)
  apply (subst simulates_def, clarsimp)
  by (metis halp simulates_helper)
  







lemma similar_coinduct:"(Q,P) \<in> X \<Longrightarrow>
(\<And>p q q' s s' l.
    (q,p) \<in> X \<Longrightarrow> (q,s) \<rightarrow>l (q', s') \<Longrightarrow> \<exists>p'. (p, s) \<rightarrow>l (p',s') \<and> (q',p') \<in> (X \<union> similar)) \<Longrightarrow>
  (\<And>p q.
    (q,p) \<in> X \<Longrightarrow> terms q \<subseteq> terms p \<and> aborts q \<subseteq> aborts p) \<Longrightarrow>
P \<leadsto> Q"
  apply (erule similar.coinduct)
  apply (atomize)
  apply (clarsimp simp: simulates_def)
  done

lemma strengthen_simulation: "\<exists>p'. (p, s) \<rightarrow>\<^sub>l (p', s') \<and> (q', p') \<in> Y \<Longrightarrow> \<exists>p'. (p, s) \<rightarrow>\<^sub>l (p', s') \<and> (q', p') \<in> X \<union> Y"
  apply (fastforce)
  done

lemma strengthen_simulation': "Z \<subseteq> X \<Longrightarrow> \<exists>p'. (p, s) \<rightarrow>\<^sub>l (p', s') \<and> (q', p') \<in> Z \<Longrightarrow> \<exists>p'. (p, s) \<rightarrow>\<^sub>l (p', s') \<and> (q', p') \<in> X"
  apply (fastforce)
  done


lemma choice_relation_thing: 
 "(p, s) \<rightarrow>\<^sub>l (p', s') \<Longrightarrow> (p, q) \<in> choice_relation X \<Longrightarrow>
   (\<And>s p q p' s' r. (p, q) \<in> X \<Longrightarrow> (p, q) \<in> simulates (choice_relation X)) \<Longrightarrow> 
 \<exists>q'. (q, s) \<rightarrow>\<^sub>l (q', s') \<and> (p', q') \<in> choice_relation X"
  apply (drule choice_relation_thingy[simplified simulates_def, simplified,rotated -1])
   apply (fastforce simp: simulates_def)
  apply (fastforce)
  done

lemma abort_helper: assumes hyp: "\<And>q p. ((q,p) \<in> X \<Longrightarrow> terms q \<subseteq> terms p \<and> aborts q \<subseteq> aborts p)"
  shows " (q, p) \<in> choice_relation X \<Longrightarrow> terms q \<subseteq> terms p \<and> aborts q \<subseteq> aborts p"
  apply (induction rule: choice_relation.inducts)
     apply (meson similar.cases)
    apply (erule hyp)
   apply blast
  apply (intro conjI)
   apply (clarsimp)
   apply (drule (1) bspec)
  apply (clarsimp)
   apply (metis UN_E in_mono)

  apply (clarsimp)
  apply (metis UN_E in_mono)
  done


lemma similar_coinduct':"(Q, P) \<in> X \<Longrightarrow>
(\<And>p q q' s s' l v. (q, p) \<in> X \<Longrightarrow> v \<in> q \<Longrightarrow> (l, (v, s), (q', s')) \<in> oper \<Longrightarrow> \<exists>p'. (p, s) \<rightarrow>\<^sub>l (p', s') \<and> ({q'}, p') \<in> X \<union> similar) \<Longrightarrow>
(\<And>p q. (q, p) \<in> X \<Longrightarrow> terms q \<subseteq> terms p \<and> aborts q \<subseteq> aborts p) \<Longrightarrow> P \<leadsto> Q"
  apply (rule similar_coinduct[where X="choice_relation X"], clarsimp)
  apply (clarsimp)
  apply (erule (1) choice_relation_thing)
  apply (clarsimp simp: simulates_def)
   apply (erule prooove; clarsimp)
   apply (meson choice_relation.simps)
  by (meson abort_helper)

lemma "{P} \<leadsto> {Choice P P}"
  apply (rule similar_coinduct'[where X="{(x,y). \<exists>p. y = {p} \<and> x = {Choice p  p}}"], clarsimp)
   apply (erule oper.cases; clarsimp)
  using  refines_refl apply blast
    apply (meson  oper_nondet.nondet refines_refl singletonI)
   apply (meson  oper_nondet.nondet refines_refl singletonI)
  by (clarsimp)

lemma choice_is_nondet: "{Choice P Q} ~ {P, Q}"
  apply (clarsimp simp: bisimulate_def, intro conjI)
   apply (rule similar_coinduct'[where X="{(x,y). \<exists>P Q. x = {Choice P Q} \<and> y = { P,Q}}"], clarsimp)
    apply (erule oper.cases; clarsimp)
      apply (meson abort_top insert_iff oper.abortIntro oper_nondet.nondet)
     apply (meson insertI1 oper_nondet.nondet refines_refl)
    apply (meson insertI2 oper_nondet.nondet refines_refl singletonI)
  apply (clarsimp)
  apply (rule similar_coinduct'[where X="{(x,y). \<exists>P Q. y = {Choice P Q} \<and> x = { P,Q}}"], clarsimp)
   apply (clarsimp)
   apply (meson oper_nondet_intros(11) oper_nondet_intros(12) refines_refl)
  apply (clarsimp)
  done

lemma bisimulateD1: "P ~ Q \<Longrightarrow> P \<leadsto> Q" unfolding bisimulate_def by clarsimp
lemma bisimulateD2: "P ~ Q \<Longrightarrow> Q \<leadsto> P" unfolding bisimulate_def by clarsimp

 




lemma choice_is_conj: "{P \<bar> Q} \<leadsto> {Conj P Q}"
  apply (rule refines_trans[OF choice_is_nondet[THEN bisimulateD1]])
  apply (rule similar_coinduct'[where X="{(x,y). \<exists>P Q. y = {P,Q} \<and> x = {Conj P Q}}"], clarsimp)
   apply (erule oper.cases; clarsimp)
      apply (meson abort_top insert_iff oper.abortIntro oper_nondet.nondet)
  
   apply (metis all_not_in_conv insert_iff oper_nondet.branch oper_nondet.nondet)
  apply (clarsimp)
  by (metis (no_types, lifting) Int_subset_iff abort_term inf_sup_absorb le_infI2 subset_trans sup_ge2)


lemma mono_nondet: "{P} \<leadsto> {P'} \<Longrightarrow> {P} \<union> R \<leadsto> {P'} \<union> R"
  apply (rule similar_coinduct[where X="choice_relation {}"])
    apply (rule choice_relation.multi)
    apply (clarsimp, intro conjI)
  apply (rule_tac x="{P}" in exI, clarsimp)
    apply (clarsimp)
    apply auto[1]
  apply (clarsimp)
  apply (erule (1) choice_relation_thing)
   apply (clarsimp simp: simulates_def)
  by (meson abort_helper empty_iff)

lemma mono_choice: " {P} \<leadsto> {P'} \<Longrightarrow> {Q} \<leadsto> {Q'} \<Longrightarrow> {P \<bar> Q} \<leadsto>  {P' \<bar> Q'}"
  apply (rule refines_trans[OF choice_is_nondet[THEN bisimulateD1]])
  apply (rule refines_trans[rotated, OF choice_is_nondet[THEN bisimulateD2]])
  by (metis (no_types, hide_lams) insert_commute insert_is_Un mono_nondet refines_trans)


quotient_type 'a prog = "'a program set" / "(~)"
  apply (intro equivpI reflpI sympI transpI; clarsimp?)
   apply (clarsimp simp: bisim_sym)
  using bisim_trans by blast


lemma sup_bisim: "\<forall>x\<in>set1. \<exists>xa\<in>set2. x ~ xa \<Longrightarrow> \<forall>y\<in>set2. \<exists>x\<in>set1. x ~ y \<Longrightarrow> \<Union> set1 ~ \<Union> set2"
 apply (clarsimp simp: bisimulate_def, intro conjI)
   apply (rule similar_coinduct'[where X="{(x,y). \<exists>a b. (\<forall>v\<in>a. \<exists>v'\<in>b. v \<leadsto> v' \<and> v' \<leadsto> v) \<and>
           x = \<Union>a \<and> y = \<Union>b}"], clarsimp)
     apply (rule_tac x="set1" in exI)
     apply (rule_tac x="set2" in exI)
     apply (clarsimp)
     apply auto[1]
    apply (clarsimp)
    apply (drule_tac  x="X" in bspec, assumption) 
    apply (clarsimp)
    apply (drule (2) simulatesD[rotated, OF oper_nondet.nondet, rotated])
  apply (clarsimp)
    apply (meson Union_upper choose_sub')
   apply (clarsimp)
   apply (intro conjI)
    apply (smt SUP_le_iff Union_upper image_iff similar.cases subset_antisym terms_def)
   apply (smt SUP_le_iff Union_upper image_iff similar.cases subset_antisym aborts_def)
apply (rule similar_coinduct'[where X="{(x,y). \<exists>a b. (\<forall>v\<in>a. \<exists>v'\<in>b. v \<leadsto> v' \<and> v' \<leadsto> v) \<and>
           x = \<Union>a \<and> y = \<Union>b}"], clarsimp)
     apply (rule_tac x="set2" in exI)
     apply (rule_tac x="set1" in exI)
     apply (clarsimp)
     apply auto[1]
    apply (drule_tac  x="X" in bspec, assumption) 
    apply (clarsimp)
    apply (drule (2) simulatesD[rotated, OF oper_nondet.nondet, rotated])
  apply (clarsimp)
    apply (meson Union_upper choose_sub')
   apply (clarsimp)
   apply (intro conjI)
    apply (smt SUP_le_iff Union_upper image_iff similar.cases subset_antisym terms_def)
  apply (smt SUP_le_iff Union_upper image_iff similar.cases subset_antisym aborts_def)
  done

lemma sup_sim: "\<forall>x\<in>set2. \<exists>xa\<in>set1. xa \<leadsto> x \<Longrightarrow>  \<Union> set1 \<leadsto> \<Union> set2"
   apply (rule similar_coinduct'[where X="{(x,y). \<exists>a b. (\<forall>v\<in>a. \<exists>v'\<in>b. v' \<leadsto> v ) \<and>
           x = \<Union>a \<and> y = \<Union>b}"], clarsimp)
     apply (rule_tac x="set2" in exI)
     apply (rule_tac x="set1" in exI)
     apply (clarsimp)+
    apply (drule_tac  x="X" in bspec, assumption) 
    apply (clarsimp)
    apply (drule (2) simulatesD[rotated, OF oper_nondet.nondet, rotated])
  apply (clarsimp)
    apply (meson Union_upper choose_sub')
   apply (clarsimp)
  apply (intro conjI; clarsimp)
   apply (metis (no_types, hide_lams) UN_E UN_I similar.cases subsetD terms_def)
  apply (metis (no_types, hide_lams) UN_E UN_I similar.cases subsetD aborts_def)
  done
  


lift_definition sup :: "'a prog set \<Rightarrow> 'a prog" is "(\<Union>)"
  apply (clarsimp simp: rel_set_def)
  apply (erule (1) sup_bisim)
  done
  
definition "choice p q = sup {p, q}"

lemma "choice p p = p"
  apply (clarsimp simp: choice_def, transfer, clarsimp)
  done

lemma nondet_abort[intro, simp]: "s \<in> aborts p  \<Longrightarrow> (p, s) \<rightarrow>\<beta> ({Prim Abort}, s')" 
  apply (clarsimp)
  apply (erule oper_nondet.nondet)
  by simp


definition "conjs p q = (\<Union>x\<in>(p \<union> {MAGIC}). \<Union>y\<in>(q \<union> {MAGIC}). {Conj x y}) "

definition "ands p q = (\<Union>x\<in>p. \<Union>y\<in>q. {And x y}) "


lemma union_greater[simp]: "P \<union> Q \<leadsto> Q"
  apply (rule similar_coinduct'[where X="{(x,y). \<exists>A. y = A \<union> x}"]; clarsimp)
   apply (fastforce)
  by (metis Un_iff oper_nondet.nondet)

lemma union_mono: "P \<leadsto> P' \<Longrightarrow> P \<union> Q \<leadsto> P' \<union> Q"
  apply (rule similar_coinduct'[where X="{(x,y). \<exists>A B C. A \<leadsto> B \<and>  x = B \<union> C \<and> y = A \<union> C}"]; clarsimp)
    apply (fastforce)
   apply (elim disjE; clarsimp?)
    apply (drule (2) simulatesD[ OF _ oper_nondet.nondet])
  apply (clarsimp)
    apply (meson choose_sub' sup.cobounded1)
   apply (meson Un_iff oper_nondet.nondet refines_refl)
  apply (safe)
   apply (metis UN_I similar.cases subset_iff terms_def)
  apply (metis UN_I similar.cases subset_iff aborts_def)
  done



lemma sim_union_ord: "P \<leadsto> Q \<longleftrightarrow> P \<union> Q ~ P" 
  apply (rule iffI)
   apply (clarsimp simp: bisimulate_def)
  apply (rule conjI)
    apply (metis inf_sup_aci(5) sup.idem union_mono)
   apply (metis inf_sup_aci(5) union_greater)
  by (meson bisimulateD2 refines_trans union_greater)


lemma rewrite_sets: "(\<Union>x\<in>R. P x) \<union> (\<Union>x\<in>R. Q x) = (\<Union>x\<in>R. P x \<union> Q x)"
  by auto

lemma no_magic_allowed[dest!]: "({MAGIC}, s) \<rightarrow>\<^sub>l (p', s') \<Longrightarrow> False"
  apply (erule oper_nondet.inducts[where P="\<lambda>\<beta> a s b s'. a = {MAGIC} \<longrightarrow> R \<beta> a s b s'" for R, THEN mp]; clarsimp)
  apply (erule oper.cases; clarsimp)
  done

lemma magic_empty[simp]: "{} ~ {MAGIC}"
  apply (clarsimp simp: bisimulate_def, intro conjI)
   apply (rule similar.simStep)
     apply (clarsimp simp: simulates_def)
     apply (meson choose_sub' empty_subsetI refines_refl)
    apply (clarsimp)+
   apply (rule similar.simStep; clarsimp?)
  by (clarsimp simp: simulates_def)

lemma sim_conj_magic: "abort x \<subseteq> aborts P \<Longrightarrow> P \<leadsto> {x \<sqdot> MAGIC}" 
  apply (rule similar_coinduct'[where X="{(x,y).  \<exists>r. abort r \<subseteq> aborts y  \<and> x = {Conj r MAGIC}}"];
            clarsimp)
   apply (erule oper.cases;clarsimp)
    apply (metis (no_types, hide_lams) aborts_def in_mono nondet_abort refines_refl)
  apply (meson no_magic_allowed oper_nondet.nondet singletonI)
  by (metis UN_E abort_term subset_eq)



abbreviation "assert R \<equiv> {test (abort R); Prim Abort}"

lemma conj_magic_abort[simp]: "{Conj R MAGIC} ~ {test (abort R) ; Prim Abort}"
  apply (clarsimp simp: bisimulate_def, intro conjI)
   apply (rule sim_conj_magic)
   apply (clarsimp)
 apply (rule similar_coinduct'[where X="{(x,y).  \<exists>r. x = {Prim (Test (abort r)) ; Prim Abort}  \<and> y = {Conj r MAGIC}}"];
            clarsimp)
  apply (erule oper.cases;clarsimp)
    apply fastforce
  apply (erule oper.cases;clarsimp)
  apply (erule oper.cases;clarsimp)
  by fastforce

lemma [dest!]:"(\<beta>, (MAGIC, sa), pr', s'a) \<in> oper  \<Longrightarrow> False"
  apply (erule oper.cases;clarsimp)
  done

lemma empty_no_move[dest!]:"{} \<leadsto> Q \<Longrightarrow> v \<in> Q \<Longrightarrow> (\<beta>, (v,s), v' , s') \<in> oper \<Longrightarrow> False"
  apply (drule simulatesD, erule (1) oper_nondet.nondet)
  apply (clarsimp)
  by (meson choose_sub' empty_subsetI no_magic_allowed)

lemma empty_no_aborts[simp, dest]:"{} \<leadsto> Q \<Longrightarrow> v \<in> Q \<Longrightarrow> abort v = {}"
  by blast

lemma insert_mono[intro]: "P \<leadsto> Q \<Longrightarrow> insert R P \<leadsto> insert R Q"
  by (metis inf_sup_aci(5) insert_is_Un union_mono)

lemma insert_mono'[intro]: "insert R P \<leadsto> Q \<Longrightarrow> insert R P \<leadsto> insert R Q"
  by (simp add: sim_union_ord)



lemma sup_simI[simp, intro]: "(\<And>x. x \<in> Q \<Longrightarrow> P \<leadsto> P' x) \<Longrightarrow> P \<leadsto> (\<Union>y\<in>Q. P' y)"
  apply (rule refines_trans[where q= "\<Union>{P}"], clarsimp)

  apply (rule sup_sim)
  apply (clarsimp)
  done


lemma sup_simI2[simp, intro]: "Q \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> Q \<Longrightarrow> P' x \<leadsto> P) \<Longrightarrow> (\<Union>y\<in>Q. P' y) \<leadsto> P "
  apply (rule refines_trans[rotated, where q= "\<Union>{P}"], clarsimp)

  apply (rule sup_sim)
  apply (fastforce)
  done



lemma sup_simI'[simp, intro]:  "(\<And>x. x \<in> R \<Longrightarrow> P x \<leadsto> Q x) \<Longrightarrow> (\<Union>x\<in>R. P x) \<leadsto> (\<Union>x\<in>R. Q x)"
  apply (rule sup_sim, clarsimp)
  apply (fastforce)
  done

lemma [intro!]:" s \<in> aborts P \<Longrightarrow> (\<exists>p'. (P, s) \<rightarrow>\<^sub>\<beta> (p', s') \<and> p' \<leadsto> {Prim Abort})"
   apply (clarsimp)
  by (metis UN_I aborts_def nondet_abort refines_refl)


lemma wconj_commute[simp, intro]: "{Conj P Q} \<leadsto> {Conj Q P}"

 apply (rule similar_coinduct'[where X="{(x,y).  \<exists>p q. x = {Conj p q}  \<and> y = {Conj q p}}"];
            clarsimp)
  apply (erule oper.cases; clarsimp)
   apply blast
  apply (fastforce)
  done

lemma sconj_commute[simp,intro]: "{And P Q} \<leadsto> {And Q P}"
apply (rule similar_coinduct'[where X="{(x,y).  \<exists>p q. x = {And p q}  \<and> y = {And q p}}"];
            clarsimp)
  apply (erule oper.cases; clarsimp)
   apply blast
  done



lemma magic_bot[simp]: "P \<leadsto> {MAGIC}" 
  apply (rule similar.simStep; clarsimp simp: simulates_def)
  done



lemma bisim_sim1: "Q ~ Q' \<Longrightarrow> P \<leadsto> Q' \<Longrightarrow> P \<leadsto> Q"
  apply (clarsimp simp: bisimulate_def)
  by auto

lemma union_sim1 [simp, intro]: "Q \<leadsto> P \<Longrightarrow> P \<union> Q ~ Q"
  by (simp add: sim_union_ord sup_commute)


lemma refines_trans_quad: "a \<leadsto> b \<Longrightarrow> c \<leadsto> d \<Longrightarrow> b \<leadsto> c  \<Longrightarrow> a \<leadsto> d"
  by auto

lemma and_nondet: "(\<beta>, (p,s), (p',s')) \<in> oper \<Longrightarrow> (\<beta>, (q, s), (q', s')) \<in> oper_nondet \<Longrightarrow>
       (\<beta>, (And p ` q , s), ((And p' ` q'),s')) \<in> oper_nondet" 
  apply (erule oper_nondet.inducts[where P="\<lambda>\<beta> a st b st'. (\<beta>, (p,st), (p', st')) \<in> oper \<longrightarrow> R \<beta> a st b st'" for R, THEN mp] )
    apply (clarsimp)
    apply (rule branch, clarsimp)
  apply (clarsimp)
  apply (rule_tac p="And p pa" in  nondet)
    apply (clarsimp simp: image_def)
    apply (erule (1) oper.andIntro)
   apply (clarsimp)
  apply (rule oper_nondet.branch)
  apply blast
   apply (fastforce)
  apply (assumption)
  done

lemma ands_mono: "P \<leadsto> Q \<Longrightarrow> ands R P \<leadsto> ands R Q"
  apply (clarsimp simp: ands_def)
  apply (rule sup_simI')
  apply (rule sup_simI)
 apply (rule similar_coinduct'[where X="{(x,y). \<exists>A B R v.  v \<in> B \<and> A \<leadsto> B \<and> y = (\<Union>y\<in>A. {R && y}) \<and> x = {R && v}}"]; clarsimp)
  apply (rule_tac x="P" in exI, clarsimp, fastforce)
   apply (erule oper.cases;clarsimp)
  apply (metis (no_types, lifting) UN_E UN_I aborts_def similar.cases subsetD)
     apply (drule (2) simulatesD[ OF _ oper_nondet.nondet])
     apply (clarsimp)
     apply (rule_tac x="And pl' ` q'" in exI)
   apply (intro conjI, clarsimp simp: conjs_def)
      apply (subgoal_tac "(\<Union>x\<in>A. {pl && x}) = And pl ` A")
       apply (simp only:)
  apply (erule (1) and_nondet)
       apply (clarsimp)+
    apply (rule UNION_singleton_eq_range)

  apply (metis UNION_singleton_eq_range insertI1)
  apply (safe; clarsimp)
   apply (metis (no_types, lifting) UN_E UN_I similar.cases subset_eq terms_def)
  by (metis (no_types, lifting) UN_E UN_I similar.cases subset_eq  aborts_def)

lemma ands_commute[simp]: "ands P R \<leadsto> ands R P"
  apply (unfold ands_def)
  apply (subst SUP_commute, clarsimp)
  done


lemma Union_conj_mono: "P \<leadsto> Q \<Longrightarrow> P \<noteq> {} \<Longrightarrow> (\<Union>x\<in>P. {Conj r x}) \<leadsto>  (\<Union>x\<in>Q. {Conj r x})"
 apply (rule sup_simI)
    apply (rule similar_coinduct'[where X="{(x,y). \<exists>A B R v. A \<noteq> {} \<and> v \<in> B \<and> A \<leadsto> B \<and> y = (\<Union>y\<in>A. {R \<sqdot> y}) \<and> x = {R \<sqdot> v}}"]; clarsimp)
  apply (rule_tac x="P" in exI, clarsimp, fastforce)
   apply (erule oper.cases;clarsimp)
  apply (metis (no_types, lifting) UN_E UN_I aborts_def similar.cases subsetD)
     apply (drule (2) simulatesD[ OF _ oper_nondet.nondet])
     apply (clarsimp)
     apply (rule_tac x="Conj pl' ` q'" in exI)
   apply (intro conjI, clarsimp simp: conjs_def)
      apply (subgoal_tac "(\<Union>x\<in>A. {pl \<sqdot> x}) = Conj pl ` A")
       apply (simp only:)
  apply (erule (1) conj_nondet)
       apply (clarsimp)+
    apply (rule UNION_singleton_eq_range)

  apply (metis UNION_singleton_eq_range insertI1 never_empty)
  apply (safe; clarsimp)
   apply (metis (no_types, lifting) UN_E UN_I similar.cases subset_eq terms_def)
  apply (fastforce)
  apply (metis (no_types, lifting) UN_E UN_I similar.cases subset_eq  aborts_def)
  by (metis (no_types, lifting) UN_E UN_I aborts_def similar.cases subsetD)

lemma wconj_mono[simp, intro]: "{Q} \<leadsto> {Q'} \<Longrightarrow> {Conj P Q} \<leadsto> {Conj P Q'}"
  apply (drule Union_conj_mono[where r=P], clarsimp)
  apply (clarsimp)
  done

lemma conjs_singleton_mono: "P \<leadsto> Q \<Longrightarrow> conjs {R} P \<leadsto> conjs {R} Q"
  apply (case_tac "P = {}")
   apply (unfold conjs_def, clarsimp)
   apply (rule insert_mono')+
  apply (subst insert_commute, rule insert_mono) 
  apply (rule bisim_sim1[where Q'="(\<Union>x\<in>Q. {R \<sqdot> x})"], rule union_sim1)
    apply (rule sup_simI)
    apply (rule refines_trans[rotated, OF wconj_commute], rule sim_conj_magic)
  
    apply blast
   apply (rule sup_simI)
  apply (rule wconj_mono)
   apply (metis Un_insert_right insert_absorb refines_trans_quad sup_bot_right union_greater)
  apply (clarsimp intro!: insert_mono)
  apply (rule refines_trans[where q="(\<Union>x\<in>P. {R \<sqdot> x})"])
   apply (clarsimp)
  apply (rule bisim_sim1[where Q'="(\<Union>x\<in>Q. {R \<sqdot> x})"])
  apply (rule union_sim1)
   apply (rule sup_simI')
   apply (rule refines_trans[OF wconj_commute], rule refines_trans[rotated, OF wconj_commute], rule wconj_mono, clarsimp)
  by (erule (1) Union_conj_mono)
   


lemma magic_conj_magic: "{MAGIC \<sqdot> MAGIC} ~ {MAGIC}" 
  by (simp add: bisimulate_def sim_conj_magic)


lemma union_mono2: "P \<leadsto> P' \<Longrightarrow> R \<leadsto> R' \<Longrightarrow> P \<union> R \<leadsto> P' \<union>  R'"
  by (metis inf_sup_aci(5) refines_trans union_mono)

lemma conjs_mono: "P \<leadsto> Q \<Longrightarrow> conjs R P \<leadsto> conjs R Q"
  apply (case_tac "P = {}")
  apply (clarsimp simp: conjs_def)
   apply (rule insert_mono')
   apply (subst insert_is_Un, rule union_mono2)
    apply (rule sup_simI)
    apply (smt abort.simps(8) bisim_sim1 bisimulateD1 conj_magic_abort empty_no_aborts refines_trans_quad wconj_commute)
   apply (rule sup_simI')
   apply (rule insert_mono')
   apply (rule sup_simI)
  apply (rule wconj_mono)
   apply (metis Operational.insert_mono insert_absorb refines_trans sup_bot_right union_greater)
  apply (unfold conjs_def, rule sup_simI')
  apply (clarsimp simp: conjs_def)
  apply (elim disjE, clarsimp)
   apply (intro insert_mono)
   apply (rule sup_simI)
   apply (rule refines_trans[OF _ wconj_commute], rule sim_conj_magic)
   apply (clarsimp)
   apply (metis (no_types, hide_lams) UN_E UN_I aborts_def similar.cases subsetD)
  apply (intro insert_mono)
  by (erule (1) Union_conj_mono)


lemma conjs_commute[simp]: "conjs p q \<leadsto> conjs q p" 
  apply (unfold conjs_def, subst SUP_commute)
  apply (clarsimp)
  apply (intro insert_mono)
  apply (rule union_mono2)
   apply (rule sup_simI')
   apply (clarsimp)
  apply (rule sup_simI')
  apply (subst insert_is_Un, subst insert_is_Un, rule union_mono2, clarsimp)
  apply (rule sup_simI', clarsimp)
  done

lift_definition conj :: "'a prog \<Rightarrow> 'a prog \<Rightarrow> 'a prog" is "conjs"
  apply (subst bisimulate_def, intro conjI) 

   apply (meson bisimulateD2 conjs_commute conjs_mono refines_trans)
  apply (meson bisimulateD1 conjs_commute conjs_mono refines_trans)
  done

lift_definition sand :: "'a prog \<Rightarrow> 'a prog \<Rightarrow> 'a prog" is "ands"
  apply (subst bisimulate_def, intro conjI) 

   apply (meson bisimulateD2 ands_commute ands_mono refines_trans)
   apply (meson bisimulateD1 ands_commute ands_mono refines_trans)
  done


lift_definition ref :: "'a prog \<Rightarrow> 'a prog \<Rightarrow> bool" is "(\<leadsto>)"
  by (auto simp: bisimulate_def)

lift_definition crash :: "'a prog" is "{Prim Abort}" done

lift_definition magic :: "'a prog" is "{MAGIC}" done

lemma sup_refinesl: "x \<in> p \<Longrightarrow> P x \<leadsto> R \<Longrightarrow> (\<Union>x\<in>p. P x) \<leadsto> R" sorry


lemma refines_eq: "P = Q \<longleftrightarrow> ref P Q \<and> ref Q P"
  apply (transfer, clarsimp simp: bisimulate_def, safe)
  done



lemma refines_choice: "ref P Q \<longleftrightarrow> choice P Q = P"
  apply (clarsimp simp: choice_def, transfer)
  apply (safe)
   apply (simp add: sim_union_ord)
  apply (simp add: sim_union_ord)
  done

lemma sand_smaller: "{x} \<leadsto> {x && xa}"
  apply (rule similar_coinduct'[where X="{(x,y). \<exists>v v'.  y = {v} \<and> x =  {v && v'}}"]; clarsimp)
  apply (erule oper.cases; clarsimp)
  by (meson oper_nondet.nondet singleton_iff)



lemma refines_in[simp]:  "x \<in> P \<Longrightarrow> P \<leadsto> {x}"
  by (metis Set.set_insert Un_insert_right sup_bot_right union_greater)


lemma refines_every[intro]:  "(\<And>x. x \<in> Q \<Longrightarrow> P \<leadsto> {x}) \<Longrightarrow> P \<leadsto> Q"
  apply (rule similar_coinduct'[where X="{(x,y). \<forall>v\<in>x. y \<leadsto> {v}}"]; clarsimp)
   apply (meson insertI1 oper_nondet.nondet similar.cases simulates_helper)
  apply (safe)
   apply (metis cSup_singleton image_empty image_insert similar.cases subset_iff terms_def)
  apply (metis cSup_singleton image_empty image_insert similar.cases subset_iff aborts_def)
  done

lemma ands_idemp[simp]: "ands P P ~ P"
  apply (clarsimp simp: ands_def)
  apply (clarsimp simp: bisimulate_def, rule conjI)
   apply (rule sup_simI)+
   apply (rule refines_trans[OF _ sand_smaller], clarsimp)
  apply (rule refines_every)
  apply (rule sup_refinesl, assumption)
  apply (rule sup_refinesl, assumption)
  apply (rule similar_coinduct'[where X="{(x,y). \<exists>v. y = {v && v} \<and> x = {v}}"]; clarsimp)
  by blast


declare bisimulateD1[dest]
declare bisimulateD2[dest]


lemma refines_sand: "ref P Q \<longleftrightarrow> sand P Q = Q"
  apply (transfer)
  apply (rule iffI)
  
   apply (clarsimp simp: bisimulate_def, safe)
  apply (clarsimp simp: ands_def)

    apply (intro sup_simI)
    apply (rule refines_trans[OF _ sconj_commute])
    apply (rule refines_trans[OF _ sand_smaller])
    apply (simp add: sim_union_ord insert_absorb)
   apply (rule refines_trans[OF ands_commute], erule refines_trans[OF ands_mono])   
   apply (simp add: bisimulateD1)
  apply (clarsimp simp: bisimulate_def)
  apply (erule refines_trans[rotated])
  apply (clarsimp simp: ands_def)
  apply (intro sup_simI)
    apply (rule refines_trans[OF _ sand_smaller])
  apply (clarsimp)
  done


lemma "{MAGIC} \<union> P ~ P"
  by (metis Un_commute magic_bot sim_union_ord)

lemma sand_commute: "sand p q = sand q p"
  by (transfer, clarsimp simp: bisimulate_def)


lemma abort_sand: "{Prim Abort && P} ~ {P}"
  apply (clarsimp simp: bisimulate_def)
  apply (intro conjI)
   apply (rule similar_coinduct'[where X="{(x,y). \<exists>A. x = {Prim Abort && A} \<and> y = {A}}"]; clarsimp)
   apply (erule oper.cases; clarsimp)
   apply (rule_tac x="{pr'}" in exI, clarsimp)
   apply (rule conjI)
    apply (rule oper_nondet.nondet, fastforce, assumption)
   apply (rule disjI1)
   apply (erule oper.cases; clarsimp)
  apply (rule similar_coinduct'[where X="{(x,y). \<exists>A. y = {Prim Abort && A} \<and> x = {A}}"]; clarsimp)
  apply (rule_tac x="{Prim Abort && q'}" in exI, clarsimp)
  done


lemma sand_assoc[simp]: "sand p (sand q r) = (sand (sand p q) r)"
  apply (transfer, clarsimp simp: bisimulate_def)
  apply (intro conjI)
   apply (clarsimp simp: ands_def)
   apply (intro sup_simI | elim sup_refinesl)+
   apply (rule similar_coinduct'[where X="{(x,y). \<exists>A B C. y = {And (And A B) C} \<and> x = {And A (And B C)}}"]; clarsimp)
    apply (safe)
   apply (erule oper.cases; clarsimp)
   apply (erule oper.cases; clarsimp) back
  apply (rule_tac x="{(pl' && Prim Abort) && Prim Abort}" in exI)
    apply (clarsimp)
    apply (meson abort_sand bisimulate_def refines_trans sconj_commute)
   apply blast
 apply (clarsimp simp: ands_def)
  apply (intro sup_simI | elim sup_refinesl)+
  apply (rule similar_coinduct'[where X="{(x,y). \<exists>A B C. x = {And (And A B) C} \<and> y = {And A (And B C)}}"]; clarsimp)
    apply (safe)
   apply (erule oper.cases; clarsimp)
   apply (erule oper.cases; clarsimp) 
  apply (rule_tac x="{Prim Abort && (Prim Abort && pr')}" in exI)
    apply (clarsimp)
    apply (meson abort_sand bisimulate_def refines_trans sconj_commute)
  apply blast
  done

lemma conj_commute: "conj p q = conj q p"
  apply (transfer)
  apply (clarsimp simp: bisimulate_def)
  done

lemma choice_assoc: "choice p (choice q r) = choice (choice p q) r"
  apply (clarsimp simp: choice_def, transfer)
  by (metis (no_types, lifting) Union_insert bisim_refl inf_sup_aci(5) insert_commute)

lemma insert_mono2: "{P} \<leadsto> {P'} \<Longrightarrow> Q \<leadsto> Q' \<Longrightarrow> insert P Q \<leadsto> insert P' Q'" 
  using union_mono2 by force 

lemma insert_drop: "Q \<leadsto> Q' \<Longrightarrow> insert P Q \<leadsto> Q'"
  by (metis insert_is_Un refines_trans union_greater) 


lemma bisim_coinduct: "(Q, P) \<in> X \<union> converse X \<Longrightarrow>
(\<And>p q q' s s' l v. (q, p) \<in> X \<Longrightarrow> v \<in> q \<Longrightarrow> (l, (v, s), q', s') \<in> oper \<Longrightarrow> \<exists>p'. (p, s) \<rightarrow>\<^sub>l (p', s') \<and> ({q'}, p') \<in> X \<union> converse X \<union> similar) \<Longrightarrow>
(\<And>p q q' s s' l v. (p, q) \<in> X \<Longrightarrow> v \<in> q \<Longrightarrow> (l, (v, s), q', s') \<in> oper \<Longrightarrow> \<exists>p'. (p, s) \<rightarrow>\<^sub>l (p', s') \<and> ({q'}, p') \<in> X \<union> converse X \<union> similar) \<Longrightarrow>
(\<And>p q. (q, p) \<in> X \<Longrightarrow> terms q = terms p \<and> aborts q = aborts p) \<Longrightarrow> P ~ Q"
  apply (unfold bisimulate_def, rule conjI)
  apply (rule similar_coinduct'[where X="X \<union> converse X"])
     apply blast
    apply (metis Un_iff converse_iff)
   apply (metis Un_iff converse_iff subsetI)
 apply (rule similar_coinduct'[where X="X \<union> converse X"])
     apply blast
    apply (metis Un_iff converse_iff)
  apply (metis Un_iff converse_iff subsetI)
  done



lemma wconj_assoc[simp]: "{Conj p (Conj q r)} ~ {Conj (Conj p q) r}"
  apply (rule bisim_coinduct[where X="{(x,y). \<exists>A B C. y = {Conj (Conj A B) C} \<and> x = {Conj A (Conj B C)}}"]; clarsimp)
    apply (safe)
   apply (erule oper.cases; clarsimp)
   apply (erule oper.cases; fastforce) 
  apply (erule oper.cases; clarsimp)
  by (erule oper.cases; fastforce)

lemma un_drop: "Q \<leadsto> R \<Longrightarrow> (P \<union> Q) \<leadsto> R" 
  by (meson refines_trans union_greater)

notation conj (infixr "@@" 50)

lemma conj_assoc: "conj p (conj q r) = conj (conj p q) r"
  apply (transfer)
  apply (clarsimp simp: bisimulate_def, intro conjI)
  apply (unfold conjs_def)
  apply (intro sup_simI)
   apply ( clarsimp)
   apply (rule insert_drop)+
   apply (elim disjE; clarsimp simp: sim_conj_magic)
  apply (rule refines_trans[where q="{MAGIC}"]; clarsimp)
         apply (meson bisimulateD2 magic_conj_magic refines_trans wconj_mono)
        apply (rule_tac q="{Conj xb MAGIC}" in refines_trans)
         apply (rule sim_conj_magic)
  apply (clarsimp)
        apply (smt abort.simps(4) abort.simps(8) bisim_sim1 bisimulateD1 conj_magic_abort
                                   refines_trans_quad sup_bot.left_neutral wconj_commute)
       apply (rule refines_trans[rotated, OF wconj_commute], rule sim_conj_magic, clarsimp)
       apply auto[1]
      apply ( rule sim_conj_magic, clarsimp)
       apply (rule_tac q="{Conj x MAGIC}" in refines_trans)
      apply (rule sim_conj_magic, clarsimp)
     apply (simp add: bisimulateD2 magic_conj_magic)
       apply (rule_tac q="{Conj (Conj x xb) MAGIC}" in refines_trans)

     apply ( rule sim_conj_magic, clarsimp)
     apply (intro conjI; clarsimp)
    apply (clarsimp)
    defer
    apply (erule disjE; clarsimp)
     apply (rule_tac q="{Conj (Conj x xb) MAGIC}" in refines_trans)
      apply ( rule sim_conj_magic, clarsimp)
     apply (intro conjI; clarsimp)
     apply (simp add: bisimulateD2)
    apply (intro un_drop  | elim sup_refinesl)+
  apply (rule insert_drop)
     apply (clarsimp)
    apply (rule un_drop)
    apply (rule sup_refinesl, assumption)
  apply (rule insert_drop)
    apply (rule sup_refinesl, assumption)
    apply (clarsimp simp: bisimulateD2)
   apply (intro sup_simI)
   apply clarsimp
   apply (elim disjE; clarsimp simp: sim_conj_magic)
        apply ( rule refines_trans[OF _ wconj_commute], rule sim_conj_magic, clarsimp)
        apply blast
       apply (rule sim_conj_magic, clarsimp)
      apply (rule sim_conj_magic, clarsimp)
      apply auto[1]
     apply (metis (no_types, lifting) bisimulateD1 inf_sup_aci(5) insert_drop sup_refinesl un_drop wconj_assoc)
    apply (rule_tac q="{Conj (Conj xa xb) MAGIC}" in refines_trans)
      apply (rule sim_conj_magic, clarsimp)
     apply blast
    apply (meson bisimulateD2 refines_trans wconj_assoc wconj_commute wconj_mono)
   apply (elim disjE; clarsimp)
    apply (rule_tac q="{Conj (Conj xa xb) MAGIC}" in refines_trans)
  apply (rule sim_conj_magic, clarsimp)
     apply blast
    apply (meson bisimulateD2 refines_trans wconj_assoc wconj_commute wconj_mono)
  apply (rule insert_drop)
   apply (rule insert_drop)      
   apply (intro un_drop  | elim sup_refinesl)+
   apply (rule insert_drop, clarsimp)      
   apply (rule insert_drop)      
   apply (intro un_drop  | elim sup_refinesl)+
   apply (rule insert_drop, clarsimp)      
   apply (intro un_drop  | elim sup_refinesl)+
    apply (meson bisimulateD2 refines_trans wconj_assoc wconj_commute wconj_mono)
  by (meson bisimulateD2 refines_trans wconj_assoc wconj_commute wconj_mono)


lemma refines_abort_subset[simp, dest]: "P \<leadsto> P' \<Longrightarrow> aborts P' \<subseteq> aborts P"
  apply (erule similar.cases)
  by auto

lemma refines_abort_subset'[simp, dest]: "P \<leadsto> P' \<Longrightarrow> x \<in> aborts P' \<Longrightarrow> x \<in> aborts P"
  apply (erule similar.cases)
  by auto

instantiation prog :: (type) order 
begin
definition "less_eq_prog = (\<lambda>x y. ref y x)"
definition "less_prog (p :: 'state prog) q \<equiv> (p \<le> q) \<and> \<not>(q \<le> p)"  
instance
  apply(intro_classes)
     apply (clarsimp simp: less_prog_def)
    apply (clarsimp simp: less_eq_prog_def, transfer, clarsimp simp: similarp_similar_eq)
  apply (clarsimp simp: less_eq_prog_def, transfer, clarsimp simp: similarp_similar_eq)
  using refines_trans apply auto[1]
  apply (clarsimp simp: less_eq_prog_def, transfer, clarsimp simp: similarp_similar_eq bisimulate_def)
  done

end

instantiation prog :: (type) semilattice_sup 
begin
definition "sup_prog = choice"
instance
  apply(intro_classes; clarsimp simp: sup_prog_def)
    apply (clarsimp simp: less_eq_prog_def, transfer, clarsimp simp: similarp_similar_eq)
    apply (clarsimp simp: choice_def, transfer)
    apply auto[1]

    apply (clarsimp simp: less_eq_prog_def, transfer, clarsimp simp: similarp_similar_eq)
   apply (clarsimp simp: choice_def, transfer)
    apply auto[1]
  by (simp add: choice_assoc less_eq_prog_def refines_choice)
end

instantiation prog :: (type) semilattice_inf
begin
definition "inf_prog = sand"
instance
  apply(intro_classes; clarsimp simp: inf_prog_def)
    apply (clarsimp simp: less_eq_prog_def, transfer)
    apply (clarsimp simp: ands_def)
  apply (intro sup_simI)
    apply (meson refines_in refines_trans sand_smaller)
apply (clarsimp simp: less_eq_prog_def, transfer)
    apply (clarsimp simp: ands_def)
   apply (intro sup_simI)
   apply (meson refines_in refines_trans_quad sand_smaller sconj_commute)
  by (metis less_eq_prog_def refines_sand sand_assoc)
end

instantiation prog :: (type) bounded_lattice begin
definition "bot_prog = magic"
definition "top_prog = crash"
instance
  by (intro_classes; clarsimp simp: bot_prog_def top_prog_def less_eq_prog_def, transfer, clarsimp)
end

lemma union_refinesI: "P \<leadsto> Q \<Longrightarrow> P \<leadsto> Q' \<Longrightarrow> P \<leadsto> (Q \<union> Q')"
  by (metis sup.idem union_mono2)
thm sup.idem

instantiation prog :: (type) distrib_lattice begin
instance
  apply (intro_classes)
  apply (rule order_antisym)
   apply (subst le_inf_iff, intro conjI; clarsimp)
    apply (simp add: inf.coboundedI1)
   apply (simp add: inf.coboundedI2)
  apply (clarsimp simp: sup_prog_def inf_prog_def choice_def less_eq_prog_def, transfer)
  apply (clarsimp simp: ands_def)
  apply (intro union_refinesI sup_simI)
     apply (metis inf_sup_aci(5) refines_in refines_trans sand_smaller un_drop)
  apply (metis inf_sup_aci(5) refines_in refines_trans sand_smaller un_drop)
   apply (metis inf_sup_aci(5) refines_in refines_trans_quad sand_smaller sconj_commute un_drop)
  apply (rule un_drop)
  by auto
end

find_theorems Sup Inf

lemma complete_lattice_helper: " \<forall>x\<in>A. ref x (Operational.sup {b. \<forall>a\<in>A. ref a b})"
  apply (transfer, clarsimp)
  apply (rule_tac q="\<Union>{x}" in refines_trans, clarsimp)
  apply (rule sup_sim; clarsimp)
  done

lemma sup_greatest: " \<forall>x\<in>A. x \<le> sup A"
  apply (unfold less_eq_prog_def, transfer)
  apply (clarsimp)
  by (meson UnionI refines_every refines_in)

lemma sup_lowerbound: " (\<forall>x\<in>A. x \<le> z) \<Longrightarrow> sup A \<le> z"
  apply (unfold less_eq_prog_def, transfer)
  apply (rule_tac q="\<Union>{z}" in refines_trans, clarsimp)
  by (rule sup_sim; clarsimp)
 
lemma complete_lattice_helper': "(\<forall>x\<in>A. z \<le> x) \<Longrightarrow> z \<le> sup {b. \<forall>a\<in>A. b \<le> a}"
  apply (clarsimp simp: less_eq_prog_def, transfer)
  apply (rule_tac q="\<Union>{z}" in refines_trans[rotated], clarsimp)
  apply (rule sup_sim; clarsimp)
  using refines_refl by blast

instantiation prog :: (type) complete_lattice begin

definition "Sup_prog = sup"
definition "Inf_prog A = sup {b. \<forall>a\<in>A. b \<le> a}"
instance
  apply (intro_classes; clarsimp simp: Inf_prog_def Sup_prog_def)
       apply (clarsimp simp: Inf_prog_def less_eq_prog_def)
       apply (simp add: complete_lattice_helper)
      apply (simp add: complete_lattice_helper')
     apply (simp add: sup_greatest)
    apply (simp add: sup_lowerbound)
   apply (clarsimp simp: top_prog_def, transfer)
   apply (clarsimp simp: bisimulate_def)
  apply (clarsimp simp: bot_prog_def, transfer, clarsimp)
  done
end




lemma sup_simI1[]:"(\<And>x. x \<in> Q \<Longrightarrow> P \<leadsto>  x) \<Longrightarrow> P \<leadsto> \<Union> (Q)"
  by (metis ccpo_Sup_singleton insertI1 sup_sim)


lemma union_step: "(\<And>x y. x \<in> p \<Longrightarrow> (\<beta>, (x, s), (y, s')) \<in> oper \<Longrightarrow> (f x, s) \<rightarrow>\<beta> (g y, s')) \<Longrightarrow>
    (p, s) \<rightarrow>\<^sub>\<beta> (p', s') \<Longrightarrow>  ((\<Union>x\<in>p. f x), s) \<rightarrow>\<^sub>\<beta> ((\<Union>x\<in>p'. g x), s')"
  apply (erule oper_nondet.inducts[where P="\<lambda>l a st b st'. \<beta> = l \<and> a = p \<and> st = s \<and> st' = s' \<longrightarrow> R \<beta> a st b st'" for R, THEN mp]; clarsimp)
    apply (rule_tac v="f pa" in choose_sub')
     apply (drule_tac x=pa in meta_spec)
     apply (drule_tac x=q in meta_spec)
     apply (drule (1) meta_mp)
  apply (drule (1) meta_mp)
  apply blast
   apply blast
  by (smt UNION_empty_conv(1) UN_E choose_single ex_in_conv oper_nondet.branch)


lemma "(p, s) \<rightarrow>\<^sub>\<beta> (p', s') \<Longrightarrow> (q, s) \<rightarrow>\<^sub>\<beta> (q', s') \<Longrightarrow> ((\<Union>x\<in>p. \<Union>y\<in>q. {x && y}), s) \<rightarrow>\<^sub>\<beta> ((\<Union>x\<in>p'. \<Union>y\<in>q'. {x && y}), s')"
  apply (rule union_step)
   apply (rule union_step)
    apply (rule oper_nondet.nondet)
     apply (fastforce)
  apply (erule (1) oper.andIntro)
   apply blast
  apply blast
  done


lemma sand_inf: "sand P Q = Inf {P, Q}"
  apply (clarsimp simp: Inf_prog_def, transfer)
  apply (rule order_antisym; clarsimp simp: less_eq_prog_def)
   apply (transfer)
   apply (clarsimp simp: ands_def)
   apply (rule sup_sim; clarsimp)
   apply (rule_tac x="(\<Union>y\<in>Q. {x && y})" in exI; clarsimp)
   apply (intro conjI sup_simI)
    apply (meson refines_in refines_trans sand_smaller)
   apply (meson refines_in refines_trans sand_smaller sconj_commute)
  apply (transfer, clarsimp simp: ands_def)
  apply (case_tac "P = {}"; clarsimp?)
   apply (smt Union_iff mem_Collect_eq refines_every refines_in refines_trans)
  apply (case_tac "Q = {}"; clarsimp?)
   apply (smt Union_iff mem_Collect_eq refines_every refines_in refines_trans)
  apply (rule sup_simI1, clarsimp)
  apply (rule similar_coinduct'[where X="{(x,y). \<exists>P Q. P \<noteq> {} \<and> Q \<noteq> {} \<and> P \<leadsto> x \<and> Q \<leadsto> x \<and> y = (\<Union>x\<in>P. \<Union>y\<in>Q. {x && y})}"]; clarsimp  )
    apply (rule_tac x=P in exI, clarsimp,  rule_tac x=Q in exI, clarsimp)
     apply (drule (2) simulatesD[ OF _ oper_nondet.nondet])
     apply (drule (2) simulatesD[ OF _ oper_nondet.nondet])
   apply (clarsimp)
   apply (rule exI, rule conjI)
    apply (rule union_step)
  apply (rule union_step)
      apply (erule (1) nondet[rotated, OF oper.andIntro]) back back back
      apply (clarsimp)
     apply (assumption)
    apply (assumption)
   apply (clarsimp)
   apply (metis oper_nondet_nonempty)
  apply (safe; clarsimp)
     apply (metis UN_E UN_I similar.cases subsetD terms_def)
  apply (metis UN_E UN_I similar.cases subsetD terms_def)
   apply (metis UN_E UN_I similar.cases subsetD aborts_def)
  apply (metis UN_E UN_I similar.cases subsetD aborts_def)
  done


definition "seqs p q \<equiv> \<Union>x\<in>p. (\<Union>y\<in>(q \<union> {MAGIC}). {Seq x y})"


lemma magic_seq[simp]: "{x}  \<leadsto> {x ; MAGIC}"
  apply (rule similar_coinduct'[where X="{(x,y). \<exists>P. y = {P} \<and> x = {P;MAGIC} }"]; clarsimp  )
  apply (erule oper.cases; clarsimp)
  using oper_nondet.nondet by fastforce


lemma magic_seq'[simp]: "{x ; MAGIC}  \<leadsto> {x}"
  apply (rule similar_coinduct'[where X="{(x,y). \<exists>P. x = {P} \<and> y = {P;MAGIC} }"]; clarsimp  )
   apply blast
  apply (induct_tac P; clarsimp)
  oops

lemma magic_seq'[simp]: "{MAGIC} \<leadsto> {MAGIC ; j}"
  apply (rule similar_coinduct'[where X="{(x,y). \<exists>j. y = {MAGIC} \<and> x = {MAGIC; j}}"]; clarsimp)
  apply (erule oper.cases; clarsimp)
  done

lemma terminate_sim_singleton: "s \<in> terminate P \<Longrightarrow> A \<leadsto> {P} \<Longrightarrow> \<exists>v. v \<in> A \<and> s \<in> terminate v"
  by (metis UN_E UN_I insertI1 similar.cases subsetD terms_def)

lemma seqs_mono_l: "p \<leadsto> q \<Longrightarrow> seqs p r \<leadsto> seqs q r"
  apply (unfold seqs_def)
  thm sup_simI'
  apply (subst SUP_commute, subst SUP_commute, rule sup_simI')
  apply (clarsimp)
  apply (elim disjE; clarsimp?)
   apply (rule sup_simI)
     apply (rule similar_coinduct'[where X="{(x,y). \<exists>A B v. A \<leadsto> B \<and> y = (\<Union>x\<in>A. {x ; MAGIC}) \<and> x = {v ; MAGIC} \<and> v \<in> B }"]; clarsimp)
     apply blast
    apply (erule oper.cases; clarsimp)
     apply fastforce
   apply (drule (2) simulatesD[ OF _ oper_nondet.nondet])
    apply (clarsimp)
    apply (rule_tac x="\<Union>x\<in>q'. {x ; MAGIC}" in exI)
    apply (intro conjI)
     apply (erule union_step[rotated])
     apply blast
    apply blast
   apply (fastforce)
  apply (rule sup_simI)
  apply (case_tac "p={}")
   apply (clarsimp)
   apply (rule similar_coinduct'[where X="{(x,y). \<exists> B v v'. {} \<leadsto> B \<and> y = {} \<and> x = {v ; v'} \<and> v \<in> B }"]; clarsimp)
     apply meson
  apply (erule oper.cases; clarsimp)
      apply (metis UN_E UN_I empty_iff similar.cases subsetD terms_def)
     apply blast
    apply (metis UN_E UN_I all_not_in_conv similar.cases subsetD terms_def)
 
  apply (metis (no_types, hide_lams) UN_E UN_I ex_in_conv inf_bot_left similar.cases subsetD terms_def)
  apply (rule similar_coinduct'[where X="{(x,y). \<exists>A B v v'. A \<noteq> {} \<and> A \<leadsto> B \<and> y = (\<Union>x\<in>A. {x ; v'}) \<and> x = {v ; v'} \<and> v \<in> B }"]; clarsimp)
    apply blast
   apply (erule oper.cases; clarsimp)
  apply (metis (no_types, lifting) UN_E UN_I aborts_def similar.cases subsetD terms_def)
   apply (drule (2) simulatesD[ OF _ oper_nondet.nondet])
    apply (clarsimp)
    apply (rule_tac x="\<Union>x\<in>q'. {x ; pr}" in exI)
    apply (intro conjI)
     apply (erule union_step[rotated])
     apply blast
  apply (metis insertI1 oper_nondet_nonempty)
   apply (rule_tac x=" {pr'}" in exI, clarsimp)
   apply (drule_tac A=A in terminate_sim_singleton)
     apply (meson refines_in refines_refl refines_trans_quad)
    apply (clarsimp)
    apply (rule_tac p="v ; pr" in nondet)
  apply (fastforce)

   apply (erule (1) oper.seqStep)
  apply (safe; clarsimp)
     apply (meson refines_in refines_trans terminate_sim_singleton)
    apply fastforce
   apply fastforce
     apply (meson refines_in refines_trans terminate_sim_singleton)
  done

lemma sim_insertI: "P \<leadsto> {A} \<Longrightarrow> P \<leadsto> B \<Longrightarrow>  P \<leadsto> insert A B"
  by (metis insert_is_Un union_refinesI) 

lemma seqs_mono_r: "p \<leadsto> q \<Longrightarrow> seqs r p \<leadsto> seqs r q"
  apply (unfold seqs_def)
  apply (case_tac "p = {}", clarsimp)
   apply (rule sup_simI')
   apply (rule sim_insertI, clarsimp)
   apply (rule sup_simI)
   apply (rule similar_coinduct'[where X="{(x,y). \<exists> B v v'. {} \<leadsto> B \<and> y = {v ; MAGIC} \<and> x = {v ; v'} \<and> v' \<in> B }"]; clarsimp)
     apply meson
    apply (erule oper.cases; clarsimp)
     apply (metis oper_nondet_intros(6))
    apply blast
   apply (meson equals0D refines_in refines_trans terminate_sim_singleton)
  apply (rule sup_simI')
  apply (clarsimp)
  apply (rule insert_mono)
   apply (rule sup_simI)
  apply (rule similar_coinduct'[where X="{(x,y). \<exists>A B v v'. A \<noteq> {} \<and> A \<leadsto> B \<and> y = (\<Union>x\<in>A. {v' ; x}) \<and> x = {v' ; v} \<and> v \<in> B }"]; clarsimp)
    apply blast
   apply (erule oper.cases; clarsimp)
  apply (metis (no_types, lifting) UN_E UN_I aborts_def similar.cases subsetD terms_def)
    apply (rule_tac x="\<Union>x\<in>A. {pl' ; x}" in exI)
    apply (intro conjI)
  apply (rule branch)
      apply blast
     apply (clarsimp)
     apply (meson UN_upper choose_sub' oper_nondet_intros(6))
    apply blast
   apply (drule (2) simulatesD[ OF _ oper_nondet.nondet], clarsimp)
   apply (rule_tac x="\<Union>x\<in>q'. {x}" in exI, rule conjI)
    apply (erule union_step[rotated])
    apply (fastforce)
   apply simp
  by (smt Int_iff SUP_le_iff UnI1 UnI2 aborts_def similar.cases subsetD subsetI terms_def)


lift_definition seq :: "'a prog \<Rightarrow> 'a prog \<Rightarrow> 'a prog" is "seqs"
  apply (clarsimp simp: bisimulate_def)
  by (meson refines_trans seqs_mono_l seqs_mono_r)

lemma magic_seq_magic[simp]: "{MAGIC; MAGIC} ~ {MAGIC}"
  by (simp add: bisimulate_def)

lemma seq_magic_absorb_l: "seq magic p = magic" 
  apply (transfer)
  apply (clarsimp simp: seqs_def)
  apply (clarsimp simp: bisimulate_def)
  apply (rule sim_insertI; clarsimp)
  done

lift_definition skip :: "'a prog" is "{TAU}" done

lemma seq_monoid_r[simp]: "seq p skip = p"  
  apply (transfer)
  apply (clarsimp simp: seqs_def)
  apply (clarsimp simp: bisimulate_def, intro conjI)
   apply (rule sup_simI)
   apply (rule sim_insertI; clarsimp?)
    apply (erule refines_trans[OF refines_in])
    apply (rule similar_coinduct'[where X="{(x,y). \<exists>v. y = {v} \<and> x = {v; TAU}}"]; clarsimp)
    apply (erule oper.cases; clarsimp)
  using oper_nondet.nondet apply fastforce
  apply (erule oper.cases; clarsimp)
   apply (meson magic_seq refines_in refines_trans)
  apply (rule)
  apply (erule sup_refinesl)
  apply (rule similar_coinduct'[where X="{(x,y). \<exists>v. x = {v} \<and> y \<supseteq> {v; TAU}}"]; clarsimp)
   apply (meson insertI1 oper.seqIntro oper_nondet.nondet)
  apply (safe; clarsimp)
   apply (metis Un_iff inf_top.right_neutral terminate.simps(1) terminate.simps(6))
  by (metis UnCI abort.simps(1))

lemma seq_monoid_l[simp]: "seq skip p = p"  
  apply (transfer)
  apply (clarsimp simp: seqs_def)
  apply (clarsimp simp: bisimulate_def, intro conjI)
   apply (rule sim_insertI)
    apply (rule similar_coinduct'[where X="{(x,y). x = {TAU; MAGIC}}"]; clarsimp)
    apply (erule oper.cases; clarsimp)
    apply (erule oper.cases; clarsimp)
   apply (rule sup_simI)
    apply (erule refines_trans[OF refines_in])
    apply (rule similar_coinduct'[where X="{(x,y). \<exists>v. y = {v} \<and> x = {TAU; v}}"]; clarsimp)
   apply (erule oper.cases; clarsimp)
    apply (erule oper.cases; clarsimp)
  using oper_nondet.nondet apply fastforce
  apply (rule insert_drop)
  apply (rule)
  apply (erule sup_refinesl)
  apply (rule similar_coinduct'[where X="{(x,y). \<exists>v. x = {v} \<and> y = {TAU; v}}"]; clarsimp)
  by fastforce


lemma [simp]: "P \<leadsto> {}"
  apply (rule similar.simStep; clarsimp simp: simulates_def)
  by (meson choose_sub' empty_subsetI no_magic_allowed)

lemma seq_crash_absorb_l: "seq crash p = crash"
  apply (transfer)
  apply (clarsimp simp: seqs_def)
  apply (clarsimp simp: bisimulate_def)
  apply (case_tac "p = {}", clarsimp)
   apply (simp add: bisimulateD1 seq_abort_left_absorb)
  apply (rule insert_drop)
  apply (subgoal_tac "\<exists>v. v \<in> p", clarsimp)
   apply (erule sup_refinesl)
   apply (simp add: bisimulateD1 seq_abort_left_absorb)
  apply (fastforce)
  done


lemma seq_choice_distrib_l: "seq p (choice q r) = choice (seq p q) (seq p r)"
  apply (clarsimp simp: choice_def, transfer)
  apply (clarsimp simp: bisimulate_def, intro conjI)
   apply (clarsimp simp: seqs_def)
   apply (subst rewrite_sets, rule sup_simI', clarsimp)
  by (metis inf_sup_aci(5) seqs_mono_r union_greater union_refinesI)

lemma seq_choice_distrib_r: "seq (choice q r) p = choice (seq q p) (seq r p)"
  apply (clarsimp simp: choice_def, transfer)
  apply (clarsimp simp: bisimulate_def, intro conjI)
   apply (clarsimp simp: seqs_def)
  by (simp add: seqs_def)

definition "infp A = \<Union> {b. \<forall>a\<in>A. a \<leadsto> b }"

lemma aborts_abort: "aborts P = UNIV \<Longrightarrow> P \<leadsto> {Prim Abort}" 
  apply (rule similar.simStep; clarsimp simp: simulates_def)
   apply (metis UNIV_I abort_top aborts_def nondet_abort)
  by (metis UNIV_I UN_iff abort_term subsetD)


lemma aborts_un:"aborts (p \<union> q) = aborts p \<union> aborts q"
  apply (clarsimp)
  done

lemma aborts_insert:"aborts (insert v p) = abort v \<union> aborts p"
  apply (clarsimp)
  done

lemma hm: "p \<union> x ~ {Prim Abort} \<longleftrightarrow> aborts x \<supseteq> (- aborts p)" 
  apply (safe)
   apply (clarsimp simp: bisimulate_def, erule similar.cases; clarsimp)
   apply auto[1]
  apply (clarsimp simp: bisimulate_def)
  apply (rule aborts_abort)
  apply (clarsimp)
  by auto


lemma "ands p x ~ {MAGIC} \<Longrightarrow> aborts x \<inter> aborts p = {}"
  apply (clarsimp simp: bisimulate_def)
  apply (erule similar.cases; clarsimp simp: ands_def)
  by blast


lemma "(l, (v, s), (v', s')) \<in> oper \<Longrightarrow> v\<in> p \<Longrightarrow> s \<notin> aborts p  \<Longrightarrow> \<not>(\<exists>x. p \<union> x ~ {Prim Abort} \<and>  ands p x ~ {MAGIC})"
  apply (rule ccontr)
  apply (clarsimp)
  apply (simp only: hm)
  apply (clarsimp simp: bisimulate_def)
  apply (erule similar.cases, clarsimp simp: simulates_def)
  apply (erule_tac x=l in allE)
  apply (erule_tac x="s" in allE)
  apply (erule_tac x="s'" in allE)
  apply (erule_tac x="{v' && Prim Abort}" in allE)
  apply (drule mp)
  apply (subgoal_tac "\<exists>a. a \<in> x \<and> s \<in> abort a", clarsimp)
    apply (rule_tac p="v && a" in nondet)
     apply (clarsimp simp: ands_def)
    apply (erule oper.andIntro)
    apply (rule oper.abortIntro)
    apply (clarsimp)
   apply (drule subsetD[where c=s])

    apply blast
   apply (fastforce)
  apply (clarsimp)
  done

  

lemma "\<Union> (infp ` {f ` A |f. \<forall>Y\<in>A. f Y \<in> Y}) \<leadsto> infp (\<Union> ` A) "
  apply (case_tac "A = {}", clarsimp)
  apply (case_tac "{} \<in> A", clarsimp)
   apply (smt SUP_bot_conv(2) Sup_empty empty_iff imageI infp_def mem_Collect_eq sup_simI1)
  apply (clarsimp)
  apply (rule similar_coinduct'[where X="{(x,y). \<exists>S. S \<noteq> {} \<and> {} \<notin> S \<and> y = \<Union> (infp ` {f ` S |f. \<forall>Y\<in>S. f Y \<in> Y}) \<and> x = infp (\<Union> ` S)}"];
    clarsimp)
    apply (rule_tac x=A in exI, clarsimp)
  oops

lemma "ands x y ~ infp {x,y}"
  apply (rule bisim_coinduct[where X="{(A,B). \<exists>x y. A = ands x y \<and> B = infp {x,y} }"])
     apply (fastforce)
    apply (clarsimp)
    apply (rule_tac x="{q'}" in exI, clarsimp)
    apply (rule_tac v="ands x y" in choose_sub')
     apply (erule (1) nondet)
    apply (clarsimp simp: infp_def)
    apply (rule_tac x="ands x y" in exI)
    apply (clarsimp)
    defer
    apply (clarsimp)
  sorry
  find_theorems "_ \<rightarrow>\<^sub>?l _"
  sledgehammer
  thm bisim_coinduct

lemma [simp]:"UNIV \<leadsto> c" sorry

lemma "infp {c, UNIV} ~ c"
  apply (clarsimp simp: infp_def)
  by (metis (no_types, lifting) CollectD CollectI Union_iff bisimulate_def refines_every refines_in sup_simI1)
  apply (clarsimp)


thm Inf_le_iff

lemma "(x \<leadsto> infp S) \<longleftrightarrow> (\<forall>v. v \<leadsto> x \<longrightarrow> (\<exists>s\<in>S. v \<leadsto> s))"
  apply (rule iffI)
   apply (clarsimp simp: infp_def)
   apply (case_tac "S = {}", clarsimp)
  term conj

  thm le_Inf_iff

lemma " (c @@ (Inf S)) \<ge> Inf (conj c ` S)"
  apply (subst le_INF_iff)
  apply (clarsimp)
  oops
  sledgehammer
  thm conj_mono
  apply (rule conj_mono)

  find_theorems "Inf (insert _ _) = _" 


lemma "{} \<in> S \<Longrightarrow> infp S ~ {}"
  apply (clarsimp simp: bisimulate_def)
  apply (rule)
  apply (clarsimp simp: infp_def)
  apply (drule_tac x="{}" in bspec, assumption)
  by (simp add: refines_trans)

find_theorems "{} \<notin> ?S \<Longrightarrow> ?P (Inf ?S) " 
thm conjs_def union_comp_emptyL

definition "conjs' x y = (\<Union>a\<in>x. (\<Union>b\<in>y. {a && b})) \<union> {test (aborts x) ; Prim Abort} \<union> {test (aborts y) ; Prim Abort}"

lemma conjs_helper: "conjs x y  ~ (\<Union>a\<in>x. (\<Union>b\<in>y. {a && b})) \<union> {test (aborts x) ; Prim Abort} \<union> {test (aborts y) ; Prim Abort}"
  apply (clarsimp simp: bisimulate_def, intro conjI)
   defer
  find_theorems simjudge insert
   apply (rule sim_insertI)

lemma "{MAGIC, p} ~ {p}"
  apply (clarsimp simp: bisimulate_def) 
  by (simp add: sim_insertI)

lemma "{MAGIC; p} ~ {MAGIC}" 
  by (simp add: bisimulate_def)

lemma "{Conj c (And a b)} \<leadsto> {And (Conj c a) (Conj c b)}" 
  apply (rule similar_coinduct'[where X="{(x,y). \<exists>a b c. y = {Conj c (And a b)} \<and> x = {And (Conj c a) (Conj c b)} }"])
    apply (fastforce)
   apply (clarsimp)
   apply (erule oper.cases; clarsimp)
   apply (erule oper.cases; clarsimp)
    apply (erule oper.cases; clarsimp)
     apply (elim disjE; clarsimp?)
        apply (rule_tac x="{Prim Abort}" in exI)
        apply (clarsimp)
        apply (rule_tac x="{Prim Abort}" in exI)
       apply (clarsimp)
        apply (rule_tac x="{Prim Abort}" in exI)
      apply (clarsimp)
        apply (rule_tac x="{Prim Abort}" in exI)
     apply (clarsimp)
    apply (erule disjE; clarsimp?)

        apply (rule_tac x="{Prim Abort}" in exI)
     apply (clarsimp)
    apply (rule_tac x="{Conj pl' (And (Prim Abort) pr'a)}" in exI)
    apply (clarsimp)
  
    apply (meson abort_sand bisimulate_def refines_trans_quad sand_smaller sconj_commute wconj_mono)
    apply (erule oper.cases; clarsimp)
    apply (erule disjE; clarsimp?)

        apply (rule_tac x="{Prim Abort}" in exI)
     apply (clarsimp)

    apply (rule_tac x="{Conj pl'a (And  pr'a (Prim Abort))}" in exI)
    apply (clarsimp)
    apply (meson abort_sand bisimulate_def refines_trans_quad sand_smaller sconj_commute wconj_mono)
  oops
  sledgehammer


lemma [simp]: "{TAU; q'} \<leadsto> {q'}" sorry 

lemma helper: " \<forall>a\<in>S. p a \<leadsto> q a \<Longrightarrow> \<forall>a\<in>S. terms (p a) \<supseteq> terms (q a) "
  apply (clarsimp)
  apply (drule (1) bspec)
  by (meson refines_in refines_trans terminate_sim_singleton)

lemma "terminate (Conj p q) = terminate p \<inter> terminate q"
  apply (clarsimp)
  oops

definition "conjjs p q = (\<Union>x\<in>p. \<Union>y\<in>q. {Conj x  y})"

lemma "a \<noteq> {} \<Longrightarrow> {b. conjjs a b \<leadsto> c} \<noteq> {}"
  apply (clarsimp simp: conjjs_def)
  apply (rule_tac x="{Prim Abort}" in exI, clarsimp)

  find_theorems "{Conj MAGIC _}"

lemma "{Conj MAGIC p} ~ {test (abort p); Prim Abort}" 
  apply (rule bisim_coinduct[where X="{(x,y). \<exists>p. {Conj MAGIC p} = x \<and> y = {test (abort p); Prim Abort} }"])
     apply (fastforce)
    apply (clarsimp)
    apply (erule oper.cases; clarsimp)
   apply (clarsimp)
    apply (erule oper.cases; clarsimp)
    apply (erule oper.cases; clarsimp)
   apply (rule_tac x="{Prim Abort}" in exI, clarsimp)
  apply (clarsimp)
  done


lemma refines_terms_subset[simp, dest]: "P \<leadsto> P' \<Longrightarrow> terms P' \<subseteq> terms P"
  apply (erule similar.cases)
  by auto

lemma "aborts (infp {b. conjjs {MAGIC} b \<leadsto> c}) \<supseteq> aborts c"
  apply (clarsimp simp: infp_def conjjs_def)
     apply (rule_tac x="{test {x}; Prim Abort}" in exI)
  apply (clarsimp)
  apply (subgoal_tac "x \<in> aborts a"; clarsimp)
  defer
   apply (frule refines_abort_subset)
   apply (clarsimp)
  apply auto[1]
  oops
  find_theorems "_ \<leadsto> _" abort

lemma "{MAGIC \<sqdot> x} \<leadsto> c \<Longrightarrow> abort x \<supseteq> terms c "
  apply (frule refines_abort_subset)
  apply (frule refines_terms_subset)
  apply (clarsimp)
  done

lemma sim_test_abort: "x \<subseteq> aborts a \<Longrightarrow> a \<leadsto> {test x; Prim Abort}"
  sorry

lemma "terms (conjs {MAGIC} (infp {b. conjs {MAGIC} b \<leadsto> c})) \<supseteq> terms c"
  apply (clarsimp simp:  infp_def conjs_def)  
  apply (rule_tac x="{test {x}; Prim Abort}" in exI, clarsimp)
  find_theorems "_ \<leadsto> _" insert
  apply (subgoal_tac "x \<in> aborts a"; clarsimp)
  defer
  
   apply (frule refines_abort_subset; clarsimp)
   apply (frule refines_terms_subset; clarsimp)
  
   apply auto[1]
  using sim_test_abort 
  by (metis UN_I aborts_def singletonD subsetI)

definition "arbitrary S = (SOME x. x \<in> S)"

definition "connjs p q = (if p = {} then (Conj MAGIC) ` q else 
                         if q = {} then (Conj MAGIC) ` p else
                        (\<Union>x\<in>p. \<Union>y\<in>q. {Conj x  y}))"

definition "conjtract A B = (infp {b. connjs A b \<leadsto> B})"

lemma [simp]: "conjtract A B \<noteq> {}"
  apply (clarsimp simp: conjtract_def infp_def )
  apply (rule_tac x="{MAGIC}" in exI)
  apply (clarsimp)
  done

definition "step l s s' \<equiv> if l = \<pi> then pgm {(s,s')} else env {(s,s')}"

thm seqs_def

lemma [intro!, simp]: "p \<leadsto> {q} \<Longrightarrow> p \<leadsto> {TAU ; q}" sorry

lemma infp_not_empty: "P \<noteq> {} \<Longrightarrow> infp P \<noteq> {}"
  apply (clarsimp simp: infp_def)
  by (metis empty_not_insert magic_bot)

lemma sim_step_inf: "{a'. (a, s) \<rightarrow>l (a', s') } \<noteq> {} \<Longrightarrow> a \<leadsto> (seqs {step l s s'} (infp {a'. (a, s) \<rightarrow>l (a', s') }))"
  apply (rule similar_coinduct'[where X="{(x,y). x = seqs {step l s s'} (infp {a'. (a, s) \<rightarrow>l (a', s')}) \<and> y = a}"]; clarsimp)
   apply (clarsimp simp: seqs_def)
   apply (elim disjE; clarsimp)
  defer
    apply (erule oper.cases; clarsimp)
     apply (clarsimp simp: step_def split: if_splits)
    apply (clarsimp simp: step_def split: if_splits)
      apply (erule oper.cases; clarsimp)
      apply (clarsimp simp: infp_def)
      apply (rule exI, rule conjI, assumption)
  apply (clarsimp)
      apply (meson refines_in refines_trans)
     apply (erule oper.cases; clarsimp)
     apply (clarsimp simp: infp_def)
  apply (subgoal_tac "l = \<epsilon>")
      apply (rule exI, rule conjI, fastforce split: label.splits)
  apply (clarsimp)
      apply (meson refines_in refines_trans)
  using label.exhaust apply blast
    apply (clarsimp simp: step_def split: if_splits)
   apply (intro conjI)
    apply (clarsimp simp: seqs_def)
    apply (intro conjI; clarsimp simp: step_def)
   apply (clarsimp simp: step_def seqs_def split: if_splits)
  apply (erule oper.cases; clarsimp)
   apply (clarsimp simp: step_def  split: if_splits)
   apply (clarsimp simp: step_def  split: if_splits)
  apply (erule oper.cases; clarsimp)
   apply (fastforce)
  apply (erule oper.cases; clarsimp)
  using label.exhaust apply blast
  done

lemma refines_single_sim_step: "x \<in> infp {a'. (a, s) \<rightarrow>l (a', s') } \<Longrightarrow> {a'. (a, s) \<rightarrow>l (a', s') } \<noteq> {} \<Longrightarrow> a \<leadsto> ({step l s s'; x})"
  apply (rule refines_trans, erule sim_step_inf)
  apply (rule refines_in)
  apply (clarsimp simp: seqs_def)
  done

lemma refines_step_inf_refines: "{a'. (a, s) \<rightarrow>l (a', s') } \<noteq> {} \<Longrightarrow> infp {a'. (a, s) \<rightarrow>l (a', s') } \<leadsto>  {x} \<Longrightarrow> a \<leadsto> ({step l s s'; x})"
  apply (rule refines_trans, erule sim_step_inf)
  apply (rule refines_trans, erule seqs_mono_r)
  apply (clarsimp simp: seqs_def)
  done


   



lemma "(a, s) \<rightarrow>l (a', s') \<Longrightarrow> a \<leadsto> {step l s s'}"
  apply (rule similar_coinduct'[where X="{(x,y). x = {step l s s'} \<and> y = a}"]; clarsimp)
   apply (clarsimp simp: step_def split: if_splits)
  apply (erule oper.cases; clarsimp)
  apply (clarsimp)
  apply (rule simStep; clarsimp simp: step_def)
  apply (intro conjI impI)
  apply (unfold simulates_def; clarsimp)
  oops

  thm choose_sub

lemma choose_group: "P \<noteq> {} \<Longrightarrow> (\<And>p'. p' \<in> P \<Longrightarrow> (p, s) \<rightarrow>l (p', s')) \<Longrightarrow> (p, s) \<rightarrow>l (\<Union>P, s')"
  apply (case_tac "P={}")
  apply (clarsimp)
  apply (atomize)
  thm 
  thm oper_nondet.inducts
  thm oper_nondet.inducts[where P="\<lambda>l p s q s'. (q = \<Union>P \<longrightarrow>(\<forall>p'\<in>P. (p, s) \<rightarrow>l (p', s')) \<longrightarrow> (p, s) \<rightarrow>l (\<Union>P, s'))", THEN mp, THEN mp]
  apply (rule oper_nondet.inducts[where P="\<lambda>l p s q s'. (q = \<Union>P \<longrightarrow>(\<forall>p'\<in>P. (p, s) \<rightarrow>l (p', s')) \<longrightarrow> (p, s) \<rightarrow>l (\<Union>P, s'))", THEN mp, THEN mp]) 
      prefer 4
      apply (rule refl)
     apply (metis (full_types) UnionE choose_single empty_Union_conv ex_in_conv oper_nondet.branch)
    apply (clarsimp)
    apply (metis oper_nondet.nondet)
   apply (clarsimp)
   apply (metis UnionE Union_upper oper_nondet.branch subset_empty)
  apply (fastforce)
  done


lemma "q \<noteq> {} \<Longrightarrow> \<exists>p'\<in>p. \<exists>q'. (p', s) \<rightarrow>\<^sub>l (q', s')  \<Longrightarrow>
   (infp p, s) \<rightarrow>l (\<Union>p\<in>{p' \<in> p. \<exists>q'. (p', s) \<rightarrow>\<^sub>l (q', s')}. (;) TAU ` infp {p'. (p, s) \<rightarrow>\<^sub>l (p', s')}, s')"
  apply (rule choose_group; clarsimp)
  apply (fastforce)
  apply (rule branch; clarsimp)
  apply (clarsimp simp: infp_def)
  apply (meson insert_not_empty magic_bot)
  apply (clarsimp)
  thm choose_sub'
  apply (rule_tac v="seqs {step l s s'} (infp {a'. (x, s) \<rightarrow>l (a', s') })" in choose_sub')
   apply (rule_tac p="step l s s'; qa" in nondet)
    apply (clarsimp simp: seqs_def)
  apply (clarsimp simp: step_def)
  
  using label.exhaust apply blast
  apply (clarsimp)
  apply (clarsimp simp: seqs_def infp_def)
  apply (elim disjE; clarsimp)
   apply (rule_tac x="{step l s s'; MAGIC}" in exI)
   apply (clarsimp)
  oops
  apply ()

definition "moves l s s' a =  {a'. (a, s) \<rightarrow>\<^sub>l (a', s')}"


lemma "conjtract A B = infp (moves l s s' ` {b. connjs A b \<leadsto> B})"
  apply (clarsimp simp: conjtract_def moves_def image_def)
  oops

  thm connjs_def

lemma empty_no_moves [simp]:"moves l s s' {}  = {}" 
  apply (clarsimp simp: moves_def)
    by (meson choose_sub' no_magic_allowed subset_singleton_iff)



lemma empty_no_moves' [simp]:"{a'. ({}, s) \<rightarrow>\<^sub>\<beta> (a', s')} = {}"
  apply (clarsimp)
  by (meson choose_sub' no_magic_allowed subset_singleton_iff)

lemma empty_not_in_moves[simp]: "{} \<in> moves l s s' r = False" 
  apply (clarsimp simp: moves_def)
  done

lemma empty_not_in_moves'[simp]: "(\<forall>x\<in>moves \<beta> s s' a. x = {}) \<longleftrightarrow> moves \<beta> s s' a = {}"
  apply (clarsimp simp: moves_def)
  done
  oops


lemma helper_connjs: "(p, s) \<rightarrow>\<^sub>l (b, s') \<Longrightarrow> p = connjs A a  \<Longrightarrow> s \<notin> aborts A \<Longrightarrow> s \<notin> aborts a \<Longrightarrow> b \<subseteq> connjs (Sup (moves l s s' A)) (Sup (moves l s s' a))" 
  apply (induction arbitrary:  rule: oper_nondet.inducts)
   apply (clarsimp simp: connjs_def split: if_splits, safe; clarsimp?)
      apply (erule oper.cases; clarsimp)
         apply (erule oper.cases; clarsimp)
      apply (erule oper.cases; clarsimp)
      apply (erule oper.cases; clarsimp)
      apply (erule oper.cases; clarsimp)


      apply (clarsimp simp: moves_def)
      apply (meson oper_nondet.nondet)
     apply (erule oper.cases; clarsimp)

      apply (clarsimp simp: moves_def)
     apply (meson oper_nondet.nondet)

     apply (erule oper.cases; clarsimp)

      apply (clarsimp simp: moves_def)
      apply (meson oper_nondet.nondet)

   apply (erule oper.cases; clarsimp)
  apply (clarsimp simp: moves_def)
   apply (metis insertI1 oper_nondet.nondet)
  apply (clarsimp)
  done
  

lemma refines_subset: "a \<subseteq> b \<Longrightarrow> b \<leadsto> a"
  by (metis sup.orderE union_greater)

lemma refines_step: " \<Union> (moves l s s' a) \<leadsto> y \<Longrightarrow> qa \<in> y \<Longrightarrow> a \<leadsto> {step l s s' ; qa}"
  sorry

lemma "(A, s :: bool) \<rightarrow>l (A',s') \<Longrightarrow> s \<notin> aborts (conjtract A q)"
  apply (clarsimp simp: conjtract_def)
  apply (clarsimp simp: infp_def)
  oops

lemma aborts_infp[simp]: " \<Union>(abort ` (infp A)) = \<Union>(abort ` {x. abort x \<subseteq> \<Inter>(aborts ` A)})"
  apply (clarsimp simp: conjtract_def infp_def connjs_def)
  apply (intro set_eqI iffI)
   apply (clarsimp)
   apply (rule_tac x="xb" in exI)
   apply (clarsimp)
   apply (drule_tac x=xd in bspec, assumption)
  
   apply (metis UN_E UN_I aborts_def similar.cases subsetD)
  apply (clarsimp)
  apply (rule_tac x="{test (abort xa); Prim Abort}" in exI)
  apply (clarsimp)
  by (simp add: sim_test_abort subset_iff)

lemma abort_sim_step: "s \<in> aborts a \<Longrightarrow> a \<leadsto> {step l s s' ; q}" sorry


lemma conjtract_step[simplified moves_def, simplified]:
   "(A, s) \<rightarrow>l (A',s') \<Longrightarrow> (q, s) \<rightarrow>l (q',s') \<Longrightarrow> s \<notin> aborts A   \<Longrightarrow> (Seq TAU) ` conjtract (\<Union> (moves l s s' A)) q' \<in> (moves l s s' (conjtract A q))"
  apply (clarsimp simp: moves_def conjtract_def infp_def)
  apply (rule branch)
   apply (clarsimp)
   apply (meson insert_not_empty magic_bot)
  apply (clarsimp)
  
       apply (rule_tac p="(step l s s'; qa)" in nondet)
   apply (clarsimp)
   apply (rule_tac x="{(step l s s'; qa)}" in exI)
   apply (clarsimp)
   
   apply (frule (1)  simulatesD, clarsimp)
   apply (case_tac "s \<in> aborts a")
  defer
   apply (drule helper_connjs, rule refl)
     defer
     defer
     apply (erule_tac x="(\<Union> (moves l s s' a))" in allE) back
     apply (drule mp)
      apply (erule refines_trans[rotated])
  apply (clarsimp simp: moves_def)


      apply (simp add: refines_subset)

  apply (simp add: refines_step)
     apply (case_tac "l"; clarsimp simp: step_def)
  defer
    apply (fastforce)
  apply (clarsimp)
  by (simp add: abort_sim_step)


definition "all_moves l s s' c = Sup (moves l s s' c)"

thm similar_coinduct'[no_vars]

term Range

find_consts "'a rel \<Rightarrow> 'a set"

  

lemma [intro!]: "(P, s) \<rightarrow>l (Q, s') \<Longrightarrow> ((;) TAU ` P, s) \<rightarrow>\<^sub>l (Q, s')"
  apply (induction rule: oper_nondet.inducts)
   apply (rule_tac p="TAU ; p" in nondet)
    apply (fastforce)
  apply (rule seqStep, clarsimp, assumption)
  by (meson oper_nondet.branch)

lemma [intro!]: "s \<in> aborts a \<Longrightarrow> a \<leadsto> {Prim (Test {s}) ; Prim Abort}" sorry

lemma magic_conj_sim: "(\<sqdot>) MAGIC ` a \<leadsto> q \<Longrightarrow> {s. \<exists>l s' q'. (q, s) \<rightarrow>l (q',s')} \<subseteq> aborts a" sorry

lemma [simp]:"connjs {} p = (\<sqdot>) MAGIC ` p "
  by (clarsimp simp: connjs_def)

lemma no_move_conj_abort':"(p, s) \<rightarrow>l (b, s') \<Longrightarrow> A \<noteq> {} \<Longrightarrow> moves l s s' A = {} \<Longrightarrow>  p = connjs A a \<Longrightarrow> s \<in> aborts a"
  apply (induction rule: oper_nondet.inducts)
   apply (clarsimp simp: connjs_def split: if_splits)
    apply (erule oper.cases; clarsimp simp: moves_def)
    apply (erule_tac x="{Prim Abort}" in allE, erule notE, erule nondet, clarsimp)
   apply (erule oper.cases; clarsimp simp: moves_def)

    apply (metis UN_I aborts_def nondet_abort)
   apply (meson oper_nondet.nondet)
  apply (clarsimp)
  by blast

lemma no_move_conj_abort:"( connjs A a, s) \<rightarrow>l (b, s') \<Longrightarrow> A \<noteq> {} \<Longrightarrow> moves l s s' A = {} \<Longrightarrow>  s \<in> aborts a"
  by (erule no_move_conj_abort'; fastforce)


lemma [simp]: "aa \<leadsto> {Prim (Test {x})} \<longleftrightarrow> x \<in> terms aa" sorry
lemma [simp]: "Sup (terminate ` (connjs A B)) = (terms A) \<inter> (terms B) \<union> (aborts A) \<union> (aborts B)"
  apply (intro set_eqI iffI; clarsimp simp: connjs_def split: if_splits)
   apply blast
  apply blast
  done


lemma terms_infp[simp]: " (Sup (terminate ` (infp A))) = terms {x. terminate x \<subseteq> \<Inter>(terms ` A)} \<union> aborts (infp A)"
  apply (clarsimp simp: conjtract_def infp_def connjs_def)
  apply (intro set_eqI iffI)
   apply (clarsimp)
   apply (rule_tac x="xb" in exI)
   apply (clarsimp)
  apply (meson refines_in refines_trans terminate_sim_singleton)
  apply (clarsimp)
  apply (elim disjE; clarsimp)
   apply (rule_tac x="{test {x}}" in exI)
   apply (clarsimp)
  
   apply auto[1]
   apply (rule_tac x="{test {x}}" in exI)
  apply (clarsimp)
  by (meson abort_term refines_in refines_trans subsetD terminate_sim_singleton)

thm aborts_infp

lemma abort_connjs: "\<Union> (abort ` connjs A B) = aborts A \<union> aborts B"
  by (clarsimp simp: connjs_def)

lemma aborts_seq_tau_image: "aborts ((;) TAU ` A) =  aborts A"
  by (clarsimp)

lemma oper_nondet_case:"(p, s) \<rightarrow>\<^sub>\<beta> (p', s') \<Longrightarrow> \<exists>x\<in>p. (\<exists>y\<in>p'. (\<beta>, (x,s), (y,s')) \<in> oper) "
  apply (induction rule: oper_nondet.inducts)
   apply (clarsimp)
   apply (fastforce)
  apply (fastforce)
  done

lemma magic_conj_helper: "(\<sqdot>) MAGIC ` b \<leadsto> q \<longleftrightarrow> aborts b \<supseteq> {s. \<exists>q' s' l. (q, s) \<rightarrow>l (q',s')} \<and> terms q \<subseteq> aborts b" 
  apply (intro iffI conjI; clarsimp)
    apply (case_tac "b = {}", clarsimp)

     apply (meson bisimulateD2 magic_empty no_magic_allowed simulatesD)
    apply (drule (1) simulatesD)
    apply (clarsimp)
    apply (frule oper_nondet_case) back
    apply (clarsimp)
    apply (erule oper.cases; clarsimp)
    apply blast
   apply (frule refines_terms_subset; clarsimp)
   apply auto[1]
  apply (rule simStep; clarsimp simp: simulates_def)
  apply (drule subsetD, fastforce)
   apply (clarsimp)
   apply (rule_tac x="{Prim Abort}" in exI, clarsimp)
   apply (rule nondet_abort, clarsimp)
   apply (auto)[1]
  by (metis (no_types, lifting) UN_E UN_I abort_term subset_iff)

lemma aborts_infp'[simp]:"aborts (infp A) = aborts {x. abort x \<subseteq> \<Inter>(aborts ` A)}" sorry

lemma conj_image_refines: "aborts c \<supseteq> aborts c' \<Longrightarrow>  (\<sqdot>) MAGIC ` c \<leadsto> (\<sqdot>) MAGIC ` c'"
  apply (subst magic_conj_helper; clarsimp)
  apply (case_tac "c' = {}"; clarsimp?)
   apply (meson choose_sub' empty_subsetI no_magic_allowed)
  apply (frule oper_nondet_case)
  apply (clarsimp)
  apply (erule oper.cases;clarsimp)
  by (auto)
  
  

lemma seq_tau_refines[simp]: " c \<leadsto> (;) TAU ` c"
  apply (rule similar_coinduct'[where X="{(x,y). x = (;) TAU ` y}"]; clarsimp)
  apply (erule oper.cases; clarsimp)
  
    apply (metis UN_I aborts_def nondet_abort refines_refl)
   apply (erule oper.cases;clarsimp)
  by (meson oper_nondet.nondet refines_refl)

lemma " connjs a (conjtract a c) \<leadsto> c"
  thm refines_trans
  apply (rule refines_trans[where q="connjs a (Seq TAU ` (conjtract a c) )"])
  
  defer
  apply (rule similar_coinduct'[where X="{(x,y). \<exists>A .   y = connjs A (Seq TAU `(conjtract A x))    }"]; clarsimp?)
    apply (rule_tac x=a in exI, clarsimp)
   apply (case_tac "s \<in> aborts A", rule_tac x="{Prim Abort}" in exI, clarsimp)
    apply (rule)
     apply (clarsimp simp: connjs_def)
     apply (intro conjI impI; clarsimp?)
     apply (erule bexI[rotated])
     apply (clarsimp simp: conjtract_def)
     apply (rule_tac x="MAGIC" in exI)
     apply (clarsimp simp: infp_def)
     apply (rule_tac x="{MAGIC}" in exI, clarsimp)
   apply (case_tac "{a'. (A, s) \<rightarrow>l (a', s')} = {}")
    apply (rule_tac x="{Prim Abort}" in exI, clarsimp)
    apply (rule nondet_abort)
    apply (clarsimp simp: connjs_def)
    apply (safe; clarsimp?)
     apply (clarsimp simp: conjtract_def infp_def connjs_def)
     apply (rule_tac x="{test {s}; Prim Abort}" in exI)
       apply (clarsimp)
       apply (drule magic_conj_sim, clarsimp)
  thm subsetD
       apply (drule_tac c="s" in subsetD)
        apply (clarsimp)
        apply (fastforce elim: nondet)
  apply (fastforce)
  
  apply (fastforce)
     apply (clarsimp simp: conjtract_def infp_def split: if_splits)
     apply (rule_tac x="{test {s}; Prim Abort}" in exI)
     apply (clarsimp)
     apply (rule ccontr, clarsimp)
     apply (drule (2) simulatesD[OF _ nondet])
     apply (clarsimp)
  apply (drule no_move_conj_abort)
       apply (fastforce)
      apply (clarsimp simp: moves_def)
     apply (fastforce)
    apply (case_tac "A = {}")
  apply simp
  find_theorems  " (\<Union>x\<in>?A. \<Union>y\<in>?x. ?P y) = _" 
   apply (rule_tac x="connjs ((all_moves l s s' A)) (Seq TAU ` (conjtract (all_moves l s s' A) {q'})) " in exI)
  apply (rule conjI[rotated])
    
    apply (rule disjI1)
         apply (fastforce)
        apply (unfold connjs_def)[1]
         apply (subgoal_tac "all_moves l s s' A \<noteq> {}")
          apply (subgoal_tac "(;) TAU ` conjtract A q \<noteq> {}")
  apply (subgoal_tac "(;) TAU ` conjtract (all_moves l s s' A) {q'} \<noteq> {}")
            apply (simp only: if_distrib if_False refl if_True)
            apply (rule union_step)
      apply (rule union_step)
              apply (blast)
             apply (clarsimp simp: all_moves_def moves_def)
  thm conjtract_step
  apply (erule conjtract_step)
              apply (clarsimp)
              apply (simp add: oper_nondet.nondet)
             apply (assumption)
            apply (clarsimp simp: all_moves_def moves_def, rule branch)
             apply (fastforce)
            apply (clarsimp)
           apply (clarsimp)
          apply (clarsimp)
    apply (clarsimp simp: all_moves_def moves_def)
   apply (intro conjI)
    apply (unfold conjtract_def)[1]
    apply (simp only: terms_infp aborts_infp' aborts_infp)
    apply (clarsimp)
    apply (intro conjI) 
     apply (case_tac "A = {}", clarsimp)
      apply (clarsimp simp: magic_conj_helper)
  apply (erule_tac x="test {x}; Prim Abort" in allE)
  thm aborts_infp
      apply (clarsimp)
      apply blast
     apply (rule ccontr, clarsimp)
  apply (erule_tac x="test {x}; Prim Abort" in allE)
     apply (clarsimp)
  apply (clarsimp simp: connjs_def split:if_splits)
      apply (metis UN_E UN_I aborts_def magic_conj_helper subset_iff terms_def)
      apply (frule refines_abort_subset)
     apply (frule refines_terms_subset)
  apply (clarsimp)
     apply (drule_tac c=x in subsetD) back
  apply (clarsimp)

      apply blast
     apply (clarsimp)
    apply (rule_tac x="test {x}" in exI, clarsimp)
apply (frule refines_abort_subset)
    apply (frule refines_terms_subset)
    apply (drule_tac c=x in subsetD) back
     apply (clarsimp)
     apply (fastforce)
    apply (clarsimp)
    apply (meson abort_term in_mono)
   apply (simp only: abort_connjs aborts_seq_tau_image, subst conjtract_def, simp only: aborts_infp' aborts_infp)
   apply (clarsimp)
  apply (rule ccontr; clarsimp)
   apply (erule_tac x="test {x} ; Prim Abort" in allE, clarsimp)
  apply (clarsimp simp: connjs_def split: if_splits)

      apply (frule refines_abort_subset)
     apply (drule_tac c=x in subsetD, fastforce, clarsimp)
    apply (frule refines_abort_subset)
     apply (drule_tac c=x in subsetD, fastforce, clarsimp)
   apply (frule refines_abort_subset)
     apply (drule_tac c=x in subsetD, fastforce, clarsimp)
  apply (clarsimp simp: connjs_def)
  apply (rule conj_image_refines, clarsimp)
  done
 

lemma conjs_distrib_infp: "conjs c (infp S) \<leadsto> infp ((conjs c) ` S)"
  sorry


lemma infp_helper: "\<forall>x\<in>S. x \<leadsto> a \<Longrightarrow> infp S \<leadsto> a"
  by (smt infp_def mem_Collect_eq mem_simps(9) refines_every refines_in)

lemma conjs_mp: " conjs a (infp {b. conjs a b \<leadsto> c}) \<leadsto> c"
  apply (rule refines_trans[OF conjs_distrib_infp], clarsimp simp: image_def)
  apply (rule infp_helper; clarsimp)
  done


lemma "False"
  apply (insert conjs_mp[where a="{MAGIC}" and c="{test {x}} "])
  apply (drule refines_terms_subset)
  apply (clarsimp simp: conjs_def infp_def)
  sledgehammer
  apply (erule_tac x="{test {


lemma "conjs' {c} (infp S) \<leadsto> infp ((conjs' {c}) ` S)"
  apply (case_tac "S = {}"; clarsimp)
   apply (clarsimp simp: infp_def )
   defer
   apply (case_tac "{} \<in> S")
  defer
 
     apply (rule similar_coinduct'[where X="{(x,y). \<exists>c S. S \<noteq> {}  \<and> y = conjs' {c} (infp S) \<and> x = infp (conjs' {c} ` S)  }"])
      apply (fastforce)
     defer
     apply (intro conjI; clarsimp)
  apply (clarsimp simp: infp_def)
       apply (drule helper)
      apply (clarsimp)
      apply (subgoal_tac "\<forall>a\<in>Sa. x \<in> \<Union> (terminate ` conjs' {c} a)")
       apply (subst (asm) conjs'_def) back
  apply (clarsimp)

  sledgehammer
       apply (clarsimp simp: Ball_def)
  apply (clarsimp simp: conjs'_def)
  nitpick
  oops
      apply (clarsimp)
      apply (clarsimp simp: infp_def)
      apply (case_tac "s \<in> abort c")
      apply (rule_tac x="{Prim Abort}" in exI)
      apply (clarsimp)
      apply (rule nondet_abort)
      apply (clarsimp simp: conjs'_def)
     apply (case_tac "\<forall>x\<in>Sa. s \<in> aborts x")
      apply (rule_tac x="{Prim Abort}" in exI, clarsimp)
      apply (rule nondet_abort)
      apply (clarsimp simp: conjs'_def)
  oops



     apply (rule_tac x="conjs c' {TAU; q'}" in exI)
  apply (rule_tac v="conjs c {step l  choose_sub')
  find_theorems "transition" "(\<subseteq>)"
  sledgehammer
  oops
    defer
    apply (case_tac "infp S = {}", clarsimp simp: conjs'_def)
  defer
  apply (clarsimp simp: conjs'_def)
  apply (clarsimp simp: image_def)
  apply (clarsimp simp: infp_def)
   apply (rule, clarsimp)
   apply (clarsimp simp: ands_def)
  apply (rule sup_refinesl)
  find_theorems "Sup _ \<leadsto> _"
  apply (rule sup_simI)


end

  
