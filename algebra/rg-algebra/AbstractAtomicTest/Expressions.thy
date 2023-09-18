section \<open>Expressions\<close>
  
theory Expressions
imports
  "Idle"
  "IntroPar"
  "HOL-Library.FSet"
begin

locale expressions = idle_command (* _ _ lib_bool_sets *) + intro_par (*_ _ lib_bool_sets *)
  (* for lib_bool_sets :: "'c \<Rightarrow> 'b set \<Rightarrow> 'b set" ("E\<^sup>S\<^sub>_ _" [999, 999] 999) *)
begin

text \<open> The type of the state is 's, and 'v is the type of values.
  A variable is represented generically as a state accessor function.
  Unary and binary operators are represented by their semantics on values.
 \<close>
datatype ('s,'v) expr = Constant "'v" | 
                        Variable "'s\<Rightarrow>'v" | 
                        UnaryOp  "'v\<Rightarrow>'v" "('s,'v) expr" | 
                        BinaryOp "'v\<Rightarrow>'v\<Rightarrow>'v" "('s,'v) expr" "('s,'v) expr"
                     
fun eval :: "('s,'v) expr\<Rightarrow>'s\<Rightarrow>'v" where
  "eval (Constant k) state = k" |
  "eval (Variable accessor) state = accessor state" |
  "eval (UnaryOp operator e1) state = operator (eval e1 state)" |
  "eval (BinaryOp operator e1 e2) state = operator (eval e1 state) (eval e2 state)"  
    
definition estable :: "('b,'v) expr\<Rightarrow>'b rel\<Rightarrow>bool" where
  "(estable e r) \<equiv> (\<forall>(x,y)\<in>r. ((eval e x) = (eval e y)))"
  
definition expr_eq :: "('b,'v) expr\<Rightarrow>'v\<Rightarrow>('b) set" where
  "(expr_eq e k) \<equiv> {x::'b. eval e x = k}"

text \<open> An expression that is stable under r means that each of the expression's 
   possible results are stable under r. \<close>
lemma estable_stable_eq:
  shows "estable e r = (\<forall>v::'v. (stable (expr_eq e v) r))"
proof (rule iffI)
  show "estable e r \<Longrightarrow> (\<forall>v. stable (expr_eq e v) r)"
    unfolding stable_def estable_def expr_eq_def by auto
next
  show "\<forall>v.((stable (expr_eq e v) r)) \<Longrightarrow> estable e r"
  unfolding estable_def proof (auto)
    fix x y
    assume a1: "\<forall>v::'v. stable (expr_eq e v) r"
    assume a2: "(x,y) \<in> r"
    show "eval e x = eval e y"
    proof -
      obtain k where b1: "eval e x = k" by simp
      then have "x \<in> (expr_eq e k)" unfolding expr_eq_def by auto
      then have "y \<in> (expr_eq e k)" using a1 a2 unfolding stable_def by auto
      then show ?thesis unfolding expr_eq_def using b1 by auto
    qed
  qed
qed

lemma estable_stable_neq:
  shows "estable e r = (\<forall>v. stable (-expr_eq e v) r)"
  unfolding expr_eq_def estable_stable_eq using stable_eq_stable_neq2 by metis

lemma stable_expression_constant:
  shows "estable (Constant k) r"
proof -
   have "\<forall>(x,y)\<in>r. eval (Constant k) x = eval (Constant k) y"
    by simp
  then have "estable (Constant k) r"
    by (simp add: estable_def)
  then show ?thesis .
qed
  
lemma stable_expression_variable:
  assumes accesor_stable: "(\<forall>(x,y)\<in>r. (accessor x = accessor y))"
  shows "estable (Variable accessor) r"
proof -
  have "\<forall>(x,y)\<in>r. eval (Variable accessor) x = eval (Variable accessor) y"
    using accesor_stable by simp
  then have "estable (Variable accessor) r"
    by (simp add: estable_def)
  then show ?thesis .
qed

lemma stable_expression_unaryop:
  assumes e1_stable: "estable e1 r"
  shows "estable (UnaryOp operator e1) r"
proof -
  have "\<forall>(x,y)\<in>r. (eval e1 x) = (eval e1 y)"
     using e1_stable by (simp add: estable_def)
  then have "\<forall>(x,y)\<in>r. operator (eval e1 x) = operator (eval e1 y)"
    by auto
  then have "estable (UnaryOp operator e1) r"
    by (simp add: estable_def)
  then show ?thesis .
qed
  
lemma stable_expression_binaryop:
  assumes e1_stable: "estable e1 r"
  assumes e2_stable: "estable e2 r"
  shows "estable (BinaryOp operator e1 e2) r"
proof -
  have a1: "\<forall>(x,y)\<in>r. (eval e1 x) = (eval e1 y)"
     using e1_stable by (simp add: estable_def)
  have a2: "\<forall>(x,y)\<in>r. (eval e2 x) = (eval e2 y)"
     using e2_stable by (simp add: estable_def)
  have a3: "\<forall>(x,y)\<in>r. operator (eval e1 x) (eval e2 x) = operator (eval e1 y) (eval e2 y)"
    using a1 a2 by (simp add: split_def)
  then have "estable (BinaryOp operator e1 e2) r"
    by (simp add: estable_def)
  then show ?thesis .
qed

fun single_reference :: "('b,'v) expr\<Rightarrow>'b rel\<Rightarrow>bool" where
  "single_reference (Constant k) r = True" | 
  "single_reference (Variable accessor) r = True" | 
  "single_reference (UnaryOp oper e1) r = (single_reference e1 r)" |
  "single_reference (BinaryOp oper e1 e2) r = 
      ((single_reference e1 r) \<and> (single_reference e2 r) \<and> 
      ((estable e1 r) \<or> (estable e2 r)))"

(* Lemma 23. Formerly Lemma 5, rely_stable_expression. *)
lemma rely_constant_expression:
  assumes constant_under_r: "estable e r"
  shows "(rely r) \<iinter> idle;\<tau>(expr_eq e v) \<ge> (rely r) \<iinter> \<tau>(expr_eq e v);idle"
    using estable_stable_eq constant_under_r rely_idle_stable by metis

fun expr_cmd :: "('b,'v) expr\<Rightarrow>'v\<Rightarrow>'a::refinement_lattice"  ("\<lbrakk>_\<rbrakk>_" [100,100] 1000) where
  "expr_cmd (Constant k) v = idle;\<tau>(expr_eq (Constant k) v);idle" | 
  "expr_cmd (Variable accessor) v = idle;\<tau>(expr_eq (Variable accessor) v);idle" | 
  "expr_cmd (UnaryOp operator e1) v = (\<Squnion>v1\<in>({v1. (operator v1 = v)}). (expr_cmd e1 v1))" |
  "expr_cmd (BinaryOp operator e1 e2) v = 
            (\<Squnion>(v1,v2)\<in>({(v1,v2). (operator v1 v2 = v)}). (expr_cmd e1 v1) \<parallel> (expr_cmd e2 v2))"

lemma seq_NONDET_distrib_empty:
  shows "c;(\<Squnion>d\<in>D. f d) \<ge> (\<Squnion>d\<in>D. c ; f d)"
proof (cases "D={}")
  case empty: True
  then show ?thesis by simp
next
  case nonempty: False
  then show ?thesis using par.seq_Nondet_distrib by (simp add:image_image)
qed

lemma seq_NONDET_distrib_empty2:
  shows "c ; (\<Squnion>(d1,d2)\<in>D. f d1 d2) \<ge> (\<Squnion>(d1,d2)\<in>D. c ; f d1 d2)"
proof -
  have a1: "(\<lambda>d. c;d) \<circ> (\<lambda>(d1,d2). f d1 d2) = (\<lambda>(d1,d2). c;(f d1 d2))"
    by auto
  have "c ; (\<Squnion>(d1,d2)\<in>D. f d1 d2) = c ; (\<Squnion>(d1,d2)\<in>D. (f d1 d2))"
    by auto
  also have "... \<ge> (\<Squnion>(d1,d2)\<in>D. c; (f d1 d2))"
    using seq_NONDET_distrib_empty
    by (metis SUP_image a1 image_is_empty order_refl par.seq_Nondet_distrib)
  finally show ?thesis using a1
    using \<open>c ; (\<Squnion>(d1, d2)\<in>D. f d1 d2) \<ge> (\<Squnion>(d1, d2)\<in>D. c ; f d1 d2)\<close> by blast
qed

lemma conj_NONDET_distrib_empty:
  shows "c \<iinter> (\<Squnion>d\<in>D. f d) \<ge> (\<Squnion>d\<in>D. c \<iinter> f d)"
proof (cases "D={}")
  case empty: True
  then show ?thesis by simp
next
  case nonempty: False
  then show ?thesis using conj.sync_Nondet_distrib by (simp add:image_image)
qed

lemma conj_NONDET_distrib_empty2:
  shows "c \<iinter> (\<Squnion>(d1,d2)\<in>D. f d1 d2) \<ge> (\<Squnion>(d1,d2)\<in>D. c \<iinter> f d1 d2)"
proof -
  have a1: "(\<lambda>d. c \<iinter> d) \<circ> (\<lambda>(d1,d2). f d1 d2) = (\<lambda>(d1,d2). c \<iinter> (f d1 d2))"
    by auto
  have "c \<iinter> (\<Squnion>(d1,d2)\<in>D. f d1 d2) = c \<iinter> (\<Squnion>(d1,d2)\<in>D. (f d1 d2))"
    by auto
  also have "... \<ge> (\<Squnion>(d1,d2)\<in>D. c \<iinter> (f d1 d2))"
    by (metis SUP_image Sup_least a1 conj.sync_Nondet_distrib empty_iff image_is_empty order_refl)
  finally show ?thesis using a1
    using \<open>c \<iinter> (\<Squnion>(d1, d2)\<in>D. f d1 d2) \<ge> (\<Squnion>(d1, d2)\<in>D. c \<iinter> f d1 d2)\<close> by blast
qed
  
lemma test_Nondet2:
  shows "\<tau> (\<Union>(x1,x2)\<in>P. p x1 x2) = (\<Squnion>(x1,x2)\<in>P. \<tau> (p x1 x2))"
proof -
  (* Required to help SUP_image application *)
  have a1: "((\<lambda>x. \<tau>(x)) \<circ> (\<lambda>(x1,x2). p x1 x2)) = (\<lambda>(x1,x2). \<tau>(p x1 x2))"
    by auto
  show ?thesis
    by (simp add: Sup.SUP_image a1 test_Sup) 
  (* This can be done in one step using a1 test_Sup by simp, but this explains
     better what is going on under the covers. 
  have "\<tau> (\<Union>(x1,x2)\<in>P. p x1 x2) = \<tau>(\<Union>(x1,x2)\<in>P. p x1 x2)"
    by simp
  also have "... = SUPREMUM (((\<lambda>(x1,x2). p x1 x2)) ` P) (\<lambda>x. \<tau>(x))"
    using test_Sup by simp
  also have "... = SUPREMUM P (\<lambda>(x1,x2). \<tau>(p x1 x2))"
    using a1 by (simp add:SUP_image)
  finally show ?thesis . *)
qed
  
lemma NONDET_seq_distrib2:
  shows  "(\<Squnion>(v1,v2)\<in>P. (d v1 v2));c = (\<Squnion>(v1,v2)\<in>P. (d v1 v2);c)"    
proof -
  have a1: "(\<lambda>d. d;c) \<circ> (\<lambda>(v1,v2). d v1 v2) = (\<lambda>(v1,v2). (d v1 v2);c)"
    by auto
  have "(\<Squnion>(v1,v2)\<in>P. (d v1 v2));c = (\<Squnion>d\<in>((\<lambda>(v1,v2). d v1 v2) ` P). d;c)"
    using NONDET_seq_distrib by (simp add:SUP_image)
  also have "... = (\<Squnion>(v1,v2)\<in>P. (d v1 v2);c)"
    using a1 by (simp add:SUP_image)
  finally show ?thesis by auto
qed  
  
lemma single_reference_eval_e1_first:
  assumes e1_stable: "estable e1 r"
  shows "(rely r) \<iinter> idle;\<tau>((expr_eq e1 v1) \<inter> (expr_eq e2 v2));idle
       \<ge> (rely r) \<iinter> (idle;\<tau>(expr_eq e1 v1);idle;\<tau>(expr_eq e2 v2);idle)"
proof -
  have "(rely r) \<iinter> idle;\<tau>((expr_eq e1 v1) \<inter> (expr_eq e2 v2));idle = 
        (rely r) \<iinter> idle;idle;\<tau>(expr_eq e1 v1);\<tau>(expr_eq e2 v2);idle"
    by (simp add: idle_seq_idle seq_assoc test_seq_test)
  also have "... \<ge> (rely r) \<iinter> idle;\<tau>(expr_eq e1 v1);idle;\<tau>(expr_eq e2 v2);idle"
    using rely_constant_expression e1_stable rely_refine_within seq_assoc by metis
  finally show ?thesis .
qed

lemma single_reference_eval_e2_first:
  assumes e1_stable: "estable e1 r"
  shows "(rely r) \<iinter> idle;\<tau>((expr_eq e1 v1) \<inter> (expr_eq e2 v2));idle
       \<ge> (rely r) \<iinter> idle;\<tau>(expr_eq e2 v2);idle;\<tau>(expr_eq e1 v1);idle"
proof -
  have cases: "nil = \<tau>(expr_eq e1 v1) \<squnion> \<tau>(-expr_eq e1 v1)"
    using test_nondet_compl by auto
  have "(rely r) \<iinter> idle;\<tau>((expr_eq e1 v1) \<inter> (expr_eq e2 v2));idle =
                   (rely r) \<iinter> \<tau>(expr_eq e1 v1);idle;\<tau>((expr_eq e1 v1) \<inter> (expr_eq e2 v2));idle \<squnion>
                   (rely r) \<iinter> \<tau>(-expr_eq e1 v1);idle;\<tau>((expr_eq e1 v1) \<inter> (expr_eq e2 v2));idle"
    by (metis cases nondet_seq_distrib conj.sync_nondet_distrib seq_nil_left)
  also have "... = (rely r) \<iinter> \<tau>(expr_eq e1 v1);idle;\<tau>(expr_eq e1 v1);\<tau>(expr_eq e2 v2);idle \<squnion>
                   (rely r) \<iinter> \<tau>(-expr_eq e1 v1);idle;\<tau>(expr_eq e1 v1);\<tau>(expr_eq e2 v2);idle"
    by (simp add: test_inf_eq_seq seq_assoc)
  also have "... = (rely r) \<iinter> \<tau>(expr_eq e1 v1);idle;\<tau>(expr_eq e2 v2);idle \<squnion>
                   (rely r) \<iinter> \<tau>(-expr_eq e1 v1);idle;\<tau>(expr_eq e1 v1);idle"
  proof -
    have "(rely r) \<iinter> \<tau>(expr_eq e1 v1);idle;\<tau>(expr_eq e1 v1);\<tau>(expr_eq e2 v2);idle
        = (rely r) \<iinter> \<tau>(expr_eq e1 v1);idle;\<tau>(expr_eq e2 v2);idle"
       using stable_test estable_stable_eq e1_stable equal_within_rely_left by metis
    moreover have "(rely r) \<iinter> \<tau>(-expr_eq e1 v1);idle;\<tau>(expr_eq e1 v1);\<tau>(expr_eq e2 v2);idle =
                   (rely r) \<iinter> \<tau>(-expr_eq e1 v1);idle;\<tau>(expr_eq e1 v1);idle"
      using stable_negate_test estable_stable_neq e1_stable 
            equal_within_rely_left seq_assoc by metis
    ultimately show ?thesis by simp
  qed
  also have "... \<ge> (rely r) \<iinter> \<tau>(expr_eq e1 v1);idle;\<tau>(expr_eq e2 v2);idle;\<tau>(expr_eq e1 v1);idle \<squnion>
                   (rely r) \<iinter> \<tau>(-expr_eq e1 v1);idle;\<tau>(expr_eq e2 v2);idle;\<tau>(expr_eq e1 v1);idle" (is "_ \<ge> ?rhs")
      using seq_nil_left nil_ref_test seq_assoc seq_mono_left seq_mono_right
          idle_seq_idle conj.sync_mono_right sup_mono by metis
  also have "?rhs = (rely r) \<iinter> idle;\<tau>(expr_eq e2 v2);idle;\<tau>(expr_eq e1 v1);idle"
    by (metis cases nondet_seq_distrib conj.sync_nondet_distrib seq_nil_left)
  finally show ?thesis .      
qed

lemma single_reference_eval_binary_one_stable:
  assumes e1_stable: "estable e1 r"
  assumes r_reflexive: "refl r"
  shows "(rely r) \<iinter> idle;\<tau>((expr_eq e1 v1) \<inter> (expr_eq e2 v2));idle
       \<ge> (rely r) \<iinter> idle;\<tau>(expr_eq e1 v1);idle \<parallel> (rely r) \<iinter> idle;\<tau>(expr_eq e2 v2);idle"
proof -
  have "(rely r) \<iinter> idle;\<tau>((expr_eq e1 v1) \<inter> (expr_eq e2 v2));idle \<ge> 
        (rely r) \<iinter> (idle;\<tau>(expr_eq e1 v1);idle;\<tau>(expr_eq e2 v2);idle \<squnion>
                   idle;\<tau>(expr_eq e2 v2);idle;\<tau>(expr_eq e1 v1);idle)" (is "_ \<ge> ?rhs")
    using e1_stable single_reference_eval_e1_first single_reference_eval_e2_first
       conj.sync_nondet_distrib by fastforce
  also have "?rhs = (rely r) \<iinter> (idle;\<tau>(expr_eq e1 v1);idle \<parallel> idle;\<tau>(expr_eq e2 v2);idle)"
    using idle_sync_test by metis
  also have "... \<ge> ((rely r) \<iinter> (guar r) \<iinter> idle;\<tau>(expr_eq e1 v1);idle)
                     \<parallel> ((rely r) \<iinter> (guar r) \<iinter> idle;\<tau>(expr_eq e2 v2);idle)" (is "_ \<ge> ?rhs")
    using rely_par_distrib by metis
  also have "?rhs \<ge> (rely r) \<iinter> idle;\<tau>(expr_eq e1 v1);idle \<parallel> (rely r) \<iinter> idle;\<tau>(expr_eq e2 v2);idle"
    using guar_conj_idle_test_idle r_reflexive conj.sync_mono_right conj_assoc par.sync_mono by metis
  finally show ?thesis .
qed
  
lemma single_reference_test_binary:
  assumes e1_or_e2_stable: "estable e1 r \<or> estable e2 r"
  assumes r_reflexive: "refl r"
  shows "(rely r) \<iinter> idle;\<tau>((expr_eq e1 (v1::'v)) \<inter> (expr_eq e2 (v2::'v)));idle
       \<ge> (rely r) \<iinter> idle;\<tau>(expr_eq e1 v1);idle \<parallel> (rely r) \<iinter> idle;\<tau>(expr_eq e2 v2);idle"
proof (cases "estable e1 r")
  case True
  then show ?thesis using single_reference_eval_binary_one_stable r_reflexive by simp
next
  case False
  then have e2_stable: "estable e2 r" using e1_or_e2_stable by simp
  then show ?thesis using single_reference_eval_binary_one_stable e2_stable r_reflexive
    inf_commute par_commute by metis
qed
  
lemma NONDET_mono_quant:
  assumes "\<forall>a\<in>p. ((x a)::'a) \<ge> (y a)"
  shows "(\<Squnion>(a)\<in>p. (x a)) \<ge> (\<Squnion>(a)\<in>p. (y a)) "
  by (simp add: SUP_subset_mono assms)

lemma single_reference_eval_helper: 
  assumes r_reflexive: "refl r"
  shows "(single_reference e r) \<Longrightarrow> (rely r) \<iinter> idle;\<tau>(expr_eq e (v::'v));idle \<ge> (expr_cmd e v)"
proof (induction e arbitrary: v)
  case const: (Constant x)   
  show "(rely r) \<iinter> (idle;\<tau>(expr_eq (Constant x) v);idle) \<ge> 
                    expr_cmd (Constant x) v"
    using rely_remove by simp
next
  case (Variable x)
  show "(rely r) \<iinter> (idle;\<tau>(expr_eq (Variable x) v);idle) \<ge>
                    expr_cmd (Variable x) v"
    using rely_remove by simp
next
  case unaryop: (UnaryOp opr e1)    
  have "(expr_eq (UnaryOp opr e1) v) = (\<Union>v1\<in>{v1. opr v1 = v}. (expr_eq e1 v1))"
    unfolding expr_eq_def by auto
  then have "(rely r) \<iinter> idle;\<tau>(expr_eq (UnaryOp opr e1) v);idle 
      = (rely r) \<iinter> idle;(\<Squnion>v1\<in>{v1. opr v1 = v}. \<tau>(expr_eq e1 v1);idle)"
    using test_Sup Nondet_seq_distrib by (simp add: seq_assoc SUP_image)
  (* This is a refinement because the set {v1. opr v1 = v} may be empty! *)
  also have "... \<ge> (rely r) \<iinter> (\<Squnion>v1\<in>{v1. opr v1 = v}. idle;\<tau>(expr_eq e1 v1);idle)" (is "_ \<ge> ?rhs")
    by (simp add: seq_NONDET_distrib_empty conj.sync_mono_right seq_assoc)
  also have "?rhs \<ge> (\<Squnion>v1\<in>{v1. opr v1 = v}. (rely r) \<iinter> idle;\<tau>(expr_eq e1 v1);idle)" (is "_ \<ge> ?rhs")
    by (simp add: conj_NONDET_distrib_empty)
  also have "?rhs \<ge> (\<Squnion>v1\<in>{v1. opr v1 = v}. expr_cmd e1 v1)" (is "_ \<ge> ?rhs")
  proof -
    have "single_reference e1 r" using unaryop by auto
    then show ?thesis using unaryop by (meson NONDET_mono_quant)
  qed
  also have "?rhs = expr_cmd (UnaryOp opr e1) v" 
    by simp
  finally show ?case .
next
  case binaryop: (BinaryOp opr e1 e2)
  let ?vsplit = "{(v1,v2). (opr v1 v2 = v)}"
  have "(expr_eq (BinaryOp opr e1 e2) v) = (\<Union>(v1,v2)\<in>?vsplit. (expr_eq e1 v1) \<inter> (expr_eq e2 v2))"
    unfolding expr_eq_def by auto
  then have "(rely r) \<iinter> idle;\<tau>(expr_eq (BinaryOp opr e1 e2) v);idle
         = (rely r) \<iinter> idle;(\<Squnion>(v1,v2)\<in>?vsplit. \<tau>((expr_eq e1 v1) \<inter> (expr_eq e2 v2)));idle" 
    by (simp add: test_Nondet2)
  (* This is a refinement because the set {(v1,v2). opr v1 v2 = v} may be empty! *)
  also have "... \<ge> (rely r) \<iinter> (\<Squnion>(v1,v2)\<in>?vsplit. idle;\<tau>((expr_eq e1 v1) \<inter> (expr_eq e2 v2));idle)" (is "_ \<ge> ?rhs")
    by (simp add: NONDET_seq_distrib2 seq_NONDET_distrib_empty2 conj.sync_mono_right seq_assoc)
  also have "?rhs \<ge> (\<Squnion>(v1,v2)\<in>?vsplit. (rely r) \<iinter>  idle;\<tau>((expr_eq e1 v1) \<inter> (expr_eq e2 v2));idle)" (is "_ \<ge> ?rhs")
    by (simp add: conj_NONDET_distrib_empty2)
  also have "?rhs \<ge> (\<Squnion>(v1,v2)\<in>?vsplit. ((rely r) \<iinter> (idle;\<tau>(expr_eq e1 v1);idle))
                                      \<parallel> ((rely r) \<iinter> (idle;\<tau>(expr_eq e2 v2);idle)))" (is "_ \<ge> ?rhs")
    using single_reference_test_binary[where ?'v = 'v] binaryop
    by (simp add: NONDET_mono_quant r_reflexive)
  also have "?rhs \<ge> (\<Squnion>(v1,v2)\<in>?vsplit. (expr_cmd e1 v1) \<parallel> (expr_cmd e2 v2))" (is "_ \<ge> ?rhs")
  proof -
    have a1: "single_reference e1 r \<and> single_reference e2 r" using binaryop by simp
    have "\<forall>v1. (rely r) \<iinter> (idle;\<tau>(expr_eq e1 v1);idle) \<ge> (expr_cmd e1 v1)"
      using a1 binaryop by blast
    moreover have "\<forall>v2. (rely r) \<iinter> (idle;\<tau>(expr_eq e2 v2);idle) \<ge> (expr_cmd e2 v2)"
      using a1 binaryop by blast
    ultimately show ?thesis by (simp add: NONDET_mono_quant par.sync_mono)
  qed
  also have "?rhs \<ge> expr_cmd (BinaryOp opr e1 e2) v"
    by simp
  finally show ?case .
qed 
  
lemma single_reference_impl_id:
  "(single_reference e r) \<Longrightarrow> (single_reference e (r \<union> Id))"
proof (induction e)
  case (Constant x) then show ?case by simp
next
  case (Variable x) then show ?case by simp
next
  case (UnaryOp x1a e) then show ?case by simp
next
  case b1: (BinaryOp x1a e1 e2)    
  then show ?case
  proof (cases "estable e1 r")
    case True
    then have "estable e1 (r \<union> Id)" using estable_def by blast
    then show ?thesis using b1 by simp
  next
    case False
    then have "estable e2 r" using b1 by simp
    then have "estable e2 (r \<union> Id)" using b1 estable_def by blast
    then show ?thesis using b1 by simp
  qed
qed

(* Lemma 25. Formerly  Law 5 - single-reference-test *)
lemma single_reference_eval:
  assumes single_ref: "(single_reference e r)"
  shows "(rely r) \<iinter> idle;\<tau>(expr_eq e v);idle \<ge> (\<lbrakk>e\<rbrakk>v)"
proof -
  have "r \<subseteq> (r \<union> Id)"
    by simp  
  then have "(rely r) \<iinter> (idle;\<tau>(expr_eq e v);idle) \<ge> (rely (r \<union> Id)) \<iinter> (idle;\<tau>(expr_eq e v);idle)" (is "_ \<ge> ?rhs")
    using rely_weaken conj.sync_mono_left by metis
  also have "?rhs \<ge> (expr_cmd e v)"
  proof - 
    have "(refl (r \<union> Id))" by auto
    then show ?thesis using single_reference_impl_id single_ref single_reference_eval_helper by metis
  qed
  finally show ?thesis .
qed

lemma rely_eval:
  assumes single_reference_e: "single_reference e r"
  assumes q_impl: "(p \<inter> (expr_eq e k)) \<triangleleft> Id \<subseteq> q"
  assumes tolerates_interference: "tolerates_interference p q r" (* q tolerates r from p*)
  shows "(rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr> q\<rparr> \<ge> (\<lbrakk>e\<rbrakk>k)"
proof -  
  have "(rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr> q\<rparr> = (rely r) \<iinter> idle;\<lbrace>p\<rbrace>; \<lparr> q\<rparr>;idle"
    using tolerate_interference tolerates_interference by simp
  also have "... \<ge> (rely r) \<iinter> idle;\<lbrace>p\<rbrace>; \<lparr> (expr_eq e k) \<triangleleft> Id\<rparr>;idle" (is "_ \<ge> ?rhs")
  proof -
    have "(p \<inter> (expr_eq e k)) \<triangleleft> Id = p \<triangleleft> ((expr_eq e k) \<triangleleft> Id)"
      unfolding restrict_domain_def by auto
    then show ?thesis
      using q_impl spec_strengthen assert_restricts_spec conj.sync_mono_right 
            rely_refine_within seq_assoc by metis
  qed
  also have "?rhs \<ge> (rely r) \<iinter> idle;\<lparr>(expr_eq e k) \<triangleleft> Id\<rparr>;idle" (is "_ \<ge> ?rhs")
    using rely_refine_within spec_to_test
    by (smt assert_nil conj.nil_sync_assert conj.sync_assoc 
        conj.sync_commute nil_conj_rely seq_assoc seq_nil_right)
  also have "?rhs \<ge> (rely r) \<iinter> idle;\<tau>(expr_eq e k);idle" (is "_ \<ge> ?rhs")
  proof -
    have "{s. (s,s) \<in> ((expr_eq e k) \<triangleleft> Id)} = (expr_eq e k)"
      unfolding restrict_domain_def restrict_range_def by auto
    then have "\<lparr>(expr_eq e k) \<triangleleft> Id\<rparr> \<ge> \<tau> (expr_eq e k)" using spec_to_test by metis
    then show ?thesis using spec_to_test rely_refine_within conj.sync_mono_right by simp
  qed
  also have "?rhs \<ge> \<lbrakk>e\<rbrakk>k"
    using single_reference_eval single_reference_e by simp
  finally show ?thesis .
qed

(* TODO: This proof is old and can be much simplified by proving it in terms of the above lemma. *)
lemma rely_eval_expr: 
  assumes single_reference_e: "single_reference e r"
  assumes r_maintains_p: "stable p r" (* "p \<triangleleft> r \<subseteq> range_restrict p" *)
  assumes e_establishes_e0: "p \<inter> (expr_eq e k) \<subseteq> b0"
  assumes e0_stable_under_pr: "stable b0 (p \<triangleleft> r)"
  shows "(rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr> r\<^sup>* \<triangleright> (p \<inter> b0)\<rparr> \<ge> (\<lbrakk>e\<rbrakk>k)"
proof -  
  have "(rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr> r\<^sup>* \<triangleright> (p \<inter> b0)\<rparr> \<ge> (rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr> r\<^sup>* \<triangleright> p\<rparr>;\<lbrace>p\<rbrace>; \<lparr> r\<^sup>* \<triangleright> (p \<inter> b0)\<rparr>" (is "_ \<ge> ?rhs")
  proof -
    have "relcomp (r\<^sup>* ) (r\<^sup>* \<triangleright> (p \<inter> b0)) = (r\<^sup>* \<triangleright> (p \<inter> b0))" unfolding restrict_range_def by auto
    then show ?thesis using spec_seq_introduce conj.sync_mono_right
      by (metis seq_assoc seq_mono_right) 
  qed
  also have "?rhs \<ge> (rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr> r\<^sup>* \<triangleright> p\<rparr>;\<lbrace>p\<rbrace>; \<lparr> Id \<triangleright> (p \<inter> b0)\<rparr>;\<lbrace>p \<inter> b0\<rbrace>; \<lparr>r\<^sup>* \<triangleright> (p \<inter> b0)\<rparr>" (is "_ \<ge> ?rhs")
  proof -
    have "relcomp Id (r\<^sup>* \<triangleright> (p \<inter> b0)) = (r\<^sup>* \<triangleright> (p \<inter> b0))" unfolding restrict_range_def by auto
    then show ?thesis using spec_seq_introduce seq_mono_right seq_assoc conj.sync_mono_right by metis
  qed
  also have "?rhs \<ge> (rely r) \<iinter> idle;\<lbrace>p\<rbrace>; \<lparr> Id \<triangleright> (p \<inter> b0)\<rparr>; \<lbrace>p \<inter> b0\<rbrace>;\<lparr>r\<^sup>* \<triangleright> (p \<inter> b0)\<rparr>" (is "_ \<ge> ?rhs")
    using r_maintains_p rely_idle refine_within_rely_left by metis
  also have "?rhs \<ge> (rely r) \<iinter> idle;\<lbrace>p\<rbrace>; \<lparr> Id \<triangleright> (p \<inter> b0)\<rparr>;idle" (is "_ \<ge> ?rhs")
  proof -
    have "stable (p \<inter> b0) r"
      using r_maintains_p e0_stable_under_pr unfolding stable_def restrict_domain_def by auto
    then show ?thesis using rely_idle refine_within_rely_right
      by (simp add: seq_assoc)
  qed
  also have "?rhs \<ge> (rely r) \<iinter> idle;\<tau>(expr_eq e k);idle" (is "_ \<ge> ?rhs")
  proof -
    have "p \<triangleleft> (Id \<triangleright> (expr_eq e k)) \<subseteq> Id \<triangleright> (p \<inter> b0)"
      using e_establishes_e0 unfolding restrict_range_def restrict_domain_def by auto
    then have "\<lbrace>p\<rbrace>; \<lparr> Id \<triangleright> (p \<inter> b0)\<rparr> \<ge> \<lbrace>p\<rbrace>; \<lparr> Id \<triangleright> (expr_eq e k)\<rparr>" (is "_ \<ge> ?rhs")
      using spec_strengthen
      by (metis seq_mono_right assert_restricts_spec) 
    also have "?rhs \<ge> \<tau>(expr_eq e k)" 
    proof -
      have "{s. (s,s) \<in> (Id \<triangleright> (expr_eq e k))} = (expr_eq e k)" unfolding restrict_range_def by auto
      then show ?thesis using spec_to_test
        by (metis (no_types, lifting) assert_galois_test nil_ref_test order_trans seq_mono_left spec_id_nil spec_test_restricts) 
    qed
    finally show ?thesis using conj.sync_mono_right seq_mono_left seq_mono_right seq_assoc by metis
  qed
  also have "?rhs \<ge> (\<lbrakk>e\<rbrakk>k)"
    using single_reference_eval single_reference_e by metis
  finally show ?thesis .
qed

lemma idle_eval: "idle \<ge> (\<lbrakk>e\<rbrakk>k)"
proof (induct e arbitrary: k)
  case (Constant x)
  have "idle \<ge> idle ; \<tau> (expr_eq (Constant x) k) ; idle"
    by (metis guar_distrib_seq idle_def idle_seq_idle nil_ref_test seq_mono seq_nil_right seq_term_term)
  thus ?case by simp
next
  case (Variable x)
  have "idle \<ge> idle ; \<tau> (expr_eq (Variable x) k) ; idle"
    by (metis guar_distrib_seq idle_def idle_seq_idle nil_ref_test seq_mono seq_nil_right seq_term_term)
  thus ?case by simp
next
  case (UnaryOp x1a e)
  have "(\<And>k::'c. \<lbrakk>e\<rbrakk>k \<le> idle) \<Longrightarrow> \<Squnion> (expr_cmd e ` {v1::'c. x1a v1 = k}) \<le> idle"
    by (rule SUP_least, clarsimp)
  thus ?case by (simp add: UnaryOp.hyps)
next
  case (BinaryOp x1a e1 e2)
  then show ?case
    apply(clarsimp)
    apply(rule SUP_least)
    using idle_par_idle par.sync_mono by fastforce
qed

lemma eval_guar_absorb:
  assumes g_reflexive: "refl g"
  shows "(guar g) \<iinter> (\<lbrakk>e\<rbrakk>k) = (\<lbrakk>e\<rbrakk>k)"
proof (rule antisym)
  show "guar g \<iinter> (\<lbrakk>e\<rbrakk>k) \<ge> (\<lbrakk>e\<rbrakk>k)"
  proof (induction e arbitrary: k)
    case (Constant x)
    have "(guar g) \<iinter> (\<lbrakk>(Constant x)\<rbrakk>k) = (guar g) \<iinter> idle;\<tau>(expr_eq (Constant x) k);idle"
      by simp
    also have "... \<ge> idle;\<tau>(expr_eq (Constant x) k);idle"
      using guar_idle g_reflexive guar_distrib_seq guar_conj_idle_test_idle by blast
    finally show ?case by simp
  next
    case (Variable x)
    have "(guar g) \<iinter> (\<lbrakk>(Variable x)\<rbrakk>k) = (guar g) \<iinter> idle;\<tau>(expr_eq (Variable x) k);idle"
      by simp
    also have "... \<ge> idle;\<tau>(expr_eq (Variable x) k);idle"
      using guar_idle g_reflexive guar_distrib_seq guar_conj_idle_test_idle by blast
    finally show ?case by simp
  next
    case a1: (UnaryOp op e)
    have "(guar g) \<iinter> (\<lbrakk>(UnaryOp op e)\<rbrakk>k) = (guar g) \<iinter> (\<Squnion>v1\<in>({v1. (op v1 = k)}). (expr_cmd e v1))"
      by simp
    also have "... \<ge> (\<Squnion>v1\<in>({v1. (op v1 = k)}). (guar g) \<iinter> (expr_cmd e v1))" (is "_ \<ge> ?rhs")
      using conj_NONDET_distrib_empty by auto
    also have "?rhs \<ge>  (\<Squnion>v1\<in>({v1. (op v1 = k)}). (expr_cmd e v1))"
      using a1 by (simp add: NONDET_mono_quant)
    finally show ?case by simp
  next
    case a1: (BinaryOp op e1 e2)
    have "(guar g) \<iinter> (\<lbrakk>(BinaryOp op e1 e2)\<rbrakk>k) =
           (guar g) \<iinter> (\<Squnion>(v1,v2)\<in>({(v1,v2). (op v1 v2 = k)}). (expr_cmd e1 v1) \<parallel> (expr_cmd e2 v2))"
      by simp
    also have "... \<ge> (\<Squnion>(v1,v2)\<in>({(v1,v2). (op v1 v2 = k)}).
                           (guar g) \<iinter> ((expr_cmd e1 v1) \<parallel> (expr_cmd e2 v2)))" (is "_ \<ge> ?rhs")
      using conj_NONDET_distrib_empty2 by auto
    also have "?rhs \<ge> (\<Squnion>(v1,v2)\<in>({(v1,v2). (op v1 v2 = k)}). 
                          ((guar g) \<iinter> (expr_cmd e1 v1)) \<parallel> ((guar g) \<iinter> (expr_cmd e2 v2)))" (is "_ \<ge> ?rhs")
      using guar_distrib_par by (simp add: NONDET_mono_quant)
    also have "?rhs \<ge> (\<Squnion>(v1,v2)\<in>({(v1,v2). (op v1 v2 = k)}). 
                          (expr_cmd e1 v1) \<parallel> (expr_cmd e2 v2))"
      using a1 par.sync_mono by (simp add: NONDET_mono_quant)
    finally show ?case by simp
  qed
next
  show "(\<lbrakk>e\<rbrakk>k) \<ge> guar g \<iinter> (\<lbrakk>e\<rbrakk>k)"
    using guar_introduce by simp
qed


(* Given a variable accessor 'v', a relation '\<preceq>', and a value 'k',
   defines the condition that v \<preceq> k *)
definition fn_less :: "('d\<Rightarrow>'e)\<Rightarrow>'e rel\<Rightarrow>'e\<Rightarrow>'d set"
  where "(fn_less v relation k) \<equiv> {s::'d. (v s, k) \<in> relation }"
    
(* Given a variable accessor 'v', and a value 'k',
   defines the condition that v = k *)
definition fn_eq ::  "('d\<Rightarrow>'e)\<Rightarrow>'e\<Rightarrow>'d set"
  where "(fn_eq v k) \<equiv> {s::'d. (v s) = k }"
    
lemma fn_eq_all:
  shows "(\<Squnion>k. \<tau>(fn_eq v k)) = nil"
proof -
  have "(\<Union>k. (fn_eq v k)) = UNIV" unfolding fn_eq_def by blast (* i.e. all states evaluate to some value *)
  then show ?thesis by (metis range_composition test_Sup test_top)
qed  


end  
end
