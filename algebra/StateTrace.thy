theory StateTrace
  imports Traces 
begin

unbundle lattice_syntax

datatype symbols = Term


type_synonym ('var, 'val) state_trace = "(('var \<Rightarrow> 'val option), symbols) trace"

type_synonym ('var, 'val) command = "('var set \<times> ('var, 'val) state_trace set)"


definition "same_dom c \<equiv> (\<forall>t\<in>(snd c). \<forall>n. case_sum (\<lambda>s. dom s = fst c) (\<lambda>_. True) (index t n))"

lemma same_domI: "(\<forall>t\<in>(snd c). \<forall>n. case_sum (\<lambda>s. dom s = fst c) (\<lambda>_. True) (index t n)) \<Longrightarrow> same_dom c"
  by (clarsimp simp: same_dom_def)

definition "non_empty c \<equiv> (\<forall>t\<in>(snd c). lengthS t \<noteq> Some 0)"

definition valid_command :: "('var, 'val) command => bool" where
 "valid_command c \<equiv> same_dom c \<and> non_empty c"

lemma valid_commandI: "same_dom c \<Longrightarrow> non_empty c \<Longrightarrow> valid_command c" by (clarsimp simp: valid_command_def)


definition first :: "('var, 'val) state_trace \<Rightarrow> ('var \<Rightarrow> 'val option) option"  
  where "first s \<equiv> (case (index s 0) of (Inl s) \<Rightarrow> Some s | (Inr s) \<Rightarrow> None )"


definition last :: "('var, 'val) state_trace \<Rightarrow> ('var \<Rightarrow> 'val option) option"  
  where "last s \<equiv> if finiteS s then (case (index s (the (lengthS s) - 1)) of 
                                 (Inl s) \<Rightarrow> Some s | (Inr s) \<Rightarrow> None ) else None"

definition "emptyS \<equiv> liftF (\<lambda>n. Inr Term)"

definition "glue t t' = (if finiteS t then 
                            liftF (\<lambda>n. if n < the (lengthS t) then index t n else
                                  (index (tail t') (n - (the (lengthS t))))) else t)" 

notation glue (infixr \<open>-o\<close> 50)

definition "match t t' \<equiv> if finiteS t then (last t = first t') else True"




definition gluing_seq :: "'var set \<Rightarrow> ('var, 'val) command  \<Rightarrow> ('var, 'val) command  \<Rightarrow> ('var, 'val) command" 
  where "gluing_seq d P Q \<equiv>
   (d, {c. \<exists>s s'. s \<in> (snd P) \<and> s' \<in> (snd Q) \<and> glue s s' = c \<and> match s s'})"

lemma dom_on_state_eq: "same_dom c \<Longrightarrow> t \<in> snd c \<Longrightarrow> isl (index t n) \<Longrightarrow> dom (projl (index t n)) = fst c" 
  apply (clarsimp simp: same_dom_def)
  apply (erule_tac x=t in ballE, erule_tac x=n in allE)
   apply (cases \<open>index t n\<close>; clarsimp)
  by (clarsimp)

lemma valid_has_first: "valid_command c \<Longrightarrow> t \<in> snd c \<Longrightarrow> first t \<noteq> None"
  apply (rule ccontr, clarsimp)
  apply (clarsimp simp: valid_command_def)
  apply (clarsimp simp: non_empty_def)
  apply (erule_tac x=t in ballE; clarsimp?)
  oops
  apply (clarsimp simp: lengthS_def first_def split: if_splits sum.splits)
  apply (clarsimp simp: finiteS_def)
  by (erule_tac x=0 in allE, clarsimp)

lemma different_doms_no_glue: "valid_command c \<Longrightarrow> valid_command c' \<Longrightarrow> fst c \<noteq> fst c' \<Longrightarrow> gluing_seq d c c' = (d, {})"
  apply (clarsimp simp: gluing_seq_def valid_command_def)
  
  apply (clarsimp simp: match_def)
  apply (clarsimp simp: last_def first_def valid_has_first split: sum.splits if_splits)
  
  oops



definition "restrict_trace d = map_trace (\<lambda>s. restrict_map s d)"

definition restrict :: "('var, 'val) command \<Rightarrow> ('var set) \<Rightarrow> ('var, 'val) command"
  where  "restrict c d = (fst c \<inter> d, restrict_trace d ` snd c)"



lemma restrict_comp: "d \<subseteq> d' \<Longrightarrow> restrict_trace d o restrict_trace d' = restrict_trace d"
  apply (clarsimp simp: restrict_trace_def)
  apply (clarsimp simp: map_trace_comp)
  by (simp add: Int_absorb1 comp_def)

lemma functorial: "d \<subseteq> d' \<Longrightarrow> d' \<subseteq> fst c \<Longrightarrow> (restrict (restrict c d') d) = (restrict c d)"
  apply (clarsimp simp: restrict_def)
  apply (intro conjI)
   apply (fastforce)
  apply (subst image_comp)
  by (clarsimp simp: restrict_comp)


lemma functorial': "d \<subseteq> d' \<Longrightarrow>  (restrict (restrict c d') d) = (restrict c d)"
  apply (clarsimp simp: restrict_def)
  apply (intro conjI)
   apply (fastforce)
  apply (subst image_comp)
  by (clarsimp simp: restrict_comp)

lemma lengthS_map_eq[simp]: "lengthS (map_trace f s) = lengthS s"
  oops
  apply (clarsimp simp: lengthS_def )
  apply (safe)
    apply (simp add: index_map_sum isl_map_sum)
   apply (clarsimp simp: finiteS_def)
    apply (simp add: index_map_sum isl_map_sum)
   apply (fastforce)
 apply (clarsimp simp: finiteS_def)
  apply (simp add: index_map_sum isl_map_sum)
  done

lemma valid_valid_restrict: "valid_command c \<Longrightarrow> d \<subseteq> fst c \<Longrightarrow> valid_command (restrict c d)"
  apply (clarsimp simp: valid_command_def)
  apply (intro conjI)
  apply (rule same_domI)
   apply (clarsimp simp:  split: sum.splits)
  apply (clarsimp simp: restrict_def)
   apply (frule_tac t=x and n=n in dom_on_state_eq, clarsimp)
  apply (clarsimp simp: restrict_trace_def)
    apply (metis index_map_sum isl_map_sum sum.disc(1))
   apply (clarsimp simp: restrict_trace_def)
   apply (frule index_map_eqD, clarsimp)
  apply (clarsimp simp: non_empty_def)
  apply (clarsimp simp: restrict_def restrict_trace_def)
  done

definition "cyl_set S d = \<Union>(snd ` {c'. valid_command c' \<and> fst c' = d \<and>  (\<exists>d'\<le>d. snd (restrict c' d') = S)})"

definition "cyl d c = (d \<union> (fst c),  (cyl_set (snd c) d  ))"

definition "refinement_order c d \<equiv> fst d \<subseteq> fst c \<and> snd (restrict c (fst d)) \<subseteq> snd d"

notation refinement_order (infixr \<open>\<preceq>\<close> 50)



lemma restrict_idemp_iff: "s |` d = s \<longleftrightarrow> dom s \<subseteq> d"
  apply (safe)
   apply (metis option.simps(3) restrict_map_def)
  apply (intro ext)
  by (metis domIff in_mono restrict_in restrict_out)


lemma refine_trans: "a \<preceq> b \<Longrightarrow> b \<preceq> c \<Longrightarrow> a \<preceq> c"
  apply (clarsimp simp: refinement_order_def, intro conjI)
   apply (blast, clarsimp simp: restrict_def)
  by (smt (verit, ccfv_SIG) Set.set_insert image_comp image_insert
              image_mono insert_subset restrict_comp)

lemma valid_restrict_eq: "valid_command a \<Longrightarrow> restrict a (fst a) = a"
  apply (clarsimp simp: restrict_def)
  apply (intro prod_eqI; clarsimp)
  apply (intro set_eqI iffI; clarsimp simp: image_iff)
   apply (clarsimp simp: restrict_trace_def)
  apply (subgoal_tac "map_trace (\<lambda>s. s |` fst a) xa = xa" )
    apply fastforce
   apply (rule trace_eqI)
   apply (clarsimp simp: index_map_sum split: sum.splits)
   apply (case_tac \<open>index xa n\<close>; clarsimp)
  apply (clarsimp simp: restrict_idemp_iff)
   apply (metis domI dom_on_state_eq sum.disc(1) sum.sel(1) valid_command_def)
  apply (rule_tac x=x in bexI; clarsimp?)
  apply (clarsimp simp: restrict_trace_def)
  apply (rule trace_eqI)
   apply (clarsimp simp: index_map_sum split: sum.splits)
   apply (case_tac \<open>index x n\<close>; clarsimp)
  by (metis dom_on_state_eq restrict_idemp_iff subsetI sum.disc(1) sum.sel(1) valid_command_def)

lemma refine_refl: "valid_command a \<Longrightarrow> a \<preceq> a"
  apply (clarsimp simp: refinement_order_def)
  by (simp add: valid_restrict_eq)

lemma refine_asym: "valid_command a \<Longrightarrow> valid_command b \<Longrightarrow> a \<preceq> b \<Longrightarrow> b \<preceq> a \<Longrightarrow> a = b"
  apply (clarsimp simp: refinement_order_def)
  apply (intro prod_eqI)
   apply (clarsimp)
  by (metis subset_antisym valid_restrict_eq)


lemma valid_valid_cyl: "valid_command b \<Longrightarrow> (fst b) \<subseteq> d \<Longrightarrow> valid_command (cyl d b)"
  apply (clarsimp simp: valid_command_def)
  apply (intro conjI)
   apply (clarsimp simp: cyl_def cyl_set_def, clarsimp simp: same_dom_def split: sum.splits)
  
  apply (metis dom_on_state_eq fst_eqD snd_eqD sum.disc(1) sum.sel(1) sup_absorb1 valid_command_def)
  apply (clarsimp simp: non_empty_def)
  apply (clarsimp simp: cyl_def cyl_set_def)
  by (simp add: non_empty_def valid_command_def)


lemma valid_dom_eq: "valid_command a \<Longrightarrow> isl (index t n) \<Longrightarrow> t \<in> snd a \<Longrightarrow> dom (projl (index t n)) = fst a"
  by (simp add: dom_on_state_eq valid_command_def)

lemma add_restrict_dom: "dom x = d \<Longrightarrow> (y ++ x) |` d = x"
  apply (intro ext; clarsimp simp: restrict_map_def, intro conjI impI; clarsimp?)
  by fastforce



definition "zip_trace f a b = liftF 
  (\<lambda>n. if (isl (index a n) \<and> isl (index b n)) then (Inl (f (projl (index a n)) (projl (index b n)))) else Inr Term)" 

lemma zip_tracedom[simp]: "s \<in> traceDom \<Longrightarrow> s' \<in> traceDom \<Longrightarrow> 
 (\<lambda>n. if isl (s n) \<and> isl (s' n) then Inl (f (projl (s n)) (projl (s' n))) else Inr Term) \<in> traceDom" 
  apply (clarsimp simp: traceDom_def)
  by metis

lemma index_zipE: "index (zip_trace f s s') n = Inl x \<Longrightarrow>
      (isl (index s n) \<Longrightarrow> isl (index s' n) \<Longrightarrow> P (f (projl (index s n)) (projl (index s' n)))) \<Longrightarrow>
     P x "
  apply (clarsimp simp: zip_trace_def, transfer, clarsimp)
  apply (clarsimp split: if_splits)
  done

lemma finiteS_lengthS_cases:
" (\<And>n. finiteS x \<Longrightarrow> \<not>isl (index x n) \<Longrightarrow> \<forall>n'\<ge>n. \<not>isl (index x n') \<Longrightarrow> \<forall>n'<n. isl (index x n') \<Longrightarrow>  P (Some n)) \<Longrightarrow> (\<not>finiteS x \<Longrightarrow> P None) \<Longrightarrow> 
      P (lengthS x)"
  apply (case_tac "finiteS x")
  apply (clarsimp simp: finiteS_def lengthS_def, transfer)
  apply (atomize)
   apply (erule_tac x="LEAST n. \<not> isl (x n)" in allE)
  apply (drule mp) back
    apply (metis (mono_tags, lifting) LeastI mem_Collect_eq traceDom_def)
   apply (drule mp) back
  apply (clarsimp)
  using not_less_Least apply blast
   apply (clarsimp)
  apply (clarsimp)
  apply (clarsimp simp: lengthS_def)
  done


lemma lengthS_eqI:"(m = None \<Longrightarrow> \<forall>n. isl (index t n)) \<Longrightarrow> 
   (\<And>n. m = Some n \<Longrightarrow> \<forall>n'. if n' < n then isl (index t n') else \<not>isl (index t n')) \<Longrightarrow> 
  lengthS t = m" 
  apply (rule finiteS_lengthS_cases)
   apply (clarsimp)
   apply (metis dual_order.refl not_Some_eq not_less_iff_gr_or_eq)
  by (metis finiteS_def not_None_eq verit_comp_simplify1(1))

lemma index_liftF: "f \<in> traceDom \<Longrightarrow> index (liftF f) = f"
  by (intro ext, transfer, clarsimp)

lemma isl_monotone: "isl (index b j) \<Longrightarrow> j \<ge> i \<Longrightarrow> isl (index b i)"
  apply (transfer)
  apply (clarsimp simp: traceDom_def)
  by fastforce

lemma index_zip_iff: "index (zip_trace f a b) n =
   (if isl (index a n) \<and> isl (index b n) then Inl (f (projl (index a n)) (projl (index b n))) else Inr Term)"
  apply (clarsimp simp: zip_trace_def)
  apply (subst index_liftF)
   apply (clarsimp simp: traceDom_def) 
  apply (meson isl_monotone)
  apply (subst index_liftF)
   apply (clarsimp simp: traceDom_def)
  apply (meson isl_monotone)
  apply (safe)
    apply (clarsimp)+
  done




lemma finite_zip_iff[simp]: "finiteS (zip_trace f s s') \<longleftrightarrow> finiteS s \<or> finiteS s'" 
  apply (safe; clarsimp simp: finiteS_def index_zip_iff)
    apply (rule_tac x=n in exI)
    apply (fastforce)+
  done



lemma id_imageI: "(\<And>x. x \<in> S \<Longrightarrow> f x = x) \<Longrightarrow> f ` S = S"
  apply (clarsimp)
  done




lemma subset_imageD: "f ` A \<subseteq> B \<Longrightarrow> x \<in> A \<Longrightarrow> f x \<in> B"
  apply (clarsimp)
  apply (drule_tac c="f x" in subsetD)
   apply (fastforce simp: image_iff)
  apply (clarsimp)
  done

definition "junk d \<equiv> (\<lambda>v. if v \<in> d then Some undefined else None)"




lemma [simp]: "dom (junk d) = d"
  by (clarsimp simp: junk_def dom_def)

lemma map_add_idemp[simp]:"a ++ a = a"
  by (intro ext; clarsimp simp: map_add_def split: option.splits)

lemma restrict_fst_iff[simp]: "fst (restrict a d) = (fst a \<inter> d)"
  by (clarsimp simp: restrict_def)

lemma [simp]: "fst (cyl d b) = d \<union> (fst b) " by (clarsimp simp: cyl_def)

notation fst ("_\<^sub>\<delta>")

notation "cyl_set" (infixr "\<rhd>" 45 )

definition gluing_seq' :: "('a \<Rightarrow> 'c option, symbols) trace  \<Rightarrow> ('a \<Rightarrow> 'c option, symbols) trace  \<Rightarrow> ('a \<Rightarrow> 'c option, symbols) trace set" 
  where "gluing_seq' t t' \<equiv>
   ({c. \<exists>s s'. s = t \<and> s' = t' \<and> glue s s' = c \<and> match s s'})"

definition "conv f P Q =  (\<Squnion>x\<in>P. \<Squnion>y\<in>Q. f x y)"

definition "lift_op f c c' = (let d = fst c \<union> fst c' in (d, conv f (snd c \<rhd> d) (snd c' \<rhd> d)) )" 

definition "states t = {x. \<exists>n. index t n = Inl x}"

definition "dom_t t = (\<Squnion>x \<in> (states t). dom x)"

lemma valid_dom_fst: "valid_command a \<Longrightarrow> \<forall>x\<in>(snd a). dom_t x = fst a"
  apply (clarsimp simp: valid_command_def dom_t_def)
  apply (intro set_eqI iffI; clarsimp simp: states_def)
   apply (metis domI dom_on_state_eq sum.disc(1) sum.sel(1))
  by (metis Least_eq_0 dom_on_state_eq finiteS_def lengthS_def non_empty_def sum.collapse(1))

lemma valid_dom_t_restrict: "valid_command a \<Longrightarrow> t \<in> snd a \<Longrightarrow> dom_t (restrict_trace d t) = fst a \<inter> d"
  apply (clarsimp simp: dom_t_def states_def restrict_trace_def index_map_sum split: sum.splits)
  apply (intro set_eqI iffI; clarsimp split: sum.splits)
   apply (case_tac "(index t n)"; clarsimp)
  apply (subgoal_tac "x \<in> dom (aa |` d)")
    apply (metis IntE dom_restrict sum.disc(1) sum.sel(1) valid_dom_eq)
   apply blast
  by (metis (no_types, lifting) Int_iff bot_nat_0.not_eq_extremum dom_restrict finiteS_def
      index_map_eqD index_map_sum isl_map_sum lengthS_def non_empty_def not_less_Least 
      sum.collapse(1) valid_command_def valid_dom_eq)

lemma in_cyl_iff: " valid_command (c, C) \<Longrightarrow> c \<subseteq> d \<Longrightarrow> valid_command (d, A) \<Longrightarrow> a \<in> A \<Longrightarrow>  
      a \<in> (cyl_set C d) \<longleftrightarrow> (\<exists>c'. c' \<in> C \<and> restrict_trace c a = c')" 
  apply (intro iffI)
   defer
   apply (clarsimp)
   apply (clarsimp simp: cyl_set_def)
    apply (rule_tac x="map_index_trace (\<lambda>n x. case_sum (\<lambda>y. ( y ++ x)) (\<lambda>_.  (junk (d) ++ x)) (index a n)) `  C" in exI) 
   apply (safe)
   apply (rule valid_commandI)
  apply (intro same_domI)
      apply (clarsimp split: sum.splits)
      apply (erule index_map_indexE, clarsimp)
      apply (case_tac "index a n"; clarsimp)
       apply (metis fst_eqD snd_eqD sum.disc(1) sum.sel(1) sup.absorb_iff1 sup.commute valid_dom_eq)
      apply (simp add: subset_Un_eq valid_dom_eq)
     apply (clarsimp simp: non_empty_def)
  apply (simp add: non_empty_def valid_command_def)
  apply (rule_tac x="c" in exI)
    apply (clarsimp)
    apply (clarsimp simp: restrict_def restrict_trace_def image_comp map_map_index)
  apply (rule id_imageI)
    apply (intro trace_eqI)
    apply (clarsimp simp: index_map_index_iff, case_tac "index x n"; clarsimp)
    apply (clarsimp split: sum.splits, safe; clarsimp?)
     apply (subst add_restrict_dom)
  apply (metis fst_conv old.prod.case snd_def sum.disc(1) sum.sel(1) valid_dom_eq)
     apply (metis sum.disc(1) sum.sel(1) valid_dom_eq)
    apply (metis add_restrict_dom fst_eqD snd_eqD sum.disc(1) sum.sel(1) valid_dom_eq)
  apply (clarsimp simp: image_iff)
   apply (rule_tac x=" map_trace (\<lambda>s. s |` c) a" in bexI)
    apply (intro trace_eqI)
    apply (clarsimp simp: index_map_index_iff index_map_sum, case_tac "index a n"; clarsimp)
    apply (intro ext, clarsimp simp: map_add_def restrict_map_def split: option.splits)
   apply (simp add: restrict_trace_def)
  apply (clarsimp simp: cyl_set_def restrict_def)
  apply (subgoal_tac "d' = c")
    apply (clarsimp)
   apply (metis (no_types, opaque_lifting) fst_conv image_eqI inf.absorb_iff2 
          snd_conv valid_dom_fst valid_dom_t_restrict)
  done
  

lemma restrict_cyl_galois: "valid_command a \<Longrightarrow> valid_command b \<Longrightarrow> (restrict a (fst b)) \<preceq> b \<longleftrightarrow> a \<preceq> (cyl (fst a) b)"
  apply (intro iffI, clarsimp simp: refinement_order_def)
   apply (clarsimp simp: cyl_def restrict_def)
   apply (subst in_cyl_iff[where c="fst b" and A="snd a"], clarsimp)
  apply (clarsimp)
     apply (clarsimp simp: restrict_comp image_comp)
   apply (clarsimp simp: restrict_comp image_comp)

    apply (frule subset_imageD, assumption)
    apply (clarsimp simp: restrict_trace_def)
  oops
    apply (metis image_eqI restrict_def restrict_trace_def snd_conv sup.orderE valid_restrict_eq)
   apply (clarsimp simp: restrict_comp image_comp)
   apply (metis (no_types, lifting) image_eqI restrict_def snd_conv subset_eq sup.orderE valid_restrict_eq)
  apply (clarsimp simp: cyl_def restrict_def  refinement_order_def)
  by (smt (verit) image_eqI in_cyl_iff prod.collapse restrict_def snd_conv subsetD sup.orderE valid_restrict_eq)
 



lemma match_restrict: "match x y \<Longrightarrow> match (restrict_trace d x) (restrict_trace d y)" 
  apply (clarsimp simp: match_def last_def restrict_trace_def)
  by (case_tac "finiteS x"; clarsimp simp: index_map_sum first_def split: option.splits sum.splits)



lemma index_liftF': "f \<in> traceDom \<Longrightarrow> index (liftF f) n = f n"
  by (transfer, clarsimp)


lemma restrict_seq: "restrict_trace d (x -o y) = ((restrict_trace d x) -o (restrict_trace d y))"
  by (clarsimp simp: restrict_trace_def map_seq)

abbreviation "rest_set d c \<equiv> (restrict_trace d ` c)" 

notation "rest_set" ("_ \<lhd> _")



lemma restrict_cyl_galois_sets: " valid_command (d, b) \<Longrightarrow> valid_command (d', a) \<Longrightarrow> d \<subseteq> d' \<Longrightarrow>  (d \<lhd> a) \<subseteq> b \<longleftrightarrow> (a) \<subseteq> (b \<rhd> d') " 
  find_theorems name:galois
  apply (frule  (1) restrict_cyl_galois) back
  apply (clarsimp simp: refinement_order_def)
  apply (clarsimp simp: functorial')
  apply (clarsimp simp: restrict_def cyl_def)
  by (simp add: in_cyl_iff subset_eq)
  
  


lemma restrict_cyl: "restrict_trace d ` (c \<rhd> d) \<subseteq> (c \<rhd> d)"
  apply (clarsimp simp: cyl_def cyl_set_def restrict_trace_def)
  apply (rule_tac x=b in exI)
  apply (clarsimp)
  by (metis (mono_tags) fst_eqD image_eqI old.prod.case refine_refl 
    refinement_order_def restrict_def restrict_trace_def snd_def subset_eq)



lemma map_trace_comp': "map_trace f (map_trace g x) = map_trace (f o g) x"
  by (metis comp_eq_id_dest id_comp map_trace_comp)



definition cyl_trace :: "'var set \<Rightarrow> ('var \<Rightarrow> 'val option, symbols) trace \<Rightarrow> ('var \<Rightarrow> 'val option, symbols) trace set"
  where  "cyl_trace d t = {s. 
     \<exists>t' :: ('var \<Rightarrow> 'val option, symbols) trace. lengthS t = lengthS t' \<and> dom_t t' = d \<and> zip_trace map_add t' t = s}" 

lemma lengthS_restrict[simp]: "lengthS (restrict_trace d t) = lengthS t"
  by (clarsimp simp: restrict_trace_def)



lemma dom_t_constS[simp]: "dom_t (constS s) = dom s" 
  apply (clarsimp simp: dom_t_def)
  by (safe; clarsimp simp: states_def index_constS)

lemma cyl_set_cyl_trace_sup: "cyl_set S d = \<Union>(cyl_trace d ` S)" 
  apply (clarsimp simp: cyl_trace_def cyl_set_def, intro set_eqI iffI; clarsimp simp: restrict_def)
    apply (rule_tac x=x in bexI; clarsimp?)
   apply (rule_tac x=x in exI; clarsimp)
   apply (intro conjI)
    apply (simp add: valid_dom_fst)
   apply (intro trace_eqI)
  apply (clarsimp simp: zip_map_r restrict_trace_def)
  find_theorems zip_trace map_trace
   apply (subst index_zip_iff, clarsimp simp: split: if_splits)
   apply (safe; clarsimp?)
    apply (case_tac "index x n"; clarsimp)
  apply (intro ext)
    apply (metis (mono_tags, lifting) add_restrict_dom dom_restrict fst_conv
                 inf.absorb_iff2 map_add_dom_app_simps(3) 
                 restrict_in snd_conv sum.disc(1) sum.sel(1) valid_dom_eq)
  apply (metis sum.collapse(2) symbols.exhaust)
  oops




lemma dom_t_zipI: "(\<And>n c c'. index t n = Inl c \<Longrightarrow> index t' n = Inl c' \<Longrightarrow> dom (f c c') = d) \<Longrightarrow> lengthS t \<noteq> Some 0 \<Longrightarrow> lengthS t' \<noteq> Some 0 \<Longrightarrow>
        dom_t (zip_trace f t t') = d"
  apply (clarsimp simp: index_zip_iff dom_t_def split: if_splits)
  apply (safe; clarsimp simp: states_def)
   apply (smt (verit) domI index_zip_Inl_iff)
  apply (rule_tac x=" (f (projl (index t 0)) (projl (index t' 0)))" in exI) 
  apply (intro conjI)
   apply (rule_tac x=0 in exI)
   apply (metis finiteS_def gr_zeroI index_zip_iff lengthS_def not_less_Least)
  by (metis Least_eq_0 finiteS_def lengthS_def sum.collapse(1))
  

lemma valid_command_subset: "valid_command (d, b) \<Longrightarrow> a \<subseteq> b \<Longrightarrow> valid_command (d, a)"
  apply (clarsimp simp: valid_command_def, intro conjI)
   apply (rule same_domI)
   apply (simp add: subsetD sum.case_eq_if valid_command_def valid_dom_eq)
  apply (clarsimp simp: non_empty_def)
  by blast

lemma in_cylD: " valid_command (c, C) \<Longrightarrow> c \<subseteq> d \<Longrightarrow>   
      a \<in> (cyl_set C d) \<Longrightarrow> (\<exists>c'. c' \<in> C \<and> restrict_trace c a = c' \<and>  valid_command (d, {a}))" 

   apply (clarsimp)
  apply (clarsimp simp: cyl_set_def restrict_def image_iff)
  apply (intro conjI)
   apply (rule_tac x="a" in bexI)
    apply (subgoal_tac "d' = c", clarsimp)
    apply (metis fst_conv image_eqI inf.absorb_iff2 snd_conv valid_dom_fst valid_dom_t_restrict)
   apply (clarsimp)
  apply (subgoal_tac "d' = c", clarsimp)
  apply (erule valid_command_subset, clarsimp)
  by (metis (no_types, opaque_lifting) fst_conv image_eqI inf.absorb_iff2 snd_conv valid_dom_fst valid_dom_t_restrict)
 

lemma cyl_cyl: "valid_command a \<Longrightarrow> snd a = S \<Longrightarrow> fst a \<subseteq> c \<Longrightarrow> c \<subseteq> d \<Longrightarrow>  ((S \<rhd> c) \<rhd> d) = (S \<rhd> (c \<union> d))"
  apply (rule antisym)
   apply (clarsimp)
   apply (subst in_cyl_iff[where c="fst a"], clarsimp)
      apply (fastforce)
     prefer 2
     apply (assumption)
  
    apply (metis cyl_def fst_conv snd_conv subset_Un_eq sup.orderE valid_valid_cyl)
   apply (drule in_cylD[rotated 2])
     prefer 2
  apply (assumption)
       apply (metis cyl_def sup.orderE valid_valid_cyl)
   apply (clarsimp)
   apply (drule in_cylD[rotated 2])
   prefer 2
     apply (assumption)
    apply (clarsimp)
   apply (clarsimp)
   apply (smt (verit, best) image_comp image_insert insert_iff restrict_comp restrict_def snd_conv valid_restrict_eq)
  apply (clarsimp)
  apply (subst in_cyl_iff[where c="c"])
       apply (metis cyl_def sup.orderE valid_valid_cyl)
     apply (clarsimp)
    prefer 2
    apply (assumption)

   apply (metis cyl_def subset_trans sup.absorb_iff1 sup_absorb2 valid_valid_cyl)
  apply (drule in_cylD[where c="fst a", rotated 2])
    apply (clarsimp)
   apply (fastforce)
  apply (clarsimp)
  apply (subst in_cyl_iff[where c="fst a" and A="{restrict_trace c _}"]; clarsimp?)
  prefer 2
    apply (fastforce)
   apply (metis (no_types, lifting) Un_Int_eq(1) Un_absorb1 fst_eqD image_empty image_insert restrict_def snd_eqD valid_valid_restrict)
   apply (smt (verit, best) image_comp image_insert insert_iff restrict_comp restrict_def snd_conv valid_restrict_eq)
  done



lemma valid_cylI: "valid_command (d', c) \<Longrightarrow> d' \<subseteq> d \<Longrightarrow> valid_command (d,  c \<rhd> d)" 
  apply (intro valid_commandI)
   apply (clarsimp simp: same_dom_def split: sum.splits)
   apply (clarsimp simp: cyl_set_def restrict_def)
   apply (metis fst_eqD snd_eqD sum.disc(1) sum.sel(1) valid_dom_eq)
  apply (clarsimp simp: non_empty_def)
  apply (drule in_cylD[rotated 2], assumption, clarsimp)
  apply (clarsimp)
  by (simp add: non_empty_def valid_command_def)


lemma valid_cylI': "valid_command c \<Longrightarrow> fst c \<subseteq> d \<Longrightarrow> valid_command (d,  snd c \<rhd> d)" 
  by (metis prod.collapse valid_cylI)


lemma mono_cyl: "valid_command c \<Longrightarrow> valid_command c' \<Longrightarrow> c \<preceq> c' \<Longrightarrow> fst c \<subseteq> d \<Longrightarrow>  (snd c \<rhd> d) \<subseteq> (snd c' \<rhd> d)"
  apply (subst restrict_cyl_galois_sets[symmetric, where d="fst c'"])
    apply (fastforce)
   apply (rule valid_cylI[where d'="fst c"], fastforce)
    apply (assumption)
   apply (clarsimp simp: refinement_order_def)
  apply (fastforce)
  apply (clarsimp simp: refinement_order_def restrict_def)+
  apply (erule_tac x=xa in subset_imageD[rotated])
  apply (erule order_trans[rotated])
  apply (subst restrict_cyl_galois_sets)
    apply (metis Int_absorb1 restrict_def valid_valid_restrict)
   apply (rule_tac d'="fst c" in  valid_cylI)
    apply (clarsimp)
    apply (clarsimp)
  apply (fastforce)
  apply (clarsimp simp: cyl_def)
  apply (drule in_cylD[where c="fst c", rotated 2])
    apply (clarsimp)
   apply (clarsimp)
  apply (clarsimp)
  apply (subst in_cyl_iff[where c="fst c'"])
      apply (metis inf.absorb_iff2 restrict_def valid_valid_restrict)
     apply (fastforce)
    apply (assumption)
   apply (fastforce)
  apply (rule_tac x="restrict_trace (fst c') x" in exI)
  apply (clarsimp)
  apply (clarsimp simp: image_def)
  apply (rule_tac x="restrict_trace (fst c) x" in bexI; clarsimp?)
  by (metis (no_types, lifting) image_comp image_empty image_insert restrict_comp singletonD singletonI)

lemma cyl_commute: "valid_command (C, c) \<Longrightarrow> C \<subseteq> d \<Longrightarrow> d \<subseteq> d' \<Longrightarrow>  
   ((c \<rhd> d) \<rhd> d') = ((c \<rhd> d') \<rhd> d)" oops

lemma "d \<lhd> gluing_seq' t t' \<subseteq> gluing_seq' (restrict_trace d t) (restrict_trace d t')"
  by (clarsimp simp: gluing_seq'_def restrict_seq match_restrict)

lemma fst_lift_op: "fst (lift_op f d e) = fst d \<union> fst e"
  by (clarsimp simp: lift_op_def Let_unfold)

lemma valid_valid_conv: "valid_command (d, c) \<Longrightarrow> valid_command (d', c') \<Longrightarrow>
   valid_command (d \<union> d', conv f ( c \<rhd> d \<union> d') (c' \<rhd> d \<union> d')) "
  oops


definition "join_trace t t' = {t''. lengthS t = lengthS t' \<and> t'' = zip_trace map_add t t'}"

definition epsilon :: "'var set \<Rightarrow> ('var \<Rightarrow> 'val option, symbols) trace set"
  where
"epsilon d = {t. (\<forall>n s.  index t n = Inl s \<longrightarrow> dom s = d) \<and> lengthS t \<noteq> Some 0}" 


lemma conv_has_domain: "conv f (c \<rhd> d) (c' \<rhd> d) = (conv f (c \<rhd> d) (c' \<rhd> d) \<rhd> d)" oops

lemma snd_restrict_simp[simp]:"snd (restrict c d) = (d \<lhd> snd c)"
  by (clarsimp simp: restrict_def)


lemma conv_restrict_distrib: "(\<And>x y. f (restrict_trace d x) (restrict_trace d y) = d \<lhd> f x y) \<Longrightarrow>
  d \<lhd> (conv f c c') = (conv f (d \<lhd> c)  (d \<lhd> c'))"
  apply (intro set_eqI iffI; clarsimp simp: image_iff conv_def)
  done

lemma when_id_imageI: "(\<And>x. x \<in> c \<Longrightarrow>  f x = x) \<Longrightarrow> f ` c = c"
  apply (clarsimp)
  done

lemma galois_inj: "valid_command (d, c) \<Longrightarrow> d \<subseteq> d'' \<Longrightarrow>  d \<lhd> (c \<rhd> d'') = c"
  apply (rule antisym)
   apply (subst restrict_cyl_galois_sets, assumption)
  apply (rule valid_cylI, assumption, clarsimp)
   apply simp
   apply (clarsimp)
  apply (clarsimp simp: image_iff Bex_def )
  apply (rule_tac x="map_trace (\<lambda>t. junk (d'') ++ t) x" in exI)
  apply (intro conjI)
   apply (clarsimp simp: cyl_set_def)
   apply (rule_tac x="map_trace (\<lambda>t. junk (d'') ++ t) ` c" in exI)
   apply (intro conjI)
     apply (intro valid_commandI same_domI)
      apply (clarsimp simp: index_map_sum split: sum.splits)
      apply (case_tac "index t n"; clarsimp)
      apply (metis fst_conv old.prod.case snd_def sum.disc(1) sum.sel(1) sup.commute sup.orderE valid_dom_eq)
     apply (clarsimp simp: non_empty_def)
     apply (simp add: non_empty_def valid_command_def)
    apply (rule_tac x="d" in exI, clarsimp)
    apply (clarsimp simp: image_comp restrict_trace_def map_trace_comp')
  apply (rule when_id_imageI)
    apply (intro ext trace_eqI iffI; clarsimp simp: comp_def index_map_sum; case_tac "index xa n"; clarsimp)
    apply (intro ext; clarsimp simp: restrict_map_def map_add_def junk_def split: option.splits)
  apply (safe)
     apply (metis domIff fst_conv snd_conv sum.disc(1) sum.sel(1) valid_dom_eq)
    apply (metis domI fst_conv snd_conv sum.disc(1) sum.sel(1) valid_dom_eq)
   apply (rule image_eqI, rule refl, clarsimp)
  apply (clarsimp simp: restrict_trace_def)
  apply (intro ext trace_eqI iffI; (clarsimp simp: comp_def index_map_sum); case_tac "index x n"; clarsimp)
  by (metis add_restrict_dom fst_eqD snd_eqD sum.disc(1) sum.sel(1) valid_dom_eq)


definition "relational_join c d = (fst c \<union> fst d, 
  {t. (\<forall>n s. index t n = Inl s \<longrightarrow> dom s = (fst c \<union> fst d)) \<and> restrict_trace (fst c) t \<in> snd c \<and>
    restrict_trace (fst d) t \<in> snd d})"

lemma valid_command_interI: "valid_command (c, C)  \<Longrightarrow> valid_command (c, C \<inter> D)"
  by (meson inf.cobounded1 valid_command_subset)

lemma empty_cyl_empty: "({} \<rhd> d) = {}"
  by (clarsimp simp: cyl_set_def)

lemma galois_inf: "a \<inter> b \<subseteq> c \<longleftrightarrow> a \<subseteq>  c \<union> -b"
  apply (safe; clarsimp?)
   apply (blast)+
  done


lemma in_cylI: "valid_command (c, C) \<Longrightarrow> c \<subseteq> d \<Longrightarrow> valid_command (d, {a}) \<Longrightarrow>
   (\<exists>c'. c' \<in> C \<and> restrict_trace c a = c') \<Longrightarrow> (a \<in> (C \<rhd> d))"
  by (simp add: in_cyl_iff)

lemma relational_join_is_inf: "valid_command c \<Longrightarrow> valid_command d \<Longrightarrow>
 relational_join c d = (fst c \<union> fst d, (snd c \<rhd> (fst c \<union> fst d)) \<inter> (snd d \<rhd> (fst c \<union> fst d)))"
  apply (intro prod_eqI, clarsimp simp: relational_join_def)
  apply (clarsimp simp: relational_join_def)
  apply (rule antisym)
   apply (subst inf.bounded_iff)
   apply (intro conjI)
    apply (clarsimp)
  thm in_cylI
    apply (rule in_cylI[where c="fst c"], clarsimp)
      apply (blast)
     apply (intro valid_commandI same_domI; clarsimp?)
      apply (simp add: sum.case_eq_if)
     apply (clarsimp simp: non_empty_def)
     apply (metis lengthS_restrict non_empty_def valid_command_def)
    apply (blast)
   apply (clarsimp)
   apply (rule in_cylI[where c="fst d"], clarsimp)
  apply (blast)
     apply (intro valid_commandI same_domI; clarsimp?)
      apply (simp add: sum.case_eq_if)
     apply (clarsimp simp: non_empty_def)
     apply (metis lengthS_restrict non_empty_def valid_command_def)
    apply (blast)
  apply (clarsimp)
  apply (drule in_cylD[rotated 2, where c="fst c"], clarsimp, blast, clarsimp)
  apply (drule in_cylD[rotated 2, where c="fst d"], clarsimp, blast, clarsimp)
  by (metis fst_eqD insertI1 snd_eqD sum.disc(1) sum.sel(1) valid_dom_eq)


definition "gc_join c d = (fst c \<inter> fst d, ((fst c \<inter> fst d) \<lhd> snd c) \<union> ((fst c \<inter> fst d) \<lhd> snd d))"


lemma gc_join_refinement_order_le: 
  "c \<preceq> gc_join c d"
  apply (clarsimp simp: refinement_order_def)
  apply (intro conjI)
   apply (clarsimp simp: gc_join_def)
  apply (clarsimp simp: gc_join_def)
  done

lemma relational_join_le: "relational_join c d \<preceq> c"
  apply (clarsimp simp: refinement_order_def)
  apply (intro conjI)
   apply (clarsimp simp: relational_join_def)
  by (clarsimp simp: relational_join_def)

lemma gc_join_is_join: 
  "y \<preceq> x \<Longrightarrow> z \<preceq> x \<Longrightarrow> valid_command y \<Longrightarrow> valid_command z \<Longrightarrow> valid_command x \<Longrightarrow> gc_join y z \<preceq> x"
  apply (clarsimp simp: refinement_order_def)
  apply (intro conjI)
   apply (clarsimp simp: gc_join_def)
  apply (clarsimp simp: gc_join_def)
  apply (elim disjE)
   apply (smt (verit, ccfv_SIG) Int_greatest image_comp in_mono restrict_comp rev_image_eqI)
  apply (smt (verit, ccfv_SIG) Int_greatest image_comp in_mono restrict_comp rev_image_eqI)
  done

lemma relational_join_is_meet: "x \<preceq> y \<Longrightarrow> x \<preceq> z \<Longrightarrow> valid_command y \<Longrightarrow> valid_command z \<Longrightarrow> valid_command x \<Longrightarrow> x \<preceq> relational_join y z"
  apply (subst relational_join_is_inf; clarsimp?)
  apply (clarsimp simp: refinement_order_def)
  apply (intro conjI)
   apply (subst restrict_cyl_galois_sets[where d'="fst x"])
     apply (erule valid_cylI', fastforce)
     apply (clarsimp)
  apply (blast)
   apply (metis (no_types, lifting) cyl_cyl prod.collapse restrict_cyl_galois_sets subset_Un_eq sup_assoc sup_ge1)
  by (smt (verit, ccfv_SIG) cyl_cyl prod.collapse restrict_cyl_galois_sets sup.orderE sup_assoc sup_commute sup_ge2 valid_cylI)

lemma rel_join_inf_iff: "valid_command c \<Longrightarrow> valid_command d \<Longrightarrow> c \<preceq> d \<longleftrightarrow> relational_join d c = c"
  by (smt (verit, ccfv_threshold) cyl_def inf.absorb2 mono_cyl refine_asym
      refine_refl refinement_order_def relational_join_is_inf 
      relational_join_le restrict_cyl_galois sup_absorb2 valid_cylI' valid_restrict_eq)

lemma gc_join_sup_iff: "valid_command c \<Longrightarrow> valid_command d \<Longrightarrow> c \<preceq> d \<longleftrightarrow> gc_join d c = d"
  by (smt (z3) eq_snd_iff fst_conv gc_join_def inf.order_iff
      refinement_order_def snd_restrict_simp sup.orderE sup_ge2 valid_restrict_eq)
 

lemma valid_command_conv: "valid_command (C, c) \<Longrightarrow> valid_command (C, c') \<Longrightarrow> valid_command (C, conv f c c')"
  apply (clarsimp simp: conv_def)
  apply (clarsimp simp: valid_command_def)
  apply (intro conjI)
   apply (clarsimp simp: same_dom_def split: sum.splits)
  oops



lemma prop_6: "valid_command (A, a) \<Longrightarrow> (B \<lhd> (a \<rhd> A \<union> B)) = ((A \<inter> B \<lhd> a) \<rhd> B)"
  apply (rule antisym)
  oops

lemma conv_mono_r: "Q \<subseteq> Q' \<Longrightarrow> conv f P Q \<subseteq> conv f P Q'"
  apply (clarsimp simp: conv_def)
  apply (fastforce)
  done

lemma conv_mono_l: "P \<subseteq> P' \<Longrightarrow> conv f P Q \<subseteq> conv f P' Q"
  apply (clarsimp simp: conv_def)
  apply (fastforce)
  done

lemma valid_command_restrict: "valid_command (d, b) \<Longrightarrow> valid_command (d, d' \<lhd> b) \<Longrightarrow> d' \<subseteq> d \<Longrightarrow>   x \<in> b \<Longrightarrow>  d' = d"
  apply (frule valid_dom_fst)
  apply (frule valid_dom_fst) back
  apply (clarsimp)
  apply (erule_tac x=x in ballE)
  apply (erule_tac x=x in ballE)
    apply (clarsimp)
    apply (simp add: inf.absorb_iff2 valid_dom_t_restrict)
   apply (clarsimp)
  apply (clarsimp)
  done

  
lemma valid_restrict_iff: "valid_command (d, b) \<Longrightarrow> b = (d \<lhd> b)"
  apply (intro set_eqI iffI; clarsimp simp: image_iff)
   apply (rule_tac x=x in bexI; clarsimp?)
apply (intro trace_eqI)
    apply (clarsimp simp: restrict_trace_def index_map_sum)
    apply (case_tac "index x n"; clarsimp)
    apply (metis dual_order.refl fst_conv old.prod.case restrict_idemp_iff 
   snd_def sum.disc(1) sum.sel(1) valid_dom_eq)
  apply (subgoal_tac "restrict_trace d xa = xa"; clarsimp?)
   apply (intro trace_eqI)
    apply (clarsimp simp: restrict_trace_def index_map_sum)
    apply (case_tac "index xa n"; clarsimp)
    apply (metis dual_order.refl fst_conv old.prod.case restrict_idemp_iff 
   snd_def sum.disc(1) sum.sel(1) valid_dom_eq)
  done


lemma valid_command_cyl: "valid_command (d, c) \<Longrightarrow> c = (c \<rhd> d)" 
  apply (safe, clarsimp simp: cyl_set_def)
   apply (rule_tac x=c in exI, clarsimp)
   apply (rule_tac x=d in exI)
   apply (clarsimp simp: restrict_def)
   apply (safe)
    apply (subgoal_tac "restrict_trace d xb = xb", clarsimp)
    apply (intro trace_eqI)
    apply (clarsimp simp: restrict_trace_def index_map_sum)
    apply (case_tac "index xb n"; clarsimp)
    apply (metis dual_order.refl fst_conv old.prod.case restrict_idemp_iff 
   snd_def sum.disc(1) sum.sel(1) valid_dom_eq)
   apply (clarsimp simp: image_iff)
   apply (rule_tac x=xa in bexI)
apply (intro trace_eqI)
    apply (clarsimp simp: restrict_trace_def index_map_sum)
    apply (case_tac "index xa n"; clarsimp)
    apply (metis dual_order.refl fst_conv old.prod.case restrict_idemp_iff 
   snd_def sum.disc(1) sum.sel(1) valid_dom_eq)
   apply (clarsimp)
  apply (clarsimp simp: cyl_set_def restrict_def)
  apply (frule (1) valid_command_restrict, assumption, assumption)
  apply (clarsimp)
  using valid_restrict_iff 
  by blast





lemma "conv gluing_seq' c (conv gluing_seq' d e) = conv gluing_seq' (conv gluing_seq' c d) e"
  apply (intro set_eqI iffI)
   apply (clarsimp simp: conv_def gluing_seq'_def)
   apply (rule_tac x=xa in bexI)
    apply (rule_tac x=xb in bexI)
     apply (intro conjI)
      apply (erule match_match_glue, assumption)
     apply (rule_tac x=xc in bexI)
      apply (intro conjI)
       apply (rule trace_eqI)
  apply (subgoal_tac "match xa xb")
        apply (case_tac "finiteS xa"; case_tac "finiteS xb"; clarsimp simp: finite_index_iff infinite_index_iff index_tail_iff lengthS_iff')
  apply (subgoal_tac "\<exists>n n'. lengthS xa = Some n \<and> lengthS xb = Some n'", clarsimp)
         apply (smt (verit) Nat.diff_add_assoc Suc_diff_1 Suc_diff_Suc diff_is_0_eq gr_zeroI index_eq_finished int_ops(6) isl_iff less_Suc_eq match_empty_iff not_less_eq of_nat_0_less_iff of_nat_add plus_1_eq_Suc zero_less_diff zero_less_one)
        apply (simp add: lengthS_def)
  apply (erule match_match_glue, assumption)
      apply (erule match_match_glue', assumption)
     apply (clarsimp)+
  apply (clarsimp simp: conv_def gluing_seq'_def)
  apply (rule_tac x=xa in bexI)
   apply (rule_tac x=xb in bexI)
     apply (rule_tac x=xc in bexI)
  sorry



lemma cyl_exists: "valid_command (C, c) \<Longrightarrow> x \<in> c \<Longrightarrow> C \<subseteq> D \<Longrightarrow>  \<exists>x'. x' \<in> (c \<rhd> D)" 
 apply (rule_tac x="map_trace (\<lambda>t. junk (D) ++ t) x" in exI)
   apply (clarsimp simp: cyl_set_def)
   apply (rule_tac x="map_trace (\<lambda>t. junk (D) ++ t) ` c" in exI)
   apply (intro conjI)
     apply (intro valid_commandI same_domI)
      apply (clarsimp simp: index_map_sum split: sum.splits)
      apply (case_tac "index t n"; clarsimp)
      apply (metis fst_conv old.prod.case snd_def sum.disc(1) sum.sel(1) sup.commute sup.orderE valid_dom_eq)
     apply (clarsimp simp: non_empty_def)
     apply (simp add: non_empty_def valid_command_def)
    apply (rule_tac x="C" in exI, clarsimp)
    apply (clarsimp simp: image_comp restrict_trace_def map_trace_comp')
  apply (rule when_id_imageI)
    apply (intro ext trace_eqI iffI; clarsimp simp: comp_def index_map_sum; case_tac "index xa n"; clarsimp)
    apply (intro ext; clarsimp simp: restrict_map_def map_add_def junk_def split: option.splits)
  apply (safe)
     apply (metis domIff fst_conv snd_conv sum.disc(1) sum.sel(1) valid_dom_eq)
    apply (metis domI fst_conv snd_conv sum.disc(1) sum.sel(1) valid_dom_eq)
  by (rule image_eqI, rule refl, clarsimp)



thm in_cyl_iff[no_vars]



lemma valid_dropS: "valid_command (d, S) \<Longrightarrow> x \<in> S \<Longrightarrow> \<not>(\<exists>m. lengthS x = Some m \<and> m \<le> n)
                             \<Longrightarrow>  valid_command (d, {dropS n x})"
  apply (clarsimp simp: valid_command_def)
  apply (intro conjI)
   apply (clarsimp simp: same_dom_def)
   apply (clarsimp simp: index_drop)
   apply (metis fst_conv)
  apply (clarsimp simp: non_empty_def)
  by (metis (mono_tags, lifting) add_0 bot_nat_0.extremum_strict
      diff_is_0_eq  finiteS_def index_drop isl_iff 
     lengthS_def not_less_iff_gr_or_eq zero_less_diff)

lemma valid_takeS: "valid_command (d, S) \<Longrightarrow> x \<in> S \<Longrightarrow> n > 0 
                             \<Longrightarrow>  valid_command (d, {takeS n x})"
  apply (clarsimp simp: valid_command_def)
  apply (intro conjI)
   apply (clarsimp simp: same_dom_def)
   apply (clarsimp simp: index_take)
   apply (metis fst_conv)
  apply (clarsimp simp: non_empty_def)
  
  by (metis first_None_iff first_def index_take)

lemma lengthS_glue_le: "lengthS (x -o y) = Some n \<Longrightarrow> lengthS x = Some m \<Longrightarrow> m \<le> n"
  by (metis finite_index_iff isl_iff leI lengthS_def
     option.distinct(1) option.sel verit_comp_simplify1(1))

lemma restrict_drop_commute: "restrict_trace C (dropS n t) = (dropS n (restrict_trace C t))"
  by (intro trace_eqI; clarsimp simp: restrict_trace_def index_map_sum index_drop)


lemma restrict_take_commute: "restrict_trace C (takeS n t) = (takeS n (restrict_trace C t))"
  by (intro trace_eqI; clarsimp simp: restrict_trace_def index_map_sum index_drop index_take)

lemma restrict_drop_eq: 
      "(x -o y) = restrict_trace C t \<Longrightarrow> match x y \<Longrightarrow> lengthS x = Some n \<Longrightarrow> lengthS y \<noteq> Some 0 \<Longrightarrow>
       restrict_trace C (dropS (n - Suc 0) t) = y"
  apply (subst restrict_drop_commute)
  apply (erule subst)
  apply (intro trace_eqI, clarsimp simp: index_drop, subst finite_index_iff)
   apply (metis lengthS_def option.distinct(1))
  apply (clarsimp, intro conjI impI)
   apply (case_tac "n = 0", clarsimp)
  apply (subgoal_tac "na = 0", clarsimp)
    apply (clarsimp simp: match_def split: if_splits)
  apply (clarsimp simp: last_def first_def split: option.splits sum.splits)
     apply (metis first_None_iff first_def old.sum.simps(6))
    apply (clarsimp simp: finiteS_def lengthS_def)
   apply linarith
  apply (clarsimp simp: index_tail_iff)
  by (metis (no_types, lifting) One_nat_def Suc_pred add_diff_cancel_right
        add_less_cancel_right bot_nat_0.not_eq_extremum lengthS_def match_empty_iff option.distinct(1) plus_1_eq_Suc zero_less_Suc)

lemma restrict_take_eq: 
      "(x -o y) = restrict_trace C t \<Longrightarrow> match x y \<Longrightarrow> lengthS x = Some n \<Longrightarrow> 
       restrict_trace C (takeS n t) = x"
  apply (subst restrict_take_commute)
  apply (erule subst)
  apply (intro trace_eqI, clarsimp simp: index_take, subst finite_index_iff)
   apply (metis lengthS_def option.distinct(1))
  apply (clarsimp)
  by (metis isl_iff sum.collapse(2) symbols.exhaust)

lemma distrib_rest_conv_gluing_seq: "valid_command (C', c) \<Longrightarrow> valid_command (C', c') \<Longrightarrow> C \<subseteq> C' \<Longrightarrow> 
 C \<lhd> conv gluing_seq' c c' \<subseteq> conv gluing_seq' (C \<lhd> c) (C \<lhd> c')"
  apply (clarsimp simp: conv_def)
  apply (rule_tac x=xb in bexI)
   apply (rule_tac x=y in bexI)
    apply (clarsimp simp: gluing_seq'_def restrict_seq match_restrict)
   apply (clarsimp)+
  done


lemma conv_distrib_gluing_cyl: "valid_command (C, c) \<Longrightarrow> valid_command (C, c') \<Longrightarrow> C \<subseteq> d \<Longrightarrow>
  ((conv (gluing_seq') c c') \<rhd> d) = conv gluing_seq' (c \<rhd> d) (c' \<rhd> d)"
  apply (rule antisym)
   apply (clarsimp)
   apply (drule in_cylD[rotated 2, where c=C])
  oops
     apply (simp add: valid_command_conv)
    apply (clarsimp)
   apply (clarsimp)
   apply (clarsimp simp: conv_def)
   apply (clarsimp simp: gluing_seq'_def)
   apply (case_tac "lengthS xa = None")
    apply (clarsimp simp: inf_left_glue_left)
    apply (rule_tac x=x in bexI)
  apply (frule (1) cyl_exists[where c=c' and D=d], clarsimp)
     apply (clarsimp)
     apply (rule_tac x=x' in bexI)
      apply (clarsimp simp: inf_left_glue_left)
      apply (clarsimp simp: match_inf, assumption)
    apply (simp add: in_cyl_iff)
   apply (clarsimp)
   apply (rule_tac x="takeS y x" in bexI)
    apply (rule_tac x="dropS (y - 1) x" in bexI)
     apply (subgoal_tac "y \<noteq> 0")
  apply (metis lengthS_def lengthS_glue_le lengthS_restrict partition_glue partition_glue')
      apply (metis first_None_iff' lengthS_constS lengthS_takeS_min' match_empty_iff match_inf snd_conv valid_has_first)
    apply (erule in_cylI, clarsimp)
     apply (erule valid_dropS, clarsimp)
     apply (clarsimp)
     apply (metis One_nat_def add_diff_inverse_nat first_None_iff' le_zero_eq lengthS_glue_le lengthS_restrict nat_diff_split not_less_eq_eq plus_1_eq_Suc snd_conv valid_has_first)
    apply (rule_tac x=xb in exI; clarsimp)
    apply (rule restrict_drop_eq, assumption, clarsimp, clarsimp)
  apply (metis first_None_iff' lengthS_def match_empty_iff option.distinct(1) snd_conv valid_has_first)
   apply (erule in_cylI, clarsimp)
    apply (erule valid_takeS)
     apply (clarsimp)
  apply (metis bot_nat_0.not_eq_extremum lengthS_def match_empty_iff non_empty_def option.distinct(1) snd_conv valid_command_def)
   apply (clarsimp)
  apply (simp add: restrict_take_eq)
  apply (subst restrict_cyl_galois_sets[symmetric])
  apply (erule valid_command_conv, assumption)
   apply (simp add: valid_command_conv valid_cylI)
  apply (rule order_trans)
   apply (rule distrib_rest_conv_gluing_seq)
     apply (rule valid_cylI, assumption, clarsimp)
    apply (erule valid_cylI, clarsimp, clarsimp)
  by (simp add: galois_inj)

  

lemma lift_op_assoc: assumes conv_assoc: "(\<And>c e d. conv f c (conv f d e) = conv f (conv f c d) e)"
assumes conv_distrib: "(\<And>c c' d. ((conv f c c') \<rhd> d) = (conv f (c \<rhd> d) (c' \<rhd> d)))"
  shows "valid_command d \<Longrightarrow> 
   valid_command c \<Longrightarrow> valid_command e \<Longrightarrow>   
   lift_op f c (lift_op f d e) \<preceq> (lift_op f (lift_op f c d) e)"
  apply (subst gc_join_sup_iff)
    apply (clarsimp simp: lift_op_def Let_unfold)
    prefer 3
    apply (clarsimp simp: gc_join_def)
    apply (rule prod_eqI; clarsimp?)
     apply (clarsimp simp: lift_op_def Let_unfold)
     apply blast
    apply (clarsimp simp: fst_lift_op)
    apply (clarsimp simp: Un_assoc)
    apply (clarsimp simp: lift_op_def Let_unfold)
    apply (smt (verit, ccfv_threshold) Int_Un_eq(2) Un_Int_eq(4) conv_assoc conv_distrib cyl_cyl prod.collapse restrict_cyl sup.orderE sup_assoc sup_ge1 valid_restrict_iff valid_valid_conv)
   apply (simp add: valid_valid_conv)
  apply (clarsimp simp: lift_op_def Let_unfold)
  by (simp add: valid_valid_conv)

lemma lift_op_assoc: assumes conv_assoc: "(\<And>c e d. conv f c (conv f d e) = conv f (conv f c d) e)"
  shows "valid_command d \<Longrightarrow> 
   valid_command c \<Longrightarrow> valid_command e \<Longrightarrow>   
   lift_op f c (lift_op f d e) \<preceq> (lift_op f (lift_op f c d) e)"
  apply (clarsimp simp: refinement_order_def fst_lift_op)
  apply (intro conjI; clarsimp)
  apply (clarsimp simp: restrict_def)
  apply (clarsimp simp: lift_op_def Let_unfold)
  apply (erule_tac x="xa" in subset_imageD[rotated])
  apply (subst restrict_cyl_galois_sets)
    apply (rule valid_valid_conv)
     apply (rule valid_valid_conv)
      apply (clarsimp)+
     apply (rule valid_valid_conv)
    apply (clarsimp)
     apply (rule valid_valid_conv)
    apply (clarsimp)
   apply (clarsimp)
  oops
  apply (subst distrib_conv)
   apply (fastforce)
  apply (subst distrib_conv)
   apply (fastforce)
  apply (subst conv_assoc)
  apply (simp only: Un_assoc)
  apply (subst valid_command_cyl[where c="conv f (conv f (snd c \<rhd> fst c \<union> (fst d \<union> fst e)) (snd d \<rhd> fst c \<union> (fst d \<union> fst e))) (snd e \<rhd> fst c \<union> (fst d \<union> fst e))" and d="fst c \<union> (fst d \<union> fst e)", symmetric])
  using valid_command_cyl
   apply (smt (verit, ccfv_SIG) prod.collapse subset_Un_eq sup_commute sup_ge2 sup_left_commute valid_cylI valid_valid_conv) 
  apply (rule order_refl)
  done

lemma restrict_distrib_conv: "(\<And>d t t'. d \<lhd> f t t' \<subseteq> f (restrict_trace d t) (restrict_trace d t')) \<Longrightarrow>
    d \<lhd> conv f t t' \<subseteq> conv f (d \<lhd> t) (d \<lhd> t')"
  apply (clarsimp simp: conv_def)
  by blast

lemma conv_mono: "P \<subseteq> P' \<Longrightarrow> Q \<subseteq> Q' \<Longrightarrow> conv f P Q \<subseteq> conv f P' Q'"
  apply (clarsimp simp: conv_def)
  apply (fastforce)
  done

lemma monotone_lift_op: "valid_command d \<Longrightarrow> valid_command d' \<Longrightarrow> 
   valid_command c \<Longrightarrow> valid_command c' \<Longrightarrow>  c \<preceq> c' \<Longrightarrow> d \<preceq> d' \<Longrightarrow> 
  (\<And>d t t'. d \<lhd> f t t' \<subseteq> f (restrict_trace d t) (restrict_trace d t')) \<Longrightarrow> 
   lift_op f c d \<preceq> lift_op f c' d'"
  apply (clarsimp simp: lift_op_def Let_unfold)
  apply (subst refinement_order_def)
  apply (intro conjI; clarsimp simp: lift_op_def Let_unfold)
   apply (simp add: refinement_order_def sup.coboundedI1 sup.coboundedI2)
  apply (erule_tac x="xa" in subset_imageD[rotated])
  apply (rule order_trans)
   apply (rule restrict_distrib_conv, assumption)
  apply (clarsimp simp: galois_inj)
  apply (erule_tac c=x in subsetD[rotated])
  apply (rule conv_mono)
   apply (smt (verit) cyl_cyl mono_cyl refinement_order_def restrict_cyl_galois_sets sup.absorb_iff2 sup_assoc sup_commute sup_ge1 valid_cylI')
  apply (smt (verit) cyl_cyl mono_cyl refinement_order_def restrict_cyl_galois_sets sup.absorb_iff2 sup_assoc sup_commute sup_ge1 valid_cylI')
  done

thm relational_join_def

lemma monotone_gluing_seq: "valid_command d \<Longrightarrow> valid_command d' \<Longrightarrow> 
   valid_command c \<Longrightarrow> valid_command c' \<Longrightarrow>  c \<preceq> c' \<Longrightarrow> d \<preceq> d' \<Longrightarrow>  
   lift_op (gluing_seq') c d \<preceq> lift_op (gluing_seq') c' d'"
  apply (rule monotone_lift_op; assumption?)
  apply (clarsimp simp: gluing_seq'_def)
  by (simp add: match_restrict restrict_seq)

lemma relational_join_commute:" relational_join c d = relational_join d c"
  by (smt (verit) Collect_cong relational_join_def sup_commute)

lemma valid_relational_join: "valid_command c \<Longrightarrow> valid_command d \<Longrightarrow> valid_command (relational_join c d)"
  apply (subst relational_join_is_inf[where c=c and d=d]; clarsimp?)

  apply (intro valid_commandI; (clarsimp simp: relational_join_is_inf)?)
  apply (rule same_domI)
   apply (smt (verit) Int_Un_eq(3) UnCI dom_on_state_eq
        fst_conv snd_conv sum.case_eq_if sup_ge1 valid_command_def valid_cylI')
  apply (clarsimp simp: non_empty_def)
  by (metis first_None_iff' snd_conv sup_ge1 valid_cylI' valid_has_first)

lemma relational_join_mono: "valid_command d \<Longrightarrow> valid_command d' \<Longrightarrow> 
   valid_command c \<Longrightarrow> valid_command c' \<Longrightarrow>  c \<preceq> c' \<Longrightarrow> d \<preceq> d' \<Longrightarrow>
 relational_join c d \<preceq> relational_join c' d'"
  apply (rule relational_join_is_meet)
  using refine_trans relational_join_le apply blast
     apply (metis refine_trans relational_join_commute relational_join_le)
    apply (clarsimp)+
  by (erule (1) valid_relational_join)

lemma relational_join_assoc: "valid_command d \<Longrightarrow> valid_command e \<Longrightarrow> 
   valid_command c \<Longrightarrow> 
 relational_join c (relational_join d e) \<preceq> relational_join (relational_join c d) e"
  apply (rule relational_join_is_meet)
      apply (simp add: refine_refl relational_join_le relational_join_mono valid_relational_join)
     apply (metis refine_trans relational_join_commute relational_join_le)
    apply (clarsimp simp: valid_relational_join)+
  done

abbreviation "gseq \<equiv> lift_op gluing_seq'"

notation gseq (infixr \<open>\<Zsemi>\<close> 50)


lemma valid_gluing_seq: "valid_command a \<Longrightarrow>  valid_command c \<Longrightarrow> valid_command (a \<Zsemi> c)"
  apply (intro valid_commandI)
   apply (rule same_domI)
   apply (clarsimp simp: lift_op_def Let_unfold conv_def gluing_seq'_def fst_lift_op)
   apply (clarsimp simp: fst_lift_op split: sum.splits )
   apply (case_tac "finiteS y"; clarsimp simp: infinite_index_iff finite_index_iff index_tail_iff split: if_splits)
     apply (metis dom_on_state_eq fst_conv snd_conv sum.disc(1) sum.sel(1) sup_ge1 valid_command_def valid_cylI')
    apply (metis dom_on_state_eq fst_conv snd_conv sum.disc(1) sum.sel(1) sup_commute sup_ge1 valid_command_def valid_cylI')
   apply (metis dom_on_state_eq fst_conv snd_conv sum.disc(1) sum.sel(1) sup_ge1 valid_command_def valid_cylI')
  apply (clarsimp simp: non_empty_def lift_op_def Let_unfold conv_def gluing_seq'_def)
  by (metis finiteS_glue first_None_iff' le_zero_eq lengthS_def lengthS_glue_le snd_conv sup_ge1 valid_cylI' valid_has_first)

  

lemma relational_join_exchange:
  "valid_command a \<Longrightarrow> valid_command b \<Longrightarrow> valid_command c \<Longrightarrow> valid_command d \<Longrightarrow> 
 lift_op gluing_seq' (relational_join a b) (relational_join c d) \<preceq> relational_join (lift_op gluing_seq' a c) (lift_op gluing_seq' b d)"
  apply (rule relational_join_is_meet)
      apply (rule monotone_gluing_seq)
           apply (clarsimp simp: valid_relational_join)+
  using relational_join_le apply blast
      apply (metis relational_join_le)
  apply (rule monotone_gluing_seq)
           apply (clarsimp simp: valid_relational_join)+
  using relational_join_le relational_join_commute 
      apply (metis relational_join_le)
using relational_join_le relational_join_commute 
   apply (metis relational_join_le)
  by (clarsimp simp: valid_relational_join valid_gluing_seq)+


lemma fst_relational_join[simp]: "fst (relational_join a b) = fst a \<union> fst b"
  by (clarsimp simp: relational_join_def)


lemma snd_relational_join[simp]: "valid_command a \<Longrightarrow> valid_command b \<Longrightarrow> snd (relational_join a b) = ((snd a \<rhd> fst a \<union> fst b) \<inter> (snd b \<rhd>  fst a \<union> fst b))"
  by (subst relational_join_is_inf; clarsimp)

lemma restrict_restrict_trace: "d \<subseteq> d' \<Longrightarrow> restrict_trace (d) (restrict_trace d' t) = restrict_trace d t"
  by (metis comp_apply restrict_comp)


lemma cyl_dom: "valid_command a \<Longrightarrow> (snd a \<rhd> fst a) = snd a"
  by (metis prod.exhaust_sel valid_command_cyl)

lemma valid_resI:"valid_command c \<Longrightarrow> fst c \<ge>  d \<Longrightarrow> valid_command (d, d \<lhd> snd c)"
  by (metis inf.absorb_iff2 restrict_def valid_valid_restrict)

lemma monotone_restrict: "valid_command (C, c) \<Longrightarrow> valid_command (D, d) \<Longrightarrow> a \<subseteq> C \<Longrightarrow> a \<subseteq> D \<Longrightarrow> 
  (C, c) \<preceq> (D, d) \<Longrightarrow> a \<lhd> c \<subseteq> a \<lhd> d"
  apply (clarsimp simp: refinement_order_def)
  by (metis image_eqI restrict_restrict_trace subset_imageD)

lemma valid_command_inf: "valid_command (C, c) \<Longrightarrow> valid_command (C, d) \<Longrightarrow> valid_command (C, c \<inter> d)"
  apply (intro valid_commandI same_domI) 
   apply (clarsimp)
   apply (simp add: sum.case_eq_if valid_dom_eq)
  apply (clarsimp simp: non_empty_def)
  by (metis first_None_iff' snd_conv valid_has_first)

lemma valid_singletonI: "(\<And>n s. index x n = Inl s \<Longrightarrow> dom s = c) \<Longrightarrow> lengthS x \<noteq> Some 0 \<Longrightarrow>  valid_command (c, {x})"
  apply (intro valid_commandI same_domI, clarsimp)
   apply (simp add: sum.case_eq_if)
  apply (clarsimp simp: non_empty_def)
  done

lemma refine_no_restrict: "valid_command a \<Longrightarrow> valid_command b \<Longrightarrow> fst a = fst b \<Longrightarrow> snd a \<subseteq> snd b \<Longrightarrow> a \<preceq> b"
  by (metis refine_refl refinement_order_def valid_restrict_eq)


lemma agree_intersection_restrict: "m |` (c \<inter> d) = m' |` (c \<inter> d) \<Longrightarrow> dom m = c \<Longrightarrow> dom m' = d \<Longrightarrow> (m ++ m') |` c = m"
  apply (intro ext; clarsimp simp: restrict_map_def)
  apply (safe; clarsimp?)
   apply (drule_tac x=x in fun_cong, clarsimp split: if_splits)
   apply (simp add: domI map_add_dom_app_simps(3))
   apply (drule_tac x=x in fun_cong, clarsimp split: if_splits)
  by fastforce


lemma relational_join_combination: 
 "valid_command a \<Longrightarrow> valid_command b \<Longrightarrow> 
 restrict (relational_join a b) (fst a)  =  relational_join a (restrict b (fst a \<inter> fst b))"
  apply (rule refine_asym)
     apply (meson refinement_order_def relational_join_le
                  valid_relational_join valid_valid_restrict)
    apply (simp add: valid_relational_join valid_valid_restrict)
   apply (rule relational_join_is_meet)
       apply (clarsimp simp: refinement_order_def)
  
  apply (metis in_cylD prod.exhaust_sel rev_image_eqI snd_restrict_simp sup.cobounded1 valid_restrict_eq)
       apply (clarsimp simp: refinement_order_def)
      apply (intro conjI)
       apply (blast)
      apply (clarsimp simp: Un_commute)
      apply (subst restrict_restrict_trace)
       apply (clarsimp)
      apply (smt (verit, ccfv_threshold) Int_subset_iff galois_inj image_comp image_eqI prod.collapse 
                  restrict_comp restrict_fst_iff snd_conv snd_restrict_simp
                   sup.absorb_iff1 sup.idem sup_commute sup_ge1 sup_ge2 valid_restrict_eq)
     apply (clarsimp)+
  
    apply (simp add: valid_valid_restrict)
   apply (simp add:  valid_relational_join valid_valid_restrict)
  apply (rule refine_no_restrict)
  apply (simp add: valid_relational_join valid_valid_restrict)
    apply (simp add: valid_relational_join valid_valid_restrict)
  apply (clarsimp)
  apply (blast)
  apply (simp only: snd_restrict_simp restrict_fst_iff fst_relational_join snd_relational_join)
  apply (subst snd_relational_join, clarsimp)
   apply (simp add: valid_valid_restrict)
  apply (simp only: snd_restrict_simp restrict_fst_iff fst_relational_join snd_relational_join)
   apply (subgoal_tac " fst a \<union> fst b \<inter> (fst a \<inter> fst b) = (fst a)", simp only:)
   apply (clarsimp simp: cyl_dom)
   apply (clarsimp simp: image_iff, clarsimp simp: Bex_def)
   apply (drule in_cylD[rotated 2])
     apply (erule valid_resI, blast, blast)
   apply (clarsimp)
   apply (rule_tac x="zip_trace (++) x c'" in exI)
   apply (intro conjI)
     apply (rule in_cylI[where c="fst a"], clarsimp, clarsimp)
  apply (rule valid_singletonI)
       apply (smt (verit, ccfv_SIG) dom_map_add index_zip_Inl_iff sum.disc(1) sum.sel(1) sup_commute valid_dom_eq)
      apply (clarsimp)
      apply (clarsimp simp: lengthS_zip split: if_splits)
        apply (metis lengthS_restrict option.distinct(1))
  apply (metis lengthS_restrict option.distinct(1))
      apply (metis min_def non_empty_def valid_command_def)
     apply (rule_tac x=x in exI)
     apply (clarsimp)
     apply (intro trace_eqI)
     apply (clarsimp simp: restrict_trace_def map_zip)
  apply (case_tac "index x n"; clarsimp)
      apply (clarsimp simp: index_zip_iff)
      apply (intro conjI impI; clarsimp?)
       apply (drule (1) map_trace_eqD, clarsimp)
  apply (erule agree_intersection_restrict)
        apply (metis sum.disc(1) sum.sel(1) valid_dom_eq)
  apply (metis sum.disc(1) sum.sel(1) valid_dom_eq)
  using map_trace_eqD apply fastforce
     apply (metis (mono_tags, lifting) index_zip_iff sum.disc(2) symbols.exhaust)
     apply (rule in_cylI[where c="fst b"], clarsimp, clarsimp)
  apply (rule valid_singletonI)
       apply (smt (verit, ccfv_SIG) dom_map_add index_zip_Inl_iff sum.disc(1) sum.sel(1) sup_commute valid_dom_eq)
      apply (clarsimp)
      apply (clarsimp simp: lengthS_zip split: if_splits)
        apply (metis lengthS_restrict option.distinct(1))
  apply (metis lengthS_restrict option.distinct(1))
      apply (metis min_def non_empty_def valid_command_def)
     apply (rule_tac x=c' in exI)
     apply (clarsimp)
     apply (intro trace_eqI)
     apply (clarsimp simp: restrict_trace_def map_zip)
  apply (case_tac "index c' n"; clarsimp)
      apply (clarsimp simp: index_zip_iff)
     apply (intro conjI impI; clarsimp?)
      apply (metis add_restrict_dom dom_on_state_eq sum.disc(1) sum.sel(1) valid_command_def)
  apply (metis lengthS_map_eq length_eq_isl_iff sum.disc(1))
    apply (metis (mono_tags, lifting) index_zip_iff sum.disc(2) symbols.exhaust)
  apply (intro trace_eqI)
     apply (clarsimp simp: restrict_trace_def map_zip)
  apply (case_tac "index x n"; clarsimp)
      apply (clarsimp simp: index_zip_iff)
    apply (intro conjI impI; clarsimp?)
  apply (smt (verit, ccfv_SIG) agree_intersection_restrict isl_def map_trace_eqD sum.sel(1) valid_dom_eq)
  apply (metis lengthS_map_eq length_eq_isl_iff sum.disc(1))
   apply (metis (mono_tags, lifting) index_zip_iff sum.disc(2) symbols.exhaust)
  apply (blast)
  done

lemma valid_command_prod[simp]: "valid_command a \<Longrightarrow> valid_command (fst a, snd a)"
  by (clarsimp)




lemma restrict_add_junk:"valid_command (a, S) \<Longrightarrow> t \<in> S \<Longrightarrow> restrict_trace a (map_trace (\<lambda>s. d ++ s ) t) = t"
  apply (clarsimp simp: restrict_trace_def map_trace_comp' comp_def)
  apply (rule trace_eqI)
  by (smt (verit, del_insts) add_restrict_dom fst_conv index_map_eqD 
          lengthS_map_eq length_eq_isl_iff snd_conv sum.collapse(1) 
          sum.expand symbols.exhaust valid_dom_eq)




lemma gluing_seq_combination: 
 "valid_command a \<Longrightarrow> valid_command b \<Longrightarrow> 
 restrict ( a \<Zsemi> b) (fst a) = (a \<Zsemi> (restrict b (fst a \<inter> fst b)))"
  apply (rule refine_asym)  
     apply (simp add: fst_lift_op valid_gluing_seq valid_valid_restrict)
    apply (simp add: fst_lift_op valid_gluing_seq valid_valid_restrict)
    apply (rule refine_no_restrict)
      apply (simp add: fst_lift_op valid_gluing_seq valid_valid_restrict)
  apply (simp add: fst_lift_op valid_gluing_seq valid_valid_restrict)
    apply (clarsimp)
    apply (simp add: fst_lift_op inf_left_commute)
   apply (clarsimp simp: lift_op_def Let_unfold)
   apply (clarsimp simp: conv_def)
   apply (subgoal_tac " fst a \<union> fst b \<inter> (fst a \<inter> fst b) = (fst a)", simp only:)
    apply (clarsimp simp: cyl_dom)
    apply (drule in_cylD[rotated 2])
      apply (erule valid_command_prod)
     apply (clarsimp)
    apply (clarsimp)
apply (drule in_cylD[rotated 2])
      apply (erule valid_command_prod)
     apply (clarsimp)
    apply (clarsimp)
    apply (rule_tac x="restrict_trace (fst a) x" in bexI)
     apply (clarsimp simp: Bex_def image_iff)
     apply (clarsimp simp: gluing_seq'_def)
     apply (clarsimp simp: restrict_seq match_restrict)
     apply (rule_tac x="restrict_trace (fst a) xb" in exI)
     apply (clarsimp)
     apply (intro conjI)
      apply (rule in_cylI)
         apply (erule valid_resI, clarsimp)
        apply (clarsimp)
       apply (rule valid_singletonI)
        apply (smt (verit, best) Un_Int_eq(1) dom_on_state_eq fst_conv image_eqI 
                insertCI restrict_def snd_conv sum.disc(1) sum.sel(1) sup_ge1 
                valid_command_def valid_valid_restrict)
       apply (metis lengthS_restrict non_empty_def valid_command_def)
      apply (clarsimp)
      apply (rule_tac x="restrict_trace (fst b) xb" in bexI)
  apply (simp add: restrict_restrict_trace)
      apply (clarsimp)
  using match_restrict apply blast
    apply (clarsimp)
   apply (blast)
  apply (rule refine_no_restrict)
   apply (simp add: fst_lift_op valid_gluing_seq valid_valid_restrict)
  apply (simp add: fst_lift_op valid_gluing_seq valid_valid_restrict)
   apply (clarsimp)
  apply (simp add: fst_lift_op inf_left_commute)
  apply (clarsimp simp: lift_op_def Let_unfold)
  apply (clarsimp simp: image_iff)
  apply (clarsimp simp: conv_def)
   apply (subgoal_tac " fst a \<union> fst b \<inter> (fst a \<inter> fst b) = (fst a)", simp only:)
   apply (clarsimp simp: image_iff cyl_dom)
   apply (drule in_cylD[rotated 2])
     apply (erule valid_resI)
     apply (clarsimp)
    apply (clarsimp)
   apply (clarsimp)
   apply (clarsimp simp: gluing_seq'_def restrict_seq match_restrict)
   apply (case_tac "lengthS xa = None", clarsimp simp: inf_left_glue_left)
    apply (rule_tac x="map_trace (\<lambda>s. junk (fst b) ++ s ) xa" in bexI)
     apply (subst restrict_add_junk)
       apply (erule valid_command_prod)
      apply (clarsimp)
     apply (clarsimp simp: inf_left_glue_left)
     apply (subgoal_tac "\<not>finiteS (map_trace ((++) (junk (fst b))) xa)") 
  apply (clarsimp simp: match_def)
      apply (metis all_not_in_conv galois_inj image_empty prod.exhaust_sel sup_ge2)
     apply (metis finite_map_iff lengthS_def option.distinct(1))
    apply (rule in_cylI)
       apply (erule valid_command_prod)
      apply (blast)
apply (rule valid_singletonI)
      apply (erule index_map_eqE; clarsimp)
      apply (simp add: valid_dom_eq)
     apply (clarsimp)
    apply (rule_tac x=xa in exI)
    apply (clarsimp)
  apply (meson restrict_add_junk valid_command_prod)
   apply (rule_tac x=" (map_trace (\<lambda>s. the (first c') ++ s ) xa)" in bexI)
    apply (rule_tac x="zip_trace (++) c' xb" in bexI)
     apply (intro conjI)
      apply (clarsimp simp: match_def)
      apply (clarsimp simp: first_def split: option.splits sum.splits)
       apply (intro conjI allI impI ; clarsimp?)
           apply (erule index_zipE)
          apply (intro ext; clarsimp simp: restrict_map_def map_add_def junk_def index_zip_iff split: if_splits option.splits)
         apply (simp add: index_zip_iff)
        apply (simp add: Inl_Inr_False index_zip_iff)
       apply (metis lengthS_restrict length_eq_isl_iff sum.disc(1) sum.disc(2))
      apply (intro conjI impI allI; clarsimp)
       apply (simp add: index_zip_iff)
  apply (simp add: index_zip_iff)
     apply (subgoal_tac "xa = restrict_trace (fst a) (map_trace ((++) (the (first c'))) xa)")
      apply (subgoal_tac "xb = restrict_trace (fst a) (zip_trace (++) c' xb)")
       apply (clarsimp)
      apply (rule trace_eqI; clarsimp simp: restrict_trace_def map_zip)
      apply (clarsimp simp: index_zip_iff, intro conjI impI allI; clarsimp?)
       apply (simp add: add_restrict_dom valid_dom_eq)
      apply (metis (mono_tags, lifting) lengthS_map_eq length_eq_isl_iff sum.collapse(2) symbols.exhaust)
     apply (metis prod.collapse restrict_add_junk)
    apply (rule in_cylI)
       apply (erule valid_command_prod, blast)
     apply (rule valid_singletonI)
      apply (smt (verit, ccfv_threshold) dom_map_add fst_conv index_zip_Inl_iff
        insertCI snd_conv sum.disc(1) sum.sel(1) valid_dom_eq)
     apply (metis (no_types, lifting) first_None_iff' lengthS_def 
           lengthS_zip match_empty_iff min_def option.exhaust_sel valid_has_first)
    apply (rule_tac x=c' in exI)
    apply (clarsimp)
      apply (rule trace_eqI; clarsimp simp: restrict_trace_def map_zip)
    apply (clarsimp simp: index_zip_iff, intro conjI impI allI; clarsimp?)
     apply (smt (verit) Collect_conv_if2 Int_commute agree_intersection_restrict fst_conv map_trace_eqD mem_Collect_eq snd_conv sum.collapse(1) sum.sel(1) valid_dom_eq)
    apply (metis (mono_tags, lifting) lengthS_map_eq length_eq_isl_iff sum.collapse(2) symbols.exhaust)
   apply (rule in_cylI)
      apply (erule valid_command_prod, blast)
    apply (rule valid_singletonI)
     apply (erule index_map_eqE)
     apply (clarsimp simp: first_def)
  apply (case_tac "index c' 0"; clarsimp)
      apply (metis sum.disc(1) sum.sel(1) valid_dom_eq)
     apply (metis first_def sum.case_eq_if sum.disc(2) valid_has_first)
    apply (metis first_None_iff' lengthS_map_eq valid_has_first)
   apply (rule_tac x=xa in exI)
   apply (meson restrict_add_junk valid_command_prod)
  apply (blast)
  done

definition "test a = (a, {t. lengthS t = Some 1 \<and> dom (projl (index t 0)) = a})"

lemma fst_test[simp]: "fst (test a) = a" by (clarsimp simp: test_def)

lemma valid_test: "valid_command (test c)"
  apply (rule valid_commandI)
   apply (clarsimp simp: same_dom_def test_def)
   apply (simp add: isl_iff sum.case_eq_if)
  by (clarsimp simp: non_empty_def test_def)

lemma test_cyl: "(snd (test c) \<rhd> c) = snd (test c)"
  by (metis cyl_dom fst_test valid_test)



lemma test_seq_neutral_r: "valid_command c \<Longrightarrow> (c \<Zsemi> test (fst c)) = c"
  apply (rule refine_asym)  
     apply (simp add: valid_gluing_seq valid_test)
    apply (simp add: valid_gluing_seq valid_test)
   apply (rule refine_no_restrict)

     apply (simp add: valid_gluing_seq valid_test)
     apply (simp add: valid_gluing_seq valid_test)
    apply (clarsimp simp: fst_lift_op)
   apply (clarsimp simp: lift_op_def Let_unfold cyl_dom test_cyl )
   apply (clarsimp simp: gluing_seq'_def conv_def test_def)
   apply (subst glue_l1_trace, clarsimp, clarsimp, clarsimp)
  apply (rule refine_no_restrict)

     apply (simp add: valid_gluing_seq valid_test)
     apply (simp add: valid_gluing_seq valid_test)
    apply (clarsimp simp: fst_lift_op)
   apply (clarsimp simp: lift_op_def Let_unfold cyl_dom test_cyl )
  apply (clarsimp simp: gluing_seq'_def conv_def test_def)
  apply (rule_tac x=x in bexI; clarsimp?)
  apply (case_tac "finiteS x")
  apply (rule_tac x="takeS 1 (constS (the (last x)))" in exI)
  apply (intro conjI)
     apply (simp add: lengthS_takeS_min')
    apply (clarsimp simp: index_take index_consts)
  apply (clarsimp simp: last_def)
  apply (metis (mono_tags, lifting) diff_Suc_less dom_on_state_eq first_def isl_iff lengthS_def option.sel sum.case_eq_if valid_command_def valid_has_first)
    apply (clarsimp)
    apply (subst glue_l1_trace)
      apply (clarsimp simp: lengthS_takeS_min')
     apply (clarsimp simp: match_def first_def index_take index_consts)
  apply (metis first_None_iff lengthS_constS lengthS_takeS_min' match_def match_empty_iff non_empty_def option.collapse valid_command_def)
    apply (clarsimp simp: last_def)

     apply (clarsimp simp: match_def first_def index_take index_consts)
   apply (metis first_None_iff lengthS_constS lengthS_takeS_min' match_def match_empty_iff non_empty_def option.collapse valid_command_def)
  apply (rule_tac x="takeS 1 (constS (junk (fst c)))" in exI)
  apply (clarsimp)
  apply (intro conjI)
      apply (clarsimp simp: lengthS_takeS_min')
    apply (clarsimp simp: index_take index_consts)
   apply (simp add: glue_def)
  apply (clarsimp simp: match_def)
  done


lemma test_seq_neutral_l: "valid_command c \<Longrightarrow> (test (fst c) \<Zsemi> c ) = c"
  apply (rule refine_asym)  
     apply (simp add: valid_gluing_seq valid_test)
    apply (simp add: valid_gluing_seq valid_test)
   apply (rule refine_no_restrict)

     apply (simp add: valid_gluing_seq valid_test)
     apply (simp add: valid_gluing_seq valid_test)
    apply (clarsimp simp: fst_lift_op)
   apply (clarsimp simp: lift_op_def Let_unfold cyl_dom test_cyl )
   apply (clarsimp simp: gluing_seq'_def conv_def test_def)
   apply (subst glue_l1_trace', clarsimp, clarsimp, clarsimp)
  apply (rule refine_no_restrict)

     apply (simp add: valid_gluing_seq valid_test)
     apply (simp add: valid_gluing_seq valid_test)
    apply (clarsimp simp: fst_lift_op)
   apply (clarsimp simp: lift_op_def Let_unfold cyl_dom test_cyl )
  apply (clarsimp simp: gluing_seq'_def conv_def test_def)
  apply (rule_tac x="takeS 1 (constS (the (first x)))" in exI)
  apply (intro conjI)
     apply (simp add: lengthS_takeS_min')
   apply (clarsimp simp: index_take index_consts)
   apply (metis first_def option.sel sum.case_eq_if valid_dom_eq valid_has_first)
  apply (rule_tac x=x in bexI)
   apply (intro conjI)
    apply (subst glue_l1_trace')
      apply (clarsimp)
      apply (simp add: lengthS_takeS_min')
     apply (clarsimp simp: match_def)
     apply (clarsimp simp: last_def lengthS_takeS_min' index_take index_consts)
     apply (simp add: valid_has_first)
    apply (clarsimp)
apply (clarsimp simp: match_def)
   apply (clarsimp simp: last_def lengthS_takeS_min' index_take index_consts)
     apply (simp add: valid_has_first)
  apply (clarsimp)
  done

lemma test_d_par: "test d \<preceq> relational_join (test d) (test d)"
  apply (rule refine_no_restrict)
  using valid_test apply blast
  using valid_relational_join valid_test apply blast
   apply (clarsimp)
  apply (clarsimp )
  by (metis refine_refl rel_join_inf_iff valid_test)

definition "univ_t a = (a, {t. lengthS t \<noteq> Some 0 \<and> (\<forall>n. case_sum dom (\<lambda>_. a) (index t n) = a)})"

lemma univ_t_dom[simp]: "fst (univ_t a) = a" by (clarsimp simp: univ_t_def)

lemma valid_univ_t: "valid_command (univ_t a)"
  apply (clarsimp simp: valid_command_def, intro conjI)
   apply (rule same_domI; clarsimp simp: univ_t_def)
   apply (smt (verit) fst_conv sum.case_eq_if univ_t_def)
  by (clarsimp simp: non_empty_def univ_t_def)

lemma univ_t_cyl[simp]:"(snd (univ_t d) \<rhd> d) = (snd (univ_t d))"
  by (metis cyl_dom univ_t_dom valid_univ_t)

lemma rel_join_neutral_l: "valid_command c \<Longrightarrow> (relational_join (univ_t (fst c)) c ) = c"
  apply (rule refine_asym)  
  using valid_relational_join valid_univ_t apply blast
    apply (clarsimp)
   apply (rule refine_no_restrict)
  using valid_relational_join valid_univ_t apply blast
     apply (clarsimp)
    apply (clarsimp)
   apply (clarsimp)
   apply (subst (asm) snd_relational_join)
     apply (simp add: valid_univ_t)
  apply (clarsimp)
   apply (simp add: cyl_dom)
   apply (rule refine_no_restrict)
  using valid_relational_join valid_univ_t apply blast
  using valid_relational_join valid_univ_t apply blast
   apply (clarsimp)
   apply (subst  snd_relational_join)
     apply (simp add: valid_univ_t)
  apply (clarsimp)
  apply (clarsimp simp: cyl_dom)
  apply (clarsimp simp: univ_t_def)
  apply (intro conjI)
   apply (metis first_None_iff' valid_has_first)
  apply (clarsimp)
  by (simp add: sum.case_eq_if valid_dom_eq)

lemma univ_t_seq_ref: "((univ_t d) \<Zsemi> (univ_t d))  \<preceq> (univ_t d)"
   apply (rule refine_no_restrict)
     apply (simp add: valid_gluing_seq valid_univ_t)
  apply (simp add: valid_gluing_seq valid_univ_t)
   apply (clarsimp)
   apply (simp add: fst_lift_op)
  apply (clarsimp simp: lift_op_def conv_def gluing_seq'_def)
  apply (clarsimp simp: univ_t_def)
  apply (intro conjI)
   apply (metis finiteS_glue le_zero_eq lengthS_def lengthS_glue_le)
  apply (clarsimp)
  by (metis finite_index_iff index_tail_iff infinite_index_iff)

lemma univ_t_seq_ref': "(univ_t d) \<preceq> ((univ_t d) \<Zsemi> (univ_t d))"
  by (metis fst_test monotone_gluing_seq rel_join_inf_iff rel_join_neutral_l 
  test_seq_neutral_r univ_t_dom valid_test valid_univ_t)





end

