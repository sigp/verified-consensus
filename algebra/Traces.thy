theory Traces
imports Main CRA_Obs CRA_Atomic  "~~/src/HOL/Library/Monad_Syntax" "rg-algebra/AbstractAtomicTest/Constrained_Atomic_Commands"

begin

find_consts "'a + 'b \<Rightarrow> bool"

term sum.isl 

definition "traceDom \<equiv> {(f). \<forall> (i :: nat) j. j \<le> i \<longrightarrow> \<not>(sum.isl (f j)) \<longrightarrow> f i = f j}"

typedef ('state, 'sym) trace = "traceDom :: (nat \<Rightarrow> ('state + 'sym)) set"
  apply (rule_tac x="\<lambda>_. Inr undefined" in exI)
  apply (clarsimp simp: traceDom_def)
  done

setup_lifting type_definition_trace     


lift_definition index :: " ('state, 'sym) trace \<Rightarrow> nat \<Rightarrow>  'state + 'sym" is "\<lambda>f n. f n" done

primrec iterate where
  "iterate x f 0       = x" |
  "iterate x f (Suc n) = f (iterate x f n)" 


definition "finiteS f \<equiv> \<exists>n. \<not>isl (index f n)"

lift_definition pred :: "((nat \<Rightarrow>  'state + 'sym) \<Rightarrow> 'b) \<Rightarrow> ( ('state, 'sym) trace \<Rightarrow> 'b)" is "\<lambda>P f. P f"
  done

definition lengthS where "lengthS \<equiv> \<lambda>f. if finiteS f then Some (LEAST n. \<not>isl (index f n)) else None"

lift_definition liftF :: "(nat \<Rightarrow>  'state + 'sym) \<Rightarrow>  ('state, 'sym) trace " is
 "\<lambda>f. if f \<in> traceDom then f else (\<lambda>_. Inr undefined)" 
  by (clarsimp simp: traceDom_def)

lemma traceDom_antimono: "g \<in> traceDom \<Longrightarrow> antimono P \<Longrightarrow> (\<And>n. P n \<longrightarrow> isl (f n)) \<Longrightarrow> (\<lambda>n. if P n then f n else g n ) \<in> traceDom"
  apply ( clarsimp simp: traceDom_def split: if_splits)
  by (metis monotoneD)

lemma traceDom_antimono': "\<not>(\<lambda>n. if P n then f n else g n ) \<in> traceDom \<Longrightarrow>  antimono P \<Longrightarrow> (\<And>n. P n \<Longrightarrow> isl (f n)) \<Longrightarrow> \<not>g \<in> traceDom "
  apply ( clarsimp simp: traceDom_def split: if_splits)
  by (metis monotoneD)

primrec coerce :: "'a + 'b \<Rightarrow> 'a + 'c"
  where
  "coerce (Inl a) = Inl a" |
  "coerce (Inr b) = Inr undefined"


definition "tail s = liftF (\<lambda>n. index s (n + 1))"

lemma tail_traceDom[simp]: "(\<lambda>n. index s (n + 1)) \<in> traceDom"
  by (clarsimp simp: traceDom_def, transfer, clarsimp simp: traceDom_def)


lemma lengthS_le: "(\<And>n.  isl (index s n) \<Longrightarrow> isl (index s' n)) ==>  finiteS s' \<Longrightarrow>   the ( lengthS s) \<le> the (lengthS s')"
  apply (transfer)
  apply (clarsimp simp: lengthS_def )
  apply (intro conjI impI; clarsimp?)
   apply (rule Least_le)
   apply (metis LeastI finiteS_def)
  by (simp add: finiteS_def)


definition "map_trace f t \<equiv> liftF (\<lambda>n. case_sum (Inl o f) (Inr) (index t n))"

lemma map_traceDom[simp]: "(\<lambda>n. case_sum (Inl o f o projl) (Inr) (index t n)) \<in> traceDom"
  apply (clarsimp simp: traceDom_def split: sum.splits)
  apply (intro conjI; clarsimp)
   apply (transfer, clarsimp simp: traceDom_def)
  apply (transfer, clarsimp simp: traceDom_def)
  done

lemma trace_eqI: "(\<And>n. index c n = index d n) \<Longrightarrow> c = d" 
  apply (transfer)
  apply (intro ext)
  apply (clarsimp)
  done

definition appendS :: " ('state, 'syma) trace \<Rightarrow>  ('state, 'sym) trace \<Rightarrow>  ('state, 'sym) trace"
  where "appendS s s' \<equiv> 
   if finiteS s then
       liftF (\<lambda>n. if (n < the ( lengthS s)) then coerce (index s n) else index s' (n - (the (lengthS s))))
                        else
       liftF (coerce o index s)"




definition first :: "('state, 'sym) trace \<Rightarrow> ('state) option"  
  where "first s \<equiv> (case (index s 0) of (Inl s) \<Rightarrow> Some s | (Inr s) \<Rightarrow> None )"


definition last :: "('state, 'sym) trace \<Rightarrow> ('state) option"  
  where "last s \<equiv> if finiteS s then (case (index s (the (lengthS s) - 1)) of 
                                 (Inl s) \<Rightarrow> Some s | (Inr s) \<Rightarrow> None ) else None"

definition "emptyS \<equiv> liftF (\<lambda>n. Inr undefined)"


definition glue :: " ('state, 'sym) trace \<Rightarrow> ('state, 'sym) trace \<Rightarrow>('state, 'sym) trace "
  where  "glue t t' = (if finiteS t then 
                            liftF (\<lambda>n. if n < the (lengthS t) then index t n else
                                  (index (tail t') (n - (the (lengthS t))))) else t)" 

notation glue (infixr \<open>-o\<close> 50)

definition "match t t' \<equiv> if finiteS t then (last t = first t') else True"

primrec to_list_rec :: "nat \<Rightarrow> ('state, 'sym) trace \<Rightarrow> 'state list"
  where
  "to_list_rec (Suc n) t = projl (index t n) # (to_list_rec n t)" |
  "to_list_rec 0 t = []" 

definition to_list :: "('state, 'sym) trace \<Rightarrow> 'state list option"
  where "to_list t = (if finiteS t then (Some (to_list_rec (the (lengthS t)) t)) else None)"

definition from_list :: "'state list \<Rightarrow> ('state, 'sym) trace"
  where "from_list xs = liftF (\<lambda>n. if n \<le> length xs then Inl (xs ! n) else Inr undefined)  "

definition remdups  :: "('state, 'sym) trace \<Rightarrow> ('state, 'sym) trace"
  where "remdups s \<equiv> case (to_list s) of Some xs \<Rightarrow> from_list (remdups_adj xs) | _ \<Rightarrow> undefined"


lemma map_traceDom'[simp]: "t \<in> traceDom \<Longrightarrow> 
 (\<lambda>n. case t n of Inl x \<Rightarrow> (Inl \<circ> f) x | Inr x \<Rightarrow> Inr x) \<in> traceDom" 
  apply (clarsimp simp: traceDom_def)
  by (metis comp_apply old.sum.simps(5) sum.collapse(1) sum.disc(1))

lemma index_map_sum: "index (map_trace f t) n = map_sum f id (index t n)"
  apply (clarsimp simp: map_trace_def, transfer, clarsimp)
  by (clarsimp simp: map_sum_def split: sum.splits)

lemma map_trace_comp: "map_trace f o map_trace g = map_trace (f o g)"
  apply (intro ext trace_eqI)
  apply (clarsimp simp: index_map_sum)
  by (case_tac "index x n"; clarsimp)

lemma index_map_eqD: "index (map_trace f t) n = Inl s \<Longrightarrow> s = f (projl (index t n))"
  apply (clarsimp simp: index_map_sum)
  by (clarsimp simp: map_sum_def split: sum.splits)

lemma index_map_eqE: "index (map_trace f t) n = Inl s \<Longrightarrow> (isl (index t n) \<Longrightarrow> P (f (projl (index t n)))) \<Longrightarrow> P s"
  apply (clarsimp simp: index_map_sum)
  by (clarsimp simp: map_sum_def split: sum.splits)

lemma lengthS_map_eq[simp]: "lengthS (map_trace f s) = lengthS s"
  apply (clarsimp simp: lengthS_def )
  apply (safe)
    apply (simp add: index_map_sum isl_map_sum)
   apply (clarsimp simp: finiteS_def)
    apply (simp add: index_map_sum isl_map_sum)
   apply (fastforce)
 apply (clarsimp simp: finiteS_def)
  apply (simp add: index_map_sum isl_map_sum)
  done

fun comb_sum where
 "comb_sum f (Inl x) (Inl y) = Inl (f x y)" |
 "comb_sum f (Inr x) y = Inr x" | 
 "comb_sum f x (Inr y) = Inr y"



primrec foldrS :: "('a, 'b) trace \<Rightarrow> ('c \<Rightarrow> 'a + 'b \<Rightarrow> 'c + 'b) \<Rightarrow> 'c \<Rightarrow> nat \<Rightarrow> 'c + 'b" where
  "foldrS t f x 0       = (case (index t 0) of (Inl v) \<Rightarrow> f x (Inl v) | (Inr v) \<Rightarrow> Inr v)" |
  "foldrS t f x (Suc n) = (case (foldrS t f x n) of (Inl v) \<Rightarrow> f v (index t (Suc n)) | (Inr v) \<Rightarrow> Inr v) " 

definition "iterateF f x = liftF (iterate x f)"

definition "foldrF f t x = liftF (foldrS t f x)"

definition "pair_traces a b = liftF (\<lambda>n. Inl (index a n, index b n))"

definition "zip_trace f a b =  foldrF (\<lambda>_. case_prod (comb_sum f) o projl) (pair_traces a b) undefined " 

definition "zip_trace' f a b =  foldrF (\<lambda>_. case_prod f o projl) (pair_traces a b) undefined " 


lemma zip_tracedom[simp]: "s \<in> traceDom \<Longrightarrow> s' \<in> traceDom \<Longrightarrow> 
 (\<lambda>n. if isl (s n) \<and> isl (s' n) then Inl (f (projl (s n)) (projl (s' n))) else Inr Term) \<in> traceDom" 
  apply (clarsimp simp: traceDom_def)
  by metis

lemma comb_sum_isl[simp]: "comb_sum f x y = Inl a \<Longrightarrow> isl x \<and> isl y"
  by (metis Inl_not_Inr comb_sum.elims isl_def)

lemma foldr_traceDom[simp]: "foldrS t f x \<in> traceDom"
  apply (unfold traceDom_def, intro CollectI)
  apply (rule allI)
  apply (induct_tac i; clarsimp)
  apply (clarsimp split: sum.splits, safe)
   apply (metis foldrS.simps(2) isl_def le_Suc_eq old.sum.simps(5))
  by (clarsimp simp: le_Suc_eq, erule disjE; clarsimp)

lemma pair_trace_valid[simp]: "(\<lambda>n. Inl (index a n, index b n)) \<in> traceDom" 
  by (clarsimp simp: traceDom_def)

lemma index_foldrF_suc[simp]: "index (foldrF f t x) (Suc n) = (case (foldrS t f x n) of (Inl v) \<Rightarrow> f v (index t (Suc n)) | (Inr v) \<Rightarrow> Inr v)"
  by (clarsimp simp: foldrF_def, transfer, clarsimp)

lemma index_liftF[simp]: "f \<in> traceDom \<Longrightarrow> index (liftF f) n = f n "
  by (transfer, clarsimp)

lemma index_pair[simp]: "index (pair_traces s s') n = Inl ((index s n),  (index s' n))" 
  by (clarsimp simp: pair_traces_def)

lemma index_foldrF_zero[simp]: "index (foldrF f t x) (0) = (case (index t 0) of (Inl v) \<Rightarrow> f x (Inl v) | (Inr v) \<Rightarrow> Inr v)"
  by (clarsimp simp: foldrF_def)

lemma comb_sum_Inl_iff: "comb_sum f x y = Inl z \<longleftrightarrow> (\<exists>v v'. x = Inl v \<and> y = Inl v' \<and> f v v' = z)"
  apply (safe; clarsimp)
  by (case_tac x; case_tac y; clarsimp?)

lemma index_zipE: "index (zip_trace f s s') n = Inl x \<Longrightarrow>
      (isl (index s n) \<Longrightarrow> isl (index s' n) \<Longrightarrow> P (f (projl (index s n)) (projl (index s' n)))) \<Longrightarrow>
     P x "
  apply (clarsimp simp: zip_trace_def  comp_def)
  apply (case_tac n; clarsimp?)
   apply (metis comb_sum.simps(1) comb_sum_isl sum.collapse(1) sum.sel(1))
  apply (clarsimp split: sum.splits)
  by (clarsimp simp: comb_sum_Inl_iff)

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


lemma isl_monotone[intro]: "isl (index b j) \<Longrightarrow> j \<ge> i \<Longrightarrow> isl (index b i)"
  apply (transfer)
  apply (clarsimp simp: traceDom_def)
  by fastforce

lemma isr_antitone[intro]: "(index c j) = Inr v \<Longrightarrow> j \<le> i \<Longrightarrow>  (index c i) = Inr v"
  apply (transfer)
  by (clarsimp simp: traceDom_def)

lemma isr_antitone'[intro]: "\<not>isl (index c j) \<Longrightarrow> j \<le> i \<Longrightarrow>  \<not>isl (index c i)"
  apply (transfer)
  by (clarsimp simp: traceDom_def)


lemma comb_sum_l[simp]:  "\<not>isl c \<Longrightarrow> isl c' \<Longrightarrow> comb_sum f c c' = c"
  by (metis comb_sum.simps(2) sum.collapse(2))


lemma comb_sum_r[elim]:  "c' = Inr x \<Longrightarrow> isl c  \<Longrightarrow> P(Inr x) \<Longrightarrow>  P (comb_sum f c c')"
  by (metis comb_sum.simps(3) isl_def sumE)


lemma comb_sum_r'[elim]:  "\<not>isl c' \<Longrightarrow> isl c  \<Longrightarrow> P(c') \<Longrightarrow>  P (comb_sum f c c')"
  by (metis comb_sum.simps(3) isl_def sumE)

definition "retype_inr = Inr o projr"

lemma comb_sum_eqI[intro]:  "\<not>isl c' \<Longrightarrow> isl c  \<Longrightarrow> \<not>isl x \<Longrightarrow> (c') = retype_inr x \<Longrightarrow>   (comb_sum (f :: 'a \<Rightarrow> 'b \<Rightarrow> 'c) c c') =  x"
  apply (case_tac "c'"; case_tac "c" ; clarsimp)
  by (clarsimp simp: retype_inr_def)+


lemma index_zip_iff: "index (zip_trace f a b) n =
   (comb_sum f (index a n) (index b n))"
  apply (induct n; clarsimp?)
   apply (clarsimp simp: zip_trace_def)
  apply (clarsimp simp: zip_trace_def)
  apply (case_tac "index a n"; case_tac "index b n"; clarsimp split: sum.splits)
  oops


lemma isl_comb_sum_iff: "isl (comb_sum f x y) = (\<exists>v v' z. x = Inl v \<and> y = Inl v' \<and> f v v' = z \<and> comb_sum f x y = Inl z)"
  apply (clarsimp simp: isl_def)
  by (safe; clarsimp simp: comb_sum_Inl_iff)

lemma isl_comb_sum_isl: "isl (comb_sum f x y) \<longleftrightarrow> isl x \<and> isl y"
  apply (clarsimp simp: isl_comb_sum_iff, safe; fastforce?)
  by (clarsimp simp: isl_def)


lemma isl_case_simp[simp]: "isl x \<Longrightarrow> (case x of Inl l \<Rightarrow> f l x | Inr r \<Rightarrow> g r x) = (f (projl x)  x)"
  by (case_tac x; clarsimp)

lemma isl_suc: "isl (index (zip_trace f s s') (Suc n)) \<Longrightarrow> isl (index (zip_trace f s s') n)" 
  apply (clarsimp simp: zip_trace_def split: sum.splits)
  by (case_tac n; clarsimp)

lemma index_zip_traces_cases: "(\<not>isl (index (zip_trace f s s') n) \<Longrightarrow> P (index (zip_trace f s s') n)) \<Longrightarrow>
       (isl (index (zip_trace f s s') n) \<Longrightarrow> P (comb_sum f (index s (Suc n)) (index s' (Suc n)))) \<Longrightarrow> 
        P ( index (zip_trace f s s') (Suc n))"
  apply (case_tac "isl (index (zip_trace f s s') n)")
   apply (clarsimp)
   apply (subst zip_trace_def, clarsimp split: sum.splits)
   apply (simp add: foldrF_def zip_trace_def)
  apply (clarsimp)
  apply (clarsimp simp: zip_trace_def, clarsimp split: sum.splits)
  apply (safe; clarsimp?)
   apply (simp add: foldrF_def)+
  done

lemma index_zip_traces_zero: "  
        index (zip_trace f s s') (0) = comb_sum f (index s 0) (index s' 0)"
  by (subst zip_trace_def, clarsimp)

lemma isl_index_zip: "isl (index (zip_trace f s s') n) \<longleftrightarrow> isl (index s n) \<and> isl (index s' n)"
  apply (induct n; clarsimp?)
   apply (clarsimp simp: isl_def zip_trace_def comb_sum_Inl_iff, blast)
  apply (intro iffI conjI)
  apply (clarsimp simp: isl_suc)
    apply (clarsimp simp: zip_trace_def isl_comb_sum_isl split: sum.splits )
  apply (clarsimp simp: isl_suc)
   apply (clarsimp simp: zip_trace_def isl_comb_sum_isl split: sum.splits )
  apply (rule index_zip_traces_cases, clarsimp)
  using Suc_n_not_le_n nat_le_linear apply blast
  by (clarsimp simp: isl_comb_sum_isl)
 

lemma finite_zip_iff[simp]: "finiteS (zip_trace f s s') \<longleftrightarrow> finiteS s \<or> finiteS s'" 
  apply (safe; clarsimp simp: finiteS_def isl_index_zip)
   apply blast+
  done

lemma lengthS_zip: "lengthS (zip_trace f s s') = 
   (if lengthS s = None then lengthS s' else if (lengthS s' = None) then lengthS s else Some (min (the (lengthS s)) (the (lengthS s'))))"
  apply (rule lengthS_eqI)
   apply (clarsimp simp: isl_index_zip split: if_splits )
   apply (metis finiteS_def lengthS_def option.distinct(1))
  apply (clarsimp simp: isl_index_zip split: if_splits )
    apply (metis LeastI finiteS_def isr_antitone' le_eq_less_or_eq lengthS_def not_less_Least not_less_iff_gr_or_eq option.distinct(1) option.sel)
  apply (metis LeastI finiteS_def isr_antitone' le_eq_less_or_eq lengthS_def not_less_Least not_less_iff_gr_or_eq option.distinct(1) option.sel)
  apply (metis LeastI finiteS_def isr_antitone' le_eq_less_or_eq lengthS_def not_less_Least not_less_iff_gr_or_eq option.distinct(1) option.sel)
  done

lemma id_imageI: "(\<And>x. x \<in> S \<Longrightarrow> f x = x) \<Longrightarrow> f ` S = S"
  apply (clarsimp)
  done

lemma isl_comb_sum_all: "isl (comb_sum f x y) \<longleftrightarrow> isl (comb_sum g x y)"
  by (simp add: isl_comb_sum_isl)

lemma isr_comb_sum_left: "\<not> isl (comb_sum f t t') \<Longrightarrow> \<not>isl t \<Longrightarrow> comb_sum f t t' = t "
  by (cases t; clarsimp)

lemma isr_comb_sum_right: "\<not> isl (comb_sum f t t') \<Longrightarrow> isl t \<Longrightarrow> comb_sum f t t' = t' "
  by (cases t'; cases t; clarsimp)

lemma map_zip: "map_trace g (zip_trace f t t') = zip_trace (\<lambda>x y. g (f x y)) t t'"
  apply (intro trace_eqI)
  apply (clarsimp simp: index_map_sum)
  apply (induct_tac n; clarsimp)
  apply (clarsimp simp: index_zip_traces_zero)
   apply (rule sum.expand; clarsimp?)
     apply (clarsimp simp: isl_map_sum isl_comb_sum_all)
    apply (clarsimp simp: isl_map_sum isl_comb_sum_all)

    apply (metis (no_types, lifting) isl_comb_sum_iff map_sum.simps(1) sum.sel(1))
   apply (clarsimp simp: isl_map_sum isl_comb_sum_all map_sum_sel(2))
  apply (case_tac \<open>index t 0\<close> ; clarsimp simp: isr_comb_sum_left isr_comb_sum_right )
   apply (metis comb_sum.simps(3) isl_comb_sum_isl sum.collapse(2) sum.disc(1) sum.sel(2))
  apply (rule index_zip_traces_cases)
   apply (smt (verit) Suc_n_not_le_n isl_map_sum isr_antitone nat_le_linear sum.collapse(2))
  apply (rule index_zip_traces_cases)
   apply (metis isl_map_sum)
  apply (case_tac "index t (Suc na)"; clarsimp) 
  by (case_tac "index t' (Suc na)"; clarsimp) 

definition "map_index_trace f t \<equiv> liftF (\<lambda>n. case index t n of Inl x \<Rightarrow> (Inl \<circ> f n) x | Inr x \<Rightarrow> Inr x)"

lemma [simp]: "s \<in> traceDom \<Longrightarrow>
      (\<lambda>n. case s n of Inl x \<Rightarrow> (Inl \<circ> f n) x | Inr x \<Rightarrow> Inr x) \<in> traceDom" 
  apply (clarsimp simp: traceDom_def)
  by (metis Inl_Inr_False comp_apply sum.case_eq_if sum.collapse(2))

lemma [simp]: "
      (\<lambda>n. case index s n of Inl x \<Rightarrow> (Inl \<circ> f n) x | Inr x \<Rightarrow> Inr x) \<in> traceDom" 
  apply (clarsimp simp: traceDom_def, transfer, clarsimp)
  by (metis (mono_tags, lifting) Inl_Inr_False comp_apply
        mem_Collect_eq sum.case_eq_if sum.collapse(2) traceDom_def)

lemma index_map_indexE: "index (map_index_trace f s) n = Inl x \<Longrightarrow>
      (isl (index s n) \<Longrightarrow> P (f n (projl (index s n)))) \<Longrightarrow>
     P x "
  apply (clarsimp simp: map_index_trace_def, transfer)
  by (clarsimp split: if_splits sum.splits)

lemma index_map_index_iff: "index (map_index_trace f t) n = map_sum (f n) id (index t n)"
  by (case_tac "(index t n)"; clarsimp simp: map_index_trace_def index_liftF)

lemma lengthS_map_index[simp]: "lengthS (map_index_trace f s) = lengthS s" 
  apply (rule lengthS_eqI; clarsimp simp: index_map_index_iff split: sum.splits)
   apply (metis finiteS_def isl_map_sum lengthS_def option.distinct(1))
  apply (safe ;  clarsimp?)
   apply (metis isl_map_sum lengthS_def not_less_Least option.distinct(1) option.sel)
  by (metis (no_types, lifting) LeastI finiteS_def index_map_sum 
  isl_monotone leI lengthS_def lengthS_map_eq option.distinct(1) option.sel)


lemma map_map_index: "map_trace f (map_index_trace g t) = (map_index_trace (\<lambda>n x. f (g n x)) t) "
  apply (rule trace_eqI)
  by (clarsimp simp: index_map_index_iff index_map_sum, case_tac "(index t n)" ; clarsimp) 

  

lemma finite_map_iff[simp]:"finiteS (map_trace f t) = finiteS t"
  by (metis lengthS_def lengthS_map_eq option.simps(3))

lemma finiteS_lengthSE:
"finiteS x \<Longrightarrow> (\<And>n. \<not>isl (index x n) \<Longrightarrow> \<forall>n'\<ge>n. \<not>isl (index x n') \<Longrightarrow> \<forall>n'<n. isl (index x n') \<Longrightarrow>  P n) \<Longrightarrow> 
      P (the (lengthS x))"
  apply (clarsimp simp: finiteS_def lengthS_def, transfer)
  apply (atomize)
  apply (erule_tac x="LEAST n. \<not> isl (x n)" in allE)
  apply (erule impE)
  apply (clarsimp)
   apply (metis (mono_tags, lifting) LeastI mem_Collect_eq traceDom_def)
  apply (drule mp)
   apply (clarsimp)
  using not_less_Least apply blast
  apply (clarsimp)
  done


lemma index_tail_iff: "index (tail y) n = index y (Suc n)"
  apply (clarsimp simp: tail_def)
  apply (transfer)
  apply (clarsimp simp: traceDom_def)
  done

lemma index_eq_finished: "m \<ge> i \<Longrightarrow> \<not>isl (index t i) \<Longrightarrow> n \<ge> m \<Longrightarrow> index t n  = index t m"
  apply (transfer)
  apply (clarsimp simp: traceDom_def)
  done


lemma finite_index_iff: "finiteS x \<Longrightarrow> index (x -o y) n = (if n < the (lengthS x) then (index x n) else (index (tail y) (n - (the (lengthS x))) ))"
  apply (clarsimp simp:  glue_def)
  apply (erule finiteS_lengthSE)
  apply (clarsimp)
  apply (intro conjI impI)
   apply (transfer; clarsimp)
   apply (erule contrapos_np)
   apply (clarsimp simp: traceDom_def tail_def)
   apply (transfer, clarsimp)
   apply (clarsimp simp: traceDom_def tail_def)
  apply (subst index_liftF)
   apply (clarsimp simp: traceDom_def)
   apply (clarsimp simp: index_tail_iff)
   defer
  apply (clarsimp)
  by (metis Suc_le_mono diff_le_mono index_eq_finished leI verit_comp_simplify1(1))  

lemma infinite_index_iff: "\<not>finiteS x \<Longrightarrow> index (x -o y) n = (index x n)"
  by (clarsimp simp: glue_def)
  
lemma map_seq: "(map_trace f (x -o y)) = (map_trace f x -o map_trace f y)"
  apply (rule trace_eqI)
  apply (case_tac "finiteS x")
  apply (subgoal_tac "finiteS (map_trace f x)")
    apply (clarsimp simp: index_map_sum finite_index_iff split: sum.splits)
    apply (case_tac \<open>(index (tail y) (n - the (lengthS x)))\<close>; clarsimp simp: index_tail_iff index_map_sum)
   apply (simp add: finiteS_def index_map_sum isl_map_sum)
  by (clarsimp simp: infinite_index_iff index_map_sum)

definition "constS s = liftF (\<lambda>n. Inl s)"

lemma lengthS_constS[simp]: "lengthS (constS s) = None" 
  apply (clarsimp simp: constS_def lengthS_def finiteS_def)
  by (simp add: index_liftF traceDom_def)

lemma index_constS:"index (constS s) n = Inl s"
  by (clarsimp simp: constS_def index_liftF traceDom_def)

lemma isl_Suc[dest]: "index t (Suc n) = Inl a \<Longrightarrow> isl (index t n)"
  by (metis isr_antitone' le_add2 plus_1_eq_Suc sum.disc(1))

lemma index_zip_Inl_iff: "index (zip_trace f t t') n = Inl x \<longleftrightarrow> (\<exists>a b. index t n = Inl a \<and> index t' n = Inl b \<and> x = f a b)"
  apply (safe)
   apply (erule index_zipE)
   apply (clarsimp simp: isl_def)
  apply (induct n; clarsimp?)
   apply (clarsimp simp: index_zip_traces_zero)
  apply (rule index_zip_traces_cases; clarsimp?)
  by (clarsimp simp: isl_index_zip isl_Suc)
  

lemma zip_map_r: "zip_trace f t (map_trace g t') = zip_trace (\<lambda>x y. f x (g y)) t t'" 
  apply (rule trace_eqI)
  find_theorems index map_trace
  apply (induct_tac n; clarsimp simp: index_zip_traces_zero index_map_sum)
   apply (case_tac "index t 0"; case_tac "index t' 0"; clarsimp?)
  apply (rule index_zip_traces_cases; clarsimp?)
   apply (metis isr_antitone le_add2 plus_1_eq_Suc sum.collapse(2))
  apply (rule index_zip_traces_cases; clarsimp?)
  apply (clarsimp simp: index_zip_traces_zero index_map_sum isl_index_zip)
  by (case_tac "index t (Suc na)"; case_tac "index t' (Suc na)"; clarsimp?)


definition "repeatN n s s' = liftF (\<lambda>m. if m < n then Inl s else Inr s')"


lemma first_is_some_iff_index: "first (t -o t') = Some x \<longleftrightarrow> index (t -o t') 0 = Inl x"
  apply (clarsimp simp: first_def split: sum.splits)
  done

lemma first_is_some_iff_index': "Some x = first (t -o t')  \<longleftrightarrow> index (t -o t') 0 = Inl x" 
  using first_is_some_iff_index by force

lemma first_None_iff: "first x = None \<longleftrightarrow> lengthS x = Some 0" 
  apply (clarsimp simp: first_def split: sum.splits, safe; clarsimp?)
   apply (metis LeastI finiteS_def is_none_code(2) is_none_simps(1) lengthS_def option.inject sum.disc(1))
  by (metis Least_eq_0 finiteS_def lengthS_def sum.disc(2))


lemma first_None_iff': "None = first x  \<longleftrightarrow> lengthS x = Some 0" 
apply (clarsimp simp: first_def split: sum.splits, safe; clarsimp?)
   apply (metis LeastI finiteS_def is_none_code(2) is_none_simps(1) lengthS_def option.inject sum.disc(1))
  by (metis Least_eq_0 finiteS_def lengthS_def sum.disc(2))


lemma [simp]: "finiteS t \<Longrightarrow> 
 (\<lambda>n. if n < the (lengthS t) then index t n else index (tail t') (n - the (lengthS t))) \<in> traceDom"
  by (smt (verit, del_insts) dual_order.refl finite_index_iff
                             index_eq_finished mem_Collect_eq traceDom_def)

lemma option_bind_None_iff: "Option.bind v f = None \<longleftrightarrow> (v = None \<or> (\<exists>c.  v = Some c \<and> f c = None))"
  by (case_tac v; clarsimp)

lemma option_bind_Some_iff: "Option.bind v f = Some c \<longleftrightarrow> (\<exists>a. v = Some a \<and> f a = Some c)"
  by (case_tac v; clarsimp)

lemma isl_iff: "lengthS t = Some n \<Longrightarrow> isl (index t m) \<longleftrightarrow> m < n"
  apply (clarsimp simp: lengthS_def split: if_splits)
  by (metis LeastI finiteS_def index_eq_finished leI not_less_Least)

lemma lengthS_iff: "lengthS t' \<noteq> Some 0 \<Longrightarrow>  lengthS (t -o t') = (Option.bind (lengthS t) (\<lambda>s. Option.bind (lengthS t') (\<lambda>s'. Some (s + s' - 1))))" 
  apply (rule lengthS_eqI)
   apply (clarsimp)
   apply (clarsimp simp: option_bind_None_iff)
   apply (elim disjE)
    apply (subgoal_tac "\<not> finiteS (t)")
     apply (clarsimp simp: infinite_index_iff)
  using finiteS_def apply blast
    apply (clarsimp simp: lengthS_def)
   apply (clarsimp)
   apply (subgoal_tac "finiteS (t)")
    apply (clarsimp simp: finite_index_iff)
    apply (safe)
     apply (metis lengthS_def not_less_Least option.sel)
    apply (metis finiteS_def index_tail_iff lengthS_def option.distinct(1))
   apply (clarsimp simp: finiteS_def)
   apply (metis finiteS_def lengthS_def option.distinct(1))
  apply (clarsimp simp: bind_eq_Some_conv)
   apply (subgoal_tac "finiteS (t)")
   apply (clarsimp simp: finite_index_iff split: if_splits)
   apply (clarsimp simp: index_tail_iff)
  apply (safe; clarsimp?)
      apply (metis lengthS_def not_less_Least option.sel)
     apply (meson Suc_leI add_less_le_mono less_diff_conv)
    apply (clarsimp simp: isl_iff)
    apply simp
    apply (clarsimp simp: isl_iff)
  apply simp
  by (metis lengthS_def option.distinct(1))

lemma match_empty_iff: "match t t' \<Longrightarrow> finiteS t \<Longrightarrow> lengthS t = Some 0 \<longleftrightarrow> lengthS t' = Some 0"
  apply (clarsimp simp: match_def)
  apply (clarsimp simp: match_def last_def first_def split: sum.splits if_splits option.splits)
    apply (metis bot_nat_0.extremum_strict isl_iff sum.disc(1))
  apply (metis diff_Suc_less finiteS_def gr_zeroI isl_iff lengthS_def option.sel sum.disc(2))
  done

lemma lengthS_iff': "match t t' \<Longrightarrow>  lengthS (t -o t') = (Option.bind (lengthS t) (\<lambda>s. Option.bind (lengthS t') (\<lambda>s'. Some (s + s' - 1))))" 
  apply (rule lengthS_eqI)
   apply (clarsimp)
   apply (clarsimp simp: option_bind_None_iff)
   apply (elim disjE)
    apply (subgoal_tac "\<not> finiteS (t)")
     apply (clarsimp simp: infinite_index_iff)
  using finiteS_def apply blast
    apply (clarsimp simp: lengthS_def)
   apply (clarsimp)
   apply (subgoal_tac "finiteS (t)")
    apply (clarsimp simp: finite_index_iff)
    apply (safe)
     apply (metis lengthS_def not_less_Least option.sel)
    apply (metis finiteS_def index_tail_iff lengthS_def option.distinct(1))
   apply (clarsimp simp: finiteS_def)
   apply (metis finiteS_def lengthS_def option.distinct(1))
  apply (clarsimp simp: bind_eq_Some_conv)
   apply (subgoal_tac "finiteS (t)")
   apply (clarsimp simp: finite_index_iff split: if_splits)
   apply (clarsimp simp: index_tail_iff)
  apply (safe; clarsimp?)
      apply (metis lengthS_def not_less_Least option.sel)
  using match_empty_iff apply fastforce
    apply (clarsimp simp: isl_iff)
    apply simp
    apply (clarsimp simp: isl_iff)
  apply simp
  by (metis lengthS_def option.distinct(1))

lemma match_match_glue: "match y z \<Longrightarrow> match x (y -o z) \<Longrightarrow> match x y"
  apply (clarsimp simp: match_def first_is_some_iff_index first_None_iff first_is_some_iff_index' first_None_iff' last_def split: if_splits sum.splits)
          apply (metis (no_types, lifting) One_nat_def diff_is_0_eq finite_index_iff first_def isl_iff 
    lengthS_def less_Suc_eq_0_disj linordered_semidom_class.add_diff_inverse option.sel order_le_less plus_1_eq_Suc sum.disc(1))
          apply (metis (no_types, lifting) One_nat_def diff_is_0_eq finite_index_iff first_def isl_iff 
    lengthS_def less_Suc_eq_0_disj linordered_semidom_class.add_diff_inverse option.sel order_le_less plus_1_eq_Suc sum.disc(1))
        apply (metis One_nat_def diff_0_eq_0 finite_index_iff first_def index_tail_iff isl_iff not_one_less_zero sum.disc(1))
    apply (metis bot_nat_0.not_eq_extremum finite_index_iff first_None_iff' first_def lengthS_def option.sel)
   apply (metis infinite_index_iff trace_eqI)
  by (simp add: glue_def)




lemma finiteS_glue[simp]: "finiteS (x -o y) \<longleftrightarrow> finiteS x \<and> finiteS y " 
  apply (intro iffI; clarsimp simp: finiteS_def)
   apply (intro conjI)
    apply (metis finiteS_def infinite_index_iff)
   apply (metis finiteS_def finite_index_iff
    index_tail_iff infinite_index_iff isl_iff lengthS_def option.sel) 
  apply (subst finite_index_iff)
  using finiteS_def apply blast
  apply (clarsimp simp: index_tail_iff)
  by (metis diff_add_inverse isl_monotone le0 not0_implies_Suc not_add_less1)



lemma length_eq_isl_iff: "lengthS x = lengthS y \<Longrightarrow> isl(index x n) \<longleftrightarrow> isl (index y n)"
  by (metis finiteS_def isl_iff lengthS_def)

lemma map_trace_eqD: "map_trace f x = map_trace f y \<Longrightarrow> index x n = Inl s \<Longrightarrow> \<exists>s'. index y n = Inl s' \<and> f s = f s'"
  by (metis (no_types, lifting) index_map_eqD lengthS_map_eq length_eq_isl_iff sum.collapse(1) sum.disc(1) sum.sel(1))


definition "modify n f t = liftF (\<lambda>m. if m = n then map_sum f id (index t m) else index t m)" 

lemma index_modify_iff: "index (modify n f t) = (\<lambda>m. if m = n then map_sum f id (index t m) else index t m)"
  apply (clarsimp simp: modify_def)
  apply (intro ext)
  apply (subst index_liftF)
   apply (clarsimp simp: traceDom_def)
   apply (metis (mono_tags, lifting) id_apply index_eq_finished
           isl_map_sum map_sum_sel(2) order_refl sum.expand)
  apply (clarsimp)
  done

lemma finiteS_modify[simp]: "finiteS (modify n f t) \<longleftrightarrow> finiteS t"
  apply (clarsimp simp: finiteS_def index_modify_iff  )
  by (metis isl_map_sum)

lemma lengthS_modify[simp]: "lengthS (modify n f t) = lengthS t"
  apply (clarsimp simp: lengthS_def)
  by (metis index_modify_iff isl_map_sum)

lemma lengthS_some_finite[simp]: "lengthS t = Some m \<Longrightarrow> finiteS t"
  by (metis lengthS_def option.distinct(1))

lemma last_modify_last: "lengthS t = (Some m) \<Longrightarrow> n = m - 1 \<Longrightarrow> m > 0 \<Longrightarrow>  last (modify n f t) = Some (f (projl (index t n)))"
  apply (clarsimp simp: last_def)
   apply (clarsimp split: sum.splits option.splits, intro conjI impI allI; clarsimp?)
    apply (clarsimp simp: index_modify_iff)
    apply (simp add: index_map_eqD index_map_sum)
  by (metis diff_Suc_less isl_iff lengthS_modify sum.disc(2))

find_consts "'a \<Rightarrow> ('a, 'b) trace"

definition "singleton x y = liftF (\<lambda>n. if n = 0 then Inl x else Inr y)"

definition "takeS n t = liftF (\<lambda>m. if m < n then (index t m) else (if lengthS t \<noteq> None then index t (the (lengthS t)) else Inr undefined))"

definition "dropS n t = liftF (\<lambda>m. index t (m + n))"

lemma index_take: "lengthS t = Some i \<Longrightarrow> 
   index (takeS n t) m = (if m < n then (index t m) else (index t i))" 
  apply (subst takeS_def, subst index_liftF)
   apply (clarsimp simp: traceDom_def)
  apply (intro conjI impI; clarsimp?)
    apply (meson dual_order.refl index_eq_finished)
  apply (metis index_eq_finished isl_iff leI nat_neq_iff)
  apply (clarsimp)
  done

lemma inf_all_l[dest, simp]: "lengthS t = None \<Longrightarrow> isl (index t n)"
  by (metis finiteS_def lengthS_def option.distinct(1))


lemma index_take_inf: "lengthS t = None \<Longrightarrow> 
   index (takeS n t) m = (if m < n then (index t m) else Inr undefined)" 
  by (subst takeS_def, subst index_liftF; clarsimp simp: traceDom_def)

lemma index_drop: "index (dropS n t) m = index t (m + n)"
  apply (subst dropS_def, subst index_liftF)
   apply (clarsimp simp: traceDom_def)
  apply (meson add_le_cancel_right dual_order.refl index_eq_finished)
  apply (clarsimp)
  done

lemma finiteS_takeS[simp]:"finiteS (takeS n t)"
  apply (clarsimp simp: finiteS_def)
  apply (rule_tac x=n in exI)
  by (case_tac \<open>lengthS t = None\<close>; clarsimp simp: index_take_inf index_take isl_iff)

lemma lengthS_takeS_min: "lengthS x = Some n \<Longrightarrow> lengthS (takeS y x) = Some (min y n)"
 by (smt (verit, best) finiteS_takeS index_take isl_iff leI lengthS_def min_def nle_le order_less_irrefl)

lemma lengthS_takeS_min': "lengthS x = None \<Longrightarrow> lengthS (takeS y x) = Some (y)"
  by (smt (verit) finiteS_def finiteS_takeS index_take_inf is_none_code(2) is_none_simps(1) isl_iff lengthS_def nat_neq_iff)

(* definition "emptyS s \<equiv> liftF (\<lambda>n. Inr s)" *)


lemma isl_coerce[simp]: "isl (coerce c) \<longleftrightarrow> isl c"
  by (cases c; clarsimp simp: coerce_def)

lemma index_append: "lengthS x = Some i \<Longrightarrow> index (appendS x y) n = (if n < i then coerce (index x n) else index y (n - i))"
  apply (clarsimp simp: appendS_def, intro iffI conjI impI)
   apply (subst index_liftF)
    apply (clarsimp simp: traceDom_def)
    apply (safe; clarsimp?)
      apply (metis coerce.simps(1) dual_order.strict_trans1 isl_def isl_iff nat_less_le)
     apply (metis coerce.simps(1) isl_def isl_iff )
    apply (meson diff_le_mono dual_order.refl index_eq_finished)
   apply (clarsimp)
  apply (subst index_liftF)
apply (clarsimp simp: traceDom_def)
    apply (safe; clarsimp?)
      apply (metis coerce.simps(1) dual_order.strict_trans1 isl_def isl_iff nat_less_le)
     apply (metis coerce.simps(1) isl_def isl_iff )
   apply (meson diff_le_mono dual_order.refl index_eq_finished)
  apply (clarsimp)
  done

lemma index_append_inf: "lengthS x = None \<Longrightarrow> index (appendS x y) n = coerce (index x n)"
  apply (clarsimp simp: appendS_def, intro iffI conjI impI)
   apply (metis lengthS_def option.distinct(1))
  apply (subst index_liftF, clarsimp simp: traceDom_def)
  apply (clarsimp)
  done

lemma [simp]: "coerce \<circ> index x \<in> traceDom"
  apply (clarsimp simp: traceDom_def)
  by (metis dual_order.refl index_eq_finished)

lemma lengthS_coerce[simp]: "lengthS (liftF (coerce \<circ> index x)) = lengthS x"
  by (rule lengthS_eqI; clarsimp simp: isl_iff)

lemma lengthS_coerceE[elim]: "P (lengthS x) \<Longrightarrow> P (lengthS (liftF (coerce \<circ> index x))) "
  by (clarsimp)

lemma drop_zero[simp]: "(dropS 0 x) = x"
  by (clarsimp simp: dropS_def, transfer, clarsimp)

lemma length_zero_append[simp]: "lengthS x = Some 0 \<Longrightarrow> appendS x y = y"
  by (intro trace_eqI, subst index_append[where i=0]; clarsimp)


lemma coerce_infinite[simp]:"lengthS y = None \<Longrightarrow> coerce (index y n) = index y n"
  by (metis coerce.simps(1) inf_all_l isl_def)


lemma coerce_le[simp]:"lengthS y = Some n \<Longrightarrow> m < n \<Longrightarrow> coerce (index y m) = index y m"
  by (metis coerce.simps(1) isl_iff sum.collapse(1))

lemma length_zero_append'[simp]: "lengthS x = Some 0 \<Longrightarrow> appendS y x = y"
  apply (case_tac "lengthS y = None")
   apply (intro trace_eqI, clarsimp simp: index_append_inf)
  apply (clarsimp)
  apply (intro trace_eqI, subst index_append, assumption, clarsimp)
  oops

lemma coerce_coerce[simp]: "coerce (coerce c) = coerce c"
  by (cases c; clarsimp)

lemma lengthS_dropS: 
  assumes l: "lengthS x = Some n" shows "lengthS (dropS i x) = Some (n - i)"
proof (rule lengthS_eqI) 
  assume "Some (n - i) = None"
  then show "\<forall>n. isl (index (dropS i x) n)" by blast
next 
  fix na :: nat
  assume a: "Some (n - i) = Some na"
  show "\<forall>n'. if n' < na then isl (index (dropS i x) n') else \<not> isl (index (dropS i x) n')"
  proof 
     fix n'
     have "na = n - i" using a by simp
    then show "if n' < na then isl (index (dropS i x) n') else \<not> isl (index (dropS i x) n')"
    using l 
    by (metis index_drop isl_iff less_diff_conv )
  qed
qed

lemma lengthS_dropS_inf:  "lengthS x = None \<Longrightarrow> lengthS (dropS i x) = None"
  by (rule lengthS_eqI; clarsimp simp: index_drop isl_iff)

definition "clean t = liftF ( coerce o index t)"

lemma lengthS_clean[simp]: "lengthS (clean t) = lengthS t"
  by (clarsimp simp: clean_def)


lemma index_liftF'[simp]: "f \<in> traceDom \<Longrightarrow> index (liftF f) = f  "
  by (transfer, clarsimp)

lemma index_clean: "index (clean t) = coerce o index t"
  by (clarsimp simp: clean_def)

find_consts "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) trace"

lemma [simp]: "(\<lambda>n. if n = 0 then Inl x else Inr y) \<in> traceDom"
  by (clarsimp simp: traceDom_def)

lemma lengthS_singleton: "lengthS (singleton x y) = Some 1"
  apply (rule lengthS_eqI; clarsimp)
  apply (safe)
   apply (clarsimp simp: singleton_def )
   apply (clarsimp simp: singleton_def )
  done


lemma lengthS_appendI: "lengthS x = Some m  \<Longrightarrow> lengthS y = Some m' \<Longrightarrow> lengthS (appendS x y) = Some (m + m')"
    apply (rule lengthS_eqI; clarsimp simp: isl_iff)
  apply (intro conjI impI; clarsimp simp: index_append isl_iff)
   apply linarith
  apply linarith
  done

lemma lengthS_appendI': "lengthS x = Some m  \<Longrightarrow> lengthS y = Some m' \<Longrightarrow> n = m + m' \<Longrightarrow> lengthS (appendS x y) = Some (n)"
    apply (rule lengthS_eqI; clarsimp simp: isl_iff)
  apply (intro conjI impI; clarsimp simp: index_append isl_iff)
   apply linarith
  apply linarith
  done

lemma lengthS_appendD: "lengthS (appendS x y) = Some n \<Longrightarrow> 
   \<exists>m m'. lengthS x = Some m  \<and> lengthS y = Some m' \<and> n = m + m' "
  apply (case_tac "lengthS x = None \<or> lengthS y = None", elim disjE; clarsimp?)
    apply (metis appendS_def lengthS_coerce lengthS_def option.distinct(1))
   apply (metis (no_types, lifting) appendS_def index_append inf_all_l 
           isl_coerce isl_iff lengthS_coerce lengthS_def verit_comp_simplify1(1))
  using lengthS_appendI 
  by (metis option.inject)

lemma lengthS_append_eq: "lengthS (appendS x y) = Some n \<longleftrightarrow> (\<exists>m m'. lengthS x = Some m  \<and> lengthS y = Some m' \<and> n = m + m') "
  apply (case_tac "lengthS x = None \<or> lengthS y = None", elim disjE; clarsimp?)
    apply (metis appendS_def lengthS_coerce lengthS_def option.distinct(1))
   apply (metis (no_types, lifting) appendS_def index_append inf_all_l 
           isl_coerce isl_iff lengthS_coerce lengthS_def verit_comp_simplify1(1))
  using lengthS_appendI 
  by (metis option.inject)

lemma last_index_iff[simp]: "lengthS x = Some (Suc n) \<Longrightarrow> Traces.last x = Some (projl (index x n))"
  apply (clarsimp simp: last_def)
  by (simp add: isl_iff sum.case_eq_if)


lemma first_index_iff: "lengthS x = Some (Suc n) \<Longrightarrow> Traces.first x = Some (projl (index x 0))"
  apply (clarsimp simp: first_def)
  by (simp add: isl_iff sum.case_eq_if)


lemma first_index_iff': "lengthS x = None \<Longrightarrow> Traces.first x = Some (projl (index x 0))"
  apply (clarsimp simp: first_def)
  by (simp add: isl_iff sum.case_eq_if)

lemma split_match: "lengthS x = Some (Suc n) \<Longrightarrow> match x y \<longleftrightarrow> (\<exists>x' z y'. lengthS z = Some 1 \<and>  x = appendS x' z \<and> y = appendS z y')"
  apply (safe)
  apply (rule_tac x="clean (takeS n x)" in exI, rule_tac x="dropS n x" in exI)
   apply (clarsimp simp: index_append index_drop lengthS_dropS)
   apply (rule conjI)
    apply (rule trace_eqI)
    apply (subst index_append, subst lengthS_clean, 
           subst lengthS_takeS_min, assumption, clarsimp, rule refl)
    apply (clarsimp split: if_splits, safe; (clarsimp simp: index_clean index_take index_drop)?)
   apply (rule_tac x="dropS 1 y" in exI)
   apply (rule trace_eqI)
   apply (clarsimp simp: index_append lengthS_dropS index_drop)
   apply (clarsimp simp: match_def last_def first_def isl_iff split: sum.splits)
   apply (metis isl_iff lessI sum.disc(2))
  apply (clarsimp simp: match_def)

  apply (case_tac "lengthS y' = None")
   apply (subst first_index_iff')
    apply (metis lengthS_appendD option.distinct(1) option.exhaust)
   apply (clarsimp simp: index_append)
   apply (drule lengthS_appendD, clarsimp simp: index_append)
   apply (metis coerce.simps(1) isl_iff lessI sum.collapse(1) sum.sel(1))
  apply (clarsimp)
  apply (subst first_index_iff, rule lengthS_appendI', assumption, assumption)
   apply (clarsimp, rule refl, clarsimp)
  apply (drule lengthS_appendD, clarsimp simp: index_append)
   apply (metis coerce.simps(1) isl_iff lessI sum.collapse(1) sum.sel(1))
  done

lemma split_match_fixtype: "lengthS x = Some (Suc n) \<Longrightarrow> 
   match (x :: ('a, 'b) trace) y \<longleftrightarrow>
   (\<exists>(x' :: ('a, 'b) trace) z y'. lengthS z = Some 1 \<and>  x = appendS x' z \<and> y = appendS z y')"
  apply (safe)
  apply (rule_tac x="clean (takeS n x)" in exI, rule_tac x="dropS n x" in exI)
   apply (clarsimp simp: index_append index_drop lengthS_dropS)
   apply (rule conjI)
    apply (rule trace_eqI)
    apply (subst index_append, subst lengthS_clean, 
           subst lengthS_takeS_min, assumption, clarsimp, rule refl)
    apply (clarsimp split: if_splits, safe; (clarsimp simp: index_clean index_take index_drop)?)
   apply (rule_tac x="dropS 1 y" in exI)
   apply (rule trace_eqI)
   apply (clarsimp simp: index_append lengthS_dropS index_drop)
   apply (clarsimp simp: match_def last_def first_def isl_iff split: sum.splits)
   apply (metis isl_iff lessI sum.disc(2))
  apply (clarsimp simp: match_def)
  apply (case_tac "lengthS y' = None")
   apply (subst first_index_iff')
    apply (metis lengthS_appendD option.distinct(1) option.exhaust)
   apply (clarsimp simp: index_append)
   apply (drule lengthS_appendD, clarsimp simp: index_append)
   apply (metis coerce.simps(1) isl_iff lessI sum.collapse(1) sum.sel(1))
  apply (clarsimp)
  apply (subst first_index_iff, rule lengthS_appendI', assumption, assumption)
   apply (clarsimp, rule refl, clarsimp)
  apply (drule lengthS_appendD, clarsimp simp: index_append)
   apply (metis coerce.simps(1) isl_iff lessI sum.collapse(1) sum.sel(1))
  done

definition "empty_trace s \<equiv> liftF (\<lambda>n. Inr s)"

lemma index_empty[simp]: "index (empty_trace s) n = Inr s"
  apply (clarsimp simp: empty_trace_def)
  by (subst index_liftF, clarsimp simp: traceDom_def, clarsimp)

lemma index_cong: "t = t' \<Longrightarrow> index t n = index t' n"
  by (transfer, clarsimp)

lemma lengthS_zero_empty_trace: "lengthS t = Some 0 \<longleftrightarrow> t = empty_trace (projr (index t 0))"
  apply (safe)
   apply (rule trace_eqI, clarsimp simp: empty_trace_def)
   apply (subst index_liftF, clarsimp simp: traceDom_def)
   apply (metis isl_iff isr_antitone less_nat_zero_code nat_le_linear sum.collapse(2))
  apply (rule lengthS_eqI; clarsimp)
  by (drule_tac n=n' in index_cong, clarsimp)

lemma lengthS_empty[simp]: "lengthS (empty_trace s) = Some 0"
  by (rule lengthS_eqI; clarsimp)

lemma append_empty: "t = empty_trace s \<Longrightarrow> appendS t x = x"
  using [[show_types]]
  by (rule trace_eqI, clarsimp simp: index_append)


lemma append_empty_r: "t = empty_trace s \<Longrightarrow> appendS x t = x"
  using [[show_types]]
  apply (case_tac "lengthS x = None", clarsimp)
   apply (simp add: index_append_inf trace_eqI)
  apply (clarsimp)
  apply (rule trace_eqI, clarsimp simp: index_append)
  oops

lemma inf_append_simp[simp]: "lengthS x = None \<Longrightarrow> appendS (x :: ('a, 'b) trace) (y :: ('a, 'c) trace) = clean x"
  apply (rule trace_eqI, simp add: index_append_inf trace_eqI)
  by (clarsimp simp: index_clean)

lemma inf_glue_simp[simp]: "lengthS x = None \<Longrightarrow>  (x -o y) = x"
  apply (simp add: index_append_inf trace_eqI glue_def)
  apply (safe)
  by (metis lengthS_def option.distinct(1))


lemma finiteS_append_iff[simp]: "finiteS (appendS x z) \<longleftrightarrow> finiteS x \<and> finiteS z"
  apply (safe)
    apply (metis finiteS_def inf_all_l inf_append_simp lengthS_clean lengthS_def)
   apply (metis lengthS_appendD lengthS_def option.distinct(1))
  by (meson lengthS_appendI' lengthS_def lengthS_some_finite)

lemma glue_is_append: "lengthS z = Some 1 \<Longrightarrow> (appendS x z -o appendS z y) = appendS x (appendS z y)"
  apply (case_tac "lengthS x = None"; clarsimp)
  apply (rule trace_eqI)
  apply (subst finite_index_iff)
   apply (clarsimp)
  by (clarsimp simp: index_append index_tail_iff lengthS_appendI)

definition "terminal y = dropS (the (lengthS y)) y"

lemma inf_is_clean[simp]: "lengthS x = None \<Longrightarrow> x = clean x"
  by (metis coerce_infinite index_append_inf inf_append_simp trace_eqI)

lemma terminal_append: "lengthS z = Some n \<Longrightarrow> lengthS y \<noteq> None \<Longrightarrow>  terminal (appendS z y) = terminal y"
  apply (clarsimp simp: terminal_def, rule trace_eqI)
  apply (clarsimp simp: index_drop index_append, safe)
   apply (simp add: lengthS_appendI')
  by (clarsimp simp: lengthS_appendI)

lemma clean_idemp[simp]: "clean (clean x) = (clean x)"
  by (rule trace_eqI; clarsimp simp: index_clean)

lemma infinite_appendS_iff: "lengthS (appendS x y) = None \<longleftrightarrow> (lengthS y = None \<or> lengthS x = None)"
  by (metis lengthS_append_eq option.distinct(1) option.exhaust)

lemma appendS_assoc: "appendS x (appendS y z) = appendS (appendS x y) (z)"
  apply (rule trace_eqI)
  apply (case_tac "lengthS x = None"; clarsimp?)
  apply (case_tac "lengthS y = None"; clarsimp?)
   apply (metis coerce_coerce index_append index_append_inf inf_append_simp infinite_appendS_iff)
  apply (clarsimp simp: index_append lengthS_appendI, safe; clarsimp?)
   apply (linarith)+
  done

lemma empty_is_terminal: "y = empty_trace s \<Longrightarrow> (terminal y = y)"
  by (rule trace_eqI, clarsimp simp: terminal_def)

lemma glue_l1_trace: "lengthS y = Some 1 \<Longrightarrow>  match x y \<Longrightarrow> (x -o y) = appendS x (terminal y)"
  apply (case_tac "lengthS x = None"; clarsimp)
  apply (case_tac "ya")
  apply (metis One_nat_def lengthS_some_finite match_empty_iff option.inject zero_neq_one)
  thm split_match
   apply (subst (asm) split_match_fixtype, fastforce)
  apply (clarsimp simp: glue_is_append)
  apply (clarsimp simp: lengthS_append_eq lengthS_zero_empty_trace)
  apply (subst terminal_append, assumption)
   apply (metis lengthS_empty option.distinct(1))
  by (clarsimp simp: empty_is_terminal appendS_assoc)


lemma glue_l1_trace': "lengthS x = Some 1 \<Longrightarrow> match x y \<Longrightarrow> (x -o y) = y"
  apply (rule trace_eqI)
  apply (clarsimp simp: finite_index_iff index_tail_iff)
  apply (clarsimp simp: match_def last_def first_def split: sum.splits option.splits)
  by (metis isl_iff sum.disc(2) zero_less_Suc)

lemma index_consts: "index (constS s) n = Inl s"
  apply (clarsimp simp: constS_def, subst index_liftF)
   apply (clarsimp simp: traceDom_def)
  by (clarsimp)


lemma last_map[simp]: "last (map_trace f t) = map_option f (last t)"
  by (clarsimp simp: last_def index_map_sum split: sum.splits)


lemma first_map[simp]: "first (map_trace f t) = map_option f (first t)"
  by (clarsimp simp: first_def index_map_sum split: sum.splits)




lemma inf_left_glue_left: "lengthS x = None \<Longrightarrow>  (x -o y) = x"
  by (clarsimp simp: inf_glue_simp )


lemma match_inf: "lengthS x = None \<Longrightarrow> match x x'" 
  by (clarsimp simp: match_def finiteS_def)



lemma partition_glue: "lengthS x = Some n \<Longrightarrow> y \<le> n \<Longrightarrow> y \<noteq> 0 \<Longrightarrow>
   (takeS y x -o dropS (y - 1) x) = x \<and> match (takeS y x) (dropS (y - 1) x)"
  apply (intro conjI)
  apply (intro trace_eqI)
   apply (clarsimp simp: finite_index_iff index_take index_tail_iff index_drop lengthS_takeS_min)
  by (clarsimp simp: match_def last_def first_def index_take 
      index_tail_iff index_drop lengthS_takeS_min split: sum.splits option.splits)

lemma partition_glue': " y \<noteq> 0 \<Longrightarrow> lengthS x = None \<Longrightarrow>
   (takeS y x -o dropS (y - 1) x) = x \<and> match (takeS y x) (dropS (y - 1) x)"
  apply (intro conjI)
  apply (intro trace_eqI)
   apply (clarsimp simp: finite_index_iff index_take index_tail_iff index_drop lengthS_takeS_min')
  apply (simp add: index_take_inf)
  apply (clarsimp simp: match_def last_def first_def index_take lengthS_takeS_min'
      index_tail_iff index_drop lengthS_takeS_min split: sum.splits option.splits)
  by (metis One_nat_def diff_less index_take_inf sum.sel(1) sum.simps(4) zero_less_one)

lemma zero_length_match: "lengthS x = Some 0 \<Longrightarrow> match x y \<longleftrightarrow> lengthS y = Some 0"
  apply (clarsimp simp: match_def)
  by (metis Traces.last_def diff_0_eq_0 first_None_iff' first_def option.sel)


lemma zero_length_match': "lengthS x = Some 0 \<Longrightarrow> match y x \<longleftrightarrow> (\<forall>n. lengthS y \<noteq> Some (Suc n))"
  apply (clarsimp simp: match_def)
  apply (safe; clarsimp?)
   apply (metis first_None_iff last_index_iff option.distinct(1))
  by (metis Traces.last_def diff_0_eq_0 finiteS_def first_None_iff' first_def inf_all_l old.nat.exhaust option.exhaust_sel)


lemma lengthS_glueI: "lengthS x = Some m \<Longrightarrow> lengthS y = Some m' \<Longrightarrow> Suc n = m + m' \<Longrightarrow> match x y \<Longrightarrow>  lengthS (x -o y) = Some n" 
  apply (rule lengthS_eqI; clarsimp simp:)
  apply (safe; clarsimp?)
  apply (clarsimp simp:  finite_index_iff index_tail_iff)
   apply (metis add_Suc_right add_diff_inverse_nat isl_iff nat_add_left_cancel_less not_less_eq)
  apply (drule leI)
  apply (clarsimp simp:  finite_index_iff index_tail_iff isl_iff split:if_splits)
  apply (metis Suc_lessI add_diff_cancel_left' diff_add_0 gr_implies_not0 isl_iff le_less_Suc_eq lengthS_some_finite match_empty_iff not_add_less1 trans_less_add1)
  by auto

lemma length_glue_zero_iff: "match x y \<Longrightarrow> lengthS (x -o y) = Some 0 \<longleftrightarrow> (lengthS x = Some 0 \<and> lengthS y = Some 0)" 
  apply (safe)
    apply (metis (mono_tags, lifting) finiteS_glue finite_index_iff isl_iff lengthS_def not_gr_zero option.sel)
   apply (rule lengthS_eqI; clarsimp simp: isl_iff)
  apply (case_tac "lengthS y = None", clarsimp)
    apply (metis finiteS_glue lengthS_def option.distinct(1))
   apply (clarsimp)
  apply (case_tac "lengthS x = None"; clarsimp)
   apply (meson isl_iff less_zeroE match_match_glue zero_length_match)
   apply (rule lengthS_eqI; clarsimp simp: isl_iff)
  by (simp add: finite_index_iff index_tail_iff isl_iff)

lemma first_appendS[simp]: "lengthS x \<noteq> Some 0 \<Longrightarrow> first (appendS x y) = Some (projl (index x 0))"
  by (smt (verit, ccfv_threshold) Least_eq_0 coerce.simps(1) first_def index_append index_append_inf inf_all_l isl_coerce isl_iff lengthS_def sum.case_eq_if sum.collapse(1) sum.sel(1))


lemma last_glue_r: "match x y \<Longrightarrow> lengthS x = Some n \<Longrightarrow>  last (x -o y) = last y"
  apply (cases n; clarsimp?)

   apply (metis lengthS_some_finite length_glue_zero_iff match_def zero_length_match)
  apply (case_tac "lengthS y = None")
   apply (metis Traces.last_def finiteS_def finiteS_glue inf_all_l)
  apply (clarsimp)
  apply (case_tac ya; clarsimp?)
  using zero_length_match' apply blast
  apply (clarsimp simp: last_index_iff lengthS_glueI)
  find_theorems index glue
  apply (subst finite_index_iff)
  using lengthS_some_finite apply blast
  apply (clarsimp, safe)
   apply (simp add: first_index_iff last_index_iff match_def)
  by (clarsimp simp: index_tail_iff)


lemma match_match_glue': "match y z \<Longrightarrow> match x (y -o z) \<Longrightarrow> match (x -o y) z" 
  apply (case_tac "lengthS x = None"; clarsimp)
  apply (clarsimp simp: match_def)
   apply (metis lengthS_def option.distinct(1))

  apply (case_tac "lengthS y = None"; clarsimp)
  apply (clarsimp simp: match_def)
   apply (metis lengthS_def option.distinct(1))
  apply (subst match_def; clarsimp)
  apply (subst last_glue_r)
  using match_match_glue apply blast
   apply (assumption)
  apply (clarsimp simp: match_def)
  done

datatype symbols = Abort | Term | Incomplete

datatype 'state Step = Env 'state | Pgm 'state 


datatype 'state Trace = Trace (int : 'state) (tra : "('state Step, symbols) trace") | Empty

definition "trace s t = (if s = None then Empty else Trace (the s) t)"

primrec tr where
 "tr (Trace _ t) = t" |
 "tr (Empty) = (empty_trace Incomplete)" 


primrec init where
 "init (Trace s t) = Some s" |
 "init (Empty) = None" 

lemma init_trace[simp]: "init (trace s t) = s"
  apply (clarsimp simp: trace_def)
  done
term case_option

lemma tr_trace[simp]: "tr (trace s t) = case_option (empty_trace Incomplete) (\<lambda>_. t) s "
  apply (clarsimp simp: trace_def)
  done

instantiation Trace :: (type)  preorder_bot begin

primrec bottom_Trace where
 "bottom_Trace (Trace s _) = Trace (s) (empty_trace Incomplete) " |
 "bottom_Trace Empty = Empty"

fun ref_step where
 "ref_step (Inl s) (Inl s')    = (s = s')" |
 "ref_step (Inr Incomplete) _  = True" |
 "ref_step _ (Inr Abort)       = True" |
 "ref_step (Inr Abort) c       = (c = Inr Abort)" |
 "ref_step  c (Inr Incomplete) = (c = Inr Abort)" |
 "ref_step  (Inr Term) (Inr Term) = True" |
 "ref_step  (Inr Term) (Inl v) = False" | 
 "ref_step  (Inl v) (Inr Term) = False" 

lemma ref_step_refl[simp]: "ref_step x x"
  apply (case_tac x; clarsimp)
  apply (case_tac b; clarsimp)
  done

lemma ref_step_trans[simp]: "ref_step x y \<Longrightarrow> ref_step y z \<Longrightarrow> ref_step x z"
  apply (case_tac x; case_tac y; case_tac z; clarsimp)
      apply (case_tac b; clarsimp)
     apply (case_tac b; case_tac ba; clarsimp)
  apply (case_tac b; case_tac ba; clarsimp)
  apply (case_tac b; case_tac ba; clarsimp)
  apply (case_tac b; case_tac ba; clarsimp)
  apply (case_tac bb; clarsimp)
  done

definition "ref_option t t' = (if t = None then True else t = t')"

lemma ref_option_refl[simp]:"ref_option x x"
  by (clarsimp simp: ref_option_def)


lemma ref_option_antisym:"ref_option x y \<Longrightarrow> ref_option y x \<Longrightarrow> x = y"
  by (clarsimp simp: ref_option_def split: if_splits)



lemma ref_none[simp]: "ref_option None t"
  apply (clarsimp simp: ref_option_def)
  done

lemma ref_Some[simp]: "ref_option (Some a) t \<longleftrightarrow> t = Some a"
  apply (clarsimp simp: ref_option_def, fastforce)
  done

lemma ref_Some'[simp]: "ref_option (Some a) (Some b) \<longleftrightarrow> a = b"
  apply (clarsimp simp: ref_option_def)
  done


lemma ref_option_trans[elim, simp]:"ref_option x y \<Longrightarrow> ref_option y z \<Longrightarrow> ref_option x z"
  by (cases x; cases y; cases z; clarsimp)

find_consts "'a option \<Rightarrow> 'b option \<Rightarrow> 'c option"

definition less_eq_Trace where
 "less_eq_Trace t t' \<equiv> ( (init t) = (init t')) \<and> (\<forall>n. ref_step (index (tr t) n)  (index (tr t') n))  "


definition
  "(f:: ('a) Trace) < g \<longleftrightarrow> f \<le> g \<and> \<not> (g \<le> f)"

instance
  apply (standard)
     apply (clarsimp simp: bottom_Trace_def less_eq_Trace_def less_Trace_def split: if_splits)
  apply (clarsimp simp: bottom_Trace_def less_eq_Trace_def less_Trace_def split: if_splits)
  apply (clarsimp simp: bottom_Trace_def less_eq_Trace_def less_Trace_def split: if_splits)

  using ref_step_trans apply blast
  apply (case_tac y; case_tac x; clarsimp)
    apply (clarsimp simp:  less_eq_Trace_def less_Trace_def split: if_splits)
    apply (clarsimp simp:  less_eq_Trace_def less_Trace_def split: if_splits)
    apply (clarsimp simp:  less_eq_Trace_def less_Trace_def split: if_splits)
  done

end

definition "cons_t x xs = liftF (\<lambda>n. if n = 0 then Inl x else index xs (n - 1) )"

definition "incomplete_trace t \<equiv> finiteS (tr t) \<and> (index (tr t) (the (lengthS (tr t))) = Inr Incomplete)" 

definition "aborted_trace t \<equiv> finiteS (tr t) \<and> (index (tr t) (the (lengthS (tr t))) = Inr Abort)" 

lemma incomplete_trace_empty[simp]: "incomplete_trace (Empty)"
  by (clarsimp simp: incomplete_trace_def)

definition "failed_trace \<equiv> incomplete_trace \<squnion> aborted_trace"

lemma failed_trace_empty[simp]: "failed_trace (Empty)"
  by (clarsimp simp: failed_trace_def)

definition "first_trace t \<equiv> (if t = Empty then Empty else trace ( (init t)) (empty_trace Term))"

definition "terminates t \<equiv> (if finiteS t then index t (the (lengthS t)) = Inr Term else False)"

lemma terminates_empty[simp]: "terminates (empty_trace c) \<longleftrightarrow> c = Term"
  by (clarsimp simp: terminates_def)

lemma incomplete_is_incomplete[simp]: "incomplete_trace (Trace (init x) (empty_trace Incomplete))"
  by (clarsimp simp: incomplete_trace_def)

primrec state_of where
 "state_of (Pgm s) = s" |
 "state_of (Env s) = s" 

fun last_trace where
 "last_trace (Empty) = (Empty)"|
 "last_trace (Trace s t) = (let t' = cons_t (Pgm s) t in (if terminates t' then trace (map_option state_of (last t')) (empty_trace Term) else Empty))"
definition "seq_trace x y = (let y' = (if last_trace x = first_trace y then (tr y) else (empty_trace Incomplete)) in
                                      (if failed_trace x then x else trace ( (init x)) (appendS (tr x) y')))"

(* definition "seq_trace x y = {Trace (init t) (appendS (tr t) (tr t')) | t t'. t \<in> \<down>x \<and> t' \<in> \<down>y \<and> last_trace t = first_trace t'} " *)



lemma index_cons_t:"index (cons_t x xs) n = (if n = 0 then Inl x else index xs (n - 1))"
  apply (clarsimp simp: cons_t_def, safe)
   apply (subst index_liftF)
    apply (clarsimp simp: traceDom_def)
    apply (meson diff_le_mono dual_order.eq_iff index_eq_finished)
   apply (clarsimp)
apply (subst index_liftF)
    apply (clarsimp simp: traceDom_def)
    apply (meson diff_le_mono dual_order.eq_iff index_eq_finished)
  apply (clarsimp)
  done

(* lemma in_seq_trace_iff: "w \<in> seq_trace x v \<longleftrightarrow> (\<exists>x' v'. x' \<le> x \<and> v' \<le> v \<and> first_trace v' = last_trace x' \<and> w = Trace (init x') (appendS (tr x') (tr v')))"
  apply (intro iffI)
   apply (clarsimp simp: seq_trace_def in_down_iff  split: if_splits)
   apply (rule_tac x=t in exI, clarsimp)
  apply (rule_tac x=t' in exI)
  apply (blast)
  apply (clarsimp simp: seq_trace_def in_down_iff  split: if_splits)
  by metis *)

lemma lengthS_cons: "lengthS (cons_t x xs) = map_option Suc (lengthS xs)"
  apply (rule lengthS_eqI; clarsimp simp: index_cons_t isl_iff)
  apply (safe)
   apply (simp add: isl_iff)  
  by linarith

lemma finiteS_cons[simp]: "finiteS (cons_t x xs) \<longleftrightarrow> finiteS xs"
  by (metis Zero_neq_Suc diff_Suc_1 finiteS_def index_cons_t sum.disc(1))

lemma last_cons_empty[simp]: "Traces.last (cons_t s (empty_trace c)) = Some s"
  apply (clarsimp simp: last_def)
  by (clarsimp simp: index_cons_t lengthS_cons)

lemma bot_eq_iff: "v = v\<^sub>\<bottom> \<longleftrightarrow> tr v = (empty_trace Incomplete)"
  apply (case_tac v; clarsimp)
  done

lemma le_init_first_le: "v \<le> Trace t ts \<Longrightarrow> first_trace v \<le> Trace t (empty_trace Term)"
  apply (clarsimp simp: less_eq_Trace_def)
  apply (intro conjI)
   apply (clarsimp simp: first_trace_def)
  apply (clarsimp)
  apply (clarsimp simp: first_trace_def bot_eq_iff)
  done
  

lemma aborted_end[simp]: "aborted_trace x \<Longrightarrow> index (tr x) (the (lengthS (tr x))) = Inr Abort"
  apply (clarsimp simp: aborted_trace_def)
  done

lemma ref_Abort_iff[simp]:" ref_step (Inr Abort) c \<longleftrightarrow> c = Inr Abort "
  apply (case_tac c; clarsimp)
  apply (case_tac b; clarsimp)
  done

lemma ref_term_iff[simp]:" ref_step (Inr Term) c \<longleftrightarrow> (c = Inr Abort \<or> c = Inr Term) "
  apply (case_tac c; clarsimp)
  apply (case_tac b; clarsimp)
  done

lemma not_aborted_no_aborts[simp]: "\<not> aborted_trace y \<Longrightarrow> index (tr y) n = Inr Abort = False"
  apply (clarsimp simp: aborted_trace_def)
  apply (case_tac "finiteS (tr y)"; clarsimp)
   apply (smt (verit) finiteS_lengthSE index_eq_finished isr_antitone linorder_le_less_linear
                                                                      linorder_linear)
  by (metis inf_all_l lengthS_def sum.disc(2))

lemma failed_ref_nonfailed_incomplete: "failed_trace x \<Longrightarrow> \<not> failed_trace y \<Longrightarrow> x \<le> y \<Longrightarrow>
                                        incomplete_trace x"
  apply (clarsimp simp: failed_trace_def less_eq_Trace_def)
  apply (erule_tac x="the (lengthS (tr x))" in allE, clarsimp)
  done




abbreviation (input) "len t \<equiv> the (lengthS (tr t))"


lemma not_failed_finite_index_iff[simp]:"\<not>aborted_trace x \<Longrightarrow> \<not>incomplete_trace x \<Longrightarrow> finiteS (tr x) \<Longrightarrow> index (tr x) (len x) = Inr Term"
  apply (subst (asm) aborted_trace_def, simp)
  apply (subst (asm) incomplete_trace_def, simp)
  by (smt (verit, best) isl_iff lengthS_def less_irrefl option.sel sum.collapse(2) symbols.exhaust)

lemma incomplete_index_len: "incomplete_trace y \<Longrightarrow> index (tr y) (len y) = Inr Incomplete"
  apply (clarsimp simp: incomplete_trace_def)
  done

lemma ref_incomplete_r[simp]:"ref_step c (Inr Incomplete) \<longleftrightarrow> c = (Inr Incomplete)"
  using ref_step.elims(2) by auto

lemma non_fail_ref_failed_aborted: "failed_trace y \<Longrightarrow> \<not> failed_trace x  \<Longrightarrow> x \<le> y \<Longrightarrow> aborted_trace y"
  apply (clarsimp simp: failed_trace_def less_eq_Trace_def)
  apply (case_tac "finiteS (tr x)")
   apply (erule_tac x="the (lengthS (tr x))" in allE)
   apply (clarsimp)
   apply (metis incomplete_trace_def isr_antitone linorder_linear not_aborted_no_aborts not_failed_finite_index_iff)
  apply (erule_tac x="the (lengthS (tr y))" in allE, clarsimp simp: incomplete_index_len)
  by (metis inf_all_l lengthS_def sum.disc(2))



lemma not_failed_len_le: "x \<le> y \<Longrightarrow> \<not> failed_trace y \<Longrightarrow> len x \<le> len y"  sorry

lemma aborted_len_le: "x \<le> y \<Longrightarrow> aborted_trace y \<Longrightarrow> \<not>incomplete_trace x \<Longrightarrow> finiteS (tr x) \<Longrightarrow> len y \<le> len x"
  apply (subst (asm) aborted_trace_def; clarsimp)
  apply (subgoal_tac "\<exists>m. lengthS (tr x) = Some m")
   apply (clarsimp)
   apply (subgoal_tac "\<exists>n. lengthS (tr y) = Some n"; clarsimp?)
  apply (clarsimp simp: less_eq_Trace_def)
    apply (metis aborted_end isl_iff lengthS_some_finite linorder_le_less_linear not_failed_finite_index_iff option.sel ref_Abort_iff ref_term_iff sum.disc(2))
   apply (meson lengthS_def)
  by (meson lengthS_def)



lemma less_eq_ref_stepD: "x \<le> y \<Longrightarrow> ref_step (index (tr x) n) (index (tr y) n)"
   apply (clarsimp simp: less_eq_Trace_def)
  done

lemma ref_clean_inf: "lengthS (tr y) = None \<Longrightarrow> x \<le> y \<Longrightarrow>  ref_step (index (tr x) n) (index (clean (tr y)) n)"
  apply (clarsimp simp: less_eq_Trace_def)
  apply (erule_tac x=n in allE)
  by (metis inf_is_clean)

lemma ref_clean_inf': "lengthS (tr x) = None \<Longrightarrow> x \<le> y \<Longrightarrow>  ref_step (index (clean (tr x)) n) (index ( (tr y)) n)"
  apply (clarsimp simp: less_eq_Trace_def)
  apply (erule_tac x=n in allE)
  by (metis inf_is_clean)

lemma not_failed_has_init: "\<not>failed_trace y \<Longrightarrow> \<exists>s. (init y) = Some s"
  apply (clarsimp simp: failed_trace_def)
  by (metis incomplete_trace_empty init.simps(1) last_trace.cases)

lemma not_failed_case_option_init[simp]: "\<not>failed_trace y \<Longrightarrow> case_option a (\<lambda>_. x) (init y) = x"
  apply (clarsimp simp: failed_trace_def)
   by (metis incomplete_trace_empty init.simps(1) last_trace.cases not_Some_eq option.case_eq_if)

lemma incomplete_ref: "incomplete_trace x \<Longrightarrow> x \<le> y \<Longrightarrow> \<not>failed_trace y \<Longrightarrow>  x \<le> trace (init y) (appendS (tr y) b)"
  apply (subst less_eq_Trace_def; clarsimp)
  apply (intro conjI)
   apply (clarsimp simp: less_eq_Trace_def)
  apply (clarsimp)
  apply (case_tac "\<exists>m. lengthS (tr y) = Some m", clarsimp simp: index_append)
   apply (safe)
    apply (erule less_eq_ref_stepD)
   apply (metis incomplete_trace_def isr_antitone linorder_le_less_linear not_failed_len_le option.sel ref_step.simps(2))
  apply (clarsimp)
  apply (erule (1) ref_clean_inf)
  done

lemma aborted_ref: "aborted_trace y \<Longrightarrow> x \<le> y \<Longrightarrow> \<not>incomplete_trace x \<Longrightarrow> trace (init x) (appendS (tr x) b) \<le> y"
  apply (subst (asm)  aborted_trace_def, elim conjE)
 apply (subst less_eq_Trace_def; clarsimp)
  apply (intro conjI)
   apply (clarsimp simp: less_eq_Trace_def)
  apply (clarsimp)
  apply (case_tac x; clarsimp)
 apply (case_tac "\<exists>m. lengthS (tr x) = Some m", clarsimp simp: index_append)
   apply (safe; clarsimp?)
    apply (metis less_eq_ref_stepD tr.simps(1))
   apply (smt (z3) aborted_trace_def incomplete_trace_def index_empty inf_all_l isl_iff isr_antitone lengthS_def less_eq_ref_stepD linorder_le_less_linear nless_le not_aborted_no_aborts not_failed_finite_index_iff option.sel ref_Abort_iff 
ref_incomplete_r ref_step.elims(1) ref_step.elims(3) ref_step.simps(10) ref_step.simps(2) ref_term_iff sum.disc(1) sum.disc(2) sum.inject(2) tr.simps(1))
  apply (clarsimp)
  by (metis inf_is_clean less_eq_ref_stepD tr.simps(1))



lemma isl_c_ref_iff[simp]: "isl c \<Longrightarrow> ref_step c d \<longleftrightarrow> (d = c) \<or> d = Inr Abort"
  apply (case_tac d; clarsimp)
   apply (case_tac c; clarsimp)
   apply (auto)[1]
  apply (case_tac c; clarsimp)
  apply (case_tac b; clarsimp)
  done

lemma clean_ref:  "x \<le> y \<Longrightarrow> \<not> failed_trace x \<Longrightarrow> \<not> failed_trace y  \<Longrightarrow> trace (init x) (clean (tr x)) \<le> trace (init y) (clean (tr y))" 
  apply (clarsimp simp: less_eq_Trace_def)
  apply (erule_tac x=n in allE; clarsimp?)
  apply (case_tac "(index  (tr x) n)"; clarsimp simp: index_clean)
   apply (case_tac "(index  (tr y) n)"; clarsimp simp: index_clean)
   apply (simp add: failed_trace_def)
   apply (case_tac "(index  (tr y) n)"; clarsimp simp: index_clean)
   apply (simp add: failed_trace_def)
  by (metis inf_all_l isr_antitone lengthS_def linorder_linear not_failed_finite_index_iff ref_step.simps(12) sum.disc(2))

lemma non_failed_ref_lengthS: "\<not>failed_trace y \<Longrightarrow> \<not>failed_trace x \<Longrightarrow>  x \<le> y \<Longrightarrow> lengthS (tr x) = lengthS (tr y)" 
  apply (rule lengthS_eqI; clarsimp)
 apply (safe) 
    apply (metis failed_trace_def finiteS_def inf_all_l less_eq_Trace_def not_failed_finite_index_iff ref_term_iff sum.disc(2) sup1CI)
   apply (smt (verit, ccfv_threshold) failed_trace_def inf_all_l isl_iff le_eq_less_or_eq lengthS_def
               less_eq_ref_stepD not_failed_finite_index_iff not_failed_len_le option.sel ref_term_iff sum.disc(2) sup1CI)
  apply (clarsimp simp: linorder_not_less isl_iff)
  apply (drule_tac n=n' in less_eq_ref_stepD)
  apply (clarsimp simp: isl_iff)
  by (metis failed_trace_def isl_iff not_aborted_no_aborts sup1CI verit_comp_simplify1(3))

lemma init_refD: "x \<le> y \<Longrightarrow> init x = init y"   by (clarsimp simp: less_eq_Trace_def)


lemma trace_refI: " init x = init y \<Longrightarrow> (\<And>n. ref_step (index (tr x) n) (index (tr y) n)) \<Longrightarrow>  x \<le> y"
  by (clarsimp simp: less_eq_Trace_def)

lemma Trace_eqI: "init x = init y \<Longrightarrow> (tr x = tr y) \<Longrightarrow> x = y"
  apply (cases x; cases y; clarsimp)
  done

lemma nonfailed_ref: " \<not>failed_trace x \<Longrightarrow> \<not>failed_trace y \<Longrightarrow> x \<le> y \<longleftrightarrow> x = y"
  apply (safe)
  apply (rule Trace_eqI)
   apply (clarsimp simp: init_refD)
  apply (rule trace_eqI)
  apply (drule_tac n=n in less_eq_ref_stepD)
  by (smt (z3) Inr_inject failed_trace_def inf_all_l isr_antitone lengthS_some_finite linorder_le_less_linear
     nless_le not_failed_finite_index_iff option.exhaust_sel ref_incomplete_r ref_step.elims(2) ref_step.simps(10) sum.disc(2) sup1CI symbols.distinct(5))

lemma incomplete_trace_ref_incomplete: "a \<le> b \<Longrightarrow> incomplete_trace b \<Longrightarrow> incomplete_trace a"
  apply (clarsimp simp: incomplete_trace_def, intro conjI)
   apply (metis inf_all_l lengthS_def less_eq_Trace_def ref_incomplete_r sum.disc(2))
  by (smt (verit) index_eq_finished inf_all_l isl_iff isr_antitone less_eq_ref_stepD linorder_linear not_less_iff_gr_or_eq option.exhaust_sel ref_incomplete_r)

lemma lengthS_bottom[simp]: "lengthS (tr (bottom a)) = Some 0"
  apply (cases a; clarsimp)
  done

lemma index_bottom[simp]: "index (tr (bottom a)) n = Inr Incomplete"
  apply (cases a; clarsimp)
  done

lemma [simp]:"incomplete_trace (bottom a)"
  by (clarsimp simp: incomplete_trace_def)

lemma le_bottom_iff[simp]:"(a :: 'a Trace) \<le> bottom b \<longleftrightarrow> a = bottom b"
  apply (safe; clarsimp?)
  apply (rule Trace_eqI)
  using init_refD apply auto[1]
  apply (rule trace_eqI)
  by (simp add: less_eq_Trace_def)

lemma first_neq_ref: "a \<le> b \<Longrightarrow> first_trace a \<noteq> first_trace b \<Longrightarrow> incomplete_trace (first_trace a)"
  apply (clarsimp simp: first_trace_def split: if_splits)
  apply (simp add: init_refD trace_def)
   apply (simp add: bot_eq_iff incomplete_trace_def)
  by (simp add: init_refD)

lemma aborted_trace_iff[simp]: "aborted_trace (Trace x2 (empty_trace c)) \<longleftrightarrow> c = Abort"
    apply (simp add: aborted_trace_def)
  done

lemma incomplete_trace_iff[simp]: "incomplete_trace (Trace x2 (empty_trace c)) \<longleftrightarrow> c = Incomplete"
    apply (simp add: incomplete_trace_def)
  done


lemma failed_trace_empty_trace[simp]: "failed_trace (Trace x2 (empty_trace c)) \<longleftrightarrow> c = Abort \<or> c = Incomplete"
  apply (clarsimp simp: failed_trace_def)
  apply (safe; clarsimp?)
  done



lemma non_failed_finite_not_failed_last: "\<not>failed_trace y \<Longrightarrow> finiteS (tr y) \<Longrightarrow> \<not>failed_trace (last_trace y)" 
  apply (case_tac y; clarsimp)
  apply (clarsimp simp: Let_unfold split: if_splits)
   apply (metis (no_types, lifting) failed_trace_empty_trace last_index_iff lengthS_cons 
  lengthS_def option.simps(3) option.simps(9) symbols.distinct(5) symbols.simps(2) trace_def)
  by (metis diff_add_inverse failed_trace_def finiteS_def index_cons_t inf_all_l lengthS_cons
            less_Suc_eq_0_disj less_numeral_extra(3) not_failed_finite_index_iff option.map_sel
             plus_1_eq_Suc sup1I1 sup1I2 terminates_def tr.simps(1))

lemma inf_append[simp]: "\<not> finiteS t \<Longrightarrow> appendS t t' = t"
  by (metis inf_append_simp inf_is_clean lengthS_def)

lemma ref_join_bot:"trace (init y) (appendS (tr y) (empty_trace Incomplete)) \<le> trace (init y) (appendS (tr y) (tr b))"
  apply (rule trace_refI; clarsimp simp: init_refD)
  apply (case_tac y; clarsimp)
  apply (case_tac "\<exists>m. lengthS (tr y) = Some m"; clarsimp simp: index_append)
  done


lemma seq_trace_mono: "x \<le> y \<Longrightarrow> a \<le> b \<Longrightarrow> seq_trace x a \<le> seq_trace y b"
  apply (clarsimp simp: seq_trace_def, safe)
             apply (drule (2) failed_ref_nonfailed_incomplete)
             apply (erule (1) incomplete_ref)
             apply (clarsimp)
            apply (drule (2) non_fail_ref_failed_aborted)
            apply (erule (1) aborted_ref) 
            apply (simp add: failed_trace_def)
           apply (frule (2) non_failed_ref_lengthS)
           apply (case_tac "lengthS (tr y)"; clarsimp)
            apply (erule (2) clean_ref)
           apply (rule trace_refI; clarsimp simp: init_refD)
           apply (clarsimp simp: index_append)
           apply (intro conjI impI; clarsimp?)
            apply (erule less_eq_ref_stepD)
           apply (erule less_eq_ref_stepD)
          apply (simp add: failed_ref_nonfailed_incomplete incomplete_ref)
  apply (metis aborted_ref failed_trace_def non_fail_ref_failed_aborted sup1CI)
        apply (clarsimp simp: nonfailed_ref) 
        apply (frule (1) first_neq_ref)
        apply (case_tac "finiteS (tr y)")
         apply (metis failed_trace_def non_failed_finite_not_failed_last sup1CI)
        apply (clarsimp)
  using failed_ref_nonfailed_incomplete incomplete_ref apply blast
  apply (metis aborted_ref failed_trace_def non_fail_ref_failed_aborted sup1CI)
     apply (clarsimp simp: nonfailed_ref) 
     apply (rule ref_join_bot)
  using failed_ref_nonfailed_incomplete incomplete_ref apply blast
  apply (metis aborted_ref failed_trace_def non_fail_ref_failed_aborted sup1CI)
  using nonfailed_ref by auto


lemma failed_trace_seq[simp]: "failed_trace a \<Longrightarrow> seq_trace a b = a"
  apply (clarsimp simp: seq_trace_def)
  done

lemma non_failed_trace_eq[simp]:"\<not> failed_trace a \<Longrightarrow> trace (init a) (tr a) = a"
  by (case_tac a; clarsimp simp: trace_def)

lemma infinite_seq[simp]:"\<not>finiteS (tr a) \<Longrightarrow> seq_trace a b = a"
  apply (clarsimp simp: seq_trace_def)
  done

lemma first_trace_Trace[simp]:"first_trace (Trace x t) = (Trace x (empty_trace Term))"
  by (clarsimp simp: first_trace_def trace_def)

lemma failed_seq_trace_iff: "finiteS (tr a) \<Longrightarrow> \<not>failed_trace a \<Longrightarrow> last_trace a = first_trace b \<Longrightarrow> failed_trace (seq_trace a b) \<longleftrightarrow> failed_trace b"
  apply (safe; clarsimp simp: seq_trace_def)
   apply (clarsimp simp: failed_trace_def)
   apply (elim disjE)
    apply (clarsimp simp: incomplete_trace_def)
  apply (case_tac a; clarsimp)
    apply (smt (verit) coerce_le diff_add_inverse finiteS_append_iff index_append isl_iff lengthS_append_eq lengthS_def option.sel sum.disc(2))
   apply (clarsimp simp: incomplete_trace_def)
   apply (subst (asm) aborted_trace_def, clarsimp)+
  apply (case_tac a; clarsimp)

   apply (smt (verit, best) aborted_end index_append isl_coerce isl_iff lengthS_def not_aborted_no_aborts sum.disc(2))
  apply (clarsimp simp: failed_trace_def)
  apply (clarsimp simp: incomplete_trace_def)
  apply (subst (asm) aborted_trace_def, clarsimp)+
  apply (case_tac a; clarsimp)
  apply (clarsimp simp: Let_unfold split: if_splits)
  apply (elim disjE; clarsimp?)
    apply (smt (verit, del_insts) coerce_le diff_add_inverse finiteS_append_iff index_append isl_iff lengthS_append_eq lengthS_def nless_le option.sel)
   apply (smt (verit, ccfv_threshold) aborted_trace_def coerce_le diff_add_inverse finiteS_append_iff index_append isl_iff lengthS_append_eq lengthS_def option.sel order.strict_iff_order)
  apply (case_tac b; clarsimp)
  by (smt (verit, ccfv_threshold) diff_add_inverse incomplete_trace_def incomplete_trace_empty index_append lengthS_append_eq lengthS_def not_add_less1 option.sel tr.simps(2))

lemma non_matching_fails: "finiteS (tr a) \<Longrightarrow> last_trace a \<noteq> first_trace b \<Longrightarrow> failed_trace (seq_trace a b)"
  apply (clarsimp simp: failed_trace_def)
  apply (clarsimp simp: seq_trace_def split: if_splits)
   apply (clarsimp simp: failed_trace_def)
  apply (subgoal_tac "\<exists>m. lengthS (tr a) = Some m", clarsimp)
   apply (smt (z3) bottom_Trace.simps(2) coerce_le finiteS_append_iff incomplete_trace_def incomplete_trace_empty index_append index_bottom isl_iff lengthS_some_finite not_failed_finite_index_iff sum.disc(2) tr.simps(1) tr.simps(2) trace_def)
  by (meson lengthS_def)

lemma bottom_trace_iff[simp]: "bottom (trace a t) = trace a (empty_trace Incomplete)"
  by (case_tac a; clarsimp simp: trace_def)

lemma non_failed_trace_eq_iff:"\<not> failed_trace a \<Longrightarrow> trace (init a) b = trace a' b' \<longleftrightarrow> (init a) = a' \<and> b = b'"
  apply (case_tac a; clarsimp simp: trace_def)
  done

lemma appendS_eq_empty_iff: " appendS t t' = empty_trace c \<longleftrightarrow> (\<exists>c'. (t = empty_trace c') \<and> t' = empty_trace c)"
  apply (safe; clarsimp)
  apply (intro conjI)
   apply (metis first_None_iff' first_appendS lengthS_empty lengthS_zero_empty_trace option.simps(3))
  by (metis first_None_iff' first_appendS lengthS_empty length_zero_append option.distinct(1))


lemma trace_None_simp[simp]: "trace None t = Empty"
  by (clarsimp simp: trace_def)

lemma first_trace_seq:" first_trace (seq_trace a b) = first_trace a" 
  apply (clarsimp simp: seq_trace_def; clarsimp?)
   apply (clarsimp simp: first_trace_def split: if_splits)
(*   apply (intro conjI impI; (clarsimp simp: non_failed_trace_eq_iff appendS_eq_empty_iff)?)
  apply (clarsimp)
   apply (metis bot_eq_iff non_failed_trace_eq)
  oops *)
  by (metis init_trace trace_None_simp)
 


  
lemma matching_nonfailed_seq_iff: "\<not>failed_trace a \<Longrightarrow> last_trace a = first_trace b  \<Longrightarrow> seq_trace a b = trace (init a) (appendS (tr a) (tr b))"
  apply (clarsimp simp: seq_trace_def)
  done

lemma trace_Some_simp[simp]: "trace (Some a) t = Trace a t"
  by (clarsimp simp: trace_def)



lemma first_nonfailed_simp[simp]: "~failed_trace (Trace a t) ==> first_trace (Trace a t) = Trace a (empty_trace Term)"
  by (clarsimp simp: failed_trace_def first_trace_def)


lemma first_not_bot_simp[simp]: "(Trace a t) \<noteq> bottom (Trace a t) ==> first_trace (Trace a t) = Trace a (empty_trace Term)"
  apply (clarsimp simp: failed_trace_def first_trace_def)
  done


lemma empty_first_trace_iff: "Empty = first_trace b \<longleftrightarrow> b = Empty"
  apply (clarsimp simp: first_trace_def)
   apply (clarsimp simp: trace_def split: if_splits)
   apply (metis init.simps(1) last_trace.cases option.simps(3))
  done

lemma length_cons_someI[intro]:"lengthS (xs) = Some n \<Longrightarrow> lengthS (cons_t x xs) = Some (Suc n)"
  by (simp add: lengthS_cons)


lemma length_cons_none_iff[simp]:"lengthS (cons_t x xs) = None \<longleftrightarrow> lengthS xs = None"
  by (simp add: lengthS_cons)

lemma clean_const_iff[simp]:"clean (cons_t x xs) = cons_t x (clean xs)"
    apply (rule trace_eqI)
  apply (clarsimp simp: index_cons_t, safe)
   apply (simp add: index_clean index_cons_t)
  apply (simp add: index_clean index_cons_t)
  done

lemma cons_t_appendS_shift: "cons_t x (appendS xs ys) = appendS (cons_t x xs) ys"
  apply (rule trace_eqI)
  apply (case_tac "\<exists>m. lengthS xs = Some m"; case_tac "\<exists>m'. lengthS ys = Some m'"; clarsimp simp: index_append) 
   apply (subst index_append, fastforce)
   apply (clarsimp simp: index_cons_t, safe; clarsimp simp: index_append)
    apply linarith
   apply linarith
  apply (subst index_append, fastforce)
   apply (clarsimp simp: index_cons_t, safe; clarsimp simp: index_append)
   apply (linarith)
  apply (linarith)
  done


lemma term_is_lastI: "terminates (tr b) \<Longrightarrow> lengthS (tr b) = Some (Suc n) \<Longrightarrow> index (tr b) n = Inl s \<Longrightarrow> (Trace (state_of s) (empty_trace Term)) = last_trace b"  
  apply (case_tac b; clarsimp simp: Let_unfold split: option.splits if_splits)
   apply (simp add: last_index_iff lengthS_cons)
  apply (simp add: index_cons_t last_index_iff lengthS_cons)
  by (simp add: index_cons_t lengthS_cons terminates_def)

thm last_index_iff

lemma last_appendS: "finiteS (tr a) \<Longrightarrow> last_trace a = first_trace b \<Longrightarrow>
      last_trace (trace (init a) (appendS (tr a) (tr b))) = last_trace b" 
  apply (cases a; clarsimp simp: Let_unfold empty_first_trace_iff split: option.splits if_splits)
   apply ( intro conjI impI; (clarsimp split: sum.splits option.splits)?)
  sorry
 (*  oops
     apply (intro conjI impI)
       apply (smt (verit) cons_t_def last_index_iff lengthS_cons lengthS_def 
                          option.map(2) option.simps(3) terminates_def)
      apply (metis Traces.last_def add_diff_inverse_nat diff_is_0_eq finiteS_cons index_cons_t inf_all_l 
                  last_index_iff nless_le option.exhaust_sel option.simps(3) plus_1_eq_Suc sum.case_eq_if
                  sum.disc(1) terminates_def)
     apply (intro conjI impI)
          apply (metis Traces.last_def add_diff_inverse_nat diff_is_0_eq finiteS_cons index_cons_t inf_all_l 
   last_index_iff le_eq_less_or_eq option.exhaust_sel option.simps(3) plus_1_eq_Suc sum.case_eq_if sum.disc(1) terminates_def)
    apply (intro conjI impI allI; clarsimp simp: cons_t_appendS_shift)
    apply (case_tac "\<exists>m. lengthS (tr b) = Some m", clarsimp)
  sorry *)


lemma first_glue_traces: " first_trace b = first_trace (trace (init b) (appendS (tr b) (tr c)))"
  by (cases b; clarsimp simp: empty_first_trace_iff)


lemma non_failed_notmatching_seq: "\<not>failed_trace b \<Longrightarrow> \<not>first_trace c = last_trace b \<Longrightarrow> seq_trace b c = (trace (init b) (appendS (tr b) (empty_trace Incomplete)))"
  by (clarsimp simp: seq_trace_def)

lemma seq_assoc: "seq_trace a (seq_trace b c) \<le> seq_trace (seq_trace a b) c"
  apply (case_tac "failed_trace a"; clarsimp?)
  apply (case_tac "finiteS (tr a)"; clarsimp?)
  apply (case_tac "failed_trace b"; clarsimp?)
   apply (case_tac "last_trace a = first_trace b")
    apply (clarsimp simp: failed_seq_trace_iff)
   apply (clarsimp simp: non_matching_fails)
  apply (case_tac "finiteS (tr b)"; clarsimp?)
   apply (case_tac "last_trace a = first_trace b"; clarsimp?)
    apply (case_tac "last_trace b = first_trace c"; clarsimp?)
     apply (clarsimp simp: matching_nonfailed_seq_iff last_appendS)
     apply (subst matching_nonfailed_seq_iff) back
       apply (metis failed_seq_trace_iff matching_nonfailed_seq_iff)
      apply (clarsimp simp: last_appendS)
     apply (clarsimp)
     apply (subst matching_nonfailed_seq_iff; clarsimp?) 
      apply (clarsimp simp: first_glue_traces)
     apply (clarsimp simp: appendS_assoc)
    apply (clarsimp simp: non_failed_notmatching_seq)
  apply (smt (verit) appendS_assoc dual_order.refl failed_seq_trace_iff init_trace last_appendS non_failed_notmatching_seq not_failed_case_option_init ref_join_bot seq_trace_def tr_trace)
    apply (case_tac "last_trace b = first_trace c"; clarsimp?)
    apply (metis dual_order.refl failed_trace_seq first_glue_traces matching_nonfailed_seq_iff non_failed_notmatching_seq non_matching_fails)
   apply (smt (z3) bot_eq_iff dual_order.refl failed_trace_def first_trace_def incomplete_trace_def incomplete_trace_empty init_trace non_matching_fails seq_trace_def sup1I1 tr.simps(2))
  by (metis dual_order.refl failed_trace_seq finiteS_append_iff infinite_seq matching_nonfailed_seq_iff non_matching_fails not_failed_has_init tr.simps(1) trace_Some_simp)


lemma seq_assoc': "seq_trace a (seq_trace b c) \<ge> seq_trace (seq_trace a b) c"
  apply (case_tac "failed_trace a"; clarsimp?)
  apply (case_tac "finiteS (tr a)"; clarsimp?)
  apply (case_tac "failed_trace b"; clarsimp?)
   apply (case_tac "last_trace a = first_trace b")
    apply (clarsimp simp: failed_seq_trace_iff)
   apply (clarsimp simp: non_matching_fails)
  apply (case_tac "finiteS (tr b)"; clarsimp?)
   apply (case_tac "last_trace a = first_trace b"; clarsimp?)
    apply (case_tac "last_trace b = first_trace c"; clarsimp?)
     apply (smt (z3) appendS_assoc dual_order.refl failed_seq_trace_iff first_glue_traces init_trace last_appendS not_failed_has_init seq_trace_def tr.simps(1) trace_Some_simp)
  apply (smt (verit) appendS_assoc failed_seq_trace_iff first_trace_seq last_appendS non_failed_trace_eq non_failed_trace_eq_iff option.case_eq_if seq_assoc seq_trace_def tr_trace)
   apply (smt (z3) non_matching_fails ref_join_bot seq_trace_def tr.simps(2))
  by (metis dual_order.refl failed_trace_seq finiteS_append_iff infinite_seq matching_nonfailed_seq_iff non_matching_fails not_failed_has_init tr.simps(1) trace_Some_simp)

lemma failed_bottom[simp]: "failed_trace (bottom x)"
  by (clarsimp simp: failed_trace_def)
 


interpretation ordered_semigroup seq_trace
  apply (standard)
     apply (erule (1) seq_trace_mono)
    apply (rule seq_assoc)
   apply (rule seq_assoc')
  apply (clarsimp)
  done

lemma first_empty[simp]: "first_trace Empty = Empty"
  by (clarsimp simp: first_trace_def)

lemma terminates_cons_t[simp]: "terminates (cons_t s t) = terminates t"
  by (metis Zero_neq_Suc diff_add_inverse finiteS_cons index_cons_t lengthS_def
            length_cons_someI option.sel plus_1_eq_Suc terminates_def)

lemma last_first_last[simp]: "last_trace (first_trace a) = first_trace a"
  by (case_tac a; clarsimp simp: Let_unfold split: if_splits)

lemma first_last_last[simp]: "first_trace (last_trace a) = last_trace a"
  apply (case_tac a; clarsimp simp: Let_unfold split: if_splits)
  by (clarsimp simp: first_trace_def  )

 
lemma failed_first_iff: "failed_trace (first_trace a) \<longleftrightarrow> (a = Empty)"
  by (case_tac a; clarsimp)

lemma seq_first_idemp: "a \<le> seq_trace (first_trace a) a"
  apply (case_tac a; clarsimp)
  by (clarsimp simp: seq_trace_def failed_first_iff )

lemma Empty_le_iff[simp]: "Empty \<le> c \<longleftrightarrow> c = Empty"
  by (clarsimp simp: less_eq_Trace_def, case_tac c; clarsimp)

lemma trace_init_empty_iff[simp]: "trace (init b) t  = Empty \<longleftrightarrow> b = Empty"
  by (cases b; clarsimp simp: trace_def)

lemma first_least: " a \<le> seq_trace (Trace t (empty_trace Term)) a \<Longrightarrow> first_trace a \<le> (Trace t (empty_trace Term))" 
  apply (case_tac a; clarsimp)
  apply (rule trace_refI)
     apply (clarsimp)
  apply (metis init.simps(1) init_refD init_trace option.inject seq_trace_def)
   apply (simp add: init_refD )
  by (clarsimp simp: seq_trace_def split: option.splits if_splits)
 
 

lemma seq_match_or_fail: "x \<le> seq_trace (first_trace a) b \<Longrightarrow> x \<le> b \<or> x \<le> a\<^sub>\<bottom>"
  apply (case_tac a; clarsimp)
  apply (clarsimp simp: seq_trace_def failed_first_iff split: if_splits)
  apply (clarsimp simp: first_trace_def split: if_splits option.splits)
  by (metis init.simps(1) init_trace less_eq_Trace_def tr.simps(1))


definition "abort_from s = trace (init s) (empty_trace Abort)"

lemma failed_abort_from[simp]: "failed_trace (abort_from c)"
  apply (case_tac c; clarsimp simp: abort_from_def)
  done

lemma last_cons_t_none_inf[simp]: "Traces.last (cons_t  b bs) = None \<longleftrightarrow> \<not>finiteS (bs)"
  apply (clarsimp simp: last_def)
  by (metis One_nat_def Suc_pred Traces.last_def finiteS_cons index_cons_t isl_iff last_index_iff lengthS_def option.sel sum.disc(1))

lemma ref_trace_iff: "Trace x s \<le> Trace x s' \<longleftrightarrow> (\<forall>n. ref_step (index s n) (index s' n))"
  by (clarsimp simp: less_eq_Trace_def)

lemma empty_inj[simp]: "empty_trace c = empty_trace d \<longleftrightarrow> c = d"
  apply (safe; clarsimp?)
  by (metis Inr_inject index_empty)

lemma ref_step_index_append_incomplete[simp]: "ref_step (index (appendS t (empty_trace Incomplete)) n) (index t n)"
  apply (case_tac "\<exists>m. lengthS t = Some m"; clarsimp simp: index_append)
  by (metis inf_is_clean)


lemma ref_step_index_append_term[simp]: "terminates t \<Longrightarrow> ref_step (index (appendS t (empty_trace Term)) n) (index t n)"
  apply (case_tac "\<exists>m. lengthS t = Some m"; clarsimp simp: index_append)
  apply (metis isr_antitone linorder_le_less_linear option.sel terminates_def)
  by (metis inf_is_clean)


lemma ref_step_index_append_term'[simp]: "terminates t \<Longrightarrow> ref_step (index t n) (index (appendS t (empty_trace Term)) n) "
  apply (case_tac "\<exists>m. lengthS t = Some m"; clarsimp simp: index_append)
  apply (metis isr_antitone linorder_le_less_linear option.sel ref_step_refl terminates_def)
  by (metis inf_is_clean)

lemma seq_last_le: "seq_trace b (last_trace a) \<le> b"
  apply (case_tac a; case_tac b; clarsimp)
  apply (clarsimp simp: seq_trace_def  split: option.splits)
   apply (safe; (clarsimp simp: ref_trace_iff)?)
  apply (clarsimp simp: seq_trace_def)
  by (clarsimp simp: ref_trace_iff)

lemma first_trace_incomplete[simp]: "first_trace (Trace s (empty_trace Incomplete)) = Trace s (empty_trace Term)"
  by (clarsimp simp: first_trace_def)
 

lemma last_trace_seq_unit: "b \<le> seq_trace b (last_trace b)"
  apply (case_tac b; clarsimp)
  apply (clarsimp simp: seq_trace_def)
  apply (clarsimp simp:  split: option.splits)
  apply (intro conjI impI; clarsimp?)
   apply (clarsimp simp: ref_trace_iff)
  apply (clarsimp simp: ref_trace_iff)
  by (metis failed_trace_def last_cons_t_none_inf not_failed_finite_index_iff
            option.simps(3) sup1I1 sup1I2 terminates_def tr.simps(1))

lemma bottom_idemp[simp]: " bottom (bottom x) = bottom (x :: 'a Trace)"
  by (cases x; clarsimp)

lemma ref_step_abort[simp]: "ref_step s (Inr Abort)"
  apply (cases s; clarsimp)
  by (case_tac b; clarsimp)

lemma le_abort_from: "x \<le> abort_from x"
  apply (cases x; clarsimp simp: abort_from_def)
  by (clarsimp simp: ref_trace_iff)

lemma "first_trace (Trace t (empty_trace Term)) \<le> Trace t (empty_trace Term)"
  apply (clarsimp)
  done

interpretation seq_elem seq_trace last_trace "(\<lambda>c. Trace c (empty_trace Term))" first_trace
  apply (standard)
              apply (erule (1) seq_trace_mono)
             apply (rule seq_assoc')
    apply (rule seq_assoc)
           apply (clarsimp)
          apply (intro iffI)
           apply (rule order_trans[rotated])
            apply (rule seq_trace_mono, assumption, rule order_refl)
           apply (rule seq_first_idemp)
          apply (erule  first_least)
         apply (erule seq_match_or_fail)
        apply (rule seq_first_idemp)
       apply (clarsimp simp: first_trace_def)
        apply (simp add: trace_refI)
  apply (clarsimp)
      apply (rule_tac x="abort_from x" in exI)
      apply (intro conjI)
  apply (rule le_abort_from)
      apply (case_tac x; clarsimp simp: abort_from_def)
      apply (clarsimp simp: ref_trace_iff)
      apply (case_tac x; clarsimp simp: )
    apply (rule seq_last_le)
   apply (rule last_trace_seq_unit)
  apply (rule set_eqI; clarsimp simp: image_iff)
  apply (intro iffI; clarsimp?) 
  
   apply (metis first_last_last)
  by (metis last_first_last)

lemma case_last_simp[simp]: "(case Traces.last (cons_t t ts) of None \<Rightarrow> P t ts | Some s \<Rightarrow> Q t ts s) = (if finiteS ts then Q t ts (the (last (cons_t t ts))) else P t ts)" 
  apply (clarsimp split: option.splits)
  by (metis last_cons_t_none_inf option.simps(3))

lemma init_bottom_simp[simp]: "init (bottom y) = init y"
  by (cases y; clarsimp)

lemma init_first_simp[simp]:" init (first_trace y) = init y"
  apply (clarsimp simp: first_trace_def)
  done

lemma terminates_finite[simp]: "terminates x \<Longrightarrow> \<not>finiteS x = False"
  by (meson terminates_def)

thm seq_trace_def

lemma first_le_last_cases: "first_trace y \<le> last_trace x \<Longrightarrow> first_trace y = last_trace x "
  apply (clarsimp simp: first_trace_def split: if_splits)
  by (metis first_last_last first_trace_def init_refD init_trace trace_init_empty_iff)
  oops
  by (metis failed_first_iff first_last_last last_first_last le_bottom_iff nonfailed_ref)

lemma first_last_matching: "first_trace y \<le> last_trace x \<Longrightarrow> last_trace y \<le> last_trace (seq_trace x y)"
  apply (frule first_le_last_cases, clarsimp?)
  apply (case_tac "failed_trace x"; clarsimp?)
   apply (cases x; cases y; clarsimp split: if_splits)
  apply (intro conjI; clarsimp)
    apply (metis Inr_inject aborted_trace_def failed_trace_def incomplete_trace_def ref_incomplete_r
                 ref_step.simps(10) sup1E symbols.distinct(5) terminates_def tr.simps(1))
  apply (metis aborted_end failed_trace_def incomplete_index_len sum.simps(2) sup1E symbols.simps(2) symbols.simps(6) terminates_def tr.simps(1))
   apply (case_tac "finiteS (tr x)"; clarsimp?)
    apply (subst matching_nonfailed_seq_iff; clarsimp?)
   apply (simp add: last_appendS)
  by (smt (verit, best) Empty_le_iff empty_first_trace_iff finiteS_cons last_trace.elims last_trace.simps(1) terminates_finite tr.simps(1))


interpretation test_seq seq_trace last_trace "(\<lambda>c. Trace c (empty_trace Term))" first_trace
  apply (standard)
      apply (safe)[1]
        apply (clarsimp simp: image_iff)
        apply (rule_tac x="Trace c (empty_trace Term)" in exI, clarsimp)
  apply (metis bot_eq_iff bottom_idemp empty_inj in_omega le_bottom_iff symbols.distinct(5) tr.simps(1))

      apply (clarsimp simp: image_iff)
  apply (metis bottom_Trace.simps(2) first_trace_def trace_def)
     apply (clarsimp)
  apply (metis append_empty bottom_trace_iff failed_ref_nonfailed_incomplete failed_trace_empty_trace incomplete_ref le_bottom_iff nonfailed_ref symbols.distinct(1) symbols.distinct(5) tr.simps(1))
    apply (simp add: nonfailed_ref)
  apply (metis first_trace_def less_eq_Trace_def order_refl trace_init_empty_iff)
  by (simp add: first_last_matching)


fun sync_step where
 "sync_step f (Inl x)    (Inl y) = f x y" |
 "sync_step f (Inr Term) (Inl y) = Inr (Incomplete)" |
 "sync_step f (Inl y) (Inr Term) = Inr (Incomplete)" |
 "sync_step f (Inr Abort) y = (Inr Abort)" | 
 "sync_step f x (Inr Abort) = (Inr Abort)" | 
 "sync_step f x (Inr Incomplete) = Inr Incomplete" |
 "sync_step f (Inr Incomplete) y = Inr Incomplete" |
 "sync_step f x y = x"

definition "sync_trace f c d = zip_trace' (sync_step f) c d "

fun par_sync where
 "par_sync (Env x) (Env y) = (if x = y then Inl (Env x) else Inr Incomplete)" |
 "par_sync (Env x) (Pgm y) = (if x = y then Inl (Pgm x) else Inr Incomplete)" |
 "par_sync (Pgm x) (Env y) = (if x = y then Inl (Pgm x) else Inr Incomplete)" |
 "par_sync _ _ = Inr Incomplete"


definition "conj_sync x y = (if x = y then Inl x else Inr Incomplete)" 

definition "par_t x y = (if init x = init y then trace (init x) (sync_trace par_sync (tr x) (tr y)) else Empty)"


definition "conj_t x y = (if init x = init y then trace (init x) (sync_trace conj_sync (tr x) (tr y)) else Empty)"

definition "regular t = (if \<not>failed_trace t then t else trace (init t) (appendS (tr t) (empty_trace Incomplete)))"

definition "fmap_trace f g t \<equiv> liftF (\<lambda>n. map_sum f g (index t n))"

lemma index_fmap: "index (fmap_trace f g t) n = map_sum f g (index t n)"
  apply (clarsimp simp: fmap_trace_def)
  apply (subst index_liftF; clarsimp?)
  apply (clarsimp simp: traceDom_def)
  by (metis dual_order.refl index_eq_finished isl_map_sum)

lemma fmap_trace_comp: "fmap_trace f g (fmap_trace f' g' t) = fmap_trace (f o f') (g o g') t"
  apply (rule trace_eqI; clarsimp simp: index_fmap)
  apply (case_tac "index t n"; clarsimp)
  done


fun proj_sym where
        "proj_sym Term = Term" |
        "proj_sym Abort = Incomplete" |
        "proj_sym Incomplete = Incomplete"

fun env :: "'a Trace \<Rightarrow> 'a Trace" and proj_env :: "'a Step \<Rightarrow> 'a Step" 
  where "env Empty = Empty" |
        "env (Trace s t) = (Trace s (fmap_trace proj_env proj_sym t)) " |
        "proj_env (Pgm x) = (Env x)" |
        "proj_env (Env x) = (Env x)" 



lemma conj_sync_idemp[simp]:"conj_sync x x = Inl x"
  apply (clarsimp simp: conj_sync_def)
  done

lemma ref_inlD[simp, dest]: "x \<le> y \<Longrightarrow> index (tr x) n = Inl a \<Longrightarrow> index (tr y) n = Inl b \<Longrightarrow> a = b"
  by (metis less_eq_ref_stepD ref_step.simps(1))


lemma ref_inl_inrD[simp, dest]: "x \<le> y \<Longrightarrow> index (tr x) n = Inl a \<Longrightarrow> index (tr y) n = Inr b \<Longrightarrow> b = Abort"
  by (metis Inl_Inr_False isl_c_ref_iff less_eq_Trace_def sum.disc(1) sum.inject(2))


lemma ref_inr_inlD[simp, dest]: "x \<le> y \<Longrightarrow> index (tr x) n = Inr a \<Longrightarrow> index (tr y) n = Inl b \<Longrightarrow> a = Incomplete"
  by (metis (full_types) less_eq_ref_stepD old.sum.distinct(2) ref_step.simps(12) ref_step.simps(6) symbols.exhaust)


lemma ref_inr_inl_iff[simp]: "ref_step (Inr ba) (Inl aa) \<longleftrightarrow> ba = Incomplete"
  apply (safe)
   apply (case_tac ba; clarsimp)
  apply (clarsimp)
  done

lemma sync_incomplete: "sync_step f (Inr Incomplete) (Inr x) = (if x = Abort then (Inr x) else (Inr Incomplete))"
  by (case_tac x; clarsimp)

lemma sync_incomplete': "sync_step f  (Inr x) (Inr Incomplete) = (if x = Abort then (Inr x) else (Inr Incomplete))"
  by (case_tac x; clarsimp)

lemma sync_step_conj_mono: "x \<le> y \<Longrightarrow> a \<le> b \<Longrightarrow> ref_step (sync_step conj_sync (index (tr x) n) (index (tr a) n)) (sync_step conj_sync (index (tr y) n) (index (tr b) n))" 
  apply (drule less_eq_ref_stepD[where n=n])
  
  apply (drule less_eq_ref_stepD[where n=n]) back
  apply (case_tac "index (tr x) n"; case_tac "index (tr a) n"; case_tac "index (tr y) n"; case_tac "index (tr b) n"; clarsimp)
       apply (case_tac ba; clarsimp)
    apply (case_tac ba; clarsimp)
    apply (case_tac ba; clarsimp)
    apply (case_tac ba; clarsimp)
    apply (case_tac ba; clarsimp)
  by (smt (z3) ref_step.simps(10) ref_step.simps(7) ref_step_abort symbols.exhaust sync_step.simps(10) 
               sync_step.simps(12) sync_step.simps(13) sync_step.simps(4) sync_step.simps(6) sync_step.simps(7) sync_step.simps(9))

lemma ref_step_sync_trace_conj_mono: "x \<le> y \<Longrightarrow> a \<le> b \<Longrightarrow> init y = init b \<Longrightarrow> ref_step (index (sync_trace conj_sync (tr x) (tr a)) n) (index (sync_trace conj_sync (tr y) (tr b)) n)"
  apply (induct n; (clarsimp simp: sync_trace_def zip_trace'_def)?)
  apply (erule (1) sync_step_conj_mono)
           apply (clarsimp split: sum.splits, intro conjI impI)
    apply (clarsimp)
  apply (erule (1) sync_step_conj_mono)
   apply (clarsimp)
   apply (simp add: foldrF_def foldr_traceDom index_liftF isl_c_ref_iff
              ref_step_abort sum.disc(1) sum.simps(4))
  apply (clarsimp)
  apply (intro conjI impI allI; clarsimp?)
   apply (simp add: foldrF_def)
  by (simp add: foldrF_def)


lemma conj_t_mono: "x \<le> y \<Longrightarrow> a \<le> b \<Longrightarrow> conj_t x a \<le> conj_t y b"
  apply (clarsimp simp: conj_t_def, safe; clarsimp simp: init_refD)
  apply (rule trace_refI; clarsimp)
  apply (cases "init b")
   apply (simp)
  apply (simp)
  apply (erule (1) ref_step_sync_trace_conj_mono, clarsimp)
  done

lemma tr_some_bot[simp]: "tr (SOME x. \<exists>y. x = bottom y) = empty_trace Incomplete"
oops


lemma sync_assoc: "sync_step conj_sync a (sync_step conj_sync b c) = sync_step conj_sync  (sync_step conj_sync a b) c"
  apply (cases a; cases b; cases c; clarsimp simp: conj_sync_def split: if_splits)
        apply (safe; (clarsimp simp: conj_sync_def)?)+
         apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
      apply (case_tac ba; clarsimp)
       apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
   apply (case_tac ba; clarsimp)
    apply (case_tac bb; clarsimp)
  apply (case_tac bb; clarsimp)
  apply (case_tac bb; clarsimp)
   apply (case_tac ba; clarsimp)
   apply (case_tac ba; clarsimp)
   apply (case_tac ba; clarsimp)
  done

lemma index_zip_trace_failed: "index (zip_trace' f x y) n = Inr c \<Longrightarrow> index (zip_trace' f x y) (Suc n) = Inr c"
  by auto

lemma index_zip_trace_success: "index (zip_trace' f x y) n = Inl c \<Longrightarrow> index (zip_trace' f x y) (Suc n) = f (index x (Suc n)) (index y (Suc n))"
  apply (clarsimp simp: zip_trace'_def split: sum.splits)
  by (clarsimp simp: foldrF_def)

lemma index_zip_trace_inlD: "index (zip_trace' f x y) n = Inl s \<Longrightarrow> f (index x n) (index y n) = Inl s "
  apply (induct n; clarsimp?)
   apply (clarsimp simp: zip_trace'_def)
  by (clarsimp simp: zip_trace'_def split: sum.splits)

lemma sync_inl_iff:"sync_step conj_sync a b = Inl c \<longleftrightarrow>  a = Inl c \<and> b = Inl c"
  apply (case_tac a; case_tac b; clarsimp simp: conj_sync_def)
    apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  done



lemma index_zip_trace_assoc: "index (zip_trace' (sync_step conj_sync) a (zip_trace' (sync_step conj_sync) b c)) n = index (zip_trace' (sync_step conj_sync) (zip_trace' (sync_step conj_sync) a b) c) n" 
  apply (induct n, clarsimp simp: zip_trace'_def)
   apply (rule sync_assoc)
  apply (case_tac "index (zip_trace' (sync_step conj_sync) a (zip_trace' (sync_step conj_sync) b c)) n")
  apply (subst index_zip_trace_success, assumption)
   apply (clarsimp simp: index_zip_trace_success)
   apply (subst index_zip_trace_success, erule sym)
   apply (drule sym)
  apply (clarsimp)
   apply (drule index_zip_trace_inlD)+
   apply (clarsimp simp: sync_inl_iff)
   apply (subst index_zip_trace_success, assumption)
apply (subst index_zip_trace_success, assumption)
  using sync_assoc apply blast
  apply (clarsimp simp: index_zip_trace_failed)
  apply (drule sym, clarsimp)
  apply (clarsimp simp: index_zip_trace_failed)
  done

  


lemma sync_trace_conj_assoc: "sync_trace conj_sync a (sync_trace conj_sync b c)= sync_trace conj_sync (sync_trace conj_sync a b) c "
  apply (rule trace_eqI)
  apply (clarsimp simp: sync_trace_def)
  apply (simp add: index_zip_trace_assoc)
  done

lemma conj_t_assoc: "conj_t a (conj_t b c) \<le> conj_t (conj_t a b) c" 
  apply (clarsimp simp: conj_t_def, safe, clarsimp?)
       apply (metis trace_None_simp trace_init_empty_iff)
      apply (cases c; clarsimp simp: sync_trace_conj_assoc)
     apply (cases c; clarsimp simp: sync_trace_conj_assoc)
    apply auto[1]
   apply (metis trace_None_simp trace_init_empty_iff)
  apply (metis trace_None_simp trace_init_empty_iff)
  done

lemma conj_t_assoc': "conj_t a (conj_t b c) \<ge> conj_t (conj_t a b) c" 
  apply (clarsimp simp: conj_t_def, safe, clarsimp?)
      apply (cases c; clarsimp simp: sync_trace_conj_assoc)
     apply (cases c; clarsimp simp: sync_trace_conj_assoc)
  done

lemma index_immediate_sync_trace: "index t 0 = Inr c \<Longrightarrow> index t' 0 = Inr d \<Longrightarrow> sync_trace f t t' = empty_trace (projr (sync_step f (Inr c) (Inr d)))"
  apply (rule trace_eqI)
  apply (induct_tac n; clarsimp)
   apply (clarsimp simp: sync_trace_def)
   apply (clarsimp simp: zip_trace'_def)
   apply (cases c; cases d; clarsimp)
  by (simp add: index_zip_trace_failed sync_trace_def)

lemma sync_bottom:"sync_trace f (tr (bottom x)) (tr (bottom x)) = (tr (bottom x))"
  apply (subst index_immediate_sync_trace, clarsimp, rule refl)
   apply (clarsimp, rule refl)
  apply (clarsimp)
  apply (rule trace_eqI; clarsimp)
  done

lemma index_zip_trace'_zero[simp]: "index (zip_trace' f t t') 0 = f (index t 0) (index t' 0)"
  by (clarsimp simp: zip_trace'_def)

lemma sync_trace_conj_idemp[simp]: "sync_trace conj_sync t t = t"
  apply (rule trace_eqI)
  apply (induct_tac n; clarsimp)
   apply (clarsimp simp: sync_trace_def)
   apply (case_tac "index t 0"; clarsimp)
   apply (case_tac b; clarsimp)
  apply (case_tac "index (sync_trace conj_sync t t) na")
   apply (clarsimp)
   apply (drule sym, clarsimp)
   apply (smt (verit, ccfv_threshold) index_zip_trace_success old.sum.exhaust symbols.exhaust sync_inl_iff sync_step.simps(10) sync_step.simps(13) sync_step.simps(4) sync_trace_def)
  apply (clarsimp)
    apply (drule sym, clarsimp)
  by (metis isr_antitone le_add2 plus_1_eq_Suc)

lemma conj_t_idemp: "a \<le> conj_t a a"
  apply (clarsimp simp: conj_t_def)
  apply (rule trace_refI, clarsimp)
  by (cases a; clarsimp )

lemma conj_t_empty[simp]: "conj_t Empty c = Empty"
  by (clarsimp simp: conj_t_def)


lemma conj_t_empty'[simp]: "conj_t c Empty  = Empty"
  by (clarsimp simp: conj_t_def)

lemma [simp]: "sync_step conj_sync a a = a"
  apply (cases a; clarsimp)
  by (case_tac b; clarsimp)


declare linorder_not_less[simp]

lemma failed_trace_has_lengthD: "failed_trace (Trace x t) \<Longrightarrow> \<exists>m. lengthS t = Some m"
  by (metis aborted_trace_def failed_trace_def incomplete_trace_def lengthS_def sup1E tr.simps(1))

lemma failed_conj_incomplete_ref: "failed_trace (Trace x t) \<Longrightarrow> ref_step (index t n) (index (sync_trace conj_sync t (appendS t (empty_trace Incomplete))) n)"
  apply (induct n; clarsimp?)
   apply (clarsimp simp: sync_trace_def)
   apply (subgoal_tac "\<exists>m. lengthS t = Some m", clarsimp simp: index_append)
    apply (metis failed_trace_empty_trace index_empty lengthS_zero_empty_trace ref_incomplete_r ref_step.simps(4) sync_step.simps(10) sync_step.simps(4))
   apply (metis aborted_trace_def failed_trace_def incomplete_trace_def lengthS_def sup1E tr.simps(1))
  apply (case_tac "index (sync_trace conj_sync t (appendS t (empty_trace Incomplete))) n")
  apply (clarsimp simp: sync_trace_def)
   apply (clarsimp simp: index_zip_trace_success)
   apply (subgoal_tac "\<exists>m. lengthS t = Some m", clarsimp simp: index_append)
  
    apply (metis aborted_end failed_trace_def incomplete_index_len isr_antitone option.sel ref_step_refl sup1E sync_step.simps(10) sync_step.simps(4) tr.simps(1))
   apply (erule failed_trace_has_lengthD)
  apply (clarsimp simp: sync_trace_def index_zip_trace_failed)
  apply (case_tac b; clarsimp)
   apply (smt (z3) isr_antitone le_add2 plus_1_eq_Suc ref_incomplete_r ref_step.elims(1) ref_step.simps(10))
  by (metis isr_antitone le_add2 plus_1_eq_Suc)

lemma conj_t_regular: "a \<le> conj_t a (regular a)"
  apply (clarsimp simp: regular_def, safe)
   apply (rule conj_t_idemp)
  apply (cases a; clarsimp)
  apply (clarsimp simp: conj_t_def)
  apply (rule trace_refI, clarsimp)
  apply (clarsimp)
  apply (erule failed_conj_incomplete_ref)
  done

lemma " a \<le> conj_t a b \<Longrightarrow> regular a \<le> b"
  apply (clarsimp simp: regular_def)
  apply (case_tac a; clarsimp)
  oops

lemma regular_empty[simp]: "regular Empty = Empty"
  apply (clarsimp simp: regular_def)
  done

lemma nonfailed_sync_trace_conj_sync_le: "\<not>aborted_trace (Trace x t') \<Longrightarrow> ref_step (index (sync_trace conj_sync t t') n) (index t n)"
  apply (induct n; clarsimp simp: sync_trace_def)
   apply (case_tac "index t 0"; case_tac "index t' 0"; clarsimp)
      apply (clarsimp simp: conj_sync_def)
     apply (case_tac b; clarsimp)
     apply (metis failed_trace_def not_aborted_no_aborts sup1I2 tr.simps(1))
    apply (case_tac b; clarsimp)
   apply (case_tac b; case_tac ba; clarsimp)
     apply (metis failed_trace_def not_aborted_no_aborts sup1I2 tr.simps(1))
     apply (metis failed_trace_def not_aborted_no_aborts sup1I2 tr.simps(1))
  apply (case_tac "index (zip_trace' (sync_step conj_sync) t t') n"; clarsimp simp: index_zip_trace_success index_zip_trace_failed)
  apply (elim disjE; clarsimp?)
  sorry



lemma le_conj_regular: "x \<le> conj_t b (regular a) \<Longrightarrow> x \<notin> \<Omega> \<Longrightarrow> x \<le> b"
  apply (cases a; cases b; clarsimp)
   defer
   apply (metis bottom_Trace.simps(2) le_bottom_iff)
  apply (clarsimp simp: regular_def split: if_splits)
   apply (clarsimp simp: conj_t_def split: if_splits)
    apply (erule order_trans)
    apply (rule trace_refI; clarsimp)
    apply (rule_tac x=x11 in nonfailed_sync_trace_conj_sync_le)
    apply (clarsimp simp: failed_trace_def)
   apply (metis bottom_Trace.simps(2) le_bottom_iff)
  apply (clarsimp simp: conj_t_def split: if_splits)
    apply (erule order_trans)
    apply (rule trace_refI; clarsimp)
   apply (rule_tac x=x11 in nonfailed_sync_trace_conj_sync_le)
   apply (smt (z3) aborted_end bottom_Trace.simps(2) coerce_le failed_trace_has_lengthD index_append 
                   index_bottom isl_iff not_arg_cong_Inr ref_incomplete_r ref_term_iff sum.disc(2) 
                   symbols.distinct(5) tr.simps(1) tr.simps(2))
  by (metis bottom_Trace.simps(2) le_bottom_iff)

lemma sync_step_conj_sync_commute: "sync_step conj_sync a b = sync_step conj_sync b a"
 apply (case_tac "a"; case_tac "b"; clarsimp split: symbols.splits)
      apply (clarsimp simp: conj_sync_def)
     apply (case_tac ba; clarsimp)
     apply (case_tac ba; clarsimp)
  by (case_tac ba; case_tac baa; clarsimp)


lemma sync_trace_conj_sync_commute: "sync_trace conj_sync t t' = sync_trace conj_sync t' t"
  apply (rule trace_eqI)
  apply (induct_tac n; clarsimp simp: sync_trace_def)
 apply (case_tac "index t 0"; case_tac "index t' 0"; clarsimp)
      apply (clarsimp simp: conj_sync_def)
     apply (case_tac b; clarsimp)
     apply (case_tac b; clarsimp)
   apply (case_tac b; case_tac ba; clarsimp)
  apply (case_tac "index (zip_trace' (sync_step conj_sync) t t') na"; clarsimp simp: index_zip_trace_success index_zip_trace_failed)
   apply (drule sym, clarsimp simp: index_zip_trace_success index_zip_trace_failed sync_step_conj_sync_commute)
  apply (drule sym, clarsimp simp: index_zip_trace_success index_zip_trace_failed sync_step_conj_sync_commute)
  done


lemma le_empty_iff[simp]:"c \<le> Empty \<longleftrightarrow> c = Empty"
  apply (cases c; clarsimp)
  using init_refD by fastforce

lemma unrefinedD:"\<not> Trace s t \<le> a \<Longrightarrow> init a = Some s  \<Longrightarrow>  \<exists>n x y. index t n = x \<and> index (tr a) n = y \<and> \<not>ref_step x y"
  apply (erule contrapos_np)
  apply (simp)
 apply (cases a; clarsimp)
  by (simp add: ref_trace_iff)

lemma sync_step_conj_abort_iff:"sync_step conj_sync a b = Inr Abort \<longleftrightarrow> a = Inr Abort \<or> b = Inr Abort"
  apply (cases a; cases b; clarsimp simp: conj_sync_def)
    apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  done

lemma sync_step_conj_term_iff:"sync_step conj_sync a b = Inr Term \<longleftrightarrow> a = Inr Term \<and> b = Inr Term"
  apply (cases a; cases b; clarsimp simp: conj_sync_def)
    apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  done

lemma zip_trace_conj_abortsD:" index (zip_trace' (sync_step conj_sync) t t') n = Inr Abort \<Longrightarrow> (\<exists>n'. n' \<le> n \<and> (index t n' = Inr Abort \<or> index t' n' = Inr Abort) )"
    apply (erule contrapos_pp, clarsimp)
    apply (induct n; clarsimp)
   apply (case_tac "index (zip_trace' (sync_step conj_sync) t t') n"; clarsimp?)
    apply (metis Inl_not_Inr index_zip_trace'_zero isr_antitone less_eq_nat.simps(1))
   apply (case_tac n; clarsimp simp: sync_step_conj_abort_iff)
  apply (case_tac "index (zip_trace' (sync_step conj_sync) t t') n"; clarsimp)
   apply (simp add: index_zip_trace_success sync_step_conj_abort_iff)
  apply (case_tac b; clarsimp)
   apply (simp add: index_zip_trace_failed)
  apply (simp add: index_zip_trace_failed)
  done

lemma zip_trace_conj_termD:" index (zip_trace' (sync_step conj_sync) t t') n = Inr Term \<Longrightarrow> (\<exists>n'. n' \<le> n \<and> (index t n' = Inr Term \<and> index t' n' = Inr Term) )"
    apply (erule contrapos_pp, clarsimp)
    apply (induct n; clarsimp)
   apply (case_tac "index (zip_trace' (sync_step conj_sync) t t') n"; clarsimp?)
    apply (metis Inl_not_Inr index_zip_trace'_zero isr_antitone less_eq_nat.simps(1))
   apply (case_tac n; clarsimp simp: sync_step_conj_abort_iff)
  apply (case_tac "index (zip_trace' (sync_step conj_sync) t t') n"; clarsimp)
   apply (simp add: index_zip_trace_success sync_step_conj_term_iff)
   apply (case_tac b; clarsimp simp: sync_step_conj_term_iff)
  apply (case_tac "index (zip_trace' (sync_step conj_sync) t t') n"; clarsimp)
   apply (simp add: index_zip_trace_success sync_step_conj_term_iff)
  apply blast
  by (simp add: index_zip_trace_failed)


interpretation conj_command: conj_elem "conj_t" regular
  apply (standard)
           apply (erule (1) conj_t_mono)
          apply (rule conj_t_assoc)
         apply (rule conj_t_assoc')
        apply (clarsimp simp: conj_t_def)
        apply (simp add: trace_refI)
       apply (safe)
  using conj_t_regular apply (metis conj_t_mono dual_order.refl order_trans)
       apply (erule (1) le_conj_regular)
  apply (simp add: less_eq_Trace_def regular_def)
      apply (clarsimp simp: conj_t_def sync_trace_conj_sync_commute)
     apply (rule_tac x="abort_from x" in exI)  
     apply (metis (no_types, lifting) abort_from_def append_empty bottom_trace_iff conj_t_regular dual_order.trans failed_abort_from le_abort_from le_bottom_iff preorder_bot_class.bot_least regular_def tr.simps(1) trace_def)
    apply (case_tac x; clarsimp)
     apply (clarsimp simp: conj_t_def split: if_splits)
      apply (case_tac b; clarsimp)
      apply (case_tac "aborted_trace a")
       apply (subgoal_tac "x11 = x11a", clarsimp)
        defer
        apply (metis init.simps(1) init_refD option.inject)
  apply (smt (verit, del_insts) aborted_trace_def init.simps(1) less_eq_Trace_def nonfailed_sync_trace_conj_sync_le ref_step_trans sync_trace_conj_sync_commute tr.simps(1))
     apply (metis bottom_Trace.simps(2))
    apply (simp add: conj_t_idemp)
   apply (clarsimp simp: ref_trace_iff)
   apply (frule unrefinedD; clarsimp)
  apply (case_tac "na \<le> n"; clarsimp?)
    apply (case_tac "(index (tr a) na)"; case_tac "(index x12 na)";  clarsimp)
      apply (erule_tac x=na in allE; clarsimp)
      apply (elim disjE; clarsimp?)
       apply (metis (no_types, opaque_lifting) index_zip_trace_inlD sum.inject(1) sync_inl_iff sync_trace_def)
      apply (clarsimp simp: sync_trace_def)
  apply (metis (no_types, lifting) Inl_Inr_False isr_antitone ref_step_abort zip_trace_conj_abortsD)
     apply (erule_tac x=na in allE; clarsimp)
  apply (case_tac b; clarsimp)
      apply (metis (no_types, lifting) Inl_Inr_False isr_antitone ref_Abort_iff sync_trace_def zip_trace_conj_abortsD)
     apply (elim disjE; clarsimp?)
      apply (smt (z3) isr_antitone ref_step.simps(12) ref_term_iff sync_trace_def zip_trace_conj_abortsD)
     apply (clarsimp simp: sync_trace_def)
  apply (metis Inl_Inr_False isr_antitone zip_trace_conj_termD)
   apply (erule_tac x=na in allE; clarsimp)
     apply (metis aborted_end isr_antitone linorder_linear sum.sel(2))
    apply (erule_tac x=na in allE; clarsimp)

    apply (metis aborted_trace_def isr_antitone linorder_linear ref_step_abort) 
   apply (clarsimp simp: linorder_not_le)
  apply (case_tac "(index (tr a) na)"; case_tac "(index x12 na)";  clarsimp)
     apply (smt (z3) index_zip_trace_inlD isl_c_ref_iff isl_monotone isr_antitone nless_le sum.collapse(1) sum.disc(1) sync_inl_iff sync_trace_def zip_trace_conj_abortsD)
  apply (smt (z3) index_zip_trace_inlD isl_def isr_antitone nless_le not_arg_cong_Inr ref_step.elims(2) sum.disc(2) symbols.simps(2) sync_inl_iff sync_trace_def zip_trace_conj_abortsD zip_trace_conj_termD)
    apply (metis aborted_end isr_antitone nle_le not_arg_cong_Inr)
  by (metis aborted_end isr_antitone linorder_le_cases ref_step_abort)

lemma ref_step_sync_par: "ref_step a b \<Longrightarrow> ref_step c d \<Longrightarrow> ref_step (sync_step par_sync a c) (sync_step par_sync b d)"
  apply (cases a; cases b; cases c; cases d; clarsimp)
       apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
   apply (case_tac bb; clarsimp)
  apply (case_tac ba; clarsimp)
   apply (elim disjE; clarsimp)
  apply (case_tac bb; clarsimp)
  apply (case_tac ba; clarsimp)
  done




lemma mono_sync_trace_par_sync: 
  "x \<le> y \<Longrightarrow> a \<le> Trace s t \<Longrightarrow> init y = Some s \<Longrightarrow> 
   ref_step (index (sync_trace par_sync (tr x) (tr a)) n) (index (sync_trace par_sync (tr y) t) n)"
  apply (induct n; clarsimp?)
   apply (clarsimp simp: sync_trace_def)
  using ref_step_sync_par 
   apply (metis less_eq_ref_stepD tr.simps(1))
  apply (clarsimp simp: sync_trace_def)
  apply (case_tac "index (zip_trace' (sync_step par_sync) (tr x) (tr a)) n"; clarsimp simp: index_zip_trace_success index_zip_trace_failed)
   apply (elim disjE)
    apply (metis index_zip_trace_success less_eq_Trace_def ref_step_sync_par tr.simps(1))
   apply (simp add: index_zip_trace_failed)
  by (metis (full_types) index_zip_trace_failed proj_sym.cases ref_Abort_iff ref_step.simps(2) ref_term_iff)

lemma sync_step_abort[simp]: " sync_step f c (Inr Abort) = (Inr Abort)"
  apply (cases c; clarsimp)
  by (case_tac b; clarsimp)


lemma sync_step_abort'[simp]: " sync_step f (Inr Abort) c = (Inr Abort)"
  by (cases c; clarsimp)

lemma sync_step_par_sync_assoc: "sync_step par_sync a (sync_step par_sync b c) = 
      sync_step par_sync (sync_step par_sync a b) c"
  apply (cases a; cases b; cases c; clarsimp split: symbols.splits)
         apply (case_tac aa; clarsimp)
          apply (case_tac aa; clarsimp)
           apply (case_tac ab; clarsimp)
          apply (case_tac ab; clarsimp)
         apply (case_tac aa; clarsimp)
           apply (case_tac ab; clarsimp)
           apply (case_tac ab; clarsimp)
        apply (case_tac ba; clarsimp)
         apply (case_tac aa; clarsimp)
         apply (case_tac aa; clarsimp)
         apply (case_tac aa; clarsimp)
         apply (case_tac aa; clarsimp)
         apply (case_tac aa; clarsimp)
        apply (case_tac aa; clarsimp)
        apply (case_tac ba; clarsimp)
        apply (case_tac ba; clarsimp)
        apply (case_tac ba; clarsimp)
        apply (case_tac ba; clarsimp)
     apply (case_tac ba; clarsimp)
         apply (case_tac aa; clarsimp)
         apply (case_tac aa; clarsimp)
         apply (case_tac aa; clarsimp)
         apply (case_tac aa; clarsimp)
         apply (case_tac aa; clarsimp)
     apply (case_tac aa; clarsimp)
        apply (case_tac ba; clarsimp)
        apply (case_tac ba; clarsimp)
        apply (case_tac ba; clarsimp)
        apply (case_tac ba; clarsimp)
        apply (case_tac ba; clarsimp)
        apply (case_tac ba; clarsimp)
        apply (case_tac ba; clarsimp)
        apply (case_tac ba; clarsimp)
    apply (case_tac bb; clarsimp)
   apply (case_tac bb; clarsimp)
        apply (case_tac ba; clarsimp)
   apply (case_tac bb; clarsimp)
   apply (case_tac bb; clarsimp)
  done

lemma sync_inl_env_iff:"sync_step par_sync a b = Inl (Env s) \<longleftrightarrow>  a = Inl (Env s) \<and> b = Inl (Env s)"
  apply (case_tac a; case_tac b; clarsimp simp: conj_sync_def)
     apply (case_tac aa; clarsimp)
    apply (case_tac aa; clarsimp)
    apply (case_tac aa; clarsimp)
  apply (clarsimp split: if_splits)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
   apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  done

lemma sync_inl_pgm_iff:"sync_step par_sync a b = Inl (Pgm s) \<longleftrightarrow>  (a = Inl (Pgm s) \<and> b = Inl (Env s)) \<or> (b = Inl (Pgm s) \<and> a = Inl (Env s)) "
  apply (case_tac a; case_tac b; clarsimp simp: conj_sync_def)
     apply (case_tac aa; clarsimp)
    apply (case_tac aa; clarsimp)
     apply (case_tac aa; clarsimp)
    apply (case_tac aa; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
   apply (case_tac ba; clarsimp)
   apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  done

lemma sync_trace_par_sync_assoc: "(sync_trace par_sync x (sync_trace par_sync y z)) =
       (sync_trace par_sync (sync_trace par_sync x y) z)"
  apply (clarsimp simp: sync_trace_def)
  apply (rule trace_eqI)
  apply (induct_tac n; clarsimp simp: sync_step_par_sync_assoc)
  apply (case_tac "index (zip_trace' (sync_step par_sync) x (zip_trace' (sync_step par_sync) y z)) na"; clarsimp)
   apply (drule sym; clarsimp)
  apply (subst index_zip_trace_success, assumption)+
   apply (drule index_zip_trace_inlD)+
   apply (case_tac a; clarsimp simp: sync_inl_pgm_iff sync_inl_env_iff)
  apply (clarsimp simp: index_zip_trace_failed index_zip_trace_success)
  using sync_step_par_sync_assoc apply blast
   apply (elim disjE; clarsimp simp: index_zip_trace_failed index_zip_trace_success)
  using sync_step_par_sync_assoc apply blast
  using sync_step_par_sync_assoc apply blast
  using sync_step_par_sync_assoc apply blast
  using sync_step_par_sync_assoc apply blast
  apply (drule sym, clarsimp)
  apply (clarsimp simp: index_zip_trace_failed index_zip_trace_success)
  done

lemma mono_par_t: "x \<le> y \<Longrightarrow> a \<le> b \<Longrightarrow> par_t x a \<le> par_t y b"
  apply (clarsimp simp: par_t_def; safe)
    apply (rule trace_refI)
     apply (clarsimp simp: init_refD)
  apply (clarsimp)
    apply (simp add: init_refD)
    apply (cases b; clarsimp)
  apply (erule (2) mono_sync_trace_par_sync)
    apply (simp add: init_refD)
  by (simp add: init_refD)

lemma par_t_assoc: "par_t a (par_t b c) \<le> par_t (par_t a b) c"
  apply (cases c; clarsimp)
  apply (clarsimp simp: par_t_def, safe)
    apply (clarsimp)
    apply (rule trace_refI; clarsimp?)
    apply (clarsimp simp: sync_trace_par_sync_assoc)

   apply (rule trace_refI; clarsimp?)
  apply (clarsimp simp: par_t_def)
  done

lemma par_t_assoc': "par_t a (par_t b c) \<ge> par_t (par_t a b) c"
  apply (cases c; clarsimp)
  apply (clarsimp simp: par_t_def, safe)
    apply (clarsimp)
    apply (rule trace_refI; clarsimp?)
    apply (clarsimp simp: sync_trace_par_sync_assoc)

   apply (rule trace_refI; clarsimp?)
  apply (clarsimp simp: par_t_def)
  done

lemma sync_step_par_sync_commute: "sync_step par_sync a b = sync_step par_sync b a"
  apply (cases a; cases b; clarsimp)
     apply (case_tac aa; clarsimp)
  apply (case_tac aa; clarsimp)
  apply (case_tac aa; clarsimp)
  apply (case_tac aa; clarsimp)
     apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  done

declare index_zip_trace_failed[simp] index_zip_trace_success[simp]

lemma par_t_commute: "par_t a b = par_t b a"
  apply (clarsimp simp: par_t_def)
  apply (cases a; clarsimp)
  apply (rule trace_eqI)
  apply (induct_tac n; clarsimp simp: sync_trace_def sync_step_par_sync_commute)
  apply (case_tac "index (zip_trace' (sync_step par_sync) x12 (tr b)) na"; clarsimp)
   apply (drule sym; clarsimp)
   apply (drule sym; clarsimp)
   apply (clarsimp simp: sync_step_par_sync_commute)
  apply (drule sym; clarsimp)

  by (drule sym; clarsimp)



lemma par_t_empty[simp]: "par_t Empty c = Empty"
  by (clarsimp simp: par_t_def)


lemma par_t_empty'[simp]: "par_t c Empty  = Empty"
  by (clarsimp simp: par_t_def)


lemma par_t_bottom[simp]: "par_t (bottom x) (bottom x) = bottom x"
  apply (clarsimp simp: par_t_def)
  apply (cases x; clarsimp)
  by (metis bottom_Trace.simps(2) sync_bottom tr.simps(2))

lemma le_par_t_env: "a \<le> par_t a (env a)"
  apply (cases a; clarsimp)
  apply (clarsimp simp: par_t_def)
  apply (rule trace_refI; clarsimp)
  apply (induct_tac n; clarsimp simp: sync_trace_def index_fmap)
   apply (case_tac "(index x12 0)"; clarsimp)
    apply (case_tac aa; clarsimp)
   apply (case_tac b; clarsimp)
  apply (case_tac "index (zip_trace' (sync_step par_sync) x12 (fmap_trace proj_env proj_sym x12)) na"; clarsimp)
   apply (clarsimp simp: index_fmap)
   apply (case_tac "(index x12 (Suc na))"; clarsimp)
    apply (case_tac aa; clarsimp)
     apply (case_tac aa; clarsimp)
    apply (case_tac aa; clarsimp)

   apply (case_tac b; clarsimp)
   apply (case_tac b; clarsimp)
   apply (metis (no_types, lifting) Inr_inject add_le_imp_le_left add_mono_thms_linordered_semiring(3) index_eq_finished
    isl_c_ref_iff isr_antitone le_add_same_cancel2 le_numeral_extra(4) linordered_nonzero_semiring_class.zero_le_one plus_1_eq_Suc symbols.distinct(1))
  by auto

thm sync_trace_def

lemma par_sync_inrD[simp,dest]:"par_sync a b = Inr c \<Longrightarrow> c = Incomplete"
  by (cases a; cases b; clarsimp split: if_splits)


lemma sync_step_par_sync_abort[simp]:"(sync_step par_sync a b) = Inr Abort \<longleftrightarrow> a = Inr Abort \<or> b = Inr Abort"
  apply (cases a; cases b; clarsimp split: if_splits)
     apply (case_tac aa; clarsimp)
      apply (case_tac aa; clarsimp split: if_splits)
      apply (case_tac aa; clarsimp split: if_splits)
      apply (case_tac aa; clarsimp split: if_splits)
     apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  done


lemma sync_step_conj_sync_abort[simp]:"(sync_step conj_sync a b) = Inr Abort \<longleftrightarrow> a = Inr Abort \<or> b = Inr Abort"
  apply (cases a; cases b; clarsimp split: if_splits)
  apply (clarsimp simp: conj_sync_def split: if_splits)
     apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  done

lemma sync_step_par_sync_term[simp]:"(sync_step par_sync a b) = Inr Term \<longleftrightarrow> a = Inr Term \<and> b = Inr Term"
  apply (cases a; cases b; clarsimp split: if_splits)
     apply (case_tac aa; clarsimp)
      apply (case_tac aa; clarsimp split: if_splits)
      apply (case_tac aa; clarsimp split: if_splits)
      apply (case_tac aa; clarsimp split: if_splits)
     apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  done

lemma "n' \<le> n \<Longrightarrow> index t n' = Inr Abort \<Longrightarrow> index (zip_trace' (sync_step par_sync) t t') n = Inr Abort"
  apply (induction "n - n'"; clarsimp)
  oops


lemma zip_trace_abortsD:" index (zip_trace' (sync_step par_sync) t t') n = Inr Abort \<Longrightarrow> (\<exists>n'. n' \<le> n \<and> (index t n' = Inr Abort \<or> index t' n' = Inr Abort) )"
    apply (erule contrapos_pp, clarsimp)
    apply (induct n; clarsimp)
  by (case_tac "index (zip_trace' (sync_step par_sync) t t') n"; clarsimp)

lemma zip_trace_termsD:" index (zip_trace' (sync_step par_sync) t t') n = Inr Term \<Longrightarrow> (\<exists>n'. n' \<le> n \<and> (index t n' = Inr Term \<and> index t' n' = Inr Term) )"
    apply (erule contrapos_pp, clarsimp)
    apply (induct n; clarsimp)
  by (case_tac "index (zip_trace' (sync_step par_sync) t t') n"; clarsimp)
  

lemma sync_trace_par_aborts_nonenv: "index (sync_trace par_sync t (fmap_trace proj_env proj_sym t')) n = Inr Abort \<Longrightarrow> index t n = Inr Abort"
  apply (clarsimp simp: sync_trace_def)
  apply (drule zip_trace_abortsD; clarsimp)
  apply (elim disjE)
     apply blast
  apply (clarsimp simp: index_fmap)
  by (metis (mono_tags, lifting) isl_map_sum map_sum_sel(2)
    proj_sym.elims sum.disc(2) sum.sel(2) symbols.simps(2) symbols.simps(4))

lemma par_t_envD: "x \<le> par_t b (env a) \<Longrightarrow> x \<le> b \<or> x \<in> \<Omega>"
  apply (clarsimp)
  apply (cases x; clarsimp)
   apply (clarsimp simp: par_t_def split: if_splits)
   apply (rule trace_refI; clarsimp)
  using init_refD apply force
  apply (frule init_refD)
   apply (clarsimp)
   apply (drule_tac n=n in less_eq_ref_stepD)
   apply (clarsimp)
   apply (cases a; clarsimp)
   apply (case_tac "(index x12 n)"; clarsimp)
    apply (elim disjE; clarsimp?)
     apply (clarsimp simp: sync_trace_def)
     apply (drule index_zip_trace_inlD; clarsimp?)
     apply (clarsimp simp: index_fmap)
     apply (case_tac "(index x12a n)"; clarsimp)
  apply (case_tac aa; clarsimp simp: sync_inl_pgm_iff sync_inl_env_iff)
  using proj_env.elims apply blast
     apply (case_tac aa; clarsimp simp: sync_inl_pgm_iff sync_inl_env_iff)
    apply (clarsimp simp: sync_trace_def)
    apply (drule zip_trace_abortsD; clarsimp)
  apply (elim disjE)
     apply blast
    apply (clarsimp simp: index_fmap)
    apply (metis (mono_tags, lifting) isl_map_sum map_sum_sel(2)
    proj_sym.elims sum.disc(2) sum.sel(2) symbols.simps(2) symbols.simps(4))


   apply (case_tac ba; clarsimp)
    apply (clarsimp simp: sync_trace_def)
    apply (drule zip_trace_abortsD; clarsimp)
  apply (elim disjE)
     apply blast
  apply (clarsimp simp: index_fmap)
    apply (metis (mono_tags, lifting) isl_map_sum map_sum_sel(2)
    proj_sym.elims sum.disc(2) sum.sel(2) symbols.simps(2) symbols.simps(4))
   apply (elim disjE; clarsimp?)
  apply (erule sync_trace_par_aborts_nonenv)
   apply (metis isr_antitone sync_trace_def zip_trace_termsD)
  by (metis bottom_Trace.simps(2))

interpretation par_command: par_elem par_t env
  apply (standard)
          apply (erule (1) mono_par_t)
         apply (rule par_t_assoc)
        apply (rule par_t_assoc')
       apply (clarsimp)
      apply (simp add: par_t_commute)
     apply (rule_tac x="abort_from x" in exI)
  apply (intro conjI)
      apply (simp add: le_abort_from)
     apply (case_tac x; clarsimp simp: abort_from_def)
     apply (clarsimp simp: par_t_def)
  apply (rule trace_refI; clarsimp)
     apply (simp add: index_immediate_sync_trace)
    apply (rule le_par_t_env)
   apply (erule par_t_envD)
  apply (case_tac x; clarsimp)
  by (rule trace_refI; clarsimp)

find_theorems seq_trace name:mono

lemma "first_trace (par_t x y) \<le> par_t (first_trace x) (first_trace y)"
  apply (rule trace_refI; clarsimp?)
   apply (clarsimp simp: par_t_def)
  apply (clarsimp simp: par_t_def split: option.splits)
  apply (cases x; cases y; clarsimp)
  by (simp add: index_immediate_sync_trace)


lemma init_seq_trace[simp]:"init (seq_trace x x') = init x"
  by (clarsimp simp: seq_trace_def)

lemma finiteS_sync_par: "finiteS (tr x) \<Longrightarrow> finiteS (sync_trace par_sync (tr x) (tr y))"
  apply (clarsimp simp: finiteS_def)
  apply (rule_tac x=n in exI)
  apply (erule contrapos_nn)
  apply (clarsimp simp: isl_def)
  apply (clarsimp simp: sync_trace_def)
  apply (drule index_zip_trace_inlD)
  by (smt (z3) Inl_Inr_False sync_step.elims)


lemma finiteS_sync_conj: "finiteS (tr x) \<Longrightarrow> finiteS (sync_trace conj_sync (tr x) (tr y))"
  apply (clarsimp simp: finiteS_def)
  apply (rule_tac x=n in exI)
  apply (erule contrapos_nn)
  apply (clarsimp simp: isl_def)
  apply (clarsimp simp: sync_trace_def)
  apply (drule index_zip_trace_inlD)
  by (smt (z3) Inl_Inr_False sync_step.elims)

lemma failed_trace_sync_par: "failed_trace x \<Longrightarrow> failed_trace (trace (init y) (sync_trace par_sync (tr x) (tr y)))"
  apply (clarsimp simp: failed_trace_def)
  apply (elim disjE; clarsimp?)
   apply (rule ccontr)
   apply (clarsimp simp: incomplete_trace_def split: if_splits option.splits)
   apply (drule mp, rule finiteS_sync_par, assumption)
   apply (subst (asm) aborted_trace_def, clarsimp)
   apply (drule mp)
    apply (erule finiteS_sync_par)
   apply (clarsimp simp: sync_trace_def)
  apply (case_tac "index (zip_trace' (sync_step par_sync) (tr x) (tr y)) (the (lengthS (zip_trace' (sync_step par_sync) (tr x) (tr y))))")
    apply (metis finiteS_sync_par isl_iff lengthS_def not_less_iff_gr_or_eq option.sel sum.disc(1) sync_trace_def)
   apply (case_tac b; clarsimp)
   apply (smt (verit, best) Inr_inject isr_antitone linorder_le_cases symbols.distinct(5) zip_trace_termsD)
  apply (rule ccontr)
  apply (subst (asm) aborted_trace_def, clarsimp)
  apply (clarsimp simp:  split: if_splits option.splits)
  apply (clarsimp simp: incomplete_trace_def)
  apply (subst (asm) aborted_trace_def, clarsimp)

   apply (drule mp, rule finiteS_sync_par, assumption)
   apply (drule mp)
    apply (erule finiteS_sync_par)
   apply (clarsimp simp: sync_trace_def)
  apply (case_tac "index (zip_trace' (sync_step par_sync) (tr x) (tr y)) (the (lengthS (zip_trace' (sync_step par_sync) (tr x) (tr y))))")
    apply (metis finiteS_sync_par isl_iff lengthS_def not_less_iff_gr_or_eq option.sel sum.disc(1) sync_trace_def)
  apply (case_tac b; clarsimp)
  by (smt (verit, ccfv_SIG) Inr_inject isr_antitone linorder_le_cases ref_incomplete_r ref_step.simps(10) symbols.distinct(5) zip_trace_termsD)


lemma sync_conj_sync_term_iff[simp]:"sync_step conj_sync a b = Inr Term \<longleftrightarrow> a = Inr Term \<and> b = Inr Term "
  apply (cases a; cases b; clarsimp)
  
     apply (metis Inl_Inr_False Inr_inject conj_sync_def symbols.distinct(5))
  apply (metis (full_types) Inr_inject ref_step.simps(10) ref_step.simps(11) symbols.exhaust symbols.simps(2) sync_step.simps(3) sync_step.simps(5) sync_step.simps(8))
   apply (case_tac "ba"; clarsimp)
  apply (case_tac "ba"; clarsimp)
  apply (case_tac "ba"; clarsimp)
  apply (case_tac "ba"; clarsimp)
  done

lemma zip_trace_conj_sync_termD: "index (zip_trace' (sync_step conj_sync) t t') n = Inr Term \<Longrightarrow> \<exists>n'\<le>n. index t n' = Inr Term \<and> index t' n' = Inr Term"
     apply (erule contrapos_pp, clarsimp)
    apply (induct n; clarsimp)
  by (case_tac "index (zip_trace' (sync_step conj_sync) t t') n"; clarsimp)
thm zip_trace_termsD[no_vars]

lemma failed_trace_sync_conj: "failed_trace x \<Longrightarrow> failed_trace (trace (init y) (sync_trace conj_sync (tr x) (tr y)))"
  apply (clarsimp simp: failed_trace_def)
  apply (elim disjE; clarsimp?)
   apply (rule ccontr)
   apply (clarsimp simp: incomplete_trace_def split: if_splits option.splits)
   apply (drule mp, rule finiteS_sync_conj, assumption)
   apply (subst (asm) aborted_trace_def, clarsimp)
   apply (drule mp)
    apply (erule finiteS_sync_conj)
   apply (clarsimp simp: sync_trace_def)
  apply (case_tac "index (zip_trace' (sync_step conj_sync) (tr x) (tr y)) (the (lengthS (zip_trace' (sync_step conj_sync) (tr x) (tr y))))")
    apply (metis finiteS_sync_conj isl_iff lengthS_def not_less_iff_gr_or_eq option.sel sum.disc(1) sync_trace_def)
   apply (case_tac b; clarsimp)
   apply (smt (verit, best) Inr_inject isr_antitone linorder_le_cases symbols.distinct(5) zip_trace_conj_sync_termD)
  apply (rule ccontr)
  apply (subst (asm) aborted_trace_def, clarsimp)
  apply (clarsimp simp:  split: if_splits option.splits)
  apply (clarsimp simp: incomplete_trace_def)
  apply (subst (asm) aborted_trace_def, clarsimp)

   apply (drule mp, rule finiteS_sync_conj, assumption)
   apply (drule mp)
    apply (erule finiteS_sync_conj)
   apply (clarsimp simp: sync_trace_def)
  apply (case_tac "index (zip_trace' (sync_step conj_sync) (tr x) (tr y)) (the (lengthS (zip_trace' (sync_step conj_sync) (tr x) (tr y))))")

    apply (metis finiteS_sync_conj isl_iff lengthS_def not_less_iff_gr_or_eq option.sel sum.disc(1) sync_trace_def)
  apply (case_tac b; clarsimp)
  by (smt (verit, ccfv_SIG) Inr_inject isr_antitone linorder_le_cases ref_incomplete_r ref_step.simps(10) symbols.distinct(5) zip_trace_conj_sync_termD)

lemma appendS_induct: "(\<And>m. lengthS x = Some m \<Longrightarrow> P (appendS x y)) \<Longrightarrow> (lengthS x = None \<Longrightarrow> P x) \<Longrightarrow> P (appendS x y)"
  by (metis inf_append lengthS_def)

lemma last_len_zero[simp]:"lengthS t = Some 0 \<Longrightarrow> last t = None" 
  apply (clarsimp simp: last_def split: if_splits option.splits)
  by (metis first_None_iff' first_def)

lemma last_cons_len_zero[simp]:"lengthS t = Some 0 \<Longrightarrow> Traces.last (cons_t s t) = Some s"
  apply (clarsimp simp: last_def index_cons_t)
  by (simp add: lengthS_cons)

lemma not_failed_index_term: "\<not> failed_trace y \<Longrightarrow> lengthS (tr y) = Some n \<Longrightarrow> index (tr y) n = Inr Term"
  by (metis failed_trace_def lengthS_some_finite not_failed_finite_index_iff option.sel sup1I1 sup1I2)

lemma first_last_len_suc: "first_trace y' = last_trace y \<Longrightarrow> lengthS (tr y) = Some (Suc m) \<Longrightarrow> index (appendS (tr y) (tr y')) 0 = index (tr y) 0" 
  apply (cases y; clarsimp)

   apply (rule appendS_induct)
    apply (clarsimp simp: index_append split: if_splits)
  apply (clarsimp simp: first_trace_def split: if_splits)
  done


lemma seq_conj_exchange: "seq_trace (conj_t x y) (conj_t x' y') \<le> conj_t (seq_trace x x') (seq_trace y y')"
  apply (clarsimp simp: conj_t_def, safe; clarsimp?)
   apply (case_tac "failed_trace x")
    apply (subst failed_trace_seq, erule failed_trace_sync_conj)
    apply (subst failed_trace_seq, assumption)
    apply (rule trace_refI; clarsimp split: option.splits)
    apply (clarsimp simp: seq_trace_def)
    apply (intro conjI impI)
     apply (induct_tac n; clarsimp simp: sync_trace_def)
      apply (rule appendS_induct)
       apply (case_tac m; clarsimp)
        apply (clarsimp simp: not_failed_index_term)
  apply (case_tac "(index (tr x) 0)"; clarsimp)
        apply (smt (z3) Trace_eqI failed_trace_def first_None_iff' first_def lengthS_some_finite lengthS_zero_empty_trace not_failed_finite_index_iff option.sel 
                ref_step.elims(3) sum.disc(1) sum.disc(2) sup1I1 sup1I2 symbols.exhaust sync_step.simps(12) sync_step_conj_sync_abort)
       apply (simp add: first_last_len_suc)
  apply (clarsimp)
     apply (case_tac "index (zip_trace' (sync_step conj_sync) (tr x) (tr y)) na"; clarsimp)
      apply (elim disjE; clarsimp)
      apply (drule index_zip_trace_inlD)+
      apply (clarsimp simp: sync_inl_iff)
      apply (rule appendS_induct)
       apply (clarsimp simp: index_append split: if_splits)
  sorry

lemma seq_par_exchange: "seq_trace (par_t x y) (par_t x' y') \<le> par_t (seq_trace x x') (seq_trace y y')"
  sorry
 (* apply (clarsimp simp: conj_t_def, safe; clarsimp?)
   apply (case_tac "failed_trace x")
    apply (subst failed_trace_seq, erule failed_trace_sync_conj)
    apply (subst failed_trace_seq, assumption)
    apply (rule trace_refI; clarsimp split: option.splits)
    apply (clarsimp simp: seq_trace_def)
    apply (intro conjI impI)
     apply (induct_tac n; clarsimp simp: sync_trace_def)
      apply (rule appendS_induct)
       apply (case_tac m; clarsimp)
        apply (clarsimp simp: not_failed_index_term)
  apply (case_tac "(index (tr x) 0)"; clarsimp)
        apply (smt (z3) Trace_eqI failed_trace_def first_None_iff' first_def lengthS_some_finite lengthS_zero_empty_trace not_failed_finite_index_iff option.sel 
                ref_step.elims(3) sum.disc(1) sum.disc(2) sup1I1 sup1I2 symbols.exhaust sync_step.simps(12) sync_step_conj_sync_abort)
       apply (simp add: first_last_len_suc)
  apply (clarsimp)
     apply (case_tac "index (zip_trace' (sync_step conj_sync) (tr x) (tr y)) na"; clarsimp)
      apply (elim disjE; clarsimp)
      apply (drule index_zip_trace_inlD)+
      apply (clarsimp simp: sync_inl_iff)
      apply (rule appendS_induct)
       apply (clarsimp simp: index_append split: if_splits)
  sorry *)


interpretation seq_par_elem seq_trace last_trace "(\<lambda>s. Trace s (empty_trace Term))" first_trace conj_t regular
  apply (standard)
      apply (rule seq_conj_exchange)
     apply (clarsimp simp: conj_t_def)
    apply (clarsimp simp: first_trace_def regular_def)
    apply (metis failed_first_iff first_trace_def)
   apply (clarsimp simp: regular_def)
   apply (intro conjI impI; clarsimp?)
       defer
       apply (metis dual_order.refl failed_seq_trace_iff infinite_seq non_matching_fails)
      apply (smt (z3) appendS_assoc append_empty dual_order.refl first_trace_def init_trace seq_trace_def tr.simps(1) tr.simps(2) trace_def trace_init_empty_iff)
     apply (smt (verit) appendS_assoc append_empty failed_seq_trace_iff infinite_seq init_trace nonfailed_ref ref_join_bot seq_trace_def tr.simps(1) trace_def)
    apply (smt (z3) appendS_assoc append_empty dual_order.refl failed_first_iff failed_trace_seq infinite_seq non_failed_notmatching_seq non_failed_trace_eq non_failed_trace_eq_iff non_matching_fails)
   apply (clarsimp simp: first_trace_def conj_t_def split: option.splits)
  sorry

lemma init_env[simp]: "init (env t) = init t"
  by (cases t; clarsimp)

lemma lengthS_fmap_trace[simp]: "lengthS (fmap_trace f g t) = lengthS t"
  apply (rule lengthS_eqI; clarsimp simp: index_fmap)
   apply (simp add: isl_map_sum)
  by (simp add: isl_iff isl_map_sum)

lemma finiteS_fmap[simp]: "finiteS (fmap_trace f g t) \<longleftrightarrow> finiteS t"
  by (metis finiteS_def inf_all_l lengthS_def lengthS_fmap_trace)

lemma failed_trace_failed_env[simp]: "failed_trace (env t) \<longleftrightarrow> failed_trace t"
  apply (rule iffI[rotated])
  apply (clarsimp simp: failed_trace_def)
  apply (elim disjE; clarsimp simp: incomplete_trace_def)
   apply (cases t; clarsimp simp: index_fmap)
  apply (subst (asm) aborted_trace_def, clarsimp)+
   apply (cases t; clarsimp simp: index_fmap)
 apply (clarsimp simp: failed_trace_def)
  apply (elim disjE; clarsimp simp: incomplete_trace_def)
   apply (cases t; clarsimp simp: index_fmap)
  using incomplete_index_len not_failed_finite_index_iff apply fastforce
  apply (subst (asm) aborted_trace_def, clarsimp)+
  apply (cases t; clarsimp simp: index_fmap)
  by (metis (mono_tags, lifting) isl_map_sum map_sum_sel(2) proj_sym.elims sum.disc(2) sum.sel(2) symbols.distinct(1) symbols.simps(4))


lemma fmap_appendS: "fmap_trace f g (appendS t t') = appendS (fmap_trace f g t) (fmap_trace f g t')"
  apply (rule trace_eqI)
  apply (rule appendS_induct; clarsimp simp: index_append index_fmap)
   apply (metis coerce_le index_fmap lengthS_fmap_trace)
  by (metis inf_is_clean)

lemma terminates_fmap_iff[simp]: "terminates (fmap_trace f proj_sym t) \<longleftrightarrow> terminates t"
  apply (safe)
   apply (clarsimp simp: terminates_def index_fmap split: if_splits)
   apply (metis (mono_tags, lifting) isl_map_sum map_sum_sel(2) proj_sym.elims sum.collapse(2) sum.disc(2) sum.sel(2) symbols.simps(6))
   apply (clarsimp simp: terminates_def index_fmap split: if_splits)
  done

lemma fmap_empty_simp[simp]: "fmap_trace f g (empty_trace c) = (empty_trace (g c))"
  by (rule trace_eqI; clarsimp simp: index_fmap)


lemma first_env[simp]:"first_trace (env t) = first_trace t"
  by (cases t; clarsimp?)


lemma last_env[simp]:"last_trace (env t) = last_trace t" 
  apply (cases t; clarsimp?)
  apply (clarsimp simp: trace_def)
  apply (clarsimp simp: last_def index_cons_t index_fmap lengthS_cons split: if_splits sum.splits option.splits)
  by (case_tac x1; clarsimp)

lemma env_seq_distrib: "env (seq_trace t t') = (seq_trace (env t) (env t'))"
  apply (clarsimp simp: seq_trace_def, safe; clarsimp?)
  apply (cases t; cases t'; clarsimp split: if_splits)
     apply (clarsimp simp: fmap_appendS)+
  apply (cases t; cases t'; clarsimp split: if_splits)
     apply (clarsimp simp: fmap_appendS)+
  done

declare index_immediate_sync_trace[simp]

interpretation spe: seq_par_elem seq_trace last_trace "(\<lambda>s. Trace s (empty_trace Term))" first_trace par_t env
  apply (standard)
      apply (rule seq_par_exchange)
     apply (clarsimp simp: par_t_def)
    apply (clarsimp simp: first_trace_def)
    apply (case_tac x; clarsimp)
   apply (clarsimp simp: env_seq_distrib)
  by (clarsimp simp: first_trace_def par_t_def split: option.splits)

lemma init_par_t: "init (par_t x y) = (if init x = init y then init x else None)"
  by (clarsimp simp: par_t_def)


lemma init_conj_t: "init (conj_t x y) = (if init x = init y then init x else None)"
  by (clarsimp simp: conj_t_def)

lemma sync_step_par_incomp[simp]: "sync_step par_sync (Inr Incomplete) c = (if c = Inr Abort then c else Inr Incomplete)"
  apply (cases c; clarsimp)
  apply (case_tac b; clarsimp)
  done

lemma sync_step_par_incomp'[simp]: "sync_step par_sync c (Inr Incomplete) = (if c = Inr Abort then c else Inr Incomplete)"
  apply (cases c; clarsimp)
  apply (case_tac b; clarsimp)
  done


lemma conj_never_aborts[simp]: "\<not>(conj_sync c d = Inr Abort)" 
  by (clarsimp simp: conj_sync_def)

lemma conj_sync_not[simp]: "x \<noteq> y \<Longrightarrow> conj_sync x y = Inr Incomplete"
  by (clarsimp simp: conj_sync_def)

lemma exchange_conj_par: "ref_step (sync_step par_sync (sync_step conj_sync a b) (sync_step conj_sync c d ))
           (sync_step conj_sync (sync_step par_sync a c) (sync_step par_sync b d ))"
  apply (cases a; cases b; cases c; cases d; clarsimp)
  apply (case_tac "aa = aaa"; case_tac "ab = ac"; clarsimp)
                apply (case_tac ba; clarsimp)
                apply (case_tac ba; clarsimp)
              apply (case_tac ba; clarsimp)
                apply (case_tac ba; clarsimp)
               apply (clarsimp simp: conj_sync_def)
              apply (case_tac ba; clarsimp)
               apply (case_tac ba; clarsimp)
               apply (case_tac ba; clarsimp)
               apply (case_tac ba; clarsimp)
               apply (case_tac ba; clarsimp)
               apply (case_tac ba; clarsimp)
               apply (case_tac ba; clarsimp)
               apply (case_tac ba; clarsimp)
               apply (case_tac ba; clarsimp)
               apply (case_tac ba; clarsimp)
               apply (case_tac ba; clarsimp)
      apply (clarsimp simp: conj_sync_def)
               apply (case_tac ba; clarsimp)
               apply (case_tac ba; clarsimp)
               apply (case_tac ba; clarsimp)
               apply (case_tac bb; clarsimp)
               apply (case_tac ba; clarsimp)
               apply (case_tac ba; clarsimp)
               apply (case_tac ba; clarsimp)
               apply (case_tac bb; clarsimp)
               apply (case_tac ba; clarsimp)
               apply (case_tac ba; clarsimp)
   apply (case_tac ba; clarsimp)
               apply (case_tac bb; clarsimp)
    apply (case_tac bc; clarsimp)
   apply (case_tac bc; clarsimp)
               apply (case_tac ba; clarsimp)
  done





lemma par_t_exchange: "par_t (conj_t x y) (conj_t x' y') \<le> conj_t (par_t x x') (par_t y y')"
  apply (rule trace_refI; clarsimp?)
   apply (clarsimp simp: init_conj_t init_par_t)
  apply (subst conj_t_def, clarsimp split: if_splits)
  apply (subst conj_t_def, clarsimp split: if_splits)
  apply (subst conj_t_def, clarsimp split: if_splits)
  apply (subst par_t_def, clarsimp split: if_splits)
  apply (subst par_t_def, clarsimp split: if_splits)
  apply (subst par_t_def, clarsimp split: if_splits)
  apply (subst par_t_def, clarsimp split: if_splits)+
  apply (clarsimp split: option.splits)
  apply (induct_tac n; clarsimp simp: sync_trace_def)
   apply (rule exchange_conj_par)
  apply (case_tac "(index (zip_trace' (sync_step par_sync) (zip_trace' (sync_step conj_sync) (tr x) (tr y)) (zip_trace' (sync_step conj_sync) (tr x') (tr y'))) na)", clarsimp)
   apply (elim disjE; clarsimp)
   apply (drule index_zip_trace_inlD)+
   apply (clarsimp simp: sync_inl_iff)
   apply (drule index_zip_trace_inlD)+
   apply (case_tac a; clarsimp simp: sync_inl_pgm_iff sync_inl_env_iff)
    apply (rule exchange_conj_par)
  apply (erule disjE; clarsimp)+
    apply (rule exchange_conj_par)
    apply (rule exchange_conj_par)
    apply (rule exchange_conj_par)
    apply (rule exchange_conj_par)
  apply (clarsimp)
  apply (case_tac b; clarsimp)
  apply (elim disjE; clarsimp)
  done



lemma empty_bot_empty[simp]: "\<exists>y. Empty = y\<^sub>\<bottom>"
  apply (rule_tac x="Empty" in exI)
  by (clarsimp)



  


lemma failed_failed_par_sync: "failed_trace (Trace x t) \<Longrightarrow> failed_trace (Trace y (sync_trace par_sync t t'))"
  apply (clarsimp simp: failed_trace_def)
  apply (elim disjE)
   apply (clarsimp simp: incomplete_trace_def)
   apply (intro conjI)
    apply (metis finiteS_sync_par tr.simps(1))
   apply (subst (asm) aborted_trace_def, clarsimp)
   apply (drule mp)
    apply (metis finiteS_sync_par tr.simps(1))
  apply (case_tac "index (sync_trace par_sync t t') (the (lengthS (sync_trace par_sync t t')))"; clarsimp)

    apply (metis finiteS_sync_par isl_iff lengthS_def nless_le option.sel sum.disc(1) tr.simps(1))
   apply (case_tac b; clarsimp)
  apply (clarsimp simp: sync_trace_def)
   apply (drule zip_trace_termsD, clarsimp)
   apply (metis Inr_inject isr_antitone nat_le_linear symbols.distinct(5))
  apply (clarsimp simp: incomplete_trace_def)
   apply (subst (asm) aborted_trace_def, clarsimp)
   apply (subst (asm) aborted_trace_def, clarsimp)
  apply (drule mp)
    apply (metis finiteS_sync_par tr.simps(1))
  apply (intro conjI)
   apply (metis finiteS_sync_par tr.simps(1))
 apply (case_tac "index (sync_trace par_sync t t') (the (lengthS (sync_trace par_sync t t')))"; clarsimp)

    apply (metis finiteS_sync_par isl_iff lengthS_def nless_le option.sel sum.disc(1) tr.simps(1))
   apply (case_tac b; clarsimp)
  apply (clarsimp simp: sync_trace_def)
  apply (drule zip_trace_termsD, clarsimp)
  by (metis Inr_inject isr_antitone nle_le ref_incomplete_r ref_step.simps(10) symbols.distinct(5))

fun non_aborting :: "'a Trace \<Rightarrow> 'a Trace"  
  where "non_aborting Empty = Empty" |
        "non_aborting (Trace s t) = (Trace s (fmap_trace id proj_sym t)) " 

lemma regular_is_nonaborting: "regular t = non_aborting t"
  apply (cases t; clarsimp)
  apply (clarsimp simp: regular_def)
  apply (intro conjI impI)
   apply (rule trace_eqI, clarsimp simp: index_fmap)
   apply (clarsimp simp: failed_trace_def incomplete_trace_def)
   apply (subst (asm) aborted_trace_def, clarsimp)
   apply (case_tac "finiteS x12"; clarsimp)
  apply (case_tac "index x12 n"; clarsimp)
    apply (metis (no_types, lifting) aborted_end not_aborted_no_aborts proj_sym.elims tr.simps(1))
  apply (case_tac "index x12 n"; clarsimp)
   apply (metis finiteS_def sum.disc(2))
  apply (rule trace_eqI)
  apply (rule appendS_induct; clarsimp simp: index_append index_fmap)
   apply (safe)
    apply (metis (mono_tags, lifting) isl_iff isl_map_sum map_sum_sel(1) sum.expand)
apply (clarsimp simp: failed_trace_def incomplete_trace_def)
   apply (subst (asm) aborted_trace_def, clarsimp)
  apply (elim disjE; clarsimp?)
  
  using isr_antitone apply fastforce
  using isr_antitone apply fastforce
apply (clarsimp simp: failed_trace_def incomplete_trace_def)
  apply (subst (asm) aborted_trace_def, clarsimp)
  apply (elim disjE; clarsimp)
   apply (metis inf_all_l sum.disc(2))
  apply (metis inf_all_l sum.disc(2))
  done


lemma ref_map_sync_nonabort: "ref_step (sync_step par_sync (map_sum (\<lambda>a. a) proj_sym a) (map_sum (\<lambda>a. a) proj_sym b)) (map_sum (\<lambda>a. a) proj_sym (sync_step par_sync a b))"
  apply (cases a; cases b; clarsimp)
     apply (case_tac aa; clarsimp)
  apply (case_tac aa; clarsimp)
  apply (case_tac aa; clarsimp)
  apply (case_tac aa; clarsimp)
     apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  apply (case_tac ba; clarsimp)
  done

lemma map_sum_InlD: "map_sum f g x = Inl a \<Longrightarrow> \<exists>b. x = Inl b \<and> a = f b"
  by (cases x; clarsimp)


lemma map_sum_InrD: "map_sum f g x = Inr a \<Longrightarrow> \<exists>b. x = Inr b \<and> a = g b"
  by (cases x; clarsimp)


interpretation cpe: conj_par_elem conj_t regular par_t env
  apply (standard)
      apply (rule par_t_exchange)
   apply (clarsimp simp: par_t_def regular_def)
   apply (safe; clarsimp?)
      apply (case_tac b; clarsimp)
  apply (rule_tac x="Trace x11 (empty_trace Incomplete)" in exI, clarsimp)
       apply (smt (verit) failed_trace_def first_None_iff' first_def incomplete_index_len incomplete_trace_empty index_zip_trace'_zero lengthS_empty 
lengthS_zero_empty_trace not_aborted_no_aborts option.sel sup1I2 sync_step_par_incomp' sync_trace_def tr.simps(2))
   apply (case_tac b; clarsimp)
   apply (rule_tac x="Trace x11 (empty_trace Incomplete)" in exI, clarsimp)
  apply (rule trace_eqI)
   apply (rule appendS_induct; clarsimp simp: index_append)
    apply (case_tac m; clarsimp)
    apply (smt (verit, ccfv_threshold) coerce_le first_None_iff' first_def index_append index_empty 
               index_zip_trace'_zero isl_iff lengthS_empty lengthS_zero_empty_trace sum.disc(2) sync_step_par_incomp' sync_trace_def)
   apply (metis failed_trace_has_lengthD failed_trace_sync_conj option.simps(3) sync_trace_conj_idemp trace_Some_simp)
  apply (case_tac a; case_tac b; clarsimp)
  apply (simp add: regular_is_nonaborting)
        apply (clarsimp simp: par_t_def)
  apply (rule trace_refI; clarsimp simp: index_fmap)
  apply (induct_tac n; clarsimp simp: sync_trace_def index_fmap)
   apply (rule ref_map_sync_nonabort)
  apply (case_tac "(index (zip_trace' (sync_step par_sync) (fmap_trace (\<lambda>a. a) proj_sym x12) (fmap_trace (\<lambda>a. a) proj_sym x12a)) na)", clarsimp)
   apply (elim disjE; clarsimp?)
    apply (drule map_sum_InlD, clarsimp simp: index_fmap)
    apply (rule ref_map_sync_nonabort)
   apply (drule map_sum_InrD, clarsimp)
  apply (clarsimp)
  apply (case_tac b; clarsimp)
  using map_sum_InrD apply fastforce
  apply (elim disjE)
  using map_sum_InrD apply fastforce
  using map_sum_InrD apply fastforce
  done


definition atomic_trace where
  "atomic_trace l s = (if l = labels.Pgm then Trace (fst s) (singleton (Pgm (snd (s))) Term) else Trace (fst s) (singleton (Env (snd (s))) Term)) "

lemma singleton_not_empty[simp]:"\<not>(singleton s r = empty_trace c)"
  by (metis One_nat_def index_empty isl_iff lengthS_singleton lessI sum.disc(2))

lemma not_pgm_then_env[simp]: "l \<noteq> labels.Pgm \<longleftrightarrow> l = labels.Env"
  by (cases l; clarsimp)

lemma trace_refD: "x \<le> y \<Longrightarrow> init x = init y \<and> (\<forall>n. ref_step (index (tr x) n) (index (tr y) n))"
  apply (clarsimp simp: less_eq_Trace_def)
  done

lemma index_singleton_0[simp]: "index (singleton a b) 0 = Inl a"
  apply (clarsimp simp: singleton_def)
  done

lemma index_singleton_n[simp]: "index (singleton a b) (Suc n) = Inr b"
  apply (clarsimp simp: singleton_def)
  done

lemma ref_step_iff: " ref_step c (Inl (Step.Pgm b)) \<longleftrightarrow> c = Inl (Step.Pgm b) \<or> c = Inr Incomplete "
  apply (safe; clarsimp?)
  apply (cases c; clarsimp)
  done

lemma le_singleton_len:"Trace i t \<le> Trace a (singleton c Term) \<Longrightarrow> \<exists>n. lengthS t = Some n \<and> n \<le> 1" sorry

lemma le_singleton_len_term:"Trace i t \<le> Trace a (singleton c Term) \<Longrightarrow> terminates t \<Longrightarrow>  t = (singleton c Term)"
  apply (rule trace_eqI)
  apply (case_tac n; clarsimp)
   apply (metis (no_types, opaque_lifting) Inr_not_Inl gr0I index_singleton_0 isl_c_ref_iff 
            isl_iff le_singleton_len less_eq_ref_stepD option.sel ref_step.simps(12) terminates_def tr.simps(1))
  apply (clarsimp simp: less_eq_Trace_def)
  apply (erule_tac x="Suc nat" in allE, clarsimp)
  by (metis (no_types, lifting) isl_c_ref_iff isl_iff isr_antitone lengthS_def
 linorder_le_less_linear option.sel ref_incomplete_r ref_step.simps(10) terminates_def)

lemma finiteS_singleton[simp]: "finiteS (singleton c d)"
  by (simp add: lengthS_singleton)

lemma not_empty_not_in_omega[simp]:" \<not>(\<forall>y. Empty \<noteq> y\<^sub>\<bottom>)"
  apply (clarsimp)
  done

lemma le_step_last_trace_disj: "x \<le> atomic_trace l (a, b) \<Longrightarrow> last_trace x \<in> \<Omega> \<or> last_trace x \<le> Trace b (empty_trace Term)" 
  apply (clarsimp simp: atomic_trace_def split: if_splits)
   apply (erule contrapos_np)
   apply (cases x; clarsimp split: if_splits)
  apply (drule le_singleton_len_term, assumption, clarsimp simp: lengthS_singleton)
   apply (clarsimp simp: last_def lengthS_cons lengthS_singleton index_cons_t split: option.splits)
  apply (erule contrapos_np)
   apply (erule contrapos_np)
   apply (cases x; clarsimp split: if_splits)
  apply (drule le_singleton_len_term, assumption, clarsimp simp: lengthS_singleton)
  by (clarsimp simp: last_def lengthS_cons lengthS_singleton index_cons_t split: option.splits)


lemma step_ref_test_step: "atomic_trace l (a, b) \<le> seq_trace (Trace a (empty_trace Term)) (atomic_trace l (a, b))"
  apply (rule trace_refI; clarsimp?)
   apply (clarsimp simp: atomic_trace_def)
  apply (clarsimp simp: atomic_trace_def split: if_splits)
  apply (safe)
   apply (case_tac n; clarsimp)
    apply (clarsimp simp: seq_trace_def)
  apply (clarsimp simp: seq_trace_def)
  apply (clarsimp simp: seq_trace_def)
  done

lemma first_atomic_seq[simp]: "first_trace (seq_trace (atomic_trace l (a, b)) x) = Trace a (empty_trace Term)"
  apply (clarsimp simp: first_trace_def seq_trace_def)
  apply (intro conjI impI)
   apply (clarsimp simp: atomic_trace_def)
  apply (clarsimp simp: atomic_trace_def)
  done

lemma terminates_singleton_iff[simp]: "terminates (singleton c d) \<longleftrightarrow> d = Term"
  apply (safe; clarsimp?)
   apply (clarsimp simp: terminates_def lengthS_singleton)
  apply (clarsimp simp: terminates_def lengthS_singleton)
  done

lemma last_atomic_iff[simp]:"last_trace (atomic_trace l s) = Trace (snd s) (empty_trace Term)"
  apply (clarsimp simp: atomic_trace_def, intro conjI impI; clarsimp?)
   apply (clarsimp simp: last_def index_cons_t lengthS_cons lengthS_singleton)
  apply (clarsimp simp: last_def index_cons_t lengthS_cons lengthS_singleton)
  done

lemma failed_singleton_iff[simp]:"failed_trace (Trace a (singleton c d)) \<longleftrightarrow> d = Abort \<or> d = Incomplete"
  apply (safe; clarsimp simp: failed_trace_def)
    apply (metis Inr_inject One_nat_def aborted_end incomplete_trace_def index_singleton_n lengthS_singleton option.sel tr.simps(1))
   apply (subst (asm) aborted_trace_def, clarsimp simp: lengthS_singleton)
  by (clarsimp simp: incomplete_trace_def lengthS_singleton)

lemma last_cons_singleton[simp]: "Traces.last (cons_t s (singleton s' Term)) = Some s'"
  by (clarsimp simp: last_def index_cons_t lengthS_singleton lengthS_cons)

lemma step_le_step_append_test: "atomic_trace l (a, b) \<le> seq_trace (atomic_trace l (a, b)) (Trace b (empty_trace Term))"
apply (rule trace_refI; clarsimp?)
   apply (clarsimp simp: atomic_trace_def)
  apply (safe)
   apply (case_tac n; clarsimp)
    apply (clarsimp simp: seq_trace_def)
    apply (rule appendS_induct)
     apply (clarsimp simp: lengthS_singleton index_append)
    apply (clarsimp simp: lengthS_singleton index_append)
 apply (clarsimp simp: seq_trace_def)
    apply (rule appendS_induct)
     apply (clarsimp simp: lengthS_singleton index_append)
   apply (clarsimp simp: lengthS_singleton index_append)
 apply (case_tac n; clarsimp)
    apply (clarsimp simp: seq_trace_def)
    apply (rule appendS_induct)
     apply (clarsimp simp: lengthS_singleton index_append)
    apply (clarsimp simp: lengthS_singleton index_append)
 apply (clarsimp simp: seq_trace_def)
    apply (rule appendS_induct)
     apply (clarsimp simp: lengthS_singleton index_append)
  apply (clarsimp simp: lengthS_singleton index_append)
  done

declare lengthS_singleton[simp]

lemma seq_step_le_matching: "seq_trace (atomic_trace l' s') x \<le> atomic_trace l s \<Longrightarrow> l = l' \<and> s = s'"
  apply (clarsimp simp: less_eq_Trace_def atomic_trace_def split: if_splits)
     apply (drule_tac x=0 in spec; clarsimp simp: seq_trace_def index_append )
  using prod.expand apply blast
     apply (drule_tac x=0 in spec; clarsimp simp: seq_trace_def index_append )
     apply (drule_tac x=0 in spec; clarsimp simp: seq_trace_def index_append )
  apply (drule_tac x=0 in spec; clarsimp simp: seq_trace_def index_append )
  using prod.expand apply blast
  done

lemma not_failed_atomic[simp]: "\<not>failed_trace ( (atomic_trace l s))" sorry

lemma init_atomic[simp]:"init (atomic_trace l s) = Some (fst s)"
  apply (clarsimp simp: atomic_trace_def)
  done

definition "label_map l = (if l = labels.Pgm then Pgm else Env)"

lemma label_map_pgm[simp]: "label_map labels.Pgm s = Pgm s"
  by (clarsimp simp: label_map_def)


lemma label_map_env[simp]: "label_map labels.Env s = Env s"
  by (clarsimp simp: label_map_def)

lemma tr_atomic_trace[simp]: "tr (atomic_trace l s) = singleton (label_map l (snd s)) Term"
  by (clarsimp simp: atomic_trace_def)

lemma appendS_iff_cons: "appendS (singleton c d) t = cons_t c t"
  apply (rule trace_eqI)
  by (clarsimp simp: index_append index_cons_t)


lemma seq_trace_step_leD: "seq_trace (atomic_trace l s) d \<le> seq_trace (atomic_trace l s) c \<Longrightarrow> seq_trace (Trace (snd s) (empty_trace Term)) d \<le> seq_trace (Trace (snd s) (empty_trace Term)) c"
  apply (clarsimp simp: seq_trace_def split: if_splits)
    apply (clarsimp simp: appendS_iff_cons)
    apply (clarsimp simp: less_eq_Trace_def)
    apply (clarsimp simp: first_trace_def split: if_splits)
    apply (cases d; clarsimp)
    apply (cases c; clarsimp)
  apply (clarsimp simp: index_cons_t)
    apply (smt (verit) Zero_neq_Suc diff_add_inverse plus_1_eq_Suc)
   apply (clarsimp simp: appendS_iff_cons)
   apply (clarsimp simp: less_eq_Trace_def)
  apply (clarsimp simp: appendS_iff_cons)
  apply (clarsimp simp: less_eq_Trace_def)
  apply (clarsimp simp: index_cons_t)
  by (smt (verit, best) Zero_neq_Suc diff_add_inverse index_empty plus_1_eq_Suc ref_incomplete_r)

lemma trace_le_atomic_iff: "Trace i t \<le> atomic_trace l (a, b) \<longleftrightarrow> a = i \<and> (\<forall>n. ref_step (index t n) ((index (singleton (label_map l b) Term)) n))"
  by (clarsimp simp: atomic_trace_def, safe; clarsimp simp: less_eq_Trace_def)


lemma trace_le_atomic_iff': "Trace i t \<ge> atomic_trace l (a, b) \<longleftrightarrow> a = i \<and> (\<forall>n. ref_step ((index (singleton (label_map l b) Term)) n) (index t n) )"
  by (clarsimp simp: atomic_trace_def, safe; clarsimp simp: less_eq_Trace_def)

lemma atomic_trace_cases:"x \<le> atomic_trace l (a, b) \<Longrightarrow> x \<in> \<Omega> \<or> x \<le> seq_trace (atomic_trace l (a, b)) (bottom (Trace b (empty_trace Term))) \<and> seq_trace (atomic_trace l (a, b)) (bottom (Trace b (empty_trace Term))) \<le> x \<or> atomic_trace l (a, b) \<le> x"
  apply (clarsimp)
  apply (cases x; clarsimp)
  apply (intro conjI)
   apply (clarsimp simp: seq_trace_def appendS_iff_cons)
   apply (rule trace_refI; clarsimp)
  using init_refD apply fastforce
   apply (clarsimp simp: index_cons_t)
   apply (safe; clarsimp?)
    apply (clarsimp simp: trace_le_atomic_iff trace_le_atomic_iff')
    apply (erule_tac x=0 in allE)
  apply (clarsimp)
   apply (clarsimp simp: trace_le_atomic_iff trace_le_atomic_iff')
   apply (case_tac na; clarsimp)
  apply (smt (z3) Inl_Inr_False index_singleton_0 inf_all_l isl_c_ref_iff isr_antitone le_singleton_len lengthS_def ref_incomplete_r ref_step.elims(1) ref_step.elims(2) 
           ref_step.simps(10) ref_step.simps(12) ref_step.simps(2) ref_step.simps(8) ref_step_abort ref_trace_iff zero_le zero_less_one_class.zero_le_one)
   apply (smt (z3) One_nat_def Suc_pred index_eq_finished index_singleton_n isl_c_ref_iff isl_iff le_add1 lengthS_singleton 
 nless_le not_arg_cong_Inr plus_1_eq_Suc ref_step.elims(2) symbols.simps(2))
 apply (rule trace_refI; clarsimp)
  using init_refD apply fastforce
   apply (clarsimp simp: seq_trace_def appendS_iff_cons)

   apply (clarsimp simp: index_cons_t)
  apply (clarsimp simp: trace_le_atomic_iff trace_le_atomic_iff')
    apply (erule_tac x=0 in allE)
  apply (clarsimp)
  apply (case_tac "(index x12 0)"; clarsimp)
  by (metis bot_eq_iff index_empty isr_antitone tr.simps(1) trace_eqI zero_le)

instantiation Trace :: (type)  order begin
instance
  apply (standard)
  apply (clarsimp simp: less_eq_Trace_def)
  apply (rule Trace_eqI; clarsimp?)
  apply (rule trace_eqI)
  apply (erule_tac x=n in allE)
  apply (erule_tac x=n in allE)
  apply (case_tac "index (tr x) n"; case_tac "index (tr x) n"; clarsimp)
   apply (elim disjE; clarsimp)
  apply (case_tac b; clarsimp)
  apply (elim disjE; clarsimp)
  done

lemma seq_atomic_incomplete: "seq_trace (atomic_trace l' (aa, ba)) (Trace ba (empty_trace Incomplete)) = Trace aa (singleton (label_map l' ba) Incomplete)"
  apply (clarsimp simp: seq_trace_def appendS_iff_cons)
  apply (rule trace_eqI; clarsimp simp: index_cons_t)
  apply (case_tac n; clarsimp)
  done

lemma bottom_le_atomic_iff: "bottom y \<le> atomic_trace l (a, b) \<longleftrightarrow> bottom y = Trace a (empty_trace Incomplete)"
  apply (safe; clarsimp?)
   apply (case_tac y)
    apply (clarsimp simp: trace_le_atomic_iff)
   apply (clarsimp simp: atomic_trace_def split: if_splits) 
    apply (clarsimp simp: trace_le_atomic_iff)
  done

lemma atomic_trace_simp: "atomic_trace l (a, b) = Trace a (singleton (label_map l b) Term)"
  by (clarsimp simp: atomic_trace_def)

lemma le_failed_step_iff: "x \<le> Trace a (singleton (label_map l b) Incomplete) \<Longrightarrow> x = Trace a (empty_trace Incomplete) \<or> x = Trace a (singleton (label_map l b) Incomplete)"
  sorry

lemma empty_le[simp]: "Trace a (empty_trace Incomplete) \<le> Trace a t"
  by (metis bottom_Trace.simps(1) order_refl preorder_bot_class.bot_least)

lemma empty_not_singleton[simp]: "\<not>(empty_trace c = singleton a b)"
  apply (clarsimp)
  by (metis singleton_not_empty)

lemma singleton_eq_iff[simp]:"singleton c d = singleton c' d' \<longleftrightarrow> c = c' \<and> d = d'"
  apply (safe; clarsimp?)
   apply (metis index_singleton_0 sum.sel(1))
  by (metis index_singleton_n sum.sel(2))

lemma incomp_ref_seq_atomic_iff: "Trace a (singleton (label_map l b) Incomplete) \<le> seq_trace (atomic_trace l' (aa, ba)) d \<longleftrightarrow> aa = a \<and> l = l' \<and> b = ba"
  apply (safe; clarsimp?)
     apply (clarsimp simp: seq_trace_def appendS_iff_cons split: if_splits)
      apply (metis first_trace_Trace le_init_first_le test_le)
  using init_refD apply force
    apply (clarsimp simp: seq_trace_def appendS_iff_cons split: if_splits)
     apply (clarsimp simp: less_eq_Trace_def)
     apply (erule_tac x=0 in allE, clarsimp simp: index_cons_t)
     apply (clarsimp simp: label_map_def split: if_splits)
 apply (clarsimp simp: less_eq_Trace_def)
     apply (erule_tac x=0 in allE, clarsimp simp: index_cons_t)
    apply (clarsimp simp: label_map_def split: if_splits)
 apply (clarsimp simp: seq_trace_def appendS_iff_cons split: if_splits)
     apply (clarsimp simp: less_eq_Trace_def)
    apply (erule_tac x=0 in allE, clarsimp simp: index_cons_t)
    apply (clarsimp simp: label_map_def split: if_splits)
     apply (clarsimp simp: less_eq_Trace_def)
    apply (erule_tac x=0 in allE, clarsimp simp: index_cons_t)
   apply (clarsimp simp: label_map_def split: if_splits)
  apply (rule trace_refI; clarsimp?)
 apply (clarsimp simp: seq_trace_def appendS_iff_cons split: if_splits)
  apply (safe)
   apply (case_tac n; clarsimp simp: index_cons_t)
  apply (case_tac n; clarsimp simp: index_cons_t)
  done

lemma ref_step_any_inl_iff[simp]: "ref_step a (Inl s) \<longleftrightarrow> (a = Inl s \<or> a = Inr Incomplete)"
  apply (cases a ;clarsimp)
  done

lemma le_step_len0: "x \<le> Trace a (cons_t (label_map l b) t) \<Longrightarrow> lengthS (tr x) = Some 0 \<Longrightarrow> x = Trace a (empty_trace Incomplete)"
  apply (rule Trace_eqI; clarsimp?)
   apply (simp add: init_refD)
  apply (rule trace_eqI)
  apply (induct_tac n; clarsimp)
  apply (clarsimp simp: less_eq_Trace_def)
  apply (erule_tac x=0 in allE; clarsimp simp: index_cons_t split: if_splits)
   apply (simp add: lengthS_zero_empty_trace)
  by (metis index_empty lengthS_zero_empty_trace)

lemma le_step_len1: "x \<le> Trace a (cons_t (label_map l b) t) \<Longrightarrow> lengthS (tr x) = Some 1 \<Longrightarrow> x = Trace a (cons_t (label_map l b) (empty_trace (projr (index (tr x) 1)))) "
  apply (clarsimp)
  apply (rule Trace_eqI; clarsimp?)
   apply (simp add: init_refD)
  apply (rule trace_eqI)
  apply (induct_tac n; clarsimp)
  apply (clarsimp simp: less_eq_Trace_def)
   apply (erule_tac x=0 in allE; clarsimp simp: index_cons_t split: if_splits)
   apply (metis One_nat_def isl_iff sum.disc(2) zero_less_one)
  apply (clarsimp simp: less_eq_Trace_def)
  apply (erule_tac x="Suc na" in allE, clarsimp simp: index_cons_t split: if_splits)
   apply (metis isl_iff nless_le sum.collapse(2))
  apply (meson isr_antitone lessI nless_le)
  done

lemma cons_t_eq_iff[simp]: "cons_t a t = cons_t b t' \<longleftrightarrow> a = b \<and> t = t'" sorry

lemma label_map_eq_iff[simp]:"label_map l b = label_map l' ba \<longleftrightarrow> l' = l \<and> b = ba" sorry

lemma state_of_label_map[simp]: "state_of (label_map l b) = b"
  by (clarsimp simp: label_map_def)

lemma meet_init_eq: "x \<le> Trace a t \<Longrightarrow> x \<le> Trace b t' \<Longrightarrow> a = b"
  by (clarsimp simp: less_eq_Trace_def)

lemma cons_empty_is_singleton:"cons_t s (empty_trace c) = singleton s c"
  by (rule trace_eqI, case_tac n; clarsimp simp: index_cons_t)

thm atomic_trace_cases


lemma seq_inf_interchange: "ab \<le> atomic_trace l (a, b) \<Longrightarrow> bb \<le> atomic_trace l' (aa, ba) \<Longrightarrow> x \<le> seq_trace ab c \<Longrightarrow> x \<le> seq_trace bb d \<Longrightarrow> \<exists>y\<le>ab. y \<le> bb  \<and> x \<le> seq_trace y c \<and>  x \<le> seq_trace y d"
  apply (frule_tac x=ab in atomic_trace_cases; clarsimp)
  apply (frule_tac x=bb in atomic_trace_cases; clarsimp)
  apply (elim disjE; clarsimp?)
         apply (clarsimp simp: bottom_le_atomic_iff seq_atomic_incomplete)
  apply (clarsimp simp: bottom_le_atomic_iff seq_atomic_incomplete)
        apply (simp add: less_eq_Trace_def)
  apply (clarsimp simp: bottom_le_atomic_iff seq_atomic_incomplete)
      apply (clarsimp simp: bottom_le_atomic_iff seq_atomic_incomplete)
      apply (simp add: less_eq_Trace_def)
     apply (clarsimp simp: bottom_le_atomic_iff seq_atomic_incomplete )
  apply (clarsimp simp: atomic_trace_simp)
     apply (cases x; clarsimp)
     apply (drule le_failed_step_iff)+
     apply (clarsimp)
     apply (elim disjE; clarsimp)
      apply (rule_tac x=" Trace a (empty_trace Incomplete)" in exI, intro conjI; clarsimp?)
     apply (rule_tac x="Trace a (singleton (label_map l b) Incomplete)" in exI; clarsimp)
    apply (clarsimp simp: bottom_le_atomic_iff seq_atomic_incomplete )
     apply (drule le_failed_step_iff)+
    apply (elim disjE; clarsimp)
     apply (rule_tac x=" Trace a (empty_trace Incomplete)" in exI; clarsimp)
     apply (metis index_empty init_seq_trace less_eq_Trace_def ref_step.simps(2) tr.simps(1))
    apply (clarsimp simp: incomp_ref_seq_atomic_iff)
    apply (rule_tac x="Trace a (singleton (label_map l' ba) Incomplete)" in exI; clarsimp)
   apply (clarsimp simp: bottom_le_atomic_iff seq_atomic_incomplete incomp_ref_seq_atomic_iff)
     apply (drule le_failed_step_iff)+
   apply (elim disjE; clarsimp)
    apply (subgoal_tac "a = aa", clarsimp)
     apply (rule_tac x="Trace aa (empty_trace Incomplete)" in exI; clarsimp)
     apply (metis bottom_Trace.simps(1) bottom_le_atomic_iff)
  apply (metis first_atomic_seq first_trace_incomplete test_le test_seq.first_le test_seq_axioms)
   apply (clarsimp simp: bottom_le_atomic_iff seq_atomic_incomplete incomp_ref_seq_atomic_iff)
   apply (rule_tac x=" Trace aa (singleton (label_map l b) Incomplete)" in exI; clarsimp)
  apply (subst (asm) seq_trace_def, clarsimp)
  apply (subst (asm) seq_trace_def, clarsimp)
  apply (clarsimp split: if_splits)
     apply (cases c; cases d; clarsimp simp: appendS_iff_cons)
     apply (case_tac "\<exists>m. lengthS (tr x) = Some m", clarsimp)
      apply (case_tac "m = 0 \<or> m = 1"; clarsimp)
  apply (elim disjE; clarsimp)
       apply (drule le_step_len0, clarsimp)+
  apply (clarsimp)
        apply (rule_tac x="Trace a (empty_trace Incomplete)" in exI, clarsimp)
        apply (intro conjI)
     apply (metis bottom_Trace.simps(1) bottom_le_atomic_iff)
        apply (metis atomic_trace_simp empty_le init.simps(1) init_refD option.inject)
       apply (frule le_step_len1, clarsimp)
       apply (frule le_step_len1, clarsimp) back

       apply (clarsimp)
       apply (case_tac "index (tr x) 1")
        apply (metis One_nat_def isl_iff nless_le sum.disc(1))
  apply (case_tac bc; clarsimp)
       apply (rule_tac x="Trace a (singleton (label_map l b) Term)" in exI, clarsimp)
         apply (intro conjI; clarsimp?)
           apply (clarsimp simp: atomic_trace_simp)
          apply (clarsimp simp: seq_trace_def appendS_iff_cons)
  apply (simp add: appendS_iff_cons seq_trace_def)
        apply (rule_tac x="Trace a (singleton (label_map l b) Term)" in exI, clarsimp)
        apply (intro conjI; clarsimp?)
          apply (clarsimp simp: atomic_trace_simp)
         apply (clarsimp simp: seq_trace_def appendS_iff_cons index_cons_t)
        apply (clarsimp simp: seq_trace_def appendS_iff_cons index_cons_t)
       apply (rule_tac x="Trace a (singleton (label_map l b) Incomplete)" in exI, clarsimp)
  apply (intro conjI; clarsimp?)
          apply (clarsimp simp: atomic_trace_simp)
         apply (clarsimp simp: seq_trace_def appendS_iff_cons index_cons_t)
 
        apply (metis atomic_trace_simp dual_order.trans incomp_ref_seq_atomic_iff le_test)
       apply (metis appendS_iff_cons init.simps(1) ref_step_index_append_incomplete tr.simps(1) trace_refI)
      apply (rule_tac x="Trace a (singleton (label_map l b) Term)" in exI)
      apply (intro conjI)
         apply (clarsimp simp: atomic_trace_simp)
  apply (subgoal_tac "a = aa")

        apply (drule less_eq_ref_stepD[where n=0])+
        apply (clarsimp simp: index_cons_t)
         apply (elim disjE; clarsimp simp: atomic_trace_simp)
  apply (metis isl_iff sum.disc(2))
        apply (erule (1) meet_init_eq)
       apply (erule order_trans)
       apply (clarsimp simp: seq_trace_def appendS_iff_cons)
 apply (subgoal_tac "a = aa")

       apply (frule less_eq_ref_stepD[where n=0])
        apply (frule less_eq_ref_stepD[where n=0]) back

       apply (clarsimp simp: index_cons_t)
  apply (elim disjE; clarsimp simp: isl_iff)
 apply (erule order_trans) back
        apply (clarsimp simp: seq_trace_def appendS_iff_cons)
       apply (metis isl_iff sum.disc(2))
        apply (erule (1) meet_init_eq)
     apply (clarsimp)
     apply (subgoal_tac "a = aa \<and> l = l' \<and> b = ba", clarsimp)
      apply (rule_tac x="Trace a (singleton (label_map l b) Term)" in exI)
      apply (clarsimp simp: atomic_trace_simp appendS_iff_cons seq_trace_def)
     apply (smt (verit) index_cons_t inf_all_l isl_c_ref_iff isl_def label_map_eq_iff less_eq_Trace_def meet_init_eq sum.disc(2) sum.sel(1) tr.simps(1))
    apply (clarsimp simp:  appendS_iff_cons cons_empty_is_singleton)
  apply (drule le_failed_step_iff, elim disjE; clarsimp)
     apply (metis bottom_Trace.simps(1) bottom_le_atomic_iff dual_order.refl failed_trace_empty_trace meet_init_eq seq_trace_def)
  apply (metis cons_empty_is_singleton cons_t_eq_iff dual_order.antisym incomp_ref_seq_atomic_iff le_step_len1 le_test lengthS_singleton step_le_step_append_test tr.simps(1))
   apply (clarsimp simp:  appendS_iff_cons cons_empty_is_singleton)
   apply (drule le_failed_step_iff, elim disjE; clarsimp)
     apply (metis bottom_Trace.simps(1) bottom_le_atomic_iff dual_order.refl failed_trace_empty_trace meet_init_eq seq_trace_def)

  apply (metis cons_empty_is_singleton cons_t_eq_iff dual_order.antisym incomp_ref_seq_atomic_iff le_step_len1 le_test lengthS_singleton step_le_step_append_test tr.simps(1))
   apply (clarsimp simp:  appendS_iff_cons cons_empty_is_singleton)
  apply (drule le_failed_step_iff)+
  apply (elim disjE; clarsimp)
     apply (metis bottom_Trace.simps(1) bottom_le_atomic_iff dual_order.refl failed_trace_empty_trace meet_init_eq seq_trace_def)

  apply (metis cons_empty_is_singleton cons_t_eq_iff dual_order.antisym incomp_ref_seq_atomic_iff le_step_len1 le_test lengthS_singleton step_le_step_append_test tr.simps(1))
  done

 

interpretation seq_trace_atom: seq_atomic seq_trace last_trace "\<lambda>c. (Trace c (empty_trace Term))" first_trace atomic_trace
  apply (standard)
            apply (intro set_eqI; clarsimp simp: atomic_trace_def)
            apply (intro conjI impI; clarsimp)
  using le_step_last_trace_disj  apply metis
          apply (rule step_ref_test_step)
         apply (clarsimp)
        apply (clarsimp)
       apply (rule step_le_step_append_test)
      apply (safe; clarsimp)
      apply (metis atomic_trace_def bot_eq_iff bottom_idemp index_empty isl_iff lengthS_singleton sum.disc(2) tr.simps(1) zero_less_one)
     apply (erule seq_step_le_matching)
    apply (clarsimp)
  apply (erule (3) seq_inf_interchange)
  using seq_trace_step_leD apply blast
  by (meson atomic_trace_cases)

lemma trace_eq_bot_iff[simp]:"Trace a b  = y\<^sub>\<bottom> \<longleftrightarrow> b = empty_trace Incomplete \<and> (bottom y) = Trace a b"
  apply (intro iffI)
   apply (cases y; clarsimp)
  apply (clarsimp)
  done

find_theorems zip_trace' Inr

lemma sync_fails_immediately: "sync_step f (index t 0) (index t' 0) = Inr c \<Longrightarrow>  sync_trace f t t' = empty_trace c"
  by (metis first_None_iff first_def index_zip_trace'_zero 
           lengthS_zero_empty_trace old.sum.simps(6) sum.sel(2) sync_trace_def)

lemma empty_eq_bot_iff[simp]: "Empty = y\<^sub>\<bottom> \<longleftrightarrow> y = Empty" 
  by (cases y; clarsimp)

lemma in_omega_par_step_omega: "x \<in> \<Omega> \<Longrightarrow> par_t (seq_trace (atomic_trace l s) c) x \<in> \<Omega>"
  apply (clarsimp)
  apply (rule_tac x="par_t (seq_trace (atomic_trace l s) c) y" in exI)
  apply (rule Trace_eqI; clarsimp?)
   apply (clarsimp simp: par_t_def)
  apply (cases x; clarsimp)
   apply (clarsimp simp: par_t_def split: if_splits option.splits)
   apply (safe; clarsimp)
     apply (metis init.simps(1) init_bottom_simp option.distinct(1))
    apply (clarsimp simp: seq_trace_def appendS_iff_cons, safe, clarsimp?)
     apply (smt (verit, ccfv_SIG) bottom_Trace.simps(2) incomplete_index_len incomplete_trace_empty index_cons_t index_immediate_sync_trace 
       index_zip_trace'_zero isl_def lengthS_empty option.sel sum.disc(2) sync_bottom sync_step_par_incomp' sync_trace_def sync_trace_par_sync_assoc tr.simps(2))
    apply (rule sync_fails_immediately)
    apply (clarsimp simp: index_cons_t)
    apply (rule sync_fails_immediately)
  by (clarsimp simp: index_cons_t seq_trace_def appendS_iff_cons)

lemma test_par_omega_omega: "x \<in> \<Omega> \<Longrightarrow> par_t (Trace t (empty_trace Term)) x \<in> \<Omega>"
  apply (clarsimp)
  apply (rule_tac x="par_t (Trace t (empty_trace Term)) y" in exI)
  apply (rule Trace_eqI; clarsimp?)
   apply (clarsimp simp: par_t_def)
   apply (clarsimp simp: par_t_def)
  done

lemma test_conj_omega_omega: "x \<in> \<Omega> \<Longrightarrow> conj_t (Trace t (empty_trace Term)) x \<in> \<Omega>"
  apply (clarsimp)
  apply (rule_tac x="conj_t (Trace t (empty_trace Term)) y" in exI)
  apply (rule Trace_eqI; clarsimp?)
   apply (clarsimp simp: conj_t_def)
   apply (clarsimp simp: conj_t_def)
  done

lemma in_omega_conj_step_omega: "x \<in> \<Omega> \<Longrightarrow> conj_t (seq_trace (atomic_trace l s) c) x \<in> \<Omega>"
  apply (clarsimp)
  apply (rule_tac x="conj_t (seq_trace (atomic_trace l s) c) y" in exI)
  apply (rule Trace_eqI; clarsimp?)
   apply (clarsimp simp: conj_t_def)
  apply (cases x; clarsimp)
   apply (clarsimp simp: conj_t_def split: if_splits option.splits)
   apply (safe; clarsimp)
     apply (metis init.simps(1) init_bottom_simp option.distinct(1))
   apply (clarsimp simp: seq_trace_def appendS_iff_cons, safe, clarsimp?)
    apply (rule sync_fails_immediately)
    apply (clarsimp simp: index_cons_t)
   apply (clarsimp simp: sync_fails_immediately index_cons_t)
    apply (rule sync_fails_immediately)
    apply (clarsimp simp: index_cons_t)
  by (clarsimp simp: index_cons_t seq_trace_def appendS_iff_cons)

declare index_cons_t[simp]

lemma par_test_step_omega: "par_t (Trace t (empty_trace Term)) (seq_trace (atomic_trace l s) x) \<in> \<Omega>"
  apply (clarsimp)
  apply (case_tac "t = fst s"; clarsimp?)
   apply (rule_tac x="(Trace t (empty_trace Term))" in exI; clarsimp)
   apply (rule Trace_eqI; clarsimp simp: par_t_def)
   apply (clarsimp simp: seq_trace_def appendS_iff_cons)
   apply (safe)
    apply (rule sync_fails_immediately)
    apply (clarsimp simp: )

    apply (rule sync_fails_immediately)
   apply (clarsimp simp: )
  apply (rule_tac x="Empty" in exI)
  apply (rule Trace_eqI; clarsimp simp: par_t_def)
  done

lemma conj_test_step_omega: "conj_t (Trace t (empty_trace Term)) (seq_trace (atomic_trace l s) x) \<in> \<Omega>"
  apply (clarsimp)
  apply (case_tac "t = fst s"; clarsimp?)
   apply (rule_tac x="(Trace t (empty_trace Term))" in exI; clarsimp)
   apply (rule Trace_eqI; clarsimp simp: conj_t_def)
   apply (clarsimp simp: seq_trace_def appendS_iff_cons)
   apply (safe)
    apply (rule sync_fails_immediately)
    apply (clarsimp simp: )

    apply (rule sync_fails_immediately)
   apply (clarsimp simp: )
  apply (rule_tac x="Empty" in exI)
  apply (rule Trace_eqI; clarsimp simp: conj_t_def)
  done

lemma isr_sync_isr[simp]: "\<not>isl (sync_step f (Inr x) c)"
  apply (cases x; cases c; clarsimp) by (case_tac b; clarsimp)+


lemma isr_sync_isr'[simp]: "\<not>isl (sync_step f c (Inr x))"
  by (cases x; cases c; clarsimp) 

lemma sync_singletons_all: "(sync_trace f (singleton c x) (singleton d y)) =  case_sum (\<lambda>z. singleton z (projr (sync_step f (Inr x) (Inr y)))) empty_trace (f c d)"
  apply (clarsimp split: sum.splits)
  apply (safe)
   apply (rule trace_eqI)
   apply (induct_tac n; clarsimp simp: sync_trace_def)
   apply (case_tac "index (zip_trace' (sync_step f) (singleton c x) (singleton d y)) na"; clarsimp)
    apply (drule sym; clarsimp)
  apply (drule sym; clarsimp)
   apply (case_tac na; clarsimp)
apply (rule trace_eqI)
   apply (induct_tac n; clarsimp simp: sync_trace_def)
  done

lemma sync_singletons: "(sync_trace f (singleton c Term) (singleton d Term)) = case_sum (\<lambda>x. singleton x Term) empty_trace (f c d)"
  apply (clarsimp split: sum.splits)
  apply (safe)
   apply (rule trace_eqI)
   apply (induct_tac n; clarsimp simp: sync_trace_def)
   apply (case_tac "index (zip_trace' (sync_step f) (singleton c Term) (singleton d Term)) na"; clarsimp)
    apply (drule sym; clarsimp)
  apply (drule sym; clarsimp)
   apply (case_tac na; clarsimp)
apply (rule trace_eqI)
   apply (induct_tac n; clarsimp simp: sync_trace_def)
  done

lemma par_sync_env_iff[simp]: "par_sync a b = Inl (Step.Env s) \<longleftrightarrow> a =  (Step.Env s) \<and> b =  (Step.Env  s) "
  by (cases a; cases b; clarsimp)

lemma par_sync_pgm_iff[simp]: "par_sync a b = Inl (Step.Pgm s) \<longleftrightarrow> (a =  (Step.Env s) \<and> b =  (Step.Pgm  s) \<or> a =  (Step.Pgm s) \<and> b =  (Step.Env  s)) "
  by (cases a; cases b; clarsimp)


lemma "(par_sync a b = Inr c) \<Longrightarrow> c = Incomplete "
  by (cases a; cases b; clarsimp split: if_splits)


lemma seq_atomic_match_simp[simp]:" snd s = a \<Longrightarrow> (seq_trace (atomic_trace l s) (Trace a t)) = Trace (fst s) (cons_t (label_map l (snd s)) t )"
  by (clarsimp simp: seq_trace_def appendS_iff_cons)

lemma last_trace_bot[simp]:"last_trace (bottom y) = Empty"
  by (cases y; clarsimp)

lemma label_map_env_iff[simp]: " label_map l s = Step.Env x \<longleftrightarrow> l = labels.Env \<and> s = x"
  by (clarsimp simp: label_map_def)


lemma label_map_pgm_iff[simp]: " label_map l s = Step.Pgm x \<longleftrightarrow> l = labels.Pgm \<and> s = x"
  by (clarsimp simp: label_map_def)


lemma le_par_stepsD:"x \<le> par_t (atomic_trace l s) (atomic_trace l' s') \<Longrightarrow>  x \<notin> \<Omega> \<Longrightarrow> \<exists>l'' s''. x \<le> atomic_trace l'' s'' \<and> atomic_trace l'' s'' \<le> par_t (atomic_trace l s) (atomic_trace l' s')"
  apply (subst (asm) par_t_def, clarsimp)
  apply (clarsimp split: if_splits)
   apply (clarsimp simp: sync_singletons split: sum.splits)
   apply (case_tac x1; clarsimp simp: par_sync_env_iff)
    apply (subgoal_tac "x \<le> atomic_trace l (fst s, snd s)", frule atomic_trace_cases)
  apply (elim disjE; clarsimp )
     apply (clarsimp simp: atomic_trace_simp)
      apply (rule_tac x="labels.Env" in exI, clarsimp)
      apply (rule_tac x="fst s" in exI)
      apply (rule_tac x="snd s" in exI)
      apply (clarsimp)
      apply (clarsimp simp: par_t_def sync_singletons)
  apply (clarsimp simp: atomic_trace_simp)
      apply (rule_tac x="labels.Env" in exI, clarsimp)
      apply (rule_tac x="fst s" in exI)
      apply (rule_tac x="snd s" in exI)
      apply (clarsimp)
     apply (clarsimp simp: par_t_def sync_singletons)
    apply (simp add: atomic_trace_simp)
   apply (elim disjE; clarsimp simp: label_map_def split: if_splits)
    apply (subgoal_tac "x \<le> atomic_trace labels.Pgm (fst s, snd s)")
     apply (elim disjE; clarsimp )
     apply (clarsimp simp: atomic_trace_simp)
     apply (rule_tac x="labels.Pgm" in exI, clarsimp, rule exI, rule exI, intro conjI)
      apply (assumption)
     apply (clarsimp simp: par_t_def sync_singletons)
    apply (clarsimp simp: atomic_trace_simp)
apply (clarsimp simp: atomic_trace_simp)
     apply (rule_tac x="labels.Pgm" in exI, clarsimp, rule exI, rule exI, intro conjI)
      apply (assumption)
     apply (clarsimp simp: par_t_def sync_singletons)
  apply (clarsimp simp: atomic_trace_simp)
  apply (erule_tac x="Trace (fst s') (empty_trace x2)" in allE)
  apply (clarsimp)
  using preorder_bot_class.bot_least by fastforce


lemma failed_cons_empty_iff[simp]: "failed_trace (Trace a (cons_t b (empty_trace c))) \<longleftrightarrow> c = Incomplete \<or> c = Abort" sorry

lemma sync_cons: "sync_trace f (cons_t s t) (cons_t s' t') = case_sum (\<lambda>x. cons_t x (sync_trace f t t')) (empty_trace) (f s s')" sorry 



find_theorems seq_trace par_t


lemma seq_atomic_nomatch_simp[simp]:" snd s \<noteq> a \<Longrightarrow> (seq_trace (atomic_trace l s) (Trace a t)) = Trace (fst s) (cons_t (label_map l (snd s)) (empty_trace Incomplete) )"
  by (clarsimp simp: seq_trace_def appendS_iff_cons)

lemma "index t 0 \<noteq> Inr Abort \<Longrightarrow> sync_trace par_sync (empty_trace Incomplete) t = (empty_trace Incomplete)"
  by (simp add: sync_fails_immediately)

lemma par_sync_inl_state_of: "par_sync (label_map l s) (label_map l' s') = Inl x1 \<Longrightarrow>  s = s' \<and>  state_of x1 = s"
  sorry


lemma aborting_par_seq_sync: " index (tr y) 0 = Inr Abort \<Longrightarrow>  
   par_t (seq_trace (atomic_trace l s) y) (seq_trace (atomic_trace l' s') b) \<le> seq_trace (par_t (atomic_trace l s) (atomic_trace l' s')) (par_t y (bottom y)) \<or>
   par_t (seq_trace (atomic_trace l s) y) (seq_trace (atomic_trace l' s') b) \<le> seq_trace (par_t (atomic_trace l s) (atomic_trace l' s')) (par_t b (bottom b))"
  apply (case_tac "index (tr b) 0 = Inr Abort")
  defer
  apply (subgoal_tac "(par_t y (bottom y)) = (trace (init y) (empty_trace Abort))", clarsimp)
   apply (case_tac y; clarsimp)
   apply (case_tac b; clarsimp)
    apply (clarsimp simp: par_t_def)
    apply (case_tac "snd s = x11"; clarsimp)
     apply (case_tac "snd s' = x11a"; clarsimp)
      apply (clarsimp simp: sync_singletons_all sync_cons split: sum.splits)
      apply (clarsimp simp: seq_trace_def  appendS_iff_cons sync_cons appendS_iff_cons sync_cons sync_fails_immediately split: sum.splits)
      apply (meson par_sync_inl_state_of)
      apply (clarsimp simp: sync_singletons_all sync_cons split: sum.splits)

     apply (clarsimp simp: seq_trace_def  appendS_iff_cons sync_cons appendS_iff_cons sync_cons sync_fails_immediately split: sum.splits)
     apply (meson par_sync_inl_state_of)
     apply (case_tac "snd s' = x11a"; clarsimp)

 apply (clarsimp simp: sync_singletons_all sync_cons split: sum.splits)

     apply (clarsimp simp: seq_trace_def  appendS_iff_cons sync_cons appendS_iff_cons sync_cons sync_fails_immediately split: sum.splits)
      apply (metis par_sync_inl_state_of)
     apply (clarsimp simp: sync_singletons_all sync_cons split: sum.splits)
     apply (clarsimp simp: seq_trace_def  appendS_iff_cons sync_cons appendS_iff_cons sync_cons sync_fails_immediately split: sum.splits)
     apply(rule trace_refI; clarsimp)
    apply (case_tac "snd s = x11"; clarsimp)
  apply (clarsimp simp: par_t_def)

     apply (clarsimp simp: sync_singletons_all sync_cons split: sum.splits)
     apply (clarsimp simp: seq_trace_def  appendS_iff_cons sync_cons appendS_iff_cons sync_cons sync_fails_immediately split: sum.splits)
      apply (drule par_sync_inl_state_of, clarsimp)
     apply (subgoal_tac "x2 = Incomplete"; clarsimp)
     apply (clarsimp simp: seq_trace_def  appendS_iff_cons sync_cons appendS_iff_cons sync_cons sync_fails_immediately split: sum.splits)
    apply (clarsimp simp: par_t_def)
    apply (clarsimp simp: sync_singletons_all sync_cons split: sum.splits)
     apply (clarsimp simp: seq_trace_def  appendS_iff_cons sync_cons appendS_iff_cons sync_cons sync_fails_immediately split: sum.splits)
     apply (clarsimp simp: seq_trace_def  appendS_iff_cons sync_cons appendS_iff_cons sync_cons sync_fails_immediately split: sum.splits)
   apply (clarsimp simp: par_t_def)
  apply (simp add: par_t_def)
  apply (intro impI)
  apply (case_tac y; simp)
  apply (case_tac b; simp)
  apply (case_tac "snd s = x11"; simp)
   apply (case_tac "snd s' = x11a"; simp?)
    apply (simp add: sync_cons sync_singletons_all split: sum.splits)
    apply (intro conjI impI allI)
    apply (clarsimp simp: seq_trace_def  appendS_iff_cons sync_cons appendS_iff_cons sync_cons sync_fails_immediately split: sum.splits)
    apply (drule par_sync_inl_state_of, clarsimp)
   apply (simp add: sync_cons sync_singletons_all split: sum.splits)
   apply (intro conjI impI allI)
   apply (clarsimp simp: seq_trace_def  appendS_iff_cons sync_cons appendS_iff_cons sync_cons sync_fails_immediately split: sum.splits)
   apply (drule par_sync_inl_state_of, clarsimp)
  apply (case_tac "snd s' = x11a"; simp?)
 apply (simp add: sync_cons sync_singletons_all split: sum.splits)
    apply (intro conjI impI allI)
    apply (clarsimp simp: seq_trace_def  appendS_iff_cons sync_cons appendS_iff_cons sync_cons sync_fails_immediately split: sum.splits)
    apply (drule par_sync_inl_state_of, clarsimp)
   apply (simp add: sync_cons sync_singletons_all split: sum.splits)
   apply (intro conjI impI allI)
   apply (clarsimp simp: seq_trace_def  appendS_iff_cons sync_cons appendS_iff_cons sync_cons sync_fails_immediately split: sum.splits)
  apply (drule par_sync_inl_state_of, clarsimp)
  done


lemma bottom_par_seq_sync: " x \<in> \<Omega> \<Longrightarrow> 
   par_t (seq_trace x y) (seq_trace (atomic_trace l s) b) \<le> seq_trace (par_t x (atomic_trace l s)) (par_t y b)" 
  apply (cases x; clarsimp)
  apply (clarsimp simp: par_t_def)
  apply (intro conjI impI allI)
   apply (clarsimp simp: sync_fails_immediately)
   apply (subst sync_fails_immediately[where c="Incomplete"]; clarsimp?)
  apply (clarsimp simp: appendS_iff_cons seq_trace_def split: if_splits)
  apply (subst sync_fails_immediately[where c="Incomplete"]; clarsimp?)
  apply (clarsimp simp: appendS_iff_cons seq_trace_def split: if_splits)
  apply (subst sync_fails_immediately[where c="Incomplete"]; clarsimp?)
  done


lemma nonaborting_par_seq_sync: " index (tr y) 0 \<noteq> Inr Abort \<Longrightarrow> index (tr b) 0 \<noteq> Inr Abort \<Longrightarrow> 
   par_t (seq_trace (atomic_trace l s) y) (seq_trace (atomic_trace l' s') b) \<le> seq_trace (par_t (atomic_trace l s) (atomic_trace l' s')) (par_t y b)"
  apply (case_tac s; case_tac s'; clarsimp)
  apply (clarsimp simp: par_t_def)
  apply (safe)
   apply (subst sync_singletons_all, clarsimp split: sum.splits, safe ; clarsimp?)
    apply (case_tac x1; clarsimp)
     apply (cases b; clarsimp)
      apply (cases y; clarsimp)
      apply (case_tac "ba = x11", clarsimp)
       apply (subst sync_cons; clarsimp split: sum.splits)
       apply (metis atomic_trace_simp fst_conv label_map_env_iff order_refl seq_atomic_match_simp snd_conv)
      apply (subst seq_atomic_nomatch_simp; clarsimp)+
      apply (clarsimp simp: seq_trace_def)
       apply (subst sync_cons; clarsimp split: sum.splits)
      apply (simp add: appendS_iff_cons)
     apply (subgoal_tac "y = Empty"; clarsimp?)
      apply (clarsimp simp: seq_trace_def appendS_iff_cons sync_cons)
     apply (metis trace_None_simp trace_init_empty_iff)
    apply (elim disjE; clarsimp)
     apply (cases b; clarsimp)
      apply (cases y; clarsimp)
      apply (case_tac "ba = x11", clarsimp)
       apply (clarsimp simp: seq_trace_def appendS_iff_cons sync_cons)
      apply (subst seq_atomic_nomatch_simp; clarsimp)+
      apply (clarsimp simp: seq_trace_def appendS_iff_cons sync_cons)
     apply (subgoal_tac "y = Empty"; clarsimp?)
      apply (clarsimp simp: seq_trace_def appendS_iff_cons sync_cons)
     apply (metis trace_None_simp trace_init_empty_iff)
apply (cases b; clarsimp)
      apply (cases y; clarsimp)
      apply (case_tac "ba = x11", clarsimp)
       apply (clarsimp simp: seq_trace_def appendS_iff_cons sync_cons)
      apply (subst seq_atomic_nomatch_simp; clarsimp)+
      apply (clarsimp simp: seq_trace_def appendS_iff_cons sync_cons)
     apply (subgoal_tac "y = Empty"; clarsimp?)
      apply (clarsimp simp: seq_trace_def appendS_iff_cons sync_cons)
    apply (metis trace_None_simp trace_init_empty_iff)
apply (cases b; clarsimp)
      apply (cases y; clarsimp)
    apply (case_tac "ba = x11")
     apply (case_tac "baa = x11"; clarsimp)
      apply (clarsimp simp: seq_trace_def appendS_iff_cons sync_cons)
      apply (clarsimp simp: seq_trace_def appendS_iff_cons sync_cons)
    apply (clarsimp)
    apply (case_tac "baa = x11"; clarsimp)
      apply (clarsimp simp: seq_trace_def appendS_iff_cons sync_cons)
      apply (clarsimp simp: seq_trace_def appendS_iff_cons sync_cons)
     apply (subgoal_tac "y = Empty"; clarsimp?)
      apply (clarsimp simp: seq_trace_def appendS_iff_cons sync_cons)
   apply (metis trace_None_simp trace_init_empty_iff) 
apply (cases b; clarsimp)
   apply (cases y; clarsimp)
    apply (clarsimp simp: sync_singletons split: sum.splits)
    apply (intro conjI impI allI; clarsimp?)
     apply (case_tac x1; clarsimp)
      apply (case_tac "ba = x11", clarsimp)
      apply (clarsimp simp:  appendS_iff_cons sync_cons split: sum.splits)
      apply (clarsimp simp: seq_trace_def appendS_iff_cons sync_cons sync_fails_immediately)
      apply (clarsimp)
      apply (case_tac "ba = x11a"; clarsimp)
      apply (clarsimp simp:  appendS_iff_cons sync_cons split: sum.splits)
       apply (clarsimp simp: seq_trace_def appendS_iff_cons sync_cons sync_fails_immediately)
      apply (clarsimp simp:  appendS_iff_cons sync_cons split: sum.splits)
      apply (clarsimp simp: seq_trace_def  appendS_iff_cons sync_cons appendS_iff_cons sync_cons sync_fails_immediately split: sum.splits)
     apply (elim disjE; clarsimp)
      apply (case_tac "ba = x11"; clarsimp)
      apply (clarsimp simp: seq_trace_def  appendS_iff_cons sync_cons appendS_iff_cons sync_cons sync_fails_immediately split: sum.splits)
      apply (clarsimp simp: seq_trace_def  appendS_iff_cons sync_cons appendS_iff_cons sync_cons sync_fails_immediately split: sum.splits)
 apply (case_tac "ba = x11"; clarsimp)
      apply (clarsimp simp: seq_trace_def  appendS_iff_cons sync_cons appendS_iff_cons sync_cons sync_fails_immediately split: sum.splits)
     apply (clarsimp simp: seq_trace_def  appendS_iff_cons sync_cons appendS_iff_cons sync_cons sync_fails_immediately split: sum.splits)
    apply (case_tac "ba = x11"; clarsimp?)
     apply (clarsimp simp: seq_trace_def  appendS_iff_cons sync_cons appendS_iff_cons sync_cons sync_fails_immediately split: sum.splits)
    apply (clarsimp simp: seq_trace_def  appendS_iff_cons sync_cons appendS_iff_cons sync_cons sync_fails_immediately split: sum.splits)
   apply (case_tac "baa = x11"; clarsimp?)
    apply (clarsimp simp: seq_trace_def  appendS_iff_cons sync_cons appendS_iff_cons sync_cons sync_fails_immediately split: sum.splits)
  apply (safe)
     apply (simp add: sync_singletons)
    apply (clarsimp simp: sync_singletons appendS_iff_cons)
    apply (clarsimp simp: seq_trace_def  appendS_iff_cons sync_cons appendS_iff_cons sync_cons sync_fails_immediately split: sum.splits)
   apply (safe)
    apply (clarsimp simp: sync_singletons appendS_iff_cons)
    apply (clarsimp simp: sync_singletons appendS_iff_cons)
  apply (case_tac y; clarsimp)
  apply (case_tac "ba = ya"; clarsimp?)
    apply (clarsimp simp: seq_trace_def  appendS_iff_cons sync_cons appendS_iff_cons sync_cons sync_fails_immediately split: sum.splits)
  apply (safe)
    apply (clarsimp simp: sync_singletons appendS_iff_cons)
    apply (clarsimp simp: sync_singletons appendS_iff_cons)
    apply (clarsimp simp: seq_trace_def  appendS_iff_cons sync_cons appendS_iff_cons sync_cons sync_fails_immediately split: sum.splits)
 apply (safe)
    apply (clarsimp simp: sync_singletons appendS_iff_cons)
  apply (clarsimp simp: sync_singletons appendS_iff_cons)
  done

lemma par_t_not_in_omega: "par_t y (y\<^sub>\<bottom>) \<in> \<Omega>  \<longleftrightarrow> index (tr y) 0 \<noteq> Inr Abort"
  apply (clarsimp)
  apply (cases y; clarsimp)
  apply (clarsimp simp: par_t_def)
  apply (safe; clarsimp?)
   apply (simp add: sync_fails_immediately)
  apply (rule_tac x="Trace x11 (sync_trace par_sync x12 (empty_trace Incomplete))" in exI)
   apply (simp add: sync_fails_immediately)
  done


thm nonaborting_par_seq_sync
interpretation cra_trace_sync: cra_atomic_sync conj_t regular par_t env seq_trace last_trace "\<lambda>c. (Trace c (empty_trace Term))" first_trace atomic_trace
  apply (standard)
               apply (rule aborting_par_seq_sync)
  using par_t_not_in_omega 
  apply blast
  apply (rule nonaborting_par_seq_sync)
                apply (subst (asm) par_t_not_in_omega, assumption)
  apply (subst (asm) par_t_not_in_omega, assumption)
  using bottom_par_seq_sync apply blast
  using in_omega_par_step_omega apply blast
            apply (meson test_par_omega_omega)
  apply (metis par_test_step_omega)
  
         apply (erule (1) le_par_stepsD)
  sorry

lemma fmap_cons[simp]:"fmap_trace proj_env proj_sym (cons_t s t) = cons_t (proj_env s) (fmap_trace proj_env proj_sym t)"
  by (rule trace_eqI; clarsimp simp: index_fmap)

lemma index_fst_seq_atomic: "index (tr (seq_trace (atomic_trace l s) d)) 0 = Inl (label_map l (snd s))"
  by (clarsimp simp:seq_trace_def appendS_iff_cons)

lemma no_pgm_and_env: "x \<le> seq_trace (atomic_trace labels.Pgm s) c \<Longrightarrow> x \<le> seq_trace (atomic_trace labels.Env s') d \<Longrightarrow> x \<in> \<Omega>"
  apply (clarsimp)
  apply (rule_tac x=x in exI)
  apply (cases x; clarsimp)
  apply (subgoal_tac "index x12 0 = Inr Incomplete")
   apply (rule trace_eqI)
   apply auto[1]
  apply (subgoal_tac "ref_step (index x12 0) (Inl (Pgm (snd s)))")
   apply (subgoal_tac "ref_step (index x12 0) (Inl (Env (snd s)))")
    apply (case_tac "index x12 0"; clarsimp)
    apply (drule_tac n=0 in less_eq_ref_stepD)+
   apply (simp add: index_fst_seq_atomic)
   apply (elim disjE; clarsimp)
 apply (drule_tac n=0 in less_eq_ref_stepD)+
  by (simp add: index_fst_seq_atomic)


interpretation cra_atomic_traces: cra_atomic_elem conj_t regular par_t env seq_trace last_trace "\<lambda>c. (Trace c (empty_trace Term))" first_trace atomic_trace
  apply (standard)
     apply (clarsimp simp: seq_trace_def appendS_iff_cons)
     apply (safe; clarsimp?)
       apply (case_tac l; clarsimp)
      apply (case_tac c; clarsimp)
       apply (case_tac l; clarsimp)
    apply (clarsimp simp: par_t_def sync_singletons split: if_splits sum.splits)
    apply (safe; clarsimp?)
     apply (metis Inl_inject atomic_trace_simp label_map_def order_le_less par_sync_env_iff par_sync_pgm_iff)
    apply (clarsimp simp: atomic_trace_simp)
    apply (case_tac l; clarsimp)
    apply (case_tac l; clarsimp)
    apply (clarsimp simp: par_t_def sync_singletons atomic_trace_simp split: if_splits sum.splits)
   apply (clarsimp simp: par_t_def sync_singletons atomic_trace_simp split: if_splits sum.splits)
  apply (erule (1) no_pgm_and_env)
  done

lemma le_reg_not_aborted: "\<not>aborted_trace x \<Longrightarrow> x \<le> regular x"
  apply (clarsimp simp: regular_def)
  apply (clarsimp simp: failed_trace_def)
  apply (rule trace_refI; clarsimp)
  apply (cases x; clarsimp)
  apply (rule appendS_induct; clarsimp?)
  apply (clarsimp simp: index_append)
  using incomplete_index_len isr_antitone by fastforce

lemma failed_trace_iff: "failed_trace (Trace a t) \<longleftrightarrow> (\<exists>n b. index t n = Inr b \<and> (b = Abort \<or> b = Incomplete))" sorry

lemma aborted_trace_iff_index: "aborted_trace (Trace a t) \<longleftrightarrow> (\<exists>n. index t n = Inr Abort)" sorry


lemma map_env_never_abort[simp]: "map_sum proj_env proj_sym a = Inr Abort \<longleftrightarrow> False"
  apply (case_tac a; clarsimp)
  apply (case_tac b; clarsimp)
  done

lemma map_env_never_pgm[simp]: "map_sum proj_env proj_sym a = Inl (Pgm s) \<longleftrightarrow> False"
  apply (case_tac a; clarsimp)
  apply (case_tac aa; clarsimp)
  done


lemma lengthS_tailI:"lengthS t = Some (Suc m) \<Longrightarrow> lengthS (tail t) = Some m " 
  apply (rule lengthS_eqI; clarsimp?)
  by (intro conjI impI; (clarsimp simp: index_tail_iff isl_iff)?)

lemma appendS_is_seq_pgm: "index t 0 = Inl (Pgm b) \<Longrightarrow> (Trace a (appendS t (empty_trace Term))) = seq_trace (atomic_trace (labels.Pgm) (a, b)) (Trace b (appendS (tail t) (empty_trace Term)))"
  apply (clarsimp simp: appendS_iff_cons)
  apply (rule trace_eqI; clarsimp, intro conjI impI)
   apply (rule appendS_induct[where x=t]; clarsimp simp: index_clean index_append)
   apply (metis isl_iff sum.disc(1))
   apply (rule appendS_induct[where x=t]; clarsimp simp: index_clean index_append)
   apply (intro conjI; clarsimp?)
    apply (case_tac m; clarsimp)
    apply (subgoal_tac "lengthS (tail t) = Some nat"; (clarsimp simp: index_append)?)
  apply (intro conjI impI)
      apply (clarsimp simp: index_tail_iff)
     apply simp
    apply (erule lengthS_tailI)
    apply (case_tac m; clarsimp)

    apply (metis isl_iff less_numeral_extra(3) sum.disc(1))
   apply (subgoal_tac "lengthS (tail t) = Some nat"; (clarsimp simp: index_append)?)
      apply (clarsimp simp: index_tail_iff)
     apply simp
   apply (erule lengthS_tailI)
  apply (subgoal_tac "lengthS (tail t) = None"; clarsimp?)
   apply (simp add: index_clean index_tail_iff)
  by (metis finiteS_def index_tail_iff inf_all_l lengthS_def)

lemma appendS_is_seq_env: "index t 0 = Inl (Env b) \<Longrightarrow> (Trace a (appendS t (empty_trace Term))) = seq_trace (atomic_trace (labels.Env) (a, b)) (Trace b (appendS (tail t) (empty_trace Term)))"
  apply (clarsimp simp: appendS_iff_cons)
  apply (rule trace_eqI; clarsimp, intro conjI impI)
   apply (rule appendS_induct[where x=t]; clarsimp simp: index_clean index_append)
   apply (metis isl_iff sum.disc(1))
   apply (rule appendS_induct[where x=t]; clarsimp simp: index_clean index_append)
   apply (intro conjI; clarsimp?)
    apply (case_tac m; clarsimp)
    apply (subgoal_tac "lengthS (tail t) = Some nat"; (clarsimp simp: index_append)?)
  apply (intro conjI impI)
      apply (clarsimp simp: index_tail_iff)
     apply simp
    apply (erule lengthS_tailI)
    apply (case_tac m; clarsimp)

    apply (metis isl_iff less_numeral_extra(3) sum.disc(1))
   apply (subgoal_tac "lengthS (tail t) = Some nat"; (clarsimp simp: index_append)?)
      apply (clarsimp simp: index_tail_iff)
     apply simp
   apply (erule lengthS_tailI)
  apply (subgoal_tac "lengthS (tail t) = None"; clarsimp?)
   apply (simp add: index_clean index_tail_iff)
  by (metis finiteS_def index_tail_iff inf_all_l lengthS_def)

lemma append_term_is_finite_obs: "failed_trace x \<Longrightarrow> \<not> x \<le> trace (init x) (appendS (tr x) (empty_trace Incomplete)) \<Longrightarrow> lengthS (tr x) = Some m \<Longrightarrow> cra_atomic_traces.finite_obs {labels.Pgm, labels.Env} m (trace (init x) (appendS (tr x) (empty_trace Term)))"
  apply (induct m arbitrary: x; clarsimp?)
   apply (case_tac x; clarsimp)
  apply (case_tac x; clarsimp)
       apply (case_tac "index x12 0", case_tac a; clarsimp?)
    apply (atomize)
    apply (erule_tac x="Trace x1 (tail x12)" in allE)
    apply (drule mp)
     apply (metis dual_order.refl failed_trace_iff index_tail_iff isr_antitone le_Suc_eq)
  apply (subgoal_tac "lengthS (tail x12) = Some m")
     apply (drule mp; clarsimp)
     apply (erule notE)
     apply (rule trace_refI; clarsimp simp: index_append)
     apply (drule trace_refD, clarsimp)
      apply (erule_tac x=" n" in allE; clarsimp simp: index_tail_iff index_append)
      apply (metis aborted_end incomplete_index_len isr_antitone lengthS_some_finite nat_le_linear not_failed_finite_index_iff option.sel tr.simps(1))
  apply (subst appendS_is_seq_env, assumption)
     apply (erule cra_atomic_traces.finite_obs.stepI, clarsimp, clarsimp)
    apply (erule lengthS_tailI)
apply (atomize)
    apply (erule_tac x="Trace x2 (tail x12)" in allE)
    apply (drule mp)
     apply (metis dual_order.refl failed_trace_iff index_tail_iff isr_antitone le_Suc_eq)
  apply (subgoal_tac "lengthS (tail x12) = Some m")
     apply (drule mp; clarsimp)
     apply (erule notE)
     apply (rule trace_refI; clarsimp simp: index_append)
     apply (drule trace_refD, clarsimp)
      apply (erule_tac x=" n" in allE; clarsimp simp: index_tail_iff index_append)
      apply (metis aborted_end incomplete_index_len isr_antitone lengthS_some_finite nat_le_linear not_failed_finite_index_iff option.sel tr.simps(1))
  apply (subst appendS_is_seq_pgm, assumption)
     apply (erule cra_atomic_traces.finite_obs.stepI, clarsimp, clarsimp)
   apply (erule lengthS_tailI)
  by (metis isl_iff sum.disc(2) zero_less_Suc)


lemma seq_immediately_abort: "seq_trace (trace x (empty_trace Abort)) c =  (trace x (empty_trace Abort))"
  by (case_tac x; clarsimp)

lemma seq_trace_empty_matching: "seq_trace (trace (init x) (empty_trace Term)) (trace (init x) t) = trace (init x) t"
  apply (case_tac x; clarsimp)
  apply (clarsimp simp: seq_trace_def)
  done

lemma finite_appendS_term_term:"finiteS t \<Longrightarrow> terminates (appendS t (empty_trace Term))"
  apply (rule appendS_induct[where x=t], clarsimp)
   apply (simp add: index_append lengthS_appendI' terminates_def)
  apply (clarsimp)
  by (simp add: finiteS_def)

lemma appendS_empty_term[simp]: "(appendS (empty_trace Term) d) = d"
  by (rule trace_eqI; clarsimp)

interpretation cra_atomic_iter_trace: cra_atomic_iter conj_t regular par_t env seq_trace last_trace "\<lambda>c. (Trace c (empty_trace Term))" first_trace atomic_trace
  apply (standard)
     apply (case_tac "x = Empty", rule disjI1)
      apply clarsimp
  apply (rule disjI2)
     apply (subst (asm) regular_def, clarsimp split: if_splits)
  apply (subgoal_tac "\<not>aborted_trace x")

      apply (case_tac x; clarsimp)
       apply (case_tac "index x12 0", case_tac a; clarsimp?)
         apply (erule_tac x=labels.Env in allE)
         apply (erule_tac x=x11 in allE)
         apply (erule_tac x=x1 in allE)
         apply (erule_tac x="Trace x1 (tail x12)" in allE)
         apply (drule mp)
          apply (clarsimp)
          apply (rule trace_refI; clarsimp simp: index_tail_iff)
         apply (erule contrapos_np, rule le_reg_not_aborted)
         apply (rule ccontr; clarsimp)
         apply (clarsimp simp: failed_trace_iff index_tail_iff aborted_trace_iff_index)
  apply (erule_tac x=labels.Pgm in allE)
         apply (erule_tac x=x11 in allE)
         apply (erule_tac x=x2 in allE)
         apply (erule_tac x="Trace x2 (tail x12)" in allE)
         apply (drule mp)
          apply (clarsimp)
          apply (rule trace_refI; clarsimp simp: index_tail_iff)
         apply (erule contrapos_np, rule le_reg_not_aborted)
         apply (rule ccontr; clarsimp)
  apply (clarsimp simp: failed_trace_iff index_tail_iff aborted_trace_iff_index)
       apply (metis (mono_tags, lifting) empty_le first_None_iff' first_def lengthS_zero_empty_trace not_aborted_no_aborts old.sum.simps(6) order_refl sum.sel(2) symbols.exhaust tr.simps(1))
      apply (metis Inr_inject aborted_end failed_ref_nonfailed_incomplete failed_trace_def incomplete_index_len sup1I2 symbols.distinct(3))
     apply (case_tac x; clarsimp)
     apply (case_tac "index x12 0", case_tac a; clarsimp?)
apply (erule_tac x=labels.Env in allE)
         apply (erule_tac x=x11 in allE)
         apply (erule_tac x=x1 in allE)
         apply (erule_tac x="Trace x1 (tail x12)" in allE)
       apply (drule mp)
        apply (rule trace_refI; clarsimp simp: index_tail_iff)
       apply (erule contrapos_np, rule le_reg_not_aborted)
       apply (clarsimp simp: failed_trace_iff index_tail_iff aborted_trace_iff_index)
       apply (drule trace_refD, clarsimp)
       apply (erule_tac x="Suc n" in allE, clarsimp split: option.splits)
       apply (case_tac "\<exists>m. lengthS (tr y) = Some m"; clarsimp simp: index_append split: if_splits)
        apply (metis isl_iff sum.disc(2))
       apply (metis inf_all_l inf_is_clean sum.disc(2))
apply (erule_tac x=labels.Pgm in allE)
         apply (erule_tac x=x11 in allE)
         apply (erule_tac x=x2 in allE)
         apply (erule_tac x="Trace x2 (tail x12)" in allE)
       apply (drule mp)
        apply (rule trace_refI; clarsimp simp: index_tail_iff)
       apply (erule contrapos_np, rule le_reg_not_aborted)
       apply (clarsimp simp: failed_trace_iff index_tail_iff aborted_trace_iff_index)
       apply (drule trace_refD, clarsimp)
       apply (erule_tac x="Suc n" in allE, clarsimp split: option.splits)
       apply (case_tac "\<exists>m. lengthS (tr y) = Some m"; clarsimp simp: index_append split: if_splits)
        apply (metis isl_iff sum.disc(2))
      apply (metis inf_all_l inf_is_clean sum.disc(2))
     apply (rule_tac x=x11 in exI, rule trace_refI; clarsimp)
     apply (smt (verit, ccfv_SIG) bot_nat_0.extremum cpe.chaos_par_magic isr_antitone less_eq_ref_stepD 
                 par_t_not_in_omega proj_sym.cases ref_Abort_iff ref_step.simps(11) 
                 ref_step.simps(2) regular_def tr.simps(1))
  apply (case_tac "x = Empty", rule disjI1)
      apply clarsimp
    apply (rule disjI2)
    apply (case_tac y; clarsimp)
    apply (case_tac x; clarsimp)
  apply (case_tac "index x12a 0", case_tac a; clarsimp?)
         apply (erule_tac x=x11a in allE)
         apply (erule_tac x=x1 in allE)
         apply (erule_tac x="Trace x1 (tail x12a)" in allE)
         apply (drule mp)
          apply (clarsimp)
          apply (rule trace_refI; clarsimp simp: index_tail_iff)
      apply (erule contrapos_np)
      apply (clarsimp)
  apply (rule trace_refI; clarsimp)
      apply (clarsimp simp: failed_trace_iff index_tail_iff aborted_trace_iff_index index_fmap)
      apply (drule trace_refD, clarsimp)
      apply (erule_tac x="Suc n" in allE)
  apply (clarsimp simp: index_fmap)
  apply (case_tac "index x12a (Suc n)"; clarsimp)
       apply (metis isl_def isl_map_sum map_sum_sel(1) proj_env.elims proj_env.simps(2) sum.sel(1)) 
      apply (case_tac b; clarsimp)
      apply (drule trace_refD, clarsimp)
     apply (erule_tac x="0" in allE, clarsimp simp: index_fmap)
    apply (rule_tac x="x11a" in exI, rule trace_refI; clarsimp)
      apply (drule trace_refD, clarsimp)
     apply (erule_tac x="n" in allE, clarsimp simp: index_fmap)
    apply (metis (no_types, opaque_lifting) isr_antitone le0 map_env_never_abort proj_sym.cases ref_Abort_iff ref_step.simps(11) ref_step.simps(2))

   apply (clarsimp simp: regular_def split: if_splits)
  apply (case_tac "x = Empty"; clarsimp?)
   apply (subgoal_tac "\<exists>m. lengthS (tr x) = Some m"; clarsimp?)
    apply (rule_tac x="trace (init x) (appendS (tr x) (empty_trace Term))" in exI)
    apply (intro conjI)
     apply (rule_tac x=m in exI)
     apply (erule (2) append_term_is_finite_obs)
    apply (case_tac m; clarsimp)
     apply (rule_tac x="trace (init x) (empty_trace Abort)" in exI)
  apply (intro conjI)
  apply (clarsimp simp: conj_t_def split: option.splits)
       apply (case_tac x; clarsimp)
      apply (metis Trace.exhaust dual_order.refl first_trace_Trace init.simps(1) last_first_last trace_Some_simp)
     apply (rule_tac x="trace (init x) (empty_trace Abort)" in exI)
     apply (rule order_trans, rule assoc')
     apply (clarsimp simp: seq_immediately_abort seq_trace_empty_matching)
     apply (rule trace_refI; clarsimp split: option.splits)
     apply (metis Trace_eqI dual_order.refl failed_trace_empty_trace index_empty init.simps(1) lengthS_zero_empty_trace tr.simps(1))
    apply (rule_tac x="trace (map_option state_of (last ( (tr x)))) (empty_trace Abort)" in exI)
    apply (intro conjI)
      apply (clarsimp)
      apply (clarsimp simp: conj_t_def)
     apply (clarsimp)
     apply (case_tac x; clarsimp)
     apply (intro conjI impI)
      apply (rule trace_refI; clarsimp)
       apply (clarsimp simp: last_def lengthS_cons lengthS_appendI index_append split: sum.splits)
       apply (metis isl_iff lessI sum.disc(2))
      apply (clarsimp split: option.splits)
  using finite_appendS_term_term lengthS_some_finite apply blast
    apply (clarsimp simp: case_last_simp comp_def)
    apply (rule_tac x="trace (init x) (empty_trace Abort)" in exI)
     apply (rule order_trans, rule assoc')
    apply (clarsimp simp: seq_immediately_abort seq_trace_empty_matching)
    apply (rule trace_refI)
     apply (clarsimp)
    apply (case_tac x; clarsimp)
    apply (subgoal_tac "terminates (appendS x12 (empty_trace Term))")
  apply (case_tac "n \<le> nat")
    apply (subst seq_trace_def, simp only: Let_unfold split: if_splits)
      apply (intro conjI impI; clarsimp simp: appendS_assoc index_append)
       apply (subst appendS_assoc[symmetric], simp, clarsimp simp: index_append)
      apply (subst appendS_assoc[symmetric], simp)
     apply (subgoal_tac "index x12 n = Inr Abort"; clarsimp?)
     apply (erule contrapos_np)
     apply (rule trace_refI; clarsimp simp: index_append)
     apply (metis aborted_end failed_trace_def incomplete_index_len isr_antitone not_less_eq_eq option.sel sup1E tr.simps(1))
    apply (rule finite_appendS_term_term)
  using lengthS_some_finite apply blast
   apply (metis aborted_trace_def finiteS_def inf_all_l le_reg_not_aborted option.exhaust_sel regular_def)
  apply (case_tac x; clarsimp)
  sorry

end


definition "bindCont (f :: ('a \<Rightarrow> 'r) \<Rightarrow> 'r) (g :: 'a \<Rightarrow> ('b \<Rightarrow> 'r) \<Rightarrow> 'r) \<equiv> \<lambda>(c :: ('b \<Rightarrow> 'r)). f (\<lambda>a. g a c) ::  'r" 

definition "return a f = f a"

type_synonym ('a, 'r) cont = "('a \<Rightarrow> 'r) \<Rightarrow> 'r"

type_notation cont (infixr "\<leadsto>" 10)

definition callCC :: "(('a \<Rightarrow> ('b, 'r) cont) \<Rightarrow> ('a, 'r) cont) \<Rightarrow> ('a, 'r) cont"
  where "callCC f \<equiv> \<lambda>cc. f (\<lambda>a _. cc a) cc "

definition liftM :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'r) cont \<Rightarrow> ('b, 'r) cont" where
  "liftM f m = bindCont m (return o f)"

definition k_comp :: "('a \<Rightarrow> ('b, 'r) cont) =>  ('b \<Rightarrow> ('c, 'r) cont) => ('a \<Rightarrow> ('c, 'r) cont)" where 
 "k_comp f g \<equiv> \<lambda>a. bindCont (f a) g"

definition foldrM  where
  "foldrM f xs = foldr (k_comp) (map f xs) (return)"

definition mapM  where
  "mapM f xs = foldrM (\<lambda>a xs. liftM (\<lambda>x. x # xs) f a) xs []" 

adhoc_overloading
  bind bindCont

definition ifM :: "(bool, 'a) cont \<Rightarrow> ('b, 'a) cont \<Rightarrow> ('b, 'a) cont \<Rightarrow> ('b, 'a) cont"
  where "ifM b m m'=
        do {c <- b;  
            if c then m else m'}"

lemma bindCont_return: "bindCont f return = f"
  by (intro ext; clarsimp simp: bindCont_def return_def)


lemma bindCont_return': "bindCont (return a) f = f a"
  by (intro ext; clarsimp simp: bindCont_def return_def)

lemma kcomp_assoc: "k_comp (k_comp f g) h = k_comp f (k_comp g h)"
  by (intro ext; clarsimp simp: k_comp_def bindCont_def return_def)

               
context constrained_atomic begin


definition "select S f \<equiv> \<Squnion>x\<in>S. f x"  

definition "getState f \<equiv>  (\<Squnion>a. \<tau> {a} ; f a)  "   

definition "setState s f \<equiv>  (\<pi> (UNIV \<triangleright> {s}) ; f () )"   



definition "modifyState f = do { a <- (getState);  (setState (f a))}"


definition "fail f = \<top> "

definition "todo f = \<bottom> "

definition flatten :: "(('b, 'a) cont, 'a) cont \<Rightarrow> ('b, 'a) cont" where
  "flatten f = bindCont f id"

term "lfp (flatten o liftM (f :: ('b => ('b, 'a) cont)))   "

definition "thendo f g = bindCont f (\<lambda>_. g)"

definition loop :: "('b => ('b, 'a) cont) \<Rightarrow> ('b, 'a) cont "
  where "loop f = lfp (\<lambda>y. bindCont y f )"

definition whileStep :: "(bool, 'a) cont \<Rightarrow> ('b, 'a) cont \<Rightarrow> (unit, 'a) cont" where
 "whileStep b m = ifM b (thendo m (return ())) (return ())"

(* definition while :: "(bool, 'a) cont \<Rightarrow> ('b, 'a) cont \<Rightarrow> (unit, 'a) cont"
  where "while b m = loop (\<lambda>_. whileStep b m )" *)


definition "run f = (f (\<lambda>_. nil))"

definition "check f x = f (\<lambda>P. if P then x else nil)"


definition while :: "('b \<Rightarrow> (bool, 'a) cont) \<Rightarrow> ('b, 'a) cont \<Rightarrow> 'b \<Rightarrow>  (unit, 'a) cont"
  where "while b m a f = check (b a) (gfp (\<lambda>x. check (m \<bind> b) x)) ; f ()"

definition while' :: "(bool, 'a) cont \<Rightarrow> ('b, 'a) cont \<Rightarrow> (unit, 'a) cont"
  where "while' b m = (\<lambda>f. iter (run m); bindCont b (\<lambda>c g. if c then f () else \<bottom>) f)"


definition "assertion P = do {a <- getState; (if (P a) then return () else fail)}"

definition "test_state P = do {a <- getState; return (P a)}"


definition inc :: "(nat \<Rightarrow> nat option) \<Rightarrow> (nat \<Rightarrow> nat option)"
  where "inc s = s (0 \<mapsto> 0 + 1)"


definition "pointless s = do {x <- getState;
                              setState s;
                              return x}"


lemma test_split: "\<tau> P = (\<Squnion>x\<in>P. \<tau> {x})" 
  apply (subst UN_singleton[symmetric])
  apply (subst test_Sup, clarsimp)
  by (simp add: image_image)

lemma SUP_eq_if:"(\<Squnion>x\<in>P. f x) = (\<Squnion>(x). if (x \<in> P) then ((f x) :: 'e :: complete_lattice)  else \<bottom>)"
  apply (rule antisym)
   apply (smt (verit, best) SUP_subset_mono order_class.order_eq_iff subset_UNIV)  
  by (smt (verit) SUP_empty SUP_least Sup_upper empty_iff image_eqI)


lemma in_dom_iff: "x \<in> A \<triangleleft> R \<longleftrightarrow> fst x \<in> A \<and> x \<in> R"
  by (clarsimp simp: restrict_domain_def split: prod.splits)

lemma in_ran_iff: "x \<in> R \<triangleright> A \<longleftrightarrow> snd x \<in> A \<and> x \<in> R"
  apply (clarsimp simp: restrict_range_def split: prod.splits)
  by (safe)

lemma is_id: "{x} \<triangleleft> (UNIV \<triangleright> {x}) = {(x,x)}"
  by (rule set_eqI; clarsimp simp: in_dom_iff in_ran_iff Id_on_iff)

lemma "run (assertion (\<lambda>_. False)) = \<top>"
  apply (clarsimp simp: modifyState_def assertion_def fail_def run_def bindCont_def getState_def setState_def pgm_test_pre is_id)
  apply (rule antisym)
   apply (subst Sup_le_iff; clarsimp)
  by (metis NONDET_seq_distrib Nondet_test_nil order_top_class.top_greatest seq_nil_left)

definition "compact c \<longleftrightarrow> (\<forall>S. S \<noteq> {} \<longrightarrow>  c \<le> \<Squnion> S \<longrightarrow> (\<exists>s\<in>S. c \<le> s))"

lemma algebraic: "(x :: 'a) = \<Squnion>{y. y \<le> x \<and> compact y}" sorry

end


    

end