theory Traces
imports Main
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

lemma last_index_iff: "lengthS x = Some (Suc n) \<Longrightarrow> Traces.last x = Some (projl (index x n))"
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
   apply (subst last_index_iff, assumption )

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
   apply (subst last_index_iff, assumption )

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

thm zip_trace_def




end