theory Hoare_VCG 
imports Hoare_Logic ProcessEpoch
begin

context hoare_logic begin

lemma if_wp[wp]: 
  "(B \<Longrightarrow> hoare_triple  ( lift S) ( bindCont P c) R) \<Longrightarrow> (\<not>B \<Longrightarrow> hoare_triple ( lift S') (bindCont Q c) R) \<Longrightarrow>
   hoare_triple ( lift (if B then S else S'))  (do {x <- (if B then P else Q); c x}) R"
  apply (clarsimp split: if_splits)
  done

lemma read_beacon_wp[wp]: "(\<And>x. x = v \<Longrightarrow> hoare_triple ( lift (P x)) (c x) (Q )) \<Longrightarrow> hoare_triple (lift (maps_to l v \<and>* (maps_to l v \<longrightarrow>*  (P v )))) (do {v <- read_beacon l ; c v}) (Q  )"
  apply (clarsimp simp: hoare_triple_def bindCont_def run_def read_beacon_def getState_def )
  apply (clarsimp simp: Sup_le_iff)
  apply (safe)
   apply (clarsimp simp: fail_def assert_galois_test)
   defer
   apply (clarsimp simp: fail_def assert_galois_test return_def)
   apply (case_tac "y = v"; clarsimp?)
    apply (subst seq_assoc[symmetric])
    apply (subst test_seq_test)
    apply (rule order_trans, rule seq_mono_left)
     apply (rule test.hom_mono[where p="Collect (lift (P v))"])
     apply (clarsimp)
     apply (erule lift_mono, clarsimp, sep_solve)
    apply (blast)
  apply (subst seq_assoc[symmetric])
   apply (subst test_seq_test)
 apply (rule order_trans, rule seq_mono_left)
    apply (rule test.hom_mono[where p="{}"])
    apply (clarsimp)
    defer
    apply (clarsimp)
  apply (subst seq_assoc[symmetric])
   apply (subst test_seq_test)
 apply (rule order_trans, rule seq_mono_left)
    apply (rule test.hom_mono[where p="{}"])
    apply (clarsimp)
    defer
    apply (clarsimp)
   apply (drule maps_to_get_wf, clarsimp)
  apply (drule maps_to_get_wf, clarsimp)
  done



definition "previous_epoch epoch \<equiv> 
    if epoch = GENESIS_EPOCH then GENESIS_EPOCH else Epoch (epoch_to_u64 epoch - 1)"


lemma previous_genesis[simp]: "previous_epoch GENESIS_EPOCH = GENESIS_EPOCH"
  by (clarsimp simp: previous_epoch_def)

lemma previous_is_self_simp[simp]: "previous_epoch e = e \<longleftrightarrow> e = GENESIS_EPOCH"
  apply (clarsimp simp: previous_epoch_def GENESIS_EPOCH_def) 
  by (metis diff_0_right diff_left_imp_eq epoch_to_u64.simps zero_neq_one)

declare lift_mono[elim!]

lemma sub_wp[wp]: "hoare_triple (lift (P (n - m))) (c (n - m)) Q \<Longrightarrow>
  hoare_triple (lift (\<lambda>s. n \<ge>  m \<and> (n \<ge>  m \<longrightarrow> P (n - m) s))) 
(do {x <- (n .- m); c x}) Q"
  apply (rule hoare_weaken_pre)
   apply (clarsimp simp:  word_unsigned_sub_def )
   apply (simp only: Let_unfold)
   apply (wp, clarsimp simp: bindCont_return')
  apply (safe)
  apply (clarsimp simp: bot_fun_def lift_def)
  by (simp add: word_sub_le_iff)

lemma get_current_epoch_wp[wp]: "hoare_triple (lift (P (slot_to_epoch config v))) (f (slot_to_epoch config v)) Q \<Longrightarrow>
hoare_triple (lift (maps_to beacon_slots v \<and>* (maps_to beacon_slots v \<longrightarrow>* P (slot_to_epoch config v)))) (bindCont get_current_epoch f) Q"
  apply (clarsimp simp: get_current_epoch_def)
  apply (rule hoare_weaken_pre)
  apply (clarsimp simp: bindCont_assoc[symmetric] bindCont_return')
   apply (rule read_beacon_wp, fastforce)
  apply (rule order_refl)
  done

lemma get_previous_epoch_wp':"(\<And>x. hoare_triple (lift (P x)) (f x) Q) \<Longrightarrow> hoare_triple (lift (maps_to beacon_slots v \<and>*
          (maps_to beacon_slots v \<longrightarrow>*
           (if slot_to_epoch config v = GENESIS_EPOCH then P GENESIS_EPOCH
            else (\<lambda>s. 1 \<le> epoch_to_u64 (slot_to_epoch config v) \<and>
                 (1 \<le> epoch_to_u64 (slot_to_epoch config v) \<longrightarrow> P (Epoch (epoch_to_u64 (slot_to_epoch config v) - 1)) s)))))) (bindCont get_previous_epoch f) Q"
  apply (simp only: get_previous_epoch_def, rule hoare_weaken_pre)
  apply (subst bindCont_assoc[symmetric])
   apply (rule get_current_epoch_wp)
  apply (rule if_wp)
    apply (rule return_triple', assumption)
  apply (simp add: epoch_unsigned_sub_def, wp)
  apply (rule order_refl)
  done

lemma select_wp_lift[wp]: "(\<And>x. x \<in> P \<Longrightarrow> hoare_triple (lift (pre x)) (f x) Q) \<Longrightarrow> hoare_triple (lift (\<lambda>s. \<forall>x\<in>P. pre x s)) (do {x <- select P; f x}) Q"
  apply (clarsimp simp: select_def bindCont_def hoare_triple_def run_def)
  apply (subst Sup_le_iff)
  apply (clarsimp)
  apply (atomize, erule allE, drule mp, assumption)
  apply (erule order_trans)
  apply (rule seq_mono_left)
  by (subst assert_iso[symmetric], clarsimp)

lemma lift_option_wp[wp]: "(\<And>x. v = Some x \<Longrightarrow> hoare_triple (lift (P x)) (f x) Q) \<Longrightarrow> 
  hoare_triple (lift (\<lambda>s. v \<noteq> None \<and> (v \<noteq> None \<longrightarrow> P (the v) s))) (do {b <- lift_option v; f b}) Q"
  apply (unfold lift_option_def)
  apply (rule hoare_assert_stateI, clarsimp)
   apply (clarsimp simp: lift_def)
  apply (rule hoare_weaken_pre, assumption)
  apply (clarsimp)
  apply (clarsimp simp: lift_def)
  apply (blast)
  done

lemma getState_wp_spec[wp]: " (\<And>s. hoare_triple (P s) (c s) Q) \<Longrightarrow> 
  hoare_triple (\<lambda>x. P x x) (bindCont getState c) Q"
  apply (clarsimp simp: getState_def hoare_triple_def bindCont_def run_def Sup_le_iff assert_galois_test test_restricts_Nondet)
  apply (atomize)
  apply (erule_tac x=a in allE)
  apply (erule_tac x=b in allE)
  apply (erule order_trans[rotated])
  using seq_mono_left test.hom_mono by force

lemma getState_wp_alt: "(\<And>s. P s \<Longrightarrow> hoare_triple ((=) s) (c s) Q) \<Longrightarrow> 
  hoare_triple P (bindCont getState c) Q "
  by (clarsimp simp: getState_def hoare_triple_def bindCont_def run_def Sup_le_iff assert_galois_test test_restricts_Nondet)


lemma hoare_subgoalI: "(\<And>s. P \<Longrightarrow> hoare_triple P' f Q) \<Longrightarrow> hoare_triple (\<lambda>s. P  \<and> (P  \<longrightarrow> P' s)) f Q"
  apply (rule hoare_assert_stateI)
  apply (rule hoare_weaken_pre)
   apply (clarsimp)
   apply (assumption)
  apply (clarsimp)
  done

lemma [simp]: "\<lless>\<lambda>s. P\<then> = (\<lambda>s. P)" 
  apply (intro ext, clarsimp simp: lift_def)  
  apply (safe)
  apply (rule_tac x="id_p" in exI)
  by simp

lemma div_wp_lift: "hoare_triple (lift (P (n div m))) (c (n div m)) Q \<Longrightarrow>
  hoare_triple (lift (\<lambda>s. m \<noteq> 0 \<and> (m \<noteq> 0 \<longrightarrow>  (P ( n div m)) s))) 
(do {x <- (word_unsigned_div n m); c x}) Q"
  apply (rule hoare_weaken_pre)
   apply (unfold word_unsigned_div_def, wp)
  apply (clarsimp simp: lift_def)
  done

lemma add_wp[wp]: "hoare_triple (lift (P (n + m))) (c (n + m)) Q \<Longrightarrow>
  hoare_triple (lift (\<lambda>s. n \<le> n + m \<and> (n \<le> n + m \<longrightarrow> P (n + m) s))) 
(do {x <- (word_unsigned_add n  m); c x}) Q"
  apply (rule hoare_weaken_pre)
   apply (clarsimp simp:  word_unsigned_add_def )
   apply (simp only: Let_unfold)
   apply (wp, clarsimp simp: bindCont_return')
  done

lemma mod_wp[wp]: "hoare_triple (lift (P (n mod m))) (c (n mod m)) Q \<Longrightarrow>
  hoare_triple (lift (\<lambda>s. m \<noteq> 0 \<and> (m \<noteq> 0 \<longrightarrow> P (n mod m) s)))
(do {x <- (n .% m); c x}) Q"
  apply (rule hoare_weaken_pre)
   apply (unfold word_unsigned_mod_def)
   apply wp
  apply fastforce
  done


lemma when_wp[wp]: 
  "(B \<Longrightarrow> hoare_triple  ( lift S) ( bindCont P c) R) \<Longrightarrow> (\<not>B \<Longrightarrow> hoare_triple ( lift S') (c ()) R) \<Longrightarrow>
   hoare_triple ( lift (if B then S else S'))  (do {x <- (when B P); c x}) R"
  apply (clarsimp split: if_splits)
  done

lemma lift_pure_conj[simp]: "lift (\<lambda>s. P \<and> Q s) s = (P \<and> lift Q s)"
  by (clarsimp simp: lift_def)

lemma lift_pure_imp[simp]: "lift (\<lambda>s. P \<longrightarrow> Q s) s = (P \<longrightarrow> lift Q s)"
  apply (clarsimp simp: lift_def)
  apply (safe; fastforce?)
  by (metis id_apply point_of_id)


lemma hoare_eqI': "hoare_triple (lift (P x)) (f x) Q \<Longrightarrow> hoare_triple (lift (\<lambda>s. v = x \<and> (v = x \<longrightarrow> P v s))) (f v) Q"
  apply (rule hoare_assert_stateI)
  apply (clarsimp)
  apply (clarsimp simp: lift_def)
  apply (erule hoare_weaken_pre)
  apply (clarsimp simp: lift_def)
  apply (blast)
  done

lemma hoare_eqI'': "hoare_triple (lift (P x v)) (f x) Q \<Longrightarrow> hoare_triple (lift (\<lambda>s. v = x \<and> (v = x \<longrightarrow> P x v s))) (f v) Q"
  apply (rule hoare_assert_stateI)
  apply (clarsimp)
  apply (clarsimp simp: lift_def)
  apply (erule hoare_weaken_pre)
  apply (clarsimp simp: lift_def)
  apply (blast)
  done

lemma fail_wp[wp]: "\<lblot>lift \<bottom>\<rblot> bindCont fail c \<lblot>Q\<rblot>"
  apply (rule hoare_weaken_pre, wp)
  apply (clarsimp simp: lift_def)
  done

lemma mul_wp[wp]: "hoare_triple (lift (P (n * m))) (c (n * m)) Q \<Longrightarrow>
  hoare_triple (lift (\<lambda>s. safe_mul m n  \<and> (safe_mul m n  \<longrightarrow> P (n * m) s))) 
(do {x <- (word_unsigned_mul n m); c x}) Q"
  apply (rule hoare_weaken_pre)
   apply (unfold  word_unsigned_mul_def )
   apply (simp only: Let_unfold)
   apply (rule if_wp, simp)
    apply (fastforce)
   apply (rule if_wp, simp)
   apply (wp)
  apply (clarsimp simp: safe_mul_def)
  apply (intro conjI impI; clarsimp?)
  by (simp add: mult.commute)

lemma div_wp[wp]: "hoare_triple (lift (P (n div m))) (c (n div m)) Q \<Longrightarrow>
  hoare_triple (lift (\<lambda>s. m \<noteq> 0 \<and> (m \<noteq> 0 \<longrightarrow> P ( n div m) s))) 
(do {x <- (word_unsigned_div n m); c x}) Q"
  apply (rule hoare_weaken_pre)
   apply (unfold word_unsigned_div_def, wp)
   apply (clarsimp simp: bindCont_return')
  done


lemma mapM_wp'':
  assumes c_wp: "\<And>(f :: 'e \<Rightarrow> ('f, 'a) cont) x P Q.  (\<And>xs. hoare_triple (lift (P (g x))) (f (g x)) ( Q)) \<Longrightarrow> hoare_triple (lift (pre x)) (do { b <- c x; f b}) Q"  
shows "  (\<And>x y. hoare_triple (lift (P x)) (f y) Q) \<Longrightarrow>   hoare_triple (lift (\<lambda>s. (\<forall>x\<in>list.set xs. pre x s) \<and> ((\<forall>x\<in>list.set xs. pre x s) \<longrightarrow> P (map g xs) s))) (do {vs <- mapM c (xs :: 'd list) ; (f :: 'e list \<Rightarrow> ('f, 'a) cont) (vs )}) Q"
  apply (induct xs arbitrary: f)
   apply (simp)
  apply (clarsimp)
  apply (rule hoare_weaken_pre)
  apply (clarsimp simp: bindCont_assoc[symmetric])
   apply (rule c_wp)
  defer
    apply (clarsimp)
  defer
  apply (atomize)
  apply (erule_tac x="(\<lambda>aa. f (g a # aa))" in allE)
  apply (drule mp)
   apply (clarsimp)
  apply (fastforce)
  done

lemma mapM_wp_foldr:
  assumes c_wp: "\<And>(f :: 'e \<Rightarrow> ('f, 'a) cont) x P Q. (\<And>x. hoare_triple (lift (P)) (f x) (Q)) \<Longrightarrow> hoare_triple (lift (pre P x)) (do { b <- c x; f b}) Q"  
shows " (\<And>x. hoare_triple (lift (P)) (f x) Q) \<Longrightarrow>   hoare_triple (lift (foldr (\<lambda>x R. pre R x) xs P )) (do {vs <- mapM c (xs :: 'd list) ; (f :: 'e list \<Rightarrow> ('f, 'a) cont) (vs )}) Q"
  apply (induct xs arbitrary: f; clarsimp)
  by (metis (no_types, lifting) bindCont_assoc c_wp return_triple')

lemma mapM_wp':
  assumes c_wp: "\<And>(f :: 'e \<Rightarrow> ('f, 'a) cont) x P Q. hoare_triple (lift P) (f (g x)) ( Q) \<Longrightarrow> hoare_triple (lift (pre P x)) (do { b <- c x; f b}) Q"  
  assumes pre_mono: "(\<And>x P Q s . (P s  \<Longrightarrow> Q s) \<Longrightarrow>  (pre P x) s \<Longrightarrow>  (pre Q x) s  )"
shows " hoare_triple (lift P) (f (map g xs)) Q \<Longrightarrow>   hoare_triple (lift (\<lambda>s. (\<Sqinter>x\<in>(list.set xs). pre P x) s \<and> ((\<Sqinter>x\<in>(list.set xs). pre P x) s \<longrightarrow> P s))) (do {vs <- mapM c (xs :: 'd list) ; (f :: 'e list \<Rightarrow> ('f, 'a) cont) (vs )}) Q"
  apply (induct xs arbitrary: f; clarsimp)
  apply (atomize)
  apply (clarsimp simp: bindCont_assoc[symmetric])
  apply (rule hoare_weaken_pre)
  apply (rule c_wp)
  apply (erule allE)
  apply (erule impE)
   defer
    apply (assumption)
   apply (clarsimp)
   apply (rule pre_mono[rotated], assumption)
   apply (clarsimp)
  
  apply (clarsimp)
  done

definition "mul_bound x y \<equiv> y = x * y div x"

lemma safe_mul_commute: "safe_mul (x :: u64) y = safe_mul y x"
  apply (clarsimp simp: safe_mul_def)
  apply (safe)
   apply (unat_arith, simp)
   apply (metis (no_types, lifting) bot_nat_0.not_eq_extremum div_mult_le mult.commute
        nonzero_mult_div_cancel_left order_le_less_trans unat_mult_lem unsigned_less)
 apply (unat_arith, simp)
   apply (metis (no_types, lifting) bot_nat_0.not_eq_extremum div_mult_le mult.commute
        nonzero_mult_div_cancel_left order_le_less_trans unat_mult_lem unsigned_less)
  done

lemma nonempty_ball_conj_lift: "S \<noteq> {} \<Longrightarrow> (\<forall>x\<in>S. P \<and> Q x) = (P \<and> (\<forall>x\<in>S. Q x))"
  by (safe; clarsimp?)


lemma nonempty_ball_imp_lift: "S \<noteq> {} \<Longrightarrow> (\<forall>x\<in>S. P \<longrightarrow> Q x) = (P \<longrightarrow> (\<forall>x\<in>S. Q x))"
  by (safe; clarsimp?)

lemma effective_balance_safe[simp]:
 "MAX_EFFECTIVE_BALANCE \<le> MAX_EFFECTIVE_BALANCE + EFFECTIVE_BALANCE_INCREMENT config" sorry 

lemma range_empty_iff: " (range x y z) = [] \<longleftrightarrow> (x \<ge> y) \<or> z = 0"
  apply (case_tac z; clarsimp)
  done 

lemma start_in_valid_range[simp]: "range x y z \<noteq> [] \<Longrightarrow> x \<in> list.set (range x y z)"
  apply (clarsimp simp: range_empty_iff)
  by (case_tac z; clarsimp?)

lemma EBI_ge_zero[intro]: "EFFECTIVE_BALANCE_INCREMENT config > 0" sorry


lemma hoare_eqI''': "hoare_triple (lift (P x)) (f x) Q \<Longrightarrow> v = x \<Longrightarrow>  hoare_triple (lift (P v)) (f v) Q"
  apply (rule hoare_assert_stateI)
  apply (clarsimp)
  apply (clarsimp simp: lift_def)
  apply (erule hoare_weaken_pre)
  apply (clarsimp simp: lift_def)
  apply (blast)
  done

lemma hoare_eqI_weaken: "hoare_triple (lift (P x)) (f x) Q \<Longrightarrow> (\<And>s. P' v s \<Longrightarrow> P x s) \<Longrightarrow> hoare_triple (lift (\<lambda>s. x = v \<and> (x = v \<longrightarrow> P' v s))) (f v) Q"
  apply (rule hoare_assert_stateI)
  apply (clarsimp)
  apply (clarsimp simp: lift_def)
  apply (erule hoare_weaken_pre)
  apply (clarsimp simp: lift_def)
  apply (blast)
  done

lemma read_beacon_wp'[wp]: "(\<And>x. hoare_triple ( lift (P x)) (c x) (Q )) \<Longrightarrow> 
hoare_triple (lift (maps_to l v \<and>* (maps_to l v \<longrightarrow>*  (P v )))) (do {v <- read_beacon l ; c v}) (Q  )"
  apply (wp)
  done

lemma mapM_wp_foldr':
  assumes c_wp: "\<And>(f :: 'e \<Rightarrow> ('f, 'a) cont) x P Q. (\<And>x. hoare_triple (lift (P x)) (f x) (Q)) \<Longrightarrow> 
                                                    hoare_triple (lift (pre (P (g x)) x)) (do { b <- c x; f b}) Q"  
  shows " (\<And>x. hoare_triple (lift (P x)) (f x) Q) 
          \<Longrightarrow>   hoare_triple (lift (foldr (\<lambda>x R. pre R x) xs (P (map g xs)) ))
                (do {vs <- mapM c (xs :: 'd list) ; (f :: 'e list \<Rightarrow> ('f, 'a) cont) (vs )}) Q"
  apply (induct xs arbitrary: P f; clarsimp)
  apply (rule hoare_weaken_pre, subst bindCont_assoc[symmetric])
   apply (rule c_wp)
   apply (atomize, erule allE)
  apply (erule allE) back
  apply (subst bindCont_assoc[symmetric])
   apply (erule mp)
   apply (clarsimp)
   apply (fastforce)
  apply (fastforce)
  done

lemma sep_factor_foldI':
  "(I \<and>* (foldr (\<lambda>x R. (P x \<and>* (Q x \<longrightarrow>* R))) xs (I \<longrightarrow>* R))) s \<Longrightarrow> (foldr (\<lambda>x R. (I \<and>* P x \<and>* (I \<and>* Q x \<longrightarrow>* R))) xs R) s"
  apply (induct xs arbitrary:s; clarsimp simp:)
   apply (sep_solve)
  apply (sep_cancel)+
  apply (sep_mp)
  apply (clarsimp simp: sep_conj_ac)
  done

lemma factor_foldr_conj: "(\<forall>x\<in>(list.set xs). P x) \<and> (foldr f xs R) s \<Longrightarrow> (\<And>a. mono (f a)) \<Longrightarrow>  
  (foldr (\<lambda>x R s. P x \<and> f x R s) xs R) s"
  apply (induct xs  arbitrary: s; clarsimp)
  by (metis (mono_tags, lifting) monoD predicate1D predicate1I)


lemma factor_foldr_pure: "(\<forall>x\<in>(list.set xs). P x) \<and> ((\<forall>x\<in>(list.set xs). P x) \<longrightarrow> (foldr f xs R) s) \<Longrightarrow> (\<And>a. mono (f a)) \<Longrightarrow>  
  (foldr (\<lambda>x R s. (P x \<longrightarrow> f x R s) \<and> P x) xs R) s"
  apply (induct xs  arbitrary: s; clarsimp)
  apply (atomize)
  by (metis (mono_tags, lifting) le_boolD le_funE monoD predicate1I)

lemma factor_foldr_conj': "(\<forall>x\<in>(list.set xs). P x) \<and> (foldr f xs R) s \<Longrightarrow> (\<And>a. mono (f a)) \<Longrightarrow>  
  (foldr (\<lambda>x R s. f x R s \<and> P x) xs R) s"
  apply (induct xs  arbitrary: s; clarsimp)
  by (metis (mono_tags, lifting) monoD predicate1D predicate1I)


lemma factor_foldr_sep: "(P \<and>* (foldr f xs (P \<longrightarrow>* R))) s \<Longrightarrow> (\<And>a. mono (f a)) \<Longrightarrow>  (\<And>R a. f a (P \<and>* R) = (P \<and>* f a R)) \<Longrightarrow>   (foldr (\<lambda>x R. P \<and>* (P \<longrightarrow>* f x R)) xs  R) s"
  apply (induct xs  arbitrary: s; clarsimp)
   apply (sep_mp, clarsimp)
  apply (sep_cancel)+
  apply (erule sep_curry[rotated])
  apply (clarsimp simp: sep_conj_ac)
  by (smt (verit, ccfv_threshold) monoE predicate1D predicate1I sep_conj_commute)

lemma in_set_pure_simp[simp]:"in_set (\<lambda>_. P) s = P"
  by (clarsimp simp: in_set_def)

(*  *)

lemma foldr_const[simp]: "foldr (\<lambda>_ R. R) xs R = R"
  by (induct xs; clarsimp)


lemma mono_id[simp]: "mono (\<lambda>R. R)" 
   by (rule monoI; clarsimp)


lemma hoare_let[intro, wp]: "hoare_triple P (bindCont (b a) c) Q \<Longrightarrow> hoare_triple P (bindCont (Let a b) c) Q"
  by (clarsimp simp: Let_unfold)



lemma if_lift: "(if B then lift P else lift Q) = lift (if B then P else Q)"
  by (intro ext; clarsimp simp: lift_def)





lemma add_zero_simp:"(bindCont (word_unsigned_add (a :: u64) (0 :: u64)) f) = f a"
  apply (subst word_unsigned_add_def bindCont_def)+
  apply (intro ext)
  by (clarsimp simp: Let_unfold return_def)



lemma unsigned_add_commute[intro]:" word_unsigned_add b a = a .+ b "
  apply (rule ext; clarsimp simp: Let_unfold word_unsigned_add_def)
  apply (safe; clarsimp simp: add.commute)
  using olen_add_eqv apply auto[1]
  using olen_add_eqv apply auto[1]
  done



lemma unsigned_word_add_shuffle:" bindCont (word_unsigned_add a  n) (\<lambda>y. bindCont (b .+ y) f) = bindCont (b .+ n) (\<lambda>y. bindCont ( a .+ y) f) "
  apply (clarsimp simp: word_unsigned_add_def Let_unfold, safe; (clarsimp simp: bindCont_return' bindCont_return split: if_splits)?)
      apply (simp add: add.left_commute)
  using olen_add_eqv word_random apply blast
  using olen_add_eqv word_random apply blast
   apply (metis add.left_commute le_no_overflow)
  by (simp add: add.left_commute le_no_overflow)


lemma foldrM_elems_cons: "foldrM word_unsigned_add ([a,b]) n = foldrM word_unsigned_add ([b,a]) n"
  apply (clarsimp simp: foldrM_cons)
  using unsigned_word_add_shuffle 
  by (metis bindCont_assoc bindCont_return)




lemma word_unsigned_add_shuffle2: "bindCont (word_unsigned_add x y) (\<lambda>x. x .+ z) = bindCont (x .+ z) (\<lambda>x. x .+ y)"
  apply (clarsimp simp: word_unsigned_add_def Let_unfold, safe; (clarsimp simp: bindCont_return' bindCont_return split: if_splits)?)
      apply (simp add: add.commute add.left_commute)
  apply (smt (verit, ccfv_threshold) no_olen_add word_le_def)
    apply (metis (no_types, lifting) add.commute olen_add_eqv word_random)
   apply (metis add.assoc add.commute olen_add_eqv word_plus_mono_right)
  by (metis (no_types, opaque_lifting) add.commute group_cancel.add2 nle_le olen_add_eqv word_add_increasing word_plus_mcs_4')

  

lemma foldrM_shift: "foldrM word_unsigned_add (a#xs) n = (do {x <- foldrM word_unsigned_add (xs) n; word_unsigned_add x a})   "
  apply (induct xs arbitrary: n a; clarsimp?)
   apply (clarsimp simp: foldrM_def bindCont_return' k_comp_def bindCont_return)
   apply (rule unsigned_add_commute)
  apply (clarsimp simp: foldrM_cons)
  apply (clarsimp simp: bindCont_assoc)
  apply (subst bindCont_assoc[symmetric])
  apply (subst bindCont_assoc[symmetric])
  apply (rule bindCont_right_eqI)
  apply (rule word_unsigned_add_shuffle2)
  done


lemma get_sep_conj_eq: "get l (a, b) = Some y \<Longrightarrow> lift (l \<mapsto>\<^sub>l v \<and>* R) (a, b) \<Longrightarrow> v = y  "
  apply (clarsimp simp: sep_conj_def lift_def maps_to_def)
  by (metis comp_apply get_set_def option.inject point_of_plus_domain_iff valid_lens_def)


lemma get_sep_conj_eq': "lift (l \<mapsto>\<^sub>l v \<and>* R) (a, b) \<Longrightarrow> get l (a, b) \<noteq> None  "
  apply (clarsimp simp: sep_conj_def lift_def maps_to_def)
  by (metis comp_apply get_set_def  point_of_plus_domain_iff valid_lens_def)

lemma read_beacon_wp_alt[wp]: "(\<And>x. hoare_triple ( lift (P x)) (c x) (Q )) \<Longrightarrow>
   hoare_triple (lift (maps_to l v \<and>* (maps_to l v \<longrightarrow>* (\<lambda>s. x = v \<and> (x = v \<longrightarrow> (P v s)))))) 
  (do {v <- read_beacon l ; c v}) (Q  )"
  apply (clarsimp simp: hoare_triple_def bindCont_def run_def read_beacon_def getState_def )
  apply (clarsimp simp: Sup_le_iff)
  apply (safe)
   apply (clarsimp simp: fail_def assert_galois_test)
   defer
   apply (clarsimp simp: fail_def assert_galois_test return_def)
   apply (case_tac "y = v"; clarsimp?)
    apply (subst seq_assoc[symmetric])
    apply (subst test_seq_test)
    apply (rule order_trans, rule seq_mono_left)
     apply (rule test.hom_mono[where p="Collect (lift (P v))"])
     apply (clarsimp)
  apply (sep_select_asm 2)
     apply (frule sep_mp)
  apply (clarsimp)
    apply (blast)
  apply (subst seq_assoc[symmetric])
   apply (subst test_seq_test)
 apply (rule order_trans, rule seq_mono_left)
    apply (rule test.hom_mono[where p="{}"])
    apply (clarsimp)
    defer
    apply (clarsimp)
  apply (subst seq_assoc[symmetric])
   apply (subst test_seq_test)
 apply (rule order_trans, rule seq_mono_left)
    apply (rule test.hom_mono[where p="{}"])
    apply (clarsimp)
    defer
    apply (clarsimp)
   apply (metis get_sep_conj_eq)
  by (metis get_sep_conj_eq')


lemma add_wp'[wp]: "(\<And>x. hoare_triple (lift (P x )) (c x) Q) \<Longrightarrow>
  hoare_triple (lift (\<lambda>s. n \<le> n + m \<and> (n \<le> n + m \<longrightarrow> P (n + m) s))) 
(do {x <- (word_unsigned_add n  m); c x}) Q"
  apply (rule hoare_weaken_pre)
   apply (clarsimp simp:  word_unsigned_add_def )
   apply (simp only: Let_unfold)
   apply (wp, clarsimp simp: bindCont_return')
    apply (fastforce)
   apply (wp)
  by (clarsimp)



lemma maps_exI[sep_cancel]: "(maps_to l v) s \<Longrightarrow> (EXS v. maps_to l v) s"
  by (blast)



lemma liftM_wp[wp]: "hoare_triple pre (do {x <- c; d (f x)}) post \<Longrightarrow>  hoare_triple pre (do {x <- f <$> c; d x}) post"
  apply (clarsimp simp: liftM_def comp_def bindCont_assoc)
  by (smt (verit, best) bindCont_assoc bindCont_return' bindCont_right_eqI)


lemma sub_wp'[wp]: "(\<And>x. \<lblot>\<lless>P x\<then>\<rblot> c x \<lblot>Q\<rblot>) \<Longrightarrow> \<lblot>\<lless>\<lambda>s. m \<le> n \<and> (m \<le> n \<longrightarrow> P (n - m) s)\<then>\<rblot> (bindCont (n .- m) c) \<lblot>Q\<rblot>"
  apply (rule sub_wp, fastforce)
  done

lemma mapM_fake: assumes c_wp: "\<And>(f :: 'e \<Rightarrow> ('f, 'a) cont) x P Q. (\<And>x. hoare_triple (lift (P x)) (f x) (Q)) \<Longrightarrow> 
                                                    hoare_triple (lift ( (pre x) P)) (do { b <- c x; f b}) Q"   
  shows " (\<And>x. hoare_triple (lift (P x)) (f x) Q) 
          \<Longrightarrow>   hoare_triple (lift (mapM pre xs P ) )
                (do {vs <- mapM c (xs :: 'd list) ; (f :: 'e list \<Rightarrow> ('f, 'a) cont) (vs )}) Q"
  apply (induct xs arbitrary: P f; clarsimp)
 apply (clarsimp simp: return_def)
  apply (rule hoare_weaken_pre, subst bindCont_assoc[symmetric])
apply (rule c_wp)
   apply (atomize, erule allE)
  apply (erule allE) back
  apply (subst bindCont_assoc[symmetric])
   apply (erule mp)
   apply (clarsimp)
   apply (fastforce)
  apply (clarsimp simp: foldrM_cons)
  apply (clarsimp simp: bindCont_def return_def)
  done

lemma mapM_factor_const: assumes mono_f:  "(\<And>a. mono (f a))" shows
 "(P \<and>*  mapM f xs (\<lambda>v. P \<longrightarrow>* R v)) s \<Longrightarrow> (\<And>R a. f a (\<lambda>v. P \<and>* R v) \<ge> (P \<and>* f a R)) \<Longrightarrow> mapM (\<lambda>x R s. (P \<and>*  (P  \<longrightarrow>* f x R)) s )
           xs R s"
  apply (induct xs arbitrary: R  s; clarsimp?)
  apply (clarsimp simp: return_def)
   apply (sep_mp, clarsimp)
  apply (clarsimp simp: bindCont_def return_def)
  apply (sep_cancel)+
  apply (erule sep_curry[rotated])
  apply (sep_select_asm 2)
  apply (atomize)
  apply (clarsimp)

  apply (erule_tac x="(\<lambda>a. mapM f xs (\<lambda>aa. P \<longrightarrow>* R (a # aa)))" in allE)
  apply (erule_tac x=a in allE)

  apply (drule_tac x=h in le_funD, clarsimp)
  apply (insert mono_f)
  apply (atomize)
  apply (erule_tac x=a in allE)
  apply (clarsimp simp: mono_def)
  apply (erule_tac x="(\<lambda>v. P \<and>* mapM f xs (\<lambda>aa. P \<longrightarrow>* R (v # aa)))" in allE)

  apply (erule_tac x="(\<lambda>a. mapM (\<lambda>x R. P \<and>* (P \<longrightarrow>* f x R)) xs (\<lambda>aa. R (a # aa)))" in allE)
  apply (drule mp)
   apply (clarsimp)
  apply (drule_tac x=h in le_funD, clarsimp)
  done


lemma mapM_factor_ex: assumes mono_f: 
"(\<And>a b x y s. a \<le> b \<Longrightarrow> f x a y s \<Longrightarrow> f x b y s)" shows "\<exists>y. mapM (\<lambda>x R. f x R y) xs R s \<Longrightarrow>  mapM (\<lambda>x R. EXS y. f x R y) xs R s"
  apply (induct xs arbitrary: R s; clarsimp?)
  apply (clarsimp simp: bindCont_def return_def)
  apply (rule_tac x=y in exI)
  apply (erule mono_f[rotated])
  apply (clarsimp)
  apply (blast)
  done
  
  apply (rule_tac x=a in exI)
  apply (rule_tac x=x in exI, sep_cancel)+
  apply (erule sep_curry[rotated])
  apply (sep_select_asm 2)
  apply (atomize)
  apply (erule_tac x="\<lambda>aa. R (a # aa)" in allE) 
  apply (erule_tac x="h" in allE) 
  apply (drule mp)
   apply (rule_tac x=x in exI)
  apply (sep_cancel)
  apply (sep_solve)
  done

lemma mapM_rewriteI: "mapM g xs R s \<Longrightarrow> (\<And>a b c. b \<ge> c  \<Longrightarrow> f a b \<ge> g a c) \<Longrightarrow>  mapM f xs R s"
  apply (induct xs arbitrary: R s; clarsimp?)
  apply (clarsimp simp: bindCont_def)
  apply (atomize)
  apply (erule_tac x=a in allE)
  apply (clarsimp simp: return_def)
  apply (drule_tac x="(\<lambda>a. mapM f xs (\<lambda>aa. return (a # aa) R))" in spec)
  apply (drule_tac x="(\<lambda>a. mapM g xs (\<lambda>aa. return (a # aa) R))" in spec)
  apply (drule mp)
   apply (clarsimp)
  by (drule_tac x=s in le_funD, clarsimp simp: return_def)

lemma mapM_lift_assms: assumes mono_f: "(\<And>a. mono (f a))" and mono_g: "(\<And>a. mono (g a))" shows "(\<forall>x\<in>(list.set xs). (B x \<longrightarrow> P x)) \<and> ((\<forall>x\<in>(list.set xs). (B x \<longrightarrow> P x)) \<longrightarrow> mapM (\<lambda>x R s. if B x then f x R s else g x R s) xs R s) \<Longrightarrow>
  mapM (\<lambda>x R s. if B x then (P x \<and> (P x \<longrightarrow> f x R s)) else g x R s) xs R s"
  apply (clarsimp)
  apply (induct xs arbitrary: R s; clarsimp simp: bindCont_def return_def)
  apply (intro conjI impI; clarsimp?)
  using mono_f 
   apply (smt (verit, ccfv_threshold) monotoneD predicate2I rev_predicate1D)
  using mono_g
  by (smt (verit, ccfv_threshold) monotoneD predicate2I rev_predicate1D)

lemma mapM_lift_if: "R (map (\<lambda>x. if B x then f x else g x) xs) s  \<Longrightarrow> mapM (\<lambda>x R s. if B x then R (f x) s else R (g x)s) xs R s"
  apply (clarsimp)
  apply (induct xs arbitrary: R s; clarsimp simp: bindCont_def return_def)
  apply (intro conjI impI; clarsimp?)
  done

lemma mapM_lift_if: "R (map g xs) s  \<Longrightarrow> mapM f xs R s"
  apply (clarsimp)
  apply (induct xs arbitrary: R s; clarsimp simp: bindCont_def return_def)
  apply (intro conjI impI; clarsimp?)
  done

lemma mapM_lift_imp: "(\<forall>x\<in>list.set xs. (B x \<longrightarrow> P x)) \<longrightarrow> R (map (\<lambda>x. if B x then f x else g x) xs) s  \<Longrightarrow> mapM (\<lambda>x R s. if B x then P x \<longrightarrow> R (f x) s else R (g x)s) xs R s"
  apply (clarsimp)
  apply (induct xs arbitrary: R s; clarsimp simp: bindCont_def return_def)
  apply (intro conjI impI; clarsimp?)
  done

lemma mapM_lift_imp: " mapM f xs R s \<and> mapM g xs R s \<Longrightarrow> mapM (\<lambda>x R s. (f R x s) \<and> g R x s) xs R s"
  apply (clarsimp)
  apply (induct xs arbitrary: R s; clarsimp simp: bindCont_def return_def)
  apply (intro conjI impI; clarsimp?)
  done

  

lemma mapM_lift_over_if: "mapM (\<lambda>x R . P (if B x then (f R x ) else (g R x))) xs R s \<Longrightarrow> mono P \<Longrightarrow> mono f \<Longrightarrow> mono g \<Longrightarrow> mapM (\<lambda>x R s. if B x then P (f R x) s else P (g R x) s) xs R s"
  apply (clarsimp)
  apply (erule mapM_rewriteI)
  apply (clarsimp)
  apply (intro conjI impI; clarsimp?)
  sorry

lemma factor_conj: "(\<lambda>x R s. (if C x s then (\<lambda>s. P x s \<and> A x R s) else (\<lambda>s. B x R s)) s) = (\<lambda>x R s. (C x s \<longrightarrow> P x s) \<and> (if C x s then A x R s else B x R s))" 
  apply (intro ext conjI impI iffI; clarsimp?)
  by (clarsimp split: if_splits)


lemma factor_imp: "(\<lambda>x R s. (if C x s then (\<lambda>s. P x s \<and> (P x s \<longrightarrow> A x R s)) else (\<lambda>s. B x R s)) s) = (\<lambda>x R s. (C x s \<longrightarrow> P x s) \<and> ((C x s \<longrightarrow> P x s) \<longrightarrow> (if (C x s) then A x R s else B x R s)))" 
  by (intro ext conjI impI iffI; clarsimp split: if_splits)


lemma lift_conj_mapM: "((\<forall>x\<in>(list.set xs). A x) \<and> (mapM f xs R s)) \<Longrightarrow> (\<And>a. mono (f a)) \<Longrightarrow> mapM (\<lambda>x R s. (A x ) \<and> (f x R s)) xs R s "
  apply (induct xs arbitrary: s R; clarsimp)
  apply (clarsimp simp: bindCont_def return_def)
  apply (atomize)
  apply (erule_tac x=a in allE)
  apply (drule_tac x= "(\<lambda>a. mapM f xs (\<lambda>aa. R (a # aa)))" and y="(\<lambda>a. mapM (\<lambda>x R s. A x  \<and> f x R s) xs (\<lambda>aa. R (a # aa)))" in  monoD)
  apply (clarsimp)
  by blast

lemma lift_assumes_mapM: "((\<forall>x\<in>(list.set xs). A x) \<and> ((\<forall>x\<in>(list.set xs). A x) \<longrightarrow> (mapM f xs R s))) \<Longrightarrow> (\<And>a. mono (f a)) \<Longrightarrow> mapM (\<lambda>x R s. A x \<and> ((A x ) \<longrightarrow> (f x R s))) xs R s "
  apply (induct xs arbitrary: s R; clarsimp)
  apply (clarsimp simp: bindCont_def return_def)
  apply (atomize)
  apply (erule_tac x=a in allE)
  apply (drule_tac x= "(\<lambda>a. mapM f xs (\<lambda>aa. R (a # aa)))" and y="(\<lambda>a. mapM (\<lambda>x R s. A x \<and> (A x \<longrightarrow> f x R s)) xs (\<lambda>aa. R (a # aa)))" in  monoD)
   apply (clarsimp)
  by blast
  

lemma mapM_lift_over_if: "mapM (\<lambda>x R . (if B x then (\<lambda>s. P x R \<and> f R x s ) else (g R x))) xs R s \<Longrightarrow> mono P \<Longrightarrow> mono f \<Longrightarrow> mono g \<Longrightarrow> mapM (\<lambda>x R s. if B x then (f R x) s else (g R x) s) xs R s"
  apply (clarsimp)
  apply (erule mapM_rewriteI)
  apply (clarsimp)
  apply (induct xs arbitrary: R s; clarsimp simp: bindCont_def return_def)
  apply (intro conjI impI; clarsimp?)
  sorry

lemma mapM_lift_over_if: "mapM (\<lambda>x R . P (if B x then (f R x ) else (g R x))) xs R s \<Longrightarrow> mono P \<Longrightarrow> mono f \<Longrightarrow> mono g \<Longrightarrow> mapM (\<lambda>x R s. if B x then P (f R x) s else P (g R x) s) xs R s"
  apply (clarsimp)
  apply (erule mapM_rewriteI)
  apply (clarsimp)
  apply (induct xs arbitrary: R s; clarsimp simp: bindCont_def return_def)
  apply (intro conjI impI; clarsimp?)
  sorry

lemma mapM_lift_over_if': "mapM (\<lambda>x R s. P (if B x then (f R x s) else (g R x s))) xs R s \<Longrightarrow> mono P \<Longrightarrow> mono f \<Longrightarrow> mono g \<Longrightarrow> mapM (\<lambda>x R s.  (B x \<longrightarrow> P (f R x s)) \<and> (\<not> B x \<longrightarrow> P (g R x s))) xs R s"
  apply (clarsimp)
  apply (erule mapM_rewriteI)
  apply (clarsimp)
  apply (induct xs arbitrary: R s; clarsimp simp: bindCont_def return_def)
  apply (intro conjI impI; clarsimp?)
  sorry


named_theorems mono_thms

lemma mono_if[mono_thms]:"mono f \<Longrightarrow> mono g \<Longrightarrow> mono (\<lambda>x. if B then f x else g x)"
  by (clarsimp simp: mono_def)


lemma mono_if_cont[mono_thms]:" mono (\<lambda>R x. if B x then R (f x) x else R (g x) x)"
  apply (clarsimp simp: mono_def)
  apply (intro le_funI; clarsimp split: if_splits)
  apply (intro conjI impI)
   apply (simp add: le_funD)
  apply (simp add: le_funD)
  done

lemma mono_sep_conj[mono_thms]: "mono f \<Longrightarrow> mono (\<lambda>R. (P \<and>* f R))"
  apply (clarsimp simp: mono_def)
  apply (sep_cancel)
  by blast

lemma mono_sep_impl[mono_thms]: "mono f \<Longrightarrow> mono (\<lambda>R. (P \<longrightarrow>* f R))"
  apply (clarsimp simp: mono_def)
  apply (sep_cancel)
  apply (sep_mp)
  by blast

lemma mono_app: "mono g \<Longrightarrow> mono (\<lambda>f x. g (f x))"
  apply (clarsimp simp: mono_def)
  apply (rule le_funI)
  apply (erule allE, erule allE, erule mp)
  apply (drule le_funD, blast)
  done

lemma mono_app': "mono g \<Longrightarrow> mono (\<lambda>f x. g (f x) x)"
  apply (clarsimp simp: mono_def)
  apply (rule le_funI)
  apply (erule_tac x="(x xa)" in allE, erule_tac x="(y xa)" in allE)
  apply (drule mp)
   apply (drule le_funD, blast)
  apply (drule le_funD, blast)
  done

lemma mono_conj[mono_thms]:"mono f \<Longrightarrow> mono g \<Longrightarrow> mono (\<lambda>x. f x \<and> g x)"
  by (clarsimp simp: mono_def)


lemma mono_conj'[mono_thms]:"mono f \<Longrightarrow> mono g \<Longrightarrow> mono (\<lambda>x a. f x a \<and> g x a)"
  apply (clarsimp simp: mono_def)
  by blast

lemma mono_imp[mono_thms]: "mono g \<Longrightarrow> antimono f \<Longrightarrow> mono (\<lambda>x a. f x a \<longrightarrow> g x a)" 
  apply (clarsimp simp: mono_def antimono_def)
  apply (blast)
  done


lemma mono_const[mono_thms]: "mono (\<lambda>x. y)"
  by (clarsimp simp: mono_def)


lemma antimono_const[mono_thms]: "antimono (\<lambda>x. y)"
  by (clarsimp simp: antimono_def)

lemma mono_apply[mono_thms]: "mono (\<lambda>x. x v)"
  apply (clarsimp simp: mono_def)
  apply (drule le_funD)
  by blast

declare mono_id[mono_thms]

lemma div_wp'[wp]: "(\<And>x. hoare_triple (lift (P x)) (c x) Q) \<Longrightarrow>
  hoare_triple (lift (\<lambda>s. m \<noteq> 0 \<and> (m \<noteq> 0 \<longrightarrow> P ( n div m) s))) 
(do {x <- (word_unsigned_div n m); c x}) Q"
  apply (rule hoare_weaken_pre, rule div_wp, assumption)
  by (clarsimp simp: bindCont_return')


lemma mul_wp'[wp]: "(\<And>x. hoare_triple (lift (P x)) (c x) Q) \<Longrightarrow>
  hoare_triple (lift (\<lambda>s. safe_mul m n  \<and> (safe_mul m n  \<longrightarrow> P (n * m) s))) 
(do {x <- (word_unsigned_mul n m); c x}) Q"
  apply (rule hoare_weaken_pre)
   apply (unfold  word_unsigned_mul_def )
   apply (simp only: Let_unfold)
   apply (rule if_wp, simp)
    apply (fastforce)
   apply (rule if_wp, simp)
   apply (wp)
  apply (clarsimp simp: safe_mul_def)
  apply (intro conjI impI; clarsimp?)
  by (simp add: mult.commute)


end
end