theory Hoare_VCG 
imports Hoare_Logic ProcessEpoch
begin




context hoare_logic begin

lemma if_wp[wp]: 
  "(B \<Longrightarrow> hoare_triple  ( lift S) ( bindCont P c) R) \<Longrightarrow> (\<not>B \<Longrightarrow> hoare_triple ( lift S') (bindCont Q c) R) \<Longrightarrow>
   hoare_triple ( lift (if B then S else S'))  (do {x <- (if B then P else Q); c x}) R"
  apply (clarsimp split: if_splits)
  done



definition "const_p s \<equiv> Abs_p_set (Pair {id, (\<lambda>_. s)} (\<lambda>_. s))"

lemma point_of_const_p[simp]: "point_of (const_p s) = (\<lambda>_. s)"
  apply (clarsimp simp: const_p_def point_of_def)
  thm Abs_p_set_inverse
  by (subst Abs_p_set_inverse; clarsimp?)

lemma hoare_assert_state_liftI:"(\<And>s. lift ( P) s \<Longrightarrow> hoare_triple (lift (\<lambda>s'. \<forall>s''. point_of s' s'' = s )) f Q) \<Longrightarrow> hoare_triple (lift P) f Q"
  apply (clarsimp simp: hoare_triple_def assert_galois_test)
  apply (subst test_split)
  apply (subst Nondet_seq_distrib)
  apply (subst Sup_le_iff)
  apply (clarsimp)
  apply (rule order_trans[rotated])
   apply (assumption)
  apply (rule seq_mono)
   apply (subst test.hom_iso[symmetric])
   apply (simp add: lift_def, clarsimp)
  apply (rule_tac x= "const_p (a,b)" in exI)
   apply (fastforce)
  apply (clarsimp)
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


lemma lift_exD: "lift (\<lambda>s. \<exists>x. P x s) s \<Longrightarrow> \<exists>x. lift (\<lambda>s. P x s) s"
  apply (unfold lift_def, clarsimp)
  apply (fastforce)
  done

lemma hoare_all_ex: "(\<And>x. hoare_triple (lift (P x)) f Q) \<Longrightarrow> hoare_triple (lift (EXS x. P x)) f Q"
  apply (rule hoare_assert_state_liftI)
  apply (clarsimp)
  apply (drule lift_exD, clarsimp)
  apply (rule hoare_weaken_pre, fastforce)
  apply (clarsimp simp: lift_def)
  by (rule_tac x=S in exI, fastforce)

lemma read_beacon_wp_ex[wp]: "(\<And>x. hoare_triple ( lift (P x)) (c x) (Q )) \<Longrightarrow> 
hoare_triple (lift ((EXS v. maps_to l v \<and>* (maps_to l v \<longrightarrow>*  (P v ))))) (do {v <- read_beacon l ; c v}) (Q  )"
  apply (rule hoare_all_ex)
  apply (rule read_beacon_wp)
  by (fastforce)


lemma write_beacon_wp': "\<lblot>\<lless>P\<then>\<rblot> c () \<lblot>Q\<rblot> \<Longrightarrow> \<lblot>\<lless>(EXS v. l \<mapsto>\<^sub>l v) \<and>* (l \<mapsto>\<^sub>l v' \<longrightarrow>* P)\<then>\<rblot> bindCont (write_to l v') c \<lblot>Q\<rblot>"
  apply (rule hoare_assert_state_liftI)
  apply (clarsimp simp: sep_conj_exists1)
  apply (drule lift_exD, clarsimp)

  apply (rule hoare_weaken_pre)
   apply (rule write_beacon_wp, fastforce)
  apply (clarsimp simp: lift_def)
  by (fastforce)


lemma free_wp[wp]:" \<lblot>\<lless>P ()\<then>\<rblot> c () \<lblot>Q\<rblot> \<Longrightarrow> \<lblot>\<lless>\<lambda>s.  ((EXS v. l \<mapsto>\<^sub>l v) \<and>* P ()) s\<then>\<rblot> (bindCont (free l) c) \<lblot>Q\<rblot>"
  apply (clarsimp simp: free_def hoare_triple_def run_def bindCont_def)
  apply (rule Inf_lower2)
  apply (clarsimp simp: image_iff)
   apply (rule_tac x="P ()" in exI)
   apply (rule refl)
  apply (rule order_trans)
   apply (rule seq_mono_right)
   apply (assumption)
  apply (rule order_trans)
   apply (rule hoare_chain')
   apply (rule order_refl)
  apply (rule seq_mono_left)
  apply (subst assert_iso[symmetric])
  by (clarsimp)





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




lemma range_empty_iff: " (range x y z) = [] \<longleftrightarrow> (x \<ge> y) \<or> z = 0"
  apply (case_tac z; clarsimp)
  done 

lemma start_in_valid_range[simp]: "range x y z \<noteq> [] \<Longrightarrow> x \<in> list.set (range x y z)"
  apply (clarsimp simp: range_empty_iff)
  by (case_tac z; clarsimp?)



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


lemma mapM_lift_imp: "(\<forall>x\<in>list.set xs. (B x \<longrightarrow> P x)) \<longrightarrow> R (map (\<lambda>x. if B x then f x else g x) xs) s  \<Longrightarrow> mapM (\<lambda>x R s. if B x then P x \<longrightarrow> R (f x) s else R (g x)s) xs R s"
  apply (clarsimp)
  apply (induct xs arbitrary: R s; clarsimp simp: bindCont_def return_def)
  apply (intro conjI impI; clarsimp?)
  done


  

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
  apply (intro conjI impI; clarsimp?)
   apply (metis monotoneD predicate2D)
  by (metis monotoneD predicate2D)


lemma mapM_lift_over_if2: "mapM (\<lambda>x R . P (if B x then (f R x ) else (g R x))) xs R s \<Longrightarrow> mono P \<Longrightarrow> mono f \<Longrightarrow> mono g \<Longrightarrow> mapM (\<lambda>x R s. if B x then P (f R x) s else P (g R x) s) xs R s"
  apply (clarsimp)
  apply (erule mapM_rewriteI)
  apply (clarsimp)
  apply (intro conjI impI; clarsimp?)
  apply (metis (full_types) le_boolD le_funE monotoneD)
  by (metis (full_types) le_boolD le_funE monotoneD)


lemma mapM_lift_over_if': "mapM (\<lambda>x R s. P (if B x then (f R x s) else (g R x s))) xs R s \<Longrightarrow> mono P \<Longrightarrow> mono f \<Longrightarrow> mono g \<Longrightarrow> mapM (\<lambda>x R s.  (B x \<longrightarrow> P (f R x s)) \<and> (\<not> B x \<longrightarrow> P (g R x s))) xs R s"
  apply (erule mapM_rewriteI)
  apply (clarsimp)
  apply (intro conjI impI; clarsimp?)
   apply (smt (verit, del_insts) UNIV_I le_bool_def le_fun_def monotone_on_def)
  by (smt (verit, del_insts) UNIV_I le_bool_def le_fun_def monotone_on_def)



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

lemma mono_ex[mono_thms]: "(\<And>n. mono (f n)) \<Longrightarrow> mono (\<lambda>R s. \<exists>n. f n R s)"
  apply (rule monoI; clarsimp)
  apply (rule_tac x=n in exI)
  by (meson monoE predicate1D)

lemma foldr_eq: " foldr (\<lambda>a b c d. a c (\<lambda>a. b a d)) (map (\<lambda>x xs c. f x (\<lambda>a. c (xs @ [a]))) xs) (\<lambda>a b. b a) ys (\<lambda>a. x (aa # a)) =
                        foldr (\<lambda>a b c d. a c (\<lambda>a. b a d)) (map (\<lambda>x xs c. f x (\<lambda>a. c (xs @ [a]))) xs) (\<lambda>a b. b a) (aa#ys) x" 

  by (induct xs arbitrary: ys ; clarsimp simp: k_comp_def bindCont_def return_def)



definition "foldlM f xs = foldr k_comp (map f xs) return "


definition foldrM' 
  where "foldrM' f z xs = foldl (\<lambda>f g. k_comp f g) (return) (map f xs)  z  "


primrec sequence :: "(('e, 'r) cont) list \<Rightarrow> ('e list, 'r) cont" where
  "sequence (x#xs) = do {a <- x ; b <- sequence xs; return (a # b)} " |
  "sequence [] = return []"


lemma mapM_is_foldr_map: "mapM f xs = foldr (\<lambda>x xs. do {y <- x; ys <- xs; return (y # ys)}) (map f xs) (return []) "
  apply (clarsimp simp: foldlM_def foldrM_def comp_def bindCont_def return_def k_comp_def)
  by (induct xs; clarsimp simp: bindCont_def return_def foldrM_def k_comp_def return_def)

lemma mapM_is_sequence_map: "mapM f xs = sequence (map f xs) "
  by (induct xs; clarsimp simp: bindCont_def return_def foldrM_def k_comp_def return_def)

lemma mono_sequence: "\<forall>f\<in>(list.set xs). mono f \<Longrightarrow> mono (sequence xs)"
  apply (induct xs; clarsimp intro!: monoI simp: return_def bindCont_def)
   apply (erule le_funD)
  apply (erule monoD)
  apply (rule le_funI)
  apply (erule monoD)
  apply (rule le_funI)
   apply (erule le_funD)
  done

lemma mono_mapM: "(\<And>a. mono (f a)) \<Longrightarrow> mono (mapM f xs)" 
  apply (subst mapM_is_sequence_map)
  apply (rule mono_sequence)
  apply (clarsimp)
  done



lemma seq_map_exsI: "(\<And>a b. mono (f a b)) \<Longrightarrow> (EXS g. sequence (map (\<lambda>x. f (g x) x) xs) R) s \<Longrightarrow> (sequence (map (\<lambda>c s r. \<exists>x. f x c s r) xs) R) s "
  
  apply (induct xs arbitrary: R s ; clarsimp simp: return_def)
  apply (clarsimp simp: bindCont_def return_def)
  apply (rule_tac x="x a" in exI)
  apply (atomize, erule_tac x="x a" in allE, erule_tac x="a" in allE)
  apply (drule monoD)
   defer
   apply (drule_tac x=s in le_funD)
  using le_boolD apply blast
  apply (clarsimp)
  apply (blast)
  done

lemma seq_map_factor: "sequence (map (\<lambda>x R s.  (B x \<longrightarrow> P (f R x s)) \<and> (\<not> B x \<longrightarrow> P (g R x s))) xs) R = sequence (map (\<lambda>x R s. P (if B x then (f R x s) else (g R x s))) xs) R "
  by (clarsimp)

lemma seq_map_factor': "sequence (map (\<lambda>x R s. if B x then P (f R x) s else P (g R x) s) xs) R = 
                        sequence (map (\<lambda>x R . P (if B x then (f R x ) else (g R x))) xs) R "
  apply (subst map_cong[where g="(\<lambda>x R. P (if B x then f R x else g R x)) "])
    apply (rule refl)
  apply (intro ext)
  apply (clarsimp)
  by (clarsimp)


lemma list_nonempty_induct:
  "\<lbrakk> xs \<noteq> []; \<And>x. P [x]; \<And>x xs. xs \<noteq> [] \<Longrightarrow> P xs \<Longrightarrow> P (x # xs)\<rbrakk> \<Longrightarrow> P xs"
  by(induction xs rule: induct_list012) auto

lemma sym_eq: "(x = y) = (y = x)"
  by (safe; clarsimp)


lemma commute_sequence: "(\<And>a. a \<in> list.set xs \<Longrightarrow> \<forall>v. f (\<lambda>x. a (v x)) = a (\<lambda>a. f (\<lambda>aa. v aa a))) \<Longrightarrow> sequence (xs) (\<lambda>aa. f (\<lambda>x. g x aa))  =
                      f (\<lambda>a. sequence (xs) (g a)) "
  apply (induct xs arbitrary: g)
   apply (clarsimp simp: return_def bindCont_def)
  apply (clarsimp simp: return_def bindCont_def)
 apply (atomize)
  apply (erule_tac x=a in allE)
  apply (clarsimp)
  done

lemma mapM_split:  "(\<And>x a R. x \<in> list.set xs \<Longrightarrow> f a (\<lambda>y. P x \<and>* (P x \<longrightarrow>* R y x)) = (P x \<and>* (P x \<longrightarrow>* f a (\<lambda>y. R y x)))) \<Longrightarrow>
  sequence (map (\<lambda>x R. P x \<and>* (P x \<longrightarrow>* f x R)) xs) R = (sequence (map (\<lambda>x R. (P x \<and>* (P x \<longrightarrow>* R x))) xs)  (\<lambda>xs. sequence (map f xs) R)) "
  apply (induct xs arbitrary: R)
   apply (clarsimp simp: return_def bindCont_def)
    apply (clarsimp simp: return_def bindCont_def)
  apply (subst commute_sequence[where f="f _"])
   defer
   apply (clarsimp)
  by (clarsimp)

lemma "(\<lambda>R. f a (\<lambda>y. g x (R y x))) = (bindCont (f a) (\<lambda>y f. g x (f y x))) "
  apply (clarsimp simp: bindCont_def)
  oops


lemma mapM_split_gen:  "(\<And>x a R. x \<in> list.set xs \<Longrightarrow> f a (\<lambda>y. g x (R y x)) =  g x (f a (\<lambda>y. R y x))) \<Longrightarrow>
  sequence (map (\<lambda>x R. g x (f x R)) xs) R = (sequence (map(\<lambda>x R. g x (R x)) xs)  (\<lambda>xs. sequence (map f xs) R)) "
  apply (induct xs arbitrary: R)
   apply (clarsimp simp: return_def bindCont_def)
    apply (clarsimp simp: return_def bindCont_def)
  apply (subst commute_sequence[where f="f _"])
   defer
   apply (clarsimp)
  by (clarsimp)


lemma strange: "\<forall>y\<in>{x}. P (f y) \<Longrightarrow> P (f x)"
  apply (blast)
  done



lemma seq_map_lift: "(P \<and>* (P \<longrightarrow>* R (map f xs))) s \<Longrightarrow>
           sequence (map (\<lambda>x R. (P \<and>*
                       ( P \<longrightarrow>* R (f x)))) xs) R  s"
  apply (induct xs arbitrary: R s; clarsimp simp: return_def)
   apply (sep_mp, clarsimp)
  apply (clarsimp simp: return_def bindCont_def)
  apply (sep_cancel)+
  apply (sep_select_asm 2)
  apply (atomize)
  apply (erule_tac x="\<lambda>xs. R (f a # xs)" in allE) 
  by blast


lemma lift_pure_sequence_map: "(\<forall>x\<in>(list.set xs). P x) \<and> ((\<forall>x\<in>(list.set xs). P x ) \<longrightarrow> sequence (map f xs) R s) \<Longrightarrow> (\<And>a. mono (f a)) \<Longrightarrow>
           (sequence (map (\<lambda>x R s. (P x  \<and>
                       ( P x  \<longrightarrow> f x R s))) xs)) R s"
    apply (induct xs arbitrary: R s)
     apply (clarsimp)
    apply (safe)
  apply (clarsimp simp: return_def bindCont_def)
  apply (atomize)
  apply (erule_tac x=a in allE)
  apply (drule monoD)
   defer
   apply auto[1]
  apply (rule le_funI)+
  apply (clarsimp)
  done


lemma seq_left_if_cond[simp]: "sequence (map (\<lambda>x R s. if B x s then (P x s \<and> (P x s \<longrightarrow> f x R s)) else g x R s) xs ) R = 
       sequence (map (\<lambda>x R s. (B x s \<longrightarrow> P x s) \<and> ((B x s \<longrightarrow> P x s) \<longrightarrow> (if B x s then f x R s else g x R s))) xs ) R"
  by (induct xs arbitrary: R; clarsimp simp: return_def)

lemma swap_if: " x \<in> xs \<Longrightarrow>  (B x \<Longrightarrow> f x (\<lambda>b. g x xs b R) = (\<lambda>b. g x xs b (f x R))) \<Longrightarrow> (\<not> B x \<Longrightarrow> f x (\<lambda>b. h x xs b R) = (\<lambda>b. h x xs b (f x R))) \<Longrightarrow>
       f x (if B x
          then (\<lambda>b. g x xs b R)
          else (\<lambda>b. h x xs b R))  =
        (if B x
          then (\<lambda>b. g x xs b (f x R))
          else (\<lambda>b. h x xs b (f x R)))"
  by (clarsimp split: if_splits)


lemma seq_left_if_cond'[simp]: "sequence (map (\<lambda>x R. if B x then (\<lambda>s. (P x s \<and> (P x s \<longrightarrow> f x R s))) else g x R) xs ) R = 
       sequence (map (\<lambda>x R s. (B x \<longrightarrow> P x s) \<and> ((B x \<longrightarrow> P x s) \<longrightarrow> (if B x then f x R s else g x R s))) xs ) R"
  apply (rule arg_cong[where f="\<lambda>xs. sequence xs R"])
  apply (rule map_cong; clarsimp?)
  by (intro ext iffI; clarsimp split: if_splits)


abbreviation (input) Fi  ("(fi (_)/ then (_)/ else (_))" [0, 0, 10] 10)
  where "Fi P x y \<equiv> if P then y else x"


lemma seq_right_if_cond[simp]: "sequence (map (\<lambda>x R s. fi B x s then (P x s \<and> (P x s \<longrightarrow> f x R s)) else g x R s) xs ) R = 
       sequence (map (\<lambda>x R s. (\<not>B x s \<longrightarrow> P x s) \<and> ((\<not>B x s \<longrightarrow> P x s) \<longrightarrow> (fi B x s then f x R s else g x R s))) xs ) R"
  by (induct xs arbitrary: R; clarsimp simp: return_def bindCont_def)

lemma seq_right_if_cond'[simp]: "sequence (map (\<lambda>x R. fi B x then (\<lambda>s. (P x s \<and> (P x s \<longrightarrow> f x R s))) else g x R) xs ) R = 
       sequence (map (\<lambda>x R s. (\<not>B x \<longrightarrow> P x s) \<and> ((\<not>B x \<longrightarrow> P x s) \<longrightarrow> (fi B x then f x R s else g x R s))) xs ) R"
  apply (rule arg_cong[where f="\<lambda>xs. sequence xs R"])
  apply (rule map_cong; clarsimp?)
  by (intro ext iffI; clarsimp split: if_splits)

lemma factor_R: "(\<lambda>x R s. if B x s then R (f x s) s else R (g x s) s) =  (\<lambda>x R s. R (if B x s then (f x s) else (g x s)) s)"
  by (intro ext, clarsimp split: if_splits)


lemma factor_R': "(\<lambda>x R. if B x then R (f x) else R (g x) ) =  (\<lambda>x R. R (if B x then (f x ) else (g x )) )"
  by (intro ext, clarsimp split: if_splits)

lemma seq_simp: "sequence (map (\<lambda>x R s. R (f s x) s) xs) R s = R (map (f s) xs) s"
  by (induct xs arbitrary: R; clarsimp simp: return_def bindCont_def)


lemma assumes R_split: "(\<And>x xs s. R (x#xs) s \<Longrightarrow> (R [x] \<and>* R xs) s)" shows
 "(P \<and>* R (map (if B then f else g) xs))  s \<Longrightarrow>  sequence (map (\<lambda>x R. (P  \<and>* (P  \<longrightarrow>* (if B then R (f x) else R (g x))))) xs) (\<lambda>xs. (P \<and>* R xs)) s"
  apply (subst mapM_split)
   apply (clarsimp split: if_splits)
  apply (rule seq_map_lift)
  apply (sep_cancel)+
  apply (erule sep_curry[rotated])
  apply (simp add:  factor_R' seq_simp)
  apply (sep_cancel)
  by presburger

lemma sequence_mono: "sequence (map g xs) R s \<Longrightarrow> (\<And>x R s. x \<in> list.set xs \<Longrightarrow> g x R s \<Longrightarrow> f x R s) \<Longrightarrow> (\<And>a. mono (g a)) \<Longrightarrow>  sequence (map f xs) R s"
  apply (induct xs arbitrary: s R; clarsimp simp: return_def bindCont_def)
  by (smt (verit, best) monotoneD predicate1D predicate2I)

lemma sequenceI_rewriting: assumes rewrite_loop: "(\<And>x R s. x \<in> list.set xs \<Longrightarrow>  (I \<and>* P x \<and>* (Q x \<and>* I \<longrightarrow>* R (g x))) s \<Longrightarrow> f x R s)"
  shows " (I \<and>* (foldr sep_conj (map P xs) sep_empty) \<and>* 
           ( (foldr sep_conj (map Q xs) sep_empty) \<and>* I \<longrightarrow>* R (map g xs))) s \<Longrightarrow>  sequence (map f xs) R s"
  apply (rule sequence_mono[rotated])
    apply (erule (1) rewrite_loop)
  apply (intro mono_thms)
  apply (induct xs arbitrary: R s; clarsimp simp: return_def)
  apply (sep_mp, clarsimp)
  apply (clarsimp simp: bindCont_def return_def)
  apply (sep_cancel)+
  by (smt (z3) sep.mult.left_commute sep.mult_assoc sep_conj_impl sep_curry sep_mp_gen)

lemma foldr_pure:  "(foldr sep_conj (map (\<lambda>x s. sep_empty s \<and> f x) xs) sep_empty \<and>* R) = (\<lambda>s. (\<forall>x\<in>(list.set xs). f x) \<and> R s)"
  by (induct xs arbitrary: ; clarsimp)

declare mapM_fake[wp]


lemma letI: "(\<And>x. x = y \<Longrightarrow> P x) \<Longrightarrow> (let x = y in P x)"
  by (fastforce simp: Let_unfold)


lemma letE: "(let x = y in P x) \<Longrightarrow> (\<And>x. x = y \<Longrightarrow> P x \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (fastforce simp: Let_unfold)


lemma sequenceI_rewriting': assumes rewrite_loop: "(\<And>x R s. x \<in> list.set xs \<Longrightarrow> \<exists>n. (I \<and>* P x \<and>* S n \<and>* (Q x \<and>* I \<and>* S (h n x) \<longrightarrow>* R (g x))) s \<Longrightarrow> f x R s)"
  shows " (I \<and>* S n \<and>* (foldr sep_conj (map P xs) sep_empty) \<and>* 
           ( (foldr sep_conj (map Q xs) sep_empty) \<and>* I \<and>* S (foldl h n xs) \<longrightarrow>* R (map g xs))) s \<Longrightarrow>  sequence (map f xs) R s"
  apply (rule sequence_mono[rotated])
    apply (erule (1) rewrite_loop)
  apply (intro mono_thms)
   apply (induct xs arbitrary: n R s; clarsimp simp: return_def)
  apply (sep_mp, clarsimp)
  apply (clarsimp simp: bindCont_def return_def)
  apply (rule_tac x=n in exI)
  apply (sep_cancel)+
  apply (clarsimp simp: sep_conj_ac)
  apply (atomize)
  apply (erule allE)
  apply (erule allE)
  apply (erule allE)
  apply (erule mp)
  apply (sep_cancel)+
  apply (sep_mp)
  apply (clarsimp simp: sep_conj_ac, sep_mp)
  by (clarsimp)


lemma sequenceI_rewriting'': assumes rewrite_loop: "(\<And>x R s. x \<in> list.set xs \<Longrightarrow> \<exists>n. D (h n x) \<and> (I \<and>* P x \<and>* S n \<and>* (Q x \<and>* I  \<and>* S (h n x) \<longrightarrow>* R (g x))) s \<Longrightarrow> f x R s)"
  assumes descending: "(\<And>v xs. D (foldl h v xs) \<Longrightarrow> D v)" 
  shows " (I  \<and>* S n \<and>* (foldr sep_conj (map P xs) sep_empty) \<and>* 
           ( (foldr sep_conj (map Q xs) sep_empty) \<and>* I  \<and>* S (foldl h n xs) \<longrightarrow>* R (map g xs))) s \<Longrightarrow> D (foldl h n xs) \<Longrightarrow>  sequence (map f xs) R s"
  apply (rule sequence_mono[rotated])
    apply (erule (1) rewrite_loop)
  apply (intro mono_thms)
   apply (induct xs arbitrary: n R s; clarsimp simp: return_def)
  apply (sep_mp, clarsimp)
  apply (clarsimp simp: bindCont_def return_def)
  apply (rule_tac x=n in exI)
  apply (intro conjI)
  apply (erule descending)
  apply (sep_cancel)+
  apply (clarsimp simp: sep_conj_ac)
  apply (atomize)
  apply (erule_tac x="(h n a)" in allE)
  apply (erule_tac x="\<lambda>v. R (g a # v)" in allE)
  apply (erule allE)
  apply (drule mp)
  apply (sep_cancel)+
   apply (sep_mp)
   apply (clarsimp simp: sep_conj_ac, sep_mp)
  apply (assumption)

  apply (drule mp)
   apply (clarsimp)
  apply (assumption)
  done




lemma helper_sequenceI: assumes descend: "\<And>a v n. D (h a v) n \<Longrightarrow> D v n" shows "D (fold h xs v) n \<Longrightarrow> D v n"
  apply (induct xs arbitrary: n v; clarsimp)
  apply (drule_tac x="n" in meta_spec)
  apply (drule_tac x="(h a v)" in meta_spec)
  apply (drule meta_mp, clarsimp)
  by (erule descend)



primrec scanl :: "('f \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'f list \<Rightarrow> 'g \<Rightarrow> 'g list" where
scanl_Nil:  "scanl f [] n = [n]" |
scanl_Cons: "scanl f (x # xs) n = n # scanl f xs (f x n)"  



fun pairs :: "'f list \<Rightarrow> ('f \<times> 'f) set" where
pairs_Nil:  "pairs [] = {}" |
pairs_Single: "pairs [x] = {}" |  
pairs_Pair: "pairs (x#y#xs) = {(x,y)} \<union> pairs (y#xs) "   


lemma in_pairs_iff: "(a,b) \<in> pairs xs \<longleftrightarrow> (\<exists>n. n + 1 < length xs \<and> xs ! n = a \<and> xs ! (n + 1) = b)"
  apply (rule iffI)
   apply (induct xs arbitrary: a b rule: pairs.induct  ; clarsimp?)
   apply (elim disjE; clarsimp?)
    apply (rule_tac x=0 in exI, clarsimp)
   apply (drule meta_spec, drule meta_spec, drule meta_mp, assumption)
   apply (clarsimp)
   apply (meson not_less_eq nth_Cons_Suc)
   apply (induct xs arbitrary: a b rule: pairs.induct  ; clarsimp?)
  
  by (metis One_nat_def diff_Suc_1' less_Suc_eq_0_disj nth_Cons')
 

lemma pairs_sub: "pairs (xs) \<subseteq> pairs (x # xs) "
  apply (clarsimp simp: in_pairs_iff) 
  by fastforce

lemma sequenceI_rewriting''': assumes rewrite_loop: "(\<And>x R s. x \<in> list.set xs \<Longrightarrow> \<exists>n. D (n, (h x n)) \<and> (I \<and>* P x \<and>* S n \<and>* (Q x \<and>* I  \<and>* S (h x n) \<longrightarrow>* R (g x))) s \<Longrightarrow> f x R s)"
  shows " (I  \<and>* S n \<and>* (foldr sep_conj (map P xs) sep_empty) \<and>* 
           ( (foldr sep_conj (map Q xs) sep_empty) \<and>* I  \<and>* S (fold h xs n) \<longrightarrow>* R (map g xs))) s \<Longrightarrow> \<forall>x\<in>(pairs (scanl h xs n)). D x \<Longrightarrow>   sequence (map f xs) R s"
  apply (rule sequence_mono[rotated])
    apply (erule (1) rewrite_loop)
  apply (intro mono_thms)
   apply (induct xs arbitrary: n R s; clarsimp simp: return_def)
  apply (sep_mp, clarsimp)
  apply (clarsimp simp: bindCont_def return_def)
  apply (rule_tac x=n in exI)
  apply (intro conjI)
   apply (erule bspec)
  apply (case_tac xs; clarsimp)


  apply (sep_cancel)+
  apply (clarsimp simp: sep_conj_ac)
  apply (atomize)
  apply (erule allE, erule allE, erule allE)
  apply (drule mp)
  defer
   apply (drule mp)
    defer
    apply (assumption)
   apply (sep_cancel)+
   apply (sep_mp)
  apply (clarsimp simp: sep_conj_ac, sep_mp)
   apply (assumption)
using pairs_sub 
  by (metis subset_iff)

definition "acc f \<equiv> \<lambda>x (i,y). (y, f x y)" 

lemma acc_iff: "acc f x y = (a, b) \<longleftrightarrow> a = snd y \<and> b = f x (snd y)"
  apply (simp add: acc_def)
  by (intro iffI; clarsimp split: prod.splits)

lemma acc_simp[simp]: "acc f x (y, z) = (z, f x z)" by (simp add: acc_def)

primrec transitions where 
"transitions f [] n = {}" | 
"transitions f (x#xs) n = (\<lambda>((n, s), (_, s')). (n, s, s'))  ` (pairs (scanl (acc f) (x#xs) (x, n)))" 

lemma scanl_0th[simp]: " scanl f xs n ! 0 =  n"
  by (case_tac xs; clarsimp)

lemma scanl_first[simp]: "xs \<noteq> [] \<Longrightarrow> scanl f xs n ! Suc 0 = f (xs ! 0) n"
  by (case_tac xs; clarsimp)


lemma pairs_cons[simp]: "xs \<noteq> [] \<Longrightarrow> pairs (x # xs) = {(x, xs ! 0)} \<union> pairs xs"
  by (case_tac xs; clarsimp)



lemma scanl_nonempty[simp]: "scanl f xs n \<noteq> []" by (case_tac xs; clarsimp)


primrec trans where
 "trans f [] n = {}" |
 "trans f (a#xs) n = {(a, n, f a n)} \<union> trans f xs (f a n)"



lemma sequenceI_rewriting4: assumes rewrite_loop: "(\<And>x R s. x \<in> list.set xs \<Longrightarrow> \<exists>n. D x n (h x n) \<and> (I \<and>* P x \<and>* S n \<and>* (Q x \<and>* I  \<and>* S (h x n) \<longrightarrow>* R (g x))) s \<Longrightarrow> f x R s)"
  shows " (I  \<and>* S n \<and>* (foldr sep_conj (map P xs) sep_empty) \<and>* 
           ( (foldr sep_conj (map Q xs) sep_empty) \<and>* I  \<and>* S (fold h xs n) \<longrightarrow>* R (map g xs))) s \<Longrightarrow> \<forall>(v, s, s')\<in>(trans h xs n). D v s s' \<Longrightarrow>   sequence (map f xs) R s"
  apply (rule sequence_mono[rotated])
    apply (erule (1) rewrite_loop)
  apply (intro mono_thms)
   apply (induct xs arbitrary: n R s, clarsimp simp: return_def)
  apply (sep_mp, clarsimp)
  apply (clarsimp simp: bindCont_def return_def)
  apply (rule_tac x=n in exI)
  apply (intro conjI)
  apply (erule ballE, fastforce, fastforce)

  apply (sep_cancel)+
  apply (clarsimp simp: sep_conj_ac)
  apply (atomize)
  apply (erule allE, erule allE, erule allE)
  apply (drule mp)
  defer
   apply (drule mp)
    defer
    apply (assumption)
   apply (sep_cancel)+
   apply (sep_mp)
  apply (clarsimp simp: sep_conj_ac, sep_mp)
   apply (assumption)
  apply (blast)
  done


lemma lift_exE: "lift (EXS x. P x) s \<Longrightarrow> \<exists>x. (lift (P x)) s "
  apply (clarsimp simp: lift_def)
  apply (blast)
  done

end
end