(*
 * Copyright 2017, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

(*
 Unified Correctness reasoning in Separation Logic. Defines a
 concrete model of type (heap x bool) as an early extension
 of SL to deal with failure.
*)

theory Unified_Correctness
imports
  Extended_Separation_Algebra
  Hoare_Sep_Tactics
  Det_Monad
begin

type_synonym ('a, 'b) heap = "'a \<Rightarrow> 'b option"
type_synonym ('a, 'b) machine = "('a, 'b) heap \<times> bool"

abbreviation "heap ::  ('a, 'b) machine \<Rightarrow> ('a, 'b) heap \<equiv> fst"
abbreviation "nf ::  ('a, 'b) machine \<Rightarrow> bool \<equiv> snd"

instantiation "prod" :: (cancellative_sep_algebra, cancellative_sep_algebra) cancellative_sep_algebra
begin
instance
  apply (intro_classes; clarsimp simp: sep_disj_prod_def plus_prod_def zero_prod_def)
  apply (simp add: sep_disj_positive)
  by (simp add: sep_add_cancel)
end

instantiation "bool" :: cancellative_sep_algebra
begin
instance
  by (intro_classes) (auto simp: zero_bool_def plus_bool_def sep_disj_bool_def)
end

definition
  maps_to:: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) machine \<Rightarrow> bool" ("_ \<mapsto>u _" [56,51] 56)
where
  "x \<mapsto>u y \<equiv> \<lambda>h. heap h = [x \<mapsto> y] \<and> nf h "

definition
  maps_to_ex :: "'a \<Rightarrow>  ('a, 'b) machine \<Rightarrow> bool" ("_ \<mapsto>u -" [56] 56)
where
  "x \<mapsto>u - \<equiv> (\<lambda>s. \<exists>y. (x \<mapsto>u y) s)"


lemma maps_to_maps_to_ex [elim!]:
  "(p \<mapsto>u v) s \<Longrightarrow> (p \<mapsto>u -) s"
  by (auto simp: maps_to_ex_def)

lemma maps_to_ex_simp[simp]: "(p \<mapsto>u -) ([p \<mapsto> v], True)"
  by (clarsimp simp: maps_to_ex_def maps_to_def, fastforce)


type_synonym ('a, 'b) machine_pred = "('a, 'b) machine \<Rightarrow> bool"

definition
  sept :: "('a, 'b) machine_pred \<Rightarrow> ('a, 'b) machine_pred \<Rightarrow> ('a, 'b) machine_pred" (infix "-&" 50)
where
  "sept P Q \<equiv> \<lambda>s. \<exists>h h'. P h \<and> Q h' \<and>
                         (if nf h \<and> nf s
                          then h + s = h' \<and> h ## s
                          else nf h' \<longrightarrow> (nf h  \<longrightarrow> h ## h') \<and> (nf s \<longrightarrow> s ## h'))"

definition
  sep_con :: "('a, 'b) machine_pred \<Rightarrow> ('a, 'b) machine_pred \<Rightarrow> ('a, 'b) machine_pred" (infix "\<and>&" 50)
where
  "sep_con P Q \<equiv> \<lambda>s. \<exists>h h'. P h \<and>  Q h' \<and>
                            (if nf h \<and> nf h'
                             then h' + h = s \<and> h ## h'
                             else nf s \<longrightarrow> (nf h \<longrightarrow> h ## s) \<and> (nf h' \<longrightarrow>  s ## h'))"


lemma delete_pointer_empty: "(p \<mapsto>u v -& p \<mapsto>u v) s \<Longrightarrow> \<box> s"
  apply (clarsimp simp: sept_def  maps_to_def zero_prod_def sep_empty_def split: if_splits)
  apply (drule mp)
   apply (clarsimp simp: sep_disj_prod_def sep_disj_fun_def  sep_disj_option_def
                  split: if_splits option.splits)
   apply (metis)
  apply (clarsimp)
  by (metis sep_add_cancelD disjoint_zero_sym sep_add_commute sep_add_zero_sym
             sep_disj_commuteI zero_prod_def)


lemma sep_con_commute:
  "sep_con P Q s \<Longrightarrow> sep_con Q P s"
  apply (clarsimp simp: sep_con_def)
  apply (rename_tac x y a b)
  apply (rule_tac x="a" in exI)
  apply (rule_tac x="b" in exI)
  apply (intro conjI)
   apply (clarsimp)
  apply (rule_tac x="x" in exI)
  apply (rule_tac x="y" in exI)
  apply (intro conjI)
   apply (clarsimp, intro conjI impI)
  using sep_add_commute apply fastforce
   apply (clarsimp simp: sep_disj_commute sep_add_commute)+
  using sep_disj_commuteI by fastforce

definition
  sep_imp :: "('a, 'b) machine_pred \<Rightarrow> ('a, 'b) machine_pred \<Rightarrow> ('a, 'b) machine_pred" (infix "\<longrightarrow>&" 50)
where
  "sep_imp P Q \<equiv> not (sept P (not Q))"

definition
  sep_snake :: "('a, 'b) machine_pred \<Rightarrow> ('a, 'b) machine_pred \<Rightarrow> ('a, 'b) machine_pred"
where
  "sep_snake P Q \<equiv> not ( sep_con P (not Q))"

lemma sep_mp:
  "sep_con P (sep_imp P R) s \<Longrightarrow> R s"
  apply (clarsimp simp: sep_con_def sep_imp_def pred_neg_def sept_def )
  apply (rename_tac x y a b)
  apply (erule_tac x=x in allE, erule_tac x=y in allE, simp)
  apply (erule_tac x="fst s" in allE, erule_tac x="snd s" in allE, simp)
  apply (elim disjE; clarsimp?)
  apply (erule notE)
  by (metis prod.collapse sep_add_commute sep_disj_commute)


lemma sep_curry:
  "R s \<Longrightarrow> sep_imp P (sep_con P R) s"
  apply (clarsimp simp: sep_con_def sep_imp_def pred_neg_def sept_def)
  apply (intro conjI; clarsimp)
   apply (rename_tac x y a b)
   apply (erule_tac x=x in allE, erule_tac x=y in allE, simp)
   apply (erule_tac x="fst s" in allE, erule_tac x="snd s" in allE, simp)
   apply (clarsimp simp: sep_add_commute sep_disj_commute)+
   apply (metis (mono_tags, lifting) prod.collapse sep_disj_commuteI)
  apply (rename_tac x y a b)
  apply (rule_tac x=x in exI, rule_tac x=y in exI, clarsimp)
  apply (rule_tac x="fst s" in exI, rule_tac x="snd s" in exI, simp)
  apply (metis (mono_tags, lifting) prod.collapse sep_disj_commuteI)
  done


lemma sep_adjoint:
  "(\<forall>s. sep_con P (sep_imp P R) s \<longrightarrow> R s) \<longleftrightarrow>
   (\<forall>s. R s \<longrightarrow> sep_imp P (sep_con P R) s)"
  using Unified_Correctness.sep_curry Unified_Correctness.sep_mp by blast


lemma sep_con_collapse:
  "sep_con (p \<mapsto>u v) (R and nf) s \<Longrightarrow> (p \<mapsto>u v \<and>* R) s"
  apply (clarsimp simp: sep_con_def)
  apply (clarsimp simp: sep_conj_def maps_to_def pred_conj_def)
  by (metis sep_add_commute)


section "Examples"

definition
  "delete_ptr p = do {
    state_assert (\<lambda>s.  s p \<noteq> None);
    modify (\<lambda>s. (\<lambda>p'. if p = p' then None else s p'))
  }"

lemma delete_ptr_sp:
  "\<lbrace>R\<rbrace> delete_ptr p  \<lbrace>\<lambda>_. (sept (p \<mapsto>u -) R) \<rbrace>u"
  apply (clarsimp simp: delete_ptr_def)
  apply (rule hoare_seq_extU[rotated])
   apply (rule modify_wpU)
  apply (rule hoare_chainU[OF state_assert_wpU, rotated])
   apply (assumption)
  apply (clarsimp)
  apply (rename_tac h f)
  apply (case_tac "h p = 0"; clarsimp simp: zero_option_def sept_def)
   apply (rule_tac x=" [p \<mapsto> undefined]" in exI)
   apply (rule_tac x=" True" in exI)
   apply (intro conjI, fastforce)
   apply (rule_tac x=h in exI, rule_tac x=f in exI)
   apply (clarsimp)
   apply (clarsimp simp: sep_disj_prod_def sep_disj_fun_def sep_disj_option_def sep_disj_bool_def)
  apply (case_tac "f"; clarsimp)
   apply (rename_tac v)
   apply (rule_tac x="[p \<mapsto> v]" in exI)
   apply (rule_tac x="True" in exI)
   apply (intro conjI, fastforce)
   apply (clarsimp)
   apply (rule_tac x=h in exI, rule_tac x=True in exI)
   apply (clarsimp, intro conjI)
    apply (clarsimp simp: plus_prod_def, intro conjI)
     apply (rule ext)
     apply (clarsimp simp: plus_fun_def plus_option_def)
    apply (clarsimp simp: plus_bool_def)
   apply (clarsimp simp: sep_disj_prod_def sep_disj_fun_def sep_disj_option_def sep_disj_bool_def)
  apply (rename_tac v)
  apply (rule_tac x="[p \<mapsto> v]" in exI)
  apply (rule_tac x="True" in exI)
  apply (intro conjI, fastforce)
  by blast

definition "the_f v d = (if (v = None) then d else (the v))"

definition
  "get_ptr p = do {
     v <- gets (\<lambda>s. s p);
     assert (v \<noteq> None);
     return (the_f v (0))
   }"

lemma maps_to_simp [simp]:
  "(p \<mapsto>u y) h = (h = ([p \<mapsto> y], True))"
  by (metis (mono_tags, lifting) fst_conv maps_to_def prod_eqI snd_conv)

lemma get_ptr_sp:
  "\<lbrace>R\<rbrace> get_ptr p \<lbrace>\<lambda>rv. (p \<mapsto>u rv \<and>& (p \<mapsto>u rv -& R))\<rbrace>u"
  apply (clarsimp simp: get_ptr_def, (rule hoare_seq_extU[rotated])+)
    apply (rule return_wpU assert_wpU)+
  apply (rule hoare_chainU[OF gets_wpU, rotated])
   apply (assumption)
  apply (clarsimp simp: gets_def validU_def)
  apply (rename_tac h f)
  apply (case_tac "(\<exists>y. h p = Some y)"; clarsimp simp: the_f_def  zero_option_def)
   apply (clarsimp simp: sep_con_def)
   apply (rule_tac x="(\<lambda>ptr. if ptr = p then None else  h ptr)" in exI)
   apply (rule_tac x="f" in exI)
   apply (clarsimp, intro conjI impI)
      apply (clarsimp simp: sept_def)
      apply (rule_tac x=h in exI, rule_tac x=f in exI, clarsimp, intro conjI)
       apply (clarsimp simp: plus_prod_def plus_bool_def)
       apply (rule ext, clarsimp simp: plus_fun_def plus_option_def)
      apply (clarsimp simp: sep_disj_prod_def sep_disj_fun_def sep_disj_option_def sep_disj_bool_def)
     apply (clarsimp simp: plus_prod_def plus_bool_def)
     apply (rule ext, clarsimp simp: plus_fun_def plus_option_def split: option.splits)
    apply (clarsimp simp: sep_disj_prod_def sep_disj_fun_def sep_disj_option_def sep_disj_bool_def)
   apply (clarsimp simp: sept_def)
   apply (blast)
  apply (clarsimp simp: sep_con_def)
  apply (rule_tac x="(\<lambda>ptr. if ptr = p then None else h ptr)" in exI, rule_tac x= False in exI)
  apply (clarsimp)
  apply (clarsimp simp: sept_def)
  apply (rule_tac x=h in exI)
  apply (rule_tac x=f in exI)
  apply (clarsimp simp: sep_disj_prod_def sep_disj_fun_def sep_disj_option_def sep_disj_bool_def)
  done

definition
  "set_ptr p v = do {
     x <- gets (\<lambda>s. s p);
     assert (x \<noteq> None);
     modify (\<lambda>s. s(p \<mapsto> v))
   }"

lemma set_ptr_sp:
  "\<lbrace>R\<rbrace> set_ptr p v \<lbrace>\<lambda>_. (p \<mapsto>u v \<and>& (p \<mapsto>u - -& R))\<rbrace>u"
  apply (clarsimp simp: set_ptr_def, (rule hoare_seq_extU[rotated])+)
    apply (rule return_wpU assert_wpU modify_wpU)+
  apply (rule hoare_chainU[OF gets_wpU, rotated])
   apply (assumption)
  apply (clarsimp simp: gets_def validU_def)
  apply (rename_tac h f)
  apply (case_tac "(\<exists>y. h p = Some y)"; clarsimp simp: the_f_def maps_to_ex_def zero_option_def)
   apply (clarsimp simp: sep_con_def)
   apply (rule_tac x="(\<lambda>ptr. if ptr = p then None else  h ptr)" in exI)
   apply (rule_tac x="f" in exI)
   apply (clarsimp, intro conjI impI)
      apply (clarsimp simp: sept_def)
      apply (rename_tac v)
      apply (rule_tac x="[p \<mapsto> v]" in exI, intro conjI, fastforce)
      apply (rule_tac x=f in exI, clarsimp)
      apply (rule exI, rule exI, intro conjI, fastforce)
       apply (clarsimp simp: plus_prod_def plus_bool_def)
       apply (rule ext, clarsimp simp: plus_fun_def plus_option_def)
      apply (clarsimp simp: sep_disj_prod_def sep_disj_fun_def sep_disj_option_def sep_disj_bool_def)
     apply (clarsimp simp: plus_prod_def plus_bool_def)
     apply (rule ext, clarsimp simp: plus_fun_def plus_option_def split: option.splits)
    apply (clarsimp simp: sep_disj_prod_def sep_disj_fun_def sep_disj_option_def sep_disj_bool_def)
   apply (clarsimp simp: sept_def)
   apply (blast)
  apply (clarsimp simp: sep_con_def)
  apply (rule_tac x="(\<lambda>ptr. if ptr = p then Some v else h ptr)" in exI, rule_tac x= False in exI)
  apply (clarsimp)
  apply (clarsimp simp: sept_def)
  apply (rule_tac x="[p \<mapsto> undefined]" in exI)
  apply (rule conjI)
   apply (fastforce)
  apply (rule_tac x=True in exI)
  apply (clarsimp simp: sep_disj_prod_def sep_disj_fun_def sep_disj_option_def sep_disj_bool_def)
  apply (blast)
  done


definition "move_ptr p p' = get_ptr p \<bind> set_ptr p'"

method guess_spec = (rule exI)+, (intro conjI; (fastforce)?)


lemma sep_con_impl2:
  "(p \<and>& q) s \<Longrightarrow> (\<And>s. q s \<Longrightarrow> q' s) \<Longrightarrow> (p \<and>& q') s"
  apply (clarsimp simp: sep_con_def)
  apply (rule exI, rule exI, rule conjI, assumption)
  by (metis (full_types) snd_conv)
 

lemma sept_impl2:
  "(p -& q) s \<Longrightarrow> (\<And>s. q s \<Longrightarrow> q' s) \<Longrightarrow> (p -& q') s"
  apply (clarsimp simp: sept_def)
  apply (fastforce)
  done

lemma sept_success:
  "(p \<mapsto>u v -& (p \<mapsto>u v' \<and>* (R and nf))) s \<Longrightarrow> (R and (\<lambda>s. nf s \<and> v = v')) s"
  apply (clarsimp simp: sept_def sep_conj_def maps_to_ex_def split: if_splits)
  apply (erule disjE, clarsimp simp: pred_conj_def)
   apply (subgoal_tac "v = v'", clarsimp)
    apply (metis sep_add_cancelD sep_add_commute sep_disj_commuteI)
   apply (clarsimp simp: plus_prod_def)
   apply (drule fun_cong[where x=p], clarsimp simp: plus_fun_def plus_option_def split: option.splits)
   apply (clarsimp simp: sep_disj_fun_def sep_disj_prod_def sep_disj_option_def split: if_splits, fastforce)
  apply (clarsimp simp: pred_conj_def plus_prod_def)
  apply (clarsimp simp: plus_fun_def plus_option_def sep_disj_fun_def sep_disj_prod_def
                        sep_disj_option_def plus_bool_def sep_disj_bool_def
                 split: if_splits)
  apply (fastforce)
  done

lemma sep_add_cancel_maps_toD: "[p \<mapsto> v] + x = [p \<mapsto> v'] + y \<Longrightarrow> [p \<mapsto> v] ## x \<Longrightarrow>
    [p \<mapsto> v'] ## y \<Longrightarrow> v = v'"
  apply (clarsimp simp: plus_fun_def plus_option_def sep_disj_fun_def 
         sep_disj_prod_def sep_disj_option_def plus_bool_def sep_disj_bool_def split: if_splits)
  by (drule fun_cong[where x=p], clarsimp)


lemma sept_success_ex:
  "(p \<mapsto>u - -& (p \<mapsto>u - \<and>* (R and nf))) s \<Longrightarrow> (R and nf) s"
  apply (clarsimp simp: sept_def sep_conj_def maps_to_ex_def split: if_splits)
  apply (erule disjE, clarsimp simp: pred_conj_def)
  apply (clarsimp simp: plus_prod_def, frule sep_add_cancel_maps_toD; clarsimp simp: sep_disj_prod_def)
  apply (smt Extended_Separation_Algebra.cancellative_sep_algebra_class.sep_add_cancelD prod.collapse sep_add_commute sep_disj_commuteI)
   apply (clarsimp simp: plus_prod_def)
   apply (clarsimp simp: plus_fun_def plus_option_def sep_disj_fun_def sep_disj_prod_def sep_disj_option_def plus_bool_def sep_disj_bool_def split: if_splits)
  apply (fastforce simp: pred_conj_def)
  done


lemma sep_maps_to_success:
  "(p \<mapsto>u v \<and>* R) s \<Longrightarrow> (\<And>s. R s \<Longrightarrow> nf s) \<Longrightarrow> ((p \<mapsto>u v \<and>* R) and nf) s"
  apply (clarsimp simp: sep_conj_def pred_conj_def)
  by (simp add: plus_prod_def plus_bool_def)

lemma maps_to_nf:
  "(p \<mapsto>u v) s \<Longrightarrow> ((p \<mapsto>u v) and nf) s"
  by (clarsimp simp: pred_conj_def maps_to_def)

lemma maps_to_ex_nf:
  "(p \<mapsto>u -) s \<Longrightarrow> ((p \<mapsto>u -) and nf) s"
  by (clarsimp simp: pred_conj_def maps_to_ex_def maps_to_def)


lemma move_ptr_validU:
  "\<lbrace>(p \<mapsto>u v \<and>* p' \<mapsto>u -)\<rbrace> move_ptr p p' \<lbrace>\<lambda>_. (p \<mapsto>u v \<and>* p' \<mapsto>u v)\<rbrace>u"
  apply (clarsimp simp: move_ptr_def, rule hoare_seq_extU)
   apply (rule hoare_chainU, rule get_ptr_sp, assumption, assumption)
  apply (rule hoare_chainU[OF set_ptr_sp])
   apply (assumption)
  apply (subgoal_tac "x=v", clarsimp)
   apply (drule sep_con_impl2)
    apply (drule sept_impl2)
     apply (drule sep_con_impl2)
      apply (drule sept_impl2)
       apply (sep_drule maps_to_ex_nf[where p=p'])
       apply (sep_select_asm 2, assumption)
      apply (drule sept_success, assumption+)
   apply (drule sep_con_impl2)
    apply (drule sept_impl2)
     apply (rule sep_con_collapse[where p=p and R="p' \<mapsto>u -"])
     apply (erule sep_con_impl2)
     apply (clarsimp simp: pred_conj_def)
    apply (drule sept_impl2)
     apply (sep_drule maps_to_nf)
     apply (sep_select_asm 2, assumption)
    apply (drule sept_success_ex, assumption)
   apply (drule sep_con_collapse, sep_solve)
  apply (drule sep_con_impl2)
   apply (drule sept_impl2)
    apply (drule sep_con_impl2)
     apply (drule sept_impl2)
      apply (sep_drule maps_to_ex_nf[where p=p'])
      apply (sep_select_asm 2, assumption)
     apply (drule sept_success, assumption+)
  apply (clarsimp simp: pred_conj_def sep_con_def sept_def)
  done

lemma sep_crashable: "\<exists>s. (nf -& nf) s \<and> \<not>nf s"
  apply (rule_tac x="(undefined,False)" in exI)
  apply (clarsimp simp: sept_def)
  apply (rule_tac x="[p \<mapsto> v]" in exI)
  apply (rule_tac x=True in exI)
  apply (clarsimp)
  apply (rule_tac x=0 in exI)
  apply (rule_tac x= True in exI)
  apply (clarsimp)
  apply (clarsimp simp: sep_disj_prod_def sep_disj_bool_def)
  done

end
