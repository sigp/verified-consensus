chapter "Deterministic State Monad with Failure"

theory Det_Monad
imports
  "~~/src/HOL/Library/Monad_Syntax"
  "~~/src/HOL/Library/While_Combinator"
  "../Monad_WP/wp/WP"
  SP
begin


section "Basic Monad Definitions"

type_synonym ('s,'a) det_monad = "'s \<Rightarrow> 'a \<times> 's \<times> bool"

definition
  bind :: "('s,'a) det_monad \<Rightarrow> ('a \<Rightarrow> ('s,'b) det_monad) \<Rightarrow> ('s,'b) det_monad"
where
  "bind f g \<equiv> \<lambda>s. let (r', s', f') = f s;
                       (r'', s'', f'') = g r' s'
                   in (r'', s'', f' \<or> f'')"

definition
  "return x \<equiv> \<lambda>s. (x, s, False)"

(* use do-notation for this state monad *)
adhoc_overloading
  Monad_Syntax.bind bind

(* always print do-notation *)
translations
  "CONST bind_do" == "CONST Monad_Syntax.bind"


section "State Monad Definitions"

definition
  "get \<equiv> \<lambda>s. (s, s, False)"

definition
  "put s \<equiv> \<lambda>s'. ((), s, False)"

definition
  "fail \<equiv> \<lambda>s. ((), s, True)"


section "Derived Monad Definitions"

definition
  "modify f \<equiv> get >>= (\<lambda>x. put (f x))"

definition
  "gets f \<equiv> get >>= (\<lambda>x. return (f x))"

definition
  "assert P \<equiv> if P then return () else fail"

definition
  "state_assert P \<equiv> do { s \<leftarrow> get; assert (P s) }"

definition
  while_body :: "('a \<Rightarrow> ('s, 'a) det_monad) \<Rightarrow> 'a \<times> 's \<times> bool \<Rightarrow> 'a \<times> 's \<times> bool"
where
  "while_body b \<equiv> \<lambda>(rv,s,f). let (rv',s',f') = b rv s in (rv',s',f \<or> f')"

definition
  "whileLoop_opt g b \<equiv> while_option (g o fst) (while_body b)"

definition
  whileLoop :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> ('s, 'a) det_monad) \<Rightarrow> 'a \<Rightarrow> ('s,'a) det_monad"
where
  "whileLoop g b \<equiv> \<lambda>x s. case whileLoop_opt g b (x, s, False) of
                            Some r \<Rightarrow> r
                          | None \<Rightarrow> (undefined, undefined, True)"

notation (output)
  whileLoop  ("(whileLoop (_)//  (_))" [1000, 1000] 1000)

lemma while_body_aux:
  "(while_body b ^^ k) (x, s, f) =
      (fst ((while_body b ^^ k) (x, s, f')),
       fst (snd ((while_body b ^^ k) (x, s, f'))),
       if \<not>f'
       then f \<or> snd (snd ((while_body b ^^ k) (x, s, f')))
       else snd (snd ((while_body b ^^ k) (x, s, f)))
      )"
proof (induct k)
  case 0 thus ?case by clarsimp
next
  case (Suc n)
  show ?case
    apply (clarsimp split del: if_split)
    apply (subst Suc.hyps)
    apply (clarsimp simp: while_body_def split: prod.splits)
    using Suc.hyps
    apply (clarsimp simp: while_body_def split: prod.splits)
    done
qed

lemma least_while_body_guard:
  "(LEAST k. \<not> g (fst ((while_body b ^^ k) (x, s, f)))) =
   (LEAST k. \<not> g (fst ((while_body b ^^ k) (x, s, f'))))"
  by (subst while_body_aux) simp

lemma whileLoop_opt_Some:
  "whileLoop_opt g b (x, s, f) = Some (x', s', f')
  \<Longrightarrow> whileLoop_opt g b (x, s, f'') = Some (x', s', if \<not>f then f'' \<or> f' else
      snd (snd (the (whileLoop_opt g b (x, s, f'')))))"
  unfolding whileLoop_opt_def Let_def
  apply (clarsimp simp: while_option_def split: if_split_asm)
  apply (rule conjI)
   apply clarsimp
   apply (rule conjI)
    apply clarsimp
    apply (subst least_while_body_guard[where f'=f])
    apply (subst while_body_aux[where f=f'' and f'=f])
    apply simp
   apply (rule exI)
   apply (subst while_body_aux)
   apply simp
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (subst least_while_body_guard[where f'=f])
   apply (subst while_body_aux[where f=f'' and f'=f])
   apply simp
   apply (subst least_while_body_guard[where f=True and f'=f''])
   apply simp
  apply (rule exI)
  apply (subst while_body_aux)
  apply simp
  done

lemma while_body_apply[simp]:
  "while_body b (r, s, f) = (fst (b r s), fst (snd (b r s)), f \<or> snd (snd (b r s)))"
  by (simp add: while_body_def split: prod.splits)

lemma whileLoop_unfold:
  "whileLoop g b x = (if g x then b x >>= whileLoop g b else return x)"
  unfolding whileLoop_def whileLoop_opt_def
  apply (rule ext)
  apply (rename_tac s)
  apply (subst while_option_unfold)
  apply (clarsimp simp: whileLoop_opt_def[symmetric] return_def bind_def split: prod.splits)
  apply (clarsimp split: option.splits)
   apply (drule whileLoop_opt_Some[where f''=False])
   apply clarsimp
  apply (drule_tac f''="snd (snd (b x s))" in whileLoop_opt_Some)
  apply clarsimp
  done



section "Hoare-Logic Validity"

text {* Partial correctness *}
definition
  valid :: "('s \<Rightarrow> bool) \<Rightarrow> ('s,'a) det_monad \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
  ("\<lbrace>_\<rbrace>/ _ /\<lbrace>_\<rbrace>")
where
  "\<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace> \<equiv> \<forall>s. P s \<longrightarrow> (let (r',s',f') = m s in \<not>f' \<longrightarrow> Q r' s')"

text {* Total correctness *}
definition
  validNF :: "('s \<Rightarrow> bool) \<Rightarrow> ('s,'a) det_monad \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
  ("\<lbrace>_\<rbrace>/ _ /\<lbrace>_\<rbrace>!")
where
  "\<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>! \<equiv> \<forall>s. P s \<longrightarrow> (let (r',s',f') = m s in Q r' s' \<and> \<not>f')"

text {* Unified correctness *}
definition
  validU :: "(('s \<times> bool)  \<Rightarrow> bool) \<Rightarrow> ('s,'a) det_monad \<Rightarrow> ('a \<Rightarrow> ('s \<times> bool) \<Rightarrow> bool) \<Rightarrow> bool"
  ("\<lbrace>_\<rbrace>/ _ /\<lbrace>_\<rbrace>u")
where
  "\<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>u \<equiv> \<forall>s f. P (s,f) \<longrightarrow> (let (r',s',f') = m s in Q r' (s',f \<and> \<not>f'))"


section "Hoare-Logic Rules"

text \<open>Rule collections for weakest preconditions\<close>
named_theorems wp'
named_theorems wp_pre'

text \<open>Rule collections for strongest postconditions\<close>
named_theorems sp
named_theorems sp_pre

text {* Strongest postcondition method setup *}
method sp declares sp = ((((rule sp)+), (rule sp_pre, rule sp, assumption?)?)  |
                        (rule sp_pre, rule sp, assumption?))

lemma bind_wp[wp']:
  "(\<And>x. \<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace>) \<Longrightarrow> \<lbrace>A\<rbrace> f \<lbrace>B\<rbrace> \<Longrightarrow> \<lbrace>A\<rbrace> f >>= g \<lbrace>C\<rbrace>"
  unfolding valid_def Let_def bind_def by (fastforce split: prod.splits)

lemma hoare_seq_ext[sp]:
  "\<lbrace>A\<rbrace> f \<lbrace>B \<rbrace> \<Longrightarrow> (\<And>x.\<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace>) \<Longrightarrow> \<lbrace>A\<rbrace> f >>= g \<lbrace>C\<rbrace>"
  by (rule bind_wp)

lemma hoare_chain:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<And>s. R s \<Longrightarrow> P s; \<And>r s. Q r s \<Longrightarrow> S r s \<rbrakk> \<Longrightarrow> \<lbrace>R\<rbrace> f \<lbrace>S\<rbrace>"
  by (fastforce simp: valid_def)

lemma hoare_pre[wp_pre']:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<And>s. R s \<Longrightarrow> P s \<rbrakk> \<Longrightarrow> \<lbrace>R\<rbrace> f \<lbrace>Q\<rbrace>"
  by (rule hoare_chain) blast

lemmas hoare_weaken_pre = hoare_pre

lemma hoare_post[sp_pre]:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>; \<And>rv s. R rv s \<Longrightarrow> Q rv s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  by (rule hoare_chain) blast

lemmas hoare_strengthen_post = hoare_post

lemma get_wp[wp']: "\<lbrace>\<lambda>s. P s s\<rbrace> get \<lbrace>P\<rbrace>"
  by (clarsimp simp: get_def valid_def)

lemma put_wp[wp']: "\<lbrace>\<lambda>s'. P () s\<rbrace> put s \<lbrace>P\<rbrace>"
  by (clarsimp simp: put_def valid_def)

lemma fail_wp[wp']: "\<lbrace>\<lambda>s. True\<rbrace> fail \<lbrace>P\<rbrace>"
  by (simp add: fail_def valid_def)

lemma return_wp[wp']: "\<lbrace>P x\<rbrace> return x \<lbrace>P\<rbrace>"
  by (simp add: valid_def return_def)

lemma if_wp[wp']:
  "\<lbrakk> Q \<Longrightarrow> \<lbrace>A\<rbrace> f \<lbrace>P\<rbrace>; \<not>Q \<Longrightarrow> \<lbrace>B\<rbrace> g \<lbrace>P\<rbrace>\<rbrakk> \<Longrightarrow>
  \<lbrace>\<lambda>s. (Q \<longrightarrow> A s) \<and> (\<not>Q \<longrightarrow> B s)\<rbrace> if Q then f else g \<lbrace>P\<rbrace>"
  by auto

lemma prod_wp[wp']:
  "(\<And>a b. x = (a,b) \<Longrightarrow> \<lbrace>P a b\<rbrace> f a b \<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>P (fst x) (snd x)\<rbrace> case x of (a, b) \<Rightarrow> f a b \<lbrace>Q\<rbrace>"
  by (cases x) simp

lemma prod_sp[sp]:
  "(\<And>a b. x = (a,b) \<Longrightarrow> \<lbrace>P\<rbrace> f a b \<lbrace>Q a b\<rbrace>) \<Longrightarrow> \<lbrace>P\<rbrace> case x of (a, b) \<Rightarrow> f a b \<lbrace>Q (fst x) (snd x)\<rbrace>"
  by (cases x) simp

text {* Weakest precondition method setup *}
method wp uses wp = (rule wp_pre', WP.wp wp wp', assumption?)


(* partial correctness assumes asserts *)
lemma assert_wp[wp']:
  "\<lbrace>\<lambda>s. Q \<longrightarrow> P () s\<rbrace> assert Q \<lbrace>P\<rbrace>"
  unfolding assert_def by wp auto

lemma state_assert_wp[wp']:
  "\<lbrace>\<lambda>s. Q s \<longrightarrow> P () s\<rbrace> state_assert Q \<lbrace>P\<rbrace>"
  unfolding state_assert_def by wp

lemma modify_wp[wp']:
  "\<lbrace>\<lambda>s. P () (f s)\<rbrace> modify f \<lbrace>P\<rbrace>"
  unfolding modify_def by wp

lemma gets_wp[wp']:
  "\<lbrace>\<lambda>s. P (f s) s\<rbrace> gets f \<lbrace>P\<rbrace>"
  unfolding gets_def by wp

lemma whileLoop_wp:
  "\<lbrakk> \<And>r. \<lbrace> \<lambda>s. I r s \<and> g r \<rbrace> b r \<lbrace> I \<rbrace>;
     \<And>r s. \<lbrakk> I r s; \<not> g r \<rbrakk> \<Longrightarrow> Q r s \<rbrakk> \<Longrightarrow>
  \<lbrace> I r \<rbrace> whileLoop g b r \<lbrace> Q \<rbrace>"
  unfolding whileLoop_def whileLoop_opt_def valid_def
  apply (clarsimp split: option.splits)
  apply (frule while_option_stop)
  apply (drule while_option_rule[where P="\<lambda>(r,s,f). \<not>f \<longrightarrow> I r s", rotated])
    apply simp
   apply (clarsimp simp: while_body_def split: prod.splits)
   apply (drule meta_spec)
   apply (erule allE)
   apply (erule impE, simp)
   apply simp
  apply simp
  done

definition
  whileLoop_inv :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> ('s,'a) det_monad) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> ('s,'a) det_monad"
where
  "whileLoop_inv g b I \<equiv> whileLoop g b"

lemma whileLoop_add_inv: "whileLoop g b = whileLoop_inv g b I"
  by (clarsimp simp: whileLoop_inv_def)

lemma whileLoop_inv_wp[wp']:
  "\<lbrakk> \<And>r. \<lbrace> \<lambda>s. I r s \<and> g r \<rbrace> b r \<lbrace> I \<rbrace>;
     \<And>r s. \<lbrakk> I r s; \<not> g r \<rbrakk> \<Longrightarrow> Q r s \<rbrakk> \<Longrightarrow>
  \<lbrace> I r \<rbrace> whileLoop_inv g b I r \<lbrace> Q \<rbrace>"
  unfolding whileLoop_inv_def by (rule whileLoop_wp)

lemma return_sp[sp]:
  "\<lbrace>P\<rbrace> return x \<lbrace>\<lambda>rv s. rv = x \<and> P s\<rbrace>"
  by wp simp

lemma put_sp[sp]:
  "\<lbrace>R\<rbrace> put a \<lbrace>\<lambda>_ s. s = a \<rbrace>"
  by(simp add:put_def valid_def)

lemma put_sp'[sp]:
  "\<lbrace>\<lambda>_. R\<rbrace> put a \<lbrace>\<lambda>_ s. s = a \<and> R\<rbrace>"
  by(simp add:put_def valid_def)

lemma get_sp[sp]:
  "\<lbrace>P\<rbrace> get \<lbrace>\<lambda>a s. s = a \<and> P s\<rbrace>"
  by(simp add:get_def valid_def)

lemma assert_sp[sp]:
  "\<lbrace> P \<rbrace> assert Q \<lbrace> \<lambda>r s. P s \<and> Q \<rbrace>"
  by (simp add: assert_def fail_def return_def valid_def)

lemma hoare_gets_sp[sp]:
  "\<lbrace>P\<rbrace> gets f \<lbrace>\<lambda>rv s. rv = f s \<and> P s\<rbrace>"
  apply (simp add: gets_def, sp, clarsimp)
done

section "Total Correctness Rules"

lemma bind_wp_nf:
  "\<lbrace>A\<rbrace> f \<lbrace>B\<rbrace>! \<Longrightarrow> (\<And>x. \<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace>!) \<Longrightarrow> \<lbrace>A\<rbrace> f >>= g \<lbrace>C\<rbrace>!"
    unfolding validNF_def Let_def bind_def by fastforce


section "Unified Correctness Rules"

lemma hoare_seq_extU[sp]:
  "\<lbrace>A\<rbrace> f \<lbrace>B \<rbrace>u \<Longrightarrow> (\<And>x.\<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace>u)  \<Longrightarrow> \<lbrace>A\<rbrace> f >>= g \<lbrace>C\<rbrace>u"
  unfolding validU_def Let_def bind_def by fastforce

lemma hoare_chainU:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>u;
    \<And>s. R s \<Longrightarrow> P s;
    \<And>r s. Q r s \<Longrightarrow> S r s \<rbrakk> \<Longrightarrow>
   \<lbrace>R\<rbrace> f \<lbrace>S\<rbrace>u"
  by (fastforce simp: validU_def)

lemma hoare_preU[wp_pre']:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>u;
    \<And>s. R s \<Longrightarrow> P s \<rbrakk> \<Longrightarrow>
   \<lbrace>R\<rbrace> f \<lbrace>Q\<rbrace>u"
  by (fastforce simp: validU_def)

lemma hoare_postU[sp_pre]:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>u;
    \<And>rv s. R rv s \<Longrightarrow> Q rv s \<rbrakk> \<Longrightarrow>
   \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>u"
  by (fastforce simp: validU_def)

lemma bind_wpU[wp']:
  "(\<And>x.\<lbrace>B x\<rbrace> g x \<lbrace>C\<rbrace>u) \<Longrightarrow> \<lbrace>A\<rbrace> f \<lbrace>B \<rbrace>u \<Longrightarrow> \<lbrace>A\<rbrace> f >>= g \<lbrace>C\<rbrace>u"
  by (rule hoare_seq_extU)


lemma get_wpU[wp']: "\<lbrace>\<lambda>s. P (fst s) s \<rbrace> get \<lbrace> P \<rbrace>u"
  by (clarsimp simp: get_def validU_def)

lemma put_wpU[wp']: "\<lbrace>\<lambda>s'. P () (s, snd s') \<rbrace> put s \<lbrace> P \<rbrace>u"
  by (clarsimp simp: put_def validU_def)

lemma fail_wpU[wp']: "\<lbrace>\<lambda>s. P () (fst s, False) \<rbrace> fail \<lbrace> P \<rbrace>u"
  by (simp add: fail_def validU_def)

lemma return_wpU[wp']: "\<lbrace>P x\<rbrace> return x \<lbrace>P\<rbrace>u"
  by (simp add: validU_def return_def)

lemma if_wpU[wp']:
  "\<lbrakk> Q \<Longrightarrow> \<lbrace>A\<rbrace> f \<lbrace>P\<rbrace>u; \<not>Q \<Longrightarrow> \<lbrace>B\<rbrace> g \<lbrace>P\<rbrace>u\<rbrakk> \<Longrightarrow>
  \<lbrace>\<lambda>s. (Q \<longrightarrow> A s) \<and> (\<not>Q \<longrightarrow> B s)\<rbrace> if Q then f else g \<lbrace>P\<rbrace>u"
  by auto

lemma assert_wpU[wp']:
  "\<lbrace>\<lambda>s. P () (fst s, Q \<and> snd s) \<rbrace> assert Q \<lbrace> P \<rbrace>u"
  unfolding assert_def by wp auto

lemma state_assert_wpU[wp']:
  "\<lbrace>\<lambda>s.  P () (fst s, Q (fst s) \<and> snd s) \<rbrace> state_assert Q \<lbrace> P \<rbrace>u"
  unfolding state_assert_def by wp

lemma modify_wpU[wp']:
  "\<lbrace>\<lambda>s. P ()  (f (fst s), snd s)\<rbrace> modify f \<lbrace>P\<rbrace>u"
  unfolding modify_def by wp

lemma gets_wpU[wp']: "\<lbrace>\<lambda>s.  P (f (fst s)) s \<rbrace> gets f \<lbrace> P \<rbrace>u"
  unfolding gets_def by wp



end