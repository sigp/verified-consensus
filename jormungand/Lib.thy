(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*
   Miscellaneous library definitions and lemmas.
*)

chapter "Library"

theory Lib
imports
  Eisbach_Methods
begin

definition
  pred_conj :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" (infixl "and" 35)
where
  "pred_conj P Q \<equiv> \<lambda>x. P x \<and> Q x"

definition
  pred_disj :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" (infixl "or" 30)
where
  "pred_disj P Q \<equiv> \<lambda>x. P x \<or> Q x"

definition
  pred_neg :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" ("not _" [40] 40)
where
  "pred_neg P \<equiv> \<lambda>x. \<not> P x"

definition "K \<equiv> \<lambda>x y. x"

end
