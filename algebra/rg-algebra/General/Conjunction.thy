section \<open>Weak conjunction operator \label{S:conjunction}\<close>

theory Conjunction
imports Refinement_Lattice Abstract_Sync
begin

text \<open>
  The weak conjunction operator is similar to
  greatest lower bound @{term "c \<sqinter> d"}  but it is abort strict.
\<close>

locale chaos =
  fixes chaos :: "'a"    ("chaos") 
(*
The weak conjunction operator uses a special symbol: double intersection.
To see this symbol in your Isabelle PIDE, install DejaVu Sans fonts
(available freely online at http://dejavu-fonts.org/wiki/Download)
and add the following line to ~/.isabelle/Isabelle2015/etc/symbols
(create the file if it does not exist):

\<iinter>               code: 0x0022d2  group: operator  font: DejaVuSans

Note: if the symbol is rendering correctly, you do not need to do anything.
*)
locale conj =
  fixes conj :: "'a :: top \<Rightarrow> 'a \<Rightarrow> 'a"   (infixl "\<iinter>" 80)
  assumes conj_abort_right: "c \<iinter> \<top> = \<top>"
begin
text \<open>Abort is an annihilator: @{term "c \<iinter> \<top> = \<top>"}.\<close>
end

locale conjunction = conj + chaos + conj: semilattice_neutr conj chaos

begin
text \<open>
  Weak conjunction is associative, commutative and idempotent
  and has identity the command @{term "chaos"} that allows any non-aborting behaviour,
  i.e.\ it forms a semi-lattice.
\<close>

lemmas [algebra_simps, field_simps] =
  conj.assoc
  conj.commute
  conj.left_commute

lemmas conj_assoc = conj.assoc             (* 42 *)
lemmas conj_commute = conj.commute         (* 43 *)
lemmas conj_idem = conj.idem               (* 44 *)
lemmas conj_chaos = conj.right_neutral     (* 45 *)            
lemmas conj_chaos_left = conj.left_neutral (* 45 + 43 *)

lemma conj_abort_left [simp]: "\<top> \<iinter> c = \<top>"
using conj_abort_right local.conj_commute by fastforce

lemma conj_not_abort: "a \<iinter> b \<noteq> \<top> \<Longrightarrow> a \<noteq> \<top> \<and> b \<noteq> \<top>"
  using conj_abort_right by auto

lemma conj_conj_distrib_left: "c \<iinter> (d\<^sub>0 \<iinter> d\<^sub>1) = (c \<iinter> d\<^sub>0) \<iinter> (c \<iinter> d\<^sub>1)"
  by (metis conj_assoc conj_commute conj_idem)

end



subsection \<open>Distributed weak conjunction\<close>

text \<open>
  The weak conjunction operator distributes across 
  arbitrary non-empty non-deterministic choice.
\<close>

locale conj_distrib = conjunction + abstract_sync conj
begin

lemma conj_refine: "c\<^sub>0 \<ge> d \<Longrightarrow> c\<^sub>1 \<ge> d \<Longrightarrow> c\<^sub>0 \<iinter> c\<^sub>1 \<ge> d" (* law 'refine-conjunction' *)
  by (metis conj_idem sync_mono)

lemma conj_introduce: "c \<ge> d\<^sub>0 \<Longrightarrow> c \<ge> d\<^sub>1 \<Longrightarrow> c \<ge> d\<^sub>0 \<iinter> d\<^sub>1"
  by (metis conj_idem sync_mono)

lemma conj_conjoin_non_aborting: "chaos \<ge> c \<Longrightarrow> d \<ge> d \<iinter> c"
  using sync_mono by force

lemma conj_to_inf: "c \<iinter> d \<ge> c \<sqinter> d"
  by (simp add: conj_refine)

lemma conj_to_inf_nonaborting: 
  assumes "chaos \<ge> c" and "chaos \<ge> d"
  shows "c \<iinter> d = c \<sqinter> d"
proof (rule antisym)
  show "c \<sqinter> d \<ge> c \<iinter> d" using assms(1) assms(2) conj_conjoin_non_aborting local.conj_commute by fastforce 
next
  show "c \<iinter> d \<ge> c \<sqinter> d" by (metis conj_to_inf)
qed

lemma conj_magic_nonaborting: "chaos \<ge> c \<Longrightarrow> c \<iinter> \<bottom> = \<bottom>"
by (simp add: conj_to_inf_nonaborting)

lemma conj_Nondet_distrib_nonaborting:
  assumes nonaborting: "chaos \<ge> c"
  shows "c \<iinter> (\<Squnion> D) = (\<Squnion>d\<in>D. c \<iinter> d)"
proof (cases "D = {}")
  case True
  then show ?thesis using nonaborting conj_magic_nonaborting by simp
next
  case False
  then show ?thesis using sync_Nondet_distrib by simp
qed

lemma Nondet_conj_distrib_nonaborting:
  assumes nonaborting: "chaos \<ge> c"
  shows "(\<Squnion> D) \<iinter> c = (\<Squnion>d\<in>D. d \<iinter> c)"
  using conj_Nondet_distrib_nonaborting nonaborting conj_commute nondet_mono_left by auto

end
end
