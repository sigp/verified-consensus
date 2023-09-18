section \<open>Atomic commands with three sync operators: parallel, weak conjunction, supremum\<close>

theory Atomic_Commands
imports
  "../General/CRA"
  "Abstract_Atomic_Sync"

begin

(*
notation  iter ("_\<^sup>\<omega>" [103] 102)
notation  fiter ("_\<^sup>\<star>" [101] 100)
notation  infiter ("_\<^sup>\<infinity>" [105] 106)
notation  seq_power (infixr "\<^sup>;^" 80)
*)

(*==========================================*)
text \<open>some simple locales to introduce locale names and some extra syntax\<close>

locale par_atomid = par +
  fixes atomid :: "'a::refinement_lattice"           ("\<E>") 

(*==========================================*)
text \<open>Atomic commands with the parallel operator  (as instance of sync operator)\<close>

locale par_atomic = seq + nil + abstract_atomic_commands + par_atomid +
                   par:atomic_sync_id_commands par seq nil atomic atomid 
      + assumes par_identity: "c \<parallel> atomid\<^sup>\<omega> = c"
begin
  
definition skip:: "'d::refinement_lattice"
  where "skip \<equiv> \<E>\<^sup>\<omega>"

sublocale parallel par skip
  by (unfold_locales; simp add: skip_def par_identity)
 
end   

(*==========================================*)
text \<open>Atomic commands with the conjunction operator (as instance of sync operator)\<close>

locale conj_atomic = seq + nil + abstract_atomic_commands + conj + 
            conj: atomic_sync_id_commands conj seq nil atomic Atomic +  
            assumes conj_idem: "\<And>c. c \<iinter> c = c"
            assumes conj_id: "\<And>c. c \<iinter> Atomic\<^sup>\<omega> = c"

begin

definition chaos :: "'d ::refinement_lattice"
  where "chaos \<equiv> Atomic\<^sup>\<omega>"

sublocale conjunction conj chaos
  by(unfold_locales; simp add: conj_idem chaos_def conj_id)

end

(*==========================================*)
text \<open>Atomic commands with the infimum operator (as instance of sync operator)\<close>

locale inf_atomic = seq + nil + abstract_atomic_commands +
            inf: atomic_sync_id_commands inf seq nil atomic Atomic  
begin
end

(*===================================================*)
text \<open>Atomic commands with parallel conjunction and supremum and sequential composition\<close>

locale atomic_commands = iteration + par_atomic + conj_atomic + inf_atomic + 
  assumes seq_conj_interchange: "(c\<^sub>0;c\<^sub>1) \<iinter> (d\<^sub>0;d\<^sub>1) \<ge> (c\<^sub>0 \<iinter> d\<^sub>0);(c\<^sub>1 \<iinter> d\<^sub>1)"
  assumes par_conj_interchange: "(c\<^sub>0 \<parallel> c\<^sub>1) \<iinter> (d\<^sub>0 \<parallel> d\<^sub>1) \<ge> (c\<^sub>0 \<iinter> d\<^sub>0) \<parallel> (c\<^sub>1 \<iinter> d\<^sub>1)"
  assumes seq_par_interchange: "(c0;d0) \<parallel> (c1;d1) \<ge> (c0 \<parallel> c1);(d0 \<parallel> d1)"
begin

lemma skip_ref_nil:
  shows "skip \<ge> nil"
  unfolding skip_def by (simp add: iter0)

sublocale cra seq nil par skip conj chaos
proof (unfold_locales)
  show "nil \<parallel> nil \<ge> nil"
    by (simp add: par.nil_sync_nil)
next
  show "skip \<ge> nil"
    by (simp add: skip_def iter0)
next
  show "skip \<ge> skip; skip"    
    using skip_def by auto
next 
  fix c0 d0 c1 d1
  show "c0 ; d0 \<parallel> c1 ; d1 \<ge> (c0 \<parallel> c1) ; (d0 \<parallel> d1)"
    using seq_par_interchange by simp
next
  show "\<bottom> \<ge> chaos \<parallel> \<bottom>"
    by (metis chaos_def sup.absorb_iff2 sup_bot.right_neutral par.atomic_infiter_sync_nil
          par.atomic_iter_sync_nil par.comm.left_commute Atomic_def)
next
  obtain a where a1: "a = Atomic \<parallel> Atomic \<and> Atomic \<ge> a"
    by (metis par.atomic_sync Atomic_def atomic.Hom_ref_hom)
  then have "chaos \<parallel> chaos = a\<^sup>\<omega>" 
    unfolding chaos_def Atomic_def using par.atomic_iter_sync_iter by metis
  moreover have "chaos \<ge> a\<^sup>\<omega>" 
    unfolding chaos_def using iter_mono a1 by metis 
  ultimately show "chaos \<ge> chaos \<parallel> chaos"
    by simp
next
  fix c\<^sub>0 c\<^sub>1 d\<^sub>0 d\<^sub>1
  show "(c\<^sub>0 \<parallel> c\<^sub>1) \<iinter> (d\<^sub>0 \<parallel> d\<^sub>1) \<ge> c\<^sub>0 \<iinter> d\<^sub>0 \<parallel> c\<^sub>1 \<iinter> d\<^sub>1"
    using par_conj_interchange by simp
next
  show "chaos \<ge> chaos ; chaos"
    unfolding chaos_def by simp
next
  fix c\<^sub>0 c\<^sub>1 d\<^sub>0 d\<^sub>1
  show "c\<^sub>0 ; c\<^sub>1 \<iinter> d\<^sub>0 ; d\<^sub>1 \<ge> (c\<^sub>0 \<iinter> d\<^sub>0) ; (c\<^sub>1 \<iinter> d\<^sub>1)"
    using seq_conj_interchange by simp
qed

lemma Atomic_nonaborting: "chaos \<ge> Atomic" by (simp add: chaos_def iter1)

lemma atomic_conj_inf: "atomic p \<iinter> atomic q = atomic p \<sqinter> atomic q"
  by (metis atomic.hom_inf atomic.hom_iso conj.atomic_sync 
      conj.atomic_sync_identity conj.sync_mono_left conj_to_inf eq_iff 
      inf.bounded_iff local.conj_commute atomic.Hom_ref_hom)

lemma atomic_seq_abort_conj_left: "(atomic p;\<top> \<iinter> atomic q) = (atomic p \<iinter> atomic q);\<top>"
  by (metis antisym conj.right_idem conj_abort_right conj.atomic_pre_sync_atomic_pre 
       conj_seq_abort_right local.conj_commute seq_abort_conj seq_abort_right) 

lemma atomic_seq_abort_conj_right: "(atomic p \<iinter> atomic q;\<top>) = (atomic p \<iinter> atomic q);\<top>"
  by (metis antisym conj.right_idem conj_abort_right conj.atomic_pre_sync_atomic_pre 
       conj_seq_abort_right local.conj_commute seq_abort_conj seq_abort_right) 

lemma atomic_seq_abort: "atomic p;\<top> = atomic p \<iinter> atomic p;\<top>"
  using conj.sync_commute conj_seq_abort_right by auto 

lemma atomic_abort_absorb: 
  assumes "p \<le> q" 
  shows "atomic p \<squnion> atomic q ; \<top> = atomic q ; \<top>"
proof -
  have "atomic q \<ge> atomic p"
    by (simp add: assms atomic.hom_mono)
  then show ?thesis
    by (meson sup_absorb2 order.trans seq_abort_right) 
qed 

lemma atomic_seq_bot_conj_inf_distrib:
  assumes "a0 = atomic p0" and "a1 = atomic p1" and "a2 = atomic p2" and "a3 = atomic p3"
  shows "(a0; \<top> \<iinter> a1) \<squnion> (a3 \<iinter> a2;\<top>) \<squnion> (a0; \<top> \<iinter> a2;\<top>)
       = ((a0 \<iinter> a1) \<squnion> (a3 \<iinter> a2) \<squnion> (a0 \<iinter> a2));\<top>"
    by (simp add: assms(1) assms(2) assms(3) assms(4) atomic_seq_abort_conj_left 
         atomic_seq_abort_conj_right conj.atomic_pre_sync_atomic_pre nondet_seq_distrib) 

lemma atomid_sup_compl: "\<E> \<sqinter> atomic.negate(\<E>) = \<bottom>"
  by (metis atomic.hom_compl_sup inf_commute par.syncid_atomic) 

(*
lemma atomic_inf_conj_distrib_seq:
  assumes a_atomic[simp]: "a = (atomic p)"
  shows "a\<^sup>\<omega> \<iinter> c;d = (a\<^sup>\<omega> \<iinter> c); (a\<^sup>\<omega> \<iinter> d)" sorry
(* proof using the canonical representation *)
*)


end
end
