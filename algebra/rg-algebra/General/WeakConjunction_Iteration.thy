section \<open>Iteration for distributive models \label{S:conjunctive-iteration}\<close>

theory WeakConjunction_Iteration
imports
  Distributive_Iteration
  CRA
begin

locale conj_iteration = cra + iteration_infinite_distrib

begin

lemma conj_distrib4: "c\<^sup>\<star> \<iinter> d\<^sup>\<star> \<ge> (c \<iinter> d)\<^sup>\<star>"
proof -
  have "c\<^sup>\<star> \<iinter> d\<^sup>\<star> = (nil \<squnion> (c;c\<^sup>\<star>)) \<iinter> d\<^sup>\<star>" by (metis fiter_unfold) 
  then have "c\<^sup>\<star> \<iinter> d\<^sup>\<star> = (nil \<iinter> d\<^sup>\<star>) \<squnion> ((c;c\<^sup>\<star>) \<iinter> d\<^sup>\<star>)" by (simp add: nondet_sync_distrib) 
  then have "c\<^sup>\<star> \<iinter> d\<^sup>\<star> \<ge> nil \<squnion> ((c;c\<^sup>\<star>) \<iinter> (d;d\<^sup>\<star>))"
    by (metis conj_refine fiter0 fiter_unfold le_sup_iff sup.cobounded2 sync_mono)
  then have "c\<^sup>\<star> \<iinter> d\<^sup>\<star> \<ge> nil \<squnion> ((c \<iinter> d);(c\<^sup>\<star> \<iinter> d\<^sup>\<star>))" 
    by (meson nondet_mono_right order.trans seq_conj_interchange) 
  thus ?thesis by (metis seq_nil_right fiter_induct) 
qed

end
end
