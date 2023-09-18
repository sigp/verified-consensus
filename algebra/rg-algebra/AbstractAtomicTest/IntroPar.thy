section \<open>Parallel introduction\<close>

theory IntroPar
imports
  "Specification"
  "Relies_Guarantees"
begin

locale intro_par = strong_spec + relies_guarantees
begin

lemma Pgm_par_pgm: "Pgm \<parallel> \<pi>(r) = \<bottom>" 
  by (metis Pgm_def pgm_com_par_pgm_com seq_nil_right) 

lemma Pgm_par_Env: "Pgm \<parallel> \<E> = Pgm" 
  using Pgm_def Env_def env_com_par_pgm_com
  by (metis par.atomic_sync_identity par.sync_commute pgm_atomic)

lemma env_par_pgm2: "\<epsilon>(r) \<parallel> \<pi>(r) = \<pi>(r)" using env_com_par_pgm_com seq_nil_right
  by (simp add: env_par_pgm_axiom local.flip_def2)
 
lemma env_par_Env: "\<epsilon>(r) \<parallel> \<E> = \<epsilon>(r)" 
  by (metis env_atomic par.atomic_sync_identity par.sync_commute) 


(*-------------------------------------------------------------------*)
(* some helper lemmas to spec_introduce_par:                      *)

lemma rely_ref_rely_par_guar: "(rely r) \<ge> (rely r) \<parallel> (guar r)"
proof -
  have h1: "(Pgm \<squnion> \<epsilon>(r))\<parallel> (\<pi>(r) \<squnion> \<E>) = (Pgm \<squnion> \<epsilon>(r))"
    by (metis atomic_negate_env env_par_Env env_par_pgm2 Env_def env_negate_def2 
         sup.orderE par.nondet_sync_product Pgm_inverse_Env Pgm_par_Env Pgm_par_pgm 
         Pgm_Env_disjoint pgm.Hom_ref_hom) 
  have h2: "\<epsilon>(-r) \<parallel> (\<pi>(r) \<squnion> \<E>) = \<epsilon>(-r)"
    using abstract_hom_commands.hom_compl_sup env_par_Env env_par_pgm_axiom flip_def2  
      par.sync_nondet_distrib pgm.abstract_hom_commands_axioms by fastforce 

  have a1: "rely r \<ge> (rely r) \<parallel> (guar r) \<longleftrightarrow>  (env_assump r)\<^sup>\<omega> \<ge> (rely r) \<parallel> (guar r)" by simp
  have a2: "nil \<squnion> (env_assump r);((rely r) \<parallel> (guar r)) \<ge> (rely r) \<parallel> (guar r)"
  proof -
    have b1: "(rely r) \<parallel> (guar r) = (env_assump r)\<^sup>\<omega> \<parallel> (pgm_restrict r)\<^sup>\<omega>" by simp
    then have b2: "... = (nil \<squnion> (env_assump r);(env_assump r)\<^sup>\<omega>) \<parallel> 
                      (nil \<squnion> (pgm_restrict r);(pgm_restrict r)\<^sup>\<omega>)" using iter_unfold by auto
    then have b3: "... = nil\<parallel>nil \<squnion> nil\<parallel>(pgm_restrict r);(pgm_restrict r)\<^sup>\<omega> \<squnion>
                         (env_assump r);(env_assump r)\<^sup>\<omega>\<parallel>nil \<squnion>
                         ((env_assump r);(env_assump r)\<^sup>\<omega> \<parallel> (pgm_restrict r);(pgm_restrict r)\<^sup>\<omega>)"
       using par.nondet_sync_product by blast
    then have b4: "... = nil \<squnion>
                       ((env_assump r);(env_assump r)\<^sup>\<omega> \<parallel> (pgm_restrict r);(pgm_restrict r)\<^sup>\<omega>)"
       by (metis sup_bot_right par.nil_sync_nil par.nil_sync_atomic_pre pgm_restrict_atomic 
                 env_assump_par_nil)
    then have b5: "... = nil \<squnion> 
                 ((atomic.negate(\<epsilon>(-r)) \<squnion> \<epsilon>(-r);\<top>);(env_assump r)\<^sup>\<omega> \<parallel> (\<pi>(r) \<squnion> \<E>);(pgm_restrict r)\<^sup>\<omega>)"
      using env_assump_def4 by simp
    then have b6: "... = nil \<squnion> 
                 ((atomic.negate(\<epsilon>(-r));(env_assump r)\<^sup>\<omega> \<squnion> \<epsilon>(-r);\<top>) \<parallel> (\<pi>(r) \<squnion> \<E>);(pgm_restrict r)\<^sup>\<omega>)"
      by (simp add: nondet_seq_distrib seq_assoc)
    then have b7: "... = nil \<squnion> 
                  (atomic.negate(\<epsilon>(-r));(env_assump r)\<^sup>\<omega>\<parallel> (\<pi>(r) \<squnion> \<E>);(pgm_restrict r)\<^sup>\<omega>) \<squnion> 
                  (\<epsilon>(-r);\<top> \<parallel> (\<pi>(r) \<squnion> \<E>);(pgm_restrict r)\<^sup>\<omega>)"
      by (simp add: sup_assoc par.nondet_sync_distrib)
    then have b8: "... = nil \<squnion>
                  (atomic.negate(\<epsilon>(-r)) \<parallel> (\<pi>(r) \<squnion> \<E>));((env_assump r)\<^sup>\<omega> \<parallel> (pgm_restrict r)\<^sup>\<omega>) \<squnion>
                  ((\<epsilon>(-r) \<parallel> (\<pi>(r) \<squnion> \<E>));(\<top> \<parallel> (pgm_restrict r)\<^sup>\<omega>))" 
      by (metis atomic.hom_not env_negate_def2 env.hom_not negate_env_sup_Env_atomic par.atomic_pre_sync_atomic_pre 
               pgm_restrict_atomic pgm_restrict_def)
    then have b9: "... = nil \<squnion> (atomic.negate(\<epsilon>(-r)) \<parallel> (\<pi>(r) \<squnion> \<E>)); ((rely r) \<parallel> (guar r)) \<squnion>
                        ((\<epsilon>(-r) \<parallel> (\<pi>(r) \<squnion> \<E>));(\<top> \<parallel> (guar r)))" by simp    
    then have b10: "... = nil \<squnion> (Pgm \<squnion> \<epsilon>(r)); ((rely r) \<parallel> (guar r)) \<squnion>
                                (\<epsilon>(-r);(\<top> \<parallel> (guar r)))" using h1
       by (metis h2 atomic_negate_env double_compl env.hom_not sup.commute)
    then have b11: "... = nil \<squnion> atomic.negate(\<epsilon>(-r)); ((rely r) \<parallel> (guar r)) \<squnion>
                             (\<epsilon>(-r);(\<top> \<parallel> (guar r)))"
       by (metis atomic_negate_env double_compl env.hom_not sup.commute)   
    have a3: "nil \<squnion> (env_assump r);((rely r) \<parallel> (guar r)) \<ge> 
                        nil \<squnion> atomic.negate(\<epsilon>(-r)); ((rely r) \<parallel> (guar r)) \<squnion> (\<epsilon>(-r);(\<top> \<parallel> (guar r)))"
    proof -
      have c1: "nil \<squnion> (env_assump r);((rely r) \<parallel> (guar r)) = 
                      nil \<squnion> (atomic.negate(\<epsilon>(-r)) \<squnion> \<epsilon>(-r);\<top>); ((rely r) \<parallel> (guar r))"
        using env_assump_def4 by presburger 
      have c2: "... = nil \<squnion> atomic.negate(\<epsilon>(-r));((rely r) \<parallel> (guar r)) \<squnion> 
                            \<epsilon>(-r);\<top>;((rely r) \<parallel> (guar r))"
        by (simp add: sup_assoc nondet_seq_distrib)
      have c3: "... = nil \<squnion> atomic.negate(\<epsilon>(-r));((rely r) \<parallel> (guar r)) \<squnion> \<epsilon>(-r);\<top>"
        by (simp add: seq_assoc)
      have c4: "... \<ge> nil \<squnion> atomic.negate(\<epsilon>(-r));((rely r) \<parallel> (guar r)) \<squnion> \<epsilon>(-r);(\<top> \<parallel> (guar r))"
        by (simp add: par_abort)
      thus ?thesis using c1 c2 c3 by auto 
    qed
    thus ?thesis by (metis b1 b10 b11 b2 b3 b4 b5 b6 b7 b8 b9)
  qed
  thus ?thesis by (simp add: iter_induct_nil) 
qed

lemma pspec_introduce_par_helper: "(rely r) \<iinter> \<lceil>q\<rceil> \<ge> (rely(r \<squnion> r1) \<iinter> \<lceil>q\<rceil>) \<parallel> guar(r \<squnion> r1)"
proof -
  have a1: "(rely r) \<iinter> \<lceil>q\<rceil> \<ge> rely(r \<squnion> r1) \<iinter> \<lceil>q\<rceil>" (is "_ \<ge> ?rhs")
    using rely_weaken conj.sync_mono_left by blast
  have a2: "?rhs \<ge> (rely(r \<squnion> r1) \<parallel> guar(r \<squnion> r1)) \<iinter> (\<lceil>q\<rceil> \<parallel> chaos)" (is "_ \<ge> ?rhs")
    using rely_ref_rely_par_guar pspec_par_term by (metis conj.sync_mono_left)
  have a3: "?rhs \<ge> (rely(r \<squnion> r1) \<iinter> \<lceil>q\<rceil>) \<parallel> (guar(r \<squnion> r1) \<iinter> chaos)"
    by (rule par_conj_interchange)
  thus ?thesis using a1 a2 a3 by auto
qed

(*
lemma spec_introduce_par_helper: "(rely r) \<iinter> \<lparr>q\<rparr> \<ge> (rely(r \<squnion> r1) \<iinter> \<lparr>q\<rparr>) \<parallel> (guar(r \<squnion> r1) \<iinter> term)"
proof -
  have a1: "(rely r) \<iinter> \<lparr>q\<rparr> \<ge> rely(r \<squnion> r1) \<iinter> \<lparr>q\<rparr>" (is "_ \<ge> ?rhs") using rely_weaken
    using conj.sync_mono_left by blast
  have a2: "?rhs \<ge> (rely(r \<squnion> r1) \<parallel> guar(r \<squnion> r1)) \<iinter> (\<lparr>q\<rparr> \<parallel> term)" (is "_ \<ge> ?rhs")
    using rely_ref_rely_par_guar spec_par_term by (metis conj.sync_mono_left)
  have a3: "?rhs \<ge> (rely(r \<squnion> r1) \<iinter> \<lparr>q\<rparr>)  \<parallel> (guar(r \<squnion> r1) \<iinter> term)"
    by (rule par_conj_interchange)
  thus ?thesis using a1 a2 a3 by auto
qed
*)
(*---------------------------------------------------------*)

lemma pspec_introduce_par: 
  "(rely r) \<iinter> \<lceil>q1 \<sqinter> q2\<rceil> \<ge> (guar(r \<squnion> r2) \<iinter> rely(r \<squnion> r1) \<iinter> \<lceil>q1\<rceil>) \<parallel>
                          (guar(r \<squnion> r1) \<iinter> rely(r \<squnion> r2) \<iinter> \<lceil>q2\<rceil>)"
proof -
  have a1: "(rely r) \<iinter> \<lceil>q1 \<sqinter> q2\<rceil> = (rely r) \<iinter> \<lceil>q1\<rceil> \<iinter> (rely r) \<iinter> \<lceil>q2\<rceil>"
    using conj.sync_assoc conj_conj_distrib_left conj_pspec_pspec by metis
  then have a2: "... \<ge> ((rely(r \<squnion> r1) \<iinter> \<lceil>q1\<rceil>) \<parallel> guar(r \<squnion> r1)) \<iinter>
                  (guar(r \<squnion> r2) \<parallel> (rely(r \<squnion> r2) \<iinter> \<lceil>q2\<rceil>))" (is "_ \<ge> ?rhs")
    by (metis pspec_introduce_par_helper conj.sync_assoc conj.sync_mono par.sync_commute)
  then have a3: "?rhs \<ge> (rely(r \<squnion> r1) \<iinter> \<lceil>q1\<rceil> \<iinter> guar(r \<squnion> r2) \<iinter> chaos) \<parallel>
                   (guar(r \<squnion> r1) \<iinter> chaos \<iinter> rely(r \<squnion> r2) \<iinter> \<lceil>q2\<rceil>)" (is "_ \<ge> ?rhs")
    using conj_chaos local.conj_assoc par_conj_interchange by metis
  then have a4: "?rhs = (guar(r \<squnion> r2) \<iinter> rely(r \<squnion> r1) \<iinter> \<lceil>q1\<rceil> \<iinter> chaos) \<parallel>
                  (guar(r \<squnion> r1) \<iinter> rely(r \<squnion> r2) \<iinter> \<lceil>q2\<rceil> \<iinter> chaos)"
     by (metis conj.comm.left_commute conj.sync_commute)
  then have a5: "... = (guar(r \<squnion> r2) \<iinter> rely(r \<squnion> r1) \<iinter> \<lceil>q1\<rceil>) \<parallel>
                  (guar(r \<squnion> r1) \<iinter> rely(r \<squnion> r2) \<iinter> \<lceil>q2\<rceil>)"
     using conj.sync_assoc conj_chaos by metis
  thus ?thesis using a1 a2 a3 a4 by auto
qed

lemma spec_introduce_par: 
  "(rely r) \<iinter> \<lparr>q1 \<sqinter> q2\<rparr> \<ge> (guar(r \<squnion> r2) \<iinter> rely(r \<squnion> r1) \<iinter> \<lparr>q1\<rparr>) \<parallel>
                          (guar(r \<squnion> r1) \<iinter> rely(r \<squnion> r2) \<iinter> \<lparr>q2\<rparr>)"
proof -
  have "(rely r) \<iinter> \<lparr>q1 \<sqinter> q2\<rparr> = (rely r) \<iinter> \<lceil>q1 \<sqinter> q2\<rceil> \<iinter> term"
    using spec_def conj_assoc by simp
  also have "... \<ge> ((guar(r \<squnion> r2) \<iinter> rely(r \<squnion> r1) \<iinter> \<lceil>q1\<rceil>) \<parallel>
                          (guar(r \<squnion> r1) \<iinter> rely(r \<squnion> r2) \<iinter> \<lceil>q2\<rceil>)) \<iinter> term" (is "_ \<ge> ?rhs")
    using pspec_introduce_par conj.sync_mono_left by simp
  also have "?rhs = ((guar(r \<squnion> r2) \<iinter> rely(r \<squnion> r1) \<iinter> \<lceil>q1\<rceil>) \<parallel>
                          (guar(r \<squnion> r1) \<iinter> rely(r \<squnion> r2) \<iinter> \<lceil>q2\<rceil>)) \<iinter> (term \<parallel> term)"
    using par_term_term by simp
  also have "... \<ge> (guar(r \<squnion> r2) \<iinter> rely(r \<squnion> r1) \<iinter> \<lceil>q1\<rceil> \<iinter> term) \<parallel>
                          (guar(r \<squnion> r1) \<iinter> rely(r \<squnion> r2) \<iinter> \<lceil>q2\<rceil> \<iinter> term)" (is "_ \<ge> ?rhs")
    using par_conj_interchange by simp
  also have "?rhs = (guar(r \<squnion> r2) \<iinter> rely(r \<squnion> r1) \<iinter> \<lparr>q1\<rparr>) \<parallel>
                          (guar(r \<squnion> r1) \<iinter> rely(r \<squnion> r2) \<iinter> \<lparr>q2\<rparr>)"
    using spec_def conj_assoc by simp
  finally show ?thesis .
qed
  
(*-----------------------------------------------------------------*)
lemma pgmenv_conj_split: "(\<epsilon>(p1) \<squnion> Pgm) \<iinter> (\<E> \<squnion> \<pi>(p2)) = \<epsilon>(p1) \<squnion> \<pi>(p2)"
proof -
  have "(\<epsilon>(p1) \<squnion> Pgm) \<iinter> (\<E> \<squnion> \<pi>(p2)) = (\<pi>(\<top>) \<squnion> \<epsilon>(p1)) \<iinter> (\<pi>(p2) \<squnion> \<epsilon>(\<top>))"
    by (metis Env_def sup_commute Pgm_def)
  also have "... = \<pi>(\<top> \<sqinter> p2) \<squnion> \<epsilon>(p1 \<sqinter> \<top>)"
    using pgmenv_conj_pgmenv by presburger
  also have "... = \<epsilon>(p1) \<squnion> \<pi>(p2)"
    using sup_commute by simp
  finally show ?thesis .
qed
  
lemma restrict_par_restrict:
  shows "restrict p1 \<parallel> restrict p2 = restrict(p1 \<sqinter> p2) \<iinter> pgm_restrict(p1 \<squnion> p2)"
proof -
  have a1: "restrict p1 \<parallel> restrict p2 = (\<epsilon>(p1) \<squnion> Pgm) \<parallel> (\<epsilon>(p2) \<squnion> Pgm)"
     using restrict_def by auto
  then have a2: "... = (\<epsilon>(p1) \<parallel> \<epsilon>(p2)) \<squnion> (\<epsilon>(p1) \<parallel> Pgm) \<squnion> (Pgm \<parallel> \<epsilon>(p2)) \<squnion> (Pgm\<parallel>Pgm)"
     by (simp add: par.nondet_sync_product)
  then have a3: "... =  (\<epsilon>(p1 \<sqinter> p2) \<squnion> \<pi>(p1 \<sqinter> top) \<squnion> \<pi>(top \<sqinter> p2) \<squnion> \<bottom>)"
     by (metis env.hom_inf env_par_env_axiom env_par_pgm_axiom flip_def2 par.sync_commute Pgm_def 
               Pgm_par_pgm pgm.hom_inf)
  then have a3: "... =  (\<epsilon>(p1 \<sqinter> p2) \<squnion> \<pi>(p1 \<squnion> p2))" by (simp add: sup_assoc)
  then have a4: "... = (\<epsilon>(p1 \<sqinter> p2) \<squnion> Pgm) \<iinter> (\<E> \<squnion> \<pi>(p1 \<squnion> p2))"
    using pgmenv_conj_split by presburger 
  thus ?thesis by (metis a2 a3 env_par_env_axiom env_par_pgm_axiom sup.commute flip_def2 par.sync_commute 
        Pgm_def Pgm_par_pgm pgm_restrict_def restrict_def env.hom_inf pgm.hom_inf)
qed


lemma restrict_iter_par_restrict_iter: 
  shows "(restrict p1)\<^sup>\<omega> \<parallel> (restrict p2)\<^sup>\<omega> = (restrict (p1 \<sqinter> p2))\<^sup>\<omega> \<iinter> (guar (p1 \<squnion> p2))"
proof -
  have a1: "(restrict p1)\<^sup>\<omega> \<parallel> (restrict p2)\<^sup>\<omega> = (\<epsilon>(p1) \<squnion> Pgm)\<^sup>\<omega> \<parallel> (\<epsilon>(p2) \<squnion> Pgm)\<^sup>\<omega>"
    using restrict_def by auto
  then have a2: "\<dots> = ((\<epsilon>(p1) \<squnion> Pgm) \<parallel> (\<epsilon>(p2) \<squnion> Pgm))\<^sup>\<omega>"
    by (metis env_or_Pgm_atomic par.atomic_iter_sync_iter)
  then have a3: "\<dots> = ((\<epsilon>(p1) \<parallel> (\<epsilon>(p2) \<squnion> Pgm)) \<squnion> (Pgm \<parallel> (\<epsilon>(p2) \<squnion> Pgm)))\<^sup>\<omega>"
    by (simp add: par.nondet_sync_distrib) 
  then have a4: "\<dots> = ((\<epsilon>(p1) \<parallel> \<epsilon>(p2)) \<squnion> (\<epsilon>(p1) \<parallel> Pgm) \<squnion> 
                        (Pgm \<parallel> \<epsilon>(p2)) \<squnion> (Pgm \<parallel> Pgm))\<^sup>\<omega>"
    by (simp add: sup_assoc par.sync_nondet_distrib) 
  then have a5: "\<dots> = (\<epsilon>(p1 \<sqinter> p2) \<squnion> \<pi>(p1 \<squnion> p2))\<^sup>\<omega>" 
    proof -
      have "((\<epsilon>(p1) \<parallel> \<epsilon>(p2)) \<squnion> (\<epsilon>(p1) \<parallel> Pgm) \<squnion> (Pgm \<parallel> \<epsilon>(p2)) \<squnion> (Pgm \<parallel> Pgm))\<^sup>\<omega> =
            ((\<epsilon>(p1) \<sqinter> \<epsilon>(p2)) \<squnion> \<pi>(p1) \<squnion> \<pi>(p2) \<squnion> \<bottom>)\<^sup>\<omega> "  
<<<<<<< HEAD
        by (metis (no_types, opaque_lifting) env_par_env_axiom env_par_pgm_axiom inf_top.right_neutral 
=======
        by (metis (no_types) env_par_env_axiom env_par_pgm_axiom inf_top.right_neutral 
>>>>>>> a87ff0585792b159a497ae6dae5b85c93f31726d
                local.flip_def2 par.sync_commute Pgm_def pgm.hom_inf pgm_par_pgm)
      thus ?thesis by (simp add: sup_assoc)
    qed
  then have a6: "... = ((\<epsilon>(p1 \<sqinter> p2) \<squnion> Pgm) \<iinter> (\<E> \<squnion> \<pi>(p1 \<squnion> p2)))\<^sup>\<omega>"
    proof -
      have "(\<epsilon>(p1 \<sqinter> p2) \<squnion> Pgm) \<iinter> (\<E> \<squnion> \<pi>(p1 \<squnion> p2)) = \<epsilon>(p1 \<sqinter> p2) \<squnion> \<pi>(p1 \<squnion> p2)"
          using pgmenv_conj_split by presburger 
      thus ?thesis by auto
    qed
  thus ?thesis 
   proof -
     obtain q where atomic1: "(\<epsilon>(p1 \<sqinter> p2) \<squnion> Pgm) = atomic(q)"
            by (metis restrict_atomic restrict_def)
     obtain q2 where general_atomic: "(\<E> \<squnion> \<pi>(p1 \<squnion> p2)) = atomic(q2)" 
            by (metis sup.commute pgm_or_Env_atomic)
     have "((\<epsilon>(p1 \<sqinter> p2) \<squnion> Pgm) \<iinter> (\<E> \<squnion> \<pi>(p1 \<squnion> p2)))\<^sup>\<omega> = 
                    (\<epsilon>(p1 \<sqinter> p2) \<squnion> Pgm)\<^sup>\<omega> \<iinter> (\<E> \<squnion> \<pi>(p1 \<squnion> p2))\<^sup>\<omega>"
         using atomic1 general_atomic conj.atomic_iter_sync_iter by auto
     thus ?thesis using a2 a3 a4 a5 a6 restrict_def by (simp add: sup.commute) 
  qed
qed

lemma rely_par_distrib: "(rely r) \<iinter> (c \<parallel> d) \<ge> (rely r) \<iinter> (guar r) \<iinter> c \<parallel> (rely r) \<iinter> (guar r) \<iinter> d"
proof -
  have "(rely r) \<iinter> (c \<parallel> d) = (rely r) \<iinter> (rely r) \<iinter> (c \<parallel> d)"
    by simp
  also have "... \<ge> ((rely r) \<parallel> (guar r)) \<iinter> ((guar r) \<parallel> (rely r)) \<iinter> (c \<parallel> d)" (is "_ \<ge> ?rhs")
    using conj.sync_mono_left par_commute rely_ref_rely_par_guar by auto
  also have "?rhs \<ge> ((rely r) \<iinter> (guar r) \<parallel> (guar r) \<iinter> (rely r)) \<iinter> (c \<parallel> d)" (is "_ \<ge> ?rhs")
    by (simp add: par_conj_interchange conj.sync_mono_left)
  also have "?rhs \<ge> ((rely r) \<iinter> (guar r) \<iinter> c \<parallel> (guar r) \<iinter> (rely r) \<iinter> d)"
    by (simp add: par_conj_interchange)
  finally show ?thesis using conj_commute by simp
qed
  
end
 
end
