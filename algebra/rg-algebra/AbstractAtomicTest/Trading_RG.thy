section \<open>Trading Rely-Guarantee laws.\<close>

theory Trading_RG
imports
  "Relies_Guarantees"    
  "Specification"
begin
  
locale spec_trade_rely_guar = strong_spec + relies_guarantees + 
  constrains test :: "'state :: type set \<Rightarrow> 'a"
  constrains pgm  :: "'state rel \<Rightarrow> 'a" 
  constrains env  :: "'state rel \<Rightarrow> 'a"
begin    

lemma rely_sequential: "(rely r) \<iinter> \<lparr>(q1 O q2) \<triangleright> p2\<rparr>
                        \<ge> ((rely r) \<iinter> \<lparr>q1 \<triangleright> p1\<rparr>); ((rely r) \<iinter> \<lbrace>p1\<rbrace>; \<lparr>q2 \<triangleright> p2\<rparr>)"
proof -
  have "q1 O (q2 \<triangleright> p2) = (q1 O q2) \<triangleright> p2"
    using range_restrict_relcomp by metis
  then have "\<lparr>(q1 O q2) \<triangleright> p2\<rparr> \<ge> \<lparr>q1 \<triangleright> p1\<rparr>;\<lbrace>p1\<rbrace>; \<lparr>q2 \<triangleright> p2\<rparr>"
    using spec_seq_introduce by metis
  then have "(rely r) \<iinter> \<lparr>(q1 O q2) \<triangleright> p2\<rparr> \<ge> (rely r) \<iinter> \<lparr>q1 \<triangleright> p1\<rparr>;\<lbrace>p1\<rbrace>; \<lparr>q2 \<triangleright> p2\<rparr>" (is "_ \<ge> ?rhs")
    using conj.sync_mono_right seq_mono_right seq_assoc by simp
  also have "?rhs \<ge> ((rely r) \<iinter> \<lparr>q1 \<triangleright> p1\<rparr>);((rely r) \<iinter> \<lbrace>p1\<rbrace>; \<lparr>q2 \<triangleright> p2\<rparr>)"
    using rely_seq_distrib by (simp add: seq_assoc)
  finally show ?thesis .
qed
  
lemma rely_sequential_nopost: "(rely r) \<iinter> \<lparr>q1 O q2\<rparr>
                            \<ge> ((rely r) \<iinter> \<lparr>q1 \<triangleright> p1\<rparr>);((rely r) \<iinter> \<lbrace>p1\<rbrace>; \<lparr>q2\<rparr>)"
proof -
  have "(rely r) \<iinter> \<lparr>q1 O q2\<rparr> = (rely r) \<iinter> \<lparr>(q1 O q2) \<triangleright> UNIV\<rparr>"
  proof -
    have "q1 O q2 = (q1 O q2) \<triangleright> UNIV"
      using restrict_range_def by auto
    then show ?thesis by simp
  qed
  also have "... \<ge> ((rely r) \<iinter> \<lparr>q1 \<triangleright> p1\<rparr>);((rely r) \<iinter> \<lbrace>p1\<rbrace>; \<lparr>q2 \<triangleright> UNIV\<rparr>)" (is "_ \<ge> ?rhs")
    using rely_sequential by metis
  also have "?rhs = ((rely r) \<iinter> \<lparr>q1 \<triangleright> p1\<rparr>);((rely r) \<iinter> \<lbrace>p1\<rbrace>; \<lparr>q2\<rparr>)"
  proof -
    have "q2 = q2 \<triangleright> UNIV"
      using restrict_range_def by auto
    then show ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma guar_conj_chaos: "(guar g) \<iinter> chaos = ((\<pi>(g) \<squnion> \<epsilon>(\<top>)))\<^sup>\<omega>"
proof -      
  have "(guar g) \<iinter> chaos = (\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<omega> \<iinter> (\<pi>(\<top>) \<squnion> \<epsilon>(\<top>))\<^sup>\<omega>"
    using guar_def chaos_def2 pgm_restrict_def Env_def by metis
  also have "... = ((\<pi>(g) \<squnion> \<epsilon>(\<top>)) \<iinter> (\<pi>(\<top>) \<squnion> \<epsilon>(\<top>)))\<^sup>\<omega>"
    using conj.atomic_iter_sync_fiter_pre conj.atomic_iter_sync_iter 
          pgm_or_env_atomic env_atomic by metis
  also have "... = ((\<pi>(g \<inter> \<top>) \<squnion> \<epsilon>(\<top> \<inter> \<top>)))\<^sup>\<omega>"
    using pgmenv_conj_pgmenv pgmenv_conj_env by presburger
  also have "... = ((\<pi>(g) \<squnion> \<epsilon>(\<top>)))\<^sup>\<omega>"
    by simp
  finally show ?thesis .
qed

lemma guar_conj_term: "(guar g) \<iinter> term = ((\<pi>(g) \<squnion> \<epsilon>(\<top>)))\<^sup>\<star>;(\<epsilon>(\<top>))\<^sup>\<omega>"
proof -      
  have "(guar g) \<iinter> term = (\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<omega> \<iinter> (\<pi>(\<top>) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>"
    using guar_def term_def pgm_restrict_def Env_def by metis
  also have "... = ((\<pi>(g) \<squnion> \<epsilon>(\<top>)) \<iinter> (\<pi>(\<top>) \<squnion> \<epsilon>(\<top>)))\<^sup>\<star>;((\<pi>(g) \<squnion> \<epsilon>(\<top>)) \<iinter> \<epsilon>(\<top>))\<^sup>\<omega>"
    using conj.atomic_iter_sync_fiter_pre conj.atomic_iter_sync_iter 
          pgm_or_env_atomic env_atomic by metis
  also have "... = ((\<pi>(g \<inter> \<top>) \<squnion> \<epsilon>(\<top> \<inter> \<top>)))\<^sup>\<star>;(\<epsilon>(\<top> \<inter> \<top>))\<^sup>\<omega>"
    using pgmenv_conj_pgmenv pgmenv_conj_env by presburger
  also have "... = ((\<pi>(g) \<squnion> \<epsilon>(\<top>)))\<^sup>\<star>;(\<epsilon>(\<top>))\<^sup>\<omega>"
    by simp
  finally show ?thesis .
qed  

(* Rely weak conjunction with a 'term'-like command *)

(* Helpers for Trading RG and Expressions. *)
lemma rely_guar_term_helper1: "(nil \<squnion> \<epsilon>(-r);\<top>) \<iinter> \<epsilon>(\<top>)\<^sup>\<omega> = (nil \<squnion> \<epsilon>(-r);\<top>)"
proof -
  have a1: "\<epsilon>(-r);\<top> \<iinter> nil = \<bottom>"
    using conj.nil_sync_atomic_pre env_atomic conj.sync_commute by metis
  have a2: "\<epsilon>(-r);\<top> \<iinter> \<epsilon>(\<top>);\<epsilon>(\<top>)\<^sup>\<omega>= (\<epsilon>(-r));\<top>"
    using conj.nil_sync_atomic_pre conj.atomic_pre_sync_atomic_pre env_atomic conj.sync_commute
          conj_abort_left inf_top_right env_conj_env by metis
  have "(nil \<squnion> \<epsilon>(-r);\<top>) \<iinter> \<epsilon>(\<top>)\<^sup>\<omega> = (nil \<iinter> \<epsilon>(\<top>)\<^sup>\<omega> \<squnion> \<epsilon>(-r);\<top> \<iinter> \<epsilon>(\<top>)\<^sup>\<omega>)"
    using conj.nondet_sync_distrib by auto
  also have "... = nil \<squnion> \<epsilon>(-r);\<top> \<iinter> \<epsilon>(\<top>)\<^sup>\<omega>"
    using conj.atomic_fiter_pre_sync_nil conj.sync_commute conj.atomic_iter_sync_nil 
           env_atomic by metis
  also have "... = nil \<squnion> \<epsilon>(-r);\<top> \<iinter> (nil \<squnion> \<epsilon>(\<top>);\<epsilon>(\<top>)\<^sup>\<omega>)"
    using iter_unfold by simp
  also have "... = nil \<squnion> (\<epsilon>(-r));\<top>"
    using  conj.sync_nondet_distrib seq_assoc a1 a2 by simp
  finally show ?thesis .
qed

lemma rely_guar_term_helper2: "(nil \<squnion> \<epsilon>(-r);\<top>) \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> = (nil \<squnion> \<epsilon>(-r);\<top>)"
proof -
  have a1: "nil \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>));(\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> = \<bottom>"
    using conj.nil_sync_atomic_pre pgm_or_env_atomic seq_assoc by metis    
  have a2: "\<epsilon>(-r);\<top> \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>));(\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> = (\<epsilon>(-r));\<top>"
  proof -
    have "\<epsilon>(-r);\<top> \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>));(\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> = (\<epsilon>(-r) \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>)));\<top>"
      using conj.nil_sync_atomic_pre conj.atomic_pre_sync_atomic_pre env_atomic pgm_or_env_atomic 
            conj.sync_commute conj_abort_left seq_assoc by metis 
    also have "... = (\<epsilon>(-r));\<top>"
      by (metis inf_top_right local.conj_commute env_conj_env pgmenv_conj_env)
    finally show ?thesis .
  qed      
  have  "(nil \<squnion> \<epsilon>(-r);\<top>) \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>  = 
                     (nil \<squnion> \<epsilon>(-r);\<top>) \<iinter> (nil \<squnion> (\<pi>(g) \<squnion> \<epsilon>(\<top>));(\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>);\<epsilon>(\<top>)\<^sup>\<omega>"
    using iter_unfold fiter_unfold by simp
  also have "... = (nil \<squnion> \<epsilon>(-r);\<top>) \<iinter> (\<epsilon>(\<top>)\<^sup>\<omega> \<squnion> (\<pi>(g) \<squnion> \<epsilon>(\<top>));(\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>)"
    using iter_unfold nondet_seq_distrib by simp 
  also have "... = (nil \<squnion> \<epsilon>(-r);\<top>) \<squnion> (nil \<squnion> \<epsilon>(-r);\<top>) \<iinter> ((\<pi>(g) \<squnion> \<epsilon>(\<top>));(\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>)"
    using  conj.sync_nondet_distrib seq_assoc rely_guar_term_helper1 by simp
  also have "... =(nil \<squnion> \<epsilon>(-r);\<top>) \<squnion> (nil \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>));(\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> 
                                     \<squnion> \<epsilon>(-r);\<top> \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>));(\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>)"
    using conj.nondet_sync_distrib by auto
  also have "... = (nil \<squnion> \<epsilon>(-r);\<top>)"
    using a1 a2 by simp
  finally show ?thesis .
qed

(* TODO Move this somewhere more appropriate *)
lemma atomic_one_iter:
  assumes a_atomic[simp]: "a = atomic p"
  assumes b_atomic[simp]: "b = atomic q"
  shows "a \<iinter> b\<^sup>\<omega> = a \<iinter> b"
proof -
  have "a \<iinter> b\<^sup>\<omega> = a \<iinter> (nil \<squnion> b;b\<^sup>\<omega>)" using iter_def
    using iter_unfold by simp
  also have "... = (a \<iinter> nil) \<squnion> (a \<iinter> b;b\<^sup>\<omega>)"
    by (rule conj.sync_nondet_distrib)
  also have "... = ((atomic p);nil \<iinter> nil) \<squnion> (a \<iinter> b;b\<^sup>\<omega>)"
    by simp
  also have "... = \<bottom> \<squnion> (a \<iinter> b;b\<^sup>\<omega>)"
    using conj.atomic_pre_sync_nil by metis
  also have "... = a \<iinter> b;b\<^sup>\<omega>"
    by (rule Lattices.bounded_semilattice_sup_bot_class.sup_bot_left)
  also have "... = a \<iinter> b;(nil \<squnion> b;b\<^sup>\<omega>)"
    using iter_unfold by simp
  also have "... = a;nil \<iinter> b;(nil \<squnion> b;b\<^sup>\<omega>)"
    by simp
  also have "... = (a \<iinter> b);(nil \<iinter> (nil \<squnion> b;b\<^sup>\<omega>))"
    using a_atomic b_atomic conj.atomic_pre_sync_atomic_pre by blast
  also have "... = (a \<iinter> b);((nil \<iinter> nil) \<squnion> (nil \<iinter> b;b\<^sup>\<omega>))"
    using conj.sync_nondet_distrib by simp
  also have "... = (a \<iinter> b);((nil \<iinter> nil) \<squnion> \<bottom>)"
    by (simp add: conj.nil_sync_atomic_pre)
  also have "... = (a \<iinter> b);(nil \<iinter> nil)"
    by simp
  also have "... = (a \<iinter> b);nil"
    by simp
  also have "... = a \<iinter> b"
    by simp
  finally show ?thesis .
qed

lemma rely_guar:
  shows "(rely r) \<iinter> (guar g) = (\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<omega>;(nil \<squnion> \<epsilon>(-r);\<top>)"
proof -
  have "(rely r) \<iinter> (guar g) = ((\<pi>(\<top>) \<squnion> \<epsilon>(r))\<^sup>\<omega>;(nil \<squnion> \<epsilon>(-r);\<top>)) \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<omega>"
    using rely_def3 guar_conj_chaos conj_assoc conj_chaos by metis
  also have "... = ((\<pi>(\<top>) \<squnion> \<epsilon>(r))\<^sup>\<omega>;nil \<squnion> (\<pi>(\<top>) \<squnion> \<epsilon>(r))\<^sup>\<omega>;\<epsilon>(-r);\<top>) \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<omega>"
    using calculation par.seq_nondet_distrib seq_assoc by simp
  also have "... = ((\<pi>(\<top>) \<squnion> \<epsilon>(r))\<^sup>\<omega>;nil \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<omega>) \<squnion> ((\<pi>(\<top>) \<squnion> \<epsilon>(r))\<^sup>\<omega>;\<epsilon>(-r);\<top> \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<omega>)"
    using conj.nondet_sync_distrib by simp
  also have "... = ((\<pi>(\<top>) \<squnion> \<epsilon>(r))\<^sup>\<omega>;nil \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<omega>) \<squnion> (((\<pi>(\<top>) \<squnion> \<epsilon>(r))\<^sup>\<omega> \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<omega>);(\<epsilon>(-r) \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<omega>);\<top>)"
    using conj_abort_right env.Hom_def guar_def guar_distrib_seq_eq local.conj_commute pgm_restrict_def by (metis (no_types, lifting))
  also have "... = ((\<pi>(\<top>) \<squnion> \<epsilon>(r))\<^sup>\<omega>;nil \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<omega>) \<squnion> (((\<pi>(\<top>) \<squnion> \<epsilon>(r))\<^sup>\<omega> \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<omega>);(\<epsilon>(-r) \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>)));\<top>)"
    using atomic_one_iter pgm_or_env_atomic env_atomic by metis
  also have "... = ((\<pi>(\<top>) \<squnion> \<epsilon>(r))\<^sup>\<omega>;nil \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<omega>) \<squnion> (((\<pi>(\<top>) \<squnion> \<epsilon>(r))\<^sup>\<omega> \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<omega>);\<epsilon>(-r);\<top>)"
    using local.conj.sync_nondet_distrib env_conj_pgm by (simp add: env_conj_env)
  also have "... = ((\<pi>(\<top>) \<squnion> \<epsilon>(r))\<^sup>\<omega> \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<omega>) \<squnion> (((\<pi>(\<top>) \<squnion> \<epsilon>(r))\<^sup>\<omega> \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<omega>);\<epsilon>(-r);\<top>)"
    by simp
  also have "... = ((\<pi>(\<top>) \<squnion> \<epsilon>(r)) \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>)))\<^sup>\<omega> \<squnion> (((\<pi>(\<top>) \<squnion> \<epsilon>(r))\<^sup>\<omega> \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<omega>);\<epsilon>(-r);\<top>)"
    using pgm_or_env_atomic conj.atomic_iter_sync_iter by metis
  also have "... = ((\<pi>(\<top>) \<squnion> \<epsilon>(r)) \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>)))\<^sup>\<omega> \<squnion> (((\<pi>(\<top>) \<squnion> \<epsilon>(r)) \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>)))\<^sup>\<omega>;\<epsilon>(-r);\<top>)"
    using pgm_or_env_atomic conj.atomic_iter_sync_iter by metis
  also have "... = (\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<omega> \<squnion> ((\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<omega>;\<epsilon>(-r);\<top>)"
    by (simp add: pgmenv_conj_pgmenv)
  also have "... = (\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<omega>;nil \<squnion> ((\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<omega>;\<epsilon>(-r);\<top>)"
    by simp
  also have "... = (\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<omega>;(nil \<squnion> \<epsilon>(-r);\<top>)"
    using calculation rely_guar_def by simp
  finally show ?thesis .
qed

lemma rely_guar_term:
  shows "(rely r) \<iinter> (guar g) \<iinter> term = (\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<star>;\<epsilon>(r)\<^sup>\<omega>;(nil \<squnion> \<epsilon>(-r);\<top>)"
proof -
  have "(rely r) \<iinter> (guar g) \<iinter> term = ((\<pi>(\<top>) \<squnion> \<epsilon>(r))\<^sup>\<omega>;(nil \<squnion> \<epsilon>(-r);\<top>)) \<iinter> ((\<pi>(g) \<squnion> \<epsilon>(\<top>)))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>"
    using rely_def3 guar_conj_term conj_assoc by metis
  also have "... = ((\<pi>(\<top>) \<squnion> \<epsilon>(r)) \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>)))\<^sup>\<star>;
                    (((nil \<squnion> \<epsilon>(-r);\<top>) \<iinter> ((\<pi>(g) \<squnion> \<epsilon>(\<top>)))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>)
                      \<squnion> (((\<pi>(\<top>) \<squnion> \<epsilon>(r))\<^sup>\<omega>;(nil \<squnion> \<epsilon>(-r);\<top>))             \<iinter> \<epsilon>(\<top>)\<^sup>\<omega>)) "
    using conj.atomic_iter_pre_sync_fiter_pre2 pgm_or_env_atomic env_atomic by metis
  also have "... = ((\<pi>(\<top>) \<squnion> \<epsilon>(r)) \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>)))\<^sup>\<star>;
                    (((nil \<squnion> \<epsilon>(-r);\<top>) \<iinter> ((\<pi>(g) \<squnion> \<epsilon>(\<top>)))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>)
                      \<squnion> (((\<pi>(\<top>) \<squnion> \<epsilon>(r)) \<iinter> \<epsilon>(\<top>))\<^sup>\<omega>;   ((nil \<squnion> \<epsilon>(-r);\<top>) \<iinter> \<epsilon>(\<top>)\<^sup>\<omega>))) "
    using conj.atomic_iter_pre_sync_iter pgm_or_env_atomic env_atomic by metis
  also have "... = (\<pi>(\<top> \<sqinter> g) \<squnion> \<epsilon>(r \<sqinter> \<top>))\<^sup>\<star>;
                    (((nil \<squnion> \<epsilon>(-r);\<top>) \<iinter> ((\<pi>(g) \<squnion> \<epsilon>(\<top>)))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>)
                      \<squnion> (((\<epsilon>(r \<sqinter> \<top>))\<^sup>\<omega>;                ((nil \<squnion> \<epsilon>(-r);\<top>) \<iinter> \<epsilon>(\<top>)\<^sup>\<omega>)))) "
    using pgmenv_conj_pgmenv pgmenv_conj_env by presburger
  also have "... = (\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<star>;
                    (((nil \<squnion> \<epsilon>(-r);\<top>) \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>)
                      \<squnion> \<epsilon>(r)\<^sup>\<omega>;                         ((nil \<squnion> \<epsilon>(-r);\<top>) \<iinter> \<epsilon>(\<top>)\<^sup>\<omega>))"
    by simp
  also have "... = (\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<star>; (((nil \<squnion> \<epsilon>(-r);\<top>)) \<squnion> \<epsilon>(r)\<^sup>\<omega>;(nil \<squnion> \<epsilon>(-r);\<top>))"
    using rely_guar_term_helper1 rely_guar_term_helper2 by simp
  also have "... = (\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<star>;\<epsilon>(r)\<^sup>\<omega>;(nil \<squnion> \<epsilon>(-r);\<top>)"
    by (metis sup.absorb2 inf_sup_ord(3) par.iter_induct seq_assoc)
  finally show ?thesis .
qed

lemma pspec_trade_rely_guar_test_pre:  "(\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<omega>;\<tau>(((r \<union> g)\<^sup>*``{s})) \<ge> 
                            \<tau>(((r \<union> g)\<^sup>*``{s}));(\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<omega>"
proof -
  (* All states in the transitive closure of relation (r or g) that 
     are reachable from initial state s. *)
  define post where "post \<equiv> ((r \<union> g)\<^sup>*``{s})"     
  (* Given that the state is within ?post, any step following relation (r or g) 
     will keep the state within ?post.  *)
  have rg_restrict: "((r \<union> g) `` post) \<subseteq> post"
  proof -
    define q where q_def: "q = (r \<union> g)"
    have "(q `` ((q)\<^sup>*``{s})) \<subseteq> ((q)\<^sup>*``{s})"
      by auto
    then show ?thesis using q_def post_def by simp
  qed
  have env_ref: "\<epsilon>(r);\<tau>(post) \<ge> \<tau>(post);\<epsilon>(r)"
    using env_test_ref rg_restrict by blast
  have "\<pi>(g);\<tau>(post) \<ge> \<tau>(post);\<pi>(g)"
    using pgm_test_ref rg_restrict by blast
  then have pgm_env_ref: "(\<pi>(g) \<squnion> \<epsilon>(r));\<tau>(post) \<ge> \<tau>(post);(\<pi>(g) \<squnion> \<epsilon>(r))"
    using env_ref sup_mono nondet_seq_distrib par.seq_nondet_distrib by simp    
  have "(\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<omega>;\<tau>(post) \<ge> \<tau>(post);(\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<omega>"
    using iter_test_pre pgm_env_ref by metis
  then show ?thesis using post_def by simp
qed

(*
lemma spec_trade_rely_guar_test_pre:  "(\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<star>;\<epsilon>(r)\<^sup>\<omega>;\<tau>(((r \<union> g)\<^sup>*``{s})) \<ge> 
                            \<tau>(((r \<union> g)\<^sup>*``{s}));(\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<star>;\<epsilon>(r)\<^sup>\<omega>"
proof -
  (* All states in the transitive closure of relation (r or g) that 
     are reachable from initial state s. *)
  define post where "post \<equiv> ((r \<union> g)\<^sup>*``{s})"     
  (* Given that the state is within ?post, any step following relation (r or g) 
     will keep the state within ?post.  *)
  have rg_restrict: "((r \<union> g) `` post) \<subseteq> post"
  proof -
    define q where q_def: "q = (r \<union> g)"
    have "(q `` ((q)\<^sup>*``{s})) \<subseteq> ((q)\<^sup>*``{s})"
      by auto
    then show ?thesis using q_def post_def by simp
  qed
  have env_ref: "\<epsilon>(r);\<tau>(post) \<ge> \<tau>(post);\<epsilon>(r)"
    using env_test_ref rg_restrict by blast
  have "\<pi>(g);\<tau>(post) \<ge> \<tau>(post);\<pi>(g)"
    using pgm_test_ref rg_restrict by blast
  then have pgm_env_ref: "(\<pi>(g) \<squnion> \<epsilon>(r));\<tau>(post) \<ge> \<tau>(post);(\<pi>(g) \<squnion> \<epsilon>(r))"
    using env_ref sup_mono nondet_seq_distrib par.seq_nondet_distrib by simp    
  have "(\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<star>;\<epsilon>(r)\<^sup>\<omega>;\<tau>(post) \<ge> (\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<star>;\<tau>(post);\<epsilon>(r)\<^sup>\<omega>" (is "_ \<ge> ?rhs")
    using iter_test_pre env_ref seq_mono_right seq_assoc by simp
  also have "?rhs  \<ge> \<tau>(post);(\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<star>;\<epsilon>(r)\<^sup>\<omega>"
    using fiter_test_pre pgm_env_ref seq_mono_left seq_assoc by metis
  finally show ?thesis using post_def by simp
qed
*)

lemma pspec_trade_rely_guar_helper: "(rely r) \<iinter> (\<tau>({s}); chaos; \<tau>((r \<squnion> g)\<^sup>*``{s})) \<ge> 
                           \<tau>({s});((rely r) \<iinter> (guar g))"
proof -
  have a1: "\<forall>s. rely r \<iinter> \<tau>(s) = \<tau>(s)"
    using conj.sync_commute test_rely_conj by auto
  have a2: "{s} \<inter> (r \<squnion> g)\<^sup>*``{s} = {s}"
      by blast              
  have "(rely r) \<iinter> (\<tau>({s}); chaos; \<tau>((r \<squnion> g)\<^sup>*``{s})) \<ge>
        \<tau>({s});((rely r) \<iinter> (chaos; \<tau>((r \<squnion> g)\<^sup>*``{s})))" (is "_ \<ge> ?rhs")
    using a1 by (metis rely_seq_distrib seq_assoc)
  also have "?rhs \<ge>  \<tau>({s});((rely r) \<iinter> (chaos)); \<tau>((r \<squnion> g)\<^sup>*``{s})" (is "_ \<ge> ?rhs")
    using a1 by (metis rely_seq_distrib seq_assoc seq_mono_right)
  also have "?rhs \<ge>  \<tau>({s});((rely r) \<iinter> (guar g) \<iinter> (chaos)); \<tau>((r \<squnion> g)\<^sup>*``{s})" (is "_ \<ge> ?rhs")
    using a1 chaos_ref_guar conj.sync_mono_left by (meson conj_conjoin_non_aborting seq_mono_left seq_mono_right)
  also have "?rhs \<ge>  \<tau>({s});((rely r) \<iinter> (guar g)); \<tau>((r \<squnion> g)\<^sup>*``{s})" (is "_ \<ge> ?rhs")
    by simp
  also have "?rhs =  \<tau>({s});((\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<omega>;(nil \<squnion> \<epsilon>(-r);\<top>)); \<tau>((r \<squnion> g)\<^sup>*``{s})"
    using rely_guar by simp
  also have "... =  \<tau>({s});((\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<omega>;(\<tau>((r \<squnion> g)\<^sup>*``{s}) \<squnion> \<epsilon>(-r);\<top>))"
    using nondet_seq_distrib seq_assoc by simp
  also have "... =  \<tau>({s});((\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<omega>;\<tau>((r \<squnion> g)\<^sup>*``{s}) \<squnion> 
                            (\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<omega>;\<epsilon>(-r);\<top>)"
    using par.seq_nondet_distrib seq_assoc by simp
  also have "... \<ge>  \<tau>({s});(\<tau>((r \<squnion> g)\<^sup>*``{s});(\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<omega> \<squnion> 
                            (\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<omega>;\<epsilon>(-r);\<top>)" (is "_ \<ge> ?rhs") 
    using pspec_trade_rely_guar_test_pre nondet_mono_left seq_mono_right by metis
  also have "?rhs =  \<tau>({s});((\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<omega> \<squnion> 
                            (\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<omega>;\<epsilon>(-r);\<top>)"
    by (metis a2 par.seq_nondet_distrib seq_assoc test_inf_eq_seq test.hom_inf) 
  also have "... =  \<tau>({s});((\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<omega>);(nil \<squnion> \<epsilon>(-r);\<top>)"
    by (simp add: par.seq_nondet_distrib seq_assoc)
  also have "... =  \<tau>({s});((rely r) \<iinter> (guar g))"
    using rely_guar seq_assoc by simp
  finally show ?thesis .
qed

(*
lemma spec_trade_rely_guar_helper: "(rely r) \<iinter> (\<tau>({s}); term; \<tau>((r \<squnion> g)\<^sup>*``{s})) \<ge> 
                           \<tau>({s});((rely r) \<iinter> (guar g) \<iinter> term)"
proof -
  have a1: "\<forall>s. rely r \<iinter> \<tau>(s) = \<tau>(s)"
    using conj.sync_commute test_rely_conj by auto
  have a2: "{s} \<inter> (r \<squnion> g)\<^sup>*``{s} = {s}"
      by blast              
  have "(rely r) \<iinter> (\<tau>({s}); term; \<tau>((r \<squnion> g)\<^sup>*``{s})) \<ge>
        \<tau>({s});((rely r) \<iinter> (term; \<tau>((r \<squnion> g)\<^sup>*``{s})))" (is "_ \<ge> ?rhs")
    using a1 by (metis rely_seq_distrib seq_assoc)
  also have "?rhs \<ge>  \<tau>({s});((rely r) \<iinter> (term)); \<tau>((r \<squnion> g)\<^sup>*``{s})" (is "_ \<ge> ?rhs")
    using a1 by (metis rely_seq_distrib seq_assoc seq_mono_right)
  also have "?rhs \<ge>  \<tau>({s});((rely r) \<iinter> (guar g) \<iinter> (term)); \<tau>((r \<squnion> g)\<^sup>*``{s})" (is "_ \<ge> ?rhs")
    using a1 chaos_ref_guar conj.sync_mono_left by (meson conj_conjoin_non_aborting seq_mono_left seq_mono_right)
  also have "?rhs =  \<tau>({s});((\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<star>;\<epsilon>(r)\<^sup>\<omega>;(nil \<squnion> \<epsilon>(-r);\<top>)); \<tau>((r \<squnion> g)\<^sup>*``{s})"
    using rely_guar_term by simp
  also have "... =  \<tau>({s});((\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<star>;\<epsilon>(r)\<^sup>\<omega>;(\<tau>((r \<squnion> g)\<^sup>*``{s}) \<squnion> \<epsilon>(-r);\<top>))"
    using nondet_seq_distrib seq_assoc by simp
  also have "... =  \<tau>({s});((\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<star>;\<epsilon>(r)\<^sup>\<omega>;\<tau>((r \<squnion> g)\<^sup>*``{s}) \<squnion> 
                            (\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<star>;\<epsilon>(r)\<^sup>\<omega>;\<epsilon>(-r);\<top>)"
    using par.seq_nondet_distrib seq_assoc by simp
  also have "... \<ge>  \<tau>({s});(\<tau>((r \<squnion> g)\<^sup>*``{s});(\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<star>;\<epsilon>(r)\<^sup>\<omega> \<squnion> 
                            (\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<star>;\<epsilon>(r)\<^sup>\<omega>;\<epsilon>(-r);\<top>)" (is "_ \<ge> ?rhs") 
    using spec_trade_rely_guar_test_pre nondet_mono_left seq_mono_right by metis
  also have "?rhs =  \<tau>({s});((\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<star>;\<epsilon>(r)\<^sup>\<omega> \<squnion> 
                            (\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<star>;\<epsilon>(r)\<^sup>\<omega>;\<epsilon>(-r);\<top>)"
    by (metis a2 par.seq_nondet_distrib seq_assoc test_inf_eq_seq test.hom_inf) 
  also have "... =  \<tau>({s});((\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<star>;\<epsilon>(r)\<^sup>\<omega>);(nil \<squnion> \<epsilon>(-r);\<top>)"
    by (simp add: par.seq_nondet_distrib seq_assoc)
  also have "... =  \<tau>({s});((rely r) \<iinter> (guar g) \<iinter> term)"
    using rely_guar_term seq_assoc by simp
  finally show ?thesis .
qed
*)

lemma pspec_trade_rely_guar: "(rely r) \<iinter> \<lceil>(r \<squnion> g)\<^sup>*\<rceil> \<ge> (rely r) \<iinter> (guar g)"
proof -
  have "(rely r) \<iinter>  \<lceil>(r \<squnion> g)\<^sup>*\<rceil> = (rely r) \<iinter> (\<Squnion>s. (\<tau>({s}); chaos; \<tau>(((r \<squnion> g)\<^sup>*``{s}))))"
    using pspec_def by simp
  also have "... = (\<Squnion>s. (rely r) \<iinter> (\<tau>({s}); chaos; \<tau>(((r \<squnion> g)\<^sup>*``{s}))))"
    using conj.sync_Nondet_distrib by (simp add:image_image)
  also have "... \<ge> (\<Squnion>s. \<tau>({s});((rely r) \<iinter> (guar g)))" (is "_ \<ge> ?rhs")
    using pspec_trade_rely_guar_helper by (meson SUP_mono)
  also have "?rhs = (\<Squnion>s. \<tau>({s}));((rely r) \<iinter> (guar g))"
    by (simp add: NONDET_seq_distrib)
  also have "... = (rely r) \<iinter> (guar g)"
    by (simp add: Nondet_test_nil)
  finally show ?thesis .
qed

lemma spec_trade_rely_guar: "(rely r) \<iinter> \<lparr>(r \<squnion> g)\<^sup>*\<rparr> \<ge> (rely r) \<iinter> (guar g) \<iinter> term"
proof -
  have "(rely r) \<iinter> \<lparr>(r \<squnion> g)\<^sup>*\<rparr> = (rely r) \<iinter> \<lceil>(r \<squnion> g)\<^sup>*\<rceil> \<iinter> term"
    using spec_def conj_assoc by simp
  also have "... \<ge> (rely r) \<iinter> (guar g) \<iinter> term" using pspec_trade_rely_guar
    using pspec_trade_rely_guar conj.sync_mono_left by simp
  finally show ?thesis .
qed

lemma pspec_trading: "(rely r) \<iinter> (guar g) \<iinter> \<lceil>(r \<squnion> g)\<^sup>* \<sqinter> q\<rceil> = (rely r) \<iinter> (guar g) \<iinter> \<lceil>q\<rceil>"
proof (rule antisym)
  have a: "(guar g) \<iinter> (rely r) \<iinter> \<lceil>(r \<squnion> g)\<^sup>* \<sqinter> q\<rceil> = (guar g) \<iinter> ((rely r) \<iinter> \<lceil>(r \<squnion> g)\<^sup>*\<rceil>) \<iinter> \<lceil>q\<rceil>"
    using conj_pspec_pspec conj_assoc by metis
  also have b: "... \<ge> (guar g) \<iinter> ((rely r) \<iinter> (guar g)) \<iinter> \<lceil>q\<rceil>" (is "_ \<ge> ?rhs")
    using pspec_trade_rely_guar conj_assoc conj.sync_mono_left conj_commute conj.sync_mono_right by blast 
  also have "?rhs =  (rely r) \<iinter> (guar g) \<iinter> \<lceil>q\<rceil>"
    using conj_commute conj_assoc conj_idem by simp
  also have "... =  (rely r) \<iinter> (guar g) \<iinter> \<lceil>q\<rceil>"
    using spec_conj_term conj_assoc conj_commute by metis
  finally show "(rely r) \<iinter> (guar g) \<iinter> \<lceil>(r \<squnion> g)\<^sup>* \<sqinter> q\<rceil> \<ge> (rely r) \<iinter> (guar g) \<iinter> \<lceil>q\<rceil>"
    using a b conj_commute by simp
next
  show "(rely r) \<iinter> (guar g) \<iinter> \<lceil>q\<rceil> \<ge> (rely r) \<iinter> (guar g) \<iinter> \<lceil>(r \<squnion> g)\<^sup>* \<sqinter> q\<rceil>"
    using pspec_strengthen conj.sync_mono_right by simp
qed

lemma spec_trading: "(rely r) \<iinter> (guar g) \<iinter> \<lparr>(r \<squnion> g)\<^sup>* \<sqinter> q\<rparr> = (rely r) \<iinter> (guar g) \<iinter> \<lparr>q\<rparr>"
proof -
  have "(rely r) \<iinter> (guar g) \<iinter> \<lparr>(r \<squnion> g)\<^sup>* \<sqinter> q\<rparr> = (rely r) \<iinter> (guar g) \<iinter> \<lceil>(r \<squnion> g)\<^sup>* \<sqinter> q\<rceil> \<iinter> term"
    using spec_def conj_assoc by simp
  also have "... = (rely r) \<iinter> (guar g) \<iinter> \<lceil>q\<rceil> \<iinter> term"
    using pspec_trading by simp
  also have "... = (rely r) \<iinter> (guar g) \<iinter> \<lparr>q\<rparr>"
    using spec_def conj_assoc by simp
  finally show ?thesis .
qed

(*
lemma frame_restrict:
  assumes restrict_set: "Z \<subseteq> X"
  assumes nochange_Y: "Y \<subseteq> negate X"
  assumes rely_nochange_Y: "r \<subseteq> id_set Y"
  shows "(rely r) \<iinter> X:\<^sub>s\<lparr>q \<inter> (id_set Y)\<rparr> \<ge> (rely r) \<iinter> Z:\<^sub>s\<lparr>q\<rparr>"
  sorry
*)

end  
end
