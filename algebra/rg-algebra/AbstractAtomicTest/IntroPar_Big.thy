section \<open>Parallel introduction rules for set-based parallel.\<close>

theory IntroPar_Big
imports
  "IntroPar"
  "../General/Parallel_Big"
begin
                                
locale intro_par_big = intro_par
begin

sublocale big_parallel_distrib conj chaos par skip
proof
qed

(* We need to redeclare the syntax for big parallel because it does not flow
   through in locale instantiations. *)
notation
  Setpar ("\<parallel>\<parallel>_" [1000] 999) and
  Setpar_in ("\<parallel>\<parallel>\<in>_./ _" [51, 10] 10)

lemma pspec_introduce_par_rhs:
  assumes finf: "finite F"
  assumes somef: "F \<noteq> {}"
  shows "(guar(r) \<iinter> (\<parallel>\<parallel>\<in>F. (\<lambda>x. guar(r) \<iinter> rely(r) \<iinter> \<lceil>q x\<rceil>))) \<ge> 
      (\<parallel>\<parallel>\<in>F. (\<lambda>x. (guar(r) \<iinter> rely(r) \<iinter> \<lceil>q x\<rceil>)))"
proof -
  have a0: "guar r \<ge> guar r \<parallel> guar r" using guar_par_idem by simp
  (* Absorb guar(r) *)
  have a1: "(guar(r) \<iinter> (\<parallel>\<parallel>\<in>F. (\<lambda>x. guar(r) \<iinter> rely(r) \<iinter> \<lceil>q x\<rceil>)))
           = (guar(r) \<iinter> (\<parallel>\<parallel>\<in>F. (\<lambda>x. guar(r) \<iinter> (rely(r) \<iinter> \<lceil>q x\<rceil>))))"
    using conj.sync_assoc by metis
  have a2: "... \<ge> (\<parallel>\<parallel>\<in>F. (\<lambda>x. guar(r) \<iinter> (rely(r) \<iinter> \<lceil>q x\<rceil>)))" (is "_ \<ge> ?rhs")
    using conj_setpar_absorb a0 finf somef conj.sync_assoc conj.sync_mono_right by metis
  have a3: "?rhs = (\<parallel>\<parallel>\<in>F. (\<lambda>x. (guar(r) \<iinter> rely(r) \<iinter> \<lceil>q x\<rceil>)))"
    using conj.sync_assoc conj.sync_commute by metis
  show ?thesis using a1 a2 a3 by simp
qed

lemma spec_introduce_par_rhs:
  assumes finf: "finite F"
  assumes somef: "F \<noteq> {}"
  shows "(guar(r) \<iinter> (\<parallel>\<parallel>\<in>F. (\<lambda>x. guar(r) \<iinter> rely(r) \<iinter> \<lparr>q x\<rparr>))) \<ge> 
      (\<parallel>\<parallel>\<in>F. (\<lambda>x. (guar(r) \<iinter> rely(r) \<iinter> \<lparr>q x\<rparr>)))"
proof -
  have a0: "guar r \<ge> guar r \<parallel> guar r" using guar_par_idem by simp
  (* Absorb guar(r) *)
  have a1: "(guar(r) \<iinter> (\<parallel>\<parallel>\<in>F. (\<lambda>x. guar(r) \<iinter> rely(r) \<iinter> \<lparr>q x\<rparr>)))
           = (guar(r) \<iinter> (\<parallel>\<parallel>\<in>F. (\<lambda>x. guar(r) \<iinter> (rely(r) \<iinter> \<lparr>q x\<rparr>))))"
    using conj.sync_assoc by metis
  have a2: "... \<ge> (\<parallel>\<parallel>\<in>F. (\<lambda>x. guar(r) \<iinter> (rely(r) \<iinter> \<lparr>q x\<rparr>)))" (is "_ \<ge> ?rhs")
    using conj_setpar_absorb a0 finf somef conj.sync_assoc conj.sync_mono_right by metis
  have a3: "?rhs = (\<parallel>\<parallel>\<in>F. (\<lambda>x. (guar(r) \<iinter> rely(r) \<iinter> \<lparr>q x\<rparr>)))"
    using conj.sync_assoc conj.sync_commute by metis
  show ?thesis using a1 a2 a3 by simp
qed
  
  
lemma pspec_introduce_par_big:
  "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow>(rely r) \<iinter> \<lceil>\<Sqinter>x\<in>A. (q x)\<rceil> \<ge> (\<parallel>\<parallel>\<in>A. (\<lambda>x. guar(r) \<iinter> rely(r) \<iinter> \<lceil>q x\<rceil>))"
proof (induct A rule: finite_ne_induct)
  fix x
  have "(rely r) \<iinter> \<lceil>q x\<rceil> \<ge> rely(r) \<iinter> \<lceil>q x\<rceil>" 
    by (simp add: conj.sync_commute conj.sync_mono_right)
  also have "... = chaos \<iinter> rely(r) \<iinter> \<lceil>q x\<rceil>" 
    by (simp)
  also (xtrans) have "... \<ge> guar(r) \<iinter> rely(r) \<iinter> \<lceil>q x\<rceil>" 
    using conj.sync_mono_left chaos_ref_guar by blast
  finally show "(rely r) \<iinter> \<lceil>\<Sqinter>x\<in>{x}. (q x)\<rceil> \<ge> (\<parallel>\<parallel>\<in>{x}. (\<lambda>x. guar(r) \<iinter> rely(r) \<iinter> \<lceil>q x\<rceil>))" 
    by (simp)
next
  fix x F
  assume finf: "finite F"
    and somef: "F \<noteq> {}"
    and newx: "x \<notin> F"
    and step: "(rely r) \<iinter> \<lceil>\<Sqinter>x\<in>F. (q x)\<rceil> \<ge> (\<parallel>\<parallel>\<in>F. (\<lambda>x. guar(r) \<iinter> rely(r) \<iinter> \<lceil>q x\<rceil>))"
  
  have a1: "(rely r) \<iinter> \<lceil>q x \<sqinter> (\<Sqinter>x\<in>F. (q x))\<rceil> = (rely r) \<iinter> \<lceil>q x\<rceil> \<iinter> (rely r) \<iinter> \<lceil>\<Sqinter>x\<in>F. (q x)\<rceil>"
    using conj.sync_assoc conj_conj_distrib_left conj_pspec_pspec by metis
  have a2: "... \<ge> (guar(r) \<iinter> rely(r) \<iinter> \<lceil>q x\<rceil>) \<parallel> 
                   (guar(r) \<iinter> rely(r) \<iinter> \<lceil>\<Sqinter>x\<in>F. (q x)\<rceil>)"
    using pspec_introduce_par a1 sup_inf_absorb by metis
  
  (* Apply induction hypothesis *)
  have rhs1: "(guar(r) \<iinter> rely(r) \<iinter> \<lceil>\<Sqinter>x\<in>F. (q x)\<rceil>)
            \<ge> (guar(r) \<iinter> (\<parallel>\<parallel>\<in>F. (\<lambda>x. guar(r) \<iinter> rely(r) \<iinter> \<lceil>q x\<rceil>)))" (is "_ \<ge> ?rhs")
    using conj.sync_mono_right conj_assoc step by auto
  have rhs2: "?rhs \<ge> (\<parallel>\<parallel>\<in>F. (\<lambda>x. (guar(r) \<iinter> rely(r) \<iinter> \<lceil>q x\<rceil>)))"
    using pspec_introduce_par_rhs finf somef by simp
      
  have a3: "(guar(r) \<iinter> rely(r) \<iinter> \<lceil>q x\<rceil>) \<parallel> (guar(r) \<iinter> rely(r) \<iinter> \<lceil>\<Sqinter>x\<in>F. (q x)\<rceil>) \<ge>
            (guar(r) \<iinter> rely(r) \<iinter> \<lceil>q x\<rceil>) \<parallel> (\<parallel>\<parallel>\<in>F. (\<lambda>x. (guar(r) \<iinter> rely(r) \<iinter> \<lceil>q x\<rceil>)))" (is "_ \<ge> ?rhs")
    using rhs1 rhs2 par.sync_mono_right by simp
  then have a4: "?rhs = (\<parallel>\<parallel>\<in>(insert x F). (\<lambda>x. (guar(r) \<iinter> rely(r) \<iinter> \<lceil>q x\<rceil>)))"
    using finf newx by simp
  then show "(rely r) \<iinter> \<lceil>(\<Sqinter>x\<in>(insert x F). (q x))\<rceil> 
              \<ge> (\<parallel>\<parallel>\<in>(insert x F). (\<lambda>x. (guar(r) \<iinter> rely(r) \<iinter> \<lceil>q x\<rceil>)))"
    using a1 a2 a3 a4 by simp
qed

lemma par_big_conj_term_distrib: "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> (\<parallel>\<parallel>\<in>A. f) \<iinter> term \<ge> (\<parallel>\<parallel>\<in>A. (\<lambda>x. f x \<iinter> term))"
proof (induct A rule: finite_ne_induct)
  case (singleton x)
  then show ?case by simp
next
  case (insert x F)
  have "(\<parallel>\<parallel>\<in>insert x F. (\<lambda>x. f x \<iinter> term)) = (\<parallel>\<parallel>\<in>F. (\<lambda>x. f x \<iinter> term)) \<parallel> (f x \<iinter> term)"
    using insert.hyps(1) insert.hyps(3) par_commute by simp
  also have "... \<le> ((\<parallel>\<parallel>\<in>F. f) \<iinter> term) \<parallel> (f x \<iinter> term)"
    using insert.hyps(4) par.sync_mono_left by simp
  also have "... \<le> ((\<parallel>\<parallel>\<in>F. f) \<parallel> f x) \<iinter> (term \<parallel> term)"
    using par.comm.left_commute par_conj_interchange by simp
  also have "... = (\<parallel>\<parallel>\<in>insert x F. f) \<iinter> (term \<parallel> term)"
    using insert.hyps(1) insert.hyps(3) par_commute by simp
  also have "... = (\<parallel>\<parallel>\<in>insert x F. f) \<iinter> term"
    using par_term_term par_assoc by simp
  finally show ?case .
qed

lemma spec_introduce_par_big:
  "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow>(rely r) \<iinter> \<lparr>\<Sqinter>x\<in>A. (q x)\<rparr> \<ge> (\<parallel>\<parallel>\<in>A. (\<lambda>x. guar(r) \<iinter> rely(r) \<iinter> \<lparr>q x\<rparr>))"
proof -
  assume "finite A"
  assume "A \<noteq> {}"
  have "(rely r) \<iinter> \<lparr>\<Sqinter>x\<in>A. (q x)\<rparr> = ((rely r) \<iinter> \<lceil>\<Sqinter>x\<in>A. (q x)\<rceil>) \<iinter> term"
    using spec_def conj_assoc by simp
  also have "... \<ge> (\<parallel>\<parallel>\<in>A. (\<lambda>x. guar(r) \<iinter> rely(r) \<iinter> \<lceil>q x\<rceil>)) \<iinter> term" (is "_ \<ge> ?rhs")
    using pspec_introduce_par_big \<open>finite A\<close> \<open>A \<noteq> {}\<close> conj.sync_mono_left setpar.cong by blast
  also have "?rhs \<ge> (\<parallel>\<parallel>\<in>A. (\<lambda>x. guar(r) \<iinter> rely(r) \<iinter> \<lceil>q x\<rceil> \<iinter> term))" (is "_ \<ge> ?rhs") 
    using \<open>A \<noteq> {}\<close> \<open>finite A\<close> par_big_conj_term_distrib by simp
  also have "?rhs = (\<parallel>\<parallel>\<in>A. (\<lambda>x. guar(r) \<iinter> rely(r) \<iinter> \<lparr>q x\<rparr>))"
    using spec_def conj_assoc by simp
  finally show ?thesis .
qed

end

end
