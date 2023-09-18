section \<open>Operators and lemmas for dealing with relations\<close>

theory Relations
imports
    Main
begin

(* Why was this a locale? 
locale extended_relations
begin *)

(* Convenience definitions to help constrain domain and range of relations. *)
abbreviation domain_restriction :: "'a set \<Rightarrow> 'a rel" where
  "domain_restriction p \<equiv> ({(x::'a, y::'a). x \<in> p}::'a rel)"
abbreviation range_restriction :: "'a set \<Rightarrow> 'a rel" where
  "range_restriction p \<equiv> ({(x::'a, y::'a). y \<in> p}::'a rel)"

lemma range_restrict_range: 
  assumes "(a, b) \<in> (range_restriction p)"
  shows "b \<in> p"
proof -
  have "(a,b) \<in> ({(x::'a, y::'a). y \<in> p}::'a rel)" using assms by simp
  then have "b \<in> p" by simp
  then show ?thesis .
qed
  
definition restrict_domain :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a rel" (infixr "\<triangleleft>" 101)
  where "restrict_domain p r = (domain_restriction p) \<inter> r"
definition restrict_range :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a rel" (infixl "\<triangleright>" 100)
  where "restrict_range r p = r \<inter> (range_restriction p)" 
    
lemma restrict_domain_range_assoc:
  shows "(p1 \<triangleleft> q1) \<triangleright> p2 = p1 \<triangleleft> (q1 \<triangleright> p2)"
    by (simp add: restrict_domain_def restrict_range_def inf_assoc)
    
lemma range_restrict_relcomp: 
  shows "q1 O (q2 \<triangleright> p) = (q1 O q2) \<triangleright> p"
proof -
  have "q1 O (q2 \<triangleright> p) = (q1 O q2) \<inter> (range_restriction p)"
    using restrict_range_def by auto
  then show ?thesis using restrict_range_def by metis
qed

lemma domain_restrict_relcomp: 
  shows "(p \<triangleleft> q1) O q2 = p \<triangleleft> (q1 O q2)"
proof -
  have "(p \<triangleleft> q1) O q2 = (domain_restriction p) \<inter> (q1 O q2)"
    using restrict_domain_def by auto
  then show ?thesis using restrict_domain_def by metis
qed

lemma domain_restrict_q_mono:
  assumes "q1 \<subseteq> q2"
  shows "p \<triangleleft> q1 \<subseteq> p \<triangleleft> q2"
proof -
  have "domain_restriction p \<inter> q1 \<subseteq> domain_restriction p \<inter> q2"
    using assms by auto
  then show ?thesis using restrict_domain_def by metis
qed

lemma range_restrict_q_mono:
  assumes "q1 \<subseteq> q2"
  shows "q1 \<triangleright> p \<subseteq> q2 \<triangleright> p"
proof -
  have "q1 \<inter> range_restriction p \<subseteq> q2 \<inter> range_restriction p"
    using assms by auto
  then show ?thesis using restrict_range_def by metis
qed

lemma domain_restrict_p_mono:
  assumes "p1 \<subseteq> p2"
  shows "p1 \<triangleleft> q \<subseteq> p2 \<triangleleft> q"
proof -
  have "domain_restriction p1 \<inter> q \<subseteq> domain_restriction p2 \<inter> q"
    using assms by blast 
  then show ?thesis using restrict_domain_def by metis
qed

lemma range_restrict_p_mono:
  assumes "p1 \<subseteq> p2"
  shows "q \<triangleright> p1 \<subseteq> q \<triangleright> p2"
proof -
  have "q \<inter> range_restriction p1 \<subseteq> q \<inter> range_restriction p2"
    using assms by blast 
  then show ?thesis using restrict_range_def by metis
qed

lemma domain_restrict_remove:
  "p \<triangleleft> r \<subseteq> r"
  by (simp add: restrict_domain_def)

lemma domain_restrict_twice:
  "p1 \<triangleleft> p2 \<triangleleft> r = (p1 \<inter> p2) \<triangleleft> r"
proof -
  have dom_int: "domain_restriction p1 \<inter> domain_restriction p2 = domain_restriction (p1 \<inter> p2)"
  proof -
    have a: "domain_restriction p1 \<inter> domain_restriction p2 = {(x, y). x \<in> p1} \<inter> {(x, y). x \<in> p2}"
      by simp
    also have b: "\<dots> = {(x,y). (x,y) \<in> {(x, y). x \<in> p1} \<and> (x,y) \<in> {(x, y). x \<in> p2}}"
      using Int_def by auto 
    show ?thesis by (simp add: b) 
  qed

  have "p1 \<triangleleft> p2 \<triangleleft> r = domain_restriction p1 \<inter> domain_restriction p2 \<inter> r"
    by (simp add: restrict_domain_def inf_assoc)
  also have b: "\<dots> = domain_restriction (p1 \<inter> p2) \<inter> r"
    using dom_int by auto 
  show ?thesis using b restrict_domain_def calculation by auto 
qed

lemma range_restrict_twice:
  "r \<triangleright> p1 \<triangleright> p2 = r \<triangleright> (p1 \<inter> p2)"
proof -
  have range_int: "range_restriction p1 \<inter> range_restriction p2 = range_restriction (p1 \<inter> p2)"
  proof -
    have a: "range_restriction p1 \<inter> range_restriction p2 = {(x, y). y \<in> p1} \<inter> {(x, y). y \<in> p2}"
      by simp
    also have b: "\<dots> = {(x,y). (x,y) \<in> {(x, y). y \<in> p1} \<and> (x,y) \<in> {(x, y). y \<in> p2}}"
      using Int_def by auto 
    show ?thesis by (simp add: b) 
  qed

  have "r \<triangleright> p1 \<triangleright> p2 = r \<inter> range_restriction p1 \<inter> range_restriction p2"
    by (simp add: restrict_range_def inf_assoc)
  also have b: "\<dots> = r \<inter> range_restriction (p1 \<inter> p2)"
    using range_int by auto 
  show ?thesis using b restrict_range_def calculation by auto 
qed

lemma mid_domain_to_range:
  shows "q1 O (p \<triangleleft> q2) = (q1 \<triangleright> p) O q2"
proof -
  have expand: "(\<And>x z. (x,z) \<in> q1 O (p \<triangleleft> q2) \<longleftrightarrow> (x,z) \<in> (q1 \<triangleright> p) O q2)"
  proof -
    fix x z
    have r1: "(x,z) \<in> q1 O (p \<triangleleft> q2) \<longleftrightarrow> (\<exists>y. (x,y) \<in> q1 \<and> (y,z) \<in> (p \<triangleleft> q2))"
      by blast
    have r2: "\<dots> \<longleftrightarrow> (\<exists>y. (x,y) \<in> q1 \<and> y \<in> p \<and> (y,z) \<in> q2)"
      by (simp add: restrict_domain_def)
    have r3: "\<dots> \<longleftrightarrow> (\<exists>y. (x,y) \<in> (q1 \<triangleright> p) \<and> (y,z) \<in> q2)"
      by (simp add: restrict_range_def)
    have r4: "\<dots> \<longleftrightarrow> (x,z) \<in> (q1 \<triangleright> p) O q2"
      by (simp add: relcomp.simps)
    show "(x,z) \<in> q1 O (p \<triangleleft> q2) \<longleftrightarrow> (x,z) \<in> (q1 \<triangleright> p) O q2"
      by (simp add: r1 r2 r3 r4)
  qed
  show ?thesis using expand by blast 
qed

lemma id_maintains_pre:
  assumes "p1 \<subseteq> p2"
  shows "p1 \<triangleleft> Id \<subseteq> Id \<triangleright> p2"
  apply(unfold restrict_domain_def restrict_range_def)
  apply clarsimp
  using assms by auto

(* Definition 1 *)
(* p is be stable under r, if for all p, taking a step
   according to r, leaves us in a state in p *)
definition stable :: "'c set\<Rightarrow>'c rel\<Rightarrow>bool" where
  (* (r `` p) refers to the the image of p in r *)
  "(stable p r) = ((r `` p) \<subseteq> p)"

lemma stable_inter: 
  assumes stable_p1: "stable p1 r"
  assumes stable_p2: "stable p2 r"
  shows "stable (p1 \<inter> p2) r"
proof -
  have "r``(p1 \<inter> p2) \<subseteq> r``p1 \<inter> r``p2"
    by blast
  also have s: "\<dots> \<subseteq> p1 \<inter> p2"
    using stable_p1 stable_p2 stable_def
    by (metis inf_mono)
  show ?thesis using stable_def
    by (metis calculation s subset_trans)
qed

lemma stable_relcomp:
  assumes stable_r1: "stable p r1"
  assumes stable_r2: "stable p r2"
  shows "stable p (r1 O r2)"
proof -
  have "(r1 O r2)``p = r2``(r1``p)"
    by (simp add: relcomp_Image)
  also have x: "\<dots> \<subseteq> p"
    using stable_r1 stable_r2
    by (meson Image_subset_eq stable_def order_trans)
  show ?thesis
    by (simp add: calculation stable_def x)
qed

lemma stable_maintains_invariant:
  assumes "stable p r"
  shows "p \<triangleleft> r = (p \<triangleleft> r) \<triangleright> p"
  using assms unfolding restrict_domain_def stable_def restrict_range_def by auto

(* If we can partition the state space into k partitions, each of which 
   is stable under r, then not being in a specific partition k is also stable,
   and vica-versa *)
lemma stable_eq_stable_neq:
  shows "(\<forall>x. (stable {s. p s = x} r)) = (\<forall>x. (stable  {s. (p s \<noteq> x)} r))"
proof (rule iffI)
  show "\<forall>x. (stable {s. p s = x} r) \<Longrightarrow> \<forall>x. (stable  {s. (p s \<noteq> x)} r)"
  proof 
    fix x' 
    assume a1: "\<forall>x. (stable {s. p s = x} r)"
    show "stable {s. p s \<noteq> x'} r"
      unfolding stable_def proof (auto)
      fix a b
      assume b1: "(a, b) \<in> r"
      obtain ax where b2: "a \<in> {s. p s = ax}" by fastforce
      then have b3: "b \<in> {s. p s = ax}" using a1 b1 unfolding stable_def by auto    
      moreover assume b4: "p a \<noteq> p b"
      then have b5: "b \<notin> {s. p s = ax}" using b2 by auto
      show "False" using b3 b5 by simp
    qed
  qed
next
  show "\<forall>x. (stable {s. (p s \<noteq> x)} r) \<Longrightarrow> \<forall>x. (stable  {s. p s = x} r)"
  proof
    fix x' 
    assume a1: "\<forall>x. (stable {s. p s \<noteq> x} r)"
    show "stable {s. p s = x'} r"
      unfolding stable_def proof (auto)
      fix a b
      assume b1: "(a, b) \<in> r"
      then have "\<forall>x. x \<noteq> (p a) \<longrightarrow> a \<in> {s. p s \<noteq> x}" by fastforce
      then have "\<forall>x. x \<noteq> (p a) \<longrightarrow> b \<in> {s. p s \<noteq> x}" using b1 a1 unfolding stable_def by fastforce
      then have "b \<in> {s. p s = p a}" by blast
      then show "p b = p a" by blast
    qed
  qed
qed

lemma stable_eq_stable_neq2:
  shows "(\<forall>x. (stable {s. p s = x} r)) = (\<forall>x. (stable (-{s. (p s = x)}) r))"
proof -
  have "\<And>p x. {s. p s \<noteq> x} = -{s. p s = x}" by auto
  then show ?thesis using stable_eq_stable_neq by metis
qed


(* Lemmas about intereference, and tolerating interference. *)
lemma stable_rtrancl_helper:
  assumes r_maintains_p: "stable p r"
  shows "(x,y)\<in>(r\<^sup>*) \<Longrightarrow> x \<in> p \<Longrightarrow> (y \<in> p)"
proof  (induction rule:rtrancl_induct)
  case base
  then show ?case by simp
next
  case (step a b)
  then have "(a,b) \<in> (p \<triangleleft> r)" unfolding restrict_domain_def by auto
  then have "b \<in> p" using r_maintains_p unfolding stable_def restrict_domain_def by auto
  then show ?case .
qed

lemma stable_rtrancl:
  assumes r_maintains_p: "stable p r"
  shows "stable p (r\<^sup>*)"
    using stable_rtrancl_helper
          r_maintains_p unfolding stable_def by auto
      
lemma stable_rtrancl_relcomp:
  assumes r_maintains_p: "stable p r"
  shows "p \<triangleleft> ((r\<^sup>*) O q) = p \<triangleleft> ((r\<^sup>*) O (p \<triangleleft> q))"
proof -
  have a1: "p \<triangleleft> r\<^sup>* = p \<triangleleft> r\<^sup>* \<inter> range_restriction p"
    using stable_rtrancl r_maintains_p 
        unfolding stable_def restrict_domain_def by auto  
  then have "p \<triangleleft> ((r\<^sup>*) O q) = p \<triangleleft> ((r\<^sup>*) O (p \<triangleleft> q))"
    unfolding restrict_domain_def by auto
  then show ?thesis .
qed

lemma stable_rtrancl_relcomp_subset:
  assumes "p1 \<subseteq> p2"
  assumes r_maintains_p: "stable p2 r"
  shows "p1 \<triangleleft> ((r\<^sup>*) O q) = p1 \<triangleleft> ((r\<^sup>*) O (p2 \<triangleleft> q))"
  using stable_rtrancl_relcomp
  by (metis assms(1) domain_restrict_twice inf.orderE r_maintains_p) 

(*
lemma rrtrancl_maintains_p_relcomp:
  assumes r_maintains_p: "p \<triangleleft> r \<subseteq> range_restriction p"
  shows "p \<triangleleft> ((r\<^sup>* ) O q) = p \<triangleleft> ((r\<^sup>* ) O (p \<triangleleft> q))"
proof -
  have "p \<triangleleft> ((r\<^sup>* ) O q) = (p \<triangleleft> r\<^sup>* ) O q"
    using domain_restrict_relcomp by metis
  also have "... =  (p \<triangleleft> (r\<^sup>* ) \<inter> range_restriction p) O q"
    using r_maintains_p stable_rtrancl stable_rtrancl_relcomp 
  also have "... =  ((domain_restriction p) \<inter> (r\<^sup>* \<inter> range_restriction p)) O q"
    using restrict_domain_def by auto
  also have "... = (domain_restriction p) \<inter> ((r\<^sup>* ) O ((domain_restriction p) \<inter> q))"
    using domain_restrict_relcomp by auto
  finally show ?thesis using restrict_domain_def by metis
qed
*)

definition tolerates_interference :: "'c set\<Rightarrow>'c rel\<Rightarrow>'c rel\<Rightarrow>bool" where
  "(tolerates_interference p q r) \<equiv> (stable p r) \<and>
                                    (p \<triangleleft> (r O q) \<subseteq> q) \<and>
                                    (p \<triangleleft> (q O r) \<subseteq> q)"

lemma tolerates_interference_restict_pre:
  assumes tolerate: "tolerates_interference p q r"
  assumes stable: "stable (p \<inter> p') r"
  shows "tolerates_interference (p \<inter> p') q r"           
proof -
  have "stable (p \<inter> p') r" using stable by simp
  moreover have "((p \<inter> p') \<triangleleft> (r O q) \<subseteq> q)"
    using tolerate unfolding tolerates_interference_def restrict_domain_def by auto
  moreover have "((p \<inter> p') \<triangleleft> (q O r) \<subseteq> q)"
    using tolerate unfolding tolerates_interference_def restrict_domain_def by auto
  ultimately show ?thesis unfolding tolerates_interference_def by simp
qed
  
lemma tolerates_interference_restict_post:
  assumes tolerate: "tolerates_interference p q r"
  assumes stable: "stable p' r"
  shows "tolerates_interference p (q \<triangleright> p') r"
proof -
  have "p \<triangleleft> (r O q) \<subseteq> q"
    using tolerate unfolding tolerates_interference_def by auto
  then have a1: "p \<triangleleft> (r O (q \<triangleright> p')) \<subseteq> (q \<triangleright> p')"
    unfolding restrict_domain_def restrict_range_def by auto
  have "p \<triangleleft> (q O r) \<subseteq> q"
    using tolerate unfolding tolerates_interference_def by auto
  then have a2: "p \<triangleleft> ((q \<triangleright> p') O r) \<subseteq> (q \<triangleright> p')"
    using stable unfolding stable_def restrict_domain_def restrict_range_def by auto
  show ?thesis using tolerate a1 a2 unfolding tolerates_interference_def by simp
qed


lemma stable_rtrancl2:
  assumes tolerates_interference: "tolerates_interference p q r"
  shows "stable p (r\<^sup>*)"
    using stable_rtrancl tolerates_interference
    unfolding tolerates_interference_def stable_def 
              restrict_range_def restrict_domain_def by auto

lemma q_tolerates_rtrancl_left_helper:
  assumes tolerates_interference: "tolerates_interference p q r"
  shows "(x,y)\<in>(rtrancl r) \<Longrightarrow> x \<in> p \<Longrightarrow> (y,z) \<in> q \<Longrightarrow> (x,z) \<in> q"
proof (induction rule:rtrancl_induct)
  case base
  then show ?case by simp
next
  case step:(step a b)
  then have "(x,a) \<in> (p \<triangleleft> (r\<^sup>*))" unfolding restrict_domain_def by auto
  then have "a \<in> p" using stable_rtrancl tolerates_interference 
      unfolding tolerates_interference_def stable_def restrict_domain_def by auto
  then have "(a,z) \<in> (p \<triangleleft> (r O q))" using step restrict_domain_def by auto
  then have "(a,z) \<in> q" using tolerates_interference unfolding tolerates_interference_def by auto
  then have "(x,z) \<in> q" using step by simp
  then show ?case .
qed
  
lemma q_tolerates_rtrancl_left:  
  assumes tolerates_interference: "tolerates_interference p q r"
  shows "p \<triangleleft> ((r\<^sup>*) O (q)) \<subseteq> q"
  using q_tolerates_rtrancl_left_helper tolerates_interference
    unfolding restrict_domain_def by auto

lemma q_tolerates_rtrancl_right_helper:
  assumes tolerates_interference: "tolerates_interference p q r"
  shows "(y,z)\<in>(r\<^sup>*) \<Longrightarrow> (x,y) \<in> q \<Longrightarrow> x \<in> p \<Longrightarrow> (x,z) \<in> q"
proof  (induction rule:rtrancl_induct)
  case base
  then show ?case by simp
next
  case step:(step a b)
  then have "(x,a) \<in> q \<and> x \<in> p" by simp
  then have "(x,b) \<in> q" using step tolerates_interference restrict_domain_def
       unfolding tolerates_interference_def by blast
  then show ?case .
qed

lemma q_tolerates_rtrancl_right:
  assumes tolerates_interference: "tolerates_interference p q r"
  shows "p \<triangleleft> (q O r\<^sup>*) \<subseteq> q"
  using q_tolerates_rtrancl_right_helper tolerates_interference
    unfolding restrict_domain_def by auto

lemma q_tolerates_rtrancl:
  assumes tolerates_interference: "tolerates_interference p q r"
  shows "p \<triangleleft> ((r\<^sup>*) O q O (r\<^sup>*)) \<subseteq> q"
  using q_tolerates_rtrancl_right_helper tolerates_interference
proof -
  have "p \<triangleleft> ((r\<^sup>*) O q O (r\<^sup>*)) = p \<triangleleft> ((r\<^sup>*) O (p \<triangleleft> (q O r\<^sup>*)))"
    using stable_rtrancl_relcomp tolerates_interference 
    unfolding tolerates_interference_def by auto
  also have "... \<subseteq> p \<triangleleft> ((r\<^sup>*) O q)"
    using q_tolerates_rtrancl_right tolerates_interference
    unfolding restrict_domain_def by blast       
  also have "... \<subseteq> q"
    using q_tolerates_rtrancl_left tolerates_interference
    unfolding restrict_domain_def by blast 
  finally show ?thesis .
qed

lemma rtrancl_inter_rtrancl:
  shows "(a\<^sup>* \<inter> b\<^sup>*) = (a\<^sup>* \<inter> b\<^sup>*)\<^sup>*"
proof -
  have "trans (a\<^sup>* \<inter> b\<^sup>*)" by (simp add: trans_Int trans_rtrancl)
  moreover have "refl (a\<^sup>* \<inter> b\<^sup>*)" using refl_on_Int refl_rtrancl by fastforce
  ultimately show ?thesis using trancl_reflcl 
    by (metis (full_types) rtrancl_reflcl_absorb sup_inf_distrib2 trancl_id)
qed

end