theory findP2                           
  imports "programming_constructs_extended"
begin

locale findP = programming_constructs_extended +
  constrains test :: "'state set \<Rightarrow> 'a"
              and pgm :: "'state rel \<Rightarrow> 'a"
              and env :: "'state rel \<Rightarrow> 'a"
              and get_var :: "'varname \<Rightarrow> 'state \<Rightarrow> nat"
              and lib :: "'varname \<Rightarrow> 'a \<Rightarrow> 'a"
              and lib_bool :: "'varname \<Rightarrow> 'state rel \<Rightarrow> 'state rel"
  fixes v :: "nat \<Rightarrow> 'd" and
           Pr :: "'d \<Rightarrow> bool" and
           N :: "nat" 
begin

definition 
P :: "nat \<Rightarrow> bool" where
"P i \<equiv> (i < N) \<longrightarrow> (Pr (v i))"

definition
even :: "nat set" where
"even = {k. k mod 2 = 0 \<and> k \<le> N + 1}"

definition                     
odd :: "nat set" where
"odd = {k. k mod 2 = 1 \<and> k \<le> N + 1}"

definition
nats :: "nat set" where
"nats = {k. k \<le> N + 1}"

definition
minP :: "nat set \<Rightarrow> nat" where
"minP S = Min {i | i. i \<in> S \<and> (P i)}"

definition inv :: "nat \<Rightarrow> nat set \<Rightarrow> bool " where
  "inv st S \<equiv> ((st \<noteq> N) \<longrightarrow> (st = (minP S)))"

lemma even_union_odd : "even \<union> odd = nats"
  unfolding odd_def nats_def even_def by auto

lemma joining_min : 
  assumes "finite S" and "finite T" and "S \<noteq> {}" and "T \<noteq> {}"
  shows "min (Min S) (Min T) = Min (S \<union> T)"
  by (simp add: Min.union assms(1) assms(2) assms(3) assms(4))

lemma even_non_empty :  
  shows "{i |i. i \<in> even \<and> P i} \<noteq> {}"
proof (cases "N mod 2 = 0") 
  case True
  then have "N \<in> {i |i. i \<in> even \<and> P i}" unfolding even_def P_def by auto
  thus ?thesis by auto
next
  case False
  then have "(N + 1) \<in> {i |i. i \<in> even \<and> P i}" 
    unfolding even_def P_def by (auto, presburger)
  thus ?thesis by auto
qed

lemma odd_non_empty :
  shows "{i |i. i \<in> odd \<and> P i} \<noteq> {}"
proof (cases "N mod 2 = 1") 
  case True
  then have "N \<in> {i |i. i \<in> odd \<and> P i}" unfolding odd_def P_def by auto
  thus ?thesis by auto
next
  case False
  then have "(N + 1) \<in> {i |i. i \<in> odd \<and> P i}" unfolding odd_def P_def by auto
  thus ?thesis by auto
qed

lemma finite_even : " finite {i | i. i \<in> even \<and> (P i)}"
  unfolding even_def by auto

lemma finite_odd : "finite {i | i. i \<in> odd \<and> (P i)}"
  unfolding odd_def by auto

lemma containment :
  assumes "l = Min S" and "finite S" and "S \<noteq> {}"
  shows "l \<in> S"
  using assms by simp

lemma minP_even_upper_bound : 
  shows "minP even \<le> N + 1"
proof -
  have "\<forall> e \<in> {i |i. i \<in> even \<and> P i}. e \<le> N + 1" 
    unfolding even_def by auto
  then show "minP even \<le> N + 1" 
    unfolding minP_def using finite_even even_non_empty Min_in by auto
qed

lemma minP_odd_upper_bound :
  shows "minP odd \<le> N + 1"
proof -
  have "\<forall> e \<in> {i |i. i \<in> odd \<and> P i}. e \<le> N + 1"
    unfolding odd_def by auto
  then show "minP odd \<le> N + 1" 
    unfolding minP_def using finite_odd odd_non_empty Min_in by auto
qed

lemma minP_even_upper_bound_restrict :
  assumes "(minP even) \<le> (minP odd)"
  shows "minP even \<le> N"
proof (rule ccontr)
  assume "\<not>(minP even \<le> N)"
  then have minP_value : "minP even = N + 1" 
    using minP_even_upper_bound by simp
  then have "N + 1 \<in> {i |i. i \<in> even \<and> P i}"
    unfolding minP_def using finite_even even_non_empty containment by fastforce
  then have "(N + 1) mod 2 = 0" unfolding even_def by auto
  moreover have "(N + 1) mod 2 = 1"
  proof -
    have "minP odd = N + 1" 
      using minP_odd_upper_bound assms minP_value by simp
    then have "N + 1 \<in> {i |i. i \<in> odd \<and> P i}" 
      unfolding minP_def using containment finite_odd odd_non_empty by metis
    then show ?thesis unfolding odd_def by auto
  qed
  ultimately show "False" by simp
qed

lemma minP_odd_upper_bound_restrict :
  assumes odd_le_even : "(minP odd) \<le> (minP even)"
  shows "minP odd \<le> N"
proof (rule ccontr)
  assume "\<not>(minP odd \<le> N)"
  then have minP_value : "minP odd = N + 1" 
    using minP_odd_upper_bound by simp
  then have "N + 1 \<in> {i |i. i \<in> odd \<and> P i}" 
    unfolding minP_def using containment finite_odd odd_non_empty  by metis
  then have "N + 1 \<in> odd" by simp
  then have "(N + 1) mod 2 = 1" unfolding odd_def by auto
  moreover have "(N + 1) mod 2 = 0"
  proof -
    have "minP even = N + 1" 
      using minP_even_upper_bound odd_le_even minP_value by simp
    then have "N + 1 \<in> {i |i. i \<in> even \<and> P i}" 
      unfolding minP_def using containment finite_even even_non_empty by metis
    then have "N + 1 \<in> even" by simp
    then show ?thesis unfolding even_def by auto
  qed
  ultimately show "False" by simp
qed

lemma ot_equals_N :
  assumes m_ot : "inv (ot m') odd" and ot_false : "(ot m') \<noteq> minP odd"
  shows "(ot m') = N"
  using assms unfolding inv_def by blast

lemma et_equals_N :
  assumes m_et : "inv (et m') even" and et_false : "(et m') \<noteq> minP even"
  shows "(et m') = N"
  using assms unfolding inv_def by blast

lemma joining_minP :
  shows "min (minP even) (minP odd) = minP (even \<union> odd)"
proof -
  have "{i |i. i \<in> even \<and> P i} \<union> {i |i. i \<in> odd \<and> P i} = {i |i. i \<in> even \<union> odd \<and> P i}" by auto
  moreover have "min (minP even) (minP odd) = 
        Min ({i |i. i \<in> even \<and> P i} \<union> {i |i. i \<in> odd \<and> P i})" 
    unfolding minP_def using finite_even finite_odd odd_non_empty 
      even_non_empty joining_min by fastforce
  ultimately show ?thesis unfolding minP_def by simp
qed

definition local_sets :: "'varname \<Rightarrow> 'state set \<Rightarrow> 'state set" where
  "local_sets x p = id_bar {|x|} `` p"

lemma "X \<noteq> {} \<Longrightarrow> c ; (\<Squnion>x\<in>X. d x) = (\<Squnion>x\<in>X. c ; d x)"
  by (simp add: par.seq_NONDET_distrib)

lemma introduce_var_init :
  assumes single_ref: "single_reference e r"
  assumes tolerates: "tolerates_interference p\<^sub>1 q r"
  assumes free: "\<And>s. \<And>k. eval e s = eval e (set_var x k s)"
  assumes "\<And>s. (expr_eq e (get_var x s) \<inter> (local_sets x p\<^sub>1)) \<subseteq> (local_sets x p\<^sub>2)"
  shows "(rely r) \<iinter> (guar ((E\<^sup>R\<^sub>x g) \<inter> {(s, s'). get_var x s = get_var x s'})) \<iinter> \<lbrace>p\<^sub>1\<rbrace>;Y:\<^sub>s\<lparr>E\<^sup>R\<^sub>x q\<rparr> \<ge> 
        (var x . x ::= e);(rely ((E\<^sup>R\<^sub>x r) \<inter> {(s, s'). get_var x s = get_var x s'})) \<iinter> (guar g) \<iinter> \<lbrace>p\<^sub>2\<rbrace>;({|x|} |\<union>| Y):\<^sub>s\<lparr>q\<rparr>"
proof -
  have a: "\<And>k. \<lbrakk>e\<rbrakk>k \<ge> idle;\<lbrakk>e\<rbrakk>k" 
  proof (induct e)
    case (Constant x)
    then show ?case
    proof -
      have "\<lbrakk>Constant x\<rbrakk>k = idle ; \<lbrakk>Constant x\<rbrakk>k"
        by (metis (no_types) expr_cmd.simps(1) idle_seq_idle seq_assoc)
      then show ?thesis
        by (simp add: idle_seq_idle seq_assoc)
    qed 
  next
    case (Variable x)
    then show ?case
    proof -
      have "\<forall>a. idle ; (idle ; a) = idle ; a"
        by (metis idle_seq_idle seq_assoc)
      then show ?thesis
        by (simp add: idle_seq_idle seq_assoc)
    qed 
  next
    case (UnaryOp x1a e)
    then show ?case sorry
  next
    case (BinaryOp x1a e1 e2)
    then show ?case sorry
  qed
  then have c: "(x ::= e) \<ge> idle;(x ::= e);idle"
  proof -
    have "(x ::= e) = (\<Squnion>k::nat. \<lbrakk>e\<rbrakk>k ; opt (id_bar {|x|} \<triangleright> var_eq x k) ; idle)" 
      unfolding assign_def by simp
    also have b: "... = (\<Squnion>k::nat. \<lbrakk>e\<rbrakk>k ; opt (id_bar {|x|} \<triangleright> var_eq x k) ; idle ; idle)" 
      using idle_seq_idle seq_assoc by auto
    also have "... = (\<Squnion>k::nat. \<lbrakk>e\<rbrakk>k ; opt (id_bar {|x|} \<triangleright> var_eq x k) ; idle)  ; idle" 
      by (simp add: NONDET_seq_distrib) 
    also have "... \<ge> (\<Squnion>k::nat. (idle ; \<lbrakk>e\<rbrakk>k) ; opt (id_bar {|x|} \<triangleright> var_eq x k) ; idle)  ; idle" (is "_ \<ge> ?rhs")
      by (simp add: NONDET_mono_quant a seq_mono_left)
    also have "?rhs \<ge> (\<Squnion>k::nat. idle ; (\<lbrakk>e\<rbrakk>k ; opt (id_bar {|x|} \<triangleright> var_eq x k) ; idle))  ; idle" (is "_ \<ge> ?rhs") 
      using seq_assoc by auto
    also have "?rhs \<ge> idle ; (\<Squnion>k::nat. \<lbrakk>e\<rbrakk>k ; opt (id_bar {|x|} \<triangleright> var_eq x k) ; idle)  ; idle" 
         by (simp add: par.seq_NONDET_distrib par.seq_NONDET_distrib_UNIV)
    finally show ?thesis using assign_def by auto
  qed
  also have b: "(x ::= e) \<ge> E\<^sup>C\<^sub>x (x ::= e) \<iinter> guar (id(x))" sorry
  then have d: "(x ::= e) \<ge> (var x . E\<^sup>C\<^sub>x (x ::= e))" using introduce_var_refine c by auto
  then have "(rely r) \<iinter> (guar ((E\<^sup>R\<^sub>x g) \<inter> {(s, s'). get_var x s = get_var x s'})) \<iinter> Y:\<^sub>s\<lparr>E\<^sup>R\<^sub>x q\<rparr> \<ge> 
        (x ::= e);(rely r) \<iinter> (guar ((E\<^sup>R\<^sub>x g) \<inter> {(s, s'). get_var x s = get_var x s'})) \<iinter> Y:\<^sub>s\<lparr>E\<^sup>R\<^sub>x q\<rparr>" (is "_ \<ge> ?rhs") sorry
  then have "?rhs \<ge> (var x . E\<^sup>C\<^sub>x (x ::= e));(rely r) \<iinter> (guar ((E\<^sup>R\<^sub>x g) \<inter> {(s, s'). get_var x s = get_var x s'})) \<iinter> Y:\<^sub>s\<lparr>E\<^sup>R\<^sub>x q\<rparr>" (is "_ \<ge> ?rhs")
    using d  by (simp add: conj.sync_mono_left seq_mono)
  then show ?thesis sorry
qed

lemma step_22': 
  "(rely {(s, s') . get_var t s = get_var t s'}) \<iinter> {|t|}:\<^sub>s\<lparr>{(s, s'). (get_var t s') = minP nats}\<rparr> \<ge> 
      (var et . et ::= (Constant N));(var ot . ot ::= (Constant N));
            ( (guar_inv {s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}) \<iinter> 
                  (rely ({(s, s') . get_var t s = get_var t s'})) \<iinter> 
                 \<lbrace>{s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}\<rbrace>;\<lparr>{(s, s'). (get_var t s') = minP nats}\<rparr> )"
proof -
  have "(rely {(s, s') . get_var t s = get_var t s'}) \<iinter> {|t|}:\<^sub>s\<lparr>{(s, s'). (get_var t s') = minP nats}\<rparr> \<ge>
              (var et . et ::= (Constant N));
                (rely {(s, s') . get_var t s = get_var t s' \<and> get_var et s = get_var et s'}) \<iinter> 
                \<lbrace>{s. (inv (get_var et s) even)}\<rbrace>;{|t, et|}:\<^sub>s\<lparr>{(s, s'). (get_var t s') = minP nats}\<rparr>"
  proof -
    have "(rely {(s, s') . get_var t s = get_var t s'}) \<iinter> {|t|}:\<^sub>s\<lparr>{(s, s'). (get_var t s') = minP nats}\<rparr> \<ge> 
      (var et . et ::= (Constant N));
        (rely {(s, s') . get_var t s = get_var t s' \<and> get_var et s = get_var et s'}) \<iinter> 
        \<lbrace>{s. (inv (get_var et s) even)}\<rbrace>;{|et, t|}:\<^sub>s\<lparr>{(s, s'). (get_var t s') = minP nats}\<rparr>" using introduce_var_init sorry
    then show ?thesis sorry
  qed
  then show ?thesis sorry
qed


lemma step_22: 
  "(rely {(s, s') . get_var t s = get_var t s'}) \<iinter> \<lparr>{(s, s'). (get_var t s') = minP nats}\<rparr> \<ge> 
      (var et . et ::= (Constant N));(var ot . ot ::= (Constant N));
            ( (guar_inv {s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}) \<iinter> 
                  (rely ({(s, s') . get_var t s = get_var t s'})) \<iinter> 
                 \<lbrace>{s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}\<rbrace>;\<lparr>{(s, s'). (get_var t s') = minP nats}\<rparr> )"
proof -
  have subset: "{(s, s'). (get_var ot s') = N \<and> (get_var et s') = N} \<subseteq> UNIV \<triangleright> {s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}"
    unfolding inv_def restrict_range_def by blast
  have "{(s, s'). (get_var t s') = minP nats} = relcomp UNIV {(s, s'). (get_var t s') = minP nats}" 
    by auto
  then have "\<lparr>{(s, s'). (get_var t s') = minP nats}\<rparr> \<ge> \<lparr>UNIV\<rparr>;\<lparr>{(s, s'). (get_var t s') = minP nats}\<rparr>" (is "_ \<ge> ?rhs")
    using spec_to_sequential by metis
  also have "?rhs \<ge> \<lparr>UNIV \<triangleright> {s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}\<rparr>;
        \<lbrace>{s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}\<rbrace>;\<lparr>{(s, s'). (get_var t s') = minP nats}\<rparr>" (is "_ \<ge> ?rhs")
    using seq_mono_right seq_assoc seq_mono_left spec_assert_restricts spec_univ spec_term by auto
  also have "?rhs \<ge> \<lparr>{(s, s'). (get_var ot s') = N \<and> (get_var et s') = N}\<rparr>;
          \<lbrace>{s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}\<rbrace>;\<lparr>{(s, s'). (get_var t s') = minP nats}\<rparr>" (is "_ \<ge> ?rhs")
      using spec_strengthen seq_mono subset by simp
   finally have "(rely ({(s, s') . get_var t s = get_var t s'})) \<iinter> \<lparr>{(s, s'). (get_var t s') = minP nats}\<rparr> \<ge>
          (rely ({(s, s') . get_var t s = get_var t s'})) \<iinter> ( \<lparr>{(s, s'). (get_var ot s') = N \<and> (get_var et s') = N}\<rparr>;
          \<lbrace>{s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}\<rbrace>;\<lparr>{(s, s'). (get_var t s') = minP nats}\<rparr> )" (is "_ \<ge> ?rhs") 
    using conj.sync_mono_right by simp
  also have "?rhs \<ge>  ( (rely ({(s, s') . get_var t s = get_var t s'})) \<iinter> \<lparr>{(s, s'). (get_var ot s') = N \<and> (get_var et s') = N}\<rparr> );
                                    ((rely ({(s, s') . get_var t s = get_var t s'})) \<iinter> \<lbrace>{s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}\<rbrace>
                                    ;\<lparr>{(s, s'). (get_var t s') = minP nats}\<rparr>)" (is "_ \<ge> ?rhs")
    using rely_seq_distrib seq_assoc by auto
  also have "?rhs \<ge> ( (rely ({(s, s') . get_var t s = get_var t s'})) \<iinter> \<lparr>{(s, s'). (get_var ot s') = N \<and> (get_var et s') = N}\<rparr> ) ; 
          ((guar_inv {s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}) \<iinter> (rely ({(s, s') . get_var t s = get_var t s'})) \<iinter> 
          \<lbrace>{s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}\<rbrace>;\<lparr>{(s, s'). (get_var t s') = minP nats}\<rparr>)" (is "_ \<ge> ?rhs")
    using conj.sync_mono_left guar_introduce guar_inv_def seq_mono_right by auto
  also have a: "?rhs \<ge> (var et . et::= (Constant N));(var ot . ot ::= (Constant N));
          ( (guar_inv {s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}) \<iinter> 
          (rely ({(s, s') . get_var t s = get_var t s'})) \<iinter> 
          \<lbrace>{s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}\<rbrace>;\<lparr>{(s, s'). (get_var t s') = minP nats}\<rparr> )" 
    using introduce_var_init empty_not_UNIV get_set1 set_set1 set_set2 sorry
  finally (xtrans) show ?thesis using a by simp
qed

lemma strengthen_under_invariant :
  assumes "r \<subseteq> (P' p)" and "g \<subseteq> (P' p)" and "p \<triangleleft> q2 \<triangleright> p \<subseteq> q1 "
  shows "(rely r) \<iinter> (guar g) \<iinter> \<lbrace>p\<rbrace>;\<lparr>q1\<rparr> \<ge> (rely r) \<iinter> (guar g) \<iinter> \<lbrace>p\<rbrace>;\<lparr>q2\<rparr>" 
proof -
  have "(r \<squnion> g)\<^sup>* \<subseteq> (P' p)" 
    using rg_rtrancl_maintains_invariant assms(1) assms(2) sorry 
  then have "p \<triangleleft> (r \<squnion> g)\<^sup>* \<sqinter> q2 \<subseteq> p \<triangleleft> (P' p) \<sqinter> q2"
    using domain_restrict_q_mono by blast
  also have "... \<subseteq> p \<triangleleft> q2 \<triangleright> p" 
    unfolding restrict_domain_def restrict_range_def by auto
  also have "... \<subseteq> q1" using assms by simp
  finally have "p \<triangleleft> (r \<squnion> g)\<^sup>* \<sqinter> q2 \<subseteq> q1" .
  then show ?thesis using  strengthen_under_rely_guar by auto
qed

lemma step_23 :
  "(var ot . ot ::= (Constant N));(var et . et ::= (Constant N));
            ( (guar_inv {s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}) \<iinter> 
                  (rely ({(s, s') . get_var t s = get_var t s' \<and> get_var et s = get_var et s' \<and> get_var ot s = get_var ot s'})) \<iinter> 
                 \<lbrace>{s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}\<rbrace>;\<lparr>{(s, s'). (get_var t s') = minP nats}\<rparr> ) \<ge>
  (var ot . ot ::= (Constant N));(var et . et ::= (Constant N));
            ( (guar_inv {s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}) \<iinter> 
                  (rely ({(s, s') . get_var t s = get_var t s' \<and> get_var et s = get_var et s' \<and> get_var ot s = get_var ot s'})) \<iinter> 
                 \<lbrace>{s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}\<rbrace>;
                    \<lparr>{(s, s'). ((get_var ot s') \<le> (minP even) \<or> (get_var et s') = (minP even)) \<and> 
                      ((get_var et s') \<le> (minP odd) \<or> (get_var ot s') = (minP odd)) 
                      \<and> (get_var t s') = (min (get_var et s') (get_var ot s')) }\<rparr> ) "
proof -
  have r_implies_P' : "{(s, s') . get_var t s = get_var t s' \<and> get_var et s = get_var et s' \<and> get_var ot s = get_var ot s'} \<subseteq> 
                                      P' {s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}" by auto
  moreover have g_implies_P' : "P' {s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)} \<subseteq> 
                                                          P' {s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}" by simp
  moreover have post_cond_implies : "{s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)} \<triangleleft> {(s, s'). ((get_var ot s') \<le> 
                        (minP even) \<or> (get_var et s') = (minP even)) \<and> ((get_var et s') \<le> (minP odd) \<or> (get_var ot s') = (minP odd)) 
                        \<and> (get_var t s') = (min (get_var et s') (get_var ot s')) } \<triangleright> {s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)} \<subseteq> 
                        {(s, s'). (get_var t s') = minP nats}" 
        using minP_even_upper_bound minP_odd_upper_bound minP_even_upper_bound_restrict 
              et_equals_N ot_equals_N joining_minP even_union_odd 
        unfolding restrict_range_def restrict_domain_def by fastforce
   ultimately have a:"(rely ({(s, s') . get_var t s = get_var t s' \<and> get_var et s = get_var et s' \<and> get_var ot s = get_var ot s'})) \<iinter>
        (guar_inv {s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}) \<iinter> 
        \<lbrace>{s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}\<rbrace>;\<lparr>{(s, s'). (get_var t s') = minP nats}\<rparr> \<ge> 
        (rely ({(s, s') . get_var t s = get_var t s' \<and> get_var et s = get_var et s' \<and> get_var ot s = get_var ot s'})) \<iinter> 
        (guar_inv {s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}) \<iinter> 
        \<lbrace>{s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}\<rbrace>;\<lparr>{(s, s'). ((get_var ot s') \<le> (minP even) \<or> (get_var et s') = (minP even)) \<and> 
                    ((get_var et s') \<le> (minP odd) \<or> (get_var ot s') = (minP odd)) 
                    \<and> (get_var t s') = (min (get_var et s') (get_var ot s')) }\<rparr>" 
        unfolding guar_inv_def using strengthen_under_invariant by auto
  then have b:"(guar_inv {s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}) \<iinter> 
        rely ({(s, s') . get_var t s = get_var t s' \<and> get_var et s = get_var et s' \<and> get_var ot s = get_var ot s'}) \<iinter> 
        \<lbrace>{s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}\<rbrace>;\<lparr>{(s, s'). (get_var t s') = minP nats}\<rparr> \<ge> 
        (guar_inv {s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}) \<iinter> 
                    (rely ({(s, s') . get_var t s = get_var t s' \<and> get_var et s = get_var et s' \<and> get_var ot s = get_var ot s'})) \<iinter> 
                    \<lbrace>{s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}\<rbrace>;\<lparr>{(s, s'). ((get_var ot s') \<le> (minP even) \<or> (get_var et s') = (minP even)) \<and> 
                    ((get_var et s') \<le> (minP odd) \<or> (get_var ot s') = (minP odd)) 
                    \<and> (get_var t s') = (min (get_var et s') (get_var ot s')) }\<rparr>" 
    using conj.sync_commute a by presburger
  then show ?thesis using seq_mono_right a b by auto
qed

lemma step_24 : "(var ot . ot ::= (Constant N));(var et . et ::= (Constant N));
            ( (guar_inv {s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}) \<iinter> 
                  (rely ({(s, s') . get_var t s = get_var t s' \<and> get_var et s = get_var et s' \<and> get_var ot s = get_var ot s'})) \<iinter> 
                 \<lbrace>{s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}\<rbrace>;
                    \<lparr>{(s, s'). ((get_var ot s') \<le> (minP even) \<or> (get_var et s') = (minP even)) \<and> 
                      ((get_var et s') \<le> (minP odd) \<or> (get_var ot s') = (minP odd)) 
                      \<and> (get_var t s') = (min (get_var et s') (get_var ot s')) }\<rparr> )  
        \<ge> (var ot . ot ::= (Constant N));(var et . et ::= (Constant N));
            ( (guar_inv {s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}) \<iinter> 
                  (rely ({(s, s') . get_var t s = get_var t s' \<and> get_var et s = get_var et s' \<and> get_var ot s = get_var ot s'})) \<iinter> 
                 \<lbrace>{s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}\<rbrace>;
                    \<lparr>{(s, s'). ((get_var ot s') \<le> (minP even) \<or> (get_var et s') = (minP even)) \<and> 
                      ((get_var et s') \<le> (minP odd) \<or> (get_var ot s') = (minP odd))}\<rparr> );
                      (t::=  (BinaryOp min (Variable (\<lambda>s. (get_var et s))) (Variable (\<lambda>s. (get_var ot s)))))"
proof -
  have equality_1 : "{(s, s'). get_var et s' = get_var et s \<and> get_var ot s' = get_var ot s} \<inter> {(s, s'). s \<in> {s. (inv (get_var ot s) odd) \<and> 
    (inv (get_var et s) even)} \<longrightarrow> s' \<in> {s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}} = {(s, s'). get_var et s' = get_var et s \<and> get_var ot s' = get_var ot s}"
    by auto
  have simp_to_post : "(guar_inv {s. (inv (get_var ot s) odd) \<and> (inv (get_var et s) even)}) \<iinter> 
      (rely {(s, s') . get_var t s = get_var t s' \<and> get_var et s = get_var et s' \<and> get_var ot s = get_var ot s'}) \<iinter> 
      \<lparr>{(s, s'). (get_var t s') = (min (get_var et s') (get_var ot s')) \<and> (get_var ot s) = (get_var ot s') \<and> (get_var et s) = (get_var et s') }\<rparr> \<ge> 
        (guar {(s, s'). get_var et s' = get_var et s \<and> get_var ot s' = get_var ot s}) \<iinter> 
        (rely {(s, s') . get_var t s = get_var t s' \<and> get_var et s = get_var et s' \<and> get_var ot s = get_var ot s'}) \<iinter> 
        \<lparr>{(s, s'). (get_var t s') = (min (get_var et s') (get_var ot s')) \<and> (get_var ot s) = (get_var ot s') \<and> (get_var et s) = (get_var et s') }\<rparr>"
    unfolding guar_inv_def using guar_introduce conj.sync_mono_left 
      guar_merge equality_1 by (metis (no_types, lifting))
  then show ?thesis sorry
qed

theorem findP_final :
  shows "(rely ({(s, s'). s' = s})) \<iinter> \<lparr>{(s, s'). (get_var t s') = minP nats}\<rparr> \<ge> 
  (var ot . ot ::= (Constant N));(var et . et ::= (Constant N)); 
    ((var ec . ec ::= (Constant 0)); (While b\<^sub>w do (If b\<^sub>i then (et::= e\<^sub>1) else (ec::= e\<^sub>2)))) \<parallel>
    ((var oc . oc ::= (Constant 1)) ; (While b\<^sub>w\<^sub>o do (If b\<^sub>i\<^sub>o then (ot::= e\<^sub>1\<^sub>o) else (oc::= e\<^sub>2\<^sub>o))));
    (t::=  (BinaryOp min (Variable (\<lambda>s. (get_var et s))) (Variable (\<lambda>s. (get_var ot s)))))"
  apply (auto simp add: step_22 step_23 step_24)
(*
  also have step_23 : "... \<ge> (Vet::= (Constant N));(Vot::= (Constant N)); 
        ( (guar_inv p_inv) \<iinter> (rely no_change) \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>s23_post\<rparr> )"
  proof -
    have r_implies_P' : "no_change \<subseteq> P' p_inv" by auto
    moreover have g_implies_P' : "P' p_inv \<subseteq> P' p_inv" by simp
    moreover have post_cond_implies : "p_inv \<triangleleft> s23_post \<triangleright> p_inv \<subseteq> 
          {(k, k'). (t k') = minP nats}" 
      using minP_even_upper_bound minP_odd_upper_bound minP_even_upper_bound_restrict 
        et_equals_N ot_equals_N joining_minP even_union_odd 
        unfolding restrict_range_def restrict_domain_def by fastforce
    ultimately have "(rely (no_change)) \<iinter> (guar_inv p_inv) \<iinter> 
          \<lbrace>p_inv\<rbrace>;\<lparr>{(k, k'). (t k') = minP nats}\<rparr> \<ge> 
          (rely (no_change)) \<iinter> (guar_inv p_inv) \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>s23_post\<rparr>" 
      unfolding guar_inv_def using strengthen_under_invariant by auto
    then have "(guar_inv p_inv) \<iinter> (rely (no_change)) \<iinter> 
          \<lbrace>p_inv\<rbrace>;\<lparr>{(k, k'). (t k') = minP nats}\<rparr> \<ge> 
          (guar_inv p_inv) \<iinter> (rely (no_change)) \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>s23_post\<rparr>" 
      using conj.sync_commute by presburger
    then show ?thesis using seq_mono_right by blast
  qed
  also have step_24 : "... \<ge> (Vet::= (Constant N));(Vot::= (Constant N)) ; 
        ( (guar_inv p_inv) \<iinter> (rely no_change) \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>s24_first_post\<rparr> ) ;
        (Vt::= e\<^sub>t)"
  proof -
    have simp_to_post : "(guar_inv p_inv) \<iinter> (rely no_change) \<iinter> \<lparr>s24_second_post\<rparr> \<ge> 
          post_assign_t"
      unfolding guar_inv_def using guar_introduce conj_mono_left 
        guar_merge equality_1 by (metis (no_types, lifting))
    have "( relcomp s24_first_post s24_second_post ) \<subseteq> s23_post" by auto
    then have "\<lbrace>p_inv\<rbrace>;\<lparr>s23_post\<rparr> \<ge> \<lbrace>p_inv\<rbrace>;\<lparr>s24_first_post\<rparr>;\<lparr>s24_second_post\<rparr>" 
      using spec_chain_pre spec_strengthen by (simp add: spec_chain seq_assoc seq_mono_right)
    then have "( (guar_inv p_inv) \<iinter> (rely no_change) \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>s23_post\<rparr> ) \<ge> 
          ((guar_inv p_inv) \<iinter> (rely no_change) \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>s24_first_post\<rparr>;\<lparr>s24_second_post\<rparr>)"
      using conj_mono_right by auto
    also have "... \<ge> ( (guar_inv p_inv) \<iinter> (rely no_change) \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>s24_first_post\<rparr> ) ;
          ( (guar_inv p_inv) \<iinter> (rely no_change) \<iinter> \<lparr>s24_second_post\<rparr> )"
      unfolding guar_inv_def using conj_seq_distrib guar_distrib_seq 
        rely_seq_idem conj_mono_right by (metis (no_types, lifting))
    also have "... \<ge> ( (guar_inv p_inv) \<iinter> (rely (no_change)) \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>s24_first_post\<rparr> ) ; 
          (Vt::= e\<^sub>t)" using post_assignment simp_to_post seq_mono_right by auto
    finally show ?thesis using seq_mono_right by (simp add: seq_assoc)
  qed
  also have step_25 : "... \<ge> (Vet::= (Constant N));(Vot::= (Constant N)) ; 
        ( ( (guar (et_less \<sqinter> P' p_inv)) \<iinter> (rely (ot_less \<sqinter> P' p_inv)) \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>q1_25\<rparr> ) \<parallel>
        ( (guar (ot_less \<sqinter> P' p_inv)) \<iinter> (rely (et_less \<sqinter> P' p_inv)) \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>q2_25\<rparr> ) ) ;
        (Vt::= e\<^sub>t)"
  proof -
    have "(rely (no_change)) \<iinter> \<lparr>s24_first_post\<rparr> \<ge> (rely no_change) \<iinter> \<lparr>q1_25 \<sqinter> q2_25\<rparr>"
      using subset_8 conj_mono_right spec_strengthen by auto
    also have "... \<ge> (guar(no_change \<squnion> (et_less \<sqinter> P' p_inv)) \<iinter> 
          rely(no_change \<squnion> (ot_less \<sqinter> P' p_inv)) \<iinter> \<lparr>q1_25\<rparr>) \<parallel>
          (guar(no_change \<squnion> (ot_less \<sqinter> P' p_inv)) \<iinter> 
          rely(no_change \<squnion> (et_less \<sqinter> P' p_inv)) \<iinter> \<lparr>q2_25\<rparr>)" 
      using spec_introduce_par by blast
    also have "... = (guar (et_less \<sqinter> P' p_inv) \<iinter> rely (ot_less \<sqinter> P' p_inv) \<iinter> \<lparr>q1_25\<rparr>) \<parallel>
          (guar (ot_less \<sqinter> P' p_inv) \<iinter> rely (et_less \<sqinter> P' p_inv) \<iinter> \<lparr>q2_25\<rparr>)" 
      using equality_2 equality_3 by auto
    finally have "(rely (no_change)) \<iinter> \<lparr>s24_first_post\<rparr> \<ge> 
          ( (guar (et_less \<sqinter> P' p_inv)) \<iinter> (rely (ot_less \<sqinter> P' p_inv)) \<iinter> \<lparr>q1_25\<rparr>) \<parallel> 
          ( (guar (ot_less \<sqinter> P' p_inv)) \<iinter> (rely (et_less \<sqinter> P' p_inv)) \<iinter> \<lparr>q2_25\<rparr>)" by simp
    then have "(guar_inv p_inv) \<iinter> (rely (no_change)) \<iinter> \<lparr>s24_first_post\<rparr> \<ge> 
          (guar_inv p_inv) \<iinter> 
          ( ( (guar (et_less \<sqinter> P' p_inv)) \<iinter> (rely (ot_less \<sqinter> P' p_inv)) \<iinter> \<lparr>q1_25\<rparr>) \<parallel> 
          ( (guar (ot_less \<sqinter> P' p_inv)) \<iinter> (rely (et_less \<sqinter> P' p_inv)) \<iinter> \<lparr>q2_25\<rparr>) )" 
      using conj_mono_right conj_assoc by auto
    also have "... \<ge> ( (guar_inv p_inv) \<iinter> (guar (et_less \<sqinter> P' p_inv)) \<iinter> 
          (rely (ot_less \<sqinter> P' p_inv)) \<iinter> \<lparr>q1_25\<rparr>) \<parallel> 
          ( (guar_inv p_inv) \<iinter> (guar (ot_less \<sqinter> P' p_inv)) \<iinter> 
          (rely (et_less \<sqinter> P' p_inv)) \<iinter> \<lparr>q2_25\<rparr>)" 
      unfolding guar_inv_def using guar_distrib_par conj_assoc by auto
    also have "... \<ge> ( (guar (et_less \<sqinter> P' p_inv)) \<iinter> (rely (ot_less \<sqinter> P' p_inv)) \<iinter> \<lparr>q1_25\<rparr>) \<parallel> 
          ( (guar (ot_less \<sqinter> P' p_inv)) \<iinter> (rely (et_less \<sqinter> P' p_inv)) \<iinter> \<lparr>q2_25\<rparr>)"
      using refinement_1 refinement_2 conj_mono_left par_mono by auto
    finally have no_pre : "(guar_inv p_inv) \<iinter> (rely (no_change)) \<iinter> \<lparr>s24_first_post\<rparr> \<ge> 
          ( (guar (et_less \<sqinter> P' p_inv)) \<iinter> (rely (ot_less \<sqinter> P' p_inv)) \<iinter> \<lparr>q1_25\<rparr>) \<parallel> 
          ( (guar (ot_less \<sqinter> P' p_inv)) \<iinter> (rely (et_less \<sqinter> P' p_inv)) \<iinter> \<lparr>q2_25\<rparr>)" by auto
    then have "(guar_inv p_inv) \<iinter> (rely no_change) \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>s24_first_post\<rparr> = 
          \<lbrace>p_inv\<rbrace>;( (guar_inv p_inv) \<iinter> (rely (no_change)) \<iinter> \<lparr>s24_first_post\<rparr>)" 
      using conj.sync_commute initial_assert_rely_generic by auto
    also have "... \<ge> ( (guar (et_less \<sqinter> P' p_inv)) \<iinter> (rely (ot_less \<sqinter> P' p_inv)) \<iinter> 
          \<lbrace>p_inv\<rbrace>;\<lparr>q1_25\<rparr>) \<parallel> 
          ((guar (ot_less \<sqinter> P' p_inv)) \<iinter> (rely (et_less \<sqinter> P' p_inv)) \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>q2_25\<rparr>)" 
      using no_pre seq_mono_right pre_par_distrib move_pre par_mono by auto
    finally show ?thesis using seq_mono_right seq_mono_left by auto
  qed
  also have even_odd_refinement : "... \<ge> (Vet::= (Constant N));(Vot::= (Constant N)) ; 
  (((Vec::= (Constant 0)) ; (While b\<^sub>w do (If b\<^sub>i then (Vet::= e\<^sub>1) else (Vec::= e\<^sub>2)))) \<parallel>
  ((Voc::= (Constant 1)) ; (While b\<^sub>w\<^sub>o do (If b\<^sub>i\<^sub>o then (Vot::= e\<^sub>1\<^sub>o) else (Voc::= e\<^sub>2\<^sub>o)))));
  (Vt::= e\<^sub>t)"
    using even_refinement odd_refinement par_mono seq_mono_left seq_mono_right by auto
  finally show ?thesis .
*)