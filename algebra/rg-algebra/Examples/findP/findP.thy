section {*Find Least First Element That Satisfies $P$*}

theory findP
  imports  
  "./programming_constructs_extended"
begin

subsection{*Proof Constructs*}
subsubsection {*State Description*}
text{*This record describes the components of the state of the program. 
$oc$ and $ec$ are included as part of the state and not as local variables for this proof.*}
record state =
  t :: nat
  et :: nat
  ot :: nat
  ec :: nat
  oc :: nat
(*describe a get and set function to access the components of the record*)
datatype varname = Vt | Vet | Vot | Vec | Voc

fun get_var :: "varname \<Rightarrow> state \<Rightarrow> nat" where
  "get_var Vt s = t s" |
  "get_var Vet s = et s" |
  "get_var Vot s = ot s" |
  "get_var Vec s = ec s" |
  "get_var Voc s = oc s" 

fun set_var :: "varname \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state" where
  "set_var Vt val s = s\<lparr>t := val\<rparr>" |
  "set_var Vet val s = s\<lparr>et := val\<rparr>" |
  "set_var Vot val s = s\<lparr>ot := val\<rparr>" |
  "set_var Vec val s = s\<lparr>ec := val\<rparr>" |
  "set_var Voc val s = s\<lparr>oc := val\<rparr>" 

subsubsection{*Value Definition*}
text{*An additional datatype, denoted a "Value" is used throughout the proof.*}
datatype Value = Natural (the_Nat:"nat") | Bool (the_Bool:"bool")

instantiation Value :: has_booleans
begin
  definition true_Value :: "Value" where
    "true_Value = Bool True"
  definition false_Value :: "Value" where
    "false_Value = Bool False"

  instance proof
    show "(has_booleans_class.true::Value) \<noteq> has_booleans_class.false"
      by (simp add: true_Value_def false_Value_def)
  qed
end

definition Nat_less_than :: "Value \<Rightarrow> Value \<Rightarrow> Value" (infix "<\<^sub>n" 50)
  where "Nat_less_than m n = Bool (the_Nat m < the_Nat n)"

definition Nat_and :: "Value \<Rightarrow> Value \<Rightarrow> Value" (infix "\<and>\<^sub>n" 50)
  where "Nat_and m n = Bool (the_Bool m \<and> the_Bool n)"

subsubsection{*Definitions*}
text{*This section covers the fundamental definitions used for the proof.*}
locale findP_rules =
  fixes v :: "nat \<Rightarrow> 'd" and
        Pr :: "'d \<Rightarrow> bool" and
        N :: "nat" 
begin

definition 
P :: "nat \<Rightarrow> bool" where
"P i \<equiv> (i < N) \<longrightarrow> (Pr (v i))"

definition
minP :: "nat set \<Rightarrow> nat" where
"minP S = Min {i | i. i \<in> S \<and> (P i)}"

definition
inv :: "nat \<Rightarrow> nat set \<Rightarrow> bool " where
"inv st S \<equiv> ((st \<noteq> N) \<longrightarrow> (st = (minP S)))"

definition
inv_loop :: "nat \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> bool" where
"inv_loop sc st S \<equiv> sc \<le> minP S \<and> sc \<in> S \<and> sc \<le> st + 1"

text{*Evens, odds and nats are bounded by N + 1 as Min operations require finite sets.*}
definition
even :: "nat set" where
"even = {k. k mod 2 = 0 \<and> k \<le> N + 1}"

definition
odd :: "nat set" where
"odd = {k. k mod 2 = 1 \<and> k \<le> N + 1}"

definition
nats :: "nat set" where
"nats = {k. k \<le> N + 1}"
end

subsubsection{*Proof Instantiation*} 
text{*This locale instantiates the proof on top of the existing theory using the described 
\textit{set\_var} and \textit{get\_var} functions.*}
locale findP_pre = while_loop + intro_par_big + assignments +
  constrains test :: "state set \<Rightarrow> 'a" 
  constrains pgm :: "state rel \<Rightarrow> 'a"
  constrains env :: "state rel \<Rightarrow> 'a"
  constrains get_var :: "'varname \<Rightarrow> state \<Rightarrow> 'b"
begin

lemma set_get_consistent : "set_var k (get_var k s) s = s"
  by (simp add: set_get)

sublocale programming_constructs_extended seq test par conj pgm env set_var get_var
proof
  show "\<And>k s. set_var k (get_var k s) s = s" using set_get_consistent by simp
qed

notation 
  assign (infix "::=" 60) and
  var_frame (infix ":\<^sub>f" 60)
end                  

subsection{*Abbreviations*}
text{*This section contains abbreviations used throughout the proof.*}
locale findP_abbreviations = findP_pre + findP_rules
begin

subsubsection{*General Abbreviations*}
abbreviation p_inv :: "state set" where
"p_inv \<equiv> {k. (inv (ot k) odd) \<and> (inv (et k) even)}"

abbreviation p_inv_ext :: "state set" where
"p_inv_ext \<equiv> {k. (inv (ot k) odd) \<and> (inv (et k) even) \<and> (inv_loop (ec k) (et k) even)}"

abbreviation no_change :: "state rel" where
"no_change \<equiv> {(k, k'). k' = k}"

abbreviation ot_less :: "state rel" where
"ot_less \<equiv> {(k, k'). ot k' \<le> ot k \<and> et k = et k' \<and> ec k = ec k'}"

abbreviation et_less :: "state rel" where
"et_less \<equiv> {(k, k'). et k' \<le> et k \<and> ot k = ot k' \<and> oc k = oc k'}"

subsubsection{*Assignment Abbreviations*}
abbreviation var_init :: 'a where
"var_init \<equiv> ( (rely ({(k, k'). k' = k})) \<iinter> \<lparr>{(k, k'). (ot k') = N \<and> (et k') = N}\<rparr> )"

abbreviation ec_to_0 :: "state rel" where
"ec_to_0 \<equiv> ( {(k, k'). ec k' = 0 \<and> et k = et k' \<and> (( inv (ot k) odd) \<longrightarrow> (inv (ot k') odd))} )"

abbreviation var_init_ec :: 'a where
"var_init_ec \<equiv> ((guar (et_less \<sqinter> P' p_inv)) \<iinter> (rely (ot_less \<sqinter> P' p_inv)) \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>ec_to_0\<rparr>)"

abbreviation post_assign_t :: "'a" where
"post_assign_t \<equiv> (guar {(k, k'). et k' = et k \<and> ot k' = ot k}) \<iinter> (rely {(k, k'). k' = k}) \<iinter> 
      \<lparr>{(k, k'). (t k') = (min (et k') (ot k')) \<and> (ot k) = (ot k') \<and> (et k) = (et k') }\<rparr>"

subsubsection{*While Loop Abbreviations (w)*}
abbreviation ec_le_ot :: "(state, Value) expr" where
"ec_le_ot \<equiv> (BinaryOp (<\<^sub>n) (Variable (\<lambda>k::state. Natural (ec k))) 
      (Variable (\<lambda>k::state. Natural (ot k))))"

abbreviation ec_le_et :: "(state, Value) expr" where
"ec_le_et \<equiv> (BinaryOp (<\<^sub>n) (Variable (\<lambda>k::state. Natural (ec k))) 
      (Variable (\<lambda>k::state. Natural (et k))))"

abbreviation b\<^sub>w :: "(state, Value) expr" where
"b\<^sub>w \<equiv> (BinaryOp (\<and>\<^sub>n) ec_le_et ec_le_ot)"

abbreviation b0\<^sub>w :: "state set" where
"b0\<^sub>w \<equiv> {k::state. (ec k) < (et k)}"

abbreviation b1\<^sub>w :: "state set" where
"b1\<^sub>w \<equiv> {k. (ec k) \<ge> (et k) \<or> (ec k) \<ge> (ot k)}"

abbreviation v\<^sub>w :: "state \<Rightarrow> nat" where
"v\<^sub>w \<equiv> (\<lambda>k::state. ((et k) - (ec k)))"

abbreviation p\<^sub>w :: "state set" where
"p\<^sub>w \<equiv> p_inv_ext"

abbreviation q\<^sub>w :: "state rel" where
"q\<^sub>w \<equiv> UNIV"

abbreviation r\<^sub>w :: "state rel" where
"r\<^sub>w \<equiv> (ot_less \<sqinter> P' p_inv)"

abbreviation g\<^sub>w :: "state rel" where
"g\<^sub>w \<equiv> (et_less \<sqinter> P' p_inv)"

abbreviation wfr\<^sub>w :: "nat rel" where 
"wfr\<^sub>w \<equiv> {((n::nat), n'). (n < n') \<and> (n' \<le> N + 1) }"

abbreviation c\<^sub>w_pre :: "state set" where
"c\<^sub>w_pre \<equiv> {k. (ec k) < (et k) \<and> (inv_loop (ec k) (et k) even) \<and> (inv (et k) even)}"

abbreviation c\<^sub>w_post :: "state rel" where
"c\<^sub>w_post \<equiv> {(k, k'). (inv_loop (ec k') (et k') even) \<and> 
      (-1 \<le> (et k') - (ec k')) \<and> (et k') - (ec k') < (et k) - (ec k)}"

abbreviation c\<^sub>w :: 'a where
"c\<^sub>w \<equiv> (rely r\<^sub>w) \<iinter> (guar g\<^sub>w) \<iinter> \<lbrace>c\<^sub>w_pre\<rbrace>;\<lparr>c\<^sub>w_post\<rparr>"

subsubsection{*If Statement Abbreviations (i)*}
abbreviation b\<^sub>i :: "(state, Value) expr" where
"b\<^sub>i \<equiv> Variable (\<lambda>k::state. Bool (P (ec k)))"

abbreviation b0\<^sub>i :: "state set" where
"b0\<^sub>i \<equiv> {k. P (ec k)}"

abbreviation b1\<^sub>i :: "state set" where
"b1\<^sub>i \<equiv> {k. \<not>(P (ec k))}"

abbreviation r\<^sub>i :: "state rel" where
"r\<^sub>i \<equiv> {(k, k'). (ec k') = (ec k) \<and> (et k') = (et k)}"

abbreviation g\<^sub>i :: "state rel" where
"g\<^sub>i \<equiv> (et_less \<sqinter> P' p_inv)"

abbreviation p\<^sub>i :: "state set" where
"p\<^sub>i \<equiv> {k. (ec k) < (et k) \<and> (inv_loop (ec k) (et k) even) \<and> (inv (et k) even)}"

abbreviation q\<^sub>i :: "state rel" where
"q\<^sub>i \<equiv> {(k, k'). (inv_loop (ec k') (et k') even) \<and> 
      (-1 \<le> (et k') - (ec k')) \<and> (et k') - (ec k') < (et k) - (ec k)}"

abbreviation if1 :: 'a where
"if1 \<equiv> ((guar g\<^sub>i) \<iinter> (rely r\<^sub>i) \<iinter> \<ltort>b0\<^sub>i \<inter> p\<^sub>i, q\<^sub>i\<rtort>)"

abbreviation if2 :: 'a where
"if2 \<equiv> ((guar g\<^sub>i) \<iinter>(rely r\<^sub>i) \<iinter> \<ltort>b1\<^sub>i \<inter> p\<^sub>i,q\<^sub>i\<rtort>)"

subsubsection{*$ec$ Assignment Abbreviations (c) *}
abbreviation g\<^sub>c :: "state rel" where
"g\<^sub>c \<equiv> (et_less \<sqinter> P' p_inv)"

abbreviation r\<^sub>c :: "state rel" where
"r\<^sub>c \<equiv> (ot_less \<sqinter> P' p_inv)"

abbreviation p\<^sub>c :: "state set" where
"p\<^sub>c \<equiv> p_inv"

abbreviation q\<^sub>c :: "state rel" where
"q\<^sub>c \<equiv> ec_to_0"

abbreviation e\<^sub>c :: "(state, nat) expr" where
"e\<^sub>c \<equiv> (Constant 0)"

abbreviation e0\<^sub>c :: "nat \<Rightarrow> state set" where
"e0\<^sub>c \<equiv> (\<lambda>k. {m. k = 0})"

subsubsection{*$et$ Assignment Abbreviations (e) *}
abbreviation p\<^sub>e :: "state set" where
"p\<^sub>e \<equiv> UNIV"

abbreviation q\<^sub>e :: "state rel" where
"q\<^sub>e \<equiv> {(k, k'). (et k') = N}"

abbreviation r\<^sub>e :: "state rel" where
"r\<^sub>e \<equiv> {(k, k'). k' = k}"

abbreviation g\<^sub>e :: "state rel" where
"g\<^sub>e \<equiv> UNIV"

abbreviation e\<^sub>e :: "(state, nat) expr" where
"e\<^sub>e \<equiv> (Constant N)"

abbreviation e0\<^sub>e :: "nat \<Rightarrow> state set" where
"e0\<^sub>e \<equiv> (\<lambda>k. {m. k = N})"

subsubsection{*$ot$ Assignment Abbreviations (o) *}
abbreviation p\<^sub>o :: "state set" where
"p\<^sub>o \<equiv> UNIV"

abbreviation q\<^sub>o :: "state rel" where
"q\<^sub>o \<equiv> {(k, k'). (et k') = (et k) \<and> (ot k') = N}"

abbreviation r\<^sub>o :: "state rel" where
"r\<^sub>o \<equiv> {(k, k'). k' = k}"

abbreviation g\<^sub>o :: "state rel" where
"g\<^sub>o \<equiv> UNIV"

abbreviation e\<^sub>o :: "(state, nat) expr" where
"e\<^sub>o \<equiv> (Constant N)"

abbreviation e0\<^sub>o :: "nat \<Rightarrow> state set" where
"e0\<^sub>o \<equiv> (\<lambda>k. {m. k = N})"

subsubsection{*Post Assignment Abbreviations (t) *}
abbreviation p\<^sub>t :: "state set" where
"p\<^sub>t \<equiv> UNIV"

abbreviation q\<^sub>t :: "state rel" where
"q\<^sub>t \<equiv> {(k, k'). (t k') = (min (et k') (ot k')) \<and> (ot k) = (ot k') \<and> (et k) = (et k') }"

abbreviation g\<^sub>t :: "state rel" where
"g\<^sub>t \<equiv> {(k, k'). et k' = et k \<and> ot k' = ot k}"

abbreviation r\<^sub>t :: "state rel" where
"r\<^sub>t \<equiv> {(k, k'). k' = k}"

abbreviation e\<^sub>t :: "(state, nat) expr" where
"e\<^sub>t \<equiv> (BinaryOp min (Variable (\<lambda>s. (et s))) (Variable (\<lambda>s. (ot s))))"

abbreviation e0\<^sub>t :: "nat \<Rightarrow> state set" where
"e0\<^sub>t \<equiv> (\<lambda>k. {s. (min (et s) (ot s)) = k})"

subsubsection{*True If Statement Abbreviations (1) *}
abbreviation p\<^sub>1 :: "state set" where
"p\<^sub>1 \<equiv> b0\<^sub>i \<inter> p\<^sub>i"

abbreviation q\<^sub>1 :: "state rel" where
"q\<^sub>1 \<equiv> q\<^sub>i"

abbreviation g\<^sub>1 :: "state rel" where
"g\<^sub>1 \<equiv> g\<^sub>i"

abbreviation r\<^sub>1 :: "state rel" where
"r\<^sub>1 \<equiv> r\<^sub>i"

abbreviation e\<^sub>1 :: "(state, nat) expr" where
"e\<^sub>1 \<equiv> (Variable (\<lambda>s. (ec s)))"

abbreviation e0\<^sub>1 :: "nat \<Rightarrow> state set" where
"e0\<^sub>1 \<equiv> (\<lambda>k. {s. (ec s) = k})"

subsubsection{*False If Statement Abbreviations (2) *}
abbreviation p\<^sub>2 :: "state set" where
"p\<^sub>2 \<equiv> b1\<^sub>i \<inter> p\<^sub>i"

abbreviation q\<^sub>2 :: "state rel" where
"q\<^sub>2 \<equiv> q\<^sub>i"

abbreviation g\<^sub>2 :: "state rel" where
"g\<^sub>2 \<equiv> g\<^sub>i"

abbreviation r\<^sub>2 :: "state rel" where
"r\<^sub>2 \<equiv> r\<^sub>i"

abbreviation e\<^sub>2 :: "(state, nat) expr" where
"e\<^sub>2 \<equiv> (Variable (\<lambda>s. (ec s) + 2))"

abbreviation e0\<^sub>2 :: "nat \<Rightarrow> state set" where
"e0\<^sub>2 \<equiv> (\<lambda>k. {s. (ec s) + 2 = k})"

subsubsection{*Step Abbreviations*}
abbreviation s23_post :: "state rel" where
"s23_post \<equiv> {(k, k'). ((ot k') \<le> (minP even) \<or> (et k') = (minP even)) \<and> 
      ((et k') \<le> (minP odd) \<or> (ot k') = (minP odd)) \<and> (t k') = (min (et k') (ot k')) }"

abbreviation s24_first_post :: "state rel" where
"s24_first_post \<equiv> {(k, k'). ((ot k') \<le> (minP even) \<or> (et k') = (minP even)) \<and> 
      ((et k') \<le> (minP odd) \<or> (ot k') = (minP odd))}"

abbreviation s24_second_post :: "state rel" where
"s24_second_post \<equiv> {(k, k'). (t k') = (min (et k') (ot k')) \<and> 
      (ot k) = (ot k') \<and> (et k) = (et k') }"

abbreviation q1_25 :: "state rel" where
"q1_25 \<equiv> {(k, k'). (ot k') \<le> (minP even) \<or> (et k') = (minP even)}"

abbreviation q2_25 :: "state rel" where
"q2_25 \<equiv> {(k, k'). (et k') \<le> (minP odd) \<or> (ot k') = (minP odd)}"

abbreviation e28_post :: "state rel" where
"e28_post \<equiv> {(k, k'). ( (ot k') \<le> (minP even) \<or> (et k') = (minP even) ) \<and> 
      (inv_loop (ec k') (et k') even)}"

abbreviation e29_post :: "state rel" where
"e29_post \<equiv> {(k, k'). (inv_loop (ec k') (et k') even) \<and> (ec k' \<ge> ot k' \<or> ec k' \<ge> et k')}"

abbreviation e31_loop :: 'a where
"e31_loop \<equiv> ( (rely r\<^sub>i) \<iinter> (guar g\<^sub>i) \<iinter> \<lbrace>p\<^sub>i\<rbrace>;\<lparr>q\<^sub>i\<rparr> )"

subsubsection{*Odd Refinement Abbreviations*}
abbreviation oc_le_et :: "(state, Value) expr" where
"oc_le_et \<equiv> (BinaryOp (<\<^sub>n) (Variable (\<lambda>k::state. Natural (oc k))) 
      (Variable (\<lambda>k::state. Natural (et k))))"

abbreviation oc_le_ot :: "(state, Value) expr" where
"oc_le_ot \<equiv> (BinaryOp (<\<^sub>n) (Variable (\<lambda>k::state. Natural (oc k))) 
      (Variable (\<lambda>k::state. Natural (ot k))))"

abbreviation b\<^sub>w\<^sub>o :: "(state, Value) expr" where
"b\<^sub>w\<^sub>o \<equiv> (BinaryOp (\<and>\<^sub>n) oc_le_ot oc_le_et)"

abbreviation b\<^sub>i\<^sub>o :: "(state, Value) expr" where
"b\<^sub>i\<^sub>o \<equiv> Variable (\<lambda>k::state. Bool (P (oc k)))"

abbreviation e\<^sub>1\<^sub>o :: "(state, nat) expr" where
"e\<^sub>1\<^sub>o \<equiv> (Variable (\<lambda>s. (oc s)))"

abbreviation e\<^sub>2\<^sub>o :: "(state, nat) expr" where
"e\<^sub>2\<^sub>o \<equiv> (Variable (\<lambda>s. (oc s) + 2))"
end

subsection{*Formal Proof*}
text{*This section contains the formal proof of \emph{Find least first element of an array that satisfies $P$}
as described in \emph{A Guid to Rely/Guarantee Thinking}.*}
locale findP = findP_abbreviations
begin

subsubsection{*Basic Proofs*}
text{*This section contains proofs relating to evens, odds, nats and the Min function.*}
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

subsubsection{*minP Proofs*}
text{*This section contains proofs relating to the minP function.*}
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

subsubsection{*Miscallaneous Proofs*}
text{*This section contains additional proofs which are useful in the final proof.*}
lemma ot_equals_N :
  assumes m_ot : "inv (ot m') odd" and ot_false : "(ot m') \<noteq> minP odd"
  shows "(ot m') = N"
  using assms unfolding inv_def by blast

lemma et_equals_N :
  assumes m_et : "inv (et m') even" and et_false : "(et m') \<noteq> minP even"
  shows "(et m') = N"
  using assms unfolding inv_def by blast

lemma expr_true_simp : "expr_eq b\<^sub>w true = {k. (ec k) < (et k) \<and> (ec k) < (ot k)}"
  unfolding expr_eq_def Nat_and_def Nat_less_than_def 
  by (simp add: Collect_mono true_Value_def)

lemma expr_false_simp : "expr_eq b\<^sub>w false = {k. (ec k) \<ge> (et k) \<or> (ec k) \<ge> (ot k)}"
  unfolding expr_eq_def Nat_and_def Nat_less_than_def 
  by (simp add: Collect_mono false_Value_def, auto)

lemma finite_wfr : "finite wfr\<^sub>w"
proof -
  have "wfr\<^sub>w \<subseteq> {(n, n'). n \<le> N + 1 \<and> n' \<le> N + 1}" by auto
  then show ?thesis using infinite_super by auto
qed

lemma wfr_ordered : "(x, y) \<in> wfr\<^sub>w\<^sup>+ \<Longrightarrow> x < y"
  by (induct rule:trancl.induct, auto)

lemma refl_1 : "refl g\<^sub>i"
  unfolding refl_on_def by blast

lemma stable_simp_1 : "stable p\<^sub>i r\<^sub>i" 
  unfolding stable_def by auto

lemma stable_simp_2 : "stable p\<^sub>1 r\<^sub>1"
  unfolding stable_def by auto

lemma stable_simp_3 : "stable p\<^sub>2 r\<^sub>2"
  unfolding stable_def by auto

lemma subset_1 : "p_inv \<triangleleft> ec_to_0 \<subseteq> p_inv \<triangleleft> UNIV \<triangleright> p_inv_ext"
  unfolding restrict_domain_def inv_loop_def even_def restrict_range_def by auto

lemma subset_2 : "((dec wfr\<^sub>w\<^sup>= v\<^sub>w) \<inter> q\<^sub>w\<^sup>*) \<triangleright> (p\<^sub>w \<inter> b1\<^sub>w) \<subseteq> e29_post"
  unfolding restrict_range_def by auto

lemma subset_3 : "b0\<^sub>w \<inter> p\<^sub>w \<inter> (fn_less v\<^sub>w (wfr\<^sub>w\<^sup>=) k) \<subseteq> c\<^sub>w_pre" by auto

lemma subset_4 : "e28_post \<subseteq> q1_25" by blast

lemma subset_5 : "ot_less \<sqinter> P' p_inv \<subseteq> ot_less" by blast

lemma subset_6 : "r\<^sub>w \<subseteq> {(k, k'). (ec k') = (ec k) \<and> (et k') = (et k)}" by auto

lemma subset_7 : "{(k, k'). (ot k') = N \<and> (et k') = N} \<subseteq> UNIV \<triangleright> p_inv"
  unfolding inv_def restrict_range_def by blast

lemma subset_8 : "q1_25 \<sqinter> q2_25 \<subseteq> s24_first_post" by auto

lemma equality_1 : "{(k, k'). et k' = et k \<and> ot k' = ot k} \<inter> 
      {(k, k'). k \<in> p_inv \<longrightarrow> k' \<in> p_inv} = {(k, k'). et k' = et k \<and> ot k' = ot k}" 
  by auto

lemma equality_2 : "no_change \<squnion> (ot_less \<sqinter> P' p_inv) = ot_less \<sqinter> P' p_inv" by auto

lemma equality_3 : "no_change \<squnion> (et_less \<sqinter> P' p_inv) = et_less \<sqinter> P' p_inv" by auto

lemma change_t : "y\<lparr>t := (t x)\<rparr> = x \<Longrightarrow> (et x) = (et y) \<and> (ot x) = (ot y)"
  by (metis ext_inject surjective update_convs(1))

lemma change_et : "y\<lparr>et := (et x)\<rparr> = x \<Longrightarrow> (ot x) = (ot y) \<and> 
      (ec x) = (ec y) \<and> (oc x) = (oc y)"
  by (metis ext_inject surjective update_convs(2))

lemma change_ot: "y\<lparr>ot := (ot x)\<rparr> = x \<Longrightarrow> (et x) = (et y)"
  by (metis ext_inject surjective update_convs(3))

lemma change_ec : "y\<lparr>ec := (ec x)\<rparr> = x \<Longrightarrow> (et x) = (et y) \<and> (ot x) = (ot y) \<and> 
      (oc x) = (oc y) \<and> (t x) = (t y)"
  by (metis ext_inject surjective update_convs(4))

lemma refinement_1 : "(guar_inv p_inv) \<iinter> (guar (et_less \<sqinter> P' p_inv)) \<ge> 
      (guar (et_less \<sqinter> P' p_inv))"
proof -
  have "(P' p_inv) \<sqinter> (et_less \<sqinter> P' p_inv) = (et_less \<sqinter> P' p_inv)" by fast
  then show ?thesis 
    unfolding guar_inv_def using guar_nested order_refl by (metis (no_types, lifting))
qed

lemma refinement_2 : "(guar_inv p_inv) \<iinter> (guar (ot_less \<sqinter> P' p_inv)) \<ge> 
      (guar (ot_less \<sqinter> P' p_inv))" 
proof -
  have "(P' p_inv) \<sqinter> (ot_less \<sqinter> P' p_inv) = (ot_less \<sqinter> P' p_inv)" by fast
  then show ?thesis 
    unfolding guar_inv_def using guar_nested order_refl by (metis (no_types, lifting))
qed

lemma refinement_3 : "(guar (et_less \<sqinter> P' p_inv)) \<iinter> (rely (ot_less \<sqinter> P' p_inv)) \<iinter> 
      \<lbrace>p_inv\<rbrace>;\<lparr>ec_to_0\<rparr>;\<lbrace>p_inv_ext\<rbrace>;\<lparr>q1_25\<rparr> \<ge> 
      (guar (et_less \<sqinter> P' p_inv)) \<iinter> ( ( (rely (ot_less \<sqinter> P' p_inv)) \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>ec_to_0\<rparr> ) ;
      ( (rely (ot_less \<sqinter> P' p_inv)) \<iinter> \<lbrace>p_inv_ext\<rbrace>;\<lparr>q1_25\<rparr> ) )"
proof -
  have "guar g\<^sub>c \<iinter> (rely r\<^sub>c \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>ec_to_0\<rparr>;(\<lbrace>p\<^sub>w\<rbrace>;\<lparr>q1_25\<rparr>)) \<ge> 
        guar g\<^sub>c \<iinter> (rely r\<^sub>c \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>ec_to_0\<rparr>);(rely r\<^sub>c \<iinter> \<lbrace>p_inv_ext\<rbrace>;\<lparr>q1_25\<rparr>)"
    using conj_mono_right rely_seq_distrib by presburger
  then show ?thesis
    by (simp add: local.conj_assoc seq_assoc)
qed

lemma element_argument_1 :
  fixes k\<^sub>a
  assumes "(m, m') \<in> (b0\<^sub>w \<inter> p\<^sub>w \<inter> (fn_less v\<^sub>w (wfr\<^sub>w\<^sup>=) k\<^sub>a) ) \<triangleleft> ( (r\<^sub>w \<union> g\<^sub>w)\<^sup>* \<inter> c\<^sub>w_post )"
  shows "(m, m') \<in> q\<^sub>w\<^sup>* \<triangleright> (p\<^sub>w \<inter> (fn_less v\<^sub>w wfr\<^sub>w k\<^sub>a))"
proof -
  have "m' \<in> p\<^sub>w"
  proof -
    have "(m, m') \<in> (P' p_inv \<inter> (ot_less \<union> et_less))\<^sup>*" 
      using assms unfolding restrict_domain_def by (simp add: inf_commute inf_sup_distrib1)
    then have "(m, m') \<in> P' p_inv" 
      by (induction, auto)
    then show ?thesis using assms unfolding restrict_domain_def by blast
  qed
  moreover have "m' \<in> (fn_less v\<^sub>w wfr\<^sub>w k\<^sub>a)"
  proof -
    have "k\<^sub>a \<le> N + 1"
    proof (rule ccontr)
      assume assm : "\<not>(k\<^sub>a \<le> N + 1)"
      have "(et m) \<le> N + 1" 
        using assms minP_even_upper_bound et_equals_N 
        unfolding restrict_domain_def by fastforce
      then show "False" using assm assms unfolding restrict_domain_def fn_less_def by auto
    qed
    then show ?thesis using assms unfolding restrict_domain_def fn_less_def by auto
  qed
  ultimately show ?thesis 
    unfolding restrict_range_def by auto
qed

lemma element_argument_2 :
  assumes "P (ec s) \<and> (ec s) < (et s) \<and> 
        (inv_loop (ec s) (et s) even) \<and> (inv (et s) even) \<and> 
        (ec s) = k \<and> (et s') = (ec s) \<and>
        (ot s) = (ot s') \<and> (ec s) = (ec s') \<and> (oc s) = (oc s')"
  shows "(s, s') \<in> g\<^sub>1"
proof -
  have "(et s') = minP even" using assms unfolding minP_def inv_loop_def
    using even_non_empty finite_even by (auto, simp add: le_antisym)
  then show ?thesis unfolding inv_def using assms by auto
qed

lemma element_argument_3 :
  assumes "P (ec s) \<and> (ec s) < (et s) \<and> 
        (inv_loop (ec s) (et s) even) \<and> (inv (et s) even) \<and> 
        (ec s) = k \<and> (et s') = (ec s) \<and>
        (ot s) = (ot s') \<and> (ec s) = (ec s') \<and> (oc s) = (oc s')"
 shows "(s, s') \<in> q\<^sub>1"
  using assms unfolding inv_loop_def by auto

lemma element_argument_4 :
  assumes "\<not>(P (ec s)) \<and> (ec s) < (et s) \<and> 
        (inv_loop (ec s) (et s) even) \<and> (inv (et s) even) \<and> 
        (ec s) + 2 = k \<and> (ec s') = (ec s) + 2 \<and>
        (et s) = (et s') \<and> (ot s) = (ot s') \<and> (oc s) = (oc s')"
  shows "(s, s') \<in> g\<^sub>2"
  using assms unfolding inv_loop_def by auto

lemma element_argument_5 :
  assumes "\<not>(P (ec s)) \<and> (ec s) < (et s) \<and> 
        (inv_loop (ec s) (et s) even) \<and> (inv (et s) even) \<and> 
        (ec s) + 2 = k \<and> (ec s') = (ec s) + 2 \<and>
        (et s) = (et s') \<and> (ot s) = (ot s') \<and> (oc s) = (oc s')"
  shows "(s, s') \<in> q\<^sub>2"
proof -
  have "(inv_loop (ec s') (et s') even)"
  proof -
    have "(ec s') \<le> minP even"
    proof -
      have "\<forall>x. x < (ec s) \<longrightarrow> x \<notin> {i |i. i \<in> even \<and> P i}" 
        using assms even_non_empty finite_even unfolding inv_loop_def minP_def by auto
      moreover have "(ec s) + 1 \<notin> {i |i. i \<in> even \<and> P i}"
        using assms unfolding even_def inv_loop_def by fastforce
      moreover have "{x. x < (ec s) + 2} = 
            {x. x < (ec s) \<or> x = (ec s) \<or> x = (ec s) + 1}" by auto
      ultimately have "\<forall>x. x < (ec s) + 2 \<longrightarrow> x \<notin> {i |i. i \<in> even \<and> P i}" 
        using assms by auto
      then show ?thesis unfolding minP_def 
        using assms finite_even even_non_empty by (auto, meson Min_eq_iff not_le)
    qed
    then show ?thesis using assms minP_even_upper_bound 
      unfolding even_def inv_loop_def by auto
  qed
  then show ?thesis using assms by auto
qed

lemma if_assign_1_step : "\<And>k. (p\<^sub>1 \<inter> (e0\<^sub>1 k)) \<triangleleft> (id_bar [Vet]) \<triangleright> (var_eq Vet k) \<subseteq> g\<^sub>1 \<inter> q\<^sub>1" 
proof -
  fix k
  have "(p\<^sub>1 \<inter> (e0\<^sub>1 k)) \<triangleleft> (id_bar [Vet]) \<triangleright> (var_eq Vet k) \<subseteq> 
        {(s, s'). P (ec s) \<and> (ec s) < (et s) \<and> 
        (inv_loop (ec s) (et s) even) \<and> (inv (et s) even) \<and> 
        (ec s) = k \<and> (et s') = (ec s) \<and>
        (ot s) = (ot s') \<and> (ec s) = (ec s') \<and> (oc s) = (oc s')}" 
    unfolding var_eq_def id_bar_def bulk_set_vars_def restrict_domain_def 
      restrict_range_def using change_et by auto
  also have "... \<subseteq> g\<^sub>1 \<inter> q\<^sub>1" 
    using element_argument_2 element_argument_3 by blast
  finally show "(p\<^sub>1 \<inter> (e0\<^sub>1 k)) \<triangleleft> (id_bar [Vet]) \<triangleright> (var_eq Vet k) \<subseteq> g\<^sub>1 \<inter> q\<^sub>1" by simp
qed

lemma if_assign_2_step : "\<And>k. (p\<^sub>2 \<inter> (e0\<^sub>2 k)) \<triangleleft> (id_bar [Vec]) \<triangleright> (var_eq Vec k) \<subseteq> g\<^sub>2 \<inter> q\<^sub>2"
proof -
  fix k
  have "(p\<^sub>2 \<inter> (e0\<^sub>2 k)) \<triangleleft> (id_bar [Vec]) \<triangleright> (var_eq Vec k) \<subseteq> 
        {(s, s'). \<not>(P (ec s)) \<and> (ec s) < (et s) \<and> 
        (inv_loop (ec s) (et s) even) \<and> (inv (et s) even) \<and> 
        (ec s) + 2 = k \<and> (ec s') = (ec s) + 2 \<and>
        (et s) = (et s') \<and> (ot s) = (ot s') \<and> (oc s) = (oc s')}" 
    unfolding var_eq_def id_bar_def bulk_set_vars_def restrict_domain_def 
      restrict_range_def using change_ec by auto
  also have "... \<subseteq> g\<^sub>2 \<inter> q\<^sub>2" 
    using element_argument_4 element_argument_5 by blast
  finally show "(p\<^sub>2 \<inter> (e0\<^sub>2 k)) \<triangleleft> (id_bar [Vec]) \<triangleright> (var_eq Vec k) \<subseteq> g\<^sub>2 \<inter> q\<^sub>2" by simp
qed

subsubsection{*Major Proofs*}
text{*This section contains large proofs which are important to the final proof.*}
lemma step_29_argument : 
  assumes "(m, m') \<in> p_inv \<triangleleft> e29_post \<triangleright> p_inv"
  shows "(m, m') \<in> e28_post"
proof (cases "ec m' \<ge> ot m'")
  case True
  then show ?thesis using assms 
    unfolding inv_loop_def restrict_range_def restrict_domain_def by auto
next
  case f1 : False
  show ?thesis
  proof (cases "et m' = minP even")
    case True
    then show ?thesis using True assms 
      unfolding restrict_range_def restrict_domain_def by auto
  next
    case f2 : False
    show ?thesis 
    proof (cases "N \<in> even")
      case True
      have "N + 1 \<notin> even" using True unfolding even_def by auto
      then have "minP even \<noteq> N + 1" 
        unfolding minP_def using even_non_empty finite_even Min_eq_iff by auto
      then show ?thesis using assms minP_even_upper_bound f1 f2 
        unfolding inv_loop_def inv_def restrict_range_def restrict_domain_def by auto
    next
      case False
      then show ?thesis using assms f1 f2 minP_even_upper_bound minP_odd_upper_bound
        unfolding inv_loop_def inv_def restrict_range_def restrict_domain_def by auto
    qed
  qed
qed

lemma s30_step : "\<And>k. (guar g\<^sub>w) \<iinter> (rely r\<^sub>w) \<iinter> 
          \<ltort>b0\<^sub>w \<inter> p\<^sub>w \<inter> (fn_less v\<^sub>w (wfr\<^sub>w\<^sup>=) k), q\<^sub>w\<^sup>* \<triangleright> (p\<^sub>w \<inter> (fn_less v\<^sub>w wfr\<^sub>w k))\<rtort> \<ge> c\<^sub>w"
proof -
  fix k
  have "(guar g\<^sub>w) \<iinter> (rely r\<^sub>w) \<iinter> 
        \<ltort>b0\<^sub>w \<inter> p\<^sub>w \<inter> (fn_less v\<^sub>w (wfr\<^sub>w\<^sup>=) k), q\<^sub>w\<^sup>* \<triangleright> (p\<^sub>w \<inter> (fn_less v\<^sub>w wfr\<^sub>w k))\<rtort> \<ge> 
        (guar g\<^sub>w) \<iinter> (rely r\<^sub>w) \<iinter> \<ltort>b0\<^sub>w \<inter> p\<^sub>w \<inter> (fn_less v\<^sub>w (wfr\<^sub>w\<^sup>=) k), c\<^sub>w_post\<rtort>"
  proof -
    have "(b0\<^sub>w \<inter> p\<^sub>w \<inter> (fn_less v\<^sub>w (wfr\<^sub>w\<^sup>=) k) ) \<triangleleft> ( (r\<^sub>w \<union> g\<^sub>w)\<^sup>* \<inter> c\<^sub>w_post ) \<subseteq>
      q\<^sub>w\<^sup>* \<triangleright> (p\<^sub>w \<inter> (fn_less v\<^sub>w wfr\<^sub>w k))" using element_argument_1 by auto
    then have "\<lbrace>(b0\<^sub>w \<inter> p\<^sub>w \<inter> (fn_less v\<^sub>w (wfr\<^sub>w\<^sup>=) k) )\<rbrace>;
          \<lparr>q\<^sub>w\<^sup>* \<triangleright> (p\<^sub>w \<inter> (fn_less v\<^sub>w wfr\<^sub>w k))\<rparr> \<ge>
          \<lbrace>(b0\<^sub>w \<inter> p\<^sub>w \<inter> (fn_less v\<^sub>w (wfr\<^sub>w\<^sup>=) k) )\<rbrace>;\<lparr>( (r\<^sub>w \<union> g\<^sub>w)\<^sup>* \<inter> c\<^sub>w_post )\<rparr>" 
      using spec_strengthen seq_mono_right specpre_pre_internalise 
        specpre_strengthen_post unfolding specpre_def by (metis (no_types, lifting))
    then have "(guar g\<^sub>w) \<iinter> (rely r\<^sub>w) \<iinter> \<lbrace>(b0\<^sub>w \<inter> p\<^sub>w \<inter> (fn_less v\<^sub>w (wfr\<^sub>w\<^sup>=) k) )\<rbrace>;
          \<lparr>q\<^sub>w\<^sup>* \<triangleright> (p\<^sub>w \<inter> (fn_less v\<^sub>w wfr\<^sub>w k))\<rparr> \<ge>
          (guar g\<^sub>w) \<iinter> (rely r\<^sub>w) \<iinter> \<lbrace>(b0\<^sub>w \<inter> p\<^sub>w \<inter> (fn_less v\<^sub>w (wfr\<^sub>w\<^sup>=) k) )\<rbrace>;
          \<lparr>( (r\<^sub>w \<union> g\<^sub>w)\<^sup>* \<inter> c\<^sub>w_post )\<rparr>" using conj_mono_right by blast
    moreover have "... \<ge> (guar g\<^sub>w) \<iinter> (rely r\<^sub>w) \<iinter> 
          \<lbrace>(b0\<^sub>w \<inter> p\<^sub>w \<inter> (fn_less v\<^sub>w (wfr\<^sub>w\<^sup>=) k) )\<rbrace>;\<lparr>c\<^sub>w_post\<rparr>"
      using conj_mono_right move_pre conj.sync_assoc order_refl conj.left_commute 
        spec_trading_refinement seq_mono_right conj_mono_right 
        order_refl conj.left_idem by presburger
    ultimately show ?thesis unfolding specpre_def by auto
  qed
  also have "... \<ge> (rely r\<^sub>w) \<iinter> (guar g\<^sub>w) \<iinter>  \<ltort>c\<^sub>w_pre, c\<^sub>w_post\<rtort>"
    using specpre_weaken_pre conj_mono_right seq_mono_left conj.sync_commute 
      subset_3 unfolding specpre_def by auto
  finally show "(guar g\<^sub>w) \<iinter> (rely r\<^sub>w) \<iinter> 
        \<ltort>b0\<^sub>w \<inter> p\<^sub>w \<inter> (fn_less v\<^sub>w (wfr\<^sub>w\<^sup>=) k), q\<^sub>w\<^sup>* \<triangleright> (p\<^sub>w \<inter> (fn_less v\<^sub>w wfr\<^sub>w k))\<rtort> \<ge> c\<^sub>w" 
    unfolding specpre_def by simp
qed

lemma s30_while_refinement : "(guar g\<^sub>w) \<iinter> (rely r\<^sub>w) \<iinter> 
      \<ltort>p\<^sub>w, ((dec wfr\<^sub>w\<^sup>= v\<^sub>w) \<inter> q\<^sub>w\<^sup>*) \<triangleright> (p\<^sub>w \<inter> b1\<^sub>w)\<rtort> \<ge> (While b\<^sub>w do c\<^sub>w)"
proof -
  have g_reflexive : "refl g\<^sub>w" unfolding refl_on_def by auto
  moreover have wellfounded : "wf wfr\<^sub>w" 
    using finite_acyclic_wf unfolding acyclic_def using wfr_ordered finite_wfr by blast  
  moreover have wfr_trans : "trans wfr\<^sub>w" using trans_def by fastforce
  moreover have single_reference_b : "single_reference b\<^sub>w r\<^sub>w" 
    using estable_def eval.simps(2) by fastforce
  moreover have tolerate_interference: "tolerates_interference p\<^sub>w (q\<^sub>w\<^sup>* \<triangleright> p\<^sub>w) r\<^sub>w"
    unfolding tolerates_interference_def stable_def 
      restrict_range_def restrict_domain_def by auto
  moreover have b_boolean : "p\<^sub>w \<subseteq> expr_type b\<^sub>w boolean" 
    unfolding expr_type_def using expr_false_simp expr_true_simp by auto
  moreover have pb_establishes_b0 :  "p\<^sub>w \<inter> (expr_eq b\<^sub>w true) \<subseteq> b0\<^sub>w" 
    using expr_true_simp by blast
  moreover have pr_maintains_b0: "stable b0\<^sub>w (p\<^sub>w \<triangleleft> r\<^sub>w)"
    unfolding stable_def restrict_domain_def by auto
  moreover have pnegb_establishes_b1: "p\<^sub>w \<inter> (expr_eq b\<^sub>w false) \<subseteq> b1\<^sub>w" 
    using expr_false_simp by auto
  moreover have pr_maintains_b1: "stable b1\<^sub>w (p\<^sub>w \<triangleleft> r\<^sub>w)"
    unfolding stable_def restrict_domain_def by auto
  moreover have pr_variant: "p\<^sub>w \<triangleleft> r\<^sub>w \<subseteq> (dec wfr\<^sub>w\<^sup>= v\<^sub>w)" 
    unfolding restrict_domain_def dec_variant_def by auto
  moreover have step: "\<And>k. (guar g\<^sub>w) \<iinter> (rely r\<^sub>w) \<iinter> 
        \<ltort>b0\<^sub>w \<inter> p\<^sub>w \<inter> (fn_less v\<^sub>w (wfr\<^sub>w\<^sup>=) k), q\<^sub>w\<^sup>* \<triangleright> (p\<^sub>w \<inter> (fn_less v\<^sub>w wfr\<^sub>w k))\<rtort> \<ge> c\<^sub>w" 
    using s30_step by blast
  ultimately show ?thesis using rely_while by blast
qed

lemma s32_if_refinement : "(rely r\<^sub>i) \<iinter> \<ltort>p\<^sub>i, q\<^sub>i\<rtort> \<ge> (If b\<^sub>i then ((rely r\<^sub>i) \<iinter> \<ltort>b0\<^sub>i \<inter> p\<^sub>i, q\<^sub>i\<rtort>) 
      else ((rely r\<^sub>i)\<iinter>\<ltort>b1\<^sub>i \<inter> p\<^sub>i,q\<^sub>i\<rtort>))"
proof -
  have single_reference_b: "single_reference b\<^sub>i r\<^sub>i" by simp
  moreover have tolerate_interference: "tolerates_interference p\<^sub>i q\<^sub>i r\<^sub>i"
    unfolding tolerates_interference_def restrict_domain_def using stable_simp_1 by auto
  moreover have b_boolean: "p\<^sub>i \<subseteq> expr_type b\<^sub>i boolean" 
    unfolding expr_type_def expr_eq_def false_Value_def true_Value_def by auto
  moreover have pb_establishes_b0: "p\<^sub>i \<inter> (expr_eq b\<^sub>i (true)) \<subseteq> b0\<^sub>i" 
    by (simp add: expr_eq_def true_Value_def)
  moreover have pr_maintains_b0: "stable b0\<^sub>i (p\<^sub>i \<triangleleft> r\<^sub>i)"
    unfolding stable_def restrict_domain_def by auto
  moreover have pnegb_establishes_b1: "p\<^sub>i \<inter> (expr_eq b\<^sub>i (false)) \<subseteq> b1\<^sub>i" 
    by (simp add: expr_eq_def false_Value_def)
  moreover have pr_maintains_b1: "stable b1\<^sub>i (p\<^sub>i \<triangleleft> r\<^sub>i)"
    unfolding stable_def restrict_domain_def by auto
  ultimately show ?thesis using if_introduce by blast
qed

subsubsection{*Assignment Proofs*}
text{*This section contains proofs of refinements of specifications to assignments.*}
lemma initial_assignment_et : "(rely ({(k, k'). k' = k})) \<iinter> \<lparr>{(k, k'). (et k') = N}\<rparr> \<ge> 
      (Vet::= (Constant N))"
proof -
  have "(rely ({(k, k'). k' = k})) \<iinter> \<lparr>{(k, k'). (et k') = N}\<rparr> \<ge> 
        (rely r\<^sub>e) \<iinter> (guar g\<^sub>e) \<iinter> \<lbrace>p\<^sub>e\<rbrace>;([Vet] :\<^sub>f \<lparr>q\<^sub>e\<rparr>)" 
    using assert_top conj_mono_right guar_introduce rely_def3 
      var_frame_def rely_guar_def by auto
  also have "... \<ge> (Vet ::= e\<^sub>e)"
  proof -
    have refl_g : "refl g\<^sub>e" unfolding refl_on_def by simp
    moreover have single_ref: "single_reference e\<^sub>e r\<^sub>e" by simp
    moreover have stable_p: "stable p\<^sub>e r\<^sub>e" unfolding stable_def by auto
    moreover have tolerate: "tolerates_interference p\<^sub>e q\<^sub>e r\<^sub>e"
      unfolding tolerates_interference_def stable_def restrict_domain_def by auto
    moreover have e_impl_e0: "\<And>k. p\<^sub>e \<inter> (expr_eq e\<^sub>e k) \<subseteq> (e0\<^sub>e k)"
      unfolding expr_eq_def by simp
    moreover have stable_e0: "\<And>k. stable (e0\<^sub>e k) (p\<^sub>e \<triangleleft> r\<^sub>e)" unfolding stable_def by simp
    moreover have assign: "\<And>k. (p\<^sub>e \<inter> (e0\<^sub>e k)) \<triangleleft> (id_bar [Vet]) \<triangleright> (var_eq Vet k) \<subseteq> g\<^sub>e \<inter> q\<^sub>e"
      unfolding restrict_domain_def restrict_range_def id_bar_def var_eq_def by fastforce
    ultimately show ?thesis using rely_guar_assignment by presburger
  qed
  finally show ?thesis .
qed

lemma initial_assignment_ot : "( (rely ({(k, k'). k' = k})) \<iinter> 
      \<lparr>{(k, k'). (et k') = (et k) \<and> (ot k') = N}\<rparr> ) \<ge> (Vot::= (Constant N))"
proof -
  have "( (rely ({(k, k'). k' = k})) \<iinter> \<lparr>{(k, k'). (et k') = (et k) \<and> (ot k') = N}\<rparr> ) \<ge> 
        (rely r\<^sub>o) \<iinter> (guar g\<^sub>o) \<iinter> \<lbrace>p\<^sub>o\<rbrace>;([Vot] :\<^sub>f \<lparr>q\<^sub>o\<rparr>)" 
    using assert_top conj_mono_right guar_introduce rely_def3 rely_guar_def 
      var_frame_def by auto
  also have "... \<ge> (Vot ::= e\<^sub>o)"
  proof -
    have "refl g\<^sub>o" unfolding refl_on_def by simp
    moreover have single_ref: "single_reference e\<^sub>o r\<^sub>o" by simp
    moreover have stable_p: "stable p\<^sub>o r\<^sub>o" unfolding stable_def by auto
    moreover have tolerate: "tolerates_interference p\<^sub>o q\<^sub>o r\<^sub>o"
      unfolding tolerates_interference_def stable_def restrict_domain_def by auto
    moreover have e_impl_e0: "\<And>k. p\<^sub>o \<inter> (expr_eq e\<^sub>o k) \<subseteq> (e0\<^sub>o k)"
      unfolding expr_eq_def by auto
    moreover have stable_e0: "\<And>k. stable (e0\<^sub>o k) (p\<^sub>o \<triangleleft> r\<^sub>o)" unfolding stable_def by simp
    moreover have assign: "\<And>k. (p\<^sub>o \<inter> (e0\<^sub>o k)) \<triangleleft> (id_bar [Vot]) \<triangleright> (var_eq Vot k) \<subseteq> g\<^sub>o \<inter> q\<^sub>o"
      unfolding restrict_domain_def restrict_range_def id_bar_def var_eq_def 
      using change_ot by fastforce
    ultimately show ?thesis using rely_guar_assignment by presburger
  qed
  finally show ?thesis .
qed

lemma initial_assignment : "var_init \<ge> (Vet::= (Constant N));(Vot::= (Constant N))"
proof -
  have "relcomp {(k, k'). (et k') = N} {(k, k'). (et k') = (et k) \<and> (ot k') = N} \<subseteq> 
        {(k, k'). (ot k') = N \<and> (et k') = N}" by auto
  then have "\<lparr>{(k, k'). (ot k') = N \<and> (et k') = N}\<rparr> \<ge> 
        \<lparr>{(k, k'). (et k') = N}\<rparr>;\<lparr>{(k, k'). (et k') = (et k) \<and> (ot k') = N}\<rparr>" 
    using spec_chain by blast
  then have "var_init \<ge> (rely ({(k, k'). k' = k})) \<iinter> 
        \<lparr>{(k, k'). (et k') = N}\<rparr>;\<lparr>{(k, k'). (et k') = (et k) \<and> (ot k') = N}\<rparr>"
    by (simp add: conj_mono_right)
  also have "... \<ge> ( (rely ({(k, k'). k' = k})) \<iinter> \<lparr>{(k, k'). (et k') = N}\<rparr> ) ;
        ( (rely ({(k, k'). k' = k})) \<iinter> \<lparr>{(k, k'). (et k') = (et k) \<and> (ot k') = N}\<rparr> )" 
    using rely_seq_distrib by auto
  also have "... \<ge> (Vet::= (Constant N));(Vot::= (Constant N))" 
    using initial_assignment_ot initial_assignment_et seq_mono by blast
  finally show ?thesis by auto
qed

lemma assign_ec : "var_init_ec \<ge> (Vec::= (Constant 0))"
proof -
  have "var_init_ec \<ge> ( (guar g\<^sub>c) \<iinter> (rely r\<^sub>c) \<iinter> \<lbrace>p\<^sub>c\<rbrace>;([Vec] :\<^sub>f \<lparr>q\<^sub>c\<rparr>) )" 
    using conj_mono_right guar_introduce seq_mono_right var_frame_def by auto
  also have "... \<ge> (rely r\<^sub>c) \<iinter> (guar g\<^sub>c) \<iinter> \<lbrace>p\<^sub>c\<rbrace>;([Vec] :\<^sub>f \<lparr>q\<^sub>c\<rparr>)" 
    using conj_commute conj_assoc by auto
  also have "... \<ge> (Vec::= e\<^sub>c)"
  proof -
    have refl: "refl g\<^sub>c" unfolding refl_on_def by simp
    moreover have single_ref: "single_reference e\<^sub>c r\<^sub>c" by simp
    moreover have stable_p: "stable p\<^sub>c r\<^sub>c" unfolding stable_def by auto
    moreover have tolerate: "tolerates_interference p\<^sub>c q\<^sub>c r\<^sub>c"
      unfolding tolerates_interference_def stable_def restrict_domain_def by auto
    moreover have e_impl_e0: "\<And>k. p\<^sub>c \<inter> (expr_eq e\<^sub>c k) \<subseteq> (e0\<^sub>c k)"
      unfolding expr_eq_def by simp
    moreover have stable_e0: "\<And>k. stable (e0\<^sub>c k) (p\<^sub>c \<triangleleft> r\<^sub>c)" unfolding stable_def by auto
    moreover have assign: "\<And>k. (p\<^sub>c \<inter> (e0\<^sub>c k)) \<triangleleft> (id_bar [Vec]) \<triangleright> (var_eq Vec k) \<subseteq> g\<^sub>c \<inter> q\<^sub>c"
    proof -
      fix k
      have "{(x, y). bulk_set_vars [Vec] x y = x} \<subseteq> 
            {(x,y). et x = et y \<and> ot x = ot y \<and> oc x = oc y \<and> t x = t y }"
        using change_ec by auto
      then show "(p\<^sub>c \<inter> (e0\<^sub>c k)) \<triangleleft> (id_bar [Vec]) \<triangleright> (var_eq Vec k) \<subseteq> g\<^sub>c \<inter> q\<^sub>c"
        unfolding restrict_domain_def restrict_range_def id_bar_def var_eq_def by auto
    qed
    ultimately show ?thesis using rely_guar_assignment by presburger
  qed
  finally show ?thesis .
qed

lemma post_assignment : "post_assign_t \<ge> (Vt::= e\<^sub>t)"
proof -
  have "post_assign_t \<ge> (rely r\<^sub>t) \<iinter> (guar g\<^sub>t) \<iinter> \<lbrace>p\<^sub>t\<rbrace>;([Vt] :\<^sub>f \<lparr>q\<^sub>t\<rparr>)" 
    by (metis (no_types, lifting) assert_top conj.sync_commute 
        conj_mono_right guar_introduce seq_nil_left var_frame_def)
  also have "... \<ge> (Vt::= e\<^sub>t)"
  proof -
    have "refl g\<^sub>t" unfolding refl_on_def by simp
    moreover have single_ref: "single_reference e\<^sub>t r\<^sub>t" using estable_def by fastforce
    moreover have stable_p: "stable p\<^sub>t r\<^sub>t" unfolding stable_def by auto
    moreover have tolerate: "tolerates_interference p\<^sub>t q\<^sub>t r\<^sub>t"  
      unfolding tolerates_interference_def stable_def restrict_domain_def by auto
    moreover have e_impl_e0: "\<And>k. p\<^sub>t \<inter> (expr_eq e\<^sub>t k) \<subseteq> (e0\<^sub>t k)"
      unfolding expr_eq_def by auto
    moreover have stable_e0: "\<And>k. stable (e0\<^sub>t k) (p\<^sub>t \<triangleleft> r\<^sub>t)"
      unfolding stable_def restrict_domain_def by auto
    moreover have assign: "\<And>k. (p\<^sub>t \<inter> (e0\<^sub>t k)) \<triangleleft> (id_bar [Vt]) \<triangleright> (var_eq Vt k) \<subseteq> g\<^sub>t \<inter> q\<^sub>t"
    proof -
      fix k
      have "{(x, y). bulk_set_vars [Vt] x y = x} \<subseteq> {(x,y). et x = et y \<and> ot x = ot y}"
        using change_t by auto
      then show "(p\<^sub>t \<inter> (e0\<^sub>t k)) \<triangleleft> (id_bar [Vt]) \<triangleright> (var_eq Vt k) \<subseteq> g\<^sub>t \<inter> q\<^sub>t" 
        unfolding restrict_domain_def restrict_range_def id_bar_def var_eq_def by auto
    qed
    ultimately show ?thesis using rely_guar_assignment by presburger
  qed
  finally show ?thesis .
qed

lemma if_assign_1 : "if1 \<ge> (Vet::= e\<^sub>1)"
proof -
  have "if1 \<ge> (rely r\<^sub>1) \<iinter> (guar g\<^sub>1) \<iinter> \<lbrace>p\<^sub>1\<rbrace>;([Vet] :\<^sub>f \<lparr>q\<^sub>1\<rparr>)" using guar_introduce var_frame_def
      conj.sync_commute conj_mono_right seq_mono_right specpre_def by presburger
  also have "... \<ge> (Vet::= e\<^sub>1)"
  proof -
    have "refl g\<^sub>1" unfolding refl_on_def by simp
    moreover have single_ref: "single_reference e\<^sub>1 r\<^sub>1" using estable_def by fastforce
    moreover have stable_p: "stable p\<^sub>1 r\<^sub>1" unfolding stable_def by auto
    moreover have tolerate: "tolerates_interference p\<^sub>1 q\<^sub>1 r\<^sub>1"
      unfolding tolerates_interference_def restrict_domain_def using stable_simp_2 by auto
    moreover have e_impl_e0: "\<And>k. p\<^sub>1 \<inter> (expr_eq e\<^sub>1 k) \<subseteq> (e0\<^sub>1 k)"
      unfolding expr_eq_def by auto
    moreover have stable_e0: "\<And>k. stable (e0\<^sub>1 k) (p\<^sub>1 \<triangleleft> r\<^sub>1)"
      unfolding stable_def restrict_domain_def by auto
    moreover have assign: "\<And>k. (p\<^sub>1 \<inter> (e0\<^sub>1 k)) \<triangleleft> (id_bar [Vet]) \<triangleright> (var_eq Vet k) \<subseteq> g\<^sub>1 \<inter> q\<^sub>1" 
      using if_assign_1_step by auto
    ultimately show ?thesis using rely_guar_assignment by presburger
  qed
  finally show ?thesis by simp
qed

lemma if_assign_2 : "if2 \<ge> (Vec::= e\<^sub>2)"
proof -               
  have "if2 \<ge> (rely r\<^sub>2) \<iinter> (guar g\<^sub>2) \<iinter> \<lbrace>p\<^sub>2\<rbrace>;([Vec] :\<^sub>f \<lparr>q\<^sub>2\<rparr>)" using guar_introduce var_frame_def
      conj.sync_commute conj_mono_right seq_mono_right specpre_def by presburger
  also have "... \<ge> (Vec::= e\<^sub>2)"
  proof -
    have "refl g\<^sub>2" unfolding refl_on_def by simp
    moreover have single_ref: "single_reference e\<^sub>2 r\<^sub>2" using estable_def by fastforce
    moreover have stable_p: "stable p\<^sub>2 r\<^sub>2" unfolding stable_def by auto
    moreover have tolerate: "tolerates_interference p\<^sub>2 q\<^sub>2 r\<^sub>2" 
      unfolding tolerates_interference_def restrict_domain_def using stable_simp_3 by auto
    moreover have e_impl_e0: "\<And>k. p\<^sub>2 \<inter> (expr_eq e\<^sub>2 k) \<subseteq> (e0\<^sub>2 k)"
      unfolding expr_eq_def by auto
    moreover have stable_e0: "\<And>k. stable (e0\<^sub>2 k) (p\<^sub>2 \<triangleleft> r\<^sub>2)"
      unfolding stable_def restrict_domain_def by auto
    moreover have assign: "\<And>k. (p\<^sub>2 \<inter> (e0\<^sub>2 k)) \<triangleleft> (id_bar [Vec]) \<triangleright> (var_eq Vec k) \<subseteq> g\<^sub>2 \<inter> q\<^sub>2"
      using if_assign_2_step by auto
    ultimately show ?thesis using rely_guar_assignment by presburger
  qed
  finally show ?thesis by simp
qed

subsubsection{*Even Refinement*}
text{*This section contains the refinement of the even thread as described 
in section 4.3 of \cite{AGTRGT}.*}
lemma even_refinement : "(guar (et_less \<sqinter> P' p_inv)) \<iinter> (rely (ot_less \<sqinter> P' p_inv)) \<iinter> 
      \<lbrace>p_inv\<rbrace>;\<lparr>q1_25\<rparr> \<ge> (Vec::= (Constant 0)) ; 
      (While b\<^sub>w do (If b\<^sub>i then (Vet::= e\<^sub>1) else (Vec::= e\<^sub>2)))"
proof -
  have step_28 : "(guar (et_less \<sqinter> P' p_inv)) \<iinter> (rely (ot_less \<sqinter> P' p_inv)) \<iinter> 
        \<lbrace>p_inv\<rbrace>;\<lparr>q1_25\<rparr> \<ge> 
        (Vec::= (Constant 0));
        ( (guar (et_less \<sqinter> P' p_inv)) \<iinter> (rely (ot_less \<sqinter> P' p_inv)) \<iinter> \<lbrace>p_inv_ext\<rbrace>;\<lparr>e28_post\<rparr> )"
  proof -
    have "q1_25 = relcomp UNIV q1_25" by auto
    then have "\<lbrace>p_inv\<rbrace>;\<lparr>q1_25\<rparr> \<ge> \<lbrace>p_inv\<rbrace>;\<lparr>UNIV\<rparr>;\<lparr>q1_25\<rparr>" 
      using spec_chain seq_mono_right seq_assoc by auto
    also have "... \<ge> \<lbrace>p_inv\<rbrace>;\<lparr>p_inv \<triangleleft> UNIV\<rparr>;\<lparr>q1_25\<rparr>" 
      using specpre_pre_internalise unfolding specpre_def by auto
    also have "... \<ge> \<lbrace>p_inv\<rbrace>;\<lparr>p_inv \<triangleleft> UNIV \<triangleright> p_inv_ext\<rparr>;\<lbrace>p_inv_ext\<rbrace>;\<lparr>q1_25\<rparr>" 
      using seq_mono_right seq_assoc
      by (simp add: spec_test_post_extract test_seq_assert test_seq_refine)
    also have "... \<ge> \<lbrace>p_inv\<rbrace>;\<lparr>p_inv \<triangleleft> ec_to_0\<rparr>;\<lbrace>p_inv_ext\<rbrace>;\<lparr>q1_25\<rparr>"
      using spec_strengthen subset_1 seq_mono_left seq_mono_right by auto
    also have "... \<ge> \<lbrace>p_inv\<rbrace>;\<lparr>ec_to_0\<rparr>;\<lbrace>p_inv_ext\<rbrace>;\<lparr>q1_25\<rparr>" 
      using seq_mono_left specpre_def specpre_ref_spec specpre_pre_internalise by auto
    finally have "\<lbrace>p_inv\<rbrace>;\<lparr>q1_25\<rparr> \<ge> \<lbrace>p_inv\<rbrace>;\<lparr>ec_to_0\<rparr>;\<lbrace>p_inv_ext\<rbrace>;\<lparr>q1_25\<rparr>" by simp
    then have "(guar (et_less \<sqinter> P' p_inv)) \<iinter> (rely (ot_less \<sqinter> P' p_inv)) \<iinter> 
          \<lbrace>p_inv\<rbrace>;\<lparr>q1_25\<rparr> \<ge> 
          (guar (et_less \<sqinter> P' p_inv)) \<iinter> (rely (ot_less \<sqinter> P' p_inv)) \<iinter> 
          \<lbrace>p_inv\<rbrace>;\<lparr>ec_to_0\<rparr>;\<lbrace>p_inv_ext\<rbrace>;\<lparr>q1_25\<rparr>" 
      using conj_mono_right conj_assoc by fast
    also have "... \<ge> (guar (et_less \<sqinter> P' p_inv)) \<iinter> 
          ( ( (rely (ot_less \<sqinter> P' p_inv)) \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>ec_to_0\<rparr> ) ;
          ( (rely (ot_less \<sqinter> P' p_inv)) \<iinter> \<lbrace>p_inv_ext\<rbrace>;\<lparr>q1_25\<rparr> ) )"
      using refinement_3 by auto
    also have "... \<ge> var_init_ec;
          ( (guar (et_less \<sqinter> P' p_inv)) \<iinter> (rely (ot_less \<sqinter> P' p_inv)) \<iinter> 
          \<lbrace>p_inv_ext\<rbrace>;\<lparr>q1_25\<rparr> )" 
      by (metis (no_types, lifting) conj.sync_assoc guar_distrib_seq)
    moreover have "... \<ge> var_init_ec; 
          ( (guar (et_less \<sqinter> P' p_inv)) \<iinter> (rely (ot_less \<sqinter> P' p_inv)) \<iinter> 
          \<lbrace>p_inv_ext\<rbrace>;\<lparr>e28_post\<rparr> )"
      using subset_4 specpre_strengthen_post conj_mono_right seq_mono_right 
      unfolding specpre_def by auto
    moreover have "... \<ge> (Vec::= (Constant 0)); 
          ( (guar (et_less \<sqinter> P' p_inv)) \<iinter> (rely (ot_less \<sqinter> P' p_inv)) \<iinter> 
          \<lbrace>p_inv_ext\<rbrace>;\<lparr>e28_post\<rparr> )" 
      using assign_ec seq_mono_left by blast
    ultimately show ?thesis by auto
  qed
  also have step_29 : "... \<ge> (Vec::= (Constant 0));
        ( (guar (et_less \<sqinter> P' p_inv)) \<iinter> (rely (ot_less \<sqinter> P' p_inv)) \<iinter> \<lbrace>p_inv_ext\<rbrace>;\<lparr>e29_post\<rparr> )"
  proof -
    have r_implies_P' : "(ot_less \<sqinter> P' p_inv) \<subseteq> P' p_inv" by blast
    moreover have g_implies_P' : "(et_less \<sqinter> P' p_inv) \<subseteq> P' p_inv" by blast
    moreover have refinement : "p_inv \<triangleleft> e29_post \<triangleright> p_inv \<subseteq> e28_post" 
      using step_29_argument by auto
    ultimately have "(rely (ot_less \<sqinter> P' p_inv)) \<iinter> (guar (et_less \<sqinter> P' p_inv)) \<iinter> 
          \<lbrace>p_inv\<rbrace>;\<lparr>e28_post\<rparr> \<ge> 
          (rely (ot_less \<sqinter> P' p_inv)) \<iinter> (guar (et_less \<sqinter> P' p_inv)) \<iinter> 
          \<lbrace>p_inv\<rbrace>;\<lparr>e29_post\<rparr>" 
      using strengthen_under_invariant by presburger
    then have "\<lbrace>p_inv\<rbrace>;((rely (ot_less \<sqinter> P' p_inv)) \<iinter> 
          (guar (et_less \<sqinter> P' p_inv)) \<iinter> \<lparr>e28_post\<rparr>) \<ge>
          \<lbrace>p_inv\<rbrace>;( (rely (ot_less \<sqinter> P' p_inv)) \<iinter> 
          (guar (et_less \<sqinter> P' p_inv)) \<iinter> \<lparr>e29_post\<rparr> )" 
      using initial_assert_rely_generic by presburger
    moreover have "p_inv_ext \<subseteq> p_inv" by blast
    ultimately have "\<lbrace>p_inv_ext\<rbrace>;((rely (ot_less \<sqinter> P' p_inv)) \<iinter> 
          (guar (et_less \<sqinter> P' p_inv)) \<iinter> \<lparr>e28_post\<rparr>) \<ge> 
          \<lbrace>p_inv_ext\<rbrace>;((rely (ot_less \<sqinter> P' p_inv)) \<iinter> 
          (guar (et_less \<sqinter> P' p_inv)) \<iinter> \<lparr>e29_post\<rparr>)" 
      using pre_strengthen_both by blast
    then have "(rely (ot_less \<sqinter> P' p_inv)) \<iinter> (guar (et_less \<sqinter> P' p_inv)) \<iinter> 
          \<lbrace>p_inv_ext\<rbrace>;\<lparr>e28_post\<rparr> \<ge> 
          (rely (ot_less \<sqinter> P' p_inv)) \<iinter> (guar (et_less \<sqinter> P' p_inv)) \<iinter> 
          \<lbrace>p_inv_ext\<rbrace>;\<lparr>e29_post\<rparr>" 
      using initial_assert_rely_generic by metis
    then have "(guar (et_less \<sqinter> P' p_inv)) \<iinter> (rely (ot_less \<sqinter> P' p_inv)) \<iinter> 
          \<lbrace>p_inv_ext\<rbrace>;\<lparr>e28_post\<rparr> \<ge> 
          (guar (et_less \<sqinter> P' p_inv)) \<iinter> (rely (ot_less \<sqinter> P' p_inv)) \<iinter> 
          \<lbrace>p_inv_ext\<rbrace>;\<lparr>e29_post\<rparr>" 
      using conj.sync_commute initial_assert_rely_generic by auto
    moreover have "... \<ge> (guar (et_less \<sqinter> P' p_inv)) \<iinter> (rely ot_less) \<iinter> \<lbrace>p_inv_ext\<rbrace>;\<lparr>e29_post\<rparr>"
      using rely_weaken conj_mono_left conj_mono_right subset_5 by presburger
    ultimately show ?thesis using seq_mono_right by blast
  qed
  also have step_30 : "... \<ge> (Vec::= (Constant 0)); (While b\<^sub>w do c\<^sub>w)"
  proof -
    have "(guar (et_less \<sqinter> P' p_inv)) \<iinter> (rely (ot_less \<sqinter> P' p_inv)) \<iinter> 
          \<lbrace>p_inv_ext\<rbrace>;\<lparr>e29_post\<rparr> \<ge> 
          (guar g\<^sub>w) \<iinter> (rely r\<^sub>w) \<iinter> \<ltort>p\<^sub>w, ((dec wfr\<^sub>w\<^sup>= v\<^sub>w) \<inter> q\<^sub>w\<^sup>*) \<triangleright> (p\<^sub>w \<inter> b1\<^sub>w)\<rtort>"
      using spec_strengthen subset_2 conj_mono_right seq_mono_right unfolding specpre_def by auto
    also have "... \<ge> (While b\<^sub>w do c\<^sub>w)" using s30_while_refinement by blast
    finally have "(guar (et_less \<sqinter> P' p_inv)) \<iinter> (rely (ot_less \<sqinter> P' p_inv)) \<iinter> 
          \<lbrace>p_inv_ext\<rbrace>;\<lparr>e29_post\<rparr> \<ge> (While b\<^sub>w do c\<^sub>w)" by simp
    then show ?thesis using seq_mono_right by blast
  qed
  also have step_31 : "... \<ge> (Vec::= (Constant 0)) ; (While b\<^sub>w do e31_loop)"
  proof -
    have "c\<^sub>w \<ge> e31_loop" 
      using rely_weaken subset_6 conj_mono_right conj_mono_left by presburger
    then show ?thesis using conj_mono_right conj_mono_left seq_mono_right while_mono by blast
  qed
  also have step_32 : "... \<ge> (Vec::= (Constant 0)) ; (While b\<^sub>w do (If b\<^sub>i then if1 else if2))"
  proof -
    have "e31_loop \<ge> (guar g\<^sub>i) \<iinter> (rely r\<^sub>i) \<iinter> \<lbrace>p\<^sub>i\<rbrace>;\<lparr>q\<^sub>i\<rparr>" by (simp add: conj.sync_commute)
    also have "... \<ge> (guar g\<^sub>i) \<iinter> (If b\<^sub>i then ((rely r\<^sub>i) \<iinter> \<ltort>b0\<^sub>i \<inter> p\<^sub>i, q\<^sub>i\<rtort>) 
          else ((rely r\<^sub>i) \<iinter> \<ltort>b1\<^sub>i \<inter> p\<^sub>i,q\<^sub>i\<rtort>))" 
      using s32_if_refinement conj_mono_right 
      by (metis (no_types, lifting) conj.sync_assoc specpre_def)
    also have "... \<ge>  (If b\<^sub>i then if1 else if2)" 
      using refl_1 guar_if_distrib conj_assoc by fastforce
    finally have "e31_loop \<ge> ..." by simp
    then show ?thesis using seq_mono_right specpre_def while_mono by blast
  qed
  also have step_33 : "... \<ge> (Vec::= (Constant 0));
        (While b\<^sub>w do (If b\<^sub>i then (Vet::= e\<^sub>1) else if2))" 
    using if_assign_1 if_mono_left seq_mono_right while_mono by blast
  also have step_34 : "... \<ge> (Vec::= (Constant 0));
        (While b\<^sub>w do (If b\<^sub>i then (Vet::= e\<^sub>1) else (Vec::= e\<^sub>2)))" 
    using if_assign_2 if_mono_right seq_mono_right while_mono by blast
  finally show ?thesis by auto
qed

subsubsection{*Odd Refinement*}
text{*The proof of the odd thread is trivial given the proof of the even thread. 
A complete proof is unneccessary given the even thread proof and so is not included here.*}
lemma odd_refinement : "(guar (ot_less \<sqinter> P' p_inv)) \<iinter> (rely (et_less \<sqinter> P' p_inv)) \<iinter> 
      \<lbrace>p_inv\<rbrace>;\<lparr>q2_25\<rparr> \<ge> 
      (Voc::= (Constant 1)) ; 
      (While b\<^sub>w\<^sub>o do (If b\<^sub>i\<^sub>o then (Vot::= e\<^sub>1\<^sub>o) else (Voc::= e\<^sub>2\<^sub>o)))" 
  sorry

subsubsection{*Final Proof*}
text{*This Section shows the final proof of the findP problem as described in section 4 of \cite{AGTRGT}.*}
theorem findP_proof : 
  shows "(rely (no_change)) \<iinter> \<lparr>{(k, k'). (t k') = minP nats}\<rparr> \<ge> 
  (Vet::= (Constant N));(Vot::= (Constant N)) ;         
  (((Vec::= (Constant 0)) ; (While b\<^sub>w do (If b\<^sub>i then (Vet::= e\<^sub>1) else (Vec::= e\<^sub>2)))) \<parallel>
  ((Voc::= (Constant 1)) ; (While b\<^sub>w\<^sub>o do (If b\<^sub>i\<^sub>o then (Vot::= e\<^sub>1\<^sub>o) else (Voc::= e\<^sub>2\<^sub>o)))));
  (Vt::= e\<^sub>t)"
proof -
  have step_22: "(rely no_change) \<iinter> \<lparr>{(k, k'). (t k') = minP nats}\<rparr> \<ge> 
        (Vet::= (Constant N));(Vot::= (Constant N));
        ( (guar_inv p_inv) \<iinter> (rely (no_change)) \<iinter> 
        \<lbrace>p_inv\<rbrace>;\<lparr>{(k, k'). (t k') = minP nats}\<rparr> )"
  proof -
    have "{(k, k'). (t k') = minP nats} = relcomp UNIV {(k, k'). (t k') = minP nats}" 
      by auto
    then have "\<lparr>{(k, k'). (t k') = minP nats}\<rparr> \<ge> \<lparr>UNIV\<rparr>;\<lparr>{(k, k'). (t k') = minP nats}\<rparr>" 
      using spec_chain_pre by metis
    also have "... \<ge> \<lparr>UNIV \<triangleright> p_inv\<rparr>;
          \<lbrace>p_inv\<rbrace>;\<lparr>{(k, k'). (t k') = minP nats}\<rparr>" 
      using seq_mono_right seq_assoc seq_mono_left spec_assert_post 
        spec_top term_ref_spec by auto
    also have "... \<ge> \<lparr>{(k, k'). (ot k') = N \<and> (et k') = N}\<rparr>;
          \<lbrace>p_inv\<rbrace>;\<lparr>{(k, k'). (t k') = minP nats}\<rparr>"
      using spec_strengthen seq_mono subset_7 by simp
    finally have "(rely (no_change)) \<iinter> \<lparr>{(k, k'). (t k') = minP nats}\<rparr> \<ge> 
          (rely (no_change)) \<iinter> ( \<lparr>{(k, k'). (ot k') = N \<and> (et k') = N}\<rparr>;
          \<lbrace>p_inv\<rbrace>;\<lparr>{(k, k'). (t k') = minP nats}\<rparr> )" using conj_mono_right by simp
    also have "... \<ge> var_init;((rely (no_change)) \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>{(k, k'). (t k') = minP nats}\<rparr>)" 
      using rely_seq_distrib seq_assoc by auto
    also have "... \<ge> var_init ; 
          ((guar_inv p_inv) \<iinter> (rely (no_change)) \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>{(k, k'). (t k') = minP nats}\<rparr>)"
      using conj_mono_left guar_introduce guar_inv_def seq_mono_right by auto
    also have "... \<ge> (Vet::= (Constant N));(Vot::= (Constant N));
          ( (guar_inv p_inv) \<iinter> (rely (no_change)) \<iinter> \<lbrace>p_inv\<rbrace>;\<lparr>{(k, k'). (t k') = minP nats}\<rparr> )" 
      using initial_assignment seq_mono_left by blast
    finally show ?thesis by simp
  qed
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
        guar_nested equality_1 by (metis (no_types, lifting))
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
qed
end
end