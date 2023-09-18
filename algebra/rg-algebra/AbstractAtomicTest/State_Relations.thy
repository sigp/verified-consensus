theory State_Relations
  imports
  "Idle"
  "HOL-Library.FSet"
begin

locale state_relations = idle_command (* lib_last
  for lib_last :: "'b \<Rightarrow> 'a::refinement_lattice \<Rightarrow> 'a" ("L\<^sup>C\<^sub>_ _" [999, 999] 999) + *) +
  constrains test :: "'state set \<Rightarrow> 'a"
  constrains pgm ::  "'state rel \<Rightarrow> 'a"
  constrains env ::  "'state rel \<Rightarrow> 'a"
  fixes set_var   :: "'varname \<Rightarrow> 'v \<Rightarrow> 'state \<Rightarrow> 'state"
  fixes get_var   :: "'varname \<Rightarrow> 'state \<Rightarrow> 'v" 
  assumes set_get: "\<And>k s. (set_var k (get_var k s) s) = s"
  assumes get_set1: "\<And>k x s. get_var k (set_var k x s) = x"
  assumes get_set2: "\<And>k x k' s. k \<noteq> k' \<Longrightarrow> get_var k' (set_var k x s) = get_var k' s"
  assumes set_set1: "\<And>k x x' s. set_var k x (set_var k x' s) = set_var k x s"
  assumes set_set2: "\<And>k x x' s. set_var k x (set_var k x' s) = set_var k x' (set_var k x s)"
begin

text \<open>The identity relation on all variables not in the set $vars$. \<close>
definition id_bar :: "'varname fset \<Rightarrow> 'state rel"
  where "id_bar vars = {(\<sigma>,\<sigma>'). \<forall>x::'varname. x |\<notin>| vars \<longrightarrow> get_var x \<sigma> = get_var x \<sigma>'}"

text \<open>Add a frame of $vars$ to a command $c$.\<close>
definition var_frame_set :: "'varname fset \<Rightarrow> 'a \<Rightarrow> 'a" (infix ":\<^sub>s" 95)
  where "var_frame_set vars c \<equiv> (guar (id_bar vars)) \<iinter> c"

text \<open>Add a frame of a single variable $x$ to a command $c$.\<close>
definition var_frame :: "'varname \<Rightarrow> 'a \<Rightarrow> 'a" (infix ":\<^sub>f" 95)
  where "var_frame x c \<equiv> {|x|}:\<^sub>sc"

lemma var_frame_expand: "x:\<^sub>fc = (guar (id_bar {|x|})) \<iinter> c"
  using var_frame_def var_frame_set_def by simp

text \<open>Set of states in which varible $var$ equals $value$.\<close>
definition var_eq :: "'varname => 'v \<Rightarrow> 'state set"
  where "var_eq var value \<equiv> {s. get_var var s = value}"

definition id_set :: "'varname fset \<Rightarrow> 'state rel"
  where "id_set vars = {(\<sigma>,\<sigma>'). \<forall>x::'varname. x |\<in>| vars \<longrightarrow> get_var x \<sigma> = get_var x \<sigma>'}"

definition id :: "'varname \<Rightarrow> 'state rel"
  where "id x = {(\<sigma>,\<sigma>'). get_var x \<sigma> = get_var x \<sigma>'}"

lemma id_consistent : "id(x) = id_set {|x|}"
  using id_set_def local.id_def by auto 

lemma id_univ : "id(x) O id_bar({|x|}) = UNIV"
proof -
  have "id(x) O id_bar({|x|}) = {(\<sigma>,\<sigma>'). get_var x \<sigma> = get_var x \<sigma>'} O 
      {(\<sigma>,\<sigma>'). \<forall>x'::'varname. x' |\<notin>| {|x|} \<longrightarrow> get_var x' \<sigma> = get_var x' \<sigma>'}"
    unfolding id_def id_bar_def by simp
  also have "... = {(\<sigma>, \<sigma>'). (\<exists>\<sigma>''. (\<sigma>, \<sigma>'') \<in> {(\<sigma>,\<sigma>'). get_var x \<sigma> = get_var x \<sigma>'} \<and>
      (\<sigma>'', \<sigma>') \<in> {(\<sigma>,\<sigma>'). \<forall>x'::'varname. x' \<noteq> x \<longrightarrow> get_var x' \<sigma> = get_var x' \<sigma>'})}"
    by (simp add: relcomp_unfold)
  also have "... = {(\<sigma>, \<sigma>'). True}"
  proof -
    have "\<exists>\<sigma>''. (\<sigma>,\<sigma>'') \<in> {(\<sigma>,\<sigma>'). get_var x \<sigma> = get_var x \<sigma>'} \<and> (\<sigma>'',\<sigma>') \<in> {(\<sigma>,\<sigma>'). \<forall>x'. (x' \<noteq> x \<longrightarrow> get_var x' \<sigma> = get_var x' \<sigma>')}" for \<sigma> \<sigma>'
      by (intro exI[of _ "set_var x (get_var x \<sigma>) \<sigma>'"]) (simp add: get_set1 get_set2)
    then show ?thesis by auto
  qed
  finally show ?thesis by simp
qed

end
end
