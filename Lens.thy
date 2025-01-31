theory Lens
imports Main  "HOL-Library.Adhoc_Overloading"

begin

datatype ('a, 'b) lens = Lens (get : "'a \<Rightarrow> 'b") (set: "'a \<Rightarrow> 'b \<Rightarrow> 'a") (valid: "'b \<Rightarrow> bool")

abbreviation (input) "swp f \<equiv> (\<lambda>x y. f y x)"

definition "set_set p \<equiv> \<forall>l l' s . (set p (set p s l') l) = set p s l"

definition "get_set p \<equiv> \<forall>l s. (get p (set p s l)) = l"

definition "set_get p \<equiv>  \<forall>s. set p s (get p s) = s"

definition "valid_lens p \<equiv> get_set p \<and> set_get p \<and> set_set p" 

definition "first \<equiv> Lens fst (\<lambda>s a. (a, snd s)) (\<lambda>_. True)"


consts
  lcomp :: "('a, 'b) lens \<Rightarrow> ('c, 'd) lens \<Rightarrow>  ('e, 'f) lens" 

definition lens_comp :: "('b, 'a) lens \<Rightarrow> ('c, 'b) lens \<Rightarrow>  ('c, 'a) lens" (infixl "|>" 54)
 where "lens_comp l l' \<equiv> Lens (get l o get l') (\<lambda>s a. set l' s (set l (get l' s) a)) (\<lambda>_. True) "


definition lens_ocomp :: "('b, 'a) lens \<Rightarrow> ('c, 'b option) lens \<Rightarrow> ('c, 'a option) lens" (infixl "|o>" 54) where 
"lens_ocomp l l' \<equiv> Lens (\<lambda>s. map_option (get l) (get l' s) ) (\<lambda>s a. set l' s (Option.bind (get l' s) (\<lambda>s'. Option.bind a (\<lambda>a. Some (set l s' a)))) ) (\<lambda>_. True) "


definition lens_oocomp :: "('b, 'a option) lens \<Rightarrow> ('c, 'b option) lens \<Rightarrow> ('c, 'a option) lens" (infixl "|oo>" 54) where 
"lens_oocomp l l' \<equiv> Lens (\<lambda>s. Option.bind (get l' s) (get l)  ) (\<lambda>s a. set l' s (Option.bind (get l' s) (\<lambda>s'. Some (set l s' a) )) ) (\<lambda>_. True) "

adhoc_overloading
  lcomp lens_comp lens_ocomp lens_oocomp
end