theory Cont_Monad_Algebra
 imports "Verified_Consensus.Constrained_Atomic_Commands" "HOL-Library.Monad_Syntax"
begin         


definition bindCont :: "(('a \<Rightarrow> 'r) \<Rightarrow> 'r) \<Rightarrow> ('a \<Rightarrow> ('b \<Rightarrow> 'r) \<Rightarrow> 'r) \<Rightarrow> ('b \<Rightarrow> 'r) \<Rightarrow> 'r" (infixl "\<bind>" 54)
where
 "bindCont (f :: ('a \<Rightarrow> 'r) \<Rightarrow> 'r) (g :: 'a \<Rightarrow> ('b \<Rightarrow> 'r) \<Rightarrow> 'r) \<equiv> \<lambda>(c :: ('b \<Rightarrow> 'r)). f (\<lambda>a. g a c) ::  'r" 

definition "return a f = f a"

type_synonym ('a, 'r) cont = "('a \<Rightarrow> 'r) \<Rightarrow> 'r"

type_notation cont (infixr "\<leadsto>" 10)

definition callCC :: "(('a \<Rightarrow> ('b, 'r) cont) \<Rightarrow> ('a, 'r) cont) \<Rightarrow> ('a, 'r) cont"
  where "callCC f \<equiv> \<lambda>cc. f (\<lambda>a _. cc a) cc "

definition liftM  :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'r) cont \<Rightarrow> ('b, 'r) cont" (infixl "<$>" 50) where
  "liftM f m = bindCont m (return o f)"

definition k_comp :: "('a \<Rightarrow> ('b, 'r) cont) =>  ('b \<Rightarrow> ('c, 'r) cont) => ('a \<Rightarrow> ('c, 'r) cont)" where 
 "k_comp f g \<equiv> \<lambda>a. bindCont (f a) g"

definition foldrM :: "('a \<Rightarrow> 'b \<Rightarrow> ('b, 'r) cont) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> ('b, 'r) cont" where
  "foldrM f xs = foldr (k_comp) (map f xs) (return)"


adhoc_overloading bind == bindCont


primrec mapM :: "('a \<Rightarrow> ('b, 'r) cont) \<Rightarrow> 'a list \<Rightarrow> ('b list, 'r) cont" where
  "mapM f (x#xs) = do {a <- f x ; b <- mapM f xs; return (a # b)} " |
  "mapM f [] = return []"


definition ifM :: "(bool, 'a) cont \<Rightarrow> ('b, 'a) cont \<Rightarrow> ('b, 'a) cont \<Rightarrow> ('b, 'a) cont"
  where "ifM b m m'=
        do {c <- b;  
            if c then m else m'}"

lemma bindCont_return: "bindCont f return = f"
  by (intro ext; clarsimp simp: bindCont_def return_def)


lemma bindCont_return': "bindCont (return a) f = f a"
  by (intro ext; clarsimp simp: bindCont_def return_def)

lemma kcomp_assoc: "k_comp (k_comp f g) h = k_comp f (k_comp g h)"
  by (intro ext; clarsimp simp: k_comp_def bindCont_def return_def)

               
context constrained_atomic begin


definition "select S f \<equiv> \<Squnion>x\<in>S. f x"  

definition "angel S f \<equiv> \<Sqinter>x\<in>S. f x"


definition "getState f \<equiv>  (\<Squnion>a. \<tau> {a} ; f a)  "   

definition "setState s f \<equiv>  (\<pi> (UNIV \<triangleright> {s}) ; f () )"   


definition "modifyState f = do { a <- (getState);  (setState (f a))}"


definition "fail f = \<top> "

definition "todo f = \<bottom> "

definition flatten :: "(('b, 'a) cont, 'a) cont \<Rightarrow> ('b, 'a) cont" where
  "flatten f = bindCont f id"

term "lfp (flatten o liftM (f :: ('b => ('b, 'a) cont)))   "

definition "thendo f g = bindCont f (\<lambda>_. g)"

definition loop :: "('b => ('b, 'a) cont) \<Rightarrow> ('b, 'a) cont "
  where "loop f = lfp (\<lambda>y. bindCont y f )"

definition whileStep :: "(bool, 'a) cont \<Rightarrow> ('b, 'a) cont \<Rightarrow> (unit, 'a) cont" where
 "whileStep b m = ifM b (thendo m (return ())) (return ())"

(* definition while :: "(bool, 'a) cont \<Rightarrow> ('b, 'a) cont \<Rightarrow> (unit, 'a) cont"
  where "while b m = loop (\<lambda>_. whileStep b m )" *)


definition "run f = (f (\<lambda>_. nil))"

definition "check f x = f (\<lambda>P. if P then x else nil)"


definition while' :: "(bool, 'a) cont \<Rightarrow> ('b, 'a) cont \<Rightarrow> (unit, 'a) cont"
  where "while' b m = (\<lambda>f. iter (run m); bindCont b (\<lambda>c g. if c then f () else \<bottom>) f)"



lemma kcomp_assoc: "k_comp (k_comp f g) h = k_comp f (k_comp g h)"
  by (intro ext; clarsimp simp: k_comp_def bindCont_def return_def)

definition "assertion P = do {a <- getState; (if (P a) then return () else fail)}"

definition "test_state P = do {a <- getState; return (P a)}"


definition inc :: "(nat \<Rightarrow> nat option) \<Rightarrow> (nat \<Rightarrow> nat option)"
  where "inc s = s (0 \<mapsto> 0 + 1)"


definition "pointless s = do {x <- getState;
                              setState s;
                              return x}"


lemma test_split: "\<tau> P = (\<Squnion>x\<in>P. \<tau> {x})" 
  apply (subst UN_singleton[symmetric])
  apply (subst test_Sup, clarsimp)
  by (simp add: image_image)

lemma SUP_eq_if:"(\<Squnion>x\<in>P. f x) = (\<Squnion>(x). if (x \<in> P) then ((f x) :: 'e :: complete_lattice)  else \<bottom>)"
  apply (rule antisym)
   apply (smt (verit, best) SUP_subset_mono order_class.order_eq_iff subset_UNIV)  
  by (smt (verit) SUP_empty SUP_least Sup_upper empty_iff image_eqI)


lemma in_dom_iff: "x \<in> A \<triangleleft> R \<longleftrightarrow> fst x \<in> A \<and> x \<in> R"
  by (clarsimp simp: restrict_domain_def split: prod.splits)

lemma in_ran_iff: "x \<in> R \<triangleright> A \<longleftrightarrow> snd x \<in> A \<and> x \<in> R"
  apply (clarsimp simp: restrict_range_def split: prod.splits)
  by (safe)

lemma is_id: "{x} \<triangleleft> (UNIV \<triangleright> {x}) = {(x,x)}"
  by (rule set_eqI; clarsimp simp: in_dom_iff in_ran_iff Id_on_iff)

lemma "run (assertion (\<lambda>_. False)) = \<top>"
  apply (clarsimp simp: modifyState_def assertion_def fail_def run_def bindCont_def getState_def setState_def pgm_test_pre is_id)
  apply (rule antisym)
   apply (subst Sup_le_iff; clarsimp)
  by (metis NONDET_seq_distrib Nondet_test_nil order_top_class.top_greatest seq_nil_left)

definition "compact c \<longleftrightarrow> (\<forall>S. S \<noteq> {} \<longrightarrow>  c \<le> \<Squnion> S \<longrightarrow> (\<exists>s\<in>S. c \<le> s))"

lemma foldrM_empty[simp]: "foldrM f [] x = return (x)" by (clarsimp simp: foldrM_def)


lemma foldrM_cons: "foldrM f (x # xs) v = do {y <- f x v; foldrM f xs y}"
  by (clarsimp simp: foldrM_def k_comp_def)

lemmas bind_assoc =  kcomp_assoc[simplified k_comp_def]

lemma bindCont_assoc: "bindCont f (\<lambda>a. bindCont (g a) h) = bindCont (bindCont f g) h"
  by (clarsimp simp: bindCont_def)

lemma foldrM_append: "foldrM f (xs@ys) n = do {v <- foldrM f (xs) n; foldrM f ys v}"
  apply (induct xs arbitrary: n; clarsimp simp: bindCont_return bindCont_return')
  apply (clarsimp simp: foldrM_cons bindCont_return bindCont_return' )
  by (simp add: bindCont_assoc bindCont_return bindCont_return')

lemma bindCont_right_eqI: "(\<And>x. c x = d x) \<Longrightarrow> bindCont f c = (bindCont f d)"
  apply (intro ext; clarsimp simp: bindCont_def)
  done

lemma  bindCont_fail_absorb [simp]: "(bindCont fail c) = fail"
  apply (clarsimp simp: bindCont_def fail_def)
  apply (rule ext)
  apply (clarsimp simp: fail_def)
  done

lemma fail_absorb_left[simp]: " (bindCont fail c) = fail"
  by (intro ext; clarsimp simp: fail_def bindCont_def)

lemma algebraic: "(x :: 'a) = \<Squnion>{y. y \<le> x \<and> compact y}" sorry

end



end
