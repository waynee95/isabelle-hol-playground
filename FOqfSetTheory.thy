theory FOqfSetTheory
  imports Main
begin

(*
############################################################
#  Quantifier-free FOL over finite sets: Small-model proof #
############################################################

High-level idea:
- We work with a quantifier-free language built from set variables Xi,
  the constants \<emptyset> and {c}, and the operators \<union>, \<inter>. Atoms are:
    e \<in> s,  s = t,  s \<subseteq> t,  e1 = e2,
  and we use only Boolean connectives (no quantifiers).

- For any *non-constant* element u, what matters to the evaluation
  of any set expression using only the *mentioned* set variables
  is precisely the *membership pattern* of u across those variables:
      { i in vars | u \<in> \<sigma> i }.
  Two non-constant elements with the same pattern are indistinguishable
  for the language.

- We therefore build a finite "support" D consisting of:
    (i) all values of element constants that occur in the formula, and
   (ii) one representative element for each *active region*
        (each membership pattern that actually occurs).
  We then restrict \<sigma> to \<sigma>'(i) = \<sigma>(i) \<inter> D and prove truth is preserved.

- Cardinality bound:
      |D| \<le> |{values of constants}| + 2^(#set variables in the formula).

*)

(* ===================================== *)
(* ============  Syntax  =============== *)
(* ===================================== *)

(* Two sorts of syntactic variables: set variables X_i and element variables a_i *)
datatype var = SetVar nat | ElemVar nat

datatype set_expr =
    SetVarRef nat
  | Empty
  | Singleton nat
  | Union set_expr set_expr
  | Inter set_expr set_expr

datatype elem_expr = Const nat

datatype atom =
    ElemInSet elem_expr set_expr
  | SetEq set_expr set_expr
  | SetSubset set_expr set_expr
  | ElemEq elem_expr elem_expr

datatype formula =
    Atom atom
  | Not formula
  | And formula formula
  | Or formula formula

(* ===================================== *)
(* ============  Semantics  ============ *)
(* ===================================== *)

(* A structure is given by:
  - an interpretation \<iota> mapping element constants to domain elements (in \<nat>),
  - an interpretation \<sigma> mapping set-variable indices to subsets of \<nat> 
*)
type_synonym elem_interp = "nat \<Rightarrow> nat"
type_synonym set_interp  = "nat \<Rightarrow> nat set"

fun eval_elem :: "elem_interp \<Rightarrow> elem_expr \<Rightarrow> nat" where
  "eval_elem \<iota> (Const n) = \<iota> n"

fun eval_set :: "set_interp \<Rightarrow> elem_interp \<Rightarrow> set_expr \<Rightarrow> nat set" where
  "eval_set \<sigma> \<iota> (SetVarRef i) = \<sigma> i" |
  "eval_set \<sigma> \<iota> Empty         = {}" |
  "eval_set \<sigma> \<iota> (Singleton n) = {\<iota> n}" |
  "eval_set \<sigma> \<iota> (Union t u)   = eval_set \<sigma> \<iota> t \<union> eval_set \<sigma> \<iota> u" |
  "eval_set \<sigma> \<iota> (Inter t u)   = eval_set \<sigma> \<iota> t \<inter> eval_set \<sigma> \<iota> u"

fun eval_atom :: "set_interp \<Rightarrow> elem_interp \<Rightarrow> atom \<Rightarrow> bool" where
  "eval_atom \<sigma> \<iota> (ElemInSet e s) = (eval_elem \<iota> e \<in> eval_set \<sigma> \<iota> s)" |
  "eval_atom \<sigma> \<iota> (SetEq s1 s2)   = (eval_set \<sigma> \<iota> s1 = eval_set \<sigma> \<iota> s2)" |
  "eval_atom \<sigma> \<iota> (SetSubset s1 s2) = (eval_set \<sigma> \<iota> s1 \<subseteq> eval_set \<sigma> \<iota> s2)" |
  "eval_atom \<sigma> \<iota> (ElemEq e1 e2)  = (eval_elem \<iota> e1 = eval_elem \<iota> e2)"

fun eval_formula :: "set_interp \<Rightarrow> elem_interp \<Rightarrow> formula \<Rightarrow> bool" where
  "eval_formula \<sigma> \<iota> (Atom a) = eval_atom \<sigma> \<iota> a" |
  "eval_formula \<sigma> \<iota> (Not f)  = (\<not> eval_formula \<sigma> \<iota> f)" |
  "eval_formula \<sigma> \<iota> (And f g) = (eval_formula \<sigma> \<iota> f \<and> eval_formula \<sigma> \<iota> g)" |
  "eval_formula \<sigma> \<iota> (Or f g)  = (eval_formula \<sigma> \<iota> f \<or> eval_formula \<sigma> \<iota> g)"

(* ===================================== *)
(* ======  Vars/Consts (of a \<phi>)  ======= *)
(* ===================================== *)

(* 
  Collect 
  - which set variables occur, 
  - which element constants occur.

  These are then used to (a) determine the relevant coordinates of 
  membership patterns, and (b) bound the size of domain D (the restricted domain).
*)

fun set_vars_set_expr :: "set_expr \<Rightarrow> nat set" where
  "set_vars_set_expr (SetVarRef i) = {i}" |
  "set_vars_set_expr Empty = {}" |
  "set_vars_set_expr (Singleton _) = {}" |
  "set_vars_set_expr (Union a b) = set_vars_set_expr a \<union> set_vars_set_expr b" |
  "set_vars_set_expr (Inter a b) = set_vars_set_expr a \<union> set_vars_set_expr b"

fun set_vars_atom :: "atom \<Rightarrow> nat set" where
  "set_vars_atom (ElemInSet _ s) = set_vars_set_expr s" |
  "set_vars_atom (SetEq s1 s2)   = set_vars_set_expr s1 \<union> set_vars_set_expr s2" |
  "set_vars_atom (SetSubset s1 s2) = set_vars_set_expr s1 \<union> set_vars_set_expr s2" |
  "set_vars_atom (ElemEq _ _)    = {}"

fun set_vars :: "formula \<Rightarrow> nat set" where
  "set_vars (Atom a) = set_vars_atom a" |
  "set_vars (Not f)  = set_vars f" |
  "set_vars (And f g) = set_vars f \<union> set_vars g" |
  "set_vars (Or f g)  = set_vars f \<union> set_vars g"

fun consts_elem :: "elem_expr \<Rightarrow> nat set" where
  "consts_elem (Const n) = {n}"

fun consts_set_expr :: "set_expr \<Rightarrow> nat set" where
  "consts_set_expr (SetVarRef _) = {}" |
  "consts_set_expr Empty = {}" |
  "consts_set_expr (Singleton n) = {n}" |
  "consts_set_expr (Union a b) = consts_set_expr a \<union> consts_set_expr b" |
  "consts_set_expr (Inter a b) = consts_set_expr a \<union> consts_set_expr b"

fun consts_atom :: "atom \<Rightarrow> nat set" where
  "consts_atom (ElemInSet e s) = consts_elem e \<union> consts_set_expr s" |
  "consts_atom (SetEq s1 s2)   = consts_set_expr s1 \<union> consts_set_expr s2" |
  "consts_atom (SetSubset s1 s2) = consts_set_expr s1 \<union> consts_set_expr s2" |
  "consts_atom (ElemEq e1 e2)  = consts_elem e1 \<union> consts_elem e2"

fun consts_formula :: "formula \<Rightarrow> nat set" where
  "consts_formula (Atom a) = consts_atom a" |
  "consts_formula (Not f)  = consts_formula f" |
  "consts_formula (And f g) = consts_formula f \<union> consts_formula g" |
  "consts_formula (Or f g)  = consts_formula f \<union> consts_formula g"

(* ===================================== *)
(* =========  Region patterns  ========= *)
(* ===================================== *)

(* 
  A membership pattern records, for a given element u, exactly which of the
  mentioned set variables contain u
*)
definition membership_pattern :: "nat list \<Rightarrow> set_interp \<Rightarrow> nat \<Rightarrow> nat set" where
  "membership_pattern vars \<sigma> u = {i \<in> set vars. u \<in> \<sigma> i}"

(* visible universe induced by the set variables, i.e. all elements 
  that appear in any X_i *)
definition U\<sigma> :: "nat list \<Rightarrow> (nat \<Rightarrow> nat set) \<Rightarrow> nat set" where
  "U\<sigma> vars \<sigma> = (\<Union>i\<in>set vars. \<sigma> i)"

(* active regions = the set of membership patterns that 
  that actually occur among elements of U *)
definition active_regions :: "nat list \<Rightarrow> set_interp \<Rightarrow> nat set \<Rightarrow> nat set set" where
  "active_regions vars \<sigma> U = { membership_pattern vars \<sigma> u | u. u \<in> U }"

(* the set of active regions is a subset over all possible regions *)
lemma regions_subset_Pow:
  "active_regions vars \<sigma> U \<subseteq> Pow (set vars)"
  unfolding active_regions_def membership_pattern_def by auto

(* hence, the number of active regions is finite *)
lemma finite_regions: "finite (active_regions vars \<sigma> U)"
    using finite_subset regions_subset_Pow
  by (metis List.finite_set finite_Pow_iff) 

(* and the number of active regions is at most 2^n *)
lemma card_regions_le:
  "card (active_regions vars \<sigma> U) \<le> 2 ^ length vars"
proof -
  have "active_regions vars \<sigma> U \<subseteq> Pow (set vars)"
    by (simp add: regions_subset_Pow)
  then have "card (active_regions vars \<sigma> U) \<le> card (Pow (set vars))"
    by (simp add: card_mono)
  also have "\<dots> = 2 ^ card (set vars)"
    using finite_Pow_iff by (simp add: card_Pow)
  also have "\<dots> \<le> 2 ^ length vars"
    by (simp add: card_length)
  finally show ?thesis .
qed

(* ===================================== *)
(* =======  Small-model property  ====== *)
(* ===================================== *)

(*
  Idea of the proof:

  1) Compute the finite syntactic support (vars and constants).
  2) Build a finite set D = (values of constants) \<union> (one representative per region).
  3) Restrict \<sigma> to \<sigma>'(i) = \<sigma>(i) \<inter> D.
  4) Prove preservation of atoms and hence formulas:
     - agreement on D
     - region invariance for non-constants
  5) Derive the size bound |D| \<le> |const values| + 2^(#vars).
*)

(* --- Finite-ness of the syntactic support --- *)

lemma finite_set_vars_expr [simp]: "finite (set_vars_set_expr e)"
  by (induction e) auto

lemma finite_set_vars_atom [simp]: "finite (set_vars_atom a)"
  by (induction a) auto

lemma finite_set_vars [simp]: "finite (set_vars f)"
  by (induction f) auto

lemma finite_consts_set_expr [simp]: "finite (consts_set_expr e)"
  by (induction e) auto

lemma finite_consts_elem [simp]: "finite (consts_elem e)"
  by (induction e) auto

lemma finite_consts_atom [simp]: "finite (consts_atom a)"
  by (induction a) auto

lemma finite_consts_formula [simp]: "finite (consts_formula f)"
  by (induction f) auto

(* concrete values of element constants under \<iota> *)
definition const_vals :: "elem_interp \<Rightarrow> nat set \<Rightarrow> nat set" where
  "const_vals \<iota> C = \<iota> ` C"

abbreviation region_of :: "nat list \<Rightarrow> set_interp \<Rightarrow> nat \<Rightarrow> nat set"
  where "region_of vars \<sigma> u \<equiv> membership_pattern vars \<sigma> u"

(* all active regions with respect to the full visible universe *)
definition regions_all :: "nat list \<Rightarrow> set_interp \<Rightarrow> nat set set" where
  "regions_all vars \<sigma> = active_regions vars \<sigma> (U\<sigma> vars \<sigma>)"

lemma finite_regions_all: "finite (regions_all vars \<sigma>)"
  unfolding regions_all_def by (rule finite_regions)

(* some regions may have elements not equal to any constant value *)
definition has_nonconst_region :: "nat list \<Rightarrow> set_interp \<Rightarrow> elem_interp \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> bool" where
  "has_nonconst_region vars \<sigma> \<iota> C R \<longleftrightarrow> 
      (\<exists>u\<in>U\<sigma> vars \<sigma>. membership_pattern vars \<sigma> u = R \<and> u \<notin> \<iota> ` C)"

(* chose a non-constant representative of region R, if it exists *)
definition rep_nc :: "nat list \<Rightarrow> set_interp \<Rightarrow> elem_interp \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> nat" where
  "rep_nc vars \<sigma> \<iota> C R = 
      (SOME u. u \<in> U\<sigma> vars \<sigma> \<and> membership_pattern vars \<sigma> u = R \<and> u \<notin> \<iota> ` C)"

lemma rep_nc_spec:
  assumes "has_nonconst_region vars \<sigma> \<iota> C R"
  shows "rep_nc vars \<sigma> \<iota> C R \<in> U\<sigma> vars \<sigma>
       \<and> membership_pattern vars \<sigma> (rep_nc vars \<sigma> \<iota> C R) = R
       \<and> rep_nc vars \<sigma> \<iota> C R \<notin> \<iota> ` C"
    using assms unfolding has_nonconst_region_def rep_nc_def
    by (metis (mono_tags, lifting) some_eq_ex) 

(* Fallback rep if a region has no non-const element *)
definition rep_any :: "nat list \<Rightarrow> set_interp \<Rightarrow> nat set \<Rightarrow> nat" where
  "rep_any vars \<sigma> R = (SOME u. u \<in> U\<sigma> vars \<sigma> \<and> membership_pattern vars \<sigma> u = R)"

lemma rep_any_spec:
  assumes "R \<in> regions_all vars \<sigma>"
  shows "rep_any vars \<sigma> R \<in> U\<sigma> vars \<sigma>
       \<and> membership_pattern vars \<sigma> (rep_any vars \<sigma> R) = R"
  using assms unfolding active_regions_def rep_any_def
  by (smt (verit) active_regions_def mem_Collect_eq regions_all_def
      some_eq_ex)

(* the set of all chosen representatives: one per region, 
  preferring non-constant witness when available *)
definition reps :: "nat list \<Rightarrow> set_interp \<Rightarrow> elem_interp \<Rightarrow> nat set \<Rightarrow> nat set" where
  "reps vars \<sigma> \<iota> C =
     { rep_nc  vars \<sigma> \<iota> C R | R. R \<in> regions_all vars \<sigma> \<and> has_nonconst_region vars \<sigma> \<iota> C R } \<union>
     { rep_any vars \<sigma>        R | R. R \<in> regions_all vars \<sigma> \<and> \<not> has_nonconst_region vars \<sigma> \<iota> C R }"

(* the finite support D used to restrict \<sigma> *)
definition support :: "nat list \<Rightarrow> set_interp \<Rightarrow> elem_interp \<Rightarrow> nat set \<Rightarrow> nat set" where
  "support vars \<sigma> \<iota> C = (\<iota> ` C) \<union> reps vars \<sigma> \<iota> C"

lemma rep_nc_in_support:
  assumes "has_nonconst_region vars \<sigma> \<iota> C R" "R \<in> regions_all vars \<sigma>"
  shows   "rep_nc vars \<sigma> \<iota> C R \<in> support vars \<sigma> \<iota> C"
  using assms by (simp add: support_def reps_def) blast

lemma rep_nc_not_const:
  assumes "has_nonconst_region vars \<sigma> \<iota> C R"
  shows   "rep_nc vars \<sigma> \<iota> C R \<notin> \<iota> ` C"
  using rep_nc_spec[OF assms] by simp

(* get canonical representative of a region *)
definition rep_of :: "nat list \<Rightarrow> set_interp \<Rightarrow> nat set \<Rightarrow> nat" where
  "rep_of vars \<sigma> R = (SOME u. u \<in> U\<sigma> vars \<sigma> \<and>
                      membership_pattern vars \<sigma> u = R)"

lemma rep_of_spec:
  assumes "R \<in> regions_all vars \<sigma>"
  shows "rep_of vars \<sigma> R \<in> U\<sigma> vars \<sigma>
       \<and> membership_pattern vars \<sigma> (rep_of vars \<sigma> R) = R"
proof -
  have "\<exists>u\<in>U\<sigma> vars \<sigma>. membership_pattern vars \<sigma> u = R"
    using assms unfolding regions_all_def active_regions_def by auto
  then show ?thesis
    using rep_of_def
    by (metis (mono_tags, lifting) some_eq_ex)
qed

lemma finite_reps: "finite (reps vars \<sigma> \<iota> C)"
  unfolding reps_def by (simp add: finite_regions_all) 

(* at most one chosen representative per region *)
lemma card_reps_le:
  fixes vars :: "nat list" and \<sigma> :: set_interp and \<iota> :: elem_interp and C :: "nat set"
  defines "Rs \<equiv> regions_all vars \<sigma>"
  defines "A  \<equiv> {r\<in>Rs. has_nonconst_region vars \<sigma> \<iota> C r}"
  defines "B  \<equiv> {r\<in>Rs. \<not> has_nonconst_region vars \<sigma> \<iota> C r}"
  shows "card (reps vars \<sigma> \<iota> C) \<le> card (regions_all vars \<sigma>)"
proof -
  have part: "A \<union> B = Rs" and disj: "A \<inter> B = {}"
    unfolding A_def B_def Rs_def by auto

  have finRs: "finite Rs"
    unfolding Rs_def by (rule finite_regions_all)
  have finA: "finite A" and finB: "finite B"
    using finRs unfolding A_def B_def by auto

  (* rewrite the two comprehensions as images *)
  have reps_A:
    "{ rep_nc vars \<sigma> \<iota> C r | r. r \<in> Rs \<and> has_nonconst_region vars \<sigma> \<iota> C r }
     = rep_nc vars \<sigma> \<iota> C ` A"
    unfolding A_def by auto

  have reps_B:
    "{ rep_any vars \<sigma> r | r. r \<in> Rs \<and> \<not> has_nonconst_region vars \<sigma> \<iota> C r }
     = rep_any vars \<sigma> ` B"
    unfolding B_def by auto

  have reps_img:
    "reps vars \<sigma> \<iota> C = (rep_nc vars \<sigma> \<iota> C ` A) \<union> (rep_any vars \<sigma> ` B)"
    unfolding reps_def Rs_def A_def B_def
    using A_def B_def Rs_def reps_A reps_B by auto

  have "card (reps vars \<sigma> \<iota> C)
        = card ((rep_nc vars \<sigma> \<iota> C ` A) \<union> (rep_any vars \<sigma> ` B))"
    by (simp add: reps_img)
  also have "\<dots> \<le> card (rep_nc vars \<sigma> \<iota> C ` A) + card (rep_any vars \<sigma> ` B)"
    using finA finB
    using card_Un_le by auto
  also have "\<dots> \<le> card A + card B"
    using finA finB
    by (meson add_le_mono card_image_le)
  also have "\<dots> = card (A \<union> B)"
    using finA finB disj by (simp add: card_Un_disjoint)
  also have "\<dots> = card Rs" using part by simp
  also have "\<dots> = card (regions_all vars \<sigma>)" by (simp add: Rs_def)
  finally show ?thesis .
qed



lemma finite_support:
  assumes "finite C"
  shows "finite (support vars \<sigma> \<iota> C)"
  by (simp add: assms const_vals_def finite_reps support_def) 

(* Restrict set interpretation to the finite support *)
definition restrict_set_interp :: "nat set \<Rightarrow> set_interp \<Rightarrow> set_interp" where
  "restrict_set_interp D \<sigma> i = \<sigma> i \<inter> D"

(* On D, membership in \<sigma> and in the restriction agree *)
lemma eval_set_on_D_agree:
  fixes x :: nat
  assumes "x \<in> D"
  shows   "(x \<in> eval_set (restrict_set_interp D \<sigma>) \<iota> s) = (x \<in> eval_set \<sigma> \<iota> s)"
    using assms restrict_set_interp_def
  by (induction s) simp_all

(* For elements that are not equal to any occurring constant, membership in a set expression
   depends only on the region pattern w.r.t. the used set variables. *)
lemma region_invariance:
  assumes SV: "set_vars_set_expr s \<subseteq> set vars"
  assumes SC: "consts_set_expr s \<subseteq> C"
  assumes uC: "u \<notin> const_vals \<iota> C" and vC: "v \<notin> const_vals \<iota> C"
  assumes same: "membership_pattern vars \<sigma> u = membership_pattern vars \<sigma> v"
  shows "(u \<in> eval_set \<sigma> \<iota> s) = (v \<in> eval_set \<sigma> \<iota> s)"
    using assms 
    unfolding membership_pattern_def const_vals_def
    by (induction s) auto

lemma nonconst_in_eval_set_in_U\<sigma>:
  assumes SV: "set_vars_set_expr s \<subseteq> set vars"
      and SC: "consts_set_expr s \<subseteq> C"
      and x_s: "x \<in> eval_set \<sigma> \<iota> s"
      and x_nonconst: "x \<notin> \<iota> ` C"
  shows "x \<in> U\<sigma> vars \<sigma>"
    using assms
    unfolding U\<sigma>_def
    by (induction s) auto

(* the restricted evaluation always produces elements in D 
  once D contains all constant values *)
lemma eval_set_restricted_subset_D:
  assumes SC: "consts_set_expr s \<subseteq> C"
      and CD: "const_vals \<iota> C \<subseteq> D"
  shows "eval_set (restrict_set_interp D \<sigma>) \<iota> s \<subseteq> D"
  using assms
proof (induction s)
  case (SetVarRef x)
  then show ?case
    by (simp add: restrict_set_interp_def) 
next
  case (Singleton x)
  then show ?case
    by (auto simp: const_vals_def) 
qed auto

lemma eval_set_restricted_subset_support:
  assumes D_def: "D = support vars \<sigma> \<iota> C"
      and SC:    "consts_set_expr s \<subseteq> C"
  shows "eval_set (restrict_set_interp D \<sigma>) \<iota> s \<subseteq> D"
  using assms
proof (induction s)
  case (SetVarRef x)
  then show ?case
    by (simp add: restrict_set_interp_def) 
next
  case (Singleton x)
  from Singleton.prems have "x \<in> C" by simp
  then have "\<iota> x \<in> const_vals \<iota> C"
    by (simp add: const_vals_def) 
  with \<open>x \<in> C\<close> show ?case
    by (simp add: D_def support_def)
qed auto

(* Subset/equality between set-expressions is preserved by restriction to D
   that contains all constant values and one representative per region. *)
lemma subset_preserved_by_support:
  fixes vars :: "nat list" and C :: "nat set"
    and \<sigma> :: "set_interp" and \<iota> :: "elem_interp"
  defines "D \<equiv> support vars \<sigma> \<iota> C"
  defines "\<sigma>' \<equiv> restrict_set_interp D \<sigma>"
  assumes SVs: "set_vars_set_expr s \<subseteq> set vars"
  assumes SVt: "set_vars_set_expr t \<subseteq> set vars"
  assumes SCs: "consts_set_expr s \<subseteq> C"
  assumes SCt: "consts_set_expr t \<subseteq> C"
  shows "(eval_set \<sigma> \<iota> s \<subseteq> eval_set \<sigma> \<iota> t) = (eval_set \<sigma>' \<iota> s \<subseteq> eval_set \<sigma>' \<iota> t)"
proof
  (* If s \<subseteq> t under \<sigma>, then also under restriction \<sigma>' *)
  assume H: "eval_set \<sigma> \<iota> s \<subseteq> eval_set \<sigma> \<iota> t"
  show "eval_set \<sigma>' \<iota> s \<subseteq> eval_set \<sigma>' \<iota> t"
  proof
    fix x assume xs': "x \<in> eval_set \<sigma>' \<iota> s"
      (* 1) Any element produced by the restricted interpretation lives in D *)
    have s'_subset_D: "eval_set \<sigma>' \<iota> s \<subseteq> D"
      using SCs by (simp add: \<sigma>'_def D_def eval_set_restricted_subset_support)
    from s'_subset_D xs' have xD: "x \<in> D" by blast
        (* 2) On D, \<sigma>' and \<sigma> agree elementwise *)
    have xs: "x \<in> eval_set \<sigma> \<iota> s"
      using xD xs' by (simp add: \<sigma>'_def eval_set_on_D_agree)
        (* 3) Use the assumed subset under \<sigma> *)
    have xt: "x \<in> eval_set \<sigma> \<iota> t"
      using H xs by auto
        (* 4) Switch back to \<sigma>' using agreement on D *)
    have "(x \<in> eval_set \<sigma>' \<iota> t) = (x \<in> eval_set \<sigma> \<iota> t)"
      using xD by (simp add: \<sigma>'_def eval_set_on_D_agree)
    then show "x \<in> eval_set \<sigma>' \<iota> t" using xt by simp
  qed
next
  (* If s \<subseteq> t under \<sigma>', then also under \<sigma> *)
  assume H': "eval_set \<sigma>' \<iota> s \<subseteq> eval_set \<sigma>' \<iota> t"
  show "eval_set \<sigma> \<iota> s \<subseteq> eval_set \<sigma> \<iota> t"
  (* Proof by contradiction: assume a counterexample exists under \<sigma> *)
  proof (rule ccontr)
    assume "\<not> eval_set \<sigma> \<iota> s \<subseteq> eval_set \<sigma> \<iota> t"
    then obtain x where xs: "x \<in> eval_set \<sigma> \<iota> s" and nxt: "x \<notin> eval_set \<sigma> \<iota> t" by auto
    (* that element is either a constant from C, or not *)
    consider (Const) n where "n \<in> C" "x = \<iota> n"
           | (NonConst) "x \<notin> \<iota> ` C" by auto
    then obtain y where yD: "y \<in> D" and ys: "y \<in> eval_set \<sigma> \<iota> s" and nyt: "y \<notin> eval_set \<sigma> \<iota> t"
    proof cases
      (* Constant case: constant values are included in D by _construction_ *)
      case Const
      then have "x \<in> D" by (simp add: D_def support_def const_vals_def)
      with xs nxt show ?thesis by (intro that[of x]) auto
    next
      (* Non-constant case *)
      case NonConst
      (* x is in the visible universe because s only uses the listed vars *)
      have xU: "x \<in> U\<sigma> vars \<sigma>"
        using nonconst_in_eval_set_in_U\<sigma>[OF SVs SCs xs NonConst] .
      let ?R = "membership_pattern vars \<sigma> x"

      (* the region R is active (realized in the original model) *)
      have R_in: "?R \<in> regions_all vars \<sigma>"
        unfolding regions_all_def active_regions_def U\<sigma>_def
        using xU U\<sigma>_def by auto 

      (* since x itself is non-constant, region R has a non-constant witness *)
      have has_nc: "has_nonconst_region vars \<sigma> \<iota> C ?R"
        unfolding has_nonconst_region_def U\<sigma>_def
        using xU NonConst U\<sigma>_def by auto

      (* pick the designated non-constant representative of R, which is in D *)
      have rep_in_D: "rep_nc vars \<sigma> \<iota> C ?R \<in> D"
        using rep_nc_in_support[OF has_nc R_in] by (simp add: D_def)

      (* this representative has the exact same membership pattern as x *)
      have same: "membership_pattern vars \<sigma> (rep_nc vars \<sigma> \<iota> C ?R) = membership_pattern vars \<sigma> x"
        using rep_nc_spec[OF has_nc] by simp

      (* and is non-constant *)
      have rnC: "rep_nc vars \<sigma> \<iota> C ?R \<notin> \<iota> ` C"
        using rep_nc_not_const[OF has_nc] .

      (* transport x's membership in s to the representative using 
        region invariance *)
      have ys': "rep_nc vars \<sigma> \<iota> C ?R \<in> eval_set \<sigma> \<iota> s"
        by (metis NonConst SCs SVs const_vals_def region_invariance rnC same xs) 

      (* transport x's non-membership in t *)
      have nyt': "rep_nc vars \<sigma> \<iota> C ?R \<notin> eval_set \<sigma> \<iota> t"
        by (metis NonConst SCt SVt const_vals_def nxt region_invariance rnC same)

      (* package the representative as the desired y in D *)
      from rep_in_D ys' nyt' show ?thesis by (intro that)
    qed
    (* agreement on D converts y into a _counterexample_ under \<sigma>', 
      which contradicts assumption H' *)
    from yD have "y \<in> eval_set \<sigma>' \<iota> s"
      by (simp add: \<sigma>'_def eval_set_on_D_agree ys) 
    moreover from yD have "y \<notin> eval_set \<sigma>' \<iota> t"
      by (simp add: \<sigma>'_def eval_set_on_D_agree nyt) 
    ultimately show False using H' by auto
  qed
qed

lemma seteq_preserved_by_support:
  fixes vars :: "nat list" and C :: "nat set"
    and \<sigma> :: "set_interp" and \<iota> :: "elem_interp"
  defines "D \<equiv> support vars \<sigma> \<iota> C"
  defines "\<sigma>' \<equiv> restrict_set_interp D \<sigma>"
  assumes SVs: "set_vars_set_expr s \<subseteq> set vars"
  assumes SVt: "set_vars_set_expr t \<subseteq> set vars"
  assumes SCs: "consts_set_expr s \<subseteq> C"
  assumes SCt: "consts_set_expr t \<subseteq> C"
  shows "(eval_set \<sigma> \<iota> s = eval_set \<sigma> \<iota> t) = (eval_set \<sigma>' \<iota> s = eval_set \<sigma>' \<iota> t)"
    using assms subset_preserved_by_support
  by (metis set_eq_subset) 

(* Atomic preservation when restricting to the small support *)
lemma atom_preserved_by_support:
  fixes vars :: "nat list" and C :: "nat set"
    and \<sigma> :: "set_interp" and \<iota> :: "elem_interp"
  defines "D \<equiv> support vars \<sigma> \<iota> C"
  defines "\<sigma>' \<equiv> restrict_set_interp D \<sigma>"
  assumes Avars: "set_vars_atom a \<subseteq> set vars"
  assumes Ac:    "consts_atom a \<subseteq> C"
  shows "eval_atom \<sigma> \<iota> a = eval_atom \<sigma>' \<iota> a"
proof (cases a)
  case (ElemInSet e s)
  then obtain n where [simp]: "e = Const n" 
    by (cases e) auto
  from Ac ElemInSet have nC: "n \<in> C" 
    by auto
  have in_D: "\<iota> n \<in> D"
    by (simp add: D_def const_vals_def nC support_def)
  then show ?thesis
    by (simp add: ElemInSet \<sigma>'_def eval_set_on_D_agree)
next
  case (SetEq s t)
  with Avars Ac show ?thesis
    by (simp add: D_def \<sigma>'_def seteq_preserved_by_support)
next
  case (SetSubset s t)
  with Avars Ac show ?thesis
    by (simp add: D_def \<sigma>'_def subset_preserved_by_support)
next
  case (ElemEq e1 e2)
  then show ?thesis by simp
qed

(* a formula under restricted domain has same truth value *)
lemma formula_preserved_by_support:
   fixes vars :: "nat list" and C :: "nat set"
    and \<sigma> :: "set_interp" and \<iota> :: "elem_interp"
  defines "D \<equiv> support vars \<sigma> \<iota> C"
  defines "\<sigma>' \<equiv> restrict_set_interp D \<sigma>"
  assumes Fvars: "set_vars f \<subseteq> set vars"
  assumes Fc:    "consts_formula f \<subseteq> C"
  shows "eval_formula \<sigma> \<iota> f = eval_formula \<sigma>' \<iota> f"
  using Fvars Fc
proof (induction f)
  case (Atom a)
  then show ?case
      unfolding D_def \<sigma>'_def 
    by (metis atom_preserved_by_support consts_formula.simps(1) eval_formula.simps(1)
        set_vars.simps(1))
qed auto

(* --- The small-model theorem and the size bound --- *)

lemma card_regions_all_le:
  "card (regions_all vars \<sigma>) \<le> 2 ^ length vars"
  unfolding regions_all_def by (rule card_regions_le)

(* counting representatives + all constant values yields final bound *)
lemma card_support_bound:
  assumes "finite C"
  shows "card (support vars \<sigma> \<iota> C)
       \<le> card (\<iota> ` C) + 2 ^ length vars"
proof -
  have "card (support vars \<sigma> \<iota> C)
        \<le> card (\<iota> ` C) + card (regions_all vars \<sigma>)"
    unfolding support_def const_vals_def
    by (meson card_Un_le card_reps_le le_trans nat_add_left_cancel_le)
  also have "\<dots> \<le> card (\<iota> ` C) + 2 ^ length vars"
    using card_regions_all_le by simp
  finally show ?thesis .
qed

(* final theorem: restricting to domain D preserves truth value of \<phi>;
  D is finite and satisfies the syntactic size bound *)
theorem small_model_property:
  fixes \<phi> :: formula
  assumes sat: "eval_formula \<sigma> \<iota> \<phi>"
  defines "vars_list \<equiv> sorted_list_of_set (set_vars \<phi>)"
  defines "C \<equiv> consts_formula \<phi>"
  defines "D \<equiv> support vars_list \<sigma> \<iota> C"
  defines "\<sigma>' \<equiv> restrict_set_interp D \<sigma>"
  shows "eval_formula \<sigma>' \<iota> \<phi>"
    and "finite D"
    and "card D \<le> card (\<iota> ` C) + 2 ^ length vars_list"
    and "card D \<le> card C + 2 ^ card (set_vars \<phi>)"
proof -
  have FV: "set_vars \<phi> \<subseteq> set vars_list"
    unfolding vars_list_def by simp
  have FC: "consts_formula \<phi> \<subseteq> C"
    unfolding C_def by simp
  have finC: "finite C" unfolding C_def by simp

  (* preservation of truth under restriction to D *)
  have "eval_formula \<sigma> \<iota> \<phi> = eval_formula \<sigma>' \<iota> \<phi>"
    using formula_preserved_by_support
    by (simp add: C_def D_def \<sigma>'_def vars_list_def)
  with sat show "eval_formula \<sigma>' \<iota> \<phi>" by simp

  (* finiteness and size bound of D *)
  have "finite D" using finite_support[OF finC] unfolding D_def by simp
  then show "finite D" .
  have "card D \<le> card (\<iota> ` C) + 2 ^ length vars_list"
    using card_support_bound[OF finC] unfolding D_def by simp
  then show "card D \<le> card (\<iota> ` C) + 2 ^ length vars_list" .

  (* convert to purely syntactic bound using |\<iota> ` C| \<le> |C| *)
  moreover have "length vars_list = card (set_vars \<phi>)"
    unfolding vars_list_def by simp
  moreover have "card (\<iota> ` C) \<le> card C"
    using card_image_le finC by auto
  ultimately show "card D \<le> card C + 2 ^ card (set_vars \<phi>)"
    using add_le_mono by simp
qed

end
