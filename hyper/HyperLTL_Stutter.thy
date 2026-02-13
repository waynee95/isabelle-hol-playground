theory HyperLTL_Stutter
  imports Main
begin

section \<open>1. Syntax and Well-Formedness\<close>

typedecl AP

(* The syntax of HyperLTL without the 'Next' (X) operator *)
datatype formula =
  Atom "string" "AP"        (* Atomic prop 'a' on trace '\<pi>' *)
| Not "formula"
| And "formula" "formula"
| Until "formula" "formula"
| Exists "string" "formula"

(* Trace variables are strings *)
type_synonym variable = string

primrec free_vars :: "formula \<Rightarrow> variable set" where
  "free_vars (Atom \<pi> a) = {\<pi>}"
| "free_vars (Not \<phi>) = free_vars \<phi>"
| "free_vars (And \<phi> \<psi>) = free_vars \<phi> \<union> free_vars \<psi>"
| "free_vars (Until \<phi> \<psi>) = free_vars \<phi> \<union> free_vars \<psi>"
| "free_vars (Exists \<pi> \<phi>) = free_vars \<phi> - {\<pi>}"

(* A formula is closed if it has no free variables *)
definition closed :: "formula \<Rightarrow> bool" where
  "closed \<phi> \<longleftrightarrow> free_vars \<phi> = {}"


section \<open>2. Semantics\<close>

(* A trace maps time (nat) to a set of atomic propositions *)
type_synonym trace = "nat \<Rightarrow> AP set"

(* An environment maps variable names to concrete traces *)
type_synonym env = "variable \<Rightarrow> trace"

(* A system is a set of infinite traces *)
type_synonym system = "trace set"

(* The semantic evaluation function *)
primrec sem :: "system \<Rightarrow> env \<Rightarrow> nat \<Rightarrow> formula \<Rightarrow> bool" ("_, _, _ \<Turnstile> _" [80,80,80,80] 80) where
  "sem T E i (Atom \<pi> a) = (a \<in> (E \<pi>) i)"
| "sem T E i (Not \<phi>) = (\<not> sem T E i \<phi>)"
| "sem T E i (And \<phi> \<psi>) = (sem T E i \<phi> \<and> sem T E i \<psi>)"
| "sem T E i (Until \<phi> \<psi>) = (\<exists>k\<ge>i. sem T E k \<psi> \<and> (\<forall>j. i \<le> j \<and> j < k \<longrightarrow> sem T E j \<phi>))"
| "sem T E i (Exists \<pi> \<phi>) = (\<exists>t \<in> T. sem T (E(\<pi> := t)) i \<phi>)"

(* Top-level validity: A system satisfies a CLOSED formula starting at time 0 *)
definition models_system :: "system \<Rightarrow> formula \<Rightarrow> bool" ("_ \<Turnstile> _" [80,80] 80) where
  "models_system T \<phi> \<longleftrightarrow> closed \<phi> \<and> (\<forall>E. sem T E 0 \<phi>)"

lemma semantics_depend_only_on_free_vars:
  assumes "\<forall>\<pi> \<in> free_vars \<phi>. E1 \<pi> = E2 \<pi>"
  shows "sem T E1 i \<phi> \<longleftrightarrow> sem T E2 i \<phi>"
using assms proof (induction \<phi> arbitrary: i E1 E2)
  case (Atom \<pi> a)
  then show ?case by simp
next
  case (Not \<phi>)
  then show ?case by auto
next
  case (And \<phi>1 \<phi>2)
  then show ?case
    by (metis (mono_tags, lifting) Un_iff free_vars.simps(3) sem.simps(3))
next
  case (Until \<phi>1 \<phi>2)
  have vars1: "\<forall>\<pi> \<in> free_vars \<phi>1. E1 \<pi> = E2 \<pi>" using Until.prems by auto
  have vars2: "\<forall>\<pi> \<in> free_vars \<phi>2. E1 \<pi> = E2 \<pi>" using Until.prems by auto

  (* Establish equivalence for sub-formulas at ANY time step k/j *)
  have eq_phi1: "\<And>k. sem T E1 k \<phi>1 \<longleftrightarrow> sem T E2 k \<phi>1"
    using Until.IH(1)[OF vars1] by simp
  have eq_phi2: "\<And>k. sem T E2 k \<phi>2 \<longleftrightarrow> sem T E1 k \<phi>2"
    using Until.IH(2)[OF vars2] by simp

  show ?case
  proof
    assume "sem T E1 i (Until \<phi>1 \<phi>2)"
    then obtain k where k_def: "k \<ge> i"
      and k_sat: "sem T E1 k \<phi>2"
      and interval: "\<forall>j. i \<le> j \<and> j < k \<longrightarrow> sem T E1 j \<phi>1" by auto

    have "sem T E2 k \<phi>2" using k_sat eq_phi2 by simp
    moreover have "\<forall>j. i \<le> j \<and> j < k \<longrightarrow> sem T E2 j \<phi>1"
      using interval eq_phi1 by simp
    ultimately show "sem T E2 i (Until \<phi>1 \<phi>2)"
      using k_def by auto
  next
    assume "sem T E2 i (Until \<phi>1 \<phi>2)"
    then obtain k where k_def: "k \<ge> i"
      and k_sat: "sem T E2 k \<phi>2"
      and interval: "\<forall>j. i \<le> j \<and> j < k \<longrightarrow> sem T E2 j \<phi>1" by auto

    have "sem T E1 k \<phi>2" using k_sat eq_phi2 by simp
    moreover have "\<forall>j. i \<le> j \<and> j < k \<longrightarrow> sem T E1 j \<phi>1"
      using interval eq_phi1 by simp
    ultimately show "sem T E1 i (Until \<phi>1 \<phi>2)"
      using k_def by auto
  qed
next
  case (Exists \<pi> \<phi>)
  show ?case
  proof
    assume "sem T E1 i (Exists \<pi> \<phi>)"
    then obtain t where "t \<in> T" and "sem T (E1(\<pi> := t)) i \<phi>" by auto
    have "\<forall>x \<in> free_vars \<phi>. (E1(\<pi> := t)) x = (E2(\<pi> := t)) x"
      using Exists.prems by auto
    then have "sem T (E2(\<pi> := t)) i \<phi>"
      using Exists.IH \<open>T, E1(\<pi> := t), i \<Turnstile> \<phi>\<close> by blast
    then show "sem T E2 i (Exists \<pi> \<phi>)" using \<open>t \<in> T\<close> by auto
  next
    assume "sem T E2 i (Exists \<pi> \<phi>)"
    then obtain t where "t \<in> T" and "sem T (E2(\<pi> := t)) i \<phi>" by auto
    have "\<forall>x \<in> free_vars \<phi>. (E2(\<pi> := t)) x = (E1(\<pi> := t)) x"
      using Exists.prems by auto
    then have "sem T (E1(\<pi> := t)) i \<phi>"
      using Exists.IH[of "E2(\<pi> := t)" "E1(\<pi> := t)"]
      using \<open>T, E2(\<pi> := t), i \<Turnstile> \<phi>\<close> by blast
    then show "sem T E1 i (Exists \<pi> \<phi>)" using \<open>t \<in> T\<close> by auto
  qed
qed


section \<open>3. Stuttering Definitions\<close>

(* Definition of a valid time-stretching function *)
definition is_stutter_fn :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "is_stutter_fn f \<longleftrightarrow> (f 0 = 0 \<and> mono f \<and> surj f)"

(* Stretched Trace: t \<circ> f *)
definition stretch_trace :: "(nat \<Rightarrow> nat) \<Rightarrow> trace \<Rightarrow> trace" where
  "stretch_trace f t = t \<circ> f"

(* Stretched System: Apply stretch to all traces in the set *)
definition stretch_sys :: "(nat \<Rightarrow> nat) \<Rightarrow> system \<Rightarrow> system" where
  "stretch_sys f T = {stretch_trace f t | t. t \<in> T}"

(* Stretched Environment: Apply stretch to all bound traces *)
definition stretch_env :: "(nat \<Rightarrow> nat) \<Rightarrow> env \<Rightarrow> env" where
  "stretch_env f E = (\<lambda>\<pi>. stretch_trace f (E \<pi>))"


section \<open>4. The Invariance Proof\<close>

(* Helper: Properties of surjective monotone functions on nat *)
lemma stutter_properties:
  assumes "is_stutter_fn f"
  shows "i \<le> j \<Longrightarrow> f i \<le> f j"
    and "\<exists>j. f j = k"
proof -
  from assms have "mono f" and "surj f"
    unfolding is_stutter_fn_def by auto

  (* Prove Monotonicity *)
  show "f i \<le> f j" if "i \<le> j"
    using \<open>mono f\<close> that unfolding mono_def by simp

  (* Prove Surjectivity *)
  show "\<exists>j. f j = k"
    using \<open>surj f\<close> by (metis surjD)
qed

(* Helper Lemma:
   If f is a stuttering function (monotone + surjective), then for any range of
   indices [i, j) in the domain, the image covers the range [f(i), f(j)) in the codomain.
*)
lemma stutter_interval_surj:
  assumes "is_stutter_fn f"
  assumes "i \<le> j"
  assumes "k \<in> {f i ..< f j}" (* k is in the image range *)
  shows "\<exists>m. i \<le> m \<and> m < j \<and> f m = k"
proof -
  (* Since f is surjective and starts at 0, it hits every value up to f(j) *)
  (* Since f is monotone, the pre-image of k must intersect [i, j) if k is in [f(i), f(j)) *)
  have "surj f" and "mono f" using assms(1) is_stutter_fn_def by auto

  (* We look for the smallest index that maps to k or higher.
     Let's use a simpler argument: The set of pre-images of k is non-empty. *)
  have "\<exists>x. f x = k" using \<open>surj f\<close>
    by (simp add: assms(1) stutter_properties(2))
  then obtain x where "f x = k" by blast

  (* We need to show we can find such an x within [i, j) *)
  (* If x < i, then f(x) <= f(i). But k >= f(i). So f(x)=f(i)=k. Then i works. *)
  (* If x >= j, then f(x) >= f(j). But k < f(j). Contradiction. *)

  consider (less) "x < i" | (in_range) "i \<le> x \<and> x < j" | (greater) "x \<ge> j"
    by linarith
  then show ?thesis
  proof cases
    case less
    then have "f x \<le> f i" using \<open>mono f\<close> mono_def
      by (simp add: monoD)
    with \<open>f x = k\<close> and \<open>k \<in> {f i ..< f j}\<close> have "f i = k" by simp
    then have "f i = k \<and> i \<le> i \<and> i < j" using assms(3)
      using assms(2) nat_less_le by auto
    then show ?thesis by blast
  next
    case in_range
    with \<open>f x = k\<close> show ?thesis by blast
  next
    case greater
    then have "f x \<ge> f j" using \<open>mono f\<close> mono_def by auto
    with \<open>f x = k\<close> have "k \<ge> f j" by simp
    then have False using assms(3) by simp
    then show ?thesis by blast
  qed
qed

(* Main Lemma *)
lemma stutter_invariance_general:
  assumes "is_stutter_fn f"
  shows "sem T E (f i) \<phi> \<longleftrightarrow> sem (stretch_sys f T) (stretch_env f E) i \<phi>"
proof (induction \<phi> arbitrary: i E)
  case (Atom \<pi> a)
  show ?case
    unfolding sem.simps stretch_env_def stretch_trace_def o_def
    by simp
next
  case (Not \<phi>)
  show ?case using Not.IH by simp
next
  case (And \<phi>1 \<phi>2)
  show ?case using And.IH by simp
next
  case (Exists \<pi> \<phi>)
  show ?case
  proof
    (* Left to Right: Mapping a trace from T to stretch(T) *)
    assume "sem T E (f i) (Exists \<pi> \<phi>)"
    then obtain t where "t \<in> T" and witness: "sem T (E(\<pi> := t)) (f i) \<phi>" by auto

    (* Define the updated environment with the stretched trace *)
    let ?E_stretched = "(stretch_env f E)(\<pi> := stretch_trace f t)"

    (* 1. Show environment equivalence: stretch(E[\<pi>:=t]) == E'[\<pi>:=stretch(t)] *)
    have env_eq: "stretch_env f (E(\<pi> := t)) = ?E_stretched"
      unfolding stretch_env_def stretch_trace_def fun_upd_def by auto

    (* 2. Apply IH *)
    have "sem (stretch_sys f T) (stretch_env f (E(\<pi> := t))) i \<phi>"
      using Exists witness by blast
    then have "sem (stretch_sys f T) ?E_stretched i \<phi>"
      using env_eq by simp

    (* 3. Show the witness exists in the stretched system *)
    moreover have "stretch_trace f t \<in> stretch_sys f T"
      using \<open>t \<in> T\<close> unfolding stretch_sys_def by auto

    ultimately show "sem (stretch_sys f T) (stretch_env f E) i (Exists \<pi> \<phi>)"
      by auto
  next
    (* Right to Left: Mapping a trace from stretch(T) back to T *)
    assume "sem (stretch_sys f T) (stretch_env f E) i (Exists \<pi> \<phi>)"
    then obtain tf where "tf \<in> stretch_sys f T"
      and witness: "sem (stretch_sys f T) ((stretch_env f E)(\<pi> := tf)) i \<phi>" by auto

    (* Retrieve original trace t *)
    from \<open>tf \<in> stretch_sys f T\<close> obtain t where "t \<in> T" and "tf = stretch_trace f t"
      unfolding stretch_sys_def by auto

    let ?E_orig_upd = "E(\<pi> := t)"

    (* 1. Show environment equivalence *)
    have "stretch_env f ?E_orig_upd = (stretch_env f E)(\<pi> := tf)"
      using \<open>tf = stretch_trace f t\<close> unfolding stretch_env_def stretch_trace_def fun_upd_def by auto

    (* 2. Apply IH (Reverse direction) *)
    (* We know RHS holds for stretched env, implies LHS holds for orig env *)
    have "sem (stretch_sys f T) (stretch_env f ?E_orig_upd) i \<phi>"
      using witness \<open>stretch_env f ?E_orig_upd = (stretch_env f E)(\<pi> := tf)\<close> by simp

    then have "sem T ?E_orig_upd (f i) \<phi>"
      using Exists.IH by blast

    then show "sem T E (f i) (Exists \<pi> \<phi>)" using \<open>t \<in> T\<close> by auto
  qed
next
  case (Until \<phi>1 \<phi>2)
  show ?case
  proof
    (* === Direction 1: LHS (Original) implies RHS (Stretched) === *)
    assume LHS: "sem T E (f i) (Until \<phi>1 \<phi>2)"
    then obtain K where "K \<ge> f i"
      and sat2: "sem T E K \<phi>2"
      and sat1: "\<forall>J. f i \<le> J \<and> J < K \<longrightarrow> sem T E J \<phi>1" by auto

    (* We need to find a k' in the stretched time such that f(k') = K *)
    (* Since f is surjective, K has a pre-image. Since f is mono, we pick the smallest. *)
    (* However, we just need ANY k' \<ge> i. *)

    (* Let k_min be the smallest index mapping to K *)
    have "\<exists>x. f x = K" using assms is_stutter_fn_def surj_def
      by metis
    then have set_nonempty: "{x. f x = K} \<noteq> {}" by auto
    define k_min where "k_min = Inf {x. f x = K}"

    have "f k_min = K"
      using set_nonempty Inf_nat_def1
      by (metis (mono_tags, lifting) k_min_def mem_Collect_eq)

    (* We define our witness k' for the RHS.
       If K == f(i), we can just pick i.
       If K > f(i), then k_min must be > i. *)
    define k_prime where "k_prime = max i k_min"

    (* Proof that k_prime is a valid witness for RHS *)
    have "f k_prime = K"
    proof (cases "K = f i")
      case True
      (* If K = f i, then f k_min = f i. Since f is mono, k_min <= i is possible. *)
      (* But f(max i k_min) = f(i) = K is valid. *)
      then show ?thesis using \<open>f k_min = K\<close> assms is_stutter_fn_def mono_def
        by (simp add: k_prime_def)

    next
      case False
      (* If K > f i, then k_min must be > i *)
      have "K > f i" using \<open>K \<ge> f i\<close> False by simp
      have "f i < f k_min" using \<open>K > f i\<close> \<open>f k_min = K\<close> by simp
      then have "i < k_min" using assms is_stutter_fn_def mono_def
        by (meson mono_strict_invE)

      then have "k_prime = k_min" unfolding k_prime_def by simp
      then show ?thesis using \<open>f k_min = K\<close> by simp
    qed

    (* 1. Check \<phi>2 at k_prime *)
    have "sem (stretch_sys f T) (stretch_env f E) k_prime \<phi>2"
      using Until.IH(2) sat2 \<open>f k_prime = K\<close>
      by blast

    (* 2. Check \<phi>1 on interval [i, k_prime) *)
    have "\<forall>j'. i \<le> j' \<and> j' < k_prime \<longrightarrow> sem (stretch_sys f T) (stretch_env f E) j' \<phi>1"
    proof (rule allI, rule impI)
      fix j' assume range: "i \<le> j' \<and> j' < k_prime"

      let ?J = "f j'"

      (* Map j' to ?J. Check if ?J is in the LHS interval [f i, K) *)
      have "f i \<le> ?J" using range assms is_stutter_fn_def mono_def by (simp add: monoD)
      have "?J < K"
      proof -
        have "f j' \<le> f k_prime" using range assms is_stutter_fn_def mono_def by (simp add: monoD)
        (* We need strict inequality. Since k_prime is the MINIMUM or i, and j' < k_prime. *)
        (* If j' < k_prime, then j' < k_min (since k_prime is max i k_min and j' >= i) *)
        have "j' < k_min" using range k_prime_def
          by linarith
        (* If f j' = K, that contradicts k_min being the Inf of {x. f x = K} *)
        have "f j' \<noteq> K"
        proof
           assume "f j' = K"
           then have "j' \<in> {x. f x = K}" by simp
           then have "k_min \<le> j'" unfolding k_min_def using Inf_nat_def1
             by (simp add: wellorder_Inf_le1)

           then show False using \<open>j' < k_min\<close> by simp
        qed
        then show ?thesis using \<open>f j' \<le> f k_prime\<close> \<open>f k_prime = K\<close> by simp
      qed

      (* Since ?J is in LHS interval, \<phi>1 holds at ?J in LHS *)
      have "sem T E ?J \<phi>1" using sat1 \<open>f i \<le> ?J\<close> \<open>?J < K\<close> by simp

      (* By IH, \<phi>1 holds at j' in RHS *)
      then show "sem (stretch_sys f T) (stretch_env f E) j' \<phi>1"
        using Until.IH(1) by simp
    qed

    then show "sem (stretch_sys f T) (stretch_env f E) i (Until \<phi>1 \<phi>2)"
      using \<open>sem (stretch_sys f T) (stretch_env f E) k_prime \<phi>2\<close> k_prime_def
      by (smt (verit) dual_order.refl max_def sem.simps(4))

  next
    (* === Direction 2: RHS (Stretched) implies LHS (Original) === *)
    assume RHS: "sem (stretch_sys f T) (stretch_env f E) i (Until \<phi>1 \<phi>2)"
    then obtain k_prime where "k_prime \<ge> i"
      and sat2: "sem (stretch_sys f T) (stretch_env f E) k_prime \<phi>2"
      and sat1: "\<forall>j'. i \<le> j' \<and> j' < k_prime \<longrightarrow> sem (stretch_sys f T) (stretch_env f E) j' \<phi>1"
      by auto

    let ?K = "f k_prime"

    (* 1. Check \<phi>2 at ?K *)
    have "sem T E ?K \<phi>2"
      using Until.IH(2) sat2 by simp

    (* 2. Check \<phi>1 on LHS interval [f i, ?K) *)
    have "\<forall>J. f i \<le> J \<and> J < ?K \<longrightarrow> sem T E J \<phi>1"
    proof (rule allI, rule impI)
      fix J assume range: "f i \<le> J \<and> J < ?K"

      (* We need a witness j' in [i, k_prime) such that f j' = J *)
      have "\<exists>j'. i \<le> j' \<and> j' < k_prime \<and> f j' = J"
        using stutter_interval_surj[OF assms(1)] \<open>k_prime \<ge> i\<close> range by simp
      then obtain j' where "i \<le> j'" "j' < k_prime" "f j' = J" by auto

      (* RHS satisfies \<phi>1 at j' *)
      have "sem (stretch_sys f T) (stretch_env f E) j' \<phi>1"
        using sat1 \<open>i \<le> j'\<close> \<open>j' < k_prime\<close> by simp

      (* By IH, LHS satisfies \<phi>1 at f(j') = J *)
      then show "sem T E J \<phi>1"
        using Until.IH(1) \<open>f j' = J\<close> by auto
    qed

    then show "sem T E (f i) (Until \<phi>1 \<phi>2)"
      using \<open>sem T E ?K \<phi>2\<close> \<open>k_prime \<ge> i\<close> assms is_stutter_fn_def mono_def
      by (metis (no_types, lifting) sem.simps(4)) 
  qed
qed


section \<open>5. Final Theorem\<close>

(* Theorem: A system T satisfies a closed HyperLTL_{-X} formula \<phi>
   if and only if the synchronously stuttered system T_f satisfies \<phi>.
*)
theorem hyperltl_stutter_invariant:
  assumes "is_stutter_fn f"
  assumes "closed \<phi>"
  shows "T \<Turnstile> \<phi> \<longleftrightarrow> (stretch_sys f T) \<Turnstile> \<phi>"
proof -
  (* Unpack the top-level definition *)
  have LHS: "T \<Turnstile> \<phi> \<longleftrightarrow> (\<forall>E. sem T E 0 \<phi>)"
    using assms(2) models_system_def by simp

  have RHS: "(stretch_sys f T) \<Turnstile> \<phi> \<longleftrightarrow> (\<forall>E'. sem (stretch_sys f T) E' 0 \<phi>)"
    using assms(2) models_system_def by simp

  (* Apply the main lemma at i=0 *)
  have "sem T E 0 \<phi> \<longleftrightarrow> sem (stretch_sys f T) (stretch_env f E) 0 \<phi>" for E
    using stutter_invariance_general[OF assms(1), where i=0]
    using assms(1) unfolding is_stutter_fn_def by simp

  (* Since \<phi> is closed, we can map any E' back to a corresponding E *)
  show ?thesis
    unfolding LHS RHS
    using stutter_invariance_general[OF assms(1), where i=0]
    using assms(1) unfolding is_stutter_fn_def
      by (metis assms(2) closed_def empty_iff semantics_depend_only_on_free_vars)
  qed

section \<open>6. Concrete Example: Doubling Time\<close>

(* 1. Define a concrete stuttering function: f(n) = n div 2
      Mapping: 0->0, 1->0, 2->1, 3->1, 4->2 ...
      This causes every state in the original trace to repeat twice. *)
definition f_double :: "nat \<Rightarrow> nat" where
  "f_double n = n div 2"

(* 2. Prove it is a valid stuttering function *)
lemma f_double_is_stutter: "is_stutter_fn f_double"
proof -
  have "f_double 0 = 0" unfolding f_double_def by simp

  have "mono f_double"
    unfolding mono_def f_double_def by (auto simp: div_le_mono)

    have "surj f_double"
    unfolding surj_def f_double_def
    by (metis add_self_div_2)

   show ?thesis
    by (simp add: \<open>f_double 0 = 0\<close> \<open>mono f_double\<close> \<open>surj f_double\<close> is_stutter_fn_def)
qed

(* 3. Define a setup with concrete atoms *)
axiomatization a b :: AP

(* A simple trace: {a} at step 0, {b} forever after *)
definition "trace_simple n = (if n = 0 then {a} else {b})"

(* The system containing just this one trace *)
definition "Sys_Simple = {trace_simple}"

(* A formula: "There exists a trace where 'a' holds until 'b' holds" *)
definition "phi_example = Exists ''pi'' (Until (Atom ''pi'' a) (Atom ''pi'' b))"

(* 4. If formula holds on the original system, it holds on the stuttered one. *)
theorem example_stutter_equivalence:
  "(Sys_Simple \<Turnstile> phi_example) \<longleftrightarrow> (stretch_sys f_double Sys_Simple \<Turnstile> phi_example)"
proof -
  have "is_stutter_fn f_double" using f_double_is_stutter .
  moreover have "closed phi_example"
    unfolding phi_example_def closed_def by simp
  ultimately show ?thesis
    using hyperltl_stutter_invariant by blast
qed

(* 5. Sanity check that the property actually holds *)
lemma example_sanity_check: "Sys_Simple \<Turnstile> phi_example"
  unfolding models_system_def
proof (intro conjI)
  (* 1. Show Closedness *)
  show "closed phi_example"
    unfolding phi_example_def closed_def by simp
next
  (* 2. Show Validity for any environment *)
  show "\<forall>E. sem Sys_Simple E 0 phi_example"
    unfolding Sys_Simple_def phi_example_def trace_simple_def
    by auto
qed

end
