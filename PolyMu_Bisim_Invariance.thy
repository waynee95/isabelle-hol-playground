theory PolyMu_Bisim_Invariance
  imports Main "HOL-Library.FSet" "HOL-Library.FuncSet" "HOL-Library.Finite_Map"
begin

text \<open>Finite index type for tuple dimensions\<close>
class finite_index = finite

text \<open>Labelled transition systems\<close>
record ('s,'a,'p) LTS =
  step :: "'s \<Rightarrow> 'a \<Rightarrow> 's set"    (* transitions *)
  props :: "'s \<Rightarrow> 'p set"         (* atomic propositions true at a state *)

abbreviation step_unl :: "('s,'a,'p) LTS \<Rightarrow> 's \<Rightarrow> 's set" where
  "step_unl M s \<equiv> (\<Union>a. step M s a)"

text \<open>Tuples are functions from an index type \<iota> to states\<close>
type_synonym ('\<iota>,'s) tup = "'\<iota> \<Rightarrow> 's"

text \<open>Apply a permutation \<pi> to a tuple: (\<pi>\<bullet>t) i = t (\<pi> i)\<close>
definition perm_tup :: "('\<iota> \<Rightarrow> '\<iota>) \<Rightarrow> ('\<iota>,'s) tup \<Rightarrow> ('\<iota>,'s) tup"
  where "perm_tup \<pi> t i = t (\<pi> i)"

text \<open>Move only the i-th component along one transition step\<close>
definition move_i :: "('s,'a,'p) LTS \<Rightarrow> 'a \<Rightarrow> '\<iota> \<Rightarrow> ('\<iota>,'s) tup \<Rightarrow> ('\<iota>,'s) tup set"
  where "move_i M a i t = {t'. (\<forall>j. j \<noteq> i \<longrightarrow> t' j = t j) \<and> t' i \<in> step M (t i) a}"

text \<open>Atoms are component-indexed: p holds at component i\<close>
datatype ('\<iota>::finite_index,'a,'p,'var) pfml =
    Atom '\<iota> 'p
  | Not "('\<iota>,'a,'p,'var) pfml"
  | And "('\<iota>,'a,'p,'var) pfml" "('\<iota>,'a,'p,'var) pfml"
  | Dia '\<iota> 'a "('\<iota>,'a,'p,'var) pfml"
  | Perm "('\<iota> \<Rightarrow> '\<iota>)" "('\<iota>,'a,'p,'var) pfml"
  | Var 'var
  | Mu 'var "('\<iota>,'a,'p,'var) pfml"
  | Nu 'var "('\<iota>,'a,'p,'var) pfml"

text \<open>Environments map variables to sets of tuples\<close>
type_synonym ('\<iota>,'s,'var) env = "'var \<Rightarrow> ('\<iota>,'s) tup set"

text \<open>Semantic evaluation as a set of satisfying tuples\<close>
primrec eval ::
  "('s,'a,'p) LTS \<Rightarrow> ('\<iota>::finite_index,'s,'var) env \<Rightarrow> ('\<iota>,'a,'p,'var) pfml \<Rightarrow> ('\<iota>,'s) tup set"
where
  "eval M \<rho> (Atom i p) = {t. p \<in> props M (t i)}"
| "eval M \<rho> (Not \<phi>) = - (eval M \<rho> \<phi>)"
| "eval M \<rho> (And \<phi> \<psi>) = (eval M \<rho> \<phi>) \<inter> (eval M \<rho> \<psi>)"
| "eval M \<rho> (Dia i a \<phi>) = {t. \<exists>t' \<in> eval M \<rho> \<phi>. \<exists>u\<in>move_i M a i t. u = t'}"
| "eval M \<rho> (Perm \<pi> \<phi>) = {t. perm_tup \<pi> t \<in> eval M \<rho> \<phi>}"
| "eval M \<rho> (Var X) = \<rho> X"
| "eval M \<rho> (Mu X \<phi>) = lfp (\<lambda>S. eval M (\<rho>(X := S)) \<phi>)"
| "eval M \<rho> (Nu X \<phi>) = gfp (\<lambda>S. eval M (\<rho>(X := S)) \<phi>)"

text \<open>We will assume standard positivity/monotonicity side-condition for \<mu>, \<nu>.\<close>

text \<open>Pointwise order on environments\<close>
definition env_le :: "('\<iota>,'s,'var) env \<Rightarrow> ('\<iota>,'s,'var) env \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
  where "\<rho> \<sqsubseteq> \<rho>' \<longleftrightarrow> (\<forall>X. \<rho> X \<subseteq> \<rho>' X)"

lemma env_le_refl [simp]: "\<rho> \<sqsubseteq> \<rho>"
  by (simp add: env_le_def)

lemma env_le_trans: "\<rho> \<sqsubseteq> \<rho>' \<Longrightarrow> \<rho>' \<sqsubseteq> \<rho>'' \<Longrightarrow> \<rho> \<sqsubseteq> \<rho>''"
  by (simp add: env_le_def; blast)

lemma env_le_update:
  assumes "S \<subseteq> T"
  shows "\<rho>(X := S) \<sqsubseteq> \<rho>(X := T)"
  using assms by (simp add: env_le_def)

text \<open>Positivity of variable X in a formula (no rule for Not)\<close>
inductive pos :: "'var \<Rightarrow> ('\<iota>::finite_index,'a,'p,'var) pfml \<Rightarrow> bool" where
  pos_Atom:        "pos X (Atom i p)"
| pos_Var_same:    "X \<noteq> Y \<Longrightarrow> pos X (Var Y)"
| pos_Var_self:    "pos X (Var X)"
| pos_And:         "pos X \<phi> \<Longrightarrow> pos X \<psi> \<Longrightarrow> pos X (And \<phi> \<psi>)"
| pos_Dia:         "pos X \<phi> \<Longrightarrow> pos X (Dia i a \<phi>)"
| pos_Perm:        "pos X \<phi> \<Longrightarrow> pos X (Perm \<pi> \<phi>)"
| pos_Mu:          "pos X \<phi> \<Longrightarrow> pos Y \<phi> \<Longrightarrow> pos X (Mu Y \<phi>)"
| pos_Nu:          "pos X \<phi> \<Longrightarrow> pos Y \<phi> \<Longrightarrow> pos X (Nu Y \<phi>)"
(* No constructor for Not: if you use Not, ensure the variable X does not occur under it. *)

text \<open>Helper: monotonicity in all env variables for positive formulas\<close>
lemma eval_mono_env:
  fixes \<phi>  :: "('\<iota>::finite_index,'a,'p,'var) pfml"
    and \<rho>  :: "('\<iota>,'s,'var) env"
    and \<rho>' :: "('\<iota>,'s,'var) env"
  assumes "pos X \<phi>" and "\<rho> \<sqsubseteq> \<rho>'"
  shows "eval M \<rho> \<phi> \<subseteq> eval M \<rho>' \<phi>"
  using assms
proof (induction arbitrary: \<rho> \<rho>')
  case (pos_Atom X i p)
  then show ?case by simp 
next
  case (pos_Var_same X Y)
  then show ?case by (simp add: env_le_def) 
next
  case (pos_Var_self X)
  then show ?case by (simp add: env_le_def)
next
  case (pos_And X \<phi> \<psi>)
  then show ?case
    by fastforce 
next
  case (pos_Dia X \<phi> i a)
  then show ?case by (auto simp: move_i_def)
next
  case (pos_Perm X \<phi> \<pi>)
  then show ?case by auto
next
  case (pos_Mu X \<phi> Y)
  note IH_X = pos_Mu.IH(1)
  note IH_Y = pos_Mu.IH(2)

  have upd_mono_same:
    "\<rho> \<sqsubseteq> \<rho>' \<Longrightarrow> \<rho>(Y := S) \<sqsubseteq> \<rho>'(Y := S)" for S
    unfolding env_le_def by simp
  have upd_mono_arg:
    "S \<subseteq> T \<Longrightarrow> \<rho>(Y := S) \<sqsubseteq> \<rho>(Y := T)" for S T
    unfolding env_le_def by simp

  define F  :: "(('\<iota>,'s) tup) set \<Rightarrow> (('\<iota>,'s) tup) set"
    where "F  S = eval M (\<rho> (Y := S))  \<phi>" for S
  define F' :: "(('\<iota>,'s) tup) set \<Rightarrow> (('\<iota>,'s) tup) set"
    where "F' S = eval M (\<rho>'(Y := S)) \<phi>" for S

  have mono_F: "mono F"
  proof (rule monoI)
    fix S T :: "(('\<iota>,'s) tup) set"
    assume "S \<subseteq> T"
    then have "\<rho>(Y := S) \<sqsubseteq> \<rho>(Y := T)" by (rule upd_mono_arg)
    then have "eval M (\<rho>(Y := S)) \<phi> \<subseteq> eval M (\<rho>(Y := T)) \<phi>" by (rule IH_Y)
    then show "F S \<subseteq> F T" unfolding F_def by simp
  qed

  have mono_F': "mono F'"
  proof (rule monoI)
    fix S T :: "(('\<iota>,'s) tup) set"
    assume "S \<subseteq> T"
    then have "\<rho>'(Y := S) \<sqsubseteq> \<rho>'(Y := T)"
      unfolding env_le_def by simp
    then have "eval M (\<rho>'(Y := S)) \<phi> \<subseteq> eval M (\<rho>'(Y := T)) \<phi>" by (rule IH_Y)
    then show "F' S \<subseteq> F' T" unfolding F'_def by simp
  qed

  have F_le_F': "F \<le> F'"
  proof (intro le_funI)
    fix S :: "(('\<iota>,'s) tup) set"
     have "\<rho>(Y := S) \<sqsubseteq> \<rho>'(Y := S)"
       using pos_Mu.prems upd_mono_same by blast 
     then have "eval M (\<rho>(Y := S)) \<phi> \<subseteq> eval M (\<rho>'(Y := S)) \<phi>" by (rule IH_X)
     then show "F S \<subseteq> F' S" unfolding F_def F'_def by simp
  qed

  have "lfp F \<subseteq> lfp F'"
    by (meson F_le_F' lfp_mono le_fun_def)
  moreover have "eval M \<rho>  (Mu Y \<phi>) = lfp F"
    by (simp add: \<open>F \<equiv> \<lambda>S. eval M (\<rho>(Y := S)) \<phi>\<close>) 
  moreover have "eval M \<rho>' (Mu Y \<phi>) = lfp F'" 
    by (simp add: \<open>F' \<equiv> \<lambda>S. eval M (\<rho>'(Y := S)) \<phi>\<close>) 
  ultimately show ?case by simp
next
  case (pos_Nu X \<phi> Y)
  note IH_X = pos_Nu.IH(1)
  note IH_Y = pos_Nu.IH(2)

  have upd_mono_same:
    "\<rho> \<sqsubseteq> \<rho>' \<Longrightarrow> \<rho>(Y := S) \<sqsubseteq> \<rho>'(Y := S)" for S
    unfolding env_le_def by simp
  have upd_mono_arg:
    "S \<subseteq> T \<Longrightarrow> \<rho>(Y := S) \<sqsubseteq> \<rho>(Y := T)" for S T
    unfolding env_le_def by simp

  define F  :: "(('\<iota>,'s) tup) set \<Rightarrow> (('\<iota>,'s) tup) set"
    where "F  S = eval M (\<rho> (Y := S))  \<phi>" for S
  define F' :: "(('\<iota>,'s) tup) set \<Rightarrow> (('\<iota>,'s) tup) set"
    where "F' S = eval M (\<rho>'(Y := S)) \<phi>" for S

  have mono_F: "mono F"
  proof (rule monoI)
    fix S T :: "(('\<iota>,'s) tup) set"
    assume "S \<subseteq> T"
    then have "\<rho>(Y := S) \<sqsubseteq> \<rho>(Y := T)" by (rule upd_mono_arg)
    then have "eval M (\<rho>(Y := S)) \<phi> \<subseteq> eval M (\<rho>(Y := T)) \<phi>" by (rule IH_Y)
    then show "F S \<subseteq> F T" unfolding F_def by simp
  qed

  have mono_F': "mono F'"
  proof (rule monoI)
    fix S T :: "(('\<iota>,'s) tup) set"
    assume "S \<subseteq> T"
    then have "\<rho>'(Y := S) \<sqsubseteq> \<rho>'(Y := T)"
      unfolding env_le_def by simp
    then have "eval M (\<rho>'(Y := S)) \<phi> \<subseteq> eval M (\<rho>'(Y := T)) \<phi>" by (rule IH_Y)
    then show "F' S \<subseteq> F' T" unfolding F'_def by simp
  qed

  have F_le_F': "F \<le> F'"
  proof (intro le_funI)
    fix S :: "(('\<iota>,'s) tup) set"
     have "\<rho>(Y := S) \<sqsubseteq> \<rho>'(Y := S)"
       using pos_Nu.prems upd_mono_same by blast 
     then have "eval M (\<rho>(Y := S)) \<phi> \<subseteq> eval M (\<rho>'(Y := S)) \<phi>" by (rule IH_X)
     then show "F S \<subseteq> F' S" unfolding F_def F'_def by simp
  qed

  have "gfp F \<subseteq> gfp F'"
    by (meson F_le_F' gfp_mono le_fun_def)
  moreover have "eval M \<rho>  (Nu Y \<phi>) = gfp F"
    by (simp add: \<open>F \<equiv> \<lambda>S. eval M (\<rho>(Y := S)) \<phi>\<close>) 
  moreover have "eval M \<rho>' (Nu Y \<phi>) = gfp F'" 
    by (simp add: \<open>F' \<equiv> \<lambda>S. eval M (\<rho>'(Y := S)) \<phi>\<close>) 
  ultimately show ?case by simp
qed

text \<open>Specialization: monotone in a single variable via env update\<close>
lemma mono_eval_in_var:
  assumes "pos X \<phi>"
  shows "mono (\<lambda>S :: ('\<iota>::finite_index,'s) tup set. eval M (\<rho>(X := S)) \<phi>)"
proof (rule monoI)
  fix A B :: "('\<iota>,'s) tup set"
  assume "A \<subseteq> B"
  then have "\<rho>(X := A) \<sqsubseteq> \<rho>(X := B)"
    by (simp add: env_le_def)
  then show "eval M (\<rho>(X := A)) \<phi> \<subseteq> eval M (\<rho>(X := B)) \<phi>"
    using eval_mono_env[OF assms]
    by blast 
qed

text \<open>Product bisimulation between models M and N relates tuples component-wise
      and is closed under: atoms, component moves, and permutations.\<close>
locale prod_bisim =
  fixes M :: "('s,'a,'p) LTS" and N :: "('t,'a,'p) LTS"
  fixes R :: "(('\<iota>::finite_index,'s) tup \<times> ('\<iota>,'t) tup) set"
  assumes atoms:
    "\<lbrakk>(s,t)\<in>R; i\<in>UNIV\<rbrakk> \<Longrightarrow> props M (s i) = props N (t i)"
  and forth:
    "\<lbrakk>(s,t)\<in>R; i\<in>UNIV\<rbrakk> \<Longrightarrow>
      (\<forall>a s'. s' \<in> step M (s i) a \<longrightarrow>
            (\<exists>t'. t' \<in> step N (t i) a \<and> (s(i := s'), t(i := t')) \<in> R))"
  and backk:
    "\<lbrakk>(s,t)\<in>R; i\<in>UNIV\<rbrakk> \<Longrightarrow>
      (\<forall>a t'. t' \<in> step N (t i) a \<longrightarrow>
            (\<exists>s'. s' \<in> step M (s i) a \<and> (s(i := s'), t(i := t')) \<in> R))"
  and perm_closed:
    "\<lbrakk>(s,t)\<in>R\<rbrakk> \<Longrightarrow> (perm_tup \<pi> s, perm_tup \<pi> t) \<in> R"
begin

text \<open>Relational lifting of environments across R\<close>
definition lift_env :: "('\<iota>,'s,'var) env \<Rightarrow> ('\<iota>,'t,'var) env"
  where "lift_env \<rho> X = { t. \<exists>s\<in>\<rho> X. (s,t)\<in>R }"

lemma lift_env_mono: "A \<subseteq> B \<Longrightarrow> lift_env (\<lambda>_. A) X \<subseteq> lift_env (\<lambda>_. B) X"
  by (auto simp: lift_env_def)

text \<open>Main preservation lemma by structural induction\<close>
definition R_src :: "((('\<iota> \<Rightarrow> 's)) \<times> (('\<iota> \<Rightarrow> 's))) set" where
  "R_src \<equiv> { (u,v). \<exists>w. (u,w) \<in> R \<and> (v,w) \<in> R }"

definition R_closed :: "(('\<iota> \<Rightarrow> 's) set) \<Rightarrow> bool" where
  "R_closed S \<longleftrightarrow> (\<forall>u v. (u,v) \<in> R_src \<longrightarrow> (u\<in>S \<longleftrightarrow> v\<in>S))"

definition env_R_closed :: "('\<iota>,'s,'var) env \<Rightarrow> bool" where
  "env_R_closed \<rho> \<longleftrightarrow> (\<forall>X. R_closed (\<rho> X))"

lemma preservation:
  assumes "(s,t)\<in>R" and "env_R_closed \<rho>"
  shows "(s \<in> eval M \<rho> \<phi>) \<longleftrightarrow> (t \<in> eval N (lift_env \<rho>) \<phi>)"
  using assms
proof (induction \<phi> arbitrary: s t \<rho>)
  case (Atom i p)
  then show ?case
    using atoms[of s t i] by simp
next
  case (Not \<phi>)
  then show ?case by auto
next
  case (And \<phi> \<psi>)
  then show ?case by auto
next
case (Var X)
  have "(s \<in> \<rho> X) \<longleftrightarrow> (t \<in> lift_env \<rho> X)"
    proof
      assume "s \<in> \<rho> X"
      with Var.prems(1) show "t \<in> lift_env \<rho> X"
        by (auto simp: lift_env_def)
    next
      assume "t \<in> lift_env \<rho> X"
      then obtain s' where "s' \<in> \<rho> X" "(s',t) \<in> R"
        by (auto simp: lift_env_def)
      with Var.prems(1) have "(s,s') \<in> R_src"
        by (auto simp: R_src_def)
      moreover have "R_closed (\<rho> X)"
        using Var.prems(2) by (auto simp: env_R_closed_def)
      ultimately show "s \<in> \<rho> X"
        using \<open>s' \<in> \<rho> X\<close> by (auto simp: R_closed_def)
    qed
  then show ?case by simp 
next
  case (Dia i a \<phi>)
  then show ?case sorry
(* proof -
  assume "s \<in> eval M \<rho> (Dia i a \<phi>)"
  then obtain u where u_def:
    "u \<in> eval M \<rho> \<phi>" "\<exists>u'. u' \<in> move_i M a i s \<and> u' = u"
    by auto
  from Dia.prems forth[of s t i] obtain t' where
    t'_step: "t' \<in> step N (t i) a" and
    rel: "(s(i := u i), t(i := t')) \<in> R"
    using u_def(2) move_i_def by (metis (no_types, lifting) UNIV_I mem_Collect_eq)

  (* By IH, the related update satisfies \<phi> on the N-side *)
  obtain u' where umove: "u' \<in> move_i M a i s" "u' = u"
    using u_def(2) by blast
  then have u_move: "u \<in> move_i M a i s" by simp

  have u_eq: "s(i := u i) = u"
    using u_move unfolding move_i_def by auto

  from Dia.IH[OF rel, of \<rho>]
  have eqv: "(s(i := u i) \<in> eval M \<rho> \<phi>) = (t(i := t') \<in> eval N (lift_env \<rho>) \<phi>)"
    using Dia.prems(2) by blast 

  have t_eval: "t(i := t') \<in> eval N (lift_env \<rho>) \<phi>"
    using eqv u_def(1) u_eq by simp

  (* And the updated tuple is exactly a one-step i-move from t *)
  have t_move: "t(i := t') \<in> move_i N a i t"
    using t'_step by (auto simp: move_i_def)

  (* Package both facts to witness the diamond on the N-side *)
  have "\<exists>v\<in>eval N (lift_env \<rho>) \<phi>. \<exists>w\<in>move_i N a i t. w = v"
    using t_eval t_move by (intro bexI[of _ "t(i := t')"]) auto
  then show "t \<in> eval N (lift_env \<rho>) (Dia i a \<phi>)" by auto
next
  (* the reverse direction is your other subcase *)
  assume "t \<in> eval N (lift_env \<rho>) (Dia i a \<phi>)"
  then obtain v where v_def:
    "v \<in> eval N (lift_env \<rho>) \<phi>" "\<exists>w\<in>move_i N a i t. w = v"
    by auto
  then obtain vstep where vstep:
    "(\<forall>j. j \<noteq> i \<longrightarrow> v j = t j)" "v i \<in> step N (t i) a"
    using move_i_def by fastforce
  have v_eq: "v = t(i := v i)"
    using vstep(1) by (intro ext) (auto)
  have vin: "t(i := v i) \<in> eval N (lift_env \<rho>) \<phi>"
    using v_def(1) v_eq by simp
  from Dia.prems backk[of s t i] obtain s_i where
    s_i_step: "s_i \<in> step M (s i) a" and
    rel2: "(s(i := s_i), t(i := v i)) \<in> R"
    using vstep(2) by blast
  from IH[OF rel2, of \<rho>] vin
  have "(s(i := s_i)) \<in> eval M \<rho> \<phi>" by simp
  then have "\<exists>u\<in>eval M \<rho> \<phi>. \<exists>u'\<in>move_i M a i s. u' = u"
    using s_i_step move_i_def by fastforce 
  then show "s \<in> eval M \<rho> (Dia i a \<phi>)" by auto
qed *)
next
  case (Perm \<pi> \<phi>)
  then show ?case sorry
next 
  case (Mu X \<phi>)
  then show ?case sorry
next 
  case (Nu X \<phi>)
  then show ?case sorry
qed

text \<open>Main theorem: bisimulation invariance for closed formulas\<close>
theorem bisim_invariance_closed:
  assumes "(s,t)\<in>R"
  shows "(s \<in> eval M (\<lambda>_. {}) \<phi>) = (t \<in> eval N (\<lambda>_. {}) \<phi>)"
  using preservation[OF assms, of "\<lambda>_. {}" \<phi>] sorry

end  (* locale prod_bisim *)

end
