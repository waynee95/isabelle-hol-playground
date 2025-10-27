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
  then show ?case by fastforce 
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
    using eval_mono_env[OF assms] by blast 
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

(* little helpers *)
lemma perm: "(s,t)\<in>R \<Longrightarrow> (perm_tup \<pi> s, perm_tup \<pi> t)\<in>R"
  by (simp add: perm_closed)

lemma pos_Dia_inv: "pos X (Dia i a \<phi>) \<Longrightarrow> pos X \<phi>"
  by (auto elim: pos.cases)

lemma pos_Perm_inv: "pos X (Perm \<pi> \<phi>) \<Longrightarrow> pos X \<phi>"
  by (auto elim: pos.cases)

lemma pos_NotE: "pos X (Not \<phi>) \<Longrightarrow> False"
  using pos.cases by fastforce

lemma pos_And_inv1: "pos X (And \<phi> \<psi>) \<Longrightarrow> pos X \<phi>"
  using pos.cases by fastforce

lemma pos_And_inv2: "pos X (And \<phi> \<psi>) \<Longrightarrow> pos X \<psi>"
  using pos.cases by fastforce

definition lift_set :: "(('\<iota>,'s) tup) set \<Rightarrow> (('\<iota>,'t) tup) set"
  where "lift_set S = { v. \<exists>u\<in>S. (u,v) \<in> R }"

lemma lift_env_update:
  "lift_env (\<rho>(X := S)) = (lift_env \<rho>)(X := lift_set S)"
  by (auto simp: lift_env_def lift_set_def fun_eq_iff split: if_splits)

primrec funpow  where
  "funpow 0 f x = x"
| "funpow (Suc n) f x = f (funpow n f x)"

definition appr
  where "appr F n = funpow n F {}"

definition appr'
  where "appr' G n = funpow n G {}"

lemma appr_0[simp]: "appr F 0 = {}"
  by (simp add: appr_def)

lemma appr_Suc[simp]: "appr F (Suc n) = F (appr F n)"
  by (simp add: appr_def funpow_Suc_right)

lemma appr'_0[simp]: "appr' G 0 = {}"
  by (simp add: appr'_def)

lemma appr'_Suc[simp]: "appr' G (Suc n) = G (appr' G n)"
  by (simp add: appr'_def funpow_Suc_right)

(* increasing chain *)
lemma appr_chain: 
  assumes "mono F" 
  shows "appr F n \<subseteq> appr F (Suc n)"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  from assms Suc.IH have "F (appr F n) \<subseteq> F (appr F (Suc n))"
    by (rule monoD)
  then show ?case by simp
qed

lemma appr'_chain: 
  assumes "mono G" 
  shows "appr' G n \<subseteq> appr' G (Suc n)"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  from assms Suc.IH have "G (appr' G n) \<subseteq> G (appr' G (Suc n))"
    by (rule monoD)
  then show ?case by simp
qed

(* preservation lemma *)
lemma preservation:
  assumes "(s,t)\<in>R" and "env_R_closed \<rho>" and "pos X \<phi>"
  shows "(s \<in> eval M \<rho> \<phi>) \<longleftrightarrow> (t \<in> eval N (lift_env \<rho>) \<phi>)"
    using assms
proof (induction \<phi> arbitrary: s t \<rho>)
  case (Atom i p)
  then show ?case
    by (simp add: atoms) 
next
  case (Not \<phi>)
  have False using Not.prems(3) by (rule pos_NotE)
  then show ?case by simp
next
  case (And \<phi>1 \<phi>2)
  have pos1: "pos X \<phi>1" using And.prems(3) by (rule pos_And_inv1)
  have pos2: "pos X \<phi>2" using And.prems(3) by (rule pos_And_inv2)

  have IH1: "s \<in> eval M \<rho> \<phi>1 \<longleftrightarrow> t \<in> eval N (lift_env \<rho>) \<phi>1"
    using And.IH(1)[OF And.prems(1) And.prems(2) pos1] .

  have IH2: "s \<in> eval M \<rho> \<phi>2 \<longleftrightarrow> t \<in> eval N (lift_env \<rho>) \<phi>2"
    using And.IH(2)[OF And.prems(1) And.prems(2) pos2] .

  with IH1 IH2 show ?case by simp
next
  case (Dia i a \<phi>)
  show ?case 
  proof (rule iffI)
    (* \<rightarrow> direction *)
    assume "s \<in> eval M \<rho> (Dia i a \<phi>)"
    then obtain u where u\<phi>: "u \<in> eval M \<rho> \<phi>" and umv: "u \<in> move_i M a i s"
      by auto
    
    from Dia.prems(1) forth umv
    obtain t' where tstep: "t' \<in> step N (t i) a"
                  and rel:   "(s(i := u i), t(i := t')) \<in> R"
      by (metis (no_types, lifting) iso_tuple_UNIV_I mem_Collect_eq
          move_i_def)

    have pos\<phi>: "pos X \<phi>" using Dia.prems(3) by (rule pos_Dia_inv)
    
    have IH_inst:
      "s(i := u i) \<in> eval M \<rho> \<phi> \<longleftrightarrow> t(i := t') \<in> eval N (lift_env \<rho>) \<phi>"
      using Dia.IH[OF rel Dia.prems(2) pos\<phi>] .

    from umv have u_eq: "u = s(i := u i)"
      using move_i_def by fastforce
    with u\<phi> have "s(i := u i) \<in> eval M \<rho> \<phi>"
      by simp
    then have "t(i := t') \<in> eval N (lift_env \<rho>) \<phi>"
      using \<open>s(i := u i) \<in> eval M \<rho> \<phi> 
        \<longleftrightarrow> t(i := t') \<in> eval N (lift_env \<rho>) \<phi>\<close> by blast
    moreover have "t(i := t') \<in> move_i N a i t"
      using tstep by (auto simp: move_i_def)
    ultimately show "t \<in> eval N (lift_env \<rho>) (Dia i a \<phi>)"
      by auto
  next
    (* \<leftarrow> direction *)
    assume "t \<in> eval N (lift_env \<rho>) (Dia i a \<phi>)"
    then obtain v where v\<phi>: "v \<in> eval N (lift_env \<rho>) \<phi>"
                    and vmv: "v \<in> move_i N a i t"
      by auto
    from vmv have vshape: "(\<forall>j. j \<noteq> i \<longrightarrow> v j = t j)" 
                    and vstep: "v i \<in> step N (t i) a"
      by (auto simp: move_i_def)

    from Dia.prems(1) backk vstep
    obtain s_i where sstep: "s_i \<in> step M (s i) a"
                and rel2:  "(s(i := s_i), t(i := v i)) \<in> R"
      by blast

    have pos\<phi>: "pos X \<phi>" using Dia.prems(3) by (rule pos_Dia_inv)

    have IH_inst':
      "s(i := s_i) \<in> eval M \<rho> \<phi> \<longleftrightarrow> t(i := v i) \<in> eval N (lift_env \<rho>) \<phi>"
      using Dia.IH[OF rel2 Dia.prems(2) pos\<phi>] .

    then have "s(i := s_i) \<in> eval M \<rho> \<phi>"
      using v\<phi> vshape
      by (metis (no_types, lifting) ext fun_upd_other fun_upd_same) 
    moreover have "s(i := s_i) \<in> move_i M a i s"
      using sstep by (auto simp: move_i_def)
    ultimately show "s \<in> eval M \<rho> (Dia i a \<phi>)"
      by auto
  qed
next
  case (Perm \<pi> \<phi>)
  (* R is closed under permuting coordinates *)
  have rel\<pi>: "(perm_tup \<pi> s, perm_tup \<pi> t) \<in> R"
    using Perm.prems(1) by (rule perm)

  (* Positivity passes through Perm, needed to apply the IH on \<phi> *)
  have pos\<phi>: "pos X \<phi>"
    using Perm.prems(3) by (rule pos_Perm_inv)

  (* Apply the IH at the permuted pair *)
  have "perm_tup \<pi> s \<in> eval M \<rho> \<phi> \<longleftrightarrow> perm_tup \<pi> t \<in> eval N (lift_env \<rho>) \<phi>"
    using Perm.IH[OF rel\<pi> Perm.prems(2) pos\<phi>] .

  then show ?case by simp
next
  case (Var x)
  have "s \<in> \<rho> x \<longleftrightarrow> t \<in> lift_env \<rho> x"
  proof (rule iffI)
    assume hs: "s \<in> \<rho> x"
    from Var.prems(1) have "(s,t) \<in> R" .
    with hs show "t \<in> lift_env \<rho> x"
      by (auto simp: lift_env_def)
  next
    assume ht: "t \<in> lift_env \<rho> x"
    then obtain s' where s'in: "s' \<in> \<rho> x" and s'R: "(s',t) \<in> R"
      by (auto simp: lift_env_def)

    from Var.prems(1) have st: "(s,t) \<in> R" .

    (* turn the two R-edges with common right node t into a pair in R_src *)
    have "(s,s') \<in> R_src"
      using st s'R by (auto simp: R_src_def)

    (* use that \<rho> is R-closed componentwise *)
    have "R_closed (\<rho> x)"
      using Var.prems(2) by (auto simp: env_R_closed_def)

    from this and \<open>(s,s') \<in> R_src\<close> and s'in
    show "s \<in> \<rho> x"
      by (auto simp: R_closed_def)
  qed
  then show ?case by simp
next
  case (Mu X \<phi>)
  define F  where "F  S = eval M (\<rho>(X := S))  \<phi>" for S
  define G  where "G  T = eval N ((lift_env \<rho>)(X := T)) \<phi>" for T

  have mono_F: "mono F" 
  proof (rule monoI)
    fix S T :: "(('\<iota>,'s) tup) set"
    assume "S \<subseteq> T"
    then have "\<rho>(Y := S) \<sqsubseteq> \<rho>(Y := T)" for Y
      by (simp add: env_le_update) 
    then have "eval M (\<rho>(Y := S)) \<phi> \<subseteq> eval M (\<rho>(Y := T)) \<phi>" for Y
      by (smt (verit, best) Mu.prems(3) eval_mono_env pfml.distinct(11,33,47,51,55)
          pfml.inject(7) pfml.simps(50) pos.cases)
    then show "F S \<subseteq> F T" unfolding F_def by simp
  qed

  have mono_G: "mono G" 
  proof (rule monoI)
    fix T U :: "(('\<iota>,'t) tup) set"
    assume "T \<subseteq> U"
    hence "((lift_env \<rho>)(X := T)) \<sqsubseteq> ((lift_env \<rho>)(X := U))"
      by (simp add: env_le_update)
    hence "eval N ((lift_env \<rho>)(X := T)) \<phi> \<subseteq> eval N ((lift_env \<rho>)(X := U)) \<phi>"
      using Mu.prems(3)
      by (smt (verit) eval_mono_env pfml.distinct(11,33,41,47,51,55) pfml.inject(7)
          pos.cases) (* pos X \<phi> *) 
    then show "G T \<subseteq> G U" unfolding G_def by simp
  qed

  (* If S is R-closed then both updated envs are R-closed. *)
  have env_closed_upd:
    "R_closed S \<Longrightarrow> env_R_closed (\<rho>(X := S))" for S
    using Mu.prems(2)
    by (auto simp: env_R_closed_def R_closed_def)

  (* IH instantiated on the body, with an updated env and the lifted env on N. *)
  have IH_upd:
    "\<lbrakk> (u,v)\<in>R; R_closed S \<rbrakk> \<Longrightarrow>
       (u \<in> eval M (\<rho>(X := S)) \<phi>) \<longleftrightarrow> (v \<in> eval N (lift_env (\<rho>(X := S))) \<phi>)"
    for u v S
    using Mu.IH[of u v "\<rho>(X := S)"] env_closed_upd Mu.prems(3)
    by (smt (verit, ccfv_threshold) pfml.distinct(34) pfml.inject(7)
        pfml.simps(20,50,56,60,64) pos.cases)

  (* Rewrite the N-side env update into the “G (lift_set S)” shape. *)
  have IH_bridge:
    "\<lbrakk> (u,v)\<in>R; R_closed S \<rbrakk> \<Longrightarrow>
       (u \<in> F S) \<longleftrightarrow> (v \<in> G (lift_set S))"
    for u v S
    by (simp add: IH_upd F_def G_def lift_env_update)

  (* Every approximant on the M-side is R-closed (by IH on \<phi>). *)
  have appr_closed: "R_closed (appr F n)" for n 
  proof (induction n)
    case 0 show ?case by (simp add: R_closed_def)   (* {} is R-closed *)
  next
    case (Suc n)
    have "env_R_closed (\<rho>(X := appr F n))"
      using env_closed_upd Suc.IH .
    (* Use the body-preservation (Mu.IH) to transport membership across R,
       which gives R_closed of F (appr n) = appr (Suc n). *)
    show ?case
    proof (unfold R_closed_def, intro allI impI)
      fix u v assume "(u,v) \<in> R_src"
      then obtain w where uw: "(u,w)\<in>R" and vw: "(v,w)\<in>R"
        by (auto simp: R_src_def)
      have "(u \<in> F (appr F n)) \<longleftrightarrow> (w \<in> G (lift_set (appr F n)))"
        using IH_bridge[OF uw Suc.IH] .
      moreover have "(v \<in> F (appr F n)) \<longleftrightarrow> (w \<in> G (lift_set (appr F n)))"
        using IH_bridge[OF vw Suc.IH] .
      ultimately show "u \<in> appr F (Suc n) \<longleftrightarrow> v \<in> appr F (Suc n)"
        by simp   
    qed
  qed

(* Synchronization: approximants correspond pointwise along R. *) 
  have appr_sync: "(u,v) \<in> R \<Longrightarrow> (u \<in> appr F n \<longleftrightarrow> v \<in> appr' G n)" for u v n 
  proof (induction n arbitrary: u v) 
    case 0 
    then show ?case by simp 
  next 
    case (Suc n u v) 
    from Suc.prems have uv: "(u,v) \<in> R" . 
    have IHn: "(w,z)\<in>R \<Longrightarrow> (w \<in> appr F n \<longleftrightarrow> z \<in> appr' G n)" for w z 
      using Suc.IH by blast 
    have "u \<in> appr F (Suc n) \<longleftrightarrow> u \<in> F (appr F n)" 
      by simp also have "... \<longleftrightarrow> v \<in> G (appr' G n)" 
    proof - 
      have PRES_\<phi>: "u \<in> eval M (\<rho>(X := appr F n)) \<phi> \<longleftrightarrow> v \<in> eval N ((lift_env \<rho>)(X := appr' G n)) \<phi>" 
        sorry 
      then show ?thesis 
        unfolding F_def G_def by blast 
    qed 
    also have "... \<longleftrightarrow> v \<in> appr' G (Suc n)" 
      by simp 
    finally show ?case . 
  qed
  have appr_pre_fix: "F (\<Union>n. appr F n) \<subseteq> (\<Union>n. appr F n)" 
  proof 
    fix u assume "u \<in> F (\<Union>n. appr F n)" 
    then obtain n where "u \<in> F (appr F n)" 
      using mono_F sorry 
    thus "u \<in> (\<Union>n. appr F n)" 
      by (metis UNIV_I UN_I appr_Suc) 
  qed 
  have appr_le_lfp: "appr F n \<subseteq> lfp F" for n 
    apply (induction n) 
     apply simp 
    by (metis lfp_fixpoint mono_F monotoneD prod_bisim.appr_Suc prod_bisim_axioms) 
  have lfpF_eq: "lfp F = (\<Union>n. appr F n)" 
  proof (rule antisym) 
    show "lfp F \<subseteq> (\<Union>n. appr F n)" 
    proof (rule lfp_lowerbound) 
      show "F (\<Union>n. appr F n) \<subseteq> (\<Union>n. appr F n)" 
        by (rule appr_pre_fix) 
    qed 
    show "(\<Union>n. appr F n) \<subseteq> lfp F" 
      using appr_le_lfp by blast 
  qed 

  (* The same for G / appr' *) 
  have appr'_pre_fix: "G (\<Union>n. appr' G n) \<subseteq> (\<Union>n. appr' G n)" 
  proof fix v assume "v \<in> G (\<Union>n. appr' G n)" 
    then obtain n where "v \<in> G (appr' G n)" 
      using mono_G sorry 
    thus "v \<in> (\<Union>n. appr' G n)" 
      by (metis UNIV_I UN_iff appr'_Suc) 
  qed 
  have appr'_le_lfp: "appr' G n \<subseteq> lfp G" for n 
    apply (induction n) 
     apply simp 
    by (metis lfp_fixpoint mono_G monotoneD prod_bisim.appr'_Suc prod_bisim_axioms) 
  
  have lfpG_eq: "lfp G = (\<Union>n. appr' G n)" 
  proof (rule antisym) 
    show "lfp G \<subseteq> (\<Union>n. appr' G n)" 
      by (simp add: appr'_pre_fix lfp_lowerbound) 
    show "(\<Union>n. appr' G n) \<subseteq> lfp G" 
      using appr'_le_lfp by blast 
  qed

  have "s \<in> lfp F \<longleftrightarrow> t \<in> lfp G"
  proof -
    have "(s \<in> (\<Union>n. appr F n)) \<longleftrightarrow> (t \<in> (\<Union>n. appr' G n))"
      using appr_sync[OF Mu.prems(1)] by blast
    then show ?thesis by (simp add: lfpF_eq lfpG_eq)
  qed

  then show ?case
    unfolding F_def G_def by simp 
next
  case (Nu X \<phi>)
  then show ?case sorry
qed

text \<open>Main theorem: bisimulation invariance for closed formulas\<close>
theorem bisim_invariance_closed:
  assumes "(s,t)\<in>R" 
  shows "(s \<in> eval M (\<lambda>_. {}) \<phi>) = (t \<in> eval N (\<lambda>_. {}) \<phi>)"
  using preservation[OF assms, of "\<lambda>_. {}" \<phi>] 

end  (* locale prod_bisim *)

end
