theory HyperLTL_Bisim_Counterexample
  imports Main
begin

section \<open>Kripke structures and paths\<close>

record ('s) kripke =
  Init :: "'s set"              (* initial states *)
  step :: "'s \<Rightarrow> 's set"     (* transition relation as successor set *)
  lab  :: "'s \<Rightarrow> bool"      (* we use a single AP: a; True = a holds *)

(* Paths are infinite sequences consistent with step *)
type_synonym 's path = "nat \<Rightarrow> 's"

definition path_in :: "('s) kripke \<Rightarrow> 's path \<Rightarrow> bool" where
  "path_in M \<pi> \<longleftrightarrow> (\<pi> 0 \<in> Init M) \<and> (\<forall>i. \<pi> (Suc i) \<in> step M (\<pi> i))"

abbreviation a_at :: "('s) kripke \<Rightarrow> 's path \<Rightarrow> nat \<Rightarrow> bool" where
  "a_at M \<pi> i \<equiv> lab M (\<pi> i)"

section \<open>HyperLTL fragment we need\<close>

(* Our target sentence: \<forall>\<pi>1. \<exists>\<pi>2. G( a_\<pi>1 -> X a_\<pi>2 ) *)

definition phi :: "('s) kripke \<Rightarrow> bool" where
  "phi M \<equiv> \<forall>pi1. path_in M pi1 
          \<longrightarrow> (\<exists>pi2. path_in M pi2 \<and> (\<forall>i. a_at M pi1 i \<longrightarrow> a_at M pi2 (Suc i)))"

section \<open>Bisimulation\<close>

(* Standard state bisimulation between two Kripke structures with the same AP vocabulary *)

definition bisim :: "('s) kripke \<Rightarrow> ('t) kripke \<Rightarrow> ('s \<times> 't) set \<Rightarrow> bool" where
  "bisim M N R \<longleftrightarrow>
     (\<forall>(s,t)\<in>R. lab M s = lab N t) \<and>
     (\<forall>(s,t)\<in>R. (\<forall>s'. s' \<in> step M s \<longrightarrow> (\<exists>t'. t' \<in> step N t \<and> (s',t') \<in> R))) \<and>
     (\<forall>(s,t)\<in>R. (\<forall>t'. t' \<in> step N t \<longrightarrow> (\<exists>s'. s' \<in> step M s \<and> (s',t') \<in> R)))"

(* Rooted bisimilarity of initial states *)

definition rooted_bisim :: "('s) kripke \<Rightarrow> ('t) kripke \<Rightarrow> bool" where
  "rooted_bisim M N \<longleftrightarrow> (\<exists>R. bisim M N R \<and> (\<forall>s\<in>Init M. \<exists>t\<in>Init N. (s,t)\<in>R) \<and> (\<forall>t\<in>Init N. \<exists>s\<in>Init M. (s,t)\<in>R))"

section \<open>A concrete pair of systems A and B\<close>

subsection \<open>System A: a single infinite chain with even positions labelled a\<close>

datatype Astate = A (idx: nat)

definition AA :: "Astate kripke" where
  "AA = \<lparr>
      Init = {A 0},
      step = (\<lambda>s. {A (Suc (idx s))}),
      lab  = (\<lambda>s. even (idx s))
    \<rparr>"

subsection \<open>System B: two bisimilar copies of A glued at the root\<close>

datatype branch = L | R

datatype Bstate = B0 | B branch nat

fun idxB :: "Bstate \<Rightarrow> nat" where
  "idxB B0 = 0" |
  "idxB (B _ k) = Suc k"

(* successors: from root to the 0th of each branch, then linear inside a branch *)
definition BB :: "Bstate kripke" where
  "BB = \<lparr>
      Init = {B0},
      step = (\<lambda>s. case s of
                        B0 \<Rightarrow> {B L 0, B R 0} |
                        B b k \<Rightarrow> {B b (Suc k)}),
      lab  = (\<lambda>s. even (idxB s))
    \<rparr>"

lemma A_depth_labels: "lab AA (A n) = even n" by (simp add: AA_def)
lemma B_depth_labels: "lab BB s = even (idxB s)" by (cases s) (simp_all add: BB_def)

(* A standard bisimulation relating depth i in A to all B-states at depth i *)
definition R where
  "R = {(A i, t) | i t. idxB t = i}"

lemma bisim_AB: "bisim AA BB R" 
  apply (unfold bisim_def R_def AA_def BB_def, safe)
  apply auto
  apply (smt (verit, best) Bstate.simps(4) Bstate.simps(5) idxB.elims idxB.simps(2) insertCI)
  apply (smt (verit) Bstate.simps(4) Bstate.simps(5) idxB.elims idxB.simps(1) idxB.simps(2) insertE insert_absorb insert_not_empty)
  done

lemma rooted_bisim_AB: "rooted_bisim AA BB"
  unfolding rooted_bisim_def using bisim_AB by (auto simp: R_def AA_def BB_def)

section \<open>Evaluating the HyperLTL sentence on A and B\<close>

(* Convenient paths by depth *)

definition A_path :: "nat \<Rightarrow> Astate path" where
  "A_path i = (\<lambda>k. A (i + k))"

lemma A_path_ok: "path_in AA (A_path 0)"
  unfolding path_in_def A_path_def AA_def by auto

(* In B we pick a branch-specific path *)

definition B_path :: "branch \<Rightarrow> nat \<Rightarrow> Bstate path" where
  "B_path b i = (\<lambda>k. case k of 0 \<Rightarrow> B0 | Suc k' \<Rightarrow> B b (i + k'))"

lemma B_path_ok: "path_in BB (B_path b 0)"
  unfolding path_in_def B_path_def BB_def
  apply (auto split:nat.splits)
  using branch.exhaust by blast

(* Show phi is FALSE in A for our even/odd labelling *)
lemma AA_next_not_a:
  assumes P: "path_in AA pi"
  shows "\<not> a_at AA pi (Suc 0)"
proof -
  from P have init: "pi 0 \<in> Init AA" and step: "\<forall>i. pi (Suc i) \<in> step AA (pi i)"
    unfolding path_in_def by auto
  from init have "pi 0 = A 0" unfolding AA_def by auto
  from step[rule_format, of 0] this have "pi (Suc 0) \<in> step AA (A 0)" by auto
  hence "pi (Suc 0) = A (Suc 0)" unfolding AA_def by auto
  hence "lab AA (pi (Suc 0)) = even (Suc 0)" unfolding AA_def by simp
  thus ?thesis by simp
qed

lemma phi_A_False: "\<not> phi AA"
proof -
  have p: "path_in AA (A_path 0)" by (rule A_path_ok)
  have "\<not>(\<exists>pi2. path_in AA pi2 \<and> (\<forall>i. a_at AA (A_path 0) i \<longrightarrow> a_at AA pi2 (Suc i)))"
  proof
    assume ex: "(\<exists>pi2. path_in AA pi2 \<and> (\<forall>i. a_at AA (A_path 0) i \<longrightarrow> a_at AA pi2 (Suc i)))"
    then obtain pi2 where q: "path_in AA pi2"
      and shift: "\<forall>i. even i \<longrightarrow> lab AA (pi2 (Suc i))"
      unfolding A_path_def
        using A_depth_labels by auto 
    from AA_next_not_a[OF q] have "\<not> a_at AA pi2 (Suc 0)" .
    with shift[rule_format, of 0] show False by simp
  qed
  thus ?thesis unfolding phi_def using p by blast
qed

(* For B as currently defined, all depth-k labels match A, so phi also fails. *)
lemma BB_next_not_a:
  assumes P: "path_in BB pi"
  shows "\<not> a_at BB pi (Suc 0)"
proof -
  from P have init: "pi 0 \<in> Init BB"
    and step: "\<forall>i. pi (Suc i) \<in> step BB (pi i)"
    unfolding path_in_def by auto
  hence root: "pi 0 = B0"
    unfolding BB_def by auto

  from step[rule_format, of 0] root have "pi (Suc 0) \<in> step BB B0" by auto
  then have "idxB (pi (Suc 0)) = Suc 0"
    by (metis BB_def Bstate.simps(4) empty_iff idxB.simps(2) insert_iff select_convs(2)) 
  hence "lab BB (pi (Suc 0)) = even (Suc 0)"
    unfolding BB_def by simp
  thus "\<not> a_at BB pi (Suc 0)" by simp
qed

lemma phi_BB_False: "\<not> phi BB"
proof -
  have p: "path_in BB (B_path L 0)" by (rule B_path_ok) 
  (* At i=0, (B_path L 0) has a; but any path has \<not>a at time 1. *)
  have no_witness:
    "\<not> (\<exists>pi2. path_in BB pi2 \<and> (\<forall>i. a_at BB (B_path L 0) i \<longrightarrow> a_at BB pi2 (Suc i)))"
  proof
    assume ex: "\<exists>pi2. path_in BB pi2 \<and> (\<forall>i. a_at BB (B_path L 0) i \<longrightarrow> a_at BB pi2 (Suc i))"
    then obtain pi2 where pi2P: "path_in BB pi2"
      and shift: "\<forall>i. a_at BB (B_path L 0) i \<longrightarrow> a_at BB pi2 (Suc i)" by blast
    have a0: "a_at BB (B_path L 0) 0"
      by (simp add: BB_def B_path_def)  (* root is labelled a *)
    from BB_next_not_a[OF pi2P] have "\<not> a_at BB pi2 (Suc 0)" .
    with shift[rule_format, of 0] a0 show False by blast
  qed
  thus ?thesis
    unfolding phi_def using p by blast
qed

end
