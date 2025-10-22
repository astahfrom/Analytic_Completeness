theory Q0_Completeness imports
  Analytic_Completeness
  "Q0_2"
begin

abbreviation Neg :: \<open>'c trm \<Rightarrow> 'c trm\<close> (\<open>\<^bold>\<sim> _\<close> [70] 70) where
 \<open>\<^bold>\<sim> A \<equiv> A \<^bold>\<longrightarrow> F\<close>

inductive confl_class :: \<open>'c trm list \<Rightarrow> 'c trm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<crossmark>\<close> 50) where
  CF: \<open>[ F ] \<leadsto>\<^sub>\<crossmark> [ F ]\<close>
| CVar: \<open>[ \<^bold>\<sim> (Var x Ind) ] \<leadsto>\<^sub>\<crossmark> [ Var x Ind ]\<close>
| CCst: \<open>[ \<^bold>\<sim> (Cst x Ind) ] \<leadsto>\<^sub>\<crossmark> [ Cst x Ind ]\<close>

inductive alpha_class :: \<open>'c trm list \<Rightarrow> 'c trm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<alpha>\<close> 50) where
(*
  CEta: \<open>[ A ] \<leadsto>\<^sub>\<alpha> [ \<eta> A]\<close> (* normal form ? *)
|*)
  CConP: \<open>wff Tv A \<Longrightarrow> wff Tv B \<Longrightarrow> [ A \<^bold>\<and> B ] \<leadsto>\<^sub>\<alpha> [ A, B ]\<close>
| CImpN: \<open>wff Tv A \<Longrightarrow> wff Tv B \<Longrightarrow> [ \<^bold>\<sim> (A \<^bold>\<longrightarrow> B) ] \<leadsto>\<^sub>\<alpha> [ A, \<^bold>\<sim> B ]\<close>

inductive beta_class :: \<open>'c trm list \<Rightarrow> 'c trm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<beta>\<close> 50) where
  CConN: \<open>wff Tv A \<Longrightarrow> wff Tv B \<Longrightarrow> [ \<^bold>\<sim> (A \<^bold>\<and> B) ] \<leadsto>\<^sub>\<beta> [ \<^bold>\<sim> A, \<^bold>\<sim> B ]\<close>
| CImpP: \<open>wff Tv A \<Longrightarrow> wff Tv B \<Longrightarrow> [ A \<^bold>\<longrightarrow> B ] \<leadsto>\<^sub>\<beta> [ \<^bold>\<sim> A, B ]\<close>

inductive gamma_class :: \<open>'c trm list \<Rightarrow> ('c trm set \<Rightarrow> _) \<times> ('c trm \<Rightarrow> _) \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<gamma>\<close> 50) where
  CPiP: \<open>wff (Tv \<^bold>\<Leftarrow> \<alpha>) A \<Longrightarrow> [ PI \<alpha> \<^bold>\<cdot> A ] \<leadsto>\<^sub>\<gamma> (\<lambda>_. {B. wff \<alpha> B}, \<lambda>B. [ PI \<alpha> \<^bold>\<cdot> A \<^bold>\<cdot> A, B ])\<close>

(* TODO: could narrow to negation of PI if needed for soundness *)
(* TODO: actually just consider negation of equality instead of PI? *)
fun \<delta> :: \<open>'c trm \<Rightarrow> 'c \<Rightarrow> 'c trm list\<close> where
  CDelta: \<open>\<delta> A c = (
  if \<exists>\<alpha>. wff (Tv \<^bold>\<Leftarrow> \<alpha>) A
  then [ \<^bold>\<sim> (A \<^bold>\<cdot> Cst (Par c (SOME \<alpha>. wff (Tv \<^bold>\<Leftarrow> \<alpha>) A)) (SOME \<alpha>. wff (Tv \<^bold>\<Leftarrow> \<alpha>) A)) ]
  else [])\<close>

lemma wff_cst_trm [iff]: \<open>wff_cst \<alpha> (map_cst f cst) = wff_cst \<alpha> cst\<close>
  by (induct cst) simp_all

lemma wff_map_trm [iff]: \<open>wff \<alpha> (map_trm f A) = wff \<alpha> A\<close>
  by (induct A arbitrary: \<alpha>) simp_all

lemma finite_cst_syms [simp]: \<open>finite (cst_syms cst)\<close>
  by (induct cst) simp_all

lemma finite_trm_csts [simp]: \<open>finite (trm_csts A)\<close>
  by (induct A) simp_all

interpretation P: Params map_trm trm_csts
  by unfold_locales (simp_all add: trm.map_id0 cong: trm.map_cong)

interpretation C: Confl map_trm trm_csts confl_class
  by unfold_locales (auto elim!: confl_class.cases simp: confl_class.simps
      simp: Con_def Con_sym_def Eql_def Imp_def Imp_sym_def T_def)

interpretation A: Alpha map_trm trm_csts alpha_class
  by unfold_locales (auto elim!: alpha_class.cases simp: alpha_class.simps
      Con_def Con_sym_def Eql_def Imp_def Imp_sym_def T_def)

interpretation B: Beta map_trm trm_csts beta_class
  by unfold_locales (auto elim!: beta_class.cases simp: beta_class.simps
      Con_def Con_sym_def Eql_def Imp_def Imp_sym_def T_def)

interpretation G: Gamma map_trm map_trm trm_csts gamma_class
  by unfold_locales (auto elim!: gamma_class.cases simp: gamma_class.simps
      Con_def Con_sym_def Eql_def Imp_def Imp_sym_def T_def PI_def)

interpretation D: Delta map_trm trm_csts \<delta>
proof
  show \<open>\<And>f. \<delta> (map_trm f p) (f x) = map (map_trm f) (\<delta> p x)\<close> for p :: \<open>'c trm\<close> and x
  proof (induct p x rule: \<delta>.induct)
    case (1 A c)
    then show ?case
      by (auto simp: T_def Eql_def Imp_def Imp_sym_def Con_def Con_sym_def)
  qed
qed

abbreviation Kinds :: \<open>('c, 'c trm) kind list\<close> where
  \<open>Kinds \<equiv> [C.kind, A.kind, B.kind, G.kind, D.kind]\<close>

lemma prop\<^sub>E_Kinds:
  assumes \<open>sat\<^sub>E C.kind C\<close> \<open>sat\<^sub>E A.kind C\<close> \<open>sat\<^sub>E B.kind C\<close> \<open>sat\<^sub>E G.kind C\<close> \<open>sat\<^sub>E D.kind C\<close>
  shows \<open>prop\<^sub>E Kinds C\<close>
  unfolding prop\<^sub>E_def using assms by simp

interpretation Consistency_Kinds map_trm trm_csts Kinds
  using P.Params_axioms C.Consistency_Kind_axioms A.Consistency_Kind_axioms B.Consistency_Kind_axioms
    G.Consistency_Kind_axioms D.Consistency_Kind_axioms
  by (auto intro: Consistency_Kinds.intro simp: Consistency_Kinds_axioms_def)

interpretation Maximal_Consistency map_trm trm_csts Kinds
proof
 have \<open>infinite (UNIV :: 'c trm set)\<close>
   using infinite_UNIV_size[of \<open>\<lambda>A. A \<^bold>\<cdot> A\<close>] by simp
  then show \<open>infinite (UNIV :: 'c trm set)\<close>
    using finite_prod by blast
qed simp

section \<open>Model\<close>

text \<open>
  Equivalence classes of equal wffs as domain.
\<close>

context set_theory
begin

primrec my_denot :: \<open>('c trm, 'c trm set) denotation\<close> where
  \<open>my_denot (Q \<alpha>) \<beta> = undefined\<close>
| \<open>my_denot Iota \<beta> = undefined\<close>
| \<open>my_denot (Par A \<alpha>) \<beta> = undefined\<close>

(* Have to do stuff with set_theory, I think? *)

primrec my_frame :: \<open>'c trm set \<Rightarrow> 'c trm set set frame\<close> where
  \<open>my_frame H Ind = { my_denot undefined Ind | A :: 'c trm. wff Ind A }\<close>
| \<open>my_frame H Tv = {T, F}\<close>
| \<open>my_frame H (\<beta> \<^bold>\<Leftarrow> \<alpha>) = undefined\<close>

end

end