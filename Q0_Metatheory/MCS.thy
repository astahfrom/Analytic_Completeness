theory MCS imports
  "../Analytic_Completeness"
  Consistency
begin

section \<open>Consistency Property\<close>

inductive confl_class :: \<open>form list \<Rightarrow> form list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<crossmark>\<close> 50) where
  CFalse: \<open>[ F\<^bsub>o\<^esub> ] \<leadsto>\<^sub>\<crossmark> [ F\<^bsub>o\<^esub> ]\<close>
| CVar: \<open>[ \<sim>\<^sup>\<Q> x\<^bsub>i\<^esub> ] \<leadsto>\<^sub>\<crossmark> [ x\<^bsub>i\<^esub> ]\<close> (* should these be individuals or any type? *)
| CCon: \<open>\<not> is_logical_constant (c, i) \<Longrightarrow> [ \<sim>\<^sup>\<Q> \<lbrace>c\<rbrace>\<^bsub>i\<^esub> ] \<leadsto>\<^sub>\<crossmark> [ \<lbrace>c\<rbrace>\<^bsub>i\<^esub> ]\<close>


inductive alpha_class :: \<open>form list \<Rightarrow> form list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<alpha>\<close> 50) where
(*
  CEta: \<open>[ A ] \<leadsto>\<^sub>\<alpha> [ \<eta> A]\<close> (* normal form ? *)
|*)
  CConP: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> [ A \<and>\<^sup>\<Q> B ] \<leadsto>\<^sub>\<alpha> [ A, B ]\<close>
| CImpN: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> [ \<sim>\<^sup>\<Q> (A \<supset>\<^sup>\<Q> B) ] \<leadsto>\<^sub>\<alpha> [ A, \<sim>\<^sup>\<Q> B ]\<close>

inductive beta_class :: \<open>form list \<Rightarrow> form list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<beta>\<close> 50) where
  CConN: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> [ \<sim>\<^sup>\<Q> (A \<and>\<^sup>\<Q> B) ] \<leadsto>\<^sub>\<beta> [ \<sim>\<^sup>\<Q> A, \<sim>\<^sup>\<Q> B ]\<close>
| CImpP: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> [ A \<supset>\<^sup>\<Q> B ] \<leadsto>\<^sub>\<beta> [ \<sim>\<^sup>\<Q> A, B ]\<close>

inductive gamma_class :: \<open>form list \<Rightarrow> (form set \<Rightarrow> _) \<times> (form \<Rightarrow> _) \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<gamma>\<close> 50) where
  CPiP: \<open>A \<in> wffs\<^bsub>\<alpha> \<rightarrow> o\<^esub> \<Longrightarrow> [ \<Prod>\<^bsub>\<alpha>\<^esub> \<sqdot> A ] \<leadsto>\<^sub>\<gamma> (\<lambda>_. wffs\<^bsub>\<alpha>\<^esub>, \<lambda>B. [ \<Prod>\<^bsub>\<alpha>\<^esub> \<sqdot> A \<sqdot> A, B ])\<close>

(* TODO: I have no idea about this one *)
fun \<delta> :: \<open>form \<Rightarrow> nat \<Rightarrow> form list\<close> where
  CDelta: \<open>\<delta> A c = (
    if \<exists>\<alpha> B. A = (\<Prod>\<^bsub>\<alpha>\<^esub> \<sqdot> B) then
      let (\<alpha>, B) = (SOME (\<alpha>, B). A = (\<Prod>\<^bsub>\<alpha>\<^esub> \<sqdot> B)) in
        [ \<sim>\<^sup>\<Q> (B \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<alpha> \<rightarrow> o\<^esub>) ]
    else [])\<close>


section \<open>Operations\<close>

fun map_con :: "(con \<Rightarrow> con) \<Rightarrow> form \<Rightarrow> form" where
  "map_con _ (x\<^bsub>\<alpha>\<^esub>) = (x\<^bsub>\<alpha>\<^esub>)"
| "map_con f (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) =
    (if is_logical_constant (c, \<alpha>)
    then \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>
    else FCon (f (c, \<alpha>)))"
| "map_con f (A \<sqdot> B) = map_con f A \<sqdot> map_con f B"
| "map_con f (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) = \<lambda>x\<^bsub>\<alpha>\<^esub>. map_con f A"

fun cons_form :: "form \<Rightarrow> con set" where
  "cons_form (x\<^bsub>\<alpha>\<^esub>) = {}"
| "cons_form (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) = (if is_logical_constant (c, \<alpha>)
    then {}
    else {(c, \<alpha>)})"
| "cons_form (A \<sqdot> B) = cons_form A \<union> cons_form B"
| "cons_form (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) = cons_form A"


section \<open>Lemmas\<close>

lemma map_con_id [simp]: \<open>map_con id = id\<close>
proof
  fix A
  show \<open>map_con id A = id A\<close>
    by (induct A) auto
qed

lemma map_con_cong [simp]:
  assumes \<open>\<forall>x \<in> cons_form A. f x = g x\<close>
  shows \<open>map_con f A = map_con g A\<close>
  using assms by (induct A) auto

lemma finite_cons_form [simp]: \<open>finite (cons_form A)\<close>
  by (induct A) auto

section \<open>Parameter Substitutions\<close>

locale Param_Subst =
  fixes f :: \<open>con \<Rightarrow> con\<close>
  assumes \<open>\<And>n. is_logical_constant n \<Longrightarrow> f n = n\<close>

section \<open>Interpretations\<close>

interpretation P: Params map_con cons_form
  by unfold_locales simp_all

lemma map_con_non_logical_constant:
  assumes \<open>\<not> is_logical_constant (c, \<alpha>)\<close>
  shows \<open>map_con f (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) = FCon (f (c, \<alpha>))\<close>
  using assms by auto

lemma map_con_neg [simp]: \<open>map_con f (\<sim>\<^sup>\<Q> A) =  \<sim>\<^sup>\<Q> (map_con f A)\<close>
  by (induct A) auto

interpretation C: Confl map_con cons_form confl_class
proof unfold_locales
  fix ps qs f
  assume *: \<open>ps \<leadsto>\<^sub>\<crossmark> qs\<close>
  then show \<open>map (map_con f) ps \<leadsto>\<^sub>\<crossmark> map (map_con f) qs\<close>
  proof (cases ps qs rule: confl_class.cases)
    case CFalse
    then show ?thesis
      using confl_class.CFalse by simp
  next
    case CVar
    then show ?thesis
      using confl_class.CVar by simp
  next
    case (CCon c)
    then show ?thesis
      apply (simp del: neg_def)
      using confl_class.CCon
      unfolding map_con_non_logical_constant[OF CCon(3)]
      sorry

(*
lemma wff_cst_trm [iff]: \<open>wff_cst \<alpha> (map_cst f cst) = wff_cst \<alpha> cst\<close>
  by (induct cst) simp_all

lemma wff_map_con [iff]: \<open>wff \<alpha> (map_con f A) = wff \<alpha> A\<close>
  by (induct A arbitrary: \<alpha>) simp_all

lemma finite_cst_syms [simp]: \<open>finite (cst_syms cst)\<close>
  by (induct cst) simp_all

lemma finite_cons_form [simp]: \<open>finite (cons_form A)\<close>
  by (induct A) simp_all



interpretation A: Alpha map_con cons_form alpha_class
  by unfold_locales (auto elim!: alpha_class.cases simp: alpha_class.simps
      Con_def Con_sym_def Eql_def Imp_def Imp_sym_def T_def)

interpretation B: Beta map_con cons_form beta_class
  by unfold_locales (auto elim!: beta_class.cases simp: beta_class.simps
      Con_def Con_sym_def Eql_def Imp_def Imp_sym_def T_def)

interpretation G: Gamma map_con map_con cons_form gamma_class
  by unfold_locales (auto elim!: gamma_class.cases simp: gamma_class.simps
      Con_def Con_sym_def Eql_def Imp_def Imp_sym_def T_def PI_def)

interpretation D: Delta map_con cons_form \<delta>
proof
  show \<open>\<And>f. \<delta> (map_con f p) (f x) = map (map_con f) (\<delta> p x)\<close> for p :: \<open>form\<close> and x
  proof (induct p x rule: \<delta>.induct)
    case (1 A c)
    then show ?case
      by (auto simp: T_def Eql_def Imp_def Imp_sym_def Con_def Con_sym_def)
  qed
qed

abbreviation Kinds :: \<open>('c, form) kind list\<close> where
  \<open>Kinds \<equiv> [C.kind, A.kind, B.kind, G.kind, D.kind]\<close>

lemma prop\<^sub>E_Kinds:
  assumes \<open>sat\<^sub>E C.kind C\<close> \<open>sat\<^sub>E A.kind C\<close> \<open>sat\<^sub>E B.kind C\<close> \<open>sat\<^sub>E G.kind C\<close> \<open>sat\<^sub>E D.kind C\<close>
  shows \<open>prop\<^sub>E Kinds C\<close>
  unfolding prop\<^sub>E_def using assms by simp

interpretation Consistency_Kinds map_con cons_form Kinds
  using P.Params_axioms C.Consistency_Kind_axioms A.Consistency_Kind_axioms B.Consistency_Kind_axioms
    G.Consistency_Kind_axioms D.Consistency_Kind_axioms
  by (auto intro: Consistency_Kinds.intro simp: Consistency_Kinds_axioms_def)

interpretation Maximal_Consistency map_con cons_form Kinds
proof
 have \<open>infinite (UNIV :: form set)\<close>
   using infinite_UNIV_size[of \<open>\<lambda>A. A \<^bold>\<cdot> A\<close>] by simp
  then show \<open>infinite (UNIV :: form set)\<close>
    using finite_prod by blast
qed simp
*)

end