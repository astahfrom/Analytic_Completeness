theory MCS imports
  "../Analytic_Completeness"
  Consistency
begin

section \<open>Consistency Property\<close>

inductive confl_class :: \<open>form list \<Rightarrow> form list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<crossmark>\<close> 50) where
  CFalse: \<open>[ F\<^bsub>o\<^esub> ] \<leadsto>\<^sub>\<crossmark> [ F\<^bsub>o\<^esub> ]\<close>
| CVar: \<open>[ \<sim>\<^sup>\<Q> x\<^bsub>o\<^esub> ] \<leadsto>\<^sub>\<crossmark> [ x\<^bsub>o\<^esub> ]\<close>
| CCon: \<open>[ \<sim>\<^sup>\<Q> \<lbrace>c\<rbrace>\<^bsub>o\<^esub> ] \<leadsto>\<^sub>\<crossmark> [ \<lbrace>c\<rbrace>\<^bsub>o\<^esub> ]\<close>


inductive alpha_class :: \<open>form list \<Rightarrow> form list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<alpha>\<close> 50) where
(*
  CEta: \<open>[ A \<in> wffs\<^bsub>\<alpha>\<^esub> \<Longrightarrow> A ] \<leadsto>\<^sub>\<alpha> [ \<eta> A]\<close> (* normal form ? *)
|*)
  CConP: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> [ A \<and>\<^sup>\<Q> B ] \<leadsto>\<^sub>\<alpha> [ A, B ]\<close>
| CImpN: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> [ \<sim>\<^sup>\<Q> (A \<supset>\<^sup>\<Q> B) ] \<leadsto>\<^sub>\<alpha> [ A, \<sim>\<^sup>\<Q> B ]\<close>

inductive beta_class :: \<open>form list \<Rightarrow> form list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<beta>\<close> 50) where
  CConN: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> [ \<sim>\<^sup>\<Q> (A \<and>\<^sup>\<Q> B) ] \<leadsto>\<^sub>\<beta> [ \<sim>\<^sup>\<Q> A, \<sim>\<^sup>\<Q> B ]\<close>
| CImpP: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> [ A \<supset>\<^sup>\<Q> B ] \<leadsto>\<^sub>\<beta> [ \<sim>\<^sup>\<Q> A, B ]\<close>

inductive gamma_class :: \<open>form list \<Rightarrow> (form set \<Rightarrow> _) \<times> (form \<Rightarrow> _) \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<gamma>\<close> 50) where
  CPiP: \<open>A \<in> wffs\<^bsub>\<alpha> \<rightarrow> o\<^esub> \<Longrightarrow> [ \<forall>x\<^bsub>\<alpha>\<^esub>. A ] \<leadsto>\<^sub>\<gamma> (\<lambda>_. wffs\<^bsub>\<alpha>\<^esub>, \<lambda>B. [ A \<sqdot> B ])\<close>

inductive delta_match :: \<open>form \<Rightarrow> type \<times> form \<Rightarrow> bool\<close> where
  \<open>delta_match (\<sim>\<^sup>\<Q> (\<forall>x\<^bsub>\<alpha>\<^esub>. A)) (\<alpha>, A)\<close>

inductive_cases delta_matchE: \<open>delta_match (\<sim>\<^sup>\<Q> (\<forall>x\<^bsub>\<alpha>\<^esub>. A)) (\<alpha>', A')\<close>

lemma delta_match_uniq: \<open>delta_match A (\<alpha>, B) \<Longrightarrow> delta_match A (\<alpha>', B') \<Longrightarrow> \<alpha> = \<alpha>' \<and> B = B'\<close>
  by (auto elim!: delta_match.cases)

lemma delta_match_THE: \<open>delta_match A (\<alpha>, B) \<Longrightarrow> delta_match A (THE (\<alpha>, B). delta_match A (\<alpha>, B))\<close>
  using delta_match_uniq theI by fastforce

fun \<delta> :: \<open>form \<Rightarrow> nat \<Rightarrow> form list\<close> where
  CDelta: \<open>\<delta> A c =
    (if \<exists>\<alpha> B. delta_match A (\<alpha>, B) then 
       case THE (\<alpha>, B). delta_match A (\<alpha>, B) of
         (\<alpha>, B) \<Rightarrow> [ \<sim>\<^sup>\<Q> (B \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) ]
    else [])\<close>


section \<open>Operations\<close>

abbreviation \<open>is_logical_name c \<equiv> c = \<cc>\<^sub>Q \<or> c = \<cc>\<^sub>\<iota>\<close>

abbreviation \<open>is_param c \<equiv> \<not> is_logical_name c\<close>

fun map_con :: "(nat \<Rightarrow> nat) \<Rightarrow> form \<Rightarrow> form" where
  "map_con _ (x\<^bsub>\<alpha>\<^esub>) = (x\<^bsub>\<alpha>\<^esub>)"
| "map_con f (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) = (if is_logical_name c then \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub> else \<lbrace>f c\<rbrace>\<^bsub>\<alpha>\<^esub>)"
| "map_con f (A \<sqdot> B) = map_con f A \<sqdot> map_con f B"
| "map_con f (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) = \<lambda>x\<^bsub>\<alpha>\<^esub>. map_con f A"

fun cons_form :: "form \<Rightarrow> nat set" where
  "cons_form (x\<^bsub>\<alpha>\<^esub>) = {}"
| "cons_form (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) = (if is_logical_name c then {} else {c})"
| "cons_form (A \<sqdot> B) = cons_form A \<union> cons_form B"
| "cons_form (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) = cons_form A"

section \<open>Lemmas\<close>

(* This property is really what dodging the logical constants is all about. *)
proposition \<open>map_con f (\<sim>\<^sup>\<Q> A) = \<sim>\<^sup>\<Q> (map_con f A)\<close>
  by simp

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

lemma wff_map_con [iff]: \<open>A \<in> wffs\<^bsub>\<alpha>\<^esub> \<Longrightarrow> map_con f A \<in> wffs\<^bsub>\<alpha>\<^esub>\<close>
proof (induct A arbitrary: \<alpha>)
  case (FVar x)
  then show ?case
    by (metis map_con.simps(1) surj_pair)
next
  case (FCon x)
  then show ?case
    apply (induct x rule: prod_cases)
    using wff_has_unique_type by auto
next
  case (FApp A B)
  then show ?case
    by (metis map_con.simps(3) wffs_from_app wffs_of_type_intros(3))
next
  case (FAbs x1a A)
  then show ?case
    by (metis form.distinct(11,5,9) form.inject(4) map_con.simps(4) wffs_of_type_cases wffs_of_type_intros(4))
qed

lemma finite_cons_form [simp]: \<open>finite (cons_form A)\<close>
  by (induct A) auto

lemma map_con_delta_match [intro]: \<open>delta_match A (\<alpha>, B) \<Longrightarrow> delta_match (map_con f A) (\<alpha>, map_con f B)\<close>
  by (auto elim: delta_match.cases simp: delta_match.simps)

lemma delta_match [dest]: \<open>delta_match A (\<alpha>, B) \<Longrightarrow> \<exists>x. A = \<sim>\<^sup>\<Q> (\<forall>x\<^bsub>\<alpha>\<^esub>. B)\<close>
  by (auto elim: delta_match.cases)

section \<open>Interpretations\<close>

interpretation P: Params map_con cons_form is_param
  by unfold_locales simp_all

interpretation C: Confl map_con cons_form is_param confl_class
  by unfold_locales (fastforce elim!: confl_class.cases simp: confl_class.simps)

interpretation A: Alpha map_con cons_form is_param alpha_class
  by unfold_locales (auto elim!: alpha_class.cases simp: alpha_class.simps)

interpretation B: Beta map_con cons_form is_param beta_class
  by unfold_locales (auto elim!: beta_class.cases simp: beta_class.simps)

interpretation G: Gamma map_con map_con cons_form is_param gamma_class
  by unfold_locales (auto elim!: gamma_class.cases simp: gamma_class.simps)

interpretation D: Delta map_con cons_form is_param \<delta>
proof
  fix p x
  assume x: \<open>is_param x\<close>
  then show \<open>\<And>f. \<delta> (map_con f p) (f x) = map (map_con f) (\<delta> p x)\<close>
  proof (induct p x rule: \<delta>.induct)
    case (1 A c)
    then show ?case
    proof (cases \<open>\<exists>\<alpha> B. delta_match A (\<alpha>, B)\<close>)
      case True
      then obtain \<alpha> B y where A: \<open>A = \<sim>\<^sup>\<Q> (\<forall>y\<^bsub>\<alpha>\<^esub>. B)\<close>
        by (auto elim: delta_match.cases)
      then have *: \<open>\<delta> A c = [ \<sim>\<^sup>\<Q> (B \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) ]\<close>
        by (metis (no_types, lifting) MCS.CDelta case_prod_conv delta_match.intros delta_match_THE delta_match_uniq surj_pair)
      then have \<open>map (map_con f) (\<delta> A c) = [ \<sim>\<^sup>\<Q> (map_con f B \<sqdot> \<lbrace>f c\<rbrace>\<^bsub>\<alpha>\<^esub>) ]\<close>
        using 1 by simp
      moreover have \<open>\<delta> (map_con f A) (f c) = [ \<sim>\<^sup>\<Q> (map_con f B \<sqdot> \<lbrace>f c\<rbrace>\<^bsub>\<alpha>\<^esub>) ]\<close>
        using * A MCS.CDelta
        by (smt (verit, ccfv_SIG) case_prod_conv delta_match.cases delta_match.intros delta_match_THE delta_match_uniq map_con_delta_match)
      ultimately show ?thesis
        by simp
    next
      case False
        (* TODO: need to prove some structural property about parameter substitution *)
      then have \<open>\<nexists>\<alpha> B. delta_match (map_con f A) (\<alpha>, B)\<close>
        sorry
      then show ?thesis
        using False by simp
    qed
  qed
qed

abbreviation Kinds :: \<open>(nat, form) kind list\<close> where
  \<open>Kinds \<equiv> [C.kind, A.kind, B.kind, G.kind, D.kind]\<close>

lemma prop\<^sub>E_Kinds:
  assumes \<open>sat\<^sub>E C.kind C\<close> \<open>sat\<^sub>E A.kind C\<close> \<open>sat\<^sub>E B.kind C\<close> \<open>sat\<^sub>E G.kind C\<close> \<open>sat\<^sub>E D.kind C\<close>
  shows \<open>prop\<^sub>E Kinds C\<close>
  unfolding prop\<^sub>E_def using assms by simp

interpretation Consistency_Kinds map_con cons_form is_param Kinds
  using P.Params_axioms C.Consistency_Kind_axioms A.Consistency_Kind_axioms B.Consistency_Kind_axioms
    G.Consistency_Kind_axioms D.Consistency_Kind_axioms
  by (auto intro: Consistency_Kinds.intro simp: Consistency_Kinds_axioms_def)

interpretation Maximal_Consistency map_con cons_form is_param Kinds
proof
 have \<open>infinite (UNIV :: form set)\<close>
   using infinite_UNIV_size[of \<open>\<lambda>A. A \<sqdot> A\<close>] by simp
  then show \<open>infinite (UNIV :: form set)\<close>
    using finite_prod by blast
qed simp

end