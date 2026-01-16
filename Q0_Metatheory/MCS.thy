theory MCS imports
  "../Analytic_Completeness"
  "Q0_Metatheory.Consistency"
begin

section \<open>Consistency Property\<close>

inductive confl_class :: \<open>form list \<Rightarrow> form list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<crossmark>\<close> 50) where
  CFalse: \<open>[ F\<^bsub>o\<^esub> ] \<leadsto>\<^sub>\<crossmark> [ F\<^bsub>o\<^esub> ]\<close>
| CVar: \<open>[ \<sim>\<^sup>\<Q> x\<^bsub>o\<^esub> ] \<leadsto>\<^sub>\<crossmark> [ x\<^bsub>o\<^esub> ]\<close>
| CCon: \<open>[ \<sim>\<^sup>\<Q> \<lbrace>c\<rbrace>\<^bsub>o\<^esub> ] \<leadsto>\<^sub>\<crossmark> [ \<lbrace>c\<rbrace>\<^bsub>o\<^esub> ]\<close>
| CIneq: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow>  [ \<sim>\<^sup>\<Q> (A =\<^bsub>o\<^esub> A) ] \<leadsto>\<^sub>\<crossmark> [ \<sim>\<^sup>\<Q> (A =\<^bsub>o\<^esub> A) ]\<close>

inductive alpha_class :: \<open>form list \<Rightarrow> form list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<alpha>\<close> 50) where
(*
  CEta: \<open>[ A \<in> wffs\<^bsub>\<alpha>\<^esub> \<Longrightarrow> A ] \<leadsto>\<^sub>\<alpha> [ \<eta> A]\<close> (* normal form ? *)
|*)
  CConP: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> [ A \<and>\<^sup>\<Q> B ] \<leadsto>\<^sub>\<alpha> [ A, B ]\<close>
| CImpN: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> [ \<sim>\<^sup>\<Q> (A \<supset>\<^sup>\<Q> B) ] \<leadsto>\<^sub>\<alpha> [ A, \<sim>\<^sup>\<Q> B ]\<close>
| CEqual: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> [ A =\<^bsub>o\<^esub> B ] \<leadsto>\<^sub>\<alpha> [ (A \<and>\<^sup>\<Q> B) \<or>\<^sup>\<Q> (\<sim>\<^sup>\<Q> A \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> B)]\<close>

inductive beta_class :: \<open>form list \<Rightarrow> form list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<beta>\<close> 50) where
  CConN: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> [ \<sim>\<^sup>\<Q> (A \<and>\<^sup>\<Q> B) ] \<leadsto>\<^sub>\<beta> [ \<sim>\<^sup>\<Q> A, \<sim>\<^sup>\<Q> B ]\<close>
| CImpP: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> [ A \<supset>\<^sup>\<Q> B ] \<leadsto>\<^sub>\<beta> [ \<sim>\<^sup>\<Q> A, B ]\<close>
| CDisP: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> [ A \<or>\<^sup>\<Q> B ] \<leadsto>\<^sub>\<beta> [ A, B ]\<close>

inductive gamma_class :: \<open>form list \<Rightarrow> (form set \<Rightarrow> _) \<times> (form \<Rightarrow> _) \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<gamma>\<close> 50) where
  CPiP: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> [ \<forall>x\<^bsub>\<alpha>\<^esub>. A ] \<leadsto>\<^sub>\<gamma> (\<lambda>_. wffs\<^bsub>\<alpha>\<^esub>, \<lambda>B. [ A \<sqdot> B ])\<close>
| CExt: \<open>A \<in> wffs\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> \<Longrightarrow> [ A =\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> B ] \<leadsto>\<^sub>\<gamma> (\<lambda>_. wffs\<^bsub>\<alpha>\<^esub>, \<lambda>C. [ A \<sqdot> C =\<^bsub>\<beta>\<^esub> B \<sqdot> C ])\<close>

subsection \<open>Negated Forall\<close>

inductive exists_match :: \<open>form \<Rightarrow> type \<times> form \<Rightarrow> bool\<close> where
  \<open>exists_match (\<sim>\<^sup>\<Q> (\<forall>x\<^bsub>\<alpha>\<^esub>. A)) (\<alpha>, A)\<close>

inductive_cases exists_matchE [elim]: \<open>exists_match (\<sim>\<^sup>\<Q> (\<forall>x\<^bsub>\<alpha>\<^esub>. A)) (\<alpha>', A')\<close>

lemma exists_match_uniq [dest]: \<open>exists_match C (\<alpha>, A) \<Longrightarrow> exists_match C (\<alpha>', A') \<Longrightarrow> \<alpha> = \<alpha>' \<and> A = A'\<close>
  by (auto elim: exists_match.cases)

lemma exists_match_THE [intro]: \<open>exists_match C (\<alpha>, A) \<Longrightarrow> exists_match C (THE (\<alpha>, A). exists_match C (\<alpha>, A))\<close>
  using exists_match_uniq theI by fastforce

lemma THE_exists_match: \<open>exists_match C (\<alpha>, A) \<Longrightarrow> (THE (\<alpha>, A). exists_match C (\<alpha>, A)) = (\<alpha>, A)\<close>
  by blast

lemma exists_matchD [dest]: \<open>exists_match C (\<alpha>, A) \<Longrightarrow> \<exists>x. C = \<sim>\<^sup>\<Q> (\<forall>x\<^bsub>\<alpha>\<^esub>. A)\<close>
  by (auto elim: exists_match.cases)

lemma exists_matchI [intro]: \<open>\<exists>x. C = \<sim>\<^sup>\<Q> (\<forall>x\<^bsub>\<alpha>\<^esub>. A) \<Longrightarrow> exists_match C (\<alpha>, A)\<close>
  using exists_match.intros by blast


subsection \<open>Negated Equality\<close>

inductive ineq_match :: \<open>form \<Rightarrow> type \<times> type \<times> form \<times> form \<Rightarrow> bool\<close> where
  \<open>ineq_match (\<sim>\<^sup>\<Q> (A =\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> B)) (\<alpha>, \<beta>, A, B)\<close>

inductive_cases ineq_matchE [elim]: \<open>ineq_match (\<sim>\<^sup>\<Q> (A =\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> B)) (\<alpha>', \<beta>', A', B')\<close>

lemma ineq_match_uniq [dest]: \<open>ineq_match C (\<alpha>, \<beta>, A, B) \<Longrightarrow> ineq_match C (\<alpha>', \<beta>', A', B') \<Longrightarrow> \<alpha> = \<alpha>' \<and> \<beta> = \<beta>' \<and> A = A' \<and> B = B'\<close>
  by (auto elim: ineq_match.cases)

lemma ineq_match_THE [intro]: \<open>ineq_match C (\<alpha>, \<beta>, A, B) \<Longrightarrow> ineq_match C (THE (\<alpha>, \<beta>, A, B). ineq_match C (\<alpha>, \<beta>, A, B))\<close>
  using ineq_match_uniq theI by fastforce

lemma THE_ineq_match: \<open>ineq_match C (\<alpha>, \<beta>, A, B) \<Longrightarrow> (THE (\<alpha>, \<beta>, A, B). ineq_match C (\<alpha>, \<beta>, A, B)) = (\<alpha>, \<beta>, A, B)\<close>
  by blast

lemma ineq_matchD [dest]: \<open>ineq_match C (\<alpha>, \<beta>, A, B) \<Longrightarrow> C = \<sim>\<^sup>\<Q> (A =\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> B)\<close>
  by (auto elim!: ineq_match.cases)

lemma ineq_matchI [intro]: \<open>C = \<sim>\<^sup>\<Q> (A =\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> B) \<Longrightarrow> ineq_match C (\<alpha>, \<beta>, A, B)\<close>
  using ineq_match.intros by blast


subsection \<open>Delta\<close>

(*
  I cannot tell whether this actually holds with the encoding of syntax. I don't know if it matters.
  I don't even know which one we need for the model existence.
*)
proposition \<open>exists_match C p \<Longrightarrow> ineq_match C q \<Longrightarrow> False\<close>
  apply (elim exists_match.cases ineq_match.cases)
  oops

fun \<delta> :: \<open>form \<Rightarrow> nat \<Rightarrow> form list\<close> where
  CDelta: \<open>\<delta> C c =
    (if C \<in> wffs\<^bsub>o\<^esub> \<and> (\<exists>\<alpha> A. exists_match C (\<alpha>, A)) then 
       case THE (\<alpha>, A). exists_match C (\<alpha>, A) of
         (\<alpha>, A) \<Rightarrow> [ \<sim>\<^sup>\<Q> (A \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) ]
     else if C \<in> wffs\<^bsub>o\<^esub> \<and> (\<exists>\<alpha> \<beta> A B. ineq_match C (\<alpha>, \<beta>, A, B)) then 
       case THE (\<alpha>, \<beta>, A, B). ineq_match C (\<alpha>, \<beta>, A, B) of
         (\<alpha>, \<beta>, A, B) \<Rightarrow> [ \<sim>\<^sup>\<Q> (A \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> B \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) ]
     else [])\<close>

lemma exists_match_delta [simp]:
  assumes \<open>C \<in> wffs\<^bsub>o\<^esub>\<close> \<open>exists_match C (\<alpha>, A)\<close>
  shows \<open>\<delta> C c = [ \<sim>\<^sup>\<Q> (A \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) ]\<close>
  unfolding CDelta using assms THE_exists_match by auto

lemma ineq_match_delta [simp]:
  assumes \<open>C \<in> wffs\<^bsub>o\<^esub>\<close> \<open>\<not> (\<exists>\<alpha> A. exists_match C (\<alpha>, A))\<close> \<open>ineq_match C (\<alpha>, \<beta>, A, B)\<close>
  shows \<open>\<delta> C c = [ \<sim>\<^sup>\<Q> (A \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> B \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) ]\<close>
    unfolding CDelta using assms THE_ineq_match by auto

section \<open>Operations\<close>

abbreviation \<open>is_logical_name c \<equiv> c = \<cc>\<^sub>Q \<or> c = \<cc>\<^sub>\<iota>\<close>

definition \<open>is_param c \<equiv> \<not> is_logical_name c\<close>

fun map_con :: "(nat \<Rightarrow> nat) \<Rightarrow> form \<Rightarrow> form" where
  "map_con _ (x\<^bsub>\<alpha>\<^esub>) = (x\<^bsub>\<alpha>\<^esub>)"
| "map_con f (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) = (if is_logical_name c \<or> is_logical_name (f c) then \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub> else \<lbrace>f c\<rbrace>\<^bsub>\<alpha>\<^esub>)"
| "map_con f (A \<sqdot> B) = map_con f A \<sqdot> map_con f B"
| "map_con f (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) = \<lambda>x\<^bsub>\<alpha>\<^esub>. map_con f A"

fun cons_form :: "form \<Rightarrow> nat set" where
  "cons_form (x\<^bsub>\<alpha>\<^esub>) = {}"
| "cons_form (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) = (if is_logical_name c then {} else {c})"
| "cons_form (A \<sqdot> B) = cons_form A \<union> cons_form B"
| "cons_form (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) = cons_form A"

section \<open>Lemmas\<close>

text \<open>This property is really what dodging the logical constants is all about.\<close>
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

lemma wff_map_con [iff]: \<open>map_con f A \<in> wffs\<^bsub>\<alpha>\<^esub> \<longleftrightarrow> A \<in> wffs\<^bsub>\<alpha>\<^esub>\<close>
proof (induct A arbitrary: \<alpha>)
  case (FVar x)
  then show ?case
    by (metis map_con.simps(1) surj_pair)
next
  case (FCon x)
  then show ?case
    by (induct x) (auto dest: wff_has_unique_type)
next
  case (FApp A B)
  then show ?case
    by (metis map_con.simps(3) wffs_from_app wffs_of_type_intros(3))
next
  case (FAbs x1a A)
  then show ?case
    by (metis map_con.simps(4) surj_pair wffs_from_abs wffs_of_type_intros(4))
qed

lemma finite_cons_form [simp]: \<open>finite (cons_form A)\<close>
  by (induct A) auto

lemma map_con_exists_match [intro]: \<open>exists_match C (\<alpha>, A) \<Longrightarrow> exists_match (map_con f C) (\<alpha>, map_con f A)\<close>
  by (auto elim: exists_match.cases simp: exists_match.simps)

lemma map_con_ineq_match [intro]: \<open>ineq_match C (\<alpha>, \<beta>, A, B) \<Longrightarrow> ineq_match (map_con f C) (\<alpha>, \<beta>, map_con f A, map_con f B)\<close>
  by (auto elim: ineq_match.cases simp: ineq_match.simps)

subsection \<open>Parameter Substitution Inversion\<close>

lemma map_con_FVar [dest]: \<open>map_con f A = x\<^bsub>\<alpha>\<^esub> \<Longrightarrow> A = x\<^bsub>\<alpha>\<^esub>\<close>
  by (induct A) (auto split: if_splits)

lemma map_con_FCon_not_param [dest]: \<open>map_con f A = \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub> \<Longrightarrow> \<not> is_param c \<Longrightarrow> A = \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>\<close>
  unfolding is_param_def by (induct A) (auto split: if_splits)

lemma map_con_FApp [dest!]: \<open>map_con f A = B \<sqdot> C \<Longrightarrow> \<exists>B' C'. map_con f B' = B \<and> map_con f C' = C \<and> A = B' \<sqdot> C'\<close>
  by (induct A) (auto split: if_splits)

lemma map_con_FAbs [dest!]: \<open>map_con f A = \<lambda>x\<^bsub>\<alpha>\<^esub>. B \<Longrightarrow> \<exists>B'. map_con f B' = B \<and> A = \<lambda>x\<^bsub>\<alpha>\<^esub>. B'\<close>
  by (induct A) (auto split: if_splits)

lemma map_con_cQ [dest]: \<open>map_con f A = \<lbrace>\<cc>\<^sub>Q\<rbrace>\<^bsub>\<alpha>\<^esub> \<Longrightarrow> A = \<lbrace>\<cc>\<^sub>Q\<rbrace>\<^bsub>\<alpha>\<^esub>\<close>
  by (auto simp: is_param_def)

lemma map_con_Q [dest]: \<open>map_con f A = Q\<^bsub>\<alpha>\<^esub> \<Longrightarrow> A = Q\<^bsub>\<alpha>\<^esub>\<close>
  by auto

lemma map_con_equality_of_type [dest]: \<open>map_con f A = B =\<^bsub>\<alpha>\<^esub> C \<Longrightarrow> \<exists>B' C'. map_con f B' = B \<and> map_con f C' = C \<and> A = B' =\<^bsub>\<alpha>\<^esub> C'\<close>
  by fastforce

lemma map_con_true [dest]: \<open>map_con f A = T\<^bsub>o\<^esub> \<Longrightarrow> A = T\<^bsub>o\<^esub>\<close>
  by auto

lemma map_con_false [dest]: \<open>map_con f A = F\<^bsub>o\<^esub> \<Longrightarrow> A = F\<^bsub>o\<^esub>\<close>
  by (induct A) auto

lemma map_con_neg [dest]: \<open>map_con f A = \<sim>\<^sup>\<Q> B \<Longrightarrow> \<exists>B'. map_con f B' = B \<and> A = \<sim>\<^sup>\<Q> B'\<close>
  by (induct A) auto

lemma map_con_forall [dest]: \<open>map_con f A = \<forall>x\<^bsub>\<alpha>\<^esub>. B \<Longrightarrow> \<exists>B'. map_con f B' = B \<and> A = \<forall>x\<^bsub>\<alpha>\<^esub>. B'\<close>
  by auto

lemma exists_match_map_con [dest]: \<open>exists_match (map_con f A) (\<alpha>, B) \<Longrightarrow> \<exists>B'. map_con f B' = B \<and> exists_match A (\<alpha>, B')\<close>
  by fast

lemma ineq_match_map_con [dest]: \<open>ineq_match (map_con f C) (\<alpha>, \<beta>, A, B) \<Longrightarrow> \<exists>A' B'. map_con f A' = A \<and> map_con f B' = B \<and> ineq_match C (\<alpha>, \<beta>, A', B')\<close>
  by fast

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
  by unfold_locales (elim gamma_class.cases, auto simp: gamma_class.simps)

interpretation D: Delta map_con cons_form is_param \<delta>
proof
  fix p x f
  assume \<open>is_param x\<close> \<open>P.is_subst f\<close>
  then show \<open>\<delta> (map_con f p) (f x) = map (map_con f) (\<delta> p x)\<close>
  proof (induct p x rule: \<delta>.induct)
    case (1 C c)
    then have c: \<open>\<not> is_logical_name (f c)\<close>
      unfolding P.is_subst_def by (auto simp: is_param_def)
   
    from 1 show ?case
    proof (cases \<open>C \<in> wffs\<^bsub>o\<^esub> \<and> (\<exists>\<alpha> A. exists_match C (\<alpha>, A))\<close>)
      case True
      then obtain \<alpha> A y where C: \<open>C = \<sim>\<^sup>\<Q> (\<forall>y\<^bsub>\<alpha>\<^esub>. A)\<close>
        by (auto elim: exists_match.cases)
      then have *: \<open>\<delta> C c = [ \<sim>\<^sup>\<Q> (A \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) ]\<close>
        using True MCS.CDelta exists_match_delta by blast
      then have *: \<open>map (map_con f) (\<delta> C c) = [ \<sim>\<^sup>\<Q> (map_con f A \<sqdot> \<lbrace>f c\<rbrace>\<^bsub>\<alpha>\<^esub>) ]\<close>
        using 1 c by (auto simp: is_param_def)
      have \<open>exists_match (map_con f C) (\<alpha>, map_con f A)\<close>
        using C map_con_exists_match by blast
      moreover have \<open>map_con f C \<in> wffs\<^bsub>o\<^esub>\<close>
        using True wff_map_con by blast
      ultimately have \<open>\<delta> (map_con f C) (f c) = [ \<sim>\<^sup>\<Q> (map_con f A \<sqdot> \<lbrace>f c\<rbrace>\<^bsub>\<alpha>\<^esub>) ]\<close>
        unfolding MCS.CDelta using exists_match_delta by auto
      then show ?thesis
        using * by simp
    next
      case not_exists: False
      then show ?thesis
      proof (cases \<open>C \<in> wffs\<^bsub>o\<^esub> \<and> (\<exists>\<alpha> \<beta> A B. ineq_match C (\<alpha>, \<beta>, A, B))\<close>)
        case True
        then obtain \<alpha> \<beta> A B where C: \<open>C = \<sim>\<^sup>\<Q> (A =\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> B)\<close>
          by (auto elim: exists_match.cases)
        then have *: \<open>\<delta> C c = [ \<sim>\<^sup>\<Q> (A \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> B \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) ]\<close>
        using True MCS.CDelta not_exists ineq_match_delta by blast
        then have *: \<open>map (map_con f) (\<delta> C c) = [ \<sim>\<^sup>\<Q> (map_con f A \<sqdot> \<lbrace>f c\<rbrace>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> map_con f B \<sqdot> \<lbrace>f c\<rbrace>\<^bsub>\<alpha>\<^esub>) ]\<close>
          using 1 c by (auto simp: is_param_def)
        have \<open>ineq_match (map_con f C) (\<alpha>, \<beta>, map_con f A, map_con f B)\<close>
          using C map_con_ineq_match by blast
        moreover have \<open>map_con f C \<in> wffs\<^bsub>o\<^esub>\<close>
          using True wff_map_con by blast
        ultimately have \<open>\<delta> (map_con f C) (f c) = [ \<sim>\<^sup>\<Q> (map_con f A \<sqdot> \<lbrace>f c\<rbrace>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> map_con f B \<sqdot> \<lbrace>f c\<rbrace>\<^bsub>\<alpha>\<^esub>) ]\<close>
          unfolding MCS.CDelta using not_exists ineq_match_delta by auto
        then show ?thesis
          using * by simp
      next
        case False
        then show ?thesis
          using not_exists by auto
      qed
    qed
  qed
qed

abbreviation Kinds :: \<open>(nat, form) kind list\<close> where
  \<open>Kinds \<equiv> [C.kind, A.kind, B.kind, G.kind, D.kind]\<close>

lemma prop\<^sub>E_Kinds:
  assumes \<open>P.sat\<^sub>E C.kind C\<close> \<open>P.sat\<^sub>E A.kind C\<close> \<open>P.sat\<^sub>E B.kind C\<close> \<open>P.sat\<^sub>E G.kind C\<close> \<open>P.sat\<^sub>E D.kind C\<close>
  shows \<open>P.prop\<^sub>E Kinds C\<close>
  unfolding P.prop\<^sub>E_def using assms by simp

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

locale MyHintikka = Hintikka map_con cons_form is_param Kinds H
  for H :: \<open>form set\<close>
begin

lemmas
  confl = sat\<^sub>H[of C.kind] and
  alpha = sat\<^sub>H[of A.kind] and
  beta = sat\<^sub>H[of B.kind] and
  gamma = sat\<^sub>H[of G.kind] and
  delta = sat\<^sub>H[of D.kind]

lemma cFalse: \<open>F\<^bsub>o\<^esub> \<notin> H\<close>
  using confl by (force intro: CFalse)

lemma cVar: \<open>x\<^bsub>o\<^esub> \<notin> H \<or> \<sim>\<^sup>\<Q> x\<^bsub>o\<^esub> \<notin> H\<close>
  using confl by (force intro: CVar[of x])

lemma cCon: \<open>\<lbrace>c\<rbrace>\<^bsub>o\<^esub> \<notin> H \<or> \<sim>\<^sup>\<Q> \<lbrace>c\<rbrace>\<^bsub>o\<^esub> \<notin> H\<close>
  using confl by (force intro: CCon[of c])

lemma cIneq: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> \<sim>\<^sup>\<Q> (A =\<^bsub>o\<^esub> A) \<notin> H\<close>
  using confl by (force intro: CIneq[of A])

lemma cConP: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> A \<and>\<^sup>\<Q> B \<in> H \<Longrightarrow> A \<in> H \<and> B \<in> H\<close>
  using alpha by (force intro: CConP[of A B])

lemma cImpN: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> \<sim>\<^sup>\<Q> (A \<supset>\<^sup>\<Q> B) \<in> H \<Longrightarrow> A \<in> H \<and> \<sim>\<^sup>\<Q> B \<in> H\<close>
  using alpha by (force intro: CImpN[of A B])

lemma cEqual: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> A =\<^bsub>o\<^esub> B \<in> H \<Longrightarrow> ((A \<and>\<^sup>\<Q> B) \<or>\<^sup>\<Q> (\<sim>\<^sup>\<Q> A \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> B)) \<in> H\<close>
  using alpha by (force intro: CEqual[of A B])

lemma cConN: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> \<sim>\<^sup>\<Q> (A \<and>\<^sup>\<Q> B) \<in> H \<Longrightarrow> \<sim>\<^sup>\<Q> A \<in> H \<or> \<sim>\<^sup>\<Q> B \<in> H\<close>
  using beta by (force intro: CConN[of A B])

lemma cImpP: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> A \<supset>\<^sup>\<Q> B \<in> H \<Longrightarrow> \<sim>\<^sup>\<Q> A \<in> H \<or> B \<in> H\<close>
  using beta by (force intro: CImpP[of A B])

lemma cDisP: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> A \<or>\<^sup>\<Q> B \<in> H \<Longrightarrow> A \<in> H \<or> B \<in> H\<close>
  using beta by (force intro: CDisP[of A B])

lemma cPiP: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> \<forall>x\<^bsub>\<alpha>\<^esub>. A \<in> H \<Longrightarrow> B \<in> wffs\<^bsub>\<alpha>\<^esub> \<Longrightarrow> A \<sqdot> B \<in> H\<close>
  using gamma by (force intro: CPiP[of A x \<alpha>])

lemma cExt: \<open>A \<in> wffs\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> \<Longrightarrow> (A =\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> B) \<in> H \<Longrightarrow> C \<in> wffs\<^bsub>\<alpha>\<^esub> \<Longrightarrow> (A \<sqdot> C =\<^bsub>\<beta>\<^esub> B \<sqdot> C) \<in> H\<close>
  using gamma by (force intro: CExt[of A \<alpha>])

lemma cDelta:
  assumes \<open>B \<in> wffs\<^bsub>o\<^esub>\<close> \<open>\<sim>\<^sup>\<Q> (\<forall>x\<^bsub>\<alpha>\<^esub>. B) \<in> H\<close>
  shows \<open>\<exists>c. is_param c \<and> \<sim>\<^sup>\<Q> (B \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) \<in> H\<close>
proof -
  have \<open>\<sim>\<^sup>\<Q> (\<forall>x\<^bsub>\<alpha>\<^esub>. B) \<in> wffs\<^bsub>o\<^esub> \<and> (\<exists>\<alpha> B. exists_match (\<sim>\<^sup>\<Q> (\<forall>x\<^bsub>\<alpha>\<^esub>. B)) (\<alpha>, B))\<close>
    using assms(1) by blast
  then have \<open>\<delta> (\<sim>\<^sup>\<Q> (\<forall>x\<^bsub>\<alpha>\<^esub>. B)) c = [ \<sim>\<^sup>\<Q> (B \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) ]\<close> for c
    by (metis (mono_tags, lifting) \<delta>.simps case_prod_conv exists_match.intros exists_matchE exists_match_THE
        surj_pair)
  then show ?thesis
    using delta assms(2) by (metis list.set_intros(1,2) sat\<^sub>H_WitsE subset_code(1))
qed

(*
If s \<equiv>\<beta>\<eta> t and s \<in> H, then t \<in> H.
Do we have this? Do we even have notions of beta and eta?
*)

lemma equal_ext: \<open>T\<^bsub>o\<^esub> \<in> H  \<Longrightarrow> A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> (Q\<^bsub>o\<^esub> \<sqdot> A =\<^bsub>o \<rightarrow> o\<^esub> Q\<^bsub>o\<^esub> \<sqdot> A) \<in> H\<close>
  using cExt by fastforce

lemma equal_parts: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> (A =\<^bsub>o\<^esub> B) \<in> H \<Longrightarrow> A \<in> H \<and> B \<in> H \<or> \<sim>\<^sup>\<Q> A \<in> H \<and> \<sim>\<^sup>\<Q> B \<in> H\<close>
  by (metis cConP cDisP cEqual conj_op_wff neg_wff)

lemma true_saturation:
  assumes \<open>T\<^bsub>o\<^esub> \<in> H\<close> \<open>A \<in> wffs\<^bsub>o\<^esub>\<close>
  shows \<open>A \<in> H \<or> \<sim>\<^sup>\<Q> A \<in> H\<close>
proof -
  have \<open>(Q\<^bsub>o\<^esub> \<sqdot> A =\<^bsub>o \<rightarrow> o\<^esub> Q\<^bsub>o\<^esub> \<sqdot> A) \<in> H\<close>
    using equal_ext assms by fast
  then have \<open>((A =\<^bsub>o\<^esub> A) =\<^bsub>o\<^esub> (A =\<^bsub>o\<^esub> A)) \<in> H\<close>
    using assms(2) gamma by (force intro: CExt[where A=\<open>Q\<^bsub>o\<^esub> \<sqdot> A\<close> and B=\<open>Q\<^bsub>o\<^esub> \<sqdot> A\<close>])
  then show ?thesis
    by (metis assms(2) cIneq equal_parts equality_wff)
qed

end

theorem extension_lemma:
  fixes S :: \<open>form set\<close>
  assumes \<open>P.prop\<^sub>E Kinds C\<close>
    and \<open>S \<in> C\<close>
    and \<open>P.enough_new S\<close>
    and \<open>T\<^bsub>o\<^esub> \<in> S\<close>
    and \<open>A \<in> wffs\<^bsub>o\<^esub>\<close>
  shows \<open>A \<in> (mk_mcs C S) \<or> \<sim>\<^sup>\<Q> A \<in> (mk_mcs C S)\<close>
proof -
  have *: \<open>MyHintikka (mk_mcs C S)\<close>
  proof
    show \<open>P.prop\<^sub>H Kinds (mk_mcs C S)\<close>
      using mk_mcs_Hintikka[OF assms(1-3)] Hintikka.hintikka by blast
  qed
  moreover have \<open>T\<^bsub>o\<^esub> \<in> mk_mcs C S\<close>
    using assms(4) Extend_subset by blast
  ultimately show ?thesis
    using MyHintikka.true_saturation assms(5) by blast
qed

subsection \<open>Derivational Consistency\<close>

definition is_consistent_set :: "form set \<Rightarrow> bool" where
  [iff]: "is_consistent_set \<G> \<longleftrightarrow> is_hyps \<G> \<and> \<not> is_inconsistent_set \<G>"

interpretation DC: Derivational_Confl map_con cons_form is_param confl_class is_consistent_set
proof
  fix H ps qs q
  assume \<open>ps \<leadsto>\<^sub>\<crossmark> qs\<close> and *: \<open>lset ps \<subseteq> H\<close> \<open>q \<in> lset qs\<close> \<open>q \<in> H\<close>
  then show \<open>\<not> is_consistent_set H\<close>
  proof cases
    case CFalse
    then have \<open>F\<^bsub>o\<^esub> \<in> H\<close>
      using * by simp
    then show ?thesis
      using dv_hyp by blast
  next
    case (CVar x)
    then show ?thesis
    proof safe
      assume H: \<open>H \<subseteq> wffs\<^bsub>o\<^esub>\<close> \<open>finite H\<close>
      from CVar have \<open>\<sim>\<^sup>\<Q> x\<^bsub>o\<^esub> \<in> H\<close> \<open>x\<^bsub>o\<^esub> \<in> H\<close>
        using * by simp_all
      then have \<open>H \<turnstile> \<sim>\<^sup>\<Q> x\<^bsub>o\<^esub>\<close> \<open>H \<turnstile> x\<^bsub>o\<^esub>\<close>
        using dv_hyp H by blast+
      then show \<open>H \<turnstile> F\<^bsub>o\<^esub>\<close>
        using H by (metis equality_of_type_def equivalence_def neg_def prop_5201_1 prop_5201_2)
    qed
  next
    case (CCon c)
    then show ?thesis
    proof safe
      assume H: \<open>H \<subseteq> wffs\<^bsub>o\<^esub>\<close> \<open>finite H\<close>
      from CCon have \<open>\<sim>\<^sup>\<Q> \<lbrace>c\<rbrace>\<^bsub>o\<^esub> \<in> H\<close> \<open>\<lbrace>c\<rbrace>\<^bsub>o\<^esub> \<in> H\<close>
        using * by simp_all
      then have \<open>H \<turnstile> \<sim>\<^sup>\<Q> \<lbrace>c\<rbrace>\<^bsub>o\<^esub>\<close> \<open>H \<turnstile> \<lbrace>c\<rbrace>\<^bsub>o\<^esub>\<close>
        using dv_hyp H by blast+
      then show \<open>H \<turnstile> F\<^bsub>o\<^esub>\<close>
        using H by (metis equality_of_type_def equivalence_def neg_def prop_5201_1 prop_5201_2)
    qed
  qed
qed


subsection \<open>Conjunctive Consistency\<close>

lemma pre_is_taut_conj:
  assumes \<open>A \<in> pwffs\<close> and \<open>B \<in> pwffs\<close>
  shows \<open>is_tautology (A \<and>\<^sup>\<Q> B \<supset>\<^sup>\<Q> A)\<close>
    and \<open>is_tautology (A \<and>\<^sup>\<Q> B \<supset>\<^sup>\<Q> B)\<close>
    and \<open>is_tautology ((\<sim>\<^sup>\<Q> (A \<supset>\<^sup>\<Q> B)) \<supset>\<^sup>\<Q> A)\<close>
    and \<open>is_tautology ((\<sim>\<^sup>\<Q> (A \<supset>\<^sup>\<Q> B)) \<supset>\<^sup>\<Q> \<sim>\<^sup>\<Q> B)\<close>
proof-
  have val_eq: 
    \<open>\<V>\<^sub>B \<phi> (A \<and>\<^sup>\<Q> B \<supset>\<^sup>\<Q> A) = (\<V>\<^sub>B \<phi> A \<^bold>\<and> \<V>\<^sub>B \<phi> B) \<^bold>\<supset> \<V>\<^sub>B \<phi> A\<close>
    \<open>\<V>\<^sub>B \<phi> (A \<and>\<^sup>\<Q> B \<supset>\<^sup>\<Q> B) = (\<V>\<^sub>B \<phi> A \<^bold>\<and> \<V>\<^sub>B \<phi> B) \<^bold>\<supset> \<V>\<^sub>B \<phi> B\<close>
    \<open>\<V>\<^sub>B \<phi> ((\<sim>\<^sup>\<Q> (A \<supset>\<^sup>\<Q> B)) \<supset>\<^sup>\<Q> A) = ((\<sim> (\<V>\<^sub>B \<phi> A \<^bold>\<supset> \<V>\<^sub>B \<phi> B)) \<^bold>\<supset> \<V>\<^sub>B \<phi> A)\<close>
    \<open>\<V>\<^sub>B \<phi> ((\<sim>\<^sup>\<Q> (A \<supset>\<^sup>\<Q> B)) \<supset>\<^sup>\<Q> \<sim>\<^sup>\<Q> B) = ((\<sim> (\<V>\<^sub>B \<phi> A \<^bold>\<supset> \<V>\<^sub>B \<phi> B)) \<^bold>\<supset> \<sim> \<V>\<^sub>B \<phi> B)\<close>
    if \<open>is_tv_assignment \<phi>\<close> for \<phi>
    using assms that
    by (simp_all only: \<V>\<^sub>B_simps)
  moreover have eq_true: 
    \<open>(\<V>\<^sub>B \<phi> A \<^bold>\<and> \<V>\<^sub>B \<phi> B) \<^bold>\<supset> \<V>\<^sub>B \<phi> A = \<^bold>T\<close>
    \<open>(\<V>\<^sub>B \<phi> A \<^bold>\<and> \<V>\<^sub>B \<phi> B) \<^bold>\<supset> \<V>\<^sub>B \<phi> B = \<^bold>T\<close> 
    \<open>((\<sim> (\<V>\<^sub>B \<phi> A \<^bold>\<supset> \<V>\<^sub>B \<phi> B)) \<^bold>\<supset> \<V>\<^sub>B \<phi> A) = \<^bold>T\<close>
    \<open>((\<sim> (\<V>\<^sub>B \<phi> A \<^bold>\<supset> \<V>\<^sub>B \<phi> B)) \<^bold>\<supset> \<sim> \<V>\<^sub>B \<phi> B) = \<^bold>T\<close> for \<phi>
    by simp_all
  ultimately show \<open>is_tautology (A \<and>\<^sup>\<Q> B \<supset>\<^sup>\<Q> A)\<close>
    unfolding is_tautology_def
    by (safe; (intro assms)?) force
  show \<open>is_tautology (A \<and>\<^sup>\<Q> B \<supset>\<^sup>\<Q> B)\<close>
    using val_eq eq_true
    unfolding is_tautology_def
    by (safe; (intro assms)?) force
  show \<open>is_tautology ((\<sim>\<^sup>\<Q> (A \<supset>\<^sup>\<Q> B)) \<supset>\<^sup>\<Q> A)\<close>
    using val_eq eq_true
    unfolding is_tautology_def
    by (safe; (intro assms)?) force
  show \<open>is_tautology ((\<sim>\<^sup>\<Q> (A \<supset>\<^sup>\<Q> B)) \<supset>\<^sup>\<Q> \<sim>\<^sup>\<Q> B)\<close>
    using val_eq eq_true
    unfolding is_tautology_def
    by (safe; (intro assms)?) force
qed

lemma is_taut_conj:
  assumes \<open>A \<in> wffs\<^bsub>o\<^esub>\<close> and \<open>B \<in> wffs\<^bsub>o\<^esub>\<close>
  shows \<open>is_tautologous (A \<and>\<^sup>\<Q> B \<supset>\<^sup>\<Q> A)\<close>
    and \<open>is_tautologous (A \<and>\<^sup>\<Q> B \<supset>\<^sup>\<Q> B)\<close>
    and \<open>is_tautologous ((\<sim>\<^sup>\<Q> (A \<supset>\<^sup>\<Q> B)) \<supset>\<^sup>\<Q> A)\<close>
    and \<open>is_tautologous ((\<sim>\<^sup>\<Q> (A \<supset>\<^sup>\<Q> B)) \<supset>\<^sup>\<Q> \<sim>\<^sup>\<Q> B)\<close>
proof-
  obtain p r where \<open>(p, o) \<notin> vars (A \<and>\<^sup>\<Q> B \<supset>\<^sup>\<Q> A)\<close>
    and \<open>(r, o) \<notin> vars (A \<and>\<^sup>\<Q> B \<supset>\<^sup>\<Q> A)\<close> and \<open>p \<noteq> r\<close>
    using fresh_var_existence[of \<open>vars A \<union> vars B\<close>]
    by (metis ID.set_finite UnCI finite_Un 
        fresh_var_existence insert_iff vars_form_finiteness)
  let ?\<theta> = \<open>{(p, o) \<Zinj> A, (r,o) \<Zinj> B}\<close>
  have theta_is_pwff: \<open>is_pwff_substitution ?\<theta>\<close>
    using assms
    by simp
  have tauts:
    \<open>is_tautology (p\<^bsub>o\<^esub> \<and>\<^sup>\<Q> r\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> p\<^bsub>o\<^esub>)\<close>
    \<open>is_tautology (p\<^bsub>o\<^esub> \<and>\<^sup>\<Q> r\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> r\<^bsub>o\<^esub>)\<close>
    \<open>is_tautology ((\<sim>\<^sup>\<Q> (p\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> r\<^bsub>o\<^esub>)) \<supset>\<^sup>\<Q> p\<^bsub>o\<^esub>)\<close>
    \<open>is_tautology ((\<sim>\<^sup>\<Q> (p\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> r\<^bsub>o\<^esub>)) \<supset>\<^sup>\<Q> \<sim>\<^sup>\<Q> r\<^bsub>o\<^esub>)\<close>
    by (intro pre_is_taut_conj pwffs.intros)+
  have \<open>A \<and>\<^sup>\<Q> B \<supset>\<^sup>\<Q> A = \<^bold>S ?\<theta> (p\<^bsub>o\<^esub> \<and>\<^sup>\<Q> r\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> p\<^bsub>o\<^esub>)\<close>
    using \<open>p \<noteq> r\<close>
    by simp
  thus \<open>is_tautologous (A \<and>\<^sup>\<Q> B \<supset>\<^sup>\<Q> A)\<close>
    using theta_is_pwff tauts(1)
    by blast
  have \<open>A \<and>\<^sup>\<Q> B \<supset>\<^sup>\<Q> B = \<^bold>S ?\<theta> (p\<^bsub>o\<^esub> \<and>\<^sup>\<Q> r\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> r\<^bsub>o\<^esub>)\<close>
    using \<open>p \<noteq> r\<close>
    by simp
  thus \<open>is_tautologous (A \<and>\<^sup>\<Q> B \<supset>\<^sup>\<Q> B)\<close>
    using theta_is_pwff tauts(2)
    by blast
  have \<open>(\<sim>\<^sup>\<Q> (A \<supset>\<^sup>\<Q> B) \<supset>\<^sup>\<Q> A) =  \<^bold>S ?\<theta> ((\<sim>\<^sup>\<Q> (p\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> r\<^bsub>o\<^esub>)) \<supset>\<^sup>\<Q> p\<^bsub>o\<^esub>)\<close>
    using \<open>p \<noteq> r\<close>
    by simp
  thus \<open>is_tautologous ((\<sim>\<^sup>\<Q> (A \<supset>\<^sup>\<Q> B)) \<supset>\<^sup>\<Q> A)\<close>
    using theta_is_pwff tauts(3)
    by blast
  have \<open>(\<sim>\<^sup>\<Q> (A \<supset>\<^sup>\<Q> B) \<supset>\<^sup>\<Q> \<sim>\<^sup>\<Q> B) =  \<^bold>S ?\<theta> ((\<sim>\<^sup>\<Q> (p\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> r\<^bsub>o\<^esub>)) \<supset>\<^sup>\<Q> \<sim>\<^sup>\<Q> r\<^bsub>o\<^esub>)\<close>
    using \<open>p \<noteq> r\<close>
    by simp
  thus \<open>is_tautologous ((\<sim>\<^sup>\<Q> (A \<supset>\<^sup>\<Q> B)) \<supset>\<^sup>\<Q> \<sim>\<^sup>\<Q> B)\<close>
    using theta_is_pwff tauts(4)
    by blast
qed

lemma derivable_from_tautologous_imp_op:
  assumes \<open>A \<in> wffs\<^bsub>o\<^esub>\<close>
    and \<open>is_tautologous (A \<supset>\<^sup>\<Q> B)\<close>
  shows \<open>{A} \<turnstile> B\<close>
proof-
  have \<open>is_hyps {A}\<close>
    using \<open>A \<in> wffs\<^bsub>o\<^esub>\<close>
    by simp
  have obs: \<open>([X] \<supset>\<^sup>\<Q>\<^sub>\<star> Y) = (X \<supset>\<^sup>\<Q> Y)\<close> for X Y
    by simp_all
  show \<open>{A} \<turnstile> B\<close>
    using tautologous_horn_clause_is_hyp_derivable
      [OF \<open>is_hyps {A}\<close> \<open>is_hyps {A}\<close>, where hs=\<open>[A]\<close>]
    \<open>is_tautologous (A \<supset>\<^sup>\<Q> B)\<close>
    unfolding obs
    by (metis \<open>is_hyps {A}\<close> dv_hyp empty_set 
        list.simps(15))
qed

lemma rule_conj:
  assumes \<open>A \<in> wffs\<^bsub>o\<^esub>\<close> and \<open>B \<in> wffs\<^bsub>o\<^esub>\<close>
  shows \<open>{A \<and>\<^sup>\<Q> B} \<turnstile> A\<close> 
    and \<open>{A \<and>\<^sup>\<Q> B} \<turnstile> B\<close>
    and \<open>{\<sim>\<^sup>\<Q> (A \<supset>\<^sup>\<Q> B)} \<turnstile> A\<close>
    and \<open>{\<sim>\<^sup>\<Q> (A \<supset>\<^sup>\<Q> B)} \<turnstile> \<sim>\<^sup>\<Q> B\<close>
proof-
  show \<open>{A \<and>\<^sup>\<Q> B} \<turnstile> A\<close>
    apply (rule derivable_from_tautologous_imp_op[OF _ is_taut_conj(1)])
    using assms
    by fastforce+
  show \<open>{A \<and>\<^sup>\<Q> B} \<turnstile> B\<close>
    apply (rule derivable_from_tautologous_imp_op[OF _ is_taut_conj(2)])
    using assms
    by fastforce+
  show \<open>{\<sim>\<^sup>\<Q> (A \<supset>\<^sup>\<Q> B)} \<turnstile> A\<close>
    apply (rule derivable_from_tautologous_imp_op[OF _ is_taut_conj(3)])
    using assms
    by fastforce+
  show \<open>{\<sim>\<^sup>\<Q> (A \<supset>\<^sup>\<Q> B)} \<turnstile> \<sim>\<^sup>\<Q> B\<close>
    apply (rule derivable_from_tautologous_imp_op[OF _ is_taut_conj(4)])
    using assms
    by fastforce+
qed

interpretation DA: Weak_Derivational_Alpha map_con cons_form \<open>\<lambda>_. True\<close> alpha_class "is_consistent_set \<circ> lset"
proof(standard)
  fix Hs 
    and ps qs :: \<open>form list\<close>
  assume \<open>ps \<leadsto>\<^sub>\<alpha> qs\<close> 
    and sub: \<open>lset ps \<subseteq> lset Hs\<close>
    and consistent: \<open>(is_consistent_set \<circ> lset) Hs\<close>
  hence well_formed: \<open>(lset qs \<union> lset Hs) \<subseteq> wffs\<^bsub>o\<^esub>\<close>
  proof(cases)
    case (CConP B C)
    then show ?thesis
      using consistent by force
  next
    case (CImpN B C)
    then show ?thesis 
      using consistent by force
  qed
  moreover have \<open>finite (lset qs \<union> lset Hs)\<close>
    by simp
  ultimately have \<open>is_hyps (lset qs \<union> lset Hs)\<close>
    unfolding is_consistent_set_def ..
  from \<open>ps \<leadsto>\<^sub>\<alpha> qs\<close>
  have \<open>\<forall>F \<in> lset qs. lset Hs \<turnstile> F\<close>
  proof(cases)
    case (CConP B C)
    have \<open>lset Hs \<turnstile> B\<close>
      apply (rule prop_5241[OF _ _ sub])
      using consistent
      by simp (metis CConP(1) rule_conj(1)[OF CConP(3,4)] 
          list.simps(15) set_empty2)
    moreover have \<open>lset Hs \<turnstile> C\<close>
      apply (rule prop_5241[OF _ _ sub])
      using consistent
      by simp (metis CConP(1) rule_conj(2)[OF CConP(3,4)] 
          list.simps(15) set_empty2)
    ultimately show ?thesis
      using local.CConP(2) 
      by force
  next
    case (CImpN B C)
    have \<open>lset Hs \<turnstile> B\<close>
      apply (rule prop_5241[OF _ _ sub])
      using consistent
      by simp (metis list.set(1) list.simps(15) 
          CImpN(1,3,4) rule_conj(3))
    moreover have \<open>lset Hs \<turnstile> \<sim>\<^sup>\<Q> C\<close>
      apply (rule prop_5241[OF _ _ sub])
      using consistent
      by simp (metis list.set(1) list.simps(15) 
          CImpN(1,3,4) rule_conj(4))
    ultimately show ?thesis
      using local.CImpN(2) 
      by force
  qed
  have \<open>(is_consistent_set (lset qs \<union> lset Hs))\<close>
    by (metis \<open>\<forall>F\<in>lset qs. lset Hs \<turnstile> F\<close> \<open>finite (lset qs \<union> lset Hs)\<close> well_formed
        comp_apply consistent finite_Un generalized_deduction_theorem generalized_modus_ponens
        is_consistent_set_def is_inconsistent_set_def sup_commute)
  thus "(is_consistent_set \<circ> lset) (qs @ Hs)"
    by simp
qed


subsection \<open>Disjunctive Consistency\<close>

interpretation DB: Weak_Derivational_Beta map_con cons_form \<open>\<lambda>_. True\<close> beta_class "is_consistent_set \<circ> lset"
proof
  fix Hs and ps qs
  assume \<open>ps \<leadsto>\<^sub>\<beta> qs\<close>
    and sub: \<open>lset ps \<subseteq> lset Hs\<close>
    and consistent: \<open>(is_consistent_set \<circ> lset) Hs\<close>
  thus \<open>\<exists>q\<in>lset qs. (is_consistent_set \<circ> lset) (q # Hs)\<close>
  proof(cases)
    case (CConN A B)
    then show ?thesis
      sorry
  next
    case (CImpP A B)
    then show ?thesis
      sorry
  qed
qed



end
