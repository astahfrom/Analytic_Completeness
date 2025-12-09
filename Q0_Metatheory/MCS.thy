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
  CPiP: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> [ \<forall>x\<^bsub>\<alpha>\<^esub>. A ] \<leadsto>\<^sub>\<gamma> (\<lambda>_. wffs\<^bsub>\<alpha>\<^esub>, \<lambda>B. [ A \<sqdot> B ])\<close>
| CExt: \<open>A \<in> wffs\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> \<Longrightarrow> [ A =\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> B ] \<leadsto>\<^sub>\<gamma> (\<lambda>_. wffs\<^bsub>\<alpha>\<^esub>, \<lambda>C. [ A \<sqdot> C =\<^bsub>\<beta>\<^esub>  B \<sqdot> C ])\<close>

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
    (* slow *)
    by (metis form.distinct(11,5,9) form.inject(4) map_con.simps(4) vars_form.elims wffs_of_type_cases
        wffs_of_type_intros(4))
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

lemma \<open>F\<^bsub>o\<^esub> \<notin> H\<close>
  using confl by (force intro: CFalse)

lemma \<open>x\<^bsub>o\<^esub> \<notin> H \<or> \<sim>\<^sup>\<Q> x\<^bsub>o\<^esub> \<notin> H\<close>
  using confl by (force intro: CVar[of x])

lemma \<open>\<lbrace>c\<rbrace>\<^bsub>o\<^esub> \<notin> H \<or> \<sim>\<^sup>\<Q> \<lbrace>c\<rbrace>\<^bsub>o\<^esub> \<notin> H\<close>
  using confl by (force intro: CCon[of c])

lemma \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> A \<and>\<^sup>\<Q> B \<in> H \<Longrightarrow> A \<in> H \<and> B \<in> H\<close>
  using alpha by (force intro: CConP[of A B])

lemma \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> A \<and>\<^sup>\<Q> B \<in> H \<Longrightarrow> A \<in> H \<and> B \<in> H\<close>
  using alpha by (force intro: CConP[of A B])

lemma \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> A \<supset>\<^sup>\<Q> B \<in> H \<Longrightarrow> \<sim>\<^sup>\<Q> A \<in> H \<or> B \<in> H\<close>
  using beta by (force intro: CImpP[of A B])

lemma \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> \<forall>x\<^bsub>\<alpha>\<^esub>. A \<in> H \<Longrightarrow> B \<in> wffs\<^bsub>\<alpha>\<^esub> \<Longrightarrow> A \<sqdot> B \<in> H\<close>
  using gamma by (force intro: CPiP[of A x \<alpha>])

lemma
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

end
