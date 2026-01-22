theory MCS imports
  "../Analytic_Completeness"
  "Q0_Metatheory.Consistency"
begin

section \<open>Stuff from Anders\<close>

instance type :: countable
  by countable_datatype

instance form :: countable
  by countable_datatype

instance type :: small ..
instance type :: embeddable ..
instance form :: small ..
instance form :: embeddable ..

definition V_of_type :: "type \<Rightarrow> V" where
  "V_of_type = (SOME V_of. inj V_of)"

definition type_of_V :: "V \<Rightarrow> type" where
  "type_of_V = inv V_of_type"

definition is_type :: "V \<Rightarrow> bool" where
  "is_type t \<longleftrightarrow> t \<in> range V_of_type"

lemma "is_type VA \<Longrightarrow> \<exists>t. V_of_type t = VA "
  using is_type_def by auto

lemma "inj V_of_type"
  by (metis V_of_type_def embeddable_class.ex_inj someI_ex)
  
lemma "type_of_V (V_of_type t) = t"
  by (metis V_of_type_def embeddable_class.ex_inj type_of_V_def inv_f_f someI_ex)

lemma "is_type Vt \<Longrightarrow> V_of_type (type_of_V Vt) = Vt"
  by (simp add: f_inv_into_f is_type_def type_of_V_def)


definition V_of_form :: "form \<Rightarrow> V" where
  "V_of_form = (SOME V_of. inj V_of)"

definition form_of_V :: "V \<Rightarrow> form" where
  "form_of_V = inv V_of_form"

definition is_form :: "V \<Rightarrow> bool" where
  "is_form A \<longleftrightarrow> A \<in> range V_of_form"

lemma "is_form VA \<Longrightarrow> \<exists>A. V_of_form A = VA "
  using is_form_def by auto

lemma "inj V_of_form"
  by (metis V_of_form_def embeddable_class.ex_inj someI_ex)
  
lemma "form_of_V (V_of_form A) = A"
  by (metis V_of_form_def embeddable_class.ex_inj form_of_V_def inv_f_f someI_ex)

lemma "is_form VA \<Longrightarrow> V_of_form (form_of_V VA) = VA"
  by (simp add: f_inv_into_f form_of_V_def is_form_def)

(* Modified from Anders's definition. *)
definition extensionally_complete_membership :: "form set \<Rightarrow> bool" where
  \<open>extensionally_complete_membership H \<longleftrightarrow>
    (\<forall>A B \<alpha> \<beta>. A \<in> wffs\<^bsub>(\<beta> \<rightarrow> \<alpha>)\<^esub> \<longrightarrow>
               B \<in> wffs\<^bsub>(\<beta> \<rightarrow> \<alpha>)\<^esub> \<longrightarrow>
               (\<exists>C. C \<in> wffs\<^bsub>\<beta>\<^esub> \<and>
                    (((A \<sqdot> C) =\<^bsub>\<alpha>\<^esub> (B \<sqdot> C)) \<supset>\<^sup>\<Q> (A =\<^bsub>\<beta> \<rightarrow> \<alpha>\<^esub> B) \<in> H)))\<close>


section \<open>Consistency Property\<close>

(* I don't know if we need to restrict everything to sentences. *)
(* I have a feeling that we could deduce the propositional conditions from the equality ones, but I'm not sure.
   We are probably missing something for iota \<open>\<iota>\<close>.
*)

inductive confl_class :: \<open>form list \<Rightarrow> form list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<crossmark>\<close> 50) where
  CFalse: \<open>[ F\<^bsub>o\<^esub> ] \<leadsto>\<^sub>\<crossmark> [ F\<^bsub>o\<^esub> ]\<close>
| CTrueN: \<open>[\<sim>\<^sup>\<Q> T\<^bsub>o\<^esub> ] \<leadsto>\<^sub>\<crossmark> [ \<sim>\<^sup>\<Q> T\<^bsub>o\<^esub> ]\<close>
| CNot: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> [ \<sim>\<^sup>\<Q> A ] \<leadsto>\<^sub>\<crossmark> [ A ]\<close>
| CIrr: \<open>A \<in> wffs\<^bsub>\<alpha>\<^esub> \<Longrightarrow>  [ \<sim>\<^sup>\<Q> (A =\<^bsub>\<alpha>\<^esub> A) ] \<leadsto>\<^sub>\<crossmark> [ \<sim>\<^sup>\<Q> (A =\<^bsub>\<alpha>\<^esub> A) ]\<close>

inductive alpha_class :: \<open>form list \<Rightarrow> form list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<alpha>\<close> 50) where
  CConP: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> [ A \<and>\<^sup>\<Q> B ] \<leadsto>\<^sub>\<alpha> [ A, B ]\<close>
| CImpN: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> [ \<sim>\<^sup>\<Q> (A \<supset>\<^sup>\<Q> B) ] \<leadsto>\<^sub>\<alpha> [ A, \<sim>\<^sup>\<Q> B ]\<close>
| CSym: \<open>A \<in> wffs\<^bsub>\<alpha>\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>\<alpha>\<^esub> \<Longrightarrow> [ A =\<^bsub>\<alpha>\<^esub> B ] \<leadsto>\<^sub>\<alpha> [ B =\<^bsub>\<alpha>\<^esub> A ]\<close>
| CTrans: \<open>A \<in> wffs\<^bsub>\<alpha>\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>\<alpha>\<^esub> \<Longrightarrow> [ A =\<^bsub>\<alpha>\<^esub> B, B =\<^bsub>\<alpha>\<^esub> C ] \<leadsto>\<^sub>\<alpha> [ A =\<^bsub>\<alpha>\<^esub> C ]\<close>
| CCong: \<open>A \<in> wffs\<^bsub>\<alpha>\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>\<alpha>\<^esub> \<Longrightarrow> C \<in> wffs\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> \<Longrightarrow> [ A =\<^bsub>\<alpha>\<^esub> B ] \<leadsto>\<^sub>\<alpha> [ C \<sqdot> A =\<^bsub>\<beta>\<^esub> C \<sqdot> B ]\<close>

inductive beta_class :: \<open>form list \<Rightarrow> form list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<beta>\<close> 50) where
  CConN: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> [ \<sim>\<^sup>\<Q> (A \<and>\<^sup>\<Q> B) ] \<leadsto>\<^sub>\<beta> [ \<sim>\<^sup>\<Q> A, \<sim>\<^sup>\<Q> B ]\<close>
| CImpP: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> [ A \<supset>\<^sup>\<Q> B ] \<leadsto>\<^sub>\<beta> [ \<sim>\<^sup>\<Q> A, B ]\<close>
| CEqvP: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> [ A \<equiv>\<^sup>\<Q> B ] \<leadsto>\<^sub>\<beta> [ A \<and>\<^sup>\<Q> B, \<sim>\<^sup>\<Q> A \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> B]\<close>
| CEqvN: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> [ \<sim>\<^sup>\<Q> (A \<equiv>\<^sup>\<Q> B) ] \<leadsto>\<^sub>\<beta> [ A \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> B, \<sim>\<^sup>\<Q> A \<and>\<^sup>\<Q> B]\<close>

inductive gamma_class :: \<open>form list \<Rightarrow> (form set \<Rightarrow> _) \<times> (form \<Rightarrow> _) \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<gamma>\<close> 50) where
  CExt: \<open>A \<in> wffs\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> \<Longrightarrow> [ A =\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> B ] \<leadsto>\<^sub>\<gamma> (\<lambda>_. wffs\<^bsub>\<alpha>\<^esub>, \<lambda>C. [ A \<sqdot> C =\<^bsub>\<beta>\<^esub> B \<sqdot> C ])\<close>

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

fun \<delta> :: \<open>form \<Rightarrow> nat \<Rightarrow> form list\<close> where
  CDelta: \<open>\<delta> C c =
    (if C \<in> wffs\<^bsub>o\<^esub> \<and> (\<exists>\<alpha> \<beta> A B. ineq_match C (\<alpha>, \<beta>, A, B)) then 
       case THE (\<alpha>, \<beta>, A, B). ineq_match C (\<alpha>, \<beta>, A, B) of
         (\<alpha>, \<beta>, A, B) \<Rightarrow> [ \<sim>\<^sup>\<Q> (A \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> B \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) ]
     else [])\<close>

lemma ineq_match_delta [simp]:
  assumes \<open>C \<in> wffs\<^bsub>o\<^esub>\<close> \<open>ineq_match C (\<alpha>, \<beta>, A, B)\<close>
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
    proof (cases \<open>C \<in> wffs\<^bsub>o\<^esub> \<and> (\<exists>\<alpha> \<beta> A B. ineq_match C (\<alpha>, \<beta>, A, B))\<close>)
      case True
      then obtain \<alpha> \<beta> A B where C: \<open>C = \<sim>\<^sup>\<Q> (A =\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> B)\<close>
        by fast
      then have *: \<open>\<delta> C c = [ \<sim>\<^sup>\<Q> (A \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> B \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) ]\<close>
        using True MCS.CDelta ineq_match_delta by blast
      then have *: \<open>map (map_con f) (\<delta> C c) = [ \<sim>\<^sup>\<Q> (map_con f A \<sqdot> \<lbrace>f c\<rbrace>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> map_con f B \<sqdot> \<lbrace>f c\<rbrace>\<^bsub>\<alpha>\<^esub>) ]\<close>
        using 1 c by (auto simp: is_param_def)
      have \<open>ineq_match (map_con f C) (\<alpha>, \<beta>, map_con f A, map_con f B)\<close>
        using C map_con_ineq_match by blast
      moreover have \<open>map_con f C \<in> wffs\<^bsub>o\<^esub>\<close>
        using True wff_map_con by blast
      ultimately have \<open>\<delta> (map_con f C) (f c) = [ \<sim>\<^sup>\<Q> (map_con f A \<sqdot> \<lbrace>f c\<rbrace>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> map_con f B \<sqdot> \<lbrace>f c\<rbrace>\<^bsub>\<alpha>\<^esub>) ]\<close>
        unfolding MCS.CDelta using ineq_match_delta by auto
      then show ?thesis
        using * by simp
    next
      case False
      then show ?thesis
        by auto
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
  for H :: \<open>form set\<close> +
  assumes Top: \<open>T\<^bsub>o\<^esub> \<in> H\<close>
begin

lemmas
  confl = sat\<^sub>H[of C.kind] and
  alpha = sat\<^sub>H[of A.kind] and
  beta = sat\<^sub>H[of B.kind] and
  gamma = sat\<^sub>H[of G.kind] and
  delta = sat\<^sub>H[of D.kind]

(*
  With CNot at complete formulas, not just atoms, this is free.
  Notably, this does not necessarily imply derivational consistency: \<open>\<not> (H \<turnstile> A \<and> H \<turnstile> \<sim>\<^sup>\<Q> A)\<close>
*)
theorem consistent: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> A \<notin> H \<or> \<sim>\<^sup>\<Q> A \<notin> H\<close>
  using confl by (force intro: CNot[of A])

lemma cFalse: \<open>F\<^bsub>o\<^esub> \<notin> H\<close>
  using confl by (force intro: CFalse)

lemma cTrueN: \<open>\<sim>\<^sup>\<Q> T\<^bsub>o\<^esub> \<notin> H\<close>
  using confl by (force intro: CTrueN)

lemma cIrr: \<open>A \<in> wffs\<^bsub>\<alpha>\<^esub> \<Longrightarrow> \<sim>\<^sup>\<Q> (A =\<^bsub>\<alpha>\<^esub> A) \<notin> H\<close>
  using confl by (force intro: CIrr[of A \<alpha>])

lemma cConP: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> A \<and>\<^sup>\<Q> B \<in> H \<Longrightarrow> A \<in> H \<and> B \<in> H\<close>
  using alpha by (force intro: CConP[of A B])

lemma cImpN: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> \<sim>\<^sup>\<Q> (A \<supset>\<^sup>\<Q> B) \<in> H \<Longrightarrow> A \<in> H \<and> \<sim>\<^sup>\<Q> B \<in> H\<close>
  using alpha by (force intro: CImpN[of A B])

lemma cSym: \<open>A \<in> wffs\<^bsub>\<alpha>\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>\<alpha>\<^esub> \<Longrightarrow> A =\<^bsub>\<alpha>\<^esub> B \<in> H \<Longrightarrow> B =\<^bsub>\<alpha>\<^esub> A \<in> H\<close>
  using alpha by (force intro: CSym[of A \<alpha> B])

lemma cTrans: \<open>A \<in> wffs\<^bsub>\<alpha>\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>\<alpha>\<^esub> \<Longrightarrow> A =\<^bsub>\<alpha>\<^esub> B \<in> H \<Longrightarrow> B =\<^bsub>\<alpha>\<^esub> C \<in> H \<Longrightarrow> A =\<^bsub>\<alpha>\<^esub> C \<in> H\<close>
  using alpha by (force intro: CTrans[of A \<alpha> B])

lemma cCong: \<open>A \<in> wffs\<^bsub>\<alpha>\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>\<alpha>\<^esub> \<Longrightarrow> C \<in> wffs\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> \<Longrightarrow> A =\<^bsub>\<alpha>\<^esub> B \<in> H \<Longrightarrow> C \<sqdot> A =\<^bsub>\<beta>\<^esub> C \<sqdot> B \<in> H\<close>
  using alpha by (force intro: CCong[of A \<alpha> B C \<beta>])

lemma cConN: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> \<sim>\<^sup>\<Q> (A \<and>\<^sup>\<Q> B) \<in> H \<Longrightarrow> \<sim>\<^sup>\<Q> A \<in> H \<or> \<sim>\<^sup>\<Q> B \<in> H\<close>
  using beta by (force intro: CConN[of A B])

lemma cImpP: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> A \<supset>\<^sup>\<Q> B \<in> H \<Longrightarrow> \<sim>\<^sup>\<Q> A \<in> H \<or> B \<in> H\<close>
  using beta by (force intro: CImpP[of A B])

lemma cEqvP: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> A \<equiv>\<^sup>\<Q> B \<in> H \<Longrightarrow> A \<and>\<^sup>\<Q> B \<in> H \<or> \<sim>\<^sup>\<Q> A \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> B \<in> H\<close>
  using beta by (force intro: CEqvP[of A B])

lemma cEqvN: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> \<sim>\<^sup>\<Q> (A \<equiv>\<^sup>\<Q> B) \<in> H \<Longrightarrow> A \<and>\<^sup>\<Q> \<sim>\<^sup>\<Q> B \<in> H \<or> \<sim>\<^sup>\<Q> A \<and>\<^sup>\<Q> B \<in> H\<close>
  using beta by (force intro: CEqvN[of A B])

lemma cExt: \<open>A \<in> wffs\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> \<Longrightarrow> (A =\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> B) \<in> H \<Longrightarrow> C \<in> wffs\<^bsub>\<alpha>\<^esub> \<Longrightarrow> (A \<sqdot> C =\<^bsub>\<beta>\<^esub> B \<sqdot> C) \<in> H\<close>
  using gamma by (force intro: CExt[of A \<alpha>])

lemma cIneq:
  assumes \<open>A \<in> wffs\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub>\<close> \<open>B \<in> wffs\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub>\<close> \<open>\<sim>\<^sup>\<Q> (A =\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> B) \<in> H\<close>
  shows \<open>\<exists>c. is_param c \<and> \<sim>\<^sup>\<Q> (A \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> B \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) \<in> H\<close>
proof -
  have \<open>\<sim>\<^sup>\<Q> (A =\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> B) \<in> wffs\<^bsub>o\<^esub> \<and> ineq_match (\<sim>\<^sup>\<Q> (A =\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> B)) (\<alpha>, \<beta>, A, B)\<close>
    using assms(1-2) by blast
  then have \<open>\<delta> (\<sim>\<^sup>\<Q> (A =\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> B)) c = [ \<sim>\<^sup>\<Q> (A \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> B \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) ]\<close> for c
    using ineq_match_delta by fast
  then show ?thesis
    using delta assms(3) by (metis list.set_intros(1,2) sat\<^sub>H_WitsE subset_code(1))
qed

lemma equal_parts: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> A \<equiv>\<^sup>\<Q> B \<in> H \<Longrightarrow> A \<in> H \<and> B \<in> H \<or> \<sim>\<^sup>\<Q> A \<in> H \<and> \<sim>\<^sup>\<Q> B \<in> H\<close>
  by (metis cConP cEqvP neg_wff)

(*
  This proof comes from:
  On Reductions of Hintikka Sets for Higher-Order Logic
  Alexander Steen, Christoph Benzmüller
*)
lemma complete:
  assumes \<open>A \<in> wffs\<^bsub>o\<^esub>\<close>
  shows \<open>A \<in> H \<or> \<sim>\<^sup>\<Q> A \<in> H\<close>
proof -
  have \<open>(Q\<^bsub>o\<^esub> \<sqdot> A =\<^bsub>o \<rightarrow> o\<^esub> Q\<^bsub>o\<^esub> \<sqdot> A) \<in> H\<close>
    using cExt assms Top by fastforce
  then have \<open>((A \<equiv>\<^sup>\<Q> A) =\<^bsub>o\<^esub> (A \<equiv>\<^sup>\<Q> A)) \<in> H\<close>
    using assms cExt unfolding equivalence_def equality_of_type_def
    by (meson Q_wff wffs_of_type_intros(3))
  then show ?thesis
    using assms by (metis cIrr equal_parts equality_wff equivalence_def)
qed


lemma cRefl: \<open>A \<in> wffs\<^bsub>\<alpha>\<^esub> \<Longrightarrow> A =\<^bsub>\<alpha>\<^esub> A \<in> H\<close>
  by (metis cIrr complete equality_wff)

lemma cMP: \<open>A \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> B \<in> wffs\<^bsub>o\<^esub> \<Longrightarrow> A \<in> H \<Longrightarrow> A \<supset>\<^sup>\<Q> B \<in> H \<Longrightarrow> B \<in> H\<close>
  using cImpP consistent by blast

lemma extensionally_complete_membership: \<open>extensionally_complete_membership H\<close>
  unfolding extensionally_complete_membership_def
proof safe
  fix A B \<alpha> \<beta>
  assume *: \<open>A \<in> wffs\<^bsub>\<beta> \<rightarrow> \<alpha>\<^esub>\<close> \<open>B \<in> wffs\<^bsub>\<beta> \<rightarrow> \<alpha>\<^esub>\<close>
  then consider (pos) \<open>A =\<^bsub>\<beta> \<rightarrow> \<alpha>\<^esub> B \<in> H\<close> | (neg) \<open>\<sim>\<^sup>\<Q> (A =\<^bsub>\<beta> \<rightarrow> \<alpha>\<^esub> B) \<in> H\<close>
    using complete by (meson equality_wff)
  then show \<open>\<exists>C. C \<in> wffs\<^bsub>\<beta>\<^esub> \<and> ((A \<sqdot> C =\<^bsub>\<alpha>\<^esub> B \<sqdot> C) \<supset>\<^sup>\<Q> (A =\<^bsub>\<beta> \<rightarrow> \<alpha>\<^esub> B) \<in> H)\<close>
  proof cases
    case pos
    then show ?thesis
      by (metis "*"(1,2) cImpN consistent equality_wff imp_op_wff complete wffs_of_type_intros(2,3))
  next
    case neg
    then obtain c where \<open>is_param c\<close> \<open>\<sim>\<^sup>\<Q> (A \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub> =\<^bsub>\<alpha>\<^esub> B \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub>) \<in> H\<close>
      using * cIneq by blast
    then have \<open>(A \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub> =\<^bsub>\<alpha>\<^esub> B \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub>) \<notin> H\<close>
      using consistent * by (meson equality_wff wffs_of_type_intros(2,3))
    then have \<open>A \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub> =\<^bsub>\<alpha>\<^esub> B \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub> \<in> H \<longrightarrow> A =\<^bsub>\<beta> \<rightarrow> \<alpha>\<^esub> B \<in> H\<close>
      by meson
    then show ?thesis
      by (metis "*"(1,2) \<open>A \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub> =\<^bsub>\<alpha>\<^esub> B \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub> \<notin> H\<close> cImpN equality_wff imp_op_wff complete wffs_of_type_intros(2,3))
  qed
qed


section \<open>Let us have a little looksie\<close>

definition V_of_form_set :: "form set \<Rightarrow> V" where
  "V_of_form_set As = set (V_of_form ` As)"

fun
  D :: "type \<Rightarrow> V" and 
  V :: "form \<Rightarrow> type \<Rightarrow> V" and
  get_rep :: "V \<Rightarrow> type \<Rightarrow> form" where
  "D o = \<bool>"
| "D i = set {V A i | A. A \<in> wffs\<^bsub>i\<^esub>}"
| "D (\<beta> \<rightarrow> \<alpha>) = set {V A (\<beta> \<rightarrow> \<alpha>) | A. A \<in> wffs\<^bsub>\<beta> \<rightarrow> \<alpha>\<^esub>}"
| "V A o = (if A \<in> H then \<^bold>T else \<^bold>F)"
| "V A i = V_of_form_set {B. B \<in> wffs\<^bsub>i\<^esub> \<and> A =\<^bsub>i\<^esub> B \<in> H}"
| "V A (\<beta> \<rightarrow> \<alpha>) = (\<^bold>\<lambda>VC\<beta> \<^bold>: D \<beta>\<^bold>. (let C = get_rep VC\<beta> \<beta> in V (A \<sqdot> C) \<alpha>))"
| "get_rep VC\<beta> \<beta> = (SOME C. V C \<beta> = VC\<beta> \<and> C \<in> wffs\<^bsub>\<beta>\<^esub>)"


lemma one_o: "D o = set {V A o| A. A \<in> wffs\<^bsub>o\<^esub>}"
proof -
  have \<open>{bool_to_V True, bool_to_V False} \<subseteq> {V A o |A. A \<in> wffs\<^bsub>o\<^esub>}\<close>
    using Top cFalse true_wff by auto
  moreover have \<open>{bool_to_V True, bool_to_V False} \<supseteq> {V A o |A. A \<in> wffs\<^bsub>o\<^esub>}\<close>
    by auto
  ultimately show ?thesis
    by (metis (lifting) D.simps(1) bottom_def set_eq_subset top_def
        two_valued_boolean_algebra_universe_def)
qed

lemma bool_to_V_distinct: \<open>bool_to_V False \<noteq> bool_to_V True\<close>
  by (simp add: inj_eq)

lemma two_o:
  assumes "A \<in> wffs\<^bsub>o\<^esub>" "B \<in> wffs\<^bsub>o\<^esub>"
  shows \<open>V A o = V B o \<longleftrightarrow> A \<equiv>\<^sup>\<Q> B \<in> H\<close>
  using assms consistent complete
  by (metis V.simps(1) bool_to_V_distinct bottom_def cConP cEqvN
      equal_parts equivalence_wff neg_wff top_def)


lemma one_i: "D i = set {V A i| A. A \<in> wffs\<^bsub>i\<^esub>}"
  by simp (* defined to hold *)

lemma inj_V_of_form: "inj V_of_form"
  by (metis V_of_form_def embeddable_class.ex_inj someI_ex)

lemma cool_lemma:
  assumes "V_of_form_set As = V_of_form_set Bs"
  shows "As = Bs"
proof -
  have "small (V_of_form ` As)"
    by simp
  have "small (V_of_form ` Bs)"
    by simp
  show ?thesis
    using V_of_form_set_def inj_V_of_form assms inj_image_eq_iff by fastforce
qed

lemma two_i:
  assumes "A \<in> wffs\<^bsub>i\<^esub>" "B \<in> wffs\<^bsub>i\<^esub>"
  shows "V A i = V B i \<longleftrightarrow> A =\<^bsub>i\<^esub> B \<in> H"
proof -
  have A: "small {A \<in> wffs\<^bsub>i\<^esub> . A =\<^bsub>i\<^esub> B \<in> H}"
    by (simp add: setcompr_eq_image)
  have B: "small {B \<in> wffs\<^bsub>i\<^esub> . A =\<^bsub>i\<^esub> B \<in> H}"
    by (simp add: setcompr_eq_image)

  show ?thesis
  proof
    assume \<open>V A i = V B i\<close>
    then have \<open>{B' \<in> wffs\<^bsub>i\<^esub> . A =\<^bsub>i\<^esub> B' \<in> H} = {A' \<in> wffs\<^bsub>i\<^esub> . B =\<^bsub>i\<^esub> A' \<in> H}\<close>
      using cool_lemma by simp
    then have \<open>{B' \<in> wffs\<^bsub>i\<^esub> . A =\<^bsub>i\<^esub> B' \<in> H} = {A' \<in> wffs\<^bsub>i\<^esub> . A' =\<^bsub>i\<^esub> B \<in> H}\<close>
      using assms cSym by blast
    then have \<open>\<forall>C \<in> wffs\<^bsub>i\<^esub> . A =\<^bsub>i\<^esub> C \<in> H \<longleftrightarrow> C =\<^bsub>i\<^esub> B \<in> H\<close>
      by blast
    moreover have \<open>A =\<^bsub>i\<^esub> A \<in> H\<close> \<open>B =\<^bsub>i\<^esub> B \<in> H\<close>
      using assms cRefl by blast+
    ultimately show \<open>A =\<^bsub>i\<^esub> B \<in> H\<close>
      using assms cTrans by blast
  next
    assume \<open>A =\<^bsub>i\<^esub> B \<in> H\<close>
    then have \<open>\<forall>C \<in> wffs\<^bsub>i\<^esub> . A =\<^bsub>i\<^esub> C \<in> H \<longleftrightarrow> B =\<^bsub>i\<^esub> C \<in> H\<close>
      using assms cSym cTrans by meson
    then show \<open>A =\<^bsub>i\<^esub> B \<in> H \<Longrightarrow> V A i = V B i\<close>
      using assms by (metis (mono_tags, lifting) Collect_cong V.simps(2))
  qed
qed

lemma one_fun:
  "D (\<beta> \<rightarrow> \<alpha>) = set {V A (\<beta> \<rightarrow> \<alpha>)| A. A \<in> wffs\<^bsub>\<beta> \<rightarrow> \<alpha>\<^esub>}"
  by simp (* Defined to hold *)

lemma fun_ext_vfuncset:
  assumes "f \<in> elts (A \<longmapsto> B)" "g \<in> elts (A \<longmapsto> B)" "\<And>x. x \<in> elts A \<Longrightarrow> app f x = app g x"
  shows "f = g"
  using assms ZFC_Cardinals.fun_ext by auto

lemma well_typed:
  assumes "A \<in> wffs\<^bsub>\<gamma>\<^esub>"
  shows "V A \<gamma> \<in> elts (D \<gamma>)"
  using assms
proof (induction \<gamma>)
  case TInd
  then show ?case
    apply auto
    unfolding V_of_form_set_def
    apply auto
    by (simp add: setcompr_eq_image)
next
  case TBool
  then show ?case
    by simp
next
  case (TFun \<gamma>1 \<gamma>2)
  then show ?case
    apply (subgoal_tac "small (elts (local.D (\<gamma>1 \<rightarrow> \<gamma>2))) \<and> small (elts (local.D (\<gamma>1))) \<and> small (elts (local.D (\<gamma>2)))")
    subgoal
      apply auto
      apply (simp add: setcompr_eq_image)
      done
    subgoal
      apply fastforce
      done
    done
qed

fun unambiguous :: "type \<Rightarrow> bool" where
  "unambiguous i \<longleftrightarrow> True"
| "unambiguous o \<longleftrightarrow> True"
| "unambiguous (\<beta> \<rightarrow> \<alpha>) \<longleftrightarrow> 
     (\<forall>A B C. A \<in> wffs\<^bsub>\<beta> \<rightarrow> \<alpha>\<^esub> \<longrightarrow>
              B \<in> wffs\<^bsub>\<beta>\<^esub> \<longrightarrow>
              C \<in> wffs\<^bsub>\<beta>\<^esub> \<longrightarrow> 
              V B \<beta> = V C \<beta> \<longrightarrow>
              V (A \<sqdot> B) \<alpha> = V (A \<sqdot> C) \<alpha>)"

subsection \<open>1\<gamma>\<close>

lemma one_gamma: "D \<gamma> = set {V A \<gamma>| A. A \<in> wffs\<^bsub>\<gamma>\<^esub>}"
  using one_i one_o one_fun by (cases \<gamma>) auto

lemma fun_typed: (* We could make being funtyped part of being good and make this
                    proof part of the induction.
                    Or we could extract theorems from the big proof where we, like here,
                    have the needed assumptions *)
  assumes "unambiguous (\<beta> \<rightarrow> \<alpha>)"
  shows "elts (D (\<beta> \<rightarrow> \<alpha>)) \<subseteq> elts ((D \<beta> \<longmapsto> D \<alpha>))"
proof 
  fix f
  assume f: "f \<in> elts (D (\<beta> \<rightarrow> \<alpha>))"
  have sma: "small {\<^bold>\<lambda>VC\<beta>\<^bold>:D \<beta> \<^bold>. V (A \<sqdot> (SOME C. V C \<beta> = VC\<beta> \<and> C \<in> wffs\<^bsub>\<beta>\<^esub>)) \<alpha> |A. A \<in> wffs\<^bsub>\<beta> \<rightarrow> \<alpha>\<^esub>}"
    by (simp add: setcompr_eq_image)

  from f obtain A where fp:
    "f = (\<^bold>\<lambda>VC\<beta>\<^bold>:D \<beta> \<^bold>. V (A \<sqdot> (SOME C. V C \<beta> = VC\<beta> \<and> C \<in> wffs\<^bsub>\<beta>\<^esub>)) \<alpha>)"
    "A \<in> wffs\<^bsub>\<beta> \<rightarrow> \<alpha>\<^esub>"
    using sma by auto

  {
    fix VC\<beta>
    assume "VC\<beta> \<in> elts (D \<beta>)"
    then have "\<exists>C. V C \<beta> = VC\<beta> \<and> C \<in> wffs\<^bsub>\<beta>\<^esub>"
      by (smt (verit, best) elts_of_set emptyE mem_Collect_eq one_gamma)
    then obtain C where
      "V C \<beta> = VC\<beta>"
      "C \<in> wffs\<^bsub>\<beta>\<^esub>"
      by blast
    have "V (A \<sqdot> (SOME C. V C \<beta> = VC\<beta> \<and> C \<in> wffs\<^bsub>\<beta>\<^esub>)) \<alpha> \<in> elts (D \<alpha>)"
      by (metis (mono_tags, lifting) \<open>\<exists>C. V C \<beta> = VC\<beta> \<and> C \<in> wffs\<^bsub>\<beta>\<^esub>\<close> fp(2) someI well_typed wffs_of_type_intros(3))
  }
  then
  show "f \<in> elts (D \<beta> \<longmapsto> D \<alpha>)"
    unfolding fp(1) is_closed_wff_of_type_def
    apply (rule VPi_I[of "(D \<beta>)" "\<lambda>x. _ x" "(\<lambda>_. D \<alpha>)"])
    .
qed

subsection \<open>2\<gamma>\<close>

definition two_gamma :: "type \<Rightarrow> bool" where
  "two_gamma \<gamma> \<longleftrightarrow>
    (\<forall>A B. A \<in> wffs\<^bsub>\<gamma>\<^esub> \<longrightarrow> B \<in> wffs\<^bsub>\<gamma>\<^esub> \<longrightarrow>
           V A \<gamma> = V B \<gamma> \<longleftrightarrow> A =\<^bsub>\<gamma>\<^esub> B \<in> H)"

definition good_type :: "type \<Rightarrow> bool" where
  "good_type \<gamma> \<longleftrightarrow> two_gamma \<gamma> \<and> unambiguous \<gamma>"

lemma all_good: "good_type \<gamma>"
proof (induction \<gamma>)
  case TInd
  then show ?case
    using good_type_def two_gamma_def two_i unambiguous.simps(1) by blast
next
  case TBool
  then show ?case
    using good_type_def two_gamma_def two_o unambiguous.simps(2) by simp
next
  case (TFun \<beta> \<alpha>)

  {
    fix A B C
    assume "A \<in> wffs\<^bsub>(\<beta> \<rightarrow> \<alpha>)\<^esub>"
      "B \<in> wffs\<^bsub>\<beta>\<^esub>"
      "C \<in> wffs\<^bsub>\<beta>\<^esub>"
      "V B \<beta> = V C \<beta>"
    then have "V (A \<sqdot> B) \<alpha> = V (A \<sqdot> C) \<alpha>"
      using cCong TFun.IH(1,2) good_type_def two_gamma_def wffs_of_type_intros(3) by meson
    (* Sledgehammer could do it... But we could maybe write Andrew's short proof out and only
       Sledgehammer the intermediate steps. *)
  }
  then have una: "unambiguous (\<beta> \<rightarrow> \<alpha>)"
    unfolding unambiguous.simps by metis

  {
    fix A B
    assume "A \<in> wffs\<^bsub>(\<beta> \<rightarrow> \<alpha>)\<^esub>"
    assume "B \<in> wffs\<^bsub>(\<beta> \<rightarrow> \<alpha>)\<^esub>"
    have "local.V A (\<beta> \<rightarrow> \<alpha>) = local.V B (\<beta> \<rightarrow> \<alpha>) \<longleftrightarrow> A =\<^bsub>\<beta> \<rightarrow> \<alpha>\<^esub> B \<in> H"
    proof
      assume "A =\<^bsub>\<beta> \<rightarrow> \<alpha>\<^esub> B \<in> H"
      then have nice: "\<And>C. C \<in> wffs\<^bsub>\<beta>\<^esub> \<Longrightarrow> A \<sqdot> C =\<^bsub>\<alpha>\<^esub> B \<sqdot> C \<in> H"
        using \<open>A \<in> wffs\<^bsub>\<beta> \<rightarrow> \<alpha>\<^esub>\<close> \<open>B \<in> wffs\<^bsub>\<beta> \<rightarrow> \<alpha>\<^esub>\<close> cExt by blast
      {
        fix C
        assume "C \<in> wffs\<^bsub>\<beta>\<^esub>"
        have "(V A (\<beta> \<rightarrow> \<alpha>)) \<bullet> (V C \<beta>) = V (A \<sqdot> C) \<alpha>"
          apply auto
          apply (subgoal_tac "V C \<beta> \<in> elts (D \<beta>)") 
          subgoal
            apply auto
            unfolding is_closed_wff_of_type_def[symmetric]
            unfolding get_rep.simps[symmetric]
            apply (subgoal_tac "V (get_rep (V C \<beta>) \<beta>) \<beta> = V C \<beta>")
            subgoal
              apply -
              apply auto
              apply (smt (verit, ccfv_threshold) \<open>A \<in> wffs\<^bsub>(\<beta> \<rightarrow> \<alpha>)\<^esub>\<close> \<open>C \<in> wffs\<^bsub>\<beta>\<^esub>\<close> \<open>local.unambiguous (\<beta> \<rightarrow> \<alpha>)\<close>
                  is_closed_wff_of_type_def some_eq_ex unambiguous.simps(3))
              done
            subgoal
              apply (metis (mono_tags, lifting) \<open>C \<in> wffs\<^bsub>\<beta>\<^esub>\<close> get_rep.simps verit_sko_ex')
              done
            done
          subgoal
            using \<open>C \<in> wffs\<^bsub>\<beta>\<^esub>\<close> well_typed apply auto
            done
          done
        also have "... = V (B \<sqdot> C) \<alpha>"
          using nice[OF \<open>C \<in> wffs\<^bsub>\<beta>\<^esub>\<close>] TFun(2) unfolding good_type_def
          using \<open>A \<in> wffs\<^bsub>(\<beta> \<rightarrow> \<alpha>)\<^esub>\<close> \<open>B \<in> wffs\<^bsub>(\<beta> \<rightarrow> \<alpha>)\<^esub>\<close> \<open>C \<in> wffs\<^bsub>\<beta>\<^esub>\<close>
          by (simp add: two_gamma_def wffs_of_type_intros(3))
        also have "... = (V B (\<beta> \<rightarrow> \<alpha>)) \<bullet> (V C \<beta>)"
          (* Copy paste of the argument from first equality in this chain *)
          apply auto
          apply (subgoal_tac "V C \<beta> \<in> elts (D \<beta>)") 
          subgoal
            apply auto
            unfolding is_closed_wff_of_type_def[symmetric]
            unfolding get_rep.simps[symmetric]
            apply (subgoal_tac "V (get_rep (V C \<beta>) \<beta>) \<beta> = V C \<beta>")
            subgoal
              apply -
              apply auto
              apply (smt (verit, ccfv_threshold) \<open>B \<in> wffs\<^bsub>(\<beta> \<rightarrow> \<alpha>)\<^esub>\<close> \<open>C \<in> wffs\<^bsub>\<beta>\<^esub>\<close> \<open>local.unambiguous (\<beta> \<rightarrow> \<alpha>)\<close>
                  is_closed_wff_of_type_def some_eq_ex unambiguous.simps(3))
              done
            subgoal
              apply (metis (mono_tags, lifting) \<open>C \<in> wffs\<^bsub>\<beta>\<^esub>\<close> get_rep.simps verit_sko_ex')
              done
            done
          subgoal
            using \<open>C \<in> wffs\<^bsub>\<beta>\<^esub>\<close> well_typed apply auto
            done
          done
        finally have "(V A (\<beta> \<rightarrow> \<alpha>)) \<bullet> (V C \<beta>) = (V B (\<beta> \<rightarrow> \<alpha>)) \<bullet> (V C \<beta>)"
          .
      }
      note C_application = this

      show "V A (\<beta> \<rightarrow> \<alpha>) = V B (\<beta> \<rightarrow> \<alpha>)"
      proof (rule fun_ext_vfuncset[of _ "D \<beta>" "D \<alpha>"])
        show "V A (\<beta> \<rightarrow> \<alpha>) \<in> elts (D \<beta> \<longmapsto> D \<alpha>)"
          using fun_typed well_typed \<open>A \<in> wffs\<^bsub>(\<beta> \<rightarrow> \<alpha>)\<^esub>\<close> una by (metis subsetD)
      next
        show "V B (\<beta> \<rightarrow> \<alpha>) \<in> elts (D \<beta> \<longmapsto> D \<alpha>)"
          using fun_typed well_typed \<open>B \<in> wffs\<^bsub>(\<beta> \<rightarrow> \<alpha>)\<^esub>\<close> una by (metis subsetD)
      next 
        fix VC\<beta>
        assume "VC\<beta> \<in> elts (D \<beta>)"
        then obtain C where "V C \<beta> = VC\<beta> \<and> C \<in> wffs\<^bsub>\<beta>\<^esub>"
          by (smt (verit) one_gamma elts_of_set emptyE mem_Collect_eq)
        then show "V A (\<beta> \<rightarrow> \<alpha>) \<bullet> VC\<beta> = V B (\<beta> \<rightarrow> \<alpha>) \<bullet> VC\<beta>"
          using C_application by blast
      qed
    next
      assume "V A (\<beta> \<rightarrow> \<alpha>) = V B (\<beta> \<rightarrow> \<alpha>)"
      {
        fix C
        assume "C \<in> wffs\<^bsub>\<beta>\<^esub>"
        assume "((A \<sqdot> C) =\<^bsub>\<alpha>\<^esub> (B \<sqdot> C)) \<supset>\<^sup>\<Q> (A =\<^bsub>\<beta> \<rightarrow> \<alpha>\<^esub> B) \<in> H"
        have "V (A \<sqdot> C) \<alpha> = (V A (\<beta> \<rightarrow> \<alpha>)) \<bullet> (V C \<beta>)"
          apply auto (* proof copy pasted from above *)
          apply (subgoal_tac "V C \<beta> \<in> elts (D \<beta>)") 
          subgoal
            apply auto
            unfolding is_closed_wff_of_type_def[symmetric]
            unfolding get_rep.simps[symmetric]
            apply (subgoal_tac "V (get_rep (V C \<beta>) \<beta>) \<beta> = V C \<beta>")
            subgoal
              apply -
              apply auto
              apply (smt (verit, ccfv_threshold) \<open>A \<in> wffs\<^bsub>(\<beta> \<rightarrow> \<alpha>)\<^esub>\<close> \<open>C \<in> wffs\<^bsub>\<beta>\<^esub>\<close> \<open>local.unambiguous (\<beta> \<rightarrow> \<alpha>)\<close>
                  is_closed_wff_of_type_def some_eq_ex unambiguous.simps(3))
              done
            subgoal
              apply (metis (mono_tags, lifting) \<open>C \<in> wffs\<^bsub>\<beta>\<^esub>\<close> get_rep.simps verit_sko_ex')
              done
            done
          subgoal
            using \<open>C \<in> wffs\<^bsub>\<beta>\<^esub>\<close> well_typed apply auto
            done
          done
        also have "... = (V B (\<beta> \<rightarrow> \<alpha>)) \<bullet> (V C \<beta>)"
          using \<open>V A (\<beta> \<rightarrow> \<alpha>) = V B (\<beta> \<rightarrow> \<alpha>)\<close> by presburger
        also have "... = V (B \<sqdot> C) \<alpha>"
            (* Copy paste of the argument from first equality in this chain *)
          apply auto
          apply (subgoal_tac "V C \<beta> \<in> elts (D \<beta>)") 
          subgoal
            apply auto
            unfolding get_rep.simps[symmetric]
            apply (subgoal_tac "V (get_rep (V C \<beta>) \<beta>) \<beta> = V C \<beta>")
            subgoal
              apply -
              apply auto
              apply (smt (verit, ccfv_threshold) \<open>B \<in> wffs\<^bsub>(\<beta> \<rightarrow> \<alpha>)\<^esub>\<close> \<open>C \<in> wffs\<^bsub>\<beta>\<^esub>\<close> \<open>local.unambiguous (\<beta> \<rightarrow> \<alpha>)\<close>
                  is_closed_wff_of_type_def some_eq_ex unambiguous.simps(3))
              done
            subgoal
              apply (metis (mono_tags, lifting) \<open>C \<in> wffs\<^bsub>\<beta>\<^esub>\<close> get_rep.simps verit_sko_ex')
              done
            done
          subgoal
            using \<open>C \<in> wffs\<^bsub>\<beta>\<^esub>\<close> well_typed apply auto
            done
          done
        finally have "V (A \<sqdot> C) \<alpha> = V (B \<sqdot> C) \<alpha>"
          .
        then have "A \<sqdot> C =\<^bsub>\<alpha>\<^esub> B \<sqdot> C \<in> H"
          using TFun.IH(2) \<open>A \<in> wffs\<^bsub>(\<beta> \<rightarrow> \<alpha>)\<^esub>\<close>
            \<open>B \<in> wffs\<^bsub>(\<beta> \<rightarrow> \<alpha>)\<^esub>\<close> \<open>C \<in> wffs\<^bsub>\<beta>\<^esub>\<close>
            good_type_def two_gamma_def wffs_of_type_intros(3) by force
      }
      then show "A =\<^bsub>\<beta> \<rightarrow> \<alpha>\<^esub> B \<in> H"
        using \<open>A \<in> wffs\<^bsub>(\<beta> \<rightarrow> \<alpha>)\<^esub>\<close> \<open>B \<in> wffs\<^bsub>(\<beta> \<rightarrow> \<alpha>)\<^esub>\<close> cMP extensionally_complete_membership
        unfolding extensionally_complete_membership_def
        by (smt (verit, ccfv_SIG) equality_wff wffs_of_type_intros(3)) (* TODO: smt *)
    qed
  }
  then have "two_gamma (\<beta> \<rightarrow> \<alpha>)"
    unfolding two_gamma_def by auto

  then show ?case
    unfolding good_type_def using una by metis
qed

lemma two_fun:
  assumes "A \<in> wffs\<^bsub>(\<beta> \<rightarrow> \<alpha>)\<^esub>"
  assumes "B \<in> wffs\<^bsub>(\<beta> \<rightarrow> \<alpha>)\<^esub>"
  shows "V A (\<beta> \<rightarrow> \<alpha>) = V B (\<beta> \<rightarrow> \<alpha>) \<longleftrightarrow> A =\<^bsub>\<beta> \<rightarrow> \<alpha>\<^esub> B \<in> H"
  using all_good assms(1,2) good_type_def two_gamma_def by presburger

lemma two_gamma:
  assumes "A \<in> wffs\<^bsub>\<gamma>\<^esub>"
  assumes "B \<in> wffs\<^bsub>\<gamma>\<^esub>"
  shows "V A \<gamma> = V B \<gamma> \<longleftrightarrow> A =\<^bsub>\<gamma>\<^esub> B \<in> H"
  using all_good assms(1,2) good_type_def two_gamma_def by presburger


subsection \<open>M is interpretation\<close>

fun J :: "nat \<times> Syntax.type \<Rightarrow> V" where 
  "J (c,\<tau>) = V (FCon (c,\<tau>)) \<tau>"


find_consts \<open>V \<Rightarrow> V \<Rightarrow> V\<close>

(* Mapping primitive constants into D\<^sub>\<alpha>*)
lemma non_logical_constant_denotation_V: 
  "\<not> is_logical_constant (c, \<alpha>) \<Longrightarrow> V (FCon (c, \<alpha>)) \<alpha> \<in> elts (D \<alpha>)"
  using well_typed by blast
  (* I did sledgehammer instead of looking at Andrews's proof *)

lemma non_logical_constant_denotation_J: 
  "\<not> is_logical_constant (c, \<alpha>) \<Longrightarrow> J (c, \<alpha>) \<in> elts (D \<alpha>)"
  using non_logical_constant_denotation_V unfolding J.simps by auto

(* I cannot find this in the book's proof. Too obvious maybe? *)
lemma function_domain: "D (\<alpha> \<rightarrow> \<beta>) \<le> D \<alpha> \<longmapsto> D \<beta>"
  using all_good fun_typed good_type_def by blast

(* I cannot find this in the book's proof. Too obvious maybe? *)
lemma domain_nonemptiness: "D \<alpha> \<noteq> 0"
  by (metis all_not_in_conv elts_0 well_typed wffs_of_type_simps)

lemma domain_frame: \<open>frame D\<close>
  using D.simps(1) domain_nonemptiness frame.intro function_domain by blast

lemma distrib_V_app:
  assumes "A \<in> wffs\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub>" "B \<in> wffs\<^bsub>\<alpha>\<^esub>"
  shows \<open>V (A \<sqdot> B) \<beta> = V A (\<alpha> \<rightarrow> \<beta>) \<bullet> V B \<alpha>\<close>
  using assms apply simp (* TODO: nasty *)
  by (smt (verit, del_insts) ZFC_Cardinals.beta all_good good_type_def someI_ex
      unambiguous.simps(3) well_typed)


lemma Q_denotation_V_ish:
  assumes A: "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and B: "B \<in> wffs\<^bsub>\<alpha>\<^esub>"
  shows "V (Q\<^bsub>\<alpha>\<^esub>) (\<alpha>\<rightarrow>\<alpha>\<rightarrow>o) \<bullet> V A \<alpha> \<bullet> V B \<alpha> = (q\<^bsub>\<alpha>\<^esub>\<^bsup>D\<^esup>) \<bullet> V A \<alpha> \<bullet> V B \<alpha>"
proof -
  have \<open>V A \<alpha> = V B \<alpha> \<longleftrightarrow> A =\<^bsub>\<alpha>\<^esub> B \<in> H\<close>
    using assms two_gamma by blast
  also have \<open>\<dots> \<longleftrightarrow> V (Q\<^bsub>\<alpha>\<^esub> \<sqdot> A \<sqdot> B) o = \<^bold>T\<close>
    by (simp add: bool_to_V_distinct)
  also have \<open>\<dots> \<longleftrightarrow> V (Q\<^bsub>\<alpha>\<^esub>) (\<alpha>\<rightarrow>\<alpha>\<rightarrow>o) \<bullet> V A \<alpha> \<bullet> V B \<alpha> = \<^bold>T\<close>
    using distrib_V_app A B by (metis Q_wff wffs_of_type_intros(3))
  finally have \<open>V (Q\<^bsub>\<alpha>\<^esub>) (\<alpha>\<rightarrow>\<alpha>\<rightarrow>o) \<bullet> V A \<alpha> \<bullet> V B \<alpha> = \<^bold>T \<longleftrightarrow> V A \<alpha> = V B \<alpha>\<close>
    ..
  moreover have \<open>V A \<alpha> \<in> elts (D \<alpha>)\<close> \<open>V B \<alpha> \<in> elts (D \<alpha>)\<close>
    using A B well_typed by blast+
  ultimately show ?thesis
    using domain_frame frame.identity_relation_def frame.one_element_function_def by fastforce
qed

(* Q is identity relation*)
lemma Q_denotation_V: "V (Q\<^bsub>\<alpha>\<^esub>) (\<alpha>\<rightarrow>\<alpha>\<rightarrow>o) = q\<^bsub>\<alpha>\<^esub>\<^bsup>D\<^esup>"
  sorry

lemma Q_denotation_J: "J (Q_constant_of_type \<alpha>) = q\<^bsub>\<alpha>\<^esub>\<^bsup>D\<^esup>"
  using Q_denotation_V by auto


(* \<iota> is one element set*)
lemma \<iota>_denotation_V: "frame.is_unique_member_selector D (V \<iota> ((i\<rightarrow>o)\<rightarrow>i))"
  sorry

lemma \<iota>_denotation_J: "frame.is_unique_member_selector D (J iota_constant)"
  by (metis J.simps \<iota>_denotation_V iota_constant_def iota_def)


(* M constitutes an interpretation (premodel) *)
interpretation premodel D J
  apply unfold_locales
  using function_domain domain_nonemptiness Q_denotation_J \<iota>_denotation_J 
    non_logical_constant_denotation_J apply auto
  done

subsection \<open>M is general model\<close>

definition fun_E :: "(var \<Rightarrow> V) \<Rightarrow> (var \<Rightarrow> form)" where
  "fun_E \<phi> = (\<lambda>(x,\<delta>). (SOME A. \<phi> (x,\<delta>) = V A \<delta> \<and> A \<in> wffs\<^bsub>\<delta>\<^esub>))" 
  (* Andrews asks for "the first formula such that". But I think SOME formula is sufficient. *)

definition map_E :: "var set \<Rightarrow> (var \<Rightarrow> V) \<Rightarrow> (var \<rightharpoonup> form)" where
  "map_E xs \<phi> = map_restrict_set xs (Some \<circ> (fun_E \<phi>))"

definition subst_E :: "var set \<Rightarrow> (var \<Rightarrow> V) \<Rightarrow> substitution" where
  "subst_E xs \<phi> = Abs_fmap (map_E xs \<phi>)"

definition \<theta>\<^sub>E :: "(var \<Rightarrow> V) \<Rightarrow> form \<Rightarrow> substitution" where
  "\<theta>\<^sub>E \<phi> C = subst_E (free_vars C) \<phi>"

definition C\<phi> :: "form \<Rightarrow> (var \<Rightarrow> V) \<Rightarrow> form" where
  "C\<phi> C \<phi> = \<^bold>S (\<theta>\<^sub>E \<phi> C) C"

definition type_of :: "form \<Rightarrow> type" where
  "type_of A = (SOME \<gamma>. A \<in> wffs\<^bsub>\<gamma>\<^esub>)"

lemma "A \<in> wffs\<^bsub>\<gamma>\<^esub> \<Longrightarrow> type_of A = \<gamma>"
  using type_of_def wff_has_unique_type by auto

definition V\<phi> :: "(var \<Rightarrow> V) \<Rightarrow> form \<Rightarrow> V" where
  "V\<phi> \<phi> C = V (C\<phi> C \<phi>) (type_of C)"


end

section \<open>Uhh\<close>

theorem extension_lemma:
  fixes S :: \<open>form set\<close>
  assumes \<open>P.prop\<^sub>E Kinds C\<close>
    and \<open>S \<in> C\<close>
    and \<open>P.enough_new S\<close>
    and \<open>T\<^bsub>o\<^esub> \<in> S\<close>
    and \<open>A \<in> wffs\<^bsub>o\<^esub>\<close>
  shows \<open>(A \<in> (mk_mcs C S) \<or> \<sim>\<^sup>\<Q> A \<in> (mk_mcs C S)) \<and> extensionally_complete_membership (mk_mcs C S)\<close>
proof -
  have *: \<open>MyHintikka (mk_mcs C S)\<close>
  proof
    show \<open>P.prop\<^sub>H Kinds (mk_mcs C S)\<close>
      using mk_mcs_Hintikka[OF assms(1-3)] Hintikka.hintikka by blast
  next
    show \<open>T\<^bsub>o\<^esub> \<in> mk_mcs C S\<close>
      using assms(4) Extend_subset by blast
  qed
  moreover have \<open>T\<^bsub>o\<^esub> \<in> mk_mcs C S\<close>
    using assms(4) Extend_subset by blast
  ultimately show ?thesis
    using MyHintikka.complete MyHintikka.extensionally_complete_membership assms(5)
    by blast
qed

section \<open>Derivational Consistency\<close>

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
    case CTrueN
    then have \<open>\<sim>\<^sup>\<Q> T\<^bsub>o\<^esub> \<in> H\<close>
      using * by simp
    then show ?thesis
      using dv_hyp
      by (metis equality_of_type_def false_wff is_consistent_set_def is_inconsistent_set_def neg_def prop_5219_2)
  next
    case (CNot A)
    then show ?thesis
    proof safe
      assume H: \<open>H \<subseteq> wffs\<^bsub>o\<^esub>\<close> \<open>finite H\<close>
      from CNot have \<open>\<sim>\<^sup>\<Q> A \<in> H\<close> \<open>A \<in> H\<close>
        using * by simp_all
      then have \<open>H \<turnstile> \<sim>\<^sup>\<Q> A\<close> \<open>H \<turnstile> A\<close>
        using dv_hyp H by blast+
      then show \<open>H \<turnstile> F\<^bsub>o\<^esub>\<close>
        using H by (metis equality_of_type_def equivalence_def neg_def prop_5201_1 prop_5201_2)
    qed
  next
    case (CIrr A \<alpha>)
    then show ?thesis
    proof safe
      assume H: \<open>H \<subseteq> wffs\<^bsub>o\<^esub>\<close> \<open>finite H\<close>
      with CIrr have \<open>H \<turnstile> \<sim>\<^sup>\<Q> (A =\<^bsub>\<alpha>\<^esub> A)\<close>
        by (metis "*"(1) dv_hyp insert_subset list.simps(15))
      then have \<open>H \<turnstile> \<sim>\<^sup>\<Q> (A =\<^bsub>\<alpha>\<^esub> A)\<close>
        by auto
      then show \<open>H \<turnstile> F\<^bsub>o\<^esub>\<close>
        by (metis H(1,2) equality_of_type_def equivalence_def hyp_prop_5200 local.CIrr(3) neg_def prop_5201_1 prop_5201_2)
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
  next
    case (CSym A \<alpha> B)
    then show ?thesis
      using consistent by force
  next
    case (CTrans A \<alpha> B C)
    then show ?thesis
      using consistent
      by (metis comp_apply equality_wff insert_subset is_consistent_set_def le_sup_iff
          list.simps(15) sub subset_trans wffs_from_equality(2))
  next
    case (CCong A \<alpha> B C \<beta>)
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
  next
    case (CSym A \<alpha> B)
    then show ?thesis sorry
  next
    case (CTrans A \<alpha> B C)
    then show ?thesis sorry
  next
    case (CCong A \<alpha> B C \<beta>)
    then show ?thesis sorry
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
    then show ?thesis sorry
  next
    case (CImpP A B)
    then show ?thesis sorry
  next
    case (CEqvP A B)
    then show ?thesis sorry
  next
    case (CEqvN A B)
    then show ?thesis sorry
  qed
qed



end
