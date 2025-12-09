theory Completeness imports
    Consistency
begin

section \<open>5500 Extension lemma\<close>

definition consistent :: "form set \<Rightarrow> bool" where
  "consistent G \<longleftrightarrow> \<not>is_inconsistent_set G"

definition sentence_set :: "form set \<Rightarrow> bool" where
  "sentence_set G \<longleftrightarrow> (\<forall>F \<in> G. is_sentence F)"

definition complete :: "form set \<Rightarrow> bool" where
  "complete H = (\<forall>A. is_sentence A \<longrightarrow> (H \<turnstile> A \<or> H \<turnstile> \<sim>\<^sup>\<Q> A))"

definition extensionally_complete :: "form set \<Rightarrow> bool" where
  "extensionally_complete H \<longleftrightarrow>
    (\<forall>A B \<alpha> \<beta>. is_closed_wff_of_type A (\<beta> \<rightarrow> \<alpha>) \<longrightarrow>
               is_closed_wff_of_type B (\<beta> \<rightarrow> \<alpha>) \<longrightarrow>
               (\<exists>C. is_closed_wff_of_type C \<beta> \<and>
                    H \<turnstile> ((A \<sqdot> C) =\<^bsub>\<alpha>\<^esub> (B \<sqdot> C)) \<supset>\<^sup>\<Q> (A =\<^bsub>\<beta> \<rightarrow> \<alpha>\<^esub> B)))"

term Card \<comment> \<open>WARNING: We are missing the cardinality thing, i.e. property (5) of the lemma. Can we use something the library that contains Card?\<close>
lemma extension_lemma:
  assumes "consistent G"
  assumes "sentence_set G"
  obtains H where
    "sentence_set H"
    "G \<subseteq> H"
    "consistent H"
    "complete H"
    "extensionally_complete H"
  sorry

(* Definition capturing extension lemma properties *)
(* WARNING: We are missing the cardinality thing, i.e. property (5) of the lemma *)
definition is_H_extension_of :: "form set \<Rightarrow> form set \<Rightarrow> bool" where
  "is_H_extension_of H G \<longleftrightarrow>
    sentence_set H \<and>
    G \<subseteq> H \<and>
    consistent H \<and>
    complete H \<and>
    extensionally_complete H"

lemma extension_lemma2: 
  assumes "consistent G"
  assumes "sentence_set G"
  obtains H where "is_H_extension_of H G"
  by (meson assms extension_lemma is_H_extension_of_def)


section \<open>5501 Henkin's theorem\<close>

term Card \<comment> \<open>WARNING: We are missing the cardinality thing, i.e. property (5) of the lemma. Can we use something the library that contains Card
                       Clearly the definition should not say "undefined"\<close>

definition frugal_model :: "(Syntax.type \<Rightarrow> V) \<Rightarrow> (nat \<times> Syntax.type \<Rightarrow> V) \<Rightarrow> ((nat \<times> Syntax.type \<Rightarrow> V) \<Rightarrow> form \<Rightarrow> V) \<Rightarrow> bool" where
  "frugal_model D J V \<longleftrightarrow> general_model D J V \<and> undefined D J V"

definition is_frugal_model :: "model_structure \<Rightarrow> bool" where
  "is_frugal_model \<M> \<equiv> case \<M> of (\<D>, \<J>, \<V>) \<Rightarrow> frugal_model \<D> \<J> \<V>"


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

(* Do we need to align this with bool_to_V???? *)

context
  fixes G :: "form set"
  fixes H :: "form set"
  assumes "consistent G"
  assumes "is_H_extension_of H G"
begin

definition V_of_form_set :: "form set \<Rightarrow> V" where
  "V_of_form_set As = set (V_of_form ` As)"

(* Preconditions:
   * In "V A \<gamma>" A has type \<gamma>
   * In V A o, formula A is a sentence
   * More???
*)
fun
  D :: "type \<Rightarrow> V" and 
  V :: "form \<Rightarrow> type \<Rightarrow> V" and
  get_rep :: "V \<Rightarrow> type \<Rightarrow> form" where
  "D o = \<bool>"
| "D i = set {V A i | A. is_closed_wff_of_type A i}"
| "D (\<beta> \<rightarrow> \<alpha>) = set {V A (\<beta> \<rightarrow> \<alpha>) | A. is_closed_wff_of_type A (\<beta> \<rightarrow> \<alpha>)}"
| "V A o = (if (H \<turnstile> A) then \<^bold>T else \<^bold>F)"
| "V A i = V_of_form_set {B. is_closed_wff_of_type B i \<and> H \<turnstile> A =\<^bsub>i\<^esub> B}"
| "V A (\<beta> \<rightarrow> \<alpha>) = (\<^bold>\<lambda>VC\<beta> \<^bold>: D \<beta>\<^bold>. (let C = get_rep VC\<beta> \<beta> in V (A \<sqdot> C) \<alpha>))"
| "get_rep VC\<beta> \<beta> = (SOME C. V C \<beta> = VC\<beta> \<and> is_closed_wff_of_type C \<beta>)"
     (* Arguably in Andrews it is a bit unclear if the C in get_rep should be closed, but surely
        that is the case? *)

lemma one_o: "D o = set {V A o| A. is_closed_wff_of_type A o}"
proof -
  have "{bool_to_V True, bool_to_V False} =
     {uu. \<exists>A. (H \<turnstile> A \<longrightarrow> uu = bool_to_V True \<and> A \<in> wffs\<^bsub>o\<^esub> \<and> free_vars A = {}) \<and> (\<not> H \<turnstile> A \<longrightarrow> uu = bool_to_V False \<and> A \<in> wffs\<^bsub>o\<^esub> \<and> free_vars A = {})}"
    apply auto
    apply (metis Completeness.complete_def F_fv T_fv \<open>is_H_extension_of H G\<close> equality_of_type_def false_wff is_H_extension_of_def is_closed_wff_of_type_def
        is_sentence_def neg_def prop_5219_2 true_wff)
    using F_fv \<open>is_H_extension_of H G\<close> consistent_def is_H_extension_of_def by blast
  then show ?thesis
    by auto
qed

lemma two_o:
  assumes "is_closed_wff_of_type A o"
  assumes "is_closed_wff_of_type B o"
  shows "V A o = V B o \<longleftrightarrow> H \<turnstile> A =\<^bsub>o\<^esub> B"
proof -
  show ?thesis
    apply auto
         apply (metis Q_constant_of_type_def Q_def equality_of_type_def hyp_derivable_form_is_wffso prop_5201_3 prop_5219_1 prop_5219_2)
        apply (metis bool_to_V_injectivity inv_f_f)
       apply (metis Q_constant_of_type_def Q_def equality_of_type_def equivalence_def prop_5201_1)
      apply (metis bool_to_V_injectivity inv_f_f)
     apply (metis Q_constant_of_type_def Q_def equality_of_type_def equivalence_def prop_5201_1 prop_5201_2)
    apply (metis Completeness.complete_def Q_constant_of_type_def Q_def \<open>is_H_extension_of H G\<close> assms(1,2) equality_of_type_def is_H_extension_of_def is_sentence_def
        neg_def prop_5201_2 prop_5201_3)
    done
qed

lemma one_i: "D i = set {V A i| A. is_closed_wff_of_type A i}"
proof -
  show ?thesis
    by auto (* defined to hold *)
qed

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
  assumes "is_closed_wff_of_type A i"
  assumes "is_closed_wff_of_type B i"
  shows "V A i = V B i \<longleftrightarrow> H \<turnstile> A =\<^bsub>i\<^esub> B"
proof -
  have "small {B \<in> (wffs\<^bsub>i\<^esub>). free_vars B = {} \<and> H \<turnstile> \<lbrace>Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))\<rbrace>\<^bsub>i \<rightarrow> i \<rightarrow> o\<^esub> \<sqdot> A \<sqdot> B}"
    by (simp add: setcompr_eq_image)
  have "small {Ba \<in> (wffs\<^bsub>i\<^esub>). free_vars Ba = {} \<and> H \<turnstile> \<lbrace>Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))\<rbrace>\<^bsub>i \<rightarrow> i \<rightarrow> o\<^esub> \<sqdot> B \<sqdot> Ba}"
    by (simp add: setcompr_eq_image)
  show ?thesis
    apply auto
    subgoal
      apply (subgoal_tac 
          "{B \<in> (wffs\<^bsub>i\<^esub>). free_vars B = {} \<and> H \<turnstile> \<lbrace>Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))\<rbrace>\<^bsub>i \<rightarrow> i \<rightarrow> o\<^esub> \<sqdot> A \<sqdot> B} =
         {Ba \<in> (wffs\<^bsub>i\<^esub>). free_vars Ba = {} \<and> H \<turnstile> \<lbrace>Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))\<rbrace>\<^bsub>i \<rightarrow> i \<rightarrow> o\<^esub> \<sqdot> B \<sqdot> Ba}")
       apply (metis (mono_tags, lifting) CollectD CollectI F_fv Q_constant_of_type_def Q_def assms(1) equality_of_type_def false_wff
          hyp_derivability_implies_hyp_proof_existence hyp_prop_5200 is_closed_wff_of_type_def is_hyp_proof_of_def prop_5201_2 two_o)
      using cool_lemma apply auto
      done
    subgoal
      apply (metis Q_constant_of_type_def Q_def equality_of_type_def prop_5201_2 prop_5201_3)
      done
    done
qed

lemma one_fun:
  "D (\<beta> \<rightarrow> \<alpha>) = set {V A (\<beta> \<rightarrow> \<alpha>)| A. is_closed_wff_of_type A (\<beta> \<rightarrow> \<alpha>)}"
  by auto (* Defined to hold *)

lemma fun_ext_vfuncset:
  assumes "f \<in> elts (A \<longmapsto> B)" "g \<in> elts (A \<longmapsto> B)" "\<And>x. x \<in> elts A \<Longrightarrow> app f x = app g x"
  shows "f = g"
  using assms ZFC_Cardinals.fun_ext by auto

lemma well_typed:
  assumes "is_closed_wff_of_type A \<gamma>"
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
     (\<forall>A B C. is_closed_wff_of_type A (\<beta> \<rightarrow> \<alpha>) \<longrightarrow>
              is_closed_wff_of_type B \<beta> \<longrightarrow>
              is_closed_wff_of_type C \<beta> \<longrightarrow> 
              V B \<beta> = V C \<beta> \<longrightarrow>
              V (A \<sqdot> B) \<alpha> = V (A \<sqdot> C) \<alpha>)"


subsection \<open>1\<gamma>\<close>

lemma one_gamma: "D \<gamma> = set {V A \<gamma>| A. is_closed_wff_of_type A \<gamma>}"
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
  have sma: "small {\<^bold>\<lambda>VC\<beta>\<^bold>:D \<beta> \<^bold>. V (A \<sqdot> (SOME C. V C \<beta> = VC\<beta> \<and> is_closed_wff_of_type C \<beta>)) \<alpha> |A. is_closed_wff_of_type A (\<beta> \<rightarrow> \<alpha>)}"
    by (simp add: setcompr_eq_image)

  from f obtain A where fp:
    "f = (\<^bold>\<lambda>VC\<beta>\<^bold>:D \<beta> \<^bold>. V (A \<sqdot> (SOME C. V C \<beta> = VC\<beta> \<and> C \<in> wffs\<^bsub>\<beta>\<^esub> \<and> free_vars C = {})) \<alpha>)"
    "is_closed_wff_of_type A (\<beta> \<rightarrow> \<alpha>)"
    using sma by auto

  {
    fix VC\<beta>
    assume "VC\<beta> \<in> elts (D \<beta>)"
    then have "\<exists>C. V C \<beta> = VC\<beta> \<and> is_closed_wff_of_type C \<beta>"
      by (smt (verit, best) elts_of_set emptyE mem_Collect_eq one_gamma)
    then obtain C where
      "V C \<beta> = VC\<beta>"
      "is_closed_wff_of_type C \<beta>"
      by blast
    have "V (A \<sqdot> (SOME C. V C \<beta> = VC\<beta> \<and> is_closed_wff_of_type C \<beta>)) \<alpha> \<in> elts (D \<alpha>)"
      by (metis (mono_tags, lifting) \<open>\<exists>C. V C \<beta> = VC\<beta> \<and> is_closed_wff_of_type C \<beta>\<close> bound_vars.simps(2) fp(2) free_vars_form.simps(2,3) is_closed_wff_of_type_def someI vars_form.simps(2)
          vars_is_free_and_bound_vars well_typed wffs_of_type_intros(3))
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
    (\<forall>A B. is_closed_wff_of_type A \<gamma> \<longrightarrow> is_closed_wff_of_type B \<gamma> \<longrightarrow>
           V A \<gamma> = V B \<gamma> \<longleftrightarrow> H \<turnstile> A =\<^bsub>\<gamma>\<^esub> B)"

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
    using good_type_def two_gamma_def two_o unambiguous.simps(2) by blast
next
  case (TFun \<beta> \<alpha>)

  {
    fix A B C
    assume "is_closed_wff_of_type A (\<beta> \<rightarrow> \<alpha>)"
    assume "is_closed_wff_of_type B \<beta>"
    assume "is_closed_wff_of_type C \<beta>"
    assume "V B \<beta> = V C \<beta>"
    have "V (A \<sqdot> B) \<alpha> = V (A \<sqdot> C) \<alpha>"
      using TFun.IH(1,2) \<open>is_closed_wff_of_type A (\<beta> \<rightarrow> \<alpha>)\<close> \<open>is_closed_wff_of_type B \<beta>\<close> \<open>is_closed_wff_of_type C \<beta>\<close>
        \<open>local.V B \<beta> = local.V C \<beta>\<close> good_type_def prop_5201_6 two_gamma_def wffs_of_type_intros(3) by force
    (* Sledgehammer could do it... But we could maybe write Andrew's short proof out and only
       Sledgehammer the intermediate steps. *)
  }
  then have una: "unambiguous (\<beta> \<rightarrow> \<alpha>)"
    unfolding unambiguous.simps by metis

  {
    fix A B
    assume "is_closed_wff_of_type A (\<beta> \<rightarrow> \<alpha>)"
    assume "is_closed_wff_of_type B (\<beta> \<rightarrow> \<alpha>)"
    have "local.V A (\<beta> \<rightarrow> \<alpha>) = local.V B (\<beta> \<rightarrow> \<alpha>) \<longleftrightarrow> H \<turnstile> A =\<^bsub>\<beta> \<rightarrow> \<alpha>\<^esub> B"
    proof
      assume "H \<turnstile> A =\<^bsub>\<beta> \<rightarrow> \<alpha>\<^esub> B"
      then have nice: "\<And>C. is_closed_wff_of_type C \<beta> \<Longrightarrow> H \<turnstile> A \<sqdot> C =\<^bsub>\<alpha>\<^esub> B \<sqdot> C"
        using prop_5201_5 by auto
      have "\<forall>C. is_closed_wff_of_type C \<beta> \<longrightarrow> H \<turnstile> A \<sqdot> C =\<^bsub>\<alpha>\<^esub> B \<sqdot> C"
        using \<open>H \<turnstile> A =\<^bsub>\<beta> \<rightarrow> \<alpha>\<^esub> B\<close> prop_5201_5 by auto
      {
        fix C
        assume "is_closed_wff_of_type C \<beta>"
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
              apply (smt (verit, ccfv_threshold) \<open>is_closed_wff_of_type A (\<beta> \<rightarrow> \<alpha>)\<close> \<open>is_closed_wff_of_type C \<beta>\<close> \<open>local.unambiguous (\<beta> \<rightarrow> \<alpha>)\<close>
                  is_closed_wff_of_type_def some_eq_ex unambiguous.simps(3))
              done
            subgoal
              apply (metis (mono_tags, lifting) \<open>is_closed_wff_of_type C \<beta>\<close> get_rep.simps verit_sko_ex')
              done
            done
          subgoal
            using \<open>is_closed_wff_of_type C \<beta>\<close> well_typed apply auto
            done
          done
        also have "... = V (B \<sqdot> C) \<alpha>"
          using nice[OF \<open>is_closed_wff_of_type C \<beta>\<close>]
          using TFun(2) unfolding good_type_def
          by (metis \<open>is_closed_wff_of_type A (\<beta> \<rightarrow> \<alpha>)\<close> \<open>is_closed_wff_of_type B (\<beta> \<rightarrow> \<alpha>)\<close> \<open>is_closed_wff_of_type C \<beta>\<close>
              bound_vars.simps(2) free_vars_form.simps(2,3) hyp_derivable_form_is_wffso is_closed_wff_of_type_def two_gamma_def
              vars_form.simps(2) vars_is_free_and_bound_vars wffs_from_equality(1,2))
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
              apply (smt (verit, ccfv_threshold) \<open>is_closed_wff_of_type B (\<beta> \<rightarrow> \<alpha>)\<close> \<open>is_closed_wff_of_type C \<beta>\<close> \<open>local.unambiguous (\<beta> \<rightarrow> \<alpha>)\<close>
                  is_closed_wff_of_type_def some_eq_ex unambiguous.simps(3))
              done
            subgoal
              apply (metis (mono_tags, lifting) \<open>is_closed_wff_of_type C \<beta>\<close> get_rep.simps verit_sko_ex')
              done
            done
          subgoal
            using \<open>is_closed_wff_of_type C \<beta>\<close> well_typed apply auto
            done
          done
        finally have "(V A (\<beta> \<rightarrow> \<alpha>)) \<bullet> (V C \<beta>) = (V B (\<beta> \<rightarrow> \<alpha>)) \<bullet> (V C \<beta>)"
          .
      }
      note C_application = this

      show "V A (\<beta> \<rightarrow> \<alpha>) = V B (\<beta> \<rightarrow> \<alpha>)"
      proof (rule fun_ext_vfuncset[of _ "D \<beta>" "D \<alpha>"])
        show "V A (\<beta> \<rightarrow> \<alpha>) \<in> elts (D \<beta> \<longmapsto> D \<alpha>)"
          using fun_typed well_typed \<open>is_closed_wff_of_type A (\<beta> \<rightarrow> \<alpha>)\<close> una by (metis subsetD)
      next
        show "V B (\<beta> \<rightarrow> \<alpha>) \<in> elts (D \<beta> \<longmapsto> D \<alpha>)"
          using fun_typed well_typed \<open>is_closed_wff_of_type B (\<beta> \<rightarrow> \<alpha>)\<close> una by (metis subsetD)
      next 
        fix VC\<beta>
        assume "VC\<beta> \<in> elts (D \<beta>)"
        then obtain C where "V C \<beta> = VC\<beta> \<and> is_closed_wff_of_type C \<beta>"
          by (smt (verit) one_gamma elts_of_set emptyE mem_Collect_eq)
        then show "V A (\<beta> \<rightarrow> \<alpha>) \<bullet> VC\<beta> = V B (\<beta> \<rightarrow> \<alpha>) \<bullet> VC\<beta>"
          using C_application by blast
      qed
    next
      assume "V A (\<beta> \<rightarrow> \<alpha>) = V B (\<beta> \<rightarrow> \<alpha>)"
      {
        fix C
        assume "is_closed_wff_of_type C \<beta>"
        assume "H \<turnstile> ((A \<sqdot> C) =\<^bsub>\<alpha>\<^esub> (B \<sqdot> C)) \<supset>\<^sup>\<Q> (A =\<^bsub>\<beta> \<rightarrow> \<alpha>\<^esub> B)"
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
              apply (smt (verit, ccfv_threshold) \<open>is_closed_wff_of_type A (\<beta> \<rightarrow> \<alpha>)\<close> \<open>is_closed_wff_of_type C \<beta>\<close> \<open>local.unambiguous (\<beta> \<rightarrow> \<alpha>)\<close>
                  is_closed_wff_of_type_def some_eq_ex unambiguous.simps(3))
              done
            subgoal
              apply (metis (mono_tags, lifting) \<open>is_closed_wff_of_type C \<beta>\<close> get_rep.simps verit_sko_ex')
              done
            done
          subgoal
            using \<open>is_closed_wff_of_type C \<beta>\<close> well_typed apply auto
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
            unfolding is_closed_wff_of_type_def[symmetric]
            unfolding get_rep.simps[symmetric]
            apply (subgoal_tac "V (get_rep (V C \<beta>) \<beta>) \<beta> = V C \<beta>")
            subgoal
              apply -
              apply auto
              apply (smt (verit, ccfv_threshold) \<open>is_closed_wff_of_type B (\<beta> \<rightarrow> \<alpha>)\<close> \<open>is_closed_wff_of_type C \<beta>\<close> \<open>local.unambiguous (\<beta> \<rightarrow> \<alpha>)\<close>
                  is_closed_wff_of_type_def some_eq_ex unambiguous.simps(3))
              done
            subgoal
              apply (metis (mono_tags, lifting) \<open>is_closed_wff_of_type C \<beta>\<close> get_rep.simps verit_sko_ex')
              done
            done
          subgoal
            using \<open>is_closed_wff_of_type C \<beta>\<close> well_typed apply auto
            done
          done
        finally have "V (A \<sqdot> C) \<alpha> = V (B \<sqdot> C) \<alpha>"
          .
        then have "H \<turnstile> A \<sqdot> C =\<^bsub>\<alpha>\<^esub> B \<sqdot> C"
          using TFun.IH(2) \<open>is_closed_wff_of_type A (\<beta> \<rightarrow> \<alpha>)\<close>
            \<open>is_closed_wff_of_type B (\<beta> \<rightarrow> \<alpha>)\<close> \<open>is_closed_wff_of_type C \<beta>\<close>
            good_type_def two_gamma_def wffs_of_type_intros(3) by force
      }
      then show "H \<turnstile> A =\<^bsub>\<beta> \<rightarrow> \<alpha>\<^esub> B"
        by (metis \<open>is_H_extension_of H G\<close> \<open>is_closed_wff_of_type A (\<beta> \<rightarrow> \<alpha>)\<close> \<open>is_closed_wff_of_type B (\<beta> \<rightarrow> \<alpha>)\<close> extensionally_complete_def is_H_extension_of_def prop_5224)
    qed
  }
  then have "two_gamma (\<beta> \<rightarrow> \<alpha>)"
    unfolding two_gamma_def by auto

  then show ?case
    unfolding good_type_def using una by metis
qed

lemma two_fun:
  assumes "is_closed_wff_of_type A (\<beta> \<rightarrow> \<alpha>)"
  assumes "is_closed_wff_of_type B (\<beta> \<rightarrow> \<alpha>)"
  shows "V A (\<beta> \<rightarrow> \<alpha>) = V B (\<beta> \<rightarrow> \<alpha>) \<longleftrightarrow> H \<turnstile> A =\<^bsub>\<beta> \<rightarrow> \<alpha>\<^esub> B"
  using all_good assms(1,2) good_type_def two_gamma_def by presburger

lemma two_gamma:
  assumes "is_closed_wff_of_type A \<gamma>"
  assumes "is_closed_wff_of_type B \<gamma>"
  shows "V A \<gamma> = V B \<gamma> \<longleftrightarrow> H \<turnstile> A =\<^bsub>\<gamma>\<^esub> B"
  using all_good assms(1,2) good_type_def two_gamma_def by presburger


subsection \<open>M is interpretation\<close>

fun J :: "nat \<times> Syntax.type \<Rightarrow> V" where 
  "J (c,\<tau>) = V (FCon (c,\<tau>)) \<tau>"


(* Mapping primitive constants into D\<^sub>\<alpha>*)
lemma non_logical_constant_denotation_V: 
  "\<not> is_logical_constant (c, \<alpha>) \<Longrightarrow> V (FCon (c, \<alpha>)) \<alpha> \<in> elts (D \<alpha>)"
  sorry

lemma non_logical_constant_denotation_J: 
  "\<not> is_logical_constant (c, \<alpha>) \<Longrightarrow> J (c, \<alpha>) \<in> elts (D \<alpha>)"
  using non_logical_constant_denotation_V unfolding J.simps by auto



(* False *)


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


(* I cannot find this in the book's proof. Too obvious maybe? *)
lemma function_domain: "D (\<alpha> \<rightarrow> \<beta>) \<le> D \<alpha> \<longmapsto> D \<beta>"
  sorry

(* I cannot find this in the book's proof. Too obvious maybe? *)
lemma domain_nonemptiness: "D \<alpha> \<noteq> 0"
  sorry

(* M constitutes an interpretation (premodel) *)
interpretation premodel D J
  apply unfold_locales
  using function_domain domain_nonemptiness Q_denotation_J \<iota>_denotation_J 
    non_logical_constant_denotation_J apply auto
  done


subsection \<open>M is general model\<close>

definition fun_E :: "(var \<Rightarrow> V) \<Rightarrow> (var \<Rightarrow> form)" where
  "fun_E \<phi> = (\<lambda>(x,\<delta>). (SOME A. \<phi> (x,\<delta>) = V A \<delta>))" 
  (* Andrews asks for "the first formula such that". But I think SOME formula is sufficient. *)

definition map_E :: "var set \<Rightarrow> (var \<Rightarrow> V) \<Rightarrow> (var \<rightharpoonup> form)" where
  "map_E xs \<phi> = map_restrict_set xs (Some \<circ> (fun_E \<phi>))"

definition subst_E :: "var set \<Rightarrow> (var \<Rightarrow> V) \<Rightarrow> substitution" where
  "subst_E xs \<phi> = Abs_fmap (map_E xs \<phi>)"

definition \<theta>\<^sub>E :: "(var \<Rightarrow> V) \<Rightarrow> form \<Rightarrow> substitution" where
  "\<theta>\<^sub>E \<phi> C = subst_E (free_vars C) \<phi>"

definition C\<phi> :: "form \<Rightarrow> (var \<Rightarrow> V) \<Rightarrow> type \<Rightarrow> form" where
  "C\<phi> C \<phi> \<gamma> = \<^bold>S (\<theta>\<^sub>E \<phi> C) C"

definition type_of :: "form \<Rightarrow> type" where
  "type_of A = (SOME \<tau>. A \<in> wffs\<^bsub>\<tau>\<^esub>)"

definition V\<phi> :: "(var \<Rightarrow> V) \<Rightarrow> form \<Rightarrow> V" where
  "V\<phi> \<phi> C = V (C\<phi> C \<phi> (type_of C)) (type_of C)"

lemma g: "A \<in> wffs\<^bsub>\<alpha>\<^esub> \<Longrightarrow> V\<phi> \<phi> A \<in> elts (D \<alpha>)"
  sorry

(* For any variable *)
lemma denotation_function_a: "\<phi> \<leadsto> local.D \<Longrightarrow> V\<phi> \<phi> (x\<^bsub>\<alpha>\<^esub>) = \<phi> (x, \<alpha>)"
  sorry

(* For any primitive constant *)
lemma denotation_function_b: "\<phi> \<leadsto> local.D \<Longrightarrow> V\<phi> \<phi> (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) = J (c, \<alpha>)"
  sorry

(* Application *)
lemma denotation_function_c: 
  "\<phi> \<leadsto> local.D \<Longrightarrow> A \<in> wffs\<^bsub>\<beta> \<rightarrow> \<alpha>\<^esub> \<and> B \<in> wffs\<^bsub>\<beta>\<^esub> \<Longrightarrow> V\<phi> \<phi> (A \<sqdot> B) = V\<phi> \<phi> A \<bullet> V\<phi> \<phi> B"
  sorry

(* Abstraction *)
lemma denotation_function_d: 
  "\<phi> \<leadsto> local.D \<Longrightarrow> B \<in> wffs\<^bsub>\<beta>\<^esub> \<Longrightarrow> V\<phi> \<phi> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) = (\<^bold>\<lambda>z\<^bold>:D \<alpha> \<^bold>. V\<phi> (\<phi>((x, \<alpha>) := z)) B)"
  sorry

lemma denotation_function: "is_wff_denotation_function V\<phi>"
  unfolding is_wff_denotation_function_def
  using g denotation_function_a denotation_function_b denotation_function_c denotation_function_d 
  by auto

interpretation general_model D J V\<phi>
  apply unfold_locales
  using g denotation_function_a denotation_function_b denotation_function_c denotation_function_d 
    denotation_function by auto

lemma canon_frugal: "frugal_model D J V\<phi>"
  sorry

lemma canon_model_for: "is_model_for (D,J,V\<phi>) G"
  sorry

end

theorem henkins_theorem:
  assumes "sentence_set G"
  assumes "consistent G"
  shows "\<exists>M. is_frugal_model M \<and> is_model_for M G"
  unfolding is_frugal_model_def
  using canon_frugal canon_model_for assms(1,2) extension_lemma2 by (metis case_prodI)


section \<open>5502 Henkin's Completeness and Soundness Theorem\<close>

theorem sound_complete_c:
  assumes "sentence_set G"
  shows "G \<turnstile> A \<longleftrightarrow> (\<forall>M. is_frugal_model M \<longrightarrow> is_model_for M G \<longrightarrow> M \<Turnstile> A)"
  sorry

theorem sound_complete_b:
  assumes "sentence_set G"
  shows "G \<turnstile> A \<longleftrightarrow> (\<forall>M. is_general_model M \<longrightarrow> is_model_for M G \<longrightarrow> M \<Turnstile> A)"
  sorry

theorem sound_complete_a:
  "\<turnstile> A \<longleftrightarrow> \<Turnstile> A"
  by (simp add: sentence_set_def sound_complete_b)


end
