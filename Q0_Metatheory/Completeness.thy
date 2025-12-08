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

lemma extension_lemma:
  (* WARNING: We are missing the cardinality thing, i.e. property (5) of the lemma *)
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

(* Warning -- replace undefined with something. Probably something from ZFC_Cardinals *)
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
| "get_rep VC\<beta> \<beta> = (SOME C. V C \<beta> = VC\<beta> \<and> C \<in> wffs\<^bsub>\<beta>\<^esub>)"

lemma unambiguity:
  assumes "is_closed_wff_of_type A (\<beta> \<rightarrow> \<alpha>)"
  assumes "is_closed_wff_of_type B \<beta>"
  assumes "is_closed_wff_of_type C \<beta>"
  assumes "V B \<beta> = V C \<beta>"
  shows "V (A \<sqdot> B) \<alpha> = V (A \<sqdot> C) \<alpha>"
  sorry


subsection \<open>1\<gamma>\<close>

lemma one_gamma: "D \<tau> = set {V A \<gamma>| A \<gamma>. is_closed_wff_of_type A \<gamma>}"
  sorry



section \<open>2\<gamma>\<close>

lemma two_gamma:
  assumes "is_closed_wff_of_type A \<gamma>"
  assumes "is_closed_wff_of_type B \<gamma>"
  shows "V A \<gamma> = V B \<gamma> \<longleftrightarrow> H \<turnstile> A =\<^bsub>\<gamma>\<^esub> B"
  sorry


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
  using D.simps(1) one_gamma by auto

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
  sorry


end
