theory Completeness imports
    Consistency
begin


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
  fixes H :: "form set"
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


section \<open>1\<gamma>\<close>

lemma one_gamma: "D \<tau> = set {V A \<gamma>| A \<gamma>. is_closed_wff_of_type A \<gamma>}"
  sorry


section \<open>2\<gamma>\<close>

lemma two_gamma:
  assumes "is_closed_wff_of_type A \<gamma>"
  assumes "is_closed_wff_of_type B \<gamma>"
  shows "V A \<gamma> = V B \<gamma> \<longleftrightarrow> H \<turnstile> A =\<^bsub>\<gamma>\<^esub> B"
  sorry


section \<open>M is interpretation\<close>

fun J :: "nat \<times> Syntax.type \<Rightarrow> V" where 
  "J (c,\<tau>) = V (FCon (c,\<tau>)) \<tau>"


(* Mapping primitive constants into D\<^sub>\<alpha>*)
lemma non_logical_constant_denotation_V: 
  "\<not> is_logical_constant (c, \<alpha>) \<Longrightarrow> V (FCon (c, \<alpha>)) \<alpha> \<in> elts (D \<alpha>)"
  sorry

lemma non_logical_constant_denotation_J: 
  "\<not> is_logical_constant (c, \<alpha>) \<Longrightarrow> J (c, \<alpha>) \<in> elts (D \<alpha>)"
  using non_logical_constant_denotation_V unfolding J.simps by auto


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


section \<open>M is general model\<close>

definition "list_of_set xs = (SOME xl. List.set xl = xs \<and> length xl = card xs)"

definition "free_vars_list (C::form) = list_of_set (free_vars C)"

fun E :: "(var \<Rightarrow> V) \<Rightarrow> var \<Rightarrow> form" where
  "E \<phi> (x,\<delta>) = (SOME A. \<phi> (x,\<delta>) = V A \<delta>)" 
  (* Andrews asks for "the first formula such that". But I think SOME formula is sufficient. *)

definition \<theta>\<^sub>E'' :: "(var \<Rightarrow> V) \<Rightarrow> var list \<Rightarrow> form list" where
  "\<theta>\<^sub>E'' \<phi> xs = map (E \<phi>) xs"

definition \<theta>\<^sub>E' :: "(var \<Rightarrow> V) \<Rightarrow> form \<Rightarrow> form list" where
  "\<theta>\<^sub>E' \<phi> C = \<theta>\<^sub>E'' \<phi> (free_vars_list C)"

definition \<theta>\<^sub>E :: "(var \<Rightarrow> V) \<Rightarrow> form \<Rightarrow> substitution" where 
  "\<theta>\<^sub>E \<phi> C = fmap_of_list (zip (free_vars_list C) (\<theta>\<^sub>E' \<phi> C))"
(* This \<theta>\<^sub>E should be correct, but maybe can be in a more proof friendly way. *)

definition C\<phi> :: "form \<Rightarrow> (var \<Rightarrow> V) \<Rightarrow> type \<Rightarrow> form" where
  "C\<phi> C \<phi> \<gamma> = \<^bold>S (\<theta>\<^sub>E \<phi> C) C"

definition type_of :: "form \<Rightarrow> type" where
  "type_of A = (SOME \<tau>. A \<in> wffs\<^bsub>\<tau>\<^esub>)"

definition V\<phi> :: "(var \<Rightarrow> V) \<Rightarrow> form \<Rightarrow> V" where
  "V\<phi> \<phi> C = V (C\<phi> C \<phi> (type_of C)) (type_of C)"

lemma g: "A \<in> wffs\<^bsub>\<alpha>\<^esub> \<Longrightarrow> V\<phi> \<phi> A \<in> elts (D \<alpha>)"
  sorry

(* For any variable *)
lemma denotation_function_a: "V\<phi> \<phi> (x\<^bsub>\<alpha>\<^esub>) = \<phi> (x, \<alpha>)"
  sorry

(* For any primitive constant *)
lemma denotation_function_b: "V\<phi> \<phi> (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) = J (c, \<alpha>)"
  sorry

(* Application*)
lemma denotation_function_c: "A \<in> wffs\<^bsub>\<beta> \<rightarrow> \<alpha>\<^esub> \<and> B \<in> wffs\<^bsub>\<beta>\<^esub> \<Longrightarrow> V\<phi> \<phi> (A \<sqdot> B) = V\<phi> \<phi> A \<bullet> V\<phi> \<phi> B"
  sorry

(* Abstraction *)
lemma denotation_function_d: "B \<in> wffs\<^bsub>\<beta>\<^esub> \<Longrightarrow> V\<phi> \<phi> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) = (\<^bold>\<lambda>z\<^bold>:D \<alpha> \<^bold>. V\<phi> (\<phi>((x, \<alpha>) := z)) B)"
  sorry

lemma denotation_function: "is_wff_denotation_function V\<phi>"
  unfolding is_wff_denotation_function_def
  using g denotation_function_a denotation_function_b denotation_function_c denotation_function_d 
  by auto

interpretation general_model D J V\<phi>
  apply unfold_locales
  using g denotation_function_a denotation_function_b denotation_function_c denotation_function_d 
    denotation_function by auto


end

end
