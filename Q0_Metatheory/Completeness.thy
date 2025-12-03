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
  "D o = V_of_form_set {T\<^bsub>o\<^esub>,F\<^bsub>o\<^esub>}"
| "D i = set {V A i | A. is_closed_wff_of_type A i}"
| "D (\<beta> \<rightarrow> \<alpha>) = set {V A (\<beta> \<rightarrow> \<alpha>) | A. is_closed_wff_of_type A (\<beta> \<rightarrow> \<alpha>)}"
| "V A o = (if (H \<turnstile> A) then V_of_form (T\<^bsub>o\<^esub>) else V_of_form (F\<^bsub>o\<^esub>))"
| "V A i = V_of_form_set {B. is_closed_wff_of_type B i \<and> H \<turnstile> A =\<^bsub>i\<^esub> B}"
| "V A (\<beta> \<rightarrow> \<alpha>) = (\<^bold>\<lambda>VC\<beta> \<^bold>: D \<beta>\<^bold>. (let C = get_rep VC\<beta> \<beta> in V (A \<sqdot> C) \<alpha>))"
| "get_rep VC\<beta> \<beta> = (SOME C. V C \<beta> = VC\<beta> \<and> C \<in> wffs\<^bsub>\<beta>\<^esub>)"

end

end

