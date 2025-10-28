theory Completeness imports
    Consistency
begin

context
  fixes H :: "form set"
begin

definition V_of_form :: "form \<Rightarrow> V" where
  "V_of_form A = undefined A"

definition form_of_V :: "V \<Rightarrow> form" where
  "form_of_V S = undefined S"

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

