(*
  Author: Asta Halkjær From, 2025.

  Inspiration:
  - "FOL-Fitting", Stefan Berghofer.
  - "First-Order Logic and Automated Theorem Proving", 1996, Melvin Fitting.
*)

(* TODO: Might want to use a, b instead of n, m *)
(* TODO: In Isabelle2025 we can actually extend and instantiate wo_rel *)

theory Analytic_Completeness imports
  "HOL-Cardinals.Cardinal_Order_Relation"
begin

section \<open>Utility\<close>

lemma Set_Diff_Un: \<open>X - (Y \<union> Z) = X - Y - Z\<close>
  by blast

lemma infinite_diff_finite: \<open>finite A \<Longrightarrow> infinite (- B) \<Longrightarrow> infinite (- (A \<union> B))\<close>
  by (metis Compl_Diff_eq double_complement finite_Diff2 sup_commute)

lemma infinite_Diff_fin_Un: \<open>infinite (X - Y) \<Longrightarrow> finite Z \<Longrightarrow> infinite (X - (Z \<union> Y))\<close>
  by (simp add: Set_Diff_Un Un_commute)

lemma infinite_Diff_subset: \<open>infinite (X - A) \<Longrightarrow> B \<subseteq> A \<Longrightarrow> infinite (X - B)\<close>
  by (meson Diff_cancel Diff_eq_empty_iff Diff_mono infinite_super)

lemma finite_bound:
  fixes X :: \<open>('a :: size) set\<close>
  assumes \<open>finite X\<close> \<open>X \<noteq> {}\<close>
  shows \<open>\<exists>x \<in> X. \<forall>y \<in> X. size y \<le> size x\<close>
  using assms by (induct X rule: finite_induct) force+

lemma infinite_UNIV_size:
  fixes f :: \<open>('a :: size) \<Rightarrow> 'a\<close>
  assumes \<open>\<And>x. size x < size (f x)\<close>
  shows \<open>infinite (UNIV :: 'a set)\<close>
proof
  assume \<open>finite (UNIV :: 'a set)\<close>
  then obtain x :: 'a where \<open>\<forall>y :: 'a. size y \<le> size x\<close>
    using finite_bound by fastforce
  moreover have \<open>size x < size (f x)\<close>
    using assms .
  ultimately show False
    using leD by blast
qed

lemma infinite_left: \<open>finite C \<Longrightarrow> infinite A \<Longrightarrow> |A| \<le>o |- B| \<Longrightarrow> |A| \<le>o |- (C \<union> B)|\<close>
  by (metis (no_types, opaque_lifting) Compl_Diff_eq card_of_infinite_diff_finite card_of_ordLeq_finite
      double_complement ordIso_iff_ordLeq ordLeq_transitive sup_commute)

lemma card_of_infinite_smaller_Union:
  assumes \<open>\<forall>x. |f x| <o |X|\<close> \<open>infinite X\<close>
  shows \<open>|\<Union>x \<in> X. f x| \<le>o |X|\<close>
  using assms by (metis (full_types) Field_card_of card_of_UNION_ordLeq_infinite
      card_of_well_order_on ordLeq_iff_ordLess_or_ordIso ordLess_or_ordLeq)

lemma card_of_params_marker_lists:
  assumes \<open>infinite (UNIV :: 'i set)\<close> \<open>|UNIV :: 'm set| \<le>o |UNIV :: nat set|\<close>
  shows \<open>|UNIV :: ('i + 'm \<times> nat) list set| \<le>o |UNIV :: 'i set|\<close>
proof -
  have \<open>(UNIV :: 'm set) \<noteq> {}\<close>
    by simp
  then have \<open>|UNIV :: 'm set| *c |UNIV :: nat set| \<le>o |UNIV :: nat set|\<close>
    using assms(2) by (simp add: cinfinite_def cprod_cinfinite_bound ordLess_imp_ordLeq)
  then have \<open>|UNIV :: ('m \<times> nat) set| \<le>o |UNIV :: nat set|\<close>
    unfolding cprod_def by simp
  moreover have \<open>|UNIV :: nat set| \<le>o |UNIV :: 'i set|\<close>
    using assms infinite_iff_card_of_nat by blast
  ultimately have \<open>|UNIV :: ('m \<times> nat) set| \<le>o |UNIV :: 'i set|\<close>
    using ordLeq_transitive by blast
  moreover have \<open>Cinfinite |UNIV :: 'i set|\<close>
    using assms by (simp add: cinfinite_def)
  ultimately have \<open>|UNIV :: 'i set| +c |UNIV :: ('m \<times> nat) set| =o |UNIV :: 'i set|\<close>
    using csum_absorb1 by blast
  then have \<open>|UNIV :: ('i + 'm \<times> nat) set| =o |UNIV :: 'i set|\<close>
    unfolding csum_def by simp
  then have \<open>|UNIV :: ('i + 'm \<times> nat) set| \<le>o |UNIV :: 'i set|\<close>
    using ordIso_iff_ordLeq by blast
  moreover have \<open>infinite (UNIV :: ('i + 'm \<times> nat) set)\<close>
    using assms by simp
  then have \<open>|UNIV :: ('i + 'm \<times> nat) list set| =o |UNIV :: ('i + 'm \<times> nat) set|\<close>
    by (metis card_of_lists_infinite lists_UNIV)
  ultimately have \<open>|UNIV :: ('i + 'm \<times> nat) list set| \<le>o |UNIV :: 'i set|\<close>
    using ordIso_ordLeq_trans by blast
  then show ?thesis
    using ordLeq_transitive by blast
qed

context wo_rel
begin

lemma underS_bound: \<open>a \<in> underS n \<Longrightarrow> b \<in> underS n \<Longrightarrow> a \<in> under b \<or> b \<in> under a\<close>
  by (meson BNF_Least_Fixpoint.underS_Field REFL Refl_under_in in_mono under_ofilter ofilter_linord)

lemma finite_underS_bound:
  assumes \<open>finite X\<close> \<open>X \<subseteq> underS n\<close> \<open>X \<noteq> {}\<close>
  shows \<open>\<exists>a \<in> X. \<forall>b \<in> X. b \<in> under a\<close>
  using assms
proof (induct X rule: finite_induct)
  case (insert x F)
  then show ?case
  proof (cases \<open>F = {}\<close>)
    case True
    then show ?thesis
      using insert underS_bound by fast
  next
    case False
    then show ?thesis
      using insert underS_bound by (metis TRANS insert_absorb insert_iff insert_subset under_trans)
  qed
qed simp

lemma finite_bound_under:
  assumes \<open>finite p\<close> \<open>p \<subseteq> (\<Union>n \<in> Field r. f n)\<close>
  shows \<open>\<exists>m. p \<subseteq> (\<Union>n \<in> under m. f n)\<close>
  using assms
proof (induct rule: finite_induct)
  case (insert x p)
  then obtain m where \<open>p \<subseteq> (\<Union>n \<in> under m. f n)\<close>
    by fast
  moreover obtain m' where \<open>x \<in> f m'\<close> \<open>m' \<in> Field r\<close>
    using insert(4) by blast
  then have \<open>x \<in> (\<Union>n \<in> under m'. f n)\<close>
    using REFL Refl_under_in by fast
  ultimately have \<open>{x} \<union> p \<subseteq> (\<Union>n \<in> under m. f n) \<union> (\<Union>n \<in> under m'. f n)\<close>
    by fast
  then show ?case
    by (metis SUP_union Un_commute insert_is_Un sup.absorb_iff2 ofilter_linord under_ofilter)
qed simp

lemma underS_trans: \<open>a \<in> underS b \<Longrightarrow> b \<in> underS c \<Longrightarrow> a \<in> underS c\<close>
  by (meson ANTISYM TRANS underS_underS_trans)

definition is_chain :: \<open>('a \<Rightarrow> 'a set) \<Rightarrow> bool\<close> where
  \<open>is_chain f \<equiv> \<forall>n \<in> Field r. \<forall>m \<in> Field r. m \<in> under n \<longrightarrow> f m \<subseteq> f n\<close>

lemma is_chainD: \<open>is_chain f \<Longrightarrow>  m \<in> under n \<Longrightarrow> x \<in> f m \<Longrightarrow> x \<in> f n\<close>
  unfolding is_chain_def by (metis equals0D subsetD under_Field under_empty)

lemma chain_index:
  assumes ch: \<open>is_chain f\<close> and fin: \<open>finite F\<close> and ne: \<open>Field r \<noteq> {}\<close>
  shows \<open>F \<subseteq> (\<Union>n \<in> Field r. f n) \<Longrightarrow> \<exists>n \<in> Field r. F \<subseteq> f n\<close>
  using fin
proof (induct rule: finite_induct)
  case empty
  then show ?case
    using ne by blast
next
  case (insert x F)
  then have \<open>\<exists>n \<in> Field r. F \<subseteq> f n\<close> \<open>\<exists>m \<in> Field r. x \<in> f m\<close> \<open>F \<subseteq> (\<Union>x \<in> Field r. f x)\<close>
    using ch by simp_all
  then obtain n and m where f: \<open>F \<subseteq> f n\<close> \<open>x \<in> f m\<close> and nm: \<open>n \<in> Field r\<close> \<open>m \<in> Field r\<close>
    by blast
  have \<open>m \<in> under (max2 n m)\<close> \<open>n \<in> under (max2 n m)\<close>
    using nm  by (meson REFL Refl_under_in TRANS max2_greater_among subset_iff under_incl_iff)+
  have \<open>x \<in> f (max2 n m)\<close>
    using is_chainD ch \<open>m \<in> under (max2 n m)\<close> f(2) by blast
  moreover have \<open>F \<subseteq> f (max2 n m)\<close>
    using is_chainD ch \<open>n \<in> local.under (max2 n m)\<close> f(1) by blast
  ultimately show ?case
    using nm unfolding max2_def by auto
qed

end

section \<open>Finite Character\<close>

definition close :: \<open>'a set set \<Rightarrow> 'a set set\<close> where
  \<open>close C \<equiv> {S. \<exists>S' \<in> C. S \<subseteq> S'}\<close>

definition subset_closed :: \<open>'a set set \<Rightarrow> bool\<close> where
  \<open>subset_closed C \<equiv> \<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>

lemma subset_in_close: \<open>S \<subseteq> S' \<Longrightarrow> x \<union> S' \<in> C \<Longrightarrow> x \<union> S \<in> close C\<close>
  unfolding close_def by blast

lemma close_closed: \<open>subset_closed (close C)\<close>
  unfolding close_def subset_closed_def by blast

lemma close_subset: \<open>C \<subseteq> close C\<close>
  unfolding close_def by blast

definition finite_char :: \<open>'a set set \<Rightarrow> bool\<close> where
  \<open>finite_char C \<equiv> \<forall>S. S \<in> C \<longleftrightarrow> (\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C)\<close>

definition mk_finite_char :: \<open>'a set set \<Rightarrow> 'a set set\<close> where
  \<open>mk_finite_char C \<equiv> {S. \<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C}\<close>

lemma finite_char: \<open>finite_char (mk_finite_char C)\<close>
  unfolding finite_char_def mk_finite_char_def by blast

lemma finite_char_closed: \<open>finite_char C \<Longrightarrow> subset_closed C\<close>
  unfolding finite_char_def subset_closed_def by (meson order_trans)

lemma finite_char_subset: \<open>subset_closed C \<Longrightarrow> C \<subseteq> mk_finite_char C\<close>
  unfolding mk_finite_char_def subset_closed_def by blast

lemma (in wo_rel) chain_union_closed:
  assumes \<open>finite_char C\<close> \<open>is_chain f\<close> \<open>\<forall>n \<in> Field r. f n \<in> C\<close> \<open>Field r \<noteq> {}\<close>
  shows \<open>(\<Union>n \<in> Field r. f n) \<in> C\<close>
  using assms chain_index unfolding finite_char_def by metis

definition maximal :: \<open>'a set set \<Rightarrow> 'a set \<Rightarrow> bool\<close> where
  \<open>maximal C S \<longleftrightarrow> (\<forall>S' \<in> C. S \<subseteq> S' \<longrightarrow> S = S')\<close>

section \<open>Locale\<close>

locale Params =
  fixes map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close>
    and params_fm :: \<open>'fm \<Rightarrow> 'x set\<close>
  assumes map_fm_id: \<open>map_fm id = id\<close>
    and finite_params_fm [simp]: \<open>\<And>p. finite (params_fm p)\<close>
    and map_params_fm: \<open>\<And>f g p. \<forall>x \<in> params_fm p. f x = g x \<Longrightarrow> map_fm f p = map_fm g p\<close>
begin

definition mk_alt_consistency :: \<open>'fm set set \<Rightarrow> 'fm set set\<close> where
  \<open>mk_alt_consistency C = {S. \<exists>f. map_fm f ` S \<in> C}\<close>

lemma mk_alt_consistency_subset: \<open>C \<subseteq> mk_alt_consistency C\<close>
  unfolding mk_alt_consistency_def
proof
  fix x
  assume \<open>x \<in> C\<close>
  then have \<open>map_fm id ` x \<in> C\<close>
    using map_fm_id by simp
  then have \<open>\<exists>f. map_fm f ` x \<in> C\<close>
    by blast
  then show \<open>x \<in> {S. \<exists>f. map_fm f ` S \<in> C}\<close>
    by blast
qed

lemma mk_alt_consistency_closed:
  assumes \<open>subset_closed C\<close>
  shows \<open>subset_closed (mk_alt_consistency C)\<close>
  unfolding subset_closed_def mk_alt_consistency_def
proof safe
  fix S S' f
  assume \<open>map_fm f ` S' \<in> C\<close> \<open>S \<subseteq> S'\<close>
  moreover have \<open>map_fm f ` S \<subseteq> map_fm f ` S'\<close>
    using \<open>S \<subseteq> S'\<close> by blast
  moreover have \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>
    using \<open>subset_closed C\<close> unfolding subset_closed_def by blast
  ultimately show \<open>\<exists>f. map_fm f ` S \<in> C\<close>
    by blast
qed

abbreviation params :: \<open>'fm set \<Rightarrow> 'x set\<close> where
  \<open>params S \<equiv> \<Union>p \<in> S. params_fm p\<close>

lemma infinite_params: \<open>infinite (- params B) \<Longrightarrow> infinite (- params (set ps \<union> B))\<close>
  using infinite_diff_finite finite_params_fm by (metis List.finite_set UN_Un finite_UN_I)

lemma infinite_params_left: \<open>infinite A \<Longrightarrow> |A| \<le>o |- params S| \<Longrightarrow> |A| \<le>o |- params (set ps \<union> S)|\<close>
  using infinite_left by (metis List.finite_set UN_Un finite_UN_I finite_params_fm)

end

datatype ('x, 'fm) kind
  = Cond \<open>'fm list \<Rightarrow> ('fm set set \<Rightarrow> 'fm set \<Rightarrow> bool) \<Rightarrow> bool\<close> \<open>'fm set \<Rightarrow> bool\<close>
  | Wits \<open>'fm \<Rightarrow> 'x \<Rightarrow> 'fm list\<close>

inductive sat\<^sub>E :: \<open>('x, 'fm) kind \<Rightarrow> 'fm set set \<Rightarrow> bool\<close> where
  sat\<^sub>E_Cond [intro!]: \<open>(\<And>S ps Q. S \<in> C \<Longrightarrow> set ps \<subseteq> S \<Longrightarrow> P ps Q \<Longrightarrow> Q C S) \<Longrightarrow> sat\<^sub>E (Cond P H) C\<close>
| sat\<^sub>E_Wits [intro!]: \<open>(\<And>S p. S \<in> C \<Longrightarrow> p \<in> S \<Longrightarrow> \<exists>x. set (W p x) \<union> S \<in> C) \<Longrightarrow> sat\<^sub>E (Wits W) C\<close>

inductive_cases sat\<^sub>E_CondE[elim!]: \<open>sat\<^sub>E (Cond P H) C\<close>
inductive_cases sat\<^sub>E_WitsE[elim!]: \<open>sat\<^sub>E (Wits W) C\<close>

inductive (in Params) sat\<^sub>A :: \<open>('x, 'fm) kind \<Rightarrow> 'fm set set \<Rightarrow> bool\<close> where
  sat\<^sub>A_Cond [intro!]: \<open>(\<And>S ps Q. S \<in> C \<Longrightarrow> set ps \<subseteq> S \<Longrightarrow> P ps Q \<Longrightarrow> Q C S) \<Longrightarrow> sat\<^sub>A (Cond P H) C\<close>
| sat\<^sub>A_Wits [intro!]: \<open>(\<And>S p x. S \<in> C \<Longrightarrow> p \<in> S \<Longrightarrow> x \<notin> params S \<Longrightarrow> set (W p x) \<union> S \<in> C) \<Longrightarrow> sat\<^sub>A (Wits W) C\<close>

inductive_cases (in Params) sat\<^sub>A_CondE[elim!]: \<open>sat\<^sub>A (Cond P H) C\<close>
inductive_cases (in Params) sat\<^sub>A_WitsE[elim!]: \<open>sat\<^sub>A (Wits W) C\<close>

definition prop\<^sub>E :: \<open>('x, 'fm) kind list \<Rightarrow> 'fm set set \<Rightarrow> bool\<close> where
  \<open>prop\<^sub>E Ks C \<equiv> \<forall>K \<in> set Ks. sat\<^sub>E K C\<close>

definition (in Params) prop\<^sub>A :: \<open>('x, 'fm) kind list \<Rightarrow> 'fm set set \<Rightarrow> bool\<close> where
  \<open>prop\<^sub>A Ks C \<equiv> \<forall>K \<in> set Ks. sat\<^sub>A K C\<close>

inductive sat\<^sub>H :: \<open>('x, 'fm) kind \<Rightarrow> 'fm set \<Rightarrow> bool\<close> where
  sat\<^sub>H_Cond [intro!]: \<open>H S \<Longrightarrow> sat\<^sub>H (Cond P H) S\<close>
| sat\<^sub>H_Wits [intro!]: \<open>(\<And>p. p \<in> S \<Longrightarrow> \<exists>x. set (W p x) \<subseteq> S) \<Longrightarrow> sat\<^sub>H (Wits W) S\<close>

inductive_cases sat\<^sub>H_CondE[elim!]: \<open>sat\<^sub>H (Cond P H) C\<close>
inductive_cases sat\<^sub>H_WitsE[elim!]: \<open>sat\<^sub>H (Wits W) C\<close>

definition prop\<^sub>H :: \<open>('x, 'fm) kind list \<Rightarrow> 'fm set \<Rightarrow> bool\<close> where
  \<open>prop\<^sub>H Ks S \<equiv> \<forall>K \<in> set Ks. sat\<^sub>H K S\<close>

theorem sat\<^sub>H_Wits: \<open>sat\<^sub>E (Wits W) C \<Longrightarrow> S \<in> C \<Longrightarrow> maximal C S \<Longrightarrow> sat\<^sub>H (Wits W) S\<close>
  unfolding maximal_def by fast

locale Consistency_Kind = Params map_fm params_fm
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> +
  fixes K :: \<open>('x, 'fm) kind\<close>
  assumes respects_close: \<open>\<And>C. sat\<^sub>E K C \<Longrightarrow> sat\<^sub>E K (close C)\<close>
    and respects_alt: \<open>\<And>C. sat\<^sub>E K C \<Longrightarrow> subset_closed C \<Longrightarrow> sat\<^sub>A K (mk_alt_consistency C)\<close>
    and respects_fin: \<open>\<And>C. subset_closed C \<Longrightarrow> sat\<^sub>A K C \<Longrightarrow> sat\<^sub>A K (mk_finite_char C)\<close>
    and hintikka: \<open>\<And>C S. sat\<^sub>E K C \<Longrightarrow> S \<in> C \<Longrightarrow> maximal C S \<Longrightarrow> sat\<^sub>H K S\<close>

subsection \<open>Consistency Property\<close>

locale Consistency_Kinds = Params map_fm params_fm
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> +
  fixes Ks :: \<open>('x, 'fm) kind list\<close>
  assumes all_kinds: \<open>\<And>K. K \<in> set Ks \<Longrightarrow> Consistency_Kind map_fm params_fm K\<close>
begin

lemma sat\<^sub>E: \<open>K \<in> set Ks \<Longrightarrow> prop\<^sub>E Ks C \<Longrightarrow> sat\<^sub>E K C\<close>
  unfolding prop\<^sub>E_def by blast

lemma prop\<^sub>E_close: \<open>prop\<^sub>E Ks C \<Longrightarrow> prop\<^sub>E Ks (close C)\<close>
  unfolding prop\<^sub>E_def using all_kinds Consistency_Kind.respects_close by fast

lemma prop\<^sub>E_alt: \<open>prop\<^sub>E Ks C \<Longrightarrow> subset_closed C \<Longrightarrow> prop\<^sub>A Ks (mk_alt_consistency C)\<close>
  unfolding prop\<^sub>E_def prop\<^sub>A_def using all_kinds Consistency_Kind.respects_alt by fast

lemma prop\<^sub>E_fin: \<open>subset_closed C \<Longrightarrow> prop\<^sub>A Ks C \<Longrightarrow> prop\<^sub>A Ks (mk_finite_char C)\<close>
  unfolding prop\<^sub>A_def using all_kinds Consistency_Kind.respects_fin by fast

definition mk_alt_fin :: \<open>'fm set set \<Rightarrow> 'fm set set\<close> where
  \<open>mk_alt_fin C \<equiv> mk_finite_char (mk_alt_consistency (close C))\<close>

lemma mk_alt_fin_subset_closed: \<open>subset_closed (mk_alt_fin C)\<close>
  unfolding mk_alt_fin_def using finite_char finite_char_closed by blast

lemma mk_alt_fin_finite_char: \<open>finite_char (mk_alt_fin C)\<close>
  unfolding mk_alt_fin_def using finite_char by blast

lemma mk_alt_fin_in: \<open>S \<in> C \<Longrightarrow> S \<in> mk_alt_fin C\<close>
  unfolding mk_alt_fin_def
  by (meson close_closed close_subset finite_char_subset in_mono mk_alt_consistency_closed mk_alt_consistency_subset)

theorem prop\<^sub>E: \<open>prop\<^sub>E Ks C \<Longrightarrow> prop\<^sub>A Ks (mk_alt_fin C)\<close>
  unfolding mk_alt_fin_def
  by (simp add: prop\<^sub>E_alt prop\<^sub>E_close prop\<^sub>E_fin close_closed mk_alt_consistency_closed)

end

fun (in Params) witness_kinds :: \<open>('x, 'fm) kind list \<Rightarrow> 'fm \<Rightarrow> 'fm set \<Rightarrow> 'fm set\<close> where
  \<open>witness_kinds [] p S = {}\<close>
| \<open>witness_kinds (Cond _ _ # Ks) p S = witness_kinds Ks p S\<close>
| \<open>witness_kinds (Wits W # Ks) p S =
  (let
    rest = witness_kinds Ks p S;
    a = SOME x. x \<notin> params (rest \<union> {p} \<union> S)
   in set (W p a) \<union> rest)\<close>

lemma (in Params) witness_kinds: \<open>Wits W \<in> set Ks \<Longrightarrow> \<exists>x. set (W p x) \<subseteq> witness_kinds Ks p S\<close>
  by (induct Ks p S rule: witness_kinds.induct) (auto simp add: Let_def)

locale Maximal_Consistency = Consistency_Kinds map_fm params_fm Ks
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    Ks :: \<open>('x, 'fm) kind list\<close> +
  fixes r :: \<open>'fm rel\<close>
  assumes Cinfinite_r: \<open>Cinfinite r\<close>
begin

lemma inf_univ: \<open>infinite (UNIV :: 'fm set)\<close>
  using Cinfinite_r card_of_UNIV card_of_ordLeq_infinite unfolding cinfinite_def by blast

lemma wo_rel_r: \<open>wo_rel r\<close>
  by (simp add: Card_order_wo_rel Cinfinite_r)

lemma isLimOrd_r: \<open>isLimOrd r\<close>
  using Cinfinite_r card_order_infinite_isLimOrd cinfinite_def by blast

lemma WELL: \<open>Well_order r\<close>
  by (simp add: Cinfinite_r)

lemma nonempty_Field_r: \<open>Field r \<noteq> {}\<close>
  using Cinfinite_r unfolding cinfinite_def by auto 

lemma aboveS_ne: \<open>n \<in> Field r \<Longrightarrow> aboveS r n \<noteq> {}\<close>
  by (simp add: isLimOrd_r wo_rel.isLimOrd_aboveS wo_rel_r)

lemma params_left: \<open>r \<le>o |- params S| \<Longrightarrow> r \<le>o |- params (set ps \<union> S)|\<close>
  using infinite_params_left Cinfinite_r by (metis Card_order_iff_ordLeq_card_of
      Field_card_of card_of_Card_order cinfinite_def cinfinite_mono ordLeq_transitive)

definition witness :: \<open>'fm \<Rightarrow> 'fm set \<Rightarrow> 'fm set\<close> where
  \<open>witness \<equiv> witness_kinds Ks\<close>

definition extendS :: \<open>'fm set set \<Rightarrow> 'fm \<Rightarrow> 'fm set \<Rightarrow> 'fm set\<close> where
  \<open>extendS C n prev \<equiv> if {n} \<union> prev \<in> C then witness n prev \<union> {n} \<union> prev else prev\<close>

definition extendL :: \<open>'fm set set \<Rightarrow> ('fm \<Rightarrow> 'fm set) \<Rightarrow> 'fm \<Rightarrow> 'fm set\<close> where
  \<open>extendL C rec n \<equiv> \<Union>m \<in> underS r n. rec m\<close>

definition extend :: \<open>'fm set set \<Rightarrow> 'fm set \<Rightarrow> 'fm \<Rightarrow> 'fm set\<close> where
  \<open>extend C S n \<equiv> worecZSL r S (extendS C) (extendL C) n\<close>

lemma adm_woL_extendL: \<open>adm_woL r (extendL C)\<close>
  unfolding extendL_def wo_rel.adm_woL_def[OF wo_rel_r] by blast

definition Extend :: \<open>'fm set set \<Rightarrow> 'fm set \<Rightarrow> 'fm set\<close> where
  \<open>Extend C S \<equiv> \<Union>n \<in> Field r. extend C S n\<close>

lemma finite_witness_kinds: \<open>finite (witness_kinds Qs p S)\<close>
  unfolding witness_def by (induct Qs p S rule: witness_kinds.induct) (simp_all add: Let_def)

lemma finite_witness: \<open>finite (witness p S)\<close>
  unfolding witness_def using finite_witness_kinds .

lemma finite_witness_kinds_params: \<open>finite (params (witness_kinds Qs p S))\<close>
  using finite_witness_kinds by simp

lemma finite_witness_params: \<open>finite (params (witness p S))\<close>
  using finite_witness by simp

lemma extend_zero [simp]: \<open>extend C S (zero r) = S\<close>
  unfolding extend_def wo_rel.worecZSL_zero[OF wo_rel_r adm_woL_extendL] ..

lemma extend_succ [simp]:
  assumes \<open>n \<in> Field r\<close>
  shows \<open>extend C S (succ r n) =
  (if {n} \<union> extend C S n \<in> C then witness n (extend C S n) \<union> {n} \<union> extend C S n else extend C S n)\<close>
  unfolding extend_def extendS_def wo_rel.worecZSL_succ[OF wo_rel_r adm_woL_extendL aboveS_ne[OF assms]] ..

lemma extend_isLim [simp]:
  assumes \<open>isLim r n\<close> \<open>n \<noteq> zero r\<close>
  shows \<open>extend C S n = (\<Union>m \<in> underS r n. extend C S m)\<close>
  unfolding extend_def extendL_def wo_rel.worecZSL_isLim[OF wo_rel_r adm_woL_extendL assms] ..

lemma extend_subset: \<open>n \<in> Field r \<Longrightarrow> S \<subseteq> extend C S n\<close>
proof (induct n rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
  case 1
  then show ?case
    by simp
next
  case (2 i)
  moreover from this have \<open>i \<in> Field r\<close>
    using wo_rel.succ_in[OF wo_rel_r] by (auto intro: FieldI1)
  ultimately show ?case
    by auto
next
  case (3 i)
  then show ?case
    using wo_rel.zero_smallest[OF wo_rel_r] by (metis UN_upper extend_isLim extend_zero underS_I)
qed

lemma Extend_subset: \<open>S \<subseteq> Extend C S\<close>
  unfolding Extend_def using extend_subset nonempty_Field_r by fast

lemma extend_underS: \<open>m \<in> underS r n \<Longrightarrow> extend C S m \<subseteq> extend C S n\<close>
proof (induct n rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
  case 1
  then show ?case
    using wo_rel.underS_zero[OF wo_rel_r] by blast
next
  case (2 i)
  moreover from 2 have \<open>i \<in> Field r\<close>
    using wo_rel.succ_in[OF wo_rel_r] by (auto intro: FieldI1)
  moreover from 2 have \<open>m = i \<or> m \<in> underS r i\<close>
    using wo_rel.less_succ[OF wo_rel_r] by (metis underS_E underS_I)
  ultimately show ?case
    by auto
next
  case (3 i)
  then show ?case
    by auto
qed

lemma extend_under: \<open>m \<in> under r n \<Longrightarrow> extend C S m \<subseteq> extend C S n\<close>
  using extend_underS wo_rel.supr_greater[OF wo_rel_r] wo_rel.supr_under[OF wo_rel_r]
  by (metis emptyE in_Above_under set_eq_subset underS_I under_empty)

lemma params_origin:
  assumes \<open>a \<in> params (extend C S n)\<close>
  shows \<open>a \<in> params S \<or> (\<exists>m \<in> underS r n. a \<in> params (witness m (extend C S m) \<union> {m}))\<close>
  using assms
proof (induct n rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
  case 1
  then show ?case
    by simp
next
  case (2 i)
  then have i: \<open>i \<in> Field r\<close>
    by (meson FieldI1 wo_rel.succ_in_diff wo_rel_r)
  then consider
    (here) \<open>a \<in> params ({i} \<union> witness i (extend C S i))\<close> |
    (there) \<open>a \<in> params (extend C S i)\<close>
    using 2(3)
    by (fastforce split: if_splits)
  then show ?case
  proof cases
    case here
    then show ?thesis
      using 2(1) i wo_rel.succ_diff[OF wo_rel_r] wo_rel.succ_in[OF wo_rel_r]
      by (metis sup_commute underS_I )
  next
    case there
    then show ?thesis
      using 2 by (metis in_mono underS_subset_under wo_rel.underS_succ[OF wo_rel_r])
  next
  qed
next
  case (3 i)
  then obtain j where \<open>j \<in> underS r i\<close> \<open>a \<in> params (extend C S j)\<close>
    unfolding extend_def extendL_def wo_rel.worecZSL_isLim[OF wo_rel_r adm_woL_extendL 3(1-2)]
    by blast
  then show ?case
    using 3 wo_rel.underS_trans[OF wo_rel_r, of _ j i] by meson
qed

lemma is_chain_extend: \<open>wo_rel.is_chain r (extend C S)\<close>
  by (simp add: extend_under wo_rel.is_chain_def wo_rel_r)

lemma extend_in_C_step:
  assumes \<open>prop\<^sub>A Ks C\<close> \<open>{n} \<union> extend C S n \<in> C\<close>
    and inf: \<open>infinite (UNIV - params ({n} \<union> extend C S n))\<close> and n: \<open>n \<in> Field r\<close> 
  shows \<open>extend C S (succ r n) \<in> C\<close>
proof -
  have \<open>set Qs \<subseteq> set Ks \<Longrightarrow> witness_kinds Qs n (extend C S n) \<union> {n} \<union> extend C S n \<in> C\<close> for Qs
  proof (induct Qs)
    case Nil
    then show ?case
      using assms(2) by simp
  next
    case (Cons Q Qs)
    let ?S = \<open>extend C S n\<close>
    let ?rest = \<open>witness_kinds Qs n ?S\<close>

    have Q: \<open>Q \<in> set Ks\<close>
      using Cons.prems by simp

    have *: \<open>?rest \<union> {n} \<union> ?S \<in> C\<close>
      using Cons by simp

    show ?case
    proof (cases Q)
      case (Wits W)

      have \<open>infinite (UNIV - params (?rest \<union> {n} \<union> ?S))\<close>
        using finite_witness_kinds_params inf by (metis UN_Un Un_assoc infinite_Diff_fin_Un)
      then have \<open>\<exists>x. x \<notin> params (?rest \<union> {n} \<union> ?S)\<close>
        by (metis diff_shunt finite.simps subset_eq)
      then obtain a where a:
        \<open>(SOME x. x \<notin> params (?rest \<union> {n} \<union> ?S)) = a\<close>
        \<open>a \<notin> params (?rest \<union> {n} \<union> ?S)\<close>
        by (meson someI_ex)

      have \<open>n \<in> ?rest \<union> {n} \<union> ?S\<close>
        by simp
      then have \<open>\<forall>x. x \<notin> params (?rest \<union> {n} \<union> ?S) \<longrightarrow> set (W n x) \<union> ?rest \<union> {n} \<union> ?S \<in> C\<close>
        using assms(1) * Q Wits unfolding prop\<^sub>A_def Un_assoc by fast
      then have \<open>set (W n a) \<union> ?rest \<union>  {n} \<union> ?S \<in> C\<close>
        using a by fast

      moreover have \<open>witness_kinds (Q # Qs) n ?S = set (W n a) \<union> ?rest\<close>
        using Cons Wits a by (simp add: Let_def)
      ultimately show ?thesis
        by simp
    next
      case (Cond P)
      then show ?thesis
        using * by simp
    qed
  qed
  then have \<open>witness n (extend C S n) \<union> {n} \<union> extend C S n \<in> C\<close>
    unfolding witness_def by blast
  then show ?thesis
    unfolding extend_succ[OF n] using assms(2) by simp
qed

lemma extend_in_C_stop:
  assumes \<open>extend C S n \<in> C\<close>
    and \<open>{n} \<union> extend C S n \<notin> C\<close>
    and \<open>n \<in> Field r\<close>
  shows \<open>extend C S (succ r n) \<in> C\<close>
  using assms extend_succ by auto

lemma extend_in_C:
  assumes \<open>prop\<^sub>A Ks C\<close> \<open>finite_char C\<close> \<open>S \<in> C\<close> \<open>r \<le>o |- params S|\<close> \<open>n \<in> Field r\<close>
  shows \<open>extend C S n \<in> C\<close>
  using assms
proof (induct n rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
  case 1
  then show ?case
    by (simp add: adm_woL_extendL extend_def wo_rel.worecZSL_zero wo_rel_r)
next
  case (2 i)
  then have \<open>i \<in> Field r\<close>
    by (meson WELL well_order_on_domain wo_rel.succ_in_diff[OF wo_rel_r])
  then have *: \<open>|underS r i| <o r\<close>
    using card_of_underS by (simp add: Cinfinite_r)

  let ?params = \<open>\<lambda>k. params ({k} \<union> witness k (extend C S k))\<close>
  let ?X = \<open>\<Union>k \<in> underS r i. ?params k\<close>
  have \<open>|?X| <o r\<close>
  proof (cases \<open>finite (underS r i)\<close>)
    case True
    then have \<open>finite ?X\<close>
      using finite_witness_params by simp
    then show ?thesis
      using Cinfinite_r assms(2) unfolding cinfinite_def by (simp add: finite_ordLess_infinite)
  next
    case False
    moreover have \<open>\<forall>k. finite (?params k)\<close>
      using finite_witness_params by simp
    then have \<open>\<forall>k. |?params k| <o |underS r i|\<close>
      using False by simp
    ultimately have \<open>|?X| \<le>o |underS r i|\<close>
      using card_of_infinite_smaller_Union by fast
    then show ?thesis
      using * ordLeq_ordLess_trans by blast
  qed
  then have \<open>|?X| <o |- params S|\<close>
    using assms(4) ordLess_ordLeq_trans by blast
  moreover have \<open>infinite (- params S)\<close>
    using assms(4) Cinfinite_r unfolding cinfinite_def by (metis Field_card_of ordLeq_finite_Field)
  ultimately have \<open>|- params S - ?X| =o |- params S|\<close>
    using card_of_Un_diff_infinite by blast
  moreover from this have \<open>infinite (- params S - ?X)\<close>
    using \<open>infinite (- params S)\<close> card_of_ordIso_finite by blast
  moreover have \<open>\<And>a. a \<in> params (extend C S i) \<Longrightarrow> a \<in> params S \<or> a \<in> ?X\<close>
    using params_origin by simp
  then have \<open>params (extend C S i) \<subseteq> params S \<union> ?X\<close>
    by fast
  ultimately have \<open>infinite (- params (extend C S i))\<close>
    using infinite_Diff_subset by (metis (no_types, lifting) Compl_eq_Diff_UNIV Set_Diff_Un)
  then have \<open>infinite (- params ({i} \<union> extend C S i))\<close>
    using finite_params_fm by (simp add: Compl_eq_Diff_UNIV infinite_Diff_fin_Un)
  then show ?case
    using assms 2(2) extend_in_C_step extend_in_C_stop wo_rel.succ_in[OF wo_rel_r, of i]
      \<open>i \<in> Field r\<close>  by (metis Compl_eq_Diff_UNIV)
next
  case (3 i)
  show ?case
  proof (rule ccontr)
    assume \<open>extend C S i \<notin> C\<close>
    then obtain S' where S': \<open>S' \<subseteq> (\<Union>n \<in> underS r i. extend C S n)\<close> \<open>S' \<notin> C\<close> \<open>finite S'\<close>
      using 3(5) unfolding finite_char_def extend_def extendL_def
        wo_rel.worecZSL_isLim[OF wo_rel_r adm_woL_extendL 3(1-2)]
      by blast
    then obtain ns where ns: \<open>S' \<subseteq> (\<Union>n \<in> ns. extend C S n)\<close> \<open>ns \<subseteq> underS r i\<close> \<open>finite ns\<close>
      by (metis finite_subset_Union finite_subset_image)
    moreover from this(1) have \<open>ns \<noteq> {}\<close>
      using S' 3 unfolding finite_char_def
      by (metis Union_empty bot.extremum_uniqueI empty_subsetI image_empty)
    ultimately obtain j where \<open>\<forall>n \<in> ns. n \<in> under r j\<close> \<open>j \<in> underS r i\<close>
      using wo_rel.finite_underS_bound wo_rel_r by (metis in_mono)
    then have \<open>\<forall>n \<in> ns. extend C S n \<subseteq> extend C S j\<close>
      using extend_under by fast
    then have \<open>S' \<subseteq> extend C S j\<close>
      using S' ns(1) by blast
    then show False
      using 3(3-) S'(2) ns(2-3) \<open>\<forall>n\<in>ns. n \<in> under r j\<close> \<open>ns \<noteq> {}\<close> \<open>j \<in> underS r i\<close> wo_rel_r
      by (meson Order_Relation.underS_Field finite_char_closed subsetD subset_closed_def)
  qed
qed

lemma Extend_in_C:
  assumes \<open>prop\<^sub>A Ks C\<close> \<open>finite_char C\<close> \<open>S \<in> C\<close> \<open>r \<le>o |- params S|\<close>
  shows \<open>Extend C S \<in> C\<close>
  unfolding Extend_def
  using assms wo_rel.chain_union_closed[OF wo_rel_r] is_chain_extend extend_in_C nonempty_Field_r
  by blast

definition rmaximal :: \<open>'fm set set \<Rightarrow> 'fm set \<Rightarrow> bool\<close> where
  \<open>rmaximal C S \<equiv> \<forall>S' \<in> C. S' \<subseteq> Field r \<longrightarrow> S \<subseteq> S' \<longrightarrow> S = S'\<close>

theorem Extend_rmaximal:
  assumes \<open>subset_closed C\<close>
  shows \<open>rmaximal C (Extend C S)\<close>
  unfolding rmaximal_def Extend_def
proof (intro ballI impI)
  fix S'
  assume *: \<open>S' \<subseteq> Field r\<close> \<open>S' \<in> C\<close> \<open>(\<Union>x \<in> Field r. extend C S x) \<subseteq> S'\<close>
  moreover have \<open>S' \<subseteq> (\<Union>x \<in> Field r. extend C S x)\<close>
  proof (rule ccontr)
    assume \<open>\<not> S' \<subseteq> (\<Union>x \<in> Field r. extend C S x)\<close>
    then have \<open>\<exists>z. z \<in> S' \<and> z \<notin> (\<Union>x \<in> Field r. extend C S x)\<close>
      by blast
    then obtain n where n: \<open>n \<in> S'\<close> \<open>n \<notin> (\<Union>x \<in> Field r. extend C S x)\<close> \<open>n \<in> Field r\<close>
      using *(1) by blast
    then have \<open>{n} \<union> extend C S n \<subseteq> S'\<close>
      using * by blast
    moreover have \<open>\<forall>S \<subseteq> S'. S \<in> C\<close>
      using assms \<open>S' \<in> C\<close> unfolding subset_closed_def by blast
    ultimately have \<open>{n} \<union> extend C S n \<in> C\<close>
      by blast
    then have \<open>n \<in> extend C S (succ r n)\<close>
      using n by simp
    then show False
      using * n(2-3) by (meson UN_I aboveS_ne wo_rel.succ_in_Field wo_rel_r)
  qed
  ultimately show \<open>(\<Union>x \<in> Field r. extend C S x) = S'\<close>
    by simp
qed

definition rwitnessed :: \<open>'fm set \<Rightarrow> bool\<close> where
  \<open>rwitnessed S \<equiv> \<forall>p \<in> S. p \<in> Field r \<longrightarrow> (\<exists>S'. witness p S' \<subseteq> S)\<close>

theorem Extend_rwitnessed:
  assumes \<open>prop\<^sub>A Ks C\<close> \<open>finite_char C\<close> \<open>S \<in> C\<close> \<open>r \<le>o |- params S|\<close>
  shows \<open>rwitnessed (Extend C S)\<close>
  unfolding rwitnessed_def
proof safe
  fix p
  assume \<open>p \<in> Field r\<close> \<open>p \<in> Extend C S\<close>
  then have \<open>{p} \<union> extend C S p \<subseteq> Extend C S\<close>
    unfolding Extend_def by blast
  moreover have \<open>Extend C S \<in> C\<close>
    using Extend_in_C assms by blast
  ultimately have \<open>{p} \<union> extend C S p \<in> C\<close>
    using \<open>finite_char C\<close> finite_char_closed unfolding subset_closed_def by blast
  moreover have \<open>succ r p \<in> Field r\<close>
    using \<open>p \<in> Field r\<close> by (simp add: aboveS_ne wo_rel.succ_in_Field wo_rel_r)
  then have \<open>extend C S (succ r p) \<in> C\<close>
    using assms extend_in_C by blast
  ultimately have \<open>witness p (extend C S p) \<union> {p} \<union> extend C S p \<in> C\<close>
    unfolding extend_succ[OF \<open>p \<in> Field r\<close>] by simp
  then show \<open>\<exists>S'. witness p S' \<subseteq> Extend C S\<close>
    unfolding Extend_def using \<open>p \<in> Field r\<close> \<open>succ r p \<in> Field r\<close> \<open>{p} \<union> extend C S p \<in> C\<close>
    by fastforce
qed

abbreviation mk_mcs :: \<open>'fm set set \<Rightarrow> 'fm set \<Rightarrow> 'fm set\<close> where
  \<open>mk_mcs C S \<equiv> Extend (mk_alt_fin C) S\<close>

theorem mk_mcs_rmaximal: \<open>rmaximal C (mk_mcs C S)\<close>
  using Extend_rmaximal rmaximal_def mk_alt_fin_in mk_alt_fin_subset_closed by meson

theorem mk_mcs_rwitnessed:
  assumes \<open>prop\<^sub>E Ks C\<close> \<open>S \<in> C\<close> \<open>r \<le>o |- params S|\<close>
  shows \<open>rwitnessed (mk_mcs C S)\<close>
  using assms Extend_rwitnessed prop\<^sub>E mk_alt_fin_finite_char mk_alt_fin_in by blast

end

locale Maximal_Consistency_UNIV = Consistency_Kinds map_fm params_fm Ks
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    Ks :: \<open>('x, 'fm) kind list\<close> +
  assumes inf_UNIV: \<open>infinite (UNIV :: 'fm set)\<close>

sublocale Maximal_Consistency_UNIV \<subseteq> Maximal_Consistency map_fm params_fm Ks \<open>|UNIV :: 'fm set|\<close>
proof
  show \<open>Cinfinite |UNIV :: 'fm set|\<close>
    using inf_UNIV unfolding cinfinite_def by simp
qed

context Maximal_Consistency_UNIV
begin

lemma maximal: \<open>rmaximal C S \<longleftrightarrow> maximal C S\<close>
  unfolding maximal_def rmaximal_def by simp

definition witnessed :: \<open>'fm set \<Rightarrow> bool\<close> where
  \<open>witnessed S \<equiv> \<forall>p \<in> S. \<exists>S'. witness p S' \<subseteq> S\<close>

lemma witnessed: \<open>rwitnessed S \<longleftrightarrow> witnessed S\<close>
  unfolding rwitnessed_def witnessed_def by simp

corollary mk_mcs_maximal: \<open>maximal C (mk_mcs C S)\<close>
  using maximal mk_mcs_rmaximal by blast

corollary mk_mcs_witnessed:
  assumes \<open>prop\<^sub>E Ks C\<close> \<open>S \<in> C\<close> \<open>|UNIV :: 'fm set| \<le>o |- params S|\<close>
  shows \<open>witnessed (mk_mcs C S)\<close>
  using assms mk_mcs_rwitnessed witnessed by blast

end

section \<open>Hintikka Sets\<close>

context Maximal_Consistency_UNIV
begin

lemma mk_mcs_hintikka:
  assumes \<open>prop\<^sub>E Ks C\<close> \<open>S \<in> C\<close> \<open>|UNIV :: 'fm set| \<le>o |- params S|\<close>
  shows \<open>prop\<^sub>H Ks (mk_mcs C S)\<close>
  unfolding prop\<^sub>H_def
proof
  fix K
  assume K: \<open>K \<in> set Ks\<close>
  show \<open>sat\<^sub>H K (mk_mcs C S)\<close>
  proof (cases K)
    case (Cond P H)
    moreover have \<open>maximal (mk_alt_fin C) (mk_mcs C S)\<close>
      using Extend_rmaximal mk_alt_fin_subset_closed unfolding maximal by blast
    moreover have \<open>prop\<^sub>A Ks (mk_alt_fin C)\<close>
      using assms(1) prop\<^sub>E by blast
    then have \<open>mk_mcs C S \<in> mk_alt_fin C\<close>
      using assms(2-3) Extend_in_C mk_alt_fin_finite_char mk_alt_fin_in by blast
    moreover have \<open>sat\<^sub>E (Cond P H) (mk_alt_fin C)\<close>
      using \<open>prop\<^sub>A Ks (mk_alt_fin C)\<close> Cond K unfolding prop\<^sub>A_def by fast 
    ultimately show ?thesis
      using K all_kinds Consistency_Kind.hintikka by meson
  next
    case (Wits W)
    have \<open>witnessed (mk_mcs C S)\<close>
      using mk_mcs_witnessed[OF assms(1-3)] .
    then have \<open>\<forall>p \<in> mk_mcs C S. \<exists>x. set (W p x) \<subseteq> mk_mcs C S \<close>
      unfolding witnessed_def witness_def using Wits witness_kinds K by fast 
    then show ?thesis
      using Wits by fast
  qed
qed

end

locale Hintikka = Maximal_Consistency_UNIV map_fm params_fm Ks
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    Ks :: \<open>('x, 'fm) kind list\<close> +
  fixes H :: \<open>'fm set\<close>
  assumes hintikka: \<open>prop\<^sub>H Ks H\<close>
begin

lemma sat\<^sub>H: \<open>K \<in> set Ks \<Longrightarrow> sat\<^sub>H K H\<close>
  using hintikka unfolding prop\<^sub>H_def by blast

end

context Maximal_Consistency_UNIV
begin

theorem mk_mcs_Hintikka:
  assumes \<open>prop\<^sub>E Ks C\<close> \<open>S \<in> C\<close> \<open>|UNIV :: 'fm set| \<le>o |- params S|\<close>
  shows \<open>Hintikka map_fm params_fm Ks (mk_mcs C S)\<close>
  using assms mk_mcs_hintikka by unfold_locales

end

section \<open>Derivational Consistency\<close>

locale Derivational_Kind = Consistency_Kind map_fm params_fm K
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    K :: \<open>('x, 'fm) kind\<close> +
  fixes consistent :: \<open>'fm set \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes kind: \<open>infinite (UNIV :: 'fm set) \<Longrightarrow> sat\<^sub>E K {A. |UNIV :: 'fm set| \<le>o |- params A| \<and> \<turnstile> A}\<close>

locale Derivational_Consistency = Maximal_Consistency map_fm params_fm Ks r
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    Ks :: \<open>('x, 'fm) kind list\<close> and
    r :: \<open>'fm rel\<close> +
  fixes consistent :: \<open>'fm set \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes all_consistent: \<open>infinite (UNIV :: 'fm set) \<Longrightarrow> prop\<^sub>E Ks {A. |UNIV :: 'fm set| \<le>o |- params A| \<and> \<turnstile> A}\<close>
begin

theorem Consistency: \<open>prop\<^sub>E Ks {A. |UNIV :: 'fm set| \<le>o |- params A| \<and> \<turnstile> A}\<close>
  using all_consistent inf_univ unfolding prop\<^sub>E_def by fast

end

section \<open>Weak Derivational Consistency\<close>

locale Weak_Derivational_Kind = Consistency_Kind map_fm params_fm K
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    K :: \<open>('x, 'fm) kind\<close> +
  fixes consistent :: \<open>'fm list \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes kind: \<open>infinite (UNIV :: 'x set) \<Longrightarrow> sat\<^sub>E K {S. \<exists>A. set A = S \<and> \<turnstile> A}\<close>

locale Weak_Derivational_Consistency = Maximal_Consistency map_fm params_fm Ks r
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    Ks :: \<open>('x, 'fm) kind list\<close> and
    r :: \<open>'fm rel\<close> +
  fixes consistent :: \<open>'fm list \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes Consistency: \<open>infinite (UNIV :: 'x set) \<Longrightarrow> prop\<^sub>E Ks {S. \<exists>A. set A = S \<and> \<turnstile> A}\<close>


section \<open>Conflicts\<close>

locale Confl = Params map_fm params_fm
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> +
  fixes classify :: \<open>'fm list \<Rightarrow> 'fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<crossmark>\<close> 50)
  assumes confl_map: \<open>\<And>ps qs f. ps \<leadsto>\<^sub>\<crossmark> qs \<longrightarrow> map (map_fm f) ps \<leadsto>\<^sub>\<crossmark> map (map_fm f) qs\<close>
begin

inductive cond where
  cond [intro!]: \<open>ps \<leadsto>\<^sub>\<crossmark> qs \<Longrightarrow> cond ps (\<lambda>_ S. set qs \<inter> S = {})\<close>

inductive_cases condE[elim!]: \<open>cond ps Q\<close>

inductive hint where
  hint [intro!]: \<open>(\<And>ps qs q. ps \<leadsto>\<^sub>\<crossmark> qs \<Longrightarrow> set ps \<subseteq> H \<Longrightarrow> q \<in> set qs \<Longrightarrow> q \<notin> H) \<Longrightarrow> hint H\<close>

declare hint.simps[simp]

abbreviation kind :: \<open>('x, 'fm) kind\<close> where
  \<open>kind \<equiv> Cond cond hint\<close>

end

sublocale Confl \<subseteq> Consistency_Kind map_fm params_fm kind
proof
  fix C
  assume conflC: \<open>sat\<^sub>E kind C\<close>
  then show \<open>sat\<^sub>E kind (close C)\<close>
  proof safe
    fix S ps qs q
    assume \<open>S \<in> close C\<close>
    then obtain S' where S': \<open>S' \<in> C\<close> and \<open>S \<subseteq> S'\<close>
      unfolding close_def by blast

    assume \<open>set ps \<subseteq> S\<close>
    then have *: \<open>set ps \<subseteq> S'\<close>
      using \<open>S \<subseteq> S'\<close> by blast

    assume **: \<open>ps \<leadsto>\<^sub>\<crossmark> qs\<close>
    then have \<open>\<forall>q \<in> set qs. q \<notin> S'\<close>
      using conflC S' * by blast
    then have \<open>\<forall>q \<in> set qs. q \<notin> S\<close>
      using \<open>S \<subseteq> S'\<close> by blast
    moreover assume \<open>q \<in> set qs\<close> \<open>q \<in> S\<close>
    ultimately show \<open>q \<in> {}\<close>
      using ** by auto
  qed
next
  fix C
  assume conflC: \<open>sat\<^sub>E kind C\<close>
  then show \<open>sat\<^sub>A kind (mk_alt_consistency C)\<close>
  proof safe
    fix S ps qs q

    assume \<open>S \<in> mk_alt_consistency C\<close>
    then obtain f where f: \<open>map_fm f ` S \<in> C\<close>
      unfolding mk_alt_consistency_def by blast

    let ?C = \<open>mk_alt_consistency C\<close>
    let ?S = \<open>map_fm f ` S\<close>

    assume \<open>set ps \<subseteq> S\<close>
    then have *: \<open>set (map (map_fm f) ps) \<subseteq> ?S\<close>
      by auto

    assume \<open>ps \<leadsto>\<^sub>\<crossmark> qs\<close>
    then have \<open>map (map_fm f) ps \<leadsto>\<^sub>\<crossmark> (map (map_fm f) qs)\<close>
      using confl_map by blast
    then have \<open>\<forall>q \<in> set  (map (map_fm f) qs). q \<notin> ?S\<close>
      using conflC f * by blast
    then have \<open>\<forall>q \<in> set qs. map_fm f q \<notin> ?S\<close>
      by simp
    then have \<open>\<forall>q \<in> set qs. q \<notin> S\<close>
      by blast
    moreover assume \<open>q \<in> set qs\<close> \<open>q \<in> S\<close>
    ultimately show \<open>q \<in> {}\<close>
      by auto
  qed
next
  fix C
  assume conflAC: \<open>sat\<^sub>A kind C\<close> and closedC: \<open>subset_closed C\<close>
  then show \<open>sat\<^sub>A kind (mk_finite_char C)\<close>
  proof safe
    fix S ps qs q
    assume \<open>S \<in> mk_finite_char C\<close>
    then have finc: \<open>\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C\<close>
      unfolding mk_finite_char_def by blast

    have sc: \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>
      using closedC unfolding subset_closed_def by blast
    then have sc': \<open>\<And>S' x. x \<union> S' \<in> C \<Longrightarrow> \<forall>S \<subseteq> x \<union> S'. S \<in> C\<close>
      by blast

    assume *: \<open>set ps \<subseteq> S\<close> \<open>ps \<leadsto>\<^sub>\<crossmark> qs\<close> \<open>q \<in> set qs\<close> \<open>q \<in> S\<close>
    then have \<open>{q} \<union> set ps \<in> C\<close>
      using \<open>set ps \<subseteq> S\<close> finc by simp
    then have \<open>q \<in> {}\<close>
      using * conflAC by blast
    then show \<open>q \<in> {}\<close>
      by auto
  qed
next
  fix C S
  assume *: \<open>sat\<^sub>E kind C\<close> \<open>S \<in> C\<close> \<open>maximal C S\<close> 
  show \<open>sat\<^sub>H kind S\<close>
  proof safe
    fix ps qs q
    assume **: \<open>set ps \<subseteq> S\<close> \<open>ps \<leadsto>\<^sub>\<crossmark> qs\<close> \<open>q \<in> set qs\<close> \<open>q \<in> S\<close>
    then show False
      using * by blast
  qed
qed

locale Derivational_Confl = Confl map_fm params_fm classify
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    classify :: \<open>'fm list \<Rightarrow> 'fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<crossmark>\<close> 50) +
  fixes consistent :: \<open>'fm set \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes consistent: \<open>\<And>S ps qs x. set ps \<subseteq> S \<Longrightarrow> ps \<leadsto>\<^sub>\<crossmark> qs \<Longrightarrow> x \<in> set qs \<Longrightarrow> x \<in> S \<Longrightarrow> \<not> \<turnstile> S\<close>

sublocale Derivational_Confl \<subseteq> Derivational_Kind map_fm params_fm kind consistent
  using infinite_params_left consistent by unfold_locales blast+


locale Weak_Derivational_Confl = Confl map_fm params_fm classify
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    classify :: \<open>'fm list \<Rightarrow> 'fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<crossmark>\<close> 50) +
  fixes consistent :: \<open>'fm list \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes consistent: \<open>\<And>A ps qs x. set ps \<subseteq> set A \<Longrightarrow> ps \<leadsto>\<^sub>\<crossmark> qs \<Longrightarrow> x \<in> set qs \<Longrightarrow> x \<in> set A \<Longrightarrow> \<not> \<turnstile> A\<close>

sublocale Weak_Derivational_Confl \<subseteq> Weak_Derivational_Kind map_fm params_fm kind consistent
  using infinite_params_left consistent by unfold_locales blast+

section \<open>Alpha\<close>

locale Alpha = Params map_fm params_fm
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> +
  fixes classify :: \<open>'fm list \<Rightarrow> 'fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<alpha>\<close> 50)
  assumes alpha_map: \<open>\<And>ps qs f. ps \<leadsto>\<^sub>\<alpha> qs \<longrightarrow> map (map_fm f) ps \<leadsto>\<^sub>\<alpha> map (map_fm f) qs\<close>
begin

inductive cond where
  cond [intro!]: \<open>ps \<leadsto>\<^sub>\<alpha> qs \<Longrightarrow> cond ps (\<lambda>C S. set qs \<union> S \<in> C)\<close>

inductive_cases condE[elim!]: \<open>cond ps Q\<close>

inductive hint where
  hint [intro!]: \<open>(\<And>ps qs q. ps \<leadsto>\<^sub>\<alpha> qs \<Longrightarrow> set ps \<subseteq> H \<Longrightarrow> q \<in> set qs \<Longrightarrow> q \<in> H) \<Longrightarrow> hint H\<close>

declare hint.simps[simp]

abbreviation kind :: \<open>('x, 'fm) kind\<close> where
  \<open>kind \<equiv> Cond cond hint\<close>

end

sublocale Alpha \<subseteq> Consistency_Kind map_fm params_fm kind
proof
  fix C
  assume alphaC: \<open>sat\<^sub>E kind C\<close>
  then show \<open>sat\<^sub>E kind (close C)\<close>
  proof safe
    fix S ps qs q
    assume \<open>S \<in> close C\<close>
    then obtain S' where S': \<open>S' \<in> C\<close> and \<open>S \<subseteq> S'\<close>
      unfolding close_def by blast

    assume \<open>set ps \<subseteq> S\<close> \<open>ps \<leadsto>\<^sub>\<alpha> qs\<close>
    then have *: \<open>set ps \<subseteq> S'\<close>
      using \<open>S \<subseteq> S'\<close> by blast

    assume **: \<open>ps \<leadsto>\<^sub>\<alpha> qs\<close>
    then have \<open>set qs \<union> S' \<in> C\<close>
      using alphaC S' * by blast
    then show  \<open>set qs \<union> S \<in> close C\<close>
      using \<open>S \<subseteq> S'\<close> subset_in_close by blast
  qed
next
  fix C
  assume alphaC: \<open>sat\<^sub>E kind C\<close>
  then show \<open>sat\<^sub>A kind (mk_alt_consistency C)\<close>
  proof safe
    fix S ps qs

    assume \<open>S \<in> mk_alt_consistency C\<close>
    then obtain f where f: \<open>map_fm f ` S \<in> C\<close>
      unfolding mk_alt_consistency_def by blast

    let ?C = \<open>mk_alt_consistency C\<close>
    let ?S = \<open>map_fm f ` S\<close>

    assume \<open>set ps \<subseteq> S\<close>
    then have *: \<open>set (map (map_fm f) ps) \<subseteq> ?S\<close>
      by auto

    assume \<open>ps \<leadsto>\<^sub>\<alpha> qs\<close>
    then have \<open>map (map_fm f) ps \<leadsto>\<^sub>\<alpha> (map (map_fm f) qs)\<close>
      using alpha_map by blast
    then have \<open>set (map (map_fm f) qs) \<union> ?S \<in> C\<close>
      using alphaC * f by blast
    then show \<open>set qs \<union> S \<in> ?C\<close>
      unfolding mk_alt_consistency_def by (auto simp: image_Un)
  qed
next
  fix C
  assume alphaAC: \<open>sat\<^sub>A kind C\<close> and closedC: \<open>subset_closed C\<close>
  then show \<open>sat\<^sub>A kind (mk_finite_char C)\<close>
  proof safe
    fix S ps qs q
    assume \<open>S \<in> mk_finite_char C\<close>
    then have finc: \<open>\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C\<close>
      unfolding mk_finite_char_def by blast

    have sc: \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>
      using closedC unfolding subset_closed_def by blast
    then have sc': \<open>\<And>S' x. x \<union> S' \<in> C \<Longrightarrow> \<forall>S \<subseteq> x \<union> S'. S \<in> C\<close>
      by blast

    assume *: \<open>set ps \<subseteq> S\<close> and **: \<open>ps \<leadsto>\<^sub>\<alpha> qs\<close>

    show \<open>set qs \<union> S \<in> mk_finite_char C\<close>
      unfolding mk_finite_char_def
    proof safe
      fix S'
      let ?S' = \<open>set ps \<union> (S' - set qs)\<close>

      assume \<open>S' \<subseteq> set qs \<union> S\<close> and \<open>finite S'\<close>
      then have \<open>?S' \<subseteq> S\<close>
        using * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite S'\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      then have \<open>set qs \<union> ?S' \<in> C\<close>
        using ** alphaAC by fast
      then show \<open>S' \<in> C\<close>
        using sc by fast
    qed
  qed
next
  fix C S
  assume *: \<open>sat\<^sub>E kind C\<close> \<open>S \<in> C\<close> \<open>maximal C S\<close> 
  show \<open>sat\<^sub>H kind S\<close>
  proof safe
    fix ps qs q
    assume **: \<open>set ps \<subseteq> S\<close> \<open>ps \<leadsto>\<^sub>\<alpha> qs\<close>
    then have \<open>set qs \<union> S \<in> C\<close>
      using * by blast
    moreover assume \<open>q \<in> set qs\<close>
    ultimately show \<open>q \<in> S\<close>
      using \<open>maximal C S\<close> unfolding maximal_def by fast
  qed
qed

locale Derivational_Alpha = Alpha map_fm params_fm classify
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    classify :: \<open>'fm list \<Rightarrow> 'fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<alpha>\<close> 50) +
  fixes consistent :: \<open>'fm set \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes consistent: \<open>\<And>S ps qs. set ps \<subseteq> S \<Longrightarrow> ps \<leadsto>\<^sub>\<alpha> qs \<Longrightarrow> \<turnstile> S \<Longrightarrow> \<turnstile> set qs \<union> S\<close>

sublocale Derivational_Alpha \<subseteq> Derivational_Kind map_fm params_fm kind consistent
  using infinite_params_left consistent by unfold_locales blast+


locale Weak_Derivational_Alpha = Alpha map_fm params_fm classify
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    classify :: \<open>'fm list \<Rightarrow> 'fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<alpha>\<close> 50) +
  fixes consistent :: \<open>'fm list \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes consistent: \<open>\<And>A ps qs. set ps \<subseteq> set A \<Longrightarrow> ps \<leadsto>\<^sub>\<alpha> qs \<Longrightarrow> \<turnstile> A \<Longrightarrow> \<turnstile> qs @ A\<close>

sublocale Weak_Derivational_Alpha \<subseteq> Weak_Derivational_Kind map_fm params_fm kind consistent
proof
  show \<open>sat\<^sub>E kind {S. \<exists>A. set A = S \<and> \<turnstile> A}\<close>
  proof safe
    fix ps qs A
    assume \<open>set ps \<subseteq> set A\<close> \<open>ps \<leadsto>\<^sub>\<alpha> qs\<close> \<open>\<turnstile> A\<close>
    then show \<open>\<exists>B. set B = set qs \<union> set A \<and> \<turnstile> B\<close>
      using consistent[of ps A qs] by (meson set_append)
  qed
qed

section \<open>Beta\<close>

locale Beta = Params map_fm params_fm
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> +
  fixes classify :: \<open>'fm list \<Rightarrow> 'fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<beta>\<close> 50)
  assumes beta_map: \<open>\<And>ps qs f. ps \<leadsto>\<^sub>\<beta> qs \<longrightarrow> map (map_fm f) ps \<leadsto>\<^sub>\<beta> map (map_fm f) qs\<close>
begin

inductive cond where
  cond [intro!]: \<open>ps \<leadsto>\<^sub>\<beta> qs \<Longrightarrow> cond ps (\<lambda>C S. \<exists>q \<in> set qs. {q} \<union> S \<in> C)\<close>

inductive_cases condE[elim!]: \<open>cond ps Q\<close>

inductive hint where
  hint [intro!]: \<open>(\<And>ps qs. ps \<leadsto>\<^sub>\<beta> qs \<Longrightarrow> set ps \<subseteq> H \<Longrightarrow> \<exists>q \<in> set qs. q \<in> H) \<Longrightarrow> hint H\<close>

declare hint.simps[simp]

abbreviation kind :: \<open>('x, 'fm) kind\<close> where
  \<open>kind \<equiv> Cond cond hint\<close>

end

sublocale Beta \<subseteq> Consistency_Kind map_fm params_fm kind
proof
  fix C
  assume betaC: \<open>sat\<^sub>E kind C\<close>
  then show \<open>sat\<^sub>E kind (close C)\<close>
  proof safe
    fix S ps qs q
    assume \<open>S \<in> close C\<close>
    then obtain S' where S': \<open>S' \<in> C\<close> and \<open>S \<subseteq> S'\<close>
      unfolding close_def by blast

    assume \<open>set ps \<subseteq> S\<close> \<open>ps \<leadsto>\<^sub>\<beta> qs\<close>
    then have *: \<open>set ps \<subseteq> S'\<close>
      using \<open>S \<subseteq> S'\<close> by blast

    assume **: \<open>ps \<leadsto>\<^sub>\<beta> qs\<close>
    then have \<open>\<exists>q \<in> set qs. {q} \<union> S' \<in> C\<close>
      using betaC S' * by blast
    then show \<open>\<exists>q \<in> set qs. insert q S \<in> close C\<close>
      using \<open>S \<subseteq> S'\<close> subset_in_close by (metis insert_is_Un)
  qed
next
  fix C
  assume betaC: \<open>sat\<^sub>E kind C\<close>
  then show \<open>sat\<^sub>A kind (mk_alt_consistency C)\<close>
  proof safe
    fix S ps qs

    assume \<open>S \<in> mk_alt_consistency C\<close>
    then obtain f where f: \<open>map_fm f ` S \<in> C\<close>
      unfolding mk_alt_consistency_def by blast

    let ?C = \<open>mk_alt_consistency C\<close>
    let ?S = \<open>map_fm f ` S\<close>

    assume \<open>set ps \<subseteq> S\<close>
    then have *: \<open>set (map (map_fm f) ps) \<subseteq> ?S\<close>
      by auto

    assume \<open>ps \<leadsto>\<^sub>\<beta> qs\<close>
    then have \<open>map (map_fm f) ps \<leadsto>\<^sub>\<beta> (map (map_fm f) qs)\<close>
      using beta_map by blast
    then have \<open>\<exists>q \<in> set (map (map_fm f) qs). {q} \<union> ?S \<in> C\<close>
      using betaC * f by blast
    then show \<open>\<exists>q \<in> set qs. insert q S \<in> ?C\<close>
      unfolding mk_alt_consistency_def by (auto simp: image_Un)
  qed
next
  fix C
  assume betaAC: \<open>sat\<^sub>A kind C\<close> and closedC: \<open>subset_closed C\<close>
  then show \<open>sat\<^sub>A kind (mk_finite_char C)\<close>
  proof safe
    fix S ps qs q
    assume \<open>S \<in> mk_finite_char C\<close>
    then have finc: \<open>\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C\<close>
      unfolding mk_finite_char_def by blast

    have sc: \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>
      using closedC unfolding subset_closed_def by blast
    then have sc': \<open>\<And>S' x. x \<union> S' \<in> C \<Longrightarrow> \<forall>S \<subseteq> x \<union> S'. S \<in> C\<close>
      by blast

    assume *: \<open>set ps \<subseteq> S\<close> and **: \<open>ps \<leadsto>\<^sub>\<beta> qs\<close>

    show \<open>\<exists>q \<in> set qs. insert q S \<in> mk_finite_char C\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then have \<open>\<forall>q \<in> set qs. \<exists>Sq. Sq \<subseteq> insert q S \<and> finite Sq \<and> Sq \<notin> C\<close>
        unfolding mk_finite_char_def by blast
      then obtain f where f: \<open>\<forall>q \<in> set qs. f q \<subseteq> insert q S \<and> finite (f q) \<and> f q \<notin> C\<close>
        by metis

      let ?S' = \<open>set ps \<union> \<Union>{f q - {q} |q. q \<in> set qs}\<close>

      have \<open>?S' \<subseteq> S\<close>
        using * f by fast
      moreover have \<open>finite ?S'\<close>
        using f by auto
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      then have \<open>\<exists>q \<in> set qs. {q} \<union> ?S' \<in> C\<close>
        using ** betaAC by fast
      then have \<open>\<exists>q \<in> set qs. f q \<in> C\<close>
        using sc' by blast
      then show False
        using f by blast
    qed
  qed
next
  fix C S
  assume *: \<open>sat\<^sub>E kind C\<close> \<open>S \<in> C\<close> \<open>maximal C S\<close> 
  show \<open>sat\<^sub>H kind S\<close>
  proof safe
    fix ps qs
    assume **: \<open>set ps \<subseteq> S\<close> \<open>ps \<leadsto>\<^sub>\<beta> qs\<close>
    then have \<open>\<exists>q \<in> set qs. {q} \<union> S \<in> C\<close>
      using * by blast
    then show \<open>\<exists>q \<in> set qs. q \<in> S\<close>
      using \<open>maximal C S\<close> unfolding maximal_def by fast
  qed
qed

locale Derivational_Beta = Beta map_fm params_fm classify
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    classify :: \<open>'fm list \<Rightarrow> 'fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<beta>\<close> 50) +
  fixes consistent :: \<open>'fm set \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes consistent: \<open>\<And>S ps qs. set ps \<subseteq> S \<Longrightarrow> ps \<leadsto>\<^sub>\<beta> qs \<Longrightarrow> \<turnstile> S \<Longrightarrow> \<exists>q \<in> set qs. \<turnstile> {q} \<union> S\<close>

sublocale Derivational_Beta \<subseteq> Derivational_Kind map_fm params_fm kind consistent
proof
  assume inf: \<open>infinite (UNIV :: 'fm set)\<close>
  then show \<open>sat\<^sub>E kind {A. |UNIV :: 'fm set| \<le>o |- params A| \<and> \<turnstile> A}\<close>
  proof safe
    fix S ps qs
    assume *: \<open>set ps \<subseteq> S\<close> \<open>ps \<leadsto>\<^sub>\<beta> qs\<close> \<open>\<turnstile> S\<close>
    then have \<open>\<exists>q \<in> set qs. \<turnstile> {q} \<union> S\<close>
      using consistent by blast
    moreover assume \<open>|UNIV :: 'fm set| \<le>o |- params S|\<close> 
    ultimately show \<open>\<exists>q\<in>set qs. insert q S \<in> {A. |UNIV :: 'fm set| \<le>o |- params A| \<and> \<turnstile> A}\<close>
      using infinite_params_left[OF inf]
      by (metis (no_types, lifting) empty_set insert_code(1) insert_is_Un mem_Collect_eq)
  qed
qed

locale Weak_Derivational_Beta = Beta map_fm params_fm classify
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    classify :: \<open>'fm list \<Rightarrow> 'fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<beta>\<close> 50) +
  fixes consistent :: \<open>'fm list \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes consistent: \<open>\<And>A ps qs. set ps \<subseteq> set A \<Longrightarrow> ps \<leadsto>\<^sub>\<beta> qs \<Longrightarrow> \<turnstile> A \<Longrightarrow> \<exists>q \<in> set qs. \<turnstile> q # A\<close>

sublocale Weak_Derivational_Beta \<subseteq> Weak_Derivational_Kind map_fm params_fm kind consistent
proof
  show \<open>sat\<^sub>E kind {S. \<exists>A. set A = S \<and> \<turnstile> A}\<close>
  proof safe
    fix ps qs A
    assume *: \<open>set ps \<subseteq> set A\<close> \<open>ps \<leadsto>\<^sub>\<beta> qs\<close> \<open>\<turnstile> A\<close>
    then have \<open>\<exists>q \<in> set qs. \<turnstile> q # A\<close>
      using consistent by blast
    then show \<open>\<exists>q\<in>set qs. insert q (set A) \<in> {S. \<exists>A. set A = S \<and> \<turnstile> A}\<close>
      by (metis (mono_tags, lifting) CollectI list.simps(15))
  qed
qed

section \<open>Gamma\<close>

locale Gamma = Params map_fm params_fm
  for
    map_tm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'tm \<Rightarrow> 'tm\<close> and
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> +
  fixes classify :: \<open>'fm list \<Rightarrow> ('fm set \<Rightarrow> 'tm set) \<times> ('tm \<Rightarrow> 'fm list) \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<gamma>\<close> 50)
  assumes gamma_map: \<open>\<And>ps F qs f. ps \<leadsto>\<^sub>\<gamma> (F, qs) \<Longrightarrow> \<exists>G rs. map (map_fm f) ps \<leadsto>\<^sub>\<gamma> (G, rs) \<and>
      (\<forall>S. map_tm f ` F S \<subseteq> G (map_fm f ` S)) \<and>
      (\<forall>t. map (map_fm f) (qs t) = rs (map_tm f t))\<close>
    and gamma_mono: \<open>\<And>ps F qs S S'. ps \<leadsto>\<^sub>\<gamma> (F, qs) \<Longrightarrow> S \<subseteq> S' \<Longrightarrow> F S \<subseteq> F S'\<close>
    and gamma_fin: \<open>\<And>ps F qs t A. ps \<leadsto>\<^sub>\<gamma> (F, qs) \<Longrightarrow> t \<in> F A \<Longrightarrow> \<exists>B \<subseteq> A. finite B \<and> t \<in> F B\<close>
begin

inductive cond where
  cond [intro!]: \<open>ps \<leadsto>\<^sub>\<gamma> (F, qs) \<Longrightarrow> cond ps (\<lambda>C S. \<forall>t \<in> F S. set (qs t) \<union> S \<in> C)\<close>

inductive_cases condE[elim!]: \<open>cond ps Q\<close>

inductive hint where
  hint [intro!]: \<open>(\<And>ps F qs. ps \<leadsto>\<^sub>\<gamma> (F, qs) \<Longrightarrow> set ps \<subseteq> H \<Longrightarrow> \<forall>t \<in> F H. set (qs t) \<subseteq> H) \<Longrightarrow> hint H\<close>

declare hint.simps[simp]

abbreviation kind :: \<open>('x, 'fm) kind\<close> where
  \<open>kind \<equiv> Cond cond hint\<close>

end

sublocale Gamma \<subseteq> Consistency_Kind map_fm params_fm kind
proof
  fix C
  assume gammaC: \<open>sat\<^sub>E kind C\<close>
  then show \<open>sat\<^sub>E kind (close C)\<close>
  proof safe
    fix S ps qs F t
    assume \<open>S \<in> close C\<close>
    then obtain S' where S': \<open>S' \<in> C\<close> and \<open>S \<subseteq> S'\<close>
      unfolding close_def by blast

    assume \<open>set ps \<subseteq> S\<close>
    then have *: \<open>set ps \<subseteq> S'\<close>
      using \<open>S \<subseteq> S'\<close> by blast

    assume **: \<open>ps \<leadsto>\<^sub>\<gamma> (F, qs)\<close> \<open>t \<in> F S\<close>
    then have \<open>t \<in> F S'\<close>
      using ** gamma_mono \<open>S \<subseteq> S'\<close> by blast
    then have \<open>set (qs t) \<union> S' \<in> C\<close>
      using gammaC S' * ** by blast
    then have \<open>set (qs t) \<union> S \<in> close C\<close>
      using \<open>S \<subseteq> S'\<close> subset_in_close by blast
    then show \<open>set (qs t) \<union> S \<in> close C\<close>
      by (meson close_closed equalityE subset_closed_def sup.mono)
  qed
next
  fix C
  assume gammaC: \<open>sat\<^sub>E kind C\<close>
  then show \<open>sat\<^sub>A kind (mk_alt_consistency C)\<close>
  proof safe
    fix S ps F qs t

    assume \<open>S \<in> mk_alt_consistency C\<close>
    then obtain f where f: \<open>map_fm f ` S \<in> C\<close>
      unfolding mk_alt_consistency_def by blast

    let ?C = \<open>mk_alt_consistency C\<close>
    let ?S = \<open>map_fm f ` S\<close>

    assume \<open>set ps \<subseteq> S\<close>
    then have *: \<open>set (map (map_fm f) ps) \<subseteq> ?S\<close>
      by auto

    assume **: \<open>ps \<leadsto>\<^sub>\<gamma> (F, qs)\<close> and t: \<open>t \<in> F S\<close>
    obtain rs G where rs:
      \<open>map (map_fm f) ps \<leadsto>\<^sub>\<gamma> (G, rs)\<close>
      \<open>\<forall>S. map_tm f ` F S \<subseteq> G (map_fm f ` S)\<close>
      \<open>\<forall>t. map (map_fm f) (qs t) = rs (map_tm f t)\<close>
      using gamma_map ** by meson
    then have \<open>set (rs (map_tm f t)) \<union> ?S \<in> C\<close>
      using gammaC f * t by blast
    then have \<open>set (map (map_fm f) (qs t)) \<union> ?S \<in> C\<close>
      using rs by simp
    then show \<open>set (qs t) \<union> S \<in> ?C\<close>
      unfolding mk_alt_consistency_def by (auto simp: image_Un)
  qed
next
  fix C
  assume gammaAC: \<open>sat\<^sub>A kind C\<close> and closedC: \<open>subset_closed C\<close>
  then show \<open>sat\<^sub>A kind (mk_finite_char C)\<close>
  proof safe
    fix S ps F qs t
    assume \<open>S \<in> mk_finite_char C\<close>
    then have finc: \<open>\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C\<close>
      unfolding mk_finite_char_def by blast

    have sc: \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>
      using closedC unfolding subset_closed_def by blast
    then have sc': \<open>\<And>S' x. x \<union> S' \<in> C \<Longrightarrow> \<forall>S \<subseteq> x \<union> S'. S \<in> C\<close>
      by blast

    assume *: \<open>set ps \<subseteq> S\<close> and **: \<open>ps \<leadsto>\<^sub>\<gamma> (F, qs)\<close> and t: \<open>t \<in> F S\<close>

    show \<open>set (qs t) \<union> S \<in> mk_finite_char C\<close>
      unfolding mk_finite_char_def 
    proof safe
      fix S'
      assume 1: \<open>S' \<subseteq> set (qs t) \<union> S\<close> and 2: \<open>finite S'\<close>

      obtain A where A: \<open>A \<subseteq> S\<close> \<open>finite A\<close> \<open>S' \<subseteq> set (qs t) \<union> A\<close> 
        using 1 2 by (meson Diff_subset_conv equalityD2 finite_Diff)

      obtain B where B: \<open>B \<subseteq> S\<close> \<open>finite B\<close> \<open>t \<in> F B\<close>
        using ** t gamma_fin by meson

      let ?S = \<open>set ps \<union> A \<union> B\<close>

      have \<open>finite ?S\<close>
        using A(2) B(2) by blast
      moreover have \<open>?S \<subseteq> S\<close>
        using * A(1) B(1) by simp
      ultimately have \<open>?S \<in> C\<close>
        using finc by simp

      moreover have \<open>set ps \<subseteq> ?S\<close>
        by blast
      moreover have \<open>t \<in> F ?S\<close>
        using ** B(3) gamma_mono by blast
      ultimately have \<open>set (qs t) \<union> ?S \<in> C\<close>
        using ** gammaAC by blast

      moreover have \<open>S' \<subseteq> set (qs t) \<union> ?S\<close>
        using A(3) by blast
      ultimately show \<open>S' \<in> C\<close>
        using sc by blast
    qed
  qed
next
  fix C S
  assume *: \<open>sat\<^sub>E kind C\<close> \<open>S \<in> C\<close> \<open>maximal C S\<close> 
  show \<open>sat\<^sub>H kind S\<close>
  proof safe
    fix ps F qs t
    assume **: \<open>set ps \<subseteq> S\<close> \<open>ps \<leadsto>\<^sub>\<gamma> (F, qs)\<close>
    then have \<open>\<forall>t \<in> F S. set (qs t) \<union> S \<in> C\<close>
      using * by blast
    then have \<open>\<forall>t \<in> F S. set (qs t) \<subseteq> S\<close>
      using \<open>maximal C S\<close> unfolding maximal_def by fast
    then show \<open>t \<in> F S \<Longrightarrow> x \<in> set (qs t) \<Longrightarrow> x \<in> S\<close> for x
      by blast
  qed
qed

locale Derivational_Gamma = Gamma map_tm map_fm params_fm classify
  for
    map_tm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'tm \<Rightarrow> 'tm\<close> and
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    classify :: \<open>'fm list \<Rightarrow> ('fm set \<Rightarrow> 'tm set) \<times> ('tm \<Rightarrow> 'fm list) \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<gamma>\<close> 50) +
  fixes consistent :: \<open>'fm set \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes consistent: \<open>\<And>S ps F qs t. set ps \<subseteq> S \<Longrightarrow> ps \<leadsto>\<^sub>\<gamma> (F, qs) \<Longrightarrow> t \<in> F S \<Longrightarrow> \<turnstile> S \<Longrightarrow> \<turnstile> set (qs t) \<union> S\<close>

sublocale Derivational_Gamma \<subseteq> Derivational_Kind map_fm params_fm kind consistent
  using infinite_params_left consistent by unfold_locales blast+

locale Weak_Derivational_Gamma = Gamma map_tm map_fm params_fm classify
  for
    map_tm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'tm \<Rightarrow> 'tm\<close> and
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    classify :: \<open>'fm list \<Rightarrow> ('fm set \<Rightarrow> 'tm set) \<times> ('tm \<Rightarrow> 'fm list) \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<gamma>\<close> 50) +
  fixes consistent :: \<open>'fm list \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes consistent: \<open>\<And>A ps F qs t. set ps \<subseteq> set A \<Longrightarrow> ps \<leadsto>\<^sub>\<gamma> (F, qs) \<Longrightarrow> t \<in> F (set A) \<Longrightarrow> \<turnstile> A \<Longrightarrow> \<turnstile> qs t @ A\<close>

sublocale Weak_Derivational_Gamma \<subseteq> Weak_Derivational_Kind map_fm params_fm kind consistent
proof
  show \<open>sat\<^sub>E kind {S. \<exists>A. set A = S \<and> \<turnstile> A}\<close>
  proof safe
    fix ps qs A F t
    assume *: \<open>set ps \<subseteq> set A\<close> \<open>ps \<leadsto>\<^sub>\<gamma> (F, qs)\<close> \<open>\<turnstile> A\<close> \<open>t \<in> F (set A)\<close>
    then show \<open>\<exists>B. set B = set (qs t) \<union> set A \<and> \<turnstile> B\<close>
      using consistent[of ps A F qs t] by (meson set_append)
  qed
qed

locale Gamma_UNIV = Params map_fm params_fm
  for
    map_tm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'tm \<Rightarrow> 'tm\<close> and
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> +
  fixes classify :: \<open>'fm list \<Rightarrow> ('tm \<Rightarrow> 'fm list) \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<gamma>''\<close> 50)
  assumes gamma_map_UNIV: \<open>\<And>ps qs f. ps \<leadsto>\<^sub>\<gamma>' qs \<Longrightarrow> \<exists>rs. map (map_fm f) ps \<leadsto>\<^sub>\<gamma>' rs \<and>
      (\<forall>t. map (map_fm f) (qs t) = rs (map_tm f t))\<close>
begin

abbreviation (input) classify_UNIV where
  \<open>classify_UNIV \<equiv> \<lambda>ps (F, qs). (F = (\<lambda>_. UNIV)) \<and> ps \<leadsto>\<^sub>\<gamma>' qs\<close>

end

sublocale Gamma_UNIV \<subseteq> Gamma map_tm map_fm params_fm classify_UNIV
proof
  show \<open>\<And>ps F qs f.
       (case (F, qs) of (F, qs) \<Rightarrow> F = (\<lambda>_. UNIV) \<and> ps \<leadsto>\<^sub>\<gamma>' qs) \<Longrightarrow>
       \<exists>G rs.
          (case (G, rs) of (F, qs) \<Rightarrow> F = (\<lambda>_. UNIV) \<and> map (map_fm f) ps \<leadsto>\<^sub>\<gamma>' qs) \<and>
          (\<forall>S. map_tm f ` F S \<subseteq> G (map_fm f ` S)) \<and> (\<forall>t. map (map_fm f) (qs t) = rs (map_tm f t))\<close>
    using gamma_map_UNIV image_subset_iff by fastforce
  show \<open>\<And>ps F qs S S'. (case (F, qs) of (F, qs) \<Rightarrow> F = (\<lambda>_. UNIV) \<and> ps \<leadsto>\<^sub>\<gamma>' qs) \<Longrightarrow> S \<subseteq> S' \<Longrightarrow> F S \<subseteq> F S'\<close>
    by simp
  show \<open>\<And>ps F qs t A. (case (F, qs) of (F, qs) \<Rightarrow> F = (\<lambda>_. UNIV) \<and> ps \<leadsto>\<^sub>\<gamma>' qs) \<Longrightarrow> t \<in> F A \<Longrightarrow> \<exists>B\<subseteq>A. finite B \<and> t \<in> F B\<close>
    by blast
qed

section \<open>Delta\<close>

locale Delta = Params map_fm params_fm
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> +
  fixes delta_fun :: \<open>'fm \<Rightarrow> 'x \<Rightarrow> 'fm list\<close>
  assumes delta_map: \<open>\<And>p f x. delta_fun (map_fm f p) (f x) = map (map_fm f) (delta_fun p x)\<close>
begin

abbreviation \<open>kind \<equiv> Wits delta_fun\<close>
end

sublocale Delta \<subseteq> Consistency_Kind map_fm params_fm kind
proof
  fix C
  assume deltaC: \<open>sat\<^sub>E kind C\<close>
  then show \<open>sat\<^sub>E kind (close C)\<close>
  proof safe
    fix S p qs q
    assume \<open>S \<in> close C\<close>
    then obtain S' where S': \<open>S' \<in> C\<close> and \<open>S \<subseteq> S'\<close>
      unfolding close_def by blast

    assume \<open>p \<in> S\<close>
    then have *: \<open>p \<in> S'\<close>
      using \<open>S \<subseteq> S'\<close> by blast

    have \<open>\<exists>x. set (delta_fun p x) \<union> S' \<in> C\<close>
      using deltaC S' * by blast
    then show \<open>\<exists>x. set (delta_fun p x) \<union> S \<in> close C\<close>
      using \<open>S \<subseteq> S'\<close> by (metis subset_in_close)

  qed
next
  fix C
  assume deltaC: \<open>sat\<^sub>E kind C\<close>
  then show \<open>sat\<^sub>A kind (mk_alt_consistency C)\<close>
  proof safe
    fix S p qs x

    assume \<open>S \<in> mk_alt_consistency C\<close>
    then obtain f where f: \<open>map_fm f ` S \<in> C\<close>
      unfolding mk_alt_consistency_def by blast

    let ?C = \<open>mk_alt_consistency C\<close>
    let ?S = \<open>map_fm f ` S\<close>

    assume \<open>p \<in> S\<close>
    then have *: \<open>map_fm f p \<in> ?S\<close>
      by auto

    assume x: \<open>x \<notin> params S\<close>
    obtain y where y: \<open>set (delta_fun (map_fm f p) y) \<union> ?S \<in> C\<close>
      using deltaC f * by blast

    let ?g = \<open>f(x := y)\<close>

    have \<open>\<forall>x \<in> params S. f x = ?g x\<close>
      using x by simp
    then have S: \<open>\<forall>q \<in> S. map_fm ?g q = map_fm f q\<close>
      using map_params_fm by simp
    then have \<open>map_fm ?g p = map_fm f p\<close>
      using \<open>p \<in> S\<close> by auto

    moreover have \<open>set (delta_fun (map_fm f p) (?g x)) \<union> ?S \<in> C\<close>
      using y by simp
    ultimately have \<open>set (map (map_fm ?g) (delta_fun p x)) \<union> ?S \<in> C\<close>
      using delta_map by metis
    then have \<open>\<exists>f. set (map (map_fm f) (delta_fun p x)) \<union> map_fm f ` S \<in> C\<close>
      using S by (metis image_cong)
    then show \<open>set (delta_fun p x) \<union> S \<in> ?C\<close>
      unfolding mk_alt_consistency_def
      by (metis (mono_tags, lifting) image_Un image_set mem_Collect_eq)
  qed
next
  fix C
  assume deltaAC: \<open>sat\<^sub>A kind C\<close> and closedC: \<open>subset_closed C\<close>
  then show \<open>sat\<^sub>A kind (mk_finite_char C)\<close>
  proof safe
    fix S p qs x
    assume \<open>S \<in> mk_finite_char C\<close>
    then have finc: \<open>\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C\<close>
      unfolding mk_finite_char_def by blast

    have sc: \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>
      using closedC unfolding subset_closed_def by blast
    then have sc': \<open>\<And>S' x. x \<union> S' \<in> C \<Longrightarrow> \<forall>S \<subseteq> x \<union> S'. S \<in> C\<close>
      by blast

    assume *: \<open>p \<in> S\<close> and x: \<open>x \<notin> params S\<close>
    show \<open>set (delta_fun p x) \<union> S \<in> mk_finite_char C\<close>
      unfolding mk_finite_char_def
    proof safe
      fix S'
      let ?S' = \<open>{p} \<union> (S' - set (delta_fun p x))\<close>

      assume \<open>S' \<subseteq> set (delta_fun p x) \<union> S\<close> and \<open>finite S'\<close>
      then have \<open>?S' \<subseteq> S\<close>
        using * by fast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite S'\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      moreover have \<open>\<forall>a \<in> ?S'. x \<notin> params_fm a\<close>
        using x \<open>?S' \<subseteq> S\<close> by blast
      ultimately have \<open>set (delta_fun p x) \<union> ?S' \<in> C\<close>
        using deltaAC by blast
      then show \<open>S' \<in> C\<close>
        using sc by fast
    qed
  qed
next
  show \<open>\<And>C S. sat\<^sub>E kind C \<Longrightarrow> S \<in> C \<Longrightarrow> maximal C S \<Longrightarrow> sat\<^sub>H kind S\<close>
    using sat\<^sub>H_Wits .
qed

locale Derivational_Delta = Delta map_fm params_fm delta_fun
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    delta_fun :: \<open>'fm \<Rightarrow> 'x \<Rightarrow> 'fm list\<close> +
  fixes consistent :: \<open>'fm set \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes consistent: \<open>\<And>S p x. p \<in> S \<Longrightarrow> x \<notin> params S \<Longrightarrow> \<turnstile> S \<Longrightarrow> \<turnstile> set (delta_fun p x) \<union> S\<close>

sublocale Derivational_Delta \<subseteq> Derivational_Kind map_fm params_fm kind consistent
proof
  assume inf: \<open>infinite (UNIV :: 'fm set)\<close>
  show \<open>sat\<^sub>E kind {A. |UNIV :: 'fm set| \<le>o |- params A| \<and> \<turnstile> A}\<close>
  proof safe
    fix S p
    assume *: \<open>p \<in> S\<close> \<open>|UNIV :: 'fm set| \<le>o |- params S|\<close> \<open>\<turnstile> S\<close>
    then have \<open>infinite (- (params ({p} \<union> S)))\<close>
      using card_of_ordLeq_finite inf by auto
    then obtain x where \<open>x \<notin> params ({p} \<union> S)\<close>
      using infinite_imp_nonempty by blast
    then have \<open>\<exists>x. \<turnstile> set (delta_fun p x) \<union> S\<close>
      using *(1,3) consistent \<open>\<turnstile> S\<close> by fast
    then show \<open>\<exists>x. set (delta_fun p x) \<union> S \<in> {A. |UNIV :: 'fm set| \<le>o |- params A| \<and> \<turnstile> A}\<close>
      using * inf infinite_params_left by blast
  qed
qed

locale Weak_Derivational_Delta = Delta map_fm params_fm delta_fun
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    delta_fun :: \<open>'fm \<Rightarrow> 'x \<Rightarrow> 'fm list\<close> +
  fixes consistent :: \<open>'fm list \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes consistent: \<open>\<And>A p x. p \<in> set A \<Longrightarrow> x \<notin> params (set A) \<Longrightarrow> \<turnstile> A \<Longrightarrow> \<turnstile> delta_fun p x @ A\<close>

sublocale Weak_Derivational_Delta \<subseteq> Weak_Derivational_Kind map_fm params_fm kind consistent
proof
  assume inf: \<open>infinite (UNIV :: 'x set)\<close>
  show \<open>sat\<^sub>E kind {S. \<exists>A. set A = S \<and> \<turnstile> A}\<close>
  proof safe
    fix p A
    assume *: \<open>p \<in> set A\<close> \<open>\<turnstile> A\<close>
    then have \<open>infinite (- (params (set (p # A))))\<close>
      using inf finite_compl by fastforce
    then obtain x where \<open>x \<notin> params (set (p # A))\<close>
      using infinite_imp_nonempty by blast
    then have \<open>\<exists>x. \<turnstile> delta_fun p x @ A\<close>
      using * consistent[of p A x] by auto
    then show \<open>\<exists>x. set (delta_fun p x) \<union> set A \<in> {S. \<exists>A. set A = S \<and> \<turnstile> A}\<close>
      by (metis (mono_tags, lifting) CollectI set_append)
  qed
qed

section \<open>Modal\<close>

text \<open>
  The Hintikka property you want depends on the concrete logic.
  See Term-Modal Logics by Fitting, Thalmann and Voronkov, p. 156 bottom.
\<close>

locale Modal = Params map_fm params_fm
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> +
  fixes classify :: \<open>'fm list \<Rightarrow> ('fm set \<Rightarrow> 'fm set) \<times> 'fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<box>\<close> 50)
    and hint :: \<open>'fm set \<Rightarrow> bool\<close>
  assumes modal_map: \<open>\<And>ps F qs f. ps \<leadsto>\<^sub>\<box> (F, qs) \<Longrightarrow> \<exists>G. map (map_fm f) ps \<leadsto>\<^sub>\<box> (G, map (map_fm f) qs) \<and>
      (\<forall>S. map_fm f ` F S \<subseteq> G (map_fm f ` S))\<close>
    and modal_mono: \<open>\<And>ps F qs S S'. ps \<leadsto>\<^sub>\<box> (F, qs) \<Longrightarrow> S \<subseteq> S' \<Longrightarrow> F S \<subseteq> F S'\<close>
    and modal_fin: \<open>\<And>ps F qs S A. ps \<leadsto>\<^sub>\<box> (F, qs) \<Longrightarrow> finite A \<Longrightarrow> A \<subseteq> F S \<Longrightarrow> \<exists>S' \<subseteq> S. finite S' \<and> A \<subseteq> F S'\<close>
begin

inductive cond where
  cond [intro!]: \<open>ps \<leadsto>\<^sub>\<box> (F, qs) \<Longrightarrow> cond ps (\<lambda>C S. set qs \<union> F S \<in> C)\<close>

inductive_cases condE[elim!]: \<open>cond ps Q\<close>

abbreviation kind :: \<open>('x, 'fm) kind\<close> where
  \<open>kind \<equiv> Cond cond hint\<close>

end

locale ModalH = Modal map_fm params_fm classify hint
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    classify :: \<open>'fm list \<Rightarrow> ('fm set \<Rightarrow> 'fm set) \<times> 'fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<box>\<close> 50) and
    hint :: \<open>'fm set \<Rightarrow> bool\<close> +
  assumes modal_hintikka: \<open>\<And>C S. sat\<^sub>E kind C \<Longrightarrow> S \<in> C \<Longrightarrow> maximal C S \<Longrightarrow> sat\<^sub>H kind S\<close>

sublocale ModalH \<subseteq> Consistency_Kind map_fm params_fm kind
proof
  fix C
  assume modalC: \<open>sat\<^sub>E kind C\<close>
  then show \<open>sat\<^sub>E kind (close C)\<close>
  proof safe
    fix S ps F qs
    assume \<open>S \<in> close C\<close>
    then obtain S' where S': \<open>S' \<in> C\<close> and \<open>S \<subseteq> S'\<close>
      unfolding close_def by blast

    assume \<open>set ps \<subseteq> S\<close>
    then have *: \<open>set ps \<subseteq> S'\<close>
      using \<open>S \<subseteq> S'\<close> by blast

    assume **: \<open>ps \<leadsto>\<^sub>\<box> (F, qs)\<close>
    then have \<open>set qs \<union> F S' \<in> C\<close>
      using modalC S' * ** by blast
    then show \<open>set qs \<union> F S \<in> close C\<close>
      using \<open>S \<subseteq> S'\<close> subset_in_close ** modal_mono by metis
  qed
next
  fix C
  assume modalC: \<open>sat\<^sub>E kind C\<close> and closedC: \<open>subset_closed C\<close>
  then show \<open>sat\<^sub>A kind (mk_alt_consistency C)\<close>
  proof safe
    fix S ps F qs

    assume \<open>S \<in> mk_alt_consistency C\<close>
    then obtain f where f: \<open>map_fm f ` S \<in> C\<close>
      unfolding mk_alt_consistency_def by blast

    let ?C = \<open>mk_alt_consistency C\<close>
    let ?S = \<open>map_fm f ` S\<close>

    assume \<open>set ps \<subseteq> S\<close>
    then have *: \<open>set (map (map_fm f) ps) \<subseteq> ?S\<close>
      by auto

    assume **: \<open>ps \<leadsto>\<^sub>\<box> (F, qs)\<close>
    obtain G where G:
      \<open>map (map_fm f) ps \<leadsto>\<^sub>\<box> (G, map (map_fm f) qs)\<close>
      \<open>\<forall>S. map_fm f ` F S \<subseteq> G (map_fm f ` S)\<close>
      using modal_map ** by meson
    then have \<open>set (map (map_fm f) qs) \<union> G ?S \<in> C\<close>
      using modalC f * by blast
    then have \<open>set (map (map_fm f) qs) \<union> map_fm f ` F S \<in> C\<close>
      using G closedC unfolding subset_closed_def by (meson Un_mono order_refl)
    then show \<open>set qs \<union> F S \<in> ?C\<close>
      unfolding mk_alt_consistency_def
      by (auto split: option.splits simp: image_Un)
  qed
next
  fix C
  assume modalAC: \<open>sat\<^sub>A kind C\<close> and closedC: \<open>subset_closed C\<close>
  then show \<open>sat\<^sub>A kind (mk_finite_char C)\<close>
  proof safe
    fix S ps F qs t
    assume S: \<open>S \<in> mk_finite_char C\<close>
    then have finc: \<open>\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C\<close>
      unfolding mk_finite_char_def by blast

    have sc: \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>
      using closedC unfolding subset_closed_def by blast
    then have sc': \<open>\<And>S' x. x \<union> S' \<in> C \<Longrightarrow> \<forall>S \<subseteq> x \<union> S'. S \<in> C\<close>
      by blast

    assume *: \<open>set ps \<subseteq> S\<close> and **: \<open>ps \<leadsto>\<^sub>\<box> (F, qs)\<close>

    show \<open>set qs \<union> F S \<in> mk_finite_char C\<close>
      unfolding mk_finite_char_def 
    proof safe
      fix S'
      assume 1: \<open>S' \<subseteq> set qs \<union> F S\<close> and 2: \<open>finite S'\<close>

      obtain A where A: \<open>A \<subseteq> S\<close> \<open>finite A\<close> \<open>S' \<subseteq> set qs \<union> F A\<close> 
        using 1 2 ** modal_fin by (meson Diff_subset_conv finite_Diff)

      let ?S = \<open>set ps \<union> A\<close>

      have \<open>finite ?S\<close>
        using A(2) by blast
      moreover have \<open>?S \<subseteq> S\<close>
        using * A(1) by simp
      ultimately have \<open>?S \<in> C\<close>
        using finc by simp

      moreover have \<open>set ps \<subseteq> ?S\<close>
        by blast
      ultimately have \<open>set qs \<union> F ?S \<in> C\<close>
        using ** modalAC by blast

      moreover have \<open>S' \<subseteq> set qs \<union> F ?S\<close>
        using A(3) ** modal_mono by (meson Diff_subset_conv inf_sup_ord(4) subset_trans)
      ultimately show \<open>S' \<in> C\<close>
        using sc by blast
    qed
  qed
next
  fix C S
  assume *: \<open>sat\<^sub>E kind C\<close> \<open>S \<in> C\<close> \<open>maximal C S\<close> 
  then show \<open>sat\<^sub>H kind S\<close>
    using modal_hintikka by simp
qed

locale Derivational_Modal = ModalH map_fm params_fm classify
  for
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    classify :: \<open>'fm list \<Rightarrow> ('fm set \<Rightarrow> 'fm set) \<times> 'fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<box>\<close> 50) +
  fixes consistent :: \<open>'fm set \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes consistent: \<open>\<And>S ps F qs. set ps \<subseteq> S \<Longrightarrow> ps \<leadsto>\<^sub>\<box> (F, qs) \<Longrightarrow> \<turnstile> S \<Longrightarrow> \<turnstile> set qs \<union> F S\<close>
    and params_subset: \<open>\<And>ps F qs S. ps \<leadsto>\<^sub>\<box> (F, qs) \<Longrightarrow> params (F S) \<subseteq> params S\<close>

sublocale Derivational_Modal \<subseteq> Derivational_Kind map_fm params_fm kind consistent
proof
  assume inf: \<open>infinite (UNIV :: 'fm set)\<close>
  then show \<open>sat\<^sub>E kind {A. |UNIV :: 'fm set| \<le>o |- params A| \<and> \<turnstile> A}\<close>
  proof safe
    fix S ps F qs
    assume *: \<open>ps \<leadsto>\<^sub>\<box> (F, qs)\<close> \<open>|UNIV :: 'fm set| \<le>o |- params S|\<close>
    then have \<open>|UNIV :: 'fm set| \<le>o |- params (F S)|\<close>
      using * params_subset by (meson Compl_subset_Compl_iff card_of_mono1 ordLeq_transitive)
    then show \<open>|UNIV :: 'fm set| \<le>o |- params (set qs \<union> F S)|\<close>
      using infinite_params_left[OF inf] by blast
  qed (use consistent in blast)
qed

(* TODO: Weak for Modal requires that F works on lists rather than sets. *)

end
