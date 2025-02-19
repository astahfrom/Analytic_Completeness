(*
  Author: Asta Halkjær From, 2025.

  Inspiration:
  - "FOL-Fitting", Stefan Berghofer.
  - "First-Order Logic and Automated Theorem Proving", 1996, Melvin Fitting.
*)

(* TODO: Might want to use a, b instead of n, m *)
(* TODO: Gamma P should be probably be Gamma F *)
(* TODO: is there a nicer way to get the useful rel_sort? *)
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

lemma mk_finite_char_Union:\<open>subset_closed C \<Longrightarrow> \<Union>(mk_finite_char C) = \<Union>C\<close>
  unfolding mk_finite_char_def subset_closed_def by blast

lemma (in wo_rel) chain_union_closed:
  assumes \<open>finite_char C\<close> \<open>is_chain f\<close> \<open>\<forall>n \<in> Field r. f n \<in> C\<close> \<open>Field r \<noteq> {}\<close>
  shows \<open>(\<Union>n \<in> Field r. f n) \<in> C\<close>
  using assms chain_index unfolding finite_char_def by metis

section \<open>Locale\<close>

type_synonym 'a cprop = \<open>'a set set\<close>

datatype ('fms, 'fmtm, 'tfms, 'xfms) sort
  = Confl \<open>'fms\<close>
  | Alpha \<open>'fms\<close>
  | Beta \<open>'fms\<close>
  | Gamma \<open>'fmtm\<close> \<open>'tfms\<close>
  | Delta \<open>'xfms\<close>

locale Consistency =
  fixes
    params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and
    map_fm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'fm \<Rightarrow> 'fm\<close> and
    map_tm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'tm \<Rightarrow> 'tm\<close> and
    classify :: \<open>'fm list \<Rightarrow> ('fm list, 'fm set \<Rightarrow> 'tm set, 'tm \<Rightarrow> 'fm list, 'x \<Rightarrow> 'fm list) sort \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<close> 50)
  assumes
    finite_params_fm [simp]: \<open>\<And>p. finite (params_fm p)\<close> and
    map_fm_id: \<open>map_fm id = id\<close> and
    map_params_fm: \<open>\<And>f g p. \<forall>x \<in> params_fm p. f x = g x \<Longrightarrow> map_fm f p = map_fm g p\<close> and
    map_fm_classify: \<open>\<And>f ps qs. ps \<leadsto> qs \<Longrightarrow> \<exists>rs. map (map_fm f) ps \<leadsto> rs \<and> rel_sort
      (\<lambda>qs rs. map (map_fm f) qs = rs)
      (\<lambda>P Q. \<forall>S. map_tm f ` P S \<subseteq> Q (map_fm f ` S))
      (\<lambda>qs rs. \<forall>t. map (map_fm f) (qs t) = rs (map_tm f t))
      (\<lambda>qs rs. \<forall>x. map (map_fm f) (qs x) = rs (f x))
      qs rs\<close> and
    mono_Gamma: \<open>\<And>ps P qs S S'. ps \<leadsto> Gamma P qs \<Longrightarrow> S \<subseteq> S' \<Longrightarrow> P S \<subseteq> P S'\<close> and
    fin_Gamma: \<open>\<And>ps P qs t A. ps \<leadsto> Gamma P qs \<Longrightarrow> t \<in> P A \<Longrightarrow>
      \<exists>B \<subseteq> A. finite B \<and> t \<in> P B\<close> and
    singleton_Delta: \<open>\<And>ps qs. ps \<leadsto> Delta qs \<Longrightarrow> \<exists>p. ps = [p]\<close> and
    unique_Delta: \<open>\<And>ps qs rs. ps \<leadsto> Delta qs \<Longrightarrow> ps \<leadsto> Delta rs \<Longrightarrow> qs = rs\<close>
begin

abbreviation params :: \<open>'fm set \<Rightarrow> 'x set\<close> where
  \<open>params S \<equiv> \<Union>p \<in> S. params_fm p\<close>

lemma infinite_params: \<open>infinite (- params B) \<Longrightarrow> infinite (- params (set ps \<union> B))\<close>
  using infinite_diff_finite finite_params_fm by (metis List.finite_set UN_Un finite_UN_I)

lemma infinite_params_left: \<open>infinite A \<Longrightarrow> |A| \<le>o |- params S| \<Longrightarrow> |A| \<le>o |- params (set ps \<union> S)|\<close>
  using infinite_left by (metis List.finite_set UN_Un finite_UN_I finite_params_fm)

definition consistency :: \<open>'fm set set \<Rightarrow> bool\<close> where
  \<open>consistency C \<equiv> \<forall>S. S \<in> C \<longrightarrow> (\<forall>ps. set ps \<subseteq> S \<longrightarrow>
    (\<forall>qs. ps \<leadsto> Confl qs \<longrightarrow> (\<forall>q \<in> set qs. q \<notin> S)) \<and>
    (\<forall>qs. ps \<leadsto> Alpha qs \<longrightarrow> set qs \<union> S \<in> C) \<and>
    (\<forall>qs. ps \<leadsto> Beta qs \<longrightarrow> (\<exists>q \<in> set qs. {q} \<union> S \<in> C)) \<and>
    (\<forall>P qs. ps \<leadsto> Gamma P qs \<longrightarrow> (\<forall>t \<in> P S. set (qs t) \<union> S \<in> C)) \<and>
    (\<forall>qs. ps \<leadsto> Delta qs \<longrightarrow> (\<exists>x. set (qs x) \<union> S \<in> C)))\<close>

lemma
  assumes \<open>consistency C\<close> \<open>S \<in> C\<close> \<open>set ps \<subseteq> S\<close>
  shows
    confl [dest]: \<open>\<And>qs q. ps \<leadsto> Confl qs \<Longrightarrow> q \<in> set qs \<Longrightarrow> q \<notin> S\<close> and
    alpha [dest]: \<open>\<And>qs. ps \<leadsto> Alpha qs \<Longrightarrow> set qs \<union> S \<in> C\<close> and
    beta [dest]: \<open>\<And>qs. ps \<leadsto> Beta qs \<Longrightarrow> \<exists>q \<in> set qs. {q} \<union> S \<in> C\<close> and
    gamma [dest]: \<open>\<And>P qs t. ps \<leadsto> Gamma P qs \<Longrightarrow> t \<in> P S \<Longrightarrow> set (qs t) \<union> S \<in> C\<close> and
    delta [dest]: \<open>\<And>qs. ps \<leadsto> Delta qs \<Longrightarrow> \<exists>x. set (qs x) \<union> S \<in> C\<close>
  using assms unfolding consistency_def by fast+

definition alt_consistency :: \<open>'fm set set \<Rightarrow> bool\<close> where
  \<open>alt_consistency C \<equiv> \<forall>S. S \<in> C \<longrightarrow> (\<forall>ps. set ps \<subseteq> S \<longrightarrow>
    (\<forall>qs. ps \<leadsto> Confl qs \<longrightarrow> (\<forall>q \<in> set qs. q \<notin> S)) \<and>
    (\<forall>qs. ps \<leadsto> Alpha qs \<longrightarrow> set qs \<union> S \<in> C) \<and>
    (\<forall>qs. ps \<leadsto> Beta qs \<longrightarrow> (\<exists>q \<in> set qs. {q} \<union> S \<in> C)) \<and>
    (\<forall>P qs. ps \<leadsto> Gamma P qs \<longrightarrow> (\<forall>t \<in> P S. set (qs t) \<union> S \<in> C)) \<and>
    (\<forall>qs. ps \<leadsto> Delta qs \<longrightarrow> (\<forall>x. x \<notin> params S \<longrightarrow> set (qs x) \<union> S \<in> C)))\<close>

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

lemma alt_consistency:
  assumes conc: \<open>consistency C\<close>
  shows \<open>alt_consistency (mk_alt_consistency C)\<close>
  unfolding alt_consistency_def
proof safe
  fix S :: \<open>'fm set\<close> and ps :: \<open>'fm list\<close> and qs

  assume \<open>S \<in> mk_alt_consistency C\<close>
  then obtain f :: \<open>'x \<Rightarrow> 'x\<close> where f: \<open>map_fm f ` S \<in> C\<close>
    unfolding mk_alt_consistency_def by blast

  let ?C' = \<open>mk_alt_consistency C\<close>
  let ?S' = \<open>map_fm f ` S\<close>

  assume \<open>set ps \<subseteq> S\<close>
  then have *: \<open>set (map (map_fm f) ps) \<subseteq> ?S'\<close>
    by auto

  {
    fix q
    assume **: \<open>ps \<leadsto> Confl qs\<close> \<open>q \<in> set qs\<close> \<open>q \<in> S\<close>
    then have \<open>map (map_fm f) ps \<leadsto> Confl (map (map_fm f) qs)\<close>
      using map_fm_classify by (fastforce elim: sort.rel_cases)
    then have \<open>\<forall>q \<in> set qs. map_fm f q \<notin> ?S'\<close>
      using confl[OF conc f *] by simp
    then have \<open>\<forall>q \<in> set qs. q \<notin> S\<close>
      by blast
    then show False
      using **(2-) by blast
  }

  {
    assume \<open>ps \<leadsto> Alpha qs\<close>
    then have \<open>map (map_fm f) ps \<leadsto> Alpha (map (map_fm f) qs)\<close>
      using map_fm_classify by (fastforce elim: sort.rel_cases)
    then have \<open>set (map (map_fm f) qs) \<union> ?S' \<in> C\<close>
      using conc f * by blast
    then show \<open>set qs \<union> S \<in> ?C'\<close>
      unfolding mk_alt_consistency_def by (auto simp: image_Un)
  }

  {
    assume \<open>ps \<leadsto> Beta qs\<close>
    then have \<open>map (map_fm f) ps \<leadsto> Beta (map (map_fm f) qs)\<close>
      using map_fm_classify by (fastforce elim: sort.rel_cases)
    then have \<open>\<exists>q \<in> set (map (map_fm f) qs). {q} \<union> ?S' \<in> C\<close>
      using conc f * by blast
    then show \<open>\<exists>q \<in> set qs. {q} \<union> S \<in> ?C'\<close>
      unfolding mk_alt_consistency_def by (auto simp: image_Un)
  }

  {
    fix P t
    assume **: \<open>ps \<leadsto> Gamma P qs\<close> and t: \<open>t \<in> P S\<close>
    obtain rs Q where rs:
      \<open>map (map_fm f) ps \<leadsto> Gamma Q rs\<close>
      \<open>\<forall>S. map_tm f ` P S \<subseteq> Q (map_fm f ` S)\<close>
      \<open>\<forall>t. map (map_fm f) (qs t) = rs (map_tm f t)\<close>
      using map_fm_classify[OF **, of f] by (auto elim: sort.rel_cases)
    then have \<open>set (rs (map_tm f t)) \<union> ?S' \<in> C\<close>
      using conc f * t by blast
    then have \<open>set (map (map_fm f) (qs t)) \<union> ?S' \<in> C\<close>
      using rs by simp
    then show \<open>set (qs t) \<union> S \<in> ?C'\<close>
      unfolding mk_alt_consistency_def
      by (auto split: option.splits simp: image_Un)
  }

  {
    fix x
    have map_fm_Delta: \<open>\<And>ps qs f. ps \<leadsto> Delta qs \<Longrightarrow>
        \<exists>rs. map (map_fm f) ps \<leadsto> Delta rs \<and> (\<forall>x. map (map_fm f) (qs x) = rs (f x))\<close>
      using map_fm_classify by (fastforce elim: sort.rel_cases)

    assume **: \<open>ps \<leadsto> Delta qs\<close> and x: \<open>x \<notin> params S\<close>
    then obtain rs where rs: \<open>map (map_fm f) ps \<leadsto> Delta rs\<close> \<open>\<forall>x. map (map_fm f) (qs x) = rs (f x)\<close>
      using map_fm_Delta by meson
    then obtain y where y: \<open>set (rs y) \<union> ?S' \<in> C\<close>
      using conc f * by blast

    let ?g = \<open>f(x := y)\<close>

    have \<open>\<forall>x \<in> params S. f x = ?g x\<close>
      using x by simp
    then have S: \<open>\<forall>q \<in> S. map_fm ?g q = map_fm f q\<close>
      using map_params_fm by simp
    then have \<open>map (map_fm ?g) ps = map (map_fm f) ps\<close>
      using \<open>set ps \<subseteq> S\<close> by auto
    then have \<open>map (map_fm ?g) ps \<leadsto> Delta rs\<close> \<open>\<forall>x. map (map_fm ?g) (qs x) = rs (?g x)\<close>
      using rs map_fm_Delta unique_Delta ** by metis+

    moreover have \<open>set (rs (?g x)) \<union> ?S' \<in> C\<close>
      using y by simp
    ultimately have \<open>set (map (map_fm ?g) (qs x)) \<union> ?S' \<in> C\<close>
      by simp
    then have \<open>\<exists>f. set (map (map_fm f) (qs x)) \<union> map_fm f ` S \<in> C\<close>
      using S by (metis image_cong)
    then show \<open>set (qs x) \<union> S \<in> ?C'\<close>
      unfolding mk_alt_consistency_def
      by (metis (mono_tags, lifting) image_Un image_set mem_Collect_eq)
  }
qed

lemma close_consistency:
  assumes conc: \<open>consistency C\<close>
  shows \<open>consistency (close C)\<close>
  unfolding consistency_def
proof safe
  fix S ps qs
  assume \<open>S \<in> close C\<close>
  then obtain S' where S': \<open>S' \<in> C\<close> and \<open>S \<subseteq> S'\<close>
    unfolding close_def by blast

  assume \<open>set ps \<subseteq> S\<close>
  then have *: \<open>set ps \<subseteq> S'\<close>
    using \<open>S \<subseteq> S'\<close> by blast

  {
    fix q
    assume **: \<open>ps \<leadsto> Confl qs\<close> \<open>q \<in> set qs\<close> \<open>q \<in> S\<close>
    then have \<open>\<forall>q \<in> set qs. q \<notin> S'\<close>
      using conc S' * by blast
    then have \<open>\<forall>q \<in> set qs. q \<notin> S\<close>
      using \<open>S \<subseteq> S'\<close> by blast
    then show False
      using ** by blast
  }

  {
    assume \<open>ps \<leadsto> Alpha qs\<close>
    then have \<open>set qs \<union> S' \<in> C\<close>
      using conc S' * by blast
    then show \<open>set qs \<union> S \<in> close C\<close>
      using \<open>S \<subseteq> S'\<close> by (metis subset_in_close)
  }

  {
    assume \<open>ps \<leadsto> Beta qs\<close>
    then have \<open>\<exists>q \<in> set qs. {q} \<union> S' \<in> C\<close>
      using conc S' * by blast
    then show \<open>\<exists>q \<in> set qs. {q} \<union> S \<in> close C\<close>
      using \<open>S \<subseteq> S'\<close> by (metis subset_in_close)
  }

  {
    fix t P
    assume \<open>ps \<leadsto> Gamma P qs\<close> \<open>t \<in> P S\<close>
    moreover from this have \<open>t \<in> P S'\<close>
      using mono_Gamma \<open>S \<subseteq> S'\<close> by blast
    ultimately have \<open>set (qs t) \<union> S' \<in> C\<close>
      using conc S' * by blast
    then have \<open>set (qs t) \<union> S \<in> close C\<close>
      using \<open>S \<subseteq> S'\<close> subset_in_close by blast
    then show \<open>set (qs t) \<union> S \<in> close C\<close>
      by (meson close_closed equalityE subset_closed_def sup.mono)
  }

  {
    assume \<open>ps \<leadsto> Delta qs\<close>
    then have \<open>\<exists>x. set (qs x) \<union> S' \<in> C\<close>
      using conc S' * by blast
    then show \<open>\<exists>x. set (qs x) \<union> S \<in> close C\<close>
      using \<open>S \<subseteq> S'\<close> by (metis subset_in_close)
  }
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

lemma finite_alt_consistency:
  assumes altconc: \<open>alt_consistency C\<close>
    and \<open>subset_closed C\<close>
  shows \<open>alt_consistency (mk_finite_char C)\<close>
  unfolding alt_consistency_def
proof safe
  fix S ps qs
  assume \<open>S \<in> mk_finite_char C\<close>
  then have finc: \<open>\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C\<close>
    unfolding mk_finite_char_def by blast

  have sc: \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>
    using \<open>subset_closed C\<close> unfolding subset_closed_def by blast
  then have sc': \<open>\<And>S' x. x \<union> S' \<in> C \<Longrightarrow> \<forall>S \<subseteq> x \<union> S'. S \<in> C\<close>
    by blast

  assume *: \<open>set ps \<subseteq> S\<close>

  {
    fix q
    assume **: \<open>ps \<leadsto> Confl qs\<close> \<open>q \<in> set qs\<close> \<open>q \<in> S\<close>
    then have \<open>{q} \<union> set ps \<in> C\<close>
      using \<open>set ps \<subseteq> S\<close> finc by simp
    then show False
      using ** altconc unfolding alt_consistency_def by fast
  }

  {
    assume **: \<open>ps \<leadsto> Alpha qs\<close>
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
        using ** altconc unfolding alt_consistency_def by fast
      then show \<open>S' \<in> C\<close>
        using sc by fast
    qed
  }

  {
    assume **: \<open>ps \<leadsto> Beta qs\<close>
    show \<open>\<exists>q \<in> set qs. {q} \<union> S \<in> mk_finite_char C\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then have \<open>\<forall>q \<in> set qs. \<exists>Sq. Sq \<subseteq> {q} \<union> S \<and> finite Sq \<and> Sq \<notin> C\<close>
        unfolding mk_finite_char_def by blast
      then obtain f where f: \<open>\<forall>q \<in> set qs. f q \<subseteq> {q} \<union> S \<and> finite (f q) \<and> f q \<notin> C\<close>
        by metis

      let ?S' = \<open>set ps \<union> \<Union>{f q - {q} |q. q \<in> set qs}\<close>

      have \<open>?S' \<subseteq> S\<close>
        using * f by fast
      moreover have \<open>finite ?S'\<close>
        using f by auto
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      then have \<open>\<exists>q \<in> set qs. {q} \<union> ?S' \<in> C\<close>
        using ** altconc unfolding alt_consistency_def by fast
      then have \<open>\<exists>q \<in> set qs. f q \<in> C\<close>
        using sc' by blast
      then show False
        using f by blast
    qed
  }

  {
    fix t P
    assume **: \<open>ps \<leadsto> Gamma P qs\<close> and t: \<open>t \<in> P S\<close>
   
    show \<open>set (qs t) \<union> S \<in> mk_finite_char C\<close>
      unfolding mk_finite_char_def 
    proof safe
      fix S'
      assume 1: \<open>S' \<subseteq> set (qs t) \<union> S\<close> and 2: \<open>finite S'\<close>
 
      (* Take the big S and boil it down to a finite one to get a better handle on instances. *)
     obtain A where A: \<open>A \<subseteq> S\<close> \<open>finite A\<close> \<open>S' \<subseteq> set (qs t) \<union> A\<close> 
        using 1 2 by (meson Diff_subset_conv equalityD2 finite_Diff)

      obtain B where B: \<open>B \<subseteq> S\<close> \<open>finite B\<close> \<open>t \<in> P B\<close>
        using ** t fin_Gamma by meson

      let ?S = \<open>set ps \<union> A \<union> B\<close>

      have \<open>finite ?S\<close>
        using A(2) B(2) by blast
      moreover have \<open>?S \<subseteq> S\<close>
        using * A(1) B(1) by simp
      ultimately have \<open>?S \<in> C\<close>
        using finc by simp

      moreover have \<open>set ps \<subseteq> ?S\<close>
        by blast
      moreover have \<open>t \<in> P ?S\<close>
        using ** B(3) mono_Gamma by blast
      ultimately have \<open>set (qs t) \<union> ?S \<in> C\<close>
        using ** altconc unfolding alt_consistency_def by meson
    
      moreover have \<open>S' \<subseteq> set (qs t) \<union> ?S\<close>
        using A(3) by blast
      ultimately show \<open>S' \<in> C\<close>
        using sc by blast
    qed
  }

  {
    fix x
    assume **: \<open>ps \<leadsto> Delta qs\<close> and \<open>x \<notin> params S\<close>
    show \<open>set (qs x) \<union> S \<in> mk_finite_char C\<close>
      unfolding mk_finite_char_def
    proof safe
      fix S'
      let ?S' = \<open>set ps \<union> (S' - set (qs x))\<close>

      assume \<open>S' \<subseteq> set (qs x) \<union> S\<close> and \<open>finite S'\<close>
      then have \<open>?S' \<subseteq> S\<close>
        using * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite S'\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      moreover have \<open>\<forall>a \<in> ?S'. x \<notin> params_fm a\<close>
        using \<open>x \<notin> params S\<close> \<open>?S' \<subseteq> S\<close> by blast
      ultimately have \<open>set (qs x) \<union> ?S' \<in> C\<close>
        using ** altconc unfolding alt_consistency_def by fast
      then show \<open>S' \<in> C\<close>
        using sc by fast
    qed
  }
qed

definition mk_cprop :: \<open>'fm cprop \<Rightarrow> 'fm cprop\<close> where
  \<open>mk_cprop C \<equiv> mk_finite_char (mk_alt_consistency (close C))\<close>

lemma mk_cprop_subset_closed: \<open>subset_closed (mk_cprop C)\<close>
  unfolding mk_cprop_def using finite_char finite_char_closed by blast

lemma mk_cprop_finite_char: \<open>finite_char (mk_cprop C)\<close>
  unfolding mk_cprop_def using finite_char by blast

lemma mk_cprop_alt_consistency: \<open>consistency C \<Longrightarrow> alt_consistency (mk_cprop C)\<close>
  unfolding mk_cprop_def using alt_consistency close_closed close_consistency
    finite_alt_consistency mk_alt_consistency_closed 
  by blast

lemma mk_cprop_in: \<open>S \<in> C \<Longrightarrow> S \<in> mk_cprop C\<close>  
  by (metis close_closed close_subset finite_char_subset mk_alt_consistency_closed
      mk_alt_consistency_subset mk_cprop_def subsetD)

end

locale Maximal_Consistency = Consistency params_fm map_fm map_tm classify
  for params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and map_fm map_tm and classify (infix \<open>\<leadsto>\<close> 50) +
  fixes r :: \<open>'fm rel\<close>
  assumes Cinfinite_r: \<open>Cinfinite r\<close>
begin

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
  \<open>witness p S \<equiv> if \<exists>qs. [p] \<leadsto> Delta qs
    then let a = SOME x. x \<notin> params ({p} \<union> S) in set ((THE qs. [p] \<leadsto> Delta qs) a)
    else {}\<close>

lemma witness:
  assumes \<open>[p] \<leadsto> Delta qs\<close>
  shows \<open>witness p S = set (qs (SOME x. x \<notin> params ({p} \<union> S)))\<close>
  unfolding witness_def using assms unique_Delta by (metis the_equality)

lemma no_witness:
  assumes \<open>\<nexists>qs. [p] \<leadsto> Delta qs\<close>
  shows \<open>witness p S = {}\<close>
  unfolding witness_def using assms by meson

definition extendS :: \<open>'fm cprop \<Rightarrow> 'fm \<Rightarrow> 'fm set \<Rightarrow> 'fm set\<close> where
  \<open>extendS C n prev \<equiv> if {n} \<union> prev \<in> C then witness n prev \<union> {n} \<union> prev else prev\<close>

definition extendL :: \<open>'fm cprop \<Rightarrow> ('fm \<Rightarrow> 'fm set) \<Rightarrow> 'fm \<Rightarrow> 'fm set\<close> where
  \<open>extendL C rec n \<equiv> \<Union>m \<in> underS r n. rec m\<close>

definition extend :: \<open>'fm cprop \<Rightarrow> 'fm set \<Rightarrow> 'fm \<Rightarrow> 'fm set\<close> where
  \<open>extend C S n \<equiv> worecZSL r S (extendS C) (extendL C) n\<close>

lemma adm_woL_extendL: \<open>adm_woL r (extendL C)\<close>
  unfolding extendL_def wo_rel.adm_woL_def[OF wo_rel_r] by blast

definition Extend :: \<open>'fm cprop \<Rightarrow> 'fm set \<Rightarrow> 'fm set\<close> where
  \<open>Extend C S \<equiv> \<Union>n \<in> Field r. extend C S n\<close>

lemma finite_witness_params: \<open>finite (params (witness p S))\<close>
  unfolding witness_def by (auto split: sort.split)

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
  assumes \<open>alt_consistency C\<close> \<open>{n} \<union> extend C S n \<in> C\<close>
    and \<open>\<exists>x. x \<notin> params ({n} \<union> extend C S n)\<close> \<open>n \<in> Field r\<close> 
  shows \<open>extend C S (succ r n) \<in> C\<close>
proof (cases \<open>\<exists>qs. [n] \<leadsto> Delta qs\<close>)
  case True
  then obtain qs where Delta: \<open>[n] \<leadsto> Delta qs\<close>
    by blast

  let ?S' = \<open>{n} \<union> extend C S n\<close>
  let ?a = \<open>SOME x. x \<notin> params ?S'\<close>

  have \<open>set [n] \<subseteq> ?S'\<close>
    by simp
  then have \<open>\<forall>x. x \<notin> params ?S' \<longrightarrow> set (qs x) \<union> ?S' \<in> C\<close>
    using Delta \<open>?S' \<in> C\<close> \<open>alt_consistency C\<close> unfolding alt_consistency_def by meson
  then have \<open>set (qs ?a) \<union> ?S' \<in> C\<close>
    using assms(3) by (metis (mono_tags, lifting) someI2)
  then show \<open>extend C S (succ r n) \<in> C\<close>
    using witness Delta assms unfolding extend_succ[OF assms(4)] by simp
next
  case False
  then show ?thesis
    using assms(2, 4) no_witness by simp
qed

lemma extend_in_C_stop:
  assumes \<open>extend C S n \<in> C\<close>
    and \<open>{n} \<union> extend C S n \<notin> C\<close>
    and \<open>n \<in> Field r\<close>
  shows \<open>extend C S (succ r n) \<in> C\<close>
  using assms extend_succ by auto

lemma extend_in_C:
  assumes \<open>alt_consistency C\<close> \<open>finite_char C\<close> \<open>S \<in> C\<close> \<open>r \<le>o |- params S|\<close> \<open>n \<in> Field r\<close>
  shows \<open>extend C S n \<in> C\<close>
  using assms
proof (induct n rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
  case 1
  then show ?case
    by (simp add: adm_woL_extendL extend_def wo_rel.worecZSL_zero wo_rel_r)
next
  case (2 i)
 then have \<open>i \<in> Field r\<close>
    by (meson WELL  well_order_on_domain wo_rel.succ_in_diff[OF wo_rel_r])
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
    using finite_params_fm[of i]
      (* TODO: silly smt *)
    by (smt (verit) Compl_eq_Diff_UNIV Diff_infinite_finite SUP_insert Set_Diff_Un Un_commute insert_is_Un)
  then have \<open>\<exists>x. x \<notin> params ({i} \<union> extend C S i)\<close>
    by (meson Compl_iff finite_params_fm rev_finite_subset subsetI)
  then show ?case
    using assms 2(2) extend_in_C_step extend_in_C_stop wo_rel.succ_in[OF wo_rel_r, of i]
      \<open>i \<in> Field r\<close> by metis
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
  assumes \<open>alt_consistency C\<close> \<open>finite_char C\<close> \<open>S \<in> C\<close> \<open>r \<le>o |- params S|\<close>
  shows \<open>Extend C S \<in> C\<close>
  unfolding Extend_def
  using assms wo_rel.chain_union_closed[OF wo_rel_r] is_chain_extend extend_in_C nonempty_Field_r
  by blast

definition maximal :: \<open>'fm cprop \<Rightarrow> 'fm set \<Rightarrow> bool\<close> where
  \<open>maximal C S \<equiv> \<forall>S' \<in> C. S' \<subseteq> Field r \<longrightarrow> S \<subseteq> S' \<longrightarrow> S = S'\<close>

theorem Extend_maximal:
  assumes \<open>finite_char C\<close>
  shows \<open>maximal C (Extend C S)\<close>
  unfolding maximal_def Extend_def
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
    moreover have \<open>subset_closed C\<close>
      using \<open>finite_char C\<close> finite_char_closed by blast
    then have \<open>\<forall>S \<subseteq> S'. S \<in> C\<close>
       unfolding subset_closed_def using \<open>S' \<in> C\<close> by blast
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

definition witnessed :: \<open>'fm set \<Rightarrow> bool\<close> where
  \<open>witnessed S \<equiv> \<forall>p \<in> S. p \<in> Field r \<longrightarrow> (\<exists>S'. witness p S' \<subseteq> S)\<close>

theorem Extend_witnessed:
  assumes \<open>alt_consistency C\<close> \<open>finite_char C\<close> \<open>S \<in> C\<close> \<open>r \<le>o |- params S|\<close>
  shows \<open>witnessed (Extend C S)\<close>
  unfolding witnessed_def
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

abbreviation mk_mcs :: \<open>'fm cprop \<Rightarrow> 'fm set \<Rightarrow> 'fm set\<close> where
  \<open>mk_mcs C S \<equiv> Extend (mk_cprop C) S\<close>

theorem mk_mcs_maximal: \<open>maximal C (mk_mcs C S)\<close>
  using Extend_maximal maximal_def mk_cprop_finite_char mk_cprop_in by meson

theorem mk_mcs_witnessed:
  assumes \<open>consistency C\<close> \<open>S \<in> C\<close> \<open>r \<le>o |- params S|\<close>
  shows \<open>witnessed (mk_mcs C S)\<close>
  using assms Extend_witnessed mk_cprop_alt_consistency mk_cprop_finite_char mk_cprop_in by blast

end

locale Maximal_Consistency_UNIV =
  Consistency params_fm map_fm map_tm classify
  for params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and map_fm map_tm and classify (\<open>_ \<leadsto> _\<close> [50, 50] 50) +
  assumes inf_UNIV: \<open>infinite (UNIV :: 'fm set)\<close>

sublocale Maximal_Consistency_UNIV \<subseteq>
  Maximal_Consistency params_fm map_fm map_tm classify \<open>|UNIV :: 'fm set|\<close>
proof
  show \<open>Cinfinite |UNIV :: 'fm set|\<close>
    using inf_UNIV unfolding cinfinite_def by simp
qed

context Maximal_Consistency_UNIV
begin

lemma maximal: \<open>maximal C S \<longleftrightarrow> (\<forall>S' \<in> C. S \<subseteq> S' \<longrightarrow> S = S')\<close>
  unfolding maximal_def by simp

lemma witnessed: \<open>witnessed S \<longleftrightarrow> (\<forall>p \<in> S. \<exists>S'. witness p S' \<subseteq> S)\<close>
  unfolding witnessed_def by simp

end

locale Hintikka = Consistency params_fm map_fm map_tm classify
  for params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and map_fm map_tm and classify (\<open>_ \<leadsto> _\<close> [50, 50] 50)
    +
  fixes H :: \<open>'fm set\<close>
  assumes
    confl: \<open>\<And>ps qs. set ps \<subseteq> H \<Longrightarrow> ps \<leadsto> Confl qs \<Longrightarrow> \<forall>q \<in> set qs. q \<notin> H\<close> and
    alpha: \<open>\<And>ps qs. set ps \<subseteq> H \<Longrightarrow> ps \<leadsto> Alpha qs \<Longrightarrow> \<forall>q \<in> set qs. q \<in> H\<close> and
    beta: \<open>\<And>ps qs. set ps \<subseteq> H \<Longrightarrow> ps \<leadsto> Beta qs \<Longrightarrow> \<exists>q \<in> set qs. q \<in> H\<close> and
    gamma: \<open>\<And>ps P qs. set ps \<subseteq> H \<Longrightarrow> ps \<leadsto> Gamma P qs \<Longrightarrow> \<forall>t \<in> P H. set (qs t) \<subseteq> H\<close> and
    delta: \<open>\<And>ps qs. set ps \<subseteq> H \<Longrightarrow> ps \<leadsto> Delta qs \<Longrightarrow> \<exists>x. set (qs x) \<subseteq> H\<close>

context Maximal_Consistency_UNIV
begin

theorem Hintikka_MCS:
  assumes \<open>alt_consistency C\<close> \<open>S \<in> C\<close> \<open>maximal C S\<close> \<open>witnessed S\<close>
  shows \<open>Hintikka params_fm map_fm map_tm classify S\<close>
proof
  fix ps qs
  assume *: \<open>set ps \<subseteq> S\<close> \<open>ps \<leadsto> Confl qs\<close>
  then show \<open>\<forall>q \<in> set qs. q \<notin> S\<close>
    using \<open>S \<in> C\<close> \<open>alt_consistency C\<close> unfolding alt_consistency_def by fast
next
  fix ps qs
  assume *: \<open>set ps \<subseteq> S\<close> \<open>ps \<leadsto> Alpha qs\<close>
  then have \<open>set qs \<union> S \<in> C\<close>
    using * \<open>S \<in> C\<close> \<open>alt_consistency C\<close> unfolding alt_consistency_def by fast
  then show \<open>\<forall>q \<in> set qs. q \<in> S\<close>
    using \<open>maximal C S\<close> unfolding maximal by fast
next
  fix ps qs
  assume *: \<open>set ps \<subseteq> S\<close> \<open>ps \<leadsto> Beta qs\<close>
  then have \<open>\<exists>q \<in> set qs. {q} \<union> S \<in> C\<close>
    using * \<open>S \<in> C\<close> \<open>alt_consistency C\<close> unfolding alt_consistency_def by fast
  then show \<open>\<exists>q \<in> set qs. q \<in> S\<close>
    using \<open>maximal C S\<close> unfolding maximal by fast
next
  fix ps P qs
  assume *: \<open>set ps \<subseteq> S\<close> \<open>ps \<leadsto> Gamma P qs\<close>
  then have \<open>t \<in> P S \<Longrightarrow> set (qs t) \<union> S \<in> C\<close> for t
    using * \<open>S \<in> C\<close> \<open>alt_consistency C\<close> unfolding alt_consistency_def by fast
  then show \<open>\<forall>t \<in> P S. set (qs t) \<subseteq> S\<close>
    using \<open>maximal C S\<close> unfolding maximal by fast
next
  fix ps qs
  assume *: \<open>set ps \<subseteq> S\<close> \<open>ps \<leadsto> Delta qs\<close>
  then have \<open>\<exists>x. set (qs x) \<union> S \<in> C\<close>
    using assms(2, 4) witness unfolding witnessed
    by (metis in_mono list.set_intros(1) singleton_Delta subset_Un_eq)
  then show \<open>\<exists>x. set (qs x) \<subseteq> S\<close>
    using \<open>maximal C S\<close> unfolding maximal by fast
qed

corollary Hintikka_mk_mcs:
  fixes S :: \<open>'fm set\<close>
  assumes \<open>consistency C\<close> \<open>S \<in> C\<close> \<open>|UNIV :: 'fm set| \<le>o |- params S|\<close>
  shows \<open>Hintikka params_fm map_fm map_tm classify (mk_mcs C S)\<close>
  using assms Extend_in_C Extend_maximal Hintikka_MCS mk_cprop_alt_consistency
      mk_cprop_finite_char mk_cprop_in mk_mcs_witnessed
  by meson

end

locale Derivational_Consistency = Maximal_Consistency params_fm map_fm map_tm classify r
  for params_fm :: \<open>'fm \<Rightarrow> 'x set\<close> and map_fm and map_tm :: \<open>('x \<Rightarrow> 'x) \<Rightarrow> 'tm \<Rightarrow> 'tm\<close>
    and classify (infix \<open>\<leadsto>\<close> 50) and r +
  fixes refute :: \<open>'fm set \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50)
  assumes refute_confl: \<open>\<And>ps qs A q. ps \<leadsto> Confl qs \<Longrightarrow> set ps \<subseteq> A \<Longrightarrow> q \<in> set qs \<Longrightarrow> q \<in> A \<Longrightarrow> \<turnstile> A\<close>
    and refute_alpha: \<open>\<And>ps qs A. ps \<leadsto> Alpha qs \<Longrightarrow> set ps \<subseteq> A \<Longrightarrow> \<turnstile> set qs \<union> A \<Longrightarrow> \<turnstile> A\<close>
    and refute_beta: \<open>\<And>ps qs A. ps \<leadsto> Beta qs \<Longrightarrow> set ps \<subseteq> A \<Longrightarrow> \<forall>q \<in> set qs. \<turnstile> {q} \<union> A \<Longrightarrow> \<turnstile> A\<close>
    and refute_gamma: \<open>\<And>ps P qs A t. ps \<leadsto> Gamma P qs \<Longrightarrow> set ps \<subseteq> A \<Longrightarrow> t \<in> P A \<Longrightarrow> \<turnstile> set (qs t) \<union> A \<Longrightarrow> \<turnstile> A\<close>
    and refute_delta: \<open>\<And>ps qs A a. ps \<leadsto> Delta qs \<Longrightarrow> set ps \<subseteq> A \<Longrightarrow> a \<notin> params A \<Longrightarrow> \<turnstile> set (qs a) \<union> A \<Longrightarrow> \<turnstile> A\<close>
begin

theorem Consistency: \<open>consistency {A. |UNIV :: 'fm set| \<le>o |- params A| \<and> \<not> \<turnstile> A}\<close>
  unfolding consistency_def
proof safe
  fix S :: \<open>'fm set\<close> and ps qs
  assume
    *: \<open>\<not> \<turnstile> S\<close> and
    inf': \<open>|UNIV :: 'fm set| \<le>o |- params S|\<close> and
    ps: \<open>set ps \<subseteq> S\<close>
  
  have inf: \<open>|UNIV :: 'fm set| \<le>o |- params (set qs \<union> S)|\<close> for qs
    using inf' infinite_params_left Cinfinite_r card_of_UNIV card_of_ordLeq_finite cinfinite_def
    by blast

  {
    assume \<open>ps \<leadsto> Alpha qs\<close>
    then show \<open>|UNIV :: 'fm set| \<le>o |- params (set qs \<union> S)|\<close>
      using inf by blast
  }

  {
    fix t and P :: \<open>'fm set \<Rightarrow> 'tm set\<close>
    assume \<open>ps \<leadsto> Gamma P qs\<close>
    then show \<open>|UNIV :: 'fm set| \<le>o |- params (set (qs t) \<union> S)|\<close>
      using inf by blast
  }

  {
    fix q
    assume \<open>ps \<leadsto> Confl qs\<close> \<open>q \<in> set qs\<close> \<open>q \<in> S\<close>
    then show False
      using * ps refute_confl by blast
  }

  {
    assume \<open>ps \<leadsto> Alpha qs\<close> \<open>\<turnstile> set qs \<union> S\<close>
    then show False
      using * ps refute_alpha by blast
  }

  {
    assume \<open>ps \<leadsto> Beta qs\<close>
    then show \<open>\<exists>q \<in> set qs. {q} \<union> S \<in> {A. |UNIV :: 'fm set| \<le>o |- params A| \<and> \<not> \<turnstile> A}\<close>
      using * ps inf refute_beta[of ps qs]
      by (metis (no_types, lifting) finite.emptyI finite.insertI finite_list mem_Collect_eq)
    }

  {
    fix t P
    assume \<open>ps \<leadsto> Gamma P qs\<close> \<open>t \<in> P S\<close> \<open>\<turnstile> set (qs t) \<union> S\<close>
    then show False
      using * ps refute_gamma by blast
  }

  {
    assume \<open>ps \<leadsto> Delta qs\<close>
    moreover have \<open>infinite (- (params (set ps \<union> S)))\<close>
      using ps inf' card_of_ordLeq_finite infinite_params
      by (metis Cinfinite_r card_of_UNIV cinfinite_def)
    then obtain x where **: \<open>x \<notin> params (set ps \<union> S)\<close>
      using infinite_imp_nonempty by blast
    ultimately have \<open>\<exists>x. set (qs x) \<union> S \<in> {A. \<not> \<turnstile> A}\<close>
      using * ps refute_delta[of ps qs] by auto
    then show \<open>\<exists>x. set (qs x) \<union> S \<in> {A. |UNIV :: 'fm set| \<le>o |- params A| \<and> \<not> \<turnstile> A}\<close>
      using ps inf by blast
  }
qed

end

end
