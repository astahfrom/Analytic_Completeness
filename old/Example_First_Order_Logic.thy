theory Example_First_Order_Logic
  imports Analytic_Completeness
begin

section \<open>Syntax\<close>

datatype (params_tm: 'f) tm
  = Var nat (\<open>\<^bold>#\<close>)
  | Fun 'f \<open>'f tm list\<close> (\<open>\<^bold>\<bullet>\<close>)

abbreviation Const (\<open>\<^bold>\<star>\<close>) where \<open>\<^bold>\<star>a \<equiv> \<^bold>\<bullet>a []\<close>

datatype (params_fm: 'f, 'p) fm
  = Fls (\<open>\<^bold>\<bottom>\<close>)
  | Pre 'p \<open>'f tm list\<close> (\<open>\<^bold>\<cdot>\<close>)
  | Imp \<open>('f, 'p) fm\<close> \<open>('f, 'p) fm\<close> (infixr \<open>\<^bold>\<longrightarrow>\<close> 55)
  | Uni \<open>('f, 'p) fm\<close> (\<open>\<^bold>\<forall>\<close>)

abbreviation Neg :: \<open>('f, 'p) fm \<Rightarrow> ('f, 'p) fm\<close> (\<open>\<^bold>\<not> _\<close> [70] 70) where
  \<open>\<^bold>\<not> p \<equiv> p \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>

section \<open>Semantics\<close>

type_synonym ('a, 'f, 'p) model = \<open>(nat \<Rightarrow> 'a) \<times> ('f \<Rightarrow> 'a list \<Rightarrow> 'a) \<times> ('p \<Rightarrow> 'a list \<Rightarrow> bool)\<close>

fun semantics_tm :: \<open>(nat \<Rightarrow> 'a) \<times> ('f \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> 'f tm \<Rightarrow> 'a\<close> (\<open>\<lparr>_\<rparr>\<close>) where
  \<open>\<lparr>(E, _)\<rparr> (\<^bold>#n) = E n\<close>
| \<open>\<lparr>(E, F)\<rparr> (\<^bold>\<bullet>f ts) = F f (map \<lparr>(E, F)\<rparr> ts)\<close>

primrec add_env :: \<open>'a \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a\<close> (infix \<open>\<then>\<close> 0) where
  \<open>(t \<then> s) 0 = t\<close>
| \<open>(t \<then> s) (Suc n) = s n\<close>

fun semantics_fm :: \<open>('a, 'f, 'p) model \<Rightarrow> ('f, 'p) fm \<Rightarrow> bool\<close> (\<open>_ \<Turnstile>\<^sub>\<forall> _\<close> [50, 50] 50) where
  \<open>_ \<Turnstile>\<^sub>\<forall> \<^bold>\<bottom> \<longleftrightarrow> False\<close>
| \<open>(E, F, G) \<Turnstile>\<^sub>\<forall> \<^bold>\<cdot>P ts \<longleftrightarrow> G P (map \<lparr>(E, F)\<rparr> ts)\<close>
| \<open>(E, F, G) \<Turnstile>\<^sub>\<forall> p \<^bold>\<longrightarrow> q \<longleftrightarrow> (E, F, G) \<Turnstile>\<^sub>\<forall> p \<longrightarrow> (E, F, G) \<Turnstile>\<^sub>\<forall> q\<close>
| \<open>(E, F, G) \<Turnstile>\<^sub>\<forall> \<^bold>\<forall>p \<longleftrightarrow> (\<forall>x. (x \<then> E, F, G) \<Turnstile>\<^sub>\<forall> p)\<close>

section \<open>Operations\<close>

primrec lift_tm :: \<open>'f tm \<Rightarrow> 'f tm\<close> where
  \<open>lift_tm (\<^bold>#n) = \<^bold>#(n+1)\<close>
| \<open>lift_tm (\<^bold>\<bullet>f ts) = \<^bold>\<bullet>f (map lift_tm ts)\<close>

primrec sub_tm :: \<open>(nat \<Rightarrow> 'f tm) \<Rightarrow> 'f tm \<Rightarrow> 'f tm\<close> where
  \<open>sub_tm s (\<^bold>#n) = s n\<close>
| \<open>sub_tm s (\<^bold>\<bullet>f ts) = \<^bold>\<bullet>f (map (sub_tm s) ts)\<close>

primrec sub_fm :: \<open>(nat \<Rightarrow> 'f tm) \<Rightarrow> ('f, 'p) fm \<Rightarrow> ('f, 'p) fm\<close> where
  \<open>sub_fm _ \<^bold>\<bottom> = \<^bold>\<bottom>\<close>
| \<open>sub_fm s (\<^bold>\<cdot>P ts) = \<^bold>\<cdot>P (map (sub_tm s) ts)\<close>
| \<open>sub_fm s (p \<^bold>\<longrightarrow> q) = sub_fm s p \<^bold>\<longrightarrow> sub_fm s q\<close>
| \<open>sub_fm s (\<^bold>\<forall>p) = \<^bold>\<forall>(sub_fm (\<^bold>#0 \<then> \<lambda>n. lift_tm (s n)) p)\<close>

abbreviation inst_single :: \<open>'f tm \<Rightarrow> ('f, 'p) fm \<Rightarrow> ('f, 'p) fm\<close> (\<open>\<langle>_\<rangle>\<close>) where
  \<open>\<langle>t\<rangle> \<equiv> sub_fm (t \<then> \<^bold>#)\<close>

abbreviation psub :: \<open>('f \<Rightarrow> 'g) \<Rightarrow> ('f, 'p) fm \<Rightarrow> ('g, 'p) fm\<close> where
  \<open>psub f \<equiv> map_fm f id\<close>

primrec size_fm :: \<open>('f, 'p) fm \<Rightarrow> nat\<close> where
  \<open>size_fm \<^bold>\<bottom> = 1\<close>
| \<open>size_fm (\<^bold>\<cdot>_ _) = 1\<close>
| \<open>size_fm (p \<^bold>\<longrightarrow> q) = 1 + size_fm p + size_fm q\<close>
| \<open>size_fm (\<^bold>\<forall>p) = 1 + size_fm p\<close>

subsection \<open>Lemmas\<close>

lemma size_sub_fm [simp]: \<open>size_fm (sub_fm s p) = size_fm p\<close>
  by (induct p arbitrary: s) simp_all

lemma upd_params_tm [simp]: \<open>f \<notin> params_tm t \<Longrightarrow> \<lparr>(E, F(f := x))\<rparr> t = \<lparr>(E, F)\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma upd_params_fm [simp]: \<open>f \<notin> params_fm p \<Longrightarrow> (E, F(f := x), G) \<Turnstile>\<^sub>\<forall> p \<longleftrightarrow> (E, F, G)\<Turnstile>\<^sub>\<forall> p\<close>
  by (induct p arbitrary: E) (auto cong: map_cong)

lemma finite_params_tm [simp]: \<open>finite (params_tm t)\<close>
  by (induct t) simp_all

lemma finite_params_fm' [simp]: \<open>finite (params_fm p)\<close>
  by (induct p) simp_all

lemma env [simp]: \<open>P ((x \<then> E) n) = (P x \<then> \<lambda>n. P (E n)) n\<close>
  by (induct n) simp_all

lemma lift_lemma: \<open>\<lparr>(x \<then> E, F)\<rparr> (lift_tm t) = \<lparr>(E, F)\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma sub_tm_semantics: \<open>\<lparr>(E, F)\<rparr> (sub_tm s t) = \<lparr>(\<lambda>n. \<lparr>(E, F)\<rparr> (s n), F)\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma sub_fm_semantics [simp]: \<open>(E, F, G) \<Turnstile>\<^sub>\<forall> sub_fm s p \<longleftrightarrow> (\<lambda>n. \<lparr>(E, F)\<rparr> (s n), F, G) \<Turnstile>\<^sub>\<forall> p\<close>
  by (induct p arbitrary: E s) (auto cong: map_cong simp: sub_tm_semantics lift_lemma)

lemma semantics_tm_id [simp]: \<open>\<lparr>(\<^bold>#, \<^bold>\<bullet>)\<rparr> t = t\<close>
  by (induct t) (auto cong: map_cong)

lemma semantics_tm_id_map [simp]: \<open>map \<lparr>(\<^bold>#, \<^bold>\<bullet>)\<rparr> ts = ts\<close>
  by (auto cong: map_cong)

lemma map_tm_sub_tm [simp]: \<open>map_tm f (sub_tm g t) = sub_tm (map_tm f o g) (map_tm f t)\<close>
  by (induct t) simp_all

lemma map_tm_lift_tm [simp]: \<open>map_tm f (lift_tm t) = lift_tm (map_tm f t)\<close>
  by (induct t) simp_all

lemma psub_sub_fm: \<open>psub f (sub_fm g p) = sub_fm (map_tm f o g) (psub f p)\<close>
  by (induct p arbitrary: g) (simp_all add: comp_def)

lemma map_tm_inst_single: \<open>(map_tm f o (u \<then> \<^bold>#)) t = (map_tm f u \<then> \<^bold>#) t\<close>
  by (induct t) auto

lemma psub_inst_single [simp]: \<open>psub f (\<langle>t\<rangle>p) = \<langle>map_tm f t\<rangle>(psub f p)\<close>
  unfolding psub_sub_fm map_tm_inst_single ..

section \<open>Model Existence\<close>

inductive classify :: \<open>('f, 'p) fm list \<Rightarrow> (_, ('f, 'p) fm set \<Rightarrow> _, _) sort \<Rightarrow> bool\<close> (\<open>_ \<leadsto> _\<close> [50, 50] 50) where
  \<open>[ \<^bold>\<bottom> ] \<leadsto> Confl [ \<^bold>\<bottom> ]\<close>
| \<open>[ \<^bold>\<cdot>P ts ] \<leadsto> Confl [ \<^bold>\<not> (\<^bold>\<cdot>P ts) ]\<close>
| \<open>[ p \<^bold>\<longrightarrow> q ] \<leadsto> Beta [ \<^bold>\<not> p, q ]\<close>
| \<open>[ \<^bold>\<not> (p \<^bold>\<longrightarrow> q) ] \<leadsto> Alpha [ p, \<^bold>\<not> q ]\<close>
| \<open>[ \<^bold>\<forall>p ] \<leadsto> Gamma (\<lambda>_ t. [ \<langle>t\<rangle>p ])\<close>
| \<open>[ \<^bold>\<not> \<^bold>\<forall>p ] \<leadsto> Delta (\<lambda>x. [ \<^bold>\<not> \<langle>\<^bold>\<star>x\<rangle>p ])\<close>

declare classify.intros[intro]

interpretation Maximal_Consistency_UNIV params_fm psub map_tm classify
proof
  show \<open>\<And>p. finite (params_fm p)\<close>
    by simp
  show \<open>psub id = id\<close>
    using fm.map_id0 by blast
  show \<open>\<And>f g p. \<forall>x\<in>params_fm p. f x = g x \<Longrightarrow> psub f p = psub g p\<close>
    using fm.map_cong0 by fastforce
  show \<open>\<And>f ps qs. ps \<leadsto> qs \<Longrightarrow> \<exists>rs. map (psub f) ps \<leadsto> rs \<and> rel_sort
        (\<lambda>qs. (=) (map (psub f) qs))
        (\<lambda>qs rs. \<forall>S t. psub f ` set (qs S t) \<subseteq> set (rs (psub f ` S) (map_tm f t)))
        (\<lambda>qs rs. \<forall>x. map (psub f) (qs x) = rs (f x)) qs rs\<close>
    by (fastforce elim: classify.cases)
  show \<open>\<And>ps qs t S S'. ps \<leadsto> Gamma qs \<Longrightarrow> S \<subseteq> S' \<Longrightarrow> set (qs S t) \<subseteq> set (qs S' t)\<close>
    by (fastforce elim!: classify.cases)
  show \<open>\<And>ps qs A t. ps \<leadsto> Gamma qs \<Longrightarrow> \<exists>B \<subseteq> A. finite B \<and> set (qs A t) \<subseteq> set (qs B t)\<close>
    by (auto elim: classify.cases)
  show \<open>\<And>ps qs. ps \<leadsto> Delta qs \<Longrightarrow> \<exists>p. ps = [p]\<close>
    by (auto elim: classify.cases)
  show \<open>\<And>p ps qs. p \<leadsto> Delta ps \<Longrightarrow> p \<leadsto> Delta qs \<Longrightarrow> ps = qs\<close>
    by (auto elim: classify.cases)
  show \<open>infinite (UNIV :: ('f, 'p) fm set)\<close>
    using infinite_UNIV_size[of \<open>\<lambda>p. p \<^bold>\<longrightarrow> p\<close>] by simp
qed

lemma \<open>consistency C \<Longrightarrow> S \<in> C \<Longrightarrow> \<^bold>\<bottom> \<notin> S\<close>
  unfolding consistency_def by force

lemma \<open>consistency C \<Longrightarrow> S \<in> C \<Longrightarrow> \<^bold>\<cdot>P ts \<notin> S \<or> \<^bold>\<not> (\<^bold>\<cdot>P ts) \<notin> S\<close>
  unfolding consistency_def by force

lemma \<open>consistency C \<Longrightarrow> S \<in> C \<Longrightarrow> \<^bold>\<not> (p \<^bold>\<longrightarrow> q) \<in> S \<Longrightarrow> {p, \<^bold>\<not> q} \<union> S \<in> C\<close>
  unfolding consistency_def by force

lemma \<open>consistency C \<Longrightarrow> S \<in> C \<Longrightarrow> p \<^bold>\<longrightarrow> q \<in> S \<Longrightarrow> {\<^bold>\<not> p} \<union> S \<in> C \<or> {q} \<union> S \<in> C\<close>
  unfolding consistency_def by force

lemma \<open>consistency C \<Longrightarrow> S \<in> C \<Longrightarrow> \<^bold>\<forall>p \<in> S \<Longrightarrow> {\<langle>t\<rangle>p} \<union> S \<in> C\<close>
  unfolding consistency_def by force

lemma \<open>consistency C \<Longrightarrow> S \<in> C \<Longrightarrow> \<^bold>\<not> \<^bold>\<forall>p \<in> S \<Longrightarrow> \<exists>a. {\<^bold>\<not> \<langle>\<^bold>\<star>a\<rangle>p} \<union> S \<in> C\<close>
  unfolding consistency_def
  by (metis (no_types, lifting) bot.extremum classify.intros(6) insert_subsetI list.set(1) list.simps(15))

abbreviation \<open>hmodel H \<equiv> (\<^bold>#, \<^bold>\<bullet>, \<lambda>P ts. \<^bold>\<cdot>P ts \<in> H)\<close>

locale MyHintikka = Hintikka params_fm psub map_tm classify H
  for H
begin

theorem model: \<open>(p \<in> H \<longrightarrow> hmodel H \<Turnstile>\<^sub>\<forall> p) \<and> (\<^bold>\<not> p \<in> H \<longrightarrow> \<not> hmodel H \<Turnstile>\<^sub>\<forall> p)\<close>
proof (induct p rule: wf_induct [where r=\<open>measure size_fm\<close>])
  case 1
  then show ?case
    by simp
next
  case (2 x)
  then show ?case
  proof (cases x)
    case Fls
    then show ?thesis
      using confl by force
  next
    case (Pre P ts)
    then show ?thesis
      using confl by force
  next
    case (Imp p q)
    then show ?thesis
    proof (safe del: notI)
      assume \<open>x = p \<^bold>\<longrightarrow> q\<close> \<open>p \<^bold>\<longrightarrow> q \<in> H\<close>
      then have \<open>\<^bold>\<not> p \<in> H \<or> q \<in> H\<close>
        using beta by force
      then show \<open>hmodel H \<Turnstile>\<^sub>\<forall> p \<^bold>\<longrightarrow> q\<close>
        using 2 Imp by auto
    next
      assume \<open>x = p \<^bold>\<longrightarrow> q\<close> \<open>\<^bold>\<not> (p \<^bold>\<longrightarrow> q) \<in> H\<close>
      then have \<open>p \<in> H \<and> \<^bold>\<not> q \<in> H\<close>
        using alpha by force
      then show \<open>\<not> hmodel H \<Turnstile>\<^sub>\<forall> p \<^bold>\<longrightarrow> q\<close>
        using 2 Imp by auto
    qed
  next
    case (Uni p)
    then show ?thesis
    proof (safe del: notI)
      assume \<open>x = \<^bold>\<forall>p\<close> \<open>\<^bold>\<forall>p \<in> H\<close>
      then have \<open>\<forall>t. \<langle>t\<rangle>p \<in> H\<close>
        using gamma by force
      moreover have \<open>\<forall>t. (\<langle>t\<rangle>p, \<^bold>\<forall>p) \<in> measure size_fm\<close>
        by simp
      ultimately have \<open>\<forall>t. hmodel H \<Turnstile>\<^sub>\<forall> \<langle>t\<rangle>p\<close>
        using 2 \<open>x = \<^bold>\<forall>p\<close> by blast
      then show \<open>hmodel H \<Turnstile>\<^sub>\<forall> \<^bold>\<forall>p\<close>
        by simp
    next
      assume \<open>x = \<^bold>\<forall>p\<close> \<open>\<^bold>\<not> \<^bold>\<forall>p \<in> H\<close>
      then obtain t where \<open>\<^bold>\<not> \<langle>t\<rangle>p \<in> H\<close>
        using delta by (metis (no_types, lifting) bot.extremum classify.intros(6) empty_set insert_subset list.simps(15))
      moreover have \<open>(\<langle>t\<rangle>p, \<^bold>\<forall>p) \<in> measure size_fm\<close>
        by simp
      ultimately have \<open>\<not> hmodel H \<Turnstile>\<^sub>\<forall> \<langle>t\<rangle>p\<close>
        using 2 \<open>x = \<^bold>\<forall>p\<close> by blast
      then show \<open>\<not> hmodel H \<Turnstile>\<^sub>\<forall> \<^bold>\<forall>p\<close>
        by auto
    qed
  qed
qed

end

theorem model_existence:
  fixes S :: \<open>('f, 'p) fm set\<close>
  assumes \<open>consistency C\<close>
    and \<open>S \<in> C\<close>
    and \<open>|UNIV :: ('f, 'p) fm set| \<le>o |- params S|\<close>
    and \<open>p \<in> S\<close>
  shows \<open>hmodel (mk_mcs C S) \<Turnstile>\<^sub>\<forall> p\<close>
  using assms MyHintikka.model Hintikka_mk_mcs Extend_subset MyHintikka.intro by blast

section \<open>Natural Deduction with Sets\<close>

abbreviation \<open>params_set S \<equiv> \<Union>p \<in> S. params_fm p\<close>

inductive Calculus_Set :: \<open>('f, 'p) fm set \<Rightarrow> ('f, 'p) fm \<Rightarrow> bool\<close> (\<open>_ \<tturnstile>\<^sub>\<forall> _\<close> [50, 50] 50) where
  AssmX [simp]: \<open>p \<in> A \<Longrightarrow> A \<tturnstile>\<^sub>\<forall> p\<close>
| FlsEX [elim]: \<open>A \<tturnstile>\<^sub>\<forall> \<^bold>\<bottom> \<Longrightarrow> A \<tturnstile>\<^sub>\<forall> p\<close>
| ImpIX [intro]: \<open>{p} \<union> A \<tturnstile>\<^sub>\<forall> q \<Longrightarrow> A \<tturnstile>\<^sub>\<forall> p \<^bold>\<longrightarrow> q\<close>
| ImpEX [dest]: \<open>A \<tturnstile>\<^sub>\<forall> p \<^bold>\<longrightarrow> q \<Longrightarrow> A \<tturnstile>\<^sub>\<forall> p \<Longrightarrow> A \<tturnstile>\<^sub>\<forall> q\<close>
| UniIX [intro]: \<open>A \<tturnstile>\<^sub>\<forall> \<langle>\<^bold>\<star>a\<rangle>p \<Longrightarrow> a \<notin> params_set ({p} \<union> A) \<Longrightarrow> A \<tturnstile>\<^sub>\<forall> \<^bold>\<forall>p\<close>
| UniEX [dest]: \<open>A \<tturnstile>\<^sub>\<forall> \<^bold>\<forall>p \<Longrightarrow> A \<tturnstile>\<^sub>\<forall> \<langle>t\<rangle>p\<close>
| ClasX: \<open>{p \<^bold>\<longrightarrow> q} \<union> A \<tturnstile>\<^sub>\<forall> p \<Longrightarrow> A \<tturnstile>\<^sub>\<forall> p\<close>

subsection \<open>Soundness\<close>

theorem soundness_set: \<open>A \<tturnstile>\<^sub>\<forall> p \<Longrightarrow> \<forall>q \<in> A. (E, F, G) \<Turnstile>\<^sub>\<forall> q \<Longrightarrow> (E, F, G) \<Turnstile>\<^sub>\<forall> p\<close>
proof (induct A p arbitrary: F pred: Calculus_Set)
  case (UniIX A a p)
  moreover have \<open>\<forall>q \<in> A. (E, F(a := x), G) \<Turnstile>\<^sub>\<forall> q\<close> for x
    using UniIX(3-4) by simp
  then have \<open>(E, F(a := x), G) \<Turnstile>\<^sub>\<forall> \<langle>\<^bold>\<star>a\<rangle>p\<close> for x
    using UniIX by meson
  ultimately show ?case
    by fastforce
qed auto

subsection \<open>Derived Rules\<close>

lemma BooleX: \<open>{\<^bold>\<not> p} \<union> A \<tturnstile>\<^sub>\<forall> \<^bold>\<bottom> \<Longrightarrow> A \<tturnstile>\<^sub>\<forall> p\<close>
  unfolding Neg_def using ClasX FlsEX by blast

lemma calculus_confl:
  assumes \<open>ps \<leadsto> Confl qs\<close> \<open>set ps \<subseteq> A\<close> \<open>q \<in> set qs\<close> \<open>q \<in> A\<close>
  shows \<open>A \<tturnstile>\<^sub>\<forall> \<^bold>\<bottom>\<close>
  using assms
proof cases
  case 1
  then show ?thesis
    using assms(2-) by auto
next
  case (2 P ts)
  then show ?thesis
    using assms(2-) AssmX ImpEX
    by (metis empty_iff empty_set list.set_intros(1) set_ConsD subset_iff)
qed

lemma calculus_alpha:
  assumes \<open>ps \<leadsto> Alpha qs\<close> \<open>set ps \<subseteq> A\<close> \<open>set qs \<union> A \<tturnstile>\<^sub>\<forall> \<^bold>\<bottom>\<close>
  shows \<open>A \<tturnstile>\<^sub>\<forall> \<^bold>\<bottom>\<close>
  using assms
proof cases
  case (4 p q)
  then show ?thesis
    using assms(2-)
    by (metis (no_types, lifting) Calculus_Set.simps Un_insert_right empty_set insert_is_Un list.set_intros(1) list.simps(15) subsetD sup_commute)
qed

lemma calculus_beta:
  assumes \<open>ps \<leadsto> Beta qs\<close> \<open>set ps \<subseteq> A\<close> \<open>\<forall>q \<in> set qs. {q} \<union> A \<tturnstile>\<^sub>\<forall> \<^bold>\<bottom>\<close>
  shows \<open>A \<tturnstile>\<^sub>\<forall> \<^bold>\<bottom>\<close>
  using assms
proof cases
  case (3 p q)
  then show ?thesis
    using assms(2-) AssmX BooleX ImpEX ImpIX
    by (metis list.set_intros(1) set_subset_Cons subset_iff)
qed

lemma calculus_gamma:
  assumes \<open>ps \<leadsto> Gamma qs\<close> \<open>set ps \<subseteq> A\<close> \<open>set (qs A t) \<union> A \<tturnstile>\<^sub>\<forall> \<^bold>\<bottom>\<close>
  shows \<open>A \<tturnstile>\<^sub>\<forall> \<^bold>\<bottom>\<close>
  using assms
proof cases
  case (5 p)
  then show ?thesis
    using assms(2-)
    apply simp
    by (metis AssmX ImpEX ImpIX UniEX insert_is_Un)
qed

lemma calculus_delta:
  assumes \<open>ps \<leadsto> Delta qs\<close> \<open>set ps \<subseteq> A\<close> \<open>a \<notin> params A\<close> \<open>set (qs a) \<union> A \<tturnstile>\<^sub>\<forall> \<^bold>\<bottom>\<close>
  shows \<open>A \<tturnstile>\<^sub>\<forall> \<^bold>\<bottom>\<close>
  using assms
proof cases
  case (6 p)
  then show ?thesis
    using assms(2-)
    apply simp
    using AssmX BooleX ImpEX UniIX
    by (metis (no_types, opaque_lifting) UN_E Un_insert_left fm.set_intros(2) fm.simps(47) insertE sup_bot.left_neutral)
qed

subsection \<open>Derivational Consistency\<close>

lemma deriv_consistency:
  \<open>consistency {A :: ('f, 'p) fm set. |UNIV :: ('f, 'p) fm set| \<le>o |- params A| \<and> \<not> A \<tturnstile>\<^sub>\<forall> \<^bold>\<bottom>}\<close>
  unfolding consistency_def
proof safe
  fix S :: \<open>('f, 'p) fm set\<close> and ps qs
  assume
    *: \<open>\<not> S \<tturnstile>\<^sub>\<forall> \<^bold>\<bottom>\<close> and
    inf': \<open>|UNIV :: ('f, 'p) fm set| \<le>o |- params S|\<close> and
    ps: \<open>set ps \<subseteq> S\<close>
  
  have inf: \<open>|UNIV :: ('f, 'p) fm set| \<le>o |- params (set qs \<union> S)|\<close> for qs
    using inf' params_left by blast

  {
    assume \<open>ps \<leadsto> Alpha qs\<close>
    then show \<open>|UNIV :: ('f, 'p) fm set| \<le>o |- params (set qs \<union> S)|\<close>
      using inf by blast
  }

  {
    fix t
    assume \<open>ps \<leadsto> Gamma qs\<close>
    then show \<open>|UNIV :: ('f, 'p) fm set| \<le>o |- params (set (qs S t) \<union> S)|\<close>
      using inf by blast
  }

  {
    fix q
    assume \<open>ps \<leadsto> Confl qs\<close> \<open>q \<in> set qs\<close> \<open>q \<in> S\<close>
    then have \<open>S \<tturnstile>\<^sub>\<forall> \<^bold>\<bottom>\<close>
      using ps calculus_confl by blast
    then show False
      using * by fast
  }

  {
    assume \<open>ps \<leadsto> Alpha qs\<close> \<open>set qs \<union> S \<tturnstile>\<^sub>\<forall> \<^bold>\<bottom>\<close>
    then have \<open>S \<tturnstile>\<^sub>\<forall> \<^bold>\<bottom>\<close>
      using ps calculus_alpha by blast
    then show False
      using * by blast
  }

  {
    assume \<open>ps \<leadsto> Beta qs\<close>
    then show \<open>\<exists>q \<in> set qs. {q} \<union> S \<in> {A. |UNIV :: ('f, 'p) fm set| \<le>o |- params A| \<and> \<not> A \<tturnstile>\<^sub>\<forall> \<^bold>\<bottom>}\<close>
      using * ps inf calculus_beta
      by (metis (no_types, lifting) finite.intros(1-2) finite_list mem_Collect_eq)
    }

  {
    fix t
    assume \<open>ps \<leadsto> Gamma qs\<close> \<open>set (qs S t) \<union> S \<tturnstile>\<^sub>\<forall> \<^bold>\<bottom>\<close>
    then show False
      using * ps calculus_gamma by blast
  }

  {
    assume \<open>ps \<leadsto> Delta qs\<close>
    moreover have \<open>infinite (- (params (set ps \<union> S)))\<close>
      using ps inf' inf_UNIV card_of_ordLeq_finite infinite_params by blast
    then obtain x where **: \<open>x \<notin> params (set ps \<union> S)\<close>
      using infinite_imp_nonempty by blast
    ultimately have \<open>\<exists>x. set (qs x) \<union> S \<in> {A. \<not> A \<tturnstile>\<^sub>\<forall> \<^bold>\<bottom>}\<close>
      using * ps calculus_delta by (metis mem_Collect_eq sup.absorb2)
    then show \<open>\<exists>x. set (qs x) \<union> S \<in> {A. |UNIV :: ('f, 'p) fm set| \<le>o |- params A| \<and> \<not> A \<tturnstile>\<^sub>\<forall> \<^bold>\<bottom>}\<close>
      using ps inf by blast
  }
qed

theorem strong_completeness:
  fixes p :: \<open>('f, 'p) fm\<close>
  assumes mod: \<open>\<forall>(e :: _ \<Rightarrow> 'f tm) f g. (\<forall>q \<in> A. (e, f, g) \<Turnstile>\<^sub>\<forall> q) \<longrightarrow> (e, f, g) \<Turnstile>\<^sub>\<forall> p\<close>
    and inf: \<open>|UNIV :: ('f, 'p) fm set| \<le>o  |- params A|\<close>
  shows \<open>A \<tturnstile>\<^sub>\<forall> p\<close>
proof (rule ccontr)
  assume \<open>\<not> A \<tturnstile>\<^sub>\<forall> p\<close>
  then have *: \<open>\<not> {\<^bold>\<not> p} \<union> A \<tturnstile>\<^sub>\<forall> \<^bold>\<bottom>\<close>
    using BooleX by blast

  let ?S = \<open>set [\<^bold>\<not> p] \<union> A\<close>
  let ?C = \<open>{A :: ('f, 'p) fm set. |UNIV :: ('f, 'p) fm set| \<le>o |- params A| \<and> \<not> A \<tturnstile>\<^sub>\<forall> \<^bold>\<bottom>}\<close>
  let ?M = \<open>hmodel (mk_mcs ?C ?S)\<close>

  have \<open>consistency ?C\<close>
    using deriv_consistency by blast
  moreover have \<open>|UNIV :: ('f, 'p) fm set| \<le>o |- params ?S|\<close>
    using inf params_left by blast
  moreover from this have \<open>?S \<in> ?C\<close>
    using * by simp
  ultimately have *: \<open>\<forall>p \<in> ?S. ?M \<Turnstile>\<^sub>\<forall> p\<close>
    using model_existence by blast
  then have \<open>?M \<Turnstile>\<^sub>\<forall> p\<close>
    using mod by auto
  then show False
    using * by simp
qed

section \<open>Natural Deduction with Lists\<close>

abbreviation \<open>params_list l \<equiv> params_set (set l)\<close>

inductive Calculus :: \<open>('f, 'p) fm list \<Rightarrow> ('f, 'p) fm \<Rightarrow> bool\<close> (\<open>_ \<turnstile>\<^sub>\<forall> _\<close> [50, 50] 50) where
  Assm [simp]: \<open>p \<in> set A \<Longrightarrow> A \<turnstile>\<^sub>\<forall> p\<close>
| FlsE [elim]: \<open>A \<turnstile>\<^sub>\<forall> \<^bold>\<bottom> \<Longrightarrow> A \<turnstile>\<^sub>\<forall> p\<close>
| ImpI [intro]: \<open>p # A \<turnstile>\<^sub>\<forall> q \<Longrightarrow> A \<turnstile>\<^sub>\<forall> p \<^bold>\<longrightarrow> q\<close>
| ImpE [dest]: \<open>A \<turnstile>\<^sub>\<forall> p \<^bold>\<longrightarrow> q \<Longrightarrow> A \<turnstile>\<^sub>\<forall> p \<Longrightarrow> A \<turnstile>\<^sub>\<forall> q\<close>
| UniI [intro]: \<open>A \<turnstile>\<^sub>\<forall> \<langle>\<^bold>\<star>a\<rangle>p \<Longrightarrow> a \<notin> params_list (p # A) \<Longrightarrow> A \<turnstile>\<^sub>\<forall> \<^bold>\<forall>p\<close>
| UniE [dest]: \<open>A \<turnstile>\<^sub>\<forall> \<^bold>\<forall>p \<Longrightarrow> A \<turnstile>\<^sub>\<forall> \<langle>t\<rangle>p\<close>
| Clas: \<open>(p \<^bold>\<longrightarrow> q) # A \<turnstile>\<^sub>\<forall> p \<Longrightarrow> A \<turnstile>\<^sub>\<forall> p\<close>

lemma finite_kernel: \<open>A \<tturnstile>\<^sub>\<forall> p \<Longrightarrow> \<exists>K. set K \<subseteq> A \<and> (\<forall>B. set K \<subseteq> set B \<longrightarrow> set B \<subseteq> A \<longrightarrow> B \<turnstile>\<^sub>\<forall> p)\<close>
proof (induct A p pred: Calculus_Set)
  case (AssmX p A)
  then show ?case
    by (metis Calculus.simps bot.extremum insert_subset set_replicate_Suc)
next
  case (FlsEX A p)
  then show ?case
    by (meson FlsE)
next
  case (ImpIX p A q)
  then show ?case
    by (metis Diff_subset_conv ImpI insert_is_Un insert_mono list.simps(15) set_removeAll)
next
  case (ImpEX A p q)
  then obtain K1 K2 where K:
    \<open>set K1 \<subseteq> A \<and> (\<forall>B. set K1 \<subseteq> set B \<longrightarrow> set B \<subseteq> A \<longrightarrow> B \<turnstile>\<^sub>\<forall> p \<^bold>\<longrightarrow> q)\<close>
    \<open>set K2 \<subseteq> A \<and> (\<forall>B. set K2 \<subseteq> set B \<longrightarrow> set B \<subseteq> A \<longrightarrow> B \<turnstile>\<^sub>\<forall> p)\<close>
    by blast

  let ?K = \<open>K1 @ K2\<close>

  have \<open>set ?K \<subseteq> A\<close>
    using K by simp
  moreover have
    \<open>\<forall>B. set ?K \<subseteq> set B \<longrightarrow> set B \<subseteq> A \<longrightarrow> B \<turnstile>\<^sub>\<forall> p \<^bold>\<longrightarrow> q\<close>
    \<open>\<forall>B. set ?K \<subseteq> set B \<longrightarrow> set B \<subseteq> A \<longrightarrow> B \<turnstile>\<^sub>\<forall> p\<close>
    using K by simp_all
  then have \<open>\<forall>B. set ?K \<subseteq> set B \<longrightarrow> set B \<subseteq> A \<longrightarrow> B \<turnstile>\<^sub>\<forall> q\<close>
    by blast
  ultimately show ?case
    by blast
next
  case (UniIX A a p)
  then obtain K where K: \<open>set K \<subseteq> A\<close> \<open>\<forall>B. set K \<subseteq> set B \<longrightarrow> set B \<subseteq> A \<longrightarrow> B \<turnstile>\<^sub>\<forall> \<langle>\<^bold>\<star> a\<rangle> p\<close>
    by blast
  moreover from this have \<open>\<forall>B. set K \<subseteq> set B \<longrightarrow> set B \<subseteq> A \<longrightarrow> a \<notin> params_list (p # B)\<close>
    using UniIX(3) by auto
  ultimately have \<open>\<forall>B. set K \<subseteq> set B \<longrightarrow> set B \<subseteq> A \<longrightarrow> B \<turnstile>\<^sub>\<forall> \<^bold>\<forall>p\<close>
    by blast
  then show ?case
    using K(1) by blast
next
  case (UniEX A p t)
  then show ?case
    by (meson UniE)
next
  case (ClasX p q A)
  then obtain K where K:
    \<open>set K \<subseteq> {p \<^bold>\<longrightarrow> q} \<union> A\<close>
    \<open>\<forall>B. set K \<subseteq> set B \<longrightarrow> set B \<subseteq> {p \<^bold>\<longrightarrow> q} \<union> A \<longrightarrow> B \<turnstile>\<^sub>\<forall> p\<close>
    by blast

  let ?K = \<open>removeAll (p \<^bold>\<longrightarrow> q) K\<close>

  have \<open>\<forall>B. set ?K \<subseteq> set B \<longrightarrow> set B \<subseteq> A \<longrightarrow> (p \<^bold>\<longrightarrow> q) # B \<turnstile>\<^sub>\<forall> p\<close>
    using K by (metis Diff_single_insert insert_is_Un insert_mono list.simps(15) set_removeAll)
  then have \<open>\<forall>B. set ?K \<subseteq> set B \<longrightarrow> set B \<subseteq> A \<longrightarrow> B \<turnstile>\<^sub>\<forall> p\<close>
    using Clas by blast
  then show ?case
    using K(1) by (metis Diff_subset_conv set_removeAll)
qed

corollary finite_assumptions: \<open>A \<tturnstile>\<^sub>\<forall> p \<Longrightarrow> \<exists>B. set B \<subseteq> A \<and> B \<turnstile>\<^sub>\<forall> p\<close>
  using finite_kernel by blast

lemma calculus_set: \<open>A \<turnstile>\<^sub>\<forall> p \<Longrightarrow> set A \<tturnstile>\<^sub>\<forall> p\<close>
proof (induct A p pred: Calculus)
  case (Clas p q A)
  then show ?case
    using ClasX by auto
qed auto

corollary soundness: \<open>A \<turnstile>\<^sub>\<forall> p \<Longrightarrow> \<forall>q \<in> set A. (E, F, G) \<Turnstile>\<^sub>\<forall> q \<Longrightarrow> (E, F, G) \<Turnstile>\<^sub>\<forall> p\<close>
  using soundness_set calculus_set by blast 

corollary soundness_nil: \<open>[] \<turnstile>\<^sub>\<forall> p \<Longrightarrow> (E, F, G) \<Turnstile>\<^sub>\<forall> p\<close>
  using soundness by fastforce

corollary \<open>\<not> ([] \<turnstile>\<^sub>\<forall> \<^bold>\<bottom>)\<close>
  using soundness_nil by fastforce

corollary strong_completeness_list:
  fixes p :: \<open>('f, 'p) fm\<close>
  assumes mod: \<open>\<forall>(e :: _ \<Rightarrow> 'f tm) f g. (\<forall>q \<in> A. (e, f, g) \<Turnstile>\<^sub>\<forall> q) \<longrightarrow> (e, f, g) \<Turnstile>\<^sub>\<forall> p\<close>
    and inf: \<open>|UNIV :: ('f, 'p) fm set| \<le>o  |- params A|\<close>
  shows \<open>\<exists>B. set B \<subseteq> A \<and> B \<turnstile>\<^sub>\<forall> p\<close>
  using assms strong_completeness finite_assumptions by blast

theorem main:
  fixes p :: \<open>('f, 'p) fm\<close>
  assumes \<open>|UNIV :: ('f, 'p) fm set| \<le>o  |UNIV :: 'f set|\<close>
  shows \<open>[] \<turnstile>\<^sub>\<forall> p \<longleftrightarrow> (\<forall>(e :: _ \<Rightarrow> 'f tm) f g. (e, f, g) \<Turnstile>\<^sub>\<forall> p)\<close>
  using assms strong_completeness_list[where A=\<open>{}\<close>] soundness_nil by fastforce

end
