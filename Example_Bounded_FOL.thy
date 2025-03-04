(*
  Author: Asta Halkjær From, 2025.
*)

theory Example_Bounded_FOL imports
  Analytic_Completeness
begin

section \<open>Syntax\<close>

datatype (params_tm: 'f) tm
  = Var nat (\<open>\<^bold>#\<close>)
  | Fun 'f \<open>'f tm list\<close> (\<open>\<^bold>\<circle>\<close>)

abbreviation Const (\<open>\<^bold>\<star>\<close>) where \<open>\<^bold>\<star>a \<equiv> \<^bold>\<circle>a []\<close>

datatype (params_fm: 'f, 'p) fm
  = Fls (\<open>\<^bold>\<bottom>\<close>)
  | Pre 'p \<open>'f tm list\<close> (\<open>\<^bold>\<cdot>\<close>)
  | Imp \<open>('f, 'p) fm\<close> \<open>('f, 'p) fm\<close> (infixr \<open>\<^bold>\<longrightarrow>\<close> 55)
  | Uni \<open>('f, 'p) fm\<close> (\<open>\<^bold>\<forall>\<close>)

abbreviation Neg :: \<open>('f, 'p) fm \<Rightarrow> ('f, 'p) fm\<close> (\<open>\<^bold>\<not> _\<close> [70] 70) where
  \<open>\<^bold>\<not> p \<equiv> p \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>

abbreviation has_subterm :: \<open>('f, 'p) fm\<close> where
  \<open>has_subterm \<equiv> \<^bold>\<cdot>undefined [\<^bold>#0] \<^bold>\<longrightarrow> \<^bold>\<cdot>undefined [\<^bold>#0]\<close>

abbreviation with_subterm :: \<open>('f, 'p) fm \<Rightarrow> ('f, 'p) fm\<close> where
  \<open>with_subterm p \<equiv> has_subterm \<^bold>\<longrightarrow> p\<close>

section \<open>Semantics\<close>

datatype ('a, 'f, 'p) model = Model \<open>'a set\<close> \<open>nat \<Rightarrow> 'a\<close> \<open>'f \<Rightarrow> 'a list \<Rightarrow> 'a\<close> \<open>'p \<Rightarrow> 'a list \<Rightarrow> bool\<close>

primrec wf_model :: \<open>('a, 'f, 'p) model \<Rightarrow> bool\<close> where
  \<open>wf_model (Model U E F G) = ((\<forall>n. E n \<in> U) \<and> (\<forall>f ts. F f ts \<in> U))\<close>

fun semantics_tm :: \<open>(nat \<Rightarrow> 'a) \<times> ('f \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> 'f tm \<Rightarrow> 'a\<close> (\<open>\<lblot>_\<rblot>\<close>) where
  \<open>\<lblot>(E, _)\<rblot> (\<^bold>#n) = E n\<close>
| \<open>\<lblot>(E, F)\<rblot> (\<^bold>\<circle>f ts) = F f (map \<lblot>(E, F)\<rblot> ts)\<close>

primrec add_env :: \<open>'a \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a\<close> (infix \<open>\<then>\<close> 0) where
  \<open>(t \<then> s) 0 = t\<close>
| \<open>(t \<then> s) (Suc n) = s n\<close>

fun semantics_fm :: \<open>('a, 'f, 'p) model \<Rightarrow> ('f, 'p) fm \<Rightarrow> bool\<close> (infix  \<open>\<Turnstile>\<close> 50) where
  \<open>_ \<Turnstile> \<^bold>\<bottom> \<longleftrightarrow> False\<close>
| \<open>Model _ E F G \<Turnstile> \<^bold>\<cdot>P ts \<longleftrightarrow> G P (map \<lblot>(E, F)\<rblot> ts)\<close>
| \<open>Model U E F G \<Turnstile> p \<^bold>\<longrightarrow> q \<longleftrightarrow> Model U E F G \<Turnstile> p \<longrightarrow> Model U E F G \<Turnstile> q\<close>
| \<open>Model U E F G \<Turnstile> \<^bold>\<forall>p \<longleftrightarrow> (\<forall>x \<in> U. Model U (x \<then> E) F G \<Turnstile> p)\<close>

section \<open>Operations\<close>

primrec lift_tm :: \<open>'f tm \<Rightarrow> 'f tm\<close> where
  \<open>lift_tm (\<^bold>#n) = \<^bold>#(n+1)\<close>
| \<open>lift_tm (\<^bold>\<circle>f ts) = \<^bold>\<circle>f (map lift_tm ts)\<close>

primrec sub_tm :: \<open>(nat \<Rightarrow> 'f tm) \<Rightarrow> 'f tm \<Rightarrow> 'f tm\<close> where
  \<open>sub_tm s (\<^bold>#n) = s n\<close>
| \<open>sub_tm s (\<^bold>\<circle>f ts) = \<^bold>\<circle>f (map (sub_tm s) ts)\<close>

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

lemma wf_model_tm [simp]: \<open>wf_model (Model U E F G) \<Longrightarrow> \<lblot>(E, F)\<rblot> t \<in> U\<close>
  by (induct t) simp_all

lemma size_sub_fm [simp]: \<open>size_fm (sub_fm s p) = size_fm p\<close>
  by (induct p arbitrary: s) simp_all

lemma upd_params_tm [simp]: \<open>f \<notin> params_tm t \<Longrightarrow> \<lblot>(E, F(f := x))\<rblot> t = \<lblot>(E, F)\<rblot> t\<close>
  by (induct t) (auto cong: map_cong)

lemma upd_params_fm [simp]:
  assumes \<open>f \<notin> params_fm p\<close>
  shows \<open>Model U E (F(f := x)) G \<Turnstile> p \<longleftrightarrow> Model U E F G \<Turnstile> p\<close>
  using assms by (induct p arbitrary: E) (auto cong: map_cong)

lemma finite_params_tm [simp]: \<open>finite (params_tm t)\<close>
  by (induct t) simp_all

lemma finite_params_fm' [simp]: \<open>finite (params_fm p)\<close>
  by (induct p) simp_all

lemma env [simp]: \<open>P ((x \<then> E) n) = (P x \<then> \<lambda>n. P (E n)) n\<close>
  by (induct n) simp_all

lemma lift_lemma: \<open>\<lblot>(x \<then> E, F)\<rblot> (lift_tm t) = \<lblot>(E, F)\<rblot> t\<close>
  by (induct t) (auto cong: map_cong)

lemma sub_tm_semantics: \<open>\<lblot>(E, F)\<rblot> (sub_tm s t) = \<lblot>(\<lambda>n. \<lblot>(E, F)\<rblot> (s n), F)\<rblot> t\<close>
  by (induct t) (auto cong: map_cong)

lemma sub_fm_semantics [simp]:
  \<open>Model U E F G \<Turnstile> sub_fm s p \<longleftrightarrow> Model U (\<lambda>n. \<lblot>(E, F)\<rblot> (s n)) F G \<Turnstile> p\<close>
  by (induct p arbitrary: E s) (auto cong: map_cong simp: sub_tm_semantics lift_lemma)

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

section \<open>Terms\<close>

primrec terms_tm :: \<open>'f tm \<Rightarrow> 'f tm set\<close> where
  \<open>terms_tm (\<^bold>#n) = {\<^bold>#n}\<close>
| \<open>terms_tm (\<^bold>\<circle>f ts) = {\<^bold>\<circle>f ts} \<union> \<Union>(set (map terms_tm ts))\<close>

primrec terms_fm :: \<open>('f, 'p) fm \<Rightarrow> 'f tm set\<close> where
  \<open>terms_fm \<^bold>\<bottom> = {}\<close>
| \<open>terms_fm (\<^bold>\<cdot>_ ts) = \<Union>(set (map terms_tm ts))\<close>
| \<open>terms_fm (p \<^bold>\<longrightarrow> q) = terms_fm p \<union> terms_fm q\<close>
| \<open>terms_fm (\<^bold>\<forall>p) = terms_fm p\<close>

definition terms :: \<open>('f, 'p) fm set \<Rightarrow> 'f tm set\<close> where
  \<open>terms S \<equiv> \<Union>p \<in> S. terms_fm p\<close>

subsection \<open>Lemmas\<close>

lemma terms_mono: \<open>S \<subseteq> S' \<Longrightarrow> terms S \<subseteq> terms S'\<close>
  unfolding terms_def by blast

lemma terms_tm_refl [intro]: \<open>t \<in> terms_tm t\<close>
  by (induct t) simp_all

lemma terms_tm_trans [trans]: \<open>s \<in> terms_tm t \<Longrightarrow> r \<in> terms_tm s \<Longrightarrow> r \<in> terms_tm t\<close>
  by (induct t) auto

lemma map_terms_tm [simp]: \<open>terms_tm (map_tm f t) = map_tm f ` terms_tm t\<close>
  by (induct t) auto

lemma map_terms_fm [simp]: \<open>terms_fm (map_fm f g p) = map_tm f ` terms_fm p\<close>
  by (induct p) auto

lemma terms_tm_closed [dest]: \<open>t \<in> terms_tm s \<Longrightarrow> terms_tm t \<subseteq> terms_tm s\<close>
  using terms_tm_trans by blast

lemma terms_fm_closed: \<open>t \<in> terms_fm p \<Longrightarrow> terms_tm t \<subseteq> terms_fm p\<close>
  by (induct p) auto

lemma terms_source: \<open>t \<in> terms S \<Longrightarrow> \<exists>S' \<subseteq> S. finite S' \<and> t \<in> terms S'\<close>
  unfolding terms_def using insert_subset by blast

lemma terms_tm_Fun: \<open>\<^bold>\<circle>f ts \<in> terms_tm s \<Longrightarrow> t \<in> set ts \<Longrightarrow> t \<in> terms_tm s\<close>
  using terms_tm_refl terms_tm_trans
  by (metis UN_I UnI2 list.set_map terms_tm.simps(2))

lemma terms_Fun: \<open>\<^bold>\<circle>f ts \<in> terms S \<Longrightarrow> set ts \<subseteq> terms S\<close>
  using terms_tm_Fun terms_tm_refl terms_fm_closed
  unfolding terms_def by fast

section \<open>Guard\<close>

definition guard :: \<open>'a \<Rightarrow> 'a set \<Rightarrow> 'a\<close> (infix \<open>\<in>?\<close> 50) where
  \<open>x \<in>? S \<equiv> if x \<in> S then x else SOME y. y \<in> S\<close>

lemma guard_in: \<open>S \<noteq> {} \<Longrightarrow> (x \<in>? S) \<in> S\<close>
  unfolding guard_def using some_in_eq by auto

lemma guard_refl [simp]: \<open>t \<in> S \<Longrightarrow> t \<in>? S = t\<close>
  unfolding guard_def by simp

section \<open>Model Existence\<close>

inductive
  confl_class :: \<open>('f, 'p) fm list \<Rightarrow> ('f, 'p) fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<crossmark>\<close> 50) and
  alpha_class :: \<open>('f, 'p) fm list \<Rightarrow> ('f, 'p) fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<alpha>\<close> 50) and
  beta_class :: \<open>('f, 'p) fm list \<Rightarrow> ('f, 'p) fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<beta>\<close> 50) and
  gamma_class :: \<open>('f, 'p) fm list \<Rightarrow> (('f, 'p) fm set \<Rightarrow> _) \<times> ('f tm \<Rightarrow> _) \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<gamma>\<close> 50)
  where
    CFls [intro]: \<open>[ \<^bold>\<bottom> ] \<leadsto>\<^sub>\<crossmark> [ \<^bold>\<bottom> ]\<close>
  | CNeg [intro]: \<open>[ \<^bold>\<not> (\<^bold>\<cdot>P ts) ] \<leadsto>\<^sub>\<crossmark> [ \<^bold>\<cdot>P ts ]\<close>
  | CImpN [intro]: \<open>[ \<^bold>\<not> (p \<^bold>\<longrightarrow> q) ] \<leadsto>\<^sub>\<alpha> [ p, \<^bold>\<not> q ]\<close>
  | CImpP [intro]: \<open>[ p \<^bold>\<longrightarrow> q ] \<leadsto>\<^sub>\<beta> [ \<^bold>\<not> p, q ]\<close>
  | CAllP [intro]: \<open>[ \<^bold>\<forall>p ] \<leadsto>\<^sub>\<gamma> (terms, \<lambda>t. [ \<langle>t\<rangle>p ])\<close>

fun delta_fun :: \<open>('f, 'p) fm \<Rightarrow> 'f \<Rightarrow> ('f, 'p) fm list\<close> where
  \<open>delta_fun (\<^bold>\<not> \<^bold>\<forall>p) x = [ \<^bold>\<not> \<langle>\<^bold>\<star>x\<rangle>p ]\<close>
| \<open>delta_fun _ _ = []\<close>

interpretation C: Confl psub params_fm confl_class
  by unfold_locales (auto simp: fm.map_id0 cong: fm.map_cong0 elim!: confl_class.cases)

interpretation A: Alpha psub params_fm alpha_class
  by unfold_locales (auto elim!: alpha_class.cases)

interpretation B: Beta psub params_fm beta_class
  by unfold_locales (auto elim!: beta_class.cases)

interpretation G: Gamma map_tm psub params_fm gamma_class
proof
  show \<open>\<And>ps F qs t A. ps \<leadsto>\<^sub>\<gamma> (F, qs) \<Longrightarrow> t \<in> F A \<Longrightarrow> \<exists>B \<subseteq> A. finite B \<and> t \<in> F B\<close>
    by (elim gamma_class.cases) (auto simp: terms_source)  
qed (fastforce simp: terms_def elim: gamma_class.cases)+

interpretation D: Delta psub params_fm delta_fun
proof
  show \<open>\<And>f. delta_fun (psub f p) (f x) = map (psub f) (delta_fun p x)\<close> for p :: \<open>('f, 'p) fm\<close> and x
    by (induct p x rule: delta_fun.induct) simp_all
qed

abbreviation Kinds :: \<open>('f, ('f, 'p) fm) kind list\<close> where
  \<open>Kinds \<equiv> [C.kind, A.kind, B.kind, G.kind, D.kind]\<close>

lemma CProp_Kinds:
  assumes \<open>CKind C.kind C\<close> \<open>CKind A.kind C\<close> \<open>CKind B.kind C\<close> \<open>CKind G.kind C\<close> \<open>CKind D.kind C\<close>
  shows \<open>CProp Kinds C\<close>
  unfolding CProp_def using assms by simp

interpretation Consistency_Prop psub params_fm Kinds
  using C.Consistency_Kind_axioms A.Consistency_Kind_axioms B.Consistency_Kind_axioms G.Consistency_Kind_axioms D.Consistency_Kind_axioms
  by (auto intro!: Consistency_Prop.intro C.Params_Fm_axioms simp: Consistency_Prop_axioms_def)

interpretation Maximal_Consistency_UNIV psub params_fm Kinds
proof
  show \<open>infinite (UNIV :: ('f, 'p) fm set)\<close>
    using infinite_UNIV_size[of \<open>\<lambda>p. p \<^bold>\<longrightarrow> p\<close>] by simp
qed

abbreviation canonical :: \<open>('f, 'p) fm set \<Rightarrow> ('f tm, 'f, 'p) model\<close> where
  \<open>canonical S \<equiv> Model (terms S) (\<lambda>n. \<^bold>#n \<in>? terms S) (\<lambda>P ts. \<^bold>\<circle>P ts \<in>? terms S) (\<lambda>P ts. \<^bold>\<cdot>P ts \<in> S)\<close>

lemma wf_canonical:
  assumes \<open>terms H \<noteq> {}\<close>
  shows \<open>wf_model (canonical H)\<close>
  using assms guard_in by (metis (no_types, lifting) wf_model.simps)

lemma canonical_tm_id [simp]:
  \<open>t \<in> terms S \<Longrightarrow> \<lblot>(\<lambda>n. \<^bold>#n \<in>? terms S, \<lambda>P ts. \<^bold>\<circle>P ts \<in>? terms S)\<rblot> t = t\<close>
proof (induct t)
  case (Fun f ts)
  moreover from this have \<open>t \<in> set ts \<Longrightarrow> t \<in> terms S\<close> for t
    by (meson in_mono terms_Fun)
  ultimately show ?case
    by (simp add: list.map_ident_strong)
qed simp

lemma canonical_tm_id_map [simp]:
  \<open>set ts \<subseteq> terms S \<Longrightarrow> map \<lblot>(\<lambda>n. \<^bold>#n \<in>? terms S, \<lambda>P ts. \<^bold>\<circle>P ts \<in>? terms S)\<rblot> ts = ts\<close>
  by (induct ts) simp_all

locale MyHintikka = Hintikka psub params_fm Kinds S
  for S :: \<open>('f, 'p) fm set\<close> +
  assumes terms_ne: \<open>terms S \<noteq> {}\<close>
begin

lemmas
  confl = hkind[of C.kind] and
  alpha = hkind[of A.kind] and
  beta = hkind[of B.kind] and
  gamma = hkind[of G.kind] and
  delta = hkind[of D.kind]

theorem model: \<open>(p \<in> S \<longrightarrow> canonical S \<Turnstile> p) \<and> (\<^bold>\<not> p \<in> S \<longrightarrow> \<not> canonical S \<Turnstile> p)\<close>
proof (induct p rule: wf_induct[where r=\<open>measure size_fm\<close>])
  case 1
  then show ?case
    by simp
next
  case (2 x)
  then show ?case
  proof (cases x)
    case Fls
    then show ?thesis
      using confl by fastforce
  next
    case (Pre P ts)
    then show ?thesis
    proof (safe del: notI)
      assume \<open>x = \<^bold>\<cdot>P ts\<close> \<open>\<^bold>\<cdot>P ts \<in> S\<close>
      moreover from this have \<open>set ts \<subseteq> terms S\<close>
        using terms_tm_refl terms_def by fastforce
      ultimately show \<open>canonical S \<Turnstile> \<^bold>\<cdot>P ts\<close>
        by simp
    next
      assume \<open>x = \<^bold>\<cdot>P ts\<close> \<open>\<^bold>\<not> \<^bold>\<cdot>P ts \<in> S\<close>
      then have \<open>\<^bold>\<cdot>P ts \<notin> S\<close>
        using confl by force
      moreover have \<open>set ts \<subseteq> terms S\<close>
        using \<open>\<^bold>\<not> \<^bold>\<cdot>P ts \<in> S\<close> terms_def terms_tm_refl by fastforce
      ultimately show \<open>\<not> canonical S \<Turnstile> \<^bold>\<cdot>P ts\<close>
        by simp
    qed
  next
    case (Imp p q)
    then show ?thesis
    proof (safe del: notI)
      assume \<open>x = p \<^bold>\<longrightarrow> q\<close> \<open>p \<^bold>\<longrightarrow> q \<in> S\<close>
      then have \<open>\<^bold>\<not> p \<in> S \<or> q \<in> S\<close>
        using beta by force
      then show \<open>canonical S \<Turnstile> p \<^bold>\<longrightarrow> q\<close>
        using 2 Imp by auto
    next
      assume \<open>x = p \<^bold>\<longrightarrow> q\<close> \<open>\<^bold>\<not> (p \<^bold>\<longrightarrow> q) \<in> S\<close>
      then have \<open>p \<in> S \<and> \<^bold>\<not> q \<in> S\<close>
        using alpha by force
      then show \<open>\<not> canonical S \<Turnstile> p \<^bold>\<longrightarrow> q\<close>
        using 2 Imp by auto
    qed
  next
    case (Uni p)
    then show ?thesis
    proof (safe del: notI)
      assume \<open>x = \<^bold>\<forall>p\<close> \<open>\<^bold>\<forall>p \<in> S\<close>
      then have \<open>\<forall>t \<in> terms S. \<langle>t\<rangle>p \<in> S\<close>
        using gamma by fastforce
      moreover have \<open>\<forall>t. (\<langle>t\<rangle>p, \<^bold>\<forall>p) \<in> measure size_fm\<close>
        by simp
      ultimately have \<open>\<forall>t \<in> terms S. canonical S \<Turnstile> \<langle>t\<rangle>p\<close>
        using 2 \<open>x = \<^bold>\<forall>p\<close> by blast
      then show \<open>canonical S \<Turnstile> \<^bold>\<forall>p\<close>
        by simp
    next
      assume \<open>x = \<^bold>\<forall>p\<close> \<open>\<^bold>\<not> \<^bold>\<forall>p \<in> S\<close>
      then obtain a where \<open>\<^bold>\<not> \<langle>\<^bold>\<star>a\<rangle>p \<in> S\<close>
        using delta by fastforce
      moreover have \<open>(\<langle>\<^bold>\<star>a\<rangle>p, \<^bold>\<forall>p) \<in> measure size_fm\<close>
        by simp
      ultimately have \<open>\<not> canonical S \<Turnstile> \<langle>\<^bold>\<star>a\<rangle>p\<close>
        using 2 \<open>x = \<^bold>\<forall>p\<close> by blast
      then show \<open>\<not> canonical S \<Turnstile> \<^bold>\<forall>p\<close>
        using wf_canonical[OF terms_ne] by auto
    qed
  qed
qed

end

theorem model_existence:
  fixes S :: \<open>('f, 'p) fm set\<close>
  assumes \<open>CProp Kinds C\<close>
    and \<open>S \<in> C\<close>
    and \<open>|UNIV :: ('f, 'p) fm set| \<le>o |- C.params S|\<close>
    and \<open>terms S \<noteq> {}\<close>
    and \<open>p \<in> S\<close>
  shows \<open>canonical (mk_mcs C S) \<Turnstile> p\<close>
proof -
  have *: \<open>MyHintikka (mk_mcs C S)\<close>
  proof
    show \<open>terms (mk_mcs C S) \<noteq> {}\<close>
      using assms(4) terms_mono Extend_subset by blast
  next
    show \<open>HProp Kinds (mk_mcs C S)\<close>
      using mk_mcs_Hintikka[OF assms(1-3)] Hintikka.hintikka by blast
  qed
  moreover have \<open>p \<in> mk_mcs C S\<close>
    using assms(5) Extend_subset by blast
  ultimately show ?thesis
    using MyHintikka.model by blast
qed

section \<open>Natural Deduction\<close>

locale Natural_Deduction
begin

inductive ND_Set :: \<open>('f, 'p) fm set \<Rightarrow> ('f, 'p) fm \<Rightarrow> bool\<close> (infix \<open>\<tturnstile>\<close> 50) where
  Assm [dest]: \<open>p \<in> A \<Longrightarrow> A \<tturnstile> p\<close>
| FlsE [elim]: \<open>A \<tturnstile> \<^bold>\<bottom> \<Longrightarrow> A \<tturnstile> p\<close>
| ImpI [intro]: \<open>{p} \<union> A \<tturnstile> q \<Longrightarrow> A \<tturnstile> p \<^bold>\<longrightarrow> q\<close>
| ImpE [dest]: \<open>A \<tturnstile> p \<^bold>\<longrightarrow> q \<Longrightarrow> A \<tturnstile> p \<Longrightarrow> A \<tturnstile> q\<close>
| UniI [intro]: \<open>A \<tturnstile> \<langle>\<^bold>\<star>a\<rangle>p \<Longrightarrow> a \<notin> C.params ({p} \<union> A) \<Longrightarrow> A \<tturnstile> \<^bold>\<forall>p\<close>
| UniE [dest]: \<open>A \<tturnstile> \<^bold>\<forall>p \<Longrightarrow> t \<in> terms ({p} \<union> A) \<Longrightarrow> A \<tturnstile> \<langle>t\<rangle>p\<close>
| Clas: \<open>{p \<^bold>\<longrightarrow> q} \<union> A \<tturnstile> p \<Longrightarrow> A \<tturnstile> p\<close>

subsection \<open>Soundness\<close>

theorem soundness_set:
  assumes \<open>A \<tturnstile> p\<close> \<open>wf_model (Model U E F G)\<close>
  shows \<open>\<forall>q \<in> A. Model U E F G \<Turnstile> q \<Longrightarrow> Model U E F G \<Turnstile> p\<close>
  using assms
proof (induct A p arbitrary: F pred: ND_Set)
  case (UniI A a p)
  have \<open>\<forall>x \<in> U. \<forall>q \<in> A. Model U E (F(a := \<lambda>_. x)) G \<Turnstile> q\<close>
    using UniI(3-) by simp
  moreover have \<open>\<forall>x \<in> U. wf_model (Model U E (F(a := \<lambda>_. x)) G)\<close>
    using UniI(5) by simp
  ultimately have \<open>\<forall>x \<in> U. Model U E (F(a := \<lambda>_. x)) G \<Turnstile> \<langle>\<^bold>\<star>a\<rangle>p\<close>
    using UniI by meson
  then show ?case
    using UniI by simp
qed auto

subsection \<open>Derivational Consistency\<close>

lemma Boole: \<open>{\<^bold>\<not> p} \<union> A \<tturnstile> \<^bold>\<bottom> \<Longrightarrow> A \<tturnstile> p\<close>
  unfolding Neg_def using Clas FlsE by fast

sublocale DC: Derivational_Confl psub params_fm confl_class \<open>\<lambda>A. A \<tturnstile> \<^bold>\<bottom>\<close>
proof
  fix A ps qs and q :: \<open>('f, 'p) fm\<close>
  assume \<open>ps \<leadsto>\<^sub>\<crossmark> qs\<close> \<open>set ps \<subseteq> A\<close> \<open>q \<in> set qs\<close> \<open>q \<in> A\<close>
  then show \<open>A \<tturnstile> \<^bold>\<bottom>\<close>
    by cases auto
qed

sublocale DA: Derivational_Alpha psub params_fm alpha_class \<open>\<lambda>A. A \<tturnstile> \<^bold>\<bottom>\<close>
proof
  fix A and ps qs :: \<open>('f, 'p) fm list\<close>
  assume \<open>ps \<leadsto>\<^sub>\<alpha> qs\<close> and *: \<open>set ps \<subseteq> A\<close> \<open>set qs \<union> A \<tturnstile> \<^bold>\<bottom>\<close>
  then show \<open>A \<tturnstile> \<^bold>\<bottom>\<close>
  proof cases
    case (CImpN p q)
    then have \<open>A \<tturnstile> \<^bold>\<not> (p \<^bold>\<longrightarrow> q)\<close>
      using *(1) by auto
    moreover have \<open>A \<tturnstile> p \<^bold>\<longrightarrow> q\<close>
      using CImpN(2) *(2) Boole[of q \<open>{p} \<union> A\<close>] by auto
    ultimately show ?thesis
      by blast
  qed
qed

sublocale DB: Derivational_Beta psub params_fm beta_class \<open>\<lambda>A. A \<tturnstile> \<^bold>\<bottom>\<close>
proof
  fix A and ps qs :: \<open>('f, 'p) fm list\<close>
  assume \<open>ps \<leadsto>\<^sub>\<beta> qs\<close> and *: \<open>set ps \<subseteq> A\<close> \<open>\<forall>q \<in> set qs. {q} \<union> A \<tturnstile> \<^bold>\<bottom>\<close>
  then show \<open>A \<tturnstile> \<^bold>\<bottom>\<close>
  proof cases
    case (CImpP p q)
    then show ?thesis
      using * Boole[of p A]
      by (metis Assm ImpE ImpI list.set_intros(1) set_subset_Cons subset_iff)
  qed
qed

sublocale DG: Derivational_Gamma map_tm psub params_fm gamma_class \<open>\<lambda>A. A \<tturnstile> \<^bold>\<bottom>\<close>
proof
  fix A F qs t and ps :: \<open>('f, 'p) fm list\<close>
  assume \<open>ps \<leadsto>\<^sub>\<gamma> (F, qs)\<close> and *: \<open>set ps \<subseteq> A\<close> \<open>t \<in> F A\<close> \<open>set (qs t) \<union> A \<tturnstile> \<^bold>\<bottom>\<close>
  then show \<open>A \<tturnstile> \<^bold>\<bottom>\<close>
  proof cases
    case (CAllP p)
    then have \<open>t \<in> terms ({p} \<union> A)\<close>
      using * terms_mono by blast
    then show ?thesis
      using CAllP * UniE[of A p t] ImpI by auto
  qed
qed

sublocale DD: Derivational_Delta psub params_fm delta_fun \<open>\<lambda>A. A \<tturnstile> \<^bold>\<bottom>\<close>
proof
  fix A a and p :: \<open>('f, 'p) fm\<close>
  assume \<open>p \<in> A\<close> \<open>a \<notin> C.params A\<close> \<open>set (delta_fun p a) \<union> A \<tturnstile> \<^bold>\<bottom>\<close>
  then show \<open>A \<tturnstile> \<^bold>\<bottom>\<close>
  proof (induct p a rule: delta_fun.induct)
    case (1 p x)
    then have \<open>x \<notin> C.params ({p} \<union> A)\<close>
      by auto
    moreover have \<open>A \<tturnstile> \<langle>\<^bold>\<star> x\<rangle> p\<close>
      using "1.prems"(3) Boole by auto
    ultimately show ?thesis
      using 1(1) UniI by blast
  qed simp_all
qed

sublocale Derivational_Consistency psub params_fm Kinds \<open>|UNIV|\<close> \<open>\<lambda>A. A \<tturnstile> \<^bold>\<bottom>\<close>
  using CProp_Kinds[OF DC.kind DA.kind DB.kind DG.kind DD.kind] by unfold_locales

subsection \<open>Strong Completeness\<close>

lemma with_subterm_elim: \<open>A \<tturnstile> with_subterm p \<Longrightarrow> A \<tturnstile> p\<close>
  using Assm ImpE by blast

theorem strong_completeness:
  fixes p :: \<open>('f, 'p) fm\<close>
  assumes mod: \<open>\<And>(U :: 'f tm set) E F G. wf_model (Model U E F G) \<Longrightarrow> (\<forall>q \<in> A. Model U E F G \<Turnstile> q) \<Longrightarrow> Model U E F G \<Turnstile> p\<close>
    and inf: \<open>|UNIV :: ('f, 'p) fm set| \<le>o  |- C.params A|\<close>
  shows \<open>A \<tturnstile> p\<close>
proof (rule ccontr)
  assume \<open>\<not> A \<tturnstile> p\<close>
  then have \<open>\<not> A \<tturnstile> with_subterm p\<close>
    using with_subterm_elim by blast
  then have *: \<open>\<not> {\<^bold>\<not> with_subterm p} \<union> A \<tturnstile> \<^bold>\<bottom>\<close>
    using Boole by (metis insert_is_Un)

  let ?S = \<open>set [\<^bold>\<not> with_subterm p] \<union> A\<close>
  let ?C = \<open>{A :: ('f, 'p) fm set. |UNIV :: ('f, 'p) fm set| \<le>o |- C.params A| \<and> \<not> A \<tturnstile> \<^bold>\<bottom>}\<close>
  let ?M = \<open>canonical (mk_mcs ?C ?S)\<close>

  have ne: \<open>terms ?S \<noteq> {}\<close>
    unfolding terms_def by simp
  then have \<open>terms (mk_mcs ?C ?S) \<noteq> {}\<close>
    by (metis (no_types, lifting) Extend_subset subset_empty terms_mono)
  then have wf: \<open>wf_model ?M\<close>
    using wf_canonical by fast

  have \<open>CProp Kinds ?C\<close>
    using Consistency by blast
  moreover have \<open>|UNIV :: ('f, 'p) fm set| \<le>o |- C.params ?S|\<close>
    using inf params_left by blast
  moreover from this have \<open>?S \<in> ?C\<close>
    using * by simp
  ultimately have *: \<open>\<forall>p \<in> ?S. ?M \<Turnstile> p\<close>
    using model_existence ne by blast
  then have \<open>?M \<Turnstile> p\<close>
    using mod[OF wf] by fast 
  then show False
    using * by simp
qed

subsection \<open>Natural Deduction with Lists\<close>

inductive ND_List :: \<open>('f, 'p) fm list \<Rightarrow> ('f, 'p) fm \<Rightarrow> bool\<close> (infix \<open>\<turnstile>\<close> 50) where
  Assm [simp]: \<open>p \<in> set A \<Longrightarrow> A \<turnstile> p\<close>
| FlsE [elim]: \<open>A \<turnstile> \<^bold>\<bottom> \<Longrightarrow> A \<turnstile> p\<close>
| ImpI [intro]: \<open>p # A \<turnstile> q \<Longrightarrow> A \<turnstile> p \<^bold>\<longrightarrow> q\<close>
| ImpE [dest]: \<open>A \<turnstile> p \<^bold>\<longrightarrow> q \<Longrightarrow> A \<turnstile> p \<Longrightarrow> A \<turnstile> q\<close>
| UniI [intro]: \<open>A \<turnstile> \<langle>\<^bold>\<star>a\<rangle>p \<Longrightarrow> a \<notin> C.params ({p} \<union> set A) \<Longrightarrow> A \<turnstile> \<^bold>\<forall>p\<close>
| UniE [dest]: \<open>A \<turnstile> \<^bold>\<forall>p \<Longrightarrow> t \<in> terms ({p} \<union> set A) \<Longrightarrow> A \<turnstile> \<langle>t\<rangle>p\<close>
| Clas: \<open>(p \<^bold>\<longrightarrow> q) # A \<turnstile> p \<Longrightarrow> A \<turnstile> p\<close>

definition bounded :: \<open>'a list \<Rightarrow> 'a set \<Rightarrow> ('a list \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>bounded K A P \<equiv> set K \<subseteq> A \<and> (\<forall>B. set K \<subseteq> set B \<longrightarrow> set B \<subseteq> A \<longrightarrow> P B)\<close>

lemma bounded_one [elim]:
  assumes \<open>bounded K A P\<close> \<open>\<And>A. P A \<Longrightarrow> Q A\<close>
  shows \<open>bounded K A Q\<close>
  using assms unfolding bounded_def by simp

lemma bounded_two [elim]:
  assumes \<open>bounded K A P\<close> \<open>bounded K' A Q\<close> \<open>\<And>A. P A \<Longrightarrow> Q A \<Longrightarrow> R A\<close>
  shows \<open>bounded (K @ K') A R\<close>
  using assms unfolding bounded_def by simp

lemma bounded_removeAll [dest]:
  assumes \<open>bounded K ({p} \<union> A) P\<close>
  shows \<open>bounded (removeAll p K) A (\<lambda>B. P (p # B))\<close>
  using assms unfolding bounded_def
  by (metis Diff_subset_conv insert_is_Un insert_mono list.simps(15) set_removeAll)

lemma bounded_terms:
  assumes \<open>t \<in> terms ({p} \<union> A)\<close>
  shows \<open>t \<in> terms_fm p \<and> bounded [] A (\<lambda>B. t \<in> terms (set (p # B))) \<or>
    (\<exists>q \<in> A. t \<in> terms_fm q \<and> bounded [q] A (\<lambda>B. t \<in> terms (set (p # B))))\<close>
  using assms unfolding terms_def bounded_def by auto

lemma bounded_params:
  assumes \<open>a \<notin> C.params ({p} \<union> A)\<close> \<open>bounded K A P\<close>
  shows \<open>bounded K A (\<lambda>B. a \<notin> C.params (set (p # B)))\<close>
  using assms unfolding bounded_def by auto

lemma finite_kernel: \<open>A \<tturnstile> p \<Longrightarrow> \<exists>K. bounded K A (\<lambda>B. B \<turnstile> p)\<close>
proof (induct A p pred: ND_Set)
  case (Assm p A)
  then show ?case
    unfolding bounded_def by (auto intro!: exI[of _ \<open>[p]\<close>])
next
  case (UniI A a p)
  then show ?case
    using bounded_params by fastforce
next
  case (UniE A p t)
  then show ?case
    using bounded_terms by fastforce
next
  case (Clas p q A)
  then have \<open>\<exists>K. bounded K A (\<lambda>B. (p \<^bold>\<longrightarrow> q) # B \<turnstile> p)\<close>
    by fast
  then show ?case
    using ND_List.Clas unfolding bounded_def by meson
qed fast+

corollary finite_assumptions: \<open>A \<tturnstile> p \<Longrightarrow> \<exists>B. set B \<subseteq> A \<and> B \<turnstile> p\<close>
  using finite_kernel unfolding bounded_def by blast

lemma to_set: \<open>A \<turnstile> p \<Longrightarrow> set A \<tturnstile> p\<close>
  by (induct A p pred: ND_List) (auto intro: ND_Set.Clas)

corollary soundness_list:
  assumes \<open>A \<turnstile> p\<close> \<open>wf_model (Model U E F G)\<close> \<open>\<forall>q \<in> set A. Model U E F G \<Turnstile> q\<close>
  shows \<open>Model U E F G \<Turnstile> p\<close>
  using assms soundness_set to_set by fast

corollary soundness_nil: \<open>[] \<turnstile> p \<Longrightarrow> wf_model (Model U E F G) \<Longrightarrow> Model U E F G \<Turnstile> p\<close>
  using soundness_list by (metis empty_iff list.set(1))

corollary \<open>\<not> ([] \<turnstile> \<^bold>\<bottom>)\<close>
  using soundness_nil by fastforce

corollary strong_completeness_list:
  fixes p :: \<open>('f, 'p) fm\<close>
  assumes mod: \<open>\<And>(U :: 'f tm set) E F G. wf_model (Model U E F G) \<Longrightarrow> (\<forall>q \<in> A. Model U E F G \<Turnstile> q) \<Longrightarrow> Model U E F G \<Turnstile> p\<close>
    and inf: \<open>|UNIV :: ('f, 'p) fm set| \<le>o  |- C.params A|\<close>
  shows \<open>\<exists>B. set B \<subseteq> A \<and> B \<turnstile> p\<close>
  using assms strong_completeness finite_assumptions by blast

theorem main:
  fixes p :: \<open>('f, 'p) fm\<close>
  assumes \<open>|UNIV :: ('f, 'p) fm set| \<le>o |UNIV :: 'f set|\<close>
  shows \<open>[] \<turnstile> p \<longleftrightarrow> (\<forall>(U :: 'f tm set) E F G. wf_model (Model U E F G) \<longrightarrow> Model U E F G \<Turnstile> p)\<close>
  using assms strong_completeness_list[of \<open>{}\<close> p] soundness_nil[of p]
  by simp blast

end

section \<open>Tableau\<close>

locale Tableau
begin

inductive TC :: \<open>('f, 'p) fm set \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [51] 50) where
  Axiom [simp]: \<open>\<^bold>\<not> \<^bold>\<cdot>P ts \<in> A \<Longrightarrow> \<^bold>\<cdot>P ts \<in> A \<Longrightarrow> \<turnstile> A\<close>
| FlsP [simp]: \<open>\<^bold>\<bottom> \<in> A \<Longrightarrow> \<turnstile> A\<close>
| FlsN [intro]: \<open>\<turnstile> A \<Longrightarrow> \<turnstile> {\<^bold>\<not> \<^bold>\<bottom>} \<union> A\<close>
| ImpP [intro]: \<open>\<turnstile> {\<^bold>\<not> p} \<union> A \<Longrightarrow> \<turnstile> {q} \<union> A \<Longrightarrow> \<turnstile> {p \<^bold>\<longrightarrow> q} \<union> A\<close>
| ImpN [intro]: \<open>\<turnstile> {p, \<^bold>\<not> q} \<union> A \<Longrightarrow> \<turnstile> {\<^bold>\<not> (p \<^bold>\<longrightarrow> q)} \<union> A\<close>
| UniP [intro]: \<open>\<turnstile> {\<langle>t\<rangle>p} \<union> A \<Longrightarrow> t \<in> terms ({p} \<union> A) \<Longrightarrow> \<turnstile> {\<^bold>\<forall>p} \<union> A\<close>
| UniN [intro]: \<open>\<turnstile> {\<^bold>\<not> \<langle>\<^bold>\<star>a\<rangle>p} \<union> A \<Longrightarrow> a \<notin> C.params ({p} \<union> A) \<Longrightarrow> \<turnstile> {\<^bold>\<not> \<^bold>\<forall>p} \<union> A\<close>

subsection \<open>Soundness\<close>

theorem soundness:
  assumes \<open>\<turnstile> A\<close> \<open>wf_model (Model U E F G)\<close>
  shows \<open>\<exists>q \<in> A. \<not> Model U E F G \<Turnstile> q\<close>
  using assms
proof (induct A arbitrary: F pred: TC)
  case (Axiom P ts A)
  then show ?case
    by (meson semantics_fm.simps(1) semantics_fm.simps(3))
next
  case (FlsP A)
  then show ?case
    by force
next
  case (UniP t p A)
  then have \<open>\<exists>q \<in> {\<langle>t\<rangle> p} \<union> A. \<not> Model U E F G \<Turnstile> q\<close>
    by blast
  moreover have \<open>\<lblot>(E, F)\<rblot> t \<in> U\<close>
    using UniP.prems by auto
  then have \<open>\<not> Model U E F G \<Turnstile> \<langle>t\<rangle> p \<Longrightarrow> \<not> Model U E F G \<Turnstile> \<^bold>\<forall>p\<close>
    by auto
  ultimately show ?case
    by blast
next
  case (UniN a p A)
  then have \<open>\<forall>x \<in> U. wf_model (Model U E (F(a := \<lambda>_. x)) G)\<close>
    by simp
  then have \<open>\<forall>x \<in> U. \<exists>q \<in> {\<^bold>\<not> \<langle>\<^bold>\<star> a\<rangle> p} \<union> A. \<not> Model U E (F(a := \<lambda>_. x)) G \<Turnstile> q\<close>
    using UniN(2) by fast
  then show ?case
    using UniN by simp
qed auto

subsection \<open>Derivational Consistency\<close>

sublocale DC: Derivational_Confl psub params_fm confl_class TC
proof
  fix A ps qs and q :: \<open>('f, 'p) fm\<close>
  assume \<open>ps \<leadsto>\<^sub>\<crossmark> qs\<close> \<open>set ps \<subseteq> A\<close> \<open>q \<in> set qs\<close> \<open>q \<in> A\<close>
  then show \<open>\<turnstile> A\<close>
    by cases auto
qed

sublocale DA: Derivational_Alpha psub params_fm alpha_class TC
proof
  fix A and ps qs :: \<open>('f, 'p) fm list\<close>
  assume \<open>ps \<leadsto>\<^sub>\<alpha> qs\<close> and *: \<open>set ps \<subseteq> A\<close> \<open>\<turnstile> set qs \<union> A\<close>
  then show \<open>\<turnstile> A\<close>
  proof cases
    case (CImpN p q)
    then show ?thesis
      using * ImpN[of p q A]
      by (simp add: sup.order_iff)
  qed
qed

sublocale DB: Derivational_Beta psub params_fm beta_class TC
proof
  fix A and ps qs :: \<open>('f, 'p) fm list\<close>
  assume \<open>ps \<leadsto>\<^sub>\<beta> qs\<close> and *: \<open>set ps \<subseteq> A\<close> \<open>\<forall>q \<in> set qs. \<turnstile> {q} \<union> A\<close>
  then show \<open>\<turnstile> A\<close>
  proof cases
    case (CImpP p q)
    then show ?thesis
      using * ImpP[of p A q]
      by (simp add: sup.order_iff)
  qed
qed

sublocale DG: Derivational_Gamma map_tm psub params_fm gamma_class TC
proof
  fix A F qs t and ps :: \<open>('f, 'p) fm list\<close>
  assume \<open>ps \<leadsto>\<^sub>\<gamma> (F, qs)\<close> and *: \<open>set ps \<subseteq> A\<close> \<open>t \<in> F A\<close> \<open>\<turnstile> set (qs t) \<union> A\<close>
  then show \<open>\<turnstile> A\<close>
  proof cases
    case (CAllP p)
    then have \<open>t \<in> terms ({p} \<union> A)\<close>
      using * terms_mono by blast
    then show ?thesis
      using CAllP * UniP[of t p A]
      by (simp add: sup.order_iff)
  qed
qed

sublocale DD: Derivational_Delta psub params_fm delta_fun TC
proof
  fix A a and p :: \<open>('f, 'p) fm\<close>
  assume \<open>p \<in> A\<close> \<open>a \<notin> C.params A\<close> \<open>\<turnstile> set (delta_fun p a) \<union> A\<close>
  then show \<open>\<turnstile> A\<close>
  proof (induct p a rule: delta_fun.induct)
    case (1 p x)
    then have \<open>x \<notin> C.params ({p} \<union> A)\<close>
      by auto
    then show ?thesis
      using 1 UniN[of x p A]
      by (simp add: sup.order_iff insert_absorb)
  qed simp_all
qed

sublocale Derivational_Consistency psub params_fm Kinds \<open>|UNIV|\<close> TC
  using CProp_Kinds[OF DC.kind DA.kind DB.kind DG.kind DD.kind] by unfold_locales

subsection \<open>Strong Completeness\<close>

theorem strong_completeness:
  fixes p :: \<open>('f, 'p) fm\<close>
  assumes mod: \<open>\<And>(U :: 'f tm set) E F G. wf_model (Model U E F G) \<Longrightarrow> (\<forall>q \<in> A. Model U E F G \<Turnstile> q) \<Longrightarrow> Model U E F G \<Turnstile> p\<close>
    and inf: \<open>|UNIV :: ('f, 'p) fm set| \<le>o  |- C.params A|\<close>
  shows \<open>\<turnstile> {\<^bold>\<not> with_subterm p} \<union> A\<close>
proof (rule ccontr)
  assume *: \<open>\<not> \<turnstile> {\<^bold>\<not> with_subterm p} \<union> A\<close>
  
  let ?S = \<open>set [\<^bold>\<not> with_subterm p] \<union> A\<close>
  let ?C = \<open>{A :: ('f, 'p) fm set. |UNIV :: ('f, 'p) fm set| \<le>o |- C.params A| \<and> \<not> \<turnstile> A}\<close>
  let ?M = \<open>canonical (mk_mcs ?C ?S)\<close>

  have ne: \<open>terms ?S \<noteq> {}\<close>
    unfolding terms_def by simp
  then have \<open>terms (mk_mcs ?C ?S) \<noteq> {}\<close>
    by (metis (no_types, lifting) Extend_subset subset_empty terms_mono)
  then have wf: \<open>wf_model ?M\<close>
    using wf_canonical by fast

  have \<open>CProp Kinds ?C\<close>
    using Consistency by blast
  moreover have \<open>|UNIV :: ('f, 'p) fm set| \<le>o |- C.params ?S|\<close>
    using inf params_left by blast
  moreover from this have \<open>?S \<in> ?C\<close>
    using * by simp
  ultimately have *: \<open>\<forall>p \<in> ?S. ?M \<Turnstile> p\<close>
    using model_existence ne by blast
  then have \<open>?M \<Turnstile> p\<close>
    using mod[OF wf] by fast 
  then show False
    using * by simp
qed

end

end
