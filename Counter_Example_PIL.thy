theory Counter_Example_PIL imports
  Example_PIL
  Fin_Arith_Prog
begin

section \<open>Model\<close>

definition Pss :: \<open>int set set\<close> where
  \<open>Pss \<equiv> {U. fin_arith U}\<close>

lemma Pss_empty: \<open>{} \<in> Pss\<close>
  unfolding Pss_def by blast

lemma Pss_UNIV: \<open>UNIV \<in> Pss\<close>
  unfolding Pss_def by blast

lemma Pss_union: \<open>X \<in> Pss \<Longrightarrow> Y \<in> Pss \<Longrightarrow> X \<union> Y \<in> Pss\<close>
  unfolding Pss_def by blast

lemma Pss_inter: \<open>X \<in> Pss \<Longrightarrow> Y \<in> Pss \<Longrightarrow> X \<inter> Y \<in> Pss\<close>
  unfolding Pss_def by blast
  
lemma Pss_compl: \<open>X \<in> Pss \<Longrightarrow> - X \<in> Pss\<close>
  unfolding Pss_def by blast

definition my_gframe :: \<open>int gframe\<close> where
  \<open>my_gframe \<equiv> \<lparr> \<W> = UNIV, \<R> = \<lambda>x. UNIV, \<Pi> = Pss \<rparr>\<close>

lemma wf_frame_mygframe: \<open>wf_frame (frame.truncate my_gframe)\<close>
  unfolding wf_frame_def unfolds my_gframe_def by blast  

lemma admissible_mygframe: \<open>admissible (frame.truncate my_gframe) (\<Pi> my_gframe)\<close>
  unfolding admissible_def unfolds my_gframe_def Pss_def
  by (auto simp: Compl_eq_Diff_UNIV[symmetric])

lemma wf_mygframe: \<open>wf_gframe my_gframe\<close>
  using wf_frame_mygframe admissible_mygframe
  unfolding wf_gframe_def unfolds my_gframe_def Pss_def by fast

definition my_model :: \<open>(int, int) model\<close> where
  \<open>my_model \<equiv> gframe.extend my_gframe \<lparr>\<N> = \<lambda>i. i, \<NN> = \<lambda>i. int i, \<V> = \<lambda>n. {}, \<VV> = \<lambda>n. {}\<rparr>\<close>

lemma wf_mymodel: \<open>wf_model my_model\<close>
  using wf_mygframe unfolding wf_model_def wf_env_def unfolds my_model_def my_gframe_def Pss_def
  by blast

section \<open>Counterexample\<close>

abbreviation GloE :: \<open>'x fm \<Rightarrow> 'x fm\<close> (\<open>\<^bold>E\<close>) where
  \<open>\<^bold>E p \<equiv> \<^bold>\<not> (\<^bold>A (\<^bold>\<not> p))\<close>

text \<open>Nowhere-or-twice says that if formula p holds somewhere, then it holds in at least two distinct worlds.\<close>
text \<open>(We ignore de Bruijn complications and only instantiate with closed formulas.)\<close>

abbreviation \<open>nowhere_or_twice p \<equiv>
  \<^bold>@ (\<^bold>\<circle>0) (\<^bold>\<diamond> p) \<^bold>\<longrightarrow>
  \<^bold>@ (\<^bold>\<circle>0) (\<^bold>\<diamond> (\<^bold>\<down> (
    \<^bold>@ (\<^bold>\<circle>0) (\<^bold>\<diamond> (\<^bold>\<down> (
      (\<^bold>@ (\<^bold>#1) p) \<^bold>\<and>
      (\<^bold>@ (\<^bold>#0) p) \<^bold>\<and>
      \<^bold>\<not> (\<^bold>@ (\<^bold>#0) (\<^bold>\<bullet>(\<^bold>#1)))
  ))))))\<close>

text \<open>Finite unions of arithmetic progressions are either empty or infinite.\<close>

lemma fin_arith_nowhere_or_twice:
  assumes \<open>fin_arith U\<close>
  shows \<open>U = {} \<or> (\<exists>x y. x \<in> U \<and> y \<in> U \<and> x \<noteq> y)\<close>
  using assms arith_ne_infinite unfolding fin_arith_def
  by (metis infinite_int_iff_unbounded less_le_not_le)

text \<open>So nowhere-or-twice holds for all admissible propositions.\<close>

lemma nowhere_or_twice_admissible: \<open>(my_model, x) \<Turnstile> \<^bold>\<forall> (nowhere_or_twice (\<^bold>\<cdot>(\<^bold>#0)))\<close>
  unfolding my_model_def my_gframe_def unfolds Pss_def
  using fin_arith_nowhere_or_twice by simp

text \<open>However, propositional quantification lets us form a singleton.\<close>

abbreviation \<open>singleton x \<equiv> \<^bold>\<forall>( \<^bold>@(\<^bold>\<circle>x) (\<^bold>\<cdot>(\<^bold>#0)) \<^bold>\<longrightarrow> \<^bold>\<cdot>(\<^bold>#0) )\<close>

lemma singleton: \<open>((my_model, x) \<Turnstile> singleton y) \<longleftrightarrow> x = y\<close>
  unfolding my_model_def my_gframe_def unfolds Pss_def
  using fin_arith_Inter_singleton by auto

lemma fin_arith_distinguish':
  \<open>\<forall>P. fin_arith P \<longrightarrow> y \<in> P \<longrightarrow> v \<in> P \<Longrightarrow> v \<noteq> w \<Longrightarrow> \<exists>P. y \<in> P \<and> fin_arith P \<and> w \<notin> P\<close>
  by (metis disjoint_iff fin_arith_distinguish)

text \<open>The singleton does not hold nowhere-or-twice.\<close>

lemma not_nowhere_or_twice_singleton: \<open>\<not> (my_model, x) \<Turnstile> nowhere_or_twice (singleton y)\<close>
  unfolding my_model_def my_gframe_def unfolds Pss_def
  using fin_arith_distinguish' by auto

text \<open>So we cannot always eliminate a quantifier with a non-quantifier-free formula.\<close>
  
theorem counter:
  shows \<open>\<not> (my_model, x) \<Turnstile> \<^bold>\<forall> (nowhere_or_twice (\<^bold>\<cdot>(\<^bold>#0))) \<^bold>\<longrightarrow> nowhere_or_twice (singleton y)\<close>
  using nowhere_or_twice_admissible not_nowhere_or_twice_singleton
  by (meson semantics.simps(3,4))


end
