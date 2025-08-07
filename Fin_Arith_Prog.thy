theory Fin_Arith_Prog imports
  "HOL-Number_Theory.Number_Theory"
begin

(* I already use this for my logic. *)
no_syntax
  "_Pi" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set"
    (\<open>(\<open>indent=3 notation=\<open>binder \<Pi>\<in>\<close>\<close>\<Pi> _\<in>_./ _)\<close> 10)

section \<open>From Manuel Eberl's Furstenberg_Topology AFP entry\<close>

definition arith_prog :: "int \<Rightarrow> nat \<Rightarrow> int set" where
  "arith_prog a b = {x. [x = a] (mod int b)}"

lemma arith_prog_0_right [simp]: "arith_prog a 0 = {a}"
  by (simp add: arith_prog_def)

lemma arith_prog_Suc_0_right [simp]: "arith_prog a (Suc 0) = UNIV"
  by (auto simp: arith_prog_def)

lemma in_arith_progI [intro]: "[x = a] (mod b) \<Longrightarrow> x \<in> arith_prog a b"
  by (auto simp: arith_prog_def)

lemma arith_prog_disjoint:
  assumes "[a \<noteq> a'] (mod int b)" and "b > 0"
  shows   "arith_prog a b \<inter> arith_prog a' b = {}"
  using assms by (auto simp: arith_prog_def cong_def)

lemma arith_prog_dvd_mono: "b dvd b' \<Longrightarrow> arith_prog a b' \<subseteq> arith_prog a b"
  by (auto simp: arith_prog_def cong_dvd_modulus)

lemma bij_betw_arith_prog:
  assumes "b > 0"
  shows   "bij_betw (\<lambda>n. a + int b * n) UNIV (arith_prog a b)"
proof (rule bij_betwI[of _ _ _ "\<lambda>x. (x - a) div int b"], goal_cases)
  case 1
  thus ?case 
    by (auto simp: arith_prog_def cong_add_lcancel_0 cong_mult_self_right mult_of_nat_commute)
next
  case 4
  thus ?case
    by (auto simp: arith_prog_def cong_iff_lin)
qed (use \<open>b > 0\<close> in \<open>auto simp: arith_prog_def\<close>)

lemma arith_prog_altdef: "arith_prog a b = range (\<lambda>n. a + int b * n)"
proof (cases "b = 0")
  case False
  thus ?thesis
    using bij_betw_arith_prog[of b] by (auto simp: bij_betw_def)
qed auto

lemma infinite_arith_prog: "b > 0 \<Longrightarrow> infinite (arith_prog a b)"
  using bij_betw_finite[OF bij_betw_arith_prog[of b]] by simp

(* from the lemma closed_arith_prog_fb *)
lemma arith_prog_complement:
  assumes \<open>b > 0\<close>
  shows "-arith_prog a b = (\<Union>i\<in>{1..<b}. arith_prog (a + int i) b)"
proof -
  have disjoint: "x \<notin> arith_prog a b" if "x \<in> arith_prog (a + int i) b" "i \<in> {1..<b}" for x i
  proof -
    have "[a \<noteq> a + int i] (mod int b)"
    proof
      assume "[a = a + int i] (mod int b)"
      hence "[a + 0 = a + int i] (mod int b)" by simp
      hence "[0 = int i] (mod int b)" by (subst (asm) cong_add_lcancel) auto
      with that show False by (auto simp: cong_def)
    qed
    thus ?thesis using arith_prog_disjoint[of a "a + int i" b] \<open>b > 0\<close> that by auto
  qed

  have covering: "x \<in> arith_prog a b \<or> x \<in> (\<Union>i\<in>{1..<b}. arith_prog (a + int i) b)" for x
  proof -
    define i where "i = nat ((x - a) mod (int b))"
    have "[a + int i = a + (x - a) mod int b] (mod int b)"
      unfolding i_def using \<open>b > 0\<close> by simp
    also have "[a + (x - a) mod int b = a + (x - a)] (mod int b)"
      by (intro cong_add) auto
    finally have "[x = a + int i] (mod int b)"
      by (simp add: cong_sym_eq)
    hence "x \<in> arith_prog (a + int i) b"
      using \<open>b > 0\<close> by (auto simp: arith_prog_def)
    moreover have "i < b" using \<open>b > 0\<close> 
      by (auto simp: i_def nat_less_iff)
    ultimately show ?thesis using \<open>b > 0\<close>
      by (cases "i = 0") auto
  qed

  from disjoint and covering show ?thesis
    by blast
qed

(* from instance t2_space *)
lemma arith_prog_distinguish:
  assumes "x \<noteq> y"
  shows "\<exists>a c b. b > 0 \<and> x \<in> arith_prog a b \<and> y \<in> arith_prog c b \<and> arith_prog a b \<inter> arith_prog c b = {}"
proof -
  define d where "d = nat \<bar>x - y\<bar> + 1"
  from \<open>x \<noteq> y\<close> have "d > 0"
    unfolding d_def by auto
  define U where "U = arith_prog x d"
  define V where "V = arith_prog y d"

  have "U \<inter> V = {}" unfolding U_def V_def d_def
  proof (use \<open>x \<noteq> y\<close> in transfer, rule arith_prog_disjoint)
    fix x y :: int
    assume "x \<noteq> y"
    show "[x \<noteq> y] (mod int (nat \<bar>x - y\<bar> + 1))"
    proof
      assume "[x = y] (mod int (nat \<bar>x - y\<bar> + 1))"
      hence "\<bar>x - y\<bar> + 1 dvd \<bar>x - y\<bar>"
        by (auto simp: cong_iff_dvd_diff algebra_simps)
      hence "\<bar>x - y\<bar> + 1 \<le> \<bar>x - y\<bar>"
        by (rule zdvd_imp_le) (use \<open>x \<noteq> y\<close> in auto)
      thus False by simp
    qed
  qed auto
  moreover have "x \<in> U" "y \<in> V"
    unfolding U_def V_def by (use \<open>d > 0\<close> in transfer, fastforce)+
  ultimately show ?thesis
    using U_def V_def \<open>0 < d\<close> by blast
qed

section \<open>Unions of Arithmetic Progressions\<close>

lemma arith_prog_offset_in: \<open>k \<in> arith_prog a b \<Longrightarrow> arith_prog k b = arith_prog a b\<close>
  unfolding arith_prog_def by (simp add: cong_def)

lemma arith_prog_mod: \<open>arith_prog (a mod int b) b = arith_prog a b\<close>
  unfolding arith_prog_def by auto                   

lemma mod_bounds: \<open>b > 0 \<Longrightarrow> a mod int b \<ge> 0 \<and> a mod int b < b\<close>
  by simp

lemma mod_range: \<open>{a mod int b |a. b > 0} \<subseteq> {0..<int b}\<close>
  using mod_bounds by auto

lemma finite_mod_range: \<open>finite {a mod int b |a. b > 0}\<close>
  using mod_range by (meson finite_atLeastLessThan_int finite_subset)

definition arith :: \<open>nat set \<Rightarrow> int set \<Rightarrow> bool\<close> where
  \<open>arith B U \<equiv> \<forall>a \<in> U. \<exists>b \<in> B. b > 0 \<and> arith_prog a b \<subseteq> U\<close>

lemma arith_mono: \<open>arith B U \<Longrightarrow> B \<subseteq> C \<Longrightarrow> arith C U\<close>
  unfolding arith_def by blast

lemma arith_empty_steps: \<open>arith B U \<Longrightarrow> B = {} \<Longrightarrow> U = {}\<close>
  unfolding arith_def by blast

lemma arith_ne_steps: \<open>arith B U \<Longrightarrow> U \<noteq> {} \<Longrightarrow> B \<noteq> {}\<close>
  using arith_empty_steps by blast

lemma arith_decomp:
  assumes \<open>arith B U\<close>
  obtains abs where
    \<open>finite B \<Longrightarrow> finite abs\<close>
    \<open>\<And>a b. (a, b) \<in> abs \<Longrightarrow> b > 0 \<and> b \<in> B\<close>
    \<open>U = (\<Union>(a, b) \<in> abs. arith_prog a b)\<close>
proof -
  have \<open>\<forall>a\<in>U. \<exists>b \<in> B. b > 0 \<and> arith_prog (a mod int b) b \<subseteq> U\<close>
    using \<open>arith B U\<close> unfolding arith_def using arith_prog_mod by simp
  then obtain f where f: \<open>\<forall>a \<in> U. \<exists>b \<in> B. f a = b \<and> b > 0 \<and> arith_prog (a mod int b) b \<subseteq> U\<close>
    by metis

  let ?abs = \<open>{(a mod int (f a), f a) |a. a \<in> U}\<close>

  have abs: \<open>U = (\<Union>(a, b) \<in> ?abs. arith_prog a b)\<close>
    using f by fastforce

  have \<open>{a mod int (f a) |a. a \<in> U} \<subseteq> (\<Union>b \<in> B. {a mod int b |a. b > 0})\<close>
    using f by blast
  moreover have \<open>finite (\<Union>b \<in> B. {a mod int b |a. b > 0})\<close> if \<open>finite B\<close>
    using that finite_mod_range by fast
  ultimately have \<open>finite {a mod int (f a) |a. a \<in> U}\<close> if \<open>finite B\<close>
    using that by (meson finite_subset)

  moreover have \<open>?abs \<subseteq> {a mod int (f a) |a. a \<in> U} \<times> f ` U\<close>
    by blast
  moreover have fin_f: \<open>finite (f ` U)\<close> if \<open>finite B\<close>
    using that f by (meson finite_subset image_subsetI)
  ultimately have fin_abs: \<open>finite ?abs\<close> if \<open>finite B\<close>
    using that fin_f by (meson finite_SigmaI finite_subset)

  have pos: \<open>\<And>a b. (a, b) \<in> ?abs \<Longrightarrow> b > 0 \<and> b \<in> B\<close>
    using f by blast

  show ?thesis
    using fin_abs pos abs that by meson
qed

lemma arith_UNIV: \<open>arith {1} UNIV\<close>
  unfolding arith_def by blast

lemma arith_empty: "arith B {}"
  unfolding arith_def by blast

lemma finite_case_prod_lcm: \<open>finite B \<Longrightarrow> finite C \<Longrightarrow> finite (case_prod lcm ` (B \<times> C))\<close>
  by blast

lemma arith_inter:
  assumes U: \<open>arith B U\<close> and V: \<open>arith C V\<close>
  shows \<open>arith (case_prod lcm ` (B \<times> C)) (U \<inter> V)\<close>
  unfolding arith_def
proof safe
  fix a
  assume a: \<open>a \<in> U\<close> \<open>a \<in> V\<close>
  
  from a U obtain b where b: \<open>b \<in> B\<close> \<open>b > 0\<close> \<open>arith_prog a b \<subseteq> U\<close>
    unfolding arith_def by auto
  from a V obtain c where c: \<open>c \<in> C\<close> \<open>c > 0\<close> \<open>arith_prog a c \<subseteq> V\<close>
    unfolding arith_def by auto

  with a b c U V have \<open>arith_prog a (lcm b c) \<subseteq> U \<inter> V\<close>
    using arith_prog_dvd_mono[of b \<open>lcm b c\<close> a] arith_prog_dvd_mono[of c \<open>lcm b c\<close> a] by blast
  moreover from b c have \<open>lcm b c > 0\<close>
    using lcm_pos_nat by blast
  ultimately show \<open>\<exists>b\<in>(\<lambda>(x, y). lcm x y) ` (B \<times> C). 0 < b \<and> arith_prog a b \<subseteq> U \<inter> V\<close>
    using b c by blast
qed

lemma arith_Inter:
  assumes \<open>finite X\<close> and X: \<open>\<forall>U \<in> X. arith B U\<close> \<open>X \<noteq> {}\<close>
  shows \<open>\<exists>B'. (finite B \<longrightarrow> finite B') \<and> arith B' (\<Inter>X)\<close>
  using assms
proof (induct X rule: finite_induct)
  case empty
  then show ?case
    by simp
next
  case (insert U X)
  then show ?case
    using arith_inter finite_case_prod_lcm
    by (metis Inf_insert cInf_singleton insertCI)
qed

lemma arith_union:
  assumes \<open>arith B U\<close> \<open>arith C V\<close>
  shows \<open>arith (B \<union> C) (U \<union> V)\<close>
  using assms unfolding arith_def by (metis Un_iff subset_trans sup_ge1 sup_ge2)

lemma arith_ne_infinite:
  assumes \<open>arith B U\<close> \<open>U \<noteq> {}\<close>
  shows \<open>infinite U\<close>
  using assms unfolding arith_def
  by (meson equals0I infinite_arith_prog rev_finite_subset)

lemma arith_prog_arith [intro]:
  assumes \<open>b > 0\<close>
  shows \<open>arith {b} (arith_prog a b)\<close>
  unfolding arith_def using assms arith_prog_offset_in by blast

lemma arith_prog_complement_arith [intro]:
  assumes \<open>b > 0\<close>
  shows \<open>arith {b} (- arith_prog a b)\<close>
proof -
  have "-arith_prog a b = (\<Union>i\<in>{1..<b}. arith_prog (a + int i) b)"
    using assms arith_prog_complement by blast
  also from assms have "arith {b} \<dots>"
    unfolding arith_def using arith_prog_offset_in by blast
  finally show ?thesis .
qed

lemma arith_complement_arith [intro]:
  assumes \<open>arith B U\<close> \<open>finite B\<close>
  shows \<open>\<exists>B'. finite B' \<and> arith B' (- U)\<close>
proof -
  obtain abs where
    abs: \<open>\<And>a b. (a, b) \<in> abs \<Longrightarrow> b > 0 \<and> b \<in> B\<close> \<open>finite abs\<close> and
    U: \<open>U = (\<Union>(a, b) \<in> abs. arith_prog a b)\<close>
    using assms arith_decomp by metis
  then have *: \<open>\<And>a b. (a, b) \<in> abs \<Longrightarrow> - arith_prog a b = (\<Union>i\<in>{1..<b}. arith_prog (a + int i) b)\<close>
    using arith_prog_complement by simp

  have \<open>- U = (\<Inter>(a, b) \<in> abs. - arith_prog a b)\<close>
    using U by blast
  also have \<open>\<dots> = (\<Inter>(a, b) \<in> abs. (\<Union>i\<in>{1..<b}. arith_prog (a + int i) b))\<close>
    using * by blast
  finally have **: \<open>- U = (\<Inter>(a, b) \<in> abs. (\<Union>i\<in>{1..<b}. arith_prog (a + int i) b))\<close> .

  have \<open>\<And>a b. (a, b) \<in> abs \<Longrightarrow> arith {b} (\<Union>i\<in>{1..<b}. arith_prog (a + int i) b)\<close>
    using abs * by (metis arith_prog_complement_arith)
  then have ***: \<open>\<And>a b. (a, b) \<in> abs \<Longrightarrow> arith B (\<Union>i\<in>{1..<b}. arith_prog (a + int i) b)\<close>
    using arith_mono abs by fast

  define X where X: \<open>X \<equiv> (\<lambda>(a, b). \<Union>i\<in>{1..<b}. arith_prog (a + int i) b) ` abs\<close>

  from X have \<open>finite X\<close>
    using abs(2) by simp
  moreover have \<open>\<forall>U\<in>X. arith B U\<close>
    using X *** by fast
  ultimately have \<open>\<exists>B'. finite B' \<and> arith B' (\<Inter> X)\<close>
    using arith_Inter[of X] \<open>finite B\<close> arith_UNIV by fastforce

  moreover from X have \<open>- U = \<Inter>X\<close>
    using ** by simp
  ultimately show ?thesis
    by simp
qed

lemma arith_distinguish:
  assumes \<open>x \<noteq> y\<close>
  shows \<open>\<exists>B U V. finite B \<and> arith B U \<and> arith B V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}\<close>
proof -
  obtain a b c where
    b: \<open>0 < b\<close> and x: \<open>x \<in> arith_prog a b\<close> and y: \<open>y \<in> arith_prog c b\<close> and
    *: \<open>arith_prog a b \<inter> arith_prog c b = {}\<close>
    using assms arith_prog_distinguish by meson

  let ?B = \<open>{b}\<close>
  let ?U = \<open>arith_prog a b\<close>
  let ?V = \<open>arith_prog c b\<close>
  have \<open>finite ?B \<and> arith ?B ?U \<and> arith ?B ?V \<and> x \<in> ?U \<and> y \<in> ?V \<and> ?U \<inter> ?V = {}\<close>
    using b x y *
    by blast
  then show ?thesis
    by blast
qed

section \<open>Finite Unions of Arithmetic Progressions\<close>

definition fin_arith :: \<open>int set \<Rightarrow> bool\<close> where
  \<open>fin_arith U \<equiv> \<exists>B. finite B \<and> arith B U\<close>

lemma fin_arith_UNIV [intro]: \<open>fin_arith UNIV\<close>
  unfolding fin_arith_def using arith_UNIV by force

lemma fin_arith_empty [intro]: \<open>fin_arith {}\<close>
  unfolding fin_arith_def using arith_empty by blast

lemma fin_arith_inter [intro]: \<open>fin_arith U \<Longrightarrow> fin_arith V \<Longrightarrow> fin_arith (U \<inter> V)\<close>
  unfolding fin_arith_def using arith_inter finite_case_prod_lcm by metis

lemma fin_arith_union [intro]: \<open>fin_arith U \<Longrightarrow> fin_arith V \<Longrightarrow> fin_arith (U \<union> V)\<close>
  unfolding fin_arith_def using arith_union by blast

lemma fin_arith_compl [intro]: \<open>fin_arith U \<Longrightarrow> fin_arith (- U)\<close>
  unfolding fin_arith_def by blast

lemma fin_arith_distinguish:
  assumes \<open>x \<noteq> y\<close>
  shows \<open>\<exists>U V. fin_arith U \<and> fin_arith V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}\<close>
  using assms arith_distinguish unfolding fin_arith_def by meson

subsection \<open>Singletons\<close>

lemma arith_prog_singleton: \<open>\<Inter>{arith_prog a b |a b. b > 0 \<and> x \<in> arith_prog a b} = {x}\<close>
proof
  show \<open>\<Inter> {arith_prog a b |a b. 0 < b \<and> x \<in> arith_prog a b} \<subseteq> {x}\<close>
    using arith_prog_distinguish by fast
qed fast

lemma fin_arith_Inter_singleton: \<open>\<Inter>{U |U. fin_arith U \<and> x \<in> U} = {x}\<close>
proof -
  have \<open>{arith_prog a b |a b. b > 0 \<and> x \<in> arith_prog a b} \<subseteq> {U |U b. arith {b} U \<and> x \<in> U}\<close>
    using arith_prog_arith by blast
  also have \<open>\<dots> \<subseteq> {U |U B. finite B \<and> arith B U \<and> x \<in> U}\<close>
    by force
  finally have \<open>{arith_prog a b |a b. b > 0 \<and> x \<in> arith_prog a b} \<subseteq> {U |U. fin_arith U \<and> x \<in> U}\<close>
    unfolding fin_arith_def by auto
  then have \<open>\<Inter>{U |U. fin_arith U \<and> x \<in> U} \<subseteq> \<Inter>{arith_prog a b |a b. b > 0 \<and> x \<in> arith_prog a b}\<close>
    by blast
  then show ?thesis
    using arith_prog_singleton by auto
qed

lemma singleton_not_finarith: \<open>\<not> fin_arith {x}\<close>
  unfolding fin_arith_def using arith_ne_infinite by blast

end
