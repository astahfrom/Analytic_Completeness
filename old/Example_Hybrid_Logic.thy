(*
  Title:  Example Completeness Proof for a Natural Deduction Calculus for Basic Hybrid Logic
  Author: Asta Halkjær From
*)

theory Example_Hybrid_Logic imports Analytic_Completeness begin

section \<open>Syntax\<close>

datatype (nominals_tm: 'i) tm
  = Var nat (\<open>\<^bold>#\<close>)
  | Nom 'i (\<open>\<^bold>\<circle>\<close>)

datatype (nominals_fm: 'i, 'p) fm
  = Ter \<open>'i tm\<close> (\<open>\<^bold>\<bullet>\<close>)
  | Fls (\<open>\<^bold>\<bottom>\<close>)
  | Pro 'p (\<open>\<^bold>\<cdot>\<close>)
  | Imp \<open>('i, 'p) fm\<close> \<open>('i, 'p) fm\<close> (infixr \<open>\<^bold>\<longrightarrow>\<close> 55)
  | Dia \<open>('i, 'p) fm\<close> (\<open>\<^bold>\<diamond>\<close>)
  | Sat \<open>'i tm\<close> \<open>('i, 'p) fm\<close> (\<open>\<^bold>@\<close>)
  | All \<open>('i, 'p) fm\<close> (\<open>\<^bold>A\<close>)
  | Dwn \<open>('i, 'p) fm\<close> (\<open>\<^bold>\<down>\<close>)

abbreviation Neg (\<open>\<^bold>\<not> _\<close> [70] 70) where \<open>\<^bold>\<not> p \<equiv> p \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>

type_synonym ('i, 'p) lbd = \<open>'i tm \<times> ('i, 'p) fm\<close>

section \<open>Semantics\<close>

datatype ('w, 'p) model = Model (W: \<open>'w set\<close>) (R: \<open>'w \<Rightarrow> 'w set\<close>) (V: \<open>'w \<Rightarrow> 'p \<Rightarrow> bool\<close>)

type_synonym ('i, 'p, 'w) ctx = \<open>('w, 'p) model \<times> ('i \<Rightarrow> 'w) \<times> (nat \<Rightarrow> 'w) \<times> 'w\<close>

primrec add_env :: \<open>'a \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a\<close> (infix \<open>\<Zsemi>\<close> 0) where
  \<open>(t \<Zsemi> e) 0 = t\<close>
| \<open>(_ \<Zsemi> e) (Suc n) = e n\<close>

fun semantics_tm :: \<open>('i \<Rightarrow> 'w) \<times> (nat \<Rightarrow> 'w) \<Rightarrow> 'i tm \<Rightarrow> 'w\<close> (\<open>\<lparr>_\<rparr>\<close>) where
  \<open>\<lparr>(_, e)\<rparr> (\<^bold># n) = e n\<close>
| \<open>\<lparr>(g, _)\<rparr> (\<^bold>\<circle> i) = g i\<close>

fun semantics :: \<open>('i, 'p, 'w) ctx \<Rightarrow> ('i, 'p) fm \<Rightarrow> bool\<close> (\<open>_ \<Turnstile>\<^sub>@ _\<close> [50, 50] 50) where
  \<open>(M, g, e, w) \<Turnstile>\<^sub>@ \<^bold>\<bullet>t \<longleftrightarrow> \<lparr>(g, e)\<rparr> t = w\<close>
| \<open>(M, g, _, w) \<Turnstile>\<^sub>@ \<^bold>\<bottom> \<longleftrightarrow> False\<close>
| \<open>(M, _, _, w) \<Turnstile>\<^sub>@ \<^bold>\<cdot>P \<longleftrightarrow> V M w P\<close>
| \<open>(M, g, e, w) \<Turnstile>\<^sub>@ (p \<^bold>\<longrightarrow> q) \<longleftrightarrow> (M, g, e, w) \<Turnstile>\<^sub>@ p \<longrightarrow> (M, g, e, w) \<Turnstile>\<^sub>@ q\<close>
| \<open>(M, g, e, w) \<Turnstile>\<^sub>@ \<^bold>\<diamond> p \<longleftrightarrow> (\<exists>v \<in> W M \<inter> R M w. (M, g, e, v) \<Turnstile>\<^sub>@ p)\<close>
| \<open>(M, g, e, _) \<Turnstile>\<^sub>@ \<^bold>@i p \<longleftrightarrow> (M, g, e, \<lparr>(g, e)\<rparr> i) \<Turnstile>\<^sub>@ p\<close>
| \<open>(M, g, e, _) \<Turnstile>\<^sub>@ \<^bold>A p \<longleftrightarrow> (\<forall>v \<in> W M. (M, g, e, v) \<Turnstile>\<^sub>@ p)\<close>
| \<open>(M, g, e, w) \<Turnstile>\<^sub>@ \<^bold>\<down> p \<longleftrightarrow> (M, g, w \<Zsemi> e, w) \<Turnstile>\<^sub>@ p\<close>

section \<open>Operations\<close>

abbreviation psub :: \<open>('i \<Rightarrow> 'k) \<Rightarrow> ('i, 'p) fm \<Rightarrow> ('k, 'p) fm\<close> where
  \<open>psub f \<equiv> map_fm f id\<close>

abbreviation psub_lbd :: \<open>('i \<Rightarrow> 'k) \<Rightarrow> ('i, 'p) lbd \<Rightarrow> ('k, 'p) lbd\<close> where
  \<open>psub_lbd f \<equiv> map_prod (map_tm f) (psub f)\<close>

primrec nominals_lbd :: \<open>('i, 'p) lbd \<Rightarrow> 'i set\<close> where
  \<open>nominals_lbd (i, p) = nominals_tm i \<union> nominals_fm p\<close>

abbreviation nominals :: \<open>('i, 'p) lbd set \<Rightarrow> 'i set\<close> where
  \<open>nominals S \<equiv> \<Union>ip \<in> S. nominals_lbd ip\<close>

primrec lift_tm :: \<open>'i tm \<Rightarrow> 'i tm\<close> where
  \<open>lift_tm (\<^bold>#n) = \<^bold>#(n+1)\<close>
| \<open>lift_tm (\<^bold>\<circle>k) = \<^bold>\<circle>k\<close>

primrec sub_tm :: \<open>(nat \<Rightarrow> 'i tm) \<Rightarrow> 'i tm \<Rightarrow> 'i tm\<close> where
  \<open>sub_tm s (\<^bold>#n) = s n\<close>
| \<open>sub_tm _ (\<^bold>\<circle>k) = \<^bold>\<circle>k\<close>

primrec sub_fm :: \<open>(nat \<Rightarrow> 'i tm) \<Rightarrow> ('i, 'p) fm \<Rightarrow> ('i, 'p) fm\<close> where
  \<open>sub_fm s (\<^bold>\<bullet>t) = \<^bold>\<bullet>(sub_tm s t)\<close>
| \<open>sub_fm _ \<^bold>\<bottom> = \<^bold>\<bottom>\<close>
| \<open>sub_fm _ (\<^bold>\<cdot>P) = \<^bold>\<cdot>P\<close>
| \<open>sub_fm s (p \<^bold>\<longrightarrow> q) = sub_fm s p \<^bold>\<longrightarrow> sub_fm s q\<close>
| \<open>sub_fm s (\<^bold>\<diamond> p) = \<^bold>\<diamond>(sub_fm s p)\<close>
| \<open>sub_fm s (\<^bold>@i p) = \<^bold>@(sub_tm s i) (sub_fm s p)\<close>
| \<open>sub_fm s (\<^bold>A p) = \<^bold>A (sub_fm s p)\<close>
| \<open>sub_fm s (\<^bold>\<down> p) = \<^bold>\<down> (sub_fm (\<^bold>#0 \<Zsemi> \<lambda>n. lift_tm (s n)) p)\<close>

abbreviation inst_single :: \<open>'i tm \<Rightarrow> ('i, 'p) fm \<Rightarrow> ('i, 'p) fm\<close> (\<open>\<langle>_\<rangle>\<close>) where
  \<open>\<langle>t\<rangle> \<equiv> sub_fm (t \<Zsemi> \<^bold>#)\<close>

primrec size_fm :: \<open>('i, 'p) fm \<Rightarrow> nat\<close> where
  \<open>size_fm (\<^bold>\<bullet>t) = 1\<close>
| \<open>size_fm \<^bold>\<bottom> = 1\<close>
| \<open>size_fm (\<^bold>\<cdot>P) = 1\<close>
| \<open>size_fm (p \<^bold>\<longrightarrow> q) = size_fm p + size_fm q + 1\<close>
| \<open>size_fm (\<^bold>\<diamond> p) = size_fm p + 1\<close>
| \<open>size_fm (\<^bold>@i p) = size_fm p + 1\<close>
| \<open>size_fm (\<^bold>A p) = size_fm p + 1\<close>
| \<open>size_fm (\<^bold>\<down> p) = size_fm p + 1\<close>

subsection \<open>Lemmas\<close>

lemma finite_nominals_tm [simp]: \<open>finite (nominals_tm t)\<close>
  by (induct t) simp_all

lemma finite_nominals_fm [simp]: \<open>finite (nominals_fm p)\<close>
  by (induct p) simp_all

lemma finite_nominals_lbd: \<open>finite (nominals_lbd p)\<close>
  by (cases p) simp

lemma size_sub_fm [simp]: \<open>size_fm (sub_fm s p) = size_fm p\<close>
  by (induct p arbitrary: s) simp_all

lemma semantics_tm_fresh [simp]: \<open>i \<notin> nominals_tm t \<Longrightarrow> \<lparr>(g(i := v), e)\<rparr> t = \<lparr>(g, e)\<rparr> t\<close>
  by (induct t) auto

lemma semantics_fresh: \<open>i \<notin> nominals_fm p \<Longrightarrow> (M, g, e, w) \<Turnstile>\<^sub>@ p \<longleftrightarrow> (M, g(i := v), e, w) \<Turnstile>\<^sub>@ p\<close>
proof (induct p arbitrary: e w)
  case (Ter t)
  then show ?case
    by (metis fm.set_intros(1) semantics.simps(1) semantics_tm_fresh)
qed auto

lemma semantics_fresh_lbd: \<open>k \<notin> nominals_lbd (i, p) \<Longrightarrow> (M, g, e, w) \<Turnstile>\<^sub>@ p \<longleftrightarrow> (M, g(k := v), e, w) \<Turnstile>\<^sub>@ p\<close>
  by (induct p arbitrary: e w) auto

lemma env [simp]: \<open>P ((x \<Zsemi> E) n) = (P x \<Zsemi> \<lambda>n. P (E n)) n\<close>
  by (induct n) simp_all

lemma lift_lemma: \<open>\<lparr>(g, x \<Zsemi> e)\<rparr> (lift_tm t) = \<lparr>(g, e)\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma sub_tm_semantics: \<open>\<lparr>(g, e)\<rparr> (sub_tm s t) = \<lparr>(g, \<lambda>n. \<lparr>(g, e)\<rparr> (s n))\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma sub_fm_semantics [simp]: \<open>(M, g, e, w) \<Turnstile>\<^sub>@ sub_fm s p \<longleftrightarrow> (M, g, \<lambda>n. \<lparr>(g, e)\<rparr> (s n), w) \<Turnstile>\<^sub>@ p\<close>
  by (induct p arbitrary: e s w) (auto cong: map_cong simp: sub_tm_semantics lift_lemma)

lemma semantics_tm_id [simp]: \<open>\<lparr>(\<^bold>\<circle>, \<^bold>#)\<rparr> t = t\<close>
  by (induct t) (auto cong: map_cong)

lemma semantics_tm_id_map [simp]: \<open>map \<lparr>(\<^bold>\<circle>, \<^bold>#)\<rparr> ts = ts\<close>
  by (auto cong: map_cong)

lemma map_tm_sub_tm [simp]: \<open>map_tm f (sub_tm g t) = sub_tm (map_tm f o g) (map_tm f t)\<close>
  by (induct t) simp_all

lemma map_tm_lift_tm [simp]: \<open>map_tm f (lift_tm t) = lift_tm (map_tm f t)\<close>
  by (induct t) simp_all

lemma psub_sub_fm: \<open>psub f (sub_fm g p) = sub_fm (map_tm f o g) (psub f p)\<close>
  by (induct p arbitrary: g) (simp_all add: comp_def)

lemma map_tm_inst_single: \<open>(map_tm f o (u \<Zsemi> \<^bold>#)) t = (map_tm f u \<Zsemi> \<^bold>#) t\<close>
  by (induct t) auto

lemma psub_inst_single [simp]: \<open>psub f (\<langle>t\<rangle>p) = \<langle>map_tm f t\<rangle>(psub f p)\<close>
  unfolding psub_sub_fm map_tm_inst_single ..

section \<open>Model Existence\<close>

inductive classify :: \<open>('i, 'p) lbd list \<Rightarrow> (_, _, 'i tm \<Rightarrow> _, 'i \<Rightarrow> _) sort \<Rightarrow> bool\<close>
  (\<open>_ \<leadsto> _\<close> [50, 50] 50) where
  \<open>[] \<leadsto> Confl [(i, \<^bold>\<bottom>)]\<close>
| \<open>[] \<leadsto> Gamma (\<lambda>_. UNIV) (\<lambda>i. [ (i, \<^bold>\<bullet>i) ])\<close>
| \<open>[ (i, p) ] \<leadsto> Confl [(i, \<^bold>\<not> p)]\<close>
| \<open>[ (i, \<^bold>\<bullet>k) ] \<leadsto> Alpha [(k, \<^bold>\<bullet>i)]\<close>
| \<open>[ (i, \<^bold>\<not> \<^bold>\<bullet>k) ] \<leadsto> Alpha [(k, \<^bold>\<not> \<^bold>\<bullet>i)]\<close>
| \<open>[ (i, \<^bold>\<bullet>k), (i, p) ] \<leadsto> Alpha [(k, p)]\<close>
| \<open>[ (i, p \<^bold>\<longrightarrow> q) ] \<leadsto> Beta [(i, \<^bold>\<not> p), (i, q)]\<close>
| \<open>[ (i, \<^bold>\<not> (p \<^bold>\<longrightarrow> q)) ] \<leadsto> Alpha [(i, p), (i, \<^bold>\<not> q)]\<close>
| \<open>[ (i, \<^bold>@k p) ] \<leadsto> Alpha [(k, p)]\<close>
| \<open>[ (i, \<^bold>\<not> \<^bold>@k p) ] \<leadsto> Alpha [(k, \<^bold>\<not> p)]\<close>
| \<open>[ (i, \<^bold>\<diamond>p) ] \<leadsto> Delta (\<lambda>k. [(\<^bold>\<circle>k, p), (i, \<^bold>\<diamond> (\<^bold>\<bullet> (\<^bold>\<circle>k)))])\<close>
| \<open>[ (i, \<^bold>\<not> \<^bold>\<diamond>p), (i, \<^bold>\<diamond> (\<^bold>\<bullet>k)) ] \<leadsto> Alpha [(k, \<^bold>\<not> p)]\<close>
| \<open>[ (i, \<^bold>A p) ] \<leadsto> Gamma (\<lambda>_. UNIV) (\<lambda>k. [ (k, p) ])\<close>
| \<open>[ (i, \<^bold>\<not> \<^bold>A p) ] \<leadsto> Delta (\<lambda>k. [ (\<^bold>\<circle>k, \<^bold>\<not> p) ])\<close>
| \<open>[ (i, \<^bold>\<down> p) ] \<leadsto> Alpha [ (i, \<langle>i\<rangle>p) ]\<close>
| \<open>[ (i, \<^bold>\<not> \<^bold>\<down> p) ] \<leadsto> Alpha [ (i, \<^bold>\<not> \<langle>i\<rangle>p) ]\<close>

declare classify.intros(3-)[intro]

interpretation Maximal_Consistency_UNIV nominals_lbd psub_lbd map_tm classify
proof
  show \<open>\<And>p. finite (nominals_lbd p)\<close>
    by auto
  show \<open>psub_lbd id = id\<close>
    by (simp add: fm.map_id0 prod.map_id0 tm.map_id0)
  show \<open>\<And>f g. \<forall>x\<in>nominals_lbd p. f x = g x \<Longrightarrow> psub_lbd f p = psub_lbd g p\<close> for p :: \<open>('i, 'p) lbd\<close>
    by (cases p) (simp cong: tm.map_cong0 fm.map_cong0)
  show \<open>\<And>f ps qs. ps \<leadsto> qs \<Longrightarrow> \<exists>rs. map (psub_lbd f) ps \<leadsto> rs \<and>
        rel_sort (\<lambda>qs. (=) (map (psub_lbd f) qs))
         (\<lambda>P Q. \<forall>S. map_tm f ` P S \<subseteq> Q (psub_lbd f ` S))
         (\<lambda>qs rs. \<forall>t. map (psub_lbd f) (qs t) = rs (map_tm f t))
         (\<lambda>qs rs. \<forall>x. map (psub_lbd f) (qs x) = rs (f x)) qs rs\<close>
    by (fastforce elim!: classify.cases intro: classify.intros(1-2))
  show \<open>\<And>ps P qs S S'. ps \<leadsto> Gamma P qs \<Longrightarrow> S \<subseteq> S' \<Longrightarrow> P S \<subseteq> P S'\<close>
    by (auto elim: classify.cases)
  show \<open>\<And>ps P qs t A. ps \<leadsto> Gamma P qs \<Longrightarrow> t \<in> P A \<Longrightarrow> \<exists>B\<subseteq>A. finite B \<and> t \<in> P B\<close>
    by (auto elim: classify.cases)
  show \<open>\<And>ps qs. ps \<leadsto> Delta qs \<Longrightarrow> \<exists>p. ps = [p]\<close>
    by (auto elim: classify.cases)
  show \<open>\<And>p ps qs. p \<leadsto> Delta ps \<Longrightarrow> p \<leadsto> Delta qs \<Longrightarrow> ps = qs\<close>
    by (auto elim: classify.cases)
  have \<open>infinite (UNIV :: ('i, 'p) fm set)\<close>
    using infinite_UNIV_size[of \<open>\<lambda>p. p \<^bold>\<longrightarrow> p\<close>] by simp
  then show \<open>infinite (UNIV :: ('i, 'p) lbd set)\<close>
    using finite_prod by blast
qed

definition equiv_nom :: \<open>('i, 'p) lbd set \<Rightarrow> 'i tm \<Rightarrow> 'i tm \<Rightarrow> bool\<close> where
  \<open>equiv_nom S i k \<equiv> (i, \<^bold>\<bullet>k) \<in> S\<close>

definition assign :: \<open>'i tm \<Rightarrow> ('i, 'p) lbd set \<Rightarrow> 'i tm\<close> (\<open>[_]\<^sub>_\<close> [0, 100] 100) where
  \<open>[i]\<^sub>S \<equiv> minim ( |UNIV| ) {k. equiv_nom S i k}\<close>

definition reach :: \<open>('i, 'p) lbd set \<Rightarrow> 'i tm \<Rightarrow> 'i tm set\<close> where
  \<open>reach S i \<equiv> {[k]\<^sub>S |k. (i, \<^bold>\<diamond> (\<^bold>\<bullet>k)) \<in> S}\<close>

definition canonical :: \<open>('i, 'p) lbd set \<Rightarrow> 'i tm \<Rightarrow> ('i tm, 'p) model\<close> where
  \<open>canonical S i \<equiv> Model {[k]\<^sub>S | k. True} (reach S) (\<lambda>i P. (i, \<^bold>\<cdot>P) \<in> S)\<close>

definition canonical_ctx :: \<open>('i, 'p) lbd set \<Rightarrow> 'i tm \<Rightarrow> ('i, 'p, 'i tm) ctx\<close> (\<open>\<lbrakk>_, _\<rbrakk>\<close>) where
  \<open>\<lbrakk>S, i\<rbrakk> \<equiv> (canonical S i, \<lambda>i. [\<^bold>\<circle>i]\<^sub>S, \<lambda>n. [\<^bold>#n]\<^sub>S, [i]\<^sub>S)\<close>

lemma canonical_tm_eta [simp]: \<open>\<lparr>(\<lambda>i. [\<^bold>\<circle> i]\<^sub>S, \<lambda>n. [\<^bold># n]\<^sub>S)\<rparr> k = [k]\<^sub>S\<close>
  by (cases k) simp_all

locale MyHintikka = Hintikka nominals_lbd psub_lbd map_tm classify S
  for S
begin

lemma Nom_refl: \<open>(i, \<^bold>\<bullet>i) \<in> S\<close>
  using gamma by (force intro: classify.intros(2))

lemma Nom_sym:
  assumes \<open>(i, \<^bold>\<bullet>k) \<in> S\<close>
  shows \<open>(k, \<^bold>\<bullet>i) \<in> S\<close>
  using assms alpha by force

lemma Nom_trans:
  assumes \<open>(i, \<^bold>\<bullet>j) \<in> S\<close> \<open>(j, \<^bold>\<bullet>k) \<in> S\<close>
  shows \<open>(i, \<^bold>\<bullet>k) \<in> S\<close>
  using assms 
proof -
  have \<open>(j, \<^bold>\<bullet>i) \<in> S\<close>
    using assms Nom_sym by blast
  then show ?thesis
    using assms(2) alpha by force
qed

lemma equiv_nom_ne: \<open>{k. equiv_nom S i k} \<noteq> {}\<close>
  unfolding equiv_nom_def using Nom_refl by blast

lemma equiv_nom_assign: \<open>equiv_nom S i ([i]\<^sub>S)\<close>
  unfolding assign_def using equiv_nom_ne 
  by (metis Field_card_of card_of_well_order_on mem_Collect_eq top.extremum wo_rel_def wo_rel.minim_in)

lemma equiv_nom_Nom:
  assumes \<open>equiv_nom S i k\<close> \<open>(i, p) \<in> S\<close>
  shows \<open>(k, p) \<in> S\<close>
proof -
  have \<open>(i, \<^bold>\<bullet>k) \<in> S\<close>
    using assms unfolding equiv_nom_def by blast
  then show ?thesis
    using assms alpha by force
qed

theorem model: \<open>((i, p) \<in> S \<longrightarrow> \<lbrakk>S, i\<rbrakk> \<Turnstile>\<^sub>@ p) \<and> ((i, \<^bold>\<not> p) \<in> S \<longrightarrow> \<not> \<lbrakk>S, i\<rbrakk> \<Turnstile>\<^sub>@ p)\<close>
proof (induct p arbitrary: i rule: wf_induct[where r=\<open>measure size_fm\<close>])
  case 1
  then show ?case
    by simp
next
  case (2 x)
  then show ?case
  proof (cases x)
    case Fls
    then show ?thesis
      unfolding canonical_ctx_def using confl by (force intro: classify.intros(1))
  next
    case (Pro P)
    then show ?thesis
    proof (safe del: notI)
      assume \<open>x = \<^bold>\<cdot>P\<close> \<open>(i, \<^bold>\<cdot>P) \<in> S\<close>
      then have \<open>([i]\<^sub>S, \<^bold>\<cdot>P) \<in> S\<close>
        using equiv_nom_Nom equiv_nom_assign by fastforce
      then show \<open>\<lbrakk>S, i\<rbrakk> \<Turnstile>\<^sub>@ \<^bold>\<cdot>P\<close>
        unfolding canonical_ctx_def canonical_def by simp
    next
      assume \<open>x = \<^bold>\<cdot>P\<close> \<open>(i, \<^bold>\<not> \<^bold>\<cdot>P) \<in> S\<close>
      then have \<open>([i]\<^sub>S, \<^bold>\<cdot>P) \<notin> S\<close>
        using confl equiv_nom_Nom equiv_nom_assign
        by (metis classify.intros(3) empty_iff empty_set insert_subset list.simps(15) subsetI)
      then show \<open>\<not> \<lbrakk>S, i\<rbrakk> \<Turnstile>\<^sub>@ \<^bold>\<cdot>P\<close>
        unfolding canonical_ctx_def canonical_def by simp
    qed
  next
    case (Ter k)
    then show ?thesis
      proof (safe del: notI)
        assume \<open>x = \<^bold>\<bullet>k\<close> \<open>(i, \<^bold>\<bullet>k) \<in> S\<close>
        moreover from this have \<open>(k, \<^bold>\<bullet>i) \<in> S\<close>
          using Nom_sym by fast
        ultimately have \<open>[i]\<^sub>S = [k]\<^sub>S\<close>
          using Nom_trans unfolding assign_def equiv_nom_def by metis
        then show \<open>\<lbrakk>S, i\<rbrakk> \<Turnstile>\<^sub>@ \<^bold>\<bullet>k\<close>
          unfolding canonical_ctx_def by simp
      next
        assume \<open>x = \<^bold>\<bullet>k\<close> \<open>(i, \<^bold>\<not> \<^bold>\<bullet>k) \<in> S\<close>
        then have \<open>(i, \<^bold>\<bullet>k) \<notin> S\<close>
          using confl by force
        then have \<open>\<not> equiv_nom S i k\<close>
          unfolding equiv_nom_def by blast
        moreover have \<open>(k, \<^bold>\<not> \<^bold>\<bullet>i) \<in> S\<close>
          using \<open>(i, \<^bold>\<not> \<^bold>\<bullet>k) \<in> S\<close> alpha by force
        ultimately have \<open>[i]\<^sub>S \<noteq> [k]\<^sub>S\<close>
          using Nom_sym Nom_trans equiv_nom_assign unfolding equiv_nom_def by metis
        then show \<open>\<not> \<lbrakk>S, i\<rbrakk> \<Turnstile>\<^sub>@ \<^bold>\<bullet>k\<close>
          unfolding canonical_ctx_def by simp
      qed
  next
    case (Imp p q)
    then show ?thesis
    proof (safe del: notI)
      assume \<open>x = p \<^bold>\<longrightarrow> q\<close> \<open>(i, p \<^bold>\<longrightarrow> q) \<in> S\<close>
      then have \<open>(i, \<^bold>\<not> p) \<in> S \<or> (i, q) \<in> S\<close>
        using beta by force
      then show \<open>\<lbrakk>S, i\<rbrakk> \<Turnstile>\<^sub>@ p \<^bold>\<longrightarrow> q\<close>
        using 2 Imp unfolding canonical_ctx_def by auto
    next
      assume \<open>x = p \<^bold>\<longrightarrow> q\<close> \<open>(i, \<^bold>\<not> (p \<^bold>\<longrightarrow> q)) \<in> S\<close>
      then have \<open>(i, p) \<in> S \<and> (i, \<^bold>\<not> q) \<in> S\<close>
        using alpha by force
      then show \<open>\<not> \<lbrakk>S, i\<rbrakk> \<Turnstile>\<^sub>@ p \<^bold>\<longrightarrow> q\<close>
        using 2 Imp unfolding canonical_ctx_def by auto
    qed
  next
    case (Dia p)
    then show ?thesis
    proof (safe del: notI)
      assume \<open>x = \<^bold>\<diamond> p\<close> \<open>(i, \<^bold>\<diamond> p) \<in> S\<close>
      then obtain k where k: \<open>(k, p) \<in> S\<close> \<open>(i, \<^bold>\<diamond> (\<^bold>\<bullet>k)) \<in> S\<close>
        using delta
        by (metis (mono_tags, lifting) bot.extremum classify.intros(11) empty_set insert_subset list.simps(15))
      then have \<open>\<lbrakk>S, k\<rbrakk> \<Turnstile>\<^sub>@ p\<close>
        using 2 Dia by simp
      moreover have \<open>([i]\<^sub>S, \<^bold>\<diamond> (\<^bold>\<bullet>k)) \<in> S\<close>
        using k(2) equiv_nom_Nom equiv_nom_assign by fastforce
      then have \<open>[k]\<^sub>S \<in> reach S ([i]\<^sub>S)\<close>
        unfolding reach_def by blast
      ultimately show \<open>\<lbrakk>S, i\<rbrakk> \<Turnstile>\<^sub>@ \<^bold>\<diamond> p\<close>
        unfolding canonical_ctx_def canonical_def by auto
    next
      assume \<open>x = \<^bold>\<diamond> p\<close> \<open>(i, \<^bold>\<not> (\<^bold>\<diamond> p)) \<in> S\<close>
      {
        fix k
        assume \<open>[k]\<^sub>S \<in> reach S ([i]\<^sub>S)\<close>
        then obtain k' where \<open>([i]\<^sub>S, \<^bold>\<diamond> (\<^bold>\<bullet>k')) \<in> S\<close> \<open>[k']\<^sub>S = [k]\<^sub>S\<close>
          unfolding reach_def by auto
        then have \<open>(i, \<^bold>\<diamond> (\<^bold>\<bullet>k')) \<in> S\<close>
          using Nom_sym \<open>(i, \<^bold>\<not> \<^bold>\<diamond> p) \<in> S\<close> equiv_nom_Nom equiv_nom_assign
          unfolding equiv_nom_def by fast
        then have \<open>(k', \<^bold>\<not> p) \<in> S\<close>
          using \<open>(i, \<^bold>\<not> (\<^bold>\<diamond> p)) \<in> S\<close> alpha by force
        then have \<open>\<not> \<lbrakk>S, k'\<rbrakk> \<Turnstile>\<^sub>@ p\<close>
          using 2 Dia by simp
        then have \<open>\<not> \<lbrakk>S, k\<rbrakk> \<Turnstile>\<^sub>@ p\<close>
          unfolding canonical_ctx_def canonical_def using \<open>[k']\<^sub>S = [k]\<^sub>S\<close> by simp
      }
      then show \<open>\<not> \<lbrakk>S, i\<rbrakk> \<Turnstile>\<^sub>@ \<^bold>\<diamond> p\<close>
        unfolding canonical_ctx_def canonical_def by auto
    qed
  next
    case (Sat k p)
    then show ?thesis
    proof (safe del: notI)
      assume \<open>x = \<^bold>@k p\<close> \<open>(i, \<^bold>@k p) \<in> S\<close>
      then have \<open>(k, p) \<in> S\<close>
        using alpha by force
      then have \<open>\<lbrakk>S, k\<rbrakk> \<Turnstile>\<^sub>@ p\<close>
        using 2 Sat by simp
      then show \<open>\<lbrakk>S, i\<rbrakk> \<Turnstile>\<^sub>@ \<^bold>@k p\<close>
        unfolding canonical_ctx_def canonical_def by simp
    next
      assume \<open>x = \<^bold>@k p\<close> \<open>(i, \<^bold>\<not> \<^bold>@k p) \<in> S\<close>
      then have \<open>(k, \<^bold>\<not> p) \<in> S\<close>
        using alpha by force
      then have \<open>\<not> \<lbrakk>S, k\<rbrakk> \<Turnstile>\<^sub>@ p\<close>
        using 2 Sat by simp
      then show \<open>\<not> \<lbrakk>S, i\<rbrakk> \<Turnstile>\<^sub>@ \<^bold>@k p\<close>
        unfolding canonical_ctx_def canonical_def by simp
    qed
  next
    case (All p)
    then show ?thesis
    proof (safe del: notI)
      assume \<open>x = \<^bold>A p\<close> \<open>(i, \<^bold>A p) \<in> S\<close>
      then have \<open>(k, p) \<in> S\<close> for k
        using gamma by force
      then have \<open>\<lbrakk>S, k\<rbrakk> \<Turnstile>\<^sub>@ p\<close> for k
        using 2 All by simp
      then show \<open>\<lbrakk>S, i\<rbrakk> \<Turnstile>\<^sub>@ \<^bold>A p\<close>
        unfolding canonical_ctx_def canonical_def by auto
    next
      assume \<open>x = \<^bold>A p\<close> \<open>(i, \<^bold>\<not> \<^bold>A p) \<in> S\<close>
      then have \<open>\<exists>k. (k, \<^bold>\<not> p) \<in> S\<close>
        using delta[of \<open>[(i, \<^bold>\<not> \<^bold>A p)]\<close>] by fastforce
      then have \<open>\<exists>k. \<not> \<lbrakk>S, k\<rbrakk> \<Turnstile>\<^sub>@ p\<close>
        using 2 All by auto
      then show \<open>\<not> \<lbrakk>S, i\<rbrakk> \<Turnstile>\<^sub>@ \<^bold>A p\<close>
        unfolding canonical_ctx_def canonical_def by auto
    qed
  next
    case (Dwn p)
   then show ?thesis
    proof (safe del: notI)
      assume \<open>x = \<^bold>\<down> p\<close> \<open>(i, \<^bold>\<down> p) \<in> S\<close>
      then have \<open>(i, \<langle>i\<rangle>p) \<in> S\<close>
        using alpha by force
      moreover have \<open>size_fm (\<langle>i\<rangle>p) < size_fm (\<^bold>\<down> p)\<close>
        by simp
      ultimately have \<open>\<lbrakk>S, i\<rbrakk> \<Turnstile>\<^sub>@ \<langle>i\<rangle>p\<close>
        using 2 Dwn by (meson in_measure)
      then show \<open>\<lbrakk>S, i\<rbrakk> \<Turnstile>\<^sub>@ \<^bold>\<down> p\<close>
        unfolding canonical_ctx_def canonical_def by simp
    next
      assume \<open>x = \<^bold>\<down> p\<close> \<open>(i, \<^bold>\<not> \<^bold>\<down> p) \<in> S\<close>
      then have \<open>(i, \<^bold>\<not> \<langle>i\<rangle>p) \<in> S\<close>
        using alpha by force
      moreover have \<open>size_fm (\<langle>i\<rangle>p) < size_fm (\<^bold>\<down> p)\<close>
        by simp
      ultimately have \<open>\<not> \<lbrakk>S, i\<rbrakk> \<Turnstile>\<^sub>@ \<langle>i\<rangle>p\<close>
        using 2 Dwn by (meson in_measure)
      then show \<open>\<not> \<lbrakk>S, i\<rbrakk> \<Turnstile>\<^sub>@ \<^bold>\<down> p\<close>
        unfolding canonical_ctx_def canonical_def by simp
    qed
  qed
qed

end

theorem model_existence:
  fixes S :: \<open>('i, 'p) lbd set\<close>
  assumes \<open>consistency C\<close>
    and \<open>S \<in> C\<close>
    and \<open>|UNIV :: ('i, 'p) lbd set| \<le>o |- params S|\<close>
    and \<open>(i, p) \<in> S\<close>
  shows \<open>\<lbrakk>mk_mcs C S, i\<rbrakk> \<Turnstile>\<^sub>@ p\<close>
  using assms MyHintikka.model Hintikka_mk_mcs Extend_subset MyHintikka.intro by fast


section \<open>Natural Deduction\<close>

inductive Calculus :: \<open>('i, 'p) lbd list \<Rightarrow> ('i, 'p) lbd \<Rightarrow> bool\<close> (infix \<open>\<turnstile>\<close> 50) where
  Assm [simp]: \<open>(i, p) \<in> set A \<Longrightarrow> A \<turnstile> (i, p)\<close>
| Ref [simp]: \<open>A \<turnstile> (i, \<^bold>\<bullet>i)\<close>
| Nom [dest]: \<open>A \<turnstile> (i, \<^bold>\<bullet>k) \<Longrightarrow> A \<turnstile> (i, p) \<Longrightarrow> A \<turnstile> (k, p)\<close>
| FlsE [elim]: \<open>A \<turnstile> (i, \<^bold>\<bottom>) \<Longrightarrow> A \<turnstile> (k, p)\<close>
| ImpI [intro]: \<open>(i, p) # A \<turnstile> (i, q) \<Longrightarrow> A \<turnstile> (i, p \<^bold>\<longrightarrow> q)\<close>
| ImpE [dest]: \<open>A \<turnstile> (i, p \<^bold>\<longrightarrow> q) \<Longrightarrow> A \<turnstile> (i, p) \<Longrightarrow> A \<turnstile> (i, q)\<close>
| SatI [intro]: \<open>A \<turnstile> (i, p) \<Longrightarrow> A \<turnstile> (k, \<^bold>@i p)\<close>
| SatE [dest]: \<open>A \<turnstile> (i, \<^bold>@k p) \<Longrightarrow> A \<turnstile> (k, p)\<close>
| DiaI [intro]: \<open>A \<turnstile> (i, \<^bold>\<diamond> (\<^bold>\<bullet>k)) \<Longrightarrow> A \<turnstile> (k, p) \<Longrightarrow> A \<turnstile> (i, \<^bold>\<diamond> p)\<close>
| DiaE [elim]: \<open>A \<turnstile> (i, \<^bold>\<diamond> p) \<Longrightarrow> k \<notin> nominals ({(i, p), (j, q)} \<union> set A) \<Longrightarrow>
    (\<^bold>\<circle>k, p) # (i, \<^bold>\<diamond> (\<^bold>\<bullet> (\<^bold>\<circle>k))) # A \<turnstile> (j, q) \<Longrightarrow> A \<turnstile> (j, q)\<close>
| AllI [intro]: \<open>A \<turnstile> (\<^bold>\<circle>k, p) \<Longrightarrow> k \<notin> nominals ({(i, p)} \<union> set A) \<Longrightarrow> A \<turnstile> (i, \<^bold>A p)\<close>
| AllE [dest]: \<open>A \<turnstile> (i, \<^bold>A p) \<Longrightarrow> A \<turnstile> (k, p)\<close>
| DwnI [intro]: \<open>A \<turnstile> (i, \<langle>i\<rangle>p) \<Longrightarrow> A \<turnstile> (i, \<^bold>\<down> p)\<close>
| DwnE [dest]: \<open>A \<turnstile> (i, \<^bold>\<down> p) \<Longrightarrow> A \<turnstile> (i, \<langle>i\<rangle>p)\<close>
| Clas: \<open>(i, p \<^bold>\<longrightarrow> q) # A \<turnstile> (i, p) \<Longrightarrow> A \<turnstile> (i, p)\<close>

subsection \<open>Soundness\<close>

theorem soundness:
  assumes \<open>A \<turnstile> (i, p)\<close> \<open>\<forall>(k, q) \<in> set A. (M, g, e, \<lparr>(g, e)\<rparr> k) \<Turnstile>\<^sub>@ q\<close>
    \<open>range g \<subseteq> W M\<close> \<open>range e \<subseteq> W M\<close>
  shows \<open>(M, g, e, \<lparr>(g, e)\<rparr> i) \<Turnstile>\<^sub>@ p\<close>
  using assms
proof (induct \<open>(i, p)\<close> arbitrary: i p g e rule: Calculus.induct)
  case (DiaI A i k p)
  then show ?case
    apply simp
    by blast
next
  case (DiaE A i p k j q)
  then have \<open>(M, g, e, \<lparr>(g, e)\<rparr> i) \<Turnstile>\<^sub>@ \<^bold>\<diamond> p\<close>
    by blast
  then obtain v where v: \<open>v \<in> W M \<inter> R M (\<lparr>(g, e)\<rparr> i)\<close> \<open>(M, g, e, v) \<Turnstile>\<^sub>@ p\<close>
    by auto
  let ?g = \<open>g(k := v)\<close>
  have \<open>(M, ?g, e, \<lparr>(?g, e)\<rparr> (\<^bold>\<circle>k)) \<Turnstile>\<^sub>@ p\<close> \<open>(M, ?g, e, \<lparr>(?g, e)\<rparr> i) \<Turnstile>\<^sub>@ \<^bold>\<diamond> (\<^bold>\<bullet> (\<^bold>\<circle>k))\<close>
    using v fun_upd_same DiaE(3) semantics_fresh_lbd by fastforce+
  moreover have \<open>\<forall>(a, q) \<in> set A. (M, ?g, e, \<lparr>(?g, e)\<rparr> a) \<Turnstile>\<^sub>@ q\<close>
    using DiaE.prems(1) DiaE.hyps(3) semantics_fresh_lbd by fastforce
  ultimately have \<open>\<forall>(a, q) \<in> set ((\<^bold>\<circle>k, p) # (i, \<^bold>\<diamond> (\<^bold>\<bullet>(\<^bold>\<circle>k))) # A). (M, ?g, e, \<lparr>(?g, e)\<rparr> a) \<Turnstile>\<^sub>@ q\<close>
    by simp
  moreover have \<open>range ?g \<subseteq> W M\<close>
    using DiaE.prems v by auto
  moreover have \<open>range e \<subseteq> W M\<close>
    using DiaE.prems by auto
  ultimately have \<open>(M, ?g, e, \<lparr>(?g, e)\<rparr> j) \<Turnstile>\<^sub>@ q\<close>
    using DiaE.hyps by meson
  then show ?case
    using DiaE.hyps(3) semantics_fresh_lbd by fastforce
next
  case (AllI A k p i)
  {
    fix v
    assume \<open>v \<in> W M\<close>
    let ?g = \<open>g(k := v)\<close>
    have \<open>\<forall>v. \<forall>(i, p) \<in> set A. (M, ?g, e, \<lparr>(?g, e)\<rparr> i) \<Turnstile>\<^sub>@ p\<close>
      using AllI.prems(1) AllI.hyps(3) semantics_fresh_lbd by fastforce
    moreover have \<open>range ?g \<subseteq> W M\<close>
      using AllI.prems \<open>v \<in> W M\<close> by auto
    moreover have \<open>range e \<subseteq> W M\<close>
      using AllI.prems by auto
    ultimately have \<open>(M, ?g, e, \<lparr>(?g, e)\<rparr> (\<^bold>\<circle> k)) \<Turnstile>\<^sub>@ p\<close>
      using AllI.hyps by metis
  }
  then have \<open>\<forall>v \<in> W M. (M, g(k := v), e, v) \<Turnstile>\<^sub>@ p\<close>
    by simp
  then have \<open>\<forall>v \<in> W M. (M, g, e, v) \<Turnstile>\<^sub>@ p\<close>
    using AllI.hyps(3) semantics_fresh_lbd by fast
  then show ?case
    by simp
next
  case (AllE A i p k)
  then show ?case
    by (cases k) (simp_all add: image_subset_iff)
qed auto

corollary soundness':
  assumes \<open>[] \<turnstile> (\<^bold>\<circle>i, p)\<close> \<open>i \<notin> nominals_fm p\<close>
    and \<open>range g \<subseteq> W M\<close> \<open>range e \<subseteq> W M\<close> \<open>w \<in> W M\<close>
  shows \<open>(M, g, e, w) \<Turnstile>\<^sub>@ p\<close>
proof -
  let ?g = \<open>g(i := w)\<close>
  have \<open>range ?g \<subseteq> W M\<close>
    using assms(3-5) by auto
  then have \<open>(M, ?g, e, \<lparr>(?g, e)\<rparr> (\<^bold>\<circle>i)) \<Turnstile>\<^sub>@ p\<close>
    using assms(1, 4) soundness by (metis empty_iff list.set(1))
  then have \<open>(M, ?g, e, w) \<Turnstile>\<^sub>@ p\<close>
    by simp
  then show ?thesis
    using assms(2) semantics_fresh by fast
qed

corollary \<open>\<not> ([] \<turnstile> (\<^bold>\<circle>i, \<^bold>\<bottom>))\<close>
  using soundness'
  by (metis UNIV_I empty_iff fm.simps(153) model.sel(1) semantics.simps(2) top_greatest)

subsection \<open>Derived Rules\<close>

lemma Assm_head [simp]: \<open>(p, i) # A \<turnstile> (p, i)\<close>
  by auto

lemma Boole: \<open>(i, \<^bold>\<not> p) # A \<turnstile> (i, \<^bold>\<bottom>) \<Longrightarrow> A \<turnstile> (i, p)\<close>
  using Clas FlsE by meson

lemma calculus_confl:
  assumes \<open>ps \<leadsto> Confl qs\<close> \<open>set ps \<subseteq> set A\<close> \<open>q \<in> set qs\<close> \<open>q \<in> set A\<close> 
  shows \<open>A \<turnstile> (i, \<^bold>\<bottom>)\<close>
  using assms
proof cases
  case (1 i)
  then show ?thesis
    using assms(2-) Assm by fastforce
next
  case 3
  then show ?thesis
    using assms(2-)
    apply simp
    by (meson Assm ImpE FlsE)
qed

lemma calculus_alpha:
  assumes \<open>ps \<leadsto> Alpha qs\<close> \<open>set ps \<subseteq> set A\<close> \<open>qs @ A \<turnstile> (i, \<^bold>\<bottom>)\<close>
  shows \<open>A \<turnstile> (i, \<^bold>\<bottom>)\<close>
  using assms
proof cases
  case (4 i k)
  then show ?thesis
    using assms(2-)
    apply simp
    by (metis Assm FlsE ImpE ImpI Nom Ref)
next
  case (5 i k)
  then show ?thesis
    using assms(2-)
    apply simp
    by (metis Assm Clas FlsE ImpE Nom Ref)
next
  case (6 i k p)
  then show ?thesis
    using assms(2-)
    apply simp
    by (metis Assm FlsE ImpE ImpI Nom)
next
  case (8 i p q)
  then show ?thesis
    using assms(2-)
    apply simp
    by (metis Assm FlsE ImpE ImpI list.set_intros(1-2))
next
  case (9 i k p)
  then show ?thesis
    using assms(2-)
    apply simp
    by (metis Assm FlsE ImpE ImpI SatE)
next
  case (10 i k p)
  then show ?thesis
    using assms(2-)
    apply simp
    by (metis Assm Clas FlsE ImpE SatI)
next
  case (12 i p k)
  then show ?thesis
    using assms(2-)
    apply simp
    by (metis Assm Clas DiaI FlsE ImpE)
next
  case (15 i p)
  then show ?thesis
    using assms(2-)
    apply simp
    by (meson Assm DwnE FlsE ImpE ImpI)
next
  case (16 i p)
  then show ?thesis
    using assms(2-)
    apply simp
    using Assm Boole FlsE by blast
qed

lemma calculus_beta:
  assumes \<open>ps \<leadsto> Beta qs\<close> \<open>set ps \<subseteq> set A\<close> \<open>\<forall>q \<in> set qs. q # A \<turnstile> (i, \<^bold>\<bottom>)\<close>
  shows \<open>A \<turnstile> (i, \<^bold>\<bottom>)\<close>
  using assms
proof cases
  case (7 i p q)
  then show ?thesis
    using assms(2-)
    apply simp
    by (metis Assm Boole FlsE ImpE ImpI)
qed

lemma calculus_gamma:
  assumes \<open>ps \<leadsto> Gamma qs\<close> \<open>set ps \<subseteq> set A\<close> \<open>case_option [] id (qs k) @ A \<turnstile> (i, \<^bold>\<bottom>)\<close>
  shows \<open>A \<turnstile> (i, \<^bold>\<bottom>)\<close>
  using assms
proof cases
  case 2
  then show ?thesis
    using assms(2-)
    apply simp
    by (meson FlsE ImpE ImpI Ref)
next
  case (13 i p)
  then show ?thesis
    using assms(2-)
    apply simp
    by (metis AllE Assm FlsE ImpE ImpI)
qed

lemma calculus_delta:
  assumes \<open>ps \<leadsto> Delta qs\<close> \<open>set ps \<subseteq> set A\<close> \<open>k \<notin> params ({(a, \<^bold>\<bottom>)} \<union> set A)\<close> \<open>qs k @ A \<turnstile> (a, \<^bold>\<bottom>)\<close>
  shows \<open>A \<turnstile> (a, \<^bold>\<bottom>)\<close>
  using assms
proof cases
  case (11 i p)
  then have \<open>(\<^bold>\<circle>k, p) # (i, \<^bold>\<diamond> (\<^bold>\<bullet>(\<^bold>\<circle>k))) # A \<turnstile> (a, \<^bold>\<bottom>)\<close> \<open>(i, \<^bold>\<diamond> p) \<in> set A\<close>
    using assms(2-) by simp_all
  moreover have \<open>k \<notin> nominals ({(i, p), (a, \<^bold>\<bottom>)} \<union> set A)\<close>
    using assms(2-3) 11 by auto
  ultimately show ?thesis
    using DiaE by (meson Assm)
next
  case (14 i p)
  then have \<open>(\<^bold>\<circle>k, \<^bold>\<not> p) # A \<turnstile> (a, \<^bold>\<bottom>)\<close> \<open>(i, \<^bold>\<not> \<^bold>A p) \<in> set A\<close>
    using assms(2-) by simp_all
  then have \<open>(\<^bold>\<circle>k, \<^bold>\<not> p) # A \<turnstile> (\<^bold>\<circle>k, \<^bold>\<bottom>)\<close>
    by fast
  then have \<open>A \<turnstile> (\<^bold>\<circle>k, p)\<close>
    by (meson Boole)
  moreover have \<open>k \<notin> nominals ({(i, p)} \<union> set A)\<close>
    using assms(2-3) 14 by auto
  ultimately have \<open>A \<turnstile> (i, \<^bold>A p)\<close>
    by blast
  moreover have \<open>A \<turnstile> (i, \<^bold>\<not> \<^bold>A p)\<close>
    using \<open>(i, \<^bold>\<not> \<^bold>A p) \<in> set A\<close> by simp
  ultimately have \<open>A \<turnstile> (i, \<^bold>\<bottom>)\<close>
    by blast
  then show ?thesis
    by fast
qed

subsection \<open>Derivational Consistency\<close>

lemma deriv_consistency:
  assumes inf: \<open>infinite (UNIV :: 'i set)\<close>
  shows \<open>consistency {S :: ('i, 'p) lbd set. \<exists>A. S = set A \<and> \<not> A \<turnstile> (a, \<^bold>\<bottom>)}\<close>
  unfolding consistency_def
proof safe
  fix S :: \<open>('i, 'p) lbd set\<close> and A ps :: \<open>('i, 'p) lbd list\<close> and i
  assume *: \<open>\<not> A \<turnstile> (a, \<^bold>\<bottom>)\<close> and ps: \<open>set ps \<subseteq> set A\<close>

  {
    fix qs q
    assume \<open>ps \<leadsto> Confl qs\<close> \<open>q \<in> set qs\<close> \<open>q \<in> set A\<close>
    then have \<open>A \<turnstile> (a, \<^bold>\<bottom>)\<close>
      using ps calculus_confl by meson
    then show False
      using * by blast
  }

  {
    fix qs
    assume **: \<open>ps \<leadsto> Alpha qs\<close>
    {
      assume \<open>qs @ A \<turnstile> (a, \<^bold>\<bottom>)\<close>
      then have \<open>A \<turnstile> (a, \<^bold>\<bottom>)\<close>
        using ** ps calculus_alpha by meson
    }
    then show \<open>\<exists>B. set qs \<union> set A = set B \<and> \<not> B \<turnstile> (a, \<^bold>\<bottom>)\<close>
      using * by (metis set_append)
  }

  {
    fix qs
    assume **: \<open>ps \<leadsto> Beta qs\<close>
    {
      assume \<open>\<forall>q \<in> set qs. q # A \<turnstile> (a, \<^bold>\<bottom>)\<close>
      then have \<open>A \<turnstile> (a, \<^bold>\<bottom>)\<close>
        using ** ps calculus_beta by meson
    }
    then show \<open>\<exists>q \<in> set qs. {q} \<union> set A \<in> {set A |A. \<not> A \<turnstile> (a, \<^bold>\<bottom>)}\<close>
      using * by fastforce
  }

  {
    fix t and qs :: \<open>'i tm \<Rightarrow> ('i, 'p) lbd list option\<close>
    assume **: \<open>ps \<leadsto> Gamma qs\<close>
    {
      assume \<open>case_option [] id (qs t) @ A \<turnstile> (a, \<^bold>\<bottom>)\<close>
      then have \<open>A \<turnstile> (a, \<^bold>\<bottom>)\<close>
        using ** ps calculus_gamma by meson
    }
    then show \<open>\<exists>B. (case qs t of None \<Rightarrow> {} | Some x \<Rightarrow> set x) \<union> set A = set B \<and> \<not> B \<turnstile> (a, \<^bold>\<bottom>)\<close>
      using * by (metis empty_set id_apply option.case_eq_if set_append)
  }

  {
    fix qs :: \<open>'i \<Rightarrow> ('i, 'p) lbd list\<close>
    assume **: \<open>ps \<leadsto> Delta qs\<close>
    have \<open>infinite (- (nominals ({(a, \<^bold>\<bottom>)} \<union> set A)))\<close>
      using inf finite_compl by fastforce
    then obtain k where k: \<open>k \<notin> nominals ({(a, \<^bold>\<bottom>)} \<union> set A)\<close>
      using infinite_imp_nonempty by blast
    {
      assume \<open>qs k @ A \<turnstile> (a, \<^bold>\<bottom>)\<close>
      then have \<open>A \<turnstile> (a, \<^bold>\<bottom>)\<close>
        using ** k ps calculus_delta  by meson
    }
    then show \<open>\<exists>x. set (qs x) \<union> set A \<in> {set A |A. \<not> A \<turnstile> (a, \<^bold>\<bottom>)}\<close>
      using * by (metis (mono_tags, lifting) CollectI set_append)
  }
qed

subsection \<open>Completeness\<close>

theorem weak_completeness:
  fixes p :: \<open>('i, 'p) fm\<close>
  assumes mod: \<open>\<And>(M :: ('i tm, 'p) model) g e w.
      range g \<subseteq> W M \<Longrightarrow> range e \<subseteq> W M \<Longrightarrow> w \<in> W M \<Longrightarrow>
      \<forall>(k, q) \<in> set A. (M, g, e, \<lparr>(g, e)\<rparr> k) \<Turnstile>\<^sub>@ q \<Longrightarrow>
      (M, g, e, w) \<Turnstile>\<^sub>@ p\<close>
    and inf: \<open>|UNIV :: ('i, 'p) lbd set| \<le>o |- nominals (set A)|\<close>
  shows \<open>A \<turnstile> (i, p)\<close>
proof (rule ccontr)
  assume \<open>\<not> A \<turnstile> (i, p)\<close>
  then have *: \<open>\<not> (i, \<^bold>\<not> p) # A \<turnstile> (i, \<^bold>\<bottom>)\<close>
    using Boole by fast

  let ?S = \<open>set ((i, \<^bold>\<not> p) # A)\<close>
  let ?C = \<open>{S :: ('i, 'p) lbd set. \<exists>A. S = set A \<and> \<not> A \<turnstile> (i, \<^bold>\<bottom>)}\<close>
  let ?H = \<open>mk_mcs ?C ?S\<close>
  let ?M = \<open>\<lambda>i. \<lbrakk>?H, i\<rbrakk>\<close>

  have \<open>infinite (UNIV :: 'i set)\<close>
    using inf by (meson card_of_ordLeq_infinite inf_UNIV rev_finite_subset subset_UNIV)
  then have \<open>consistency ?C\<close>
    using deriv_consistency by fast
  moreover have \<open>?S \<in> ?C\<close>
    using * FlsE by fastforce
  moreover have \<open>|UNIV :: ('i, 'p) lbd set| \<le>o |- params ?S|\<close>
    using inf by (metis Un_insert_left list.set(1) list.simps(15) params_left sup_bot_left)
  ultimately have **: \<open>\<forall>(i, p) \<in> ?S. ?M i \<Turnstile>\<^sub>@ p\<close>
    using model_existence[of ?C ?S] by blast

  moreover have \<open>range (\<lambda>i. assign (\<^bold>\<circle>i) ?H) \<subseteq> W (canonical ?H i)\<close>
    unfolding canonical_def by auto
  moreover have \<open>range (\<lambda>n. assign (\<^bold>#n) ?H) \<subseteq> W (canonical ?H i)\<close>
    unfolding canonical_def by auto
  moreover have \<open>assign i ?H \<in> W (canonical ?H i)\<close>
    unfolding canonical_def by auto
  ultimately have \<open>?M i \<Turnstile>\<^sub>@ p\<close>
    using mod[of \<open>\<lambda>i. assign (\<^bold>\<circle>i) ?H\<close> \<open>canonical ?H i\<close> \<open>\<lambda>n. assign (\<^bold>#n) ?H\<close> \<open>assign i ?H\<close>]
    unfolding canonical_ctx_def canonical_def by fastforce
  moreover have \<open>\<not> ?M i \<Turnstile>\<^sub>@ p\<close>
    using ** unfolding canonical_ctx_def by simp
  ultimately show False
    by simp
qed

theorem main:
  fixes p :: \<open>('i, 'p) fm\<close>
  assumes \<open>i \<notin> nominals_fm p\<close> \<open>|UNIV :: ('i, 'p) lbd set| \<le>o  |UNIV :: 'i set|\<close>
  shows \<open>[] \<turnstile> (\<^bold>\<circle>i, p) \<longleftrightarrow> (\<forall>(M :: ('i tm, 'p) model) g e. \<forall>w \<in> W M. range g \<subseteq> W M \<longrightarrow> range e \<subseteq> W M \<longrightarrow> (M, g, e, w) \<Turnstile>\<^sub>@ p)\<close>
proof
  assume \<open>[] \<turnstile> (\<^bold>\<circle>i, p)\<close>
  then show \<open>\<forall>(M :: ('i tm, 'p) model) g e. \<forall>w\<in>W M. range g \<subseteq> W M \<longrightarrow> range e \<subseteq> W M \<longrightarrow> (M, g, e, w) \<Turnstile>\<^sub>@ p\<close>
    using soundness'[of i p] assms(1) by meson
next
  assume \<open>\<forall>(M :: ('i tm, 'p) model) g e. \<forall>w \<in> W M. range g \<subseteq> W M \<longrightarrow> range e \<subseteq> W M \<longrightarrow> (M, g, e, w) \<Turnstile>\<^sub>@ p\<close>
  then show \<open>[] \<turnstile> (\<^bold>\<circle>i, p)\<close>
    using assms weak_completeness[of \<open>[]\<close> p] by simp
qed

end
