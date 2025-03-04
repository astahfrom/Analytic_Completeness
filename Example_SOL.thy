(*
  File:      Example_SOL.thy
  Author:    Anders Schlichtkrull
  Author:    Asta Halkjær From

*)

theory Example_SOL imports
  Analytic_Completeness
begin

section \<open>Syntax\<close>

datatype (params_sym:'f) sym
  = VarS nat (\<open>\<^bold>#\<^sub>2\<close>)
  | SymS 'f (\<open>\<^bold>\<circle>\<^sub>2\<close>)

datatype (params_tm: 'f) tm
  = Var nat (\<open>\<^bold>#\<close>)
  | Fun \<open>'f sym\<close> \<open>'f tm list\<close> (\<open>\<^bold>\<circle>\<close>)
(* TODO: explicit domain in model so we don't need this guy? *)
  | Cst 'f (\<open>\<^bold>\<star>\<close>) (* Måske burde konstanterne have deres egen typevariabel.*)

datatype (params_fm: 'f) fm
  = Falsity (\<open>\<^bold>\<bottom>\<close>)
  | is_Pre: Pre \<open>'f sym\<close> \<open>'f tm list\<close> (\<open>\<^bold>\<cdot>\<close>)
  | Imp \<open>'f fm\<close> \<open>'f fm\<close> (infixr \<open>\<^bold>\<longrightarrow>\<close> 55)
  | Uni \<open>'f fm\<close> (\<open>\<^bold>\<forall>\<close>)
  | Uni2P \<open>'f fm\<close> (\<open>\<^bold>\<forall>\<^sub>P\<close>)
  | Uni2F \<open>'f fm\<close> (\<open>\<^bold>\<forall>\<^sub>F\<close>)

abbreviation Neg (\<open>\<^bold>\<not> _\<close> [70] 70) where \<open>\<^bold>\<not> p \<equiv> p \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>

abbreviation And (infix \<open>\<^bold>\<and>\<close> 50) where \<open>p \<^bold>\<and> q \<equiv> \<^bold>\<not> (p \<^bold>\<longrightarrow> \<^bold>\<not> q)\<close>

abbreviation Iff (infix \<open>\<^bold>\<longleftrightarrow>\<close> 50) where \<open>p \<^bold>\<longleftrightarrow> q \<equiv> (p \<^bold>\<longrightarrow> q) \<^bold>\<and> (q \<^bold>\<longrightarrow> p)\<close>

abbreviation Eql (\<open>_ \<^bold>= _\<close>) where \<open>t1 \<^bold>= t2 \<equiv> (\<^bold>\<forall>\<^sub>P ((\<^bold>\<cdot>(\<^bold>#\<^sub>2 0) [t1]) \<^bold>\<longleftrightarrow> (\<^bold>\<cdot>(\<^bold>#\<^sub>2 0) [t2])))\<close>

abbreviation Exi2F (\<open>\<^bold>\<exists>\<^sub>F\<close>) where \<open>\<^bold>\<exists>\<^sub>F p \<equiv> \<^bold>\<not>(\<^bold>\<forall>\<^sub>F(\<^bold>\<not>p))\<close>

abbreviation Exi2P (\<open>\<^bold>\<exists>\<^sub>P\<close>) where \<open>\<^bold>\<exists>\<^sub>P p \<equiv> \<^bold>\<not>(\<^bold>\<forall>\<^sub>P(\<^bold>\<not>p))\<close>

term \<open>\<^bold>\<forall>(\<^bold>\<bottom> \<^bold>\<longrightarrow> (\<^bold>\<cdot>(\<^bold>\<circle>\<^sub>2 ''P'') [\<^bold>\<circle>(\<^bold>\<circle>\<^sub>2 ''f'') [\<^bold>#0]]))\<close>

section \<open>Semantics\<close>

definition shift (\<open>_\<langle>_:_\<rangle>\<close>) where
  \<open>E\<langle>n:x\<rangle> m \<equiv> if m < n then E m else if m = n then x else E (m-1)\<close>

primrec semantics_fn (\<open>\<lparr>_, _\<rparr>2\<close>) where
  \<open>\<lparr>E2F, F\<rparr>2 (\<^bold>#\<^sub>2 n) = E2F n\<close>
| \<open>\<lparr>E2F, F\<rparr>2 (\<^bold>\<circle>\<^sub>2 f) = F f\<close>

primrec semantics_tm (\<open>\<lparr>_,_, _, _\<rparr>\<close>) where
  \<open>\<lparr>E, E2F, C, F\<rparr> (\<^bold>#n) = E n\<close>
| \<open>\<lparr>E, E2F, C, F\<rparr> (\<^bold>\<circle>f ts) = (\<lparr>E2F, F\<rparr>2 f) (map \<lparr>E, E2F, C, F\<rparr> ts)\<close>
| \<open>\<lparr>E, E2F, C, F\<rparr> (\<^bold>\<star> c) = C c\<close>

primrec semantics_fm (\<open>\<lbrakk>_, _, _, _, _, _, _, _\<rbrakk>\<close>) where
  \<open>\<lbrakk>_, _, _, _, _, _, _, _\<rbrakk> \<^bold>\<bottom> = False\<close>
| \<open>\<lbrakk>E, E2F, E2P, C, F, G, PS, FS\<rbrakk> (\<^bold>\<cdot>P ts) = \<lparr>E2P, G\<rparr>2 P (map \<lparr>E, E2F, C, F\<rparr> ts)\<close>
| \<open>\<lbrakk>E, E2F, E2P, C, F, G, PS, FS\<rbrakk> (p \<^bold>\<longrightarrow> q) = (\<lbrakk>E, E2F, E2P, C, F, G, PS, FS\<rbrakk> p \<longrightarrow> \<lbrakk>E, E2F, E2P, C, F, G, PS, FS\<rbrakk> q)\<close>
| \<open>\<lbrakk>E, E2F, E2P, C, F, G, PS, FS\<rbrakk> (\<^bold>\<forall>p) = (\<forall>x. \<lbrakk>E\<langle>0:x\<rangle>, E2F, E2P, C, F, G, PS, FS\<rbrakk> p)\<close>
| \<open>\<lbrakk>E, E2F, E2P, C, F, G, PS, FS\<rbrakk> (\<^bold>\<forall>\<^sub>Pp) = (\<forall>x \<in> PS. \<lbrakk>E, E2F, E2P\<langle>0:x\<rangle>, C, F, G, PS, FS\<rbrakk> p)\<close>
| \<open>\<lbrakk>E, E2F, E2P, C, F, G, PS, FS\<rbrakk> (\<^bold>\<forall>\<^sub>Fp) = (\<forall>x \<in> FS. \<lbrakk>E, E2F\<langle>0:x\<rangle>, E2P, C, F, G, PS, FS\<rbrakk> p)\<close>

proposition \<open>\<lbrakk>E, E2F, E2P, C, F, G, PS, FS\<rbrakk> (\<^bold>\<forall>(\<^bold>\<cdot>P [\<^bold># 0]) \<^bold>\<longrightarrow> \<^bold>\<cdot>P [\<^bold>\<star>a])\<close>
  by (simp add: shift_def)

section \<open>Operations\<close>

subsection \<open>Shift\<close>

context fixes n m :: nat begin

lemma shift_eq [simp]: \<open>n = m \<Longrightarrow> E\<langle>n:x\<rangle> m = x\<close>
  by (simp add: shift_def)

lemma shift_gt [simp]: \<open>m < n \<Longrightarrow> E\<langle>n:x\<rangle> m = E m\<close>
  by (simp add: shift_def)

lemma shift_lt [simp]: \<open>n < m \<Longrightarrow> E\<langle>n:x\<rangle> m = E (m-1)\<close>
  by (simp add: shift_def)

lemma shift_commute [simp]: \<open>(E\<langle>n:y\<rangle>\<langle>0:x\<rangle>) = (E\<langle>0:x\<rangle>\<langle>n+1:y\<rangle>)\<close>
proof
  fix m
  show \<open>(E\<langle>n:y\<rangle>\<langle>0:x\<rangle>) m = (E\<langle>0:x\<rangle>\<langle>n+1:y\<rangle>) m\<close>
    unfolding shift_def by (cases m) simp_all
qed

end

subsection \<open>Parameters\<close>

abbreviation \<open>params S \<equiv> \<Union>p \<in> S. params_fm p\<close>

abbreviation reasg ("_ (_ ::= _)") where
  "reasg ==  \<lambda>f. \<lambda>(b1,b2). \<lambda>c a1 a2. if a1 = b1 \<and> a2 = b2 then c else f a1 a2"

lemma upd_params_sym [simp]: \<open>f \<notin> params_sym fn \<Longrightarrow> \<lparr>E2F, F(f := x)\<rparr>2 fn = \<lparr>E2F, F\<rparr>2 fn\<close>
  by (induct fn) (auto cong: map_cong)

lemma upd_params_tm [simp]: \<open>f \<notin> params_tm t \<Longrightarrow> \<lparr>E, E2F, C, F(f := x)\<rparr> t = \<lparr>E, E2F, C, F\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma upd_params_tm_c [simp]: \<open>c \<notin> params_tm t \<Longrightarrow> \<lparr>E, E2F, C(c := x), F\<rparr> t = \<lparr>E, E2F, C, F\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma upd_params_fm [simp]: \<open>f \<notin> params_fm p \<Longrightarrow> \<lbrakk>E, E2F, E2P, C, F(f := x), G, PS, FS\<rbrakk> p = \<lbrakk>E, E2F, E2P, C, F, G, PS, FS\<rbrakk> p\<close>
  by (induct p arbitrary: E E2P E2F) (auto cong: map_cong)

lemma upd_params_fm_c [simp]: \<open>c \<notin> params_fm p \<Longrightarrow> \<lbrakk>E, E2F, E2P, C(c := x), F, G, PS, FS\<rbrakk> p = \<lbrakk>E, E2F, E2P, C, F, G, PS, FS\<rbrakk> p\<close>
  by (induct p arbitrary: E E2P E2F) (auto cong: map_cong)

lemma upd_params_fm_G [simp]: \<open>P \<notin> params_fm p \<Longrightarrow> \<lbrakk>E, E2F, E2P, C, F, G(P := x), PS, FS\<rbrakk> p = \<lbrakk>E, E2F, E2P, C, F, G, PS, FS\<rbrakk> p\<close>
  by (induct p arbitrary: E E2F E2P) (auto cong: map_cong)

lemma finite_params_sym [simp]: \<open>finite (params_sym fn)\<close>
  by (induct fn) simp_all

lemma finite_params_tm [simp]: \<open>finite (params_tm t)\<close>
  by (induct t) simp_all

lemma finite_params_fm [simp]: \<open>finite (params_fm p)\<close>
  by (induct p) simp_all


subsection \<open>Instantiation\<close>

(* TODO: use multiple substitutions *)

primrec lift_tm (\<open>\<^bold>\<up>\<close>) where
  \<open>\<^bold>\<up>(\<^bold>#n) = \<^bold>#(n+1)\<close>
| \<open>\<^bold>\<up>(\<^bold>\<circle>f ts) = \<^bold>\<circle>f (map \<^bold>\<up> ts)\<close>
| \<open>\<^bold>\<up>(\<^bold>\<star>c) = \<^bold>\<star> c\<close>

primrec lift_sym (\<open>\<^bold>\<up>2sym\<close>) where
  \<open>\<^bold>\<up>2sym(\<^bold>#\<^sub>2 n) = \<^bold>#\<^sub>2 (n+1)\<close>
| \<open>\<^bold>\<up>2sym(\<^bold>\<circle>\<^sub>2 p) = \<^bold>\<circle>\<^sub>2 p\<close>

primrec lift_tm2 (\<open>\<^bold>\<up>2Ftm\<close>) where
  \<open>\<^bold>\<up>2Ftm(\<^bold>#n) = \<^bold>#n\<close>
| \<open>\<^bold>\<up>2Ftm(\<^bold>\<circle>f ts) = \<^bold>\<circle>(\<^bold>\<up>2sym f) (map \<^bold>\<up>2Ftm ts)\<close>
| \<open>\<^bold>\<up>2Ftm(\<^bold>\<star> c) = \<^bold>\<star> c\<close>

primrec inst_tm (\<open>\<llangle>_'/_\<rrangle>\<close>) where
  \<open>\<llangle>s/m\<rrangle>(\<^bold>#n) = (if n < m then \<^bold>#n else if n = m then s else \<^bold>#(n-1))\<close>
| \<open>\<llangle>s/m\<rrangle>(\<^bold>\<circle>f ts) = \<^bold>\<circle>f (map \<llangle>s/m\<rrangle> ts)\<close>
| \<open>\<llangle>s/m\<rrangle>(\<^bold>\<star>c) = \<^bold>\<star>c\<close>

primrec inst_sym (\<open>\<llangle>_'/_\<rrangle>2\<close>) where
  \<open>\<llangle>s/m\<rrangle>2 (\<^bold>#\<^sub>2 n) = (if n < m then \<^bold>#\<^sub>2 n else if n = m then s else \<^bold>#\<^sub>2 (n-1))\<close>
| \<open>\<llangle>s/m\<rrangle>2 (\<^bold>\<circle>\<^sub>2 p) = \<^bold>\<circle>\<^sub>2 p\<close>

primrec inst_tm2Ftm (\<open>\<langle>_'/_\<rangle>2Ftm\<close>) where
  \<open>\<langle>s/m\<rangle>2Ftm(\<^bold>#n) = (\<^bold>#n)\<close>
| \<open>\<langle>s/m\<rangle>2Ftm(\<^bold>\<circle>f ts) = \<^bold>\<circle>(\<llangle>s/m\<rrangle>2 f) (map \<langle>s/m\<rangle>2Ftm ts)\<close>
| \<open>\<langle>s/m\<rangle>2Ftm(\<^bold>\<star>c) = (\<^bold>\<star>c)\<close>

primrec inst_fm (\<open>\<langle>_'/_\<rangle>\<close>) where
  \<open>\<langle>_/_\<rangle>\<^bold>\<bottom> = \<^bold>\<bottom>\<close>
| \<open>\<langle>s/m\<rangle>(\<^bold>\<cdot>P ts) = \<^bold>\<cdot>P (map \<llangle>s/m\<rrangle> ts)\<close>
| \<open>\<langle>s/m\<rangle>(p \<^bold>\<longrightarrow> q) = \<langle>s/m\<rangle>p \<^bold>\<longrightarrow> \<langle>s/m\<rangle>q\<close>
| \<open>\<langle>s/m\<rangle>(\<^bold>\<forall>p) = \<^bold>\<forall>(\<langle>\<^bold>\<up>s/m+1\<rangle>p)\<close>
| \<open>\<langle>s/m\<rangle>(\<^bold>\<forall>\<^sub>Pp) = \<^bold>\<forall>\<^sub>P(\<langle>s/m\<rangle>p)\<close>
| \<open>\<langle>s/m\<rangle>(\<^bold>\<forall>\<^sub>Fp) = \<^bold>\<forall>\<^sub>F(\<langle>\<^bold>\<up>2Ftm s/m\<rangle>p)\<close> (* TODO: Når vi går ind under denne kvantor, så skal vi
                                rette funktions-variablene til, så de peger rigtigt.
                                Nu har jeg forsøgt at gøre det *)

primrec inst_fm2P (\<open>\<langle>_'/_\<rangle>2P\<close>) where
  \<open>\<langle>_/_\<rangle>2P\<^bold>\<bottom> = \<^bold>\<bottom>\<close>
| \<open>\<langle>s/m\<rangle>2P(\<^bold>\<cdot>P ts) = \<^bold>\<cdot>(\<llangle>s/m\<rrangle>2 P) ts\<close>
| \<open>\<langle>s/m\<rangle>2P(p \<^bold>\<longrightarrow> q) = \<langle>s/m\<rangle>2Pp \<^bold>\<longrightarrow> \<langle>s/m\<rangle>2Pq\<close>
| \<open>\<langle>s/m\<rangle>2P(\<^bold>\<forall>p) = \<^bold>\<forall>(\<langle>s/m\<rangle>2Pp)\<close>
| \<open>\<langle>s/m\<rangle>2P(\<^bold>\<forall>\<^sub>Pp) = \<^bold>\<forall>\<^sub>P(\<langle>\<^bold>\<up>2sym s/m+1\<rangle>2Pp)\<close>
| \<open>\<langle>s/m\<rangle>2P(\<^bold>\<forall>\<^sub>Fp) = \<^bold>\<forall>\<^sub>F(\<langle>s/m\<rangle>2Pp)\<close>

primrec inst_fm2F (\<open>\<langle>_'/_\<rangle>2Ffm\<close>) where
  \<open>\<langle>_/_\<rangle>2Ffm\<^bold>\<bottom> = \<^bold>\<bottom>\<close>
| \<open>\<langle>s/m\<rangle>2Ffm(\<^bold>\<cdot>P ts) = \<^bold>\<cdot>P (map \<langle>s/m\<rangle>2Ftm ts)\<close>
| \<open>\<langle>s/m\<rangle>2Ffm(p \<^bold>\<longrightarrow> q) = \<langle>s/m\<rangle>2Ffmp \<^bold>\<longrightarrow> \<langle>s/m\<rangle>2Ffmq\<close>
| \<open>\<langle>s/m\<rangle>2Ffm(\<^bold>\<forall>p) = \<^bold>\<forall>(\<langle>s/m\<rangle>2Ffmp)\<close>
| \<open>\<langle>s/m\<rangle>2Ffm(\<^bold>\<forall>\<^sub>Pp) = \<^bold>\<forall>\<^sub>P(\<langle>s/m\<rangle>2Ffmp)\<close>
| \<open>\<langle>s/m\<rangle>2Ffm(\<^bold>\<forall>\<^sub>Fp) = \<^bold>\<forall>\<^sub>F(\<langle>\<^bold>\<up>2sym s/m+1\<rangle>2Ffmp)\<close>

lemma lift_lemma [simp]: \<open>\<lparr>E\<langle>0:x\<rangle>, E2F, C, F\<rparr> (\<^bold>\<up>t) = \<lparr>E, E2F, C, F\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma lift_lemma2P [simp]: \<open>\<lparr>E2P\<langle>0:x\<rangle>, G\<rparr>2 (\<^bold>\<up>2sym P) = \<lparr>E2P, G\<rparr>2 P\<close>
  by (induct P) (auto cong: map_cong)

lemma lift_lemma2Ftm [simp]: \<open>\<lparr>E, E2F\<langle>0:x\<rangle>, C, F\<rparr> (\<^bold>\<up>2Ftm tm) = \<lparr>E, E2F, C, F\<rparr> tm\<close>
  by (induct tm) (auto cong: map_cong)

lemma inst_tm_semantics [simp]: \<open>\<lparr>E, E2F, C, F\<rparr> (\<llangle>s/m\<rrangle>t) = \<lparr>E\<langle>m:\<lparr>E, E2F, C, F\<rparr> s\<rangle>, E2F, C, F\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma inst_sym_semantics [simp]: \<open>\<lparr>E2F, G\<rparr>2 (\<llangle>s/m\<rrangle>2 fn) = \<lparr>E2F\<langle>m:\<lparr>E2F, G\<rparr>2 s\<rangle>, G\<rparr>2 fn\<close>
  by (induct fn) (auto cong: map_cong)

lemma inst_tm_semantics2 [simp]: \<open>\<lparr>E, E2F, C, F\<rparr> (\<langle>s/m\<rangle>2Ftm t) = \<lparr>E, E2F\<langle>m:\<lparr>E2F, F\<rparr>2 s\<rangle>, C, F\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma inst_fm_semantics''' [simp]:
   \<open>\<lbrakk>E, E2F, E2P, C, F, G, PS, FS\<rbrakk> (\<langle>t/m\<rangle>2Ffm p) = \<lbrakk>E, E2F\<langle>m:\<lparr>E2F, F\<rparr>2 t\<rangle>, E2P, C, F, G, PS, FS\<rbrakk> p\<close>
  by (induct p arbitrary: E E2P E2F m t) (auto cong: map_cong)


lemma inst_fm_semantics [simp]:
   \<open>\<lbrakk>E, E2F, E2P, C, F, G, PS, FS\<rbrakk> (\<langle>t/m\<rangle>p) = \<lbrakk>E\<langle>m:\<lparr>E, E2F, C, F\<rparr> t\<rangle>, E2F, E2P, C, F, G, PS, FS\<rbrakk> p\<close>
proof (induct p arbitrary: E E2P E2F m t)
  case Falsity
  then show ?case
    by auto
next
  case (Pre x1 x2)
  then show ?case 
    by (auto cong: map_cong)
next
  case (Imp p1 p2)
  then show ?case 
    by auto
next
  case (Uni p)
  then show ?case 
    by auto
next
  case (Uni2P p)
  then show ?case 
    by auto
next
  case (Uni2F p)
  then show ?case 
    by (auto cong: map_cong)
qed

lemma inst_fm_semantics2 [simp]: \<open>\<lbrakk>E, E2F, E2P, C, F, G, PS, FS\<rbrakk> (\<langle>P/m\<rangle>2Pp) = \<lbrakk>E, E2F, E2P\<langle>m:\<lparr>E2P, G\<rparr>2 P\<rangle>, C, F, G, PS, FS\<rbrakk> p\<close>
  by (induct p arbitrary: E E2F E2P m P) (auto cong: map_cong)

subsection \<open>Size\<close>

text \<open>The built-in \<open>size\<close> is not invariant under substitution.\<close>

primrec size_fm where
  \<open>size_fm \<^bold>\<bottom> = 1\<close>
| \<open>size_fm (\<^bold>\<cdot>_ _) = 1\<close>
| \<open>size_fm (p \<^bold>\<longrightarrow> q) = 1 + size_fm p + size_fm q\<close>
| \<open>size_fm (\<^bold>\<forall>p) = 1 + size_fm p\<close>
| \<open>size_fm (\<^bold>\<forall>\<^sub>Pp) = 1 + size_fm p\<close>
| \<open>size_fm (\<^bold>\<forall>\<^sub>Fp) = 1 + size_fm p\<close>

lemma size_inst_fm [simp]: \<open>size_fm (\<langle>t/m\<rangle>p) = size_fm p\<close>
  by (induct p arbitrary: m t) simp_all

lemma size_inst_fm2P [simp]: \<open>size_fm (\<langle>t/m\<rangle>2Pp) = size_fm p\<close>
  by (induct p arbitrary: m t) simp_all

lemma size_inst_fm2F [simp]: \<open>size_fm (\<langle>t/m\<rangle>2Ffmp) = size_fm p\<close>
  by (induct p arbitrary: m t) simp_all

section \<open>Propositional Semantics\<close>

(* TODO: put rules in for propositional connectives? *)

primrec boolean where
  \<open>boolean _ _ \<^bold>\<bottom> = False\<close>
| \<open>boolean G _ (\<^bold>\<cdot>P ts) = G P ts\<close>
| \<open>boolean G A (p \<^bold>\<longrightarrow> q) = (boolean G A p \<longrightarrow> boolean G A q)\<close>
| \<open>boolean _ A (\<^bold>\<forall>p) = A (\<^bold>\<forall>p)\<close>
| \<open>boolean _ A (\<^bold>\<forall>\<^sub>Pp) = A (\<^bold>\<forall>\<^sub>Pp)\<close>
| \<open>boolean _ A (\<^bold>\<forall>\<^sub>Fp) = A (\<^bold>\<forall>\<^sub>Fp)\<close>

abbreviation \<open>tautology p \<equiv> \<forall>G A. boolean G A p\<close>

proposition \<open>tautology (\<^bold>\<forall>(\<^bold>\<cdot>P [\<^bold>#0]) \<^bold>\<longrightarrow> \<^bold>\<forall>(\<^bold>\<cdot>P [\<^bold>#0]))\<close>
  by simp

lemma boolean_semantics: \<open>boolean (\<lambda>a. \<lparr>E2P,G\<rparr>2 a \<circ> map \<lparr>E, E2F, C, F\<rparr>) \<lbrakk>E, E2F, E2P, C, F, G, PS, FS\<rbrakk> = \<lbrakk>E, E2F, E2P, C, F, G, PS, FS\<rbrakk>\<close>
proof
  fix p
  show \<open>boolean (\<lambda>a. \<lparr>E2P,G\<rparr>2 a \<circ> map \<lparr>E, E2F, C, F\<rparr>) \<lbrakk>E, E2F, E2P, C, F, G, PS, FS\<rbrakk> p = \<lbrakk>E, E2F, E2P, C, F, G, PS, FS\<rbrakk> p\<close>
    by (induct p) simp_all
qed

lemma tautology[simp]: \<open>tautology p \<Longrightarrow> \<lbrakk>E, E2F, E2P, C, F, G, PS, FS\<rbrakk> p\<close>
  using boolean_semantics by metis

proposition \<open>\<exists>p. (\<forall>E E2F E2P F G PS FS. \<lbrakk>E, E2F, E2P, C, F, G, PS, FS\<rbrakk> p) \<and> \<not> tautology p\<close>
  by (metis boolean.simps(4) fun_upd_same semantics_fm.simps(3) semantics_fm.simps(4) tautology)


section \<open>Calculus\<close>

text \<open>Adapted from System Q1 by Smullyan in First-Order Logic (1968).\<close>

(* TODO: change to natural deduction? *)

inductive Axiomatic (\<open>\<turnstile> _\<close> [50] 50) where
  TA: \<open>tautology p \<Longrightarrow> \<turnstile> p\<close>
| IA: \<open>\<turnstile> \<^bold>\<forall>p \<^bold>\<longrightarrow> \<langle>t/0\<rangle>p\<close> 
| IA2P: \<open>\<turnstile> \<^bold>\<forall>\<^sub>Pp \<^bold>\<longrightarrow> \<langle>P/0\<rangle>2Pp\<close> 
| IA2F: \<open>\<turnstile> \<^bold>\<forall>\<^sub>Fp \<^bold>\<longrightarrow> \<langle>P/0\<rangle>2Ffmp\<close> 
| MP: \<open>\<turnstile> p \<^bold>\<longrightarrow> q \<Longrightarrow> \<turnstile> p \<Longrightarrow> \<turnstile> q\<close> 
| GR: \<open>\<turnstile> q \<^bold>\<longrightarrow> \<langle>\<^bold>\<star>a/0\<rangle>p \<Longrightarrow> a \<notin> params {p, q} \<Longrightarrow> \<turnstile> q \<^bold>\<longrightarrow> \<^bold>\<forall>p\<close> 
| GR2P: \<open>\<turnstile> q \<^bold>\<longrightarrow> \<langle>\<^bold>\<circle>\<^sub>2 P/0\<rangle>2Pp \<Longrightarrow> P \<notin> params {p, q} \<Longrightarrow> \<turnstile> q \<^bold>\<longrightarrow> \<^bold>\<forall>\<^sub>Pp\<close>
| GR2F: \<open>\<turnstile> q \<^bold>\<longrightarrow> \<langle>\<^bold>\<circle>\<^sub>2 P/0\<rangle>2Ffmp \<Longrightarrow> P \<notin> params {p, q} \<Longrightarrow> \<turnstile> q \<^bold>\<longrightarrow> \<^bold>\<forall>\<^sub>Fp\<close>

text \<open>We simulate assumptions on the lhs of \<open>\<turnstile>\<close> with a chain of implications on the rhs.\<close>

primrec imply (infixr \<open>\<^bold>\<leadsto>\<close> 56) where
  \<open>([] \<^bold>\<leadsto> q) = q\<close>
| \<open>(p # ps \<^bold>\<leadsto> q) = (p \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> q)\<close>

abbreviation Axiomatic_assms (\<open>_ \<turnstile> _\<close> [50, 50] 50) where
  \<open>ps \<turnstile> q \<equiv> \<turnstile> ps \<^bold>\<leadsto> q\<close>

section \<open>Soundness\<close>

theorem soundness:
  shows \<open>\<turnstile> p \<Longrightarrow> range G \<subseteq> PS \<Longrightarrow> range E2P \<subseteq> PS \<Longrightarrow> range F \<subseteq> FS \<Longrightarrow> range E2F \<subseteq> FS \<Longrightarrow> \<lbrakk>E, E2F, E2P, C, F, G, PS, FS\<rbrakk> p\<close>
proof (induct p arbitrary: C F G PS FS rule: Axiomatic.induct)
  case (TA p)
  then show ?case
    by simp 
next
  case (IA p t)
  then show ?case
    by auto
next
  case (IA2P p P)
  then show ?case
    apply (cases P)
    apply auto
     apply (meson rangeI subsetD)
    by (meson range_subsetD)
next
  case (IA2F p P)
  then show ?case
    apply  (cases P)
    apply auto
     apply (simp add: subset_eq)
    by (meson rangeI subsetD)
next
  case (MP p q)
  then show ?case
    by auto
next
  case (GR q a p)
  moreover from this have \<open>\<lbrakk>E, E2F, E2P, C(a := x), F, G, PS, FS\<rbrakk> (q \<^bold>\<longrightarrow> \<langle>\<^bold>\<star>a/0\<rangle>p)\<close> for x
    by blast
  ultimately show ?case
    by fastforce
next
  case (GR2P q P p)
  moreover from this have \<open>\<forall>x. x \<in> PS \<longrightarrow> \<lbrakk>E, E2F, E2P, C, F, G(P := x), PS,FS\<rbrakk> (q \<^bold>\<longrightarrow> \<langle>\<^bold>\<circle>\<^sub>2P/0\<rangle>2Pp)\<close>
    by (smt (verit, best) fun_upd_def imageE rev_image_eqI subset_eq)
  ultimately show ?case
    by fastforce
next
  case (GR2F q P p)
  moreover from this have \<open>\<forall>x. x \<in> FS \<longrightarrow> \<lbrakk>E, E2F, E2P, C, F(P := x), G, PS,FS\<rbrakk> (q \<^bold>\<longrightarrow> \<langle>\<^bold>\<circle>\<^sub>2P/0\<rangle>2Ffmp)\<close>
    by (smt (verit, best) fun_upd_def imageE rev_image_eqI subset_eq)
  ultimately show ?case
    by fastforce
qed

corollary \<open>\<not> (\<turnstile> \<^bold>\<bottom>)\<close>
  using soundness[of "\<^bold>\<bottom>" "\<lambda>p cs. True" "{\<lambda>cs. True}" "\<lambda>n cs. True" "\<lambda>p cs. ()"] by fastforce

section \<open>Derived Rules\<close>

lemma Imp1: \<open>\<turnstile> q \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> q\<close>
  and Imp2: \<open>\<turnstile> (p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> r\<close>
  and Neg: \<open>\<turnstile> \<^bold>\<not> \<^bold>\<not> p \<^bold>\<longrightarrow> p\<close>
  by (auto intro: TA)

text \<open>The tautology axiom TA is not used directly beyond this point.\<close>

lemma Tran': \<open>\<turnstile> (q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> r\<close>
  by (meson Imp1 Imp2 MP)

lemma Swap: \<open>\<turnstile> (p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> r\<close>
  by (meson Imp1 Imp2 Tran' MP)

lemma Tran: \<open>\<turnstile> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> (q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> r\<close>
  by (meson Swap Tran' MP)

text \<open>Note that contraposition in the other direction is an instance of the lemma Tran.\<close>

lemma contraposition: \<open>\<turnstile> (\<^bold>\<not> q \<^bold>\<longrightarrow> \<^bold>\<not> p) \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> q\<close>
  by (meson Neg Swap Tran MP)

lemma GR': \<open>\<turnstile> \<^bold>\<not> \<langle>\<^bold>\<star>a/0\<rangle>p \<^bold>\<longrightarrow> q \<Longrightarrow> a \<notin> params {p, q} \<Longrightarrow> \<turnstile> \<^bold>\<not> (\<^bold>\<forall>p) \<^bold>\<longrightarrow> q\<close>
proof -
  assume *: \<open>\<turnstile> \<^bold>\<not> \<langle>\<^bold>\<star>a/0\<rangle>p \<^bold>\<longrightarrow> q\<close> and a: \<open>a \<notin> params {p, q}\<close>
  have \<open>\<turnstile> \<^bold>\<not> q \<^bold>\<longrightarrow> \<^bold>\<not> \<^bold>\<not> \<langle>\<^bold>\<star>a/0\<rangle>p\<close>
    using * Tran MP by metis
  then have \<open>\<turnstile> \<^bold>\<not> q \<^bold>\<longrightarrow> \<langle>\<^bold>\<star>a/0\<rangle>p\<close>
    using Neg Tran MP by metis
  then have \<open>\<turnstile> \<^bold>\<not> q \<^bold>\<longrightarrow> \<^bold>\<forall>p\<close>
    using a by (auto intro: GR)
  then have \<open>\<turnstile> \<^bold>\<not> (\<^bold>\<forall>p) \<^bold>\<longrightarrow> \<^bold>\<not> \<^bold>\<not> q\<close>
    using Tran MP by metis
  then show ?thesis
    using Neg Tran MP by metis
qed

lemma GR'2P: \<open>\<turnstile> \<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2P/0\<rangle>2Pp \<^bold>\<longrightarrow> q \<Longrightarrow> P \<notin> params {p, q} \<Longrightarrow> \<turnstile> \<^bold>\<not> (\<^bold>\<forall>\<^sub>Pp) \<^bold>\<longrightarrow> q\<close>
proof -
  assume *: \<open>\<turnstile> \<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2P/0\<rangle>2Pp \<^bold>\<longrightarrow> q\<close> and a: \<open>P \<notin> params {p, q}\<close>
  have \<open>\<turnstile> \<^bold>\<not> q \<^bold>\<longrightarrow> \<^bold>\<not> \<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2P/0\<rangle>2Pp\<close>
    using * Tran MP by metis
  then have \<open>\<turnstile> \<^bold>\<not> q \<^bold>\<longrightarrow> \<langle>\<^bold>\<circle>\<^sub>2P/0\<rangle>2Pp\<close>
    using Neg Tran MP by metis
  then have \<open>\<turnstile> \<^bold>\<not> q \<^bold>\<longrightarrow> \<^bold>\<forall>\<^sub>Pp\<close>
    using a by (auto intro: GR2P)
  then have \<open>\<turnstile> \<^bold>\<not> (\<^bold>\<forall>\<^sub>Pp) \<^bold>\<longrightarrow> \<^bold>\<not> \<^bold>\<not> q\<close>
    using Tran MP by metis
  then show ?thesis
    using Neg Tran MP by metis
qed

lemma GR'2F: \<open>\<turnstile> \<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2F/0\<rangle>2Ffmp \<^bold>\<longrightarrow> q \<Longrightarrow> F \<notin> params {p, q} \<Longrightarrow> \<turnstile> \<^bold>\<not> (\<^bold>\<forall>\<^sub>Fp) \<^bold>\<longrightarrow> q\<close>
proof -
  assume *: \<open>\<turnstile> \<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2F/0\<rangle>2Ffmp \<^bold>\<longrightarrow> q\<close> and a: \<open>F \<notin> params {p, q}\<close>
  have \<open>\<turnstile> \<^bold>\<not> q \<^bold>\<longrightarrow> \<^bold>\<not> \<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2F/0\<rangle>2Ffmp\<close>
    using * Tran MP by metis
  then have \<open>\<turnstile> \<^bold>\<not> q \<^bold>\<longrightarrow> \<langle>\<^bold>\<circle>\<^sub>2F/0\<rangle>2Ffmp\<close>
    using Neg Tran MP by metis
  then have \<open>\<turnstile> \<^bold>\<not> q \<^bold>\<longrightarrow> \<^bold>\<forall>\<^sub>Fp\<close>
    using a by (auto intro: GR2F)
  then have \<open>\<turnstile> \<^bold>\<not> (\<^bold>\<forall>\<^sub>Fp) \<^bold>\<longrightarrow> \<^bold>\<not> \<^bold>\<not> q\<close>
    using Tran MP by metis
  then show ?thesis
    using Neg Tran MP by metis
qed

lemma imply_ImpE: \<open>\<turnstile> ps \<^bold>\<leadsto> p \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> q\<close>
proof (induct ps)
  case Nil
  then show ?case
    by (metis Imp1 Swap MP imply.simps(1))
next
  case (Cons r ps)
  have \<open>\<turnstile> (r \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> p) \<^bold>\<longrightarrow> r \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> q\<close>
    by (meson Cons.hyps Imp1 Imp2 MP)
  then have \<open>\<turnstile> (r \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> p) \<^bold>\<longrightarrow> (r \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> (p \<^bold>\<longrightarrow> q)) \<^bold>\<longrightarrow> r \<^bold>\<longrightarrow> ps \<^bold>\<leadsto> q\<close>
    by (meson Imp1 Imp2 MP)
  then show ?case
    by simp
qed

lemma MP': \<open>ps \<turnstile> p \<^bold>\<longrightarrow> q \<Longrightarrow> ps \<turnstile> p \<Longrightarrow> ps \<turnstile> q\<close>
  using imply_ImpE MP by metis

lemma imply_Cons [intro]: \<open>ps \<turnstile> q \<Longrightarrow> p # ps \<turnstile> q\<close>
  by (auto intro: MP Imp1)

lemma imply_head [intro]: \<open>p # ps \<turnstile> p\<close>
  by (induct ps) (metis Imp1 Imp2 MP imply.simps, metis Imp1 Imp2 MP imply.simps(2))

lemma add_imply [simp]: \<open>\<turnstile> q \<Longrightarrow> ps \<turnstile> q\<close>
  using imply_head by (metis MP imply.simps(2))

lemma imply_mem [simp]: \<open>p \<in> set ps \<Longrightarrow> ps \<turnstile> p\<close>
  using imply_head imply_Cons by (induct ps) fastforce+

lemma deduct1: \<open>ps \<turnstile> p \<^bold>\<longrightarrow> q \<Longrightarrow> p # ps \<turnstile> q\<close>
  by (meson MP' imply_Cons imply_head)

lemma imply_append [iff]: \<open>(ps @ qs \<^bold>\<leadsto> r) = (ps \<^bold>\<leadsto> qs \<^bold>\<leadsto> r)\<close>
  by (induct ps) simp_all

lemma imply_swap_append: \<open>ps @ qs \<turnstile> r \<Longrightarrow> qs @ ps \<turnstile> r\<close>
proof (induct qs arbitrary: ps)
  case Cons
  then show ?case
    by (metis deduct1 imply.simps(2) imply_append)
qed simp

lemma deduct2: \<open>p # ps \<turnstile> q \<Longrightarrow> ps \<turnstile> p \<^bold>\<longrightarrow> q\<close>
  by (metis imply.simps imply_append imply_swap_append)

lemmas deduct [iff] = deduct1 deduct2

lemma cut: \<open>p # ps \<turnstile> r \<Longrightarrow> q # ps \<turnstile> p \<Longrightarrow> q # ps \<turnstile> r\<close>
  by (meson MP' deduct(2) imply_Cons)

lemma Boole: \<open>(\<^bold>\<not> p) # ps \<turnstile> \<^bold>\<bottom> \<Longrightarrow> ps \<turnstile> p\<close>
  by (meson MP' Neg add_imply deduct(2))

lemma imply_weaken: \<open>ps \<turnstile> q \<Longrightarrow> set ps \<subseteq> set ps' \<Longrightarrow> ps' \<turnstile> q\<close>
  by (induct ps arbitrary: q) (simp, metis MP' deduct(2) imply_mem insert_subset list.simps(15))


section \<open>Model Existence\<close>

inductive confl_class :: \<open>'f fm list \<Rightarrow> 'f fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<crossmark>\<close> 50) where
  CFls: \<open>[ \<^bold>\<bottom> ] \<leadsto>\<^sub>\<crossmark> [ \<^bold>\<bottom> ]\<close>
| CNeg: \<open>[ \<^bold>\<not> (\<^bold>\<cdot>P ts) ] \<leadsto>\<^sub>\<crossmark> [ \<^bold>\<cdot>P ts ]\<close>

inductive alpha_class :: \<open>'f fm list \<Rightarrow> 'f fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<alpha>\<close> 50) where
  CImpN: \<open>[ \<^bold>\<not> (p \<^bold>\<longrightarrow> q) ] \<leadsto>\<^sub>\<alpha> [ p, \<^bold>\<not> q ]\<close>

inductive beta_class :: \<open>'f fm list \<Rightarrow> 'f fm list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<beta>\<close> 50) where
  CImpP: \<open>[ p \<^bold>\<longrightarrow> q ] \<leadsto>\<^sub>\<beta> [ \<^bold>\<not> p, q ]\<close>

inductive gamma_class_FO :: \<open>'f fm list \<Rightarrow>  ('f fm set \<Rightarrow> 'f tm set) \<times> ('f tm \<Rightarrow> 'f fm list) \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<gamma>\<^sub>F\<^sub>O\<close> 50) where
  CAllP: \<open>[ \<^bold>\<forall>p ] \<leadsto>\<^sub>\<gamma>\<^sub>F\<^sub>O (\<lambda>_. UNIV, \<lambda>t. [ \<langle>t/0\<rangle>p ])\<close>

inductive gamma_class_2P :: \<open>'f fm list \<Rightarrow> ('f fm set \<Rightarrow> 'f sym set) \<times> ('f sym \<Rightarrow> 'f fm list) \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<gamma>\<^sub>2\<^sub>P\<close> 50) where
  CAllPP: \<open>[ \<^bold>\<forall>\<^sub>P p ] \<leadsto>\<^sub>\<gamma>\<^sub>2\<^sub>P (\<lambda>_. UNIV, \<lambda>t. [ \<langle>t/0\<rangle>2P p ])\<close>

inductive gamma_class_2F :: \<open>'f fm list \<Rightarrow> ('f fm set \<Rightarrow> 'f sym set) \<times> ('f sym \<Rightarrow> 'f fm list) \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<gamma>\<^sub>2\<^sub>F\<close> 50) where
  CAllFP: \<open>[ \<^bold>\<forall>\<^sub>F p ] \<leadsto>\<^sub>\<gamma>\<^sub>2\<^sub>F (\<lambda>_. UNIV, \<lambda>t. [ \<langle>t/0\<rangle>2Ffm p ])\<close>

fun delta_fun :: \<open>'f fm \<Rightarrow> 'f \<Rightarrow> 'f fm list\<close> where
  CAllN:   \<open>delta_fun (\<^bold>\<not> \<^bold>\<forall>p) x = [ \<^bold>\<not> \<langle>\<^bold>\<star>x/0\<rangle>p ]\<close> 
| CAll2PN: \<open>delta_fun (\<^bold>\<not> \<^bold>\<forall>\<^sub>P p) x = [ \<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2 x/0\<rangle>2Pp ]\<close>
| CAll2FN: \<open>delta_fun ( \<^bold>\<not> \<^bold>\<forall>\<^sub>F p ) x = [ \<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2 x/0\<rangle>2Ffm  p ]\<close>
| NOMATCH: \<open>delta_fun _ _ = []\<close>

interpretation C: Confl map_fm params_fm confl_class
  by unfold_locales (auto simp: tm.map_id0 fm.map_id0 cong: tm.map_cong0 fm.map_cong0
      elim!: confl_class.cases intro: confl_class.intros) (* From PIL2 *)

interpretation A: Alpha map_fm params_fm alpha_class
  by unfold_locales (auto simp: fm.map_id0 cong: fm.map_cong0 elim!: alpha_class.cases intro: alpha_class.intros) (* From PIL2 *)

interpretation B: Beta map_fm params_fm beta_class
  by unfold_locales (auto simp: fm.map_id0 cong: fm.map_cong0 elim!: beta_class.cases intro: beta_class.intros) (* From PIL2 *)

lemma map_tm_inst_tm [simp]:
  "map_tm f (\<llangle>t/n\<rrangle> x) = \<llangle>map_tm f t/n\<rrangle> (map_tm f x)"
  by (induct x) simp_all

lemma map_tm_lift_tm [simp]: "map_tm f (\<^bold>\<up> t) = \<^bold>\<up> (map_tm f t)"
  by (induct t) simp_all

lemma map_sym_lift_tm2 [simp]: \<open>map_sym f (\<^bold>\<up>2sym t) = \<^bold>\<up>2sym (map_sym f t)\<close>
  by (induct t) auto

lemma map_tm_lift_tm2 [simp]: "map_tm f (\<^bold>\<up>2Ftm t) = \<^bold>\<up>2Ftm (map_tm f t)"
  by (induct t) simp_all

lemma map_fm_inst_single [simp]: \<open>map_fm f (\<langle>t/m\<rangle>p) = \<langle>map_tm f t/m\<rangle>(map_fm f p)\<close>
  by (induct p arbitrary: t m) simp_all

lemma map_sym_inst_sym [simp]: \<open>map_sym f (\<llangle>t/m\<rrangle>2 p) = \<llangle>map_sym f t/m\<rrangle>2 (map_sym f p)\<close>
  by (induct p arbitrary: t m) simp_all

lemma psub_inst_single' [simp]: \<open>map_fm f (\<langle>t/m\<rangle>2P p) = \<langle>map_sym f t/m\<rangle>2P(map_fm f p)\<close>
  by (induct p arbitrary: t m) simp_all

lemma map_tm_inst_tm2Ftm [simp]: \<open>map_tm f (\<langle>t/m\<rangle>2Ftm s) = \<langle>map_sym f t/m\<rangle>2Ftm (map_tm f s)\<close>
  by (induct s) auto

lemma psub_inst_single'' [simp]: \<open>map_fm f (\<langle>t/m\<rangle>2Ffm p) = \<langle>map_sym f t/m\<rangle>2Ffm(map_fm f p)\<close>
  by (induct p arbitrary: t m) simp_all

interpretation GFO: Gamma map_tm map_fm params_fm gamma_class_FO
  apply (unfold_locales)
  subgoal for ps F qs f
    apply (cases rule: gamma_class_FO.cases)
    apply auto
    subgoal for p
      apply (rule_tac x="\<lambda>_. UNIV" in exI)
      apply (rule_tac x="\<lambda>t. [\<langle>t/0\<rangle> (map_fm f p)]" in exI)
      apply auto
      subgoal
        using CAllP[of "(map_fm f p)"]
        apply auto
        done
      done
    done
  subgoal
    apply (fastforce elim: gamma_class_FO.cases) (* From PIL2 *)
    done
  subgoal
    apply (fastforce elim: gamma_class_FO.cases) (* From PIL2 *)
    done
  done

interpretation G2P: Gamma map_sym map_fm params_fm gamma_class_2P 
  apply (unfold_locales)
  subgoal for ps F qs f
    apply (cases rule: gamma_class_2P.cases)
    apply auto
    subgoal for p
      apply (rule_tac x="\<lambda>_. UNIV" in exI)
      apply (rule_tac x="\<lambda>t. [\<langle>t/0\<rangle>2P (map_fm f p)]" in exI)
      apply auto
      subgoal
        using CAllPP
        apply auto
        done
      done
    done
  subgoal
    apply (fastforce elim: gamma_class_2P.cases) (* From PIL2 *)
    done
  subgoal
    apply (fastforce elim: gamma_class_2P.cases) (* From PIL2 *)
    done
  done

interpretation G2F: Gamma map_sym map_fm params_fm gamma_class_2F
  apply (unfold_locales)
  subgoal for ps F qs f
    apply (cases rule: gamma_class_2F.cases)
     apply auto
    subgoal for p
      apply (rule_tac x="\<lambda>_. UNIV" in exI)
      apply (rule_tac x="\<lambda>t. [\<langle>t/0\<rangle>2Ffm (map_fm f p)]" in exI)
      apply auto
      subgoal
        using CAllFP
        apply auto
        done
      done
    done
  subgoal
    apply (fastforce elim: gamma_class_2F.cases) (* From PIL2 *)
    done
  subgoal
    apply (fastforce elim: gamma_class_2F.cases) (* From PIL2 *)
    done
  done

interpretation D: Delta map_fm params_fm delta_fun
proof
  show \<open>\<And>f. delta_fun (map_fm f p) (f x) = map (map_fm f) (delta_fun p x)\<close> for p :: \<open>'x fm\<close> and x
    by (induct p x rule: delta_fun.induct) simp_all
qed

abbreviation Kinds :: \<open>('x, 'x fm) kind list\<close> where
  \<open>Kinds \<equiv> [C.kind, A.kind, B.kind, GFO.kind, G2P.kind, G2F.kind, D.kind]\<close>

lemma CProp_Kinds:
  assumes \<open>CKind C.kind C\<close> \<open>CKind A.kind C\<close> \<open>CKind B.kind C\<close> \<open>CKind GFO.kind C\<close> \<open>CKind G2P.kind C\<close> \<open>CKind G2F.kind C\<close> \<open>CKind D.kind C\<close>
  shows \<open>CProp Kinds C\<close>
  unfolding CProp_def using assms by simp

interpretation Consistency_Prop map_fm params_fm Kinds
  using C.Consistency_Kind_axioms A.Consistency_Kind_axioms B.Consistency_Kind_axioms
    GFO.Consistency_Kind_axioms G2P.Consistency_Kind_axioms G2F.Consistency_Kind_axioms
    D.Consistency_Kind_axioms
  by (auto intro!: Consistency_Prop.intro C.Params_Fm_axioms simp: Consistency_Prop_axioms_def)

interpretation Maximal_Consistency_UNIV map_fm params_fm Kinds
proof
  show \<open>infinite (UNIV :: 'x fm set)\<close>
    using infinite_UNIV_size[of \<open>\<lambda>p. p \<^bold>\<longrightarrow> p\<close>] by simp
qed


section \<open>Model Existence\<close>

abbreviation henv2P where "henv2P H == \<lambda>n ts. \<^bold>\<cdot>(\<^bold>#\<^sub>2 n) ts \<in> H"

abbreviation hpred where "hpred H == \<lambda>P ts. \<^bold>\<cdot>(\<^bold>\<circle>\<^sub>2 P) ts \<in> H"

abbreviation hdomP where "hdomP H == range (henv2P H) \<union> range (hpred H)"

abbreviation henv2F where "henv2F == \<lambda>f. \<^bold>\<circle> (\<^bold>#\<^sub>2 f)"

abbreviation hfun where "hfun ==  \<lambda>f. \<^bold>\<circle> (\<^bold>\<circle>\<^sub>2 f)"

definition hdomF where "hdomF == range henv2F \<union> range hfun"

abbreviation (input) hmodel (\<open>\<lbrakk>_\<rbrakk>\<close>) where \<open>\<lbrakk>H\<rbrakk> \<equiv> \<lbrakk>\<^bold>#, henv2F, henv2P H, \<^bold>\<star>, hfun, hpred H, hdomP H, hdomF\<rbrakk>\<close>

lemma semantics_tm_id [simp]: \<open>\<lparr>\<^bold>#, henv2F , \<^bold>\<star> , \<lambda>f. \<^bold>\<circle> (\<^bold>\<circle>\<^sub>2 f) \<rparr> t = t\<close>
proof (induct t)
  case (Var x)
  then show ?case 
    by (auto cong: map_cong)
next
  case (Fun x1a x2)
  then show ?case
    by (cases x1a) (auto cong: map_cong)
next
  case (Cst c)
  then show ?case
    by auto
qed

lemma semantics_tm_id_map [simp]: \<open>map \<lparr>\<^bold>#, \<lambda>f. \<^bold>\<circle> (\<^bold>#\<^sub>2 f) , \<^bold>\<star>, \<lambda>f. \<^bold>\<circle> (\<^bold>\<circle>\<^sub>2 f) \<rparr> ts = ts\<close>
  by (auto cong: map_cong)

lemma semantics_fn_h [simp]: \<open>\<lparr>henv2P S, hpred S\<rparr>2 P ts \<longleftrightarrow> \<^bold>\<cdot>P ts \<in> S\<close>
  by (cases P) simp_all

lemma hdomP_range: \<open>hdomP S \<subseteq> range \<lparr>henv2P S, hpred S\<rparr>2\<close>
  by fastforce

locale MyHintikka = Hintikka map_fm params_fm Kinds S for S :: \<open>'x fm set\<close>
begin

lemmas
  confl = hkind[of C.kind] and
  alpha = hkind[of A.kind] and
  beta = hkind[of B.kind] and
  gammaFO = hkind[of GFO.kind] and
  gamma2P = hkind[of G2P.kind] and
  gamma2F = hkind[of G2F.kind] and
  delta = hkind[of D.kind]


theorem model: \<open>(p \<in> S \<longrightarrow> \<lbrakk>S\<rbrakk> p) \<and> (\<^bold>\<not> p \<in> S \<longrightarrow> \<not> \<lbrakk>S\<rbrakk> p)\<close>
proof (induct p rule: wf_induct[where r=\<open>measure size_fm\<close>])
  case 1
  then show ?case
    by simp
next
  case (2 x)
  then show ?case
  proof (cases x)
    case Falsity
    then show ?thesis
      using confl by (force intro: CFls)
  next
    case (Pre P ts)
    then show ?thesis
    proof (safe del: notI)
      assume \<open>x = \<^bold>\<cdot>P ts\<close> \<open>\<^bold>\<cdot>P ts \<in> S\<close>
      then show \<open>\<lbrakk>S\<rbrakk> (\<^bold>\<cdot>P ts)\<close>
        by simp
    next
      assume \<open>x = \<^bold>\<cdot>P ts\<close> \<open>\<^bold>\<not> \<^bold>\<cdot>P ts \<in> S\<close>
      then have \<open>\<^bold>\<cdot>P ts \<notin> S\<close>
        using confl by (force intro: CNeg)
      then show \<open>\<not> \<lbrakk>S\<rbrakk> (\<^bold>\<cdot>P ts)\<close>
        by simp
    qed
  next
    case (Imp p q)
    then show ?thesis
    proof (safe del: notI)
      assume \<open>x = p \<^bold>\<longrightarrow> q\<close> \<open>p \<^bold>\<longrightarrow> q \<in> S\<close>
      then have \<open>\<^bold>\<not> p \<in> S \<or> q \<in> S\<close>
        using beta by (force intro: CImpP)
      then show \<open>\<lbrakk>S\<rbrakk> (p \<^bold>\<longrightarrow> q)\<close>
        using 2 Imp by auto
    next
      assume \<open>x = p \<^bold>\<longrightarrow> q\<close> \<open>\<^bold>\<not> (p \<^bold>\<longrightarrow> q) \<in> S\<close>
      then have \<open>p \<in> S \<and> \<^bold>\<not> q \<in> S\<close>
        using alpha by (force intro: CImpN)
      then show \<open>\<not> \<lbrakk>S\<rbrakk> (p \<^bold>\<longrightarrow> q)\<close>
        using 2 Imp by auto
    qed
  next
    case (Uni p)
    then show ?thesis
    proof (safe del: notI)
      assume \<open>x = \<^bold>\<forall>p\<close> \<open>\<^bold>\<forall>p \<in> S\<close>
      then have \<open>\<forall>t. \<langle>t/0\<rangle>p \<in> S\<close>
        using gammaFO by (fastforce intro: CAllP)
      moreover have \<open>\<forall>t. (\<langle>t/0\<rangle>p, \<^bold>\<forall>p) \<in> measure size_fm\<close>
        by simp
      ultimately have \<open>\<forall>t. \<lbrakk>S\<rbrakk> (\<langle>t/0\<rangle>p)\<close>
        using 2 \<open>x = \<^bold>\<forall>p\<close> by blast
      then show \<open>\<lbrakk>S\<rbrakk> (\<^bold>\<forall>p)\<close>
        by simp
    next
      assume \<open>x = \<^bold>\<forall>p\<close> \<open>\<^bold>\<not> \<^bold>\<forall>p \<in> S\<close>
      then obtain a where \<open>\<^bold>\<not> \<langle>\<^bold>\<star>a/0\<rangle>p \<in> S\<close>
        using delta by auto
      moreover have \<open>(\<langle>\<^bold>\<star>a/0\<rangle>p, \<^bold>\<forall>p) \<in> measure size_fm\<close>
        by simp
      ultimately have \<open>\<not> \<lbrakk>S\<rbrakk> (\<langle>\<^bold>\<star>a/0\<rangle>p)\<close>
        using 2 \<open>x = \<^bold>\<forall>p\<close> by blast
      then show \<open>\<not> \<lbrakk>S\<rbrakk> (\<^bold>\<forall>p)\<close>
        by auto
    qed
  next
    case (Uni2P p)
    then show ?thesis
    proof (safe del: notI)
      assume \<open>x = \<^bold>\<forall>\<^sub>P p\<close> \<open>\<^bold>\<forall>\<^sub>P p \<in> S\<close>
      then have \<open>\<forall>t. \<langle>t/0\<rangle>2P p \<in> S\<close>
        using gamma2P by (fastforce intro: CAllPP)
      moreover have \<open>\<forall>t. (\<langle>t/0\<rangle>2P p, \<^bold>\<forall>\<^sub>P p) \<in> measure size_fm\<close>
        by simp
      ultimately have \<open>\<forall>t. \<lbrakk>S\<rbrakk> (\<langle>t/0\<rangle>2P p)\<close>
        using 2 \<open>x = \<^bold>\<forall>\<^sub>P p\<close> by blast
      then show \<open>\<lbrakk>S\<rbrakk> (\<^bold>\<forall>\<^sub>P p)\<close>
        (* TODO: I don't know what the required lemma is here *)
        apply auto
        subgoal for n
          by (metis semantics_fn.simps(1))
        subgoal for e
          by (metis semantics_fn.simps(2))
      done
    next
      assume \<open>x = \<^bold>\<forall>\<^sub>P p\<close> \<open>\<^bold>\<not> \<^bold>\<forall>\<^sub>P p \<in> S\<close>
      then obtain a where \<open>\<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2 a/0\<rangle>2P p \<in> S\<close>
        using delta by auto
      moreover have \<open>(\<langle>\<^bold>\<circle>\<^sub>2 a/0\<rangle>2P p, \<^bold>\<forall>\<^sub>P p) \<in> measure size_fm\<close>
        by simp
      ultimately have \<open>\<not> \<lbrakk>S\<rbrakk> (\<langle>\<^bold>\<circle>\<^sub>2a/0\<rangle>2P p)\<close>
        using 2 \<open>x = \<^bold>\<forall>\<^sub>P p\<close> by blast
      then show \<open>\<not> \<lbrakk>S\<rbrakk> (\<^bold>\<forall>\<^sub>P p)\<close>
        by auto
    qed
  next
    case (Uni2F p)
    then show ?thesis
    proof (safe del: notI)
      assume \<open>x = \<^bold>\<forall>\<^sub>F p\<close> \<open>\<^bold>\<forall>\<^sub>F p \<in> S\<close>
      then have \<open>\<forall>t. \<langle>t/0\<rangle>2Ffm p \<in> S\<close>
        using gamma2F by (fastforce intro: CAllFP)
      moreover have \<open>\<forall>t. (\<langle>t/0\<rangle>2Ffm p, \<^bold>\<forall>\<^sub>F p) \<in> measure size_fm\<close>
        by simp
      ultimately have \<open>\<forall>t. \<lbrakk>S\<rbrakk> (\<langle>t/0\<rangle>2Ffm p)\<close>
        using 2 \<open>x = \<^bold>\<forall>\<^sub>F p\<close> by blast
      then show \<open>\<lbrakk>S\<rbrakk> (\<^bold>\<forall>\<^sub>F p)\<close>
        unfolding hdomF_def
          (* TODO: I don't know what the required lemma is here *)
        apply auto
        subgoal for f
          by (metis semantics_fn.simps(1))
        subgoal for e
          by (metis semantics_fn.simps(2))
        done
    next
      assume \<open>x = \<^bold>\<forall>\<^sub>F p\<close> \<open>\<^bold>\<not> \<^bold>\<forall>\<^sub>F p \<in> S\<close>
      then obtain a where \<open>\<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2 a/0\<rangle>2Ffm p \<in> S\<close>
        using delta by auto
      moreover have \<open>(\<langle>\<^bold>\<circle>\<^sub>2 a/0\<rangle>2Ffm p, \<^bold>\<forall>\<^sub>F p) \<in> measure size_fm\<close>
        by simp
      ultimately have \<open>\<not> \<lbrakk>S\<rbrakk> (\<langle>\<^bold>\<circle>\<^sub>2a/0\<rangle>2Ffm p)\<close>
        using 2 \<open>x = \<^bold>\<forall>\<^sub>F p\<close> by blast
      then show \<open>\<not> \<lbrakk>S\<rbrakk> (\<^bold>\<forall>\<^sub>F p)\<close>
        by (auto simp: hdomF_def)
    qed
  qed
qed

end

theorem model_existence:
  fixes S :: \<open>'x fm set\<close>
  assumes \<open>CProp Kinds C\<close>
    and \<open>S \<in> C\<close>
    and \<open>|UNIV :: 'x fm set| \<le>o |- C.params S|\<close>
    and \<open>p \<in> S\<close>
  shows \<open>\<lbrakk>mk_mcs C S\<rbrakk> p\<close>
proof -
  have *: \<open>MyHintikka (mk_mcs C S)\<close>
  proof
    show \<open>HProp Kinds (mk_mcs C S)\<close>
      using mk_mcs_Hintikka[OF assms(1-3)] Hintikka.hintikka by blast
  qed
  moreover have \<open>p \<in> mk_mcs C S\<close>
    using assms(4) Extend_subset by blast
  ultimately show ?thesis
    using MyHintikka.model by blast
qed

section \<open>Derivational Consistency\<close>

interpretation DC: Weak_Derivational_Confl map_fm params_fm confl_class \<open>\<lambda>A. A \<turnstile> \<^bold>\<bottom>\<close>
proof
  fix A ps qs and q :: \<open>'x fm\<close>
  assume \<open>ps \<leadsto>\<^sub>\<crossmark> qs\<close> \<open>set ps \<subseteq> set A\<close> \<open>q \<in> set qs\<close> \<open>q \<in> set A\<close>
  then show \<open>A \<turnstile> \<^bold>\<bottom>\<close>
    apply cases
     apply simp
    by (metis MP' empty_set equals0D imply_head imply_mem imply_weaken set_ConsD)
qed

interpretation DA: Weak_Derivational_Alpha map_fm params_fm alpha_class \<open>\<lambda>A. A \<turnstile> \<^bold>\<bottom>\<close>
proof
  fix A and ps qs :: \<open>'x fm list\<close>
  assume \<open>ps \<leadsto>\<^sub>\<alpha> qs\<close> and *: \<open>set ps \<subseteq> set A\<close> \<open>qs @ A \<turnstile> \<^bold>\<bottom>\<close>
  then show \<open>A \<turnstile> \<^bold>\<bottom>\<close>
  proof cases
    case (CImpN p q)
    then have \<open>A \<turnstile> \<^bold>\<not> (p \<^bold>\<longrightarrow> q)\<close>
      using *(1) by simp
    moreover have \<open>A \<turnstile> p \<^bold>\<longrightarrow> q\<close>
      using CImpN(2) *(2) Boole[of q]
      by (metis deduct2 imply.simps(1) imply.simps(2) imply_append)
    ultimately show ?thesis
      using MP' by blast
  qed
qed

interpretation DB: Weak_Derivational_Beta map_fm params_fm beta_class \<open>\<lambda>A. A \<turnstile> \<^bold>\<bottom>\<close>
proof
  fix A and ps qs :: \<open>'x fm list\<close>
  assume \<open>ps \<leadsto>\<^sub>\<beta> qs\<close> and *: \<open>set ps \<subseteq> set A\<close> \<open>\<forall>q \<in> set qs. q # A \<turnstile> \<^bold>\<bottom>\<close>
  then show \<open>A \<turnstile> \<^bold>\<bottom>\<close>
  proof cases
    case (CImpP p q)
    then show ?thesis
      using * Boole[of p A]
      by (metis MP' deduct2 imply_head imply_weaken insertI2 list.set_intros(1) list.simps(15))
  qed
qed

interpretation DGFO: Weak_Derivational_Gamma map_tm map_fm params_fm gamma_class_FO \<open>\<lambda>A. A \<turnstile> \<^bold>\<bottom>\<close>
proof
  fix A F qs t and ps :: \<open>'x fm list\<close>
  assume \<open>ps \<leadsto>\<^sub>\<gamma>\<^sub>F\<^sub>O (F, qs)\<close> and *: \<open>set ps \<subseteq> set A\<close> \<open>qs t @ A \<turnstile> \<^bold>\<bottom>\<close>
  then show \<open>A \<turnstile> \<^bold>\<bottom>\<close>
  proof cases
    case (CAllP p)
    then show ?thesis
      using * IA[of p t] MP'
      by (metis (mono_tags, lifting) imply.simps(1-2) imply_append imply_swap_append imply_weaken)
  qed
qed

interpretation DG2P: Weak_Derivational_Gamma map_sym map_fm params_fm gamma_class_2P \<open>\<lambda>A. A \<turnstile> \<^bold>\<bottom>\<close>
proof
  fix A F qs t and ps :: \<open>'x fm list\<close>
  assume \<open>ps \<leadsto>\<^sub>\<gamma>\<^sub>2\<^sub>P (F, qs)\<close> and *: \<open>set ps \<subseteq> set A\<close> \<open>qs t @ A \<turnstile> \<^bold>\<bottom>\<close>
  then show \<open>A \<turnstile> \<^bold>\<bottom>\<close>
  proof cases
    case (CAllPP p)
    then show ?thesis
      using * IA2P[of p t] MP'
      by (metis (mono_tags, lifting) imply.simps(1-2) imply_append imply_swap_append imply_weaken)
  qed
qed

interpretation DG2F: Weak_Derivational_Gamma map_sym map_fm params_fm gamma_class_2F \<open>\<lambda>A. A \<turnstile> \<^bold>\<bottom>\<close>
proof
  fix A F qs t and ps :: \<open>'x fm list\<close>
  assume \<open>ps \<leadsto>\<^sub>\<gamma>\<^sub>2\<^sub>F (F, qs)\<close> and *: \<open>set ps \<subseteq> set A\<close> \<open>qs t @ A \<turnstile> \<^bold>\<bottom>\<close>
  then show \<open>A \<turnstile> \<^bold>\<bottom>\<close>
  proof cases
    case (CAllFP p)
    then show ?thesis
      using * IA2F[of p t] MP'
      by (metis (mono_tags, lifting) imply.simps(1-2) imply_append imply_swap_append imply_weaken)
  qed
qed

lemma imply_params_fm: \<open>params_fm (ps \<^bold>\<leadsto> q) = params_fm q \<union> (\<Union>p \<in> set ps. params_fm p)\<close>
  by (induct ps) auto

interpretation DD: Weak_Derivational_Delta map_fm params_fm delta_fun \<open>\<lambda>A. A \<turnstile> \<^bold>\<bottom>\<close>
proof
  fix A a and p :: \<open>'x fm\<close>
  assume \<open>p \<in> set A\<close> \<open>a \<notin> C.params (set A)\<close> \<open>delta_fun p a @ A \<turnstile> \<^bold>\<bottom>\<close>
  then show \<open>A \<turnstile> \<^bold>\<bottom>\<close>
  proof (induct p a rule: delta_fun.induct)
    case (1 p x)
    have \<open>x \<notin> C.params {p, A \<^bold>\<leadsto> \<^bold>\<bottom>}\<close>
      using 1(1-2) imply_params_fm[of A \<open>\<^bold>\<bottom>\<close>] by auto
    moreover have \<open>\<^bold>\<not> \<langle>\<^bold>\<star>x/0\<rangle>p # A \<turnstile> \<^bold>\<bottom>\<close>
      using 1(3) by simp
    ultimately have \<open>\<^bold>\<not> \<^bold>\<forall>p # A \<turnstile> \<^bold>\<bottom>\<close>
      using GR'[of x p] by simp
    then show ?thesis
      using 1(1) by (meson Boole MP' imply_mem)
  next
    case (2 p x)
    have \<open>x \<notin> C.params {p, A \<^bold>\<leadsto> \<^bold>\<bottom>}\<close>
      using 2(1-2) imply_params_fm[of A \<open>\<^bold>\<bottom>\<close>] by auto
    moreover have \<open>\<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2 x/0\<rangle>2P p # A \<turnstile> \<^bold>\<bottom>\<close>
      using 2(3) by simp
    ultimately have \<open>\<^bold>\<not> \<^bold>\<forall>\<^sub>P p # A \<turnstile> \<^bold>\<bottom>\<close>
      using GR'2P[of x p] by simp
    then show ?thesis
      using 2(1) by (meson Boole MP' imply_mem)
  next
    case (3 p x)
    have \<open>x \<notin> C.params {p, A \<^bold>\<leadsto> \<^bold>\<bottom>}\<close>
      using 3(1-2) imply_params_fm[of A \<open>\<^bold>\<bottom>\<close>] by auto
    moreover have \<open>\<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2 x/0\<rangle>2Ffm p # A \<turnstile> \<^bold>\<bottom>\<close>
      using 3(3) by simp
    ultimately have \<open>\<^bold>\<not> \<^bold>\<forall>\<^sub>F p # A \<turnstile> \<^bold>\<bottom>\<close>
      using GR'2F[of x p] by simp
    then show ?thesis
      using 3(1) by (meson Boole MP' imply_mem)
  qed simp_all
qed

interpretation Weak_Derivational_Consistency map_fm params_fm Kinds \<open>|UNIV|\<close> \<open>\<lambda>A. A \<turnstile> \<^bold>\<bottom>\<close>
proof
  assume inf: \<open>infinite (UNIV :: 'x set)\<close>
  then
  show \<open>CProp Kinds {S :: 'x fm set. \<exists>A. set A = S \<and> \<not> A \<turnstile> \<^bold>\<bottom>}\<close>
    using CProp_Kinds[OF DC.kind[OF inf] DA.kind DB.kind DGFO.kind DG2P.kind DG2F.kind DD.kind]
    by blast
qed

theorem weak_completeness:
  fixes p :: \<open>'x fm\<close>
  assumes mod: \<open>\<forall>(E :: _ \<Rightarrow> 'x tm) E2F E2P C F G PS FS. range E2F \<subseteq> FS \<longrightarrow> range E2P \<subseteq> PS \<longrightarrow> range G \<subseteq> PS \<longrightarrow> range F \<subseteq> FS \<longrightarrow> (\<forall>q \<in> set ps. \<lbrakk>E, E2F, E2P, C, F, G, PS, FS\<rbrakk> q) \<longrightarrow> \<lbrakk>E, E2F, E2P, C, F, G, PS, FS\<rbrakk> p\<close>
    and inf: \<open>|UNIV :: 'x fm set| \<le>o  |- C.params (set ps)|\<close>
  shows \<open>ps \<turnstile> p\<close>
proof (rule ccontr)
  assume \<open>\<not> ps \<turnstile> p\<close>
  then have *: \<open>\<not> (\<^bold>\<not> p) # ps \<turnstile> \<^bold>\<bottom>\<close>
    using Boole by blast

  let ?S = \<open>set (\<^bold>\<not> p # ps)\<close>
  let ?C = \<open>{S :: 'x fm set. \<exists>A. set A = S \<and> \<not> A \<turnstile> \<^bold>\<bottom>}\<close>
  let ?M = \<open>\<lbrakk>mk_mcs ?C ?S\<rbrakk>\<close>

  have \<open>infinite (UNIV :: 'x set)\<close>
    using inf card_of_ordLeq_infinite finite_subset inf_UNIV subset_UNIV by blast
  then have \<open>CProp Kinds ?C\<close>
    using Consistency by blast
  moreover have \<open>?S \<in> ?C\<close>
    using * by blast
  moreover have \<open>|UNIV :: 'x fm set| \<le>o |- C.params ?S|\<close>
    using inf by (metis UN_insert finite_params_fm inf_univ infinite_left list.simps(15))
  ultimately have *: \<open>\<forall>p \<in> ?S. ?M p\<close>
    using model_existence by blast 
  then have \<open>?M p\<close>
    using mod unfolding hdomF_def by auto
  then show False
    using * by simp
qed

theorem completeness:
  fixes p :: \<open>'x fm\<close>
  assumes \<open>\<forall>(E :: nat \<Rightarrow> 'x tm) E2P E2F C F G PS FS. range E2F \<subseteq> FS \<longrightarrow> range E2P \<subseteq> PS \<longrightarrow> range G \<subseteq> PS \<longrightarrow> range F \<subseteq> FS \<longrightarrow> \<lbrakk>E, E2F, E2P, C, F, G, PS, FS\<rbrakk> p\<close>
    and \<open>|UNIV :: 'x fm set| \<le>o  |UNIV :: 'x set|\<close>
  shows \<open>\<turnstile> p\<close>
  using assms weak_completeness[where ps=\<open>[]\<close>, of p] by simp

end

(*

section \<open>Hmm\<close>

locale Strong
begin

abbreviation Axiomatic_set (infix \<open>\<tturnstile>\<close> 50) where
  \<open>A \<tturnstile> q \<equiv> \<exists>ps. set ps \<subseteq> A \<and> ps \<turnstile> q\<close>

lemma Clas:
  assumes \<open>(p \<^bold>\<longrightarrow> q) # A \<turnstile> p\<close>
  shows \<open>A \<turnstile> p\<close>
proof -
  have \<open>tautology ((((p \<^bold>\<longrightarrow> q) # A) \<^bold>\<leadsto> p) \<^bold>\<longrightarrow> (A \<^bold>\<leadsto> p))\<close>
    by (induct A) auto
  then have \<open>\<turnstile> ((p \<^bold>\<longrightarrow> q) # A) \<^bold>\<leadsto> p \<^bold>\<longrightarrow> (A \<^bold>\<leadsto> p)\<close>
    using TA by blast
  then show ?thesis
    using MP assms by blast
qed

lemma FlsE: \<open>A \<turnstile> \<^bold>\<bottom> \<Longrightarrow> A \<turnstile> p\<close>
  using Boole imply_Cons by blast

lemma Boole_set:
  assumes \<open>{\<^bold>\<not> p} \<union> A \<tturnstile> \<^bold>\<bottom>\<close>
  shows \<open>A \<tturnstile> p\<close>
proof -
  obtain ps where ps: \<open>ps \<turnstile> \<^bold>\<bottom>\<close> \<open>set ps \<subseteq> {\<^bold>\<not> p} \<union> A\<close>
    using assms by blast
  then have \<open>\<^bold>\<not> p # removeAll (\<^bold>\<not> p) ps \<turnstile> \<^bold>\<bottom>\<close>
    by (metis imply_weaken insert_Diff insert_absorb2 list.simps(15) removeAll_id set_removeAll subset_insertI)
  then have \<open>removeAll (\<^bold>\<not> p) ps \<turnstile> p\<close>
    using Boole by blast
  then show ?thesis
    by (metis Diff_subset_conv ps(2) set_removeAll)
qed

lemma deduct_set: \<open>{p} \<union> A \<tturnstile> q \<Longrightarrow> A \<tturnstile> p \<^bold>\<longrightarrow> q\<close>
proof -
  assume \<open>{p} \<union> A \<tturnstile> q\<close>
  then obtain ps where ps: \<open>ps \<turnstile> q\<close> \<open>set ps \<subseteq> {p} \<union> A\<close>
    by blast
  then have \<open>p # removeAll p ps \<turnstile> q\<close>
    by (metis imply_weaken insert_Diff insert_absorb2 list.simps(15) removeAll_id set_removeAll subset_insertI)
  then have \<open>removeAll p ps \<turnstile> p \<^bold>\<longrightarrow> q\<close>
    by blast
  then show ?thesis
    by (metis Diff_subset_conv ps(2) set_removeAll)
qed

lemma FlsI_set: \<open>A \<tturnstile> p \<Longrightarrow> A \<tturnstile> \<^bold>\<not> p \<Longrightarrow> A \<tturnstile> \<^bold>\<bottom>\<close>
proof -
  assume \<open>A \<tturnstile> p\<close> \<open>A \<tturnstile> \<^bold>\<not> p\<close>
  then obtain ps qs where
    ps: \<open>ps \<turnstile> p\<close> \<open>set ps \<subseteq> A\<close> and
    qs: \<open>qs \<turnstile> \<^bold>\<not> p\<close> \<open>set qs \<subseteq> A\<close>
    by blast
  then have \<open>ps @ qs \<turnstile> p\<close> \<open>ps @ qs \<turnstile> \<^bold>\<not> p\<close>
    apply (metis imply_weaken set_append sup_ge1)
    by (simp add: qs(1))
  then have \<open>ps @ qs \<turnstile> \<^bold>\<bottom>\<close>
    using MP' by blast
  then show ?thesis
    using ps qs by (metis set_append sup.boundedI)
qed

interpretation DC: Derivational_Confl map_fm params_fm confl_class \<open>\<lambda>A. A \<tturnstile> \<^bold>\<bottom>\<close>
proof
  fix A ps qs and q :: \<open>'x fm\<close>
  assume \<open>ps \<leadsto>\<^sub>\<crossmark> qs\<close> \<open>set ps \<subseteq> A\<close> \<open>q \<in> set qs\<close> \<open>q \<in> A\<close>
  then show \<open>A \<tturnstile> \<^bold>\<bottom>\<close>
    apply cases
     apply blast
    by (metis deduct1 empty_iff empty_set imply_head insert_subset list.simps(15) set_ConsD)
qed

interpretation DA: Derivational_Alpha map_fm params_fm alpha_class \<open>\<lambda>A. A \<tturnstile> \<^bold>\<bottom>\<close>
proof
  fix A and ps qs :: \<open>'x fm list\<close>
  assume \<open>ps \<leadsto>\<^sub>\<alpha> qs\<close> and *: \<open>set ps \<subseteq> A\<close> \<open>set qs \<union> A \<tturnstile> \<^bold>\<bottom>\<close>
  then show \<open>A \<tturnstile> \<^bold>\<bottom>\<close>
  proof cases
    case (CImpN p q)
    then have \<open>A \<tturnstile> \<^bold>\<not> (p \<^bold>\<longrightarrow> q)\<close>
      using *(1) by blast
    moreover have \<open>{p} \<union> A \<tturnstile> q\<close>
      using CImpN(2) *(2) Boole_set[of q \<open>{p} \<union> A\<close>] by simp
    then have \<open>A \<tturnstile> p \<^bold>\<longrightarrow> q\<close>
      using deduct_set[of p] by blast
    ultimately show ?thesis
      using FlsI_set by blast
  qed
qed


interpretation DB: Derivational_Beta map_fm params_fm beta_class \<open>\<lambda>A. A \<tturnstile> \<^bold>\<bottom>\<close>
proof
  fix A and ps qs :: \<open>'x fm list\<close>
  assume \<open>ps \<leadsto>\<^sub>\<beta> qs\<close> and *: \<open>set ps \<subseteq> A\<close> \<open>\<forall>q \<in> set qs. {q} \<union> A \<tturnstile> \<^bold>\<bottom>\<close>
  then show \<open>A \<tturnstile> \<^bold>\<bottom>\<close>
  proof cases
    case (CImpP p q)
    then show ?thesis
      using * Boole_set[of p A] sorry
  qed
qed

end

(***** OLD ******)

section \<open>Consistent\<close>

definition \<open>consistent S \<equiv> \<nexists>S'. set S' \<subseteq> S \<and> S' \<turnstile> \<^bold>\<bottom>\<close>

lemma UN_finite_bound:
  assumes \<open>finite A\<close> and \<open>A \<subseteq> (\<Union>n. f n)\<close>
  shows \<open>\<exists>m :: nat. A \<subseteq> (\<Union>n \<le> m. f n)\<close>
  using assms
proof (induct rule: finite_induct)
  case (insert x A)
  then obtain m where \<open>A \<subseteq> (\<Union>n \<le> m. f n)\<close>
    by fast
  then have \<open>A \<subseteq> (\<Union>n \<le> (m + k). f n)\<close> for k
    by fastforce
  moreover obtain m' where \<open>x \<in> f m'\<close>
    using insert(4) by blast
  ultimately have \<open>{x} \<union> A \<subseteq> (\<Union>n \<le> m + m'. f n)\<close>
    by auto
  then show ?case
    by blast
qed simp

lemma split_list:
  assumes \<open>x \<in> set A\<close>
  shows \<open>set (x # removeAll x A) = set A \<and> x \<notin> set (removeAll x A)\<close>
  using assms by auto

lemma imply_params_fm: \<open>params_fm (ps \<^bold>\<leadsto> q) = params_fm q \<union> (\<Union>p \<in> set ps. params_fm p)\<close>
  by (induct ps) auto

lemma inconsistent_fm:
  assumes \<open>consistent S\<close> and \<open>\<not> consistent ({p} \<union> S)\<close>
  obtains S' where \<open>set S' \<subseteq> S\<close> and \<open>p # S' \<turnstile> \<^bold>\<bottom>\<close>
proof -
  obtain S' where S': \<open>set S' \<subseteq> {p} \<union> S\<close> \<open>p \<in> set S'\<close> \<open>S' \<turnstile> \<^bold>\<bottom>\<close>
    using assms unfolding consistent_def by blast
  then obtain S'' where S'': \<open>set (p # S'') = set S'\<close> \<open>p \<notin> set S''\<close>
    using split_list by metis
  then have \<open>p # S'' \<turnstile> \<^bold>\<bottom>\<close>
    using \<open>S' \<turnstile> \<^bold>\<bottom>\<close> imply_weaken by blast
  then show ?thesis
    using that S'' S'(1) Diff_insert_absorb Diff_subset_conv list.simps(15) by metis
qed

lemma consistent_add_witness:
  assumes \<open>consistent S\<close> and \<open>\<^bold>\<not> (\<^bold>\<forall>p) \<in> S\<close> and \<open>a \<notin> params S\<close>
  shows \<open>consistent ({\<^bold>\<not> \<langle>\<^bold>\<star>a/0\<rangle>p} \<union> S)\<close>
  unfolding consistent_def
proof
  assume \<open>\<exists>S'. set S' \<subseteq> {\<^bold>\<not> \<langle>\<^bold>\<star>a/0\<rangle>p} \<union> S \<and> S' \<turnstile> \<^bold>\<bottom>\<close>
  then obtain S' where \<open>set S' \<subseteq> S\<close> and \<open>(\<^bold>\<not> \<langle>\<^bold>\<star>a/0\<rangle>p) # S' \<turnstile> \<^bold>\<bottom>\<close>
    using assms inconsistent_fm unfolding consistent_def by metis
  then have \<open>\<turnstile> \<^bold>\<not> \<langle>\<^bold>\<star>a/0\<rangle>p \<^bold>\<longrightarrow> S' \<^bold>\<leadsto> \<^bold>\<bottom>\<close>
    by simp
  moreover have \<open>a \<notin> params_fm p\<close>
    using assms(2-3) by auto
  moreover have \<open>\<forall>p \<in> set S'. a \<notin> params_fm p\<close>
    using \<open>set S' \<subseteq> S\<close> assms(3) by auto
  then have \<open>a \<notin> params_fm (S' \<^bold>\<leadsto> \<^bold>\<bottom>)\<close>
    by (simp add: imply_params_fm)
  ultimately have \<open>\<turnstile> \<^bold>\<not> (\<^bold>\<forall>p) \<^bold>\<longrightarrow> S' \<^bold>\<leadsto> \<^bold>\<bottom>\<close>
    using GR' by fast
  then have \<open>\<^bold>\<not> (\<^bold>\<forall>p) # S' \<turnstile> \<^bold>\<bottom>\<close>
    by simp
  moreover have \<open>set ((\<^bold>\<not> (\<^bold>\<forall>p)) # S') \<subseteq> S\<close>
    using \<open>set S' \<subseteq> S\<close> assms(2) by simp
  ultimately show False
    using assms(1) unfolding consistent_def by blast
qed

lemma consistent_add_witness2P:
  assumes \<open>consistent S\<close> and \<open>\<^bold>\<not> (\<^bold>\<forall>\<^sub>Pp) \<in> S\<close> and \<open>P \<notin> params S\<close>
  shows \<open>consistent ({\<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2P/0\<rangle>2Pp} \<union> S)\<close>
  unfolding consistent_def
proof
  assume \<open>\<exists>S'. set S' \<subseteq> {\<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2P/0\<rangle>2Pp} \<union> S \<and> S' \<turnstile> \<^bold>\<bottom>\<close>
  then obtain S' where \<open>set S' \<subseteq> S\<close> and \<open>(\<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2P/0\<rangle>2Pp) # S' \<turnstile> \<^bold>\<bottom>\<close>
    using assms inconsistent_fm unfolding consistent_def by metis
  then have \<open>\<turnstile> \<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2P/0\<rangle>2Pp \<^bold>\<longrightarrow> S' \<^bold>\<leadsto> \<^bold>\<bottom>\<close>
    by simp
  moreover have \<open>P \<notin> params_fm p\<close>
    using assms(2-3) by auto
  moreover have \<open>\<forall>p \<in> set S'. P \<notin> params_fm p\<close>
    using \<open>set S' \<subseteq> S\<close> assms(3) by auto
  then have \<open>P \<notin> params_fm (S' \<^bold>\<leadsto> \<^bold>\<bottom>)\<close>
    by (simp add: imply_params_fm)
  ultimately have \<open>\<turnstile> \<^bold>\<not> (\<^bold>\<forall>\<^sub>Pp) \<^bold>\<longrightarrow> S' \<^bold>\<leadsto> \<^bold>\<bottom>\<close>
    using GR'2P by fast
  then have \<open>\<^bold>\<not> (\<^bold>\<forall>\<^sub>Pp) # S' \<turnstile> \<^bold>\<bottom>\<close>
    by simp
  moreover have \<open>set ((\<^bold>\<not> (\<^bold>\<forall>\<^sub>Pp)) # S') \<subseteq> S\<close>
    using \<open>set S' \<subseteq> S\<close> assms(2) by simp
  ultimately show False
    using assms(1) unfolding consistent_def by blast
qed

lemma consistent_add_witness2F:
  assumes \<open>consistent S\<close> and \<open>\<^bold>\<not> (\<^bold>\<forall>\<^sub>Fp) \<in> S\<close> and \<open>F \<notin> params S\<close>
  shows \<open>consistent ({\<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2F/0\<rangle>2Ffmp} \<union> S)\<close>
  unfolding consistent_def
proof
  assume \<open>\<exists>S'. set S' \<subseteq> {\<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2F/0\<rangle>2Ffmp} \<union> S \<and> S' \<turnstile> \<^bold>\<bottom>\<close>
  then obtain S' where \<open>set S' \<subseteq> S\<close> and \<open>(\<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2F/0\<rangle>2Ffmp) # S' \<turnstile> \<^bold>\<bottom>\<close>
    using assms inconsistent_fm unfolding consistent_def by metis
  then have \<open>\<turnstile> \<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2F/0\<rangle>2Ffmp \<^bold>\<longrightarrow> S' \<^bold>\<leadsto> \<^bold>\<bottom>\<close>
    by simp
  moreover have \<open>F \<notin> params_fm p\<close>
    using assms(2-3) by auto
  moreover have \<open>\<forall>p \<in> set S'. F \<notin> params_fm p\<close>
    using \<open>set S' \<subseteq> S\<close> assms(3) by auto
  then have \<open>F \<notin> params_fm (S' \<^bold>\<leadsto> \<^bold>\<bottom>)\<close>
    by (simp add: imply_params_fm)
  ultimately have \<open>\<turnstile> \<^bold>\<not> (\<^bold>\<forall>\<^sub>Fp) \<^bold>\<longrightarrow> S' \<^bold>\<leadsto> \<^bold>\<bottom>\<close>
    using GR'2F by fast
  then have \<open>\<^bold>\<not> (\<^bold>\<forall>\<^sub>Fp) # S' \<turnstile> \<^bold>\<bottom>\<close>
    by simp
  moreover have \<open>set ((\<^bold>\<not> (\<^bold>\<forall>\<^sub>Fp)) # S') \<subseteq> S\<close>
    using \<open>set S' \<subseteq> S\<close> assms(2) by simp
  ultimately show False
    using assms(1) unfolding consistent_def by blast
qed

lemma consistent_add_instance:
  assumes \<open>consistent S\<close> and \<open>\<^bold>\<forall>p \<in> S\<close>
  shows \<open>consistent ({\<langle>t/0\<rangle>p} \<union> S)\<close>
  unfolding consistent_def
proof
  assume \<open>\<exists>S'. set S' \<subseteq> {\<langle>t/0\<rangle>p} \<union> S \<and> S' \<turnstile> \<^bold>\<bottom>\<close>
  then obtain S' where \<open>set S' \<subseteq> S\<close> and \<open>\<langle>t/0\<rangle>p # S' \<turnstile> \<^bold>\<bottom>\<close>
    using assms inconsistent_fm unfolding consistent_def by blast
  moreover have \<open>\<turnstile> \<^bold>\<forall>p \<^bold>\<longrightarrow> \<langle>t/0\<rangle>p\<close>
    using IA by blast
  ultimately have \<open>\<^bold>\<forall>p # S' \<turnstile> \<^bold>\<bottom>\<close>
    by (meson add_imply cut deduct(1))
  moreover have \<open>set ((\<^bold>\<forall>p) # S') \<subseteq> S\<close>
    using \<open>set S' \<subseteq> S\<close> assms(2) by simp
  ultimately show False
    using assms(1) unfolding consistent_def by blast
qed

lemma consistent_add_instance2P:
  assumes \<open>consistent S\<close> and \<open>\<^bold>\<forall>\<^sub>Pp \<in> S\<close>
  shows \<open>consistent ({\<langle>P/0\<rangle>2Pp} \<union> S)\<close>
  unfolding consistent_def
proof
  assume \<open>\<exists>S'. set S' \<subseteq> {\<langle>P/0\<rangle>2Pp} \<union> S \<and> S' \<turnstile> \<^bold>\<bottom>\<close>
  then obtain S' where \<open>set S' \<subseteq> S\<close> and \<open>\<langle>P/0\<rangle>2Pp # S' \<turnstile> \<^bold>\<bottom>\<close>
    using assms inconsistent_fm unfolding consistent_def by blast
  moreover have \<open>\<turnstile> \<^bold>\<forall>\<^sub>Pp \<^bold>\<longrightarrow> \<langle>P/0\<rangle>2Pp\<close>
    using IA2P by blast
  ultimately have \<open>\<^bold>\<forall>\<^sub>Pp # S' \<turnstile> \<^bold>\<bottom>\<close>
    by (meson add_imply cut deduct(1))
  moreover have \<open>set ((\<^bold>\<forall>\<^sub>Pp) # S') \<subseteq> S\<close>
    using \<open>set S' \<subseteq> S\<close> assms(2) by simp
  ultimately show False
    using assms(1) unfolding consistent_def by blast
qed

lemma consistent_add_instance2F:
  assumes \<open>consistent S\<close> and \<open>\<^bold>\<forall>\<^sub>Fp \<in> S\<close>
  shows \<open>consistent ({\<langle>F/0\<rangle>2Ffmp} \<union> S)\<close>
  unfolding consistent_def
proof
  assume \<open>\<exists>S'. set S' \<subseteq> {\<langle>F/0\<rangle>2Ffmp} \<union> S \<and> S' \<turnstile> \<^bold>\<bottom>\<close>
  then obtain S' where \<open>set S' \<subseteq> S\<close> and \<open>\<langle>F/0\<rangle>2Ffmp # S' \<turnstile> \<^bold>\<bottom>\<close>
    using assms inconsistent_fm unfolding consistent_def by blast
  moreover have \<open>\<turnstile> \<^bold>\<forall>\<^sub>Fp \<^bold>\<longrightarrow> \<langle>F/0\<rangle>2Ffmp\<close>
    using IA2F by blast
  ultimately have \<open>\<^bold>\<forall>\<^sub>Fp # S' \<turnstile> \<^bold>\<bottom>\<close>
    by (meson add_imply cut deduct(1))
  moreover have \<open>set ((\<^bold>\<forall>\<^sub>Fp) # S') \<subseteq> S\<close>
    using \<open>set S' \<subseteq> S\<close> assms(2) by simp
  ultimately show False
    using assms(1) unfolding consistent_def by blast
qed




section \<open>Extension\<close>

fun witness where
  \<open>witness used used2 (\<^bold>\<not> (\<^bold>\<forall>p)) = {\<^bold>\<not> \<langle>\<^bold>\<star>(SOME a. a \<notin> used)/0\<rangle>p}\<close>
| \<open>witness used used2 (\<^bold>\<not> (\<^bold>\<forall>\<^sub>Pp)) = {\<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2P(SOME a. a \<notin> used2)/0\<rangle>2Pp}\<close>
| \<open>witness used used2 (\<^bold>\<not> (\<^bold>\<forall>\<^sub>Fp)) = {\<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2F(SOME a. a \<notin> used)/0\<rangle>2Ffmp}\<close>
| \<open>witness _ _ _ = {}\<close>

primrec extend where
  \<open>extend S f 0 = S\<close>
| \<open>extend S f (Suc n) =
   (let Sn = extend S f n in
     if consistent ({f n} \<union> Sn)
     then witness (params ({f n} \<union> Sn)) (pparams ({f n} \<union> Sn)) (f n) \<union> {f n} \<union> Sn
     else Sn)\<close>

definition \<open>Extend S f \<equiv> \<Union>n. extend S f n\<close>

lemma extend_subset: \<open>S \<subseteq> extend S f n\<close>
  by (induct n) (fastforce simp: Let_def)+

lemma Extend_subset: \<open>S \<subseteq> Extend S f\<close>
  unfolding Extend_def by (metis Union_upper extend.simps(1) range_eqI)

lemma extend_bound: \<open>(\<Union>n \<le> m. extend S f n) = extend S f m\<close>
  by (induct m) (simp_all add: atMost_Suc Let_def)

lemma finite_params_witness [simp]: \<open>finite (params (witness used used2 p))\<close>
proof (induct p)
  case Falsity
  then show ?case 
    by auto
next
  case (Pre P ts)
  then show ?case
    by auto
next
  case (Imp p1 p2)
  show ?case
    by (cases p1; cases p2) auto
next
  case (Uni p)
  then show ?case
    by auto
next
  case (Uni2P p)
  then show ?case
    by auto
next
  case (Uni2F p)
  then show ?case
    by auto
qed

lemma finite_pparams_witness [simp]: \<open>finite (pparams (witness used used2 p))\<close>
proof (induct p)
  case Falsity
  then show ?case 
    by auto
next
  case (Pre P ts)
  then show ?case
    by auto
next
  case (Imp p1 p2)
  show ?case
    by (cases p1; cases p2) auto
next
  case (Uni p)
  then show ?case
    by auto
next
  case (Uni2P p)
  then show ?case
    by auto
next
  case (Uni2F p)
  then show ?case
    by auto
qed

lemma finite_params_extend [simp]: \<open>finite (params (extend S f n) - params S)\<close>
  by (induct n) (simp_all add: Let_def Un_Diff)

lemma finite_pparams_extend [simp]: \<open>finite (pparams (extend S f n) - pparams S)\<close>
  by (induct n) (simp_all add: Let_def Un_Diff)

lemma Set_Diff_Un: \<open>X - (Y \<union> Z) = X - Y - Z\<close>
  by blast

lemma infinite_params_extend:
  assumes \<open>infinite (UNIV - params S)\<close>
  shows \<open>infinite (UNIV - params (extend S f n))\<close>
proof -
  have \<open>finite (params (extend S f n) - params S)\<close>
    by simp
  then obtain extra where \<open>finite extra\<close> \<open>params (extend S f n) = extra \<union> params S\<close>
    using extend_subset by fast
  then have \<open>?thesis = infinite (UNIV - (extra \<union> params S))\<close>
    by simp
  also have \<open>\<dots> = infinite (UNIV - extra - params S)\<close>
    by (simp add: Set_Diff_Un)
  also have \<open>\<dots> = infinite (UNIV - params S)\<close>
    using \<open>finite extra\<close> by (metis Set_Diff_Un Un_commute finite_Diff2)
  finally show ?thesis
    using assms ..
qed

lemma infinite_pparams_extend:
  assumes \<open>infinite (UNIV - pparams S)\<close>
  shows \<open>infinite (UNIV - pparams (extend S f n))\<close>
proof -
  have \<open>finite (pparams (extend S f n) - pparams S)\<close>
    by simp
  then obtain extra where \<open>finite extra\<close> \<open>pparams (extend S f n) = extra \<union> pparams S\<close>
    using extend_subset by fast
  then have \<open>?thesis = infinite (UNIV - (extra \<union> pparams S))\<close>
    by simp
  also have \<open>\<dots> = infinite (UNIV - extra - pparams S)\<close>
    by (simp add: Set_Diff_Un)
  also have \<open>\<dots> = infinite (UNIV - pparams S)\<close>
    using \<open>finite extra\<close> by (metis Set_Diff_Un Un_commute finite_Diff2)
  finally show ?thesis
    using assms ..
qed

lemma consistent_witness:
  assumes \<open>consistent S\<close> and \<open>p \<in> S\<close> and \<open>params S \<subseteq> used\<close> and \<open>pparams S \<subseteq> used2\<close>
    and \<open>infinite (UNIV - used)\<close> and \<open>infinite (UNIV - used2)\<close>
  shows \<open>consistent (witness used used2 p \<union> S)\<close>
  using assms
proof (induct used used2 p rule: witness.induct)
  case (1 used used2 p)
  moreover have \<open>\<exists>a. a \<notin> used\<close>
    using 1(5) by (meson Diff_iff finite_params_fm finite_subset subset_iff)
  ultimately obtain a where a: \<open>witness used used2 (\<^bold>\<not> (\<^bold>\<forall>p)) = {\<^bold>\<not> \<langle>\<^bold>\<star>a/0\<rangle>p}\<close> and \<open>a \<notin> used\<close>
    by (metis someI_ex witness.simps(1))
  then have \<open>a \<notin> params S\<close>
    using 1(3) by fast
  then show ?case
    using 1(1-2) a(1) consistent_add_witness by metis
next
  case (2 used used2 p)
  moreover have \<open>\<exists>P. P \<notin> used2\<close>
    using 2(6) by (meson Diff_iff finite_params_fm finite_subset subset_iff)
  ultimately obtain P where P: \<open>witness used used2 (\<^bold>\<not> (\<^bold>\<forall>\<^sub>Pp)) = {\<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2PP/0\<rangle>2Pp}\<close> and \<open>P \<notin> used2\<close>
    by (metis someI_ex witness.simps(2))
  then have \<open>P \<notin> pparams S\<close>
    using 2 by fast
  then show ?case
    by (metis "2.prems"(2) P assms(1) consistent_add_witness2P)
next
  case (3 used used2 p)
  moreover have \<open>\<exists>F. F \<notin> used\<close>
    using 3(5) by (meson Diff_iff finite_params_fm finite_subset subset_iff)
  ultimately obtain F where F: \<open>witness used used2 (\<^bold>\<not> (\<^bold>\<forall>\<^sub>Fp)) = {\<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2FF/0\<rangle>2Ffmp}\<close> and \<open>F \<notin> used\<close>
    by (metis someI_ex witness.simps(3))
  then have \<open>F \<notin> params S\<close>
    using 3 by blast
  then show ?case
    by (metis "3.prems"(2) F assms(1) consistent_add_witness2F)
qed (auto simp: assms)

lemma consistent_extend:
  assumes \<open>consistent S\<close> and \<open>infinite (UNIV - params S)\<close> and \<open>infinite (UNIV - pparams S)\<close>
  shows \<open>consistent (extend S f n)\<close>
proof (induct n)
  case (Suc n)
  have \<open>infinite (UNIV - params (extend S f n))\<close>
    using assms(2) infinite_params_extend by fast
  with finite_params_fm have \<open>infinite (UNIV - (params_fm (f n) \<union> params (extend S f n)))\<close>
    by (metis Set_Diff_Un Un_commute finite_Diff2)
  moreover
  have \<open>infinite (UNIV - pparams (extend S f n))\<close>
    using assms(3) infinite_pparams_extend by blast
  with finite_params_fm have \<open>infinite (UNIV - (params_fm (f n) \<union> pparams (extend S f n)))\<close>
    by (metis Set_Diff_Un Un_commute finite_Diff2)
  ultimately
  show ?case
    using Suc consistent_witness[where S=\<open>{f n} \<union> extend S f n\<close>] by (simp add: Let_def)
qed (use assms(1) in simp)

lemma consistent_Extend:
  assumes \<open>consistent S\<close> and \<open>infinite (UNIV - params S)\<close>  \<open>infinite (UNIV - pparams S)\<close>
  shows \<open>consistent (Extend S f)\<close>
  unfolding consistent_def
proof
  assume \<open>\<exists>S'. set S' \<subseteq> Extend S f \<and> S' \<turnstile> \<^bold>\<bottom>\<close>
  then obtain S' where \<open>S' \<turnstile> \<^bold>\<bottom>\<close> and \<open>set S' \<subseteq> Extend S f\<close>
    unfolding consistent_def by blast
  then obtain m where \<open>set S' \<subseteq> (\<Union>n \<le> m. extend S f n)\<close>
    unfolding Extend_def using UN_finite_bound by (metis finite_set)
  then have \<open>set S' \<subseteq> extend S f m\<close>
    using extend_bound by blast
  moreover have \<open>consistent (extend S f m)\<close>
    using assms consistent_extend by blast
  ultimately show False
    unfolding consistent_def using \<open>S' \<turnstile> \<^bold>\<bottom>\<close> by blast
qed

section \<open>Maximal\<close>

definition \<open>maximal S \<equiv> \<forall>p. p \<notin> S \<longrightarrow> \<not> consistent ({p} \<union> S)\<close>

lemma maximal_exactly_one:
  assumes \<open>consistent S\<close> and \<open>maximal S\<close>
  shows \<open>p \<in> S \<longleftrightarrow> (\<^bold>\<not> p) \<notin> S\<close>
proof
  assume \<open>p \<in> S\<close>
  show \<open>(\<^bold>\<not> p) \<notin> S\<close>
  proof
    assume \<open>(\<^bold>\<not> p) \<in> S\<close>
    then have \<open>set [p, \<^bold>\<not> p] \<subseteq> S\<close>
      using \<open>p \<in> S\<close> by simp
    moreover have \<open>[p, \<^bold>\<not> p] \<turnstile> \<^bold>\<bottom>\<close>
      by blast
    ultimately show False
      using \<open>consistent S\<close> unfolding consistent_def by blast
  qed
next
  assume \<open>(\<^bold>\<not> p) \<notin> S\<close>
  then have \<open>\<not> consistent ({\<^bold>\<not> p} \<union> S)\<close>
    using \<open>maximal S\<close> unfolding maximal_def by blast
  then obtain S' where \<open>set S' \<subseteq> S\<close> \<open>(\<^bold>\<not> p) # S' \<turnstile> \<^bold>\<bottom>\<close>
    using \<open>consistent S\<close> inconsistent_fm by blast
  then have \<open>S' \<turnstile> p\<close>
    using Boole by blast
  have \<open>consistent ({p} \<union> S)\<close>
    unfolding consistent_def
  proof
    assume \<open>\<exists>S'. set S' \<subseteq> {p} \<union> S \<and> S' \<turnstile> \<^bold>\<bottom>\<close>
    then obtain S'' where \<open>set S'' \<subseteq> S\<close> and \<open>p # S'' \<turnstile> \<^bold>\<bottom>\<close>
      using assms inconsistent_fm unfolding consistent_def by blast
    then have \<open>S' @ S'' \<turnstile> \<^bold>\<bottom>\<close>
      using \<open>S' \<turnstile> p\<close> by (metis MP' add_imply imply.simps(2) imply_append)
    moreover have \<open>set (S' @ S'') \<subseteq> S\<close>
      using \<open>set S' \<subseteq> S\<close> \<open>set S'' \<subseteq> S\<close> by simp
    ultimately show False
      using \<open>consistent S\<close> unfolding consistent_def by blast
  qed
  then show \<open>p \<in> S\<close>
    using \<open>maximal S\<close> unfolding maximal_def by blast
qed

lemma maximal_Extend:
  assumes \<open>surj f\<close>
  shows \<open>maximal (Extend S f)\<close>
  unfolding maximal_def
proof safe
  fix p
  assume \<open>p \<notin> Extend S f\<close> and \<open>consistent ({p} \<union> Extend S f)\<close>
  obtain k where k: \<open>f k = p\<close>
    using \<open>surj f\<close> unfolding surj_def by metis
  then have \<open>p \<notin> extend S f (Suc k)\<close>
    using \<open>p \<notin> Extend S f\<close> unfolding Extend_def by blast
  then have \<open>\<not> consistent ({p} \<union> extend S f k)\<close>
    using k by (auto simp: Let_def)
  moreover have \<open>{p} \<union> extend S f k \<subseteq> {p} \<union> Extend S f\<close>
    unfolding Extend_def by blast
  ultimately have \<open>\<not> consistent ({p} \<union> Extend S f)\<close>
    unfolding consistent_def by auto
  then show False
    using \<open>consistent ({p} \<union> Extend S f)\<close> by blast
qed

section \<open>Saturation\<close>

definition \<open>saturated S \<equiv> \<forall>p.
              (\<^bold>\<not> (\<^bold>\<forall>p) \<in> S \<longrightarrow> (\<exists>a. (\<^bold>\<not> \<langle>\<^bold>\<star>a/0\<rangle>p) \<in> S))
              \<and>
              (\<^bold>\<not> (\<^bold>\<forall>\<^sub>Pp) \<in> S \<longrightarrow> (\<exists>P. (\<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2PP/0\<rangle>2Pp) \<in> S))
              \<and>
              (\<^bold>\<not> (\<^bold>\<forall>\<^sub>Fp) \<in> S \<longrightarrow> (\<exists>F. (\<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2FF/0\<rangle>2Ffmp) \<in> S))
        \<close>

lemma saturated_Extend:
  assumes \<open>consistent (Extend S f)\<close> and \<open>surj f\<close>
  shows \<open>saturated (Extend S f)\<close>
  unfolding saturated_def
proof safe
  fix p
  assume *: \<open>\<^bold>\<not> (\<^bold>\<forall>p) \<in> Extend S f\<close>
  obtain k where k: \<open>f k = \<^bold>\<not> (\<^bold>\<forall>p)\<close>
    using \<open>surj f\<close> unfolding surj_def by metis
  have \<open>extend S f k \<subseteq> Extend S f\<close>
    unfolding Extend_def by auto
  then have \<open>consistent ({\<^bold>\<not> (\<^bold>\<forall>p)} \<union> extend S f k)\<close>
    using assms(1) * unfolding consistent_def by blast
  then have \<open>\<exists>a. extend S f (Suc k) = {\<^bold>\<not> \<langle>\<^bold>\<star>a/0\<rangle>p} \<union> {\<^bold>\<not> (\<^bold>\<forall>p)} \<union> extend S f k\<close>
    using k by (auto simp: Let_def)
  moreover have \<open>extend S f (Suc k) \<subseteq> Extend S f\<close>
    unfolding Extend_def by blast
  ultimately show \<open>\<exists>a. \<^bold>\<not> \<langle>\<^bold>\<star> a/0\<rangle>p \<in> Extend S f\<close>
    by blast
next
  fix p
  assume *: \<open>\<^bold>\<not> (\<^bold>\<forall>\<^sub>Pp) \<in> Extend S f\<close>
  obtain k where k: \<open>f k = \<^bold>\<not> (\<^bold>\<forall>\<^sub>Pp)\<close>
    using \<open>surj f\<close> unfolding surj_def by metis
  have \<open>extend S f k \<subseteq> Extend S f\<close>
    unfolding Extend_def by auto
  then have \<open>consistent ({\<^bold>\<not> (\<^bold>\<forall>\<^sub>Pp)} \<union> extend S f k)\<close>
    using assms(1) * unfolding consistent_def by blast
  then have \<open>\<exists>P. extend S f (Suc k) = {\<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2PP/0\<rangle>2Pp} \<union> {\<^bold>\<not> (\<^bold>\<forall>\<^sub>Pp)} \<union> extend S f k\<close>
    using k by (auto simp: Let_def)
  moreover have \<open>extend S f (Suc k) \<subseteq> Extend S f\<close>
    unfolding Extend_def by blast
  ultimately show \<open>\<exists>P. \<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2P P/0\<rangle>2Pp \<in> Extend S f\<close>
    by blast
next
  fix p
  assume *: \<open>\<^bold>\<not> (\<^bold>\<forall>\<^sub>Fp) \<in> Extend S f\<close>
  obtain k where k: \<open>f k = \<^bold>\<not> (\<^bold>\<forall>\<^sub>Fp)\<close>
    using \<open>surj f\<close> unfolding surj_def by metis
  have \<open>extend S f k \<subseteq> Extend S f\<close>
    unfolding Extend_def by auto
  then have \<open>consistent ({\<^bold>\<not> (\<^bold>\<forall>\<^sub>Fp)} \<union> extend S f k)\<close>
    using assms(1) * unfolding consistent_def by blast
  then have \<open>\<exists>F. extend S f (Suc k) = {\<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2FF/0\<rangle>2Ffmp} \<union> {\<^bold>\<not> (\<^bold>\<forall>\<^sub>Fp)} \<union> extend S f k\<close>
    using k by (auto simp: Let_def)
  moreover have \<open>extend S f (Suc k) \<subseteq> Extend S f\<close>
    unfolding Extend_def by blast
  ultimately show \<open>\<exists>F. \<^bold>\<not> \<langle>\<^bold>\<circle>\<^sub>2F F/0\<rangle>2Ffmp \<in> Extend S f\<close>
    by blast
qed

section \<open>Hintikka\<close>

locale Hintikka =
  fixes H :: \<open>'f fm set\<close>
  assumes
    FlsH: \<open>\<^bold>\<bottom> \<notin> H\<close> and
    ImpH: \<open>(p \<^bold>\<longrightarrow> q) \<in> H \<longleftrightarrow> (p \<in> H \<longrightarrow> q \<in> H)\<close> and
    UniH: \<open>(\<^bold>\<forall>p \<in> H) \<longleftrightarrow> (\<forall>t. \<langle>t/0\<rangle>p \<in> H)\<close> and
    UniH2P: \<open>(\<^bold>\<forall>\<^sub>Pp \<in> H) \<longleftrightarrow> (\<forall>P. \<langle>P/0\<rangle>2Pp \<in> H)\<close> and
    UniH2F: \<open>(\<^bold>\<forall>\<^sub>Fp \<in> H) \<longleftrightarrow> (\<forall>F. \<langle>F/0\<rangle>2Ffmp \<in> H)\<close>

subsection \<open>Model Existence\<close>

term "\<lbrakk>a,b,c,d,e,f,g,h\<rbrakk>"

term "\<^bold>#\<^sub>2"

term "\<^bold>#"

term "\<^bold>\<circle>"

abbreviation henv2P where "henv2P H == \<lambda>n ts. \<^bold>\<cdot>(\<^bold>#\<^sub>2Pn) ts \<in> H"

abbreviation hpred where "hpred H == \<lambda>P ts. \<^bold>\<cdot>(\<^bold>\<circle>\<^sub>2PP) ts \<in> H"

abbreviation hdomP where "hdomP H == range (henv2P H) \<union> range (hpred H)"

abbreviation henv2F where "henv2F == \<lambda>f. \<^bold>\<circle> (\<^bold>#\<^sub>2F f)"

abbreviation hfun where "hfun ==  \<lambda>f. \<^bold>\<circle> (\<^bold>\<circle>\<^sub>2F f)"

definition hdomF where "hdomF == range henv2F \<union> range hfun"

abbreviation (input) hmodel (\<open>\<lbrakk>_\<rbrakk>\<close>) where \<open>\<lbrakk>H\<rbrakk> \<equiv> \<lbrakk>\<^bold>#, henv2F, henv2P H, \<^bold>\<star>, hfun, hpred H, hdomP H, hdomF\<rbrakk>\<close>

lemma semantics_tm_id [simp]: \<open>\<lparr>\<^bold>#, henv2F , \<^bold>\<star> , \<lambda>f. \<^bold>\<circle> (\<^bold>\<circle>\<^sub>2F f) \<rparr> t = t\<close>
proof (induct t)
  case (Var x)
  then show ?case 
    by (auto cong: map_cong)
next
  case (Fun x1a x2)
  then show ?case
    by (cases x1a) (auto cong: map_cong)
next
  case (Cst c)
  then show ?case
    by auto
qed

lemma semantics_tm_id_map [simp]: \<open>map \<lparr>\<^bold>#, \<lambda>f. \<^bold>\<circle> (\<^bold>#\<^sub>2F f) , \<^bold>\<star>, \<lambda>f. \<^bold>\<circle> (\<^bold>\<circle>\<^sub>2F f) \<rparr> ts = ts\<close>
  by (auto cong: map_cong)

theorem Hintikka_model:
  assumes \<open>Hintikka H\<close>
  shows \<open>p \<in> H \<longleftrightarrow> \<lbrakk>H\<rbrakk> p\<close>
proof (induct p rule: wf_induct[where r=\<open>measure size_fm\<close>])
  case 1
  then show ?case ..
next
  case (2 x)
  then show ?case
    using assms unfolding Hintikka_def 
    apply (cases x) 
        apply auto
    subgoal for P ts
      apply (induction P)
       apply auto
      done
    subgoal for P ts
      apply (induction P)
       apply auto
      done
    subgoal for p pred
      apply (metis semantics_pd.simps(1))
      done
    subgoal for p P
      apply (metis semantics_pd.simps(2))
      done
    subgoal for p P
      apply (induction P)
      subgoal for n
        apply auto
        done
      subgoal for P'
        apply auto
        done
      done
    subgoal for p f
      unfolding hdomF_def
      apply auto
      subgoal for n
        by (metis (mono_tags, lifting) semantics_fn.simps(1))
      subgoal for e
        by (metis (mono_tags, lifting) semantics_fn.simps(2))
      done
    subgoal for p f
      apply (induction f)
      subgoal for n
        by (simp add: hdomF_def)
      subgoal for e
        by (simp add: hdomF_def)
      done
    done
qed

subsection \<open>Maximal Consistent Sets are Hintikka Sets\<close>

lemma deriv_iff_MCS:
  assumes \<open>consistent S\<close> and \<open>maximal S\<close>
  shows \<open>(\<exists>ps. set ps \<subseteq> S \<and> ps \<turnstile> p) \<longleftrightarrow> p \<in> S\<close>
proof
  from assms maximal_exactly_one[OF assms(1)] show \<open>\<exists>ps. set ps \<subseteq> S \<and> ps \<turnstile> p \<Longrightarrow> p \<in> S\<close>
    unfolding consistent_def using MP add_imply deduct1 imply.simps(1) imply_ImpE
    by (metis insert_absorb insert_mono list.simps(15))
next
  show \<open>p \<in> S \<Longrightarrow> \<exists>ps. set ps \<subseteq> S \<and> ps \<turnstile> p\<close>
    using imply_head by (metis empty_subsetI insert_absorb insert_mono list.set(1) list.simps(15))
qed

lemma Hintikka_Extend:
  assumes \<open>consistent H\<close> and \<open>maximal H\<close> and \<open>saturated H\<close>
  shows \<open>Hintikka H\<close>
proof
  show \<open>\<^bold>\<bottom> \<notin> H\<close>
    using assms deriv_iff_MCS unfolding consistent_def by fast
next
  fix p q
  show \<open>(p \<^bold>\<longrightarrow> q) \<in> H \<longleftrightarrow> (p \<in> H \<longrightarrow> q \<in> H)\<close>
    using deriv_iff_MCS[OF assms(1-2)] maximal_exactly_one[OF assms(1-2)]
    by (metis Imp1 contraposition add_imply deduct1 insert_subset list.simps(15))
next
  fix p
  show \<open>(\<^bold>\<forall>p \<in> H) \<longleftrightarrow> (\<forall>t. \<langle>t/0\<rangle>p \<in> H)\<close>
    using assms consistent_add_instance maximal_exactly_one
    unfolding maximal_def saturated_def by metis
next
  fix p
  show \<open>(\<^bold>\<forall>\<^sub>Pp \<in> H) \<longleftrightarrow> (\<forall>t. \<langle>t/0\<rangle>2Pp \<in> H)\<close>
    by (meson assms(1) assms(2) assms(3) consistent_add_instance2P maximal_def maximal_exactly_one saturated_def)
next
  fix p
  show \<open>(\<^bold>\<forall>\<^sub>Fp \<in> H) \<longleftrightarrow> (\<forall>t. \<langle>t/0\<rangle>2Ffmp \<in> H)\<close>
    by (meson assms(1) assms(2) assms(3) consistent_add_instance2F maximal_def maximal_exactly_one saturated_def)
qed

section \<open>Countable Formulas\<close>

instance fn :: (countable) countable
  by countable_datatype

instance tm :: (countable) countable
  by countable_datatype

instance pd :: (countable) countable
  by countable_datatype

instance fm :: (countable, countable) countable
  by countable_datatype

section \<open>Completeness\<close>

lemma infinite_Diff_fin_Un: \<open>infinite (X - Y) \<Longrightarrow> finite Z \<Longrightarrow> infinite (X - (Z \<union> Y))\<close>
  by (simp add: Set_Diff_Un Un_commute)

theorem strong_completeness:
  fixes p :: \<open>('f :: countable, 'p :: countable) fm\<close>
  assumes \<open>\<forall>(E :: _ \<Rightarrow> 'f tm) E2F E2P C F G PS FS. range E2F \<subseteq> FS \<longrightarrow> range E2P \<subseteq> PS \<longrightarrow> range G \<subseteq> PS \<longrightarrow> range F \<subseteq> FS \<longrightarrow> (\<forall>q \<in> X. \<lbrakk>E, E2F, E2P, C, F, G, PS, FS\<rbrakk> q) \<longrightarrow> \<lbrakk>E, E2F, E2P, C, F, G, PS, FS\<rbrakk> p\<close>
    and \<open>infinite (UNIV - params X)\<close>
    and \<open>infinite (UNIV - pparams X)\<close>
  shows \<open>\<exists>ps. set ps \<subseteq> X \<and> ps \<turnstile> p\<close>
proof (rule ccontr)
  assume \<open>\<nexists>ps. set ps \<subseteq> X \<and> ps \<turnstile> p\<close>
  then have *: \<open>\<nexists>ps. set ps \<subseteq> X \<and> ((\<^bold>\<not> p) # ps \<turnstile> \<^bold>\<bottom>)\<close>
    using Boole by blast

  let ?S = \<open>{\<^bold>\<not> p} \<union> X\<close>
  let ?H = \<open>Extend ?S from_nat\<close>

  from inconsistent_fm have \<open>consistent ?S\<close>
    unfolding consistent_def using * imply_Cons by metis
  moreover have \<open>infinite (UNIV - params ?S)\<close>
    using assms(2) finite_params_fm by (simp add: infinite_Diff_fin_Un)
  moreover have  \<open>infinite (UNIV - pparams ?S)\<close>
    by (simp add: assms(3) infinite_Diff_fin_Un)
  ultimately have \<open>consistent ?H\<close> and \<open>maximal ?H\<close>
    using consistent_Extend maximal_Extend surj_from_nat by blast+
  moreover from this have \<open>saturated ?H\<close>
    using saturated_Extend by fastforce
  ultimately have \<open>Hintikka ?H\<close>
    using assms(2) Hintikka_Extend by blast

  have \<open>\<lbrakk>?H\<rbrakk> p\<close> if \<open>p \<in> ?S\<close> for p
    using that Extend_subset Hintikka_model \<open>Hintikka ?H\<close> by blast
  then have \<open>\<lbrakk>?H\<rbrakk> (\<^bold>\<not> p)\<close> and \<open>\<forall>q \<in> X. \<lbrakk>?H\<rbrakk> q\<close>
    by blast+
  moreover from this have \<open>\<lbrakk>?H\<rbrakk> p\<close>
    using assms(1)
    by (simp add: hdomF_def)
  ultimately show False
    by simp
qed

theorem completeness:
  fixes p :: \<open>(nat, nat) fm\<close>
  assumes \<open>\<forall>(E :: nat \<Rightarrow> nat tm) E2P E2F C F G PS FS. range E2F \<subseteq> FS \<longrightarrow> range E2P \<subseteq> PS \<longrightarrow> range G \<subseteq> PS \<longrightarrow> range F \<subseteq> FS \<longrightarrow> \<lbrakk>E, E2F, E2P, C, F, G, PS, FS\<rbrakk> p\<close>
  shows \<open>\<turnstile> p\<close>
  using assms strong_completeness[where X=\<open>{}\<close>, of p] by auto

section \<open>Main Result\<close>

abbreviation valid :: \<open>(nat, nat) fm \<Rightarrow> bool\<close> where
  \<open>valid p \<equiv> \<forall>(E :: nat \<Rightarrow> nat tm) E2P E2F C F G PS FS. range E2P \<subseteq> PS \<longrightarrow> range G \<subseteq> PS \<longrightarrow>  range E2F \<subseteq> FS \<longrightarrow> range E2P \<subseteq> PS \<longrightarrow> range G \<subseteq> PS \<longrightarrow> range F \<subseteq> FS \<longrightarrow> \<lbrakk>E, E2F, E2P, C, F, G, PS, FS\<rbrakk> p\<close>

theorem main: \<open>valid p \<longleftrightarrow> (\<turnstile> p)\<close> 
  using completeness[of p] soundness[of p] by auto

end

*)
