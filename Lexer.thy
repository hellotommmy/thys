   
theory Lexer
  imports Spec 
begin


section {* The Lexer Functions by Sulzmann and Lu  *}

fun 
  mkeps :: "rexp \<Rightarrow> val"
where
  "mkeps(ONE) = Void"
| "mkeps(SEQ r1 r2) = Seq (mkeps r1) (mkeps r2)"
| "mkeps(ALT r1 r2) = (if nullable(r1) then Left (mkeps r1) else Right (mkeps r2))"
| "mkeps(STAR r) = Stars []"

fun injval :: "rexp \<Rightarrow> char \<Rightarrow> val \<Rightarrow> val"
where
  "injval (CR d) c Void = Char d"
| "injval (ALT r1 r2) c (Left v1) = Left(injval r1 c v1)"
| "injval (ALT r1 r2) c (Right v2) = Right(injval r2 c v2)"
| "injval (SEQ r1 r2) c (Seq v1 v2) = Seq (injval r1 c v1) v2"
| "injval (SEQ r1 r2) c (Left (Seq v1 v2)) = Seq (injval r1 c v1) v2"
| "injval (SEQ r1 r2) c (Right v2) = Seq (mkeps r1) (injval r2 c v2)"
| "injval (STAR r) c (Seq v (Stars vs)) = Stars ((injval r c v) # vs)" 

fun 
  lexer :: "rexp \<Rightarrow> string \<Rightarrow> val option"
where
  "lexer r [] = (if nullable r then Some(mkeps r) else None)"
| "lexer r (c#s) = (case (lexer (der c r) s) of  
                    None \<Rightarrow> None
                  | Some(v) \<Rightarrow> Some(injval r c v))"

section {* Mkeps, Injval Properties *}

lemma mkeps_nullable:
  assumes "nullable(r)" 
  shows "\<Turnstile> mkeps r : r"
using assms
by (induct rule: nullable.induct) 
   (auto intro: Prf.intros)

lemma mkeps_flat:
  assumes "nullable(r)" 
  shows "flat (mkeps r) = []"
using assms
by (induct rule: nullable.induct) (auto)

lemma Prf_injval_flat:
  assumes "\<Turnstile> v : der c r" 
  shows "flat (injval r c v) = c # (flat v)"
using assms
apply(induct c r arbitrary: v rule: der.induct)
apply(auto elim!: Prf_elims intro: mkeps_flat split: if_splits)
done

lemma Prf_injval:
  assumes "\<Turnstile> v : der c r" 
  shows "\<Turnstile> (injval r c v) : r"
using assms
apply(induct r arbitrary: c v rule: rexp.induct)
apply(auto intro!: Prf.intros mkeps_nullable elim!: Prf_elims split: if_splits)
apply(simp add: Prf_injval_flat)
done



text {*
  Mkeps and injval produce, or preserve, Posix values.
*}

lemma Posix_mkeps:
  assumes "nullable r"
  shows "[] \<in> r \<rightarrow> mkeps r"
using assms
apply(induct r rule: nullable.induct)
apply(auto intro: Posix.intros simp add: nullable_correctness Sequ_def)
apply(subst append.simps(1)[symmetric])
apply(rule Posix.intros)
apply(auto)
done

lemma Posix_injval:
  assumes "s \<in> (der c r) \<rightarrow> v"
  shows "(c # s) \<in> r \<rightarrow> (injval r c v)"
using assms
proof(induct r arbitrary: s v rule: rexp.induct)
  case ZERO
  have "s \<in> der c ZERO \<rightarrow> v" by fact
  then have "s \<in> ZERO \<rightarrow> v" by simp
  then have "False" by cases
  then show "(c # s) \<in> ZERO \<rightarrow> (injval ZERO c v)" by simp
next
  case ONE
  have "s \<in> der c ONE \<rightarrow> v" by fact
  then have "s \<in> ZERO \<rightarrow> v" by simp
  then have "False" by cases
  then show "(c # s) \<in> ONE \<rightarrow> (injval ONE c v)" by simp
next 
  case (CR d)
  consider (eq) "c = d" | (ineq) "c \<noteq> d" by blast
  then show "(c # s) \<in> (CR d) \<rightarrow> (injval (CR d) c v)"
  proof (cases)
    case eq
    have "s \<in> der c (CR d) \<rightarrow> v" by fact
    then have "s \<in> ONE \<rightarrow> v" using eq by simp
    then have eqs: "s = [] \<and> v = Void" by cases simp
    show "(c # s) \<in> CR d \<rightarrow> injval (CR d) c v" using eq eqs 
    by (auto intro: Posix.intros)
  next
    case ineq
    have "s \<in> der c (CR d) \<rightarrow> v" by fact
    then have "s \<in> ZERO \<rightarrow> v" using ineq by simp
    then have "False" by cases
    then show "(c # s) \<in> CR d \<rightarrow> injval (CR d) c v" by simp
  qed
next
  case (ALT r1 r2)
  have IH1: "\<And>s v. s \<in> der c r1 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r1 \<rightarrow> injval r1 c v" by fact
  have IH2: "\<And>s v. s \<in> der c r2 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r2 \<rightarrow> injval r2 c v" by fact
  have "s \<in> der c (ALT r1 r2) \<rightarrow> v" by fact
  then have "s \<in> ALT (der c r1) (der c r2) \<rightarrow> v" by simp
  then consider (left) v' where "v = Left v'" "s \<in> der c r1 \<rightarrow> v'" 
              | (right) v' where "v = Right v'" "s \<notin> L (der c r1)" "s \<in> der c r2 \<rightarrow> v'" 
              by cases auto
  then show "(c # s) \<in> ALT r1 r2 \<rightarrow> injval (ALT r1 r2) c v"
  proof (cases)
    case left
    have "s \<in> der c r1 \<rightarrow> v'" by fact
    then have "(c # s) \<in> r1 \<rightarrow> injval r1 c v'" using IH1 by simp
    then have "(c # s) \<in> ALT r1 r2 \<rightarrow> injval (ALT r1 r2) c (Left v')" by (auto intro: Posix.intros)
    then show "(c # s) \<in> ALT r1 r2 \<rightarrow> injval (ALT r1 r2) c v" using left by simp
  next 
    case right
    have "s \<notin> L (der c r1)" by fact
    then have "c # s \<notin> L r1" by (simp add: der_correctness Der_def)
    moreover 
    have "s \<in> der c r2 \<rightarrow> v'" by fact
    then have "(c # s) \<in> r2 \<rightarrow> injval r2 c v'" using IH2 by simp
    ultimately have "(c # s) \<in> ALT r1 r2 \<rightarrow> injval (ALT r1 r2) c (Right v')" 
      by (auto intro: Posix.intros)
    then show "(c # s) \<in> ALT r1 r2 \<rightarrow> injval (ALT r1 r2) c v" using right by simp
  qed
next
  case (SEQ r1 r2)
  have IH1: "\<And>s v. s \<in> der c r1 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r1 \<rightarrow> injval r1 c v" by fact
  have IH2: "\<And>s v. s \<in> der c r2 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r2 \<rightarrow> injval r2 c v" by fact
  have "s \<in> der c (SEQ r1 r2) \<rightarrow> v" by fact
  then consider 
        (left_nullable) v1 v2 s1 s2 where 
        "v = Left (Seq v1 v2)"  "s = s1 @ s2" 
        "s1 \<in> der c r1 \<rightarrow> v1" "s2 \<in> r2 \<rightarrow> v2" "nullable r1" 
        "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L (der c r1) \<and> s\<^sub>4 \<in> L r2)"
      | (right_nullable) v1 s1 s2 where 
        "v = Right v1" "s = s1 @ s2"  
        "s \<in> der c r2 \<rightarrow> v1" "nullable r1" "s1 @ s2 \<notin> L (SEQ (der c r1) r2)"
      | (not_nullable) v1 v2 s1 s2 where
        "v = Seq v1 v2" "s = s1 @ s2" 
        "s1 \<in> der c r1 \<rightarrow> v1" "s2 \<in> r2 \<rightarrow> v2" "\<not>nullable r1" 
        "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L (der c r1) \<and> s\<^sub>4 \<in> L r2)"
        by (force split: if_splits elim!: Posix_elims simp add: Sequ_def der_correctness Der_def)   
  then show "(c # s) \<in> SEQ r1 r2 \<rightarrow> injval (SEQ r1 r2) c v" 
    proof (cases)
      case left_nullable
      have "s1 \<in> der c r1 \<rightarrow> v1" by fact
      then have "(c # s1) \<in> r1 \<rightarrow> injval r1 c v1" using IH1 by simp
      moreover
      have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L (der c r1) \<and> s\<^sub>4 \<in> L r2)" by fact
      then have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (c # s1) @ s\<^sub>3 \<in> L r1 \<and> s\<^sub>4 \<in> L r2)" by (simp add: der_correctness Der_def)
      ultimately have "((c # s1) @ s2) \<in> SEQ r1 r2 \<rightarrow> Seq (injval r1 c v1) v2" using left_nullable by (rule_tac Posix.intros)
      then show "(c # s) \<in> SEQ r1 r2 \<rightarrow> injval (SEQ r1 r2) c v" using left_nullable by simp
    next
      case right_nullable
      have "nullable r1" by fact
      then have "[] \<in> r1 \<rightarrow> (mkeps r1)" by (rule Posix_mkeps)
      moreover
      have "s \<in> der c r2 \<rightarrow> v1" by fact
      then have "(c # s) \<in> r2 \<rightarrow> (injval r2 c v1)" using IH2 by simp
      moreover
      have "s1 @ s2 \<notin> L (SEQ (der c r1) r2)" by fact
      then have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = c # s \<and> [] @ s\<^sub>3 \<in> L r1 \<and> s\<^sub>4 \<in> L r2)" using right_nullable
        by(auto simp add: der_correctness Der_def append_eq_Cons_conv Sequ_def)
      ultimately have "([] @ (c # s)) \<in> SEQ r1 r2 \<rightarrow> Seq (mkeps r1) (injval r2 c v1)"
      by(rule Posix.intros)
      then show "(c # s) \<in> SEQ r1 r2 \<rightarrow> injval (SEQ r1 r2) c v" using right_nullable by simp
    next
      case not_nullable
      have "s1 \<in> der c r1 \<rightarrow> v1" by fact
      then have "(c # s1) \<in> r1 \<rightarrow> injval r1 c v1" using IH1 by simp
      moreover
      have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L (der c r1) \<and> s\<^sub>4 \<in> L r2)" by fact
      then have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (c # s1) @ s\<^sub>3 \<in> L r1 \<and> s\<^sub>4 \<in> L r2)" by (simp add: der_correctness Der_def)
      ultimately have "((c # s1) @ s2) \<in> SEQ r1 r2 \<rightarrow> Seq (injval r1 c v1) v2" using not_nullable 
        by (rule_tac Posix.intros) (simp_all) 
      then show "(c # s) \<in> SEQ r1 r2 \<rightarrow> injval (SEQ r1 r2) c v" using not_nullable by simp
    qed
next
  case (STAR r)
  have IH: "\<And>s v. s \<in> der c r \<rightarrow> v \<Longrightarrow> (c # s) \<in> r \<rightarrow> injval r c v" by fact
  have "s \<in> der c (STAR r) \<rightarrow> v" by fact
  then consider
      (cons) v1 vs s1 s2 where 
        "v = Seq v1 (Stars vs)" "s = s1 @ s2" 
        "s1 \<in> der c r \<rightarrow> v1" "s2 \<in> (STAR r) \<rightarrow> (Stars vs)"
        "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L (der c r) \<and> s\<^sub>4 \<in> L (STAR r))" 
        apply(auto elim!: Posix_elims(1-5) simp add: der_correctness Der_def intro: Posix.intros)
        apply(rotate_tac 3)
        apply(erule_tac Posix_elims(6))
        apply (simp add: Posix.intros(6))
        using Posix.intros(7) by blast
    then show "(c # s) \<in> STAR r \<rightarrow> injval (STAR r) c v" 
    proof (cases)
      case cons
          have "s1 \<in> der c r \<rightarrow> v1" by fact
          then have "(c # s1) \<in> r \<rightarrow> injval r c v1" using IH by simp
        moreover
          have "s2 \<in> STAR r \<rightarrow> Stars vs" by fact
        moreover 
          have "(c # s1) \<in> r \<rightarrow> injval r c v1" by fact 
          then have "flat (injval r c v1) = (c # s1)" by (rule Posix1)
          then have "flat (injval r c v1) \<noteq> []" by simp
        moreover 
          have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L (der c r) \<and> s\<^sub>4 \<in> L (STAR r))" by fact
          then have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (c # s1) @ s\<^sub>3 \<in> L r \<and> s\<^sub>4 \<in> L (STAR r))" 
            by (simp add: der_correctness Der_def)
        ultimately 
        have "((c # s1) @ s2) \<in> STAR r \<rightarrow> Stars (injval r c v1 # vs)" by (rule Posix.intros)
        then show "(c # s) \<in> STAR r \<rightarrow> injval (STAR r) c v" using cons by(simp)
    qed
qed


section {* Lexer Correctness *}


lemma lexer_correct_None:
  shows "s \<notin> L r \<longleftrightarrow> lexer r s = None"
  apply(induct s arbitrary: r)
  apply(simp)
  apply(simp add: nullable_correctness)
  apply(simp)
  apply(drule_tac x="der a r" in meta_spec) 
  apply(auto)
  apply(auto simp add: der_correctness Der_def)
done

lemma lexer_correct_Some:
  shows "s \<in> L r \<longleftrightarrow> (\<exists>v. lexer r s = Some(v) \<and> s \<in> r \<rightarrow> v)"
  apply(induct s arbitrary : r)
  apply(simp only: lexer.simps)
  apply(simp)
  apply(simp add: nullable_correctness Posix_mkeps)
  apply(drule_tac x="der a r" in meta_spec)
  apply(simp (no_asm_use) add: der_correctness Der_def del: lexer.simps) 
  apply(simp del: lexer.simps)
  apply(simp only: lexer.simps)
  apply(case_tac "lexer (der a r) s = None")
   apply(auto)[1]
  apply(simp)
  apply(erule exE)
  apply(simp)
  apply(rule iffI)
  apply(simp add: Posix_injval)
  apply(simp add: Posix1(1))
done 

lemma lexer_correctness:
  shows "(lexer r s = Some v) \<longleftrightarrow> s \<in> r \<rightarrow> v"
  and   "(lexer r s = None) \<longleftrightarrow> \<not>(\<exists>v. s \<in> r \<rightarrow> v)"
using Posix1(1) Posix_determ lexer_correct_None lexer_correct_Some apply fastforce
using Posix1(1) lexer_correct_None lexer_correct_Some by blast




fun flex :: "rexp \<Rightarrow> (val \<Rightarrow> val) => string \<Rightarrow> (val \<Rightarrow> val)"
  where
  "flex r f [] = f"
| "flex r f (c#s) = flex (der c r) (\<lambda>v. f (injval r c v)) s"  

lemma flex_fun_apply:
  shows "g (flex r f s v) = flex r (g o f) s v"
  apply(induct s arbitrary: g f r v)
  apply(simp_all add: comp_def)
  by meson

lemma flex_append:
  shows "flex r f (s1 @ s2) = flex (ders s1 r) (flex r f s1) s2"
  apply(induct s1 arbitrary: s2 r f)
  apply(simp_all)
  done  

lemma lexer_flex:
  shows "lexer r s = (if nullable (ders s r) 
                      then Some(flex r id s (mkeps (ders s r))) else None)"
  apply(induct s arbitrary: r)
  apply(simp_all add: flex_fun_apply)
  done  

unused_thms

end