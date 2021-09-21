
theory DistinctBy
  imports "Lexer" 
begin

section \<open>Bit-Encodings\<close>

datatype bit = Z | S

fun 
  code :: "val \<Rightarrow> bit list"
where
  "code Void = []"
| "code (Char c) = []"
| "code (Left v) = Z # (code v)"
| "code (Right v) = S # (code v)"
| "code (Seq v1 v2) = (code v1) @ (code v2)"
| "code (Stars []) = [S]"
| "code (Stars (v # vs)) =  (Z # code v) @ code (Stars vs)"


fun 
  Stars_add :: "val \<Rightarrow> val \<Rightarrow> val"
where
  "Stars_add v (Stars vs) = Stars (v # vs)"

function
  decode' :: "bit list \<Rightarrow> rexp \<Rightarrow> (val * bit list)"
where
  "decode' ds ZERO = (Void, [])"
| "decode' ds ONE = (Void, ds)"
| "decode' ds (CR d) = (Char d, ds)"
| "decode' [] (ALT r1 r2) = (Void, [])"
| "decode' (Z # ds) (ALT r1 r2) = (let (v, ds') = decode' ds r1 in (Left v, ds'))"
| "decode' (S # ds) (ALT r1 r2) = (let (v, ds') = decode' ds r2 in (Right v, ds'))"
| "decode' ds (SEQ r1 r2) = (let (v1, ds') = decode' ds r1 in
                             let (v2, ds'') = decode' ds' r2 in (Seq v1 v2, ds''))"
| "decode' [] (STAR r) = (Void, [])"
| "decode' (S # ds) (STAR r) = (Stars [], ds)"
| "decode' (Z # ds) (STAR r) = (let (v, ds') = decode' ds r in
                                    let (vs, ds'') = decode' ds' (STAR r) 
                                    in (Stars_add v vs, ds''))"
by pat_completeness auto

lemma decode'_smaller:
  assumes "decode'_dom (ds, r)"
  shows "length (snd (decode' ds r)) \<le> length ds"
using assms
apply(induct ds r)
apply(auto simp add: decode'.psimps split: prod.split)
using dual_order.trans apply blast
by (meson dual_order.trans le_SucI)

termination "decode'"  
apply(relation "inv_image (measure(%cs. size cs) <*lex*> measure(%s. size s)) (%(ds,r). (r,ds))") 
apply(auto dest!: decode'_smaller)
by (metis less_Suc_eq_le snd_conv)

definition
  decode :: "bit list \<Rightarrow> rexp \<Rightarrow> val option"
where
  "decode ds r \<equiv> (let (v, ds') = decode' ds r 
                  in (if ds' = [] then Some v else None))"

lemma decode'_code_Stars:
  assumes "\<forall>v\<in>set vs. \<Turnstile> v : r \<and> (\<forall>x. decode' (code v @ x) r = (v, x)) \<and> flat v \<noteq> []" 
  shows "decode' (code (Stars vs) @ ds) (STAR r) = (Stars vs, ds)"
  using assms
  apply(induct vs)
  apply(auto)
  done

lemma decode'_code:
  assumes "\<Turnstile> v : r"
  shows "decode' ((code v) @ ds) r = (v, ds)"
using assms
  apply(induct v r arbitrary: ds) 
  apply(auto)
  using decode'_code_Stars by blast

lemma decode_code:
  assumes "\<Turnstile> v : r"
  shows "decode (code v) r = Some v"
  using assms unfolding decode_def
  by (smt append_Nil2 decode'_code old.prod.case)


section {* Annotated Regular Expressions *}

datatype arexp = 
  AZERO
| AONE "bit list"
| ACHAR "bit list" char
| ASEQ "bit list" arexp arexp
| AALTs "bit list" "arexp list"
| ASTAR "bit list" arexp

abbreviation
  "AALT bs r1 r2 \<equiv> AALTs bs [r1, r2]"

fun asize :: "arexp \<Rightarrow> nat" where
  "asize AZERO = 1"
| "asize (AONE cs) = 1" 
| "asize (ACHAR cs c) = 1"
| "asize (AALTs cs rs) = Suc (sum_list (map asize rs))"
| "asize (ASEQ cs r1 r2) = Suc (asize r1 + asize r2)"
| "asize (ASTAR cs r) = Suc (asize r)"

fun 
  erase :: "arexp \<Rightarrow> rexp"
where
  "erase AZERO = ZERO"
| "erase (AONE _) = ONE"
| "erase (ACHAR _ c) = CR c"
| "erase (AALTs _ []) = ZERO"
| "erase (AALTs _ [r]) = (erase r)"
| "erase (AALTs bs (r#rs)) = ALT (erase r) (erase (AALTs bs rs))"
| "erase (ASEQ _ r1 r2) = SEQ (erase r1) (erase r2)"
| "erase (ASTAR _ r) = STAR (erase r)"



lemma decode_code_erase:
  assumes "\<Turnstile> v : (erase  a)"
  shows "decode (code v) (erase a) = Some v"
  using assms
  by (simp add: decode_code) 


fun nonalt :: "arexp \<Rightarrow> bool"
  where
  "nonalt (AALTs bs2 rs) = False"
| "nonalt r = True"


fun good :: "arexp \<Rightarrow> bool" where
  "good AZERO = False"
| "good (AONE cs) = True" 
| "good (ACHAR cs c) = True"
| "good (AALTs cs []) = False"
| "good (AALTs cs [r]) = False"
| "good (AALTs cs (r1#r2#rs)) = (\<forall>r' \<in> set (r1#r2#rs). good r' \<and> nonalt r')"
| "good (ASEQ _ AZERO _) = False"
| "good (ASEQ _ (AONE _) _) = False"
| "good (ASEQ _ _ AZERO) = False"
| "good (ASEQ cs r1 r2) = (good r1 \<and> good r2)"
| "good (ASTAR cs r) = True"




fun fuse :: "bit list \<Rightarrow> arexp \<Rightarrow> arexp" where
  "fuse bs AZERO = AZERO"
| "fuse bs (AONE cs) = AONE (bs @ cs)" 
| "fuse bs (ACHAR cs c) = ACHAR (bs @ cs) c"
| "fuse bs (AALTs cs rs) = AALTs (bs @ cs) rs"
| "fuse bs (ASEQ cs r1 r2) = ASEQ (bs @ cs) r1 r2"
| "fuse bs (ASTAR cs r) = ASTAR (bs @ cs) r"

lemma fuse_append:
  shows "fuse (bs1 @ bs2) r = fuse bs1 (fuse bs2 r)"
  apply(induct r)
  apply(auto)
  done


fun intern :: "rexp \<Rightarrow> arexp" where
  "intern ZERO = AZERO"
| "intern ONE = AONE []"
| "intern (CR c) = ACHAR [] c"
| "intern (ALT r1 r2) = AALT [] (fuse [Z] (intern r1)) 
                                (fuse [S]  (intern r2))"
| "intern (SEQ r1 r2) = ASEQ [] (intern r1) (intern r2)"
| "intern (STAR r) = ASTAR [] (intern r)"


fun retrieve :: "arexp \<Rightarrow> val \<Rightarrow> bit list" where
  "retrieve (AONE bs) Void = bs"
| "retrieve (ACHAR bs c) (Char d) = bs"
| "retrieve (AALTs bs [r]) v = bs @ retrieve r v" 
| "retrieve (AALTs bs (r#rs)) (Left v) = bs @ retrieve r v"
| "retrieve (AALTs bs (r#rs)) (Right v) = bs @ retrieve (AALTs [] rs) v"
| "retrieve (ASEQ bs r1 r2) (Seq v1 v2) = bs @ retrieve r1 v1 @ retrieve r2 v2"
| "retrieve (ASTAR bs r) (Stars []) = bs @ [S]"
| "retrieve (ASTAR bs r) (Stars (v#vs)) = 
     bs @ [Z] @ retrieve r v @ retrieve (ASTAR [] r) (Stars vs)"



fun
 bnullable :: "arexp \<Rightarrow> bool"
where
  "bnullable (AZERO) = False"
| "bnullable (AONE bs) = True"
| "bnullable (ACHAR bs c) = False"
| "bnullable (AALTs bs rs) = (\<exists>r \<in> set rs. bnullable r)"
| "bnullable (ASEQ bs r1 r2) = (bnullable r1 \<and> bnullable r2)"
| "bnullable (ASTAR bs r) = True"

fun 
  bmkeps :: "arexp \<Rightarrow> bit list"
where
  "bmkeps(AONE bs) = bs"
| "bmkeps(ASEQ bs r1 r2) = bs @ (bmkeps r1) @ (bmkeps r2)"
| "bmkeps(AALTs bs [r]) = bs @ (bmkeps r)"
| "bmkeps(AALTs bs (r#rs)) = (if bnullable(r) then bs @ (bmkeps r) else (bmkeps (AALTs bs rs)))"
| "bmkeps(ASTAR bs r) = bs @ [S]"


fun
 bder :: "char \<Rightarrow> arexp \<Rightarrow> arexp"
where
  "bder c (AZERO) = AZERO"
| "bder c (AONE bs) = AZERO"
| "bder c (ACHAR bs d) = (if c = d then AONE bs else AZERO)"
| "bder c (AALTs bs rs) = AALTs bs (map (bder c) rs)"
| "bder c (ASEQ bs r1 r2) = 
     (if bnullable r1
      then AALT bs (ASEQ [] (bder c r1) r2) (fuse (bmkeps r1) (bder c r2))
      else ASEQ bs (bder c r1) r2)"
| "bder c (ASTAR bs r) = ASEQ bs (fuse [Z] (bder c r)) (ASTAR [] r)"


fun 
  bders :: "arexp \<Rightarrow> string \<Rightarrow> arexp"
where
  "bders r [] = r"
| "bders r (c#s) = bders (bder c r) s"

lemma bders_append:
  "bders r (s1 @ s2) = bders (bders r s1) s2"
  apply(induct s1 arbitrary: r s2)
  apply(simp_all)
  done

lemma bnullable_correctness:
  shows "nullable (erase r) = bnullable r"
  apply(induct r rule: erase.induct)
  apply(simp_all)
  done

lemma erase_fuse:
  shows "erase (fuse bs r) = erase r"
  apply(induct r rule: erase.induct)
  apply(simp_all)
  done

thm Posix.induct

lemma erase_intern [simp]:
  shows "erase (intern r) = r"
  apply(induct r)
  apply(simp_all add: erase_fuse)
  done

lemma erase_bder [simp]:
  shows "erase (bder a r) = der a (erase r)"
  apply(induct r rule: erase.induct)
  apply(simp_all add: erase_fuse bnullable_correctness)
  done

lemma erase_bders [simp]:
  shows "erase (bders r s) = ders s (erase r)"
  apply(induct s arbitrary: r )
  apply(simp_all)
  done

lemma retrieve_encode_STARS:
  assumes "\<forall>v\<in>set vs. \<Turnstile> v : r \<and> code v = retrieve (intern r) v"
  shows "code (Stars vs) = retrieve (ASTAR [] (intern r)) (Stars vs)"
  using assms
  apply(induct vs)
  apply(simp_all)
  done

lemma retrieve_fuse2:
  assumes "\<Turnstile> v : (erase r)"
  shows "retrieve (fuse bs r) v = bs @ retrieve r v"
  using assms
  apply(induct r arbitrary: v bs)
         apply(auto elim: Prf_elims)[4]
   defer
  using retrieve_encode_STARS
   apply(auto elim!: Prf_elims)[1]
   apply(case_tac vs)
    apply(simp)
   apply(simp)
  (* AALTs  case *)
  apply(simp)
  apply(case_tac x2a)
   apply(simp)
   apply(auto elim!: Prf_elims)[1]
  apply(simp)
   apply(case_tac list)
   apply(simp)
  apply(auto)
  apply(auto elim!: Prf_elims)[1]
  done

lemma retrieve_fuse:
  assumes "\<Turnstile> v : r"
  shows "retrieve (fuse bs (intern r)) v = bs @ retrieve (intern r) v"
  using assms 
  by (simp_all add: retrieve_fuse2)


lemma retrieve_code:
  assumes "\<Turnstile> v : r"
  shows "code v = retrieve (intern r) v"
  using assms
  apply(induct v r )
  apply(simp_all add: retrieve_fuse retrieve_encode_STARS)
  done

lemma r:
  assumes "bnullable (AALTs bs (a # rs))"
  shows "bnullable a \<or> (\<not> bnullable a \<and> bnullable (AALTs bs rs))"
  using assms
  apply(induct rs)
   apply(auto)
  done

lemma bnullable_Hdbmkeps_Hd:
  assumes "bnullable a" 
  shows  "bmkeps (AALTs bs (a # rs)) = bs @ (bmkeps a)"
  using assms
  by (metis bmkeps.simps(3) bmkeps.simps(4) list.exhaust)

lemma r1:
  assumes "\<not> bnullable a" "bnullable (AALTs bs rs)"
  shows  "bmkeps (AALTs bs (a # rs)) = bmkeps (AALTs bs rs)"
  using assms
  apply(induct rs)
   apply(auto)
  done

lemma r2:
  assumes "x \<in> set rs" "bnullable x"
  shows "bnullable (AALTs bs rs)"
  using assms
  apply(induct rs)
   apply(auto)
  done

lemma  r3:
  assumes "\<not> bnullable r" 
          " \<exists> x \<in> set rs. bnullable x"
  shows "retrieve (AALTs bs rs) (mkeps (erase (AALTs bs rs))) =
         retrieve (AALTs bs (r # rs)) (mkeps (erase (AALTs bs (r # rs))))"
  using assms
  apply(induct rs arbitrary: r bs)
   apply(auto)[1]
  apply(auto)
  using bnullable_correctness apply blast
    apply(auto simp add: bnullable_correctness mkeps_nullable retrieve_fuse2)
   apply(subst retrieve_fuse2[symmetric])
  apply (smt bnullable.simps(4) bnullable_correctness erase.simps(5) erase.simps(6) insert_iff list.exhaust list.set(2) mkeps.simps(3) mkeps_nullable)
   apply(simp)
  apply(case_tac "bnullable a")
  apply (smt append_Nil2 bnullable.simps(4) bnullable_correctness erase.simps(5) erase.simps(6) fuse.simps(4) insert_iff list.exhaust list.set(2) mkeps.simps(3) mkeps_nullable retrieve_fuse2)
  apply(drule_tac x="a" in meta_spec)
  apply(drule_tac x="bs" in meta_spec)
  apply(drule meta_mp)
   apply(simp)
  apply(drule meta_mp)
   apply(auto)
  apply(subst retrieve_fuse2[symmetric])
  apply(case_tac rs)
    apply(simp)
   apply(auto)[1]
      apply (simp add: bnullable_correctness)
  apply (metis append_Nil2 bnullable_correctness erase_fuse fuse.simps(4) list.set_intros(1) mkeps.simps(3) mkeps_nullable nullable.simps(4) r2)
    apply (simp add: bnullable_correctness)
  apply (metis append_Nil2 bnullable_correctness erase.simps(6) erase_fuse fuse.simps(4) list.set_intros(2) mkeps.simps(3) mkeps_nullable r2)
  apply(simp)
  done


lemma t: 
  assumes "\<forall>r \<in> set rs. nullable (erase r) \<longrightarrow> bmkeps r = retrieve r (mkeps (erase r))" 
          "nullable (erase (AALTs bs rs))"
  shows " bmkeps (AALTs bs rs) = retrieve (AALTs bs rs) (mkeps (erase (AALTs bs rs)))"
  using assms
  apply(induct rs arbitrary: bs)
   apply(simp)
  apply(auto simp add: bnullable_correctness)
   apply(case_tac rs)
     apply(auto simp add: bnullable_correctness)[2]
   apply(subst r1)
     apply(simp)
    apply(rule r2)
     apply(assumption)
    apply(simp)
   apply(drule_tac x="bs" in meta_spec)
   apply(drule meta_mp)
    apply(auto)[1]
   prefer 2
  apply(case_tac "bnullable a")
    apply(subst bnullable_Hdbmkeps_Hd)
     apply blast
    apply(subgoal_tac "nullable (erase a)")
  prefer 2
  using bnullable_correctness apply blast
  apply (metis (no_types, lifting) erase.simps(5) erase.simps(6) list.exhaust mkeps.simps(3) retrieve.simps(3) retrieve.simps(4))
  apply(subst r1)
     apply(simp)
  using r2 apply blast
  apply(drule_tac x="bs" in meta_spec)
   apply(drule meta_mp)
    apply(auto)[1]
   apply(simp)
  using r3 apply blast
  apply(auto)
  using r3 by blast

lemma bmkeps_retrieve:
  assumes "nullable (erase r)"
  shows "bmkeps r = retrieve r (mkeps (erase r))"
  using assms
  apply(induct r)
         apply(simp)
        apply(simp)
       apply(simp)
    apply(simp)
   defer
   apply(simp)
  apply(rule t)
   apply(auto)
  done

lemma bder_retrieve:
  assumes "\<Turnstile> v : der c (erase r)"
  shows "retrieve (bder c r) v = retrieve r (injval (erase r) c v)"
  using assms
  apply(induct r arbitrary: v rule: erase.induct)
         apply(simp)
         apply(erule Prf_elims)
        apply(simp)
        apply(erule Prf_elims) 
        apply(simp)
      apply(case_tac "c = ca")
       apply(simp)
       apply(erule Prf_elims)
       apply(simp)
      apply(simp)
       apply(erule Prf_elims)
  apply(simp)
      apply(erule Prf_elims)
     apply(simp)
    apply(simp)
  apply(rename_tac "r\<^sub>1" "r\<^sub>2" rs v)
    apply(erule Prf_elims)
     apply(simp)
    apply(simp)
    apply(case_tac rs)
     apply(simp)
    apply(simp)
  apply (smt Prf_elims(3) injval.simps(2) injval.simps(3) retrieve.simps(4) retrieve.simps(5) same_append_eq)
   apply(simp)
   apply(case_tac "nullable (erase r1)")
    apply(simp)
  apply(erule Prf_elims)
     apply(subgoal_tac "bnullable r1")
  prefer 2
  using bnullable_correctness apply blast
    apply(simp)
     apply(erule Prf_elims)
     apply(simp)
   apply(subgoal_tac "bnullable r1")
  prefer 2
  using bnullable_correctness apply blast
    apply(simp)
    apply(simp add: retrieve_fuse2)
    apply(simp add: bmkeps_retrieve)
   apply(simp)
   apply(erule Prf_elims)
   apply(simp)
  using bnullable_correctness apply blast
  apply(rename_tac bs r v)
  apply(simp)
  apply(erule Prf_elims)
     apply(clarify)
  apply(erule Prf_elims)
  apply(clarify)
  apply(subst injval.simps)
  apply(simp del: retrieve.simps)
  apply(subst retrieve.simps)
  apply(subst retrieve.simps)
  apply(simp)
  apply(simp add: retrieve_fuse2)
  done
  


lemma MAIN_decode:
  assumes "\<Turnstile> v : ders s r"
  shows "Some (flex r id s v) = decode (retrieve (bders (intern r) s) v) r"
  using assms
proof (induct s arbitrary: v rule: rev_induct)
  case Nil
  have "\<Turnstile> v : ders [] r" by fact
  then have "\<Turnstile> v : r" by simp
  then have "Some v = decode (retrieve (intern r) v) r"
    using decode_code retrieve_code by auto
  then show "Some (flex r id [] v) = decode (retrieve (bders (intern r) []) v) r"
    by simp
next
  case (snoc c s v)
  have IH: "\<And>v. \<Turnstile> v : ders s r \<Longrightarrow> 
     Some (flex r id s v) = decode (retrieve (bders (intern r) s) v) r" by fact
  have asm: "\<Turnstile> v : ders (s @ [c]) r" by fact
  then have asm2: "\<Turnstile> injval (ders s r) c v : ders s r" 
    by (simp add: Prf_injval ders_append)
  have "Some (flex r id (s @ [c]) v) = Some (flex r id s (injval (ders s r) c v))"
    by (simp add: flex_append)
  also have "... = decode (retrieve (bders (intern r) s) (injval (ders s r) c v)) r"
    using asm2 IH by simp
  also have "... = decode (retrieve (bder c (bders (intern r) s)) v) r"
    using asm by (simp_all add: bder_retrieve ders_append)
  finally show "Some (flex r id (s @ [c]) v) = 
                 decode (retrieve (bders (intern r) (s @ [c])) v) r" by (simp add: bders_append)
qed


definition blex where
 "blex a s \<equiv> if bnullable (bders a s) then Some (bmkeps (bders a s)) else None"



definition blexer where
 "blexer r s \<equiv> if bnullable (bders (intern r) s) then 
                decode (bmkeps (bders (intern r) s)) r else None"

lemma blexer_correctness:
  shows "blexer r s = lexer r s"
proof -
  { define bds where "bds \<equiv> bders (intern r) s"
    define ds  where "ds \<equiv> ders s r"
    assume asm: "nullable ds"
    have era: "erase bds = ds" 
      unfolding ds_def bds_def by simp
    have mke: "\<Turnstile> mkeps ds : ds"
      using asm by (simp add: mkeps_nullable)
    have "decode (bmkeps bds) r = decode (retrieve bds (mkeps ds)) r"
      using bmkeps_retrieve
      using asm era by (simp add: bmkeps_retrieve)
    also have "... =  Some (flex r id s (mkeps ds))"
      using mke by (simp_all add: MAIN_decode ds_def bds_def)
    finally have "decode (bmkeps bds) r = Some (flex r id s (mkeps ds))" 
      unfolding bds_def ds_def .
  }
  then show "blexer r s = lexer r s"
    unfolding blexer_def lexer_flex
    apply(subst bnullable_correctness[symmetric])
    apply(simp)
    done
qed


fun distinctBy :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b set \<Rightarrow> 'a list"
  where
  "distinctBy [] f acc = []"
| "distinctBy (x#xs) f acc = 
     (if (f x) \<in> acc then distinctBy xs f acc 
      else x # (distinctBy xs f ({f x} \<union> acc)))"

fun flts :: "arexp list \<Rightarrow> arexp list"
  where 
  "flts [] = []"
| "flts (AZERO # rs) = flts rs"
| "flts ((AALTs bs  rs1) # rs) = (map (fuse bs) rs1) @ flts rs"
| "flts (r1 # rs) = r1 # flts rs"




fun li :: "bit list \<Rightarrow> arexp list \<Rightarrow> arexp"
  where
  "li _ [] = AZERO"
| "li bs [a] = fuse bs a"
| "li bs as = AALTs bs as"




fun bsimp_ASEQ :: "bit list \<Rightarrow> arexp \<Rightarrow> arexp \<Rightarrow> arexp"
  where
  "bsimp_ASEQ _ AZERO _ = AZERO"
| "bsimp_ASEQ _ _ AZERO = AZERO"
| "bsimp_ASEQ bs1 (AONE bs2) r2 = fuse (bs1 @ bs2) r2"
| "bsimp_ASEQ bs1 r1 r2 = ASEQ  bs1 r1 r2"


fun bsimp_AALTs :: "bit list \<Rightarrow> arexp list \<Rightarrow> arexp"
  where
  "bsimp_AALTs _ [] = AZERO"
| "bsimp_AALTs bs1 [r] = fuse bs1 r"
| "bsimp_AALTs bs1 rs = AALTs bs1 rs"


fun bsimp :: "arexp \<Rightarrow> arexp" 
  where
  "bsimp (ASEQ bs1 r1 r2) = bsimp_ASEQ bs1 (bsimp r1) (bsimp r2)"
| "bsimp (AALTs bs1 rs) = bsimp_AALTs bs1 (distinctBy  (flts (map bsimp rs)) erase {} ) "
| "bsimp r = r"




fun 
  bders_simp :: "arexp \<Rightarrow> string \<Rightarrow> arexp"
where
  "bders_simp r [] = r"
| "bders_simp r (c # s) = bders_simp (bsimp (bder c r)) s"

definition blexer_simp where
 "blexer_simp r s \<equiv> if bnullable (bders_simp (intern r) s) then 
                decode (bmkeps (bders_simp (intern r) s)) r else None"


lemma asize0:
  shows "0 < asize r"
  apply(induct  r)
       apply(auto)
  done


lemma bders_simp_append:
  shows "bders_simp r (s1 @ s2) = bders_simp (bders_simp r s1) s2"
  apply(induct s1 arbitrary: r s2)
   apply(simp)
  apply(simp)
  done

lemma bsimp_ASEQ_size:
  shows "asize (bsimp_ASEQ bs r1 r2) \<le> Suc (asize r1 + asize r2)"
  apply(induct bs r1 r2 rule: bsimp_ASEQ.induct)
  apply(auto)
  done

lemma fuse_size:
  shows "asize (fuse bs r) = asize r"
  apply(induct r)
  apply(auto)
  done

lemma flts_size:
  shows "sum_list (map asize (flts rs)) \<le> sum_list (map asize rs)"
  apply(induct rs rule: flts.induct)
        apply(simp_all)
  by (metis (mono_tags, lifting) add_mono comp_apply eq_imp_le fuse_size le_SucI map_eq_conv)
  

lemma bsimp_AALTs_size:
  shows "asize (bsimp_AALTs bs rs) \<le> Suc (sum_list (map asize rs))"
  apply(induct rs rule: bsimp_AALTs.induct)
  apply(auto simp add: fuse_size)
  done

lemma dB_size: "sum_list (map asize (distinctBy rs erase rset) ) \<le> sum_list (map asize rs)"
  apply(induction rs arbitrary: rset)
   apply auto[1]
  apply simp
  sledgehammer
  using trans_le_add2 by blast
 

lemma bsimp_size:
  shows "asize (bsimp r) \<le> asize r"
  apply(induct r)
       apply(simp_all)
   apply (meson Suc_le_mono add_mono_thms_linordered_semiring(1) bsimp_ASEQ_size le_trans)
  apply(rule le_trans)
   apply(rule bsimp_AALTs_size)
  apply(simp)
  apply(rule le_trans)
   apply(rule dB_size)
  apply(rule le_trans)
   apply(rule flts_size)
  by (simp add: sum_list_mono)

lemma bsimp_asize0:
  shows "(\<Sum>x\<leftarrow>rs. asize (bsimp x)) \<le> sum_list (map asize rs)"
  apply(induct rs)
   apply(auto)
  by (simp add: add_mono bsimp_size)

lemma bsimp_AALTs_size2:
  assumes "\<forall>r \<in> set  rs. nonalt r"
  shows "asize (bsimp_AALTs bs rs) \<ge> sum_list (map asize rs)"
  using assms
  apply(induct rs rule: bsimp_AALTs.induct)
    apply(simp_all add: fuse_size)
  done


lemma qq:
  shows "map (asize \<circ> fuse bs) rs = map asize rs"
  apply(induct rs)
   apply(auto simp add: fuse_size)
  done

lemma flts_size2:
  assumes "\<exists>bs rs'. AALTs bs  rs' \<in> set rs"
  shows "sum_list (map asize (flts rs)) < sum_list (map asize rs)"
  using assms
  apply(induct rs)
   apply(auto simp add: qq)
   apply (simp add: flts_size less_Suc_eq_le)
  apply(case_tac a)
       apply(auto simp add: qq)
   prefer 2
   apply (simp add: flts_size le_imp_less_Suc)
  using less_Suc_eq by auto

lemma bsimp_AALTs_size3:
  assumes "\<exists>r \<in> set  (map bsimp rs). \<not>nonalt r"
  shows "asize (bsimp (AALTs bs rs)) < asize (AALTs bs rs)"
  using assms flts_size2
  apply  -
  apply(clarify)
  apply(simp)
  apply(drule_tac x="map bsimp rs" in meta_spec)
  apply(drule meta_mp)
  apply (metis list.set_map nonalt.elims(3))
  apply(simp)
  apply(rule order_class.order.strict_trans1)
   apply(rule bsimp_AALTs_size)
  apply(simp)
  by (metis (mono_tags, lifting) bsimp_asize0 comp_apply dB_size le_less_trans map_eq_conv not_less_iff_gr_or_eq)



lemma L_bsimp_ASEQ:
  "L (SEQ (erase r1) (erase r2)) = L (erase (bsimp_ASEQ bs r1 r2))"
  apply(induct bs r1 r2 rule: bsimp_ASEQ.induct)
  apply(simp_all)
  by (metis erase_fuse fuse.simps(4))

lemma L_bsimp_AALTs:
  "L (erase (AALTs bs rs)) = L (erase (bsimp_AALTs bs rs))"
  apply(induct bs rs rule: bsimp_AALTs.induct)
  apply(simp_all add: erase_fuse)
  done

lemma L_erase_AALTs:
  shows "L (erase (AALTs bs rs)) = \<Union> (L ` erase ` (set rs))"
  apply(induct rs)
   apply(simp)
  apply(simp)
  apply(case_tac rs)
   apply(simp)
  apply(simp)
  done

lemma L_erase_flts:
  shows "\<Union> (L ` erase ` (set (flts rs))) = \<Union> (L ` erase ` (set rs))"
  apply(induct rs rule: flts.induct)
        apply(simp_all)
  apply(auto)
  using L_erase_AALTs erase_fuse apply auto[1]
  by (simp add: L_erase_AALTs erase_fuse)

lemma L_erase_dB_acc:
  shows "( \<Union>(L ` acc) \<union> ( \<Union> (L ` erase ` (set (distinctBy rs erase acc) ) ) )) = \<Union>(L ` acc) \<union>  \<Union> (L ` erase ` (set rs))"
  apply(induction rs arbitrary: acc)
   apply simp
  apply simp
  by (smt (z3) SUP_absorb UN_insert sup_assoc sup_commute)

lemma L_erase_dB:
  shows " ( \<Union> (L ` erase ` (set (distinctBy rs erase {}) ) ) ) = \<Union> (L ` erase ` (set rs))"
  by (metis L_erase_dB_acc Un_commute Union_image_empty)

lemma L_bsimp_erase:
  shows "L (erase r) = L (erase (bsimp r))"
  apply(induct r)
  apply(simp)
  apply(simp)
  apply(simp)
  apply(auto simp add: Sequ_def)[1]
  apply(subst L_bsimp_ASEQ[symmetric])
  apply(auto simp add: Sequ_def)[1]
  apply(subst (asm)  L_bsimp_ASEQ[symmetric])
  apply(auto simp add: Sequ_def)[1]
   apply(simp)
   apply(subst L_bsimp_AALTs[symmetric])
   defer
   apply(simp)
  apply(subst (2)L_erase_AALTs)
  apply(subst L_erase_dB)
  apply(subst L_erase_flts)
  apply(auto)
   apply (simp add: L_erase_AALTs)
  using L_erase_AALTs by blast

lemma bsimp_ASEQ0:
  shows "bsimp_ASEQ bs r1 AZERO = AZERO"
  apply(induct r1)
  apply(auto)
  done



lemma bsimp_ASEQ1:
  assumes "r1 \<noteq> AZERO" "r2 \<noteq> AZERO" "\<forall>bs. r1 \<noteq> AONE bs"
  shows "bsimp_ASEQ bs r1 r2 = ASEQ bs r1 r2"
  using assms
  apply(induct bs r1 r2 rule: bsimp_ASEQ.induct)
  apply(auto)
  done

lemma bsimp_ASEQ2:
  shows "bsimp_ASEQ bs (AONE bs1) r2 = fuse (bs @ bs1) r2"
  apply(induct r2)
  apply(auto)
  done


lemma L_bders_simp:
  shows "L (erase (bders_simp r s)) = L (erase (bders r s))"
  apply(induct s arbitrary: r rule: rev_induct)
   apply(simp)
  apply(simp)
  apply(simp add: ders_append)
  apply(simp add: bders_simp_append)
  apply(simp add: L_bsimp_erase[symmetric])
  by (simp add: der_correctness)

lemma b1:
  "bsimp_ASEQ bs1 (AONE bs) r =  fuse (bs1 @ bs) r" 
  apply(induct r)
       apply(auto)
  done

lemma b2:
  assumes "bnullable r"
  shows "bmkeps (fuse bs r) = bs @ bmkeps r"
  by (simp add: assms bmkeps_retrieve bnullable_correctness erase_fuse mkeps_nullable retrieve_fuse2)

lemma b3:
  shows "bnullable r = bnullable (bsimp r)"
  using L_bsimp_erase bnullable_correctness nullable_correctness by auto


lemma b4:
  shows "bnullable (bders_simp r s) = bnullable (bders r s)"
  by (metis L_bders_simp bnullable_correctness lexer.simps(1) lexer_correct_None option.distinct(1))

lemma q1:
  assumes "\<forall>r \<in> set rs. bmkeps(bsimp r) = bmkeps r"
  shows "map (\<lambda>r. bmkeps(bsimp r)) rs = map bmkeps rs"
  using assms
  apply(induct rs)
  apply(simp)
  apply(simp)
  done

lemma q3:
  assumes "\<exists>r \<in> set rs. bnullable r"
  shows "bmkeps (AALTs bs rs) = bmkeps (bsimp_AALTs bs rs)"
  using assms
  apply(induct bs rs rule: bsimp_AALTs.induct)
    apply(simp)
   apply(simp)
  apply (simp add: b2)
  apply(simp)
  done

lemma qq1:
  assumes "\<exists>r \<in> set rs. bnullable r"
  shows "bmkeps (AALTs bs (rs @ rs1)) = bmkeps (AALTs bs rs)"
  using assms
  apply(induct rs arbitrary: rs1 bs)
  apply(simp)
  apply(simp)
  by (metis Nil_is_append_conv bmkeps.simps(4) neq_Nil_conv bnullable_Hdbmkeps_Hd split_list_last)

lemma qq2:
  assumes "\<forall>r \<in> set rs. \<not> bnullable r" "\<exists>r \<in> set rs1. bnullable r"
  shows "bmkeps (AALTs bs (rs @ rs1)) = bmkeps (AALTs bs rs1)"
  using assms
  apply(induct rs arbitrary: rs1 bs)
  apply(simp)
  apply(simp)
  by (metis append_assoc in_set_conv_decomp r1 r2)
  
lemma qq3:
  shows "bnullable (AALTs bs rs) = (\<exists>r \<in> set rs. bnullable r)"
  apply(induct rs arbitrary: bs)
  apply(simp)
  apply(simp)
  done

lemma fuse_empty:
  shows "fuse [] r = r"
  apply(induct r)
       apply(auto)
  done

lemma flts_fuse:
  shows "map (fuse bs) (flts rs) = flts (map (fuse bs) rs)"
  apply(induct rs arbitrary: bs rule: flts.induct)
        apply(auto simp add: fuse_append)
  done

lemma bsimp_ASEQ_fuse:
  shows "fuse bs1 (bsimp_ASEQ bs2 r1 r2) = bsimp_ASEQ (bs1 @ bs2) r1 r2"
  apply(induct r1 r2 arbitrary: bs1 bs2 rule: bsimp_ASEQ.induct)
  apply(auto)
  done

lemma bsimp_AALTs_fuse:
  assumes "\<forall>r \<in> set rs. fuse bs1 (fuse bs2 r) = fuse (bs1 @ bs2) r"
  shows "fuse bs1 (bsimp_AALTs bs2 rs) = bsimp_AALTs (bs1 @ bs2) rs"
  using assms
  apply(induct bs2 rs arbitrary: bs1 rule: bsimp_AALTs.induct)
  apply(auto)
  done



lemma bsimp_fuse:
  shows "fuse bs (bsimp r) = bsimp (fuse bs r)"
apply(induct r arbitrary: bs)
       apply(simp)
      apply(simp)
     apply(simp)
    prefer 3
    apply(simp)
   apply(simp)
   apply (simp add: bsimp_ASEQ_fuse)
  apply(simp)
  by (simp add: bsimp_AALTs_fuse fuse_append)

lemma bsimp_fuse_AALTs:
  shows "fuse bs (bsimp (AALTs [] rs)) = bsimp (AALTs bs rs)"
  apply(subst bsimp_fuse) 
  apply(simp)
  done

lemma bsimp_fuse_AALTs2:
  shows "fuse bs (bsimp_AALTs [] rs) = bsimp_AALTs bs rs"
  using bsimp_AALTs_fuse fuse_append by auto
  

lemma bsimp_ASEQ_idem:
  assumes "bsimp (bsimp r1) = bsimp r1" "bsimp (bsimp r2) = bsimp r2"
  shows "bsimp (bsimp_ASEQ x1 (bsimp r1) (bsimp r2)) = bsimp_ASEQ x1 (bsimp r1) (bsimp r2)"
  using assms
  apply(case_tac "bsimp r1 = AZERO")
    apply(simp)
 apply(case_tac "bsimp r2 = AZERO")
    apply(simp)
  apply (metis bnullable.elims(2) bnullable.elims(3) bsimp.simps(3) bsimp_ASEQ.simps(2) bsimp_ASEQ.simps(3) bsimp_ASEQ.simps(4) bsimp_ASEQ.simps(5) bsimp_ASEQ.simps(6))  
  apply(case_tac "\<exists>bs. bsimp r1 = AONE bs")
    apply(auto)[1]
    apply(subst bsimp_ASEQ2)
   apply(subst bsimp_ASEQ2)
  apply (metis assms(2) bsimp_fuse)
      apply(subst bsimp_ASEQ1)
      apply(auto)
  done


fun nonnested :: "arexp \<Rightarrow> bool"
  where
  "nonnested (AALTs bs2 []) = True"
| "nonnested (AALTs bs2 ((AALTs bs1 rs1) # rs2)) = False"
| "nonnested (AALTs bs2 (r # rs2)) = nonnested (AALTs bs2 rs2)"
| "nonnested r = True"


lemma  k0:
  shows "flts (r # rs1) = flts [r] @ flts rs1"
  apply(induct r arbitrary: rs1)
   apply(auto)
  done

lemma  k00:
  shows "flts (rs1 @ rs2) = flts rs1 @ flts rs2"
  apply(induct rs1 arbitrary: rs2)
   apply(auto)
  by (metis append.assoc k0)

lemma  k0a:
  shows "flts [AALTs bs rs] = map (fuse bs)  rs"
  apply(simp)
  done


lemma  k0b:
  assumes "nonalt r" "r \<noteq> AZERO"
  shows "flts [r] = [r]"
  using assms
  apply(case_tac  r)
  apply(simp_all)
  done

lemma nn1:
  assumes "nonnested (AALTs bs rs)"
  shows "\<nexists>bs1 rs1. flts rs = [AALTs bs1 rs1]"
  using assms
  apply(induct rs rule: flts.induct)
  apply(auto)
  done

lemma nn1q:
  assumes "nonnested (AALTs bs rs)"
  shows "\<nexists>bs1 rs1. AALTs bs1 rs1 \<in> set (flts rs)"
  using assms
  apply(induct rs rule: flts.induct)
  apply(auto)
  done

lemma nn1qq:
  assumes "nonnested (AALTs bs rs)"
  shows "\<nexists>bs1 rs1. AALTs bs1 rs1 \<in> set rs"
  using assms
  apply(induct rs rule: flts.induct)
  apply(auto)
  done

lemma nn10:
  assumes "nonnested (AALTs cs rs)" 
  shows "nonnested (AALTs (bs @ cs) rs)"
  using assms
  apply(induct rs arbitrary: cs bs)
   apply(simp_all)
  apply(case_tac a)
       apply(simp_all)
  done

lemma nn11a:
  assumes "nonalt r"
  shows "nonalt (fuse bs r)"
  using assms
  apply(induct r)
       apply(auto)
  done


lemma nn1a:
  assumes "nonnested r"
  shows "nonnested (fuse bs r)"
  using assms
  apply(induct bs r arbitrary: rule: fuse.induct)
       apply(simp_all add: nn10)
  done  

lemma n0:
  shows "nonnested (AALTs bs rs) \<longleftrightarrow> (\<forall>r \<in> set rs. nonalt r)"
  apply(induct rs  arbitrary: bs)
   apply(auto)
    apply (metis list.set_intros(1) nn1qq nonalt.elims(3))
   apply (metis list.set_intros(2) nn1qq nonalt.elims(3))
  by (metis nonalt.elims(2) nonnested.simps(3) nonnested.simps(4) nonnested.simps(5) nonnested.simps(6) nonnested.simps(7))

  
  

lemma nn1c:
  assumes "\<forall>r \<in> set rs. nonnested r"
  shows "\<forall>r \<in> set (flts rs). nonalt r"
  using assms
  apply(induct rs rule: flts.induct)
        apply(auto)
  apply(rule nn11a)
  by (metis nn1qq nonalt.elims(3))

lemma nn1bb:
  assumes "\<forall>r \<in> set rs. nonalt r"
  shows "nonnested (bsimp_AALTs bs rs)"
  using assms
  apply(induct bs rs rule: bsimp_AALTs.induct)
    apply(auto)
   apply (metis nn11a nonalt.simps(1) nonnested.elims(3))
  using n0 by auto

lemma dB_mono:
  shows "set (distinctBy rs erase acc) \<subseteq> set rs"
  apply(induction rs arbitrary: acc )
   apply simp
  apply auto
  done

lemma dB_mono1:
  shows "set (distinctBy rs erase {}) \<subseteq> set rs"
  by (meson dB_mono)

lemma contraction_prop:
  shows " \<And>x. \<lbrakk> x \<in> A \<Longrightarrow> P x; B \<subseteq> A \<rbrakk> \<Longrightarrow> x \<in> B \<Longrightarrow> P x "
  by blast

lemma dB_contraction:
  shows "  \<And>x. \<lbrakk>x \<in> set rs \<Longrightarrow> P x\<rbrakk> \<Longrightarrow> x \<in> set (distinctBy rs erase {}) \<Longrightarrow> P x"
  sledgehammer
  by (meson contraction_prop dB_mono1)

lemma nn1b:
  shows "nonnested (bsimp r)"
  apply(induct r)
       apply(simp_all)
  apply(case_tac "bsimp r1 = AZERO")
    apply(simp)
 apply(case_tac "bsimp r2 = AZERO")
   apply(simp)
    apply(subst bsimp_ASEQ0)
  apply(simp)
  apply(case_tac "\<exists>bs. bsimp r1 = AONE bs")
    apply(auto)[1]
    apply(subst bsimp_ASEQ2)
  apply (simp add: nn1a)    
   apply(subst bsimp_ASEQ1)
      apply(auto)
  apply(rule nn1bb)
  apply(auto)
  apply(subgoal_tac "x \<in> set (flts (map bsimp x2a))")
   prefer 2
   apply (meson dB_contraction)
  by (metis (mono_tags, hide_lams) imageE nn1c set_map)


lemma nn1d:
  assumes "bsimp r = AALTs bs rs"
  shows "\<forall>r1 \<in> set rs. \<forall>  bs. r1 \<noteq> AALTs bs  rs2"
  using nn1b assms
  by (metis nn1qq)

lemma nn_flts:
  assumes "nonnested (AALTs bs rs)"
  shows "\<forall>r \<in>  set (flts rs). nonalt r"
  using assms
  apply(induct rs arbitrary: bs rule: flts.induct)
        apply(auto)
  done



lemma rt:
  shows "sum_list (map asize (flts (map bsimp rs))) \<le> sum_list (map asize rs)"
  apply(induct rs)
   apply(simp)
  apply(simp)
  apply(subst  k0)
  apply(simp)
  by (smt add_le_cancel_right add_mono bsimp_size flts.simps(1) flts_size k0 le_iff_add list.simps(9) map_append sum_list.Cons sum_list.append trans_le_add1)

lemma bsimp_AALTs_qq:
  assumes "1 < length rs"
  shows "bsimp_AALTs bs rs = AALTs bs  rs"
  using  assms
  apply(case_tac rs)
   apply(simp)
  apply(case_tac list)
   apply(simp_all)
  done


lemma bsimp_AALTs1:
  assumes "nonalt r"
  shows "bsimp_AALTs bs (flts [r]) = fuse bs r"
  using  assms
  apply(case_tac r)
   apply(simp_all)
  done

lemma bbbbs:
  assumes "good r" "r = AALTs bs1 rs"
  shows "bsimp_AALTs bs (flts [r]) = AALTs bs (map (fuse bs1) rs)"
  using  assms
  by (metis (no_types, lifting) Nil_is_map_conv append.left_neutral append_butlast_last_id bsimp_AALTs.elims butlast.simps(2) good.simps(4) good.simps(5) k0a map_butlast)

lemma bbbbs1:
  shows "nonalt r \<or> (\<exists>bs rs. r  = AALTs bs rs)"
  using nonalt.elims(3) by auto
  

lemma good_fuse:
  shows "good (fuse bs r) = good r"
  apply(induct r arbitrary: bs)
       apply(auto)
     apply(case_tac r1)
          apply(simp_all)
  apply(case_tac r2)
          apply(simp_all)
  apply(case_tac r2)
            apply(simp_all)
  apply(case_tac r2)
           apply(simp_all)
  apply(case_tac r2)
          apply(simp_all)
  apply(case_tac r1)
          apply(simp_all)
  apply(case_tac r2)
           apply(simp_all)
  apply(case_tac r2)
           apply(simp_all)
  apply(case_tac r2)
           apply(simp_all)
  apply(case_tac r2)
         apply(simp_all)
  apply(case_tac x2a)
    apply(simp_all)
  apply(case_tac list)
    apply(simp_all)
  apply(case_tac x2a)
    apply(simp_all)
  apply(case_tac list)
    apply(simp_all)
  done

lemma good0:
  assumes "rs \<noteq> Nil" "\<forall>r \<in> set rs. nonalt r"
  shows "good (bsimp_AALTs bs rs) \<longleftrightarrow> (\<forall>r \<in> set rs. good r)"
  using  assms
  apply(induct bs rs rule: bsimp_AALTs.induct)
  apply(auto simp add: good_fuse)
  done


lemma flts0:
  assumes "r \<noteq> AZERO" "nonalt r"
  shows "flts [r] \<noteq> []"
  using  assms
  apply(induct r)
       apply(simp_all)
  done

lemma flts1:
  assumes "good r" 
  shows "flts [r] \<noteq> []"
  using  assms
  apply(induct r)
       apply(simp_all)
  apply(case_tac x2a)
   apply(simp)
  apply(simp)
  done

lemma flts2:
  assumes "good r" 
  shows "\<forall>r' \<in> set (flts [r]). good r' \<and> nonalt r'"
  using  assms
  apply(induct r)
       apply(simp)
      apply(simp)
     apply(simp)
    prefer 2
    apply(simp)
    apply(auto)[1]
     apply (metis bsimp_AALTs.elims good.simps(4) good.simps(5) good.simps(6) good_fuse)
  apply (metis bsimp_AALTs.elims good.simps(4) good.simps(5) good.simps(6) nn11a)
   apply fastforce
  apply(simp)
  done  


lemma flts3:
  assumes "\<forall>r \<in> set rs. good r \<or> r = AZERO" 
  shows "\<forall>r \<in> set (flts rs). good r"
  using  assms
  apply(induct rs arbitrary: rule: flts.induct)
        apply(simp_all)
  by (metis UnE flts2 k0a set_map)

lemma flts3b:
  assumes "\<exists>r\<in>set rs. good r"
  shows "flts rs \<noteq> []"
  using  assms
  apply(induct rs arbitrary: rule: flts.induct)
        apply(simp)
       apply(simp)
      apply(simp)
      apply(auto)
  done

lemma flts4:
  assumes "bsimp_AALTs bs (flts rs) = AZERO"
  shows "\<forall>r \<in> set rs. \<not> good r"
  using assms
  apply(induct rs arbitrary: bs rule: flts.induct)
        apply(auto)
        defer
  apply (metis (no_types, lifting) Nil_is_append_conv append_self_conv2 bsimp_AALTs.elims butlast.simps(2) butlast_append flts3b nonalt.simps(1) nonalt.simps(2))
  apply (metis arexp.distinct(7) bsimp_AALTs.elims flts2 good.simps(1) good.simps(2) good0 k0b list.distinct(1) list.inject nonalt.simps(3))
  apply (metis arexp.distinct(3) arexp.distinct(7) bsimp_AALTs.elims fuse.simps(3) list.distinct(1) list.inject)
  apply (metis arexp.distinct(7) bsimp_AALTs.elims good.simps(1) good_fuse list.distinct(1) list.inject)
    apply (metis arexp.distinct(7) bsimp_AALTs.elims list.distinct(1) list.inject)
  apply (metis arexp.distinct(7) bsimp_AALTs.elims flts2 good.simps(1) good.simps(33) good0 k0b list.distinct(1) list.inject nonalt.simps(6))
  by (metis (no_types, lifting) Nil_is_append_conv append_Nil2 arexp.distinct(7) bsimp_AALTs.elims butlast.simps(2) butlast_append flts1 flts2 good.simps(1) good0 k0a)


lemma flts_nil:
  assumes "\<forall>y. asize y < Suc (sum_list (map asize rs)) \<longrightarrow>
            good (bsimp y) \<or> bsimp y = AZERO"
  and "\<forall>r\<in>set rs. \<not> good (bsimp r)"
  shows "flts (map bsimp rs) = []"
  using assms
  apply(induct rs)
   apply(simp)
  apply(simp)
  apply(subst k0)
  apply(simp)
  by force

lemma flts_nil2:
  assumes "\<forall>y. asize y < Suc (sum_list (map asize rs)) \<longrightarrow>
            good (bsimp y) \<or> bsimp y = AZERO"
  and "bsimp_AALTs bs (flts (map bsimp rs)) = AZERO"
  shows "flts (map bsimp rs) = []"
  using assms
  apply(induct rs arbitrary: bs)
   apply(simp)
  apply(simp)
  apply(subst k0)
  apply(simp)
  apply(subst (asm) k0)
  apply(auto)
  apply (metis flts.simps(1) flts.simps(2) flts4 k0 less_add_Suc1 list.set_intros(1))
  by (metis flts.simps(2) flts4 k0 less_add_Suc1 list.set_intros(1))
  
  

lemma good_SEQ:
  assumes "r1 \<noteq> AZERO" "r2 \<noteq> AZERO" "\<forall>bs. r1 \<noteq> AONE bs"
  shows "good (ASEQ bs r1 r2) = (good r1 \<and> good r2)"
  using assms
  apply(case_tac r1)
       apply(simp_all)
  apply(case_tac r2)
          apply(simp_all)
  apply(case_tac r2)
         apply(simp_all)
  apply(case_tac r2)
        apply(simp_all)
  apply(case_tac r2)
       apply(simp_all)
  done

lemma dB_keeps_head:
  shows "rs = a#rs1 \<Longrightarrow> \<exists>rs1'. distinctBy rs erase {} = a#rs1'"
  apply simp
  done

lemma dB_non_empty:
  shows "rs \<noteq> [] \<Longrightarrow> distinctBy rs erase {} \<noteq> []"
  by (metis dB_keeps_head list.distinct(1) list.exhaust)

lemma good1:
  shows "good (bsimp a) \<or> bsimp a = AZERO"
  apply(induct a taking: asize rule: measure_induct)
  apply(case_tac x)
  apply(simp)
  apply(simp)
  apply(simp)
  prefer 3
    apply(simp)
   prefer 2
  (*  AALTs case  *)
  apply(simp only:)
   apply(case_tac "x52")
    apply(simp)
   (*  AALTs list at least one - case *)
   apply(simp only: )
  apply(frule_tac x="a" in spec)
   apply(drule mp)
    apply(simp)
   (* either first element is good, or AZERO *)
    apply(erule disjE)
     prefer 2
    apply(simp)
   (* in  the AZERO case, the size  is smaller *)
   apply(drule_tac x="AALTs x51 list" in spec)
   apply(drule mp)
     apply(simp add: asize0)
    apply(subst (asm) bsimp.simps)
  apply(subst (asm) bsimp.simps)
    apply(assumption)
   (* in the good case *)
  apply(frule_tac x="AALTs x51 list" in spec)
   apply(drule mp)
    apply(simp add: asize0)
   apply(erule disjE)
    apply(rule disjI1)
  apply(simp add: good0)
    apply(subst good0)
      apply(subgoal_tac "(flts (bsimp a # map bsimp list)) \<noteq> []")
  prefer 2
       apply (meson flts3b list.set_intros(1))
  using dB_non_empty apply blast
sledgehammer
      apply (metis Nil_is_append_conv flts1 k0)
  apply (metis ex_map_conv list.simps(9) nn1b nn1c)
  apply(simp)
    apply(subst k0)
    apply(simp)
    apply(auto)[1]
  using flts2 apply blast
    apply(subst  (asm) good0)
      prefer 3
      apply(auto)[1]
     apply auto[1]
    apply (metis ex_map_conv nn1b nn1c)
  (* in  the AZERO case *)
   apply(simp)
   apply(frule_tac x="a" in spec)
   apply(drule mp)
  apply(simp)
   apply(erule disjE)
    apply(rule disjI1)
    apply(subst good0)
  apply(subst k0)
  using flts1 apply blast
     apply(auto)[1]
  apply (metis (no_types, hide_lams) ex_map_conv list.simps(9) nn1b nn1c)
    apply(auto)[1]
  apply(subst (asm) k0)
  apply(auto)[1]
  using flts2 apply blast
  apply(frule_tac x="AALTs x51 list" in spec)
   apply(drule mp)
     apply(simp add: asize0)
    apply(erule disjE)
     apply(simp)
    apply(simp)
  apply (metis add.left_commute flts_nil2 less_add_Suc1 less_imp_Suc_add list.distinct(1) list.set_cases nat.inject)
   apply(subst (2) k0)
  apply(simp)
  (* SEQ case *)
  apply(simp)
  apply(case_tac "bsimp x42 = AZERO")
    apply(simp)
 apply(case_tac "bsimp x43 = AZERO")
   apply(simp)
    apply(subst (2) bsimp_ASEQ0)
  apply(simp)
  apply(case_tac "\<exists>bs. bsimp x42 = AONE bs")
    apply(auto)[1]
   apply(subst bsimp_ASEQ2)
  using good_fuse apply force
   apply(subst bsimp_ASEQ1)
     apply(auto)
  apply(subst  good_SEQ)
  apply(simp)
    apply(simp)
   apply(simp)
  using less_add_Suc1 less_add_Suc2 by blast

lemma good1a:
  assumes "L(erase a) \<noteq> {}"
  shows "good (bsimp a)"
  using good1 assms
  using L_bsimp_erase by force
  


lemma flts_append:
  "flts (xs1 @ xs2) = flts xs1 @ flts xs2"
  apply(induct xs1  arbitrary: xs2  rule: rev_induct)
   apply(auto)
  apply(case_tac xs)
   apply(auto)
   apply(case_tac x)
        apply(auto)
  apply(case_tac x)
        apply(auto)
  done

lemma g1:
  assumes "good (bsimp_AALTs bs rs)"
  shows "bsimp_AALTs bs rs = AALTs bs rs \<or> (\<exists>r. rs = [r] \<and> bsimp_AALTs bs [r] = fuse bs r)"
using assms
    apply(induct rs arbitrary: bs)
  apply(simp)
  apply(case_tac rs)
  apply(simp only:)
  apply(simp)
  apply(case_tac  list)
  apply(simp)
  by simp

lemma flts_0:
  assumes "nonnested (AALTs bs  rs)"
  shows "\<forall>r \<in> set (flts rs). r \<noteq> AZERO"
  using assms
  apply(induct rs arbitrary: bs rule: flts.induct)
        apply(simp) 
       apply(simp) 
      defer
      apply(simp) 
     apply(simp) 
    apply(simp) 
apply(simp) 
  apply(rule ballI)
  apply(simp)
  done

lemma flts_0a:
  assumes "nonnested (AALTs bs  rs)"
  shows "AZERO \<notin> set (flts rs)"
  using assms
  using flts_0 by blast 
  
lemma qqq1:
  shows "AZERO \<notin> set (flts (map bsimp rs))"
  by (metis ex_map_conv flts3 good.simps(1) good1)


fun nonazero :: "arexp \<Rightarrow> bool"
  where
  "nonazero AZERO = False"
| "nonazero r = True"

lemma flts_concat:
  shows "flts rs = concat (map (\<lambda>r. flts [r]) rs)"
  apply(induct rs)
   apply(auto)
  apply(subst k0)
  apply(simp)
  done

lemma flts_single1:
  assumes "nonalt r" "nonazero r"
  shows "flts [r] = [r]"
  using assms
  apply(induct r)
  apply(auto)
  done

lemma flts_qq:
  assumes "\<forall>y. asize y < Suc (sum_list (map asize rs)) \<longrightarrow> good y \<longrightarrow> bsimp y = y" 
          "\<forall>r'\<in>set rs. good r' \<and> nonalt r'"
  shows "flts (map bsimp rs) = rs"
  using assms
  apply(induct rs)
   apply(simp)
  apply(simp)
  apply(subst k0)
  apply(subgoal_tac "flts [bsimp a] =  [a]")
   prefer 2
   apply(drule_tac x="a" in spec)
   apply(drule mp)
    apply(simp)
   apply(auto)[1]
  using good.simps(1) k0b apply blast
  apply(auto)[1]  
  done
  
lemma test:
  assumes "good r"
  shows "bsimp r = r"
  using assms
  apply(induct r taking: "asize" rule: measure_induct)
  apply(erule good.elims)
  apply(simp_all)
  apply(subst k0)
  apply(subst (2) k0)
                apply(subst flts_qq)
                  apply(auto)[1]
                 apply(auto)[1]
                apply (metis append_Cons append_Nil bsimp_AALTs.simps(3) good.simps(1) k0b)
               apply force+
  apply (metis (no_types, lifting) add_Suc add_Suc_right asize.simps(5) bsimp.simps(1) bsimp_ASEQ.simps(19) less_add_Suc1 less_add_Suc2)
  apply (metis add_Suc add_Suc_right arexp.distinct(5) arexp.distinct(7) asize.simps(4) asize.simps(5) bsimp.simps(1) bsimp.simps(2) bsimp_ASEQ1 good.simps(21) good.simps(8) less_add_Suc1 less_add_Suc2)
         apply force+
  apply (metis (no_types, lifting) add_Suc add_Suc_right arexp.distinct(5) arexp.distinct(7) asize.simps(4) asize.simps(5) bsimp.simps(1) bsimp.simps(2) bsimp_ASEQ1 good.simps(25) good.simps(8) less_add_Suc1 less_add_Suc2)
  apply (metis add_Suc add_Suc_right arexp.distinct(7) asize.simps(4) bsimp.simps(2) bsimp_ASEQ1 good.simps(26) good.simps(8) less_add_Suc1 less_add_Suc2)
    apply force+
  done

lemma test2:
  assumes "good r"
  shows "bsimp r = r"
  using assms
  apply(induct r taking: "asize" rule: measure_induct)
  apply(case_tac x)
       apply(simp_all)
   defer  
  (* AALT case *)
   apply(subgoal_tac "1 < length x52")
    prefer 2
    apply(case_tac x52)
     apply(simp)
    apply(simp)
    apply(case_tac list)
     apply(simp)
  apply(simp)
    apply(subst bsimp_AALTs_qq)
    prefer 2
    apply(subst flts_qq)
      apply(auto)[1]
     apply(auto)[1]
   apply(case_tac x52)
     apply(simp)
    apply(simp)
    apply(case_tac list)
     apply(simp)
      apply(simp)
      apply(auto)[1]
  apply (metis (no_types, lifting) bsimp_AALTs.elims good.simps(6) length_Cons length_pos_if_in_set list.size(3) nat_neq_iff)
  apply(simp)  
  apply(case_tac x52)
     apply(simp)
    apply(simp)
    apply(case_tac list)
     apply(simp)
   apply(simp)
   apply(subst k0)
   apply(simp)
   apply(subst (2) k0)
   apply(simp)
  apply (simp add: Suc_lessI flts1 one_is_add)
  (* SEQ case *)
  apply(case_tac "bsimp x42 = AZERO")
   apply simp
  apply (metis asize.elims good.simps(10) good.simps(11) good.simps(12) good.simps(2) good.simps(7) good.simps(9) good_SEQ less_add_Suc1)  
   apply(case_tac "\<exists>bs'. bsimp x42 = AONE bs'")
   apply(auto)[1]
  defer
  apply(case_tac "bsimp x43 = AZERO")
    apply(simp)
  apply (metis bsimp.elims bsimp.simps(3) good.simps(10) good.simps(11) good.simps(12) good.simps(8) good.simps(9) good_SEQ less_add_Suc2)
  apply(auto)  
   apply (subst bsimp_ASEQ1)
      apply(auto)[3]
   apply(auto)[1]
    apply (metis bsimp.simps(3) good.simps(2) good_SEQ less_add_Suc1)
   apply (metis bsimp.simps(3) good.simps(2) good_SEQ less_add_Suc1 less_add_Suc2)
  apply (subst bsimp_ASEQ2)
  apply(drule_tac x="x42" in spec)
  apply(drule mp)
   apply(simp)
  apply(drule mp)
   apply (metis bsimp.elims bsimp.simps(3) good.simps(10) good.simps(11) good.simps(2) good_SEQ)
  apply(simp)
  done


lemma bsimp_idem:
  shows "bsimp (bsimp r) = bsimp r"
  using test good1
  by force


lemma q3a:
  assumes "\<exists>r \<in> set rs. bnullable r"
  shows "bmkeps (AALTs bs (map (fuse bs1) rs)) = bmkeps (AALTs (bs@bs1) rs)"
  using assms
  apply(induct rs arbitrary: bs bs1)
   apply(simp)
  apply(simp)
  apply(auto)
   apply (metis append_assoc b2 bnullable_correctness erase_fuse bnullable_Hdbmkeps_Hd)
  apply(case_tac "bnullable a")
   apply (metis append.assoc b2 bnullable_correctness erase_fuse bnullable_Hdbmkeps_Hd)
  apply(case_tac rs)
  apply(simp)
  apply(simp)
  apply(auto)[1]
   apply (metis bnullable_correctness erase_fuse)+
  done

lemma qq4:
  assumes "\<exists>x\<in>set list. bnullable x"
  shows "\<exists>x\<in>set (flts list). bnullable x"
  using assms
  apply(induct list rule: flts.induct)
        apply(auto)
  by (metis UnCI bnullable_correctness erase_fuse imageI)
  

lemma qs3:
  assumes "\<exists>r \<in> set rs. bnullable r"
  shows "bmkeps (AALTs bs rs) = bmkeps (AALTs bs (flts rs))"
  using assms
  apply(induct rs arbitrary: bs taking: size rule: measure_induct)
  apply(case_tac x)
  apply(simp)
  apply(simp)
  apply(case_tac a)
       apply(simp)
       apply (simp add: r1)
      apply(simp)
      apply (simp add: bnullable_Hdbmkeps_Hd)
     apply(simp)
     apply(case_tac "flts list")
      apply(simp)
  apply (metis L_erase_AALTs L_erase_flts L_flat_Prf1 L_flat_Prf2 Prf_elims(1) bnullable_correctness erase.simps(4) mkeps_nullable r2)
     apply(simp)
     apply (simp add: r1)
    prefer 3
    apply(simp)
    apply (simp add: bnullable_Hdbmkeps_Hd)
   prefer 2
   apply(simp)
  apply(case_tac "\<exists>x\<in>set x52. bnullable x")
  apply(case_tac "list")
    apply(simp)
    apply (metis b2 fuse.simps(4) q3a r2)
   apply(erule disjE)
    apply(subst qq1)
     apply(auto)[1]
     apply (metis bnullable_correctness erase_fuse)
    apply(simp)
     apply (metis b2 fuse.simps(4) q3a r2)
    apply(simp)
    apply(auto)[1]
     apply(subst qq1)
      apply (metis bnullable_correctness erase_fuse image_eqI set_map)
     apply (metis b2 fuse.simps(4) q3a r2)
  apply(subst qq1)
      apply (metis bnullable_correctness erase_fuse image_eqI set_map)
    apply (metis b2 fuse.simps(4) q3a r2)
   apply(simp)
   apply(subst qq2)
     apply (metis bnullable_correctness erase_fuse imageE set_map)
  prefer 2
  apply(case_tac "list")
     apply(simp)
    apply(simp)
   apply (simp add: qq4)
  apply(simp)
  apply(auto)
   apply(case_tac list)
    apply(simp)
   apply(simp)
   apply (simp add: bnullable_Hdbmkeps_Hd)
  apply(case_tac "bnullable (ASEQ x41 x42 x43)")
   apply(case_tac list)
    apply(simp)
   apply(simp)
   apply (simp add: bnullable_Hdbmkeps_Hd)
  apply(simp)
  using qq4 r1 r2 by auto



lemma k1:
  assumes "\<And>x2aa. \<lbrakk>x2aa \<in> set x2a; bnullable x2aa\<rbrakk> \<Longrightarrow> bmkeps x2aa = bmkeps (bsimp x2aa)"
          "\<exists>x\<in>set x2a. bnullable x"
        shows "bmkeps (AALTs x1 (flts x2a)) = bmkeps (AALTs x1 (flts (map bsimp x2a)))"
  using assms
  apply(induct x2a)
  apply fastforce
  apply(simp)
  apply(subst k0)
  apply(subst (2) k0)
  apply(auto)[1]
  apply (metis b3 k0 list.set_intros(1) qs3 bnullable_Hdbmkeps_Hd)
  by (smt b3 imageI insert_iff k0 list.set(2) qq3 qs3 bnullable_Hdbmkeps_Hd r1 set_map)
  
  
  
lemma bmkeps_simp:
  assumes "bnullable r"
  shows "bmkeps r = bmkeps (bsimp r)"
  using  assms
  apply(induct r)
       apply(simp)
      apply(simp)
     apply(simp)
    apply(simp)
    prefer 3
  apply(simp)
   apply(case_tac "bsimp r1 = AZERO")
    apply(simp)
    apply(auto)[1]
  apply (metis L_bsimp_erase L_flat_Prf1 L_flat_Prf2 Prf_elims(1) bnullable_correctness erase.simps(1) mkeps_nullable)
 apply(case_tac "bsimp r2 = AZERO")
    apply(simp)  
    apply(auto)[1]
  apply (metis L_bsimp_erase L_flat_Prf1 L_flat_Prf2 Prf_elims(1) bnullable_correctness erase.simps(1) mkeps_nullable)
  apply(case_tac "\<exists>bs. bsimp r1 = AONE bs")
    apply(auto)[1]
    apply(subst b1)
    apply(subst b2)
  apply(simp add: b3[symmetric])
    apply(simp)
   apply(subgoal_tac "bsimp_ASEQ x1 (bsimp r1) (bsimp r2) = ASEQ x1 (bsimp r1) (bsimp r2)")
    prefer 2
  apply (smt b3 bnullable.elims(2) bsimp_ASEQ.simps(17) bsimp_ASEQ.simps(19) bsimp_ASEQ.simps(20) bsimp_ASEQ.simps(21) bsimp_ASEQ.simps(22) bsimp_ASEQ.simps(24) bsimp_ASEQ.simps(25) bsimp_ASEQ.simps(26) bsimp_ASEQ.simps(27) bsimp_ASEQ.simps(29) bsimp_ASEQ.simps(30) bsimp_ASEQ.simps(31))
   apply(simp)
  apply(simp)
  thm q3
  apply(subst q3[symmetric])
   apply simp
  using b3 qq4 apply auto[1]
  apply(subst qs3)
   apply simp
  using k1 by blast

thm bmkeps_retrieve bmkeps_simp bder_retrieve

lemma bmkeps_bder_AALTs:
  assumes "\<exists>r \<in> set rs. bnullable (bder c r)" 
  shows "bmkeps (bder c (bsimp_AALTs bs rs)) = bmkeps (bsimp_AALTs bs (map (bder c) rs))"
  using assms
  apply(induct rs)
   apply(simp)
  apply(simp)
  apply(auto)
  apply(case_tac rs)
    apply(simp)
  apply (metis (full_types) Prf_injval bder_retrieve bmkeps_retrieve bnullable_correctness erase_bder erase_fuse mkeps_nullable retrieve_fuse2)
   apply(simp)
  apply(case_tac  rs)
   apply(simp_all)
  done

lemma bbs0:
  shows "blexer_simp r [] = blexer r []"
  apply(simp add: blexer_def blexer_simp_def)
  done

lemma bbs1:
  shows "blexer_simp r [c] = blexer r [c]"
  apply(simp add: blexer_def blexer_simp_def)
  apply(auto)
    defer
  using b3 apply auto[1]
  using b3 apply auto[1]  
  apply(subst bmkeps_simp[symmetric])
   apply(simp)
  apply(simp)
  done

lemma oo:
  shows "(case (blexer (der c r) s) of None \<Rightarrow> None | Some v \<Rightarrow> Some (injval r c v)) = blexer r (c # s)"
  apply(simp add: blexer_correctness)
  done


lemma bder_fuse:
  shows "bder c (fuse bs a) = fuse bs  (bder c a)"
  apply(induct a arbitrary: bs c)
       apply(simp_all)
  done


fun flts2 :: "char \<Rightarrow> arexp list \<Rightarrow> arexp list"
  where 
  "flts2 _ [] = []"
| "flts2 c (AZERO # rs) = flts2 c rs"
| "flts2 c (AONE _ # rs) = flts2 c rs"
| "flts2 c (ACHAR bs d # rs) = (if c = d then (ACHAR bs d # flts2 c rs) else flts2 c rs)"
| "flts2 c ((AALTs bs rs1) # rs) = (map (fuse bs) rs1) @ flts2 c rs"
| "flts2 c (ASEQ bs r1 r2 # rs) = (if (bnullable(r1) \<and> r2 = AZERO) then 
    flts2 c rs
    else ASEQ bs r1 r2 # flts2 c rs)"
| "flts2 c (r1 # rs) = r1 # flts2 c rs"

lemma  flts2_k0:
  shows "flts2 c (r # rs1) = flts2 c [r] @ flts2 c rs1"
  apply(induct r arbitrary: c rs1)
   apply(auto)
  done

lemma  flts2_k00:
  shows "flts2 c (rs1 @ rs2) = flts2 c rs1 @ flts2 c rs2"
  apply(induct rs1 arbitrary: rs2 c)
   apply(auto)
  by (metis append.assoc flts2_k0)





lemma XXX2_helper:
  assumes "\<forall>y. asize y < Suc (sum_list (map asize rs)) \<longrightarrow> good y \<longrightarrow> bsimp y = y" 
          "\<forall>r'\<in>set rs. good r' \<and> nonalt r'"
  shows "flts (map (bsimp \<circ> bder c) (flts (map bsimp rs))) = flts (map (bsimp \<circ> bder c) rs)"
  using assms
  apply(induct rs arbitrary: c)
   apply(simp)
  apply(simp)
  apply(subst k0)
  apply(simp add: flts_append)
  apply(subst (2) k0)
  apply(simp add: flts_append)
  apply(subgoal_tac "flts [a] =  [a]")
   prefer 2
  using good.simps(1) k0b apply blast
  apply(simp)
  done

lemma bmkeps_good:
  assumes "good a"
  shows "bmkeps (bsimp a) = bmkeps a"
  using assms
  using test2 by auto


lemma xxx_bder:
  assumes "good r"
  shows "L (erase r) \<noteq> {}"
  using assms
  apply(induct r rule: good.induct)
  apply(auto simp add: Sequ_def)
  done

lemma xxx_bder2:
  assumes "L (erase (bsimp r)) = {}"
  shows "bsimp r = AZERO"
  using assms xxx_bder test2 good1
  by blast

lemma XXX2aa:
  assumes "good a"
  shows "bsimp (bder c (bsimp a)) = bsimp (bder c a)"
  using  assms
  by (simp add: test2)

lemma XXX2aa_ders:
  assumes "good a"
  shows "bsimp (bders (bsimp a) s) = bsimp (bders a s)"
  using  assms
  by (simp add: test2)

lemma XXX4a:
  shows "good (bders_simp (bsimp r) s)  \<or> bders_simp (bsimp r) s = AZERO"
  apply(induct s arbitrary: r rule:  rev_induct)
   apply(simp)
  apply (simp add: good1)
  apply(simp add: bders_simp_append)
  apply (simp add: good1)
  done

lemma XXX4a_good:
  assumes "good a"
  shows "good (bders_simp a s) \<or> bders_simp a s = AZERO"
  using assms
  apply(induct s arbitrary: a rule:  rev_induct)
   apply(simp)
  apply(simp add: bders_simp_append)
  apply (simp add: good1)
  done

lemma XXX4a_good_cons:
  assumes "s \<noteq> []"
  shows "good (bders_simp a s) \<or> bders_simp a s = AZERO"
  using assms
  apply(case_tac s)
   apply(auto)
  using XXX4a by blast

lemma XXX4b:
  assumes "good a" "L (erase (bders_simp a s)) \<noteq> {}"
  shows "good (bders_simp a s)"
  using assms
  apply(induct s arbitrary: a)
   apply(simp)
  apply(simp)
  apply(subgoal_tac "L (erase (bder a aa)) = {} \<or> L (erase (bder a aa)) \<noteq> {}")
   prefer 2
   apply(auto)[1]
  apply(erule disjE)
   apply(subgoal_tac "bsimp (bder a aa) = AZERO")
    prefer 2
  using L_bsimp_erase xxx_bder2 apply auto[1]
   apply(simp)
  apply (metis L.simps(1) XXX4a erase.simps(1))  
  apply(drule_tac x="bsimp (bder a aa)" in meta_spec)
  apply(drule meta_mp)
  apply simp
  apply(rule good1a)
  apply(auto)
  done

lemma bders_AZERO:
  shows "bders AZERO s = AZERO"
  and   "bders_simp AZERO s = AZERO"
   apply (induct s)
     apply(auto)
  done

lemma LA:
  assumes "\<Turnstile> v : ders s (erase r)"
  shows "retrieve (bders r s) v = retrieve r (flex (erase r) id s v)"
  using assms
  apply(induct s arbitrary: r v rule: rev_induct)
   apply(simp)
  apply(simp add: bders_append ders_append)
  apply(subst bder_retrieve)
   apply(simp)
  apply(drule Prf_injval)
  by (simp add: flex_append)


lemma LB:
  assumes "s \<in> (erase r) \<rightarrow> v" 
  shows "retrieve r v = retrieve r (flex (erase r) id s (mkeps (ders s (erase r))))"
  using assms
  apply(induct s arbitrary: r v rule: rev_induct)
   apply(simp)
   apply(subgoal_tac "v = mkeps (erase r)")
    prefer 2
  apply (simp add: Posix1(1) Posix_determ Posix_mkeps nullable_correctness)
   apply(simp)
  apply(simp add: flex_append ders_append)
  sorry
(*  by (metis Posix_determ Posix_flex Posix_injval Posix_mkeps ders_snoc lexer_correctness(2) lexer_flex)
*)

lemma LB_sym:
  assumes "s \<in> (erase r) \<rightarrow> v" 
  shows "retrieve r v = retrieve r (flex (erase r) id s (mkeps (erase (bders r s))))"
  using assms
  by (simp add: LB)


lemma LC:
  assumes "s \<in> (erase r) \<rightarrow> v" 
  shows "retrieve r v = retrieve (bders r s) (mkeps (erase (bders r s)))"
  apply(simp)
  by (metis LA LB Posix1(1) assms lexer_correct_None lexer_flex mkeps_nullable)


lemma L0:
  assumes "bnullable a"
  shows "retrieve (bsimp a) (mkeps (erase (bsimp a))) = retrieve a (mkeps (erase a))"
  using assms
  by (metis b3 bmkeps_retrieve bmkeps_simp bnullable_correctness)

thm bmkeps_retrieve

lemma L0a:
  assumes "s \<in> L(erase a)"
  shows "retrieve (bsimp (bders a s)) (mkeps (erase (bsimp (bders a s)))) = 
         retrieve (bders a s) (mkeps (erase (bders a s)))"
  using assms
  by (metis L0 bnullable_correctness erase_bders lexer_correct_None lexer_flex)
  
lemma L0aa:
  assumes "s \<in> L (erase a)"
  shows "[] \<in> erase (bsimp (bders a s)) \<rightarrow> mkeps (erase (bsimp (bders a s)))"
  using assms
  by (metis Posix_mkeps b3 bnullable_correctness erase_bders lexer_correct_None lexer_flex)

lemma L0aaa:
  assumes "[c] \<in> L (erase a)"
  shows "[c] \<in> (erase a) \<rightarrow> flex (erase a) id [c] (mkeps (erase (bder c a)))"
  using assms
  by (metis bders.simps(1) bders.simps(2) erase_bders lexer_correct_None lexer_correct_Some lexer_flex option.inject)

lemma L0aaaa:
  assumes "[c] \<in> L (erase a)"
  shows "[c] \<in> (erase a) \<rightarrow> flex (erase a) id [c] (mkeps (erase (bders a [c])))"
  using assms
  using L0aaa by auto
    

lemma L02:
  assumes "bnullable (bder c a)"
  shows "retrieve (bsimp a) (flex (erase (bsimp a)) id [c] (mkeps (erase (bder c (bsimp a))))) = 
         retrieve (bder c (bsimp a)) (mkeps (erase (bder c (bsimp a))))"
  using assms
  apply(simp)
  using bder_retrieve L0 bmkeps_simp bmkeps_retrieve L0  LA LB
  apply(subst bder_retrieve[symmetric])
  apply (metis L_bsimp_erase bnullable_correctness der_correctness erase_bder mkeps_nullable nullable_correctness)
  apply(simp)
  done

lemma L02_bders:
  assumes "bnullable (bders a s)"
  shows "retrieve (bsimp a) (flex (erase (bsimp a)) id s (mkeps (erase (bders (bsimp a) s)))) = 
         retrieve (bders (bsimp a) s) (mkeps (erase (bders (bsimp a) s)))"
  using assms
  by (metis LA L_bsimp_erase bnullable_correctness ders_correctness erase_bders mkeps_nullable nullable_correctness)


  

lemma L03:
  assumes "bnullable (bder c a)"
  shows "retrieve (bder c (bsimp a)) (mkeps (erase (bder c (bsimp a)))) =
         bmkeps (bsimp (bder c (bsimp a)))"
  using assms
  by (metis L0 L_bsimp_erase bmkeps_retrieve bnullable_correctness der_correctness erase_bder nullable_correctness)

lemma L04:
  assumes "bnullable (bder c a)"
  shows "retrieve (bder c (bsimp a)) (mkeps (erase (bder c (bsimp a)))) =
         retrieve (bsimp (bder c (bsimp a))) (mkeps (erase (bsimp (bder c (bsimp a)))))"     
  using assms
  by (metis L0 L_bsimp_erase bnullable_correctness der_correctness erase_bder nullable_correctness)
    
lemma L05:
  assumes "bnullable (bder c a)"
  shows "retrieve (bder c (bsimp a)) (mkeps (erase (bder c (bsimp a)))) =
         retrieve (bsimp (bder c (bsimp a))) (mkeps (erase (bsimp (bder c (bsimp a)))))" 
  using assms
  using L04 by auto 

lemma L06:
  assumes "bnullable (bder c a)"
  shows "bmkeps (bder c (bsimp a)) = bmkeps (bsimp (bder c (bsimp a)))"
  using assms
  by (metis L03 L_bsimp_erase bmkeps_retrieve bnullable_correctness der_correctness erase_bder nullable_correctness) 

lemma L07:
  assumes "s \<in> L (erase r)"
  shows "retrieve r (flex (erase r) id s (mkeps (ders s (erase r)))) 
            = retrieve (bders r s) (mkeps (erase (bders r s)))"
  using assms
  using LB LC lexer_correct_Some by auto

lemma LXXX:
  assumes "s \<in> (erase r) \<rightarrow> v" "s \<in> (erase (bsimp r)) \<rightarrow> v'"
  shows "retrieve r v = retrieve (bsimp r) v'"
  using  assms
  apply -
  thm LC
  apply(subst LC)
   apply(assumption)
  apply(subst  L0[symmetric])
  using bnullable_correctness lexer_correctness(2) lexer_flex apply fastforce
  apply(subst (2) LC)
   apply(assumption)
  apply(subst (2)  L0[symmetric])
  using bnullable_correctness lexer_correctness(2) lexer_flex apply fastforce
   
  oops  


lemma L08:
  assumes "s \<in> L (erase r)"
  shows "retrieve (bders (bsimp r) s) (mkeps (erase (bders (bsimp r) s)))
         = retrieve (bders r s) (mkeps (erase (bders r s)))"
  using assms
  apply(induct s arbitrary: r)
   apply(simp)
  using L0 bnullable_correctness nullable_correctness apply blast
  apply(simp add: bders_append)
  apply(drule_tac x="(bder a (bsimp r))" in meta_spec)
  apply(drule meta_mp)
  apply (metis L_bsimp_erase erase_bder lexer.simps(2) lexer_correct_None option.case(1))
  apply(drule sym)
  apply(simp)
  apply(subst LA)
  apply (metis L0aa L_bsimp_erase Posix1(1) ders.simps(2) ders_correctness erase_bder erase_bders mkeps_nullable nullable_correctness)
  apply(subst LA)
  using lexer_correct_None lexer_flex mkeps_nullable apply force
  
  using L0[no_vars] bder_retrieve[no_vars] LA[no_vars] LC[no_vars] L07[no_vars]

thm L0[no_vars] bder_retrieve[no_vars] LA[no_vars] LC[no_vars] L07[no_vars]
  oops

lemma test:
  assumes "s = [c]"
  shows "retrieve (bders r s) v = XXX" and "YYY = retrieve r (flex (erase r) id s v)"
  using assms
   apply(simp only: bders.simps)
   defer
  using assms
   apply(simp only: flex.simps id_simps)
  using  L0[no_vars] bder_retrieve[no_vars] LA[no_vars] LC[no_vars] 
  find_theorems "retrieve (bders _ _) _"
  find_theorems "retrieve _ (mkeps _)"
  oops

lemma L06X:
  assumes "bnullable (bder c a)"
  shows "bmkeps (bder c (bsimp a)) = bmkeps (bder c a)"
  using assms
  apply(induct a arbitrary: c)
       apply(simp)
      apply(simp)
     apply(simp)
    prefer 3
    apply(simp)
   prefer 2
   apply(simp)
  
   defer
  oops

lemma L06_2:
  assumes "bnullable (bders a [c,d])"
  shows "bmkeps (bders (bsimp a) [c,d]) = bmkeps (bsimp (bders (bsimp a) [c,d]))"
  using assms
  apply(simp)
  by (metis L_bsimp_erase bmkeps_simp bnullable_correctness der_correctness erase_bder nullable_correctness)
  
lemma L06_bders:
  assumes "bnullable (bders a s)"
  shows "bmkeps (bders (bsimp a) s) = bmkeps (bsimp (bders (bsimp a) s))"
  using assms
  by (metis L_bsimp_erase bmkeps_simp bnullable_correctness ders_correctness erase_bders nullable_correctness)

lemma LLLL:
  shows "L (erase a) =  L (erase (bsimp a))"
  and "L (erase a) = {flat v | v. \<Turnstile> v: (erase a)}"
  and "L (erase a) = {flat v | v. \<Turnstile> v: (erase (bsimp a))}"
  using L_bsimp_erase apply(blast)
  apply (simp add: L_flat_Prf)
  using L_bsimp_erase L_flat_Prf apply(auto)[1]
  done  
    


lemma L07XX:
  assumes "s \<in> L (erase a)"
  shows "s \<in> erase a \<rightarrow> flex (erase a) id s (mkeps (ders s (erase a)))"
  using assms
  by (meson lexer_correct_None lexer_correctness(1) lexer_flex)

lemma LX0:
  assumes "s \<in> L r"
  shows "decode (bmkeps (bders (intern r) s)) r = Some(flex r id s (mkeps (ders s r)))"
  by (metis assms blexer_correctness blexer_def lexer_correct_None lexer_flex)


lemma L02_bders2:
  assumes "bnullable (bders a s)" "s = [c]"
  shows "retrieve (bders (bsimp a) s) (mkeps (erase (bders (bsimp a) s)))  =
         retrieve (bders a s) (mkeps (erase (bders a s)))"
  using assms
  apply(simp)
  
  apply(induct s arbitrary: a)
   apply(simp)
  using L0 apply auto[1]
  oops

thm bmkeps_retrieve bmkeps_simp Posix_mkeps

lemma WQ1:
  assumes "s \<in> L (der c r)"
  shows "s \<in> der c r \<rightarrow> mkeps (ders s (der c r))"
  using assms
  oops

lemma L1:
  assumes "s \<in> r \<rightarrow> v" 
  shows "decode (bmkeps (bders (intern r) s)) r = Some v"
  using assms
  by (metis blexer_correctness blexer_def lexer_correctness(1) option.distinct(1))

lemma L2:
  assumes "s \<in> (der c r) \<rightarrow> v" 
  shows "decode (bmkeps (bders (intern r) (c # s))) r = Some (injval r c v)"
  using assms
  apply(subst bmkeps_retrieve)
  using Posix1(1) lexer_correct_None lexer_flex apply fastforce
  using MAIN_decode
  apply(subst MAIN_decode[symmetric])
   apply(simp)
   apply (meson Posix1(1) lexer_correct_None lexer_flex mkeps_nullable)
  apply(simp)
  apply(subgoal_tac "v = flex (der c r) id s (mkeps (ders s (der c r)))")
   prefer 2
   apply (metis Posix_determ lexer_correctness(1) lexer_flex option.distinct(1))
  apply(simp)
  apply(subgoal_tac "injval r c (flex (der c r) id s (mkeps (ders s (der c r)))) =
    (flex (der c r) ((\<lambda>v. injval r c v) o id) s (mkeps (ders s (der c r))))")
   apply(simp)
  using flex_fun_apply by blast
  
lemma L3:
  assumes "s2 \<in> (ders s1 r) \<rightarrow> v" 
  shows "decode (bmkeps (bders (intern r) (s1 @ s2))) r = Some (flex r id s1 v)"
  using assms
  apply(induct s1 arbitrary: r s2 v rule: rev_induct)
   apply(simp)
  using L1 apply blast
  apply(simp add: ders_append)
  apply(drule_tac x="r" in meta_spec)
  apply(drule_tac x="x # s2" in meta_spec)
  apply(drule_tac x="injval (ders xs r) x v" in meta_spec)
  apply(drule meta_mp)
   defer
   apply(simp)
   apply(simp add:  flex_append)
  by (simp add: Posix_injval)



lemma bders_snoc:
  "bder c (bders a s) = bders a (s @ [c])"
  apply(simp add: bders_append)
  done


lemma QQ1:
  shows "bsimp (bders (bsimp a) []) = bders_simp (bsimp a) []"
  apply(simp)
  apply(simp add: bsimp_idem)
  done

lemma QQ2:
  shows "bsimp (bders (bsimp a) [c]) = bders_simp (bsimp a) [c]"
  apply(simp)
  done

lemma XXX2a_long:
  assumes "good a"
  shows "bsimp (bder c (bsimp a)) = bsimp (bder c a)"
  using  assms
  apply(induct a arbitrary: c taking: asize rule: measure_induct)
  apply(case_tac x)
       apply(simp)
      apply(simp)
     apply(simp)
  prefer 3
    apply(simp)
   apply(simp)
   apply(auto)[1]
apply(case_tac "x42 = AZERO")
     apply(simp)
   apply(case_tac "x43 = AZERO")
     apply(simp)
  using test2 apply force  
  apply(case_tac "\<exists>bs. x42 = AONE bs")
     apply(clarify)
     apply(simp)
    apply(subst bsimp_ASEQ1)
       apply(simp)
  using b3 apply force
  using bsimp_ASEQ0 test2 apply force
  thm good_SEQ test2
     apply (simp add: good_SEQ test2)
    apply (simp add: good_SEQ test2)
  apply(case_tac "x42 = AZERO")
     apply(simp)
   apply(case_tac "x43 = AZERO")
    apply(simp)
  apply (simp add: bsimp_ASEQ0)
  apply(case_tac "\<exists>bs. x42 = AONE bs")
     apply(clarify)
     apply(simp)
    apply(subst bsimp_ASEQ1)
      apply(simp)
  using bsimp_ASEQ0 test2 apply force
     apply (simp add: good_SEQ test2)
    apply (simp add: good_SEQ test2)
  apply (simp add: good_SEQ test2)
  (* AALTs case *)
  apply(simp)
  using test2 by fastforce

lemma XXX2a_long_without_good:
  assumes "a = AALTs bs0  [AALTs bs1 [AALTs bs2 [ASTAR [] (AONE bs7), AONE bs6, ASEQ bs3 (ACHAR bs4 d) (AONE bs5)]]]" 
  shows "bsimp (bder c (bsimp a)) = bsimp (bder c a)"
        "bsimp (bder c (bsimp a)) = XXX"
        "bsimp (bder c a) = YYY"
  using  assms
    apply(simp)
  using  assms
   apply(simp)
   prefer 2
  using  assms
   apply(simp)
  oops

lemma bder_bsimp_AALTs:
  shows "bder c (bsimp_AALTs bs rs) = bsimp_AALTs bs (map (bder c) rs)"
  apply(induct bs rs rule: bsimp_AALTs.induct)  
    apply(simp)
   apply(simp)
   apply (simp add: bder_fuse)
  apply(simp)
  done

lemma flts_nothing:
  assumes "\<forall>r \<in> set rs. r \<noteq> AZERO" "\<forall>r \<in> set rs. nonalt r"
  shows "flts rs = rs"
  using assms
  apply(induct rs rule: flts.induct)
        apply(auto)
  done

lemma flts_flts:
  assumes "\<forall>r \<in> set rs. good r"
  shows "flts (flts rs) = flts rs"
  using assms
  apply(induct rs taking: "\<lambda>rs. sum_list  (map asize rs)" rule: measure_induct)
  apply(case_tac x)
   apply(simp)
  apply(simp)
  apply(case_tac a)
       apply(simp_all  add: bder_fuse flts_append)
  apply(subgoal_tac "\<forall>r \<in> set x52. r \<noteq> AZERO")
   prefer 2
  apply (metis Nil_is_append_conv bsimp_AALTs.elims good.simps(1) good.simps(5) good0 list.distinct(1) n0 nn1b split_list_last test2)
  apply(subgoal_tac "\<forall>r \<in> set x52. nonalt r")
   prefer 2
   apply (metis n0 nn1b test2)
  by (metis flts_fuse flts_nothing)


lemma PP:
  assumes "bnullable (bders r s)" 
  shows "bmkeps (bders (bsimp r) s) = bmkeps (bders r s)"
  using assms
  apply(induct s arbitrary: r)
   apply(simp)
  using bmkeps_simp apply auto[1]
  apply(simp add: bders_append bders_simp_append)
  oops

lemma PP:
  assumes "bnullable (bders r s)"
  shows "bmkeps (bders_simp (bsimp r) s) = bmkeps (bders r s)"
  using assms
  apply(induct s arbitrary: r rule: rev_induct)
   apply(simp)
  using bmkeps_simp apply auto[1]
  apply(simp add: bders_append bders_simp_append)
  apply(drule_tac x="bder a (bsimp r)" in meta_spec)
  apply(drule_tac meta_mp)
   defer
  oops


lemma
  assumes "asize (bsimp a) = asize a"  "a = AALTs bs [AALTs bs2 [], AZERO, AONE bs3]"
  shows "bsimp a = a"
  using assms
  apply(simp)
  oops


lemma iii:
  assumes "bsimp_AALTs bs rs \<noteq> AZERO"
  shows "rs \<noteq> []"
  using assms
  apply(induct bs  rs rule: bsimp_AALTs.induct)
    apply(auto)
  done

lemma CT1_SEQ:
  shows "bsimp (ASEQ bs a1 a2) = bsimp (ASEQ bs (bsimp a1) (bsimp a2))"
  apply(simp add: bsimp_idem)
  done

lemma CT1:
  shows "bsimp (AALTs bs as) = bsimp (AALTs bs (map  bsimp as))"
  apply(induct as arbitrary: bs)
   apply(simp)
  apply(simp)
  by (simp add: bsimp_idem comp_def)
  
lemma CT1a:
  shows "bsimp (AALT bs a1 a2) = bsimp(AALT bs (bsimp a1) (bsimp a2))"
  by (metis CT1 list.simps(8) list.simps(9))

lemma WWW2:
  shows "bsimp (bsimp_AALTs bs1 (flts (map bsimp as1))) =
         bsimp_AALTs bs1 (flts (map bsimp as1))"
  by (metis bsimp.simps(2) bsimp_idem)

lemma CT1b:
  shows "bsimp (bsimp_AALTs bs as) = bsimp (bsimp_AALTs bs (map bsimp as))"
  apply(induct bs as rule: bsimp_AALTs.induct)
    apply(auto simp add: bsimp_idem)
  apply (simp add: bsimp_fuse bsimp_idem)
  by (metis bsimp_idem comp_apply)
  
lemma conj_rule: "\<lbrakk> P; Q\<rbrakk> \<Longrightarrow> P \<and> (Q \<and> P)"
  apply(rule conjI)
   apply assumption
  apply (rule conjI)
   apply assumption
  apply assumption
  done

  thm disjE

lemma disj_swap : "P \<or> Q \<Longrightarrow> Q \<or> P"
  apply(erule disjE)
  oops

lemma "\<lbrakk>\<not>(P \<longrightarrow> Q); \<not>(R \<longrightarrow> Q) \<rbrakk> \<Longrightarrow> R"
  apply (erule_tac Q = "R \<longrightarrow> Q" in contrapos_np)
  apply (intro impI)
  by (erule  notE)

lemma "(P \<or> Q) \<and> R \<Longrightarrow> P \<or> (Q \<and> R)"
  apply(rule disjCI)
  oops


thm contrapos_np


definition bcong
  where
"bcong r1 r2 \<equiv> (\<forall> v. 
                    (
                      (erase (bsimp r1) = erase (bsimp r2)) \<and>  (retrieve (bsimp r1) v = retrieve (bsimp r2) v)
                    )  
                   )"

(*\<Turnstile> v : (erase (bsimp r1)) \<longleftrightarrow> (\<Turnstile> v : erase (bsimp r2))*)

lemma rsrcong: shows "bcong r (bsimp r)"
  by (simp add: BitCodedlots.bcong_def bsimp_idem)


thm simi.induct simi.intros simi.cases

inductive_set even :: "nat set" where
zero[intro!] : "0 \<in> even" |
step[intro!]: "n \<in> even \<Longrightarrow> (Suc (Suc n)) \<in> even"

lemma two_times_even[intro!]: "2*k \<in> even"
  apply(induct_tac k)
   apply(auto)
  done

lemma dvd_imp_even: "2 dvd n \<Longrightarrow> n \<in> even"
  by (auto simp add: dvd_def)


lemma even_imp_dvd: "n \<in> even \<Longrightarrow> 2 dvd n"
  apply (erule even.induct)
   apply(simp_all add: dvd_def)
  apply clarify
  apply (rule_tac x = "Suc k" in exI, simp)
  done

theorem even_iff_dvd: "(n \<in> even) = (2 dvd n)"
  by (blast intro: dvd_imp_even even_imp_dvd)

thm even.induct 

lemma even_imp_even_minus_2: "n \<in> even \<Longrightarrow> n - 2 \<in> even"
  apply (erule even.induct)
   apply auto
  done


lemma Suc_Suc_even_imp_even:"Suc (Suc n) \<in> even \<Longrightarrow> n \<in> even"
  apply( ind_cases "Suc (Suc n) \<in> even")
  apply simp
  done

lemma [iff]: "((Suc (Suc n)) \<in> even) = (n \<in> even)"

  by(blast dest: Suc_Suc_even_imp_even)

thm even.cases

inductive_cases Suc_Suc_cases [elim!]: "Suc (Suc n) \<in> even"

thm Suc_Suc_cases

inductive_set
Even ::"nat set" and
Odd :: "nat set"
where 
zero: "0 \<in> Even"
| EvenI: "n \<in> Odd \<Longrightarrow> Suc n \<in> Even"
| OddI : "n \<in> Even \<Longrightarrow> Suc n \<in> Odd"

thm Even_Odd.induct

lemma "(m \<in> Even \<longrightarrow> 2 dvd m) \<and> (n \<in> Odd \<longrightarrow> 2 dvd (Suc n))"
  apply (rule Even_Odd.induct)
    apply simp
   apply simp
  apply(simp_all add: dvd_def)
  apply clarify
  apply (rule_tac x = "Suc k" in exI, simp)
  done

inductive evn :: "nat \<Rightarrow> bool" where
zero: "evn 0" |
step: "evn n \<Longrightarrow> evn (Suc (Suc n))"

inductive_set
rtc :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set" ("_*" [1000] 999)
for r :: "('a \<times> 'a) set" where
rtc_refl[iff]: "(x,x) \<in> r*"
| rtc_step: "\<lbrakk> (x,y) \<in> r; (y,z) \<in> r* \<rbrakk> \<Longrightarrow> (x,z) \<in> r*"

lemma [intro]: "(x,y) \<in> r \<Longrightarrow> (x,y) \<in> r*" by(blast intro: rtc_step)

lemma rtc_trans: "\<lbrakk> (x, y) \<in> r*; (y, z) \<in> r*\<rbrakk> \<Longrightarrow> (x, z) \<in> r*"
  apply (erule rtc.induct)
  oops

lemma rtc_trans[rule_format]: "(x, y) \<in> r* \<Longrightarrow> (y, z) \<in> r* \<longrightarrow> (x, z) \<in> r*"
  apply(erule rtc.induct)
   apply simp
  by (meson rtc.rtc_step)

inductive_set
rtc2:: "('a \<times> 'a)set \<Rightarrow> ('a \<times> 'a)set"
for r :: "('a \<times> 'a)set"
where
"(x,y) \<in> r \<Longrightarrow> (x, y) \<in> rtc2 r"
| "(x,x) \<in> rtc2 r"
| "\<lbrakk> (x,y) \<in> rtc2 r; (y,z) \<in> rtc2 r\<rbrakk> \<Longrightarrow> (x,z) \<in> rtc2 r"
thm rtc2.induct

lemma "(x,y) \<in> rtc2 r \<Longrightarrow> (x,y) \<in> r*"
  apply(erule rtc2.induct)
  apply blast+
  apply(blast intro: rtc_trans)
  done

lemma "(x,y) \<in> r* \<Longrightarrow> (x,y) \<in> rtc2 r"
  apply(erule rtc.induct)
   apply(simp add: rtc2.intros)
  apply(blast intro: rtc2.intros)
  done

lemma rtc_step_converse: "(x, y) \<in> r* \<Longrightarrow> (y, z) \<in> r \<longrightarrow> (x, z) \<in> r*"
  apply(erule rtc.induct)
   apply blast
  apply(rule impI)
  apply(drule mp)
   apply simp
  apply (simp add: rtc.intros(2))
  done

datatype 'f gterm = Apply 'f "'f gterm list"

datatype integer_op = Number int | UnaryMinus | Plus

inductive_set
gterms :: "'f set \<Rightarrow> 'f gterm set"
for F :: "'f set"
where
step[intro!]: "\<lbrakk>\<forall>t \<in> set args. t \<in> gterms F; f \<in> F \<rbrakk>
              \<Longrightarrow> (Apply f args) \<in> gterms F"

lemma gterms_mono: "F \<subseteq> G \<Longrightarrow> gterms F \<subseteq> gterms G"
  apply clarify

  apply (erule gterms.induct)

  apply blast
  done


lemma "xs \<noteq> [] \<longrightarrow> hd(rev xs) = last xs"
  apply(induct_tac xs)
  apply(auto)
  done












fun
 zeroable :: "rexp \<Rightarrow> bool"
where
  "zeroable (ZERO) = True"
| "zeroable (ONE) = False"
| "zeroable (CR c) = False"
| "zeroable (ALT r1 r2) = (zeroable r1 \<or> zeroable r2)"
| "zeroable (SEQ r1 r2) = (zeroable r1 \<or> zeroable r2)"
| "zeroable (STAR r) = zeroable r"

fun nzero :: "rexp \<Rightarrow> bool"
  where
  "nzero ZERO = False"
| "nzero ONE = True"
| "nzero (CR c) = True"
| "nzero (ALT r1 r2) = (nzero r1 \<and> nzero r2)"
| "nzero (SEQ r1 r2) = (nzero r1 \<and> nzero r2)"
| "nzero (STAR r1) = nzero r1"

inductive rrewrite:: "arexp \<Rightarrow> arexp \<Rightarrow> bool" ("_ \<leadsto> _" [99, 99] 99)
  where
  "ASEQ bs AZERO r2 \<leadsto> AZERO"
| "ASEQ bs r1 AZERO \<leadsto> AZERO"
| "ASEQ bs (AONE bs1) r \<leadsto> fuse (bs@bs1) r"
| "r1 \<leadsto> r2 \<Longrightarrow> ASEQ bs r1 r3 \<leadsto> ASEQ bs r2 r3"
| "r3 \<leadsto> r4 \<Longrightarrow> ASEQ bs r1 r3 \<leadsto> ASEQ bs r1 r4"
| "r \<leadsto> r' \<Longrightarrow> (AALTs bs (rs1 @ [r] @ rs2)) \<leadsto> (AALTs bs (rs1 @ [r'] @ rs2))"
(*context rule for eliminating 0, alts--corresponds to the recursive call flts r::rs = r::(flts rs)*)
| "AALTs bs (rsa@AZERO # rsb) \<leadsto> AALTs bs (rsa@rsb)"
| "AALTs bs (rsa@(AALTs bs1 rs1)# rsb) \<leadsto> AALTs bs (rsa@(map (fuse bs1) rs1)@rsb)"
(*the below rule for extracting common prefixes between a list of rexp's bitcodes*)
| "AALTs bs (map (fuse bs1) rs) \<leadsto> AALTs (bs@bs1) rs"
(*opposite direction also allowed, which means bits  are free to be moved around
as long as they are on the right path*)
| "AALTs (bs@bs1) rs \<leadsto> AALTs bs (map (fuse bs1) rs)"
| "AALTs bs [] \<leadsto> AZERO"
| "AALTs bs [r] \<leadsto> fuse bs r"



(*this rule is not powerful enough | "\<lbrakk>r \<leadsto> r'; AALTs bs rs \<leadsto> AALTs bs rs'\<rbrakk> \<Longrightarrow> AALTs bs (r#rs) \<leadsto> AALTs bs (r'#rs')"*)
(*
| "\<lbrakk>r1 \<leadsto> r2; r3 \<leadsto> r4\<rbrakk> \<Longrightarrow> ASEQ bs r1 r3 \<leadsto> ASEQ bs r2 r4"
(r + 1.0 + r2) \<rightarrow> r + 0 + r2
*)

inductive rrewrites:: "arexp \<Rightarrow> arexp \<Rightarrow> bool" ("_ \<leadsto>* _" [100, 100] 100)
  where 
rs1[intro, simp]:"r \<leadsto>* r"
| rs2[intro]: "\<lbrakk>r1 \<leadsto>* r2; r2 \<leadsto> r3\<rbrakk> \<Longrightarrow> r1 \<leadsto>* r3"

inductive srewrites:: "arexp list \<Rightarrow> arexp list \<Rightarrow> bool" (" _ s\<leadsto>* _" [100, 100] 100)
  where
ss1: "[] s\<leadsto>* []"
|ss2: "\<lbrakk>r \<leadsto>* r'; rs s\<leadsto>* rs'\<rbrakk> \<Longrightarrow> (r#rs) s\<leadsto>* (r'#rs')"
(*rs1 = [r1, r2, ..., rn] rs2 = [r1', r2', ..., rn']
[r1, r2, ..., rn] \<leadsto>* [r1', r2, ..., rn] \<leadsto>* [...r2',...] \<leadsto>* [r1', r2',... rn']
*)



lemma r_in_rstar : "r1 \<leadsto> r2 \<Longrightarrow> r1 \<leadsto>* r2"
  using rrewrites.intros(1) rrewrites.intros(2) by blast
 
lemma real_trans: 
  assumes a1: "r1 \<leadsto>* r2"  and a2: "r2 \<leadsto>* r3"
  shows "r1 \<leadsto>* r3"
  using a2 a1
  apply(induct r2 r3 arbitrary: r1 rule: rrewrites.induct) 
   apply(auto)
  done


lemma  many_steps_later: "\<lbrakk>r1 \<leadsto> r2; r2 \<leadsto>* r3 \<rbrakk> \<Longrightarrow> r1 \<leadsto>* r3"
  by (meson r_in_rstar real_trans)



lemma star_alt: "r1 \<leadsto>* r2 \<Longrightarrow> AALTs bs [r1] \<leadsto>* AALTs bs [r2]"
  apply(induct r1 r2 arbitrary: bs rule: rrewrites.induct)
   apply(rule rs1)
  apply(erule rrewrites.cases)
   apply simp
   apply (metis append_Cons append_Nil r_in_rstar rrewrite.intros(6))
  by (metis (no_types, hide_lams) append_Cons append_Nil rrewrite.intros(6) rs2)



lemma contextrewrites1: "r \<leadsto>* r' \<Longrightarrow> (AALTs bs (r#rs)) \<leadsto>* (AALTs bs (r'#rs))"
  apply(induct r r' rule: rrewrites.induct)
   apply simp
  by (metis append_Cons append_Nil rrewrite.intros(6) rs2)


lemma contextrewrites2: "r \<leadsto>* r' \<Longrightarrow> (AALTs bs (rs1@[r]@rs)) \<leadsto>* (AALTs bs (rs1@[r']@rs))"
  apply(induct r r' rule: rrewrites.induct)
   apply simp
  using rrewrite.intros(6) by blast

lemma contextrewrites1_rev: "r \<leadsto>* r' \<Longrightarrow> (AALTs bs (rs@[r])) \<leadsto>* (AALTs bs (rs@[r']))"
  using contextrewrites2 by auto


lemma srewrites_alt: "rs1 s\<leadsto>* rs2 \<Longrightarrow> (AALTs bs (rs@rs1)) \<leadsto>* (AALTs bs (rs@rs2))"

  apply(induct rs1 rs2 arbitrary: bs rs rule: srewrites.induct)
   apply(rule rs1)
  apply(drule_tac x = "bs" in meta_spec)
  apply(drule_tac x = "rsa@[r']" in meta_spec)
  apply simp
  apply(rule real_trans)
   prefer 2
   apply(assumption)
  apply(drule contextrewrites2)
  apply auto
  done


corollary srewrites_alt1: "rs1 s\<leadsto>* rs2 \<Longrightarrow> AALTs bs rs1 \<leadsto>* AALTs bs rs2"
  by (metis append.left_neutral srewrites_alt)


lemma contextchunk: "AALTs bs rs2 \<leadsto>* AALTs bs rs2' \<Longrightarrow> AALTs bs (rs1@rs2) \<leadsto>* AALTs bs (rs1@rs2')"

  apply(induct "AALTs bs rs2" "AALTs bs rs2'"  arbitrary: bs rs1 rule: rrewrites.induct)
   apply(simp)

  oops


lemma star_seq:  "r1 \<leadsto>* r2 \<Longrightarrow> ASEQ bs r1 r3 \<leadsto>* ASEQ bs r2 r3"
  apply(induct r1 r2 arbitrary: r3 rule: rrewrites.induct)
   apply(rule rs1)
  apply(erule rrewrites.cases)
   apply(simp)
   apply(rule r_in_rstar)
   apply(rule rrewrite.intros(4))
   apply simp
  apply(rule rs2)
   apply(assumption)
  apply(rule rrewrite.intros(4))
  by assumption

lemma star_seq2:  "r3 \<leadsto>* r4 \<Longrightarrow> ASEQ bs r1 r3 \<leadsto>* ASEQ bs r1 r4"
  apply(induct r3 r4 arbitrary: r1 rule: rrewrites.induct)
   apply auto
  using rrewrite.intros(5) by blast


lemma continuous_rewrite: "\<lbrakk>r1 \<leadsto>* AZERO\<rbrakk> \<Longrightarrow> ASEQ bs1 r1 r2 \<leadsto>* AZERO"
  apply(induction ra\<equiv>"r1" rb\<equiv>"AZERO" arbitrary: bs1 r1 r2 rule: rrewrites.induct)
   apply (simp add: r_in_rstar rrewrite.intros(1))

  by (meson rrewrite.intros(1) rrewrites.intros(2) star_seq)
  


lemma bsimp_aalts_simpcases: "AONE bs \<leadsto>* (bsimp (AONE bs))"  "AZERO \<leadsto>* bsimp AZERO" "ACHAR bs c \<leadsto>* (bsimp (ACHAR bs c))"
  apply (simp add: rrewrites.intros(1))
  apply (simp add: rrewrites.intros(1))
  by (simp add: rrewrites.intros(1))

lemma trivialbsimpsrewrites: "\<lbrakk>\<And>x. x \<in> set rs \<Longrightarrow> x \<leadsto>* f x \<rbrakk> \<Longrightarrow> rs s\<leadsto>* (map f rs)"

  apply(induction rs)
   apply simp
   apply(rule ss1)
  by (metis insert_iff list.simps(15) list.simps(9) srewrites.simps)


lemma bsimp_AALTsrewrites: "AALTs bs1 rs \<leadsto>* bsimp_AALTs bs1 rs"
  apply(induction rs)
  apply simp
   apply(rule r_in_rstar)
   apply(simp add:  rrewrite.intros(11))
  apply(case_tac "rs = Nil")
   apply(simp)
  using rrewrite.intros(12) apply auto[1]
  apply(subgoal_tac "length (a#rs) > 1")
   apply(simp add: bsimp_AALTs_qq)
  apply(simp)
  done

inductive frewrites:: "arexp list \<Rightarrow> arexp list \<Rightarrow> bool" (" _ f\<leadsto>* _" [100, 100] 100)
  where
fs1: "[] f\<leadsto>* []"
|fs2: "\<lbrakk>rs f\<leadsto>* rs'\<rbrakk> \<Longrightarrow> (AZERO#rs) f\<leadsto>* rs'"
|fs3: "\<lbrakk>rs f\<leadsto>* rs'\<rbrakk> \<Longrightarrow> ((AALTs bs rs1) # rs) f\<leadsto>* ((map (fuse bs) rs1) @ rs')"
|fs4: "\<lbrakk>rs f\<leadsto>* rs';nonalt r; nonazero r\<rbrakk> \<Longrightarrow> (r#rs) f\<leadsto>* (r#rs')"





lemma flts_prepend: "\<lbrakk>nonalt a; nonazero a\<rbrakk> \<Longrightarrow> flts (a#rs) = a # (flts rs)"
  by (metis append_Cons append_Nil flts_single1 k00)

lemma fltsfrewrites: "rs f\<leadsto>* (flts rs)"
  apply(induction rs)
  apply simp
   apply(rule fs1)

  apply(case_tac "a = AZERO")

   
  using fs2 apply auto[1]
  apply(case_tac "\<exists>bs rs. a = AALTs bs rs")
   apply(erule exE)+
   
   apply (simp add: fs3)
  apply(subst flts_prepend)
    apply(rule nonalt.elims(2))
  prefer 2
  thm nonalt.elims
   
         apply blast
   
  using bbbbs1 apply blast
       apply(simp add: nonalt.simps)+
   
   apply (meson nonazero.elims(3))
   
  by (meson fs4 nonalt.elims(3) nonazero.elims(3))
thm rrewrite.intros
lemma rrewrite0away: "AALTs bs ( AZERO # rsb) \<leadsto> AALTs bs rsb"
  by (metis append_Nil rrewrite.intros(7))


lemma frewritesaalts:"rs f\<leadsto>* rs' \<Longrightarrow> (AALTs bs (rs1@rs)) \<leadsto>* (AALTs bs (rs1@rs'))"
  apply(induct rs rs' arbitrary: bs rs1 rule:frewrites.induct)
    apply(rule rs1)
    apply(drule_tac x = "bs" in meta_spec)
  apply(drule_tac x = "rs1 @ [AZERO]" in meta_spec)
    apply(rule real_trans)
     apply simp
  using r_in_rstar rrewrite.intros(7) apply presburger
    apply(drule_tac x = "bsa" in meta_spec)
  apply(drule_tac x = "rs1a @ [AALTs bs rs1]" in meta_spec)
   apply(rule real_trans)
    apply simp
  using r_in_rstar rrewrite.intros(8) apply presburger
    apply(drule_tac x = "bs" in meta_spec)
  apply(drule_tac x = "rs1@[r]" in meta_spec)
    apply(rule real_trans)
   apply simp
  apply auto
  done

lemma fltsrewrites: "  AALTs bs1 rs \<leadsto>* AALTs bs1 (flts rs)"
  apply(induction rs)
   apply simp
  apply(case_tac "a = AZERO")
  apply (metis append_Nil flts.simps(2) many_steps_later rrewrite.intros(7))



  apply(case_tac "\<exists>bs2 rs2. a = AALTs bs2 rs2")
   apply(erule exE)+
   apply(simp add: flts.simps)

   
   prefer 2

  apply(subst flts_prepend)
   
     apply (meson nonalt.elims(3))
   
    apply (meson nonazero.elims(3))
   apply(subgoal_tac "(a#rs) f\<leadsto>* (a#flts rs)")
  apply (metis append_Nil frewritesaalts)
  apply (meson fltsfrewrites fs4 nonalt.elims(3) nonazero.elims(3))
  by (metis append_Cons append_Nil fltsfrewrites frewritesaalts k00 k0a)




lemma bsimp_rewrite: " (rrewrites r ( bsimp r))"
  apply(induction r rule: bsimp.induct)
       apply simp
       apply(case_tac "bsimp r1 = AZERO")
        apply simp
  using continuous_rewrite apply blast
       apply(case_tac "\<exists>bs. bsimp r1 = AONE bs")
        apply(erule exE)
        apply simp
        apply(subst bsimp_ASEQ2)
        apply (meson real_trans rrewrite.intros(3) rrewrites.intros(2) star_seq star_seq2)
       apply (smt (verit, best) bsimp_ASEQ0 bsimp_ASEQ1 real_trans rrewrite.intros(2) rs2 star_seq star_seq2)
      defer
  using bsimp_aalts_simpcases(2) apply blast
  apply simp
  apply simp
  apply simp

  apply auto
  apply(subgoal_tac "AALTs bs1 rs \<leadsto>* AALTs bs1 (map bsimp rs)")
  apply(subgoal_tac "AALTs bs1 (map bsimp rs) \<leadsto>* AALTs bs1 (flts (map bsimp rs))")
    apply(subgoal_tac "AALTs bs1 (flts (map bsimp rs)) \<leadsto>* bsimp_AALTs bs1 (flts (map bsimp rs))")
     apply(rule real_trans)
  prefer 2
      apply(assumption)
  using real_trans apply blast
  prefer 3
    apply (simp add: srewrites_alt1 trivialbsimpsrewrites)
  using bsimp_AALTsrewrites apply blast
  by (simp add: fltsrewrites)

lemma rewritenullable: "\<lbrakk>r1 \<leadsto> r2; bnullable r1 \<rbrakk> \<Longrightarrow> bnullable r2"
  apply(induction r1 r2 rule: rrewrite.induct)
             apply(simp)+
  apply (metis bnullable_correctness erase_fuse)
          apply simp
         apply simp
        apply auto[1]
       apply auto[1]
      apply auto[4]
     apply (metis UnCI bnullable_correctness erase_fuse imageI)
    apply (metis bnullable_correctness erase_fuse)
   apply (metis bnullable_correctness erase_fuse)
  by (metis bnullable_correctness erase.simps(5) erase_fuse)

lemma rewrite_non_nullable: "\<lbrakk>r1 \<leadsto> r2; \<not>bnullable r1 \<rbrakk> \<Longrightarrow> \<not>bnullable r2"
  apply(induction r1 r2 rule: rrewrite.induct)
             apply auto 
      apply (metis bnullable_correctness erase_fuse)+
  done


lemma rewritesnullable: "\<lbrakk> r1 \<leadsto>* r2; bnullable r1 \<rbrakk> \<Longrightarrow> bnullable r2"
  apply(induction r1 r2 rule: rrewrites.induct)
   apply simp
  apply(rule rewritenullable)
   apply simp
  apply simp
  done

lemma nonbnullable_lists_concat: " \<lbrakk> \<not> (\<exists>r0\<in>set rs1. bnullable r0); \<not> bnullable r; \<not> (\<exists>r0\<in>set rs2. bnullable r0)\<rbrakk> \<Longrightarrow> 
\<not>(\<exists>r0 \<in> (set (rs1@[r]@rs2)). bnullable r0 ) "
  apply simp
  apply blast
  done



lemma nomember_bnullable: "\<lbrakk> \<not> (\<exists>r0\<in>set rs1. bnullable r0); \<not> bnullable r; \<not> (\<exists>r0\<in>set rs2. bnullable r0)\<rbrakk>
 \<Longrightarrow> \<not>bnullable (AALTs bs (rs1 @ [r] @ rs2))"
  using nonbnullable_lists_concat qq3 by presburger

lemma bnullable_segment: " bnullable (AALTs bs (rs1@[r]@rs2)) \<Longrightarrow> bnullable (AALTs bs rs1) \<or> bnullable (AALTs bs rs2) \<or> bnullable r"
  apply(case_tac "\<exists>r0\<in>set rs1.  bnullable r0")

  using qq3 apply blast
  apply(case_tac "bnullable r")

  apply blast
  apply(case_tac "\<exists>r0\<in>set rs2.  bnullable r0")

  using bnullable.simps(4) apply presburger
  apply(subgoal_tac "False")

  apply blast

  using nomember_bnullable by blast

  

lemma bnullablewhichbmkeps: "\<lbrakk>bnullable  (AALTs bs (rs1@[r]@rs2)); \<not> bnullable (AALTs bs rs1); bnullable r \<rbrakk>
 \<Longrightarrow> bmkeps (AALTs bs (rs1@[r]@rs2)) = bs @ (bmkeps r)"
  using qq2 bnullable_Hdbmkeps_Hd by force

lemma rrewrite_nbnullable: "\<lbrakk> r1 \<leadsto> r2 ; \<not> bnullable r1 \<rbrakk> \<Longrightarrow> \<not>bnullable r2"
  apply(induction rule: rrewrite.induct)
             apply auto[1]
            apply auto[1]
           apply auto[1]
           apply (metis bnullable_correctness erase_fuse)
          apply auto[1]
         apply auto[1]
        apply auto[1]
       apply auto[1]
      apply auto[1]
      apply (metis bnullable_correctness erase_fuse)
     apply auto[1]
     apply (metis bnullable_correctness erase_fuse)
    apply auto[1]
    apply (metis bnullable_correctness erase_fuse)
   apply auto[1]
  apply auto[1]
  by (metis bnullable_correctness erase_fuse)

lemma spillbmkepssame: "\<lbrakk>bnullable (AALTs bs1 rs1)\<rbrakk> \<Longrightarrow> bmkeps (AALTs bs [AALTs bs1 rs1]) = bmkeps (AALTs bs (map (fuse bs1) rs1))"

  by (metis k0a list.set_intros(1) qs3)

lemma spillbmkepslist: "\<lbrakk>bnullable (AALTs bs1 rs1); \<not>bnullable (AALTs bs rs)\<rbrakk> \<Longrightarrow>
 bmkeps (AALTs bs (rs@ [AALTs bs1 rs1])) = bmkeps (AALTs bs (rs@(map (fuse bs1) rs1)))"
  by (metis (no_types, lifting) k0a list.set_intros(1) qq2 qq3 qq4 qs3)



lemma spillbmkepslistr: "bnullable (AALTs bs1 rs1)
    \<Longrightarrow> bmkeps (AALTs bs (AALTs bs1 rs1 # rsb)) = bmkeps (AALTs bs ( map (fuse bs1) rs1 @ rsb))"
  apply(subst bnullable_Hdbmkeps_Hd)
  
   apply simp
  by (metis bmkeps.simps(3) k0a list.set_intros(1) qq1 qq4 qs3)

lemma third_segment_bnullable: "\<lbrakk>bnullable (AALTs bs (rs1@rs2@rs3)); \<not>bnullable (AALTs bs rs1); \<not>bnullable (AALTs bs rs2)\<rbrakk> \<Longrightarrow> 
bnullable (AALTs bs rs3)"
  
  by (metis append.left_neutral append_Cons bnullable.simps(1) bnullable_segment rrewrite.intros(7) rrewrite_nbnullable)

lemma notbnullable_list_alt_interchange: "\<not>(bnullable (AALTs bs rs)) \<equiv> \<forall>r \<in> (set rs). \<not> bnullable r"
  by simp


lemma third_segment_bmkeps:  "\<lbrakk>bnullable (AALTs bs (rs1@rs2@rs3)); \<not>bnullable (AALTs bs rs1); \<not>bnullable (AALTs bs rs2)\<rbrakk> \<Longrightarrow> 
bmkeps (AALTs bs (rs1@rs2@rs3) ) = bmkeps (AALTs bs rs3)"
  apply(subgoal_tac "bnullable (AALTs bs rs3)")
   apply(subgoal_tac "\<forall>r \<in> set (rs1@rs2). \<not>bnullable r")
  apply(subgoal_tac "bmkeps (AALTs bs (rs1@rs2@rs3)) = bmkeps (AALTs bs ((rs1@rs2)@rs3) )")
  apply (metis qq2 qq3)

  apply (metis append.assoc)

  apply (metis append.assoc in_set_conv_decomp r2 third_segment_bnullable)

  using third_segment_bnullable by blast


lemma rewrite_bmkepsalt: " \<lbrakk>bnullable (AALTs bs (rsa @ AALTs bs1 rs1 # rsb)); bnullable (AALTs bs (rsa @ map (fuse bs1) rs1 @ rsb))\<rbrakk>
       \<Longrightarrow> bmkeps (AALTs bs (rsa @ AALTs bs1 rs1 # rsb)) = bmkeps (AALTs bs (rsa @ map (fuse bs1) rs1 @ rsb))"
  apply(case_tac "bnullable (AALTs bs rsa)")
  
  using qq1 apply force
  apply(case_tac "bnullable (AALTs bs1 rs1)")
  apply(subst qq2)

  
  using r2 apply blast
  
    apply (metis list.set_intros(1))
  apply (smt (verit, ccfv_threshold) append_eq_append_conv2 list.set_intros(1) qq2 qq3 rewritenullable rrewrite.intros(8) self_append_conv2 spillbmkepslistr)


  thm qq1
  apply(subgoal_tac "bmkeps  (AALTs bs (rsa @ AALTs bs1 rs1 # rsb)) = bmkeps (AALTs bs rsb) ")
   prefer 2
  
  apply (metis append_Cons append_Nil bnullable.simps(1) bnullable_segment rewritenullable rrewrite.intros(11) third_segment_bmkeps)

  by (metis bnullable.simps(4) rewrite_non_nullable rrewrite.intros(10) third_segment_bmkeps)



lemma rewrite_bmkeps: "\<lbrakk> r1 \<leadsto> r2; (bnullable r1)\<rbrakk> \<Longrightarrow> bmkeps r1 = bmkeps r2"

  apply(frule rewritenullable)
  apply simp
  apply(induction r1 r2 rule: rrewrite.induct)
             apply simp
  using bnullable.simps(1) bnullable.simps(5) apply blast
         apply (simp add: b2)
        apply simp
         apply simp
  apply(frule bnullable_segment)
        apply(case_tac "bnullable (AALTs bs rs1)")
  using qq1 apply force
        apply(case_tac "bnullable r")
  using bnullablewhichbmkeps rewritenullable apply presburger
        apply(subgoal_tac "bnullable (AALTs bs rs2)")
  apply(subgoal_tac "\<not> bnullable r'")
  apply (simp add: qq2 r1)
  
  using rrewrite_nbnullable apply blast

        apply blast
       apply (simp add: flts_append qs3)

  apply (meson rewrite_bmkepsalt)
  
  using bnullable.simps(4) q3a apply blast

  apply (simp add: q3a)

  using bnullable.simps(1) apply blast

  by (simp add: b2)
 



lemma rewrites_bmkeps: "\<lbrakk> (r1 \<leadsto>* r2); (bnullable r1)\<rbrakk> \<Longrightarrow> bmkeps r1 = bmkeps r2"
  apply(induction r1 r2 rule: rrewrites.induct)
   apply simp
  apply(subgoal_tac "bnullable r2")
  prefer 2
   apply(metis rewritesnullable)
  apply(subgoal_tac "bmkeps r1 = bmkeps r2")
   prefer 2
   apply fastforce
  using rewrite_bmkeps by presburger


thm rrewrite.intros(12)
lemma alts_rewrite_front: "r \<leadsto> r' \<Longrightarrow> AALTs bs (r # rs) \<leadsto> AALTs bs (r' # rs)"
  by (metis append_Cons append_Nil rrewrite.intros(6))

lemma alt_rewrite_front: "r \<leadsto> r' \<Longrightarrow> AALT bs r r2 \<leadsto> AALT bs r' r2"
  using alts_rewrite_front by blast

lemma to_zero_in_alt: " AALT bs (ASEQ [] AZERO r) r2 \<leadsto>  AALT bs AZERO r2"
  by (simp add: alts_rewrite_front rrewrite.intros(1))

lemma alt_remove0_front: " AALT bs AZERO r \<leadsto> AALTs bs [r]"
  by (simp add: rrewrite0away)

lemma alt_rewrites_back: "r2 \<leadsto>* r2' \<Longrightarrow>AALT bs r1 r2 \<leadsto>* AALT bs r1 r2'"
  apply(induction r2 r2' arbitrary: bs rule: rrewrites.induct)
   apply simp
  by (meson rs1 rs2 srewrites_alt1 ss1 ss2)

lemma rewrite_fuse: " r2 \<leadsto> r3 \<Longrightarrow> fuse bs r2 \<leadsto>* fuse bs r3"
  apply(induction r2 r3 arbitrary: bs rule: rrewrite.induct)
             apply auto

           apply (simp add: continuous_rewrite)

          apply (simp add: r_in_rstar rrewrite.intros(2))

         apply (metis fuse_append r_in_rstar rrewrite.intros(3))

  using r_in_rstar star_seq apply blast

  using r_in_rstar star_seq2 apply blast

  using contextrewrites2 r_in_rstar apply auto[1]
  
       apply (simp add: r_in_rstar rrewrite.intros(7))

  using rrewrite.intros(8) apply auto[1]

   apply (metis append_assoc r_in_rstar rrewrite.intros(9))

  apply (metis append_assoc r_in_rstar rrewrite.intros(10))

  apply (simp add: r_in_rstar rrewrite.intros(11))

  by (metis fuse_append r_in_rstar rrewrite.intros(12))


  

lemma rewrites_fuse:  "r2 \<leadsto>* r2' \<Longrightarrow>  (fuse bs1 r2) \<leadsto>*  (fuse bs1 r2')"
  apply(induction r2 r2' arbitrary: bs1 rule: rrewrites.induct)
   apply simp
  by (meson real_trans rewrite_fuse)

lemma rewrite_der_alt: "bder c (AALTs bs [AALTs bs1 rs1]) \<leadsto>* bder c (AALTs (bs@bs1) rs1)"
  apply(induction rs1)
   apply simp
  
  apply (metis fltsrewrites k0a rrewrite.intros(9) rs2)
  by (metis bder.simps(4) bder_bsimp_AALTs bsimp_AALTs.simps(2) bsimp_AALTsrewrites fuse.simps(4))

lemma  bder_fuse_list: " map (bder c \<circ> fuse bs1) rs1 = map (fuse bs1 \<circ> bder c) rs1"
  apply(induction rs1)
  apply simp
  by (simp add: bder_fuse)

lemma rewrite_der_alt0: " AALTs bs (rs0 @ [AALTs bs1 (map (bder c) rs1)]) \<leadsto>* AALTs bs (rs0 @ map (bder c \<circ> fuse bs1) rs1)"
  apply(simp add: bder_fuse_list)
  apply(induction rs1 arbitrary: rs0)
  
   apply (metis fltsfrewrites frewritesaalts k0a list.simps(8))
  apply(drule_tac x = "rs0@[(bder c  \<circ> fuse bs1) a]" in meta_spec)
  by (metis List.map.compositionality fltsfrewrites frewritesaalts k0a)
  


lemma rewrite_der_alt1: "bder c (AALTs bs (rsa@[AALTs bs1 rs1])) \<leadsto>* bder c (AALTs bs (rsa@(map (fuse bs1) rs1)))"
  apply simp
  by (meson rewrite_der_alt0)

thm rrewrite.intros(8)

lemma rewrite_der_altmiddle: "bder c (AALTs bs (rsa @ AALTs bs1 rs1 # rsb)) \<leadsto>* bder c (AALTs bs (rsa @ map (fuse bs1) rs1 @ rsb))"
   apply simp
   apply(simp add: bder_fuse_list)
  apply(rule many_steps_later)
   apply(subst rrewrite.intros(8))
   apply simp

  by fastforce

lemma rewrite_after_der: "r1 \<leadsto> r2 \<Longrightarrow> (bder c r1) \<leadsto>* (bder c r2)"
  apply(induction r1 r2 arbitrary: c rule: rrewrite.induct)
  
             apply (simp add: r_in_rstar rrewrite.intros(1))

          apply (metis L.simps(1) L_bsimp_erase bder.simps(1) bsimp.simps(1) bsimp_ASEQ0 bsimp_rewrite der_correctness erase.simps(1) erase_bder xxx_bder2)
           apply(simp)
           apply(rule many_steps_later)
            apply(rule to_zero_in_alt)
           apply(rule many_steps_later)
  apply(rule alt_remove0_front)
           apply(rule many_steps_later)
            apply(rule rrewrite.intros(12))
  using bder_fuse fuse_append rs1 apply presburger
          apply(case_tac "bnullable r1")
  prefer 2
           apply(subgoal_tac "\<not>bnullable r2")
            prefer 2
  using rewrite_non_nullable apply presburger
           apply simp+
  
  using star_seq apply auto[1]
          apply(subgoal_tac "bnullable r2")
           apply simp+
  apply(subgoal_tac "bmkeps r1 = bmkeps r2")
  prefer 2
  using rewrite_bmkeps apply auto[1]
  using contextrewrites1 star_seq apply auto[1]
  using rewritenullable apply auto[1]
         apply(case_tac "bnullable r1")
          apply simp
          apply(subgoal_tac "ASEQ [] (bder c r1) r3 \<leadsto> ASEQ [] (bder c r1) r4") 
           prefer 2
  using rrewrite.intros(5) apply blast
          apply(rule many_steps_later)
           apply(rule alt_rewrite_front)
           apply assumption
  apply (meson alt_rewrites_back rewrites_fuse) 

       apply (simp add: r_in_rstar rrewrite.intros(5))

  using contextrewrites2 apply force

  using rrewrite.intros(7) apply force
  
  using rewrite_der_altmiddle apply auto[1]
  
  apply (metis bder.simps(4) bder_fuse_list map_map r_in_rstar rrewrite.intros(9))

  apply (metis List.map.compositionality bder.simps(4) bder_fuse_list r_in_rstar rrewrite.intros(10))

  apply (simp add: r_in_rstar rrewrite.intros(11))

  by (metis bder.simps(4) bder_bsimp_AALTs bsimp_AALTs.simps(2) bsimp_AALTsrewrites)
  


lemma rewrites_after_der: "  r1 \<leadsto>* r2  \<Longrightarrow>  (bder c r1) \<leadsto>* (bder c r2)"
  apply(induction r1 r2 rule: rrewrites.induct)
   apply(rule rs1)
  by (meson real_trans rewrite_after_der)
  



lemma central: " (bders r s) \<leadsto>*  (bders_simp r s)" 
  apply(induct s arbitrary: r rule: rev_induct)

   apply simp
  apply(subst bders_append)
  apply(subst bders_simp_append)
  by (metis bders.simps(1) bders.simps(2) bders_simp.simps(1) bders_simp.simps(2) bsimp_rewrite real_trans rewrites_after_der)



thm arexp.induct

lemma quasi_main: "bnullable (bders r s) \<Longrightarrow> bmkeps (bders r s) = bmkeps (bders_simp r s)"
  using central rewrites_bmkeps by blast

lemma quasi_main1: "bnullable (bders_simp r s) \<Longrightarrow> bmkeps (bders r s) = bmkeps (bders_simp r s)"
  by (simp add: b4 quasi_main)

lemma main_main: "blexer r s = blexer_simp r s"
  by (simp add: b4 blexer_def blexer_simp_def quasi_main)



inductive simi :: "arexp \<Rightarrow> arexp \<Rightarrow> bool" ("_ ~~~~ _" [100, 100] 100)
  where
 "r ~~~~ r"
| "r1 ~~~~ r2 \<Longrightarrow> r2 ~~~~ r1"
| "bsimp r1 = AZERO \<Longrightarrow> ASEQ bs r1 r2 ~~~~ AZERO"
| "bsimp r2 = AZERO \<Longrightarrow> ASEQ bs r1 r2 ~~~~ AZERO"
| "bsimp r1 = AONE bs1 \<Longrightarrow> ASEQ bs r1 r2 ~~~~ fuse (bs@bs1) (bsimp r2)"
| "\<lbrakk>r1 ~~~~ r2; r3 ~~~~ r4\<rbrakk> \<Longrightarrow> ASEQ bs r1 r3 ~~~~ ASEQ bs r2 r4"
| "flts ( map bsimp as) = [] \<Longrightarrow> (AALTs bs as) ~~~~ AZERO"
| "flts ( map bsimp as) = [r] \<Longrightarrow> (AALTs bs as) ~~~~ fuse bs r"
| "flts ( map bsimp as) = (r1#r2#rs) \<Longrightarrow> (AALTs bs as) ~~~~ (AALTs bs (r1#r2#rs))"
| "AALTs bs (map (fuse bs1) as) ~~~~ AALTs (bs@bs1) as"
| "\<lbrakk>r1 ~~~~ r2; r2 ~~~~ r3\<rbrakk> \<Longrightarrow> r1 ~~~~ r3"


datatype tfoo = TZERO | TONE nat | TSEQ tfoo tfoo


inductive tsimilar :: "tfoo \<Rightarrow> tfoo \<Rightarrow> bool" 
  where
  "tsimilar TZERO TZERO"
|  "tsimilar t1 t2 \<Longrightarrow> tsimilar t2 t1"
| "tsimilar (TONE i)  (TONE j)"
| "\<lbrakk>tsimilar t1 t2; tsimilar t3 t4 \<rbrakk> \<Longrightarrow> tsimilar (TSEQ t1 t3) (TSEQ t2 t4)"

lemma hierachy_maintained:
  assumes "tsimilar x y" "\<exists>c t1 t2. 
 x = TZERO \<and> y = TONE c \<or> x = TONE c \<and> y = TZERO 
\<or>  x = TONE c \<and> y = TSEQ t1 t2 \<or>  x = TSEQ t1 t2 \<and> y = TONE c
\<or>  x = TZERO \<and> y = TSEQ t1 t2 \<or>  x = TSEQ t1 t2 \<and> y = TZERO"
  shows False
  using assms
  apply(induction rule: tsimilar.induct)
  apply fastforce
  apply fastforce
  apply fastforce
  apply fastforce
  done


lemma notsimilar:
  assumes "tsimilar x y" "\<exists>c. x = TZERO \<and> y = TONE c \<or> x = TONE c \<and> y = TZERO"
  shows False
  using assms by (induction rule: tsimilar.induct) auto


lemma notsimilar1 : assumes "(tsimilar TZERO (TONE i)) \<and>(tsimilar (TONE i) TZERO)"
  shows "False"
  using assms notsimilar by blast

lemma no_connect_0char: assumes "r1 ~~~~ rx" "rx ~~~~ r2" shows  
"\<forall>x1 x2a. \<not>(r1 = AZERO \<and> r2 = ACHAR x1 x2a \<or> r1 = ACHAR x1 x2a \<and> r2 = AZERO)"
  using assms
  apply -
  apply(subgoal_tac "r1 ~~~~ r2")

  apply(induction rule: simi.induct)
   
  sorry

lemma notcong0charaux: assumes "r1 ~~~~ r2"
  shows " \<forall>x1 x2a. (r1 = AZERO \<and> r2 = ACHAR x1 x2a \<or> r1 = ACHAR x1 x2a \<and> r2 = AZERO) \<longrightarrow> \<not>(\<exists>rx. r1 ~~~~ rx \<and> rx ~~~~ r2) "
  using assms
  apply -
  apply(induction rule: simi.induct)
  apply force
  using simi.intros(1) apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
   apply blast
  by (meson no_connect_0char)



lemma notcong0char: assumes "r1 ~~~~ r2" 
  shows "( \<forall>x1 x2a. \<not>(r1 = AZERO \<and> r2 = ACHAR x1 x2a \<and> (\<exists>rx. r1 ~~~~ rx \<and> rx ~~~~ r2)) \<and> \<not>(r1 = ACHAR x1 x2a \<and> r2 = AZERO) \<and> (\<exists>rx. r1 ~~~~ rx \<and> rx ~~~~ r2) ) "
  using assms
  apply -
  apply(induction rule: simi.induct)
  using simi.intros(1) apply fastforce
  apply (metis simi.intros(2))
  using simi.intros(1) simi.intros(3) apply blast
  using simi.intros(1) simi.intros(4) apply blast
  using simi.intros(1) simi.intros(5) apply blast
  apply (metis arexp.distinct(5) simi.intros(6))
  using simi.intros(1) simi.intros(7) apply blast
  using simi.intros(1) simi.intros(8) apply blast
  using simi.intros(1) simi.intros(9) apply blast
  apply (meson arexp.simps(27) simi.intros(1) simi.intros(10))
  by (metis no_connect_0char)





lemma simp_orig_cong: shows " bsimp r ~~~~ r"
  apply(induct r)
       apply simp
  apply(rule simi.intros)
  apply (simp add: simi.intros(1))
     apply (simp add: simi.intros(1))
  apply (metis b1 bsimp.simps(1) bsimp_ASEQ.simps(1) bsimp_ASEQ0 bsimp_ASEQ1 simi.intros(2) simi.intros(3) simi.intros(4) simi.intros(5) simi.intros(6))
  apply (smt (verit, best) bsimp.simps(2) bsimp_AALTs.elims simi.intros(2) simi.intros(7) simi.intros(8) simi.intros(9))
  using bsimp.simps(6) simi.intros(1) by presburger




lemma r0dercong: shows " AZERO ~~~~ r2 \<Longrightarrow> bder c AZERO ~~~~ bder c r2"
  apply(induct r2)
  apply simp
      apply (simp add: simi.intros(1))
      apply (simp add: simi.intros)
     apply (meson notcong0char)
  sorry



lemma plus0cong: shows "\<forall>r. AALTs bs (AZERO # [r]) ~~~~ fuse bs r"
  apply(rule allI)
  apply(subgoal_tac " AALT bs AZERO r ~~~~ fuse bs (bsimp r)")
   prefer 2



lemma dersimp_cong: shows "r1 ~~~~ r2 \<Longrightarrow> bder c r1 ~~~~ bder c r2"
  apply(induct r1)
  using r0dercong apply blast
  sorry



(*say I have a premise that says x=t, and there's a simplification rule for t (which we denote as r) *)

inductive sim :: "rexp \<Rightarrow> rexp \<Rightarrow> bool" ("_ ~~~ _" [100, 100] 100)
  where
  "CR c ~~~ CR c"
| "ONE ~~~ ONE"
| "\<lbrakk>r11 ~~~ r12; r21 ~~~ r22\<rbrakk> \<Longrightarrow> SEQ r11 r21 ~~~ SEQ r12 r22" 
| "\<lbrakk>r11 ~~~ r12; r21 ~~~ r22\<rbrakk> \<Longrightarrow> ALT r11 r21 ~~~ ALT r12 r22"
| "r1 ~~~ r2 \<Longrightarrow> STAR r1 ~~~ STAR r2"


lemma sim0:
  assumes "r1 ~~~ r2"
  shows "(\<forall>v.  \<Turnstile> v : r1  \<longleftrightarrow> \<Turnstile> v : r2)"
using assms
apply(induct r1 r2 rule: sim.induct)
apply(auto)
  apply (metis Prf.intros(1) Prf_elims(2))
  apply (metis Prf.intros(1) Prf_elims(2))
  apply (smt (verit, del_insts) Prf.intros(2) Prf.intros(3) Prf_elims(3))
  apply (smt (verit, del_insts) Prf.intros(2) Prf.intros(3) Prf_elims(3))
  apply (metis Prf.intros(6) Prf_elims(6))
  by (metis Prf.intros(6) Prf_elims(6))


lemma nzeroablev: "\<not> (zeroable r) \<Longrightarrow> \<exists>v. \<Turnstile> v: r"
  apply(induct r)
  apply simp
      apply simp
      apply(rule exI)
      apply(rule Prf.intros)
   apply(rule exI)
      apply(rule Prf.intros)
  apply(auto)[1]
  apply(rule exI)
    apply(rule Prf.intros)
     apply(assumption)
    apply(assumption)
   apply(auto)[1]
  apply(rule exI)
   apply(rule Prf.intros)
  apply(assumption)
  using Posix_Prf Posix_STAR2 by blast

thm bcong_def retrieve.induct
thm Prf_elims
thm Prf.intros
thm flat.simps


lemma congsymm: shows "bcong r1 r2 \<Longrightarrow> bcong r2 r1"
  by (simp add: BitCodedlots.bcong_def)


lemma altshape: shows " (\<forall>v. \<Turnstile> v : r1 \<longleftrightarrow> \<Turnstile> v : r2) \<Longrightarrow> (\<not> (zeroable r1) \<and> \<not>(zeroable r2)) \<Longrightarrow> r1 = r2"
  oops

lemma symshape: shows " (\<forall>v.  \<Turnstile> v : r1  \<longleftrightarrow> \<Turnstile> v : r2) \<and> \<not>(zeroable r1)\<and> \<not>(zeroable r2) \<Longrightarrow> r1 = r2 "
  apply(induct r1 arbitrary : r2 )
       apply(case_tac r2)
  apply simp
           apply simp
          apply simp
         apply simp
        apply simp
       apply simp
      apply simp
      apply(case_tac r2)
           apply simp
           apply simp
         apply simp

         apply(drule_tac x="Void" in spec)
  apply(simp add: Prf.intros)
         apply (meson Prf_elims(5) val.distinct(1))
  apply simp
  apply (meson Prf.intros(4) Prf_elims(2) val.distinct(3))
  apply (meson Prf.intros(4) Prf_elims(3) val.distinct(5) val.distinct(7))
      apply (meson Prf.intros(4) Prf_elims(6) val.distinct(9))
     apply(case_tac r2)
  apply fastforce
  apply (meson Prf.intros(4) Prf_elims(5) val.distinct(1))
  apply (metis Prf.intros(5) Prf_elims(5) val.inject(1))
  apply (meson Prf.intros(5) Prf_elims(2) val.distinct(11))
  apply (meson Prf.intros(5) Prf_elims(3) val.distinct(13) val.distinct(15))
     apply (metis L_flat_Prf1 flat.simps(6) mkeps.simps(4) mkeps_nullable nullable.simps(3) nullable.simps(6) nullable_correctness)
    apply(case_tac r2)
  apply fastforce
  apply (meson Prf.intros(4) Prf_elims(2) val.distinct(3))
       apply (meson Prf.intros(5) Prf_elims(2) val.distinct(11))
  apply(subst (asm) zeroable.simps)
  apply(simp del: zeroable.simps)
       apply(auto)[1]
       apply(drule_tac x="x41" in meta_spec)
       apply(drule meta_mp)
        apply(simp)
  apply(rule allI)
  apply(drule nzeroablev)
       apply(drule nzeroablev)
       apply(auto)[1]
       apply(drule_tac x="Seq v va" in spec)
       apply(drule_tac x="x41" in meta_spec)
       apply(drule meta_mp)
        apply(simp)
  apply(rule allI)
  sorry

lemma simstar:
  assumes "\<forall>v. \<turnstile> v : STAR r1 = \<turnstile> v : STAR x6" "nzero r1" "nzero x6"
  shows "\<forall>v. \<turnstile>v : r1 = \<turnstile> v : x6"
  sorry

lemma congshape: shows "bcong r1 r2 \<longrightarrow> erase(bsimp r1) = erase (bsimp r2)"

  sorry

lemma congrueninduct: shows "\<lbrakk>bcong r1 r2; bcong r3 r4 \<rbrakk> \<Longrightarrow> bcong (ASEQ bs r1 r3) (ASEQ bs r2 r4)"
  apply(simp add: bcong_def)
  apply(case_tac "\<exists>bs1. bsimp r1 = AONE bs1")
  apply(erule exE)

   apply(simp only: bsimp_ASEQ.simps)

  apply(simp only: congshape)
  sorry

(*real CT *)
thm bsimp.simps

lemma cong_pzero: shows "bsimp r0 = AZERO \<longrightarrow> bcong r (AALT []  r r0)"
  apply(simp add: bcong_def)
  sorry

lemma cong_szero: shows "bcong AZERO r \<longrightarrow> bsimp r = AZERO"
  apply(simp add: bcong_def )
  apply auto
  using L.simps(1) xxx_bder2 by presburger

lemma seq_zero_simp: shows "bsimp r1 = AZERO \<longrightarrow> bsimp r2 = AZERO \<longrightarrow> bsimp (ASEQ bs r1 r2) = AZERO"
  using bsimp.simps(1) bsimp_ASEQ.simps(1) by presburger

lemma zero_stays_zero: shows "bsimp r = AZERO \<longrightarrow> bsimp (bder c r) = AZERO"
  by (metis L_bsimp_erase bder.simps(1) der_correctness erase_bder good.simps(1) good1a xxx_bder2)

lemma one_becomes_zero: shows "bsimp r = AONE bs \<longrightarrow> bsimp (bder c r) = AZERO"
  by (metis L.simps(1) L_bsimp_erase bder.simps(2) der_correctness erase.simps(1) erase_bder xxx_bder2)


lemma zero_cong_zero: shows " bcong AZERO r \<longrightarrow> bcong (bder c AZERO) (bder c r)"
  apply(induct r)
  apply simp
  apply (metis bder.simps(1) bder.simps(2) bsimp.simps(3) rsrcong)
     apply (metis arexp.distinct(3) bsimp.simps(5) cong_szero)
  apply (metis bder.simps(1) cong_szero congsymm rsrcong zero_stays_zero)
  apply (metis bder.simps(1) cong_szero congsymm rsrcong zero_stays_zero)
  by (metis arexp.distinct(9) bsimp.simps(6) cong_szero)

thm spec retrieve.simps(1)


lemma orig_arexp: shows " (erase r = ONE) \<and>( bsimp r = r) \<longrightarrow> (\<exists>y. r = AONE y)"
  apply(induct r)
  apply(simp)
  apply(simp)
  apply(simp)
  apply(simp)
     prefer 2
  apply(simp)
  apply(simp)
  sorry


lemma retrieve_one_void :
  assumes "retrieve (AONE x) Void = retrieve r Void \<and> (erase r ) = ONE \<and>(r \<noteq> AALTs(_))"
  shows " r = AONE x"
  using assms
  apply(induct r)

       apply(simp)

  apply simp



       apply(auto)    

  apply(subst (asm) retrieve.simps)

lemma one_cong_one: shows "bcong (AONE x) r \<longrightarrow> bsimp r = AONE x"
  apply(simp add: bcong_def)
  apply(rule impI)
  apply(erule conjE)
  apply(drule_tac x = "Void" in spec)
  sorry



lemma cong_der: shows " bcong r1 r2 \<longrightarrow> bcong (bder c r1) (bder c r2)"
  apply(induct r1 )
  using zero_cong_zero apply presburger
  apply (smt (verit, best) L.simps(1) LLLL(1) bcong_def bder.simps(2) der_correctness erase.simps(1) erase_bder good1 xxx_bder)


  sorry



lemma CTU:
  shows "bsimp_AALTs bs as = li bs as"
  apply(induct bs as rule: li.induct)
    apply(auto)
  done

find_theorems "bder _ (bsimp_AALTs _ _)"

lemma CTa:
  assumes "\<forall>r \<in> set as. nonalt r \<and> r \<noteq> AZERO"
  shows  "flts as = as"
  using assms
  apply(induct as)
   apply(simp)
  apply(case_tac as)
   apply(simp)
  apply (simp add: k0b)
  using flts_nothing by auto

lemma CT0:
  assumes "\<forall>r \<in> set as1. nonalt r \<and> r \<noteq> AZERO" 
  shows "flts [bsimp_AALTs bs1 as1] =  flts (map (fuse bs1) as1)"
  using assms CTa
  apply(induct as1 arbitrary: bs1)
    apply(simp)
   apply(simp)
  apply(case_tac as1)
   apply(simp)
  apply(simp)
proof -
fix a :: arexp and as1a :: "arexp list" and bs1a :: "bit list" and aa :: arexp and list :: "arexp list"
  assume a1: "nonalt a \<and> a \<noteq> AZERO \<and> nonalt aa \<and> aa \<noteq> AZERO \<and> (\<forall>r\<in>set list. nonalt r \<and> r \<noteq> AZERO)"
  assume a2: "\<And>as. \<forall>r\<in>set as. nonalt r \<and> r \<noteq> AZERO \<Longrightarrow> flts as = as"
  assume a3: "as1a = aa # list"
  have "flts [a] = [a]"
using a1 k0b by blast
then show "fuse bs1a a # fuse bs1a aa # map (fuse bs1a) list = flts (fuse bs1a a # fuse bs1a aa # map (fuse bs1a) list)"
  using a3 a2 a1 by (metis (no_types) append.left_neutral append_Cons flts_fuse k00 k0b list.simps(9))
qed
  
  
lemma CT01:
  assumes "\<forall>r \<in> set as1. nonalt r \<and> r \<noteq> AZERO" "\<forall>r \<in> set as2. nonalt r \<and> r \<noteq> AZERO" 
  shows "flts [bsimp_AALTs bs1 as1, bsimp_AALTs bs2 as2] =  flts ((map (fuse bs1) as1) @ (map (fuse bs2) as2))"
  using assms CT0
  by (metis k0 k00)
  


lemma CT_exp:
  assumes "\<forall>a \<in> set as. bsimp (bder c (bsimp a)) = bsimp (bder c a)"
  shows "map bsimp (map (bder c) as) = map bsimp (map (bder c) (map bsimp as))"
  using assms
  apply(induct as)
   apply(auto)
  done

lemma asize_set:
  assumes "a \<in> set as"
  shows "asize a < Suc (sum_list (map asize as))"
  using assms
  apply(induct as arbitrary: a)
   apply(auto)
  using le_add2 le_less_trans not_less_eq by blast
  

lemma XXX2a_long_without_good:
  shows "bsimp (bder c (bsimp a)) = bsimp (bder c a)"
  apply(induct a arbitrary: c taking: "\<lambda>a. asize a" rule: measure_induct)
  apply(case_tac x)
       apply(simp)
      apply(simp)
     apply(simp)
  prefer 3
    apply(simp)
  (* AALT case *)
   prefer 2
   apply(simp del: bsimp.simps)
   apply(subst (2) CT1)
   apply(subst CT_exp)
    apply(auto)[1]
  using asize_set apply blast
   apply(subst CT1[symmetric])
  apply(simp)
  oops

lemma YY:
  assumes "flts (map bsimp as1) = xs"
  shows "flts (map bsimp (map (fuse bs1) as1)) = map (fuse bs1) xs"
  using assms
  apply(induct as1 arbitrary: bs1 xs)
   apply(simp)
  apply(auto)
  by (metis bsimp_fuse flts_fuse k0 list.simps(9))
  

lemma flts_nonalt:
  assumes "flts (map bsimp xs) = ys"
  shows "\<forall>y \<in> set ys. nonalt y"
  using assms
  apply(induct xs arbitrary: ys)
   apply(auto)
  apply(case_tac xs)
   apply(auto)
  using flts2 good1 apply fastforce
  by (smt ex_map_conv list.simps(9) nn1b nn1c)


lemma WWW3:
  shows "flts [bsimp_AALTs bs1 (flts (map bsimp as1))] =
         flts (map bsimp (map (fuse bs1) as1))"
  by (metis CT0 YY flts_nonalt flts_nothing qqq1)

lemma WWW4:
  shows "map (bder c \<circ> fuse bs1) as1 = map (fuse bs1) (map (bder c) as1)"
  apply(induct as1)
   apply(auto)
  using bder_fuse by blast

lemma WWW5:
  shows "map (bsimp \<circ> bder c) as1 = map bsimp (map (bder c) as1)"
  apply(induct as1)
   apply(auto)
  done

lemma WWW6:
  shows "bsimp (bder c (bsimp_AALTs x51 (flts [bsimp a1, bsimp a2]) ) )  = 
 bsimp(bsimp_AALTs x51 (map (bder c) (flts [bsimp a1, bsimp a2]))) "
  using bder_bsimp_AALTs by auto

lemma WWW7:
  shows "bsimp (bsimp_AALTs x51 (map (bder c) (flts [bsimp a1, bsimp a2]))) =
  bsimp(bsimp_AALTs x51 (flts (map (bder c) [bsimp a1, bsimp a2])))"
  sorry


lemma stupid:
  assumes "a = b"
  shows "bsimp(a) = bsimp(b)"
  using assms
  apply(auto)
  done
(*
proving idea:
bsimp_AALTs x51  (map (bder c) (flts [a1, a2])) = bsimp_AALTs x51 (map (bder c) (flts [a1]++[a2]))
= bsimp_AALTs x51  (map (bder c) ((flts [a1])++(flts [a2]))) =  
bsimp_AALTs x51 (map (bder c) (flts [a1]))++(map (bder c) (flts [a2])) = A
and then want to prove that
map (bder c) (flts [a]) = flts [bder c a] under the condition 
that a is either a seq with the first elem being not nullable, or a character equal to c,
or an AALTs, or a star
Then, A = bsimp_AALTs x51 (flts [bder c a]) ++ (map (bder c) (flts [a2])) = A1
Using the same condition for a2, we get
A1 = bsimp_AALTs x51 (flts [bder c a1]) ++ (flts [bder c a2])
=bsimp_AALTs x51 flts ([bder c a1] ++ [bder c a2])
=bsimp_AALTs x51 flts ([bder c a1, bder c a2])
 *)
lemma manipulate_flts:
  shows "bsimp_AALTs x51  (map (bder c) (flts [a1, a2])) = 
bsimp_AALTs x51 ((map (bder c) (flts [a1])) @ (map (bder c) (flts [a2])))"
  by (metis k0 map_append)
  
lemma go_inside_flts:
  assumes " (bder c a1 \<noteq> AZERO) "
 "\<not>(\<exists> a01 a02 x02. (  (a1 = ASEQ x02 a01 a02) \<and> bnullable(a01) )      )"
shows "map (bder c) (flts [a1]) = flts [bder c a1]"
  using assms
  apply -
  apply(case_tac a1)
  apply(simp)
  apply(simp)
     apply(case_tac "x32 = c")
  prefer 2
      apply(simp)
     apply(simp)
    apply(simp)
  apply (simp add: WWW4)
   apply(simp add: bder_fuse)
  done

lemma medium010:
  assumes " (bder c a1 = AZERO) "
  shows "map (bder c) (flts [a1]) = [AZERO] \<or> map (bder c) (flts [a1]) = []"
  using assms
  apply -
  apply(case_tac a1)
       apply(simp)
      apply(simp)
  apply(simp)
    apply(simp)
  apply(simp)
  apply(simp)
  done

lemma medium011:
  assumes " (bder c a1 = AZERO) "
  shows "flts (map (bder c)  [a1, a2]) = flts [bder c a2]"
  using assms
  apply -
  apply(simp)
  done

lemma medium01central:
  shows "bsimp(bsimp_AALTs x51 (map (bder c) (flts [a2])) ) = bsimp(bsimp_AALTs x51 (flts [bder c a2]))"
  sorry


lemma plus_bsimp:
  assumes "bsimp( bsimp a) = bsimp (bsimp b)"
  shows "bsimp a = bsimp b"
  using assms
  apply -
  by (simp add: bsimp_idem)
lemma patience_good5:
  assumes "bsimp r = AALTs x y"
  shows " \<exists> a aa list. y = a#aa#list"
  by (metis Nil_is_map_conv arexp.simps(13) assms bsimp_AALTs.elims flts1 good.simps(5) good1 k0a)

(*SAD*)
(*this does not hold actually
lemma bsimp_equiv0:
  shows "bsimp(bsimp r) = bsimp(bsimp (AALTs []  [r]))"
  apply(simp)
  apply(case_tac "bsimp r")
       apply(simp)
      apply(simp)
     apply(simp)
    apply(simp)
 thm good1
  using good1
   apply -
   apply(drule_tac x="r" in meta_spec)
   apply(erule disjE)

    apply(simp only: bsimp_AALTs.simps)
    apply(simp only:flts.simps)
    apply(drule patience_good5)
    apply(clarify)
    apply(subst  bsimp_AALTs_qq)
     apply simp
    prefer 2
  sorry*)

(*exercise: try multiple ways of proving this*)
(*this lemma does not hold.........
lemma bsimp_equiv1:
  shows "bsimp r = bsimp (AALTs []  [r])"
  using plus_bsimp
  apply -
  using bsimp_equiv0 by blast
  (*apply(simp)
  apply(case_tac "bsimp r")
       apply(simp)
      apply(simp)
     apply(simp)
    apply(simp)
(*use lemma good1*)
  thm good1
  using good1
   apply -
   apply(drule_tac x="r" in meta_spec)
   apply(erule disjE)
  
  apply(subst flts_single1)
  apply(simp only: bsimp_AALTs.simps)
    prefer 2
  
  thm flts_single1

  find_theorems "flts _ = _"*)
*)
lemma bsimp_equiv2:
  shows "bsimp (AALTs x51 [r])  =  bsimp (AALT x51 AZERO r)"
  sorry

lemma medium_stupid_isabelle:
  assumes "rs = a # list"
  shows  "bsimp_AALTs x51 (AZERO # rs) = AALTs x51 (AZERO#rs)"
  using assms
  apply -
  apply(simp)
  done 

lemma singleton_list_map:
  shows"map f [a] = [f a]"
  apply simp
  done
lemma map_application2:
  shows"map f [a,b] = [f a, f b]"
  apply simp
  done

lemma medium01:
  assumes " (bder c a1 = AZERO) "
  shows "bsimp(bsimp_AALTs x51 (map (bder c) (flts [ a1, a2]))) =
         bsimp(bsimp_AALTs x51 (flts (map (bder c) [ a1, a2])))"
  apply(subst manipulate_flts)
  using assms
  apply -
  apply(subst medium011)
   apply(simp)
  apply(case_tac "map (bder c) (flts [a1]) = []")
   apply(simp)
  using medium01central apply blast
apply(frule medium010)
  apply(erule disjE)
  prefer 2
   apply(simp)
  apply(simp)
  apply(case_tac a2)
       apply simp
      apply simp
     apply simp
    apply(simp only:flts.simps)
(*HOW do i say here to replace ASEQ ..... back into a2*)
(*how do i say here to use the definition of map function
without lemma, of course*)
(*how do i say here that AZERO#map (bder c) [ASEQ x41 x42 x43]'s list.len >1
without a lemma, of course*)
    apply(subst singleton_list_map)
    apply(simp only: bsimp_AALTs.simps)
    apply(case_tac "bder c (ASEQ x41 x42 x43)")
         apply simp
        apply simp
       apply simp
      prefer 3
      apply simp
     apply(rule_tac t="bder c (ASEQ x41 x42 x43)" 
and s="ASEQ x41a x42a x43a" in subst)
      apply simp
     apply(simp only: flts.simps)
     apply(simp only: bsimp_AALTs.simps)
     apply(simp only: fuse.simps)
     apply(subst (2) bsimp_idem[symmetric])
     apply(subst (1) bsimp_idem[symmetric])
     apply(simp only:bsimp.simps)
     apply(subst map_application2)
     apply(simp only: bsimp.simps)
     apply(simp only:flts.simps)
(*want to happily change between a2 and ASEQ x41 42 43, and eliminate now 
redundant conditions such as  map (bder c) (flts [a1]) = [AZERO] *)
     apply(case_tac "bsimp x42a")
          apply(simp)
         apply(case_tac "bsimp x43a")
              apply(simp)
             apply(simp)
            apply(simp)
           apply(simp)
          prefer 2
          apply(simp)
     apply(rule_tac t="bsimp x43a" 
and s="AALTs x51a x52" in subst)
          apply simp
         apply(simp only:bsimp_ASEQ.simps)
         apply(simp only:fuse.simps)
         apply(simp only:flts.simps)
         
  using medium01central mediumlittle by auto
 
  

lemma medium1:
  assumes " (bder c a1 \<noteq> AZERO) "
 "\<not>(\<exists> a01 a02 x02. (  (a1 = ASEQ x02 a01 a02) \<and> bnullable(a01) )      )"
" (bder c a2 \<noteq> AZERO)"
 "\<not>(\<exists> a11 a12 x12. (  (a2 = ASEQ x12 a11 a12) \<and> bnullable(a11) )      )"
  shows "bsimp_AALTs x51 (map (bder c) (flts [ a1, a2])) =
         bsimp_AALTs x51 (flts (map (bder c) [ a1, a2]))"
  using assms
  apply -
  apply(subst manipulate_flts)
  apply(case_tac "a1")
       apply(simp)
      apply(simp)
     apply(case_tac "x32 = c")
      prefer 2
  apply(simp)
     prefer 2
     apply(case_tac "bnullable x42")
      apply(simp)
       apply(simp)

  apply(case_tac "a2")
            apply(simp)
         apply(simp)
        apply(case_tac "x32 = c")
         prefer 2 
  apply(simp)
        apply(simp)
       apply(case_tac "bnullable x42a")
        apply(simp)
       apply(subst go_inside_flts)
  apply(simp)
        apply(simp)
       apply(simp)
      apply(simp)
      apply (simp add: WWW4)
      apply(simp)
      apply (simp add: WWW4)
  apply (simp add: go_inside_flts)
  apply (metis (no_types, lifting) go_inside_flts k0 list.simps(8) list.simps(9))
  by (smt bder.simps(6) flts.simps(1) flts.simps(6) flts.simps(7) go_inside_flts k0 list.inject list.simps(9))
  
lemma big0:
  shows "bsimp (AALT x51 (AALTs bs1 as1) (AALTs bs2 as2)) =
         bsimp (AALTs x51 ((map (fuse bs1) as1) @ (map (fuse bs2) as2)))"
  by (smt WWW3 bsimp.simps(2) k0 k00 list.simps(8) list.simps(9) map_append)

lemma bignA:
  shows "bsimp (AALTs x51 (AALTs bs1 as1 # as2)) =
         bsimp (AALTs x51 ((map (fuse bs1) as1) @ as2))"
  apply(simp)
  apply(subst k0)
  apply(subst WWW3)
  apply(simp add: flts_append)
  done


lemma XXX4ab:
  shows "good (bders_simp (bsimp r) s)  \<or> bders_simp (bsimp r) s = AZERO"
  apply(induct s arbitrary: r rule:  rev_induct)
   apply(simp)
  apply (simp add: good1)
  apply(simp add: bders_simp_append)
  apply (simp add: good1)
  done

lemma XXX4:
  assumes "good a"
  shows "bders_simp a s = bsimp (bders a s)"
  using  assms
  apply(induct s arbitrary: a rule: rev_induct)
   apply(simp)
   apply (simp add: test2)
  apply(simp add: bders_append bders_simp_append)
  oops


lemma MAINMAIN:
  "blexer r s = blexer_simp r s"
  apply(induct s arbitrary: r)
  apply(simp add: blexer_def blexer_simp_def)
  apply(simp add: blexer_def blexer_simp_def del: bders.simps bders_simp.simps)
  apply(auto simp del: bders.simps bders_simp.simps)
    prefer 2
  apply (metis b4 bders.simps(2) bders_simp.simps(2))
   prefer 2
  apply (metis b4 bders.simps(2))
  apply(subst bmkeps_simp)
   apply(simp)
  apply(case_tac s)
   apply(simp only: bders.simps)
   apply(subst bders_simp.simps)
  apply(simp)
  oops   


lemma
  fixes n :: nat
  shows "(\<Sum>i \<in> {0..n}. i) = n * (n + 1) div 2"
  apply(induct n)
  apply(simp)
  apply(simp)
  done





end