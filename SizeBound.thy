
theory SizeBound
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



lemma xxx_bder:
  assumes "good r"
  shows "L (erase r) \<noteq> {}"
  using assms
  apply(induct r rule: good.induct)
  apply(auto simp add: Sequ_def)
  done


lemma bders_AZERO:
  shows "bders AZERO s = AZERO"
  and   "bders_simp AZERO s = AZERO"
   apply (induct s)
     apply(auto)
  done







lemma LLLL:
  shows "L (erase a) =  L (erase (bsimp a))"
  and "L (erase a) = {flat v | v. \<Turnstile> v: (erase a)}"
  and "L (erase a) = {flat v | v. \<Turnstile> v: (erase (bsimp a))}"
  using L_bsimp_erase apply(blast)
  apply (simp add: L_flat_Prf)
  using L_bsimp_erase L_flat_Prf apply(auto)[1]
  done  
    




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


lemma bders_snoc:
  "bder c (bders a s) = bders a (s @ [c])"
  apply(simp add: bders_append)
  done



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
| "erase a1 = erase a2 \<Longrightarrow> AALTs bs (rsa@[a1]@rsb@[a2]@rsc) \<leadsto> AALTs bs (rsa@[a1]@rsb@rsc)"


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

lemma alts_simpalts: "\<And>bs1 rs. (\<And>x. x \<in> set rs \<Longrightarrow> x \<leadsto>* bsimp x) \<Longrightarrow> 
AALTs bs1 rs \<leadsto>* AALTs bs1 (map bsimp rs)"
  apply(subgoal_tac " rs s\<leadsto>*  (map bsimp rs)")
   prefer 2
  using trivialbsimpsrewrites apply auto[1]
  using srewrites_alt1 by auto

lemma alts_fltsalts: "\<And>bs1 rs. (\<And>x. x \<in> set rs \<Longrightarrow> x \<leadsto>* bsimp x) \<Longrightarrow> 
AALTs bs1 rs \<leadsto>* AALTs bs1 (flts (map bsimp rs))"
  by (meson alts_simpalts fltsrewrites real_trans)

lemma threelistsappend: "rsa@a#rsb = (rsa@[a])@rsb"
  apply auto
  done

fun distinctByAcc :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b set \<Rightarrow> 'b set"
  where
  "distinctByAcc [] f acc = acc"
| "distinctByAcc (x#xs) f acc = 
     (if (f x) \<in> acc then distinctByAcc xs f acc 
      else  (distinctByAcc xs f ({f x} \<union> acc)))"

(*distinctby is only going to add to the set acc*)
lemma dB_accmono: "distinctByAcc (a#rs) erase acc = distinctByAcc [] erase acc' \<Longrightarrow> acc \<subseteq> acc'"
  apply(induction rs arbitrary: acc acc')
  apply simp
   apply (simp add: subset_insertI)
  apply simp
  apply(case_tac "erase a \<in> acc")
  apply simp
   apply (smt (z3) insert_iff insert_is_Un insert_subset)
  apply simp
  by (smt (z3) insert_is_Un insert_subset sup_ge2)

lemma dB_acchas_elema: "erase a \<in> distinctByAcc (rsa@[a]@rsb) erase acc"
  apply(induction rsa arbitrary: rsb acc)
  apply(case_tac "erase a \<in> acc")
  apply simp
  
  apply (metis dB_accmono distinctByAcc.simps(1) distinctByAcc.simps(2) in_mono)
  
  apply (metis Un_insert_left append_Cons append_Nil dB_accmono distinctByAcc.simps(1) distinctByAcc.simps(2) insertI1 insert_subset)
  by simp

lemma dB_accequiv1: "distinctByAcc ((rs @ [a]) @ rsa) erase (insert (erase a) acc) = distinctByAcc ((rs @ [a]) @ rsa) erase acc"

  apply(induction rs arbitrary: rsa acc)
  apply (metis append_eq_Cons_conv distinctByAcc.simps(2) insertI1 insert_absorb insert_is_Un threelistsappend)
  by auto

lemma dB_accmono1: "  distinctByAcc rsa erase acc \<subseteq> distinctByAcc (rs@rsa) erase acc"
  apply(induction rsa arbitrary: rs acc)
  
   apply (metis dB_accmono distinctByAcc.simps(1) list.exhaust order_refl)
  apply(case_tac "erase a \<in> acc")
  apply simp

   apply (metis threelistsappend)
  apply simp
  apply(drule_tac x = "rs@[a]" in meta_spec)
  apply(drule_tac x = "insert (erase a) acc" in meta_spec)
  apply(subgoal_tac " distinctByAcc ((rs @ [a]) @ rsa) erase (insert (erase a) acc) \<subseteq> distinctByAcc (rs @ a # rsa) erase acc  ")
  apply blast
  using dB_accequiv1 by auto



lemma dB_eats_dupend : "erase a \<in> acc \<union> set (map erase rsa) \<Longrightarrow> distinctBy (rsa @ [a]) erase acc =  distinctBy rsa erase acc"
  apply(induction rsa arbitrary: acc)
   apply simp
  by force

lemma dB_keepsnew : " erase a \<notin> acc \<union> (erase `set rsa) \<Longrightarrow>  distinctBy (rsa @ [a]) erase acc = distinctBy rsa erase acc @ [a]"
  apply(induction rsa arbitrary: acc)
   apply simp
  apply simp
  done


lemma dB_compositionality: 
  shows "distinctBy (rsa@rsb) erase acc =(distinctBy rsa erase acc) @ (distinctBy rsb erase (acc \<union> set( map erase rsa)))"
  apply(induction rsb arbitrary: rsa acc)
   apply force
  apply(drule_tac x = "rsa@[a]" in meta_spec)
  apply(subst threelistsappend)
  apply(subgoal_tac " distinctBy (rsa @ [a]) erase acc @ distinctBy rsb erase (acc \<union> set (map erase (rsa @ [a]))) =
distinctBy rsa erase acc @ distinctBy (a # rsb) erase (acc \<union> set (map erase rsa))")
   apply presburger
  apply(case_tac "erase a \<in> acc \<union> set (map erase rsa)")
  apply simp
  apply simp
   apply (simp add: dB_eats_dupend insert_absorb)
  apply simp
  by (meson UnE dB_keepsnew)

lemma dB_single_step: "distinctBy (a#rs) f {} = a # distinctBy rs f {f a}"
  apply simp
  done

lemma somewhereInside: "r \<in> set rs \<Longrightarrow> \<exists>rs1 rs2. rs = rs1@[r]@rs2"
  using split_list by fastforce

lemma somewhereMapInside: "f r \<in> f ` set rs \<Longrightarrow> \<exists>rs1 rs2 a. rs = rs1@[a]@rs2 \<and> f a = f r"
  apply auto
  by (metis split_list)

lemma alts_dBrewrites_withFront: " AALTs bs (rsa @ rs) \<leadsto>* AALTs bs (rsa @ distinctBy rs erase (erase ` set rsa))"
  apply(induction rs arbitrary: rsa)
   apply simp
  apply(drule_tac x = "rsa@[a]" in meta_spec)
  apply(subst threelistsappend)
  apply(rule real_trans)
  apply simp
  apply(case_tac "a \<in> set rsa")
   apply simp
   apply(drule somewhereInside)
   apply(erule exE)+
   apply simp
  apply(subgoal_tac " AALTs bs
            (rs1 @
             a #
             rs2 @
             a #
             distinctBy rs erase
              (insert (erase a)
                (erase `
                 (set rs1 \<union> set rs2)))) \<leadsto> AALTs bs (rs1@ a # rs2 @  distinctBy rs erase
              (insert (erase a)
                (erase `
                 (set rs1 \<union> set rs2)))) ")
  prefer 2
  using rrewrite.intros(13) apply force
  using r_in_rstar apply force
  apply(subgoal_tac "erase ` set (rsa @ [a]) = insert (erase a) (erase ` set rsa)")
  prefer 2
    
   apply auto[1]
  apply(case_tac "erase a \<in> erase `set rsa")

   apply simp
  apply(subgoal_tac "AALTs bs (rsa @ a # distinctBy rs erase (insert (erase a) (erase ` set rsa))) \<leadsto>
                     AALTs bs (rsa @ distinctBy rs erase (insert (erase a) (erase ` set rsa)))")
  apply force
  apply (smt (verit, ccfv_threshold) append_Cons append_assoc append_self_conv2 r_in_rstar rrewrite.intros(13) same_append_eq somewhereMapInside)
  by force

 

lemma alts_dBrewrites: "AALTs bs rs \<leadsto>* AALTs bs (distinctBy rs erase {})"
  apply(induction rs)
   apply simp
  apply simp
  using alts_dBrewrites_withFront
  by (metis append_Nil dB_single_step empty_set image_empty)



  


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
  apply(subgoal_tac "AALTs bs1 (flts (map bsimp rs)) \<leadsto>* AALTs bs1 (distinctBy (flts (map bsimp rs)) erase {})")
    apply(subgoal_tac "AALTs bs1 (distinctBy (flts (map bsimp rs)) erase {}) \<leadsto>* bsimp_AALTs bs1 (distinctBy (flts (map bsimp rs)) erase {} )")

  
      apply (meson real_trans)

   apply (meson bsimp_AALTsrewrites)

  apply (meson alts_dBrewrites)

  using fltsrewrites apply auto[1]

  using alts_simpalts by force


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
  
   apply (metis bnullable_correctness erase.simps(5) erase_fuse)
  

  by (smt (z3) Un_iff bnullable_correctness insert_iff list.set(2) qq3 set_append)

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

  apply (metis bnullable_correctness erase_fuse)

  by (meson rewrite_non_nullable rrewrite.intros(13))

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

  apply (simp add: b2)
 
  by (smt (z3) Un_iff bnullable_correctness erase.simps(5) qq1 qq2 qq3 set_append)



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

  apply (metis fuse_append r_in_rstar rrewrite.intros(12))

  using rrewrite.intros(13) by auto

  

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

lemma erase_same_der_same:
  shows "erase a1 = erase a2 \<Longrightarrow> erase (bder c a1) = erase (bder c a2)"
  by simp

lemma lock_step_der_removal: 
  shows " erase a1 = erase a2 \<Longrightarrow> 
                                  bder c (AALTs bs (rsa @ [a1] @ rsb @ [a2] @ rsc)) \<leadsto>* 
                                  bder c (AALTs bs (rsa @ [a1] @ rsb @ rsc))"
  apply(simp)
  
  using rrewrite.intros(13) by auto

lemma rewrite_after_der: "r1 \<leadsto> r2 \<Longrightarrow> (bder c r1) \<leadsto>* (bder c r2)"
  apply(induction r1 r2 arbitrary: c rule: rrewrite.induct)
  
              apply (simp add: r_in_rstar rrewrite.intros(1))
  apply simp
  
  apply (meson contextrewrites1 r_in_rstar rrewrite.intros(11) rrewrite.intros(2) rrewrite0away rs2)
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

   apply (metis bder.simps(4) bder_bsimp_AALTs bsimp_AALTs.simps(2) bsimp_AALTsrewrites)

  
  using lock_step_der_removal by auto



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


unused_thms

end
