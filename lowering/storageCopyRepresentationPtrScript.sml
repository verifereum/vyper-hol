(* Live bytes of a copied storage string exclude the exact copied tainted. *)
Theory storageCopyRepresentationPtr
Ancestors
  storageCopyCompiledPtr exprSimCopy exprSimProps bodyPtrDefs compileEnv loweringStateRelDefs
  valueEncoding valueEncodingProps valueEncodingProofs loweringPosts
  venomMemProofs pred_set arithmetic list vyperValue

Theorem storage_copy_string_taint_live_clean:
  len <= 32*(n-1) /\ 0 < n /\
  (!i r. i < n /\ r < 32 /\ P i r ==>
     0 < i /\ len <= 32*(i-1)+r) ==>
  !x. b <= x /\ x < b+32+len ==>
    x NOTIN ((M DIFF {y | b <= y /\ y < b+32*n}) UNION
      {b+32*i+r | i < n /\ r < 32 /\ P i r})
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  fs[] >> rpt strip_tac >>
  `i < n` by decide_tac >>
  spose_not_then strip_assume_tac >>
  first_x_assum drule_all >> strip_tac >> decide_tac
QED

Theorem storage_copy_string_robust_representation:
  val_wf (BaseTV (StringT max)) (StringV str) /\
  val_in_memory (BaseTV (StringT max)) (StringV str) b mem /\
  LENGTH str <= 32*(n-1) /\ 0 < n /\
  (!i r. i < n /\ r < 32 /\ P i r ==>
     0 < i /\ LENGTH str <= 32*(i-1)+r) /\
  tainted = (M DIFF {y | b <= y /\ y < b+32*n}) UNION
      {b+32*i+r | i < n /\ r < 32 /\ P i r} ==>
  !mem'. mem_agree_outside tainted mem mem' ==>
    val_in_memory (BaseTV (StringT max)) (StringV str) b mem'
Proof
  rpt gen_tac >> strip_tac >>
  `!x. b <= x /\ x < b+32+LENGTH str ==> x NOTIN tainted` by
    (qpat_x_assum `tainted = _` SUBST1_TAC >>
     gen_tac >> strip_tac >>
     irule storage_copy_string_taint_live_clean >>
     simp[] >> qexists_tac `LENGTH str` >> simp[] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  rpt strip_tac >> irule val_in_memory_footprint_agree >>
  simp[] >> qexists_tac `mem` >> simp[val_footprint_def] >>
  irule listTheory.LIST_EQ >> simp[] >> rpt strip_tac >>
  `b+x NOTIN tainted` by (first_x_assum irule >> decide_tac) >>
  `mem_bytes_at (b+x) 1 mem = mem_bytes_at (b+x) 1 mem'` by
    metis_tac[mem_agree_outside_def] >>
  pop_assum mp_tac >> simp[LIST_EQ_REWRITE, EL_mem_bytes_at]
QED

Theorem storage_copy_string_dead_bytes_live_bound:
  (!k r. w2n a <= w2n k /\ w2n k < w2n a+n /\ r < 32 /\
     (k,r) IN X ==> dead_bytes st (w2n a) (BaseTV (StringT max)) (w2n k) r) ==>
  w2n a+n <= dimword(:256) ==>
  w2n (lookup_storage a st) = len ==>
  !i r. i < n /\ r < 32 /\ (a+n2w i,r) IN X ==>
    0 < i /\ len <= 32*(i-1)+r
Proof
  rpt gen_tac >> disch_tac >> disch_tac >> disch_tac >>
  rpt gen_tac >> strip_tac >>
  `i < dimword(:256) /\ w2n a+i < dimword(:256)` by decide_tac >>
  `w2n (a+n2w i) = w2n a+i` by
    simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w] >>
  `dead_bytes st (w2n a) (BaseTV (StringT max)) (w2n (a+n2w i)) r` by
    (first_x_assum irule >> simp[]) >>
  fs[dead_bytes_def, dyn_bytes_dead_def] >>
  gvs[] >> decide_tac
QED


Theorem copied_storage_string_robust_memory:
  val_wf (BaseTV (StringT max)) (StringV str) /\
  val_in_memory (BaseTV (StringT max)) (StringV str) b mem /\
  LENGTH str <= 32*(n-1) /\ 0 < n /\
  (!k r. w2n a <= w2n k /\ w2n k < w2n a+n /\ r < 32 /\
     (k,r) IN X ==> dead_bytes st (w2n a) (BaseTV (StringT max)) (w2n k) r) /\
  w2n a+n <= dimword(:256) /\ w2n (lookup_storage a st) = LENGTH str /\
  tainted = (M DIFF {y | b <= y /\ y < b+32*n}) UNION
      {b+32*i+r | i < n /\ r < 32 /\ (a+n2w i,r) IN X} ==>
  !mem'. mem_agree_outside tainted mem mem' ==>
    val_in_memory (BaseTV (StringT max)) (StringV str) b mem'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule storage_copy_string_dead_bytes_live_bound >>
  disch_then drule >> disch_then drule >> strip_tac >>
  rpt strip_tac >>
  irule (Q.INST [`P` |-> `\i r. ((a:256 word)+n2w i,r) IN X`]
    storage_copy_string_robust_representation) >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`M`, `X`, `a`, `mem`] >>
  simp[] >> reverse conj_tac
  >- (qpat_x_assum `tainted = _` (fn th =>
        qpat_x_assum `mem_agree_outside tainted _ _` mp_tac >>
        pure_rewrite_tac[th]) >>
      pure_rewrite_tac[GSYM arithmeticTheory.ADD_ASSOC] >> simp[]) >>
  rpt strip_tac >> first_x_assum drule_all >> simp[]
QED
