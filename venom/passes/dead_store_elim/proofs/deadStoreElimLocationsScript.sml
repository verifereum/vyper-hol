Theory deadStoreElimLocations
Ancestors
  deadStoreElimDefs memAliasProps memLocProps venomMemProps
  venomExecSemantics memLocDefs venomMemDefs finite_map
  basePtrDefs basePtrProps basePtrProofs venomState venomInst words

(* A concrete access is bounded by its abstract segment. Unknown sizes and
   offsets impose no numerical restriction, but an allocation identity still
   bounds the entire nonempty access. This includes partial CALL writes. *)
Definition dse_region_matches_def:
  dse_region_matches ml s addr len <=>
    (!n. ml.ml_size = SOME n ==> len <= n) /\
    (len <> 0 ==>
      case ml.ml_alloca of
        NONE => (!off. ml.ml_offset = SOME off ==> addr = off)
      | SOME (Allocation aid) =>
          ?base sz. FLOOKUP s.vs_allocas aid = SOME (base, sz) /\
            base <= addr /\ addr + len <= base + sz /\
            (!off. ml.ml_offset = SOME off ==> addr = base + off))
End

Theorem dse_region_matches_empty:
  dse_region_matches ml s addr 0
Proof
  simp[dse_region_matches_def]
QED

Theorem dse_region_matches_size:
  dse_region_matches ml s addr len /\ ml.ml_size = SOME n ==>
  len <= n
Proof
  simp[dse_region_matches_def]
QED

Theorem dse_region_matches_ml_empty:
  dse_region_matches ml_empty s a n <=> n = 0
Proof
  simp[dse_region_matches_def, ml_empty_def]
QED

Theorem dse_region_matches_undefined:
  dse_region_matches ml_undefined s a n
Proof
  simp[dse_region_matches_def, ml_undefined_def]
QED

Theorem dse_region_matches_nonalias:
  ~may_overlap ml1 ml2 /\ allocas_non_overlapping s /\
  dse_region_matches ml1 s a n /\ dse_region_matches ml2 s b m ==>
  regions_disjoint (a, n) (b, m)
Proof
  Cases_on `n = 0` >- simp[regions_disjoint_def] >>
  Cases_on `m = 0` >- simp[regions_disjoint_def] >>
  Cases_on `ml1.ml_alloca` >> Cases_on `ml2.ml_alloca` >>
  simp[dse_region_matches_def, may_overlap_def] >>
  rpt strip_tac >> gvs[]
  >- (Cases_on `ml1.ml_offset` >> Cases_on `ml2.ml_offset` >>
      Cases_on `ml1.ml_size` >> Cases_on `ml2.ml_size` >>
      gvs[regions_disjoint_def]) >>
  rename1 `ml1.ml_alloca = SOME al1` >>
  rename1 `ml2.ml_alloca = SOME al2` >>
  Cases_on `al1` >> Cases_on `al2` >> gvs[] >>
  rename1 `ml1.ml_alloca = SOME (Allocation aid1)` >>
  rename1 `ml2.ml_alloca = SOME (Allocation aid2)` >>
  Cases_on `aid1 = aid2` >> gvs[]
  >- (Cases_on `ml1.ml_offset` >> Cases_on `ml2.ml_offset` >>
      Cases_on `ml1.ml_size` >> Cases_on `ml2.ml_size` >>
      gvs[regions_disjoint_def]) >>
  fs[allocas_non_overlapping_def] >>
  first_x_assum drule_all >>
  simp[regions_disjoint_def] >> decide_tac
QED

Theorem bp_ptr_from_op_alloca_exists:
  bp_ptr_sound bp s /\
  bp_ptr_from_op bp op = SOME (Ptr (Allocation aid) off) /\
  IS_SOME (eval_operand op s) ==>
  ?base sz. FLOOKUP s.vs_allocas aid = SOME (base, sz)
Proof
  Cases_on `op` >> simp[bp_ptr_from_op_def, eval_operand_def] >>
  rpt strip_tac >>
  rename1 `bp_get_ptrs bp v` >>
  Cases_on `bp_get_ptrs bp v` >> gvs[] >>
  rename1 `h::t` >> Cases_on `t` >> gvs[] >>
  fs[bp_ptr_sound_def] >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[] >> strip_tac >>
  drule ptr_matches_var_alloca_exists >>
  Cases_on `FLOOKUP s.vs_allocas aid` >> simp[] >>
  rename1 `SOME pair` >> PairCases_on `pair` >> simp[]
QED

Theorem bp_segment_size_literal:
  (bp_segment_from_ops bp ops).ml_size = SOME n ==>
  ?w. ops.iao_size = SOME (Lit w) /\ n = w2n w
Proof
  Cases_on `ops.iao_size` >>
  simp[bp_segment_from_ops_def, ml_undefined_def] >>
  Cases_on `ops.iao_ofst` >> simp[ml_undefined_def]
  >> rpt CASE_TAC >> simp[]
QED

Theorem bp_segment_region_matches:
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s /\
  bp_access_ops sp inst ops /\
  eval_operand ops.iao_ofst s = SOME w /\
  ops.iao_max_size = SOME maxop /\ eval_operand maxop s = SOME bound /\
  len <= w2n bound /\
  (!sizeop. ops.iao_size = SOME sizeop ==>
     ?szword. eval_operand sizeop s = SOME szword /\ len <= w2n szword) ==>
  dse_region_matches (bp_segment_from_ops bp ops) s (w2n w) len
Proof
  rpt strip_tac >>
  Cases_on `len = 0` >- simp[dse_region_matches_empty] >>
  `bound <> 0w` by (strip_tac >> gvs[]) >>
  rewrite_tac[dse_region_matches_def] >> conj_tac
  >- (gen_tac >> strip_tac >> drule bp_segment_size_literal >>
      strip_tac >> gvs[eval_operand_def]) >>
  simp[] >> Cases_on `ops.iao_ofst` >>
  gvs[bp_segment_from_ops_def, eval_operand_def, ml_undefined_def]
  >> rename1 `ops.iao_ofst = Var v` >>
  Cases_on `bp_ptr_from_op bp (Var v)` >> simp[] >>
  rename1 `bp_ptr_from_op bp (Var v) = SOME ptr` >>
  Cases_on `ptr` >> rename1 `Ptr al off` >>
  Cases_on `al` >> simp[] >>
  rename1 `bp_ptr_from_op bp (Var v) = SOME (Ptr (Allocation aid) off)` >>
  `?base sz. FLOOKUP s.vs_allocas aid = SOME (base, sz)` by
    (irule bp_ptr_from_op_alloca_exists >>
     qexistsl_tac [`bp`, `off`, `Var v`] >> simp[eval_operand_def]) >>
  fs[bp_accesses_in_own_alloca_def] >>
  qpat_x_assum `!sp' ops' aid' off' base sz' w' size_op n. _`
    (qspecl_then [`sp`, `ops`] mp_tac) >>
  simp[eval_operand_def] >> decide_tac
QED

Theorem dse_region_matches_contains:
  completely_contains outer inner /\
  dse_region_matches outer s a n /\
  dse_region_matches inner s b m /\ outer.ml_size = SOME n ==>
  m = 0 \/ (a <= b /\ b + m <= a + n)
Proof
  Cases_on `m = 0` >- simp[] >>
  simp[completely_contains_def, dse_region_matches_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `outer.ml_offset` >> Cases_on `inner.ml_offset` >>
  Cases_on `inner.ml_size` >> gvs[] >>
  `n <> 0` by (strip_tac >> gvs[]) >>
  gvs[] >> Cases_on `inner.ml_alloca` >> gvs[] >>
  rename1 `inner.ml_alloca = SOME al` >>
  Cases_on `al` >> gvs[]
QED

(* A fixed abstract size is exact only when the size operand is evaluated
   as the actual overwrite length. In particular, a CALL maximum is not
   an exact size operand and cannot discharge this boundary. *)
Theorem bp_segment_size_eval:
  (bp_segment_from_ops bp ops).ml_size = SOME n /\
  ops.iao_size = SOME sizeop /\ eval_operand sizeop s = SOME w ==>
  n = w2n w
Proof
  rpt strip_tac >> drule bp_segment_size_literal >>
  strip_tac >> gvs[eval_operand_def]
QED

Theorem dse_region_matches_allocas_extend:
  dse_region_matches loc s a n /\
  (!aid p. FLOOKUP s.vs_allocas aid = SOME p ==>
           FLOOKUP t.vs_allocas aid = SOME p) ==>
  dse_region_matches loc t a n
Proof
  Cases_on `loc.ml_alloca` >> simp[dse_region_matches_def] >>
  rpt strip_tac >> rename1 `SOME alloc` >> Cases_on `alloc` >>
  gvs[] >> metis_tac[]
QED
