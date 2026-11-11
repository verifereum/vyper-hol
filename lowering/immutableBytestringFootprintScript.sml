(* Runtime-sized meaningful transfers for constructor bytestring assignments. *)
Theory immutableBytestringFootprint
Ancestors
  immutableDeployMeaningfulTransfer immutableDeployAssignTransfer
  bytestringCopyExecution placeStoreStorage loweringPosts valueTypingMemoryProps
  exprSimHyps venomMemProps compileEnv vyperValue immutableCopyExecution

Theorem immutable_bytestring_runtime_extent:
  is_bytestring_type sty /\ is_bytestring_type dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  val_in_memory stv v a s.vs_memory ==>
  ?len. mload a s = n2w len /\
    val_footprint stv v = 32 + len /\
    val_footprint dtv v = 32 + len /\
    32 + len <= 32 * (1 + word_size len) /\
    32 * (1 + word_size len) <= type_memory_size stv /\
    32 * (1 + word_size len) <= type_memory_size dtv
Proof
  strip_tac >>
  Cases_on `sty` >> gvs[is_bytestring_type_def] >>
  rename1 `BaseT bs` >> Cases_on `bs` >> gvs[is_bytestring_type_def] >>
  Cases_on `dty` >> gvs[is_bytestring_type_def] >>
  rename1 `BaseT bd` >> Cases_on `bd` >> gvs[is_bytestring_type_def] >>
  gvs[evaluate_type_def, AllCaseEqs(), is_bytestring_type_def] >> Cases_on `v` >>
  gvs[vyperTypingTheory.value_has_type_def,
      valueEncodingDefsTheory.val_in_memory_def, val_footprint_def,
      valueEncodingTheory.type_memory_size_def] >>
  simp[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  qmatch_goalsub_abbrev_tac `word_size len` >>
  imp_res_tac word_size_monotone >>
  mp_tac (Q.SPEC `len` word_size_capacity) >>
  simp[Abbr `len`] >> decide_tac
QED

Theorem immutable_transfers_memory_nondecreasing:
  !n off s. LENGTH s.vs_memory <=
    LENGTH (immutable_transfers store ctor a b n off s).vs_memory
Proof
  Induct >- simp[immutable_transfers_def] >> rpt gen_tac >>
  simp[immutable_transfers_def] >>
  irule arithmeticTheory.LESS_EQ_TRANS >>
  qexists `LENGTH (immutable_word_transfer store ctor a b off s).vs_memory` >>
  simp[immutable_word_transfer_fields, mstore_memory_nondecreasing]
QED

Theorem immutable_bytestring_runtime_transfer:
  is_bytestring_type sty /\ is_bytestring_type dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  val_in_memory stv v a s.vs_memory /\
  a + val_footprint stv v < dimword (:256) /\
  b + type_memory_size dtv < dimword (:256) /\
  (a + val_footprint stv v <= b \/ b + type_memory_size dtv <= a) ==>
  ?len. mload a s = n2w len /\ len + 63 < dimword (:256) /\
    val_footprint stv v <= 32 * (1 + word_size len) /\
    32 * (1 + word_size len) <= type_memory_size stv /\
    32 * (1 + word_size len) <= type_memory_size dtv /\
    val_in_memory dtv v b
      (immutable_transfers T T (n2w a) (n2w b) (1 + word_size len) 0 s).vs_memory /\
    immutable_value_bytes_rel dtv v
      (mem_bytes_at b (type_memory_size dtv)
        (immutable_transfers T T (n2w a) (n2w b) (1 + word_size len) 0 s).vs_memory) /\
    (!p k. p+k <= b \/ b+type_memory_size dtv <= p ==>
      mem_bytes_at p k
        (immutable_transfers T T (n2w a) (n2w b) (1 + word_size len) 0 s).vs_memory =
      mem_bytes_at p k s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH
      (immutable_transfers T T (n2w a) (n2w b) (1 + word_size len) 0 s).vs_memory
Proof
  strip_tac >> drule_all immutable_bytestring_runtime_extent >> strip_tac >>
  `b + 32 * (1 + word_size len) < dimword (:256)` by decide_tac >>
  `len + 63 < dimword (:256)` by
    (irule bytestring_word_count_no_wrap >> decide_tac) >>
  `mem_bytes_at b (val_footprint stv v)
     (immutable_transfers T T (n2w a) (n2w b) (1 + word_size len) 0 s).vs_memory =
   mem_bytes_at a (val_footprint stv v) s.vs_memory` by
    (irule immutable_transfers_memory_prefix >> simp[] >> decide_tac) >>
  qmatch_asmsub_abbrev_tac `mem_bytes_at b (val_footprint stv v) t.vs_memory` >>
  `val_in_memory dtv v b t.vs_memory /\
   immutable_value_bytes_rel dtv v (mem_bytes_at b (type_memory_size dtv) t.vs_memory)` by
    (irule immutable_direct_meaningful_transfer >> simp[] >>
     qexistsl [`dty`, `s.vs_memory`, `val_footprint stv v`] >>
     simp[] >> metis_tac[arithmeticTheory.ADD_SYM, arithmeticTheory.LESS_EQ_REFL]) >>
  qexists `len` >>
  simp[GSYM markerTheory.Abbrev_def, immutable_transfers_memory_nondecreasing] >>
  rpt strip_tac >> simp[Abbr `t`] >>
  irule immutable_transfers_memory_frame >> simp[] >> decide_tac
QED
