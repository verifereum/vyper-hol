(* This tests an abstract child-post implication, NOT the frozen target.
   Empty bytes occupy different capacity windows; the second field moves.
   No new definitions are needed for this concrete memory witness. *)
Theory bodyPtrMakeArraySourceLayoutProbe
Ancestors
  bodyPtrDefs valueEncoding valueEncodingProps representationCleanPtr
  compileEnv vyperTypeSystem list valueEncodingProofs finite_map words

Theorem narrow_tuple_memory_probe:
  val_in_memory
    (TupleTV [BaseTV (BytesT (Dynamic 32)); BaseTV (UintT 256)])
    (ArrayV (TupleV [BytesV []; IntV 1])) 0
    (REPLICATE 95 (0w:word8) ++ [1w]) /\
  ~val_in_memory
    (TupleTV [BaseTV (BytesT (Dynamic 64)); BaseTV (UintT 256)])
    (ArrayV (TupleV [BytesV []; IntV 1])) 0
    (REPLICATE 95 (0w:word8) ++ [1w]) /\
  type_memory_size
    (TupleTV [BaseTV (BytesT (Dynamic 32)); BaseTV (UintT 256)]) = 96 /\
  type_memory_size
    (TupleTV [BaseTV (BytesT (Dynamic 64)); BaseTV (UintT 256)]) = 128
Proof
  EVAL_TAC >> simp[]
QED

Theorem empty_taint_window[local]:
  mem_agree_outside {} mem m ==>
  mem_bytes_at off len mem = mem_bytes_at off len m
Proof
  strip_tac >> irule LIST_EQ >>
  simp[valueEncodingPropsTheory.LENGTH_mem_bytes_at] >> rpt strip_tac >>
  `mem_bytes_at (off+x) 1 mem = mem_bytes_at (off+x) 1 m` by
    metis_tac[mem_agree_outside_def, pred_setTheory.NOT_IN_EMPTY] >>
  pop_assum (mp_tac o AP_TERM ``EL 0 : word8 list -> word8``) >>
  simp[valueEncodingProofsTheory.EL_mem_bytes_at]
QED

Theorem narrow_tuple_robust_probe:
  !m. mem_agree_outside {} (REPLICATE 95 (0w:word8) ++ [1w]) m ==>
  val_in_memory
    (TupleTV [BaseTV (BytesT (Dynamic 32)); BaseTV (UintT 256)])
    (ArrayV (TupleV [BytesV []; IntV 1])) 0 m
Proof
  rpt strip_tac >> irule val_in_memory_mem_agree >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  qexistsl_tac [`96`, `REPLICATE 95 (0w:word8) ++ [1w]`] >>
  simp[narrow_tuple_memory_probe, empty_taint_window] >>
  EVAL_TAC >> simp[]
QED

(* Full lowered capacity is independent of the displaced live field. *)
Theorem wide_tuple_coverage_probe:
  ptr_covers (FEMPTY |+ ("p",0,128)) entry_taint "p"
    (s with <| vs_vars := FEMPTY |+ ("p",0w);
               vs_memory := REPLICATE 95 (0w:word8) ++ [1w] |>) 128
Proof
  simp[finite_mapTheory.FLOOKUP_UPDATE, ptr_covers_def, ptrDisciplineTheory.op_taint_def,
       ptrDisciplineTheory.entry_taint_def, venomStateTheory.lookup_var_def]
QED

Theorem wide_tuple_not_robust_probe:
  ~(!m. mem_agree_outside {} (REPLICATE 95 (0w:word8) ++ [1w]) m ==>
    val_in_memory
      (TupleTV [BaseTV (BytesT (Dynamic 64)); BaseTV (UintT 256)])
      (ArrayV (TupleV [BytesV []; IntV 1])) 0 m)
Proof
  strip_tac >>
  first_x_assum (qspec_then `REPLICATE 95 (0w:word8) ++ [1w]` mp_tac) >>
  simp[mem_agree_outside_def, narrow_tuple_memory_probe]
QED
