(* Scalar tuple stores end in a store or in an open copy-loop exit. *)
Theory assignTupleStoreOpenPtr
Ancestors
  stmtLowering exprLowering context compileEnv exprOpenPrimitives exprOpenTerminals
  venomInst list option

Theorem tuple_assign_scalar_open:
  (loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient) /\
  ((prim /\ is_word_type dty) \/
   (~prim /\ is_bytestring_type dty /\ is_bytestring_type sty)) /\
  compile_assign_value cenv dst loc src prim NONE dty sty NONE sz sa = (z,sb) ==>
  ~block_is_terminated sb
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `prim`
  >- (Cases_on `loc` >>
      gvs[compile_assign_value_def,LET_THM,comp_bind_def,comp_return_def] >>
      drule emit_void_terminated >> simp[is_terminator_def]) >>
  Cases_on `is_word_type dty` >> Cases_on `loc` >>
  Cases_on `type_memory_bytes cenv sty <= 32` >>
  gvs[compile_assign_value_def,compile_store_memory_def,compile_store_bytestring_def,
      compile_memory_to_storage_def,compile_memory_to_transient_def,
      LET_THM,comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[emit_void_terminated,is_terminator_def,compile_word_copy_loop_open]
QED

Theorem tuple_store_scalar_at_loc_open:
  (loc = NONE \/ loc = SOME LocMemory \/ loc = SOME LocStorage \/
    loc = SOME LocTransient) /\
  compile_store_at_loc imm dst src loc sa = (z,sb) ==>
  ~block_is_terminated sb
Proof
  strip_tac >> gvs[compile_store_at_loc_def] >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem tuple_store_scalar_singleton_open:
  compile_get_target_ptr compile_expr cenv bt sa =
    ((dst,loc,SOME (ValPT dty)),sp) /\
  (loc = NONE \/ loc = SOME LocMemory \/ loc = SOME LocStorage \/
    loc = SOME LocTransient) /\
  (is_word_type sty <=> is_word_type dty) /\
  (~is_word_type sty ==> is_bytestring_type sty /\ is_bytestring_type dty) /\
  compile_tuple_store_all cenv [sty] [BaseTarget bt] [op] sa = ((),sf) ==>
  ~block_is_terminated sf
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_word_type sty`
  >- (qpat_x_assum `compile_tuple_store_all _ _ _ _ _ = _` mp_tac >>
      asm_simp_tac (srw_ss())
        [compile_tuple_store_all_def,comp_bind_def,comp_ignore_bind_def,
         comp_return_def,LET_THM] >>
      pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      metis_tac[tuple_store_scalar_at_loc_open]) >>
  qpat_x_assum `compile_tuple_store_all _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss())
    [compile_tuple_store_all_def,comp_bind_def,comp_ignore_bind_def,
     comp_return_def,LET_THM] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  Cases_on `dty` >> gvs[is_bytestring_type_def] >>
  drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)
    tuple_assign_scalar_open >> simp[]
QED
