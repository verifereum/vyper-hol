(* Raw value/place boundaries for the length builtin. *)
Theory bodyPtrEnvBuiltinsLen
Ancestors
  bodyPtrEnvBuiltinsBoundary bodyPtrEnvBuiltinsEdges typedCopyPtr
  exprSimLen vyperTyping vyperValue valueEncoding loweringPosts
  representationCleanPtr compileEnv bodyPtrDefs accountsRelProps
  vyperAST vyperTypeSystem builtinSimple ptrSafeRun ptrDiscipline
  venomExecSemantics venomInstProofs venomInst emitHelper fragGasSeqPtr fragGasPathPtr
  list memLocDefs codegenRel contextCodegenRel context

Theorem sized_val_footprint_header:
  is_sized_type ty /\ evaluate_type tenv ty = SOME tv ==>
  32 <= val_footprint tv v
Proof
  Cases_on `ty` >> simp[is_sized_type_def] >>
  rpt strip_tac
  >- (Cases_on `b` >> gvs[is_sized_type_def] >>
      TRY (Cases_on `b'` >> gvs[is_sized_type_def]) >>
      gvs[evaluate_type_def] >> Cases_on `v` >>
      simp[val_footprint_def, type_memory_size_def]) >>
  Cases_on `b` >> gvs[is_sized_type_def, evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >> simp[val_footprint_def, type_memory_size_def]
QED

Theorem sized_type_not_word:
  is_sized_type ty ==> ~is_word_type ty
Proof
  Cases_on `ty` >> gvs[is_sized_type_def, is_word_type_def] >>
  Cases_on `b` >> gvs[is_sized_type_def, is_word_type_def] >>
  Cases_on `b'` >> gvs[is_sized_type_def, is_word_type_def]
QED

Theorem sized_ptr_val_header_covers:
  ptr_val_ok cx ty v op G tn s /\ is_sized_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand op s = SOME w ==>
  ?p. op = Var p /\ ptr_covers G tn p s 32
Proof
  strip_tac >>
  `32 <= val_footprint tv v` by metis_tac[sized_val_footprint_header] >>
  `~is_word_type ty` by metis_tac[sized_type_not_word] >>
  `val_footprint tv v <> 0` by decide_tac >>
  drule_all ptr_val_ok_read_covers >> simp[]
QED

Theorem sized_ptr_mem_header_clean:
  ptr_mem_ok cx ty v op G tn s /\ is_sized_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  eval_operand op s = SOME w ==>
  !i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem
Proof
  strip_tac >>
  `val_in_memory tv v (w2n w) s.vs_memory` by
    (gvs[ptr_mem_ok_def] >> metis_tac[mem_agree_outside_def]) >>
  drule_all sized_memory_header >>
  disch_then (qspecl_then [`cx`, `es`] strip_assume_tac) >>
  `!mem. val_in_memory tv v (w2n w) mem ==>
         mem_word_at (w2n w) mem = n2w n` by
    (rpt strip_tac >> drule_all sized_memory_header >>
     disch_then (qspecl_then [`cx`, `es`] strip_assume_tac) >> gvs[]) >>
  metis_tac[ptr_mem_ok_header_clean]
QED

Theorem mload_counted_suffix:
  ptr_covers G tn src s 32 /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var src] [out]) /\
  eval_operand (Var src) s = SOME w ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id MLOAD [Var src] [out])
      (update_var out (mload (w2n w) s) s))
    (step_taint (mk_inst id MLOAD [Var src] [out]) s
      (update_var out (mload (w2n w) s) s) tn)
    (OK ((update_var out (mload (w2n w) s) s)
      with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn
    (mk_inst id MLOAD [Var src] [out]) s` by
    (irule ptr_inst_ok_mload >> simp[]) >>
  `step_inst_base (mk_inst id MLOAD [Var src] [out]) s =
    OK (update_var out (mload (w2n w) s) s)` by
    simp[step_inst_base_def, mk_inst_def, exec_read1_def] >>
  `~(update_var out (mload (w2n w) s) s).vs_halted` by
    simp[venomStateTheory.update_var_def] >>
  qmatch_goalsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t)` >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G' tn' (OK t)` by
    (unabbrev_all_tac >>
     drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
     simp[mk_inst_def, is_terminator_def] >> disch_then irule >>
     gvs[mk_inst_def]) >>
  drule (cj 2 gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >>
  simp[Once gas_path_ptr_cases, Abbr `t`, venomStateTheory.update_var_def]
QED

Theorem ptr_vv_slot_header_clean:
  ptr_vv_ok cx ty tv (LocatedValue t p) es G tn s /\
  evaluate_type (get_tenv cx) ty = SOME vty /\
  0 < type_slot_size vty /\ eval_operand p.ptr_operand s = SOME w ==>
  !b. b < 32 ==>
    (p.ptr_location = LocStorage ==> (w,b) NOTIN tn.t_stor) /\
    (p.ptr_location = LocTransient ==> (w,b) NOTIN tn.t_trans)
Proof
  strip_tac >> gvs[ptr_vv_ok_def] >> rpt strip_tac >>
  spose_not_then assume_tac >>
  first_x_assum (qspecl_then [`w`, `b`] mp_tac) >>
  simp[] >> strip_tac >>
  drule (cj 1 dead_bytes_range) >> simp[]
QED

Theorem ptr_inst_ok_nonmemory_load:
  MEM opc [SLOAD; TLOAD; DLOAD] /\ op_taint tn op = {} /\
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc [op] [out]) s
Proof
  strip_tac >> gvs[MEM] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_read1_def, venomStateTheory.update_var_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem nonmemory_load_output_clean:
  MEM opc [SLOAD; TLOAD; DLOAD] /\ eval_operand op s = SOME w /\
  (opc = SLOAD ==> !b. b < 32 ==> (w,b) NOTIN tn.t_stor) /\
  (opc = TLOAD ==> !b. b < 32 ==> (w,b) NOTIN tn.t_trans) ==>
  op_taint (step_taint (mk_inst id opc [op] [out]) s
    (update_var out v s) tn) (Var out) = {}
Proof
  strip_tac >>
  simp[op_taint_def, step_taint_def, mk_inst_def, set_var_taint_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  gvs[MEM, out_taint_def, mk_inst_def, key_taint_def,
      pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem ptr_vv_memory_length_header:
  ptr_vv_ok cx ty r vv es G tn s /\ is_sized_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  (!v. read_result cx r es = (INL v,es) ==> value_has_type tv v) /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  eval_operand (vv_operand vv) s = SOME w ==>
  (?p. vv_operand vv = Var p /\ ptr_covers G tn p s 32) /\
  (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem)
Proof
  strip_tac >>
  `~is_word_type ty` by metis_tac[sized_type_not_word] >>
  Cases_on `vv` >>
  gvs[ptr_vv_ok_def, vv_location_def, vv_operand_def, ptr_val_ok_def] >>
  metis_tac[sized_ptr_val_header_covers, sized_ptr_mem_header_clean,
            ptr_val_ok_def]
QED

Theorem nonmemory_load_counted_suffix:
  MEM opc [SLOAD; TLOAD; DLOAD] /\ op_taint tn op = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc [op] [out]) /\
  step_inst_base (mk_inst id opc [op] [out]) s = OK u ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id opc [op] [out]) u)
    (step_taint (mk_inst id opc [op] [out]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn
    (mk_inst id opc [op] [out]) s` by
    (irule ptr_inst_ok_nonmemory_load >> simp[]) >>
  `opc <> INVOKE /\ ~is_terminator opc /\ opc <> GAS` by
    (gvs[MEM] >> simp[is_terminator_def]) >>
  `step_inst 0 ctx (mk_inst id opc [op] [out]) s = OK u` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  `~u.vs_halted` by
    (drule_at (Pat `step_inst _ _ _ _ = _`) step_preserves_halted >>
     simp[mk_inst_def]) >>
  qmatch_goalsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t)` >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G' tn' (OK t)` by
    (unabbrev_all_tac >>
     drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
     simp[mk_inst_def] >> disch_then irule >> gvs[mk_inst_def]) >>
  drule (cj 2 gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >>
  simp[Once gas_path_ptr_cases, Abbr `t`]
QED
