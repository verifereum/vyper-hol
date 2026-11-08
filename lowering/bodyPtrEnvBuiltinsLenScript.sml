(* Raw value/place boundaries for the length builtin. *)
Theory bodyPtrEnvBuiltinsLen
Ancestors
  wordLoadStorePtr bodyPtrEnvBuiltinsBoundary bodyPtrEnvBuiltinsEdges typedCopyPtr
  exprSimLen vyperTyping vyperValue valueEncoding loweringPosts
  representationCleanPtr compileEnv bodyPtrDefs accountsRelProps
  vyperAST vyperTypeSystem builtinSimple ptrSafeRun ptrDiscipline
  venomExecSemantics venomInstProofs venomInst venomState emitHelper fragGasSeqPtr fragGasPathPtr
  list memLocDefs codegenRel contextCodegenRel context
  emitHelperProps exprLoweringProps fragExec bodyPtrEnvBuiltinsScalar stmtFragPtr
  builtinProps

Theorem sized_val_footprint_header:
  is_sized_type ty /\ evaluate_type tenv ty = SOME tv ==>
  32 <= val_footprint tv v
Proof
  Cases_on `ty` >> simp[is_sized_type_def] >>
  rpt strip_tac
  >- (Cases_on `b` >> gvs[is_sized_type_def]
      >~ [`evaluate_type tenv (BaseT (BytesT bd)) = SOME tv`]
      >- (Cases_on `bd` >> gvs[is_sized_type_def, evaluate_type_def] >>
          Cases_on `v` >> simp[val_footprint_def, type_memory_size_def]) >>
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

Theorem load_builtin_update_ghosts:
  MEM opc [MLOAD; SLOAD; TLOAD; DLOAD] /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  ghost_kept cenv es0 sa G0 tn0 s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  ~not_fresh_at sa out ==>
  ghost_inv d cenv cx es
    (step_prov PG G (mk_inst id opc [op] [out]) (update_var out w s))
    (step_taint (mk_inst id opc [op] [out]) s (update_var out w s) tn)
    (update_var out w s) /\
  ghost_kept cenv es0 sa G0 tn0 s0
    (step_prov PG G (mk_inst id opc [op] [out]) (update_var out w s))
    (step_taint (mk_inst id opc [op] [out]) s (update_var out w s) tn)
Proof
  strip_tac >>
  `(step_taint (mk_inst id opc [op] [out]) s (update_var out w s) tn).t_mem =
   tn.t_mem` by
    (irule step_taint_no_memory_effect >>
     gvs[MEM, source_memory_write_ranges_def, mk_inst_def,
         venomStateTheory.update_var_def, written_taint_def]) >>
  `opc <> CALL /\ opc <> ISTORE /\ opc <> SSTORE /\ opc <> TSTORE` by
    gvs[MEM] >>
  conj_tac
  >- (irule single_output_ghost_inv >>
      simp[venomStateTheory.update_var_def] >>
      qexists_tac `sa` >>
      simp[venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
           finite_mapTheory.FLOOKUP_UPDATE] >>
      rpt strip_tac >> IF_CASES_TAC >> gvs[]) >>
  irule single_output_ghost_kept >> simp[]
QED

Theorem emit_checked_load_suffix:
  emit_op opc [src] sa = (op, sb) /\ fn_has_code sa sb fn /\
  MEM opc [MLOAD; SLOAD; TLOAD; DLOAD] /\
  ptr_inst_ok D 0 0 ctx fn G tn
    (mk_inst sa.cs_next_id opc [src]
      [STRING #"%" (toString sa.cs_next_var)]) s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  step_inst_base (mk_inst sa.cs_next_id opc [src]
    [STRING #"%" (toString sa.cs_next_var)]) s = OK u ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id opc [src]
      [STRING #"%" (toString sa.cs_next_var)]) u)
    (step_taint (mk_inst sa.cs_next_id opc [src]
      [STRING #"%" (toString sa.cs_next_var)]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME
      (mk_inst sa.cs_next_id opc [src]
        [STRING #"%" (toString sa.cs_next_var)])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[] >> metis_tac[]) >>
  `opc <> INVOKE /\ ~is_terminator opc /\ opc <> GAS` by
    (gvs[MEM] >> simp[is_terminator_def]) >>
  `step_inst 0 ctx (mk_inst sa.cs_next_id opc [src]
    [STRING #"%" (toString sa.cs_next_var)]) s = OK u` by
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

Theorem emit_load_builtin_run:
  emit_op opc [src] sa = (op, sb) /\ fn_has_code sa sb fn /\
  MEM opc [MLOAD; SLOAD; TLOAD; DLOAD] /\
  ptr_inst_ok D 0 0 ctx fn G tn
    (mk_inst sa.cs_next_id opc [src]
      [STRING #"%" (toString sa.cs_next_var)]) s /\
  op_taint (step_taint
    (mk_inst sa.cs_next_id opc [src] [STRING #"%" (toString sa.cs_next_var)])
    s (update_var (STRING #"%" (toString sa.cs_next_var)) w s) tn)
    (Var (STRING #"%" (toString sa.cs_next_var))) = {} /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv ss /\
  ghost_inv d cenv cx es G tn s /\
  ghost_kept cenv es0 ss G0 tn0 s0 G tn /\
  ~not_fresh_at ss (STRING #"%" (toString sa.cs_next_var)) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at ss x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at ss x) /\
  stmt_state_rel ctx fn cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  step_inst_base (mk_inst sa.cs_next_id opc [src]
    [STRING #"%" (toString sa.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var)) w s) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    ghost_inv d cenv cx es G' tn' t /\
    ghost_kept cenv es0 ss G0 tn0 s0 G' tn' /\
    op_taint tn' op = {} /\ op_prov G' op = NONE /\
    eval_operand op t = SOME w /\
    stmt_state_rel ctx fn cenv cx es t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas
Proof
  strip_tac >>
  `~not_fresh_at sa (STRING #"%" (toString sa.cs_next_var))` by
    simp[not_fresh_at_def] >>
  drule_all emit_checked_load_suffix >>
  disch_then (qspec_then `PG` assume_tac) >>
  drule_all load_builtin_update_ghosts >>
  disch_then (qspecl_then [`w`, `src`, `sa.cs_next_id`, `PG`] strip_assume_tac) >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString sa.cs_next_var))` by
    (irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel ctx fn cenv cx es
    (update_var (STRING #"%" (toString sa.cs_next_var)) w s)` by
    (irule stmt_state_rel_update_var >> simp[]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  `op_prov (step_prov PG G
      (mk_inst sa.cs_next_id opc [src]
        [STRING #"%" (toString sa.cs_next_var)])
      (update_var (STRING #"%" (toString sa.cs_next_var)) w s))
      (Var (STRING #"%" (toString sa.cs_next_var))) = NONE` by
    (irule step_prov_out_none >> simp[mk_inst_def] >>
     irule out_prov_other_none >> gvs[MEM, mk_inst_def]) >>
  qpat_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  gvs[stmt_state_rel_inst_idx, update_var_def, eval_operand_def,
      lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> IF_CASES_TAC >> gvs[]
QED

Theorem length_load_instruction_properties:
  loc <> LocCalldata /\ op_taint tn src = {} /\
  eval_operand src s = SOME w /\ ~ctx_has_dalloca ctx /\
  (loc = LocMemory ==>
    (?p. src = Var p /\ ptr_covers G tn p s 32) /\
    (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem)) /\
  (loc = LocStorage ==> !b. b < 32 ==> (w,b) NOTIN tn.t_stor) /\
  (loc = LocTransient ==> !b. b < 32 ==> (w,b) NOTIN tn.t_trans) ==>
  ?opc.
    compile_builtin_len F imm src loc = emit_op opc [src] /\
    MEM opc [MLOAD; SLOAD; TLOAD; DLOAD] /\
    ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc [src] [out]) s /\
    step_inst_base (mk_inst id opc [src] [out]) s =
      OK (update_var out (ptr_load_val F loc w s) s) /\
    op_taint (step_taint (mk_inst id opc [src] [out]) s
      (update_var out (ptr_load_val F loc w s) s) tn) (Var out) = {}
Proof
  strip_tac >> Cases_on `loc` >> gvs[]
  >- (qexists_tac `MLOAD` >>
      simp[compile_builtin_len_def, compile_ptr_load_def, MEM, ptr_load_val_def,
           step_inst_base_def, mk_inst_def, exec_read1_def] >>
      conj_tac
      >- (irule (SRULE[mk_inst_def] ptr_inst_ok_mload) >> simp[]) >>
      irule (SRULE[mk_inst_def] (cj 1 mload_ghost_clean)) >> simp[])
  >- (qexists_tac `SLOAD` >>
      simp[compile_builtin_len_def, compile_ptr_load_def, MEM, ptr_load_val_def,
           step_inst_base_def, mk_inst_def, exec_read1_def] >>
      conj_tac
      >- (irule (SRULE[mk_inst_def] ptr_inst_ok_nonmemory_load) >> simp[]) >>
      irule (SRULE[mk_inst_def] nonmemory_load_output_clean) >>
      simp[] >> qexists_tac `w` >> simp[])
  >- (qexists_tac `TLOAD` >>
      simp[compile_builtin_len_def, compile_ptr_load_def, MEM, ptr_load_val_def,
           step_inst_base_def, mk_inst_def, exec_read1_def] >>
      conj_tac
      >- (irule (SRULE[mk_inst_def] ptr_inst_ok_nonmemory_load) >> simp[]) >>
      irule (SRULE[mk_inst_def] nonmemory_load_output_clean) >>
      simp[] >> qexists_tac `w` >> simp[]) >>
  qexists_tac `DLOAD` >>
  simp[compile_builtin_len_def, compile_ptr_load_def, compile_imm_load_word_def,
       MEM, ptr_load_val_def, step_inst_base_def, mk_inst_def, exec_read1_def] >>
  conj_tac
  >- (irule (SRULE[mk_inst_def] ptr_inst_ok_nonmemory_load) >> simp[]) >>
  irule (SRULE[mk_inst_def] nonmemory_load_output_clean) >>
  simp[] >> qexists_tac `w` >> simp[]
QED

Theorem sized_type_slot_header:
  is_sized_type ty /\ evaluate_type tenv ty = SOME tv ==>
  0 < type_slot_size tv
Proof
  Cases_on `ty` >> simp[is_sized_type_def] >> rpt strip_tac
  >- (Cases_on `b` >> gvs[is_sized_type_def]
      >~ [`evaluate_type tenv (BaseT (BytesT bd)) = SOME tv`]
      >- (Cases_on `bd` >> gvs[is_sized_type_def, evaluate_type_def,
                             type_slot_size_def]) >>
      gvs[evaluate_type_def, type_slot_size_def]) >>
  Cases_on `b` >> gvs[is_sized_type_def, evaluate_type_def,
                     type_slot_size_def, AllCaseEqs()]
QED

Theorem ptr_vv_length_slot_header_clean:
  ptr_vv_ok cx ty tv vv es G tn s /\ is_sized_type ty /\
  evaluate_type (get_tenv cx) ty = SOME vty /\
  eval_operand (vv_operand vv) s = SOME w ==>
  !b. b < 32 ==>
    (vv_location vv = SOME LocStorage ==> (w,b) NOTIN tn.t_stor) /\
    (vv_location vv = SOME LocTransient ==> (w,b) NOTIN tn.t_trans)
Proof
  strip_tac >>
  `0 < type_slot_size vty` by metis_tac[sized_type_slot_header] >>
  Cases_on `vv` >> gvs[vv_location_def, vv_operand_def] >>
  metis_tac[ptr_vv_slot_header_clean]
QED

Theorem ptr_vv_length_instruction_properties:
  ptr_vv_ok cx ty r vv es G tn s /\ is_sized_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  (!v. read_result cx r es = (INL v,es) ==> value_has_type tv v) /\
  loc = (case vv_location vv of SOME l => l | NONE => LocMemory) /\
  loc <> LocCalldata /\ eval_operand (vv_operand vv) s = SOME w /\
  ~ctx_has_dalloca ctx ==>
  ?opc.
    compile_builtin_len F imm (vv_operand vv) loc = emit_op opc [vv_operand vv] /\
    MEM opc [MLOAD; SLOAD; TLOAD; DLOAD] /\
    ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc [vv_operand vv] [out]) s /\
    step_inst_base (mk_inst id opc [vv_operand vv] [out]) s =
      OK (update_var out (ptr_load_val F loc w s) s) /\
    op_taint (step_taint (mk_inst id opc [vv_operand vv] [out]) s
      (update_var out (ptr_load_val F loc w s) s) tn) (Var out) = {}
Proof
  strip_tac >>
  `op_taint tn (vv_operand vv) = {}` by
    (Cases_on `vv` >> gvs[ptr_vv_ok_def, vv_operand_def, ptr_val_ok_def]) >>
  `loc = LocMemory ==>
    (?p. vv_operand vv = Var p /\ ptr_covers G tn p s 32) /\
    (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem)` by
    (strip_tac >>
     `vv_location vv = NONE \/ vv_location vv = SOME LocMemory` by
       (Cases_on `vv_location vv` >> gvs[]) >>
     metis_tac[ptr_vv_memory_length_header]) >>
  `!b. b < 32 ==>
    (loc = LocStorage ==> (w,b) NOTIN tn.t_stor) /\
    (loc = LocTransient ==> (w,b) NOTIN tn.t_trans)` by
    (Cases_on `vv_location vv` >> gvs[] >>
     metis_tac[ptr_vv_length_slot_header_clean]) >>
  irule length_load_instruction_properties >> simp[]
QED
