Theory runtimeSymSrcInternalFunction
Ancestors
  runtimeSymSrcModuleBodies runtimeSymSrcInterfaces runtimeSymSrcEmission
  moduleLowering compileEnv context emitHelper loweringShapeDefs
  list venomInst stackPlanTypes

Theorem runtime_sym_internal_return_env:
  runtime_sym_env ce /\
  (!op. rb = SOME op ==> ~is_label_operand op) /\ ~is_label_operand pc ==>
  runtime_sym_env
    (ce with <| ce_return_buf :=
      (case rb of NONE => ce.ce_return_buf | SOME op =>
         case ce.ce_return_buf of SOME (MemLoc off sz) => SOME (PtrVar op sz)
       | _ => ce.ce_return_buf);
       ce_return_pc := SOME (PtrVar pc 0) |>)
Proof
  strip_tac >> Cases_on `rb`
  >- (gvs[runtime_sym_env_def, runtime_sym_loc_def] >> metis_tac[]) >>
  Cases_on `ce.ce_return_buf`
  >- (gvs[runtime_sym_env_def, runtime_sym_loc_def] >> metis_tac[]) >>
  Cases_on `x'` >> gvs[runtime_sym_env_def, runtime_sym_loc_def] >> metis_tac[]
QED

Theorem runtime_sym_internal_body_env:
  runtime_sym_env ce /\ (!op. imm = SOME op ==> ~is_label_operand op) ==>
  runtime_sym_env (ce with <| ce_imm_alloca := imm; ce_alloca_locals := T |>)
Proof
  simp[runtime_sym_env_def] >> metis_tac[]
QED

Theorem runtime_sym_internal_suffix:
  ~is_label_operand pc ==>
  !s u s'. EVERY runtime_sym_inst (state_insts s) /\
  (do cs <- comp_get;
      (if block_is_terminated cs then return ()
       else do (if nr then compile_nonreentrant_unlock key trans view else return ());
               (case (ret : type option) of NONE => emit_inst RET [pc] []
                          | SOME _ => emit_inst INVALID [] []) od);
      return () od) s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> simp[comp_bind_def, comp_ignore_bind_def, comp_get_def] >>
  rpt gen_tac >> Cases_on `block_is_terminated s` >>
  simp[comp_return_def] >> strip_tac >> gvs[] >>
  Cases_on `nr` >> gvs[comp_return_def] >>
  Cases_on `ret` >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac runtime_sym_nonreentrant_unlock >>
  drule_at (Pat `emit_inst _ _ _ _ = _`) runtime_sym_emit_inst >>
  disch_then irule >> simp[] >> qexists `s.cs_next_id` >>
  irule runtime_sym_ordinary_inst >> simp[]
QED

Theorem runtime_sym_internal_return_param:
  !s rb s'. EVERY runtime_sym_inst (state_insts s) /\
  (if has_buf then do op <- emit_op PARAM [Lit 0w]; return (SOME op) od
   else return NONE) s = (rb,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\
  (!op. rb = SOME op ==> ~is_label_operand op)
Proof
  Cases_on `has_buf` >> simp[comp_return_def, comp_bind_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
  simp[is_label_operand_def]
QED

Theorem runtime_sym_internal_immutable_param:
  (!n s v s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_fixed_region_with_id n s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\
    ~is_label_operand (SND v).buf_operand) ==>
  !s imm s'. EVERY runtime_sym_inst (state_insts s) /\
  (if ctor /\ len > 0 then
     do ar <- compile_fixed_region_with_id len;
        return (SOME (SND ar).buf_operand) od
   else return NONE) s = (imm,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\
  (!op. imm = SOME op ==> ~is_label_operand op)
Proof
  strip_tac >> Cases_on `ctor /\ len > 0` >>
  simp[comp_return_def, comp_bind_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem runtime_sym_internal_temp_alloc:
  (!n s v s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_alloc_buffer n s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  !s u s'. EVERY runtime_sym_inst (state_insts s) /\
  (case ret of NONE => return () | SOME ty =>
    if ce.ce_returns_count > 0 then
      do unused <- compile_alloc_buffer (type_memory_bytes ce ty); return () od
    else return ()) s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> Cases_on `ret` >> simp[comp_return_def] >>
  Cases_on `ce.ce_returns_count > 0` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem runtime_sym_internal_lock:
  !s u s'. EVERY runtime_sym_inst (state_insts s) /\
  (if nr then compile_nonreentrant_lock key trans view else return ()) s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Cases_on `nr` >> simp[comp_return_def] >>
  metis_tac[runtime_sym_nonreentrant_lock]
QED

Theorem runtime_sym_internal_function:
  !ce tops bindings body ret params has_buf nr key trans view ctor len s u s'.
  runtime_sym_env ce /\ supported_stmts tops bindings body /\
  ~supported_stmts_expr_exists is_self_code body /\
  (!ce'. runtime_sym_stmts_contract tops bindings compile_stmts ce' NoLoop
     (case ret of SOME ty => ty | NONE => BaseT BoolT) body) /\
  (!n s v s'. EVERY runtime_sym_inst (state_insts s) /\
     compile_alloc_buffer n s = (v,s') ==>
     EVERY runtime_sym_inst (state_insts s')) /\
  (!n s v s'. EVERY runtime_sym_inst (state_insts s) /\
     compile_fixed_region_with_id n s = (v,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\
     ~is_label_operand (SND v).buf_operand) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_internal_function ce params has_buf nr key trans view ctor len
    body ret s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  rpt gen_tac >> simp[compile_internal_function_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule_all runtime_sym_internal_return_param >> strip_tac >>
  PairCases_on `params_result` >>
  drule_all runtime_sym_internal_param_decls >> strip_tac >>
  drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
  simp[is_label_operand_def] >> strip_tac >>
  drule_all runtime_sym_internal_immutable_param >> strip_tac >>
  qmatch_asmsub_abbrev_tac `materialize_internal_params ce1` >>
  `runtime_sym_env ce1` by
    (simp[Abbr `ce1`] >> irule runtime_sym_internal_return_env >> simp[]) >>
  fs[] >> drule_all runtime_sym_materialize_internal_params >> strip_tac >>
  drule_all runtime_sym_internal_temp_alloc >> strip_tac >>
  `runtime_sym_env (cenv2 with <| ce_imm_alloca := imm_opt; ce_alloca_locals := T |>)` by
    (irule runtime_sym_internal_body_env >> simp[]) >>
  drule_all runtime_sym_internal_lock >> strip_tac >>
  qpat_x_assum `!ce'. runtime_sym_stmts_contract _ _ _ ce' _ _ _`
    (qspec_then `cenv2 with <| ce_imm_alloca := imm_opt; ce_alloca_locals := T |>` mp_tac) >>
  simp[runtime_sym_stmts_contract_def, runtime_sym_loop_def] >>
  disch_then drule_all >> strip_tac >>
  drule runtime_sym_internal_suffix >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_get_def, comp_return_def] >>
  disch_then irule >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`key`, `nr`, `ret`, `trans`, `view`] >>
  fs[comp_get_def] >> pairarg_tac >> gvs[]
QED
