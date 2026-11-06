Theory bodyPtrPopFullFrameOutcome
Ancestors
  bodyPtrPopFullFrameExecution bodyPtrPopFullFrameGas bodyPtrDefs
  loweringPosts compileEnv ptrDiscipline vyperStorageBackend venomState
  fragGasPathPtr gasSummary
  bodyPtrPopFullFrameProbe exprLoweringProps bodyPtrPopFullFrameRuntime

Theorem pop_full_frame_end_ghost:
  ghost_inv NONE pop_full_frame_body_env pop_full_frame_cx
    ((set_storage pop_full_frame_cx pop_full_frame_es F
       ((0w =+ 0w) (K 0w))) with gas_obs := [])
    pop_full_frame_G
    (entry_taint with t_var := FEMPTY |+ ("%7",{}) |+ ("%8",{}) |+
      ("%9",{}) |+ ("%10",{}) |+ ("%11",{}) |+ ("%12",{}) |+ ("%13",{}))
    (pop_full_frame_end with vs_inst_idx := 11)
Proof
  simp[ghost_inv_def, pop_full_frame_vars, return_buf_ptr_def,
       pop_full_frame_return_buf, pop_full_frame_specials,
       op_taint_def, entry_taint_def, stor_taint_ok_def,
       set_storage_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem pop_full_frame_end_ptr_vv:
  ptr_vv_ok pop_full_frame_cx (expr_type pop_full_frame_expr)
    (PlaceR (StoragePlace F 1w (BaseTV (UintT 256))))
    (FST pop_full_frame_compiled)
    ((set_storage pop_full_frame_cx pop_full_frame_es F
       ((0w =+ 0w) (K 0w))) with gas_obs := [])
    pop_full_frame_G
    (entry_taint with t_var := FEMPTY |+ ("%7",{}) |+ ("%8",{}) |+
      ("%9",{}) |+ ("%10",{}) |+ ("%11",{}) |+ ("%12",{}) |+ ("%13",{}))
    (pop_full_frame_end with vs_inst_idx := 11)
Proof
  simp[pop_full_frame_compiled_value, ptr_vv_ok_def,
       op_taint_def, entry_taint_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem pop_full_frame_end_kept:
  ghost_kept pop_full_frame_body_env pop_full_frame_es pop_full_frame_start
    pop_full_frame_G entry_taint pop_full_frame_ss pop_full_frame_G
    (entry_taint with t_var := FEMPTY |+ ("%7",{}) |+ ("%8",{}) |+
      ("%9",{}) |+ ("%10",{}) |+ ("%11",{}) |+ ("%12",{}) |+ ("%13",{}))
Proof
  simp[ghost_kept_def, op_taint_def, entry_taint_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> rpt IF_CASES_TAC >> simp[]
QED

Theorem pop_full_frame_end_state_rel:
  stmt_state_rel pop_full_frame_context pop_full_frame_fn pop_full_frame_body_env
    pop_full_frame_cx
    ((set_storage pop_full_frame_cx pop_full_frame_es F
       ((0w =+ 0w) (K 0w))) with gas_obs := [])
    (pop_full_frame_end with vs_inst_idx := 11)
Proof
  `alloca_room pop_full_frame_context pop_full_frame_fn
     (pop_full_frame_end with vs_inst_idx := 11)` by
    (irule alloca_room_fields >> qexists `pop_full_frame_ss` >>
     simp[pop_full_frame_alloca_room, pop_full_frame_end_def]) >>
  `fmp_room pop_full_frame_context pop_full_frame_fn
     (pop_full_frame_end with vs_inst_idx := 11)` by
    (irule fmp_room_fields >> qexists `pop_full_frame_ss` >>
     simp[pop_full_frame_fmp_room, pop_full_frame_end_def]) >>
  simp[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def,
       pop_full_frame_vars, local_region_def,
       storage_rel_def, transient_rel_def, accounts_rel_def,
       immutables_rel_def, logs_rel_def,
       bodyPtrPopFullFrameRuntimeTheory.pop_full_frame_storage_vars_rel,
       bodyPtrPopFullFrameRuntimeTheory.pop_full_frame_transient_vars_rel,
       pop_full_frame_end_def, set_storage_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``pop_full_frame_context``, ``pop_full_frame_fn``,
     ``pop_full_frame_body_env``, ``storage_dead``]) >>
  simp[SF wordsLib.SIZES_ss, storage_agree_def,
       pop_full_frame_specials] >>
  simp[venomInstTheory.fn_insts_blocks_def, pop_full_frame_blocks,
       venomInstTheory.mk_inst_def] >> rpt strip_tac >> gvs[]
QED

Theorem pop_full_frame_end_vv_post:
  vv_post pop_full_frame_context pop_full_frame_fn pop_full_frame_body_env
    pop_full_frame_cx pop_full_frame_expr pop_full_frame_es pop_full_frame_start
    (SND pop_full_frame_compiled) pop_full_frame_ss
    ((set_storage pop_full_frame_cx pop_full_frame_es F
       ((0w =+ 0w) (K 0w))) with gas_obs := [])
    (PlaceR (StoragePlace F 1w (BaseTV (UintT 256))))
    (FST pop_full_frame_compiled) (pop_full_frame_end with vs_inst_idx := 11)
Proof
  simp[vv_post_def, pop_full_frame_end_state_rel,
       pop_full_frame_compiled_value, vv_holds_def, vv_at_def,
       pop_full_frame_execution_pc, pop_full_frame_expr_def,
       storage_holds_def, pop_full_frame_end_def, locals_kept_def,
       pop_full_frame_vars, local_region_def] >>
  reverse conj_tac
  >- (simp[lookup_var_def, pop_full_frame_ss_def, init_venom_state_def,
           finite_mapTheory.FLOOKUP_UPDATE] >>
      rpt strip_tac >> rpt IF_CASES_TAC >> gvs[]) >>
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, vyperValueTheory.type_slot_size_def] >>
  EVAL_TAC
QED

Theorem pop_full_frame_vv_outcome:
  gas_outcome_ptr (cx_dead pop_full_frame_cx) (cx_tops pop_full_frame_cx)
    (pop_full_frame_context, pop_full_frame_fn) PG
    (eval_expr pop_full_frame_cx pop_full_frame_expr)
    (pop_full_frame_es, pop_full_frame_ss, pop_full_frame_G, entry_taint)
    (\res ee G tn t. ?tv. res = INL tv /\
      vv_post pop_full_frame_context pop_full_frame_fn pop_full_frame_body_env
        pop_full_frame_cx pop_full_frame_expr pop_full_frame_es pop_full_frame_start
        (SND pop_full_frame_compiled) pop_full_frame_ss ee tv
        (FST pop_full_frame_compiled) t /\
      t.vs_current_bb = (SND pop_full_frame_compiled).cs_current_bb /\
      t.vs_inst_idx = LENGTH (SND pop_full_frame_compiled).cs_current_insts /\
      ghost_inv NONE pop_full_frame_body_env pop_full_frame_cx ee G tn t /\
      ptr_vv_ok pop_full_frame_cx (expr_type pop_full_frame_expr) tv
        (FST pop_full_frame_compiled) ee G tn t /\
      (!t' op. FST pop_full_frame_compiled = StackValue t' op /\
         ~is_word_type (expr_type pop_full_frame_expr) ==>
         ptr_buf_ok pop_full_frame_body_env pop_full_frame_expr op G t) /\
      (!t' p. FST pop_full_frame_compiled = LocatedValue t' p /\
         p.ptr_location = LocMemory ==>
         ptr_buf_ok pop_full_frame_body_env pop_full_frame_expr p.ptr_operand G t) /\
      ghost_kept pop_full_frame_body_env pop_full_frame_es pop_full_frame_start
        pop_full_frame_G entry_taint pop_full_frame_ss G tn)
    (\res ee gt r. expr_exit res r)
Proof
  rewrite_tac[gas_outcome_ptr_def] >> qexists `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl [
    `INL (PlaceR (StoragePlace F 1w (BaseTV (UintT 256))))`,
    `set_storage pop_full_frame_cx pop_full_frame_es F ((0w =+ 0w) (K 0w))`,
    `pop_full_frame_G`,
    `entry_taint with t_var := FEMPTY |+ ("%7",{}) |+ ("%8",{}) |+
      ("%9",{}) |+ ("%10",{}) |+ ("%11",{}) |+ ("%12",{}) |+ ("%13",{})`,
    `OK (pop_full_frame_end with vs_inst_idx := 11)`] >>
  simp[pop_full_frame_source_eval_gas, gas_explicit_def,
       pop_full_frame_execution] >>
  simp[pop_full_frame_end_vv_post, pop_full_frame_execution_pc,
       pop_full_frame_end_ghost, pop_full_frame_end_ptr_vv,
       pop_full_frame_end_kept, pop_full_frame_compiled_value] >>
  mp_tac pop_full_frame_execution_pc >> simp[]
QED
