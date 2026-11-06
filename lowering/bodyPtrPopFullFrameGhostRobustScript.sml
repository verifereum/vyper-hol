Theory bodyPtrPopFullFrameGhostRobust
Ancestors
  bodyPtrPopFullFrameOutcome bodyPtrPopFullFrameExecution bodyPtrPopFullFrameSource
  bodyPtrPopFullFrameProbe bodyPtrPopFullFrameRuntime bodyPtrDefs compileEnv
  ptrDiscipline fragGasSeqPtr venomState vyperValue vyperStorageBackend
  bodyPtrPopFullFrameGas fragGasPathPtr gasSummary loweringPosts

Theorem pop_full_frame_live_keys:
  b < 32 /\ (j = 0 \/ j = 1) ==>
  ~storage_dead pop_full_frame_cx F pop_full_frame_storage j b
Proof
  simp[storage_dead_def, pop_full_frame_storage_regions] >>
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC >>
  rpt strip_tac >> gvs[]
QED

Theorem pop_full_frame_entry_storage_taint:
  ghost_inv NONE pop_full_frame_body_env pop_full_frame_cx pop_full_frame_es
    G tn pop_full_frame_ss /\ b < 32 /\ (k = 0w \/ k = 1w) ==>
  ~((k,b) IN tn.t_stor)
Proof
  `pop_full_frame_cx.txn.target = 0w` by EVAL_TAC >>
  simp[ghost_inv_def, stor_taint_ok_def, cx_dead_def,
       pop_full_frame_ss_def, init_venom_state_def,
       empty_call_context_def, pop_full_frame_es_def, set_storage_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``storage_dead``, ``pop_full_frame_cx``, ``pop_full_frame_body_env``,
     ``pop_full_frame_storage``]) >>
  rpt strip_tac >>
  qpat_x_assum `tn.t_stor SUBSET _`
    (mp_tac o Q.SPEC `(k,b)` o REWRITE_RULE [pred_setTheory.SUBSET_DEF]) >>
  simp[] >> metis_tac[pop_full_frame_live_keys]
QED

Theorem pop_full_frame_entry_key_taint:
  ghost_inv NONE pop_full_frame_body_env pop_full_frame_cx pop_full_frame_es
    G tn pop_full_frame_ss /\ (k = 0w \/ k = 1w) ==>
  key_taint tn.t_stor k = {}
Proof
  simp[key_taint_def, pred_setTheory.EXTENSION] >>
  metis_tac[pop_full_frame_entry_storage_taint]
QED

Theorem pop_full_frame_seq_ghost:
  ghost_inv NONE pop_full_frame_body_env pop_full_frame_cx pop_full_frame_es
    G tn pop_full_frame_ss ==>
  inst_seq_ptr (cx_dead pop_full_frame_cx) 0 pop_full_frame_context
    pop_full_frame_fn PG G tn pop_full_frame_code pop_full_frame_ss
    (DRESTRICT G (COMPL {"%7"; "%8"; "%9"; "%10"; "%11"; "%12"; "%13"}))
    (tn with <| t_var := tn.t_var |+ ("%7",{}) |+ ("%8",{}) |+
      ("%9",{}) |+ ("%10",{}) |+ ("%11",{}) |+ ("%12",{}) |+ ("%13",{});
      t_stor := key_update tn.t_stor 0w {} |>)
Proof
  strip_tac >>
  `pop_full_frame_cx.txn.target = 0w` by EVAL_TAC >>
  `key_taint tn.t_stor 0w = {}` by
    (irule pop_full_frame_entry_key_taint >> simp[] >> metis_tac[]) >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``ptrSafeRun$ptr_inst_ok``, ``pop_full_frame_context``, ``pop_full_frame_fn``,
     ``cx_dead``, ``pop_full_frame_cx``, ``key_taint``, ``key_update``, ``DRESTRICT``]) >>
  simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  simp_tac bool_ss [ptrSafeRunTheory.ptr_inst_ok_def,
    bodyPtrPopFullFrameEntryTheory.pop_full_frame_no_dalloca] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``cx_dead``, ``pop_full_frame_cx``, ``pop_full_frame_context``,
     ``pop_full_frame_fn``, ``key_taint``, ``key_update``, ``DRESTRICT``]) >>
  simp[finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_DRESTRICT] >>
  rpt conj_tac
  >~ [`DRESTRICT _ _ = DRESTRICT _ _`]
  >- (AP_TERM_TAC >> simp[pred_setTheory.EXTENSION] >> metis_tac[])
  >~ [`_ = <| t_mem := _; t_var := _; t_stor := _; t_trans := _; t_imm := _ |>`]
  >- simp[finite_mapTheory.DRESTRICT_UNIV, taint_component_equality] >>
  gen_tac >> Cases_on `op` >> simp[] >>
  rpt IF_CASES_TAC >> simp[]
QED

Theorem pop_full_frame_execution_ghost:
  ghost_inv NONE pop_full_frame_body_env pop_full_frame_cx pop_full_frame_es
    G tn pop_full_frame_ss ==>
  gas_path_ptr (cx_dead pop_full_frame_cx) 0 pop_full_frame_context
    pop_full_frame_fn PG G tn pop_full_frame_ss 0
    (DRESTRICT G (COMPL {"%7"; "%8"; "%9"; "%10"; "%11"; "%12"; "%13"}))
    (tn with <| t_var := tn.t_var |+ ("%7",{}) |+ ("%8",{}) |+
      ("%9",{}) |+ ("%10",{}) |+ ("%11",{}) |+ ("%12",{}) |+ ("%13",{});
      t_stor := key_update tn.t_stor 0w {} |>)
    (OK (pop_full_frame_end with vs_inst_idx := 11))
Proof
  strip_tac >>
  qspecl_then [`pop_full_frame_code`, `pop_full_frame_ss`,
                `pop_full_frame_end`]
    (irule o SRULE [pop_full_frame_run, pop_full_frame_code_counts])
    run_inst_seq_gas_path_ptr >>
  simp[bodyPtrPopFullFrameEntryTheory.pop_full_frame_pc,
       pop_full_frame_seq_ghost] >>
  simp[pop_full_frame_blocks, pop_full_frame_code_def,
       pop_full_frame_ss_def, init_venom_state_def,
       venomInstTheory.mk_inst_def] >> EVAL_TAC >> simp[]
QED

Theorem pop_full_frame_outputs_fresh:
  not_fresh_at pop_full_frame_start x ==>
  x NOTIN {"%7"; "%8"; "%9"; "%10"; "%11"; "%12"; "%13"}
Proof
  simp[not_fresh_at_def, pop_full_frame_start_def] >> strip_tac >>
  map_every (fn n => first_assum (qspec_then n mp_tac))
    [`7`, `8`, `9`, `10`, `11`, `12`, `13`] >>
  EVAL_TAC >> metis_tac[]
QED

Theorem pop_full_frame_ghost_kept:
  ghost_kept pop_full_frame_body_env pop_full_frame_es pop_full_frame_start
    G tn pop_full_frame_ss
    (DRESTRICT G (COMPL {"%7"; "%8"; "%9"; "%10"; "%11"; "%12"; "%13"}))
    (tn with <| t_var := tn.t_var |+ ("%7",{}) |+ ("%8",{}) |+
      ("%9",{}) |+ ("%10",{}) |+ ("%11",{}) |+ ("%12",{}) |+ ("%13",{});
      t_stor := key_update tn.t_stor 0w {} |>)
Proof
  simp[ghost_kept_def, op_taint_def, finite_mapTheory.FLOOKUP_DRESTRICT,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> drule pop_full_frame_outputs_fresh >> simp[]
QED

Theorem pop_full_frame_ghost_ptr_vv:
  ghost_inv NONE pop_full_frame_body_env pop_full_frame_cx pop_full_frame_es
    G tn pop_full_frame_ss ==>
  ptr_vv_ok pop_full_frame_cx (expr_type pop_full_frame_expr)
    (PlaceR (StoragePlace F 1w (BaseTV (UintT 256))))
    (FST pop_full_frame_compiled)
    ((set_storage pop_full_frame_cx pop_full_frame_es F
       ((0w =+ 0w) (K 0w))) with gas_obs := [])
    (DRESTRICT G (COMPL {"%7"; "%8"; "%9"; "%10"; "%11"; "%12"; "%13"}))
    (tn with <| t_var := tn.t_var |+ ("%7",{}) |+ ("%8",{}) |+
      ("%9",{}) |+ ("%10",{}) |+ ("%11",{}) |+ ("%12",{}) |+ ("%13",{});
      t_stor := key_update tn.t_stor 0w {} |>)
    (pop_full_frame_end with vs_inst_idx := 11)
Proof
  strip_tac >>
  simp[pop_full_frame_compiled_value, ptr_vv_ok_def, pop_full_frame_expr_def,
       op_taint_def, finite_mapTheory.FLOOKUP_UPDATE, key_update_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``pop_full_frame_cx``, ``dead_bytes``, ``evaluate_type``]) >>
  simp[evaluate_type_def, type_slot_size_def,
       SF wordsLib.SIZES_ss] >>
  rpt strip_tac >> gvs[] >>
  `w2n k = 1` by decide_tac >>
  `k = 1w` by metis_tac[wordsTheory.n2w_w2n] >>
  metis_tac[pop_full_frame_entry_storage_taint]
QED

Theorem pop_full_frame_dead_shorten:
  storage_dead pop_full_frame_cx tr pop_full_frame_storage j b ==>
  storage_dead pop_full_frame_cx tr ((0w =+ 0w) (K 0w)) j b
Proof
  simp[storage_dead_def, pop_full_frame_storage_regions] >>
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem pop_full_frame_ghost_inv_end:
  ghost_inv NONE pop_full_frame_body_env pop_full_frame_cx pop_full_frame_es
    G tn pop_full_frame_ss ==>
  ghost_inv NONE pop_full_frame_body_env pop_full_frame_cx
    ((set_storage pop_full_frame_cx pop_full_frame_es F
       ((0w =+ 0w) (K 0w))) with gas_obs := [])
    (DRESTRICT G (COMPL {"%7"; "%8"; "%9"; "%10"; "%11"; "%12"; "%13"}))
    (tn with <| t_var := tn.t_var |+ ("%7",{}) |+ ("%8",{}) |+
      ("%9",{}) |+ ("%10",{}) |+ ("%11",{}) |+ ("%12",{}) |+ ("%13",{});
      t_stor := key_update tn.t_stor 0w {} |>)
    (pop_full_frame_end with vs_inst_idx := 11)
Proof
  simp[ghost_inv_def, pop_full_frame_vars, return_buf_ptr_def,
       pop_full_frame_specials, set_storage_def, op_taint_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  `pop_full_frame_cx.txn.target = 0w` by EVAL_TAC >>
  simp[stor_taint_ok_def, cx_dead_def, pop_full_frame_end_def,
       pop_full_frame_ss_def, init_venom_state_def, empty_call_context_def,
       pop_full_frame_es_def, set_storage_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``storage_dead``, ``pop_full_frame_cx``, ``pop_full_frame_storage``]) >>
  simp[key_update_def, pred_setTheory.SUBSET_DEF] >>
  `(0w =+ 0w) pop_full_frame_storage = (0w =+ 0w) (K 0w)` by
    (simp[pop_full_frame_storage_def, combinTheory.UPDATE_EQ]) >>
  simp[] >> rpt strip_tac >> gvs[] >>
  metis_tac[pop_full_frame_dead_shorten, pairTheory.PAIR_EQ]
QED

Theorem pop_full_frame_vv_outcome_ghost:
  !PG G0 tn0.
  ghost_inv NONE pop_full_frame_body_env pop_full_frame_cx pop_full_frame_es
    G0 tn0 pop_full_frame_ss ==>
  gas_outcome_ptr (cx_dead pop_full_frame_cx) (cx_tops pop_full_frame_cx)
    (pop_full_frame_context, pop_full_frame_fn) PG
    (eval_expr pop_full_frame_cx pop_full_frame_expr)
    (pop_full_frame_es, pop_full_frame_ss, G0, tn0)
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
        G0 tn0 pop_full_frame_ss G tn)
    (\res ee gt r. expr_exit res r)
Proof
  rpt strip_tac >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl [
    `INL (PlaceR (StoragePlace F 1w (BaseTV (UintT 256))))`,
    `set_storage pop_full_frame_cx pop_full_frame_es F ((0w =+ 0w) (K 0w))`,
    `DRESTRICT G0 (COMPL {"%7"; "%8"; "%9"; "%10"; "%11"; "%12"; "%13"})`,
    `tn0 with <| t_var := tn0.t_var |+ ("%7",{}) |+ ("%8",{}) |+
      ("%9",{}) |+ ("%10",{}) |+ ("%11",{}) |+ ("%12",{}) |+ ("%13",{});
      t_stor := key_update tn0.t_stor 0w {} |>`,
    `OK (pop_full_frame_end with vs_inst_idx := 11)`] >>
  simp[pop_full_frame_source_eval_gas, gas_explicit_def,
       pop_full_frame_execution_ghost] >>
  simp[pop_full_frame_end_vv_post,
       pop_full_frame_ghost_inv_end, pop_full_frame_ghost_ptr_vv,
       pop_full_frame_ghost_kept, pop_full_frame_compiled_value] >>
  mp_tac pop_full_frame_execution_pc >> simp[]
QED
