(* Joint paths for the transient guard emitted at external body entry. *)
Theory nonreentrantEntryPath
Ancestors
  nonreentrantEntryEquiv transientLockProps fragGasSeqPtr fragGasEmitCtrl
  fragGasOriginPtr fragGasOrigin fragGasPathPtr fragExecMem fragExec
  ptrSafeRun ptrDiscipline gasCount gasEvents memSafeRun instMemFrontier
  codegenRel contextCodegenRel exprLoweringProps emitHelperProps
  venomExecSemantics venomExecProofs venomInst venomState list rich_list
  fragGasSeqAbort venomInstProofs instIdxIndep
  bodyPtrDefs vyperState finite_map pred_set loweringHalt stmtAppendStorageRunPtr
  unitTransformDefs

(* Acquiring or releasing a separated guard leaves every local pointer and
   every live storage observation covered by the same ghost invariant. *)
Theorem nonreentrant_ghost_inv_frame:
  storage_locks_separated (FST H) (SND H) /\
  MEM nkey (SND H) /\ nkey < dimword (:256) /\
  ghost_inv H d cenv cx es G tn ss /\ es'.scopes = es.scopes ==>
  ghost_inv H d cenv cx es' G tn (tstore (n2w nkey) value ss)
Proof
  strip_tac >>
  `stor_taint_ok H cx tn ss` by fs[ghost_inv_def] >>
  `stor_taint_ok H cx tn (tstore (n2w nkey) value ss)` by
    (irule nonreentrant_stor_taint_frame >> simp[]) >>
  Cases_on `d` >> TRY (rename1 `SOME rb` >> PairCases_on `rb`) >>
  fs[ghost_inv_def, return_buf_ptr_def, ptr_covers_def, lookup_var_def,
     tstore_def] >> rpt strip_tac >>
  qpat_x_assum `!name entry p sz. _`
    (qspecl_then [`name`, `entry`, `p`, `sz`] mp_tac) >> simp[] >> gvs[]
QED

Theorem key_update_empty_same[local]:
  (!b. ~((key,b) IN X)) ==> key_update X key {} = X
Proof
  strip_tac >>
  simp[key_update_def, EXTENSION] >>
  qx_gen_tac `p` >> PairCases_on `p` >> simp[] >> metis_tac[]
QED

(* A clean literal store keeps the entire ghost, on success and static abort. *)
Theorem literal_tstore_clean_inst_seq_ptr[local]:
  ~ctx_has_dalloca ctx /\ (!b. ~((key,b) IN tn.t_trans)) ==>
  inst_seq_ptr D 0 ctx func PG G tn
    [mk_inst id TSTORE [Lit key; Lit value] []] ss G tn
Proof
  strip_tac >>
  `step_inst_base (mk_inst id TSTORE [Lit key; Lit value] []) ss =
    if ss.vs_call_ctx.cc_static then
      Abort ExHalt_abort (halt_state (set_returndata [] ss))
    else OK (tstore key value ss)` by
    (irule loweringHaltTheory.step_TSTORE >> simp[eval_operand_def]) >>
  `step_taint (mk_inst id TSTORE [Lit key; Lit value] []) ss
     (tstore key value ss) tn = tn` by
    (mp_tac (Q.INST [`tr` |-> `T`, `a` |-> `Lit key`,
       `v` |-> `Lit value`, `slot` |-> `key`, `s` |-> `ss`,
       `s'` |-> `tstore key value ss`]
       (SPEC_ALL scalar_storage_store_taint)) >>
     simp[eval_operand_def, op_taint_def, tstore_def, key_update_empty_same]) >>
  simp[inst_seq_ptr_def, literal_tstore_ptr_inst_ok] >>
  Cases_on `ss.vs_call_ctx.cc_static` >> simp[scalar_void_prov, inst_seq_ptr_def]
QED

(* An abort stops before the unexecuted suffix, with the ghost at that point. *)
Theorem run_inst_seq_no_gas_abort_origin_ptr[local]:
  !code s t a G tn G' tn' ctx func bb.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> GAS) code /\
    run_inst_seq_mem_ok code s /\
    inst_seq_ptr D lo ctx func PG G tn code s G' tn' /\
    run_inst_seq code s = Abort a t ==>
    ?j. gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s, G, tn) []
          (Abort a (t with vs_inst_idx := j), G', tn')
Proof
  Induct >- simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[run_inst_seq_def, inst_seq_ptr_def, run_inst_seq_mem_ok_def]
  >~ [`step_inst_base h s = OK u`]
  >- (`step_inst 0 ctx h s = OK u` by simp[step_inst_non_invoke] >>
      `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
        metis_tac[step_preserves_halted, step_preserves_control_flow] >>
      `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
      first_x_assum (qspecl_then [`u with vs_inst_idx := SUC s.vs_inst_idx`,
        `t with vs_inst_idx := SUC s.vs_inst_idx`, `a`, `step_prov PG G h u`,
        `step_taint h s u tn`, `G'`, `tn'`, `ctx`, `func`, `bb`] mp_tac) >>
      simp[run_inst_seq_inst_idx, exec_result_map_def] >> strip_tac >>
      `gas_origin_ptr_edge (D, lo, explicit, ctx, func, PG) (s, G, tn) []
        (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
         step_prov PG G h u, step_taint h s u tn)` by
        (mp_tac (Q.INST [`i` |-> `h`]
           (SPEC_ALL straight_line_origin_ptr_edge)) >> simp[]) >>
      qexists_tac `j` >>
      drule (cj 2 gas_origin_ptr_path_rules) >> disch_then drule >> simp[]) >>
  qexists_tac `t.vs_inst_idx` >> simp[] >>
  irule (Q.INST [`bb` |-> `bb`, `i` |-> `h`]
    (SPEC_ALL exit_inst_origin_ptr)) >>
  simp[step_inst_non_invoke, exit_result_def, mem_safe_step_non_invoke,
       gas_events_step_def, gas_count_step_def]
QED

Theorem transient_lock_code_memory_checks[local]:
  !code s.
    EVERY (\i. MEM i.inst_opcode [TLOAD; EQ; ISZERO; ASSERT; TSTORE]) code ==>
    run_inst_seq_mem_ok code s
Proof
  Induct >- simp[run_inst_seq_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `inst_mem_below_frontier h s /\ inst_dload_in_section h s` by
    (gvs[MEM] >>
     simp[inst_mem_below_frontier_def, inst_dload_in_section_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  simp[run_inst_seq_mem_ok_def] >>
  Cases_on `step_inst_base h s` >> simp[] >> fs[]
QED

Theorem transient_lock_code_origin_ptr:
  ~ctx_has_dalloca ctx /\ key_taint tn.t_trans (n2w nkey) = {} /\
  ~ss.vs_halted /\
  lookup_block ss.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (transient_lock_code nkey iv st)
    (DROP ss.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (transient_lock_code nkey iv st) ss = OK ss' ==>
  ?G' tn'.
    gas_origin_ptr_path (D, 0, explicit, ctx, func, PG) (ss, G, tn) []
      (OK (ss' with vs_inst_idx :=
        ss.vs_inst_idx + LENGTH (transient_lock_code nkey iv st)), G', tn')
Proof
  strip_tac >>
  `?G' tn'. inst_seq_ptr D 0 ctx func PG G tn
    (transient_lock_code nkey iv st) ss G' tn'` by
    (irule transient_lock_code_ptr >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (transient_lock_code nkey iv st)` by
    (Cases_on `iv` >> simp[transient_lock_code_def, mk_inst_def,
                           is_terminator_def]) >>
  `run_inst_seq_mem_ok (transient_lock_code nkey iv st) ss` by
    (irule transient_lock_code_memory_checks >>
     Cases_on `iv` >> simp[transient_lock_code_def, mk_inst_def]) >>
  qexistsl_tac [`G'`, `tn'`] >>
  mp_tac (Q.INST [`code` |-> `transient_lock_code nkey iv st`,
                  `s` |-> `ss`, `t` |-> `ss'`, `lo` |-> `0:num`]
    (SPEC_ALL run_inst_seq_gas_origin_ptr_path)) >>
  simp[] >> Cases_on `iv` >> simp[transient_lock_code_def, mk_inst_def]
QED

Theorem transient_lock_code_abort_origin_ptr:
  ~ctx_has_dalloca ctx /\ key_taint tn.t_trans (n2w nkey) = {} /\
  ~ss.vs_halted /\
  lookup_block ss.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (transient_lock_code nkey iv st)
    (DROP ss.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (transient_lock_code nkey iv st) ss = Abort a ss' ==>
  ?G' tn' j.
    gas_origin_ptr_path (D, 0, explicit, ctx, func, PG) (ss, G, tn) []
      (Abort a (ss' with vs_inst_idx := j), G', tn')
Proof
  strip_tac >>
  `?G' tn'. inst_seq_ptr D 0 ctx func PG G tn
    (transient_lock_code nkey iv st) ss G' tn'` by
    (irule transient_lock_code_ptr >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> GAS) (transient_lock_code nkey iv st)` by
    (Cases_on `iv` >> simp[transient_lock_code_def, mk_inst_def,
                           is_terminator_def]) >>
  `run_inst_seq_mem_ok (transient_lock_code nkey iv st) ss` by
    (irule transient_lock_code_memory_checks >>
     Cases_on `iv` >> simp[transient_lock_code_def, mk_inst_def]) >>
  qexistsl_tac [`G'`, `tn'`] >>
  irule (Q.INST [`code` |-> `transient_lock_code nkey iv st`, `bb` |-> `bb`]
    (SPEC_ALL run_inst_seq_no_gas_abort_origin_ptr)) >> simp[] >>
  qexistsl_tac [`iv`, `nkey`, `st`] >> simp[]
QED
