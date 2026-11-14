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
  unitTransformDefs loweringStateRelDefs instSeqComposePtr exprSimPtrProps e2eDefs nonreentrantSource
  vyperScopePreservation context emitHelper compileEnv

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
Theorem literal_tstore_clean_inst_seq_ptr:
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

Theorem transient_lock_code_ptr_from_check[local]:
  ~ctx_has_dalloca ctx /\
  (!b. ~((n2w nkey,b) IN tn'.t_trans)) /\
  inst_seq_ptr D 0 ctx func PG G tn
    (transient_lock_code nkey T st) ss G' tn' ==>
  inst_seq_ptr D 0 ctx func PG G tn
    (transient_lock_code nkey iv st) ss G' tn'
Proof
  strip_tac >> Cases_on `iv` >- simp[] >>
  `transient_lock_code nkey F st = transient_lock_code nkey T st ++
     [mk_inst (st.cs_next_id + 4) TSTORE [Lit (n2w nkey); Lit 1w] []]` by
    simp[transient_lock_code_def] >>
  asm_rewrite_tac[] >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
     (transient_lock_code nkey T st)` by
    simp[transient_lock_code_def, mk_inst_def, is_terminator_def] >>
  `run_inst_seq (transient_lock_code nkey T st) ss =
     if tload (n2w nkey) ss = 1w then
       Abort Revert_abort (revert_state (set_returndata []
         (transient_lock_checked_state st nkey ss)))
     else OK (transient_lock_checked_state st nkey ss)` by
    simp[transient_lock_code_execution] >>
  Cases_on `tload (n2w nkey) ss = 1w`
  >- (irule inst_seq_ptr_abort_append >> simp[] >>
      goal_assum (drule_at Any)) >>
  irule inst_seq_ptr_append_ok >> simp[] >>
  qexistsl_tac [`G'`, `tn'`] >>
  simp[transient_lock_code_def, arithmeticTheory.ADD_COMM] >>
  irule literal_tstore_clean_inst_seq_ptr >> simp[]
QED

(* Only the three fresh scalar temporaries change the ghost at the guard. *)
Theorem transient_lock_code_ptr_frame:
  ~ctx_has_dalloca ctx /\
  (!b. ~((n2w nkey,b) IN tn.t_trans)) ==>
  ?G' tn'.
    inst_seq_ptr D 0 ctx func PG G tn
      (transient_lock_code nkey iv st) ss G' tn' /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `key_taint tn.t_trans (n2w nkey) = {}` by
    (simp[key_taint_def, EXTENSION] >> metis_tac[]) >>
  qabbrev_tac `G1 = DRESTRICT (DRESTRICT (DRESTRICT G
    (COMPL {STRING #"%" (toString st.cs_next_var)}))
    (COMPL {STRING #"%" (toString (st.cs_next_var + 1))}))
    (COMPL {STRING #"%" (toString (st.cs_next_var + 2))})` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+
    (STRING #"%" (toString st.cs_next_var),{}) |+
    (STRING #"%" (toString (st.cs_next_var + 1)),{}) |+
    (STRING #"%" (toString (st.cs_next_var + 2)),{})` >>
  `inst_seq_ptr D 0 ctx func PG G tn
    (transient_lock_code nkey T st) ss G1 tn1` by
    (mp_tac (Q.INST [`iv` |-> `T`]
      (SPEC_ALL transient_lock_check_ptr_ghost)) >>
     simp[transient_lock_code_def, Abbr `G1`, Abbr `tn1`]) >>
  qexistsl_tac [`G1`, `tn1`] >> rpt conj_tac
  >- (irule transient_lock_code_ptr_from_check >>
      simp[Abbr `tn1`])
  >- simp[Abbr `tn1`]
  >- simp[Abbr `tn1`]
  >- simp[Abbr `tn1`]
  >- simp[Abbr `tn1`] >>
  qx_gen_tac `x` >> strip_tac >>
  `x <> STRING #"%" (toString st.cs_next_var) /\
   x <> STRING #"%" (toString (st.cs_next_var + 1)) /\
   x <> STRING #"%" (toString (st.cs_next_var + 2))` by
    (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_ADD]) >>
  simp[Abbr `G1`, Abbr `tn1`, FLOOKUP_DRESTRICT, op_taint_def,
       FLOOKUP_UPDATE]
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

(* The successful guard establishes the ghost invariant at the body cursor. *)
Theorem transient_lock_code_origin_ptr_ghost:
  storage_locks_separated (FST H) (SND H) /\
  MEM nkey (SND H) /\ nkey < dimword (:256) /\
  ghost_inv H d cenv cx es G tn ss /\ local_ptrs_reserved cenv st /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at st x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at st x) /\
  es'.scopes = es.scopes /\
  ~ctx_has_dalloca ctx /\ ~ss.vs_halted /\
  lookup_block ss.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (transient_lock_code nkey iv st)
    (DROP ss.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (transient_lock_code nkey iv st) ss = OK ss' ==>
  ?G' tn'.
    gas_origin_ptr_path (D, 0, explicit, ctx, func, PG) (ss, G, tn) []
      (OK (ss' with vs_inst_idx :=
        ss.vs_inst_idx + LENGTH (transient_lock_code nkey iv st)), G', tn') /\
    ghost_inv H d cenv cx es' G' tn'
      (ss' with vs_inst_idx :=
        ss.vs_inst_idx + LENGTH (transient_lock_code nkey iv st))
Proof
  strip_tac >>
  `stor_taint_ok H cx tn ss` by fs[ghost_inv_def] >>
  `!b. ~((n2w nkey,b) IN tn.t_trans)` by
    (mp_tac (SPEC_ALL nonreentrant_slot_untainted) >> simp[]) >>
  mp_tac (SPEC_ALL transient_lock_code_ptr_frame) >> simp[] >> strip_tac >>
  `!x j. not_fresh_at st x ==>
    lookup_var x
      (transient_lock_checked_state st nkey ss with vs_inst_idx := j) =
    lookup_var x ss` by
    (rpt strip_tac >>
     `x <> STRING #"%" (toString st.cs_next_var) /\
      x <> STRING #"%" (toString (st.cs_next_var + 1)) /\
      x <> STRING #"%" (toString (st.cs_next_var + 2))` by
       (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_ADD]) >>
     simp[transient_lock_checked_state_def, update_var_def, lookup_var_def,
          FLOOKUP_UPDATE]) >>
  `!j. ghost_inv H d cenv cx es' G' tn'
    (transient_lock_checked_state st nkey ss with vs_inst_idx := j)` by
    (gen_tac >>
     mp_tac (Q.INST [`sa` |-> `st`, `s` |-> `ss`,
       `s'` |-> `transient_lock_checked_state st nkey ss with vs_inst_idx := j`]
       (SPEC_ALL ghost_inv_fresh_frame)) >>
     simp[transient_lock_checked_state_def, update_var_def]) >>
  qexistsl_tac [`G'`, `tn'`] >> conj_tac
  >- (`EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
        (transient_lock_code nkey iv st)` by
        (Cases_on `iv` >> simp[transient_lock_code_def, mk_inst_def,
                               is_terminator_def]) >>
      `run_inst_seq_mem_ok (transient_lock_code nkey iv st) ss` by
        (irule transient_lock_code_memory_checks >>
         Cases_on `iv` >> simp[transient_lock_code_def, mk_inst_def]) >>
      mp_tac (Q.INST [`code` |-> `transient_lock_code nkey iv st`,
        `s` |-> `ss`, `t` |-> `ss'`, `lo` |-> `0:num`]
        (SPEC_ALL run_inst_seq_gas_origin_ptr_path)) >>
      simp[] >> Cases_on `iv` >> simp[transient_lock_code_def, mk_inst_def]) >>
  Cases_on `iv` >> gvs[transient_lock_code_execution, AllCaseEqs()] >>
  `ghost_inv H d cenv cx es' G' tn'
     (tstore (n2w nkey) 1w
       (transient_lock_checked_state st nkey ss with vs_inst_idx :=
         ss.vs_inst_idx + LENGTH (transient_lock_code nkey F st)))` by
    (mp_tac (Q.INST [`es` |-> `es'`, `G` |-> `G'`, `tn` |-> `tn'`,
       `ss` |-> `transient_lock_checked_state st nkey ss with vs_inst_idx :=
         ss.vs_inst_idx + LENGTH (transient_lock_code nkey F st)`,
       `value` |-> `1w`]
       (SPEC_ALL nonreentrant_ghost_inv_frame)) >> simp[]) >>
  fs[tstore_def]
QED

Theorem compile_nonreentrant_lock_transient_same_block:
  compile_nonreentrant_lock nkey T iv st = ((),st') ==>
  st'.cs_blocks = st.cs_blocks /\
  st'.cs_current_bb = st.cs_current_bb /\
  st'.cs_current_insts = st.cs_current_insts ++ transient_lock_code nkey iv st
Proof
  Cases_on `iv` >>
  simp[compile_nonreentrant_lock_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_id_def,
       fresh_var_def, emit_def, transient_lock_code_def] >>
  strip_tac >> gvs[arithmeticTheory.ADD_ASSOC]
QED

Theorem compile_nonreentrant_lock_transient_prefix:
  compile_nonreentrant_lock nkey T iv st = ((),st') /\
  fn_has_code st st' func /\
  ss.vs_current_bb = st.cs_current_bb /\
  ss.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?bb. lookup_block ss.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (transient_lock_code nkey iv st)
      (DROP ss.vs_inst_idx bb.bb_instructions)
Proof
  strip_tac >>
  drule compile_nonreentrant_lock_transient_same_block >> strip_tac >>
  qpat_x_assum `fn_has_code _ _ _` mp_tac >>
  simp[fn_has_code_def, IS_PREFIX_APPEND] >> rpt strip_tac >>
  gvs[] >> simp[DROP_APPEND]
QED

(* Source lock acquisition and the emitted entry prefix meet at one body
   cursor, with decoded arguments and return buffers still covered. *)
Theorem checked_nonreentrant_entry_origin_ptr:
  storage_locks_separated (FST H) (SND H) /\
  MEM global_nonreentrant_slot (SND H) /\
  global_nonreentrant_slot < dimword (:256) /\
  source_typing_ok tops am tx /\ layouts_agree tops am tx /\
  MEM (FunctionDecl vis mut T rr name args dflts ret stmts) tops /\
  cx.nonreentrant_slot = lookup_nonreentrant_slot am.layouts tx.target /\
  state_rel H func cenv cx vs ss /\ fresh_vars_wrt st ss /\
  local_ptrs_rel func cenv scopes ss /\
  ghost_inv H d cenv cx vs G tn ss /\ local_ptrs_reserved cenv st /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at st x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at st x) /\
  compile_nonreentrant_lock global_nonreentrant_slot T (mut = View) st = ((),st') /\
  fn_has_code st st' func /\ ~ctx_has_dalloca ctx /\ ~ss.vs_halted /\
  ss.vs_current_bb = st.cs_current_bb /\
  ss.vs_inst_idx = LENGTH st.cs_current_insts /\
  tload (n2w global_nonreentrant_slot) ss <> 1w ==>
  ?vs' ss' G' tn'.
    (case cx.nonreentrant_slot of
       NONE => vyperState$raise
         (vyperState$Error (TypeError "nonreentrant slot missing"))
     | SOME key => acquire_nonreentrant_lock cx.txn.target key
                     (mut = View \/ mut = Pure)) vs = (INL (),vs') /\
    run_inst_seq (emitted_insts st st') ss = OK ss' /\
    state_rel H func cenv cx vs' ss' /\ fresh_vars_wrt st' ss' /\
    local_ptrs_rel func cenv scopes ss' /\
    gas_origin_ptr_path (D, 0, explicit, ctx, func, PG) (ss, G, tn) []
      (OK (ss' with vs_inst_idx := LENGTH st'.cs_current_insts), G', tn') /\
    ghost_inv H d cenv cx vs' G' tn'
      (ss' with vs_inst_idx := LENGTH st'.cs_current_insts)
Proof
  strip_tac >>
  drule_all checked_nonreentrant_entry_lock >> strip_tac >>
  `cx.nonreentrant_slot = SOME global_nonreentrant_slot` by
    metis_tac[layouts_agree_nonreentrant_slot] >>
  `vs'.scopes = vs.scopes` by
    (gvs[] >> metis_tac[acquire_nonreentrant_lock_scopes]) >>
  drule compile_nonreentrant_lock_transient_same_block >> strip_tac >>
  drule compile_nonreentrant_lock_transient_code >> strip_tac >>
  `?bb. lookup_block ss.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (transient_lock_code global_nonreentrant_slot (mut = View) st)
      (DROP ss.vs_inst_idx bb.bb_instructions)` by
    (drule_all compile_nonreentrant_lock_transient_prefix >> simp[]) >>
  mp_tac (Q.INST [`nkey` |-> `global_nonreentrant_slot`,
    `iv` |-> `mut = View`, `es` |-> `vs`, `es'` |-> `vs'`]
    (SPEC_ALL transient_lock_code_origin_ptr_ghost)) >>
  simp[] >> fs[]
QED

(* A held guard fails before the body and before the optional lock write. *)
Theorem checked_nonreentrant_entry_revert_origin_ptr:
  MEM global_nonreentrant_slot (SND H) /\
  global_nonreentrant_slot < dimword (:256) /\
  layouts_agree tops am tx /\ source_typing_ok tops am tx /\
  MEM (FunctionDecl vis mut T rr name args dflts ret stmts) tops /\
  cx.nonreentrant_slot = lookup_nonreentrant_slot am.layouts tx.target /\
  state_rel H func cenv cx vs ss /\ ghost_inv H d cenv cx vs G tn ss /\
  compile_nonreentrant_lock global_nonreentrant_slot T (mut = View) st = ((),st') /\
  fn_has_code st st' func /\ ~ctx_has_dalloca ctx /\ ~ss.vs_halted /\
  ss.vs_current_bb = st.cs_current_bb /\
  ss.vs_inst_idx = LENGTH st.cs_current_insts /\
  tload (n2w global_nonreentrant_slot) ss = 1w ==>
  (case cx.nonreentrant_slot of
     NONE => vyperState$raise
       (vyperState$Error (TypeError "nonreentrant slot missing"))
   | SOME key => acquire_nonreentrant_lock cx.txn.target key
                   (mut = View \/ mut = Pure)) vs =
    (INR (vyperState$Error (RuntimeError "nonreentrant lock")),
     vs with storage_trace := vs.storage_trace ++ [StorageLock global_nonreentrant_slot]) /\
  ?ss' G' tn' j.
    run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss' /\
    gas_origin_ptr_path (D, 0, explicit, ctx, func, PG) (ss, G, tn) []
      (Abort Revert_abort (ss' with vs_inst_idx := j), G', tn')
Proof
  strip_tac >>
  `function_header_ok vis mut T rr name args dflts ret` by
    metis_tac[source_typing_function_header] >>
  drule_all nonreentrant_entry_lock_source_revert >> strip_tac >> simp[] >>
  `stor_taint_ok H cx tn ss` by fs[ghost_inv_def] >>
  `!b. ~((n2w global_nonreentrant_slot,b) IN tn.t_trans)` by
    (mp_tac (Q.INST [`nkey` |-> `global_nonreentrant_slot`]
      (SPEC_ALL nonreentrant_slot_untainted)) >> simp[]) >>
  `key_taint tn.t_trans (n2w global_nonreentrant_slot) = {}` by
    (simp[key_taint_def, EXTENSION] >> metis_tac[]) >>
  drule_all compile_nonreentrant_lock_transient_prefix >> strip_tac >>
  drule compile_nonreentrant_lock_transient_code >> strip_tac >>
  mp_tac (Q.INST [`nkey` |-> `global_nonreentrant_slot`,
    `iv` |-> `mut = View`, `a` |-> `Revert_abort`]
    (SPEC_ALL transient_lock_code_abort_origin_ptr)) >>
  simp[] >> metis_tac[]
QED
