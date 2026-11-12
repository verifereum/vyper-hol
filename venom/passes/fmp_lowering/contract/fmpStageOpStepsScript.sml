(*
 * FmpLowering's stage simulation, one source instruction at a time: an
 * ordinary instruction, a halting terminator, a jump, and the tail of a
 * revert forwarding.  The block simulation (fmpStageBlockSim) chains them
 * with the restores, DALLOCA, RETPC_PARAM and INVOKE steps.
 *
 * TOP-LEVEL:
 *   fmp_stage_op_step        - an ordinary instruction, to the next index
 *   fmp_stage_halt_step      - a halting terminator, to related halts
 *   fmp_stage_jump_step      - a jump, to the same label
 *   fmp_stage_revert_forward - a revert forwarding's RETURNDATACOPY, to
 *                              related ends of the block
 *)
Theory fmpStageOpSteps
Ancestors
  fmpStageOpFrame fmpStageOpSimPure fmpStageOpSimMem fmpStageTermSim fmpStageControl
  fmpStageOpBase fmpStageRel ptrStaticDiscipline ptrDiscipline o1PassContract
  contextCodegenRel venomWf fmpReclaimDefs fmpAnalysisDefs
  venomExecProofs venomExecSemantics venomState venomInst list
  fmpStageOpFrameForwardAbort fmpStageOpFrameForwardFetch
  fmpStageOpFrameForwardScalars o1LowerDloadForwardInversion
  dftGasToListReachBoundary

(* Why: the opcodes the five simulation classes cover are exactly the
   ordinary ones row 3 allows: no FMP ops (pre_fmp_opcode), no ALLOCA and
   no MEMTOP (fn_static_ptr_ok). *)
Theorem fmp_stage_op_class[local]:
  ~is_terminator op /\ ~MEM op [INVOKE; DALLOCA; RETPC_PARAM; PHI] /\
  pre_fmp_opcode op /\ op <> ALLOCA /\ op <> MEMTOP ==>
  MEM op [ADD; SUB; MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
     EQ; LT; GT; SLT; SGT; ISZERO; AND; OR; XOR; NOT; SHL; SHR; SAR;
     SIGNEXTEND; BYTE; OFFSET] \/
  MEM op [GAS; CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID; COINBASE;
     TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE; BLOBBASEFEE;
     CALLDATASIZE; CODESIZE; RETURNDATASIZE; SELFBALANCE;
     BLOCKHASH; BLOBHASH; BALANCE; EXTCODESIZE; EXTCODEHASH;
     CALLDATALOAD; DLOAD; PARAM; ASSIGN; NOP; ASSERT; ASSERT_UNREACHABLE] \/
  MEM op [MLOAD; MSTORE; MSTORE8; MCOPY; CALLDATACOPY; CODECOPY;
     RETURNDATACOPY; EXTCODECOPY; DLOADBYTES; ILOAD; SHA3] \/
  MEM op [SLOAD; TLOAD; SSTORE; TSTORE; ISTORE; LOG] \/
  MEM op [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]
Proof
  Cases_on `op` >> simp[is_terminator_def, pre_fmp_opcode_def]
QED

(* Why: the row-3 facts the step proofs use about the active instruction. *)
Theorem fmp_stage_active_facts:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s ==>
  pre_fmp_opcode inst.inst_opcode /\ inst.inst_opcode <> ALLOCA /\
  inst.inst_opcode <> MEMTOP /\
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
       s.vs_inst_idx < LENGTH bb.bb_instructions /\
       inst = EL s.vs_inst_idx bb.bb_instructions
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  `fn_static_ptr_ok P fn` by gvs[EVERY_MEM] >>
  `pre_fmp_opcode inst.inst_opcode /\ inst.inst_opcode <> ALLOCA /\
   inst.inst_opcode <> MEMTOP` by
    (gvs[pre_fmp_ops_def, fn_static_ptr_ok_def, EVERY_MEM] >> metis_tac[]) >>
  simp[] >> gvs[active_inst_def] >> qexists_tac `bb` >> simp[] >>
  irule MEM_lookup_block >>
  gvs[o1_fn_shape_def, wf_function_def, fn_labels_def]
QED

(* Why: fmp_stage_kept_inst, with the instruction substituted. *)
Theorem fmp_stage_kept_inst_at[local]:
  fmp_stage_lowered infos ctx runner fn fn' /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  idx < LENGTH bb.bb_instructions /\
  (EL idx bb.bb_instructions).inst_opcode <> DALLOCA /\
  (EL idx bb.bb_instructions).inst_opcode <> INVOKE /\
  (EL idx bb.bb_instructions).inst_opcode <> RETPC_PARAM /\
  pre_fmp_opcode (EL idx bb.bb_instructions).inst_opcode ==>
  ?bb'. lookup_block lbl fn'.fn_blocks = SOME bb' /\
    fmp_stage_tidx (fmp_stage_plan infos ctx fn)
      (fmp_stage_root infos ctx fn) lbl bb.bb_instructions idx +
    (if (lbl,idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0) <
      LENGTH bb'.bb_instructions /\
    EL (fmp_stage_tidx (fmp_stage_plan infos ctx fn)
          (fmp_stage_root infos ctx fn) lbl bb.bb_instructions idx +
        (if (lbl,idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0))
       bb'.bb_instructions = EL idx bb.bb_instructions
Proof
  strip_tac >> irule fmp_stage_kept_inst >> simp[] >> metis_tac[]
QED

(* Why: a kept instruction runs at the control map's index on the target,
   past its point's restore when that has run; an unrestored point is no
   reclaim point (fmp_stage_plan_point), so it has no restore. *)
Theorem fmp_stage_target_inst:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~MEM inst.inst_opcode [DALLOCA; INVOKE; RETPC_PARAM] /\
  (~restored ==> ~is_terminator inst.inst_opcode) /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' ==>
  active_inst fn' inst t
Proof
  strip_tac >> drule_all fmp_stage_active_facts >> strip_tac >>
  gvs[fmp_stage_rel_def, fmp_frame_rel_def] >>
  drule_all fmp_stage_kept_inst_at >> strip_tac >>
  simp[active_inst_def] >> qexists_tac `bb'` >>
  imp_res_tac lookup_block_MEM >> imp_res_tac lookup_block_label >>
  Cases_on `restored` >> gvs[] >>
  Cases_on `(s.vs_current_bb,s.vs_inst_idx) IN
            FDOM (fmp_stage_plan infos ctx fn)` >> gvs[] >>
  drule_all fmp_stage_plan_point >>
  gvs[fmp_is_reclaim_point_def, fmp_callee_info_def,
      fmp_invoke_target_def] >>
  rpt strip_tac >> gvs[is_terminator_def]
QED

(* Why: an ordinary instruction's local result gives the relation at the
   next index (fmp_stage_op_frame); halts and aborts pass through. *)
Theorem fmp_stage_op_finish[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ ~is_terminator inst.inst_opcode /\
  ~MEM inst.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM; PHI] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  step_inst k C inst s = r /\ step_inst k' C' inst t = r' /\
  (case r of
     OK s1 => ?t1. r' = OK t1 /\
          (!v. ~MEM v inst.inst_outputs ==>
               FLOOKUP s1.vs_vars v = FLOOKUP s.vs_vars v /\
               FLOOKUP t1.vs_vars v = FLOOKUP t.vs_vars v) /\
          (!v x. MEM v inst.inst_outputs /\ FLOOKUP s1.vs_vars v = SOME x ==>
             ?y. FLOOKUP t1.vs_vars v = SOME y /\
                 (~retpc_var fn v ==>
                  fmp_value_rel sm (FLOOKUP (step_prov PG G inst s1) v)
                    (op_taint (step_taint inst s s1 tn) (Var v)) x y)) /\
          ld_memory_agree (fmp_ld_sites sm) eom
            (step_taint inst s s1 tn).t_mem s1.vs_memory t1.vs_memory /\
          ld_shared_agree D s.vs_call_ctx.cc_address
            (step_taint inst s s1 tn) s1 t1 /\
          s1.vs_returndata = t1.vs_returndata /\
          ~s1.vs_halted /\ ~t1.vs_halted /\
          s1.vs_current_bb = s.vs_current_bb /\ s1.vs_prev_bb = s.vs_prev_bb /\
          s1.vs_inst_idx = s.vs_inst_idx /\ s1.vs_params = s.vs_params /\
          s1.vs_call_ctx = s.vs_call_ctx /\ s1.vs_tx_ctx = s.vs_tx_ctx /\
          s1.vs_block_ctx = s.vs_block_ctx /\
          s1.vs_data_section = s.vs_data_section /\
          s1.vs_labels = s.vs_labels /\ s1.vs_code = s.vs_code /\
          s1.vs_prev_hashes = s.vs_prev_hashes /\
          s1.vs_initial_fmp = s.vs_initial_fmp /\ s1.vs_fmp = s.vs_fmp /\
          t1.vs_current_bb = t.vs_current_bb /\ t1.vs_prev_bb = t.vs_prev_bb /\
          t1.vs_inst_idx = t.vs_inst_idx /\ t1.vs_params = t.vs_params /\
          t1.vs_call_ctx = t.vs_call_ctx /\ t1.vs_tx_ctx = t.vs_tx_ctx /\
          t1.vs_block_ctx = t.vs_block_ctx /\
          t1.vs_data_section = t.vs_data_section /\
          t1.vs_labels = t.vs_labels /\ t1.vs_code = t.vs_code /\
          t1.vs_prev_hashes = t.vs_prev_hashes /\
          t1.vs_initial_fmp = t.vs_initial_fmp /\ t1.vs_fmp = t.vs_fmp
   | Halt se => dead_result_rel D r r'
   | Abort ab se => dead_result_rel D r r'
   | _ => F) ==>
  case r of
    OK s1 =>
      ?t1. r' = OK t1 /\
        fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG
          (step_prov PG G inst s1) (step_taint inst s s1 tn) fn
          (s1 with vs_inst_idx := SUC s.vs_inst_idx) lo
          (t1 with vs_inst_idx := SUC t.vs_inst_idx) ts
  | Halt se => dead_result_rel D r r'
  | Abort ab se => dead_result_rel D r r'
  | _ => F
Proof
  strip_tac >> Cases_on `r` >> fs[] >> gvs[] >>
  irule fmp_stage_op_frame >> simp[] >> metis_tac[]
QED

(* Why: the target runs the same instruction (fmp_stage_kept_inst, at the
   control map's index, since an ordinary instruction is no reclaim
   point), to a related local result (fmpStageOpSimPure, fmpStageOpSimMem), from which the
   relation at the next index follows (fmp_stage_op_frame). *)
Theorem fmp_stage_op_step:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ ~in_revert_forward fn s /\ ~is_terminator inst.inst_opcode /\
  ~MEM inst.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM; PHI] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  step_inst k C inst s = r /\ terminates r ==>
  ?inst' k' r'.
    active_inst fn' inst' t /\ step_inst k' C' inst' t = r' /\
    case r of
      OK s1 =>
        ?t1. r' = OK t1 /\
          fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG
            (step_prov PG G inst s1) (step_taint inst s s1 tn) fn
            (s1 with vs_inst_idx := SUC s.vs_inst_idx) lo
            (t1 with vs_inst_idx := SUC t.vs_inst_idx) ts
    | Halt se => dead_result_rel D r r'
    | Abort ab se => dead_result_rel D r r'
    | _ => F
Proof
  strip_tac >>
  `~MEM inst.inst_opcode [DALLOCA; INVOKE; RETPC_PARAM]` by fs[] >>
  `~F ==> ~is_terminator inst.inst_opcode` by simp[] >>
  drule_all fmp_stage_target_inst >> strip_tac >>
  drule_all fmp_stage_active_facts >> strip_tac >>
  qexistsl_tac [`inst`] >> simp[] >>
  drule_all fmp_stage_op_class >> strip_tac
  >- (drule_all fmp_stage_sim_scalar >> strip_tac >>
      drule_all fmp_stage_op_finish >> metis_tac[])
  >- (drule_all fmp_stage_sim_read >> strip_tac >>
      drule_all fmp_stage_op_finish >> metis_tac[])
  >- (drule_all fmp_stage_sim_memory >> strip_tac >>
      drule_all fmp_stage_op_finish >> metis_tac[])
  >- (drule_all fmp_stage_sim_effects >> strip_tac >>
      drule_all fmp_stage_op_finish >> metis_tac[])
  >- (drule_all fmp_stage_sim_call >> strip_tac >>
      drule_all fmp_stage_op_finish >> metis_tac[])
QED

(* Why: the target runs the same terminator, past its point's restore
   (fmp_stage_kept_inst), to a related halt (fmp_stage_sim_halt). *)
Theorem fmp_stage_halt_step:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ is_terminator inst.inst_opcode /\
  ~MEM inst.inst_opcode [JMP; JNZ; DJMP; RET] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  step_inst k C inst s = r /\ terminates r ==>
  ?inst' k' r'.
    active_inst fn' inst' t /\ step_inst k' C' inst' t = r' /\
    case r of
      OK s1 => s1.vs_halted /\
               ?t1. r' = OK t1 /\ t1.vs_halted /\
                    dead_result_rel D (Halt s1) (Halt t1)
    | Halt se => dead_result_rel D r r'
    | Abort ab se => dead_result_rel D r r'
    | _ => F
Proof
  strip_tac >>
  `~MEM inst.inst_opcode [DALLOCA; INVOKE; RETPC_PARAM]` by
    (fs[] >> rpt strip_tac >> gvs[is_terminator_def]) >>
  `~T ==> ~is_terminator inst.inst_opcode` by simp[] >>
  drule_all fmp_stage_target_inst >> strip_tac >>
  drule_all fmp_stage_active_facts >> strip_tac >>
  `MEM inst.inst_opcode [STOP; RETURN; REVERT; SINK; SELFDESTRUCT; INVALID]` by
    (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def, pre_fmp_opcode_def]) >>
  drule_all fmp_stage_sim_halt >> strip_tac >> metis_tac[]
QED

(* Why: as for halts, with fmp_stage_sim_jump. *)
Theorem fmp_stage_jump_step:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  step_inst k C inst s = r /\ terminates r ==>
  ?lbl inst'.
    r = OK (jump_to lbl s) /\ active_inst fn' inst' t /\
    !k'. step_inst k' C' inst' t = OK (jump_to lbl t)
Proof
  strip_tac >>
  `~MEM inst.inst_opcode [DALLOCA; INVOKE; RETPC_PARAM]` by gvs[] >>
  `~T ==> ~is_terminator inst.inst_opcode` by simp[] >>
  drule_all fmp_stage_target_inst >> strip_tac >>
  drule_all fmp_stage_sim_jump >> strip_tac >> metis_tac[]
QED

(* Why: a revert forwarding copies the callee's revert data and reverts
   with it, with only ASSIGNs in between, none of them reclaim points: the
   target runs the same instructions, and both runs end in a revert (or
   abort alike before it), which dead_result_rel relates whatever the
   memory holds.  The copy may write anywhere (access_ok exempts it), so
   no relation holds between the instructions. *)
Theorem fmp_stage_revert_forward:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ in_revert_forward fn s /\
  inst.inst_opcode = RETURNDATACOPY /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  exec_block k C bb s = r /\ terminates r ==>
  ?fn' bb' k' r'.
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    exec_block k' C' bb' t = r' /\ dead_result_rel D r r'
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  `ALL_DISTINCT (fn_labels fn)` by gvs[o1_fn_shape_def, wf_function_def] >>
  `get_instruction bb s.vs_inst_idx = SOME inst` by
    metis_tac[active_inst_lookup_distinct, optionTheory.SOME_11] >>
  `revert_forward_at bb s.vs_inst_idx` by
    gvs[in_revert_forward_def] >>
  drule_all revert_forward_at_terminates_abort >> strip_tac >>
  `?j. revert_forward_pair bb s.vs_inst_idx j` by
    (gvs[revert_forward_at_def]
     >- metis_tac[] >> gvs[revert_forward_pair_def]) >>
  drule_all fmp_forward_fetch >> strip_tac >>
  `?dst src sz. inst.inst_operands = [dst;src;sz]` by
    (gvs[revert_forward_pair_def] >> metis_tac[]) >>
  drule_all fmp_forward_copy_scalars >> strip_tac >>
  `s.vs_labels = t.vs_labels /\ s.vs_returndata = t.vs_returndata /\
   (!v x. FLOOKUP s.vs_vars v = SOME x ==>
     ?y. FLOOKUP t.vs_vars v = SOME y)` by
    (gvs[fmp_stage_rel_def, fmp_frame_rel_def, fmp_env_rel_def] >> metis_tac[]) >>
  `exec_block k C bb s = Abort reason se` by gvs[] >>
  drule_all fmp_forward_available_abort >>
  disch_then (qspec_then `C'` strip_assume_tac) >>
  qexistsl_tac [`fn'`, `bb'`, `k`, `Abort reason t1`] >>
  gvs[dead_result_rel_def]
QED
