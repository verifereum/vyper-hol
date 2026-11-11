Theory lowerDloadPtrJointDispatch
Ancestors
  lowerDloadPtrControlInversion lowerDloadPtrExclusions lowerDloadPtrJointScalar lowerDloadPtrJointAffine
  lowerDloadPtrJointVariable lowerDloadPtrJointMemoryRead
  lowerDloadPtrJointHash lowerDloadPtrJointMemoryStore lowerDloadPtrJointLog
  lowerDloadPtrJointStorage lowerDloadPtrJointAllocClosure
  lowerDloadPtrJointBytesClosure lowerDloadPtrJointDloadClosure
  lowerDloadPtrJointCopyClosure lowerDloadPtrJointInterior
  lowerDloadPtrTerminalClosure lowerDloadPtrJointShift lowerDloadPtrJointEnvironmentRead
  lowerDloadPtrJointGas lowerDloadPtrJointIdentity lowerDloadPtrJointExternalCall
  lowerDloadPtrJointCreate lowerDloadPtrJointDelegate lowerDloadPtrJointEntry

(* These are quotation abbreviations only, not HOL definitions. Keeping the
   normal existential literally identical at entry and exit avoids drifting
   copies of the relational invariant. R is lexically within its witnesses. *)
val normal = ``\R ds PH H un g j t.
  ?cs PG G tn f i s q emitted n pfuel t0 H0 un0 fs.
    frame_reachable vs C cs PG G tn f i s /\
    dload_boundary_core lo fs
      (set (fn_ir_vars f) DIFF {v | retpc_var f v})
      (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) cs)
      PG PH G H0 tn un0 s t0 cs ds /\
    dload_control_match q f g s t0 i emitted 0 /\
    dload_prefix_match pfuel C' PH emitted n t0 H0 un0 t H un /\
    dload_control_match q f g s t i emitted n /\ j = EL n emitted /\
    R i n emitted /\
    (!v. v IN set (fn_ir_vars f) ==>
      (lookup_var v s = NONE <=> lookup_var v t0 = NONE)) /\
    FDOM G SUBSET fn_pv P f /\
    (!k b sz. k < LENGTH PG /\ EL k PG = SOME (b,sz) ==> k IN P f.fn_name) /\
    (!c. MEM c cs ==> FDOM c.cf_prov SUBSET fn_pv P c.cf_fn) /\
    (!c k b sz. MEM c cs /\ k < LENGTH c.cf_params /\
      EL k c.cf_params = SOME (b,sz) ==> k IN P c.cf_fn.fn_name) /\
    LENGTH fs = SUC (LENGTH cs) /\ LENGTH cs = LENGTH ds /\
    (!k. k < LENGTH fs ==>
      (EL k fs).dr_scratch =
        FDOM (EL k (t0::MAP (\d. d.cf_state) ds)).vs_allocas DIFF
        {id | ?ci. MEM ci (fn_insts (EL k (f::MAP (\c. c.cf_fn) cs))) /\
                   ci.inst_id = id}) /\
    ir_supply_covers_fn q f /\
    (?q'. lower_dload_function_supply q f = (g,q')) /\
    (!k. k < LENGTH cs ==>
      let c = EL k cs; d = EL k ds in
      dload_live_layout lo c.cf_state.vs_alloca_next d.cf_state.vs_alloca_next
        (DROP (SUC k) fs) /\
      dload_equal_environment c.cf_state d.cf_state /\
      c.cf_state.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
      c.cf_inst = d.cf_inst /\
      (!a. a IN set (fn_ir_vars c.cf_fn) ==>
        (lookup_var a c.cf_state = NONE <=> lookup_var a d.cf_state = NONE)) /\
      (?qc. ir_supply_covers_fn qc c.cf_fn /\
        (?qc'. lower_dload_function_supply qc c.cf_fn = (d.cf_fn,qc')) /\
        dload_control_match qc c.cf_fn d.cf_fn c.cf_state d.cf_state
          c.cf_inst [c.cf_inst] 0))``;

val covered = ``\i n (emitted:instruction list).
  SUC n < LENGTH emitted \/
  MEM i.inst_opcode [LT; GT; EQ; MUL; Div; SDIV; Mod; SMOD; Exp;
    ADDMOD; MULMOD; SLT; SGT; ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET; BUMP] \/
  (i.inst_opcode = ADD \/ i.inst_opcode = SUB) \/
  MEM i.inst_opcode [ASSIGN; PARAM; RETPC_PARAM] \/
  MEM i.inst_opcode [MLOAD; ILOAD] \/ i.inst_opcode = SHA3 \/ i.inst_opcode = LOG \/
  (i.inst_opcode = CALL \/ i.inst_opcode = STATICCALL) \/
  (i.inst_opcode = CREATE \/ i.inst_opcode = CREATE2) \/
  i.inst_opcode = DELEGATECALL \/
  i.inst_opcode = MSTORE8 \/ MEM i.inst_opcode [MSTORE; ISTORE] \/
  i.inst_opcode = MCOPY \/ MEM i.inst_opcode [SLOAD; TLOAD] \/
  MEM i.inst_opcode [SSTORE; TSTORE] \/ i.inst_opcode = ALLOCA \/
  (i.inst_opcode = DLOAD /\ SUC n = LENGTH emitted) \/
  (i.inst_opcode = DLOADBYTES /\ SUC n = LENGTH emitted) \/
  MEM i.inst_opcode [CODECOPY; CALLDATACOPY; RETURNDATACOPY; EXTCODECOPY]``;

fun normal_row th =
  disj1_tac >> pure_rewrite_tac [AND_CLAUSES] >> irule th >> simp[] >>
  rpt (first_assum (irule_at Any)) >> simp[] >>
  qexists_tac `fuel` >> gvs[];

Theorem dload_joint_covered_next:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
  o1_src_inv D C vs /\ callee_first names C.ctx_functions /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  ALL_DISTINCT (fn_labels g) /\
  ((^normal) (^covered) ds PH H un g j t \/
   dload_terminal_mode lo P vs C ds H un g j t) /\
  frame_reachable vs C' ds PH H un g j t /\
  active_inst g j t /\ ~is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE /\
  step_inst fuel C' j t = OK t1 /\
  active_inst g next (t1 with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ((^normal) (\i n emitted. T) ds PH
    (step_prov PH H j t1) (step_taint j t t1 un) g next
    (t1 with vs_inst_idx := SUC t.vs_inst_idx) \/
   dload_terminal_mode lo P vs C ds (step_prov PH H j t1)
    (step_taint j t t1 un) g next (t1 with vs_inst_idx := SUC t.vs_inst_idx))
Proof
  CONV_TAC (REDEPTH_CONV BETA_CONV) >> strip_tac
  >~ [`SUC n < LENGTH emitted`]
  >- normal_row dload_joint_interior_next_closed
  >~ [`MEM i.inst_opcode (LT::_)`]
  >- normal_row dload_joint_tracked_scalar_next
  >~ [`i.inst_opcode = ADD`]
  >- normal_row dload_joint_tracked_affine_next
  >~ [`i.inst_opcode = SUB`]
  >- normal_row dload_joint_tracked_affine_next
  >~ [`MEM i.inst_opcode [ASSIGN; PARAM; RETPC_PARAM]`]
  >- normal_row dload_joint_tracked_variable_next
  >~ [`MEM i.inst_opcode [MLOAD; ILOAD]`]
  >- normal_row dload_joint_tracked_mload_next
  >~ [`i.inst_opcode = SHA3`]
  >- normal_row dload_joint_tracked_sha3_next
  >~ [`i.inst_opcode = LOG`]
  >- normal_row dload_joint_tracked_log_next
  >~ [`i.inst_opcode = CALL`]
  >- normal_row (SRULE [] dload_joint_tracked_external_call_next)
  >~ [`i.inst_opcode = STATICCALL`]
  >- normal_row (SRULE [] dload_joint_tracked_external_call_next)
  >~ [`i.inst_opcode = CREATE`]
  >- normal_row (SRULE [] dload_joint_tracked_create_next)
  >~ [`i.inst_opcode = CREATE2`]
  >- normal_row (SRULE [] dload_joint_tracked_create_next)
  >~ [`i.inst_opcode = DELEGATECALL`]
  >- normal_row (SRULE [] dload_joint_tracked_delegate_next)
  >~ [`i.inst_opcode = MSTORE8`]
  >- normal_row dload_joint_tracked_mstore8_next
  >~ [`MEM i.inst_opcode [MSTORE; ISTORE]`]
  >- normal_row dload_joint_tracked_mstore_next
  >~ [`i.inst_opcode = MCOPY`]
  >- normal_row dload_joint_tracked_mcopy_next
  >~ [`MEM i.inst_opcode [SLOAD; TLOAD]`]
  >- normal_row dload_joint_tracked_storage_read_next
  >~ [`MEM i.inst_opcode [SSTORE; TSTORE]`]
  >- normal_row dload_joint_tracked_storage_write_next
  >~ [`i.inst_opcode = ALLOCA`]
  >- normal_row dload_joint_tracked_alloca_next
  >~ [`i.inst_opcode = DLOAD`]
  >- normal_row dload_joint_tracked_dload_complete_next
  >~ [`i.inst_opcode = DLOADBYTES`]
  >- normal_row dload_joint_tracked_dloadbytes_complete_next
  >~ [`MEM i.inst_opcode [CODECOPY; CALLDATACOPY; RETURNDATACOPY; EXTCODECOPY]`]
  >- (pure_rewrite_tac [AND_CLAUSES] >>
      irule dload_joint_tracked_external_copy_routed_next >> simp[] >>
      rpt (first_assum (irule_at Any)) >> simp[] >>
      qexists_tac `fuel` >> gvs[])
  >> disj2_tac >> irule dload_terminal_mode_next >>
  simp[] >> rpt (first_assum (irule_at Any)) >> simp[]
QED

Theorem dload_joint_covered_shift_next:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
  o1_src_inv D C vs /\ callee_first names C.ctx_functions /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  ALL_DISTINCT (fn_labels g) /\
  ((^normal) (\i n emitted. (^covered) i n emitted \/
      MEM i.inst_opcode [SHL; SHR; SAR]) ds PH H un g j t \/
   dload_terminal_mode lo P vs C ds H un g j t) /\
  frame_reachable vs C' ds PH H un g j t /\
  active_inst g j t /\ ~is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE /\
  step_inst fuel C' j t = OK t1 /\
  active_inst g next (t1 with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ((^normal) (\i n emitted. T) ds PH
    (step_prov PH H j t1) (step_taint j t t1 un) g next
    (t1 with vs_inst_idx := SUC t.vs_inst_idx) \/
   dload_terminal_mode lo P vs C ds (step_prov PH H j t1)
    (step_taint j t t1 un) g next (t1 with vs_inst_idx := SUC t.vs_inst_idx))
Proof
  qabbrev_tac `old = ^covered` >>
  CONV_TAC (REDEPTH_CONV BETA_CONV) >> strip_tac
  >- (pure_rewrite_tac [AND_CLAUSES] >> irule (SRULE [] dload_joint_covered_next) >> simp[] >>
      rpt (first_assum (irule_at Any)) >> simp[] >>
      qexists_tac `fuel` >> simp[] >>
      conj_tac >- metis_tac[] >>
      disj1_tac >> rpt (first_assum (irule_at Any)) >> simp[Abbr `old`] >> conj_tac
      >- (qpat_x_assum
            `(_ : instruction -> num -> instruction list -> bool) i n emitted`
            mp_tac >> simp[]) >>
      qpat_x_assum `!k. k < LENGTH cs ==> _`
        (mp_tac o SIMP_RULE (srw_ss()) [LET_THM]) >> simp[])
  >- normal_row (SRULE [] dload_joint_tracked_shift_next)
  >> disj2_tac >> irule dload_terminal_mode_next >>
  simp[] >> rpt (first_assum (irule_at Any)) >> simp[]
QED

val covered_shift = ``\i n emitted. (^covered) i n emitted \/
  MEM i.inst_opcode [SHL; SHR; SAR]``;

val final_covered = ``\i n emitted. (^covered_shift) i n emitted \/
  MEM i.inst_opcode [CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID;
    COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE; BLOBBASEFEE;
    CALLDATASIZE; RETURNDATASIZE; BLOCKHASH; BLOBHASH; CALLDATALOAD;
    BALANCE; SELFBALANCE; EXTCODESIZE; EXTCODEHASH; CODESIZE; INITIAL_FMP] \/
  i.inst_opcode = GAS \/ MEM i.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE]``;

Theorem dload_joint_dispatch_residual_classification:
  !i n emitted. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    SUC n <= LENGTH emitted ==>
    (~((^final_covered) i n emitted) <=>
      ~(SUC n < LENGTH emitted) /\
      MEM i.inst_opcode [MEMTOP; PHI; DALLOCA; GETFMP; SETFMP; FMP_PARAM])
Proof
  rpt gen_tac >> Cases_on `i.inst_opcode` >>
  simp[venomInstTheory.is_terminator_def] >> decide_tac
QED

Theorem dload_joint_dispatch_actual_residual:
  o1_src_inv D C vs /\ o1_ctx_shape C /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  frame_reachable vs C cs PG G tn f i s /\
  dload_control_match q f g s t i emitted n /\ j = EL n emitted /\
  ~is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE /\
  ~((^final_covered) i n emitted) /\
  step_inst fuel C' j t = OK t1 ==>
  i.inst_opcode = DELEGATECALL /\
  ~(SUC n < LENGTH emitted)
Proof
  strip_tac >>
  `MEM f C.ctx_functions` by
    (drule lowerDloadPtrRawReachableTheory.frame_reachable_raw_certificate >>
     simp[] >> strip_tac >> simp[]) >>
  `MEM i (fn_insts f)` by
    (qpat_x_assum `dload_control_match _ _ _ _ _ _ _ _` mp_tac >>
     simp[lowerDloadPtrRelTheory.dload_control_match_def,
       contextCodegenRelTheory.active_inst_def, venomInstTheory.fn_insts_def,
       o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[listTheory.EL_MEM]) >>
  `fn_ptr_ok P f` by fs[listTheory.EVERY_MEM] >>
  drule_all dload_source_instruction_exclusions >> strip_tac >>
  drule_all dload_ptr_instruction_exclusions >> strip_tac >>
  drule_all dload_control_next_source_guards >> strip_tac >>
  `SUC n <= LENGTH emitted` by
    (drule lowerDloadPtrRelTheory.dload_control_match_expansion >>
     strip_tac >> decide_tac) >>
  drule_all dload_joint_dispatch_residual_classification >> strip_tac >>
  `i.inst_opcode <> PHI` by
    (strip_tac >>
     `emitted = [i] /\ n = 0 /\ j = i` by
       (drule lowerDloadPtrRelTheory.dload_control_match_expansion >>
        strip_tac >>
        qpat_x_assum `lower_dload_inst_supply _ _ = _` mp_tac >>
        simp[lowerDloadDefsTheory.lower_dload_inst_supply_def] >>
        rpt strip_tac >> gnvs[] >> `n = 0` by decide_tac >> gvs[]) >>
     gvs[venomExecSemanticsTheory.step_inst_non_invoke] >>
     metis_tac[dload_non_success_instruction_exclusions, listTheory.MEM]) >>
  gvs[listTheory.MEM, venomInstTheory.is_raw_fmp_opcode_def]
QED

Theorem dload_joint_covered_environment_next:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
  o1_src_inv D C vs /\ callee_first names C.ctx_functions /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  ALL_DISTINCT (fn_labels g) /\
  ((^normal) (^final_covered)
      ds PH H un g j t \/
   dload_terminal_mode lo P vs C ds H un g j t) /\
  frame_reachable vs C' ds PH H un g j t /\
  active_inst g j t /\ ~is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE /\
  step_inst fuel C' j t = OK t1 /\
  active_inst g next (t1 with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ((^normal) (\i n emitted. T) ds PH
    (step_prov PH H j t1) (step_taint j t t1 un) g next
    (t1 with vs_inst_idx := SUC t.vs_inst_idx) \/
   dload_terminal_mode lo P vs C ds (step_prov PH H j t1)
    (step_taint j t t1 un) g next (t1 with vs_inst_idx := SUC t.vs_inst_idx))
Proof
  qabbrev_tac `old = ^covered_shift` >>
  CONV_TAC (REDEPTH_CONV BETA_CONV) >> strip_tac
  >- (pure_rewrite_tac [AND_CLAUSES] >>
      irule (SRULE [] dload_joint_covered_shift_next) >> simp[] >>
      rpt (first_assum (irule_at Any)) >> simp[] >>
      qexists_tac `fuel` >> simp[] >>
      conj_tac >- metis_tac[] >>
      disj1_tac >> rpt (first_assum (irule_at Any)) >>
      simp[Abbr `old`] >> conj_tac
      >- (qpat_x_assum
            `(_ : instruction -> num -> instruction list -> bool) i n emitted`
            mp_tac >> simp[]) >>
      qpat_x_assum `!k. k < LENGTH cs ==> _`
        (mp_tac o SIMP_RULE (srw_ss()) [LET_THM]) >> simp[])
  >- normal_row (SRULE [] dload_joint_tracked_environment_read_next)
  >- normal_row (SRULE [] dload_joint_tracked_gas_next)
  >- normal_row (SRULE [] dload_joint_tracked_identity_next)
  >> disj2_tac >> irule dload_terminal_mode_next >>
  simp[] >> rpt (first_assum (irule_at Any)) >> simp[]
QED

val _ = List.app (fn (n,th) =>
  if null (hyp th) then () else raise Fail (n ^ ": nonempty hypotheses"))
  [("actual_residual", dload_joint_dispatch_actual_residual),
   ("residual_classification", dload_joint_dispatch_residual_classification),
   ("covered_next", dload_joint_covered_next),
   ("covered_shift_next", dload_joint_covered_shift_next),
   ("covered_environment_next", dload_joint_covered_environment_next)];

Theorem dload_joint_dispatch_actual_covered:
  o1_src_inv D C vs /\ o1_ctx_shape C /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  frame_reachable vs C cs PG G tn f i s /\
  dload_control_match q f g s t i emitted n /\ j = EL n emitted /\
  ~is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE /\
  step_inst fuel C' j t = OK t1 ==>
  (^final_covered) i n emitted
Proof
  strip_tac >> CCONTR_TAC >>
  drule_all dload_joint_dispatch_actual_residual >> strip_tac >>
  gvs[]
QED

Theorem dload_joint_next:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
  o1_src_inv D C vs /\ callee_first names C.ctx_functions /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  ALL_DISTINCT (fn_labels g) /\
  ((^normal) (\i n emitted. T) ds PH H un g j t \/
   dload_terminal_mode lo P vs C ds H un g j t) /\
  frame_reachable vs C' ds PH H un g j t /\
  active_inst g j t /\ ~is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE /\
  step_inst fuel C' j t = OK t1 /\
  active_inst g next (t1 with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ((^normal) (\i n emitted. T) ds PH
    (step_prov PH H j t1) (step_taint j t t1 un) g next
    (t1 with vs_inst_idx := SUC t.vs_inst_idx) \/
   dload_terminal_mode lo P vs C ds (step_prov PH H j t1)
    (step_taint j t t1 un) g next (t1 with vs_inst_idx := SUC t.vs_inst_idx))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule dload_joint_covered_environment_next >>
  simp[] >> rpt (first_assum (irule_at Any)) >> simp[] >>
  qpat_x_assum `_ \/ dload_terminal_mode _ _ _ _ _ _ _ _ _ _` strip_assume_tac
  >- (disj1_tac >>
      CONV_TAC (REDEPTH_CONV BETA_CONV) >>
      gvs[] >>
      `(^final_covered) i n emitted` by
        (irule dload_joint_dispatch_actual_covered >>
         simp[] >> rpt (first_assum (irule_at Any)) >> simp[] >>
         qexists_tac `fuel` >> simp[]) >>
      rpt (first_assum (irule_at Any)) >> fs[]) >>
  disj2_tac >> simp[]
QED

val _ = List.app (fn th => if null (hyp th) then ()
  else raise Fail "unconditional next: nonempty hypotheses")
  [dload_joint_dispatch_actual_covered, dload_joint_next];

Theorem dload_joint_entry:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
  o1_src_inv D C vs /\ callee_first names C.ctx_functions /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  C'.ctx_entry = SOME name /\ lookup_function name C'.ctx_functions = SOME g /\
  fn_entry_label g = SOME lbl /\
  enters_block g
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) t /\
  active_inst g j t ==>
  (^normal) (\i n emitted. T) [] [] FEMPTY entry_taint g j t
Proof
  strip_tac >> drule_all dload_actual_joint_entry_tracked >>
  disch_then (qspec_then `P` strip_assume_tac) >>
  `set (fn_ir_vars f) =
    {v | ?ci. MEM ci (fn_insts f) /\
      (MEM v ci.inst_outputs \/ MEM (Var v) ci.inst_operands)}` by
    (simp[irSupplyTheory.fn_ir_vars_def, irSupplyTheory.block_ir_vars_def,
      irSupplyTheory.inst_ir_vars_def, venomInstTheory.fn_insts_def,
      pred_setTheory.EXTENSION, listTheory.MEM_FLAT, listTheory.MEM_MAP,
      o1PassContractTheory.fn_insts_blocks_MEM, PULL_EXISTS] >>
     `!ops v. MEM v (venomInst$operand_vars ops) <=> MEM (Var v) ops` by
       (Induct >> simp[venomInstTheory.operand_vars_def] >>
        Cases_on `h` >> simp[venomInstTheory.operand_var_def] >> metis_tac[]) >>
     simp[venomInstTheory.inst_uses_def] >> metis_tac[]) >>
  CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  qexistsl [`[]`,`[]`,`FEMPTY`,`entry_taint`,`f`,`i`,`s`,`q`,`emitted`,
    `0`,`0`,`t`,`FEMPTY`,`entry_taint`,
    `[<|dr_source := FEMPTY; dr_target := FEMPTY; dr_scratch := {}|>]`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qpat_x_assum `set (fn_ir_vars f) = _` (fn th => rewrite_tac[th]) >>
     rewrite_tac[listTheory.MAP] >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[lowerDloadPtrPhaseTheory.dload_prefix_match_def] >>
  simp[NoAsms] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qpat_x_assum `set (fn_ir_vars f) = _` mp_tac >>
     simp[Once pred_setTheory.EXTENSION] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `q'` >> first_assum ACCEPT_TAC
QED

val _ = if null (hyp dload_joint_entry) then ()
  else raise Fail "joint entry: nonempty hypotheses";
