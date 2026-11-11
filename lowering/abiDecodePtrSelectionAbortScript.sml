Theory abiDecodePtrSelectionAbort
Ancestors
  abiDecodePtrHead abiDecodePtrSelectionPrefix abiDecodePtrScalarAbort
  abiDecodePtrContinuation abiDecoderGuard instSeqComposePtr
  emitHelperProps exprLoweringProps emitHelper compileEnv abiEncoder
  bodyPtrBopScalarCompile bodyPtrBopScalarSeq fragExec fragExecPtr
  fragGasSeqPtr bodyPtrDefs ptrDiscipline venomState venomExecSemantics
  venomInst stateFrame instIdxIndep words arithmetic list pred_set finite_map
  bodyPtrBopHashSuffix rich_list exprSimAccounts assignTuplePtrLocalBytesCopy
  stmtReasonLitFragMemory

Theorem abi_decode_getelemptr_abort_ptr:
  compile_getelemptr_abi pos T off MLOAD (Var src) hi sa = (v,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  abi_decode_ptr_window G tn s src b h /\ not_fresh_at sa src /\
  (!x. pos = Var x ==> not_fresh_at sa x) /\
  eval_operand pos s = SOME z /\ op_prov G pos = NONE /\ op_taint tn pos = {} /\
  p = w2n (z + n2w off) /\ p+32 <= h /\ w2n b+h < dimword(:256) /\
  run_inst_seq (emitted_insts sa sb) s = Abort a u ==>
  ?Gf tnf.
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s Gf tnf /\
    (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
              vs_halted := s.vs_halted; vs_returndata := s.vs_returndata|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (?n j. gas_path_ptr D 0 ctx func PG G tn s n Gf tnf
      (Abort a (u with vs_inst_idx := j)))
Proof
  strip_tac >> drule abi_decode_getelemptr_dynamic_split >> strip_tac >>
  `emit_op ADD [Var src;head] c1 = (addr,c2)` by
    fs[compile_abi_dec_addr_def] >>
  `cs_extends sa c1 /\ cs_extends c1 c2 /\ cs_extends c2 c3 /\
   cs_extends c3 mid` by metis_tac[emit_op_extends_next_var] >>
  `inst_extends sa c1 /\ inst_extends c1 c2 /\
   inst_extends c2 c3 /\ inst_extends c3 mid` by
    metis_tac[inst_extends_emit_op] >>
  `inst_extends mid sb` by
    (Cases_on `hi = Lit 0w` >> gvs[]
     >- simp[inst_extends_refl] >> metis_tac[abi_decode_ge_guard_shape]) >>
  `inst_extends sa c3 /\ inst_extends c3 sb` by
    metis_tac[inst_extends_trans] >>
  `same_blocks mid sb` by
    (Cases_on `hi = Lit 0w` >> gvs[] >- simp[same_blocks_def] >>
     fs[abi_decode_ge_guard_def, comp_bind_def] >>
     rpt (pairarg_tac >> gvs[]) >>
     imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
     metis_tac[same_blocks_trans]) >>
  `cs_extends mid sb` by
    (qpat_x_assum `inst_extends mid sb` mp_tac >>
     qpat_x_assum `same_blocks mid sb` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     irule cs_extends_same_block >>
     fs[same_blocks_def, inst_extends_def, IS_PREFIX_APPEND]) >>
  `cs_extends sa c3 /\ cs_extends c3 sb` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code sa c3 func` by metis_tac[fn_has_code_split] >>
  suspend "prefix"
QED

Resume abi_decode_getelemptr_abort_ptr[prefix]:
  `emitted_insts sa sb = emitted_insts sa c3 ++ emitted_insts c3 sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `?B. bop_scalar_seq {x | not_fresh_at c3 x} {pos;offset}
    (emitted_insts c3 sb) B /\ v IN B` by
    (irule abi_decode_position_suffix_scalar >> simp[] >> metis_tac[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa c3) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c3 sb)` by
    (reverse conj_tac
     >- (drule bop_scalar_seq_opcodes >> simp[EVERY_MEM] >> metis_tac[]) >>
     `emitted_insts sa c3 = emitted_insts sa c1 ++
       emitted_insts c1 c2 ++ emitted_insts c2 c3` by
       metis_tac[emitted_insts_append, inst_extends_def, APPEND_ASSOC] >>
     imp_res_tac emitted_insts_emit_op >>
     simp[mk_inst_def, is_terminator_def]) >>
  drule_all abi_decode_selection_prefix_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `eval_operand offset t = SOME (mload (w2n b+p) s)` >>
  qmatch_asmsub_abbrev_tac `inst_seq_ptr D 0 ctx func PG G tn
    (emitted_insts sa c3) s H tm` >>
  `run_inst_seq (emitted_insts c3 sb) t =
     Abort a (u with vs_inst_idx := t.vs_inst_idx)` by
    (irule abi_decode_run_continue_abort_normalized >> simp[] >>
     metis_tac[]) >>
  `!op. op IN {pos;offset} ==> op_prov H op = NONE /\ op_taint tm op = {}` by
    (simp[] >> metis_tac[]) >>
  drule_all scalar_seq_abort_replay_ptr >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  drule_all scalar_seq_abort_runtime_frame >> strip_tac >>
  suspend "compose"
QED

Resume abi_decode_getelemptr_abort_ptr[compose]:
  `t.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sa c3)` by
    (qpat_x_assum `inst_extends sa c3` mp_tac >>
     qpat_x_assum `t.vs_inst_idx = _` mp_tac >>
     qpat_x_assum `s.vs_inst_idx = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[inst_extends_def] >> metis_tac[]) >>
  `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s G' tn'` by
    (qpat_assum `emitted_insts sa sb = _` (fn th => pure_rewrite_tac[th]) >>
     irule inst_seq_ptr_append_run >> conj_tac >- simp[] >>
     qexistsl_tac [`H`, `t with vs_inst_idx := s.vs_inst_idx`, `tm`] >>
     `t with vs_inst_idx := LENGTH (emitted_insts sa c3) + s.vs_inst_idx = t` by
       (simp[venom_state_component_equality] >> decide_tac) >>
     gvs[ADD_COMM]) >>
  qexistsl_tac [`G'`, `tn'`] >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qpat_x_assum `state_frame t = _` mp_tac >>
      qpat_x_assum `(u with <|vs_vars := _; vs_halted := _;
        vs_returndata := _; vs_inst_idx := _|>) = t` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp[state_frame_def, venom_state_component_equality] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at c3 x` by
        (imp_res_tac emit_op_extends_next_var >>
         fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
      qpat_x_assum `!x. not_fresh_at sa x ==> _` (qspec_then `x` mp_tac) >>
      qpat_x_assum `!x. x IN _ ==> FLOOKUP G' x = _ /\ _` (qspec_then `x` mp_tac) >>
      qpat_x_assum `!x. x IN _ ==> FLOOKUP (_ with vs_inst_idx := _).vs_vars x = _`
        (qspec_then `x` mp_tac) >>
      simp[lookup_var_def, op_taint_def] >> metis_tac[]) >>
  simp[] >> suspend "gas"
QED

Resume abi_decode_getelemptr_abort_ptr[gas]:
  `same_blocks sa sb` by
    (map_every (fn pat => qpat_x_assum pat mp_tac)
       [`same_blocks mid sb`, `emit_op ADD [pos; Lit (n2w off)] sa = _`,
        `emit_op ADD [Var src;head] c1 = _`, `emit_op MLOAD [addr] c2 = _`,
        `emit_op ADD [pos;offset] c3 = _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     imp_res_tac emit_op_extends >> metis_tac[same_blocks_trans]) >>
  `inst_extends sa sb` by metis_tac[inst_extends_trans] >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   sb.cs_current_bb = sa.cs_current_bb` by
    (qpat_x_assum `inst_extends sa sb` mp_tac >>
     qpat_x_assum `same_blocks sa sb` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[inst_extends_def, same_blocks_def]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (drule_all fn_has_code_code >> simp[] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by
    (`emitted_insts sa c3 = emitted_insts sa c1 ++
       emitted_insts c1 c2 ++ emitted_insts c2 c3` by
       metis_tac[emitted_insts_append, inst_extends_def, APPEND_ASSOC] >>
     drule bop_scalar_seq_opcodes >> strip_tac >>
     imp_res_tac emitted_insts_emit_op >> fs[EVERY_CONJ]) >>
  drule_all run_inst_seq_abort_gas_path_ptr >> simp[]
QED

Finalise abi_decode_getelemptr_abort_ptr
