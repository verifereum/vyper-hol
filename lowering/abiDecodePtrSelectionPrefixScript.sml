(* Constructive checked prefix shared by selection success and abort. *)
Theory abiDecodePtrSelectionPrefix
Ancestors
  abiDecodePtrRead abiDecodePtrNormalized abiEncoderWindowSequence
  exprSimAccounts bodyPtrBopHashSuffix assignTuplePtrLocalBytesCopy
  bodyPtrBopScalarCompile bodyPtrBopScalarSeq abiDecodePtrMemberFrame
  emitHelperProps exprLoweringProps emitHelper compileEnv abiEncoder
  bodyPtrDefs ptrDiscipline venomState venomExecSemantics venomInst stateFrame
  fragGasSeqPtr fragExecPtr fragExec words arithmetic list pred_set finite_map

Theorem abi_decode_selection_prefix_ptr:
  emit_op ADD [pos; Lit (n2w off)] sa = (head,c1) /\
  compile_abi_dec_addr (Var src) head c1 = (addr,c2) /\
  emit_op MLOAD [addr] c2 = (offset,c3) /\
  fn_has_code sa c3 func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  abi_decode_ptr_window G tn s src b h /\ not_fresh_at sa src /\
  (!x. pos = Var x ==> not_fresh_at sa x) /\
  eval_operand pos s = SOME z /\ op_prov G pos = NONE /\ op_taint tn pos = {} /\
  p = w2n (z + n2w off) /\ p+32 <= h /\ w2n b+h < dimword(:256) ==>
  ?t H tm. run_inst_seq (emitted_insts sa c3) s =
      OK (t with vs_inst_idx := s.vs_inst_idx) /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa c3) s H tm /\
    t.vs_inst_idx = LENGTH c3.cs_current_insts /\
    eval_operand pos t = SOME z /\
    eval_operand offset t = SOME (mload (w2n b+p) s) /\
    op_prov H pos = NONE /\ op_taint tm pos = {} /\
    op_prov H offset = NONE /\ op_taint tm offset = {} /\
    ~t.vs_halted /\ t.vs_current_bb = c3.cs_current_bb /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_call_ctx = s.vs_call_ctx /\
    state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `emit_op ADD [Var src;head] c1 = (addr,c2)` by
    fs[compile_abi_dec_addr_def] >>
  `cs_extends sa c1 /\ sa.cs_next_var <= c1.cs_next_var /\
   cs_extends c1 c2 /\ c1.cs_next_var <= c2.cs_next_var /\
   cs_extends c2 c3 /\ c2.cs_next_var <= c3.cs_next_var` by
    metis_tac[emit_op_extends_next_var] >>
  `fn_has_code sa c1 func /\ fn_has_code c1 c3 func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `inst_extends sa c1 /\ same_blocks sa c1` by
    metis_tac[inst_extends_emit_op, emit_op_extends] >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off)` by simp[eval_operand_def] >>
  qpat_assum `emit_op ADD [pos; Lit (n2w off)] sa = _`
    (mp_then Any mp_tac window_emit_add_pure) >>
  disch_then (qspec_then `s` mp_tac) >> simp[] >>
  strip_tac >> rename1 `window_pure_seq sa c1 s raw` >>
  qabbrev_tac `s1 = raw with vs_inst_idx := LENGTH c1.cs_current_insts` >>
  `s1.vs_inst_idx = LENGTH c1.cs_current_insts /\
   run_inst_seq (emitted_insts sa c1) s = OK (s1 with vs_inst_idx := s.vs_inst_idx)` by
    fs[window_pure_seq_def, window_seq_def, Abbr `s1`, venom_state_component_equality] >>
  `bop_scalar_seq {x | not_fresh_at sa x} {pos; Lit (n2w off)}
    (emitted_insts sa c1) (head INSERT {pos; Lit (n2w off)})` by
    (irule bop_scalar_seq_emit_op >> simp[] >>
     qexistsl_tac [`ADD`, `[pos; Lit (n2w off)]`] >> simp[]) >>
  `!op. op IN {pos; Lit (n2w off)} ==>
    op_prov G op = NONE /\ op_taint tn op = {}` by
    (rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  drule_all abi_decode_scalar_compile_replay_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `inst_seq_ptr D 0 ctx func PG G tn
    (emitted_insts sa c1) s H1 tm1` >>
  suspend "load"
QED

Resume abi_decode_selection_prefix_ptr[load]:
  `s1.vs_memory = s.vs_memory /\ s1.vs_halted = s.vs_halted /\
   s1.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `s1 = s with <|vs_vars := _; vs_inst_idx := _|>` mp_tac >>
     simp[venom_state_component_equality]) >>
  `abi_decode_ptr_window H1 tm1 s1 src b h` by
    (qpat_x_assum `!x. x IN {x | not_fresh_at sa x} ==> _`
       (qspec_then `src` mp_tac) >> simp[] >> strip_tac >>
     gvs[abi_decode_ptr_window_def, ptr_covers_def, op_taint_def]) >>
  `eval_operand head s1 = SOME (n2w p)` by
    simp[Abbr `s1`, eval_operand_def] >>
  `~s1.vs_halted /\ s1.vs_current_bb = c1.cs_current_bb /\ op_taint tm1 head = {}` by
    (fs[same_blocks_def] >> metis_tac[IN_INSERT]) >>
  drule_all abi_decode_ptr_relative_load >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `inst_seq_ptr D 0 ctx func PG H1 tm1
    (emitted_insts c1 c3) s1 H2 tm2` >>
  suspend "compose"
QED

Resume abi_decode_selection_prefix_ptr[compose]:
  `inst_extends c1 c3` by
    metis_tac[inst_extends_emit_op, inst_extends_trans] >>
  `emitted_insts sa c3 = emitted_insts sa c1 ++ emitted_insts c1 c3` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `emitted_insts c1 c3 = emitted_insts c1 c2 ++ emitted_insts c2 c3` by
    (irule emitted_insts_append >> metis_tac[inst_extends_emit_op, inst_extends_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa c1) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c1 c3)` by
    (imp_res_tac emitted_insts_emit_op >>
     simp[mk_inst_def, is_terminator_def]) >>
  `s1.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sa c1) /\
   t.vs_inst_idx = s1.vs_inst_idx + LENGTH (emitted_insts c1 c3)` by
    fs[inst_extends_def] >>
  drule_all inst_seq_ptr_append_normalized >> strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at c1 x` by
    (fs[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP H2 x = FLOOKUP G x /\ op_taint tm2 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     qpat_x_assum `!x. not_fresh_at c1 x ==> _` (qspec_then `x` mp_tac) >>
     qpat_x_assum `!x. x IN {x | not_fresh_at sa x} ==> _` (qspec_then `x` mp_tac) >>
     simp[op_taint_def] >> metis_tac[]) >>
  suspend "operands"
QED

Resume abi_decode_selection_prefix_ptr[operands]:
  `state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx)` by
    (qpat_x_assum `state_frame t = _` mp_tac >>
     qpat_x_assum `s1 = s with <|vs_vars := _; vs_inst_idx := _|>` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[state_frame_def, venom_state_component_equality]) >>
  `op_prov H2 pos = NONE /\ op_taint tm2 pos = {}` by
    (Cases_on `pos` >> simp[op_prov_def, op_taint_def] >>
     rename1 `op_prov G (Var var) = NONE` >>
     qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x t = _ /\ _`
       (qspec_then `var` mp_tac) >>
     qpat_x_assum `op_prov G (Var var) = NONE` mp_tac >>
     qpat_x_assum `op_taint tn (Var var) = {}` mp_tac >>
     `not_fresh_at sa var` by fs[] >>
     pop_assum mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[op_prov_def, op_taint_def] >> metis_tac[]) >>
  `eval_operand pos t = SOME z` by
    (Cases_on `pos`
     >- fs[eval_operand_def]
     >- (rename1 `eval_operand (Var var) s = SOME z` >>
         qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x t = _ /\ _`
           (qspec_then `var` mp_tac) >>
         `not_fresh_at sa var` by fs[] >>
         qpat_x_assum `eval_operand (Var var) s = SOME z` mp_tac >>
         pop_assum mp_tac >>
         simp[eval_operand_def] >> metis_tac[]) >>
     qpat_x_assum `state_frame t = state_frame (s with vs_inst_idx := _)` mp_tac >>
     qpat_x_assum `eval_operand _ s = SOME z` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[state_frame_def, eval_operand_def]) >>
  qexistsl_tac [`t`, `H2`, `tm2`] >>
  simp[eval_operand_def, mload_def] >>
  qpat_x_assum `s1 = s with <|vs_vars := _; vs_inst_idx := _|>` mp_tac >>
  qpat_x_assum `state_frame t = state_frame (s with vs_inst_idx := _)` mp_tac >>
  simp[NoAsms, state_frame_def, venom_state_component_equality] >>
  gvs[]
QED

Finalise abi_decode_selection_prefix_ptr
