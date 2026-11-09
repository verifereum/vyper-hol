Theory bodyPtrPopTargetSimArrayRun
Ancestors
  bodyPtrPopTargetSimArrayGuard immutableCopySeqPtr immutableRegionLoadPtr
  bodyPtrBopScalarSeq bodyPtrBopScalarCompile stmtAppendStorageRunPtr exprSimArrayIndex
  exprSimCopy instIdxIndep emitHelperProps finite_map pred_set list words
  venomInst venomState compileEnv immutableCopyExecution exprSimStorageCopy
  venomExecSemantics fragExec fragGasSeqPtr ptrDiscipline exprLoweringProps

(* A scalar certificate can be run at every instruction cursor with the
   same ghost endpoints.  Pointer ADDs use emit_add_checked_uniform instead. *)
Theorem target_scalar_emit_uniform:
  emit_op opc ops sa = (dst,sb) /\
  MEM opc [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
           LT; GT; SLT; SGT; EQ; ISZERO; AND; OR; XOR; NOT;
           SHL; SHR; SAR; SIGNEXTEND; BYTE; ASSIGN] /\
  (!op. MEM op ops ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  ~ctx_has_dalloca ctx /\ run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H un. (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
                    (s with vs_inst_idx := k) H un) /\
    op_prov H dst = NONE /\ op_taint un dst = {} /\
    un.t_mem = tn.t_mem /\ un.t_stor = tn.t_stor /\
    un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
                              FLOOKUP un.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >>
  `bop_scalar_seq {x | not_fresh_at sa x} {op | MEM op ops}
     (emitted_insts sa sb) (dst INSERT {op | MEM op ops})` by
    (irule bop_scalar_seq_emit_op >> conj_tac >- simp[] >>
     qexistsl_tac [`opc`, `ops`] >>
     simp[EVERY_MEM]) >>
  drule emitted_insts_emit_op >> strip_tac >> gnvs[] >>
  qmatch_asmsub_abbrev_tac `emitted_insts sa sb = [inst]` >>
  `~is_terminator inst.inst_opcode` by
    (gvs[Abbr `inst`, MEM, mk_inst_def, is_terminator_def]) >>
  `step_inst_base inst s = OK t` by gvs[run_inst_seq_def, AllCaseEqs()] >>
  ho_match_mp_tac scalar_uniform_endpoints >> simp[] >> gen_tac >>
  `run_inst_seq [inst] (s with vs_inst_idx := k) =
      OK (t with vs_inst_idx := k)` by
    simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  drule_all bop_scalar_seq_run >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] mp_tac) >>
  simp[] >> strip_tac >> qexistsl_tac [`G'`, `tn'`] >> simp[]
QED

Theorem target_emit_mul_checked:
  emit_op MUL [left;right] sa = (dst,sb) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_prov G left = NONE /\ op_prov G right = NONE /\
  op_taint tn left = {} /\ op_taint tn right = {} /\ ~ctx_has_dalloca ctx ==>
  ?t H un. copy_runtime_frame sa s sb t /\ copy_old_operand sb dst /\
    eval_operand dst t = SOME (a*b) /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
                   (s with vs_inst_idx := k) H un) /\
    op_prov H dst = NONE /\ op_taint un dst = {} /\
    un.t_mem = tn.t_mem /\ un.t_stor = tn.t_stor /\
    un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
                              op_taint un (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  `step_inst_base (mk_inst sa.cs_next_id MUL [left;right] [out]) s =
      OK (update_var out (a*b) s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def] >>
  `run_inst_seq (emitted_insts sa sb) s = OK (update_var out (a*b) s)` by
    simp[run_inst_seq_def, Abbr `out`] >>
  `!op. MEM op [left;right] ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (rpt strip_tac >> gvs[]) >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `MUL`] target_scalar_emit_uniform)) >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`update_var out (a*b) s`, `H`, `un`] >>
  simp[Abbr `out`, op_taint_def] >>
  conj_tac
  >- (imp_res_tac emit_op_extends >>
      simp[copy_runtime_frame_def, copy_static_def, update_var_def] >>
      rpt strip_tac >>
      `x <> STRING #"%" (toString sa.cs_next_var)` by
        (gvs[not_fresh_at_def] >> metis_tac[]) >>
      simp[lookup_var_def, FLOOKUP_UPDATE]) >>
  simp[copy_old_operand_def, not_fresh_at_def, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem target_emit_add_imm_frame:
  emit_op ADD ops sa = (dst,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s H un ==>
  un.t_imm = tn.t_imm
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  gvs[run_inst_seq_def, inst_seq_ptr_def, AllCaseEqs()] >>
  irule (cj 3 decoderGhostFramePtrTheory.step_taint_nonmemory_frame) >>
  simp[mk_inst_def]
QED

Theorem target_scaled_address_checked:
  emit_op MUL [idx;Lit stride] sa = (off,sm) /\
  emit_op ADD [bop;off] sm = (dst,sb) /\ copy_old_operand sa bop /\
  eval_operand bop s = SOME b /\ eval_operand idx s = SOME i /\
  op_prov G idx = NONE /\ op_taint tn idx = {} /\
  op_taint tn bop = {} /\ ~ctx_has_dalloca ctx ==>
  ?t H un. copy_runtime_frame sa s sb t /\ copy_old_operand sb dst /\
    eval_operand dst t = SOME (b+i*stride) /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
                   (s with vs_inst_idx := k) H un) /\
    op_prov H dst = op_prov G bop /\ op_taint un dst = {} /\
    un.t_mem = tn.t_mem /\ un.t_stor = tn.t_stor /\
    un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
                              op_taint un (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `eval_operand (Lit stride) s = SOME stride /\
   op_prov G (Lit stride) = NONE /\ op_taint tn (Lit stride) = {}` by
    simp[eval_operand_def, op_prov_def, op_taint_def] >>
  drule_all target_emit_mul_checked >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  `eval_operand bop t = SOME b` by metis_tac[copy_runtime_frame_operand] >>
  `op_taint un bop = {} /\ op_prov H bop = op_prov G bop` by
    (Cases_on `bop` >> gvs[copy_old_operand_def, op_taint_def, op_prov_def]) >>
  drule_all emit_add_checked_uniform >>
  disch_then (qspecl_then [`fn`, `PG`, `H`, `D`] strip_assume_tac) >>
  `tf.t_imm = un.t_imm` by
    (`inst_seq_ptr D 0 ctx fn PG H un (emitted_insts sm sb) t Gf tf` by
       (qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ H un _ _ _ _`
          (qspec_then `t.vs_inst_idx` mp_tac) >> simp[]) >>
     `run_inst_seq (emitted_insts sm sb) t = OK (update_var out (b+i*stride) t)` by
       gvs[copy_runtime_frame_def] >>
     drule_all target_emit_add_imm_frame >> simp[]) >>
  qexistsl_tac [`update_var out (b+i*stride) t`, `Gf`, `tf`] >>
  simp[first_prov_def] >>
  `copy_runtime_frame sa s sb (update_var out (b+i*stride) t) /\
   (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
          (s with vs_inst_idx := k) Gf tf)` by
    (irule copy_runtime_uniform_compose >>
     qexistsl_tac [`H`, `sm`, `t`, `un`] >> simp[] >>
     qpat_assum `emit_op MUL _ _ = _` (mp_tac o MATCH_MP emitted_insts_emit_op) >>
     strip_tac >> simp[mk_inst_def, is_terminator_def]) >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- (Cases_on `op_prov G bop` >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (gvs[copy_runtime_frame_def, not_fresh_at_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem target_dynamic_scaled_address_checked:
  emit_op ADD [bop;Lit header] sa = (data,sm) /\
  emit_op MUL [idx;Lit stride] sm = (off,sn) /\
  emit_op ADD [data;off] sn = (dst,sb) /\ copy_old_operand sa idx /\
  eval_operand bop s = SOME b /\ eval_operand idx s = SOME i /\
  op_prov G idx = NONE /\ op_taint tn idx = {} /\
  op_taint tn bop = {} /\ ~ctx_has_dalloca ctx ==>
  ?t H un. copy_runtime_frame sa s sb t /\ copy_old_operand sb dst /\
    eval_operand dst t = SOME ((b+header)+i*stride) /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
                   (s with vs_inst_idx := k) H un) /\
    op_prov H dst = op_prov G bop /\ op_taint un dst = {} /\
    un.t_mem = tn.t_mem /\ un.t_stor = tn.t_stor /\
    un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
                              op_taint un (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `eval_operand (Lit header) s = SOME header /\ op_taint tn (Lit header) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all emit_add_checked_uniform >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] strip_assume_tac) >>
  qabbrev_tac `u = update_var out (b+header) s` >>
  `eval_operand data u = SOME (b+header)` by
    simp[Abbr `u`, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `eval_operand idx u = SOME i` by metis_tac[copy_runtime_frame_operand] >>
  `op_taint tf idx = {} /\ op_prov Gf idx = NONE` by
    (Cases_on `idx` >> gvs[copy_old_operand_def, op_taint_def, op_prov_def]) >>
  drule_all target_scaled_address_checked >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  `tf.t_imm = tn.t_imm` by
    (`inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sm) s Gf tf` by
       (qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ G tn _ _ _ _`
          (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
     `run_inst_seq (emitted_insts sa sm) s = OK u` by gvs[copy_runtime_frame_def] >>
     drule_all target_emit_add_imm_frame >> simp[]) >>
  qexistsl_tac [`t`, `H`, `un`] >>
  `copy_runtime_frame sa s sb t /\
   (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
           (s with vs_inst_idx := k) H un)` by
    (irule copy_runtime_uniform_compose >> qexistsl_tac [`Gf`, `sm`, `u`, `tf`] >>
     simp[] >> qpat_assum `emit_op ADD [bop;Lit header] _ = _`
       (mp_tac o MATCH_MP emitted_insts_emit_op) >>
     strip_tac >> simp[mk_inst_def, is_terminator_def]) >>
  simp[first_prov_def, op_prov_def |> Q.SPEC `G` |> Q.SPEC `Lit header`] >>
  conj_tac >- (Cases_on `op_prov G bop` >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (gvs[copy_runtime_frame_def, not_fresh_at_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem target_array_elem_checked:
  array_elem_ptr bop idx dyn ws esz sa = (dst,sb) /\
  copy_old_operand sa bop /\ copy_old_operand sa idx /\
  eval_operand bop s = SOME b /\ eval_operand idx s = SOME i /\
  op_prov G idx = NONE /\ op_taint tn idx = {} /\
  op_taint tn bop = {} /\ ~ctx_has_dalloca ctx ==>
  ?t H un. copy_runtime_frame sa s sb t /\ copy_old_operand sb dst /\
    eval_operand dst t = SOME ((if dyn then b+n2w ws else b)+i*n2w esz) /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
                   (s with vs_inst_idx := k) H un) /\
    op_prov H dst = op_prov G bop /\ op_taint un dst = {} /\
    un.t_mem = tn.t_mem /\ un.t_stor = tn.t_stor /\
    un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
                              op_taint un (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qpat_x_assum `array_elem_ptr _ _ _ _ _ _ = _` mp_tac >>
  simp[array_elem_ptr_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  Cases_on `dyn` >> gvs[comp_return_def]
  >- (drule_all target_dynamic_scaled_address_checked >> simp[]) >>
  drule_all target_scaled_address_checked >> simp[]
QED

Theorem target_array_elem_opcodes:
  array_elem_ptr bop idx dyn ws esz sa = (dst,sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  simp[array_elem_ptr_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  Cases_on `dyn` >> gvs[comp_return_def] >>
  imp_res_tac emitted_insts_emit_op >>
  gvs[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND, APPEND_ASSOC,
      mk_inst_def, is_terminator_def]
QED

Theorem target_array_elem_path_ptr:
  array_elem_ptr bop idx dyn ws esz sa = (dst,sb) /\
  copy_old_operand sa bop /\ copy_old_operand sa idx /\
  eval_operand bop s = SOME b /\ eval_operand idx s = SOME i /\
  op_prov G idx = NONE /\ op_taint tn idx = {} /\
  op_taint tn bop = {} /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t H un. copy_runtime_frame sa s sb t /\ copy_old_operand sb dst /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H un
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    eval_operand dst t = SOME ((if dyn then b+n2w ws else b)+i*n2w esz) /\
    op_prov H dst = op_prov G bop /\ op_taint un dst = {} /\
    un.t_mem = tn.t_mem /\ un.t_stor = tn.t_stor /\
    un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
                              op_taint un (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all target_array_elem_checked >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`t`, `H`, `un`] >> simp[] >>
  drule target_array_elem_opcodes >> strip_tac >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (simp[listTheory.FILTER_EQ_NIL, EVERY_MEM] >> gvs[EVERY_MEM]) >>
  `inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H un` by
    (first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  `run_inst_seq (emitted_insts sa sb) s = OK t` by gvs[copy_runtime_frame_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by gvs[EVERY_CONJ] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED
