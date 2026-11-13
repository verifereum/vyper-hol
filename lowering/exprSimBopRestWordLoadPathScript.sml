(* Shared protected, read-only straight-line execution boundary. *)
Theory exprSimBopRestWordLoadPath
Ancestors
  emitHelper compileEnv context fragGasSeq fragGasPath emitHelperProps venomExecSemantics venomState
  venomInst list rich_list finite_map arithmetic

Theorem rest_word_readonly_sequence_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
              ~is_terminator i.inst_opcode) code /\
  run_inst_seq code s = OK t /\
  (!i u v. MEM i code /\ step_inst_base i u = OK v ==>
     v = u with vs_vars := v.vs_vars /\
     (!x. P x ==> FLOOKUP v.vs_vars x = FLOOKUP u.vs_vars x)) ==>
  let u = t with vs_inst_idx := s.vs_inst_idx + LENGTH code in
  gas_path ctx func s 0 (OK u) /\
  u = s with <|vs_vars := t.vs_vars;
                vs_inst_idx := s.vs_inst_idx + LENGTH code|> /\
  (!x. P x ==> FLOOKUP u.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
    gvs[EVERY_MEM] >>
  `FILTER (\i. i.inst_opcode = GAS) code = []` by
    gvs[FILTER_EQ_NIL, EVERY_MEM] >>
  drule_all tuple_run_inst_seq_gas_path >> simp[] >> strip_tac >>
  drule_all run_inst_seq_protected_frame >> strip_tac >>
  simp[] >>
  qpat_x_assum `t = _` (fn th => simp[Once th])
QED

Theorem rest_word_step_load_frame:
  MEM inst.inst_opcode [MLOAD; SLOAD; TLOAD; ILOAD; DLOAD] /\
  step_inst_base inst s = OK t ==>
  t = s with vs_vars := t.vs_vars /\
  !x. ~MEM x inst.inst_outputs ==>
      FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x
Proof
  simp[] >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
  simp[exec_read1_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  simp[update_var_def, FLOOKUP_UPDATE, venom_state_component_equality]
QED

Theorem rest_word_emit_load_run:
  emit_op opc [addr] sa = (op,sb) /\
  MEM opc [MLOAD; SLOAD; TLOAD; ILOAD; DLOAD] /\
  eval_operand addr s = SOME a /\
  value = (case opc of
      SLOAD => sload a s
    | TLOAD => tload a s
    | DLOAD => word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))
    | _ => mload (w2n a) s) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME value
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  gvs[] >>
  simp[exprLoweringPropsTheory.run_inst_seq_def, mk_inst_def, step_inst_base_opcode_eqs,
       exec_read1_def, eval_operand_def, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE]
QED

Theorem rest_word_staged_load_run:
  compile_imm_load_word T (SOME region) addr sa = (op,sb) /\
  eval_operand addr s = SOME a /\ eval_operand region s = SOME b ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME (mload (w2n (a+b)) s)
Proof
  simp[compile_imm_load_word_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_var_def,
       fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  simp[exprLoweringPropsTheory.emitted_insts_def] >>
  once_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND] >>
  qspecl_then [`addr`, `region`, `a`, `b`] mp_tac step_ADD >>
  simp[] >> strip_tac >>
  simp[exprLoweringPropsTheory.run_inst_seq_def] >>
  simp[mk_inst_def, step_inst_base_opcode_eqs, exec_read1_def,
       eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       mload_def]
QED

Theorem rest_word_ptr_load_run:
  compile_ptr_load ctor imm loc addr sa = (op,sb) /\
  loc <> LocCalldata /\ eval_operand addr s = SOME a /\
  (loc = LocCode /\ ctor /\ imm <> NONE ==>
     eval_operand (THE imm) s = SOME b) /\
  value = (case loc of
      LocStorage => sload a s
    | LocTransient => tload a s
    | LocCode => if ctor then
          mload (w2n (if imm = NONE then a else a+b)) s
        else word_of_bytes T (0w:bytes32)
          (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))
    | _ => mload (w2n a) s) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME value
Proof
  Cases_on `loc` >> simp[compile_ptr_load_def] >> rpt strip_tac
  >- (drule rest_word_emit_load_run >> simp[] >>
      disch_then (qspec_then `a` mp_tac) >> simp[])
  >- (drule rest_word_emit_load_run >> simp[] >>
      disch_then (qspec_then `a` mp_tac) >> simp[])
  >- (drule rest_word_emit_load_run >> simp[] >>
      disch_then (qspec_then `a` mp_tac) >> simp[]) >>
  reverse (Cases_on `ctor`)
  >- (gvs[compile_imm_load_word_def] >>
      drule rest_word_emit_load_run >> simp[] >>
      disch_then (qspec_then `a` mp_tac) >> simp[]) >>
  Cases_on `imm` >> gvs[compile_imm_load_word_def]
  >- (drule rest_word_emit_load_run >> simp[] >>
      disch_then (qspec_then `a` mp_tac) >> simp[]) >>
  irule rest_word_staged_load_run >> simp[compile_imm_load_word_def] >>
  metis_tac[]
QED

Theorem rest_word_ptr_load_code:
  compile_ptr_load ctor imm loc addr sa = (op,sb) /\
  loc <> LocCalldata ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; SLOAD; TLOAD; ILOAD; DLOAD])
    (emitted_insts sa sb)
Proof
  Cases_on `loc` >> Cases_on `ctor` >> Cases_on `imm` >>
  simp[compile_ptr_load_def, compile_imm_load_word_def, emit_op_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  simp[exprLoweringPropsTheory.emitted_insts_def] >>
  once_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, EVERY_DEF]
QED

Theorem rest_word_ptr_load_run_frame:
  compile_ptr_load ctor imm loc addr sa = (op,sb) /\
  loc <> LocCalldata /\ run_inst_seq (emitted_insts sa sb) s = OK t ==>
  t = s with vs_vars := t.vs_vars /\
  (!x. (!i. MEM i (emitted_insts sa sb) ==> ~MEM x i.inst_outputs) ==>
       FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  strip_tac >> drule_all rest_word_ptr_load_code >> strip_tac >>
  ho_match_mp_tac run_inst_seq_protected_frame >>
  qexists `emitted_insts sa sb` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `MEM i.inst_opcode [ADD; MLOAD; SLOAD; TLOAD; ILOAD; DLOAD]` by
    (qpat_assum `EVERY (\i. MEM _ _) _` mp_tac >>
     pure_rewrite_tac[EVERY_MEM] >> disch_then (qspec_then `i` mp_tac) >> simp[]) >>
  Cases_on `i.inst_opcode = ADD`
  >- (qspec_then `i` mp_tac step_pure_opcode_frame >> simp[] >>
      disch_then drule >> strip_tac >> metis_tac[]) >>
  `MEM i.inst_opcode [MLOAD; SLOAD; TLOAD; ILOAD; DLOAD]` by fs[] >>
  drule_all rest_word_step_load_frame >> strip_tac >> metis_tac[]
QED

Theorem rest_word_ptr_load_path:
  compile_ptr_load ctor imm loc addr sa = (op,sb) /\
  loc <> LocCalldata /\ fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  eval_operand op t = SOME value ==>
  ?u. gas_path ctx func s 0 (OK u) /\
      eval_operand op u = SOME value /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      u = s with <|vs_vars := u.vs_vars;
                   vs_inst_idx := LENGTH sb.cs_current_insts|> /\
      (!x. (!i. MEM i (emitted_insts sa sb) ==> ~MEM x i.inst_outputs) ==>
           FLOOKUP u.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  strip_tac >> drule_all rest_word_ptr_load_code >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fragExecTheory.fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
               ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i _ ==> _` (qspec_then `i` mp_tac) >>
     simp[] >> rpt strip_tac >> gvs[is_terminator_def]) >>
  drule_all rest_word_ptr_load_run_frame >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    gvs[EVERY_MEM, FILTER_EQ_NIL] >>
  drule_all tuple_run_inst_seq_gas_path >> simp[] >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `LENGTH sb.cs_current_insts =
   s.vs_inst_idx + LENGTH (emitted_insts sa sb)` by simp[] >>
  qpat_x_assum `!ctx. gas_path _ _ _ _ _` (qspec_then `ctx` mp_tac) >>
  Cases_on `op` >>
  gvs[eval_operand_def, lookup_var_def, venom_state_component_equality]
QED
