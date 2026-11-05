(* Construct the counted endpoint from the run carrying the frame. *)
Theory bodyIntCallStraightWitness
Ancestors
  fragGasSeq fragGasSeqMem fragGasMode gasSummary fragExec
  exprLoweringProps list rich_list arithmetic bodyIntCallWindowCodeCopy

Theorem compiled_straight_marked_exec:
  fn_has_code sa sb func /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ code /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
              ~is_terminator i.inst_opcode) code /\
  (memory ==> run_inst_seq_mem_ok code s) /\
  run_inst_seq code s = OK t /\
  (!tail. source (es with gas_obs := tail) =
     (res, es_end with gas_obs := tail)) ==>
  gas_marked_exec memory (ctx,func) source (es,s) [] res es_end
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND]) >>
  `FILTER (\i. i.inst_opcode = GAS) code = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\
              ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
  Cases_on `memory`
  >- (`run_inst_seq_mem_ok code s` by fs[] >>
      drule_all run_inst_seq_gas_path_mem >>
      simp[gas_marked_exec_def, gas_marked_path_def, ADD_COMM]) >>
  drule_all tuple_run_inst_seq_gas_path >>
  simp[gas_marked_exec_def, gas_marked_path_def, ADD_COMM]
QED

(* This bounded producer keeps opcode and memory-safety obligations explicit. *)
Theorem loccode_copy_immutable_holds_marked:
  compile_ensure_in_memory src LocCode sz wc cenv.ce_is_ctor
    cenv.ce_imm_alloca sa = (dst,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel ctx func cenv cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  copy_old_operand sa src /\ eval_operand src s = SOME a /\
  (!region. cenv.ce_imm_alloca = SOME region ==> copy_old_operand sa region) /\
  0 < sz /\ sz < dimword (:256) /\ sz MOD 32 = 0 /\
  immutable_holds cenv cx ty raw held es s /\
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
              ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  (memory ==> run_inst_seq_mem_ok (emitted_insts sa sb) s) ==>
  ?t. gas_marked_exec memory (ctx,func) (\e. (INL (),e))
        (es,s) [] (INL ()) es (OK t) /\
      immutable_holds cenv cx ty raw held es t
Proof
  strip_tac >> drule_all loccode_copy_immutable_holds_run >> strip_tac >>
  qexists `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  conj_tac
  >- (irule compiled_straight_marked_exec >>
      simp[] >> qexistsl [`emitted_insts sa sb`, `sa`] >> simp[]) >>
  qpat_x_assum `immutable_holds _ _ _ _ _ _ t` mp_tac >>
  simp[loweringPostsTheory.immutable_holds_def]
QED
