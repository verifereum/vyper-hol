(* The concrete instruction boundary of the constructor store probe. *)
Theory bodyFullImmutableStoreRunProbe
Ancestors
  exprPtrCtorImmStore exprPtrUnwrapScalarEdges
  bodyFullImmutableStoreProbe fragGasSeqPtr bodyFullUnwrapRun immutableWordExecution
  context exprLoweringProps bodyPtrDefs loweringPosts stmtSimDefs loweringStateRelDefs
  ptrDiscipline ptrSafeRun codegenRel contextCodegenRel memLocDefs
  venomState venomExecSemantics venomInstProofs venomInst fragExec fragExecMem
  unitTransformDefs memSafeRun
  compileEnv emitHelper list finite_map pred_set arithmetic words

Theorem immutable_istore_mem_run:
  eval_operand addr s = SOME a /\ eval_operand op s = SOME w /\
  w2n a + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok [mk_inst iid ISTORE [addr;op] []] s
Proof
  simp[run_inst_seq_mem_ok_def, inst_mem_below_frontier_def,
       inst_dload_in_section_def, mk_inst_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, fixed_source_write_range_def,
       step_inst_base_opcode_eqs, exec_write2_def]
QED

Theorem immutable_istore_ptr_run:
  eval_operand addr s = SOME a /\ eval_operand op s = SOME w /\
  op_prov G addr = NONE /\ op_taint tn addr = {} /\ op_taint tn op = {} /\
  w2n a + 32 <= lo /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  run_inst_seq [mk_inst iid ISTORE [addr;op] []] s = OK (istore (w2n a) w s) /\
  inst_seq_ptr D lo ctx fn PG G tn [mk_inst iid ISTORE [addr;op] []] s G
    (tn with <|t_mem := tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32};
               t_imm := key_update tn.t_imm (w2n a) {}|>)
Proof
  strip_tac >>
  `ptr_inst_ok D lo 0 ctx fn G tn (mk_inst iid ISTORE [addr;op] []) s` by
    (irule ptr_inst_ok_istore >> simp[]) >>
  mp_tac (Q.INST [`addr` |-> `addr`, `op` |-> `op`, `a` |-> `a`,
    `w` |-> `w`, `s` |-> `s`, `tn` |-> `tn`, `iid` |-> `iid`,
    `PG` |-> `PG`, `G` |-> `G`] (SPEC_ALL immutable_istore_execution)) >>
  simp[] >> strip_tac >> simp[inst_seq_ptr_def] >>
  fs[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def]
QED

Theorem immutable_istore_origin_ptr_path:
  fn_has_code sb sc func /\ sc.cs_current_bb = sb.cs_current_bb /\
  sc.cs_current_insts = sb.cs_current_insts ++ [mk_inst iid ISTORE [addr;op] []] /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  eval_operand addr s = SOME a /\ eval_operand op s = SOME w /\
  op_prov G addr = NONE /\ op_taint tn addr = {} /\ op_taint tn op = {} /\
  w2n a + 32 <= lo /\ lo <= s.vs_alloca_next /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK ((istore (w2n a) w s) with vs_inst_idx := LENGTH sc.cs_current_insts),G,
     tn with <|t_mem := tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32};
               t_imm := key_update tn.t_imm (w2n a) {}|>)
Proof
  strip_tac >>
  `run_inst_seq_mem_ok [mk_inst iid ISTORE [addr;op] []] s` by
    metis_tac[immutable_istore_mem_run, LESS_EQ_TRANS] >>
  `run_inst_seq [mk_inst iid ISTORE [addr;op] []] s = OK (istore (w2n a) w s) /\
   inst_seq_ptr D lo ctx func PG G tn [mk_inst iid ISTORE [addr;op] []] s G
     (tn with <|t_mem := tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32};
                t_imm := key_update tn.t_imm (w2n a) {}|>)` by
    (irule immutable_istore_ptr_run >> simp[]) >>
  irule emitted_origin_ptr_path >> asm_rewrite_tac[] >>
  qexistsl_tac [`[mk_inst iid ISTORE [addr;op] []]`, `sb`] >>
  simp[mk_inst_def, is_terminator_def]
QED


Theorem immutable_ctor_word_pair_ptr_run:
  eval_operand region s = SOME 0w /\ eval_operand off s = SOME a /\
  eval_operand op s = SOME w /\ op <> Var tmp /\
  op_prov G region = NONE /\ op_prov G off = NONE /\
  op_taint tn region = {} /\ op_taint tn off = {} /\ op_taint tn op = {} /\
  w2n a + 32 <= lo /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  u = update_var tmp a s /\
  G1 = step_prov PG G (mk_inst iid ADD [region;off] [tmp]) u /\
  tn1 = step_taint (mk_inst iid ADD [region;off] [tmp]) s u tn ==>
  run_inst_seq [mk_inst iid ADD [region;off] [tmp];
    mk_inst (iid+1) ISTORE [Var tmp;op] []] s = OK (istore (w2n a) w u) /\
  inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst iid ADD [region;off] [tmp];
     mk_inst (iid+1) ISTORE [Var tmp;op] []] s G1
    (tn1 with <|t_mem := tn1.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32};
                t_imm := key_update tn1.t_imm (w2n a) {}|>)
Proof
  strip_tac >>
  `step_inst_base (mk_inst iid ADD [region;off] [tmp]) s = OK u` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, WORD_ADD_0] >>
  `ptr_inst_ok D lo 0 ctx fn G tn (mk_inst iid ADD [region;off] [tmp]) s` by
    (irule ptr_inst_ok_copy_arith >> simp[]) >>
  `op_prov G1 (Var tmp) = NONE` by
    (gvs[] >> irule step_prov_out_none >> simp[mk_inst_def] >>
     irule out_prov_arith_none >> simp[mk_inst_def]) >>
  `op_taint tn1 (Var tmp) = {}` by
    simp[step_taint_def, op_taint_def, set_var_taint_def, out_taint_def,
         mk_inst_def, FLOOKUP_UPDATE] >>
  `op_taint tn1 op = {}` by
    (Cases_on `op` >> gvs[step_taint_def, op_taint_def, set_var_taint_def,
       out_taint_def, mk_inst_def, FLOOKUP_UPDATE]) >>
  `eval_operand op u = SOME w` by
    (Cases_on `op` >>
     gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `run_inst_seq [mk_inst (iid+1) ISTORE [Var tmp;op] []]
       (u with vs_inst_idx := SUC s.vs_inst_idx) =
       OK (istore (w2n a) w (u with vs_inst_idx := SUC s.vs_inst_idx)) /\
   inst_seq_ptr D lo ctx fn PG G1 tn1 [mk_inst (iid+1) ISTORE [Var tmp;op] []]
       (u with vs_inst_idx := SUC s.vs_inst_idx) G1
       (tn1 with <|t_mem := tn1.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32};
                   t_imm := key_update tn1.t_imm (w2n a) {}|>)` by
    (irule immutable_istore_ptr_run >>
     simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
          allocas_from_def, allocas_below_fmp_def] >>
     Cases_on `op` >> gvs[eval_operand_def, lookup_var_def] >>
     fs[allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `u = _` SUBST_ALL_TAC >>
      irule immutable_word_ctor_store >> asm_rewrite_tac[]) >>
  once_rewrite_tac[inst_seq_ptr_def] >> asm_rewrite_tac[] >> gvs[]
QED
