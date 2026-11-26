(* Lift the physical raw-call tuple suffix without choosing new endpoints. *)
Theory bodyRawTupleSuffixPathMods
Ancestors
  exprSimRawCall context emitHelper venomInst venomState words list
  compileEnv[qualified,ignore_grammar] builtinSimple[qualified,ignore_grammar]
  rich_list[qualified,ignore_grammar] ptrDiscipline[qualified,ignore_grammar]
  fragGasSeqPtr fragExecMem allocaHistoryFragment
  stmtReasonLitFragMemory entrySinkExtraction memSafeRun
  exprLoweringProps fragExec fragGasOriginPtr venomMemDefs venomWf
Libs
  monadsyntax

Theorem raw_tuple_suffix_opcode_shape[local]:
  (if n > 0 then
       do z <- emit_op RETURNDATASIZE [];
          cmp <- emit_op LT [z;Lit (n2w n)];
          cap <- compile_select cmp z (Lit (n2w n));
          emit_void MSTORE [ov;cap];
          buf <- compile_alloc_buffer (64 + ((n + 31) DIV 32) * 32);
          emit_void MSTORE [buf.buf_operand;ok];
          dst <- emit_op ADD [buf.buf_operand;Lit 32w];
          emit_void MCOPY [dst;ov;Lit (n2w (32 + ((n + 31) DIV 32) * 32))];
          return buf.buf_operand od
     else return ok) sa = (result,sb) /\ 0 < n ==>
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = [] /\
  EVERY (\i. i.inst_opcode <> DALLOCA) (emitted_insts sa sb)
Proof
  strip_tac >> drule_all raw_call_nonrevert_suffix_code >> strip_tac >>
  qpat_x_assum `(if _ then _ else _) _ = _` kall_tac >>
  gvs[builtinSimpleTheory.compile_select_def, contextTheory.compile_alloc_buffer_def,
      emit_op_def, emit_void_def, compileEnvTheory.fresh_var_def,
      compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def,
      compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
      compileEnvTheory.comp_return_def] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  pure_rewrite_tac[FILTER_EQ_NIL, EVERY_APPEND, EVERY_DEF,
                   emitHelperPropsTheory.mk_inst_opcode] >>
  simp[]
QED

Theorem raw_tuple_suffix_path_at_end:
  (if n > 0 then
       do z <- emit_op RETURNDATASIZE [];
          cmp <- emit_op LT [z;Lit (n2w n)];
          cap <- compile_select cmp z (Lit (n2w n));
          emit_void MSTORE [ov;cap];
          buf <- compile_alloc_buffer (64 + ((n + 31) DIV 32) * 32);
          emit_void MSTORE [buf.buf_operand;ok];
          dst <- emit_op ADD [buf.buf_operand;Lit 32w];
          emit_void MCOPY [dst;ov;Lit (n2w (32 + ((n + 31) DIV 32) * 32))];
          return buf.buf_operand od
     else return ok) sa = (result,sb) /\ 0 < n /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_history func s /\ alloca_inv s /\
  code = emitted_insts sa sb /\ run_inst_seq_mem_ok code s /\
  run_inst_seq code s = OK t /\
  (!D. inst_seq_ptr D lo ctx func PG G tn code s Gf tnf) ==>
  let u = t with vs_inst_idx := LENGTH sb.cs_current_insts in
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func u /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK u,Gf,tnf))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all raw_tuple_suffix_opcode_shape >> strip_tac >>
  drule_all raw_call_nonrevert_suffix_code >> strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++ code` by
    (drule rich_listTheory.IS_PREFIX_IMP_TAKE >>
     disch_then (fn th => simp[emitted_insts_def, Once th, TAKE_DROP])) >>
  drule_all stmtReasonLitFragMemoryTheory.fn_has_code_code >> strip_tac >>
  `s.vs_inst_idx + LENGTH code = LENGTH sb.cs_current_insts` by
    (qpat_assum `sb.cs_current_insts = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `list$isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `s.vs_inst_idx = _` (pure_once_rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `code = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th])) >>
  drule_all entrySinkExtractionTheory.run_inst_seq_preserves_entry_control >> strip_tac >>
  simp_tac bool_ss [venom_state_accessors, LET_THM] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac
  >- (qpat_assum `s.vs_inst_idx + LENGTH code = _` (SUBST1_TAC o SYM) >>
      `EVERY (\i. ~is_terminator i.inst_opcode) code` by
        (qpat_assum `EVERY (\i. _ /\ _) code` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >>
         simp_tac bool_ss [EVERY_MEM] >> metis_tac[]) >>
      qpat_assum `list$isPREFIX code (DROP s.vs_inst_idx _)` mp_tac >>
      simp_tac bool_ss [rich_listTheory.IS_PREFIX_APPEND] >>
      disch_then (qx_choose_then `rest` assume_tac) >>
      irule allocaHistoryFragmentTheory.alloca_history_run_inst_seq >>
      goal_assum (drule_at Any) >> gvs[]) >>
  rpt gen_tac >>
  `(ptrDiscipline$ctx_has_dalloca ctx ==>
    !pre i post u. code = pre ++ i::post /\
      run_inst_seq pre s = OK u ==> unitTransformDefs$dalloca_no_wrap i u)` by
    (rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     qpat_x_assum `EVERY (\i. i.inst_opcode <> DALLOCA) code` mp_tac >>
     qpat_assum `code = _ ++ _` (pure_once_rewrite_tac o single) >>
     simp_tac (srw_ss()) [EVERY_APPEND]) >>
  qpat_assum `!D. inst_seq_ptr D _ _ _ _ _ _ _ _ _ _`
    (qspec_then `D` assume_tac) >>
  drule_all fragGasSeqPtrTheory.run_inst_seq_gas_origin_ptr_path >> simp[]
QED
