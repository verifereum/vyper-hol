(* Live-data dynamic array copying: zero payloads need clean roots, not provenance. *)
Theory typedCopyReturnDynArrayBulkDataPtr
Ancestors
  bodyPtrPopLocalRootFrame assignTuplePtrPrefix annAssignPtrCopy
  assignBasePtrMcopyTransport typedMemoryCopy forPtrBulk
  fragExecPtr ptrSafeRun ptrDiscipline codegenRel contextCodegenRel venomExecSemantics
  venomInst venomState context emitHelper compileEnv words finite_map pred_set

Theorem typed_copy_empty_operand_ok[local]:
  eval_operand count_op s = SOME 0w /\ op_taint tn count_op = {} /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  op_taint tn (Var src) = {} /\ op_taint tn (Var dst) = {} /\
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id MCOPY [Var dst; Var src; count_op] []) s
Proof
  strip_tac >>
  `step_inst fuel ctx (mk_inst id MCOPY [Var dst; Var src; count_op] []) s =
     OK (mcopy (w2n b) (w2n a) 0 s)` by
    (simp[step_inst_non_invoke] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, eval_operand_def]) >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, fixed_source_write_range_def,
       sized_source_write_range_def, eval_operand_def,
       mcopy_def, write_memory_with_expansion_def] >>
  gen_tac >> Cases_on `op = Var dst` >> gvs[] >>
  Cases_on `op = Var src` >> gvs[] >>
  Cases_on `op = count_op` >> gvs[op_taint_def]
QED

Theorem typed_copy_dynamic_operand_counted[local]:
  compile_copy_memory_dynamic (Var dst) (Var src) count_op sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  eval_operand count_op s = SOME n /\ op_taint tn count_op = {} /\
  op_taint tn (Var src) = {} /\ op_taint tn (Var dst) = {} /\
  (n <> 0w ==> ptr_covers G tn src s (w2n n) /\ ptr_covers G tn dst s (w2n n)) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;count_op] [])
      (mcopy (w2n b) (w2n a) (w2n n) s))
    (step_taint (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;count_op] []) s
      (mcopy (w2n b) (w2n a) (w2n n) s) tn)
    (OK ((mcopy (w2n b) (w2n a) (w2n n) s) with
      vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `emit_inst MCOPY [Var dst;Var src;count_op] [] sa = ((),sb)` by
    gvs[compile_copy_memory_dynamic_def,emit_void_def,emit_inst_def] >>
  `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by
    gvs[emit_inst_def,comp_bind_def,fresh_id_def,emit_def] >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;count_op] []) s` by
    (Cases_on `n = 0w`
     >- (irule typed_copy_empty_operand_ok >> gvs[] >> metis_tac[]) >>
     irule ptr_inst_ok_mcopy_operand >> simp[] >> metis_tac[]) >>
  `step_inst_base (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;count_op] []) s =
    OK (mcopy (w2n b) (w2n a) (w2n n) s)` by
    simp[step_inst_base_opcode_eqs,mk_inst_def,eval_operand_def] >>
  drule (SRULE [is_terminator_def] (Q.INST [`opc` |-> `MCOPY`] emit_inst_zero_path_ptr)) >>
  disch_then (drule_at (Pat `ptr_inst_ok _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >> simp[]
QED
