Theory bodyPtrTypeBuiltinsCastOutcome
Ancestors
  bodyPtrTypeBuiltinsCastExecution bodyPtrTypeBuiltinsCastSemantic
  exprSimPtrLiteralBuffer gasSummaryComposePtr gasSummary exprSimDefs
  fragGasPathPtr exprLoweringProps bodyPtrDefs venomState
  bodyPtrTypeBuiltinsCast fragExec

(* The callback receives the actual read-only endpoint, not an assumed run.
   The counted certificate and the semantic result use the same endpoint. *)
Theorem cast_convert_suffix_outcome_ptr:
  compile_type_convert (Var src) (ConvBytestringCast n i) sa = (out,sb) /\
  (tsrc = BaseT (BytesT (Dynamic i)) \/ tsrc = BaseT (StringT i)) /\
  (tdst = BaseT (BytesT (Dynamic n)) \/ tdst = BaseT (StringT n)) /\
  evaluate_type (get_tenv cx) tsrc = SOME tv /\
  evaluate_type (get_tenv cx) tdst = SOME tv2 /\ value_has_type tv v /\
  val_in_memory tv v (w2n w) s.vs_memory /\ lookup_var src s = SOME w /\
  not_fresh_at sa src /\ i < dimword(:256) /\ n < dimword(:256) /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ptr_covers G tn src s sz /\ 32 <= sz /\
  (!j. w2n w <= j /\ j < w2n w + 32 ==> j NOTIN tn.t_mem) /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!p z. cenv.ce_return_buf = SOME (PtrVar (Var p) z) ==> not_fresh_at sa p) /\
  (!p z. cenv.ce_return_pc = SOME (PtrVar (Var p) z) ==> not_fresh_at sa p) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n w) m) /\
  (!t vout H th. run_inst_seq (emitted_insts sa sb) s = OK t /\
    convert_result cx tsrc tdst v = INL vout /\ out = Var src /\
    (t with vs_vars := s.vs_vars) = s /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s) /\
    ghost_inv d cenv cx es H th
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)) /\
    ghost_kept cenv es sa G tn s H th /\
    ptr_covers H th src (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)) sz /\
    th.t_mem = tn.t_mem /\
    (!m. mem_agree_outside th.t_mem t.vs_memory m ==> val_in_memory tv2 vout (w2n w) m) ==>
    Q (INL vout) (es with gas_obs := []) H th
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) ==>
  gas_outcome_ptr D tops (ctx,fn) PG
    (\st. (convert_result cx tsrc tdst v,st)) (es,s,G,tn) Q
    (\res fin gt r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `is_bytestring_type tsrc /\ is_bytestring_type tdst` by
    (fs[compileEnvTheory.is_bytestring_type_def] >> simp[compileEnvTheory.is_bytestring_type_def]) >>
  drule_all cast_compile_typed_outcome >> strip_tac >>
  Cases_on `convert_result cx tsrc tdst v`
  >- (gvs[] >> drule_all convert_cast_converted_counted_certificate >>
      disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
      simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
      simp[gas_summary_ptr_at_def] >>
      qexistsl_tac [`INL x`,`es`,`H`,`th`,
        `OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))`] >>
      simp[] >> first_x_assum irule >> simp[] >>
      simp[SRULE [] (Q.INST [`gs` |-> `es.gas_obs`]
        (SPEC_ALL literal_ptr_ghost_inv_normalize))]) >>
  gvs[] >> drule_all convert_cast_abort_path >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INR (Error (RuntimeError msg))`,`es`,`H`,`th`,
    `Abort Revert_abort (t with vs_inst_idx := j)`] >>
  simp[expr_exit_def, exit_result_def]
QED
