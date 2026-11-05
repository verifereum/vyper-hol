(* Explicit msg.gas: one checked GAS edge and the unchanged S1 frame. *)
Theory bodyPtrEnvBuiltinsGas
Ancestors
  bodyPtrEnvBuiltinsScalar bodyPtrEnvBuiltinsEdges bodyPtrDefs bodyPtrPreds
  msgGasSim msgGasPost fragGasPathPtr fragGasSeqPtr gasSummary
  ptrDiscipline ptrSafeRun emitHelper emitHelperProps exprLoweringProps
  compileEnv exprLowering exprPtrUnwrap exprSimProps stmtFragPtr
  venomInst venomState venomExecSemantics finite_map pred_set list rich_list
  vyperAST vyperTypeSystem vyperValue valueEncoding codegenRel

Theorem gas_builtin_base_step:
  ?w. gas_prefix 1 s.vs_gas_readings = [w] /\
      step_inst_base (mk_inst id GAS [] [out]) s =
        OK (update_var out w (s with vs_gas_readings := DROP 1 s.vs_gas_readings))
Proof
  Cases_on `s.vs_gas_readings`
  >- (qexists_tac `0w` >>
      simp[gasOracleReplayTheory.gas_prefix_def,
       Once (numLib.num_CONV ``1``), TAKE_def, REPLICATE,
           step_inst_base_opcode_eqs, exec_gas_def, mk_inst_def] >>
      gvs[update_var_def, venom_state_component_equality] >> EVAL_TAC) >>
  qexists_tac `h` >>
  simp[gasOracleReplayTheory.gas_prefix_def,
       Once (numLib.num_CONV ``1``), TAKE_def, REPLICATE,
       step_inst_base_opcode_eqs, exec_gas_def, mk_inst_def] >> EVAL_TAC
QED

Theorem gas_builtin_ghosts:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~not_fresh_at sa out ==>
  !t. t = update_var out w (s with vs_gas_readings := gs) ==>
  ghost_inv d cenv cx es
    (step_prov PG G (mk_inst id GAS [] [out]) t)
    (step_taint (mk_inst id GAS [] [out]) s t tn) t /\
  ghost_kept cenv es sa G tn s
    (step_prov PG G (mk_inst id GAS [] [out]) t)
    (step_taint (mk_inst id GAS [] [out]) s t tn)
Proof
  strip_tac >> gen_tac >> strip_tac >>
  `(step_taint (mk_inst id GAS [] [out]) s t tn).t_mem = tn.t_mem` by
    (irule step_taint_no_memory_effect >>
     simp[source_memory_write_ranges_def, written_taint_def, mk_inst_def] >>
     gvs[update_var_def]) >>
  conj_tac
  >- (irule single_output_ghost_inv >> simp[] >>
      qexists_tac `sa` >> simp[] >>
      gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> IF_CASES_TAC >> gvs[]) >>
  irule single_output_ghost_kept >> simp[ghost_kept_refl]
QED

Theorem ghost_inv_gas_readings[simp]:
  ghost_inv d cenv cx es G tn (s with vs_gas_readings := gs) <=>
  ghost_inv d cenv cx es G tn s
Proof
  Cases_on `d` >- simp[ghost_inv_def, ptr_covers_def, return_buf_ptr_def, stor_taint_ok_def,
                        lookup_var_def] >>
  PairCases_on `x` >>
  simp[ghost_inv_def, ptr_covers_def, return_buf_ptr_def,
       stor_taint_ok_def, lookup_var_def]
QED

