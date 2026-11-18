(* General-context pointer checking and clean ghost transition for MSTORE. *)
Theory augAssignFullMstoreSafety
Ancestors
  ptrSafeRun ptrDiscipline bodyPtrDefs memLocDefs
  fragExec emitHelperProps codegenRel contextCodegenRel
  venomExecSemantics venomInst venomState
  finite_map pred_set list words

Theorem augassign_mstore_ptr_check:
  eval_operand dst s = SOME a /\ eval_operand value s = SOME w /\
  op_taint tn dst = {} /\ op_taint tn value = {} /\
  allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ((?p. dst = Var p /\ ptr_covers G tn p s 32) \/
   (w2n a + 32 <= lo /\ op_prov G dst = NONE)) ==>
  ptr_inst_ok D lo fuel ctx func G tn (mk_inst id MSTORE [dst;value] []) s
Proof
  strip_tac >>
  `step_inst_base (mk_inst id MSTORE [dst;value] []) s =
     OK (mstore (w2n a) w s)` by (irule step_MSTORE >> simp[]) >>
  simp[ptr_inst_ok_def, taint_ok_def, mk_inst_def,
       source_memory_read_ranges_def, step_inst_non_invoke, mstore_def] >>
  simp[access_ok_def, mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, fixed_source_write_range_def,
       mem_write_ops_def] >>
  gvs[ptr_covers_def, eval_operand_def] >> metis_tac[]
QED

Theorem augassign_mstore_clean_transition:
  eval_operand dst s = SOME a /\ eval_operand value s = SOME w /\
  op_taint tn value = {} ==>
  step_prov PG G (mk_inst id MSTORE [dst;value] [])
    (mstore (w2n a) w s) = G /\
  step_taint (mk_inst id MSTORE [dst;value] []) s
    (mstore (w2n a) w s) tn =
    (tn with t_mem := tn.t_mem DIFF {q | w2n a <= q /\ q < w2n a + 32})
Proof
  strip_tac >>
  simp[step_prov_def, set_prov_def, mk_inst_def] >>
  simp[taint_component_equality, step_taint_def, mk_inst_def,
       set_var_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       fixed_source_write_range_def, written_taint_def, range_bytes_def,
       new_site_bytes_def, mstore_def, FLOOKUP_DEF, DRESTRICT_UNIV,
       EXTENSION] >>
  metis_tac[]
QED
