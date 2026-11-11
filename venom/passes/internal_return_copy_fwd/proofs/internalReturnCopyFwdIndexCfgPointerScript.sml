Theory internalReturnCopyFwdIndexCfgPointer
Ancestors
  internalReturnCopyFwdIndexCfgProbe internalReturnCopyFwdIndexPointer
  internalReturnCopyFwdIndexProbe
  ptrSafeRun ptrDiscipline pointerConfinedDefs venomExecSemantics venomState
  venomInst finite_map words list memLocDefs unitShapeDefs venomWf
  relation contextCodegenRel codegenRel

Theorem ircf_index_cfg_pointer_roots:
  ptr_roots ircf_index_pointer_params ircf_index_cfg_fn = {"%src"; "%dst"} /\
  alloca_roots ircf_index_cfg_fn = {"%src"; "%dst"}
Proof
  simp[ptr_roots_def, alloca_roots_def, ircf_index_cfg_fn_def,
    ircf_index_cfg_entry_def, ircf_index_cfg_return_def,
    ircf_index_changed_def, mk_raw_function_def, fn_insts_def,
    fn_insts_blocks_def, mk_inst_def, inst_output_def,
    ircf_index_pointer_params_def, EXISTS_OR_THM] >>
  simp[venomInstTheory.EXISTS_instruction, pred_setTheory.EXTENSION,
       DISJ_IMP_THM, EXISTS_OR_THM] >> dsimp[]
QED

Theorem ircf_index_cfg_pointer_derived:
  pointer_derived_vars ircf_index_cfg_fn {} = {} /\
  fn_pv ircf_index_pointer_params ircf_index_cfg_fn = {"%src"; "%dst"}
Proof
  conj_tac >> simp[fn_pv_def, ircf_index_cfg_pointer_roots,
    pointer_derived_vars_def] >> EVAL_TAC >>
  pure_once_rewrite_tac[WhileTheory.OWHILE_THM] >> simp[] >>
  pure_once_rewrite_tac[WhileTheory.OWHILE_THM] >> simp[SET_TO_LIST_INV]
QED

Theorem ircf_index_cfg_pointer_fn_ok:
  fn_ptr_ok ircf_index_pointer_params ircf_index_cfg_fn
Proof
  simp[fn_ptr_ok_def, ircf_index_cfg_pointer_roots,
       ircf_index_cfg_pointer_derived] >>
  simp[ircf_index_cfg_fn_def, ircf_index_cfg_entry_def,
    ircf_index_cfg_return_def, ircf_index_changed_def, mk_raw_function_def,
    fn_insts_def, fn_insts_blocks_def, mk_inst_def] >>
  simp[DISJ_IMP_THM, FORALL_AND_THM, ptr_use_ok_def,
    affine_pointer_ops_def, phi_pv_all_var_def, is_pointer_preserving_op_def,
    mem_write_ops_def, mem_read_ops_def, inst_output_def,
    ircf_index_pointer_params_def, decode_invoke_def] >>
  rpt strip_tac >> gvs[] >> EVAL_TAC >> simp[EXISTS_inst_access_ops]
QED

Definition ircf_index_cfg_dead_def:
  ircf_index_cfg_dead = <|d_stor := (\a st. {}); d_trans := (\a st. {});
                         d_imm := (\im. {}); d_ret := (\r. {})|>
End

Theorem ircf_index_cfg_dead_wf:
  dead_wf ircf_index_cfg_dead
Proof
  simp[dead_wf_def, ircf_index_cfg_dead_def]
QED

Theorem ircf_index_cfg_safe_run:
  !fuel q. ptr_safe_blocks ircf_index_cfg_dead 0 fuel ircf_index_cfg_ctx
    ircf_index_main [] FEMPTY entry_taint
    ((ircf_index_state q) with
      <|vs_prev_bb := NONE; vs_current_bb := "main"; vs_inst_idx := 0|>)
Proof
  Cases >> simp[Once ptr_safe_blocks_def] >> gen_tac >> EVAL_TAC >>
  simp[] >> Cases_on `n` >> gvs[] >> EVAL_TAC >> simp[] >>
  conj_tac >- (Cases >> simp[]) >>
  Cases_on `n' = 0` >> simp[]
QED

Theorem ircf_index_cfg_pointer_discipline:
  ptr_discipline 0 ircf_index_cfg_ctx (ircf_index_state q) /\
  taint_within ircf_index_cfg_dead ircf_index_cfg_ctx (ircf_index_state q)
Proof
  irule ptr_safe_ptr_discipline >>
  simp[] >> conj_tac
  >- (qexistsl_tac [`ircf_index_main`, `"main"`, `"main"`] >>
      conj_tac >- simp[ircf_index_cfg_safe_run] >> EVAL_TAC) >>
  conj_tac >- EVAL_TAC >>
  qexists_tac `ircf_index_pointer_params` >>
  simp[ircf_index_cfg_ctx_def, ircf_index_pointer_fn_ok,
       ircf_index_cfg_pointer_fn_ok, ircf_index_cfg_reachable]
QED

(* Check that importing fixture definitions did not import the unfinished Sim proof. *)
val _ = List.app (fn th =>
  case Tag.dest_tag (Thm.tag th) of
    ([], []) => ()
  | (["DISK_THM"], []) => ()
  | _ => raise Fail "Index CFG pointer certificate has proof debt")
  [ircf_index_cfg_dead_wf, ircf_index_cfg_pointer_discipline];
