(* Selected calls are original-source calls at positions selected in a logged
   round.  Current occurrence maps are explicit, not payload-time maps. *)
Theory readonlyInvokeCopyFwdHistorySelected
Ancestors
  readonlyInvokeCopyFwdHistoryClosure readonlyInvokeCopyFwdHistoryCallPositions
  readonlyInvokeCopyFwdHistoryOrigin readonlyInvokeCopyFwdProtectionSelected
  readonlyInvokeCopyFwdHistory o1LowerDloadOccurrence
  readonlyInvokeCopyFwdReadonlyReach occurrenceGeometry occurrenceOrigin
  readonlyInvokeCopyFwdPlan internalReturnCopyFwdPlan invokeCopyFwdCommonDefs
  ptrDiscipline venomExecSemantics list finite_map

Theorem ricf_history_selected_call_endpoints:
  ricf_located_event ctx0 fn log round b es prefix e current /\
  ssa_form fn /\ ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_src_alloca fn /\
  (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands = [Var dst;Var sv;sz] /\
  dfg_get_def (dfg_build_function fn)
    (icf_assign_root (dfg_build_function fn) {} dst) = SOME di /\
  icf_is_alloca di /\ MEM di (fn_insts fn) /\ di.inst_opcode = ALLOCA /\
  di.inst_outputs = [icf_assign_root (dfg_build_function fn) {} dst] /\
  dfg_get_def (dfg_build_function fn) sv = SOME ai /\
  MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [sv] /\
  fn_inst_wf fn /\ fn_inst_ids_distinct fn /\ occurrence_syntax_origin fn a H /\
  occurrence_annotation_ok n a U B HP H stk PG G s /\
  occurrence_natural_geometry lo a U B stk s /\
  FLOOKUP B (a,di.inst_id) = SOME (db,z) /\
  FLOOKUP B (a,ai.inst_id) = SOME (sb,z) /\ 0 < z /\
  cb < LENGTH fn.fn_blocks /\ i < LENGTH (EL cb fn.fn_blocks).bb_instructions /\
  (EL i (EL cb fn.fn_blocks).bb_instructions).inst_opcode = INVOKE /\
  decode_invoke (EL i (EL cb fn.fn_blocks).bb_instructions) = SOME (nm,ops) /\
  MEM (EL i (EL cb round.fn_blocks).bb_instructions,p) e.rfe_sites ==>
  FLOOKUP s.vs_allocas di.inst_id = SOME (db,z) /\
  FLOOKUP s.vs_allocas ai.inst_id = SOME (sb,z) /\
  (!k. k < LENGTH ops /\ op_prov G (EL k ops) = SOME (db,z) ==>
     rma_is_readonly ctx0.icf_rma nm k) /\
  (!k. k < LENGTH ops /\ op_prov G (EL k ops) = SOME (sb,z) ==>
     EL k ops = Var sv /\ rma_is_readonly ctx0.icf_rma nm k)
Proof
  strip_tac >>
  `occurrence_allocas_ok B a s /\
   occurrence_env_ok B (a::MAP (\u. u.of_owner) U) H G` by
    gvs[occurrence_annotation_ok_def] >>
  conj_tac >- gvs[occurrence_allocas_ok_def] >>
  conj_tac >- gvs[occurrence_allocas_ok_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `op_prov H (EL k ops) = SOME (a,di.inst_id)` by
        (irule occurrence_geometry_op_positive_key >> metis_tac[]) >>
      drule_all ricf_located_event_destination_occurrence_operand >> strip_tac >>
      irule ricf_located_event_original_destination_readonly >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `op_prov H (EL k ops) = SOME (a,ai.inst_id)` by
    (irule occurrence_geometry_op_positive_key >> metis_tac[]) >>
  drule_all ricf_located_event_validation >> strip_tac >>
  drule_all ricf_located_event_source_block >> strip_tac >>
  drule_all ricf_located_event_source_descriptor >> strip_tac >>
  drule ricf_block_edit_EL >> strip_tac >>
  drule_all ricf_event_copy_shape >> strip_tac >>
  `!inst. MEM inst (fn_insts fn) /\ MEM (Var sv) inst.inst_operands ==>
     ~is_pointer_preserving_op inst.inst_opcode` by
    (gen_tac >> disch_tac >> irule ricf_source_copy_isolated >>
     gvs[ricf_event_copy_def] >> metis_tac[EL_MEM]) >>
  `EL k ops = Var sv` by
    (irule ricf_isolated_occurrence_operand >> metis_tac[]) >>
  simp[] >> irule ricf_located_event_original_source_readonly >> metis_tac[]
QED

(* History anchors replace the old protection_cursor; the two histories share
   the same saved original-source caller and the same inner prefix. *)
Definition ricf_history_inherited_def:
  ricf_history_inherited vs C ctx0 log p stk PG G tn fn inst s <=>
    ?anchor tail pre atn.
      stk = pre ++ anchor::tail /\ atn.t_var = anchor.cf_tvar /\
      ricf_history_cursor vs C ctx0 log p [] anchor.cf_params anchor.cf_prov
        atn anchor.cf_fn anchor.cf_state /\
      readonly_call_reachable vs C (rma_is_readonly ctx0.icf_rma)
        anchor tail (SND p.rpe_dst) p.rpe_db p.rpe_size pre PG G tn fn inst s /\
      readonly_call_reachable vs C (rma_is_readonly ctx0.icf_rma)
        anchor tail (SND p.rpe_src) p.rpe_sb p.rpe_size pre PG G tn fn inst s
End

Theorem ricf_history_inherited_start:
  !vs C ctx0 log p PG G tn caller s stk inv nm ops callee args cs s1 inst.
  ricf_history_cursor vs C ctx0 log p [] PG G tn caller s /\
  frame_reachable vs C stk PG G tn caller inv s /\
  active_inst caller inv s /\ inv.inst_opcode = INVOKE /\
  decode_invoke inv = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\ active_inst callee inst s1 /\
  FLOOKUP s.vs_allocas (SND p.rpe_dst) = SOME (p.rpe_db,p.rpe_size) /\
  FLOOKUP s.vs_allocas (SND p.rpe_src) = SOME (p.rpe_sb,p.rpe_size) /\
  0 < p.rpe_size /\
  (!k. k < LENGTH ops /\ op_prov G (EL k ops) = SOME (p.rpe_db,p.rpe_size)
       ==> rma_is_readonly ctx0.icf_rma nm k) /\
  (!k. k < LENGTH ops /\ op_prov G (EL k ops) = SOME (p.rpe_sb,p.rpe_size)
       ==> rma_is_readonly ctx0.icf_rma nm k) ==>
  ricf_history_inherited vs C ctx0 log p
    (<| cf_fn := caller; cf_inst := inv; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk)
    (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1 /\
  ricf_history_cursor vs C ctx0 log p
    [<| cf_fn := caller; cf_inst := inv; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |>]
    (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee s1
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `frame_reachable vs C stk PG G tn caller callinst s` >>
  reverse conj_tac >- (irule ricf_history_cursor_call >> metis_tac[]) >>
  simp[ricf_history_inherited_def] >>
  qexistsl_tac
    [`<| cf_fn := caller; cf_inst := callinst; cf_state := s;
         cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |>`,
     `stk`, `[]`, `tn`] >> simp[] >>
  conj_tac >> irule readonly_call_reachable_start >> metis_tac[]
QED
