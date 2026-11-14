(* Actual selected source calls establish paired readonly histories. *)
Theory readonlyInvokeCopyFwdHistorySuspension
Ancestors
  readonlyInvokeCopyFwdHistoryOrigin readonlyInvokeCopyFwdHistoryPhase
  readonlyInvokeCopyFwdHistorySelected
  readonlyInvokeCopyFwdHistoryVisitAccess fnFrameStepsRevertForward
  occurrenceGeometry o1LowerDloadOccurrence venomWf list finite_map

Theorem ricf_history_selected_suspend:
  ricf_phase_entry vs C ctx0 log stk PG G tn fn s a U B (p,[]) /\
  occ_frame_reachable vs C stk PG G tn fn callinst s n a U B HP H /\
  occurrence_natural_geometry lo a U B stk s /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ~ctx_has_dalloca C /\
  ssa_form p.rpe_fn /\ fn_inst_wf p.rpe_fn /\ fn_inst_ids_distinct p.rpe_fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts p.rpe_fn)) /\
  ricf_full_alloca_copies p.rpe_fn /\ ricf_src_alloca p.rpe_fn /\
  occurrence_syntax_origin fn a H /\
  ricf_located_event ctx0 p.rpe_fn log round b es prefix p.rpe_event current /\
  p.rpe_block = EL b p.rpe_fn.fn_blocks /\
  cb < LENGTH fn.fn_blocks /\ i < LENGTH (EL cb fn.fn_blocks).bb_instructions /\
  callinst = EL i (EL cb fn.fn_blocks).bb_instructions /\
  MEM (EL i (EL cb round.fn_blocks).bb_instructions,pos) p.rpe_event.rfe_sites /\
  active_inst fn callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\ active_inst callee inst s1 ==>
  ricf_history_inherited vs C ctx0 log p
    (<| cf_fn := fn; cf_inst := callinst; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk)
    (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1 /\
  ricf_history_cursor vs C ctx0 log p
    [<| cf_fn := fn; cf_inst := callinst; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |>]
    (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee s1
Proof
  strip_tac >>
  fs[ricf_phase_entry_def] >>
  drule ricf_history_cursor_owner_function >> strip_tac >> gvs[] >>
  `?ostk OPG OG OT. ricf_history_origin vs C ctx0 log p ostk OPG OG OT` by
    (fs[ricf_history_cursor_def] >> metis_tac[]) >>
  drule_all ricf_history_origin_original_allocas >> strip_tac >>
  `dfg_get_def (dfg_build_function p.rpe_fn)
     (icf_assign_root (dfg_build_function p.rpe_fn) {} dst) = SOME da /\
   dfg_get_def (dfg_build_function p.rpe_fn) sv = SOME sa` by
    (conj_tac >> irule dfg_build_function_ssa_def >> simp[]) >>
  gvs[] >>
  drule_all occ_frame_reachable_annotation >> strip_tac >>
  `occurrence_annotation_ok n p.rpe_owner U B HP H stk PG G s` by metis_tac[] >>
  `FLOOKUP s.vs_allocas da.inst_id = SOME (p.rpe_db,p.rpe_size) /\
   FLOOKUP s.vs_allocas sa.inst_id = SOME (p.rpe_sb,p.rpe_size) /\
   (!k. k < LENGTH ops /\ op_prov G (EL k ops) = SOME (p.rpe_db,p.rpe_size)
        ==> rma_is_readonly ctx0.icf_rma nm k) /\
   (!k. k < LENGTH ops /\ op_prov G (EL k ops) = SOME (p.rpe_sb,p.rpe_size)
        ==> EL k ops = Var sv /\ rma_is_readonly ctx0.icf_rma nm k)` by
    (irule ricf_history_selected_call_endpoints >> simp[] >> metis_tac[]) >>
  irule ricf_history_inherited_start >> simp[] >>
  metis_tac[occ_frame_reachable_projection]
QED
