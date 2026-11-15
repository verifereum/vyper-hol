(* Raw INVOKE shape comes from the actual event trace, not its weaker edit
   abstraction, which intentionally permits empty output lists. *)
Theory readonlyInvokeCopyFwdExecutionShape
Ancestors
  readonlyInvokeCopyFwdPlan readonlyInvokeCopyFwdHistory
  readonlyInvokeCopyFwdReadonlyPositions
  venomInst venomExecSemantics list indexedLists

Theorem ricf_execution_block_invoke_outputs[local]:
  !bb es last. ricf_block_trace bb es last ==>
  !i. i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode = INVOKE ==>
    (EL i last.bb_instructions).inst_opcode = INVOKE /\
    (EL i last.bb_instructions).inst_outputs =
      (EL i bb.bb_instructions).inst_outputs
Proof
  ho_match_mp_tac ricf_block_trace_ind >> simp[] >> rpt strip_tac >>
  `i <> e.rfe_index` by
    (drule ricf_event_copy_shape >> simp[ricf_event_copy_def] >>
     rpt strip_tac >> gvs[]) >>
  `LENGTH (ricf_event_apply e bb).bb_instructions = LENGTH bb.bb_instructions` by
    metis_tac[ricf_event_prefix_and_copy] >>
  `(EL i (ricf_event_apply e bb).bb_instructions).inst_opcode = INVOKE /\
   (EL i (ricf_event_apply e bb).bb_instructions).inst_outputs =
     (EL i bb.bb_instructions).inst_outputs` by
    (conj_tac
     >- (drule ricf_event_opcode >> disch_then (qspec_then `e` mp_tac) >> simp[]) >>
     drule ricf_event_outputs >> disch_then (qspec_then `e` mp_tac) >> simp[]) >>
  metis_tac[]
QED

Theorem ricf_execution_round_invoke_outputs[local]:
  ricf_round_certificate ctx fn mid /\ b < LENGTH fn.fn_blocks /\
  i < LENGTH (EL b fn.fn_blocks).bb_instructions /\
  (EL i (EL b fn.fn_blocks).bb_instructions).inst_opcode = INVOKE ==>
  (EL i (EL b mid.fn_blocks).bb_instructions).inst_opcode = INVOKE /\
  (EL i (EL b mid.fn_blocks).bb_instructions).inst_outputs =
    (EL i (EL b fn.fn_blocks).bb_instructions).inst_outputs
Proof
  rw[ricf_round_certificate_def] >> gvs[LIST_REL_EL_EQN] >>
  `?es. ricf_block_trace (EL b fn.fn_blocks) es (EL b bbs)` by metis_tac[] >>
  metis_tac[ricf_execution_block_invoke_outputs]
QED

Theorem ricf_execution_function_invoke_outputs:
  !base fn last. ricf_function_trace base fn last ==>
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) ==>
  !b i. b < LENGTH fn.fn_blocks /\
    i < LENGTH (EL b fn.fn_blocks).bb_instructions /\
    (EL i (EL b fn.fn_blocks).bb_instructions).inst_opcode = INVOKE ==>
    (EL i (EL b last.fn_blocks).bb_instructions).inst_opcode = INVOKE /\
    (EL i (EL b last.fn_blocks).bb_instructions).inst_outputs =
      (EL i (EL b fn.fn_blocks).bb_instructions).inst_outputs
Proof
  ho_match_mp_tac ricf_function_trace_ind >> simp[] >> rpt strip_tac >>
  rename1 `ricf_round_certificate (base0 with icf_dfg := _) fn mid` >>
  `ricf_function_edit fn mid` by
    (irule ricf_round_certificate_edit >> simp[] >>
     qexists_tac `base0 with icf_dfg := dfg_build_function fn` >> simp[]) >>
  `ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts mid))` by
    metis_tac[ricf_function_edit_ids] >>
  `b < LENGTH mid.fn_blocks /\
   i < LENGTH (EL b mid.fn_blocks).bb_instructions` by
    (fs[ricf_function_edit_def, LIST_REL_EL_EQN, ricf_block_edit_def] >>
     metis_tac[]) >>
  `(EL i (EL b mid.fn_blocks).bb_instructions).inst_opcode = INVOKE /\
   (EL i (EL b mid.fn_blocks).bb_instructions).inst_outputs =
     (EL i (EL b fn.fn_blocks).bb_instructions).inst_outputs` by
    metis_tac[ricf_execution_round_invoke_outputs] >>
  metis_tac[]
QED

Theorem ricf_execution_logged_invoke_shape:
  ricf_logged_function_trace ctx0 fn log mid /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  b < LENGTH fn.fn_blocks /\
  i < LENGTH (EL b fn.fn_blocks).bb_instructions /\
  (EL i (EL b fn.fn_blocks).bb_instructions).inst_opcode = INVOKE /\
  decode_invoke (EL i (EL b fn.fn_blocks).bb_instructions) = SOME (nm,args) ==>
  b < LENGTH mid.fn_blocks /\ i < LENGTH (EL b mid.fn_blocks).bb_instructions /\
  ?args'. decode_invoke (EL i (EL b mid.fn_blocks).bb_instructions) = SOME (nm,args') /\
    (EL i (EL b mid.fn_blocks).bb_instructions).inst_id =
      (EL i (EL b fn.fn_blocks).bb_instructions).inst_id /\
    (EL i (EL b mid.fn_blocks).bb_instructions).inst_opcode = INVOKE /\
    (EL i (EL b mid.fn_blocks).bb_instructions).inst_outputs =
      (EL i (EL b fn.fn_blocks).bb_instructions).inst_outputs /\
    LENGTH args' = LENGTH args /\
    (!k. k < LENGTH args ==> EL k args' = EL k args \/
      rma_is_readonly ctx0.icf_rma nm k)
Proof
  strip_tac >>
  `ricf_function_trace ctx0 fn mid` by
    metis_tac[ricf_logged_function_trace_erases] >>
  drule_all ricf_function_trace_readonly_positions >> strip_tac >>
  drule_all ricf_execution_function_invoke_outputs >> metis_tac[]
QED
