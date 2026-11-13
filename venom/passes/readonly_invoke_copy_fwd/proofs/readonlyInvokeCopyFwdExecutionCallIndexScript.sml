(* Every selected site, rather than just one witness, follows its copy. *)
Theory readonlyInvokeCopyFwdExecutionCallIndex
Ancestors
  readonlyInvokeCopyFwdHistory readonlyInvokeCopyFwdProtectionLifetime
  readonlyInvokeCopyFwdPlan readonlyInvokeCopyFwdDefs
  invokeCopyFwdCommonDefs venomInst list rich_list arithmetic

Theorem ricf_call_event_selected_not_before:
  ricf_event_ok e bb /\ MEM (ri,p) e.rfe_sites /\
  findi (\inst. inst.inst_id = ri.inst_id) bb.bb_instructions = SOME j ==>
  e.rfe_index <= j
Proof
  simp[ricf_event_ok_def, ricf_try_forward_def, ricf_event_copy_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  qpat_x_assum `_::_ = e.rfe_sites`
    (fn th => rule_assum_tac (REWRITE_RULE [GSYM th])) >>
  gvs[EVERY_MAP, EVERY_MEM, combinTheory.o_DEF, NOT_LESS] >>
  qpat_x_assum `!x. MEM x _ ==> e.rfe_index <= _`
    (qspec_then `(ri,p)` mp_tac) >> simp[]
QED

Theorem ricf_call_event_selected_invoke_after:
  ricf_event_ok e bb /\ MEM (ri,p) e.rfe_sites /\
  findi (\inst. inst.inst_id = ri.inst_id) bb.bb_instructions = SOME j /\
  (EL j bb.bb_instructions).inst_opcode = INVOKE ==>
  e.rfe_index < j
Proof
  strip_tac >> drule_all ricf_call_event_selected_not_before >> strip_tac >>
  drule ricf_event_copy_shape >> simp[ricf_event_copy_def] >>
  rpt strip_tac >> Cases_on `e.rfe_index = j` >> gvs[] >> decide_tac
QED

Theorem ricf_call_located_selected_index:
  ricf_located_event ctx0 original log round b es prefix e current /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) /\
  ricf_selected_position e (EL b original.fn_blocks) j /\
  j < LENGTH (EL b original.fn_blocks).bb_instructions /\
  (EL j (EL b original.fn_blocks).bb_instructions).inst_opcode = INVOKE ==>
  e.rfe_index < j
Proof
  strip_tac >> drule ricf_located_event_validation >> strip_tac >>
  drule_all ricf_located_event_source_block >> strip_tac >>
  `MAP (\inst. inst.inst_id) (EL b original.fn_blocks).bb_instructions =
   MAP (\inst. inst.inst_id) current.bb_instructions` by
    (fs[ricf_block_edit_def, LIST_REL_EL_EQN, LIST_EQ_REWRITE] >>
     rpt strip_tac >> first_x_assum (qspec_then `x` mp_tac) >>
     simp[ricf_inst_edit_def, EL_MAP]) >>
  `ricf_selected_position e current j` by
    (fs[ricf_selected_position_def] >>
     drule findi_inst_ids >> disch_then (qspec_then `inst.inst_id` assume_tac) >>
     metis_tac[]) >>
  `(EL j current.bb_instructions).inst_opcode = INVOKE` by
    (drule_all ricf_block_edit_EL >> strip_tac >>
     qpat_x_assum `!i. i < _ ==> ricf_inst_edit _ _`
       (qspec_then `j` mp_tac) >> simp[ricf_inst_edit_def]) >>
  fs[ricf_selected_position_def] >>
  metis_tac[ricf_call_event_selected_invoke_after]
QED
