(* Every selected site, rather than just one witness, follows its copy. *)
Theory readonlyInvokeCopyFwdExecutionCallIndex
Ancestors
  readonlyInvokeCopyFwdHistory readonlyInvokeCopyFwdProtectionLifetime
  readonlyInvokeCopyFwdPlan readonlyInvokeCopyFwdDefs
  invokeCopyFwdCommonDefs allocaRemapSSA venomWf venomWfProps
  venomInst list rich_list arithmetic

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

Theorem ricf_call_event_site_present:
  ricf_event_ok e bb /\ MEM (ri,p) e.rfe_sites ==>
  ?j. findi (\inst. inst.inst_id = ri.inst_id) bb.bb_instructions = SOME j
Proof
  simp[ricf_event_ok_def, ricf_try_forward_def, ricf_event_copy_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  qpat_x_assum `_::_ = e.rfe_sites`
    (fn th => rule_assum_tac (REWRITE_RULE [GSYM th])) >>
  gvs[EVERY_MAP, EVERY_MEM, combinTheory.o_DEF] >>
  Cases_on `findi (\inst. inst.inst_id = ri.inst_id) bb.bb_instructions` >> gvs[] >>
  qpat_x_assum `!x. MEM x _ ==> _ <> NONE`
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

Theorem ricf_call_same_id_block[local]:
  fn_inst_ids_distinct fn /\ MEM left fn.fn_blocks /\ MEM right fn.fn_blocks /\
  MEM iid (MAP (\inst. inst.inst_id) left.bb_instructions) /\
  MEM iid (MAP (\inst. inst.inst_id) right.bb_instructions) ==>
  left = right
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`fn.fn_blocks`,
    `\bb:basic_block. MAP (\inst:instruction. inst.inst_id) bb.bb_instructions`,
    `left:basic_block`,`right:basic_block`,`iid:num`]
      (INST_TYPE [alpha |-> ``:basic_block``, beta |-> ``:num``]
        all_distinct_flat_map_unique)) >> fs[fn_inst_ids_distinct_def]
QED

(* A selected record carrying the active call's original ID belongs to that
   original block and occurs at that call's actual source index. *)
Theorem ricf_call_located_same_block_selected:
  ricf_located_event ctx0 original log round b es prefix e current /\
  wf_function original /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) /\
  cb < LENGTH original.fn_blocks /\
  i < LENGTH (EL cb original.fn_blocks).bb_instructions /\
  (EL i (EL cb original.fn_blocks).bb_instructions).inst_opcode = INVOKE /\
  MEM (ri,p) e.rfe_sites /\
  ri.inst_id = (EL i (EL cb original.fn_blocks).bb_instructions).inst_id ==>
  b = cb /\ ricf_selected_position e (EL cb original.fn_blocks) i /\
  e.rfe_index < i
Proof
  strip_tac >> drule ricf_located_event_validation >> strip_tac >>
  drule_all ricf_located_event_source_block >> strip_tac >>
  drule_all ricf_call_event_site_present >> strip_tac >>
  `MAP (\inst. inst.inst_id) (EL b original.fn_blocks).bb_instructions =
   MAP (\inst. inst.inst_id) current.bb_instructions` by
    (fs[ricf_block_edit_def, LIST_REL_EL_EQN, LIST_EQ_REWRITE] >>
     rpt strip_tac >> first_x_assum (qspec_then `x` mp_tac) >>
     simp[ricf_inst_edit_def, EL_MAP]) >>
  `findi (\inst. inst.inst_id = ri.inst_id)
    (EL b original.fn_blocks).bb_instructions = SOME j` by
    (drule findi_inst_ids >> disch_then (qspec_then `ri.inst_id` assume_tac) >>
     metis_tac[]) >>
  qpat_assum `findi _ (EL b original.fn_blocks).bb_instructions = SOME j`
    (mp_then Any mp_tac findi_some_index) >> strip_tac >>
  `EL b original.fn_blocks = EL cb original.fn_blocks` by
    (mp_tac (SPEC_ALL ricf_call_same_id_block |>
       Q.INST [`fn` |-> `original`,`left` |-> `EL b original.fn_blocks`,
         `right` |-> `EL cb original.fn_blocks`,`iid` |-> `ri.inst_id`]) >>
     (impl_tac >- (fs[wf_function_def, MEM_MAP] >> metis_tac[EL_MEM])) >> simp[]) >>
  `b = cb` by
    (fs[wf_function_def, fn_labels_def] >>
     qpat_x_assum `ALL_DISTINCT (MAP (\bb. bb.bb_label) original.fn_blocks)` mp_tac >>
     simp[EL_ALL_DISTINCT_EL_EQ] >>
     disch_then (qspecl_then [`b`,`cb`] mp_tac) >> simp[EL_MAP] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\inst. inst.inst_id)
    (EL cb original.fn_blocks).bb_instructions)` by
    (qspecl_then [`\bb. MAP (\inst. inst.inst_id) bb.bb_instructions`,
      `original.fn_blocks`,`EL cb original.fn_blocks`]
      mp_tac all_distinct_flat_map_member >>
     fs[wf_function_def, fn_inst_ids_distinct_def] >> simp[EL_MEM]) >>
  `j = i` by
    (qpat_x_assum `ALL_DISTINCT (MAP _ (EL cb original.fn_blocks).bb_instructions)` mp_tac >>
     simp[EL_ALL_DISTINCT_EL_EQ] >>
     disch_then (qspecl_then [`j`,`i`] mp_tac) >> simp[EL_MAP] >> metis_tac[]) >>
  `ricf_selected_position e (EL cb original.fn_blocks) i` by
    (simp[ricf_selected_position_def] >> metis_tac[]) >>
  simp[] >> irule ricf_call_located_selected_index >> metis_tac[]
QED
