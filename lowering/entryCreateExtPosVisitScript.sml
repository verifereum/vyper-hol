(* The administrative snapshot owns no CREATE or nested INVOKE visits. *)
Theory entryCreateExtPosVisit
Ancestors
  entryCreateNativeFirstExit entryCreatePosSnapshotCode createSizeConcreteSnapshots
  entryCreateStmtCases createSizeCutRegion vyperStorageTrace
  entryCreateFocusSpec entryCreateBodyCut createSizePrefixReplay entryCreatePathScope list

Theorem extcall_pos_snapshot_visit_cut:
  body_inv tops C ce cx /\ MEM f C.ctx_functions /\
  create_cut_code {} a m /\ fn_has_code a m f /\ fn_has_code m b f /\
  compile_snapshot_vv ce copy input m = (sv,b) /\
  create_operand_cut a m E C f tops cx st0 (eval_expr cx e) (es,s) ==>
  create_operand_cut a b E C f tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s)
Proof
  strip_tac >>
  `create_cut_code {} m b` by metis_tac[create_vv_snapshot_cut_code,pairTheory.SND] >>
  simp[create_operand_cut_def] >> rpt gen_tac >> disch_tac >>
  drule_all_then strip_assume_tac create_interior_visit_first_exit
  >- (irule create_cut_bind_left >> simp[storage_trace_frame_read_result] >>
      fs[create_operand_cut_def] >> metis_tac[]) >>
  drule_then assume_tac pos_snapshot_opcode_inventory >>
  rename1 `create_interior_visit m b E C f _ t _` >>
  `create_cut_region m b t` by
    (fs[create_operand_at_def] >> metis_tac[cj 1 create_cut_region_rules]) >>
  `!u inst marks. create_expr_prefix m b E C f t marks u /\
      create_operand_fetch m b f u inst ==>
      ~MEM inst.inst_opcode [GAS;CREATE;CREATE2;INVOKE]` by
    (rpt strip_tac >>
     `create_cut_region m b u` by metis_tac[create_expr_prefix_cut_region] >>
     drule_all create_cut_region_rules >> disch_then (assume_tac o cj 2) >>
     fs[create_operand_fetch_def,create_operand_at_def,EVERY_MEM] >> metis_tac[]) >>
  qpat_assum `create_interior_visit m b _ _ _ _ t _`
    (strip_assume_tac o MATCH_MP create_interior_visit_cases) >>
  gvs[] >> TRY (irule create_cut_noncreate_visit) >> res_tac >> fs[]
QED
