(* Interpret a concrete saved-operand run as the empty-mark CREATE prefix. *)
Theory entryCreateRestoreScope
Ancestors
  fragCopyFetchRun entryCreatePathScope createSizePrefixReplay createExprSizeExitDefs
  fragExec fragGasOrigin venomExecSemantics venomInst venomState
  relation list rich_list pair arithmetic

Theorem copy_fetch_run_restore_scope:
  copy_fetch_run
    (\l j id. id IN frag_ids a b /\
      (l <> b.cs_current_bb \/ j <> LENGTH b.cs_current_insts))
    explicit ctx fn s t ==>
  create_expr_prefix a b explicit ctx fn s [] t
Proof
  disch_tac >>
  qpat_x_assum `copy_fetch_run _ _ _ _ _ _` mp_tac >>
  simp[copy_fetch_run_def, create_expr_prefix_marked] >>
  strip_tac >>
  ho_match_mp_tac RTC_INDUCT_RIGHT1 >>
  simp[FORALL_PROD, create_prefix_step_def] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule >>
  disch_then (qx_choosel_then [`bb`,`i`] strip_assume_tac) >>
  qexistsl_tac [`bb`,`i`] >>
  asm_rewrite_tac[] >>
  simp[]
QED

Theorem saved_code_list_restore_scope:
  same_blocks a b /\ b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  create_cut_code {} a b /\ fn_has_code a b f /\
  EVERY (\i. MEM i.inst_opcode [ALLOCA;ADD;ILOAD;DLOAD;MSTORE]) (emitted_insts a b) /\
  ~s.vs_halted /\ create_operand_at a s /\ create_operand_at b z /\
  (?raw. run_inst_seq (emitted_insts a b) s = OK raw /\
         z = raw with vs_inst_idx := LENGTH b.cs_current_insts) ==>
  create_operand_full_scope a b E C f s [] (OK z)
Proof
  strip_tac >>
  `b.cs_current_bb = a.cs_current_bb /\ emitted_blocks a b = []` by
    fs[same_blocks_def, emitted_blocks_def] >>
  drule_all stmtReasonLitFragMemoryTheory.fn_has_code_code >> strip_tac >>
  `EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
                i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode)
      (emitted_insts a b)` by
    (fs[create_cut_code_def, frag_code_def, EVERY_MEM] >>
     qx_gen_tac `j` >> strip_tac >>
     qpat_assum `!i. MEM i _ ==> _` (drule_then strip_assume_tac) >>
     gvs[is_terminator_def] >> metis_tac[]) >>
  `create_expr_prefix a b E C f s []
      (raw with vs_inst_idx := LENGTH b.cs_current_insts)` by
    (irule unwrap_code_list_prefix >> fs[create_operand_at_def] >>
     qexists_tac `emitted_insts a b` >> simp[]) >>
  fs[create_operand_at_def, create_operand_full_scope_def] >>
  metis_tac[LENGTH_APPEND]
QED
