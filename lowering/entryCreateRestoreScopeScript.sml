(* Interpret a concrete saved-operand run as the empty-mark CREATE prefix. *)
Theory entryCreateRestoreScope
Ancestors
  fragCopyFetchRun entryCreateUnwrapCode entryCreatePathScope
  entryCreateFocusSpec entryCreateCompletedCut
  createMarkedPath createSizePrefixReplay createExprSizeExitDefs
  fragExec fragGasOrigin venomExecSemantics venomInst venomState
  relation list pair

Theorem copy_fetch_run_restore_scope:
  copy_fetch_run
    (\l j id. id IN frag_ids a b /\
      (l <> b.cs_current_bb \/ j <> LENGTH b.cs_current_insts))
    explicit ctx fn s t ==>
  create_expr_prefix a b explicit ctx fn s [] t
Proof
  simp[copy_fetch_run_def] >> strip_tac >>
  irule RTC_lifts_invariants >> first_assum (irule_at Any) >>
  simp[] >> rpt strip_tac >>
  rename1 `gas_origin_edge F explicit ctx fn u [] (OK v)` >>
  `create_prefix_step a b explicit ctx fn u [] v` by
    (simp[create_prefix_step_def] >> metis_tac[]) >>
  `create_expr_prefix a b explicit ctx fn u [] v` by
    (simp[create_expr_prefix_marked] >> irule RTC_SINGLE >>
     simp[create_marked_edge_def]) >>
  drule_all create_expr_prefix_append >> simp[]
QED

Theorem copy_fetch_run_restore_full_scope:
  copy_fetch_run
    (\l j id. id IN frag_ids a b /\
      (l <> b.cs_current_bb \/ j <> LENGTH b.cs_current_insts))
    explicit ctx fn s t /\
  create_operand_at b t ==>
  create_operand_full_scope a b explicit ctx fn s [] (OK t)
Proof
  simp[create_operand_at_def, create_operand_full_scope_def] >>
  metis_tac[copy_fetch_run_restore_scope]
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
  ACCEPT_TAC unwrap_code_list_scope
QED
