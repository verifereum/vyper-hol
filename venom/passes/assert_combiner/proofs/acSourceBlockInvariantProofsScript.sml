Theory acSourceBlockInvariantProofs
Ancestors
  acMergeRuntimeProofs acRuntimePhiProofs acRuntimeSuccessorProofs
  runInstsExecBlockProps venomExecProofs venomWfProps venomWf rich_list list
  analysisSimDefs acMergeRuntimeDefs venomExecSemantics venomInst
  acRuntimeInvariantDefs acMergeCursorDefs acChainProofs venomExecProps venomState

(* Successful source execution advances the certificate independently of
   the transformed emission relation. *)
Theorem ac_source_suffix_cert:
  !xs n fn bb offset fuel ctx s t.
    xs = DROP n (DROP offset bb.bb_instructions) /\
    n <= LENGTH (DROP offset bb.bb_instructions) /\
    wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
    EVERY (\i. i.inst_opcode <> PHI) (DROP offset bb.bb_instructions) /\
    ac_merge_runtime_cert fn bb offset n s /\
    run_insts fuel ctx xs s = OK t ==>
    ac_merge_runtime_cert fn bb offset
      (LENGTH (DROP offset bb.bb_instructions)) t
Proof
  Induct >- (rpt strip_tac >> gvs[run_insts_def] >>
              `n = LENGTH (DROP offset bb.bb_instructions)` by
                (Cases_on `n < LENGTH (DROP offset bb.bb_instructions)` >> gvs[]) >>
              gvs[]) >>
  rpt gen_tac >> strip_tac >>
  `n < LENGTH (DROP offset bb.bb_instructions)` by
    (qpat_x_assum `_ = DROP _ _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  `EL n (DROP offset bb.bb_instructions) = h` by
    metis_tac[HD_DROP, HD] >>
  `n+offset < LENGTH bb.bb_instructions` by gvs[LENGTH_DROP] >>
  `h.inst_opcode <> PHI` by gvs[EVERY_EL] >>
  gvs[run_insts_def, AllCaseEqs()] >>
  rename1 `step_inst fuel ctx _ s = OK u` >>
  `ac_merge_runtime_cert fn bb offset (SUC n) u` by
    (irule ac_merge_runtime_cert_step >> simp[] >>
     conj_tac >- (qpat_x_assum `(EL n _).inst_opcode <> PHI` mp_tac >> simp[EL_DROP]) >>
     qexistsl [`ctx`, `fuel`, `s`] >> gvs[EL_DROP]) >>
  first_x_assum irule >> simp[] >> qexistsl [`ctx`, `fuel`, `SUC n`, `u`] >> simp[] >>
  qpat_x_assum `_ = DROP n _` (mp_tac o Q.AP_TERM `DROP 1`) >>
  simp[DROP_DROP_T, arithmeticTheory.ADD1]
QED

(* PHIs are a single parallel batch. Structural suffix premises are exposed
   for the concrete block join to discharge from well-formedness. *)
Theorem ac_source_run_block_cert:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  ac_cursor_inv fn bb 0 s /\ ac_merge_safe_labels fn s /\
  phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions /\
  EVERY (\i. i.inst_opcode <> PHI)
    (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
  run_block fuel ctx bb s = OK t ==>
  ac_merge_runtime_cert fn bb (phi_prefix_length bb.bb_instructions)
    (LENGTH (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)) t
Proof
  rpt strip_tac >>
  `(!op st j. eval_operand op (st with vs_inst_idx := j) = eval_operand op st) /\
   (!op st l j. eval_operand op (st with <|vs_current_bb := l; vs_inst_idx := j|>) =
                 eval_operand op st)` by
    (conj_tac >> Cases >> simp[eval_operand_def, lookup_var_def]) >>
  `MEM bb fn.fn_blocks` by gvs[ac_cursor_inv_def] >>
  `bb_well_formed bb` by metis_tac[wf_function_bb_well_formed] >>
  qpat_x_assum `run_block _ _ _ _ = _` mp_tac >>
  simp[run_block_def] >>
  qspec_then `s` (qspec_then `bb.bb_instructions` strip_assume_tac)
    eval_phis_ok_or_error_defs >> simp[] >> strip_tac >>
  rename1 `eval_phis s bb.bb_instructions = OK p` >>
  drule_all ac_cursor_inv_phis >> strip_tac >>
  `ac_merge_runtime_cert fn bb (phi_prefix_length bb.bb_instructions) 0 p` by
    (simp[ac_merge_runtime_cert_def, ac_merge_runtime_def] >> conj_tac
     >- (drule eval_phis_preserves_current_bb >>
         gvs[ac_cursor_inv_def, ac_dfg_inv_local_def,
             lookup_var_def, eval_operand_def] >> metis_tac[]) >>
     drule eval_phis_preserves_labels >>
     metis_tac[ac_merge_safe_labels_frame]) >>
  drule_all exec_block_run_insts_ok >> strip_tac >> gvs[] >>
  `ac_merge_runtime_cert fn bb (phi_prefix_length bb.bb_instructions)
      (LENGTH (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)) u` by
    (irule ac_source_suffix_cert >> simp[] >>
     qexistsl [`ctx`, `fuel`, `0`, `p`] >> simp[]) >>
  gvs[ac_merge_runtime_cert_def, ac_merge_runtime_raw,
      ac_dfg_inv_local_def, lookup_var_def, eval_operand_def,
      ac_merge_safe_labels_def] >> metis_tac[]
QED

Theorem ac_source_run_block_successor:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  ac_cursor_inv fn bb 0 s /\ ac_merge_safe_labels fn s /\
  phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions /\
  EVERY (\i. i.inst_opcode <> PHI)
    (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
  run_block fuel ctx bb s = OK t /\
  MEM sb fn.fn_blocks /\ sb.bb_label = t.vs_current_bb ==>
  ac_cursor_inv fn sb 0 t /\ ac_merge_safe_labels fn t
Proof
  rpt strip_tac >>
  drule_all ac_source_run_block_cert >> strip_tac >>
  `MEM bb fn.fn_blocks` by gvs[ac_cursor_inv_def] >>
  `bb_well_formed bb` by metis_tac[wf_function_bb_well_formed] >>
  `?p. eval_phis s bb.bb_instructions = OK p /\
       exec_block fuel ctx bb
         (p with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK t` by
    (qpat_x_assum `run_block _ _ _ _ = _` mp_tac >>
     qspec_then `s` (qspec_then `bb.bb_instructions` strip_assume_tac)
       eval_phis_ok_or_error_defs >> simp[run_block_def]) >>
  `t.vs_inst_idx = 0` by metis_tac[exec_block_OK_inst_idx_0] >>
  `MEM t.vs_current_bb (bb_succs bb)` by
    (irule venomExecProofsTheory.exec_block_current_bb_in_succs >>
     simp[] >>
     reverse conj_tac
     >- (conj_tac >- gvs[bb_well_formed_def] >>
         qexistsl [`ctx`, `fuel`,
           `p with vs_inst_idx := phi_prefix_length bb.bb_instructions`] >> simp[]) >>
     gvs[bb_well_formed_def] >> rpt strip_tac >>
     `i < LENGTH bb.bb_instructions` by decide_tac >>
     `i = PRE (LENGTH bb.bb_instructions)` by metis_tac[] >> decide_tac) >>
  `fn_cfg_edge fn bb.bb_label sb.bb_label` by
    (simp[fn_cfg_edge_def] >> qexists `bb` >> simp[]) >>
  `ac_cursor_inv fn bb (LENGTH bb.bb_instructions)
     (t with <|vs_current_bb := bb.bb_label;
               vs_inst_idx := LENGTH bb.bb_instructions|>)` by
    (gvs[ac_merge_runtime_cert_def, ac_merge_runtime_def, LENGTH_DROP] >>
     fs[]) >>
  drule_all ac_cursor_inv_successor >>
  gvs[] >> strip_tac >>
  gvs[ac_merge_runtime_cert_def]
QED
