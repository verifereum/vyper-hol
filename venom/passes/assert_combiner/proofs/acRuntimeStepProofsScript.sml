Theory acRuntimeStepProofs
Ancestors
  acRuntimeInvariantDefs acRuntimeInvariantProofs acChainProofs assertCombinerDefs
  venomWf venomWfProps venomExecProofs venomExecProps venomExecSemantics
  venomInstProps venomState venomInst dfgDefs dfgAnalysisProps
  algebraicOptFreshnessProofs algebraicOptDominanceProofs basePtrProofs
  simplifyCfgAvailability finite_map list

Theorem ac_def_before_output_not_current:
  wf_function fn /\ wf_ssa fn /\ MEM bb fn.fn_blocks /\
  idx < LENGTH bb.bb_instructions /\ ac_def_before fn bb idx di /\
  MEM v di.inst_outputs ==>
  ~MEM v (EL idx bb.bb_instructions).inst_outputs
Proof
  rpt strip_tac >>
  `MEM di (fn_insts_blocks fn.fn_blocks)` by
    (fs[ac_def_before_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
     metis_tac[EL_MEM]) >>
  `MEM (EL idx bb.bb_instructions) (fn_insts_blocks fn.fn_blocks)` by
    (simp[unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >> metis_tac[EL_MEM]) >>
  `di = EL idx bb.bb_instructions` by
    (fs[wf_ssa_def] >> metis_tac[ssa_outputs_same_inst]) >>
  gvs[] >>
  gvs[ac_def_before_location]
QED

Theorem ac_def_before_operand_not_current:
  wf_function fn /\ wf_ssa fn /\ MEM bb fn.fn_blocks /\
  idx < LENGTH bb.bb_instructions /\ ac_def_before fn bb idx di /\
  di.inst_opcode <> PHI /\ MEM (Var v) di.inst_operands ==>
  ~MEM v (EL idx bb.bb_instructions).inst_outputs
Proof
  rpt strip_tac >>
  `?db j. MEM db fn.fn_blocks /\ j < LENGTH db.bb_instructions /\
          EL j db.bb_instructions = di` by
    (fs[ac_def_before_def] >> metis_tac[EL_MEM, MEM_EL]) >>
  `def_available_at fn db (SOME (EL j db.bb_instructions)) v` by
    (fs[wf_ssa_def, def_dominates_uses_def] >> metis_tac[EL_MEM]) >>
  drule_all ac_available_before_cursor >> strip_tac >>
  `ac_def_before fn bb idx inst` by
    (irule ac_def_before_trans >> metis_tac[]) >>
  metis_tac[ac_def_before_output_not_current]
QED

Theorem ac_current_operand_not_output:
  wf_function fn /\ wf_ssa fn /\ MEM bb fn.fn_blocks /\
  idx < LENGTH bb.bb_instructions /\
  (EL idx bb.bb_instructions).inst_opcode <> PHI /\
  MEM (Var v) (EL idx bb.bb_instructions).inst_operands ==>
  ~MEM v (EL idx bb.bb_instructions).inst_outputs
Proof
  rpt strip_tac >>
  `def_available_at fn bb (SOME (EL idx bb.bb_instructions)) v` by
    (fs[wf_ssa_def, def_dominates_uses_def] >> metis_tac[EL_MEM]) >>
  `get_instruction bb idx = SOME (EL idx bb.bb_instructions)` by
    simp[get_instruction_def] >>
  metis_tac[ao_ssa_producer_operand_not_output]
QED

Theorem ac_old_equations_step_frame:
  wf_function fn /\ wf_ssa fn /\ MEM bb fn.fn_blocks /\
  ac_dfg_inv_local (dfg_build_function fn) (ac_def_before fn bb idx) s /\
  idx < LENGTH bb.bb_instructions /\
  step_inst fuel ctx (EL idx bb.bb_instructions) s = OK t ==>
  ac_dfg_inv_local (dfg_build_function fn) (ac_def_before fn bb idx) t
Proof
  rpt strip_tac >>
  `!di v. ac_def_before fn bb idx di /\ MEM v di.inst_outputs ==>
     lookup_var v t = lookup_var v s` by
    (rpt strip_tac >> irule step_inst_preserves_lookup >>
     metis_tac[ac_def_before_output_not_current]) >>
  `!di op. ac_def_before fn bb idx di /\ di.inst_opcode <> PHI /\
           MEM op di.inst_operands ==>
           eval_operand op t = eval_operand op s` by
    (rpt strip_tac >> Cases_on `op` >> simp[eval_operand_def]
     >- (irule step_inst_preserves_lookup >>
         metis_tac[ac_def_before_operand_not_current]) >>
     metis_tac[venomExecProofsTheory.step_inst_preserves_labels_always]) >>
  fs[ac_cursor_inv_def, ac_dfg_inv_local_def] >>
  conj_tac >> rpt strip_tac >>
  drule dfg_build_function_correct >> strip_tac >>
  `lookup_var v t = lookup_var v s` by metis_tac[] >>
  gvs[] >>
  `inst.inst_opcode <> PHI` by simp[] >>
  `!op. MEM op inst.inst_operands ==> eval_operand op t = eval_operand op s`
    by metis_tac[] >>
  fs[] >> metis_tac[]
QED

Theorem ac_cursor_old_equations_step:
  wf_function fn /\ wf_ssa fn /\ ac_cursor_inv fn bb idx s /\
  idx < LENGTH bb.bb_instructions /\
  step_inst fuel ctx (EL idx bb.bb_instructions) s = OK t ==>
  ac_dfg_inv_local (dfg_build_function fn) (ac_def_before fn bb idx) t
Proof
  simp[ac_cursor_inv_def] >> metis_tac[ac_old_equations_step_frame]
QED

Theorem ac_cursor_current_equations_step:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  MEM bb fn.fn_blocks /\ idx < LENGTH bb.bb_instructions /\
  (EL idx bb.bb_instructions).inst_opcode <> PHI /\
  step_inst fuel ctx (EL idx bb.bb_instructions) s = OK t ==>
  ac_dfg_inv_local (dfg_build_function fn)
    (\di. di = EL idx bb.bb_instructions) t
Proof
  rpt strip_tac >>
  `inst_wf (EL idx bb.bb_instructions)` by
    metis_tac[fn_inst_wf_def, EL_MEM] >>
  `!op. MEM op (EL idx bb.bb_instructions).inst_operands ==>
        eval_operand op t = eval_operand op s` by
    (rpt strip_tac >>
     Cases_on `op` >> simp[eval_operand_def]
     >- (irule step_inst_preserves_lookup >>
         metis_tac[ac_current_operand_not_output]) >>
     metis_tac[venomExecProofsTheory.step_inst_preserves_labels_always]) >>
  simp[ac_dfg_inv_local_def] >> conj_tac >> rpt strip_tac >> gvs[] >>
  drule dfg_build_function_correct >> strip_tac >>
  Cases_on `EL idx bb.bb_instructions` >>
  gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
  gvs[step_inst_non_invoke, step_inst_base_def, exec_pure1_def,
      AllCaseEqs(), update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem ac_def_before_suc:
  idx < LENGTH bb.bb_instructions ==>
  (ac_def_before fn bb (SUC idx) di <=>
   ac_def_before fn bb idx di \/ di = EL idx bb.bb_instructions)
Proof
  simp[ac_def_before_def, prim_recTheory.LESS_THM] >> metis_tac[]
QED

Theorem ac_cursor_step:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  ac_cursor_inv fn bb idx s /\ idx < LENGTH bb.bb_instructions /\
  (EL idx bb.bb_instructions).inst_opcode <> PHI /\
  step_inst fuel ctx (EL idx bb.bb_instructions) s = OK t ==>
  ac_cursor_inv fn bb (SUC idx)
    (t with <|vs_inst_idx := SUC idx; vs_current_bb := bb.bb_label|>)
Proof
  rpt strip_tac >>
  `MEM bb fn.fn_blocks` by fs[ac_cursor_inv_def] >>
  `inst_wf (EL idx bb.bb_instructions)` by
    metis_tac[fn_inst_wf_def, EL_MEM] >>
  `ac_dfg_inv_local (dfg_build_function fn) (ac_def_before fn bb idx) t` by
    metis_tac[ac_cursor_old_equations_step] >>
  `ac_dfg_inv_local (dfg_build_function fn)
      (\di. di = EL idx bb.bb_instructions) t` by
    metis_tac[ac_cursor_current_equations_step] >>
  `!op. eval_operand op
       (t with <|vs_inst_idx := SUC idx; vs_current_bb := bb.bb_label|>) =
        eval_operand op t` by
    (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  simp[ac_cursor_inv_def, lookup_var_def] >>
  `SUC idx <= LENGTH bb.bb_instructions /\ fn_reachable fn bb.bb_label`
    by (fs[ac_cursor_inv_def] >> decide_tac) >>
  simp[] >>
  `idx < LENGTH bb.bb_instructions` by decide_tac >>
  reverse conj_tac
  >- (rpt strip_tac >>
      `ac_def_before fn bb idx inst \/ inst = EL idx bb.bb_instructions`
        by metis_tac[ac_def_before_suc] >>
      gvs[]
      >- (`~MEM v (EL idx bb.bb_instructions).inst_outputs` by
            (irule ac_def_before_output_not_current >>
             conj_tac >- decide_tac >>
             qexistsl [`inst`, `fn`] >> simp[]) >>
          `lookup_var v t = lookup_var v s` by
            metis_tac[step_inst_preserves_lookup] >>
          fs[ac_cursor_inv_def, lookup_var_def] >> metis_tac[]) >>
      `IS_SOME (lookup_var v t)` by
        (irule scfg_step_outputs_defined >>
         metis_tac[fn_inst_wf_def, EL_MEM]) >>
      fs[lookup_var_def]) >>
  `idx < LENGTH bb.bb_instructions` by decide_tac >>
  simp[ac_dfg_inv_local_def, ac_def_before_suc, lookup_var_def] >>
  fs[ac_dfg_inv_local_def, lookup_var_def] >>
  rpt conj_tac >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ac_cursor_skip_assert:
  wf_function fn /\ fn_inst_wf fn /\ ac_cursor_inv fn bb idx s /\
  idx < LENGTH bb.bb_instructions /\
  (EL idx bb.bb_instructions).inst_opcode = ASSERT ==>
  ac_cursor_inv fn bb (SUC idx) (s with vs_inst_idx := SUC idx)
Proof
  rpt strip_tac >>
  `inst_wf (EL idx bb.bb_instructions)` by
    (fs[ac_cursor_inv_def, fn_inst_wf_def] >> metis_tac[EL_MEM]) >>
  `(EL idx bb.bb_instructions).inst_outputs = []` by gvs[inst_wf_def] >>
  `!op. eval_operand op (s with vs_inst_idx := SUC idx) = eval_operand op s`
    by (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  fs[ac_cursor_inv_def] >>
  simp[ac_cursor_inv_def, lookup_var_def, ac_dfg_inv_local_def,
       ac_def_before_suc] >>
  fs[ac_dfg_inv_local_def, lookup_var_def] >>
  rpt conj_tac >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ac_query_predicate_before:
  wf_function fn /\ wf_ssa fn /\ MEM bb fn.fn_blocks /\
  a < LENGTH bb.bb_instructions /\
  (EL a bb.bb_instructions).inst_opcode <> PHI /\
  MEM op (EL a bb.bb_instructions).inst_operands /\
  ac_get_iszero_operand (dfg_build_function fn) visited op = SOME pred ==>
  ?di. ac_def_before fn bb a di /\ di.inst_opcode = ISZERO /\
       di.inst_operands = [pred]
Proof
  rpt strip_tac >> irule ac_query_iszero_before >> simp[] >>
  qexistsl [`dfg_build_function fn`, `op`, `visited`] >>
  simp[] >> reverse conj_tac
  >- (rpt strip_tac >> gvs[] >> irule ac_query_use_before >> metis_tac[]) >>
  rpt strip_tac >>
  `?db j. MEM db fn.fn_blocks /\ j < LENGTH db.bb_instructions /\
          EL j db.bb_instructions = di` by
    (fs[ac_def_before_def] >> metis_tac[EL_MEM, MEM_EL]) >>
  irule ac_query_before_closed >> simp[] >>
  qexistsl [`db`, `j`, `v`] >> simp[]
QED

Theorem ac_query_predicate_step:
  wf_function fn /\ wf_ssa fn /\ MEM bb fn.fn_blocks /\
  a <= idx /\ idx < LENGTH bb.bb_instructions /\
  (EL a bb.bb_instructions).inst_opcode <> PHI /\
  MEM op (EL a bb.bb_instructions).inst_operands /\
  ac_get_iszero_operand (dfg_build_function fn) visited op = SOME pred /\
  step_inst fuel ctx (EL idx bb.bb_instructions) s = OK t ==>
  eval_operand pred t = eval_operand pred s
Proof
  rpt strip_tac >>
  `a < LENGTH bb.bb_instructions` by decide_tac >>
  drule_all ac_query_predicate_before >> strip_tac >>
  `ac_def_before fn bb idx di` by metis_tac[ac_def_before_mono] >>
  Cases_on `pred` >> simp[eval_operand_def]
  >- (irule step_inst_preserves_lookup >>
      `~MEM s' (EL idx bb.bb_instructions).inst_outputs` by
        (irule ac_def_before_operand_not_current >>
         simp[] >> qexistsl [`di`, `fn`] >> simp[]) >> metis_tac[]) >>
  metis_tac[venomExecProofsTheory.step_inst_preserves_labels_always]
QED
