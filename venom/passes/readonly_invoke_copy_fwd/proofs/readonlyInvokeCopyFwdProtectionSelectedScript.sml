(* Selected-call inversion uses syntax origins, never a numeric inverse of
   provenance.  The source is isolated by the original source-alloca check. *)
Theory readonlyInvokeCopyFwdProtectionSelected
Ancestors
  readonlyInvokeCopyFwdProtectionProducers occurrenceOrigin
  o1LowerDloadClosure ptrDiscipline invokeCopyFwdCommonDefs readonlyInvokeCopyFwdPlan
  readonlyInvokeCopyFwdDefs readonlyMemoryArgsProps
  internalReturnCopyFwdPlan dfgAnalysisProps indexedLists list pred_set finite_map

Theorem ricf_isolated_pointer_closure:
  (!inst. MEM inst (fn_insts fn) /\ MEM (Var root) inst.inst_operands ==>
     ~is_pointer_preserving_op inst.inst_opcode) ==>
  pointer_derived_vars fn {root} SUBSET {root}
Proof
  strip_tac >> irule pointer_derived_vars_least >> simp[] >> metis_tac[]
QED

Theorem ricf_isolated_occurrence_operand:
  occurrence_syntax_origin fn a H /\ fn_inst_ids_distinct fn /\
  MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\
  ai.inst_outputs = [root] /\
  (!inst. MEM inst (fn_insts fn) /\ MEM (Var root) inst.inst_operands ==>
     ~is_pointer_preserving_op inst.inst_opcode) /\
  op_prov H op = SOME (a,ai.inst_id) ==>
  op = Var root
Proof
  strip_tac >> Cases_on `op` >> gvs[op_prov_def] >>
  drule_all occurrence_syntax_origin_planned_root >> strip_tac >>
  drule ricf_isolated_pointer_closure >> simp[SUBSET_DEF] >> metis_tac[]
QED

(* Successful validation constrains every input use, not just the sites
   accumulated in the result. *)
Theorem ricf_sites_fold_accepted[local]:
  !uses acc sites.
    FOLDL (\acc (v,inst,pos).
      case acc of NONE => NONE | SOME xs =>
        if icf_is_assign_output_use inst pos then SOME xs
        else if inst.inst_opcode = MCOPY /\ pos = 0 then
          if inst.inst_id = copy_id then SOME xs else NONE
        else if inst.inst_opcode = INVOKE /\ icf_is_readonly_op rma inst pos
          then SOME ((inst,pos)::xs) else NONE) acc uses = SOME sites ==>
    acc <> NONE /\ !v inst pos. MEM (v,inst,pos) uses ==>
      icf_is_assign_output_use inst pos \/
      (inst.inst_opcode = MCOPY /\ pos = 0 /\ inst.inst_id = copy_id) \/
      (inst.inst_opcode = INVOKE /\ icf_is_readonly_op rma inst pos)
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >>
  Cases_on `acc` >> simp[] >> strip_tac >>
  first_x_assum drule >> simp[AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ricf_event_alias_use_accepted:
  ricf_event_ok e bb /\ e.rfe_ctx.icf_dfg = dfg_build_function fn /\
  (ricf_event_copy e bb).inst_operands = [Var dst;src;sz] /\
  ircf_alias fn (icf_assign_root (dfg_build_function fn) {} dst) v /\
  MEM inst (fn_insts fn) /\ pos < LENGTH inst.inst_operands /\
  EL pos inst.inst_operands = Var v ==>
  icf_is_assign_output_use inst pos \/
  (inst.inst_opcode = MCOPY /\ pos = 0 /\
     inst.inst_id = (ricf_event_copy e bb).inst_id) \/
  (inst.inst_opcode = INVOKE /\ icf_is_readonly_op e.rfe_ctx.icf_rma inst pos)
Proof
  simp[ricf_event_ok_def, ricf_try_forward_def, ricf_event_copy_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  drule (INST_TYPE [alpha |-> ``:string``] ricf_sites_fold_accepted) >>
  simp[ircf_alias_use_positions_mem]
QED

Theorem ricf_event_destination_pointer_closure:
  ricf_event_ok e bb /\ e.rfe_ctx.icf_dfg = dfg_build_function fn /\
  (ricf_event_copy e bb).inst_operands = [Var dst;src;sz] /\
  fn_inst_wf fn ==>
  pointer_derived_vars fn {icf_assign_root (dfg_build_function fn) {} dst}
    SUBSET {v | ircf_alias fn (icf_assign_root (dfg_build_function fn) {} dst) v}
Proof
  strip_tac >> irule pointer_derived_vars_least >> simp[ircf_alias_refl] >>
  rpt strip_tac >>
  `?pos. pos < LENGTH inst.inst_operands /\
     EL pos inst.inst_operands = Var u` by metis_tac[MEM_EL] >>
  drule_all ricf_event_alias_use_accepted >>
  simp[icf_is_assign_output_use_def] >> strip_tac
  >- metis_tac[ircf_assign_pointer_alias]
  >- gvs[pointerConfinedDefsTheory.is_pointer_preserving_op_def]
  >> gvs[pointerConfinedDefsTheory.is_pointer_preserving_op_def]
QED

Theorem ricf_selected_call_destination_readonly:
  ricf_event_ok e bb /\ e.rfe_ctx.icf_dfg = dfg_build_function fn /\
  (ricf_event_copy e bb).inst_operands = [Var dst;src;sz] /\
  fn_inst_wf fn /\ fn_inst_ids_distinct fn /\
  occurrence_syntax_origin fn a H /\
  MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\
  ai.inst_outputs = [icf_assign_root (dfg_build_function fn) {} dst] /\
  MEM callinst (fn_insts fn) /\ MEM (callinst,p) e.rfe_sites /\
  decode_invoke callinst = SOME (nm,ops) /\
  k < LENGTH ops /\ op_prov H (EL k ops) = SOME (a,ai.inst_id) ==>
  rma_is_readonly e.rfe_ctx.icf_rma nm k
Proof
  strip_tac >> Cases_on `EL k ops` >> gvs[op_prov_def] >>
  drule_all occurrence_syntax_origin_planned_root >> strip_tac >>
  drule_all ricf_event_destination_pointer_closure >>
  simp[SUBSET_DEF] >> strip_tac >>
  drule_all ricf_event_sites_readonly >> strip_tac >>
  `callinst.inst_operands = Label nm :: ops` by
    gvs[venomExecSemanticsTheory.decode_invoke_def, AllCaseEqs()] >>
  rename1 `FLOOKUP H v = SOME (a,ai.inst_id)` >>
  `ircf_alias fn (icf_assign_root (dfg_build_function fn) {} dst) v` by
    metis_tac[] >>
  `icf_is_readonly_op e.rfe_ctx.icf_rma callinst (SUC k)` by
    (`SUC k < LENGTH callinst.inst_operands /\
      EL (SUC k) callinst.inst_operands = Var v` by simp[] >>
     drule_all ricf_event_alias_use_accepted >>
     simp[icf_is_assign_output_use_def]) >>
  gvs[icf_is_readonly_op_def, icf_get_callee_name_def]
QED

Theorem ricf_source_copy_isolated:
  ricf_src_alloca fn /\ MEM bb fn.fn_blocks /\
  k < LENGTH bb.bb_instructions /\
  (EL k bb.bb_instructions).inst_opcode = MCOPY /\
  (EL k bb.bb_instructions).inst_operands = [Var dst;Var sv;sz] /\
  dfg_get_def (dfg_build_function fn)
    (icf_assign_root (dfg_build_function fn) {} dst) = SOME di /\
  icf_is_alloca di ==>
  !inst. MEM inst (fn_insts fn) /\ MEM (Var sv) inst.inst_operands ==>
    ~is_pointer_preserving_op inst.inst_opcode
Proof
  simp[ricf_src_alloca_def] >> metis_tac[]
QED

Theorem ricf_event_source_alloca_name:
  ricf_event_ok e bb /\ e.rfe_ctx.icf_dfg = dfg_build_function fn /\
  (ricf_event_copy e bb).inst_operands = [Var dst;Var sv;sz] /\
  dfg_get_def (dfg_build_function fn) sv = SOME ai /\
  ai.inst_opcode = ALLOCA ==>
  e.rfe_source = SOME sv /\
  icf_assign_root_op e.rfe_ctx.icf_dfg (Var sv) = Var sv
Proof
  `icf_assign_root (dfg_build_function fn) {} sv = sv` by
    (rpt strip_tac >> simp[Once icf_assign_root_def]) >>
  simp[ricf_event_ok_def, ricf_event_copy_def, ricf_try_forward_def,
       icf_assign_root_op_def] >>
  strip_tac >> gvs[AllCaseEqs()]
QED

Theorem ricf_selected_call_source_inversion:
  ricf_event_ok e bb /\ e.rfe_ctx.icf_dfg = dfg_build_function fn /\
  ricf_src_alloca fn /\ MEM bb fn.fn_blocks /\
  (ricf_event_copy e bb).inst_operands = [Var dst;Var sv;sz] /\
  dfg_get_def (dfg_build_function fn)
    (icf_assign_root (dfg_build_function fn) {} dst) = SOME di /\
  icf_is_alloca di /\
  dfg_get_def (dfg_build_function fn) sv = SOME ai /\
  MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [sv] /\
  fn_inst_ids_distinct fn /\ occurrence_syntax_origin fn a H /\
  MEM (callinst,p) e.rfe_sites /\ decode_invoke callinst = SOME (nm,ops) /\
  k < LENGTH ops /\ op_prov H (EL k ops) = SOME (a,ai.inst_id) ==>
  EL k ops = Var sv /\ rma_is_readonly e.rfe_ctx.icf_rma nm k
Proof
  strip_tac >>
  `e.rfe_index < LENGTH bb.bb_instructions /\
   (ricf_event_copy e bb).inst_opcode = MCOPY` by
    metis_tac[ricf_event_copy_shape] >>
  `!inst. MEM inst (fn_insts fn) /\ MEM (Var sv) inst.inst_operands ==>
     ~is_pointer_preserving_op inst.inst_opcode` by
    (irule ricf_source_copy_isolated >> simp[GSYM ricf_event_copy_def] >>
     metis_tac[]) >>
  `EL k ops = Var sv` by
    (irule ricf_isolated_occurrence_operand >> metis_tac[]) >>
  drule_all ricf_event_source_alloca_name >> strip_tac >> simp[] >>
  irule ricf_selected_call_source_readonly >> metis_tac[]
QED
