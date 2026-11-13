Theory concretizeLayoutParameterSteps
Ancestors concretizeLayoutCalleeRoots concretizeLayoutParameterRoots
  frameRelocationCleanValueSteps frameRelocationTaintOrder
  frameResolvedOrigins frameOriginUpdates frameRelocationGuardedValues
  frameRelocationGhostCopy frameRelocationLocal frameRelocationMemory ptrDiscipline
  venomExecSemantics venomState finite_map pred_set words list

Theorem parameter_step_taint:
  inst.inst_opcode = PARAM /\ inst.inst_operands = [Lit idx] /\
  inst.inst_outputs = [out] ==>
  step_taint inst s (update_var out x s) tn =
    tn with t_var := tn.t_var |+ (out,{})
Proof
  strip_tac >>
  `new_site_bytes s (update_var out x s) = {}` by
    (irule new_site_bytes_unchanged >> simp[update_var_def]) >>
  simp[step_taint_def, mem_taint_def, step_writes_def,
    codegenRelTheory.source_memory_write_ranges_def, written_taint_def,
    range_bytes_def, store_taint_def, adopt_reset_def, imm_taint_def,
    out_taint_def, eval_operand_def, set_var_taint_def, taint_component_equality]
QED

Theorem parameter_step_resolution:
  inst.inst_opcode = PARAM /\ inst.inst_operands = [Lit idx] /\
  inst.inst_outputs = [out] /\
  PG = MAP (OPTION_MAP SND) rp /\ resolution ct rp om rv ==>
  resolution ct rp (origin_step PG om inst post)
    (origin_set rv [out] (resolved_parameter_entry rp (w2n idx)))
Proof
  strip_tac >> Cases_on `w2n idx < LENGTH rp`
  >- (simp[origin_step_def, origin_out_def, EL_MAP] >>
      irule resolution_origin_set >> simp[] >>
      Cases_on `EL (w2n idx) rp` >> simp[] >>
      PairCases_on `x` >> simp[resolve_tag_def]) >>
  simp[origin_step_def, origin_out_def] >>
  irule resolution_origin_set >> simp[resolve_tag_def]
QED

Theorem parameter_root_write:
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R Obs s t /\
  clean_resolved_root L entry x y /\
  (!a b x y. Obs a b ==> Obs (update_var out x a) (update_var out y b)) ==>
  local_rel (\u. F) (guarded_ptr Opaque L (origin_set rv [out] entry))
    (guarded_bytes Opaque (origin_set rv [out] entry)
      (tn with t_var := tn.t_var |+ (out,{}))) R Obs
    (update_var out x s) (update_var out y t)
Proof
  strip_tac >> irule local_rel_update_observation_invariant >>
  simp[] >> reverse (rpt conj_tac)
  >- (qexistsl_tac [`guarded_bytes Opaque rv tn`, `\u. F`,
        `guarded_ptr Opaque L rv`] >>
      simp[guarded_ptr_other, guarded_bytes_other]) >> (Cases_on `entry` >>
      gvs[clean_resolved_root_def, guarded_ptr_def, guarded_bytes_def,
        copy_ptr_def, copy_bytes_def, origin_set_lookup, op_taint_def,
        FLOOKUP_UPDATE, word_agree_except_def, AllCaseEqs()]) >>
  rpt strip_tac >> gvs[]
QED

Theorem resolved_parameter_step:
  inst.inst_opcode = PARAM /\ inst.inst_operands = [Lit idx] /\
  inst.inst_outputs = [out] /\
  parameter_roots (\i x y. clean_resolved_root L (resolved_parameter_entry rp i) x y)
    s.vs_params t.vs_params /\
  PG = MAP (OPTION_MAP SND) rp /\ resolution ct rp om rv /\
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R Obs s t /\
  relocation_taint_le R tn un /\
  (!a b x y. Obs a b ==> Obs (update_var out x a) (update_var out y b)) /\
  step_inst_base inst s = OK post ==>
  ?post' rv'. step_inst_base inst t = OK post' /\
    rv' = origin_set rv [out] (resolved_parameter_entry rp (w2n idx)) /\
    resolution ct rp (origin_step PG om inst post) rv' /\
    local_rel (\u. F) (guarded_ptr Opaque L rv')
      (guarded_bytes Opaque rv' (step_taint inst s post tn)) R Obs post post' /\
    relocation_taint_le R (step_taint inst s post tn)
      (step_taint inst t post' un) /\
    parameter_roots (\i x y. clean_resolved_root L (resolved_parameter_entry rp i) x y)
      post.vs_params post'.vs_params
Proof
  strip_tac >>
  `w2n idx < LENGTH s.vs_params` by
    (qpat_x_assum `step_inst_base inst s = OK post` mp_tac >>
     pure_once_rewrite_tac[step_inst_base_def] >>
     asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
     gvs[AllCaseEqs()] >> metis_tac[]) >>
  drule_at (Pos (el 4)) parameter_roots_read >>
  disch_then (drule_at (Pos last)) >> simp[] >> strip_tac >> gvs[] >>
  `step_taint inst s (update_var out x s) tn =
     tn with t_var := tn.t_var |+ (out,{})` by
    (irule parameter_step_taint >> simp[]) >>
  `step_taint inst t (update_var out y t) un =
     un with t_var := un.t_var |+ (out,{})` by
    (irule parameter_step_taint >> simp[]) >>
  simp[] >> conj_tac
  >- (irule parameter_step_resolution >> simp[]) >>
  conj_tac
  >- (irule parameter_root_write >> simp[] >> goal_assum (drule_at Any)) >>
  irule relocation_clean_write_taint >> simp[] >> goal_assum (drule_at Any) >> simp[]
QED

(* Caller erasure is discharged here, not carried as an extra call-site premise. *)
Theorem resolved_call_parameter_step:
  resolution caller_ct caller_rp caller_om caller_rv /\
  inst.inst_opcode = PARAM /\ inst.inst_operands = [Lit idx] /\
  inst.inst_outputs = [out] /\
  parameter_roots (\i x y. clean_resolved_root L
    (resolved_parameter_entry (MAP (resolved_op caller_rv) ops) i) x y) s.vs_params t.vs_params /\
  LENGTH ops = LENGTH s.vs_params /\
  resolution ct (MAP (resolved_op caller_rv) ops) om rv /\
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R Obs s t /\
  relocation_taint_le R tn un /\
  (!a b x y. Obs a b ==> Obs (update_var out x a) (update_var out y b)) /\
  step_inst_base inst s = OK post ==>
  ?post' rv'. step_inst_base inst t = OK post' /\
    rv' = origin_set rv [out] (resolved_parameter_entry (MAP (resolved_op caller_rv) ops) (w2n idx)) /\
    resolution ct (MAP (resolved_op caller_rv) ops)
      (origin_step (MAP (op_prov (origin_erase caller_om)) ops) om inst post) rv' /\
    local_rel (\u. F) (guarded_ptr Opaque L rv')
      (guarded_bytes Opaque rv' (step_taint inst s post tn)) R Obs post post' /\
    relocation_taint_le R (step_taint inst s post tn)
      (step_taint inst t post' un) /\
    parameter_roots (\i x y. clean_resolved_root L
      (resolved_parameter_entry (MAP (resolved_op caller_rv) ops) i) x y) post.vs_params post'.vs_params
Proof
  strip_tac >>
  qpat_assum `resolution caller_ct caller_rp caller_om caller_rv`
    (mp_then Any assume_tac resolution_arguments_erasure) >>
  irule resolved_parameter_step >> simp[]
QED
