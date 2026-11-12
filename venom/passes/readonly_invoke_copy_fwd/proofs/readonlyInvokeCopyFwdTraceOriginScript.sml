(* Source correspondence before NOP clearing.  Validation remains attached
   to the edited block; correspondence is not validation transport. *)
Theory readonlyInvokeCopyFwdTraceOrigin
Ancestors
  readonlyInvokeCopyFwdPlan readonlyInvokeCopyFwdProtectionOrigin
  readonlyInvokeCopyFwdProtectionSelected list

Theorem ricf_two_event_source_copy:
  ricf_event_ok e bb /\ ricf_event_ok f (ricf_event_apply e bb) /\
  e.rfe_ctx.icf_dfg = dfg_build_function fn /\
  f.rfe_ctx.icf_dfg = dfg_build_function fn /\
  MEM bb fn.fn_blocks /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) ==>
  ricf_event_copy f (ricf_event_apply e bb) = ricf_event_copy f bb
Proof
  strip_tac >>
  `ricf_block_edit bb (ricf_event_apply e bb)` by
    (irule ricf_event_block_edit >> simp[] >>
     metis_tac[ricf_event_current_sites, ricf_block_edit_refl]) >>
  drule ricf_block_edit_EL >> strip_tac >>
  `f.rfe_index < LENGTH (ricf_event_apply e bb).bb_instructions /\
   (ricf_event_copy f (ricf_event_apply e bb)).inst_opcode = MCOPY` by
    metis_tac[ricf_event_copy_shape] >>
  fs[ricf_event_copy_def] >>
  metis_tac[ricf_inst_edit_def]
QED

Theorem ricf_two_event_source_roots:
  ricf_event_ok e bb /\ ricf_event_ok f (ricf_event_apply e bb) /\
  e.rfe_ctx.icf_dfg = dfg_build_function fn /\
  f.rfe_ctx.icf_dfg = dfg_build_function fn /\
  MEM bb fn.fn_blocks /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) ==>
  ricf_event_roots f (ricf_event_apply e bb) = ricf_event_roots f bb
Proof
  strip_tac >> drule_all ricf_two_event_source_copy >>
  simp[ricf_event_roots_def]
QED

(* At a rebuilt DFG, surviving copies and ASSIGN roots still refer back to
   the source.  Neither the INVOKE use lists nor validation are equated. *)
Theorem ricf_later_round_source_descriptor:
  ricf_function_trace ctx0 fn round /\ ssa_form fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_block_edit original current /\
  ricf_event_ok e current /\
  e.rfe_ctx.icf_dfg = dfg_build_function round ==>
  ricf_event_copy e current = ricf_event_copy e original /\
  ?dst src sz.
    (ricf_event_copy e original).inst_operands = [Var dst;src;sz] /\
    ricf_event_roots e current =
      SOME (icf_assign_root (dfg_build_function fn) {} dst,
            icf_assign_root_op (dfg_build_function fn) src, sz) /\
    icf_collect_aliases (dfg_build_function round)
      (icf_assign_root (dfg_build_function round) {} dst) =
    icf_collect_aliases (dfg_build_function fn)
      (icf_assign_root (dfg_build_function fn) {} dst)
Proof
  strip_tac >>
  drule ricf_block_edit_EL >> strip_tac >>
  drule ricf_event_copy_shape >> strip_tac >>
  `ricf_event_copy e current = ricf_event_copy e original` by
    (fs[ricf_event_copy_def] >> metis_tac[ricf_inst_edit_def]) >>
  simp[] >> qexistsl_tac [`dst`,`src`,`sz`] >>
  drule_all ricf_function_trace_assign_root >> strip_tac >>
  drule_all ricf_function_trace_assign_root_op >> strip_tac >>
  drule_all ricf_function_trace_collect_aliases >> strip_tac >>
  simp[ricf_event_roots_def] >> metis_tac[]
QED
