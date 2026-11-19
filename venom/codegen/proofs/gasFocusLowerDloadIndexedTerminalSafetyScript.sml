(* Pointwise access and taint transport along the indexed terminal slice. *)
Theory gasFocusLowerDloadIndexedTerminalSafety
Ancestors
  lowerDloadPtrTerminal venomInst venomState list finite_map pred_set
  ptrDiscipline o1PassContract venomWf contextCodegenRel unitShapeDefs
  lowerDloadPtrRawReachable codegenRel memLocDefs

Theorem ld_focus_indexed_terminal_safety:
  o1_ctx_shape C /\ access_ok lo G f (EL k mid) s /\ taint_ok f tn (EL k mid) s /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  frame_reachable vs C cs PG G tn f (EL k mid) s /\
  MEM bb f.fn_blocks /\
  lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  lookup_block t.vs_current_bb g.fn_blocks = SOME tb /\
  s.vs_inst_idx = a+k /\ t.vs_inst_idx = b+k /\
  TAKE (LENGTH mid) (DROP a bb.bb_instructions) = mid /\
  a+LENGTH mid <= LENGTH bb.bb_instructions /\
  mid <> [] /\ EVERY (\j. j.inst_opcode = ASSIGN) (FRONT mid) /\
  (LAST mid).inst_opcode = REVERT /\ k < LENGTH mid /\
  lower_dload_block_supply bs bb = (tb,bt) /\
  set (fn_ir_vars f) SUBSET set bs.irs_used_vars /\
  (!j v. MEM j bb.bb_instructions /\ MEM (Var v) j.inst_operands ==>
     v IN set (fn_ir_vars f)) /\
  (!h. h <= LENGTH mid ==> ?pre u.
    lower_dload_insts_supply bs (TAKE (a+h) bb.bb_instructions) = (pre,u) /\
    LENGTH pre = b+h) /\
  FDOM G SUBSET fn_pv P f /\ s.vs_labels = t.vs_labels /\
  dload_live_layout lo sf tf fs /\
  dload_vars_match fl fs (set (fn_ir_vars f) DIFF {v | retpc_var f v})
    G H tn un s t ==>
  access_ok lo H g (EL k mid) t /\ taint_ok g un (EL k mid) t
Proof
  strip_tac >> drule_all dload_terminal_slice_opcode >> strip_tac >>
  Cases_on `k+1 < LENGTH mid`
  >- metis_tac[dload_terminal_assign_access, dload_terminal_assign_taint] >>
  `k+1 = LENGTH mid` by decide_tac >>
  `(EL k mid).inst_opcode = REVERT` by metis_tac[] >>
  `active_inst f (EL k mid) s` by
    (irule dload_slice_active >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `MEM f C.ctx_functions` by
    (drule frame_reachable_raw_certificate >> simp[] >> strip_tac >> simp[]) >>
  `MEM (EL k mid) (fn_insts f)` by
    (gvs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `opaque_use_ok f` by
    (qpat_x_assum `o1_ctx_shape C` mp_tac >>
     simp[o1_ctx_shape_def, EVERY_MEM] >> strip_tac >>
     first_x_assum drule >> simp[o1_fn_shape_def, fn_shape_ok_def]) >>
  reverse conj_tac
  >- (`!v. MEM (Var v) (EL k mid).inst_operands ==>
            v IN set (fn_ir_vars f) DIFF {v | retpc_var f v}` by
        (rpt strip_tac >> irule dload_terminal_operand_origin >>
         simp[] >> metis_tac[]) >>
      drule_all dload_terminal_revert_taint >> simp[]) >>
  Cases_on `?dst sz. (EL k mid).inst_operands = [dst;sz]`
  >- (pop_assum strip_assume_tac >>
      `fn_ptr_ok P f` by metis_tac[EVERY_MEM] >>
      qpat_x_assum `!h. h <= LENGTH mid ==> _` (qspec_then `k` mp_tac) >>
      simp[] >> strip_tac >>
      `in_revert_forward f s ==> in_revert_forward g t` by
        (strip_tac >> irule lower_dload_terminal_forward_guard >>
         goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      drule_all dload_terminal_revert_access >> simp[]) >>
  simp[access_ok_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, mem_write_ops_def, mem_read_ops_def] >>
  namedCases_on `(EL k mid).inst_operands` ["", "dst tail"] >> gvs[] >>
  namedCases_on `tail` ["", "sz rest"] >> gvs[] >> Cases_on `rest` >> gvs[]
QED
