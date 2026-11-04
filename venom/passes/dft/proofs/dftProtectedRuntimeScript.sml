Theory dftProtectedRuntime
Ancestors
  dftProtectedPrefix dftOccurrenceAvailability dftScheduleEdits
  venomExecSemantics venomState venomWf venomInst list sorting finite_map

Definition dft_original_schedule_def:
  dft_original_schedule f b q <=>
    wf_ssa f /\ wf_function f /\ MEM b f.fn_blocks /\
    EVERY inst_wf b.bb_instructions /\ q.bb_label = b.bb_label /\
    ?body. q.bb_instructions =
      FILTER (\i. is_pseudo i.inst_opcode) b.bb_instructions ++ body /\
      PERM body (FILTER (\i. ~is_pseudo i.inst_opcode) b.bb_instructions) /\
      schedule_edges b.bb_instructions dft_must_order q.bb_instructions
End

Definition dft_original_cut_def:
  dft_original_cut f b q s <=>
    dft_original_schedule f b q /\ dft_activation_cut f q s
End

Theorem dft_original_cut_operand_defined:
  dft_original_cut f b q s /\
  q.bb_instructions = pp ++ done ++ y::todo /\
  pp = FILTER (\i. is_pseudo i.inst_opcode) b.bb_instructions /\
  s.vs_inst_idx = LENGTH (pp ++ done) ==>
  !v. MEM (Var v) y.inst_operands ==> v IN FDOM s.vs_vars
Proof
  strip_tac >>
  `dft_activation_cut f q s` by fs[dft_original_cut_def] >>
  `!d v. MEM d (pp ++ done) /\ MEM v d.inst_outputs ==> v IN FDOM s.vs_vars` by
    (`TAKE s.vs_inst_idx q.bb_instructions = pp ++ done` by
       (asm_rewrite_tac[] >>
        pure_once_rewrite_tac[GSYM APPEND_ASSOC] >> simp[TAKE_APPEND1]) >>
     fs[dft_activation_cut_def] >> metis_tac[]) >>
  rpt strip_tac >> irule dft_protected_cut_operand_defined >>
  qexistsl_tac [`b`, `done`, `f`, `pp`, `todo`, `y`] >>
  fs[dft_original_cut_def, dft_original_schedule_def, dft_activation_cut_def] >>
  gvs[] >> metis_tac[APPEND_ASSOC, APPEND]
QED

Theorem dft_original_cut_eval_operand:
  dft_original_cut f b q s /\
  q.bb_instructions = pp ++ done ++ y::todo /\
  pp = FILTER (\i. is_pseudo i.inst_opcode) b.bb_instructions /\
  s.vs_inst_idx = LENGTH (pp ++ done) /\
  (!l. MEM (Label l) y.inst_operands ==> l IN FDOM s.vs_labels) ==>
  !op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v
Proof
  strip_tac >>
  `!v. MEM (Var v) y.inst_operands ==> v IN FDOM s.vs_vars` by
    (metis_tac[dft_original_cut_operand_defined]) >>
  rpt strip_tac >> Cases_on `op` >>
  fs[eval_operand_def, lookup_var_def, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem dft_original_cut_phis:
  q.bb_label = s.vs_current_bb /\ strict_dom_vars_defined f s /\
  eval_phis s q.bb_instructions = OK sp ==>
  dft_activation_cut f q
    (sp with vs_inst_idx := phi_prefix_length q.bb_instructions)
Proof
  metis_tac[dft_activation_cut_phis]
QED
