Theory fnBlockPlanStaticAccounting
Ancestors
  fnBlockPlanStaticBalance fnBlockPlanStaticBodyPrefix list venomWf
  asmIR stackPlanGen venomInst removeUnusedSsaProofs livenessTransferProofs
  rich_list fnPlanPrefix

Definition instruction_correction_def:
  instruction_correction inst =
    if inst.inst_opcode = PHI \/ inst.inst_opcode = OFFSET \/
       is_param_opcode inst.inst_opcode \/ inst.inst_opcode = NOP
    then (0:int) else regular_correction inst (source_topics inst)
End

Theorem invoke_compute_operands_no_label[local]:
  inst.inst_opcode = INVOKE ==> ~MEM (Label l) (compute_operands inst)
Proof
  simp[compute_operands_def, get_non_label_operands_def, MEM_FILTER]
QED

Theorem generate_inst_plan_signed_balance:
  inst.inst_opcode <> JMP /\
  (inst.inst_opcode <> PHI ==> LENGTH (compute_operands inst) <= 16) /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  generate_inst_plan lv dfg cfg fn inst nl halting next_term lbl ps = SOME (ops,qs) ==>
  &(LENGTH qs.ps_stack) = (&(LENGTH ps.ps_stack):int) + trace_weight ops +
    instruction_correction inst
Proof
  strip_tac >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def] >>
  Cases_on `is_pre_codegen_opcode inst.inst_opcode` >> simp[] >>
  Cases_on `inst.inst_opcode = INVOKE /\ ~invoke_operands_wf inst` >> simp[] >>
  Cases_on `inst.inst_opcode = PHI` >> simp[]
  >- (strip_tac >> simp[instruction_correction_def] >>
      drule generate_phi_plan_signed_balance >> simp[]) >>
  Cases_on `inst.inst_opcode = OFFSET` >> simp[]
  >- (strip_tac >> simp[instruction_correction_def] >>
      drule generate_offset_plan_signed_balance >> simp[]) >>
  Cases_on `is_param_opcode inst.inst_opcode` >> simp[]
  >- (strip_tac >> gvs[instruction_correction_def, trace_weight_def]) >>
  Cases_on `inst.inst_opcode = NOP` >> simp[]
  >- (strip_tac >> gvs[instruction_correction_def, trace_weight_def]) >>
  strip_tac >> simp[instruction_correction_def] >>
  drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    generate_regular_inst_plan_signed_balance >>
  simp[invoke_compute_operands_no_label]
QED

Theorem regional_body_lower_inv_signed_balance:
  codegen_ready_fn fn /\ MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\ inst = EL i bb.bb_instructions /\
  inst.inst_opcode <> JMP /\
  regional_body_lower_inv (liveness_analyze fn) (dfg_build_function fn) spill_base bb i ps /\
  generate_inst_plan (liveness_analyze fn) (dfg_build_function fn) cfg fn inst
    nl halting next_term bb.bb_label ps = SOME (ops,qs) ==>
  &(LENGTH qs.ps_stack) = (&(LENGTH ps.ps_stack):int) + trace_weight ops +
    instruction_correction inst
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[EL_MEM]) >>
  `inst.inst_opcode <> PHI ==> LENGTH (compute_operands inst) <= 16` by
    (gvs[codegen_ready_fn_def, EVERY_MEM, codegen_ready_inst_def] >>
     metis_tac[EL_MEM]) >>
  `LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack` by
    (irule regional_body_lower_inv_input_capacity >> metis_tac[]) >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    generate_inst_plan_signed_balance >> simp[]
QED

Theorem generate_inst_plan_phi_signed_balance[local]:
  inst.inst_opcode = PHI /\
  generate_inst_plan lv dfg cfg fn inst nl halting next_term lbl ps = SOME (ops,qs) ==>
  &(LENGTH qs.ps_stack) = (&(LENGTH ps.ps_stack):int) + trace_weight ops +
    instruction_correction inst
Proof
  simp[generate_inst_plan_def, is_pre_codegen_opcode_def,
       is_unlowered_fmp_opcode_def, is_unlowered_internal_call_opcode_def,
       is_raw_fmp_opcode_def] >> strip_tac >>
  gvs[instruction_correction_def] >>
  drule generate_phi_plan_signed_balance >> simp[]
QED

Theorem reachable_suffix_signed_balance:
  !xs a ps0 ops psn.
  codegen_ready_fn fn /\ MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  a <= LENGTH bb.bb_instructions /\ start <= a /\
  xs = DROP a bb.bb_instructions /\
  EVERY (\inst. inst.inst_opcode <> JMP) xs /\
  (!j q pre. a <= j /\ j < LENGTH bb.bb_instructions /\
    generate_block_insts_prefix (liveness_analyze fn) (dfg_build_function fn)
      cfg fn bb.bb_label (bb_is_halting bb) start (LENGTH bb.bb_instructions)
      (a-start) (j-a) xs ps0 = SOME (pre,q) /\
    (EL j bb.bb_instructions).inst_opcode <> PHI ==>
    regional_body_lower_inv (liveness_analyze fn) (dfg_build_function fn)
      spill_base bb j q) /\
  generate_block_insts_plan (liveness_analyze fn) (dfg_build_function fn)
    cfg fn bb.bb_label (bb_is_halting bb) start (LENGTH bb.bb_instructions)
    (a-start) xs ps0 = SOME (ops,psn) ==>
  &(LENGTH psn.ps_stack) = (&(LENGTH ps0.ps_stack):int) + trace_weight ops +
    FOLDR ($+) (0:int) (MAP instruction_correction xs)
Proof
  Induct
  >- (simp[generate_block_insts_plan_def] >> rpt strip_tac >> gvs[trace_weight_def]) >>
  rpt gen_tac >> strip_tac >>
  `a < LENGTH bb.bb_instructions` by
    (qpat_x_assum `_ = DROP _ _` (mp_tac o AP_TERM ``LENGTH:instruction list->num``) >>
     simp[] >> decide_tac) >>
  `h = EL a bb.bb_instructions /\ xs = DROP (SUC a) bb.bb_instructions` by
    (drule DROP_CONS_EL >> simp[] >> strip_tac >>
     qpat_x_assum `h::xs = _` mp_tac >> asm_rewrite_tac[] >> simp[]) >>
  qpat_x_assum `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once generate_block_insts_plan_def, AllCaseEqs()] >> strip_tac >>
  gvs[] >>
  qmatch_asmsub_abbrev_tac `generate_inst_plan _ _ _ _ _ next_live _ next_term _ _` >>
  rename1 `generate_inst_plan _ _ _ _ _ _ _ _ _ ps0 = SOME (step_ops,ps1)` >>
  `&(LENGTH ps1.ps_stack) = (&(LENGTH ps0.ps_stack):int) +
    trace_weight step_ops + instruction_correction (EL a bb.bb_instructions)` by
    (Cases_on `(EL a bb.bb_instructions).inst_opcode = PHI`
     >- (drule_all generate_inst_plan_phi_signed_balance >> simp[]) >>
     `regional_body_lower_inv (liveness_analyze fn) (dfg_build_function fn)
       spill_base bb a ps0` by
       (qpat_x_assum `!j q pre. a <= j /\ _ ==> _`
          (qspecl_then [`a`, `ps0`, `[]`] mp_tac) >>
        simp[generate_block_insts_prefix_def]) >>
     drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
       regional_body_lower_inv_signed_balance >> simp[] >> metis_tac[]) >>
  `&(LENGTH psn.ps_stack) = (&(LENGTH ps1.ps_stack):int) +
    trace_weight rest_ops + FOLDR ($+) (0:int)
      (MAP instruction_correction (DROP (SUC a) bb.bb_instructions))` by
    (first_x_assum irule >> simp[] >>
     reverse conj_tac >- fs[arithmeticTheory.ADD1] >> rpt strip_tac >>
     qpat_x_assum `!j q pre. a <= j /\ _ ==> _`
       (qspecl_then [`j`, `q`, `step_ops ++ pre`] mp_tac) >>
     impl_tac >- (simp[] >>
       `j - a = SUC (j - SUC a)` by decide_tac >>
       pop_assum SUBST1_TAC >>
       gvs[Abbr `next_live`, Abbr `next_term`] >>
       qpat_x_assum `_ :: _ = DROP a _` (fn th => once_rewrite_tac[GSYM th]) >>
       fs[Once generate_block_insts_prefix_def, arithmeticTheory.ADD1]) >> simp[]) >>
  simp[trace_weight_append] >> intLib.ARITH_TAC
QED

Theorem generate_inst_plan_jmp_signed_balance:
  inst.inst_opcode = JMP /\ inst.inst_operands = [Label target] /\
  inst.inst_outputs = [] /\
  generate_inst_plan lv dfg cfg fn inst nl halting next_term lbl ps = SOME (ops,qs) ==>
  &(LENGTH qs.ps_stack) = (&(LENGTH ps.ps_stack):int) + trace_weight ops +
    instruction_correction inst
Proof
  strip_tac >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def, is_pre_codegen_opcode_def,
       is_unlowered_fmp_opcode_def, is_unlowered_internal_call_opcode_def,
       is_raw_fmp_opcode_def, is_param_opcode_def] >>
  Cases_on `generate_regular_inst_plan lv dfg cfg fn inst nl halting next_term lbl ps` >>
  simp[] >> strip_tac >> gvs[] >>
  drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    generate_regular_jmp_plan_signed_balance >>
  simp[instruction_correction_def, is_param_opcode_def]
QED

Theorem regional_ready_step_signed_balance:
  codegen_ready_fn fn /\ MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\ inst = EL i bb.bb_instructions /\
  ((inst.inst_opcode <> PHI /\ inst.inst_opcode <> JMP) ==>
    regional_body_lower_inv (liveness_analyze fn) (dfg_build_function fn)
      spill_base bb i ps) /\
  generate_inst_plan (liveness_analyze fn) (dfg_build_function fn) cfg fn inst
    nl halting next_term bb.bb_label ps = SOME (ops,qs) ==>
  &(LENGTH qs.ps_stack) = (&(LENGTH ps.ps_stack):int) + trace_weight ops +
    instruction_correction inst
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode = PHI`
  >- (drule_all generate_inst_plan_phi_signed_balance >> simp[]) >>
  Cases_on `inst.inst_opcode = JMP`
  >- (`inst_wf inst` by
        (gvs[codegen_ready_fn_def, fn_inst_wf_def] >>
         metis_tac[lookup_block_mem, EL_MEM]) >>
      `?target. inst.inst_operands = [Label target] /\ inst.inst_outputs = []` by
        gvs[inst_wf_def] >>
      drule_all generate_inst_plan_jmp_signed_balance >> simp[]) >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    regional_body_lower_inv_signed_balance >> simp[] >> metis_tac[]
QED
