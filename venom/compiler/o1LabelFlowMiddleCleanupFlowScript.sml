Theory o1LabelFlowMiddleCleanupFlow
Ancestors
  o1LabelFlowMiddleCleanup codegenSymRel makeSsaDefs
  makeSsaCurrentLockstepShape venomExecProofs venomInst unitLabelMapIdentity list

Theorem remove_phi_self_operand:
  !out ops a. MEM a (remove_current_phi_self out ops) ==> MEM a ops
Proof
  recInduct remove_current_phi_self_ind >>
  rpt strip_tac >> gvs[remove_current_phi_self_def] >>
  Cases_on `v = out` >> gvs[] >> metis_tac[]
QED

Theorem phi_values_operand:
  !ops vs. current_phi_values ops = SOME vs ==>
    !v. MEM v vs ==> MEM (Var v) ops
Proof
  recInduct current_phi_values_ind >>
  simp[current_phi_values_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem simplified_phi_operand:
  MEM (Var v) (simplify_current_phi i).inst_operands ==>
  MEM (Var v) i.inst_operands
Proof
  simp[simplify_current_phi_def, keep_current_phi_vars_def] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `i.inst_opcode = PHI` >> simp[simplify_current_phi_raw_def] >>
  Cases_on `current_phi_output i.inst_outputs` >> simp[] >>
  rename1 `current_phi_output _ = SOME out` >>
  Cases_on `current_phi_values (remove_current_phi_self out i.inst_operands)` >> simp[] >>
  rename1 `current_phi_values _ = SOME vs` >>
  Cases_on `vs` >> simp[] >> IF_CASES_TAC >> simp[] >>
  metis_tac[phi_values_operand, remove_phi_self_operand, MEM]
QED

Theorem cleanup_reassign_payloads:
  !ids xs. MAP (\i. (i.inst_opcode,i.inst_operands,i.inst_outputs))
    (reassign_current_inst_ids ids xs) =
    MAP (\i. (i.inst_opcode,i.inst_operands,i.inst_outputs)) xs
Proof
  Induct >> Cases_on `xs` >> simp[reassign_current_inst_ids_def]
QED

Theorem cleanup_parts_origin:
  !xs ps cs. simplify_current_phi_prefix_parts xs = (ps,cs) ==>
  !i. MEM i (ps ++ cs) ==>
    (?j. MEM j xs /\ i = j) \/
    (?j. MEM j xs /\ j.inst_opcode = PHI /\ i = simplify_current_phi j)
Proof
  Induct >> simp[simplify_current_phi_prefix_parts_def] >>
  rpt gen_tac >> Cases_on `h.inst_opcode = PHI`
  >- (simp[] >> Cases_on `simplify_current_phi_prefix_parts xs` >> gvs[] >>
      Cases_on `(simplify_current_phi h).inst_opcode = PHI` >>
      gvs[] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  simp[] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem cleanup_parts_retain:
  !xs ps cs. simplify_current_phi_prefix_parts xs = (ps,cs) ==>
  !i. MEM i xs /\ i.inst_opcode <> PHI ==> MEM i (ps ++ cs)
Proof
  Induct >> simp[simplify_current_phi_prefix_parts_def] >>
  rpt gen_tac >> Cases_on `h.inst_opcode = PHI`
  >- (simp[] >> Cases_on `simplify_current_phi_prefix_parts xs` >> gvs[] >>
      Cases_on `(simplify_current_phi h).inst_opcode = PHI` >>
      gvs[] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  simp[] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem cleanup_prefix_origin:
  MEM i (simplify_current_phi_prefix xs) ==>
  ?j. MEM j xs /\
    ((i.inst_opcode = j.inst_opcode /\ i.inst_operands = j.inst_operands /\
      i.inst_outputs = j.inst_outputs) \/
     (j.inst_opcode = PHI /\
      i.inst_opcode = (simplify_current_phi j).inst_opcode /\
      i.inst_operands = (simplify_current_phi j).inst_operands /\
      i.inst_outputs = (simplify_current_phi j).inst_outputs))
Proof
  simp[simplify_current_phi_prefix_def] >> pairarg_tac >> gvs[] >> strip_tac >>
  `MEM (i.inst_opcode,i.inst_operands,i.inst_outputs)
    (MAP (\i. (i.inst_opcode,i.inst_operands,i.inst_outputs)) (phis ++ ordinary))` by
    (mp_tac (Q.SPECL [`MAP (\i. i.inst_id) xs`, `phis ++ ordinary`]
       cleanup_reassign_payloads) >>
     disch_then (SUBST1_TAC o SYM) >> simp[MEM_MAP] >> qexists `i` >> simp[]) >>
  gvs[MEM_MAP] >> drule cleanup_parts_origin >>
  disch_then (qspec_then `i'` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem cleanup_prefix_retain:
  MEM i xs /\ i.inst_opcode <> PHI ==>
  ?j. MEM j (simplify_current_phi_prefix xs) /\
      j.inst_opcode = i.inst_opcode /\ j.inst_operands = i.inst_operands /\
      j.inst_outputs = i.inst_outputs
Proof
  strip_tac >> simp[simplify_current_phi_prefix_def] >> pairarg_tac >> gvs[] >>
  `MEM i (phis ++ ordinary)` by metis_tac[cleanup_parts_retain] >>
  mp_tac (Q.SPECL [`MAP (\i. i.inst_id) xs`, `phis ++ ordinary`]
    cleanup_reassign_payloads) >>
  disch_then (mp_tac o Q.AP_TERM `MEM (i.inst_opcode,i.inst_operands,i.inst_outputs)`) >>
  simp[MEM_MAP] >> metis_tac[MEM_APPEND]
QED

Theorem cleanup_block_origin:
  MEM i (simplify_current_phi_block b).bb_instructions ==>
  ?j. MEM j b.bb_instructions /\
    ((i.inst_opcode = j.inst_opcode /\ i.inst_operands = j.inst_operands /\
      i.inst_outputs = j.inst_outputs) \/
     (j.inst_opcode = PHI /\
      i.inst_opcode = (simplify_current_phi j).inst_opcode /\
      i.inst_operands = (simplify_current_phi j).inst_operands /\
      i.inst_outputs = (simplify_current_phi j).inst_outputs))
Proof
  Cases_on `b.bb_instructions` >> simp[simplify_current_phi_block_def] >>
  IF_CASES_TAC >> simp[] >> rpt strip_tac
  >- (drule cleanup_prefix_origin >> simp[]) >> metis_tac[]
QED

Theorem cleanup_block_retain:
  MEM i b.bb_instructions /\ i.inst_opcode <> PHI ==>
  ?j. MEM j (simplify_current_phi_block b).bb_instructions /\
      j.inst_opcode = i.inst_opcode /\ j.inst_operands = i.inst_operands /\
      j.inst_outputs = i.inst_outputs
Proof
  Cases_on `b.bb_instructions` >> simp[simplify_current_phi_block_def] >>
  IF_CASES_TAC
  >- (simp[] >> rpt strip_tac >> irule cleanup_prefix_retain >> simp[]) >>
  simp[] >> rpt strip_tac >> metis_tac[]
QED

Theorem cleanup_if_origin:
  MEM i (fn_insts (f with fn_blocks := simplify_current_phis_if enabled f.fn_blocks)) ==>
  ?j. MEM j (fn_insts f) /\
    ((i.inst_opcode = j.inst_opcode /\ i.inst_operands = j.inst_operands /\
      i.inst_outputs = j.inst_outputs) \/
     (j.inst_opcode = PHI /\
      i.inst_opcode = (simplify_current_phi j).inst_opcode /\
      i.inst_operands = (simplify_current_phi j).inst_operands /\
      i.inst_outputs = (simplify_current_phi j).inst_outputs))
Proof
  simp[fn_insts_def, fn_insts_blocks_def, simplify_current_phis_if_def,
       simplify_current_phis_def] >>
  Cases_on `enabled /\ blocks_have_leading_phi f.fn_blocks` >> simp[] >>
  gvs[fn_insts_MEM_block, MEM_MAP] >> rpt strip_tac >> gvs[]
  >- (drule cleanup_block_origin >> strip_tac >>
      qexists `j` >> simp[] >> metis_tac[]) >> metis_tac[]
QED

Theorem cleanup_if_retain:
  MEM i (fn_insts f) /\ i.inst_opcode <> PHI ==>
  ?j. MEM j (fn_insts (f with fn_blocks := simplify_current_phis_if enabled f.fn_blocks)) /\
      j.inst_opcode = i.inst_opcode /\ j.inst_operands = i.inst_operands /\
      j.inst_outputs = i.inst_outputs
Proof
  simp[fn_insts_def, fn_insts_blocks_def, simplify_current_phis_if_def,
       simplify_current_phis_def] >>
  Cases_on `enabled /\ blocks_have_leading_phi f.fn_blocks` >> simp[] >>
  gvs[fn_insts_MEM_block, MEM_MAP] >> rpt strip_tac >> gvs[]
  >- (drule_all cleanup_block_retain >> strip_tac >>
      qexists `j` >> simp[] >> metis_tac[]) >> metis_tac[]
QED

Theorem cleanup_code_end_forward:
  !f x. code_end_var f x ==> !enabled.
    code_end_var (f with fn_blocks := simplify_current_phis_if enabled f.fn_blocks) x
Proof
  Induct_on `code_end_var` >> rpt strip_tac >>
  `inst.inst_opcode <> PHI` by simp[] >>
  drule_all cleanup_if_retain >>
  disch_then (qspec_then `enabled` strip_assume_tac) >>
  metis_tac[code_end_var_rules]
QED

Theorem cleanup_phi_no_protected_read:
  label_flow_ok (ctx with ctx_functions := [f]) /\
  MEM i (fn_insts f) /\ i.inst_opcode = PHI /\ code_end_var f x ==>
  ~MEM (Var x) (simplify_current_phi i).inst_operands
Proof
  simp[label_flow_ok_def] >> rpt strip_tac >>
  drule simplified_phi_operand >> strip_tac >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[] >>
  metis_tac[]
QED

Theorem cleanup_code_end_backward:
  !g x. code_end_var g x ==> !f enabled ctx.
    g = f with fn_blocks := simplify_current_phis_if enabled f.fn_blocks /\
    label_flow_ok (ctx with ctx_functions := [f]) ==> code_end_var f x
Proof
  Induct_on `code_end_var` >> rpt strip_tac >> gvs[] >>
  drule cleanup_if_origin >> strip_tac >> gvs[]
  >- (irule (cj 1 code_end_var_rules) >> qexistsl [`j`, `op`] >> simp[]) 
  >- (drule simplify_current_phi_opcodes >> gvs[]) 
  >- (rename1 `j.inst_operands = [Var src]` >>
      irule (cj 2 code_end_var_rules) >> qexistsl [`j`, `src`] >> simp[] >>
      metis_tac[]) >>
  rename1 `inst.inst_operands = [Var src]` >>
  `code_end_var f src` by metis_tac[] >>
  drule_all cleanup_phi_no_protected_read >> simp[]
QED

Theorem cleanup_code_end_iff:
  label_flow_ok (ctx with ctx_functions := [f]) ==>
  !x. code_end_var (f with fn_blocks := simplify_current_phis_if enabled f.fn_blocks) x <=>
      code_end_var f x
Proof
  metis_tac[cleanup_code_end_forward, cleanup_code_end_backward]
QED

Theorem cleanup_if_inst_flow:
  label_flow_ok (ctx with ctx_functions := [f]) /\
  MEM i (fn_insts (f with fn_blocks := simplify_current_phis_if enabled f.fn_blocks)) ==>
  i.inst_opcode <> CODESIZE /\
  (!x. MEM (Var x) i.inst_operands /\ code_end_var f x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz.
      i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) /\
  (i.inst_opcode = CODECOPY ==> ?dst src sz.
    i.inst_operands = [dst;src;sz] /\
    (src = Label "runtime_begin" \/ ?x. src = Var x /\ code_end_var f x))
Proof
  strip_tac >> drule cleanup_if_origin >> strip_tac >> gvs[]
  >- (qpat_x_assum `label_flow_ok _` mp_tac >>
      simp[label_flow_ok_def] >> disch_then (qspec_then `j` mp_tac) >>
      simp[]) >>
  drule simplify_current_phi_opcodes >> strip_tac >> gvs[] >>
  simp[] >> rpt strip_tac >>
  metis_tac[cleanup_phi_no_protected_read]
QED

Theorem simplify_current_phis_if_label_flow:
  label_flow_ok (ctx with ctx_functions := [f]) ==>
  label_flow_ok (ctx with ctx_functions :=
    [f with fn_blocks := simplify_current_phis_if enabled f.fn_blocks])
Proof
  strip_tac >> drule cleanup_code_end_iff >>
  disch_then (qspec_then `enabled` assume_tac) >>
  simp[label_flow_ok_def] >> rpt strip_tac >>
  drule_all cleanup_if_inst_flow >> metis_tac[]
QED
