(* Structural interfaces for the SimplifyCFG step contract. *)
Theory simplifyCfgShape
Ancestors
  simplifyCfgDefs simplifyCfgLabelProps venomWf venomInst list rich_list unitShapeDefs

Theorem filter_phi_ops_empty_preds:
  !ops. phi_well_formed ops ==> filter_phi_ops [] ops = []
Proof
  ho_match_mp_tac phi_well_formed_ind >>
  simp[filter_phi_ops_def, phi_well_formed_def]
QED

Theorem fix_phi_inst_empty_preds:
  inst.inst_opcode = PHI /\ phi_well_formed inst.inst_operands ==>
  (fix_phi_inst [] inst).inst_opcode = NOP
Proof
  simp[fix_phi_inst_def, filter_phi_ops_empty_preds]
QED

Theorem fix_phi_inst_terminator:
  is_terminator inst.inst_opcode ==>
  fix_phi_inst actual_preds inst = inst /\ inst.inst_opcode <> PHI
Proof
  Cases_on `inst.inst_opcode` >> simp[is_terminator_def, fix_phi_inst_def]
QED

Theorem fix_phis_in_block_cfg:
  bb.bb_instructions = front ++ [term] /\
  is_terminator term.inst_opcode ==>
  (fix_phis_in_block actual_preds bb).bb_label = bb.bb_label /\
  bb_succs (fix_phis_in_block actual_preds bb) = bb_succs bb
Proof
  strip_tac >> drule fix_phi_inst_terminator >> strip_tac >>
  simp[fix_phis_in_block_def, bb_succs_def, MAP_APPEND, FILTER_APPEND,
       LAST_APPEND] >>
  qmatch_goalsub_abbrev_tac `xs ++ [term]` >>
  Cases_on `xs` >> Cases_on `front` >> simp[LAST_DEF, LAST_APPEND]
QED

Theorem can_bypass_jump_source_distinct:
  lookup_block a.bb_label func.fn_blocks = SOME a /\
  lookup_block b.bb_label func.fn_blocks = SOME b /\
  can_bypass_jump func a b ==>
  a.bb_label <> b.bb_label
Proof
  strip_tac >> strip_tac >>
  `a = b` by metis_tac[optionTheory.SOME_11] >>
  gvs[can_bypass_jump_def]
QED

Theorem filter_phi_ops_well_formed:
  !ops actual_preds. phi_well_formed ops ==>
    phi_well_formed (filter_phi_ops actual_preds ops)
Proof
  ho_match_mp_tac phi_well_formed_ind >>
  simp[phi_well_formed_def, filter_phi_ops_def] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[phi_well_formed_def]
QED

Theorem filter_phi_ops_member:
  !actual_preds ops op. MEM op (filter_phi_ops actual_preds ops) ==> MEM op ops
Proof
  ho_match_mp_tac filter_phi_ops_ind >>
  rw[filter_phi_ops_def] >> metis_tac[]
QED

Theorem remove_phi_label_well_formed:
  !ops lbl. phi_well_formed ops ==>
    phi_well_formed (remove_phi_label lbl ops)
Proof
  ho_match_mp_tac phi_well_formed_ind >>
  simp[phi_well_formed_def, cfgTransformTheory.remove_phi_label_def] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[phi_well_formed_def]
QED

Theorem remove_phi_label_member:
  !lbl ops op. MEM op (remove_phi_label lbl ops) ==> MEM op ops
Proof
  ho_match_mp_tac cfgTransformTheory.remove_phi_label_ind >>
  rw[cfgTransformTheory.remove_phi_label_def] >> metis_tac[]
QED

Theorem fix_phi_inst_id:
  (fix_phi_inst actual_preds inst).inst_id = inst.inst_id
Proof
  rw[fix_phi_inst_def] >>
  Cases_on `filter_phi_ops actual_preds inst.inst_operands` >> simp[] >>
  rename1 `h::rest` >> Cases_on `rest` >> simp[] >>
  rename1 `h::h'::rest` >> Cases_on `rest` >> simp[]
QED

Theorem update_phi_bypass_id:
  (update_phi_bypass a b inst).inst_id = inst.inst_id
Proof
  rw[update_phi_bypass_def]
QED

Theorem canon_jnz_inst_id:
  (canon_jnz_inst inst).inst_id = inst.inst_id
Proof
  simp[canon_jnz_inst_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  rename1 `h::rest` >> Cases_on `rest` >> simp[] >>
  rename1 `h::h'::rest` >> Cases_on `rest` >> simp[] >>
  rename1 `h::h'::h''::rest` >> Cases_on `rest` >> simp[] >>
  rw[]
QED

Theorem fix_phi_inst_var_subset:
  MEM (Var v) (fix_phi_inst actual_preds inst).inst_operands ==>
  MEM (Var v) inst.inst_operands
Proof
  rw[fix_phi_inst_def] >>
  Cases_on `filter_phi_ops actual_preds inst.inst_operands` >> gvs[] >>
  rename1 `filter_phi_ops _ _ = h::rest` >>
  Cases_on `rest` >> gvs[]
  >- metis_tac[filter_phi_ops_member, MEM] >>
  rename1 `filter_phi_ops _ _ = h::h'::rest` >>
  Cases_on `rest` >> gvs[] >>
  metis_tac[filter_phi_ops_member, MEM]
QED

Theorem subst_label_op_var:
  subst_label_op a b op = Var v <=> op = Var v
Proof
  Cases_on `op` >> simp[cfgTransformTheory.subst_label_op_def] >> rw[]
QED

Theorem update_phi_bypass_var_subset:
  MEM (Var v) (update_phi_bypass a b inst).inst_operands ==>
  MEM (Var v) inst.inst_operands
Proof
  rw[update_phi_bypass_def] >> gvs[MEM_MAP, AllCaseEqs()] >>
  metis_tac[remove_phi_label_member]
QED

(* Transport the least closure using seed and copy-edge provenance. *)
Theorem copy_phi_var_transport:
  !origin fn_new x. copy_phi_var origin fn_new x ==>
  !fn_old.
    (!inst v. MEM inst (fn_insts fn_new) /\ inst.inst_opcode = origin /\
      MEM v inst.inst_outputs ==>
      ?old. MEM old (fn_insts fn_old) /\ old.inst_opcode = origin /\
            MEM v old.inst_outputs) /\
    (!inst v w. MEM inst (fn_insts fn_new) /\
      ((inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var w]) \/
       (inst.inst_opcode = PHI /\ MEM (Var w) inst.inst_operands)) /\
      MEM v inst.inst_outputs ==>
      ?old. MEM old (fn_insts fn_old) /\ MEM v old.inst_outputs /\
        ((old.inst_opcode = ASSIGN /\ old.inst_operands = [Var w]) \/
         (old.inst_opcode = PHI /\ MEM (Var w) old.inst_operands))) ==>
    copy_phi_var origin fn_old x
Proof
  Induct_on `copy_phi_var` >> rpt strip_tac
  >- (qpat_x_assum `!inst v. _` (qspecl_then [`inst`, `x`] mp_tac) >>
      simp[] >> strip_tac >> irule copy_phi_var_seed >> metis_tac[]) >>
  (rename1 `copy_phi_var origin fn_new y` >>
   `copy_phi_var origin fn_old y` by (first_x_assum irule >> metis_tac[]) >>
   qpat_x_assum `!inst v w. _`
     (qspecl_then [`inst`, `x`, `y`] mp_tac) >>
   simp[] >> strip_tac
   >- (irule copy_phi_var_assign >> metis_tac[]) >>
   irule copy_phi_var_phi >> metis_tac[])
QED

Theorem fix_phi_inst_wf:
  inst_wf inst ==> inst_wf (fix_phi_inst actual_preds inst)
Proof
  Cases_on `inst.inst_opcode = PHI`
  >- (strip_tac >>
      `phi_well_formed (filter_phi_ops actual_preds inst.inst_operands)`
        by (irule filter_phi_ops_well_formed >> gvs[inst_wf_def]) >>
      simp[fix_phi_inst_def] >>
      Cases_on `filter_phi_ops actual_preds inst.inst_operands` >>
      gvs[inst_wf_def] >>
      rename1 `h::rest` >> Cases_on `rest` >> gvs[inst_wf_def] >>
      rename1 `h::h'::rest` >> Cases_on `rest` >> gvs[inst_wf_def]) >>
  simp[fix_phi_inst_def]
QED

Theorem phi_well_formed_subst_label:
  !ops. phi_well_formed ops ==>
    phi_well_formed (MAP (subst_label_op a b) ops)
Proof
  ho_match_mp_tac phi_well_formed_ind >>
  simp[phi_well_formed_def, cfgTransformTheory.subst_label_op_def] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[phi_well_formed_def]
QED

Theorem update_phi_bypass_wf:
  inst_wf inst ==> inst_wf (update_phi_bypass a b inst)
Proof
  Cases_on `inst.inst_opcode = PHI`
  >- (rw[update_phi_bypass_def] >> gvs[inst_wf_def]
      >- (irule remove_phi_label_well_formed >> simp[]) >>
      `MAP (\op. case op of
              Label l => if l = b then Label a else Label l
            | _ => op) inst.inst_operands =
       MAP (subst_label_op b a) inst.inst_operands` by
        (irule MAP_CONG >> simp[] >> Cases >>
         simp[cfgTransformTheory.subst_label_op_def]) >>
      simp[phi_well_formed_subst_label]) >>
  simp[update_phi_bypass_def]
QED

Theorem canon_jnz_inst_changed:
  canon_jnz_inst inst <> inst ==>
  inst.inst_opcode = JNZ /\
  ?c t. inst.inst_operands = [c; t; t] /\
    canon_jnz_inst inst = inst with <|inst_opcode := JMP; inst_operands := [t]|>
Proof
  simp[canon_jnz_inst_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  rename1 `h::rest` >> Cases_on `rest` >> simp[] >>
  rename1 `h::h'::rest` >> Cases_on `rest` >> simp[] >>
  rename1 `h::h'::h''::rest` >> Cases_on `rest` >> simp[] >>
  rw[] >> gvs[]
QED

Theorem opaque_use_ok_transport:
  opaque_use_ok fn_old /\
  (!x. gas_var fn_new x ==> gas_var fn_old x) /\
  (!x. retpc_var fn_new x ==> retpc_var fn_old x) /\
  (!inst x. MEM inst (fn_insts fn_new) /\ MEM (Var x) inst.inst_operands /\
    inst.inst_opcode <> ASSIGN /\ inst.inst_opcode <> PHI ==>
    ?old. MEM old (fn_insts fn_old) /\
      old.inst_opcode = inst.inst_opcode /\
      old.inst_operands = inst.inst_operands) ==>
  opaque_use_ok fn_new
Proof
  strip_tac >> rw[opaque_use_ok_def] >>
  Cases_on `inst.inst_opcode = ASSIGN` >>
  gvs[gas_use_ok_def, retpc_use_ok_def] >>
  Cases_on `inst.inst_opcode = PHI` >>
  gvs[gas_use_ok_def, retpc_use_ok_def] >>
  qpat_x_assum `!inst x. _`
    (qspecl_then [`inst`, `x`] mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `opaque_use_ok fn_old` mp_tac >>
  simp[opaque_use_ok_def, gas_use_ok_def, retpc_use_ok_def] >>
  metis_tac[]
QED

Theorem fix_phi_inst_opcode_source:
  code <> NOP /\ code <> ASSIGN /\
  (fix_phi_inst actual_preds inst).inst_opcode = code ==>
  inst.inst_opcode = code
Proof
  rw[fix_phi_inst_def] >>
  Cases_on `filter_phi_ops actual_preds inst.inst_operands` >> gvs[] >>
  rename1 `h::rest` >> Cases_on `rest` >> gvs[] >>
  rename1 `h::h'::rest` >> Cases_on `rest` >> gvs[]
QED

Theorem fix_phi_inst_outputs_subset:
  MEM x (fix_phi_inst actual_preds inst).inst_outputs ==>
  MEM x inst.inst_outputs
Proof
  rw[fix_phi_inst_def] >>
  Cases_on `filter_phi_ops actual_preds inst.inst_operands` >> gvs[] >>
  rename1 `h::rest` >> Cases_on `rest` >> gvs[] >>
  rename1 `h::h'::rest` >> Cases_on `rest` >> gvs[]
QED

Theorem fix_phi_inst_copy_source:
  MEM x (fix_phi_inst actual_preds inst).inst_outputs /\
  (((fix_phi_inst actual_preds inst).inst_opcode = ASSIGN /\
    (fix_phi_inst actual_preds inst).inst_operands = [Var y]) \/
   ((fix_phi_inst actual_preds inst).inst_opcode = PHI /\
    MEM (Var y) (fix_phi_inst actual_preds inst).inst_operands)) ==>
  MEM x inst.inst_outputs /\
  ((inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var y]) \/
   (inst.inst_opcode = PHI /\ MEM (Var y) inst.inst_operands))
Proof
  strip_tac >>
  (`MEM x inst.inst_outputs` by metis_tac[fix_phi_inst_outputs_subset] >>
   Cases_on `inst.inst_opcode = PHI`
   >- (simp[] >> metis_tac[fix_phi_inst_var_subset, MEM]) >>
   gvs[fix_phi_inst_def])
QED

Theorem fix_phi_inst_label_positions:
  inst_wf inst /\ label_positions_ok inst ==>
  label_positions_ok (fix_phi_inst actual_preds inst)
Proof
  Cases_on `inst.inst_opcode = PHI`
  >- (strip_tac >>
      `phi_well_formed (filter_phi_ops actual_preds inst.inst_operands)`
        by (irule filter_phi_ops_well_formed >> gvs[inst_wf_def]) >>
      simp[fix_phi_inst_def] >>
      Cases_on `filter_phi_ops actual_preds inst.inst_operands` >>
      gvs[label_positions_ok_def] >>
      rename1 `filter_phi_ops _ _ = h::rest` >>
      Cases_on `rest` >> gvs[label_positions_ok_def] >>
      rename1 `filter_phi_ops _ _ = h::h'::rest` >>
      Cases_on `rest` >> gvs[label_positions_ok_def] >>
      Cases_on `h` >> Cases_on `h'` >>
      gvs[phi_well_formed_def, stackPlanTypesTheory.is_label_operand_def]) >>
  simp[fix_phi_inst_def]
QED

Theorem update_phi_bypass_label_positions:
  label_positions_ok inst ==>
  label_positions_ok (update_phi_bypass a b inst)
Proof
  Cases_on `inst.inst_opcode = PHI` >>
  rw[update_phi_bypass_def] >> simp[label_positions_ok_def]
QED

Theorem fix_phi_inst_opcode_property:
  P inst.inst_opcode /\ P NOP /\ P ASSIGN ==>
  P (fix_phi_inst actual_preds inst).inst_opcode
Proof
  strip_tac >>
  Cases_on `(fix_phi_inst actual_preds inst).inst_opcode = NOP` >> simp[] >>
  Cases_on `(fix_phi_inst actual_preds inst).inst_opcode = ASSIGN` >> simp[] >>
  metis_tac[fix_phi_inst_opcode_source]
QED

Theorem update_phi_bypass_opcode:
  (update_phi_bypass a b inst).inst_opcode = inst.inst_opcode
Proof
  rw[update_phi_bypass_def]
QED

Theorem update_phi_bypass_outputs:
  (update_phi_bypass a b inst).inst_outputs = inst.inst_outputs
Proof
  rw[update_phi_bypass_def]
QED

Theorem canon_jnz_inst_not_jmp:
  (canon_jnz_inst inst).inst_opcode <> JMP ==> canon_jnz_inst inst = inst
Proof
  Cases_on `canon_jnz_inst inst = inst` >- simp[] >>
  drule canon_jnz_inst_changed >> strip_tac >> simp[]
QED

Theorem canon_jnz_inst_opcode_property:
  P inst.inst_opcode /\ P JMP ==> P (canon_jnz_inst inst).inst_opcode
Proof
  strip_tac >> Cases_on `(canon_jnz_inst inst).inst_opcode = JMP` >> simp[] >>
  drule canon_jnz_inst_not_jmp >> strip_tac >> gvs[]
QED

Theorem subst_label_inst_no_label_operands:
  EVERY (\op. ~is_label_operand op) inst.inst_operands ==>
  subst_label_inst a b inst = inst
Proof
  strip_tac >> simp[cfgTransformTheory.subst_label_inst_def] >>
  `MAP (subst_label_op a b) inst.inst_operands = inst.inst_operands` suffices_by
    simp[] >>
  irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >>
  rename1 `n < LENGTH inst.inst_operands` >>
  `~is_label_operand (EL n inst.inst_operands)` by
    (gvs[EVERY_EL] >> first_x_assum irule >> simp[]) >>
  Cases_on `EL n inst.inst_operands` >>
  gvs[stackPlanTypesTheory.is_label_operand_def,
      cfgTransformTheory.subst_label_op_def]
QED

Theorem fix_phi_inst_noncopy_consumer:
  (fix_phi_inst actual_preds inst).inst_opcode <> ASSIGN /\
  (fix_phi_inst actual_preds inst).inst_opcode <> PHI /\
  (fix_phi_inst actual_preds inst).inst_opcode <> NOP ==>
  fix_phi_inst actual_preds inst = inst
Proof
  strip_tac >>
  `inst.inst_opcode <> PHI` by metis_tac[fix_phi_inst_opcode_source] >>
  simp[fix_phi_inst_def]
QED

Theorem update_phi_bypass_copy_source:
  MEM x (update_phi_bypass a b inst).inst_outputs /\
  (((update_phi_bypass a b inst).inst_opcode = ASSIGN /\
    (update_phi_bypass a b inst).inst_operands = [Var y]) \/
   ((update_phi_bypass a b inst).inst_opcode = PHI /\
    MEM (Var y) (update_phi_bypass a b inst).inst_operands)) ==>
  MEM x inst.inst_outputs /\
  ((inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var y]) \/
   (inst.inst_opcode = PHI /\ MEM (Var y) inst.inst_operands))
Proof
  simp[update_phi_bypass_opcode, update_phi_bypass_outputs] >>
  strip_tac
  >- (gvs[update_phi_bypass_def]) >>
  simp[] >> metis_tac[update_phi_bypass_var_subset]
QED

Theorem canon_jnz_inst_copy_source:
  MEM x (canon_jnz_inst inst).inst_outputs /\
  (((canon_jnz_inst inst).inst_opcode = ASSIGN /\
    (canon_jnz_inst inst).inst_operands = [Var y]) \/
   ((canon_jnz_inst inst).inst_opcode = PHI /\
    MEM (Var y) (canon_jnz_inst inst).inst_operands)) ==>
  MEM x inst.inst_outputs /\
  ((inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var y]) \/
   (inst.inst_opcode = PHI /\ MEM (Var y) inst.inst_operands))
Proof
  strip_tac >>
  `(canon_jnz_inst inst).inst_opcode <> JMP` by simp[] >>
  drule canon_jnz_inst_not_jmp >> strip_tac >> gvs[]
QED

Theorem bypass_terminator_label_positions:
  is_terminator inst.inst_opcode /\ inst_wf inst /\ label_positions_ok inst ==>
  label_positions_ok (canon_jnz_inst (subst_label_inst a b inst))
Proof
  strip_tac >> Cases_on `inst.inst_opcode = JNZ`
  >- (gvs[inst_wf_def, label_positions_ok_def] >>
      simp[cfgTransformTheory.subst_label_inst_def,
           cfgTransformTheory.subst_label_op_def] >>
      Cases_on `c` >>
      gvs[label_positions_ok_def, stackPlanTypesTheory.is_label_operand_def,
          cfgTransformTheory.subst_label_op_def, canon_jnz_inst_def] >>
      rpt IF_CASES_TAC >> gvs[label_positions_ok_def,
          stackPlanTypesTheory.is_label_operand_def]) >>
  Cases_on `inst.inst_opcode = JMP`
  >- (gvs[inst_wf_def] >>
      simp[cfgTransformTheory.subst_label_inst_def,
           cfgTransformTheory.subst_label_op_def, canon_jnz_inst_def] >>
      IF_CASES_TAC >> simp[label_positions_ok_def]) >>
  `EVERY (\op. ~is_label_operand op) inst.inst_operands` by
    (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def, label_positions_ok_def]) >>
  `subst_label_inst a b inst = inst` by
    (irule subst_label_inst_no_label_operands >> simp[]) >>
  `canon_jnz_inst inst = inst` by metis_tac[canon_jnz_inst_changed] >>
  simp[]
QED
