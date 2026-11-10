Theory loadElimOperandValidity
Ancestors
  loadElimNormalizeHelpers dfgCorrectnessProof dfgDefs venomState venomInst list

Definition le_inst_operands_valid_def:
  le_inst_operands_valid d inst s <=>
    EVERY (\op. le_chain_valid d [] op s) inst.inst_operands
End

Theorem le_dfg_sound_chain_valid:
  !d visited op s. dfg_assigns_sound d s ==> le_chain_valid d visited op s
Proof
  ho_match_mp_tac normalize_operand_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
      simp[Once le_chain_valid_def] >>
      Cases_on `MEM d' visited` >- simp[] >>
      Cases_on `FLOOKUP d.dfg_defs d'` >> simp[] >>
      rename1 `FLOOKUP _ _ = SOME inst` >>
      Cases_on `inst.inst_opcode = ASSIGN` >- (
        Cases_on `inst.inst_operands` >> simp[] >>
        Cases_on `t` >> simp[] >>
        qpat_x_assum `dfg_assigns_sound d s` mp_tac >>
        simp[dfg_assigns_sound_def] >>
        disch_then (qspecl_then [`d'`, `inst`] mp_tac) >> simp[]) >>
      simp[]) >>
  simp[le_chain_valid_def]
QED

Theorem le_dfg_sound_inst_operands_valid:
  dfg_assigns_sound d s ==> le_inst_operands_valid d inst s
Proof
  simp[le_inst_operands_valid_def, EVERY_MEM] >>
  metis_tac[le_dfg_sound_chain_valid]
QED

Theorem le_inst_operands_valid_eval:
  le_inst_operands_valid d inst s /\ MEM op inst.inst_operands ==>
  eval_operand (normalize_operand d [] op) s = eval_operand op s
Proof
  simp[le_inst_operands_valid_def, EVERY_MEM] >>
  metis_tac[le_chain_valid_eval]
QED

Theorem le_chain_valid_literal[simp]:
  le_chain_valid d visited (Lit n) s
Proof
  simp[le_chain_valid_def]
QED

Theorem le_chain_valid_visited:
  MEM v visited ==> le_chain_valid d visited (Var v) s
Proof
  simp[Once le_chain_valid_def]
QED

Theorem le_chain_valid_missing:
  FLOOKUP d.dfg_defs v = NONE ==> le_chain_valid d visited (Var v) s
Proof
  simp[Once le_chain_valid_def]
QED
