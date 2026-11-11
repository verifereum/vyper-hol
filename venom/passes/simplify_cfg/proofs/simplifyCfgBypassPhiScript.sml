(* PHI operand interfaces for jump bypass, including coalesced edges. *)
Theory simplifyCfgBypassPhi
Ancestors
  simplifyCfgDefs simplifyCfgMergeEntry simplifyCfgFixupStatic
  venomWf venomExecSemantics cfgTransform
  list option

Theorem scfg_resolve_phi_remove:
  !ops. phi_well_formed ops ==>
  resolve_phi p (remove_phi_label b ops) =
    if p = b then NONE else resolve_phi p ops
Proof
  recInduct phi_well_formed_ind >>
  simp[phi_well_formed_def, remove_phi_label_def, resolve_phi_def] >>
  rpt strip_tac >> rpt IF_CASES_TAC >> gvs[resolve_phi_def]
QED

Theorem scfg_resolve_phi_absent:
  !ops. phi_well_formed ops ==>
  (resolve_phi a ops = NONE <=> ~MEM (Label a) ops)
Proof
  recInduct phi_well_formed_ind >>
  simp[phi_well_formed_def, resolve_phi_def] >>
  metis_tac[]
QED

Theorem scfg_resolve_phi_replace:
  !ops. phi_well_formed ops /\ ~MEM (Label a) ops /\ a <> b ==>
  resolve_phi p (MAP (subst_label_op b a) ops) =
    if p = a then resolve_phi b ops
    else if p = b then NONE else resolve_phi p ops
Proof
  recInduct phi_well_formed_ind >>
  simp[phi_well_formed_def, resolve_phi_def, subst_label_op_def] >>
  rpt strip_tac >> rpt IF_CASES_TAC >> gvs[resolve_phi_def]
QED

Theorem scfg_update_phi_bypass_ops:
  i.inst_opcode = PHI ==>
  (update_phi_bypass a b i).inst_operands =
    if MEM (Label a) i.inst_operands then remove_phi_label b i.inst_operands
    else MAP (subst_label_op b a) i.inst_operands
Proof
  strip_tac >> Cases_on `MEM (Label a) i.inst_operands` >>
  simp[update_phi_bypass_def] >> irule MAP_CONG >> simp[] >>
  Cases >> simp[subst_label_op_def]
QED

Theorem scfg_update_phi_bypass_resolve:
  i.inst_opcode = PHI /\ phi_well_formed i.inst_operands /\ a <> b ==>
  resolve_phi p (update_phi_bypass a b i).inst_operands =
    if p = b then NONE
    else if p = a /\ resolve_phi a i.inst_operands = NONE
      then resolve_phi b i.inst_operands else resolve_phi p i.inst_operands
Proof
  strip_tac >> simp[scfg_update_phi_bypass_ops] >>
  Cases_on `MEM (Label a) i.inst_operands`
  >- (simp[scfg_resolve_phi_remove] >>
      `resolve_phi a i.inst_operands <> NONE` by metis_tac[scfg_resolve_phi_absent] >>
      simp[]) >>
  `resolve_phi a i.inst_operands = NONE` by metis_tac[scfg_resolve_phi_absent] >>
  simp[scfg_resolve_phi_replace] >> rpt IF_CASES_TAC >> gvs[]
QED

Theorem scfg_phi_agreement_prefix:
  !xs i va vb. phi_values_agree a b xs /\
    MEM i (TAKE (phi_prefix_length xs) xs) /\
    resolve_phi a i.inst_operands = SOME va /\
    resolve_phi b i.inst_operands = SOME vb ==> va = vb
Proof
  Induct >> simp[phi_prefix_length_def] >> rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI` >>
  simp[phi_prefix_length_def, phi_values_agree_def] >>
  rpt strip_tac >>
  Cases_on `resolve_phi a h.inst_operands` >>
  Cases_on `resolve_phi b h.inst_operands` >> gvs[] >> metis_tac[]
QED

Theorem scfg_phi_agreement_member:
  bb_well_formed bb /\ phi_values_agree a b bb.bb_instructions /\
  MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\
  resolve_phi a i.inst_operands = SOME va /\
  resolve_phi b i.inst_operands = SOME vb ==> va = vb
Proof
  strip_tac >>
  `EVERY (\j. j.inst_opcode <> PHI)
    (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)` by
    (irule scfg_phi_suffix_nonphi >> fs[bb_well_formed_def]) >>
  `MEM i (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)` by
    (qpat_x_assum `MEM i bb.bb_instructions` mp_tac >>
     qspecl_then [`phi_prefix_length bb.bb_instructions`, `bb.bb_instructions`]
       (fn th => once_rewrite_tac[GSYM th]) TAKE_DROP >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  metis_tac[scfg_phi_agreement_prefix]
QED

Theorem scfg_update_phi_bypass_selected:
  bb_well_formed bb /\ phi_values_agree a b bb.bb_instructions /\
  MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\
  phi_well_formed i.inst_operands /\ a <> b /\
  resolve_phi p i.inst_operands = SOME v ==>
  resolve_phi (if p = b then a else p)
    (update_phi_bypass a b i).inst_operands = SOME v
Proof
  strip_tac >> Cases_on `p = b` >> gvs[]
  >- (simp[scfg_update_phi_bypass_resolve] >>
      Cases_on `resolve_phi a i.inst_operands` >> simp[] >>
      metis_tac[scfg_phi_agreement_member]) >>
  simp[scfg_update_phi_bypass_resolve] >> IF_CASES_TAC >> gvs[]
QED

(* The base lemma, as a rewrite for the bypass proofs. *)
Theorem update_phi_bypass_shape_rw[simp] = simplifyCfgStructTheory.update_phi_bypass_shape
