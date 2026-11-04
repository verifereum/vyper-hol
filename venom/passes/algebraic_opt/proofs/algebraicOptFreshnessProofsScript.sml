Theory algebraicOptFreshnessProofs
Ancestors
  algebraicOptTraceProofs algebraicOptDominanceProofs venomExecSemantics venomWf venomInst list unitShapeDefs

Theorem ao_resolve_phi_pair:
  !pred ops z. resolve_phi pred ops = SOME (Var z) ==>
    MEM (pred,z) (phi_pairs ops)
Proof
  recInduct resolve_phi_ind >>
  simp[resolve_phi_def, phi_pairs_def] >> rpt strip_tac >> gvs[]
  >- (Cases_on `lbl = prev_bb`
      >- gvs[phi_pairs_def] >>
      gvs[] >> Cases_on `val_op` >> gvs[phi_pairs_def]) >>
  Cases_on `v2` >> simp[phi_pairs_def]
QED

Theorem ao_selected_phi_available:
  !fn bb phi pred z.
    wf_ssa fn /\ MEM bb fn.fn_blocks /\ MEM phi bb.bb_instructions /\
    phi.inst_opcode = PHI /\
    resolve_phi pred phi.inst_operands = SOME (Var z) ==>
    ?pred_bb. MEM pred_bb fn.fn_blocks /\ pred_bb.bb_label = pred /\
      fn_cfg_edge fn pred bb.bb_label /\ def_available_at fn pred_bb NONE z
Proof
  rpt strip_tac >> drule ao_resolve_phi_pair >> strip_tac >>
  fs[wf_ssa_def, def_dominates_uses_def] >>
  first_x_assum drule_all >> simp[phi_edge_uses_wf_def] >>
  metis_tac[]
QED

Theorem ao_distinct_output_index[local]:
  !xs f n m x.
    ALL_DISTINCT (FLAT (MAP f xs)) /\
    n < LENGTH xs /\ m < LENGTH xs /\
    MEM x (f (EL n xs)) /\ MEM x (f (EL m xs)) ==> n = m
Proof
  Induct_on `xs` >- simp[] >>
  rpt gen_tac >> Cases_on `n` >> Cases_on `m` >>
  simp[ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP] >>
  rpt strip_tac >> gvs[] >> metis_tac[MEM_EL]
QED

Theorem ao_output_occurrence_blocks[local]:
  !bbs b1 b2 j1 j2 i1 i2 x.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs))) /\
    MEM b1 bbs /\ MEM b2 bbs /\
    get_instruction b1 j1 = SOME i1 /\
    get_instruction b2 j2 = SOME i2 /\
    MEM x i1.inst_outputs /\ MEM x i2.inst_outputs ==>
    b1 = b2 /\ j1 = j2 /\ i1 = i2
Proof
  Induct_on `bbs` >- simp[] >>
  simp[fn_insts_blocks_def, MAP_APPEND, FLAT_APPEND,
       ALL_DISTINCT_APPEND] >> rpt gen_tac >> strip_tac >> gvs[]
  >- (fs[get_instruction_def, AllCaseEqs()] >>
      metis_tac[ao_distinct_output_index])
  >- (fs[get_instruction_def, AllCaseEqs()] >>
      fs[MEM_FLAT, MEM_MAP, MEM_fn_insts_blocks_iff] >>
      metis_tac[MEM_EL])
  >- (fs[get_instruction_def, AllCaseEqs()] >>
      fs[MEM_FLAT, MEM_MAP, MEM_fn_insts_blocks_iff] >>
      metis_tac[MEM_EL]) >>
  metis_tac[]
QED

Theorem ao_ssa_output_occurrence:
  !fn b1 b2 j1 j2 i1 i2 x.
    wf_ssa fn /\ MEM b1 fn.fn_blocks /\ MEM b2 fn.fn_blocks /\
    get_instruction b1 j1 = SOME i1 /\
    get_instruction b2 j2 = SOME i2 /\
    MEM x i1.inst_outputs /\ MEM x i2.inst_outputs ==>
    b1 = b2 /\ j1 = j2 /\ i1 = i2
Proof
  simp[wf_ssa_def, ssa_form_def, fn_insts_def] >>
  metis_tac[ao_output_occurrence_blocks]
QED

Theorem ao_ssa_transition_writer:
  !fn bb j i x k phase s b.
    wf_ssa fn /\ MEM bb fn.fn_blocks /\
    get_instruction bb j = SOME i /\ MEM x i.inst_outputs /\
    ao_transition_writes fn x (k,phase,s) b ==>
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    (if phase then i.inst_opcode = PHI
     else s.vs_inst_idx = j /\ ~is_terminator i.inst_opcode)
Proof
  rpt gen_tac >> Cases_on `phase` >>
  simp[ao_transition_writes_def] >> strip_tac
  >- (drule venomExecPropsTheory.lookup_block_MEM >> strip_tac >>
      qpat_x_assum `MEM _ _.bb_instructions` mp_tac >>
      rewrite_tac[MEM_EL] >> strip_tac >>
      `get_instruction bb' n = SOME i'` by simp[get_instruction_def] >>
      metis_tac[ao_ssa_output_occurrence]) >>
  drule venomExecPropsTheory.lookup_block_MEM >> strip_tac >>
  metis_tac[ao_ssa_output_occurrence]
QED
