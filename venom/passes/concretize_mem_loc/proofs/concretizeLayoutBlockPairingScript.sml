Theory concretizeLayoutBlockPairing
Ancestors concretizeStepStructure passSharedProps passSharedDefs passSimulationDefs
  venomExecSemantics venomInst analysisSimProofsBase indexedLists
  list rich_list arithmetic venomWf

(* The structural cursor is independent of the ghost-trace cursor. *)
Definition layout_filter_rank_def:
  layout_filter_rank R P xs k = LENGTH (FILTER P (MAP R (TAKE k xs)))
End

Definition layout_block_pair_def:
  layout_block_pair positions bb bb' k k' <=>
    bb' = clear_nops_block
      (block_map_transform (concretize_inst_with_positions positions) bb) /\
    k' = layout_filter_rank (concretize_inst_with_positions positions)
      (\i. i.inst_opcode <> NOP) bb.bb_instructions k
End

Theorem layout_filter_rank_lookup:
  k < LENGTH xs /\ P (R (EL k xs)) ==>
  layout_filter_rank R P xs k < LENGTH (FILTER P (MAP R xs)) /\
  EL (layout_filter_rank R P xs k) (FILTER P (MAP R xs)) = R (EL k xs)
Proof
  qid_spec_tac `k` >> Induct_on `xs` >> simp[layout_filter_rank_def] >>
  Cases_on `k` >> simp[layout_filter_rank_def] >>
  Cases_on `P (R h)` >> simp[layout_filter_rank_def] >>
  fs[layout_filter_rank_def]
QED

Theorem layout_filter_rank_step:
  k < LENGTH xs ==>
  layout_filter_rank R P xs (SUC k) =
    layout_filter_rank R P xs k + (if P (R (EL k xs)) then 1 else 0)
Proof
  qid_spec_tac `k` >> Induct_on `xs` >> simp[layout_filter_rank_def] >>
  Cases_on `k` >> simp[layout_filter_rank_def] >>
  Cases_on `P (R h)` >> simp[layout_filter_rank_def] >>
  fs[layout_filter_rank_def] >> simp[ADD_CLAUSES]
QED

Theorem layout_block_pair_lookup:
  layout_block_pair positions bb bb' k k' /\
  get_instruction bb k = SOME i /\
  (concretize_inst_with_positions positions i).inst_opcode <> NOP ==>
  get_instruction bb' k' = SOME (concretize_inst_with_positions positions i)
Proof
  simp[layout_block_pair_def, get_instruction_def,
    clear_nops_block_def, block_map_transform_def] >>
  rpt strip_tac >> gvs[] >>
  qspecl_then [`concretize_inst_with_positions positions`,
    `\i. i.inst_opcode <> NOP`, `bb.bb_instructions`, `k`] mp_tac
    (Q.GENL [`R`, `P`, `xs`, `k`] layout_filter_rank_lookup) >> simp[]
QED

Theorem layout_block_pair_advance:
  layout_block_pair positions bb bb' k k' /\
  get_instruction bb k = SOME i ==>
  layout_block_pair positions bb bb' (SUC k)
    (k' + if (concretize_inst_with_positions positions i).inst_opcode <> NOP
          then 1 else 0)
Proof
  simp[layout_block_pair_def, get_instruction_def] >>
  rpt strip_tac >> gvs[] >>
  qspecl_then [`concretize_inst_with_positions positions`,
    `\i. i.inst_opcode <> NOP`, `bb.bb_instructions`, `k`] mp_tac
    (Q.GENL [`R`, `P`, `xs`, `k`] layout_filter_rank_step) >> simp[]
QED

Theorem layout_filter_rank_phi_entry:
  (!i. i.inst_opcode = PHI ==> R i = i) ==>
  layout_filter_rank R (\i. i.inst_opcode <> NOP) xs
    (phi_prefix_length xs) = phi_prefix_length xs
Proof
  strip_tac >> Induct_on `xs` >> rpt gen_tac >>
  simp[phi_prefix_length_def, layout_filter_rank_def] >>
  Cases_on `h.inst_opcode = PHI`
  >- (`R h = h` by metis_tac[] >>
      simp[phi_prefix_length_def, layout_filter_rank_def] >>
      fs[layout_filter_rank_def]) >>
  simp[phi_prefix_length_def, layout_filter_rank_def]
QED

Theorem layout_block_pair_phi_entry:
  bb_well_formed bb /\
  bb' = clear_nops_block
    (block_map_transform (concretize_inst_with_positions positions) bb) ==>
  layout_block_pair positions bb bb'
    (phi_prefix_length bb.bb_instructions)
    (phi_prefix_length bb'.bb_instructions)
Proof
  strip_tac >>
  `FILTER (\i. i.inst_opcode <> NOP)
      (MAP (concretize_inst_with_positions positions) bb.bb_instructions) =
   FLAT (MAPi (\n i. if (concretize_inst_with_positions positions i).inst_opcode <> NOP
      then [concretize_inst_with_positions positions i] else []) bb.bb_instructions)` by
    (qspec_tac (`bb.bb_instructions`, `xs`) >> Induct >>
     simp[MAPi_def] >> rpt gen_tac >>
     Cases_on `(concretize_inst_with_positions positions h).inst_opcode = NOP` >>
     simp[MAPi_def]) >>
  `phi_prefix_length bb'.bb_instructions = phi_prefix_length bb.bb_instructions` by
    (gvs[clear_nops_block_def, block_map_transform_def] >>
     pop_assum kall_tac >>
     qspecl_then [`\n i. if (concretize_inst_with_positions positions i).inst_opcode <> NOP
          then [concretize_inst_with_positions positions i] else []`,
        `bb.bb_instructions`] mp_tac phi_prefix_length_flat_mapi >>
     simp[concretize_positions_phi] >>
     impl_tac >- (rpt conj_tac >> rpt strip_tac >>
       fs[bb_well_formed_def] >>
       simp[COND_RAND, COND_RATOR, concretize_positions_phi] >> metis_tac[]) >> simp[]) >>
  simp[layout_block_pair_def] >>
  sym_tac >> match_mp_tac layout_filter_rank_phi_entry >>
  simp[concretize_positions_phi]
QED

Theorem layout_block_pair_produce:
  MEM bb fn.fn_blocks /\ bb_well_formed bb ==>
  ?bb'. MEM bb' (concretize_function_with_positions positions fn).fn_blocks /\
    bb'.bb_label = bb.bb_label /\
    layout_block_pair positions bb bb'
      (phi_prefix_length bb.bb_instructions)
      (phi_prefix_length bb'.bb_instructions)
Proof
  strip_tac >>
  qexists `clear_nops_block
    (block_map_transform (concretize_inst_with_positions positions) bb)` >>
  conj_tac
  >- (simp[concretize_positions_blocks, MEM_MAP] >> metis_tac[]) >>
  simp[concretize_positions_block_label] >>
  irule layout_block_pair_phi_entry >> simp[]
QED

val _ = export_theory();
