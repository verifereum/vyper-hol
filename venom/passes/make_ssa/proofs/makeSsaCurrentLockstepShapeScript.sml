(*
 * Where MakeSSA puts each input instruction: the block of the same label
 * in its output, shifted by the number of instructions the block gained.
 *
 * MakeSSA only prepends PHIs to a block, renames instructions in place
 * and, when its input had PHIs, rearranges the leading PHI prefix into
 * the PHIs that stay PHIs followed by the collapsed ASSIGN/NOP copies.
 * So every instruction from the input's first non-PHI on sits d places
 * later in the output block, d = LENGTH out - LENGTH in, with its opcode,
 * id and output count; and between the output's own PHI prefix and the
 * shifted input prefix there are only ASSIGNs and NOPs.
 *)
Theory makeSsaCurrentLockstepShape
Ancestors
  makeSsaCurrentProps makeSsaCurrentDefs o1PassContract unitShapeDefs
  venomWf venomExecSemantics irSupply venomInst list

(* List-level shape boundaries. *)
Theorem phi_prefix_length_prepend:
  !pre xs. EVERY (\i. i.inst_opcode = PHI) pre ==>
    phi_prefix_length (pre ++ xs) = LENGTH pre + phi_prefix_length xs
Proof
  Induct >> simp[phi_prefix_length_def] >> rpt strip_tac >> simp[]
QED

Theorem phi_prefix_length_bound:
  !xs. phi_prefix_length xs <= LENGTH xs
Proof
  Induct >> simp[phi_prefix_length_def] >>
  Cases_on `h.inst_opcode = PHI` >> simp[]
QED

Theorem instruction_signatures_length:
  MAP (\i. (i.inst_opcode,i.inst_id,LENGTH i.inst_outputs)) xs =
  MAP (\i. (i.inst_opcode,i.inst_id,LENGTH i.inst_outputs)) ys ==>
  LENGTH xs = LENGTH ys
Proof
  metis_tac[LENGTH_MAP]
QED

Theorem instruction_signatures_prefix:
  !xs ys.
  MAP (\i. (i.inst_opcode,i.inst_id,LENGTH i.inst_outputs)) xs =
  MAP (\i. (i.inst_opcode,i.inst_id,LENGTH i.inst_outputs)) ys ==>
  phi_prefix_length xs = phi_prefix_length ys
Proof
  Induct_on `xs` >- (Cases_on `ys` >> simp[phi_prefix_length_def]) >>
  gen_tac >> Cases_on `ys` >> simp[] >> rpt strip_tac >>
  gvs[phi_prefix_length_def] >> metis_tac[]
QED

Theorem instruction_signatures_EL:
  MAP (\i. (i.inst_opcode,i.inst_id,LENGTH i.inst_outputs)) xs =
  MAP (\i. (i.inst_opcode,i.inst_id,LENGTH i.inst_outputs)) ys /\
  k < LENGTH xs ==>
  (EL k xs).inst_opcode = (EL k ys).inst_opcode /\
  (EL k xs).inst_id = (EL k ys).inst_id /\
  LENGTH (EL k xs).inst_outputs = LENGTH (EL k ys).inst_outputs
Proof
  rpt strip_tac >>
  drule instruction_signatures_length >> strip_tac >>
  qpat_x_assum `MAP _ xs = MAP _ ys` (mp_tac o Q.AP_TERM `EL k`) >>
  simp[EL_MAP]
QED

Theorem replace_block_projection:
  ALL_DISTINCT (MAP basic_block_bb_label bs) /\
  lookup_block l bs = SOME b /\ f b' = f b ==>
  MAP f (replace_block l b' bs) = MAP f bs
Proof
  rpt strip_tac >> simp[cfgTransformTheory.replace_block_def] >>
  ho_match_mp_tac MAP_replace_at_FIND_distinct >>
  qexists `b` >> simp[] >>
  gvs[lookup_block_def, GSYM bb_label_eta]
QED

Theorem lookup_block_map_relation:
  (!b. (f b).bb_label = b.bb_label) /\
  lookup_block l bs = SOME b ==>
  lookup_block l (MAP f bs) = SOME (f b)
Proof
  qid_spec_tac `b` >> qid_spec_tac `bs` >>
  Induct >> simp[lookup_block_def, FIND_thm] >>
  rpt strip_tac >> Cases_on `h.bb_label = l` >> gvs[] >>
  gvs[lookup_block_def]
QED

(* Insertion only adds PHIs at the head. *)
Theorem insert_phi_lookup_prefix:
  lookup_block l bs = SOME b /\ phi.inst_opcode = PHI ==>
  ?b' pre.
    lookup_block l
      (MAP (\bb. if bb.bb_label = target then
                   insert_phi_at_block phi bb else bb) bs) = SOME b' /\
    b'.bb_instructions = pre ++ b.bb_instructions /\
    EVERY (\i. i.inst_opcode = PHI) pre
Proof
  rpt strip_tac >>
  drule_at Any lookup_block_map_relation >>
  disch_then (qspec_then
    `\bb. if bb.bb_label = target then insert_phi_at_block phi bb else bb`
    mp_tac) >>
  simp[makeSsaDefsTheory.insert_phi_at_block_def] >>
  (impl_tac >- (gen_tac >> IF_CASES_TAC >> simp[])) >> strip_tac >>
  Cases_on `b.bb_label = target`
  >- (qexistsl [`insert_phi_at_block phi b`, `[phi]`] >>
      gvs[makeSsaDefsTheory.insert_phi_at_block_def]) >>
  qexistsl [`b`, `[]`] >> gvs[]
QED

Theorem process_frontiers_supply_prefix:
  !fs s var pm li bs rest hp bs' rest' hp' s' l b.
  process_frontiers_supply s var pm li bs rest hp fs =
    (bs',rest',hp',s') /\ lookup_block l bs = SOME b ==>
  ?b' pre. lookup_block l bs' = SOME b' /\
    b'.bb_instructions = pre ++ b.bb_instructions /\
    EVERY (\i. i.inst_opcode = PHI) pre
Proof
  Induct >- (simp[process_frontiers_supply_def] >>
    rpt strip_tac >> qexistsl [`b`, `[]`] >> simp[]) >>
  pop_assum $ mk_asm "ih" >>
  simp[process_frontiers_supply_def] >> rpt gen_tac >>
  IF_CASES_TAC >> gvs[]
  >- (rpt strip_tac >> asm "ih" drule_all >> simp[]) >>
  IF_CASES_TAC >> gvs[]
  >- (rpt strip_tac >> asm "ih" drule_all >> simp[]) >>
  rpt CASE_TAC >> gvs[] >> pairarg_tac >> gvs[] >> rpt strip_tac >>
  drule insert_phi_lookup_prefix >>
  disch_then (qspecl_then [`h`, `build_phi_inst_supply id var
     (case ALOOKUP pm h of NONE => [] | SOME ps => ps)`] mp_tac) >>
  simp[build_phi_inst_supply_def] >> strip_tac >>
  gvs[build_phi_inst_supply_def] >>
  asm "ih" drule_all >> strip_tac >>
  qexistsl [`b''`, `pre' ++ pre`] >> simp[EVERY_APPEND, APPEND_ASSOC]
QED

Theorem insert_phis_for_var_supply_prefix:
  !s var df pm li bs wl hp bs' s' l b.
  insert_phis_for_var_supply s var df pm li bs wl hp = (bs',s') /\
  lookup_block l bs = SOME b ==>
  ?b' pre. lookup_block l bs' = SOME b' /\
    b'.bb_instructions = pre ++ b.bb_instructions /\
    EVERY (\i. i.inst_opcode = PHI) pre
Proof
  recInduct insert_phis_for_var_supply_ind >>
  rw[insert_phis_for_var_supply_def] >> gvs[] >>
  rpt CASE_TAC >> gvs[] >> pairarg_tac >> gvs[] >> rpt strip_tac >>
  drule_all process_frontiers_supply_prefix >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl [`b''`, `pre' ++ pre`] >> simp[EVERY_APPEND, APPEND_ASSOC]
QED

Theorem add_phi_nodes_supply_prefix:
  !defs s df pm li bs bs' s' l b.
  add_phi_nodes_supply s df pm li bs defs = (bs',s') /\
  lookup_block l bs = SOME b ==>
  ?b' pre. lookup_block l bs' = SOME b' /\
    b'.bb_instructions = pre ++ b.bb_instructions /\
    EVERY (\i. i.inst_opcode = PHI) pre
Proof
  Induct
  >- (simp[add_phi_nodes_supply_def] >> rpt strip_tac >>
      qexistsl [`b`, `[]`] >> simp[]) >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[add_phi_nodes_supply_def] >> pairarg_tac >> gvs[] >> rpt strip_tac >>
  drule_all insert_phis_for_var_supply_prefix >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl [`b''`, `pre' ++ pre`] >> simp[EVERY_APPEND, APPEND_ASSOC]
QED

Theorem make_ssa_current_fn_block_shape:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') /\
  lookup_block l fn.fn_blocks = SOME bb ==>
  ?bb'. lookup_block l fn'.fn_blocks = SOME bb' /\
    LENGTH bb.bb_instructions <= LENGTH bb'.bb_instructions /\
    phi_prefix_length bb'.bb_instructions <=
      phi_prefix_length bb.bb_instructions +
      (LENGTH bb'.bb_instructions - LENGTH bb.bb_instructions) /\
    (!j. phi_prefix_length bb'.bb_instructions <= j /\
         j < phi_prefix_length bb.bb_instructions +
             (LENGTH bb'.bb_instructions - LENGTH bb.bb_instructions) ==>
         (EL j bb'.bb_instructions).inst_opcode = ASSIGN \/
         (EL j bb'.bb_instructions).inst_opcode = NOP) /\
    !k. phi_prefix_length bb.bb_instructions <= k /\
        k < LENGTH bb.bb_instructions ==>
        (EL (k + (LENGTH bb'.bb_instructions - LENGTH bb.bb_instructions))
            bb'.bb_instructions).inst_opcode =
          (EL k bb.bb_instructions).inst_opcode /\
        (EL (k + (LENGTH bb'.bb_instructions - LENGTH bb.bb_instructions))
            bb'.bb_instructions).inst_id =
          (EL k bb.bb_instructions).inst_id /\
        LENGTH (EL (k + (LENGTH bb'.bb_instructions -
                         LENGTH bb.bb_instructions))
                   bb'.bb_instructions).inst_outputs =
          LENGTH (EL k bb.bb_instructions).inst_outputs
Proof
  cheat
QED

Theorem make_ssa_current_fn_lookup_block_rev:
  wf_function fn /\ make_ssa_current_fn s fn = (fn',s') /\
  lookup_block l fn'.fn_blocks = SOME bb' ==>
  ?bb. lookup_block l fn.fn_blocks = SOME bb
Proof
  cheat
QED
