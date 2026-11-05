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
  venomWf venomExecSemantics venomExecProofs simplifyCfgStruct irSupply venomInst list
  makeSsaCurrentCleanupBoundary o1MakeSsaFormats

(* List-level shape boundaries. *)
Theorem phi_prefix_length_prepend:
  !pre xs. EVERY (\i. i.inst_opcode = PHI) pre ==>
    phi_prefix_length (pre ++ xs) = LENGTH pre + phi_prefix_length xs
Proof
  Induct >> simp[phi_prefix_length_def] >> rpt strip_tac >> simp[]
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

(* Renaming keeps positional instruction signatures. *)
Theorem rename_current_inst_signature:
  rename_current_inst s rs i = (rs',s',i') ==>
  (i'.inst_opcode,i'.inst_id,LENGTH i'.inst_outputs) =
  (i.inst_opcode,i.inst_id,LENGTH i.inst_outputs)
Proof
  simp[rename_current_inst_def] >>
  IF_CASES_TAC >> pairarg_tac >> gvs[] >> strip_tac >>
  gvs[] >> drule o1MakeSsaFormatsTheory.rename_current_outputs_length >> simp[]
QED

Theorem rename_current_block_insts_signatures:
  !xs s rs rs' s' ys.
  rename_current_block_insts s rs xs = (rs',s',ys) ==>
  MAP (\i. (i.inst_opcode,i.inst_id,LENGTH i.inst_outputs)) ys =
  MAP (\i. (i.inst_opcode,i.inst_id,LENGTH i.inst_outputs)) xs
Proof
  Induct >> simp[rename_current_block_insts_def] >> rpt gen_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> rpt strip_tac >>
  drule rename_current_inst_signature >> strip_tac >>
  first_x_assum drule >> gvs[]
QED

Theorem update_current_succ_phis_signatures:
  ALL_DISTINCT (MAP basic_block_bb_label bs) ==>
  MAP (\b. (b.bb_label,
    MAP (\i. (i.inst_opcode,i.inst_id,LENGTH i.inst_outputs)) b.bb_instructions))
    (update_current_succ_phis rs cur bs succs) =
  MAP (\b. (b.bb_label,
    MAP (\i. (i.inst_opcode,i.inst_id,LENGTH i.inst_outputs)) b.bb_instructions)) bs
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP basic_block_bb_label
      (update_current_succ_phis rs cur bs succs)) /\
   MAP (\b. (b.bb_label,
     MAP (\i. (i.inst_opcode,i.inst_id,LENGTH i.inst_outputs)) b.bb_instructions))
     (update_current_succ_phis rs cur bs succs) =
   MAP (\b. (b.bb_label,
     MAP (\i. (i.inst_opcode,i.inst_id,LENGTH i.inst_outputs)) b.bb_instructions)) bs`
    suffices_by simp[] >>
  pure_rewrite_tac[update_current_succ_phis_def] >>
  qmatch_goalsub_abbrev_tac `FOLDL upd bs succs` >>
  qspecl_then [`succs`, `upd`, `bs`,
    `\a. ALL_DISTINCT (MAP basic_block_bb_label a) /\
     MAP (\b. (b.bb_label,
       MAP (\i. (i.inst_opcode,i.inst_id,LENGTH i.inst_outputs)) b.bb_instructions)) a =
     MAP (\b. (b.bb_label,
       MAP (\i. (i.inst_opcode,i.inst_id,LENGTH i.inst_outputs)) b.bb_instructions)) bs`]
    mp_tac FOLDL_preserves >>
  impl_tac >- (
  simp[Abbr `upd`] >> rpt strip_tac >>
  Cases_on `lookup_block x a` >> gvs[] >>
  drule makeSsaHelperTheory.lookup_block_label >> strip_tac >>
  simp[cfgTransformPropsTheory.fn_labels_replace_block] >>
  irule EQ_TRANS >> goal_assum (first_assum o mp_then Any mp_tac) >>
  irule simplifyCfgStructTheory.replace_block_projection >> simp[] >>
  simp[MAP_MAP_o, combinTheory.o_DEF] >>
  irule MAP_CONG >> simp[] >> rpt strip_tac >>
  IF_CASES_TAC >> simp[]) >> simp[]
QED

Theorem rename_current_blocks_signatures:
  (!t s rs bs sm ctrs s' bs'.
    ALL_DISTINCT (MAP basic_block_bb_label bs) /\
    rename_current_blocks s rs bs sm t = (ctrs,s',bs') ==>
    MAP (\b. (b.bb_label,
      MAP (\i. (i.inst_opcode,i.inst_id,LENGTH i.inst_outputs)) b.bb_instructions)) bs' =
    MAP (\b. (b.bb_label,
      MAP (\i. (i.inst_opcode,i.inst_id,LENGTH i.inst_outputs)) b.bb_instructions)) bs) /\
  (!ts s ctrs stacks bs sm ctrs' s' bs'.
    ALL_DISTINCT (MAP basic_block_bb_label bs) /\
    rename_current_children s ctrs stacks bs sm ts = (ctrs',s',bs') ==>
    MAP (\b. (b.bb_label,
      MAP (\i. (i.inst_opcode,i.inst_id,LENGTH i.inst_outputs)) b.bb_instructions)) bs' =
    MAP (\b. (b.bb_label,
      MAP (\i. (i.inst_opcode,i.inst_id,LENGTH i.inst_outputs)) b.bb_instructions)) bs)
Proof
  ho_match_mp_tac makeSsaCurrentInductTheory.current_dom_tree_induction >> rpt conj_tac
  >- (rpt strip_tac >>
      gvs[rename_current_blocks_def, AllCaseEqs()] >>
      pairarg_tac >> gvs[] >>
      drule makeSsaHelperTheory.lookup_block_label >> strip_tac >>
      drule rename_current_block_insts_signatures >> strip_tac >>
      first_x_assum (drule_at (Pat `rename_current_children _ _ _ _ _ _ = _`)) >>
      simp[update_current_succ_phis_labels,
        cfgTransformPropsTheory.fn_labels_replace_block] >>
      strip_tac >>
      `ALL_DISTINCT (MAP basic_block_bb_label
        (replace_block lbl (bb with bb_instructions := insts') bs))`
        by simp[cfgTransformPropsTheory.fn_labels_replace_block] >>
      drule update_current_succ_phis_signatures >>
      disch_then (qspecl_then
        [`case ALOOKUP sm lbl of NONE => [] | SOME ss => ss`, `rs1`, `lbl`]
        assume_tac) >>
      `MAP (\b. (b.bb_label,
        MAP (\i. (i.inst_opcode,i.inst_id,LENGTH i.inst_outputs)) b.bb_instructions))
        (replace_block lbl (bb with bb_instructions := insts') bs) =
       MAP (\b. (b.bb_label,
        MAP (\i. (i.inst_opcode,i.inst_id,LENGTH i.inst_outputs)) b.bb_instructions)) bs`
        by (irule simplifyCfgStructTheory.replace_block_projection >> simp[]) >>
      metis_tac[])
  >- simp[rename_current_blocks_def] >>
  rpt strip_tac >> gvs[rename_current_blocks_def] >>
  pairarg_tac >> gvs[] >>
  drule (CONJUNCT1 rename_current_blocks_labels) >> strip_tac >>
  first_x_assum (drule_at (Pat `rename_current_blocks _ _ _ _ _ = _`)) >>
  simp[] >> strip_tac >>
  first_x_assum (drule_at (Pat `rename_current_children _ _ _ _ _ _ = _`)) >>
  simp[]
QED

Theorem lookup_block_projection:
  !f bs cs l b.
  MAP (\b. (b.bb_label,f b)) cs = MAP (\b. (b.bb_label,f b)) bs /\
  lookup_block l bs = SOME b ==>
  ?c. lookup_block l cs = SOME c /\ f c = f b
Proof
  gen_tac >> Induct >> Cases_on `cs` >> simp[lookup_block_def, FIND_thm] >>
  rpt strip_tac >> Cases_on `h.bb_label = l` >> gvs[] >>
  gvs[GSYM lookup_block_def] >> first_x_assum drule_all >> simp[]
QED

Theorem rename_current_blocks_lookup_signatures:
  ALL_DISTINCT (MAP basic_block_bb_label bs) /\
  rename_current_blocks s rs bs sm t = (ctrs,s',bs') /\
  lookup_block l bs = SOME b ==>
  ?b'. lookup_block l bs' = SOME b' /\
    MAP (\i. (i.inst_opcode,i.inst_id,LENGTH i.inst_outputs)) b'.bb_instructions =
    MAP (\i. (i.inst_opcode,i.inst_id,LENGTH i.inst_outputs)) b.bb_instructions
Proof
  rpt strip_tac >>
  drule_all (CONJUNCT1 rename_current_blocks_signatures) >> strip_tac >>
  drule_all (BETA_RULE (Q.ISPEC
    `\b. MAP (\i. (i.inst_opcode,i.inst_id,LENGTH i.inst_outputs)) b.bb_instructions`
    lookup_block_projection)) >> simp[]
QED

(* Cleanup only partitions the leading PHI segment. *)
Theorem simplify_current_phi_opcodes:
  i.inst_opcode = PHI ==>
  (simplify_current_phi i).inst_opcode = PHI \/
  (simplify_current_phi i).inst_opcode = ASSIGN \/
  (simplify_current_phi i).inst_opcode = NOP
Proof
  strip_tac >>
  simp[simplify_current_phi_def, keep_current_phi_vars_def] >>
  IF_CASES_TAC >> simp[] >>
  simp[simplify_current_phi_raw_def] >>
  rpt CASE_TAC >> gvs[]
QED

Theorem simplify_current_phi_prefix_partition:
  !xs phis ord.
  simplify_current_phi_prefix_parts xs = (phis,ord) ==>
  ?copies. ord = copies ++ DROP (phi_prefix_length xs) xs /\
    EVERY (\i. i.inst_opcode = PHI) phis /\
    EVERY (\i. i.inst_opcode = ASSIGN \/ i.inst_opcode = NOP) copies /\
    LENGTH phis + LENGTH copies = phi_prefix_length xs
Proof
  Induct
  >- (simp[simplify_current_phi_prefix_parts_def, phi_prefix_length_def] >>
      rpt strip_tac >> qexists `[]` >> simp[]) >>
  rpt gen_tac >> Cases_on `h.inst_opcode = PHI`
  >- (simp[simplify_current_phi_prefix_parts_def] >>
      pairarg_tac >> gvs[] >>
      Cases_on `(simplify_current_phi h).inst_opcode = PHI`
      >- (gvs[] >> strip_tac >> gvs[] >>
          qexists `copies` >> simp[phi_prefix_length_def]) >>
      gvs[] >> strip_tac >> gvs[] >>
      qexists `simplify_current_phi h :: copies` >>
      simp[phi_prefix_length_def] >>
      drule simplify_current_phi_opcodes >> simp[]) >>
  simp[simplify_current_phi_prefix_parts_def, phi_prefix_length_def] >>
  rpt strip_tac >> qexists `[]` >> simp[]
QED

Theorem reassign_current_inst_ids_projection:
  !ids xs.
  MAP (\i. (i.inst_opcode,LENGTH i.inst_outputs))
    (reassign_current_inst_ids ids xs) =
  MAP (\i. (i.inst_opcode,LENGTH i.inst_outputs)) xs
Proof
  Induct >> Cases_on `xs` >> simp[reassign_current_inst_ids_def]
QED

Theorem reassign_current_inst_ids_phi_prefix:
  !ids xs. phi_prefix_length (reassign_current_inst_ids ids xs) =
           phi_prefix_length xs
Proof
  Induct >> Cases_on `xs` >>
  simp[reassign_current_inst_ids_def, phi_prefix_length_def]
QED

Theorem phi_prefix_length_drop:
  !xs. phi_prefix_length (DROP (phi_prefix_length xs) xs) = 0
Proof
  Induct >- simp[phi_prefix_length_def] >> gen_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[phi_prefix_length_def]
QED

Theorem simplify_current_phi_parts_prefix:
  simplify_current_phi_prefix_parts xs = (phis,ord) ==>
  phi_prefix_length (phis ++ ord) = LENGTH phis
Proof
  strip_tac >> drule simplify_current_phi_prefix_partition >> strip_tac >>
  simp[phi_prefix_length_prepend] >>
  Cases_on `copies` >> gvs[phi_prefix_length_drop, phi_prefix_length_def]
QED

Theorem reassign_current_inst_ids_EL:
  k < LENGTH xs ==>
  (EL k (reassign_current_inst_ids ids xs)).inst_opcode = (EL k xs).inst_opcode /\
  LENGTH (EL k (reassign_current_inst_ids ids xs)).inst_outputs =
  LENGTH (EL k xs).inst_outputs
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`ids`, `xs`] reassign_current_inst_ids_projection) >>
  disch_then (mp_tac o Q.AP_TERM `EL k`) >>
  simp[EL_MAP, makeSsaCurrentCleanupBoundaryTheory.current_reassign_length]
QED

Theorem simplify_current_phi_prefix_bound:
  phi_prefix_length (simplify_current_phi_prefix xs) <= phi_prefix_length xs
Proof
  simp[simplify_current_phi_prefix_def] >> pairarg_tac >> gvs[] >>
  simp[reassign_current_inst_ids_phi_prefix] >>
  drule simplify_current_phi_parts_prefix >> strip_tac >> simp[] >>
  drule simplify_current_phi_prefix_partition >> strip_tac >> simp[]
QED

Theorem simplify_current_phi_prefix_copies:
  phi_prefix_length (simplify_current_phi_prefix xs) <= j /\
  j < phi_prefix_length xs ==>
  (EL j (simplify_current_phi_prefix xs)).inst_opcode = ASSIGN \/
  (EL j (simplify_current_phi_prefix xs)).inst_opcode = NOP
Proof
  simp[simplify_current_phi_prefix_def] >> pairarg_tac >> gvs[] >>
  drule simplify_current_phi_parts_prefix >> strip_tac >>
  drule simplify_current_phi_prefix_partition >> strip_tac >>
  simp[reassign_current_inst_ids_phi_prefix] >> rpt strip_tac >>
  `j < LENGTH (phis ++ ordinary)` by
    (drule simplify_current_phi_prefix_parts_length >> strip_tac >>
     mp_tac (Q.SPEC `xs` venomExecProofsTheory.phi_prefix_length_le) >> simp[]) >>
  drule reassign_current_inst_ids_EL >>
  disch_then (qspec_then `MAP (\i. i.inst_id) xs` strip_assume_tac) >>
  gvs[] >>
  `j - LENGTH phis < LENGTH copies` by simp[] >>
  `j >= LENGTH phis` by simp[] >>
  simp[EL_APPEND_EQN] >>
  gvs[EVERY_EL] >> first_x_assum drule >> simp[]
QED

Theorem simplify_current_phi_prefix_suffix:
  phi_prefix_length xs <= k /\ k < LENGTH xs ==>
  (EL k (simplify_current_phi_prefix xs)).inst_opcode = (EL k xs).inst_opcode /\
  (EL k (simplify_current_phi_prefix xs)).inst_id = (EL k xs).inst_id /\
  LENGTH (EL k (simplify_current_phi_prefix xs)).inst_outputs =
    LENGTH (EL k xs).inst_outputs
Proof
  strip_tac >>
  `(EL k (simplify_current_phi_prefix xs)).inst_id = (EL k xs).inst_id` by
    (qspec_then `xs` mp_tac (GEN_ALL MAP_simplify_current_phi_prefix_ids) >>
     disch_then (mp_tac o Q.AP_TERM `EL k`) >>
     simp[EL_MAP, makeSsaCurrentCleanupBoundaryTheory.current_phi_prefix_length]) >>
  simp[] >>
  simp[simplify_current_phi_prefix_def] >> pairarg_tac >> gvs[] >>
  drule simplify_current_phi_prefix_parts_length >> strip_tac >>
  drule simplify_current_phi_prefix_partition >> strip_tac >>
  `k < LENGTH (phis ++ ordinary)` by simp[] >>
  drule reassign_current_inst_ids_EL >>
  disch_then (qspec_then `MAP (\i. i.inst_id) xs` strip_assume_tac) >>
  `EL k (phis ++ ordinary) = EL k xs` by
    (gvs[] >>
     `k - LENGTH phis - LENGTH copies = k - phi_prefix_length xs` by decide_tac >>
     simp[EL_APPEND_EQN, EL_DROP]) >>
  metis_tac[]
QED

Theorem simplify_current_phi_block_layout:
  LENGTH (simplify_current_phi_block b).bb_instructions = LENGTH b.bb_instructions /\
  phi_prefix_length (simplify_current_phi_block b).bb_instructions <=
    phi_prefix_length b.bb_instructions /\
  (!j. phi_prefix_length (simplify_current_phi_block b).bb_instructions <= j /\
       j < phi_prefix_length b.bb_instructions ==>
       (EL j (simplify_current_phi_block b).bb_instructions).inst_opcode = ASSIGN \/
       (EL j (simplify_current_phi_block b).bb_instructions).inst_opcode = NOP) /\
  (!k. phi_prefix_length b.bb_instructions <= k /\ k < LENGTH b.bb_instructions ==>
       (EL k (simplify_current_phi_block b).bb_instructions).inst_opcode =
         (EL k b.bb_instructions).inst_opcode /\
       (EL k (simplify_current_phi_block b).bb_instructions).inst_id =
         (EL k b.bb_instructions).inst_id /\
       LENGTH (EL k (simplify_current_phi_block b).bb_instructions).inst_outputs =
         LENGTH (EL k b.bb_instructions).inst_outputs)
Proof
  Cases_on `b.bb_instructions` >> simp[simplify_current_phi_block_def] >>
  IF_CASES_TAC >> simp[] >>
  simp[makeSsaCurrentCleanupBoundaryTheory.current_phi_prefix_length, simplify_current_phi_prefix_bound,
       simplify_current_phi_prefix_copies] >>
  rpt strip_tac >> drule simplify_current_phi_prefix_suffix >> simp[]
QED

Theorem simplify_current_phis_if_lookup_shape:
  lookup_block l bs = SOME b ==>
  ?b'. lookup_block l (simplify_current_phis_if enabled bs) = SOME b' /\
    LENGTH b'.bb_instructions = LENGTH b.bb_instructions /\
    phi_prefix_length b'.bb_instructions <= phi_prefix_length b.bb_instructions /\
    (!j. phi_prefix_length b'.bb_instructions <= j /\
         j < phi_prefix_length b.bb_instructions ==>
         (EL j b'.bb_instructions).inst_opcode = ASSIGN \/
         (EL j b'.bb_instructions).inst_opcode = NOP) /\
    (!k. phi_prefix_length b.bb_instructions <= k /\ k < LENGTH b.bb_instructions ==>
         (EL k b'.bb_instructions).inst_opcode = (EL k b.bb_instructions).inst_opcode /\
         (EL k b'.bb_instructions).inst_id = (EL k b.bb_instructions).inst_id /\
         LENGTH (EL k b'.bb_instructions).inst_outputs =
           LENGTH (EL k b.bb_instructions).inst_outputs)
Proof
  strip_tac >> Cases_on `enabled` >>
  simp[simplify_current_phis_if_def, simplify_current_phis_def]
  >- (Cases_on `blocks_have_leading_phi bs` >> simp[]
      >- (drule_at Any lookup_block_map_relation >>
          disch_then (qspec_then `simplify_current_phi_block` mp_tac) >>
          simp[] >> strip_tac >>
          simp[simplify_current_phi_block_layout]) >>
      qexists `b` >> simp[]) >>
  qexists `b` >> simp[]
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
  rpt strip_tac >>
  qpat_x_assum `make_ssa_input_ok _` kall_tac >>
  qpat_x_assum `fn_inst_wf _` kall_tac >>
  qpat_x_assum `first_block_no_preds _` kall_tac >>
  qpat_x_assum `first_block_no_phi _` kall_tac >>
  qpat_x_assum `ir_supply_covers_fn _ _` kall_tac >>
  qpat_x_assum `ir_supply_inst_ok _` kall_tac >>
  qpat_x_assum `make_ssa_current_fn _ _ = _` mp_tac >>
  simp[make_ssa_current_fn_def] >> CASE_TAC >> simp[]
  >- (rpt strip_tac >> gvs[] >> qexists `bb` >> simp[]) >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `add_phi_nodes_supply s df pm li fn.fn_blocks defs` >>
  qmatch_asmsub_abbrev_tac `rename_current_blocks s1 rs bs sm dt` >>
  drule_all add_phi_nodes_supply_prefix >> strip_tac >>
  drule add_phi_nodes_supply_labels >> strip_tac >>
  `ALL_DISTINCT (MAP basic_block_bb_label bs)` by
    gvs[wf_function_def, fn_labels_def] >>
  drule_all rename_current_blocks_lookup_signatures >> strip_tac >>
  drule_all simplify_current_phis_if_lookup_shape >>
  disch_then (qspec_then `blocks_have_leading_phi fn.fn_blocks` mp_tac) >>
  strip_tac >>
  rename1 `lookup_block l (simplify_current_phis_if _ _) = SOME out` >>
  qexists `out` >> simp[] >>
  drule instruction_signatures_length >> strip_tac >>
  drule instruction_signatures_prefix >> strip_tac >>
  gvs[phi_prefix_length_prepend] >>
  gen_tac >> strip_tac >>
  qpat_x_assum `MAP _ b''.bb_instructions = _`
    (mp_tac o Q.AP_TERM `EL (k + LENGTH pre)`) >>
  simp[EL_APPEND_EQN, EL_MAP]
QED

Theorem make_ssa_current_fn_lookup_block_rev:
  wf_function fn /\ make_ssa_current_fn s fn = (fn',s') /\
  lookup_block l fn'.fn_blocks = SOME bb' ==>
  ?bb. lookup_block l fn.fn_blocks = SOME bb
Proof
  rpt strip_tac >> drule make_ssa_current_fn_labels >> strip_tac >>
  drule makeSsaHelperTheory.lookup_block_labels_agree >>
  disch_then (qspec_then `l` mp_tac) >> simp[] >>
  Cases_on `lookup_block l fn.fn_blocks` >> simp[]
QED
