Theory lowerDloadControlPosition
Ancestors
  o1ContractLowerDload lowerDloadSupplySegment lowerDloadDefs venomExecSemantics contextCodegenRel venomInst list rich_list venomExecProps venomState

(* Position inversion is lower_dload_insts_supply_position in the ancestor.
   Retain its offset witness rather than duplicating that theorem. *)
Theorem lower_dload_insts_supply_segment_index:
  lower_dload_insts_supply a pre = (p,a1) /\
  lower_dload_inst_supply a1 i = (c,a2) /\
  lower_dload_insts_supply a2 post = (tail,b) /\
  lower_dload_insts_supply a ins = (outs,b) /\
  ins = pre ++ i::post /\ k < LENGTH c ==>
  EL (LENGTH p + k) outs = EL k c /\
  EL (LENGTH pre) ins = i
Proof
  strip_tac >>
  drule_all lower_dload_insts_supply_segment_reconstruct >>
  strip_tac >> gvs[] >>
  simp[EL_APPEND1, EL_APPEND2]
QED

Theorem lower_dload_inst_supply_nonphi_head[local]:
  lower_dload_inst_supply a i = (c,b) /\ i.inst_opcode <> PHI ==>
  c <> [] /\ (HD c).inst_opcode <> PHI
Proof
  strip_tac >>
  `c <> []` by metis_tac[lower_dload_inst_supply_nonempty] >>
  simp[] >> strip_tac >>
  `MEM (HD c) c` by (Cases_on `c` >> gvs[]) >>
  metis_tac[lower_dload_inst_supply_control]
QED

Theorem lower_dload_insts_supply_phi_length:
  !ins a outs b.
    lower_dload_insts_supply a ins = (outs,b) ==>
    phi_prefix_length outs = phi_prefix_length ins
Proof
  Induct >- simp[lower_dload_insts_supply_def, phi_prefix_length_def] >>
  rpt gen_tac >>
  Cases_on `lower_dload_inst_supply a h` >>
  Cases_on `lower_dload_insts_supply r ins` >>
  simp[lower_dload_insts_supply_def] >> strip_tac >> gvs[] >>
  Cases_on `h.inst_opcode = PHI`
  >- (`lower_dload_inst_supply a h = ([h],a)` by
        (irule lower_dload_inst_supply_special >> simp[]) >>
      gvs[phi_prefix_length_def] >> first_x_assum drule >> simp[]) >>
  drule_all lower_dload_inst_supply_nonphi_head >> strip_tac >>
  Cases_on `q` >> gvs[phi_prefix_length_def]
QED

Theorem lower_dload_insts_supply_eval_phis:
  !ins a outs b s.
    lower_dload_insts_supply a ins = (outs,b) ==>
    eval_phis s outs = eval_phis s ins
Proof
  Induct >- simp[lower_dload_insts_supply_def, eval_phis_def] >>
  rpt gen_tac >>
  Cases_on `lower_dload_inst_supply a h` >>
  Cases_on `lower_dload_insts_supply r ins` >>
  simp[lower_dload_insts_supply_def] >> strip_tac >> gvs[] >>
  Cases_on `h.inst_opcode = PHI`
  >- (`lower_dload_inst_supply a h = ([h],a)` by
        (irule lower_dload_inst_supply_special >> simp[]) >>
      gvs[] >> first_x_assum drule >>
      disch_then (qspec_then `s` assume_tac) >> simp[eval_phis_def]) >>
  drule_all lower_dload_inst_supply_nonphi_head >> strip_tac >>
  Cases_on `q` >> gvs[eval_phis_def]
QED

Theorem lower_dload_blocks_supply_lookup:
  !bs a bs' b lbl bb'.
    lower_dload_blocks_supply a bs = (bs',b) /\
    lookup_block lbl bs' = SOME bb' ==>
    ?bb a1 a2. lookup_block lbl bs = SOME bb /\
                 lower_dload_block_supply a1 bb = (bb',a2)
Proof
  Induct >- simp[lower_dload_blocks_supply_def, lookup_block_def, FIND_thm] >>
  rpt gen_tac >>
  Cases_on `lower_dload_block_supply a h` >>
  Cases_on `lower_dload_blocks_supply r bs` >>
  simp[lower_dload_blocks_supply_def] >> strip_tac >> gvs[] >>
  `q.bb_label = h.bb_label` by
    gvs[lower_dload_block_supply_def, AllCaseEqs()] >>
  Cases_on `h.bb_label = lbl`
  >- (gvs[lookup_block_def, FIND_thm] >> metis_tac[]) >>
  gvs[lookup_block_def, FIND_thm] >>
  first_x_assum drule_all >> strip_tac >> metis_tac[]
QED

Theorem lower_dload_blocks_supply_lookup_forward:
  !bs a bs' b lbl bb.
    lower_dload_blocks_supply a bs = (bs',b) /\
    lookup_block lbl bs = SOME bb ==>
    ?bb' a1 a2. lookup_block lbl bs' = SOME bb' /\
                 lower_dload_block_supply a1 bb = (bb',a2)
Proof
  Induct >- simp[lower_dload_blocks_supply_def, lookup_block_def, FIND_thm] >>
  rpt gen_tac >>
  Cases_on `lower_dload_block_supply a h` >>
  Cases_on `lower_dload_blocks_supply r bs` >>
  simp[lower_dload_blocks_supply_def] >> strip_tac >> gvs[] >>
  `q.bb_label = h.bb_label` by
    gvs[lower_dload_block_supply_def, AllCaseEqs()] >>
  Cases_on `h.bb_label = lbl`
  >- (gvs[lookup_block_def, FIND_thm] >> metis_tac[]) >>
  gvs[lookup_block_def, FIND_thm] >>
  first_x_assum drule_all >> strip_tac >> metis_tac[]
QED

Theorem lower_dload_block_supply_phis:
  lower_dload_block_supply a bb = (bb',b) ==>
  eval_phis s bb'.bb_instructions = eval_phis s bb.bb_instructions /\
  phi_prefix_length bb'.bb_instructions = phi_prefix_length bb.bb_instructions
Proof
  simp[lower_dload_block_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  metis_tac[lower_dload_insts_supply_phi_length, lower_dload_insts_supply_eval_phis]
QED

Theorem lower_dload_function_supply_enters_block:
  lower_dload_function_supply a fn = (fn',b) ==>
  (enters_block fn' s u <=> enters_block fn s u)
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  simp[enters_block_def] >> eq_tac >> strip_tac
  >- (drule_all lower_dload_blocks_supply_lookup >> strip_tac >>
      drule lower_dload_block_supply_phis >>
      disch_then (qspec_then `s` strip_assume_tac) >> metis_tac[]) >>
  drule_all lower_dload_blocks_supply_lookup_forward >> strip_tac >>
  drule lower_dload_block_supply_phis >>
  disch_then (qspec_then `s` strip_assume_tac) >> metis_tac[]
QED

Theorem lower_dload_blocks_supply_block_origin:
  !bs a bs' b bb'.
    lower_dload_blocks_supply a bs = (bs',b) /\ MEM bb' bs' ==>
    ?bb a1 a2. MEM bb bs /\ lower_dload_block_supply a1 bb = (bb',a2)
Proof
  Induct >- simp[lower_dload_blocks_supply_def] >>
  simp[Once lower_dload_blocks_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem lower_dload_function_supply_active_origin:
  lower_dload_function_supply a fn = (fn',b) /\ active_inst fn' j t ==>
  ?bb bb' a0 a1 a2 pre i post p c tail.
    MEM bb fn.fn_blocks /\ MEM bb' fn'.fn_blocks /\
    bb.bb_label = t.vs_current_bb /\
    lower_dload_block_supply a0 bb = (bb',a2) /\
    bb.bb_instructions = pre ++ i::post /\
    lower_dload_insts_supply a0 pre = (p,a1) /\
    (?a_mid. lower_dload_inst_supply a1 i = (c,a_mid) /\
      lower_dload_insts_supply a_mid post = (tail,a2)) /\
    bb'.bb_instructions = p ++ c ++ tail /\
    LENGTH p <= t.vs_inst_idx /\
    t.vs_inst_idx < LENGTH p + LENGTH c /\
    j = EL (t.vs_inst_idx - LENGTH p) c
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs(), active_inst_def] >>
  rpt strip_tac >> gvs[] >>
  drule_all lower_dload_blocks_supply_block_origin >> strip_tac >>
  `bb.bb_label = bb'.bb_label /\
   lower_dload_insts_supply a1 bb'.bb_instructions = (bb.bb_instructions,a2)` by
    gvs[lower_dload_block_supply_def, AllCaseEqs()] >>
  drule_all lower_dload_insts_supply_position >> strip_tac >>
  qexistsl_tac [`bb'`,`bb`,`a1`,`qi`,`a2`,`pre`,`i`,`post`,`before`,`code`,`after`] >>
  simp[] >> metis_tac[]
QED

(* Sequential completion moves to the next segment, not inside the old one.
   The append-forward interface already provides singleton advancement;
   keep that fact here at its control-position use site. *)
Theorem lower_dload_configured_segment_next:
  lower_dload_insts_supply a pre = (p,a1) /\
  lower_dload_inst_supply a1 i = (code,a2) /\
  lower_dload_inst_supply a2 j = (next,a3) /\
  lower_dload_insts_supply a3 post = (tail,b) /\
  next <> [] /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block t.vs_current_bb gn.fn_blocks = SOME gb /\
  bb.bb_instructions = pre ++ i::j::post /\
  gb.bb_instructions = p ++ code ++ next ++ tail ==>
  lower_dload_insts_supply a (pre ++ [i]) = (p ++ code,a2) /\
  active_inst fn j (s with vs_inst_idx := SUC (LENGTH pre)) /\
  active_inst gn (HD next)
    (t with vs_inst_idx := LENGTH p + LENGTH code)
Proof
  strip_tac >>
  conj_tac
  >- (irule lower_dload_insts_supply_append_forward >>
      goal_assum (drule_at Any) >> simp[lower_dload_insts_supply_def]) >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `MEM gb gn.fn_blocks /\ gb.bb_label = t.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  conj_tac
  >- (simp[active_inst_def] >> qexists_tac `bb` >>
      simp[EL_APPEND2]) >>
  simp[active_inst_def] >> qexists_tac `gb` >>
  Cases_on `next` >> gvs[] >> simp[EL_APPEND2, EL_APPEND1]
QED

Theorem lower_dload_insts_supply_unchanged:
  !ins a. EVERY (\i. i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES) ins ==>
    lower_dload_insts_supply a ins = (ins,a)
Proof
  Induct >- simp[lower_dload_insts_supply_def] >>
  rpt gen_tac >> strip_tac >>
  `lower_dload_inst_supply a h = ([h],a)` by
    (irule lower_dload_inst_supply_special >> gvs[]) >>
  simp[lower_dload_insts_supply_def] >> gvs[]
QED

Theorem lower_dload_configured_segment_fetch:
  lower_dload_block_supply a bb = (gb,b) /\
  lower_dload_insts_supply a pre = (p,a1) /\
  bb.bb_instructions = pre ++ ins ++ rest /\
  EVERY (\i. i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES) ins /\
  n < LENGTH ins ==>
  get_instruction gb (LENGTH p + n) = SOME (EL n ins)
Proof
  strip_tac >>
  `lower_dload_insts_supply a1 ins = (ins,a1)` by
    metis_tac[lower_dload_insts_supply_unchanged] >>
  Cases_on `lower_dload_insts_supply a1 rest` >>
  `lower_dload_insts_supply a1 (ins ++ rest) = (ins ++ q,r)` by
    metis_tac[lower_dload_insts_supply_append_forward] >>
  `lower_dload_insts_supply a (pre ++ (ins ++ rest)) = (p ++ (ins ++ q),r)` by
    (irule lower_dload_insts_supply_append_forward >>
     goal_assum (drule_at Any) >> simp[]) >>
  gvs[lower_dload_block_supply_def, get_instruction_def, EL_APPEND2, EL_APPEND1]
QED
