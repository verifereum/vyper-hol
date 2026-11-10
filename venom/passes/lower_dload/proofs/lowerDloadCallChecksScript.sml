(*
 * LowerDload keeps every CALL/STATICCALL success check (call_checks_ok,
 * a conjunct of fn_shape_ok).
 *
 * TOP-LEVEL:
 *   lower_dload_function_supply_call_checks
 *)
Theory lowerDloadCallChecks
Ancestors
  lowerDloadDefs lowerDloadSupplyProofs unitShapeDefs venomEffects
  venomInst list rich_list

Theorem ld_checks_blocks_length[local]:
  !s cs t. lower_dload_blocks_supply s bs = (cs,t) ==>
  LENGTH cs = LENGTH bs
Proof
  Induct_on `bs` >>
  simp[lower_dload_blocks_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> first_x_assum drule >> simp[]
QED

Theorem ld_checks_blocks_member[local]:
  !s cs t. lower_dload_blocks_supply s bs = (cs,t) ==>
  ((!b. MEM b bs ==> ?c u v. MEM c cs /\
      lower_dload_block_supply u b = (c,v)) /\
   (!c. MEM c cs ==> ?b u v. MEM b bs /\
      lower_dload_block_supply u b = (c,v)))
Proof
  Induct_on `bs` >>
  simp[lower_dload_blocks_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ld_checks_block_label[local]:
  lower_dload_block_supply s b = (c,t) ==>
  c.bb_label = b.bb_label
Proof
  simp[lower_dload_block_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem ld_checks_inst_revert[local]:
  lower_dload_inst_supply s i = (xs,t) /\
  i.inst_opcode <> INVOKE ==>
  xs <> [] /\ EVERY (\j. j.inst_opcode <> INVOKE) xs /\
  (MEM i.inst_opcode [JMP; REVERT] ==> xs = [i])
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[]) >>
  simp[lower_dload_inst_supply_def] >> rpt strip_tac >> gvs[]
QED

Theorem ld_checks_insts_revert[local]:
  !s xs t. lower_dload_insts_supply s ins = (xs,t) /\
  ins <> [] /\ EVERY (\i. i.inst_opcode <> INVOKE) ins /\
  MEM (LAST ins).inst_opcode [JMP; REVERT] ==>
  xs <> [] /\ EVERY (\i. i.inst_opcode <> INVOKE) xs /\
  LAST xs = LAST ins
Proof
  Induct_on `ins` >- simp[] >>
  rpt gen_tac >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >>
  strip_tac >>
  drule_all ld_checks_inst_revert >> strip_tac >>
  Cases_on `ins` >> gvs[cj 1 lower_dload_insts_supply_def] >>
  qpat_x_assum `!a z w. lower_dload_insts_supply a _ = (z,w) ==> _`
    (qspecl_then [`s1`, `outs`, `t`] mp_tac) >>
  simp[] >> strip_tac >> Cases_on `outs` >> gvs[LAST_APPEND]
QED

Theorem ld_checks_block_revert[local]:
  lower_dload_block_supply s b = (c,t) /\
  b.bb_instructions <> [] /\
  EVERY (\i. i.inst_opcode <> INVOKE) b.bb_instructions /\
  MEM (LAST b.bb_instructions).inst_opcode [JMP; REVERT] ==>
  c.bb_instructions <> [] /\
  EVERY (\i. i.inst_opcode <> INVOKE) c.bb_instructions /\
  LAST c.bb_instructions = LAST b.bb_instructions
Proof
  simp[lower_dload_block_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[ld_checks_insts_revert, MEM]
QED

Theorem ld_checks_revert_path[local]:
  !l. lower_dload_blocks_supply s bs = (cs,t) /\
  revert_path bs n l ==> revert_path cs n l
Proof
  Induct_on `n` >- simp[revert_path_def] >>
  simp[revert_path_def, EXISTS_MEM] >> rpt strip_tac >>
  drule ld_checks_blocks_member >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `MEM (LAST bb.bb_instructions).inst_opcode [JMP; REVERT]` by
    (simp[] >> metis_tac[]) >>
  drule_all ld_checks_block_revert >> strip_tac >>
  drule ld_checks_block_label >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  rpt CASE_TAC >> gvs[] >> metis_tac[]
QED

Theorem ld_checks_flag_fails[local]:
  lower_dload_blocks_supply s bs = (cs,t) /\ flag_fails bs vs i ==>
  flag_fails cs vs i
Proof
  strip_tac >>
  `LENGTH cs = LENGTH bs` by (drule ld_checks_blocks_length >> simp[]) >>
  qpat_x_assum `flag_fails _ _ _` mp_tac >>
  Cases_on `i.inst_opcode` >> simp[flag_fails_def] >>
  rpt (CASE_TAC >> gvs[]) >>
  metis_tac[ld_checks_revert_path]
QED

Theorem ld_checks_flag_step[local]:
  lower_dload_inst_supply s i = (out,t) /\
  (!vs j. flag_fails bs vs j ==> flag_fails cs vs j) /\
  (!vs. flag_path bs vs rest ==> flag_path cs vs tail) /\
  flag_path bs flags (i::rest) ==>
  flag_path cs flags (out ++ tail)
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      qpat_x_assum `!vs j. _` kall_tac >>
      qpat_x_assum `flag_path bs flags _` mp_tac >>
      pure_once_rewrite_tac[flag_path_def] >>
      qpat_assum `i.inst_opcode = _` (fn th => pure_rewrite_tac[th]) >>
      pure_rewrite_tac[write_effects_def, empty_effects_def] >>
      simp_tac (srw_ss()) [] >>
      pure_rewrite_tac[flag_fails_def] >>
      qpat_assum `i.inst_opcode = _` (fn th => pure_rewrite_tac[th]) >>
      simp_tac (srw_ss()) [] >>
      ntac 3 (pure_once_rewrite_tac[flag_path_def] >>
        simp_tac (srw_ss()) [flag_fails_def, write_effects_def, empty_effects_def]) >>
      metis_tac[]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      qpat_x_assum `!vs j. _` kall_tac >>
      qpat_x_assum `flag_path bs flags _` mp_tac >>
      pure_once_rewrite_tac[flag_path_def] >>
      qpat_assum `i.inst_opcode = _` (fn th => pure_rewrite_tac[th]) >>
      pure_rewrite_tac[write_effects_def, empty_effects_def] >>
      simp_tac (srw_ss()) [] >>
      pure_rewrite_tac[flag_fails_def] >>
      qpat_assum `i.inst_opcode = _` (fn th => pure_rewrite_tac[th]) >>
      simp_tac (srw_ss()) [] >>
      ntac 3 (pure_once_rewrite_tac[flag_path_def] >>
        simp_tac (srw_ss()) [flag_fails_def, write_effects_def, empty_effects_def]) >>
      metis_tac[]) >>
  simp[lower_dload_inst_supply_def] >> rpt strip_tac >> gvs[] >>
  gvs[Once flag_path_def] >> simp[Once flag_path_def] >> metis_tac[]
QED

Theorem ld_checks_call_step[local]:
  lower_dload_inst_supply s i = (out,t) /\
  (!vs. flag_path bs vs rest ==> flag_path cs vs tail) /\
  calls_flagged bs (i::rest) /\ calls_flagged cs tail ==>
  calls_flagged cs (out ++ tail)
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[calls_flagged_def]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[calls_flagged_def]) >>
  simp[lower_dload_inst_supply_def] >> rpt strip_tac >> gvs[] >>
  gvs[calls_flagged_def] >> rpt CASE_TAC >> gvs[] >> metis_tac[]
QED

Theorem ld_checks_flag_insts[local]:
  !s outs t flags.
  lower_dload_insts_supply s ins = (outs,t) /\
  (!vs j. flag_fails bs vs j ==> flag_fails cs vs j) /\
  flag_path bs flags ins ==> flag_path cs flags outs
Proof
  Induct_on `ins` >- simp[flag_path_def] >>
  rpt gen_tac >> simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> irule ld_checks_flag_step >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem ld_checks_call_insts[local]:
  !s outs t.
  lower_dload_insts_supply s ins = (outs,t) /\
  (!vs j. flag_fails bs vs j ==> flag_fails cs vs j) /\
  calls_flagged bs ins ==> calls_flagged cs outs
Proof
  Induct_on `ins`
  >- simp[lower_dload_insts_supply_def, calls_flagged_def] >>
  rpt gen_tac >> simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> irule ld_checks_call_step >>
  conj_tac
  >- (goal_assum (drule_at Any) >> simp[] >>
      metis_tac[ld_checks_flag_insts]) >>
  first_x_assum irule >> conj_tac
  >- (goal_assum (drule_at Any)) >>
  gvs[calls_flagged_def]
QED

Theorem ld_checks_blocks[local]:
  lower_dload_blocks_supply s bs = (cs,t) /\
  EVERY (\b. calls_flagged bs b.bb_instructions) bs ==>
  EVERY (\c. calls_flagged cs c.bb_instructions) cs
Proof
  strip_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
  drule ld_checks_blocks_member >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[EVERY_MEM, lower_dload_block_supply_def, AllCaseEqs()] >>
  irule ld_checks_call_insts >> goal_assum (drule_at Any) >>
  metis_tac[ld_checks_flag_fails]
QED

(* Why it holds: the expansion of a DLOAD (ALLOCA, ADD, CODECOPY, MLOAD)
   or a DLOADBYTES (ADD, CODECOPY) has no INVOKE and no failing
   instruction, and its CODECOPY writes memory, so flag_path empties its
   flag set there just as it does at the source DLOAD/DLOADBYTES (both
   have write_effects {Eff_MEMORY}).  Before the CODECOPY the set only
   loses the new outputs.  Other instructions are kept as they are, block
   labels and terminators are kept, so revert_path carries over. *)
Theorem lower_dload_function_supply_call_checks:
  lower_dload_function_supply s f = (g,t) /\ call_checks_ok f ==>
  call_checks_ok g
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs(), call_checks_ok_def] >>
  strip_tac >> gvs[] >> irule ld_checks_blocks >>
  metis_tac[]
QED
