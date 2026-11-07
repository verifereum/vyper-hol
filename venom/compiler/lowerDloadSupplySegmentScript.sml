(*
 * Forward composition and position lookup for LowerDload's instruction
 * supply: how the expansion of a split instruction list is assembled from
 * the expansions of its parts, and which source instruction produced a
 * given output position.
 *)
Theory lowerDloadSupplySegment
Ancestors
  o1ContractLowerDload lowerDloadDefs list rich_list

Theorem lower_dload_insts_supply_append_forward:
  !pre q before qi post after qe.
    lower_dload_insts_supply q pre = (before,qi) /\
    lower_dload_insts_supply qi post = (after,qe) ==>
    lower_dload_insts_supply q (pre ++ post) = (before ++ after,qe)
Proof
  Induct >> simp[lower_dload_insts_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> first_x_assum drule_all >> simp[APPEND_ASSOC]
QED

Theorem lower_dload_insts_supply_segment_reconstruct:
  lower_dload_insts_supply q pre = (before,qi) /\
  lower_dload_inst_supply qi i = (code,qn) /\
  lower_dload_insts_supply qn post = (after,qe) ==>
  lower_dload_insts_supply q (pre ++ i::post) = (before ++ code ++ after,qe)
Proof
  strip_tac >>
  `lower_dload_insts_supply qi (i::post) = (code ++ after,qe)` by
    simp[lower_dload_insts_supply_def] >>
  drule_all lower_dload_insts_supply_append_forward >> simp[APPEND_ASSOC]
QED

Theorem lower_dload_insts_supply_position:
  !ins q xs qe k.
    lower_dload_insts_supply q ins = (xs,qe) /\ k < LENGTH xs ==>
    ?pre i post before qi code qn after j.
      ins = pre ++ i::post /\
      lower_dload_insts_supply q pre = (before,qi) /\
      lower_dload_inst_supply qi i = (code,qn) /\
      lower_dload_insts_supply qn post = (after,qe) /\
      xs = before ++ code ++ after /\
      j < LENGTH code /\ k = LENGTH before + j /\ EL k xs = EL j code
Proof
  Induct >> simp[lower_dload_insts_supply_def] >>
  rpt gen_tac >>
  Cases_on `lower_dload_inst_supply q h` >>
  Cases_on `lower_dload_insts_supply r ins` >>
  simp[] >> strip_tac >> gvs[] >>
  Cases_on `k < LENGTH q'`
  >- (qexistsl_tac [`[]`,`h`,`ins`,`[]`,`q`,`q'`,`r`,`q''`,`k`] >>
      simp[lower_dload_insts_supply_def, EL_APPEND1]) >>
  first_x_assum (qspecl_then [`r`,`q''`,`qe`,`k - LENGTH q'`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`h::pre`,`i`,`post`,`q' ++ before`,`qi`,`code`,`qn`,`after`,`j`] >>
  simp[lower_dload_insts_supply_def, APPEND_ASSOC] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  `before ++ (code ++ after) = q''` by simp[APPEND_ASSOC] >>
  asm_rewrite_tac[] >>
  simp[EL_APPEND2] >>
  qpat_x_assum `EL (k - LENGTH q') q'' = _` mp_tac >> simp[]
QED

