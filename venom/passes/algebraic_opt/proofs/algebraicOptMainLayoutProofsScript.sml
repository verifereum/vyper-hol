Theory algebraicOptMainLayoutProofs
Ancestors
  list pred_set algebraicOptSupplyProofs algebraicOptDefs irSupply
  algebraicOptMainShapeProofs algebraicOptMainRangeProofs
  algebraicOptShapeProofs venomInst

Theorem ao_transform_insts_supply_append:
  !dfg ra lbl targets xs supply idx ys outs supply'.
  ao_transform_insts_supply dfg ra lbl targets supply idx (xs ++ ys) = (outs,supply') <=>
  ?pre mid post.
    ao_transform_insts_supply dfg ra lbl targets supply idx xs = (pre,mid) /\
    ao_transform_insts_supply dfg ra lbl targets mid (idx + LENGTH xs) ys = (post,supply') /\
    outs = pre ++ post
Proof
  ntac 4 gen_tac >> Induct >> simp[Once ao_transform_insts_supply_def] >>
  rpt gen_tac >>
  Cases_on `ao_alloc_fresh supply` >>
  rename1 `ao_alloc_fresh supply = (fr,next)` >>
  simp[Once ao_transform_insts_supply_def] >>
  simp[AllCaseEqs()] >>
  first_x_assum (qspecl_then [`next`, `SUC idx`, `ys`] mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES] >> metis_tac[APPEND_ASSOC]
QED

Theorem ao_transform_insts_supply_occurrence:
  !dfg ra lbl targets supply idx xs inst ys outs supply' V.
  ir_supply_inst_ok supply /\ V SUBSET set supply.irs_used_vars /\
  ao_transform_insts_supply dfg ra lbl targets supply idx (xs ++ inst::ys) = (outs,supply') ==>
  ?pre mid fr next post.
    ao_transform_insts_supply dfg ra lbl targets supply idx xs = (pre,mid) /\
    ao_alloc_fresh mid = (fr,next) /\
    ao_transform_insts_supply dfg ra lbl targets next (SUC (idx + LENGTH xs)) ys = (post,supply') /\
    outs = pre ++ ao_transform_inst dfg ra lbl (idx + LENGTH xs) targets fr inst ++ post /\
    ir_supply_inst_ok mid /\ V SUBSET set mid.irs_used_vars /\
    set supply.irs_used_vars SUBSET set mid.irs_used_vars /\
    set next.irs_used_vars SUBSET set supply'.irs_used_vars
Proof
  rpt gen_tac >> strip_tac >>
  gvs[ao_transform_insts_supply_append] >>
  Cases_on `ao_alloc_fresh mid` >> rename1 `ao_alloc_fresh mid = (fr,next)` >>
  Cases_on `ao_transform_insts_supply dfg ra lbl targets next (SUC (idx + LENGTH xs)) ys` >>
  rename1 `ao_transform_insts_supply dfg ra lbl targets next (SUC (idx + LENGTH xs)) ys = (post',last)` >>
  gvs[Once ao_transform_insts_supply_def] >>
  drule_all ao_transform_insts_supply_mono >> strip_tac >>
  drule_all ao_alloc_fresh_contract >> strip_tac >>
  drule_all ao_transform_insts_supply_mono >> strip_tac >>
  metis_tac[SUBSET_TRANS]
QED

Theorem ao_alloc_fresh_scalar_separation:
  !mid V fr next.
  ir_supply_inst_ok mid /\ V SUBSET set mid.irs_used_vars /\
  ao_alloc_fresh mid = (fr,next) ==>
  SND (fr "not") <> SND (fr "iz") /\
  SND (fr "not") NOTIN V /\ SND (fr "iz") NOTIN V /\
  fr "xor" = fr "not" /\
  SND (fr "not") IN (set next.irs_used_vars DIFF set mid.irs_used_vars) /\
  SND (fr "iz") IN (set next.irs_used_vars DIFF set mid.irs_used_vars)
Proof
  rpt gen_tac >> strip_tac >>
  drule ao_alloc_fresh_tags >>
  disch_then (fn th => map_every mp_tac [Q.SPEC `"not"` th, Q.SPEC `"xor"` th]) >>
  simp[] >> rpt disch_tac >>
  drule_all ao_alloc_fresh_contract >> strip_tac >>
  gvs[SUBSET_DEF] >> metis_tac[]
QED

Theorem ao_alloc_fresh_scalar_support:
  !mid V fr next p.
  ir_supply_inst_ok mid /\ V SUBSET set mid.irs_used_vars /\
  ao_alloc_fresh mid = (fr,next) /\
  (!x. MEM (Var x) p.inst_operands \/ MEM x p.inst_outputs ==> x IN V) ==>
  !y. y = SND (fr "not") \/ y = SND (fr "iz") ==>
    ~MEM (Var y) p.inst_operands /\ ~MEM y p.inst_outputs
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ao_alloc_fresh_scalar_separation >> strip_tac >>
  metis_tac[]
QED

Theorem ao_main_resolved_inst_support:
  !fn inst V p.
  MEM inst (fn_insts fn) /\
  (!i x. MEM i (fn_insts fn) /\
    (MEM (Var x) i.inst_operands \/ MEM x i.inst_outputs) ==> x IN V) /\
  p = ao_pre_flip_inst (ao_resolve_iszero_inst (ao_compute_fn_iszero_targets fn) inst) ==>
  !x. MEM (Var x) p.inst_operands \/ MEM x p.inst_outputs ==> x IN V
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\i. set (inst_ir_vars i) SUBSET V) (fn_insts fn)` by
    (simp[EVERY_MEM, inst_ir_vars_def, SUBSET_UNION] >>
     rpt strip_tac
     >- (gvs[SUBSET_DEF] >> metis_tac[]) >>
     rewrite_tac[inst_uses_def] >>
     pure_once_rewrite_tac[ao_operand_support] >>
     rpt strip_tac >> Cases_on `op` >>
     gvs[operand_vars_def, operand_var_def, SUBSET_DEF] >> metis_tac[]) >>
  `set (inst_uses inst) SUBSET V` by
    (gvs[EVERY_MEM, inst_ir_vars_def, SUBSET_DEF] >> metis_tac[]) >>
  `set (inst_uses (ao_resolve_iszero_inst (ao_compute_fn_iszero_targets fn) inst)) SUBSET V` by
    (irule ao_resolve_iszero_inst_support >> simp[ao_compute_fn_iszero_targets_def] >>
     metis_tac[ao_compute_iszero_targets_support]) >>
  rpt strip_tac
  >- (qpat_x_assum `set (inst_uses (ao_resolve_iszero_inst _ _)) SUBSET V` mp_tac >>
      rewrite_tac[inst_uses_def] >>
      pure_once_rewrite_tac[ao_operand_support] >>
      disch_then (qspec_then `Var x` mp_tac) >>
      gvs[ao_pre_flip_operand_mem, operand_vars_def, operand_var_def, SUBSET_DEF]) >>
  gvs[ao_pre_flip_inst_shape, ao_resolve_iszero_inst_fields] >> metis_tac[]
QED

Theorem ao_main_resolved_fresh_support:
  !fn inst V p mid fr next.
  MEM inst (fn_insts fn) /\
  (!i x. MEM i (fn_insts fn) /\
    (MEM (Var x) i.inst_operands \/ MEM x i.inst_outputs) ==> x IN V) /\
  p = ao_pre_flip_inst (ao_resolve_iszero_inst (ao_compute_fn_iszero_targets fn) inst) /\
  ir_supply_inst_ok mid /\ V SUBSET set mid.irs_used_vars /\
  ao_alloc_fresh mid = (fr,next) ==>
  !y. y = SND (fr "not") \/ y = SND (fr "iz") ==>
    ~MEM (Var y) p.inst_operands /\ ~MEM y p.inst_outputs
Proof
  rpt gen_tac >> strip_tac >>
  `!x. MEM (Var x) p.inst_operands \/ MEM x p.inst_outputs ==> x IN V` by
    (rpt strip_tac >> irule ao_main_resolved_inst_support >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  metis_tac[ao_alloc_fresh_scalar_support]
QED

Theorem ao_transform_insts_supply_cursor:
  ao_transform_insts_supply dfg ra lbl targets supply idx xs = (pre,mid) /\
  ao_transform_insts_supply dfg ra lbl targets supply idx (xs ++ ys) = (outs,last) ==>
  ao_transform_insts_supply dfg ra lbl targets mid (idx + LENGTH xs) ys =
    (DROP (LENGTH pre) outs,last) /\ TAKE (LENGTH pre) outs = pre
Proof
  strip_tac >>
  qpat_x_assum `ao_transform_insts_supply _ _ _ _ _ _ (_ ++ _) = _` mp_tac >>
  simp[ao_transform_insts_supply_append] >> strip_tac >>
  gvs[DROP_APPEND, rich_listTheory.TAKE_LENGTH_APPEND]
QED

Theorem ao_transform_insts_supply_cursor_step:
  ir_supply_inst_ok supply /\ V SUBSET set supply.irs_used_vars /\
  ao_transform_insts_supply dfg ra lbl targets supply idx (xs ++ inst::ys) = (outs,last) ==>
  ?pre mid fr next post.
    ao_transform_insts_supply dfg ra lbl targets supply idx xs = (pre,mid) /\
    ao_alloc_fresh mid = (fr,next) /\
    ao_transform_insts_supply dfg ra lbl targets next (SUC (idx + LENGTH xs)) ys = (post,last) /\
    DROP (LENGTH pre) outs = ao_transform_inst dfg ra lbl (idx + LENGTH xs) targets fr inst ++ post /\
    DROP (LENGTH pre + LENGTH (ao_transform_inst dfg ra lbl (idx + LENGTH xs) targets fr inst)) outs = post /\
    ir_supply_inst_ok mid /\ V SUBSET set mid.irs_used_vars /\
    set supply.irs_used_vars SUBSET set mid.irs_used_vars /\
    set next.irs_used_vars SUBSET set last.irs_used_vars
Proof
  strip_tac >> drule_all ao_transform_insts_supply_occurrence >>
  strip_tac >> goal_assum (drule_at Any) >>
  simp[DROP_APPEND, arithmeticTheory.ADD_SUB, DROP_LENGTH_TOO_LONG,
       arithmeticTheory.SUB_EQ_0] >>
  `LENGTH pre - (LENGTH pre +
     LENGTH (ao_transform_inst dfg ra lbl (idx + LENGTH xs) targets fr inst)) = 0`
    by decide_tac >> simp[]
QED

Theorem ao_transform_insts_supply_phi_prefix_length:
  !insts s idx outs s'.
    ao_transform_insts_supply dfg ra lbl targets s idx insts = (outs,s') ==>
    phi_prefix_length outs = phi_prefix_length insts
Proof
  Induct >- simp[ao_transform_insts_supply_def, venomExecSemanticsTheory.phi_prefix_length_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_alloc_fresh s` >> rename1 `ao_alloc_fresh s = (fr,next)` >>
  Cases_on `ao_transform_insts_supply dfg ra lbl targets next (SUC idx) insts` >>
  rename1 `ao_transform_insts_supply dfg ra lbl targets next (SUC idx) insts = (post,last)` >>
  gvs[Once ao_transform_insts_supply_def] >>
  Cases_on `h.inst_opcode = PHI`
  >- (`ao_transform_inst dfg ra lbl idx targets fr h =
         [ao_resolve_iszero_inst targets h]` by
        (irule ao_transform_inst_control_owner >> simp[]) >>
      gvs[venomExecSemanticsTheory.phi_prefix_length_def, ao_resolve_iszero_inst_fields] >>
      metis_tac[]) >>
  `FILTER (\i. i.inst_opcode = PHI)
      (ao_transform_inst dfg ra lbl idx targets fr h) = []` by
    simp[ao_transform_inst_phis] >>
  `ao_transform_inst dfg ra lbl idx targets fr h <> []` by
    simp[ao_transform_inst_nonempty] >>
  Cases_on `ao_transform_inst dfg ra lbl idx targets fr h` >>
  gvs[FILTER, venomExecSemanticsTheory.phi_prefix_length_def, AllCaseEqs()]
QED

Theorem ao_transform_insts_supply_take_phi_length:
  !insts s idx pre mid.
    ao_transform_insts_supply dfg ra lbl targets s idx
      (TAKE (phi_prefix_length insts) insts) = (pre,mid) ==>
    LENGTH pre = phi_prefix_length insts
Proof
  Induct >- simp[venomExecSemanticsTheory.phi_prefix_length_def,
                 ao_transform_insts_supply_def] >>
  rpt gen_tac >> Cases_on `h.inst_opcode = PHI`
  >- (simp[venomExecSemanticsTheory.phi_prefix_length_def] >> strip_tac >>
      Cases_on `ao_alloc_fresh s` >> rename1 `ao_alloc_fresh s = (fr,next)` >>
      Cases_on `ao_transform_insts_supply dfg ra lbl targets next (SUC idx)
        (TAKE (phi_prefix_length insts) insts)` >>
      rename1 `ao_transform_insts_supply dfg ra lbl targets next (SUC idx)
        (TAKE (phi_prefix_length insts) insts) = (tail,last)` >>
      `ao_transform_inst dfg ra lbl idx targets fr h =
         [ao_resolve_iszero_inst targets h]` by
        (irule ao_transform_inst_control_owner >> simp[]) >>
      gvs[Once ao_transform_insts_supply_def] >> metis_tac[]) >>
  simp[venomExecSemanticsTheory.phi_prefix_length_def, ao_transform_insts_supply_def]
QED

Theorem ao_transform_blocks_supply_lookup_none:
  !bbs supply bbs' last lbl.
    ao_transform_blocks_supply dfg ra targets supply bbs = (bbs',last) /\
    lookup_block lbl bbs = NONE ==>
    lookup_block lbl bbs' = NONE
Proof
  Induct >- simp[ao_transform_blocks_supply_def] >>
  rpt gen_tac >>
  Cases_on `ao_transform_insts_supply dfg ra h.bb_label targets supply 0 h.bb_instructions` >>
  Cases_on `ao_transform_blocks_supply dfg ra targets r bbs` >>
  simp[ao_transform_blocks_supply_def, ao_transform_block_supply_def,
       lookup_block_def, FIND_thm] >>
  rpt strip_tac >> gvs[FIND_thm] >> metis_tac[lookup_block_def]
QED

Theorem ao_transform_blocks_supply_lookup_some:
  !bbs supply bbs' last lbl bb V.
    ao_transform_blocks_supply dfg ra targets supply bbs = (bbs',last) /\
    ir_supply_inst_ok supply /\ V SUBSET set supply.irs_used_vars /\
    lookup_block lbl bbs = SOME bb ==>
    ?enter outs finish.
      lookup_block lbl bbs' = SOME (bb with bb_instructions := outs) /\
      ao_transform_insts_supply dfg ra bb.bb_label targets enter 0
        bb.bb_instructions = (outs,finish) /\
      ir_supply_inst_ok enter /\ V SUBSET set enter.irs_used_vars
Proof
  Induct >- simp[lookup_block_def, FIND_thm] >>
  rpt gen_tac >>
  Cases_on `ao_transform_insts_supply dfg ra h.bb_label targets supply 0 h.bb_instructions` >>
  rename1 `ao_transform_insts_supply dfg ra h.bb_label targets supply 0 h.bb_instructions = (outs,next)` >>
  Cases_on `ao_transform_blocks_supply dfg ra targets next bbs` >>
  gvs[ao_transform_blocks_supply_def, ao_transform_block_supply_def] >>
  strip_tac >> gvs[] >>
  Cases_on `h.bb_label = lbl`
  >- (gvs[lookup_block_def, FIND_thm] >> metis_tac[]) >>
  gvs[lookup_block_def, FIND_thm] >>
  `ir_supply_inst_ok next /\ set supply.irs_used_vars SUBSET set next.irs_used_vars` by
    metis_tac[ao_transform_insts_supply_mono] >>
  first_x_assum irule >> metis_tac[SUBSET_TRANS]
QED
