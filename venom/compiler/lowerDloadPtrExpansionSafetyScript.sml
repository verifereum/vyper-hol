Theory lowerDloadPtrExpansionSafety
Ancestors
  lowerDloadPtrPhase lowerDloadPtrExpansionTransport lowerDloadPtrTaint
  lowerDloadPtrExpansion
  ptrDiscipline lowerDloadDefs venomExecSemantics venomState venomInst
  memLocDefs codegenRel contextCodegenRel instIdxIndep list words finite_map pred_set arithmetic

Theorem dload_alloca_operand_taint[local]:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\ a.inst_outputs = [av] /\
  off <> Var av ==>
  op_taint (step_taint a t u un) off = op_taint un off /\
  op_taint (step_taint a t u un) (Var av) = {}
Proof
  strip_tac >> Cases_on `off` >>
  simp[op_taint_def, step_taint_def, out_taint_def, eval_operand_def, set_var_taint_def,
       FLOOKUP_UPDATE, DOMSUB_FLOOKUP_THM] >> gvs[]
QED

Theorem dload_add_safety:
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  op_taint un off = {} ==>
  access_ok lo H g b t /\ taint_ok g un b t
Proof
  strip_tac >>
  simp[access_ok_def, taint_ok_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, mem_write_ops_def, mem_read_ops_def] >>
  gen_tac >> Cases_on `op = off` >> simp[] >>
  Cases_on `op = Label "code_end"` >> simp[op_taint_def]
QED

Theorem dload_literal_alloca_safety:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] ==>
  access_ok lo H g a t /\ taint_ok g un a t
Proof
  strip_tac >> simp[access_ok_def, taint_ok_def,
    source_memory_write_ranges_def, source_memory_read_ranges_def,
    mem_write_ops_def, mem_read_ops_def, op_taint_def]
QED

Theorem dload_alloca_add_prefix_safety:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\ a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  off <> Var av /\ op_taint un0 off = {} /\
  dload_prefix_match fuel Ct PH (a::b::rest) 1 t0 H0 un0 t H un ==>
  access_ok lo H g b t /\ taint_ok g un b t
Proof
  strip_tac >> drule (iffLR dload_prefix_first) >> strip_tac >>
  drule_all dload_alloca_operand_taint >>
  disch_then (qspecl_then [`un0`,`v`,`t0`] strip_assume_tac) >>
  gvs[] >> irule dload_add_safety >> simp[]
QED

Theorem dload_alloca_safety_metadata[local]:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\ a.inst_outputs = [av] /\
  (FLOOKUP t0.vs_allocas a.inst_id = NONE ==>
    t0.vs_alloca_next + 32 < dimword (:256)) /\
  (!bb n. FLOOKUP t0.vs_allocas a.inst_id = SOME (bb,n) ==>
    n = 32 /\ bb+32 < dimword (:256)) /\
  step_inst fuel Ct a t0 = OK u ==>
  ?bb. bb+32 < dimword (:256) /\ lookup_var av u = SOME (n2w bb) /\
    FLOOKUP (step_prov PH H0 a u) av = SOME (bb,32)
Proof
  strip_tac >>
  qpat_x_assum `!bb n. _` (mk_asm "cached") >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[IgnAsm `!bb n. _`, step_inst_non_invoke, step_inst_base_def, eval_operand_def] >> strip_tac >>
  gvs[IgnAsm `!bb n. _`, exec_alloca_def, AllCaseEqs(), update_var_def, lookup_var_def,
      step_prov_def, out_prov_def, set_prov_def, FLOOKUP_UPDATE, dimword_def] >>
  asm_x "cached" drule >> simp[dimword_def]
QED

Theorem dload_two_prefix_metadata[local]:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\ a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\ b.inst_outputs = [cv] /\
  av <> cv /\ off <> Var av /\ (FLOOKUP t0.vs_allocas a.inst_id = NONE ==>
    t0.vs_alloca_next + 32 < dimword (:256)) /\
  (!bb n. FLOOKUP t0.vs_allocas a.inst_id = SOME (bb,n) ==>
     n = 32 /\ bb + 32 < dimword (:256)) /\
  dload_prefix_match fuel Ct PH [a;b;c;d] 2 t0 H0 un0 t H un ==>
  ?bb. bb + 32 < dimword (:256) /\ eval_operand (Var av) t = SOME (n2w bb) /\
    FLOOKUP H av = SOME (bb,32) /\
    op_taint un (Var av) = {} /\ op_taint un (Var cv) = {}
Proof
  strip_tac >>
  qpat_x_assum `!bb n. _` (mk_asm "cached") >>
  `2 = SUC 1` by decide_tac >>
  qpat_x_assum `2 = _` (fn th => RULE_ASSUM_TAC (ONCE_REWRITE_RULE [th])) >>
  drule dload_prefix_successor >> strip_tac >>
  drule (iffLR dload_prefix_first) >> strip_tac >>
  asm "cached" assume_tac >> drule_all dload_alloca_safety_metadata >>
  disch_then (qspecl_then [`PH`,`H0`] strip_assume_tac) >>
  qpat_x_assum `!bb n. _` kall_tac >>
  drule_all dload_alloca_operand_taint >>
  disch_then (qspecl_then [`un0`,`v'`,`t0`] strip_assume_tac) >>
  qpat_x_assum `dload_prefix_match _ _ _ _ (SUC _) _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `dload_prefix_match _ _ _ _ 1 _ _ _ _ _ _` kall_tac >>
  gvs[] >>
  qpat_x_assum `step_inst _ _ b _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_pure2_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> qexists_tac `bb` >>
  qmatch_goalsub_abbrev_tac `FLOOKUP HH av` >>
  qmatch_goalsub_abbrev_tac `eval_operand (Var av) tt` >>
  qmatch_goalsub_abbrev_tac `op_taint uu (Var av)` >>
  `FLOOKUP HH av = SOME (bb,32)` by
    (simp[Abbr `HH`, step_prov_def, set_prov_def, out_prov_def] >>
     Cases_on `first_prov (step_prov PH H0 a v') [off;Label "code_end"]` >>
     gvs[step_prov_def, set_prov_def, out_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
  `eval_operand (Var av) tt = SOME (n2w bb)` by
    gvs[Abbr `tt`, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[Abbr `uu`, step_taint_def, out_taint_def, set_var_taint_def,
       op_taint_def, eval_operand_def, FLOOKUP_UPDATE]
QED

Theorem dload_four_prefix_safety:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\ a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\ b.inst_outputs = [cv] /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var cv;Lit 32w] /\ c.inst_outputs = [] /\
  d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\ d.inst_outputs = [out] /\
  av <> cv /\ off <> Var av /\ eval_operand off t0 = SOME x /\
  op_taint un0 off = {} /\ (FLOOKUP t0.vs_allocas a.inst_id = NONE ==>
    t0.vs_alloca_next + 32 < dimword (:256)) /\
  (!bb n. FLOOKUP t0.vs_allocas a.inst_id = SOME (bb,n) ==>
     n = 32 /\ bb + 32 < dimword (:256)) /\
  dload_prefix_match fuel Ct PH [a;b;c;d] k t0 H0 un0 t H un /\ k < 4 ==>
  access_ok lo H g (EL k [a;b;c;d]) t /\ taint_ok g un (EL k [a;b;c;d]) t
Proof
  strip_tac >> `k = 0 \/ k = 1 \/ k = 2 \/ k = 3` by decide_tac >>
  qpat_x_assum `k = _` SUBST_ALL_TAC
  >- suspend "alloca"
  >- suspend "add"
  >- suspend "copy"
  >> suspend "load"
QED

Resume dload_four_prefix_safety[alloca]:
  simp[] >> irule dload_literal_alloca_safety >> simp[]
QED

Resume dload_four_prefix_safety[add]:
  pure_rewrite_tac [arithmeticTheory.ONE, EL, HD, TL] >>
  irule dload_alloca_add_prefix_safety >> metis_tac[]
QED
Resume dload_four_prefix_safety[copy]:
  qpat_x_assum `!bb n. _` (mk_asm "cached") >>
  asm "cached" assume_tac >> drule_all dload_two_prefix_metadata >>
  strip_tac >> qpat_x_assum `!bb n. _` kall_tac >>
  qpat_x_assum `dload_prefix_match _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  simp[] >>
  simp[access_ok_def, taint_ok_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, mem_write_ops_def, mem_read_ops_def,
       sized_source_write_range_def, eval_operand_def] >>
  conj_tac
  >- (Cases_on `lookup_var cv t` >> simp[]) >>
  gen_tac >> Cases_on `op = Var av` >> simp[] >>
  Cases_on `op = Var cv` >> simp[] >>
  Cases_on `op = Lit 32w` >> simp[op_taint_def]
QED
Resume dload_four_prefix_safety[load]:
  qpat_x_assum `!bb n. _` (mk_asm "cached") >>
  `3 = SUC 2` by decide_tac >>
  qpat_x_assum `3 = _` (fn th => RULE_ASSUM_TAC (ONCE_REWRITE_RULE [th])) >>
  drule dload_prefix_successor >> strip_tac >>
  qpat_x_assum `dload_prefix_match _ _ _ _ (SUC _) _ _ _ _ _ _` kall_tac >>
  asm "cached" assume_tac >> drule_all dload_two_prefix_metadata >>
  strip_tac >> qpat_x_assum `!bb n. _` kall_tac >>
  qpat_x_assum `dload_prefix_match _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  gvs[] >>
  qpat_x_assum `step_inst _ _ c _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `access_ok lo HH g d tt` >>
  qmatch_goalsub_abbrev_tac `taint_ok g uu d tt` >>
  `FLOOKUP HH av = SOME (bb,32)` by
    simp[Abbr `HH`, step_prov_def, set_prov_def, FLOOKUP_DRESTRICT] >>
  `eval_operand (Var av) tt = SOME (n2w bb)` by
    gvs[Abbr `tt`, eval_operand_def, lookup_var_def, write_memory_with_expansion_def,
        write_memory_def] >>
  `op_taint uu (Var av) = {}` by
    gvs[Abbr `uu`, step_taint_def, set_var_taint_def, op_taint_def, FLOOKUP_DRESTRICT] >>
  simp[access_ok_def, taint_ok_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, mem_write_ops_def, mem_read_ops_def,
       eval_operand_def]
QED
Finalise dload_four_prefix_safety

Theorem dload_supply_prefix_safety:
  i.inst_opcode = DLOAD /\ i.inst_operands = [off] /\ i.inst_outputs = [out] /\
  lower_dload_inst_supply supply i = (xs,next) /\
  (EL 0 xs).inst_outputs = [av] /\ (EL 1 xs).inst_outputs = [cv] /\
  av <> cv /\ off <> Var av /\ eval_operand off t0 = SOME x /\
  op_taint un0 off = {} /\ (FLOOKUP t0.vs_allocas (EL 0 xs).inst_id = NONE ==>
    t0.vs_alloca_next + 32 < dimword (:256)) /\
  (!bb n. FLOOKUP t0.vs_allocas (EL 0 xs).inst_id = SOME (bb,n) ==>
    n = 32 /\ bb + 32 < dimword (:256)) /\
  dload_prefix_match fuel Ct PH xs k t0 H0 un0 t H un /\ k < 4 ==>
  access_ok lo H g (EL k xs) t /\ taint_ok g un (EL k xs) t
Proof
  strip_tac >> drule_all dload_supply_expansion >> strip_tac >>
  qpat_x_assum `!bb n. _` (mk_asm "cached") >> gvs[] >>
  irule dload_four_prefix_safety >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  rpt gen_tac >> asm "cached" (qspecl_then [`bb`,`n`] mp_tac) >> simp[]
QED

Theorem dloadbytes_two_prefix_safety:
  a.inst_opcode = ADD /\ a.inst_operands = [off;Label "code_end"] /\ a.inst_outputs = [cv] /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var dst;Var cv;sz] /\ c.inst_outputs = [] /\
  dst <> cv /\ sz <> Var cv /\ FLOOKUP H0 dst = SOME (bb,n) /\
  eval_operand (Var dst) t0 = SOME p /\ eval_operand sz t0 = SOME z /\
  bb <= w2n p /\ w2n p + w2n z <= bb+n /\
  op_taint un0 (Var dst) = {} /\ op_taint un0 off = {} /\ op_taint un0 sz = {} /\
  dload_prefix_match fuel Ct PH [a;c] k t0 H0 un0 t H un /\ k < 2 ==>
  access_ok lo H g (EL k [a;c]) t /\ taint_ok g un (EL k [a;c]) t
Proof
  strip_tac >> `k = 0 \/ k = 1` by decide_tac >>
  qpat_x_assum `k = _` SUBST_ALL_TAC
  >- (gvs[dload_prefix_zero] >> irule dload_add_safety >> simp[]) >>
  drule (iffLR dload_prefix_first) >> strip_tac >>
  qpat_x_assum `dload_prefix_match _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  gvs[] >> qpat_x_assum `step_inst _ _ a _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_pure2_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `access_ok lo HH g c tt` >>
  qmatch_goalsub_abbrev_tac `taint_ok g uu c tt` >>
  `FLOOKUP HH dst = SOME (bb,n)` by
    (simp[Abbr `HH`, step_prov_def, set_prov_def, out_prov_def] >>
     Cases_on `first_prov H0 [off;Label "code_end"]` >>
     simp[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
  `eval_operand (Var dst) tt = SOME p /\ eval_operand sz tt = SOME z` by
    (Cases_on `sz` >>
     gvs[Abbr `tt`, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `?v. eval_operand (Var cv) tt = SOME v` by
    simp[Abbr `tt`, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `op_taint uu (Var dst) = {} /\ op_taint uu (Var cv) = {} /\ op_taint uu sz = {}` by
    (Cases_on `sz` >>
     gvs[Abbr `uu`, step_taint_def, set_var_taint_def, out_taint_def,
         op_taint_def, FLOOKUP_UPDATE, AllCaseEqs()]) >>
  irule dload_codecopy_safe >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem dloadbytes_supply_prefix_safety:
  i.inst_opcode = DLOADBYTES /\ i.inst_operands = [Var dst;off;sz] /\ i.inst_outputs = [] /\
  lower_dload_inst_supply supply i = (xs,next) /\ (EL 0 xs).inst_outputs = [cv] /\
  dst <> cv /\ sz <> Var cv /\ FLOOKUP H0 dst = SOME (bb,n) /\
  eval_operand (Var dst) t0 = SOME p /\ eval_operand sz t0 = SOME z /\
  bb <= w2n p /\ w2n p + w2n z <= bb+n /\
  op_taint un0 (Var dst) = {} /\ op_taint un0 off = {} /\ op_taint un0 sz = {} /\
  dload_prefix_match fuel Ct PH xs k t0 H0 un0 t H un /\ k < 2 ==>
  access_ok lo H g (EL k xs) t /\ taint_ok g un (EL k xs) t
Proof
  strip_tac >>
  qpat_x_assum `lower_dload_inst_supply _ _ = _` mp_tac >>
  simp[lower_dload_inst_supply_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  irule dloadbytes_two_prefix_safety >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem dload_supply_early_safety:
  i.inst_opcode = DLOAD /\ i.inst_operands = [off] /\ i.inst_outputs = [out] /\
  lower_dload_inst_supply supply i = (xs,next) /\
  (EL 0 xs).inst_outputs = [av] /\ off <> Var av /\
  op_taint un0 off = {} /\
  dload_prefix_match fuel Ct PH xs k t0 H0 un0 t H un /\ k < 2 ==>
  access_ok lo H g (EL k xs) t /\ taint_ok g un (EL k xs) t
Proof
  strip_tac >> drule_all dload_supply_expansion >> strip_tac >> gvs[] >>
  `k = 0 \/ k = 1` by decide_tac >> gvs[]
  >- (irule dload_literal_alloca_safety >> simp[]) >>
  irule dload_alloca_add_prefix_safety >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem dloadbytes_supply_zero_safety:
  i.inst_opcode = DLOADBYTES /\ i.inst_operands = [dst;off;sz] /\
  lower_dload_inst_supply supply i = (xs,next) /\
  op_taint un0 off = {} /\
  dload_prefix_match fuel Ct PH xs 0 t0 H0 un0 t H un ==>
  access_ok lo H g (EL 0 xs) t /\ taint_ok g un (EL 0 xs) t
Proof
  strip_tac >> gvs[lower_dload_inst_supply_def, AllCaseEqs(), dload_prefix_zero] >>
  irule dload_add_safety >> simp[]
QED

Theorem dload_supply_zero_safety:
  i.inst_opcode = DLOAD /\ i.inst_operands = [off] /\ i.inst_outputs = [out] /\
  lower_dload_inst_supply supply i = (xs,next) ==>
  access_ok lo H g (EL 0 xs) t /\ taint_ok g un (EL 0 xs) t
Proof
  strip_tac >> drule_all dload_supply_phase_shape >> strip_tac >>
  irule dload_literal_alloca_safety >> simp[]
QED
