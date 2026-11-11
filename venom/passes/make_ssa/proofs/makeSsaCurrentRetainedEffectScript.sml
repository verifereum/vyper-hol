Theory makeSsaCurrentRetainedEffect
Ancestors
  makeSsaCurrentPrefixEffect makeSsaCurrentCleanupBoundary
  makeSsaCurrentDefs o1FrameLockstep venomExecSemantics venomInst list

Theorem current_retained_phi_effect:
  !pre inst rest x p.
  EVERY (\j. j.inst_opcode = PHI /\ ~MEM x j.inst_outputs) pre /\
  inst.inst_opcode = PHI /\ inst.inst_outputs = [x] ==>
  phi_eff (SOME p) x (pre ++ inst::rest) = resolve_phi p inst.inst_operands
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- simp[phi_eff_def, phi_read_def] >>
  gvs[] >> simp[phi_eff_def, phi_read_def] >>
  first_x_assum drule >> simp[phi_eff_def]
QED

Theorem current_retained_reassign_read:
  !ids insts prev x.
  phi_read prev x (reassign_current_inst_ids ids insts) = phi_read prev x insts
Proof
  Induct >> Cases_on `insts` >> simp[reassign_current_inst_ids_def, phi_read_def]
QED

Theorem current_retained_parts_read:
  !pre inst rest phis ordinary x p suffix.
  EVERY (\j. j.inst_opcode = PHI /\
    ~MEM x (simplify_current_phi j).inst_outputs) pre /\
  inst.inst_opcode = PHI /\ inst.inst_outputs = [x] /\
  simplify_current_phi inst = inst /\
  simplify_current_phi_prefix_parts (pre ++ inst::rest) = (phis,ordinary) ==>
  phi_read (SOME p) x (phis ++ suffix) = SOME (resolve_phi p inst.inst_operands)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (gvs[simplify_current_phi_prefix_parts_def] >>
      Cases_on `simplify_current_phi_prefix_parts rest` >>
      gvs[] >> simp[phi_read_def]) >>
  gvs[] >>
  Cases_on `simplify_current_phi_prefix_parts (pre ++ inst::rest)` >>
  gvs[simplify_current_phi_prefix_parts_def] >>
  Cases_on `(simplify_current_phi h).inst_opcode = PHI` >>
  gvs[phi_read_def] >> first_x_assum drule_all >> simp[]
QED

Theorem current_retained_cleanup_effect:
  bb.bb_instructions = pre ++ inst::rest /\
  EVERY (\j. j.inst_opcode = PHI /\
    ~MEM x (simplify_current_phi j).inst_outputs) pre /\
  inst.inst_opcode = PHI /\ inst.inst_outputs = [x] /\
  simplify_current_phi inst = inst ==>
  phi_eff (SOME p) x (simplify_current_phi_block bb).bb_instructions =
    resolve_phi p inst.inst_operands
Proof
  strip_tac >>
  `(simplify_current_phi_block bb).bb_instructions =
    simplify_current_phi_prefix (pre ++ inst::rest)` by
    (Cases_on `pre` >> gvs[simplify_current_phi_block_def]) >>
  simp[simplify_current_phi_prefix_def] >>
  Cases_on `simplify_current_phi_prefix_parts (pre ++ inst::rest)` >> simp[] >>
  simp[phi_eff_def, current_retained_reassign_read] >>
  `phi_read (SOME p) x (q ++ r) = SOME (resolve_phi p inst.inst_operands)` by
    (irule current_retained_parts_read >> metis_tac[]) >> simp[]
QED

Theorem current_retained_cleanup_outputs:
  !inst x. MEM x (simplify_current_phi inst).inst_outputs ==> MEM x inst.inst_outputs
Proof
  `!inst x. MEM x (simplify_current_phi_raw inst).inst_outputs ==>
    MEM x inst.inst_outputs` by
    (rpt gen_tac >> simp[simplify_current_phi_raw_def] >>
     Cases_on `inst.inst_opcode = PHI` >> simp[] >>
     Cases_on `current_phi_output inst.inst_outputs` >> simp[] >>
     Cases_on `current_phi_values (remove_current_phi_self x' inst.inst_operands)` >>
     simp[] >> Cases_on `x''` >> simp[] >>
     Cases_on `EVERY (\w. w = h) t` >> simp[]) >>
  rpt gen_tac >> simp[simplify_current_phi_def, keep_current_phi_vars_def] >>
  IF_CASES_TAC >> simp[]
QED

Theorem current_retained_index_effect:
  q < LENGTH xs /\ (EL q xs).inst_opcode = PHI /\
  (EL q xs).inst_outputs = [x] /\
  (!i. i < q ==> (EL i xs).inst_opcode = PHI /\ ~MEM x (EL i xs).inst_outputs) ==>
  phi_eff (SOME p) x xs = resolve_phi p (EL q xs).inst_operands
Proof
  strip_tac >>
  `xs = TAKE q xs ++ EL q xs::DROP (SUC q) xs` by
    simp[GSYM listTheory.APPEND_ASSOC, rich_listTheory.TAKE_DROP_SUC] >>
  qspecl_then [`TAKE q xs`, `EL q xs`, `DROP (SUC q) xs`] mp_tac
    current_retained_phi_effect >>
  simp[listTheory.EVERY_EL, listTheory.EL_TAKE] >> metis_tac[]
QED

Theorem current_retained_index_cleanup_effect:
  q < LENGTH bb.bb_instructions /\
  (EL q bb.bb_instructions).inst_opcode = PHI /\
  (EL q bb.bb_instructions).inst_outputs = [x] /\
  simplify_current_phi (EL q bb.bb_instructions) = EL q bb.bb_instructions /\
  (!i. i < q ==> (EL i bb.bb_instructions).inst_opcode = PHI /\
    ~MEM x (EL i bb.bb_instructions).inst_outputs) ==>
  phi_eff (SOME p) x (simplify_current_phi_block bb).bb_instructions =
    resolve_phi p (EL q bb.bb_instructions).inst_operands
Proof
  strip_tac >> irule current_retained_cleanup_effect >> simp[] >>
  qexistsl [`TAKE q bb.bb_instructions`, `DROP (SUC q) bb.bb_instructions`] >>
  simp[listTheory.EVERY_EL, listTheory.EL_TAKE] >>
  conj_tac >- simp[GSYM listTheory.APPEND_ASSOC, rich_listTheory.TAKE_DROP_SUC] >>
  metis_tac[current_retained_cleanup_outputs]
QED

Theorem current_retained_filter_unique_index:
  !xs P i j.
  LENGTH (FILTER P xs) <= 1 /\ i < LENGTH xs /\ j < LENGTH xs /\
  P (EL i xs) /\ P (EL j xs) ==> i = j
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `i` >> Cases_on `j` >> gvs[]
  >- (`LENGTH (FILTER P xs) = 0` by decide_tac >>
      `FILTER P xs = []` by metis_tac[listTheory.LENGTH_NIL] >>
      fs[listTheory.FILTER_EQ_NIL, listTheory.EVERY_EL] >> metis_tac[])
  >- (`LENGTH (FILTER P xs) = 0` by decide_tac >>
      `FILTER P xs = []` by metis_tac[listTheory.LENGTH_NIL] >>
      fs[listTheory.FILTER_EQ_NIL, listTheory.EVERY_EL] >> metis_tac[]) >>
  first_x_assum irule >> simp[] >> qexists_tac `P` >> simp[] >>
  Cases_on `P h` >> gvs[] >> decide_tac
QED
