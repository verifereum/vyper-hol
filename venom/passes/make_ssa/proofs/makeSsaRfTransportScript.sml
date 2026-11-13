Theory makeSsaRfTransport
Ancestors makeSsaCurrentCleanupShape
  makeSsaRfShape makeSsaRfWitness makeSsaRfAssign contextCodegenRel
          venomInst venomWf list rich_list

Theorem rf_resolve_assigns_shape:
  !xs ys op. LIST_REL rf_copy_shape xs ys ==>
    resolve_block_assigns ys op = resolve_block_assigns xs op
Proof
  Induct >> Cases_on `ys` >> simp[resolve_block_assigns_def] >>
  rpt strip_tac >> gvs[rf_copy_shape_def] >>
  Cases_on `op` >> simp[resolve_block_assigns_def] >>
  Cases_on `MEM s h.inst_outputs` >> simp[] >>
  Cases_on `h.inst_opcode = ASSIGN` >> gvs[] >>
  Cases_on `h.inst_outputs = [s] /\ LENGTH h.inst_operands = 1` >> simp[]
QED

Theorem rf_copy_shape_get_instruction:
  LIST_REL rf_copy_shape bb.bb_instructions bb'.bb_instructions /\
  get_instruction bb k = SOME inst ==>
  ?inst'. get_instruction bb' k = SOME inst' /\ rf_copy_shape inst inst'
Proof
  simp[get_instruction_def, LIST_REL_EL_EQN] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem rf_copy_shape_segment:
  LIST_REL rf_copy_shape xs ys ==>
  LIST_REL rf_copy_shape (REVERSE (TAKE n (DROP k xs)))
    (REVERSE (TAKE n (DROP k ys)))
Proof
  strip_tac >> irule LIST_REL_REVERSE >>
  irule LIST_REL_TAKE >> irule LIST_REL_DROP >> simp[]
QED

Theorem rf_copy_shape_pair:
  LIST_REL rf_copy_shape bb.bb_instructions bb'.bb_instructions /\
  revert_forward_pair bb i j ==> revert_forward_pair bb' i j
Proof
  strip_tac >>
  qpat_x_assum `revert_forward_pair _ _ _` mp_tac >>
  simp[revert_forward_pair_def] >> strip_tac >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `?inst0. get_instruction bb k = SOME inst0 /\ rf_copy_shape inst0 inst`
        by (gvs[get_instruction_def, LIST_REL_EL_EQN, AllCaseEqs()] >>
            metis_tac[]) >>
      gvs[rf_copy_shape_def] >> metis_tac[]) >>
  `?copy. get_instruction bb' i = SOME copy /\ rf_copy_shape inst1 copy`
    by metis_tac[rf_copy_shape_get_instruction] >>
  `?rev. get_instruction bb' j = SOME rev /\ rf_copy_shape inst2 rev`
    by metis_tac[rf_copy_shape_get_instruction] >>
  qexistsl [`copy`, `rev`, `p`, `src`, `rds`, `p'`, `rds'`] >>
  `LIST_REL rf_copy_shape (REVERSE (TAKE i bb.bb_instructions))
      (REVERSE (TAKE i bb'.bb_instructions))`
    by (irule LIST_REL_REVERSE >> irule LIST_REL_TAKE >> simp[]) >>
  `LIST_REL rf_copy_shape
      (REVERSE (TAKE (j - SUC i) (DROP (SUC i) bb.bb_instructions)))
      (REVERSE (TAKE (j - SUC i) (DROP (SUC i) bb'.bb_instructions)))`
    by (irule rf_copy_shape_segment >> simp[]) >>
  imp_res_tac rf_resolve_assigns_shape >>
  imp_res_tac rf_same_after_assigns_shape >>
  gvs[rf_copy_shape_def]
QED

Theorem rf_copy_shape_at:
  LIST_REL rf_copy_shape bb.bb_instructions bb'.bb_instructions /\
  revert_forward_at bb k ==> revert_forward_at bb' k
Proof
  simp[revert_forward_at_def] >> metis_tac[rf_copy_shape_pair]
QED

Theorem rf_back_trace_forward_append:
  rf_back_trace V f g (REVERSE (xs ++ ys)) (REVERSE (xs' ++ ys')) /\
  LENGTH ys' = LENGTH ys ==>
  ?h. rf_back_trace V f h (REVERSE xs) (REVERSE xs') /\
      rf_back_trace V h g (REVERSE ys) (REVERSE ys')
Proof
  strip_tac >> drule rf_back_trace_split >>
  disch_then (qspec_then `LENGTH ys` strip_assume_tac) >>
  gvs[REVERSE_APPEND, TAKE_APPEND, DROP_APPEND,
      TAKE_LENGTH_TOO_LONG, DROP_LENGTH_TOO_LONG] >> metis_tac[]
QED

Theorem rf_back_trace_forward_cons:
  rf_back_trace V f g (REVERSE (inst::xs)) (REVERSE (inst'::ys)) ==>
  ?h. rf_local_step V f h inst inst' /\
      EVERY (rf_operand_in V) inst.inst_operands /\
      rf_back_trace V h g (REVERSE xs) (REVERSE ys)
Proof
  strip_tac >>
  `LENGTH ys = LENGTH xs` by
    (drule rf_back_trace_length >> simp[]) >>
  `?h. rf_back_trace V f h (REVERSE [inst]) (REVERSE [inst']) /\
       rf_back_trace V h g (REVERSE xs) (REVERSE ys)` by
    (irule rf_back_trace_forward_append >> gvs[REVERSE_DEF]) >>
  gvs[rf_back_trace_def] >> metis_tac[]
QED

Theorem rf_map_operand_no_outputs:
  rf_local_step V f g inst inst' /\ inst.inst_outputs = [] /\
  rf_operand_in V op ==> rf_map_operand g op = rf_map_operand f op
Proof
  Cases_on `op` >> simp[rf_operand_in_def, rf_map_operand_def, rf_local_step_def]
QED

Theorem rf_resolve_assigns_in:
  !xs op. EVERY rf_assign_inst xs /\
    EVERY (\inst. EVERY (rf_operand_in V) inst.inst_operands) xs /\
    rf_operand_in V op ==> rf_operand_in V (resolve_block_assigns xs op)
Proof
  Induct >- simp[resolve_block_assigns_def] >> rpt gen_tac >> strip_tac >>
  gvs[] >> drule rf_assign_step_total >>
  disch_then (qspec_then `op` strip_assume_tac) >>
  drule_all rf_assign_resolve_step >> disch_then (qspec_then `xs` assume_tac) >>
  simp[] >> first_x_assum irule >> metis_tac[rf_step_back_assign_in]
QED

Theorem rf_back_trace_operands_in:
  !xs ys f g. rf_back_trace V f g xs ys ==>
    EVERY (\inst. EVERY (rf_operand_in V) inst.inst_operands) xs
Proof
  Induct >> simp[rf_back_trace_def] >> rpt strip_tac >> metis_tac[]
QED

Theorem rf_back_trace_forward_split:
  rf_back_trace V f g (REVERSE xs) (REVERSE ys) ==>
  ?h. rf_back_trace V f h (REVERSE (TAKE n xs)) (REVERSE (TAKE n ys)) /\
      rf_back_trace V h g (REVERSE (DROP n xs)) (REVERSE (DROP n ys))
Proof
  strip_tac >> irule rf_back_trace_forward_append >>
  drule rf_back_trace_length >> simp[]
QED

Theorem rf_drop_at:
  !xs n. n < LENGTH xs ==> DROP n xs = EL n xs :: DROP (SUC n) xs
Proof
  Induct >> Cases_on `n` >> simp[]
QED

Theorem rf_back_trace_at:
  rf_back_trace V f g (REVERSE xs) (REVERSE ys) /\ k < LENGTH xs ==>
  ?a b. rf_back_trace V f a (REVERSE (TAKE k xs)) (REVERSE (TAKE k ys)) /\
    rf_local_step V a b (EL k xs) (EL k ys) /\
    EVERY (rf_operand_in V) (EL k xs).inst_operands /\
    rf_back_trace V b g (REVERSE (DROP (SUC k) xs)) (REVERSE (DROP (SUC k) ys))
Proof
  strip_tac >> drule rf_back_trace_length >> simp[LENGTH_REVERSE] >> strip_tac >>
  drule rf_back_trace_forward_split >>
  disch_then (qspec_then `k` strip_assume_tac) >>
  `DROP k xs = EL k xs :: DROP (SUC k) xs` by simp[rf_drop_at] >>
  `DROP k ys = EL k ys :: DROP (SUC k) ys` by simp[rf_drop_at] >>
  gvs[] >> drule (SRULE [REVERSE_DEF] rf_back_trace_forward_cons) >>
  strip_tac >> metis_tac[]
QED

Theorem rf_trace_comparison:
  rf_back_trace V f a prefix prefix' /\
  rf_local_step V a b copy copy' /\ copy.inst_outputs = [] /\
  rf_back_trace V b c middle middle' /\ EVERY rf_assign_inst middle /\
  rf_operand_in V p /\ rf_operand_in V q /\
  same_after_assigns prefix p (resolve_block_assigns middle q) ==>
  same_after_assigns prefix' (rf_map_operand a p)
    (resolve_block_assigns middle' (rf_map_operand c q))
Proof
  strip_tac >> drule_all rf_resolve_assigns_transport >> strip_tac >> simp[] >>
  drule rf_back_trace_operands_in >> strip_tac >>
  `rf_operand_in V (resolve_block_assigns middle q)` by
    (irule rf_resolve_assigns_in >> metis_tac[rf_back_trace_operands_in]) >>
  `rf_map_operand b (resolve_block_assigns middle q) =
   rf_map_operand a (resolve_block_assigns middle q)` by
    metis_tac[rf_map_operand_no_outputs] >>
  gvs[] >> irule rf_same_after_assigns_transport >> metis_tac[]
QED

Theorem rf_back_trace_between:
  rf_back_trace V f g (REVERSE xs) (REVERSE ys) /\ i < j /\ j < LENGTH xs ==>
  ?a b c d.
    rf_back_trace V f a (REVERSE (TAKE i xs)) (REVERSE (TAKE i ys)) /\
    rf_local_step V a b (EL i xs) (EL i ys) /\
    EVERY (rf_operand_in V) (EL i xs).inst_operands /\
    rf_back_trace V b c (REVERSE (TAKE (j - SUC i) (DROP (SUC i) xs)))
      (REVERSE (TAKE (j - SUC i) (DROP (SUC i) ys))) /\
    rf_local_step V c d (EL j xs) (EL j ys) /\
    EVERY (rf_operand_in V) (EL j xs).inst_operands
Proof
  strip_tac >>
  `LENGTH ys = LENGTH xs` by
    (drule rf_back_trace_length >> simp[LENGTH_REVERSE]) >>
  `i < LENGTH xs` by decide_tac >>
  drule_all rf_back_trace_at >> strip_tac >>
  `j - SUC i < LENGTH (DROP (SUC i) xs)` by (simp[LENGTH_DROP] >> decide_tac) >>
  drule_all rf_back_trace_at >> strip_tac >>
  `SUC i + (j - SUC i) = j` by decide_tac >>
  gvs[EL_DROP] >> metis_tac[]
QED

Theorem rf_wf_assign_inst:
  inst_wf inst /\ inst.inst_opcode = ASSIGN ==> rf_assign_inst inst
Proof
  strip_tac >> gvs[inst_wf_def, rf_assign_inst_def, LENGTH_EQ_NUM_compute]
QED

Theorem rf_pair_middle_assigns:
  EVERY inst_wf bb.bb_instructions /\ revert_forward_pair bb i j ==>
  EVERY rf_assign_inst
    (REVERSE (TAKE (j - SUC i) (DROP (SUC i) bb.bb_instructions)))
Proof
  simp[EVERY_REVERSE, EVERY_EL] >> strip_tac >> rpt strip_tac >>
  irule rf_wf_assign_inst >>
  `SUC i + n < LENGTH bb.bb_instructions` by (gvs[LENGTH_TAKE_EQ, LENGTH_DROP] >> decide_tac) >>
  `i < SUC i + n /\ SUC i + n < j` by
    (gvs[LENGTH_TAKE_EQ, revert_forward_pair_def] >> decide_tac) >>
  simp[EL_TAKE, EL_DROP] >>
  gvs[revert_forward_pair_def] >>
  first_x_assum irule >> qexists_tac `n + SUC i` >> simp[get_instruction_def]
QED

Theorem rf_back_trace_opcodes:
  !xs ys f g. rf_back_trace V f g xs ys ==>
    LIST_REL (\x y. x.inst_opcode = y.inst_opcode) xs ys
Proof
  Induct >> simp[rf_back_trace_def] >> rpt strip_tac >>
  gvs[rf_local_step_def] >> metis_tac[]
QED

Theorem rf_back_trace_pair:
  rf_back_trace V f g (REVERSE bb.bb_instructions) (REVERSE bb'.bb_instructions) /\
  EVERY inst_wf bb.bb_instructions /\ revert_forward_pair bb i j ==>
  revert_forward_pair bb' i j
Proof
  strip_tac >>
  `EVERY rf_assign_inst
    (REVERSE (TAKE (j - SUC i) (DROP (SUC i) bb.bb_instructions)))` by
    metis_tac[rf_pair_middle_assigns] >>
  `LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions` by
    (drule rf_back_trace_length >> simp[LENGTH_REVERSE]) >>
  `LIST_REL (\x y. x.inst_opcode = y.inst_opcode)
     bb.bb_instructions bb'.bb_instructions` by
    (drule rf_back_trace_opcodes >>
     disch_then (mp_tac o MATCH_MP LIST_REL_REVERSE) >> simp[]) >>
  qpat_x_assum `revert_forward_pair _ _ _` mp_tac >>
  simp[revert_forward_pair_def] >> strip_tac >>
  `i < LENGTH bb.bb_instructions /\ j < LENGTH bb.bb_instructions /\
   inst1 = EL i bb.bb_instructions /\ inst2 = EL j bb.bb_instructions` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  drule_all rf_back_trace_between >> strip_tac >>
  `inst1.inst_outputs = []` by
    (qpat_x_assum `EVERY inst_wf _` mp_tac >> simp[EVERY_EL] >>
     disch_then (qspec_then `i` mp_tac) >> gvs[inst_wf_def]) >>
  simp[revert_forward_pair_def] >> conj_tac
  >- (rpt strip_tac >> gvs[get_instruction_def, LIST_REL_EL_EQN, AllCaseEqs()] >>
      metis_tac[]) >>
  qexistsl [`EL i bb'.bb_instructions`, `EL j bb'.bb_instructions`,
    `rf_map_operand a p`, `rf_map_operand a src`, `rf_map_operand a rds`,
    `rf_map_operand c p'`, `rf_map_operand c rds'`] >>
  imp_res_tac (iffLR rf_local_step_def) >>
  gvs[get_instruction_def] >>
  qpat_x_assum `LIST_REL _ _ _` kall_tac >>
  qpat_x_assum `EVERY inst_wf _` kall_tac >>
  rpt (qpat_x_assum `!v. _` kall_tac) >>
  rpt (qpat_x_assum `_.inst_opcode = _` kall_tac) >>
  rpt (qpat_x_assum `_.inst_operands = _` kall_tac) >>
  conj_tac
  >- metis_tac[rf_same_after_assigns_transport, rf_map_operand_def, rf_operand_in_def] >>
  conj_tac >> irule rf_trace_comparison >> metis_tac[EVERY_REVERSE]
QED

Theorem rf_back_trace_at_pair:
  rf_back_trace V f g (REVERSE bb.bb_instructions) (REVERSE bb'.bb_instructions) /\
  EVERY inst_wf bb.bb_instructions /\ revert_forward_at bb k ==>
  revert_forward_at bb' k
Proof
  simp[revert_forward_at_def] >> metis_tac[rf_back_trace_pair]
QED

Theorem rf_unprepend_pair:
  EVERY (\inst. inst.inst_opcode = PHI) pre /\
  revert_forward_pair (bb with bb_instructions := pre ++ bb.bb_instructions)
    (LENGTH pre + i) (LENGTH pre + j) ==>
  revert_forward_pair bb i j
Proof
  simp[revert_forward_pair_def, rf_prepend_get_instruction] >> strip_tac >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      qexists_tac `LENGTH pre + k` >> simp[rf_prepend_get_instruction]) >>
  qexistsl [`inst1`, `inst2`, `p`, `src`, `rds`, `p'`, `rds'`] >>
  `j + LENGTH pre - SUC (i + LENGTH pre) = j - SUC i` by decide_tac >>
  `SUC (i + LENGTH pre) - LENGTH pre = SUC i` by decide_tac >>
  gvs[TAKE_APPEND, DROP_APPEND, REVERSE_APPEND,
      TAKE_LENGTH_TOO_LONG, DROP_LENGTH_TOO_LONG, arithmeticTheory.ADD_COMM] >>
  rpt conj_tac >> irule rf_same_after_drop_phi_suffix >>
  qexists_tac `REVERSE pre` >> simp[EVERY_REVERSE]
QED

Theorem rf_no_id_copy_shape:
  current_inst_no_id inst = current_inst_no_id inst' ==> rf_copy_shape inst inst'
Proof
  simp[current_inst_no_id_def, instruction_component_equality, rf_copy_shape_def] >>
  metis_tac[]
QED

Theorem rf_pair_phi_prefix_indices:
  bb.bb_instructions = pre ++ tail /\
  EVERY (\inst. inst.inst_opcode = PHI) pre /\ revert_forward_pair bb i j ==>
  LENGTH pre <= i /\ LENGTH pre <= j
Proof
  strip_tac >>
  qpat_x_assum `revert_forward_pair _ _ _` mp_tac >>
  simp[revert_forward_pair_def, get_instruction_def] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  conj_tac >> spose_not_then assume_tac >>
  gvs[EL_APPEND_EQN, EVERY_EL] >> metis_tac[]
QED

Theorem rf_replace_phi_prefix_pair:
  bb.bb_instructions = pre ++ tail /\
  bb'.bb_instructions = pre' ++ tail' /\
  EVERY (\inst. inst.inst_opcode = PHI) pre /\ LENGTH pre' = LENGTH pre /\
  LIST_REL rf_copy_shape tail tail' /\ revert_forward_pair bb i j ==>
  revert_forward_pair bb' i j
Proof
  strip_tac >> drule_all rf_pair_phi_prefix_indices >> strip_tac >>
  `?m n. i = LENGTH pre + m /\ j = LENGTH pre + n` by
    (qexistsl [`i - LENGTH pre`, `j - LENGTH pre`] >> decide_tac) >>
  gvs[] >>
  `bb with bb_instructions := pre ++ tail = bb` by
    simp[basic_block_component_equality] >>
  `bb' with bb_instructions := pre' ++ tail' = bb'` by
    simp[basic_block_component_equality] >>
  `revert_forward_pair (bb with bb_instructions := tail) m n` by
    (irule rf_unprepend_pair >> qexists_tac `pre` >> simp[]) >>
  `revert_forward_pair (bb' with bb_instructions := tail') m n` by
    (irule rf_copy_shape_pair >> qexists_tac `bb with bb_instructions := tail` >>
     simp[]) >>
  drule rf_prepend_pair >> disch_then (qspec_then `pre'` mp_tac) >> simp[]
QED

Theorem rf_ordinary_suffix_pair:
  bb.bb_instructions = pre ++ tail /\
  EVERY (\inst. inst.inst_opcode = PHI) pre /\
  LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions /\
  (!k. k < LENGTH tail ==>
    current_inst_no_id (EL (LENGTH pre + k) bb'.bb_instructions) =
    current_inst_no_id (EL k tail)) /\ revert_forward_pair bb i j ==>
  revert_forward_pair bb' i j
Proof
  strip_tac >>
  `LENGTH pre <= LENGTH bb'.bb_instructions` by gvs[] >>
  `LENGTH (TAKE (LENGTH pre) bb'.bb_instructions) = LENGTH pre` by simp[] >>
  `bb'.bb_instructions = TAKE (LENGTH pre) bb'.bb_instructions ++
                        DROP (LENGTH pre) bb'.bb_instructions` by simp[] >>
  `LIST_REL rf_copy_shape tail (DROP (LENGTH pre) bb'.bb_instructions)` by
    (simp[LIST_REL_EL_EQN, LENGTH_DROP] >> rpt strip_tac >> irule rf_no_id_copy_shape >> sym_tac >>
     simp[EL_DROP] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  metis_tac[rf_replace_phi_prefix_pair]
QED

Theorem rf_phi_partition_exists:
  !xs. ?pre tail. xs = pre ++ tail /\ EVERY (\inst. inst.inst_opcode = PHI) pre /\
    (tail = [] \/ (HD tail).inst_opcode <> PHI)
Proof
  Induct
  >- (qexistsl [`[]`, `[]`] >> simp[]) >>
  gen_tac >> Cases_on `h.inst_opcode = PHI`
  >- (qpat_x_assum `?pre tail. _` strip_assume_tac >>
      qexistsl [`h::pre`, `tail`] >> simp[]) >>
  qexistsl [`[]`, `h::xs`] >> simp[]
QED

Theorem rf_cleanup_pair:
  revert_forward_pair bb i j ==>
  revert_forward_pair (simplify_current_phi_block bb) i j
Proof
  strip_tac >> qspec_then `bb.bb_instructions` strip_assume_tac rf_phi_partition_exists >>
  `!k. k < LENGTH tail ==>
     current_inst_no_id (EL (LENGTH pre + k)
       (simplify_current_phi_block bb).bb_instructions) = current_inst_no_id (EL k tail)` by
    metis_tac[current_cleanup_block_ordinary_index] >>
  irule rf_ordinary_suffix_pair >> metis_tac[current_cleanup_block_length]
QED

Theorem rf_cleanup_at:
  revert_forward_at bb k ==> revert_forward_at (simplify_current_phi_block bb) k
Proof
  simp[revert_forward_at_def] >> metis_tac[rf_cleanup_pair]
QED

(* A phase certificate records only the boundaries needed by RF transport;
   it does not assert RF preservation, SSA, or semantic correctness. *)
Definition rf_phase_certificate_def:
  rf_phase_certificate V bb bb' d <=>
  ?pre renamed edged f g enabled.
    LENGTH pre = d /\
    EVERY inst_wf (pre ++ bb.bb_instructions) /\
    rf_back_trace V f g (REVERSE (pre ++ bb.bb_instructions))
      (REVERSE renamed.bb_instructions) /\
    LIST_REL rf_copy_shape renamed.bb_instructions edged.bb_instructions /\
    bb' = (if enabled then simplify_current_phi_block edged else edged)
End

Theorem rf_phase_certificate_length:
  rf_phase_certificate V bb bb' d ==>
  LENGTH bb'.bb_instructions = d + LENGTH bb.bb_instructions
Proof
  simp[rf_phase_certificate_def] >> rpt strip_tac >>
  drule rf_back_trace_length >>
  Cases_on `enabled` >> gvs[LIST_REL_EL_EQN, current_cleanup_block_length, LENGTH_REVERSE]
QED

Theorem rf_phase_certificate_pair:
  rf_phase_certificate V bb bb' d /\ revert_forward_pair bb i j ==>
  revert_forward_pair bb' (i + d) (j + d)
Proof
  simp[rf_phase_certificate_def] >> strip_tac >>
  `revert_forward_pair (bb with bb_instructions := pre ++ bb.bb_instructions)
     (LENGTH pre + i) (LENGTH pre + j)` by metis_tac[rf_prepend_pair] >>
  `revert_forward_pair renamed (LENGTH pre + i) (LENGTH pre + j)` by
    (irule rf_back_trace_pair >>
     qexistsl [`V`, `bb with bb_instructions := pre ++ bb.bb_instructions`, `f`, `g`] >> simp[] >>
     metis_tac[]) >>
  `revert_forward_pair edged (LENGTH pre + i) (LENGTH pre + j)` by
    metis_tac[rf_copy_shape_pair] >>
  Cases_on `enabled` >> gvs[] >> metis_tac[rf_cleanup_pair, arithmeticTheory.ADD_COMM]
QED

Theorem rf_phase_certificate_at:
  rf_phase_certificate V bb bb' d /\ revert_forward_at bb k ==>
  LENGTH bb.bb_instructions <= LENGTH bb'.bb_instructions /\
  revert_forward_at bb'
    (k + (LENGTH bb'.bb_instructions - LENGTH bb.bb_instructions))
Proof
  strip_tac >> drule rf_phase_certificate_length >> strip_tac >> simp[] >>
  gvs[revert_forward_at_def] >> drule_all rf_phase_certificate_pair >>
  simp[arithmeticTheory.ADD_COMM] >> metis_tac[]
QED
