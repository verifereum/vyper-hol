Theory concretizePtrForwardingBoundary
Ancestors
  concretizeStepStructure concretizeStepShape
  concretizeStepRetpc concretizeStageShape contextCodegenRel
  concretizeMemLocDefs passSharedDefs venomInst list rich_list finite_map arithmetic

Theorem ptr_forwarding_step_back:
  step_back_assign i op = SOME op' ==>
  step_back_assign (concretize_inst_with_positions p i) op = SOME op'
Proof
  Cases_on `i.inst_opcode = ALLOCA`
  >- (Cases_on `i.inst_outputs` >>
      simp[concretize_inst_with_positions_def] >>
      rename1 `i.inst_outputs = out::rest` >>
      Cases_on `rest` >> simp[concretize_inst_with_positions_def] >>
      Cases_on `FLOOKUP p (Allocation i.inst_id)` >>
      Cases_on `op` >>
      gvs[step_back_assign_def, mk_assign_inst_def, mk_nop_inst_def,
          AllCaseEqs()]) >>
  simp[concretize_positions_unchanged]
QED

Theorem ptr_forwarding_same_after_rewrite:
  !xs x y.
  EVERY (\i. i.inst_opcode = NOP ==> i.inst_outputs = []) xs /\
  same_after_assigns xs x y ==>
  same_after_assigns
    (FILTER (\i. i.inst_opcode <> NOP)
      (MAP (concretize_inst_with_positions p) xs)) x y
Proof
  Induct_on `xs` >- simp[same_after_assigns_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `x = y`
  >- (gvs[] >> Cases_on `FILTER (\i. i.inst_opcode <> NOP)
         (MAP (concretize_inst_with_positions p) (h::xs))` >>
      simp[same_after_assigns_def]) >>
  gvs[same_after_assigns_def] >>
  Cases_on `step_back_assign h x` >> gvs[] >>
  Cases_on `step_back_assign h y` >> gvs[] >>
  imp_res_tac ptr_forwarding_step_back >>
  Cases_on `(concretize_inst_with_positions p h).inst_opcode = NOP`
  >- (Cases_on `h.inst_opcode = ALLOCA`
      >- (Cases_on `x` >> Cases_on `y` >>
          gvs[step_back_assign_def, AllCaseEqs()]) >>
      gvs[concretize_positions_unchanged] >>
      Cases_on `x` >> Cases_on `y` >>
      gvs[step_back_assign_def]) >>
  simp[same_after_assigns_def]
QED

Theorem ptr_forwarding_assign_interval:
  EVERY (\i. i.inst_opcode = ASSIGN) xs ==>
  FILTER (\i. i.inst_opcode <> NOP)
    (MAP (concretize_inst_with_positions p) xs) = xs
Proof
  Induct_on `xs` >> simp[] >> rpt strip_tac >>
  simp[concretize_positions_unchanged]
QED

(* Backward order: the latest copy causes two unequal operands to meet;
   an earlier allocation must then be irrelevant, present or missing. *)
Theorem ptr_forwarding_alloca_prefix_eval:
  same_after_assigns
    [<|inst_id := 2; inst_opcode := ASSIGN;
        inst_operands := [Var "a"]; inst_outputs := ["b"]|>;
     <|inst_id := 1; inst_opcode := ALLOCA;
        inst_operands := [Lit 32w]; inst_outputs := ["a"]|>]
    (Var "b") (Var "a") /\
  same_after_assigns
    (FILTER (\i. i.inst_opcode <> NOP)
      (MAP (concretize_inst_with_positions (FEMPTY |+ (Allocation 1,64)))
        [<|inst_id := 2; inst_opcode := ASSIGN;
            inst_operands := [Var "a"]; inst_outputs := ["b"]|>;
         <|inst_id := 1; inst_opcode := ALLOCA;
            inst_operands := [Lit 32w]; inst_outputs := ["a"]|>]))
    (Var "b") (Var "a") /\
  same_after_assigns
    (FILTER (\i. i.inst_opcode <> NOP)
      (MAP (concretize_inst_with_positions FEMPTY)
        [<|inst_id := 2; inst_opcode := ASSIGN;
            inst_operands := [Var "a"]; inst_outputs := ["b"]|>;
         <|inst_id := 1; inst_opcode := ALLOCA;
            inst_operands := [Lit 32w]; inst_outputs := ["a"]|>]))
    (Var "b") (Var "a")
Proof
  EVAL_TAC
QED

Theorem ptr_forwarding_nop_prefix_eval:
  same_after_assigns
    [<|inst_id := 3; inst_opcode := NOP;
        inst_operands := []; inst_outputs := []|>;
     <|inst_id := 2; inst_opcode := ASSIGN;
        inst_operands := [Var "a"]; inst_outputs := ["b"]|>]
    (Var "b") (Var "a") /\
  same_after_assigns
    (FILTER (\i. i.inst_opcode <> NOP)
      (MAP (concretize_inst_with_positions FEMPTY)
        [<|inst_id := 3; inst_opcode := NOP;
            inst_operands := []; inst_outputs := []|>;
         <|inst_id := 2; inst_opcode := ASSIGN;
            inst_operands := [Var "a"]; inst_outputs := ["b"]|>]))
    (Var "b") (Var "a")
Proof
  EVAL_TAC
QED

Theorem ptr_forwarding_overwritten_alloca_eval:
  same_after_assigns
    [<|inst_id := 3; inst_opcode := ASSIGN;
        inst_operands := [Var "a"]; inst_outputs := ["b"]|>;
     <|inst_id := 2; inst_opcode := ASSIGN;
        inst_operands := [Lit 0w]; inst_outputs := ["a"]|>;
     <|inst_id := 1; inst_opcode := ALLOCA;
        inst_operands := [Lit 32w]; inst_outputs := ["a"]|>]
    (Var "b") (Lit 0w) /\
  same_after_assigns
    (FILTER (\i. i.inst_opcode <> NOP)
      (MAP (concretize_inst_with_positions (FEMPTY |+ (Allocation 1,64)))
        [<|inst_id := 3; inst_opcode := ASSIGN;
            inst_operands := [Var "a"]; inst_outputs := ["b"]|>;
         <|inst_id := 2; inst_opcode := ASSIGN;
            inst_operands := [Lit 0w]; inst_outputs := ["a"]|>;
         <|inst_id := 1; inst_opcode := ALLOCA;
            inst_operands := [Lit 32w]; inst_outputs := ["a"]|>]))
    (Var "b") (Lit 0w)
Proof
  EVAL_TAC
QED

Theorem ptr_forwarding_pair_split[local]:
  revert_forward_pair bb i j ==>
  ?pre c mid r post.
    bb.bb_instructions = pre ++ c::mid ++ r::post /\
    i = LENGTH pre /\ j = LENGTH pre + SUC (LENGTH mid) /\
    c.inst_opcode = RETURNDATACOPY /\ r.inst_opcode = REVERT /\
    EVERY (\inst. inst.inst_opcode = ASSIGN) mid /\
    ?p src rds p' rds'.
      c.inst_operands = [p;src;rds] /\ r.inst_operands = [p';rds'] /\
      same_after_assigns (REVERSE pre) src (Lit 0w) /\
      same_after_assigns (REVERSE pre) p (resolve_block_assigns (REVERSE mid) p') /\
      same_after_assigns (REVERSE pre) rds (resolve_block_assigns (REVERSE mid) rds')
Proof
  rw[revert_forward_pair_def, get_instruction_def] >>
  qexistsl [`TAKE i bb.bb_instructions`, `EL i bb.bb_instructions`,
            `TAKE (j - SUC i) (DROP (SUC i) bb.bb_instructions)`,
            `EL j bb.bb_instructions`, `DROP (SUC j) bb.bb_instructions`] >>
  simp[LENGTH_TAKE, LENGTH_DROP] >>
  conj_tac >- (
    qspec_then `i` (qspec_then `bb.bb_instructions` mp_tac) TAKE_DROP_SUC >>
    qspec_then `j - SUC i`
      (qspec_then `DROP (SUC i) bb.bb_instructions` mp_tac) TAKE_DROP_SUC >>
    simp[LENGTH_DROP, EL_DROP, DROP_DROP] >>
    `SUC i + SUC (j - SUC i) = SUC j` by decide_tac >>
    simp[] >> metis_tac[APPEND_ASSOC]) >>
  simp[EVERY_EL, LENGTH_TAKE, LENGTH_DROP, EL_TAKE, EL_DROP] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem ptr_forwarding_pair_rewrite:
  EVERY (\inst. inst.inst_opcode = NOP ==> inst.inst_outputs = []) bb.bb_instructions /\
  revert_forward_pair bb i j ==>
  revert_forward_pair
    (bb with bb_instructions := FILTER (\inst. inst.inst_opcode <> NOP)
      (MAP (concretize_inst_with_positions p) bb.bb_instructions))
    (LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
      (MAP (concretize_inst_with_positions p) (TAKE i bb.bb_instructions))))
    (LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
      (MAP (concretize_inst_with_positions p) (TAKE j bb.bb_instructions))))
Proof
  strip_tac >> drule ptr_forwarding_pair_split >> strip_tac >>
  `FILTER (\inst. inst.inst_opcode <> NOP)
    (MAP (concretize_inst_with_positions p) mid) = mid` by
    metis_tac[ptr_forwarding_assign_interval] >>
  `concretize_inst_with_positions p c = c /\
   concretize_inst_with_positions p r = r` by simp[concretize_positions_unchanged] >>
  `EVERY (\inst. inst.inst_opcode = NOP ==> inst.inst_outputs = []) pre` by
    fs[EVERY_APPEND] >>
  `TAKE i bb.bb_instructions = pre /\
   TAKE j bb.bb_instructions = pre ++ c::mid` by
    (qpat_assum `bb.bb_instructions = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `i = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `j = _` (fn th => pure_rewrite_tac[th]) >>
     `TAKE (LENGTH pre + SUC (LENGTH mid)) pre = pre` by
       (irule TAKE_LENGTH_TOO_LONG >> decide_tac) >>
     pure_rewrite_tac[TAKE_APPEND] >>
     qpat_assum `TAKE _ pre = pre` (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms, ADD1]) >>
  qpat_assum `TAKE i bb.bb_instructions = pre` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `TAKE j bb.bb_instructions = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `bb.bb_instructions = _` (fn th => pure_rewrite_tac[th]) >>
  pure_rewrite_tac[MAP_APPEND, MAP, FILTER_APPEND, FILTER] >>
  qpat_x_assum `concretize_inst_with_positions p c = c`
    (fn th => pure_rewrite_tac[th]) >>
  qpat_x_assum `concretize_inst_with_positions p r = r`
    (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `FILTER _ (MAP _ mid) = mid`
    (fn th => pure_rewrite_tac[th]) >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `LENGTH tpre` >>
  qmatch_goalsub_abbrev_tac `r::tpost` >>
  simp[revert_forward_pair_def, get_instruction_def, EL_APPEND_EQN] >>
  conj_tac >- (
    rpt strip_tac >>
    `?n. k - LENGTH tpre = SUC n /\ n < LENGTH mid` by
      (qexists_tac `k - LENGTH tpre - 1` >> decide_tac) >>
    simp[] >> fs[EVERY_EL]) >>
  `DROP (LENGTH tpre + 1) tpre = []` by
    (irule DROP_LENGTH_TOO_LONG >> decide_tac) >>
  `LENGTH tpre - (LENGTH tpre + 1) = 0 /\
   LENGTH tpre + 1 - (LENGTH mid + (LENGTH tpre + 1)) = 0 /\
   LENGTH tpre - (LENGTH mid + (LENGTH tpre + 1)) = 0` by decide_tac >>
  simp[TAKE_APPEND, DROP_APPEND, ADD1] >>
  simp[Abbr `tpre`, GSYM FILTER_REVERSE, GSYM MAP_REVERSE] >>
  rpt conj_tac >>
  irule ptr_forwarding_same_after_rewrite >>
  simp[EVERY_REVERSE]
QED

Theorem ptr_forwarding_at_rewrite:
  EVERY (\inst. inst.inst_opcode = NOP ==> inst.inst_outputs = []) bb.bb_instructions /\
  revert_forward_at bb k ==>
  revert_forward_at
    (bb with bb_instructions := FILTER (\inst. inst.inst_opcode <> NOP)
      (MAP (concretize_inst_with_positions p) bb.bb_instructions))
    (LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
      (MAP (concretize_inst_with_positions p) (TAKE k bb.bb_instructions))))
Proof
  simp[revert_forward_at_def] >> rpt strip_tac >>
  drule_all ptr_forwarding_pair_rewrite >>
  metis_tac[]
QED
