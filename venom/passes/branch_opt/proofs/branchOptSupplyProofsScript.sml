(*
 * Branch Optimization Pass — structural proofs for the supply-aware form
 *
 * branch_opt_function_supply keeps the function well formed and in SSA
 * form: the ISZERO it inserts takes a fresh variable and a fresh
 * instruction id from the supply, and the swapped JNZ keeps its
 * successor set.
 *
 * TOP-LEVEL:
 *   branch_opt_function_supply_ssa_form   — SSA form preservation
 *   branch_opt_function_supply_wf         — well-formed function preservation
 *)

Theory branchOptSupplyProofs
Ancestors
  branchOptDefs irSupply venomFnScheduleRunner unitShapeDefs
  stackPlanTypes dfgAnalysisProps venomWf venomInst venomState
  list rich_list

(* ===== The three shapes of a transformed block ===== *)

Theorem branch_opt_block_supply_cases[local]:
  branch_opt_block_supply dfg live_at s bb = (bb',s') ==>
  (bb' = bb /\ s' = s) \/
  (?front t v f g prev.
     bb.bb_instructions = front ++ [t] /\ t.inst_opcode = JNZ /\
     t.inst_operands = [Var v; Label f; Label g] /\
     dfg_get_def dfg v = SOME prev /\ prev.inst_opcode = ISZERO /\
     s' = s /\
     bb' = bb with bb_instructions :=
       front ++ [t with inst_operands :=
                   [HD prev.inst_operands; Label g; Label f]]) \/
  (?front t v f g tmp s1 id.
     bb.bb_instructions = front ++ [t] /\ t.inst_opcode = JNZ /\
     t.inst_operands = [Var v; Label f; Label g] /\
     fresh_ir_var s = (tmp,s1) /\ fresh_inst_id s1 = (id,s') /\
     bb' = bb with bb_instructions :=
       front ++ [<| inst_id := id; inst_opcode := ISZERO;
                    inst_operands := [Var v]; inst_outputs := [tmp] |>;
                 t with inst_operands := [Var tmp; Label g; Label f]])
Proof
  strip_tac >>
  qspec_then `bb.bb_instructions` strip_assume_tac SNOC_CASES >>
  gvs[branch_opt_block_supply_def, FRONT_SNOC, LAST_SNOC] >>
  gvs[AllCaseEqs()] >>
  BasicProvers.every_case_tac >> gvs[SNOC_APPEND]
QED

Theorem branch_opt_block_supply_label[local]:
  branch_opt_block_supply dfg live_at s bb = (bb',s') ==>
  bb'.bb_label = bb.bb_label
Proof
  strip_tac >> drule branch_opt_block_supply_cases >> strip_tac >> gvs[]
QED

(* ===== Supply monotonicity ===== *)

Theorem branch_opt_block_supply_mono[local]:
  branch_opt_block_supply dfg live_at s bb = (bb',s') ==>
  (!x. MEM x s.irs_used_vars ==> MEM x s'.irs_used_vars) /\
  (!i. MEM i s.irs_used_inst_ids ==> MEM i s'.irs_used_inst_ids) /\
  (ir_supply_inst_ok s ==> ir_supply_inst_ok s')
Proof
  strip_tac >> drule branch_opt_block_supply_cases >> strip_tac >> gvs[] >>
  drule fresh_ir_var_contract >> strip_tac >>
  gvs[fresh_inst_id_def] >>
  gvs[ir_supply_inst_ok_def, EVERY_MEM] >>
  rpt strip_tac >> gvs[] >>
  res_tac >> decide_tac
QED

(* ===== Distinctness over a block list, for any per-block projection ===== *)

Theorem branch_opt_blocks_supply_used_mono[local]:
  !U Q dfg live_at.
    (!s bb bb' s'.
       branch_opt_block_supply dfg live_at s bb = (bb',s') /\ Q s ==>
       Q s' /\ !x. MEM x (U s) ==> MEM x (U s')) ==>
    !bbs s bbs' s'.
      branch_opt_blocks_supply dfg live_at s bbs = (bbs',s') /\ Q s ==>
      !x. MEM x (U s) ==> MEM x (U s')
Proof
  rpt gen_tac >> strip_tac >>
  Induct >> simp[branch_opt_blocks_supply_def] >>
  rpt gen_tac >>
  Cases_on `branch_opt_block_supply dfg live_at s h` >>
  rename1 `_ = (b1,s1)` >>
  Cases_on `branch_opt_blocks_supply dfg live_at s1 bbs` >>
  simp[] >> strip_tac >> gvs[] >>
  rename1 `branch_opt_blocks_supply _ _ s1 bbs = (bs2,s2)` >>
  `Q s1 /\ !x. MEM x (U s) ==> MEM x (U s1)` by metis_tac[] >>
  `!x. MEM x (U s1) ==> MEM x (U s2)` by metis_tac[] >>
  metis_tac[]
QED

Theorem branch_opt_blocks_supply_distinct[local]:
  !P U Q dfg live_at.
    (!s bb bb' s'.
       branch_opt_block_supply dfg live_at s bb = (bb',s') /\ Q s /\
       ALL_DISTINCT (P bb) /\ (!x. MEM x (P bb) ==> MEM x (U s)) ==>
       ALL_DISTINCT (P bb') /\
       (!x. MEM x (P bb') ==> MEM x (P bb) \/ (MEM x (U s') /\ ~MEM x (U s)))) /\
    (!s bb bb' s'.
       branch_opt_block_supply dfg live_at s bb = (bb',s') /\ Q s ==>
       Q s' /\ !x. MEM x (U s) ==> MEM x (U s')) ==>
    !bbs s bbs' s'.
      branch_opt_blocks_supply dfg live_at s bbs = (bbs',s') /\ Q s /\
      ALL_DISTINCT (FLAT (MAP P bbs)) /\
      (!x. MEM x (FLAT (MAP P bbs)) ==> MEM x (U s)) ==>
      ALL_DISTINCT (FLAT (MAP P bbs')) /\
      (!x. MEM x (FLAT (MAP P bbs')) ==>
           MEM x (FLAT (MAP P bbs)) \/ (MEM x (U s') /\ ~MEM x (U s)))
Proof
  rpt gen_tac >> strip_tac >>
  drule branch_opt_blocks_supply_used_mono >> strip_tac >>
  Induct >> simp[branch_opt_blocks_supply_def] >>
  rpt gen_tac >>
  Cases_on `branch_opt_block_supply dfg live_at s h` >>
  rename1 `_ = (b1,s1)` >>
  Cases_on `branch_opt_blocks_supply dfg live_at s1 bbs` >>
  simp[] >> strip_tac >> gvs[] >>
  rename1 `branch_opt_blocks_supply _ _ s1 bbs = (bs2,s2)` >>
  `Q s1 /\ !x. MEM x (U s) ==> MEM x (U s1)` by metis_tac[] >>
  `!x. MEM x (U s1) ==> MEM x (U s2)` by metis_tac[] >>
  `ALL_DISTINCT (P b1) /\
   !x. MEM x (P b1) ==> MEM x (P h) \/ (MEM x (U s1) /\ ~MEM x (U s))`
    by (last_x_assum irule >> gvs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `ALL_DISTINCT (FLAT (MAP P bs2)) /\
   !x. MEM x (FLAT (MAP P bs2)) ==>
       MEM x (FLAT (MAP P bbs)) \/ (MEM x (U s2) /\ ~MEM x (U s1))`
    by (first_x_assum irule >> gvs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  qpat_x_assum `!x. MEM x (P b1) ==> _` mp_tac >>
  qpat_x_assum `!x. MEM x (FLAT (MAP P bs2)) ==> _` mp_tac >>
  qpat_x_assum `!x. MEM x (P h) \/ _ ==> _` mp_tac >>
  qpat_x_assum `ALL_DISTINCT (P h ++ _)` mp_tac >>
  rpt (qpat_x_assum `!s bb bb' s'. _` kall_tac) >>
  rpt (qpat_x_assum `!bbs s bbs' s'. _` kall_tac) >>
  simp[ALL_DISTINCT_APPEND] >> metis_tac[]
QED

(* ===== Outputs: SSA ===== *)

Theorem branch_opt_block_supply_outs[local]:
  branch_opt_block_supply dfg live_at s bb = (bb',s') /\
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
  (!x. MEM x (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) ==>
       MEM x s.irs_used_vars) ==>
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb'.bb_instructions)) /\
  (!x. MEM x (FLAT (MAP (\i. i.inst_outputs) bb'.bb_instructions)) ==>
       MEM x (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) \/
       (MEM x s'.irs_used_vars /\ ~MEM x s.irs_used_vars))
Proof
  strip_tac >> drule branch_opt_block_supply_cases >> strip_tac >> gvs[] >>
  drule fresh_ir_var_contract >> strip_tac >>
  gvs[fresh_inst_id_def, ALL_DISTINCT_APPEND] >>
  metis_tac[]
QED

Theorem fn_insts_blocks_outputs[local]:
  !bbs. FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs)) =
        FLAT (MAP (\bb. FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) bbs)
Proof
  Induct >> simp[fn_insts_blocks_def, MAP_APPEND, FLAT_APPEND]
QED

Theorem branch_opt_function_supply_ssa_form:
  !fn live_at s fn' s'.
    ssa_form fn /\ ir_supply_covers_fn s fn /\
    branch_opt_function_supply live_at s fn = (fn',s') ==>
    ssa_form fn'
Proof
  rpt strip_tac >>
  gvs[branch_opt_function_supply_def, AllCaseEqs()] >>
  Cases_on `branch_opt_blocks_supply (dfg_build_function fn) live_at s
              fn.fn_blocks` >>
  gvs[ssa_form_def, fn_insts_def, fn_insts_blocks_outputs] >>
  qspecl_then [`\bb. FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)`,
               `\s. s.irs_used_vars`, `K T`,
               `dfg_build_function fn`, `live_at`]
    mp_tac branch_opt_blocks_supply_distinct >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      metis_tac[branch_opt_block_supply_outs, branch_opt_block_supply_mono]) >>
  disch_then drule >> simp[] >> impl_tac
  >- (gvs[ir_supply_covers_fn_def, list_subset_def, EVERY_MEM, fn_ir_vars_def,
          block_ir_vars_def, inst_ir_vars_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
      metis_tac[MEM_APPEND]) >>
  simp[]
QED

(* ===== Instruction ids ===== *)

Theorem branch_opt_block_supply_ids[local]:
  branch_opt_block_supply dfg live_at s bb = (bb',s') /\
  ir_supply_inst_ok s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  (!x. MEM x (MAP (\i. i.inst_id) bb.bb_instructions) ==>
       MEM x s.irs_used_inst_ids) ==>
  ALL_DISTINCT (MAP (\i. i.inst_id) bb'.bb_instructions) /\
  (!x. MEM x (MAP (\i. i.inst_id) bb'.bb_instructions) ==>
       MEM x (MAP (\i. i.inst_id) bb.bb_instructions) \/
       (MEM x s'.irs_used_inst_ids /\ ~MEM x s.irs_used_inst_ids))
Proof
  strip_tac >> drule branch_opt_block_supply_cases >> strip_tac >> gvs[] >>
  drule fresh_ir_var_contract >> strip_tac >>
  `ir_supply_inst_ok s1` by gvs[ir_supply_inst_ok_def] >>
  drule_all fresh_inst_id_contract >> strip_tac >>
  gvs[ALL_DISTINCT_APPEND] >>
  metis_tac[]
QED

(* ===== Block shape ===== *)

Theorem bb_succs_snoc[local]:
  bb.bb_instructions = front ++ [t] ==>
  bb_succs bb = nub (REVERSE (get_successors t))
Proof
  strip_tac >> simp[bb_succs_def] >>
  Cases_on `front` >> simp[] >>
  `h::(t' ++ [t]) = SNOC t (h::t')` by simp[SNOC_APPEND] >>
  pop_assum SUBST1_TAC >> REWRITE_TAC[LAST_SNOC]
QED

Theorem bb_succs_with_snoc[local]:
  bb_succs (bb with bb_instructions := front ++ [t]) =
  nub (REVERSE (get_successors t))
Proof
  irule bb_succs_snoc >> qexists_tac `front` >> simp[]
QED

Theorem bb_succs_with_snoc2[local]:
  bb_succs (bb with bb_instructions := front ++ [a; t]) =
  nub (REVERSE (get_successors t))
Proof
  irule bb_succs_snoc >> qexists_tac `front ++ [a]` >> simp[]
QED

Theorem branch_opt_block_supply_succs[local]:
  (!v prev. dfg_get_def dfg v = SOME prev /\ prev.inst_opcode = ISZERO ==>
            ?op. prev.inst_operands = [op] /\ ~is_label_operand op) /\
  branch_opt_block_supply dfg live_at s bb = (bb',s') /\
  MEM l (bb_succs bb') ==> MEM l (bb_succs bb)
Proof
  strip_tac >> drule branch_opt_block_supply_cases >> strip_tac >> gvs[] >>
  qpat_x_assum `bb.bb_instructions = _` (assume_tac o MATCH_MP bb_succs_snoc) >>
  gvs[bb_succs_with_snoc, bb_succs_with_snoc2, get_successors_def,
      is_terminator_def, get_label_def] >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `op` >> gvs[is_label_operand_def, get_label_def]
QED

(* simp on bb_well_formed_def is slow, so these unfold it by rewriting
   and keep the arithmetic to decide_tac. *)
Theorem bb_well_formed_front[local]:
  bb_well_formed bb /\ bb.bb_instructions = front ++ [t] ==>
  (!i. i < LENGTH front ==> ~is_terminator (EL i front).inst_opcode) /\
  (!i j. i < j /\ j < LENGTH front /\ (EL j front).inst_opcode = PHI ==>
         (EL i front).inst_opcode = PHI)
Proof
  strip_tac >>
  qpat_x_assum `bb_well_formed bb`
    (STRIP_ASSUME_TAC o REWRITE_RULE[bb_well_formed_def]) >>
  qpat_x_assum `bb.bb_instructions = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  `LENGTH (front ++ [t]) = SUC (LENGTH front)` by
    simp_tac (srw_ss()) [arithmeticTheory.ADD1] >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th, prim_recTheory.PRE])) >>
  conj_tac >> rpt strip_tac
  >- (`i < SUC (LENGTH front)` by decide_tac >>
      `EL i (front ++ [t]) = EL i front` by metis_tac[EL_APPEND1] >>
      `i = LENGTH front` by metis_tac[] >>
      decide_tac) >>
  `i < LENGTH front /\ j < SUC (LENGTH front)` by decide_tac >>
  `EL i (front ++ [t]) = EL i front /\ EL j (front ++ [t]) = EL j front`
    by metis_tac[EL_APPEND1] >>
  metis_tac[]
QED

Theorem bb_well_formed_replace_last[local]:
  bb_well_formed bb /\ bb.bb_instructions = front ++ [t] /\
  is_terminator t'.inst_opcode /\ t'.inst_opcode <> PHI ==>
  bb_well_formed (bb with bb_instructions := front ++ [t'])
Proof
  strip_tac >>
  drule_all bb_well_formed_front >> strip_tac >>
  PURE_REWRITE_TAC[bb_well_formed_def] >>
  REWRITE_TAC[basic_block_accfupds, combinTheory.K_THM] >>
  `front ++ [t'] <> []` by simp_tac (srw_ss()) [] >>
  `LAST (front ++ [t']) = t'` by
    simp_tac (srw_ss()) [LAST_APPEND_CONS, LAST_CONS] >>
  `LENGTH (front ++ [t']) = SUC (LENGTH front)` by
    simp_tac (srw_ss()) [arithmeticTheory.ADD1] >>
  `EL (LENGTH front) (front ++ [t']) = t'` by
    simp_tac (srw_ss()) [EL_LENGTH_APPEND] >>
  ASM_REWRITE_TAC[prim_recTheory.PRE] >>
  conj_tac >> rpt strip_tac
  >- (Cases_on `i = LENGTH front` >- first_assum ACCEPT_TAC >>
      `i < LENGTH front` by decide_tac >>
      `EL i (front ++ [t']) = EL i front` by metis_tac[EL_APPEND1] >>
      metis_tac[]) >>
  Cases_on `j = LENGTH front` >- metis_tac[] >>
  `i < LENGTH front /\ j < LENGTH front` by decide_tac >>
  `EL i (front ++ [t']) = EL i front /\ EL j (front ++ [t']) = EL j front`
    by metis_tac[EL_APPEND1] >>
  metis_tac[]
QED

Theorem bb_well_formed_insert_before_last[local]:
  bb_well_formed bb /\ bb.bb_instructions = front ++ [t] /\
  ~is_terminator a.inst_opcode /\ a.inst_opcode <> PHI /\
  is_terminator t'.inst_opcode /\ t'.inst_opcode <> PHI ==>
  bb_well_formed (bb with bb_instructions := front ++ [a; t'])
Proof
  strip_tac >>
  drule_all bb_well_formed_front >> strip_tac >>
  PURE_REWRITE_TAC[bb_well_formed_def] >>
  REWRITE_TAC[basic_block_accfupds, combinTheory.K_THM] >>
  `front ++ [a; t'] <> []` by simp_tac (srw_ss()) [] >>
  `LAST (front ++ [a; t']) = t'` by
    simp_tac (srw_ss()) [LAST_APPEND_CONS, LAST_CONS] >>
  `LENGTH (front ++ [a; t']) = SUC (SUC (LENGTH front))` by
    (simp_tac (srw_ss()) [] >> decide_tac) >>
  `EL (LENGTH front) (front ++ [a; t']) = a` by
    simp_tac (srw_ss()) [EL_LENGTH_APPEND] >>
  `EL (SUC (LENGTH front)) (front ++ [a; t']) = t'` by
    simp_tac (srw_ss()) [EL_APPEND2, arithmeticTheory.ADD1] >>
  ASM_REWRITE_TAC[prim_recTheory.PRE] >>
  conj_tac >> rpt strip_tac
  >- (Cases_on `i = SUC (LENGTH front)` >- first_assum ACCEPT_TAC >>
      Cases_on `i = LENGTH front` >- metis_tac[] >>
      `i < LENGTH front` by decide_tac >>
      `EL i (front ++ [a; t']) = EL i front` by metis_tac[EL_APPEND1] >>
      metis_tac[]) >>
  Cases_on `j = SUC (LENGTH front)` >- metis_tac[] >>
  Cases_on `j = LENGTH front` >- metis_tac[] >>
  `i < LENGTH front /\ j < LENGTH front` by decide_tac >>
  `EL i (front ++ [a; t']) = EL i front /\ EL j (front ++ [a; t']) = EL j front`
    by metis_tac[EL_APPEND1] >>
  metis_tac[]
QED

Theorem branch_opt_block_supply_well_formed[local]:
  branch_opt_block_supply dfg live_at s bb = (bb',s') /\
  bb_well_formed bb ==> bb_well_formed bb'
Proof
  strip_tac >> drule branch_opt_block_supply_cases >> strip_tac >> gvs[] >>
  (irule bb_well_formed_replace_last ORELSE
   irule bb_well_formed_insert_before_last) >>
  simp[is_terminator_def] >> qexists_tac `t` >> simp[]
QED

(* ===== Block list ===== *)

Theorem branch_opt_blocks_supply_labels[local]:
  !bbs s bbs' s'.
    branch_opt_blocks_supply dfg live_at s bbs = (bbs',s') ==>
    MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs
Proof
  Induct >> simp[branch_opt_blocks_supply_def] >>
  rpt gen_tac >>
  Cases_on `branch_opt_block_supply dfg live_at s h` >>
  rename1 `_ = (b1,s1)` >>
  Cases_on `branch_opt_blocks_supply dfg live_at s1 bbs` >>
  simp[] >> strip_tac >> gvs[] >>
  metis_tac[branch_opt_block_supply_label]
QED

Theorem branch_opt_blocks_supply_mem[local]:
  !bbs s bbs' s'.
    branch_opt_blocks_supply dfg live_at s bbs = (bbs',s') /\ MEM bb' bbs' ==>
    ?bb s0 s1. MEM bb bbs /\ branch_opt_block_supply dfg live_at s0 bb = (bb',s1)
Proof
  Induct >> simp[branch_opt_blocks_supply_def] >>
  rpt gen_tac >>
  Cases_on `branch_opt_block_supply dfg live_at s h` >>
  rename1 `_ = (b1,s1)` >>
  Cases_on `branch_opt_blocks_supply dfg live_at s1 bbs` >>
  simp[] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem iszero_def_operand[local]:
  fn_inst_wf fn /\ EVERY label_positions_ok (fn_insts fn) ==>
  !v prev. dfg_get_def (dfg_build_function fn) v = SOME prev /\
           prev.inst_opcode = ISZERO ==>
           ?op. prev.inst_operands = [op] /\ ~is_label_operand op
Proof
  rpt strip_tac >>
  drule dfg_build_function_correct >> strip_tac >>
  `inst_wf prev` by
    (gvs[fn_inst_wf_def, fn_insts_def, MEM_fn_insts_blocks_iff] >>
     metis_tac[]) >>
  `label_positions_ok prev` by gvs[EVERY_MEM] >>
  gvs[inst_wf_def, LENGTH_EQ_NUM_compute, label_positions_ok_def]
QED

Theorem fn_ir_inst_ids_flat[local]:
  fn_ir_inst_ids fn =
  FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) fn.fn_blocks)
Proof
  simp[fn_ir_inst_ids_def, block_ir_inst_ids_def] >>
  AP_TERM_TAC >> simp[MAP_EQ_f, block_ir_inst_ids_def]
QED

Theorem branch_opt_function_supply_wf:
  !fn live_at s fn' s'.
    wf_function fn /\ fn_inst_wf fn /\ EVERY label_positions_ok (fn_insts fn) /\
    ir_supply_inst_ok s /\ ir_supply_covers_fn s fn /\
    branch_opt_function_supply live_at s fn = (fn',s') ==>
    wf_function fn'
Proof
  rpt strip_tac >>
  gvs[branch_opt_function_supply_def] >>
  Cases_on `branch_opt_blocks_supply (dfg_build_function fn) live_at s
              fn.fn_blocks` >>
  rename1 `_ = (bbs',s1)` >> gvs[] >>
  drule branch_opt_blocks_supply_labels >> strip_tac >>
  mp_tac iszero_def_operand >> impl_tac >- simp[] >>
  strip_tac >>
  gvs[wf_function_def, fn_labels_def, fn_has_entry_def] >>
  rpt conj_tac
  >- (strip_tac >> gvs[])
  >- (rpt strip_tac >>
      drule_all branch_opt_blocks_supply_mem >> strip_tac >>
      metis_tac[branch_opt_block_supply_well_formed])
  >- (gvs[fn_succs_closed_def, fn_labels_def] >> rpt strip_tac >>
      drule_all branch_opt_blocks_supply_mem >> strip_tac >>
      metis_tac[branch_opt_block_supply_succs])
  >> gvs[fn_inst_ids_distinct_def] >>
  qspecl_then [`\bb. MAP (\i. i.inst_id) bb.bb_instructions`,
               `\s. s.irs_used_inst_ids`, `ir_supply_inst_ok`,
               `dfg_build_function fn`, `live_at`]
    mp_tac branch_opt_blocks_supply_distinct >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      metis_tac[branch_opt_block_supply_ids, branch_opt_block_supply_mono]) >>
  disch_then drule >> simp[] >> impl_tac
  >- gvs[ir_supply_covers_fn_def, list_subset_def, EVERY_MEM, fn_ir_inst_ids_flat] >>
  simp[]
QED
