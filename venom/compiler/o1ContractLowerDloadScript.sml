(*
 * LowerDload against the O1 pass contract: the step part.
 *
 * The dispatched transform is lower_dload_function_supply, which draws its
 * new variables and instruction ids from the IR supply.  The step part of
 * the contract asks that one run keeps the O1 function shape, takes fresh
 * ids, and maps no labels.  The run's input supply must be well formed
 * (ir_supply_inst_ok: every used id is below the next one) and cover the
 * observed unit; the schedule runner establishes both at its start and
 * every step's checks keep them, but fn_pass_step does not say so yet, so
 * they are hypotheses here.
 *
 * TOP-LEVEL:
 *   lower_dload_function_supply_wf_function  - well-formedness kept
 *   lower_dload_function_supply_ssa_form     - SSA kept
 *   lower_dload_step_shape                   - the step part of the contract
 *)
Theory o1ContractLowerDload
Ancestors
  o1PassContract lowerDloadDefs lowerDloadSupplyProofs venomPassDispatcher venomFnScheduleRunner
  unitShapeDefs venomWf irSupply venomInst stackPlanTypes list rich_list
  contextCodegenRel stackPlanGen

(* Why these hold: the expansion of DLOAD/DLOADBYTES only inserts
   non-terminators (ALLOCA, ADD, CODECOPY, MLOAD) in place of a
   non-terminator, so block labels, terminators and successors are
   unchanged; the new ids come from fresh_inst_id, which under
   ir_supply_inst_ok returns ids above every used id, hence outside the
   function's ids when the supply covers it; the new variables come from
   fresh_ir_var, which avoids irs_used_vars.  The only label operand added
   is "code_end" as ADD's second operand, which label_positions_ok admits
   and which is reserved. *)

Theorem lower_dload_inst_supply_nonempty:
  lower_dload_inst_supply s i = (xs,t) ==> xs <> []
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      strip_tac >> gvs[]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      strip_tac >> gvs[]) >>
  rw[lower_dload_inst_supply_def] >> gvs[]
QED

Theorem lower_dload_inst_supply_special:
  ~MEM i.inst_opcode [DLOAD; DLOADBYTES] ==>
  lower_dload_inst_supply s i = ([i],s)
Proof
  simp[lower_dload_inst_supply_def]
QED

Theorem lower_dload_inst_supply_control:
  lower_dload_inst_supply s i = (xs,t) /\ MEM j xs /\
  (is_terminator j.inst_opcode \/ j.inst_opcode = PHI \/
   MEM j.inst_opcode [GAS; RETPC_PARAM; ASSIGN; PARAM; INVOKE; RET; STOP; RETURN]) ==>
  j = i
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[is_terminator_def]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[is_terminator_def]) >>
  rw[lower_dload_inst_supply_def] >> gvs[]
QED

Theorem lower_dload_inst_supply_wf:
  lower_dload_inst_supply s i = (xs,t) /\ inst_wf i ==>
  EVERY inst_wf xs
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[inst_wf_def]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[inst_wf_def]) >>
  rw[lower_dload_inst_supply_def] >> gvs[]
QED

Theorem lower_dload_inst_supply_shape:
  lower_dload_inst_supply s i = (xs,t) /\ inst_shape_ok i ==>
  EVERY inst_shape_ok xs
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >>
      gvs[inst_shape_ok_def, label_positions_ok_def, is_read0_opcode_def,
          is_label_operand_def]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >>
      gvs[inst_shape_ok_def, label_positions_ok_def, is_read0_opcode_def,
          is_label_operand_def]) >>
  rw[lower_dload_inst_supply_def] >> gvs[]
QED

Theorem lower_dload_inst_supply_operand_provenance:
  lower_dload_inst_supply s i = (xs,t) /\ MEM j xs /\
  MEM op j.inst_operands ==>
  MEM op i.inst_operands \/
  (?v. op = Var v /\ MEM v (FLAT (MAP (\k. k.inst_outputs) xs))) \/
  op = Label "code_end" \/ op = Lit 32w
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >> metis_tac[]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >> metis_tac[]) >>
  rw[lower_dload_inst_supply_def] >> gvs[]
QED

Theorem lower_dload_inst_supply_vars:
  lower_dload_inst_supply s i = (xs,t) /\
  EVERY (\v. MEM v s.irs_used_vars) i.inst_outputs /\
  ALL_DISTINCT i.inst_outputs ==>
  ALL_DISTINCT (FLAT (MAP (\k. k.inst_outputs) xs)) /\
  EVERY (\v. MEM v t.irs_used_vars) (FLAT (MAP (\k. k.inst_outputs) xs)) /\
  (!v. MEM v s.irs_used_vars ==> MEM v t.irs_used_vars) /\
  (!v. MEM v (FLAT (MAP (\k. k.inst_outputs) xs)) /\
       MEM v s.irs_used_vars ==> MEM v i.inst_outputs)
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> imp_res_tac fresh_ir_var_contract >> gvs[] >>
      metis_tac[]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> imp_res_tac fresh_ir_var_contract >> gvs[] >>
      metis_tac[]) >>
  rw[lower_dload_inst_supply_def] >> gvs[]
QED

Theorem lower_dload_insts_supply_vars:
  !s xs t.
  lower_dload_insts_supply s ins = (xs,t) /\
  EVERY (\v. MEM v s.irs_used_vars) (FLAT (MAP (\k. k.inst_outputs) ins)) /\
  ALL_DISTINCT (FLAT (MAP (\k. k.inst_outputs) ins)) ==>
  ALL_DISTINCT (FLAT (MAP (\k. k.inst_outputs) xs)) /\
  EVERY (\v. MEM v t.irs_used_vars) (FLAT (MAP (\k. k.inst_outputs) xs)) /\
  (!v. MEM v s.irs_used_vars ==> MEM v t.irs_used_vars) /\
  (!v. MEM v (FLAT (MAP (\k. k.inst_outputs) xs)) /\
       MEM v s.irs_used_vars ==>
       MEM v (FLAT (MAP (\k. k.inst_outputs) ins)))
Proof
  Induct_on `ins`
  >- simp[lower_dload_insts_supply_def] >>
  rpt gen_tac >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >>
  strip_tac >>
  gvs[ALL_DISTINCT_APPEND] >>
  drule_all lower_dload_inst_supply_vars >> strip_tac >>
  `EVERY (\v. MEM v s1.irs_used_vars)
     (FLAT (MAP (\k. k.inst_outputs) ins))` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  first_x_assum drule_all >> strip_tac >>
  simp[MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND, EVERY_APPEND] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem lower_dload_blocks_supply_vars:
  !s bs t.
  lower_dload_blocks_supply s bbs = (bs,t) /\
  EVERY (\v. MEM v s.irs_used_vars)
    (FLAT (MAP (\b. FLAT (MAP (\k. k.inst_outputs) b.bb_instructions)) bbs)) /\
  ALL_DISTINCT
    (FLAT (MAP (\b. FLAT (MAP (\k. k.inst_outputs) b.bb_instructions)) bbs)) ==>
  ALL_DISTINCT (FLAT (MAP (\b. FLAT (MAP (\k. k.inst_outputs) b.bb_instructions)) bs)) /\
  EVERY (\v. MEM v t.irs_used_vars)
    (FLAT (MAP (\b. FLAT (MAP (\k. k.inst_outputs) b.bb_instructions)) bs)) /\
  (!v. MEM v s.irs_used_vars ==> MEM v t.irs_used_vars) /\
  (!v. MEM v (FLAT (MAP (\b. FLAT (MAP (\k. k.inst_outputs) b.bb_instructions)) bs)) /\
       MEM v s.irs_used_vars ==>
       MEM v (FLAT (MAP (\b. FLAT (MAP (\k. k.inst_outputs) b.bb_instructions)) bbs)))
Proof
  Induct_on `bbs`
  >- simp[lower_dload_blocks_supply_def] >>
  rpt gen_tac >>
  simp[Once lower_dload_blocks_supply_def, lower_dload_block_supply_def,
       AllCaseEqs()] >> strip_tac >>
  gvs[ALL_DISTINCT_APPEND] >>
  drule_all lower_dload_insts_supply_vars >> strip_tac >>
  `EVERY (\v. MEM v s1.irs_used_vars)
    (FLAT (MAP (\b. FLAT (MAP (\k. k.inst_outputs) b.bb_instructions)) bbs))` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  first_x_assum drule_all >> strip_tac >>
  simp[ALL_DISTINCT_APPEND, EVERY_APPEND] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem lower_dload_outputs_blocks[local]:
  FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bs)) =
  FLAT (MAP (\b. FLAT (MAP (\i. i.inst_outputs) b.bb_instructions)) bs)
Proof
  Induct_on `bs` >> simp[fn_insts_blocks_def, MAP_APPEND, FLAT_APPEND]
QED

Theorem lower_dload_function_supply_outputs:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts f))) ==>
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts g)))
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs(), fn_insts_def,
       lower_dload_outputs_blocks] >> strip_tac >> gvs[] >>
  irule (cj 1 lower_dload_blocks_supply_vars) >>
  qexistsl [`f.fn_blocks`,`s`,`t`] >> simp[] >>
  rw[EVERY_MEM, MEM_FLAT, MEM_MAP] >>
  gvs[ir_supply_covers_fn_def, list_subset_def, EVERY_MEM] >>
  first_x_assum irule >>
  simp[fn_ir_vars_def, block_ir_vars_def, MEM_FLAT, MEM_MAP,
       PULL_EXISTS, inst_ir_vars_def] >>
  gvs[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem lower_dload_function_supply_distinct_ids:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_inst_ok s /\
  ir_supply_covers_fn s f /\ ALL_DISTINCT (fn_ir_inst_ids f) ==>
  ALL_DISTINCT (fn_ir_inst_ids g)
Proof
  strip_tac >>
  `EVERY (\id. MEM id s.irs_used_inst_ids) (fn_ir_inst_ids f)` by
    gvs[ir_supply_covers_fn_def, list_subset_def] >>
  drule_all lower_dload_function_supply_contract >>
  simp[ld_ids_supply_ok_def]
QED

Theorem lower_dload_insts_supply_member:
  !s xs t j. lower_dload_insts_supply s ins = (xs,t) /\ MEM j xs ==>
  ?i u ys v. MEM i ins /\ lower_dload_inst_supply u i = (ys,v) /\ MEM j ys /\
    EVERY (\k. MEM k xs) ys
Proof
  Induct_on `ins`
  >- simp[lower_dload_insts_supply_def] >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem lower_dload_blocks_supply_member:
  !s bs t b j. lower_dload_blocks_supply s bbs = (bs,t) /\
  MEM b bs /\ MEM j b.bb_instructions ==>
  ?a i u ys v. MEM a bbs /\ MEM i a.bb_instructions /\
    lower_dload_inst_supply u i = (ys,v) /\ MEM j ys /\
    EVERY (\k. ?c. MEM c bs /\ MEM k c.bb_instructions) ys
Proof
  Induct_on `bbs`
  >- simp[lower_dload_blocks_supply_def] >>
  simp[Once lower_dload_blocks_supply_def, lower_dload_block_supply_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[EVERY_MEM]
  >- (drule_all lower_dload_insts_supply_member >> strip_tac >>
      qexistsl [`h`,`i`,`u`,`ys`,`v`] >> simp[] >> rpt strip_tac >>
      qexists `h with bb_instructions := insts` >> gvs[EVERY_MEM]) >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl [`a`,`i`,`u`,`ys`,`v`] >> simp[] >> metis_tac[]
QED

Theorem lower_dload_insts_blocks_member[local]:
  MEM j (fn_insts_blocks bs) <=> ?b. MEM b bs /\ MEM j b.bb_instructions
Proof
  Induct_on `bs` >> simp[fn_insts_blocks_def] >> metis_tac[]
QED

Theorem lower_dload_function_supply_member:
  lower_dload_function_supply s f = (g,t) /\ MEM j (fn_insts g) ==>
  ?i u ys v. MEM i (fn_insts f) /\
    lower_dload_inst_supply u i = (ys,v) /\ MEM j ys /\
    EVERY (\k. MEM k (fn_insts g)) ys
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs()] >>
  strip_tac >> gvs[fn_insts_def, lower_dload_insts_blocks_member] >>
  drule_all lower_dload_blocks_supply_member >>
  simp[EVERY_MEM, fn_insts_def, lower_dload_insts_blocks_member] >> metis_tac[]
QED

Theorem lower_dload_function_supply_every:
  (!u i ys v. lower_dload_inst_supply u i = (ys,v) /\ P i ==> EVERY P ys) /\
  lower_dload_function_supply s f = (g,t) /\ EVERY P (fn_insts f) ==>
  EVERY P (fn_insts g)
Proof
  simp[EVERY_MEM] >> rpt strip_tac >>
  drule_all lower_dload_function_supply_member >> strip_tac >>
  metis_tac[]
QED

Theorem lower_dload_function_supply_control:
  lower_dload_function_supply s f = (g,t) /\ MEM j (fn_insts g) /\
  (is_terminator j.inst_opcode \/ j.inst_opcode = PHI \/
   MEM j.inst_opcode [GAS; RETPC_PARAM; ASSIGN; PARAM; INVOKE; RET; STOP; RETURN]) ==>
  MEM j (fn_insts f)
Proof
  strip_tac >> drule_all lower_dload_function_supply_member >> strip_tac >>
  metis_tac[lower_dload_inst_supply_control]
QED

Theorem lower_dload_blocks_supply_labels:
  !s bs t. lower_dload_blocks_supply s bbs = (bs,t) ==>
  MAP (\b. b.bb_label) bs = MAP (\b. b.bb_label) bbs
Proof
  Induct_on `bbs`
  >- simp[lower_dload_blocks_supply_def] >>
  simp[Once lower_dload_blocks_supply_def, lower_dload_block_supply_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem lower_dload_function_supply_labels:
  lower_dload_function_supply s f = (g,t) ==>
  fn_labels g = fn_labels f /\ g.fn_name = f.fn_name /\
  fn_entry_label g = fn_entry_label f /\ (fn_has_entry g <=> fn_has_entry f)
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule lower_dload_blocks_supply_labels >>
  simp[fn_labels_def, fn_entry_label_def, entry_block_def, fn_has_entry_def] >>
  Cases_on `bbs` >> Cases_on `f.fn_blocks` >> simp[]
QED

Theorem lower_dload_inst_supply_last_successors:
  lower_dload_inst_supply s i = (xs,t) ==>
  get_successors (LAST xs) = get_successors i
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      strip_tac >> gvs[get_successors_def, is_terminator_def]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      strip_tac >> gvs[get_successors_def, is_terminator_def]) >>
  rw[lower_dload_inst_supply_def] >> gvs[]
QED

Theorem lower_dload_insts_supply_last_successors:
  !s xs t. lower_dload_insts_supply s ins = (xs,t) ==>
  (xs = [] <=> ins = []) /\
  (ins <> [] ==> get_successors (LAST xs) = get_successors (LAST ins))
Proof
  Induct_on `ins`
  >- simp[lower_dload_insts_supply_def] >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >>
  rpt strip_tac >>
  drule_all lower_dload_inst_supply_nonempty >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  Cases_on `ins = []` >> gvs[LAST_APPEND_NOT_NIL, LAST_DEF] >>
  metis_tac[lower_dload_inst_supply_last_successors]
QED

Theorem lower_dload_block_supply_structure:
  lower_dload_block_supply s b = (c,t) ==>
  c.bb_label = b.bb_label /\ bb_succs c = bb_succs b
Proof
  simp[lower_dload_block_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule lower_dload_insts_supply_last_successors >>
  simp[bb_succs_def] >> strip_tac >>
  Cases_on `b.bb_instructions` >> Cases_on `insts` >> gvs[]
QED

Theorem lower_dload_blocks_supply_cfg:
  !s bs t. lower_dload_blocks_supply s bbs = (bs,t) ==>
  MAP (\b. (b.bb_label, bb_succs b)) bs =
  MAP (\b. (b.bb_label, bb_succs b)) bbs
Proof
  Induct_on `bbs`
  >- simp[lower_dload_blocks_supply_def] >>
  simp[Once lower_dload_blocks_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule lower_dload_block_supply_structure >> strip_tac >> simp[] >>
  metis_tac[]
QED

Theorem lower_dload_function_supply_succs_closed:
  lower_dload_function_supply s f = (g,t) /\ fn_succs_closed f ==>
  fn_succs_closed g
Proof
  strip_tac >>
  drule lower_dload_function_supply_labels >> strip_tac >>
  gvs[lower_dload_function_supply_def, AllCaseEqs()] >>
  drule lower_dload_blocks_supply_cfg >> strip_tac >>
  rw[fn_succs_closed_def] >>
  `MEM (bb.bb_label, bb_succs bb)
    (MAP (\b. (b.bb_label, bb_succs b)) f.fn_blocks)` by
    (first_x_assum (SUBST1_TAC o GSYM) >> simp[MEM_MAP] >> metis_tac[]) >>
  gvs[MEM_MAP, fn_succs_closed_def] >> metis_tac[]
QED

Theorem lower_dload_prefix_cons[local]:
  (!i j. i < j /\ j < LENGTH (h::xs) /\ P (EL j (h::xs)) ==>
         P (EL i (h::xs))) <=>
  ((!i j. i < j /\ j < LENGTH xs /\ P (EL j xs) ==> P (EL i xs)) /\
   ((?x. MEM x xs /\ P x) ==> P h))
Proof
  simp[MEM_EL, PULL_EXISTS] >> eq_tac
  >- (rpt strip_tac
      >- (first_x_assum (qspecl_then [`SUC i`,`SUC j`] mp_tac) >> simp[])
      >> first_x_assum (qspecl_then [`0`,`SUC n`] mp_tac) >> simp[]) >>
  strip_tac >> Cases_on `i` >> Cases_on `j` >> simp[] >> metis_tac[]
QED

Theorem lower_dload_insts_supply_every:
  (!u i ys v. lower_dload_inst_supply u i = (ys,v) /\ P i ==> EVERY P ys) /\
  lower_dload_insts_supply s ins = (xs,t) /\ EVERY P ins ==> EVERY P xs
Proof
  simp[EVERY_MEM] >> rpt strip_tac >>
  drule_all lower_dload_insts_supply_member >> strip_tac >> metis_tac[]
QED

Theorem lower_dload_inst_supply_noncontrol:
  lower_dload_inst_supply s i = (xs,t) /\
  ~is_terminator i.inst_opcode /\ i.inst_opcode <> PHI ==>
  EVERY (\j. ~is_terminator j.inst_opcode /\ j.inst_opcode <> PHI) xs
Proof
  rw[EVERY_MEM] >> metis_tac[lower_dload_inst_supply_control]
QED

Theorem lower_dload_insts_supply_phi_prefix:
  !s xs t. lower_dload_insts_supply s ins = (xs,t) /\
  (!i j. i < j /\ j < LENGTH ins /\ (EL j ins).inst_opcode = PHI ==>
         (EL i ins).inst_opcode = PHI) ==>
  (!i j. i < j /\ j < LENGTH xs /\ (EL j xs).inst_opcode = PHI ==>
         (EL i xs).inst_opcode = PHI)
Proof
  Induct_on `ins`
  >- simp[lower_dload_insts_supply_def] >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs(), lower_dload_prefix_cons] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (`lower_dload_inst_supply s h = ([h],s)` by
        (irule lower_dload_inst_supply_special >> simp[]) >>
      gvs[] >>
      first_x_assum (qspecl_then [`s`,`outs`,`t`] mp_tac) >>
      simp[] >> strip_tac >>
      Cases_on `i` >> Cases_on `j` >> simp[GSYM arithmeticTheory.ADD1] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> PHI) ins` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> PHI) (out ++ outs)` by
    (simp[EVERY_APPEND] >> conj_tac
     >- (rw[EVERY_MEM] >> metis_tac[lower_dload_inst_supply_control]) >>
     irule lower_dload_insts_supply_every >> conj_tac
     >- (rw[EVERY_MEM] >> metis_tac[lower_dload_inst_supply_control]) >>
     qexistsl [`ins`,`s1`,`t`] >> simp[]) >>
  gvs[] >> rpt strip_tac >>
  `MEM (EL j (out ++ outs)) (out ++ outs)` by
    (irule EL_MEM >> simp[]) >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem lower_dload_terminal_cons[local]:
  (Q (LAST (h::xs)) /\
   (!i. i < LENGTH (h::xs) /\ Q (EL i (h::xs)) ==>
        i = PRE (LENGTH (h::xs)))) <=>
  if xs = [] then Q h else
    ~Q h /\ Q (LAST xs) /\
    (!i. i < LENGTH xs /\ Q (EL i xs) ==> i = PRE (LENGTH xs))
Proof
  Cases_on `xs = []` >- gvs[] >>
  simp[LAST_DEF] >> eq_tac
  >- (strip_tac >> conj_tac
      >- (strip_tac >> first_x_assum (qspec_then `0` mp_tac) >>
          Cases_on `xs` >> gvs[]) >>
      simp[] >> rpt strip_tac >>
      first_x_assum (qspec_then `SUC i` mp_tac) >>
      Cases_on `xs` >> gvs[]) >>
  strip_tac >> simp[] >> Cases >> simp[] >>
  Cases_on `xs` >> gvs[]
QED

Theorem lower_dload_terminal_decomp[local]:
  (xs <> [] /\ Q (LAST xs) /\
   (!i. i < LENGTH xs /\ Q (EL i xs) ==> i = PRE (LENGTH xs))) <=>
  ?pre z. xs = pre ++ [z] /\ EVERY (\x. ~Q x) pre /\ Q z
Proof
  Induct_on `xs`
  >- simp[] >>
  gen_tac >>
  pure_rewrite_tac[NOT_CONS_NIL, boolTheory.NOT_CLAUSES,
                   boolTheory.AND_CLAUSES, lower_dload_terminal_cons] >>
  Cases_on `xs = []`
  >- gvs[] >>
  simp[] >> eq_tac
  >- (strip_tac >>
      `?pre z. xs = pre ++ [z] /\ EVERY (\x. ~Q x) pre /\ Q z` by
        metis_tac[] >>
      qexistsl [`h::pre`,`z`] >> simp[]) >>
  strip_tac >> Cases_on `pre` >> gvs[] >> metis_tac[]
QED

Theorem lower_dload_insts_supply_append:
  !s xs t. lower_dload_insts_supply s (as ++ bs) = (xs,t) ==>
  ?ys u zs. lower_dload_insts_supply s as = (ys,u) /\
    lower_dload_insts_supply u bs = (zs,t) /\ xs = ys ++ zs
Proof
  Induct_on `as`
  >- (simp[lower_dload_insts_supply_def] >> metis_tac[]) >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  simp[Once lower_dload_insts_supply_def] >> metis_tac[APPEND_ASSOC]
QED

Theorem lower_dload_insts_supply_terminal:
  lower_dload_insts_supply s ins = (xs,t) /\ ins <> [] /\
  is_terminator (LAST ins).inst_opcode /\
  (!i. i < LENGTH ins /\ is_terminator (EL i ins).inst_opcode ==>
       i = PRE (LENGTH ins)) ==>
  xs <> [] /\ is_terminator (LAST xs).inst_opcode /\
  (!i. i < LENGTH xs /\ is_terminator (EL i xs).inst_opcode ==>
       i = PRE (LENGTH xs))
Proof
  strip_tac >>
  `?pre z. ins = pre ++ [z] /\
    EVERY (\i. ~is_terminator i.inst_opcode) pre /\
    is_terminator z.inst_opcode` by
    (ho_match_mp_tac (iffLR lower_dload_terminal_decomp) >> simp[]) >>
  gvs[] >> drule lower_dload_insts_supply_append >> strip_tac >>
  `lower_dload_inst_supply u z = ([z],u)` by
    (irule lower_dload_inst_supply_special >>
     Cases_on `z.inst_opcode` >> gvs[is_terminator_def]) >>
  gvs[lower_dload_insts_supply_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) ys` by
    (irule lower_dload_insts_supply_every >> conj_tac
     >- (rw[EVERY_MEM] >> metis_tac[lower_dload_inst_supply_control]) >>
     qexistsl [`pre`,`s`,`t`] >> simp[]) >>
  rpt strip_tac >> Cases_on `i < LENGTH ys`
  >- (`EL i (ys ++ [z]) = EL i ys` by (irule EL_APPEND1 >> simp[]) >>
      gvs[EVERY_EL]) >> decide_tac
QED

Theorem lower_dload_block_supply_well_formed:
  lower_dload_block_supply s b = (c,t) /\ bb_well_formed b ==>
  bb_well_formed c
Proof
  simp[lower_dload_block_supply_def, AllCaseEqs()] >> strip_tac >>
  gvs[bb_well_formed_def] >>
  drule_all lower_dload_insts_supply_terminal >> strip_tac >> simp[] >>
  metis_tac[lower_dload_insts_supply_phi_prefix]
QED

Theorem lower_dload_blocks_supply_every:
  (!u b c v. lower_dload_block_supply u b = (c,v) /\ P b ==> P c) ==>
  !bbs s bs t. lower_dload_blocks_supply s bbs = (bs,t) /\ EVERY P bbs ==>
    EVERY P bs
Proof
  strip_tac >> Induct_on `bbs`
  >- simp[lower_dload_blocks_supply_def] >>
  simp[Once lower_dload_blocks_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem lower_dload_function_supply_blocks_wf:
  lower_dload_function_supply s f = (g,t) /\ EVERY bb_well_formed f.fn_blocks ==>
  EVERY bb_well_formed g.fn_blocks
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  irule lower_dload_blocks_supply_every
  >- metis_tac[lower_dload_block_supply_well_formed] >>
  qexistsl [`f.fn_blocks`,`s`,`t`] >> simp[]
QED

Theorem lower_dload_function_supply_inst_wf:
  lower_dload_function_supply s f = (g,t) /\ fn_inst_wf f ==> fn_inst_wf g
Proof
  strip_tac >>
  `EVERY inst_wf (fn_insts f)` by
    gvs[fn_inst_wf_def, fn_insts_def, lower_dload_insts_blocks_member, EVERY_MEM] >>
  `EVERY inst_wf (fn_insts g)` by
    (irule lower_dload_function_supply_every >> conj_tac
     >- metis_tac[lower_dload_inst_supply_wf] >>
     qexistsl [`f`,`s`,`t`] >> simp[]) >>
  gvs[fn_inst_wf_def, fn_insts_def, lower_dload_insts_blocks_member, EVERY_MEM] >>
  metis_tac[]
QED

Theorem lower_dload_function_supply_no_returns:
  lower_dload_function_supply s f = (g,t) /\
  EVERY (\i. ~MEM i.inst_opcode ops) (fn_insts f) /\
  EVERY (\op. MEM op [RET; STOP; RETURN]) ops ==>
  EVERY (\i. ~MEM i.inst_opcode ops) (fn_insts g)
Proof
  simp[EVERY_MEM] >> rpt strip_tac >>
  rename1 `MEM j (fn_insts g)` >>
  drule_all lower_dload_function_supply_member >> strip_tac >>
  `j = i` by (irule lower_dload_inst_supply_control >> simp[] >> metis_tac[]) >>
  gvs[] >> metis_tac[]
QED

Theorem lower_dload_function_supply_entry_no_ret:
  lower_dload_function_supply s f = (g,t) /\ entry_fn_no_ret f ==>
  entry_fn_no_ret g
Proof
  strip_tac >>
  `EVERY (\i. ~MEM i.inst_opcode [RET]) (fn_insts f)` by
    gvs[entry_fn_no_ret_def, fn_insts_def, lower_dload_insts_blocks_member, EVERY_MEM] >>
  `EVERY (\i. ~MEM i.inst_opcode [RET]) (fn_insts g)` by
    (irule lower_dload_function_supply_no_returns >> simp[] >>
     qexistsl [`f`,`s`,`t`] >> gvs[]) >>
  gvs[entry_fn_no_ret_def, fn_insts_def, lower_dload_insts_blocks_member, EVERY_MEM] >>
  metis_tac[]
QED

Theorem lower_dload_function_supply_first_no_preds:
  lower_dload_function_supply s f = (g,t) /\ first_block_no_preds f ==>
  first_block_no_preds g
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule lower_dload_blocks_supply_cfg >> strip_tac >>
  drule lower_dload_blocks_supply_labels >> strip_tac >>
  Cases_on `f.fn_blocks = []`
  >- (Cases_on `bbs` >> gvs[first_block_no_preds_def]) >>
  `(HD bbs).bb_label = (HD f.fn_blocks).bb_label` by
    (Cases_on `f.fn_blocks` >> Cases_on `bbs` >> gvs[]) >>
  rw[first_block_no_preds_def, EVERY_MEM] >>
  `MEM (bb.bb_label, bb_succs bb)
       (MAP (\b. (b.bb_label, bb_succs b)) f.fn_blocks)` by
    (qpat_x_assum `MAP (\b. (b.bb_label, bb_succs b)) _ = _`
       (SUBST1_TAC o GSYM) >>
     simp[MEM_MAP] >> metis_tac[]) >>
  gvs[MEM_MAP, first_block_no_preds_def, EVERY_MEM] >> metis_tac[]
QED

Theorem lower_dload_inst_supply_hd_not_param:
  lower_dload_inst_supply s i = (xs,t) /\ ~is_param_opcode i.inst_opcode ==>
  ~is_param_opcode (HD xs).inst_opcode
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[is_param_opcode_def]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[is_param_opcode_def]) >>
  rw[lower_dload_inst_supply_def] >> gvs[]
QED

Theorem lower_dload_insts_supply_no_params:
  lower_dload_insts_supply s ins = (xs,t) /\ get_params ins = [] ==>
  get_params xs = []
Proof
  Cases_on `ins` >- simp[lower_dload_insts_supply_def, get_params_def] >>
  simp[lower_dload_insts_supply_def, AllCaseEqs(), get_params_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  drule_all lower_dload_inst_supply_hd_not_param >>
  drule lower_dload_inst_supply_nonempty >>
  Cases_on `out` >> gvs[get_params_def]
QED

Theorem lower_dload_function_supply_no_params:
  lower_dload_function_supply s f = (g,t) /\ f.fn_blocks <> [] /\
  get_params (HD f.fn_blocks).bb_instructions = [] ==>
  get_params (HD g.fn_blocks).bb_instructions = []
Proof
  Cases_on `f.fn_blocks` >>
  simp[lower_dload_function_supply_def, lower_dload_blocks_supply_def,
       lower_dload_block_supply_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  metis_tac[lower_dload_insts_supply_no_params]
QED

Theorem lower_dload_function_supply_operand_provenance:
  lower_dload_function_supply s f = (g,t) /\ MEM j (fn_insts g) /\
  MEM op j.inst_operands ==>
  (?i. MEM i (fn_insts f) /\ MEM op i.inst_operands) \/
  (?v. op = Var v /\ MEM v (FLAT (MAP (\k. k.inst_outputs) (fn_insts g)))) \/
  op = Label "code_end" \/ op = Lit 32w
Proof
  strip_tac >> drule_all lower_dload_function_supply_member >> strip_tac >>
  drule_all lower_dload_inst_supply_operand_provenance >>
  gvs[EVERY_MEM, MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem lower_dload_function_supply_copy_phi:
  !origin g x. copy_phi_var origin g x ==>
  !s f t. MEM origin [GAS; RETPC_PARAM] /\
    lower_dload_function_supply s f = (g,t) ==> copy_phi_var origin f x
Proof
  Induct_on `copy_phi_var` >> rpt strip_tac
  >- (`MEM inst (fn_insts f)` by
        (irule lower_dload_function_supply_control >> gvs[] >> metis_tac[]) >>
      metis_tac[copy_phi_var_rules])
  >- (`MEM inst (fn_insts f)` by
        (irule lower_dload_function_supply_control >> gvs[] >> metis_tac[]) >>
      metis_tac[copy_phi_var_rules]) >>
  `MEM inst (fn_insts f)` by
    (irule lower_dload_function_supply_control >> gvs[] >> metis_tac[]) >>
  metis_tac[copy_phi_var_rules]
QED

Theorem lower_dload_copy_phi_output:
  !origin f x. copy_phi_var origin f x ==>
  ?i. MEM i (fn_insts f) /\ MEM x i.inst_outputs
Proof
  Induct_on `copy_phi_var` >> metis_tac[]
QED

Theorem lower_dload_copy_phi_ir_var:
  copy_phi_var origin f x ==> MEM x (fn_ir_vars f)
Proof
  strip_tac >> drule lower_dload_copy_phi_output >> strip_tac >>
  gvs[fn_insts_def, lower_dload_insts_blocks_member] >>
  simp[fn_ir_vars_def, block_ir_vars_def, MEM_FLAT, MEM_MAP, PULL_EXISTS,
       inst_ir_vars_def] >> metis_tac[]
QED

Theorem lower_dload_inst_supply_reserved_operand:
  lower_dload_inst_supply s i = (xs,t) /\ MEM x s.irs_used_vars /\
  MEM j xs /\ MEM (Var x) j.inst_operands ==>
  MEM (Var x) i.inst_operands /\
  (~MEM i.inst_opcode [DLOAD; DLOADBYTES] ==> j = i)
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> imp_res_tac fresh_ir_var_contract >> gvs[] >> metis_tac[]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> imp_res_tac fresh_ir_var_contract >> gvs[] >> metis_tac[]) >>
  rw[lower_dload_inst_supply_def] >> gvs[]
QED

Theorem lower_dload_inst_supply_preserves_vars:
  lower_dload_inst_supply s i = (xs,t) ==>
  !x. MEM x s.irs_used_vars ==> MEM x t.irs_used_vars
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> imp_res_tac fresh_ir_var_contract >> gvs[] >> metis_tac[]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> imp_res_tac fresh_ir_var_contract >> gvs[] >> metis_tac[]) >>
  rw[lower_dload_inst_supply_def] >> gvs[]
QED

Theorem lower_dload_insts_supply_reserved_operand:
  !s xs t. lower_dload_insts_supply s ins = (xs,t) ==>
  (!x. MEM x s.irs_used_vars ==> MEM x t.irs_used_vars) /\
  (!x j. MEM x s.irs_used_vars /\ MEM j xs /\ MEM (Var x) j.inst_operands ==>
   ?i. MEM i ins /\ MEM (Var x) i.inst_operands /\
       (~MEM i.inst_opcode [DLOAD; DLOADBYTES] ==> j = i))
Proof
  Induct_on `ins`
  >- simp[lower_dload_insts_supply_def] >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule lower_dload_inst_supply_preserves_vars >> strip_tac >>
  first_x_assum drule >> strip_tac >> conj_tac
  >- metis_tac[] >> rpt strip_tac
  >- (drule_all lower_dload_inst_supply_reserved_operand >>
      strip_tac >> qexists `h` >> simp[]) >>
  metis_tac[]
QED

Theorem lower_dload_blocks_supply_reserved_operand:
  !s bs t. lower_dload_blocks_supply s bbs = (bs,t) ==>
  (!x. MEM x s.irs_used_vars ==> MEM x t.irs_used_vars) /\
  (!x b j. MEM x s.irs_used_vars /\ MEM b bs /\ MEM j b.bb_instructions /\
           MEM (Var x) j.inst_operands ==>
   ?a i. MEM a bbs /\ MEM i a.bb_instructions /\ MEM (Var x) i.inst_operands /\
       (~MEM i.inst_opcode [DLOAD; DLOADBYTES] ==> j = i))
Proof
  Induct_on `bbs`
  >- simp[lower_dload_blocks_supply_def] >>
  simp[Once lower_dload_blocks_supply_def, lower_dload_block_supply_def,
       AllCaseEqs()] >> rpt gen_tac >> strip_tac >> gvs[] >>
  drule lower_dload_insts_supply_reserved_operand >> strip_tac >>
  first_x_assum drule >> strip_tac >> conj_tac
  >- metis_tac[] >> rpt strip_tac
  >- (qexists `h` >> gvs[] >> metis_tac[]) >> metis_tac[]
QED

Theorem lower_dload_function_supply_reserved_operand:
  lower_dload_function_supply s f = (g,t) /\ MEM x s.irs_used_vars /\
  MEM j (fn_insts g) /\ MEM (Var x) j.inst_operands ==>
  ?i. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\
      (~MEM i.inst_opcode [DLOAD; DLOADBYTES] ==> j = i)
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs()] >> strip_tac >>
  gvs[fn_insts_def, lower_dload_insts_blocks_member] >>
  drule lower_dload_blocks_supply_reserved_operand >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem lower_dload_function_supply_opaque_use:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  opaque_use_ok f ==> opaque_use_ok g
Proof
  strip_tac >>
  `!x. gas_var g x ==> gas_var f x` by
    (simp[gas_var_def] >> rpt strip_tac >>
     drule lower_dload_function_supply_copy_phi >> simp[] >> metis_tac[]) >>
  `!x. retpc_var g x ==> retpc_var f x` by
    (simp[retpc_var_def] >> rpt strip_tac >>
     drule lower_dload_function_supply_copy_phi >> simp[] >> metis_tac[]) >>
  rw[opaque_use_ok_def] >>
  `MEM x s.irs_used_vars` by
    (gvs[ir_supply_covers_fn_def, list_subset_def, EVERY_MEM] >>
     metis_tac[lower_dload_copy_phi_ir_var, gas_var_def, retpc_var_def]) >>
  drule_all lower_dload_function_supply_reserved_operand >> strip_tac >>
  `gas_use_ok i x \/ retpc_use_ok i x` by
    metis_tac[opaque_use_ok_gas_use, opaque_use_ok_retpc_use] >>
  `~MEM i.inst_opcode [DLOAD; DLOADBYTES]` by
    gvs[gas_use_ok_def, retpc_use_ok_def] >>
  gvs[] >> metis_tac[opaque_use_ok_gas_use, opaque_use_ok_retpc_use]
QED

Theorem lower_dload_function_supply_fn_shape:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  fn_shape_ok f ==> fn_shape_ok g
Proof
  strip_tac >> drule lower_dload_function_supply_labels >> strip_tac >>
  gvs[fn_shape_ok_def] >> conj_tac
  >- metis_tac[lower_dload_function_supply_opaque_use] >> conj_tac
  >- (`EVERY (\l. ~reserved_label l) (fn_labels f)` by
        gvs[fn_labels_def, EVERY_MAP, combinTheory.o_DEF] >>
      `EVERY (\l. ~reserved_label l) (fn_labels g)` by gvs[] >>
      qpat_x_assum `fn_labels g = _` kall_tac >>
      gvs[fn_labels_def, EVERY_MAP, combinTheory.o_DEF]) >>
  irule lower_dload_function_supply_every >> conj_tac
  >- metis_tac[lower_dload_inst_supply_shape] >>
  qexistsl [`f`,`s`,`t`] >> simp[]
QED

Theorem lower_dload_function_supply_invoke_ok:
  lower_dload_function_supply s f = (g,t) /\ fn_invoke_ok names f ==>
  fn_invoke_ok names g
Proof
  rw[fn_invoke_ok_def] >>
  `MEM inst (fn_insts f)` by
    (irule lower_dload_function_supply_control >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem lower_dload_function_supply_label_refs:
  lower_dload_function_supply s f = (g,t) /\ fn_label_refs_ok f ==>
  fn_label_refs_ok g
Proof
  strip_tac >> drule lower_dload_function_supply_labels >> strip_tac >>
  rw[fn_label_refs_ok_def] >>
  drule_all lower_dload_function_supply_member >> strip_tac >>
  Cases_on `i.inst_opcode = INVOKE`
  >- (`lower_dload_inst_supply u i = ([i],u)` by
        (irule lower_dload_inst_supply_special >> simp[]) >> gvs[]) >>
  drule_all lower_dload_inst_supply_operand_provenance >>
  strip_tac
  >- metis_tac[fn_label_refs_ok_def] >>
  gvs[] >> simp[reserved_label_def]
QED

Theorem lower_dload_function_supply_wf_function:
  !s fn fn' s'.
    wf_function fn /\ ir_supply_inst_ok s /\ ir_supply_covers_fn s fn /\
    lower_dload_function_supply s fn = (fn',s') ==>
    wf_function fn'
Proof
  rpt strip_tac >>
  drule lower_dload_function_supply_labels >> strip_tac >>
  gvs[wf_function_def] >> rpt conj_tac
  >- metis_tac[SRULE [EVERY_MEM] lower_dload_function_supply_blocks_wf]
  >- metis_tac[lower_dload_function_supply_succs_closed] >>
  gvs[fn_inst_ids_distinct_def] >>
  irule (SRULE [fn_ir_inst_ids_def, lambdify block_ir_inst_ids_def]
               lower_dload_function_supply_distinct_ids) >>
  metis_tac[]
QED

Theorem lower_dload_function_supply_ssa_form:
  !s fn fn' s'.
    ssa_form fn /\ ir_supply_covers_fn s fn /\
    lower_dload_function_supply s fn = (fn',s') ==>
    ssa_form fn'
Proof
  simp[ssa_form_def] >> rpt strip_tac >>
  irule lower_dload_function_supply_outputs >> metis_tac[]
QED

Theorem lower_dload_function_supply_o1_shape:
  o1_fn_shape ctx f /\ ir_supply_inst_ok s /\ ir_supply_covers_fn s f /\
  lower_dload_function_supply s f = (g,t) ==> o1_fn_shape ctx g
Proof
  strip_tac >> drule lower_dload_function_supply_labels >> strip_tac >>
  gvs[o1_fn_shape_def] >> rpt conj_tac
  >- metis_tac[lower_dload_function_supply_wf_function]
  >- metis_tac[lower_dload_function_supply_inst_wf]
  >- metis_tac[lower_dload_function_supply_fn_shape]
  >- metis_tac[lower_dload_function_supply_first_no_preds]
  >- metis_tac[lower_dload_function_supply_invoke_ok]
  >- metis_tac[lower_dload_function_supply_label_refs]
  >- metis_tac[lower_dload_function_supply_entry_no_ret]
  >- (strip_tac >> irule lower_dload_function_supply_no_params >>
      qexistsl [`f`,`s`,`t`] >> gvs[wf_function_def]) >>
  strip_tac >> irule lower_dload_function_supply_no_returns >> simp[] >>
  qexistsl [`f`,`s`,`t`] >> metis_tac[]
QED

(* The step part of LowerDload's contract (o1_contract_lower_dload). *)
Theorem lower_dload_step_contract:
  o1_step_contract rpolicy (CFP_Simple VP_LowerDload)
Proof
  cheat
QED
