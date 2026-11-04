(*
 * SUE against the O1 pass contract: the step part.
 *
 * The dispatched transform is sue_expand_function_supply, which keeps every
 * block label and inserts ASSIGN copies whose outputs and instruction ids
 * come from the supply.  So one run keeps the O1 function shape, its new
 * ids are fresh against the supply it was given, its label map is empty,
 * the supply it returns still has its used ids below its next one, and it
 * adds no ALLOCA (o1_fn_row).
 *)
Theory o1ContractSueStep
Ancestors
  o1PassContract singleUseExpansionSupplyProofs singleUseExpansionSupplySim singleUseExpansionDefs
  venomPassDispatcher venomWf venomInst unitShapeDefs

Theorem sue_label_projection_nonlabels:
  MAP get_label xs = MAP get_label ys ==>
  (EVERY (\op. ~is_label_operand op) xs <=>
   EVERY (\op. ~is_label_operand op) ys)
Proof
  qid_spec_tac `ys` >> Induct_on `xs` >> Cases_on `ys` >>
  simp[] >> rpt gen_tac >> strip_tac >>
  rename1 `get_label a = get_label b` >>
  Cases_on `a` >> Cases_on `b` >>
  gvs[venomStateTheory.get_label_def, stackPlanTypesTheory.is_label_operand_def]
QED

Theorem sue_label_projection_mem:
  MAP get_label xs = MAP get_label ys ==>
  (MEM (Label l) xs <=> MEM (Label l) ys)
Proof
  qid_spec_tac `ys` >> Induct_on `xs` >> Cases_on `ys` >>
  simp[] >> rpt gen_tac >> strip_tac >>
  rename1 `get_label a = get_label b` >>
  Cases_on `a` >> Cases_on `b` >>
  gvs[venomStateTheory.get_label_def] >> metis_tac[]
QED

Theorem sue_label_projection_every:
  EVERY (\op. ~is_label_operand op) ops <=>
  EVERY (\a. a = NONE) (MAP get_label ops)
Proof
  Induct_on `ops` >> simp[] >> Cases_on `h` >>
  simp[venomStateTheory.get_label_def, stackPlanTypesTheory.is_label_operand_def]
QED


Theorem sue_label_positions_projection_nf:
  label_positions_ok inst <=>
  case (inst.inst_opcode, MAP get_label inst.inst_operands) of
    (JMP, [SOME l]) => T
  | (JNZ, [a; SOME t; SOME f]) => a = NONE /\ t <> f
  | (PHI, ops) => T
  | (INVOKE, SOME l :: args) => EVERY (\a. a = NONE) args
  | (ADD, [a; SOME l]) => l = "code_end" /\ a = NONE
  | (CODECOPY, [a; SOME l; b]) => l = "runtime_begin" /\ a = NONE /\ b = NONE
  | (_, ops) => EVERY (\a. a = NONE) ops
Proof
  Cases_on `inst.inst_opcode` >>
  pure_rewrite_tac [label_positions_ok_def] >>
  pure_asm_rewrite_tac [] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``EVERY``, ``MAP``]) >>
  simp[GSYM sue_label_projection_every] >>
  namedCases_on `inst.inst_operands` ["", "a xs"] >>
  gvs[] >>
  Cases_on `a` >>
  gvs[venomStateTheory.get_label_def, stackPlanTypesTheory.is_label_operand_def] >>
  namedCases_on `xs` ["", "b ys"] >>
  gvs[] >>
  Cases_on `b` >>
  gvs[venomStateTheory.get_label_def, stackPlanTypesTheory.is_label_operand_def,
      GSYM sue_label_projection_every] >>
  namedCases_on `ys` ["", "operand3 zs"] >> gvs[] >>
  Cases_on `operand3` >>
  gvs[venomStateTheory.get_label_def, stackPlanTypesTheory.is_label_operand_def,
      GSYM sue_label_projection_every]
QED

Theorem sue_label_positions_projection:
  MAP get_label xs = MAP get_label inst.inst_operands ==>
  (label_positions_ok (inst with inst_operands := xs) <=> label_positions_ok inst)
Proof
  strip_tac >> rewrite_tac [sue_label_positions_projection_nf] >>
  simp[]
QED

Theorem sue_inst_shape_projection:
  inst_shape_ok inst /\
  MAP get_label xs = MAP get_label inst.inst_operands /\
  (inst.inst_opcode = PHI ==> xs = inst.inst_operands) ==>
  inst_shape_ok (inst with inst_operands := xs)
Proof
  strip_tac >>
  `LENGTH xs = LENGTH inst.inst_operands` by
    metis_tac[listTheory.LENGTH_MAP] >>
  drule sue_label_positions_projection >> strip_tac >>
  gvs[inst_shape_ok_def] >> metis_tac[listTheory.LENGTH_NIL]
QED

Theorem sue_assign_inst_shape:
  ~is_label_operand op ==>
  inst_shape_ok (instruction iid ASSIGN [op] [v])
Proof
  Cases_on `op` >> EVAL_TAC
QED

Theorem sue_expand_inst_supply_inst_shape:
  inst_shape_ok inst /\
  sue_expand_inst_supply dfg s inst = (out,s') ==>
  EVERY inst_shape_ok out
Proof
  strip_tac >> Cases_on `sue_should_skip inst.inst_opcode`
  >- gvs[sue_expand_inst_supply_def] >>
  Cases_on `sue_expand_ops_supply dfg inst s inst.inst_operands 0` >>
  PairCases_on `r` >> gvs[sue_expand_inst_supply_def] >>
  drule sue_expand_ops_supply_copies >> strip_tac >>
  drule sue_expand_ops_supply_operand_labels >> strip_tac >>
  simp[] >> conj_tac
  >- (gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
      first_x_assum drule >> strip_tac >> gvs[] >>
      Cases_on `e` >> gvs[] >>
      irule sue_assign_inst_shape >>
      simp[stackPlanTypesTheory.is_label_operand_def]) >>
  irule sue_inst_shape_projection >> simp[] >>
  gvs[sue_operand_label_get_label, sue_should_skip_def]
QED

Theorem sue_expand_insts_supply_inst_shape:
  !insts s outs s'.
  EVERY inst_shape_ok insts /\
  sue_expand_insts_supply dfg s insts = (outs,s') ==>
  EVERY inst_shape_ok outs
Proof
  Induct_on `insts` >> rpt strip_tac
  >- gvs[sue_expand_insts_supply_def] >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  Cases_on `sue_expand_insts_supply dfg r insts` >>
  gvs[sue_expand_insts_supply_def] >>
  metis_tac[sue_expand_inst_supply_inst_shape]
QED

Theorem sue_expand_block_supply_inst_shape:
  EVERY inst_shape_ok bb.bb_instructions /\
  sue_expand_block_supply dfg s bb = (bb',s') ==>
  EVERY inst_shape_ok bb'.bb_instructions
Proof
  strip_tac >> Cases_on `sue_expand_insts_supply dfg s bb.bb_instructions` >>
  gvs[sue_expand_block_supply_def] >>
  metis_tac[sue_expand_insts_supply_inst_shape]
QED

Theorem sue_expand_blocks_supply_inst_shape:
  !bbs s bbs' s'.
  EVERY (\bb. EVERY inst_shape_ok bb.bb_instructions) bbs /\
  sue_expand_blocks_supply dfg s bbs = (bbs',s') ==>
  EVERY (\bb. EVERY inst_shape_ok bb.bb_instructions) bbs'
Proof
  Induct_on `bbs` >> rpt strip_tac
  >- gvs[sue_expand_blocks_supply_def] >>
  Cases_on `sue_expand_block_supply dfg s h` >>
  Cases_on `sue_expand_blocks_supply dfg r bbs` >>
  gvs[sue_expand_blocks_supply_def] >>
  metis_tac[sue_expand_block_supply_inst_shape]
QED

Theorem sue_expand_function_supply_inst_shape:
  EVERY inst_shape_ok (fn_insts fn) /\
  sue_expand_function_supply s fn = (fn',s') ==>
  EVERY inst_shape_ok (fn_insts fn')
Proof
  strip_tac >>
  Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
  gvs[sue_expand_function_supply_def, fn_insts_def, fn_insts_blocks_def,
      ctxLookupAgreeHelpersTheory.fn_insts_EVERY_block] >>
  drule_all sue_expand_blocks_supply_inst_shape >> simp[]
QED

Theorem sue_label_projection_head:
  MAP get_label xs = SOME l :: rest ==>
  ?tail. xs = Label l :: tail
Proof
  Cases_on `xs` >> simp[] >> Cases_on `h` >>
  simp[venomStateTheory.get_label_def]
QED

Theorem sue_supply_fn_invoke_ok:
  ir_supply_inst_ok s /\ ir_supply_covers_fn s fn /\
  fn_invoke_ok names fn /\
  sue_expand_function_supply s fn = (fn',s') ==>
  fn_invoke_ok names fn'
Proof
  strip_tac >>
  drule_at (Pat `sue_expand_function_supply _ _ = _`)
    sue_expand_function_supply_label_projection >> simp[] >>
  strip_tac >> simp[fn_invoke_ok_def] >> rpt strip_tac >>
  qpat_x_assum `!j. MEM j (fn_insts fn') ==> _` drule >>
  strip_tac >> gvs[] >>
  `?lbl rest. i.inst_operands = Label lbl :: rest /\ MEM lbl names` by
    metis_tac[fn_invoke_ok_def] >>
  gvs[venomStateTheory.get_label_def] >>
  drule sue_label_projection_head >> strip_tac >> simp[]
QED

Theorem sue_supply_fn_label_refs_ok:
  ir_supply_inst_ok s /\ ir_supply_covers_fn s fn /\
  fn_label_refs_ok fn /\
  sue_expand_function_supply s fn = (fn',s') ==>
  fn_label_refs_ok fn'
Proof
  strip_tac >>
  drule_at (Pat `sue_expand_function_supply _ _ = _`)
    sue_expand_function_supply_label_projection >> simp[] >>
  strip_tac >>
  `fn_labels fn' = fn_labels fn` by
    (Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
     gvs[sue_expand_function_supply_def, fn_labels_def] >>
     metis_tac[sue_expand_blocks_supply_labels]) >>
  simp[fn_label_refs_ok_def] >> rpt strip_tac >>
  qpat_x_assum `!j. MEM j (fn_insts fn') ==> _` drule >> strip_tac
  >- gvs[venomStateTheory.get_label_def] >>
  drule sue_label_projection_mem >> disch_then (qspec_then `l` mp_tac) >>
  gvs[fn_label_refs_ok_def] >> metis_tac[]
QED

Theorem sue_supply_first_block_no_preds:
  fn_has_entry fn /\ first_block_no_preds fn /\
  sue_expand_function_supply s fn = (fn',s') ==>
  first_block_no_preds fn'
Proof
  strip_tac >>
  Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
  gvs[sue_expand_function_supply_def] >>
  `fn.fn_blocks <> []` by gvs[fn_has_entry_def] >>
  drule_all sue_expand_blocks_supply_head >> strip_tac >>
  drule sue_expand_block_supply_label >> strip_tac >>
  simp[first_block_no_preds_def, listTheory.EVERY_MEM] >> rpt strip_tac >>
  drule_all sue_expand_blocks_supply_member >> strip_tac >>
  drule sue_expand_block_supply_bb_succs >> strip_tac >>
  gvs[first_block_no_preds_def, listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem sue_supply_first_block_no_phi:
  fn_has_entry fn /\ first_block_no_phi fn /\
  sue_expand_function_supply s fn = (fn',s') ==>
  first_block_no_phi fn'
Proof
  strip_tac >>
  Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
  gvs[sue_expand_function_supply_def] >>
  `fn.fn_blocks <> []` by gvs[fn_has_entry_def] >>
  drule_all sue_expand_blocks_supply_head >> strip_tac >>
  simp[first_block_no_phi_def] >>
  drule_at (Pat `sue_expand_block_supply _ _ _ = _`)
    sue_expand_block_supply_opcodes >>
  disch_then (qspec_then `\op. op <> PHI` mp_tac) >>
  gvs[first_block_no_phi_def]
QED

Theorem sue_supply_entry_fn_no_return:
  entry_fn_no_return fn /\ sue_expand_function_supply s fn = (fn',s') ==>
  entry_fn_no_return fn'
Proof
  strip_tac >>
  drule_at (Pat `sue_expand_function_supply _ _ = _`)
    sue_expand_function_supply_opcodes >>
  disch_then (qspec_then `\op. ~MEM op [RET; RETFMP; DRET]` mp_tac) >>
  gvs[entry_fn_no_return_def]
QED

Theorem sue_supply_entry_fn_no_params:
  entry_fn_no_params fn /\ sue_expand_function_supply s fn = (fn',s') ==>
  entry_fn_no_params fn'
Proof
  strip_tac >>
  drule_at (Pat `sue_expand_function_supply _ _ = _`)
    sue_expand_function_supply_opcodes >>
  disch_then (qspec_then `\op. ~is_param_opcode op` mp_tac) >>
  gvs[entry_fn_no_params_def, is_param_opcode_def]
QED

Theorem sue_map_unique_head:
  MAP f xs = y::rest /\ f x = y /\ MEM x xs /\ ~MEM y rest ==>
  ?tail. xs = x::tail /\ ~MEM x tail
Proof
  Cases_on `xs` >> simp[] >> rpt strip_tac >> gvs[] >>
  gvs[listTheory.MEM_MAP] >> metis_tac[]
QED

Theorem sue_map_unique_last:
  MAP f xs = front ++ [y] /\ f x = y /\ MEM x xs /\ ~MEM y front ==>
  ?prefix. xs = prefix ++ [x] /\ ~MEM x prefix
Proof
  strip_tac >>
  `MAP f (REVERSE xs) = y::REVERSE front` by
    metis_tac[listTheory.MAP_REVERSE, listTheory.REVERSE_APPEND,
              listTheory.REVERSE_DEF, listTheory.APPEND] >>
  `?tail. REVERSE xs = x::tail /\ ~MEM x tail` by
    (irule sue_map_unique_head >> simp[] >>
     qexistsl_tac [`f`, `REVERSE front`] >> simp[]) >>
  qexists_tac `REVERSE tail` >>
  metis_tac[listTheory.REVERSE_REVERSE, listTheory.REVERSE_DEF,
            listTheory.MEM_REVERSE]
QED

Theorem sue_projection_gas_use:
  j.inst_opcode = i.inst_opcode /\
  MAP (\op. case op of Var w => project w | other => other)
    j.inst_operands = i.inst_operands /\
  project x = Var y /\ MEM (Var x) j.inst_operands /\ gas_use_ok i y ==>
  gas_use_ok j x
Proof
  simp[gas_use_ok_def] >> rpt strip_tac >> gvs[] >>
  drule sue_map_unique_head >> simp[] >>
  disch_then drule_all >> strip_tac >> metis_tac[]
QED

Theorem sue_projection_retpc_use:
  j.inst_opcode = i.inst_opcode /\
  MAP (\op. case op of Var w => project w | other => other)
    j.inst_operands = i.inst_operands /\
  project x = Var y /\ MEM (Var x) j.inst_operands /\ retpc_use_ok i y ==>
  retpc_use_ok j x
Proof
  simp[retpc_use_ok_def] >> rpt strip_tac >> gvs[] >>
  drule sue_map_unique_last >> simp[] >>
  disch_then drule_all >> strip_tac >> metis_tac[]
QED

Theorem sue_projection_copy_phi_var:
  !origin target x. copy_phi_var origin target x ==>
  !source project.
    origin <> ASSIGN /\
    (!j. MEM j (fn_insts target) ==>
      (j.inst_opcode = ASSIGN /\ ?v. j.inst_outputs = [v] /\
        MAP (\op. case op of Var w => project w | other => other)
          j.inst_operands = [project v]) \/
      (?i. MEM i (fn_insts source) /\ j.inst_opcode = i.inst_opcode /\
        j.inst_outputs = i.inst_outputs /\
        (!v. MEM v i.inst_outputs ==> project v = Var v) /\
        MAP (\op. case op of Var w => project w | other => other)
          j.inst_operands = i.inst_operands)) ==>
    ?y. project x = Var y /\ copy_phi_var origin source y
Proof
  Induct_on `copy_phi_var` >> rpt strip_tac
  >- (qpat_x_assum `!j. MEM j (fn_insts target) ==> _` drule >>
      strip_tac >> gvs[] >> metis_tac[copy_phi_var_rules])
  >- (qpat_x_assum `!source project. _` drule_all >> strip_tac >>
      qpat_x_assum `!j. MEM j (fn_insts target) ==> _` drule >>
      strip_tac >> gvs[] >> metis_tac[copy_phi_var_rules]) >>
  qpat_x_assum `!source project. _` drule_all >> strip_tac >>
  qpat_x_assum `!j. MEM j (fn_insts target) ==> _` drule >>
  strip_tac >> gvs[] >>
  `MEM (Var y) i.inst_operands` by
    (qpat_x_assum `MAP _ _ = _` (SUBST1_TAC o SYM) >>
     simp[listTheory.MEM_MAP] >> qexists_tac `Var x'` >> simp[]) >>
  metis_tac[copy_phi_var_rules]
QED

Theorem sue_projection_opaque_use_ok:
  (!j. MEM j (fn_insts target) ==>
    (j.inst_opcode = ASSIGN /\ ?v. j.inst_outputs = [v] /\
      MAP (\op. case op of Var w => project w | other => other)
        j.inst_operands = [project v]) \/
    (?i. MEM i (fn_insts source) /\ j.inst_opcode = i.inst_opcode /\
      j.inst_outputs = i.inst_outputs /\
      (!v. MEM v i.inst_outputs ==> project v = Var v) /\
      MAP (\op. case op of Var w => project w | other => other)
        j.inst_operands = i.inst_operands)) /\ opaque_use_ok source ==>
  opaque_use_ok target
Proof
  strip_tac >>
  `!x. gas_var target x ==> ?y. project x = Var y /\ gas_var source y` by
    (simp[gas_var_def] >> rpt strip_tac >>
     drule sue_projection_copy_phi_var >>
     disch_then (qspecl_then [`source`, `project`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  `!x. retpc_var target x ==> ?y. project x = Var y /\ retpc_var source y` by
    (simp[retpc_var_def] >> rpt strip_tac >>
     drule sue_projection_copy_phi_var >>
     disch_then (qspecl_then [`source`, `project`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  simp[opaque_use_ok_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!j. MEM j (fn_insts target) ==> _` drule >> strip_tac
  >- simp[gas_use_ok_def, retpc_use_ok_def] >>
  `!z y. MEM (Var z) inst.inst_operands /\ project z = Var y ==>
    MEM (Var y) i.inst_operands` by
    (rpt strip_tac >> qpat_x_assum `MAP _ _ = _` (SUBST1_TAC o SYM) >>
     simp[listTheory.MEM_MAP] >> qexists_tac `Var z` >> simp[]) >>
  conj_tac
  >- metis_tac[sue_projection_gas_use, opaque_use_ok_gas_use] >>
  metis_tac[sue_projection_retpc_use, opaque_use_ok_retpc_use]
QED


Theorem sue_supply_opaque_use_ok:
  ir_supply_inst_ok s /\ ir_supply_covers_fn s fn /\ opaque_use_ok fn /\
  sue_expand_function_supply s fn = (fn',s') ==> opaque_use_ok fn'
Proof
  strip_tac >> drule_all sue_expand_function_supply_projection >> strip_tac >>
  irule sue_projection_opaque_use_ok >> goal_assum (drule_at Any) >> simp[]
QED

Theorem sue_label_projection_single_label:
  MAP get_label xs = [SOME l] <=> xs = [Label l]
Proof
  Cases_on `xs` >> simp[] >> Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[venomStateTheory.get_label_def, EQ_SYM_EQ]
QED

Theorem sue_expand_blocks_supply_revert_path:
  !n bbs s bbs' s' l.
  sue_expand_blocks_supply dfg s bbs = (bbs',s') /\
  revert_path bbs n l ==> revert_path bbs' n l
Proof
  Induct_on `n` >- simp[revert_path_def] >>
  rpt gen_tac >> simp[revert_path_def] >>
  strip_tac >> gnvs[listTheory.EXISTS_MEM] >>
  qpat_x_assum `?bb. _` (qx_choose_then `bb`
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  drule_all sue_expand_blocks_supply_member_forward >> strip_tac >>
  drule sue_expand_block_supply_label >> strip_tac >>
  drule_all sue_expand_block_supply_last >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE) bb'.bb_instructions` by
    (drule_at (Pat `sue_expand_block_supply _ _ _ = _`)
       sue_expand_block_supply_opcodes >>
     disch_then (qspec_then `\opc. opc <> INVOKE` mp_tac) >> simp[]) >>
  simp[listTheory.EXISTS_MEM] >> qexists_tac `bb'` >> simp[] >>
  Cases_on `(LAST bb.bb_instructions).inst_opcode = REVERT`
  >- gvs[] >>
  gvs[] >>
  Cases_on `(LAST bb.bb_instructions).inst_operands` >> gvs[] >>
  Cases_on `h` >> gvs[] >> Cases_on `t` >> gvs[] >>
  Cases_on `x0` >> gvs[venomStateTheory.get_label_def] >> metis_tac[]
QED

Theorem sue_flag_fails_mono[local]:
  (!v. MEM v vs ==> MEM v ws) /\ flag_fails bbs vs inst ==>
  flag_fails bbs ws inst
Proof
  rpt strip_tac >> Cases_on `inst.inst_opcode` >> gvs[flag_fails_def]
  >- (Cases_on `inst.inst_operands` >> gvs[] >>
      Cases_on `h` >> gvs[] >> Cases_on `t` >> gvs[] >>
      Cases_on `h` >> gvs[] >> Cases_on `t'` >> gvs[] >>
      Cases_on `h` >> gvs[] >> Cases_on `t` >> gvs[] >> metis_tac[]) >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `h` >> gvs[] >> Cases_on `t` >> gvs[] >> metis_tac[]
QED

Theorem sue_flag_path_mono[local]:
  !insts bbs vs ws.
  (!v. MEM v vs ==> MEM v ws) /\ flag_path bbs vs insts ==>
  flag_path bbs ws insts
Proof
  Induct >- simp[flag_path_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `flag_path _ _ _` mp_tac >> simp[flag_path_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
  disch_then DISJ_CASES_TAC
  >- metis_tac[sue_flag_fails_mono] >>
  simp[] >> disj2_tac >> first_x_assum irule >>
  goal_assum (drule_at Any) >>
  Cases_on `write_effects h.inst_opcode = empty_effects` >> simp[] >>
  Cases_on `h.inst_opcode` >> simp[listTheory.MEM_FILTER] >>
  Cases_on `h.inst_operands` >> simp[listTheory.MEM_FILTER] >>
  Cases_on `h'` >> simp[listTheory.MEM_FILTER] >>
  Cases_on `t` >> simp[listTheory.MEM_FILTER] >>
  Cases_on `MEM s vs` >> Cases_on `MEM s ws` >>
  gvs[listTheory.MEM_FILTER] >> metis_tac[]
QED

Theorem sue_copy_prefix_flags[local]:
  !assigns vs tail.
  EVERY (\a. a.inst_opcode = ASSIGN /\
    ?op v. a.inst_operands = [op] /\ a.inst_outputs = [v]) assigns /\
  ALL_DISTINCT (FLAT (MAP (\a. a.inst_outputs) assigns)) /\
  (!v. MEM v (FLAT (MAP (\a. a.inst_outputs) assigns)) ==> ~MEM v vs) /\
  flag_path bbs
    (FLAT (MAP (\a. a.inst_outputs)
      (FILTER (\a. ?u. a.inst_operands = [Var u] /\ MEM u vs) assigns)) ++ vs) tail ==>
  flag_path bbs vs (assigns ++ tail)
Proof
  Induct_on `assigns` >> rpt gen_tac
  >- simp[] >>
  strip_tac >>
  gvs[listTheory.ALL_DISTINCT_APPEND] >>
  `FILTER (\x. x <> v) vs = vs` by
    (simp[listTheory.FILTER_EQ_ID, listTheory.EVERY_MEM] >> metis_tac[]) >>
  simp[Once flag_path_def, venomEffectsTheory.write_effects_def] >>
  disj2_tac >> Cases_on `op` >> gvs[] >>
  Cases_on `MEM s vs` >> gvs[] >>
  first_x_assum irule >> conj_tac >- (simp[] >> metis_tac[]) >>
  irule sue_flag_path_mono >> goal_assum (drule_at Any) >>
  simp[listTheory.MEM_FLAT, listTheory.MEM_MAP,
       listTheory.MEM_FILTER] >> metis_tac[]
QED

Theorem sue_expand_ops_supply_flags:
  ir_supply_inst_ok s /\
  sue_expand_ops_supply dfg inst s ops k = (assigns,new_ops,s') /\
  EVERY (\v. MEM v s.irs_used_vars) vs /\
  (!v. MEM v vs ==> MEM v ws) ==>
  ?zs. zs = FLAT (MAP (\a. a.inst_outputs)
          (FILTER (\a. ?u. a.inst_operands = [Var u] /\ MEM u vs) assigns)) ++ vs /\
    (!v. MEM v vs ==> MEM v zs) /\
    LIST_REL (\op op'. !v. op = Var v /\ MEM v vs ==>
      ?w. op' = Var w /\ MEM w zs) ops new_ops /\
    (!tail. flag_path bbs zs tail ==> flag_path bbs ws (assigns ++ tail))
Proof
  strip_tac >> drule_all sue_expand_ops_supply_prefix >> strip_tac >>
  drule sue_expand_ops_supply_copies >> strip_tac >>
  drule sue_expand_ops_supply_provenance >> strip_tac >>
  qabbrev_tac `endpoint = FLAT (MAP (\a. a.inst_outputs)
    (FILTER (\a. ?u. a.inst_operands = [Var u] /\ MEM u vs) assigns)) ++ vs` >>
  qexists_tac `endpoint` >> simp[] >>
  conj_tac >- simp[Abbr `endpoint`] >>
  conj_tac
  >- (irule listTheory.LIST_REL_mono >> goal_assum (drule_at Any) >>
      rpt strip_tac >> gvs[] >>
      simp[Abbr `endpoint`, listTheory.MEM_FLAT, listTheory.MEM_MAP,
           listTheory.MEM_FILTER] >> metis_tac[listTheory.MEM]) >>
  rpt strip_tac >> irule sue_flag_path_mono >>
  qexists_tac `vs` >> simp[] >>
  irule sue_copy_prefix_flags >>
  gvs[Abbr `endpoint`, listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem sue_flag_fails_transport[local]:
  LENGTH bbs = LENGTH bbs' /\
  (!n l. revert_path bbs n l ==> revert_path bbs' n l) /\
  MAP get_label ops = MAP get_label inst.inst_operands /\
  LIST_REL (\op op'. !v. op = Var v /\ MEM v vs ==>
    ?w. op' = Var w /\ MEM w zs) inst.inst_operands ops /\
  flag_fails bbs vs inst ==>
  flag_fails bbs' zs (inst with inst_operands := ops)
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >> gvs[flag_fails_def]
  >- (Cases_on `inst.inst_operands` >> gvs[] >>
      Cases_on `h` >> gvs[] >> Cases_on `t` >> gvs[] >>
      Cases_on `op'` >> gvs[venomStateTheory.get_label_def] >> metis_tac[])
  >- (Cases_on `inst.inst_operands` >> gvs[] >>
      Cases_on `h` >> gvs[] >> Cases_on `t` >> gvs[] >>
      Cases_on `h` >> gvs[] >> Cases_on `t'` >> gvs[] >>
      Cases_on `h` >> gvs[] >> Cases_on `t` >> gvs[] >>
      Cases_on `op''` >> gvs[venomStateTheory.get_label_def] >>
      rename1 `get_label failop = SOME _` >>
      Cases_on `failop` >> gvs[venomStateTheory.get_label_def] >> metis_tac[]) >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `h` >> gvs[] >> Cases_on `t` >> gvs[]
QED

Theorem sue_flag_instruction_transport[local]:
  LENGTH bbs = LENGTH bbs' /\
  (!n l. revert_path bbs n l ==> revert_path bbs' n l) /\
  MAP get_label ops = MAP get_label inst.inst_operands /\
  LIST_REL (\op op'. !v. op = Var v /\ MEM v vs ==>
    ?w. op' = Var w /\ MEM w zs) inst.inst_operands ops /\
  (!v. MEM v vs ==> MEM v zs) /\
  (!xs ys. (!v. MEM v xs ==> MEM v (inst.inst_outputs ++ vs)) /\
    (!v. MEM v xs ==> MEM v ys) /\ flag_path bbs xs tail ==>
    flag_path bbs' ys tail') /\
  flag_path bbs vs (inst :: tail) ==>
  flag_path bbs' zs ((inst with inst_operands := ops) :: tail')
Proof
  strip_tac >>
  qpat_x_assum `flag_path bbs vs _` mp_tac >>
  simp[Once flag_path_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
  simp[Once flag_path_def] >> disch_then DISJ_CASES_TAC
  >- (disj1_tac >> irule sue_flag_fails_transport >> metis_tac[]) >>
  disj2_tac >> first_x_assum irule >>
  goal_assum (drule_at Any) >>
  qpat_x_assum `flag_path _ _ _` kall_tac >>
  Cases_on `write_effects inst.inst_opcode = empty_effects`
  >- (simp[] >> Cases_on `inst.inst_opcode = ASSIGN`
      >- (gvs[] >> Cases_on `inst.inst_operands`
          >- (gvs[listTheory.MEM_FILTER] >> metis_tac[]) >>
          Cases_on `t`
          >- (Cases_on `h` >> gvs[listTheory.MEM_FILTER] >>
              Cases_on `x0` >> gvs[listTheory.MEM_FILTER] >>
              rpt IF_CASES_TAC >> simp[listTheory.MEM_FILTER] >> metis_tac[]) >>
          gvs[] >> Cases_on `h` >> Cases_on `op'` >>
          gvs[listTheory.MEM_FILTER] >> metis_tac[]) >>
      Cases_on `inst.inst_opcode` >> gvs[listTheory.MEM_FILTER] >> metis_tac[]) >>
  simp[]
QED

Theorem sue_expand_inst_supply_flags:
  ir_supply_inst_ok s /\
  sue_expand_inst_supply dfg s inst = (out,s') /\
  EVERY (\v. MEM v s.irs_used_vars) (inst.inst_outputs ++ vs) /\
  (!v. MEM v vs ==> MEM v ws) /\
  LENGTH bbs = LENGTH bbs' /\
  (!n l. revert_path bbs n l ==> revert_path bbs' n l) /\
  (!xs ys. ir_supply_inst_ok s' /\
    EVERY (\v. MEM v s'.irs_used_vars) xs /\
    (!v. MEM v xs ==> MEM v ys) /\ flag_path bbs xs tail ==>
    flag_path bbs' ys tail') /\
  flag_path bbs vs (inst :: tail) ==>
  flag_path bbs' ws (out ++ tail')
Proof
  strip_tac >>
  drule_all sue_expand_inst_supply_extends >> strip_tac >>
  `ir_supply_inst_ok s' /\
   (!v. MEM v s.irs_used_vars ==> MEM v s'.irs_used_vars)` by
    gvs[sue_supply_extends_def] >>
  Cases_on `sue_should_skip inst.inst_opcode`
  >- (gvs[sue_expand_inst_supply_def] >>
      irule (SRULE [] (Q.INST [`ops` |-> `inst.inst_operands`]
        sue_flag_instruction_transport)) >>
      goal_assum (drule_at Any) >> simp[listTheory.LIST_REL_refl] >>
      rpt strip_tac >> first_x_assum irule >>
      goal_assum (drule_at Any) >>
      gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  Cases_on `sue_expand_ops_supply dfg inst s inst.inst_operands 0` >>
  PairCases_on `r` >> gvs[sue_expand_inst_supply_def] >>
  drule_all sue_expand_ops_supply_flags >>
  disch_then (qspec_then `bbs'` strip_assume_tac) >>
  drule sue_expand_ops_supply_operand_labels >> strip_tac >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  first_x_assum irule >>
  irule sue_flag_instruction_transport >>
  conj_tac >- gvs[sue_operand_label_get_label] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >> first_x_assum irule >>
  goal_assum (drule_at Any) >>
  gvs[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem sue_expand_insts_supply_flags:
  !insts s out s' vs ws.
  ir_supply_inst_ok s /\
  sue_expand_insts_supply dfg s insts = (out,s') /\
  EVERY (\i. EVERY (\v. MEM v s.irs_used_vars) i.inst_outputs) insts /\
  EVERY (\v. MEM v s.irs_used_vars) vs /\
  (!v. MEM v vs ==> MEM v ws) /\
  LENGTH bbs = LENGTH bbs' /\
  (!n l. revert_path bbs n l ==> revert_path bbs' n l) /\
  flag_path bbs vs insts ==>
  flag_path bbs' ws out
Proof
  Induct >- simp[flag_path_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  rename1 `sue_expand_inst_supply dfg s h = (head,s1)` >>
  Cases_on `sue_expand_insts_supply dfg s1 insts` >>
  gvs[sue_expand_insts_supply_def] >>
  drule_all sue_expand_inst_supply_extends >> strip_tac >>
  drule sue_supply_extends_members >> strip_tac >>
  irule sue_expand_inst_supply_flags >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >> first_x_assum irule >>
  goal_assum (drule_at Any) >>
  gvs[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem sue_calls_flagged_prefix[local]:
  !pre tail. EVERY (\i. i.inst_opcode <> CALL /\
    i.inst_opcode <> STATICCALL) pre /\ calls_flagged bbs tail ==>
  calls_flagged bbs (pre ++ tail)
Proof
  Induct >> simp[calls_flagged_def]
QED

Theorem sue_expand_insts_supply_calls_flagged:
  !insts s out s'.
  ir_supply_inst_ok s /\
  sue_expand_insts_supply dfg s insts = (out,s') /\
  EVERY (\i. EVERY (\v. MEM v s.irs_used_vars) i.inst_outputs) insts /\
  LENGTH bbs = LENGTH bbs' /\
  (!n l. revert_path bbs n l ==> revert_path bbs' n l) /\
  calls_flagged bbs insts ==>
  calls_flagged bbs' out
Proof
  Induct >- simp[sue_expand_insts_supply_def, calls_flagged_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  rename1 `sue_expand_inst_supply dfg s h = (head,s1)` >>
  Cases_on `sue_expand_insts_supply dfg s1 insts` >>
  rename1 `sue_expand_insts_supply dfg s1 insts = (rest,s2)` >>
  gvs[sue_expand_insts_supply_def, calls_flagged_def] >>
  drule_all sue_expand_inst_supply_extends >> strip_tac >>
  drule sue_supply_extends_members >> strip_tac >>
  `ir_supply_inst_ok s1` by gvs[sue_supply_extends_def] >>
  `calls_flagged bbs' rest` by
    (first_x_assum irule >> goal_assum (drule_at Any) >>
     gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `!ops. calls_flagged bbs' ((h with inst_operands := ops) :: rest)` by
    (gen_tac >> simp[calls_flagged_def] >> strip_tac >>
     Cases_on `h.inst_outputs` >> gvs[] >> Cases_on `t` >> gvs[] >>
     irule sue_expand_insts_supply_flags >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  Cases_on `sue_should_skip h.inst_opcode`
  >- (gvs[sue_expand_inst_supply_def] >>
      first_x_assum (qspec_then `h.inst_operands` mp_tac) >> simp[]) >>
  Cases_on `sue_expand_ops_supply dfg h s h.inst_operands 0` >>
  PairCases_on `r` >> gvs[sue_expand_inst_supply_def] >>
  drule sue_expand_ops_supply_copies >> strip_tac >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  irule sue_calls_flagged_prefix >> simp[] >>
  gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[]
QED

Theorem sue_expand_blocks_supply_calls_flagged:
  !blocks s blocks' s'.
  ir_supply_inst_ok s /\
  sue_expand_blocks_supply dfg s blocks = (blocks',s') /\
  EVERY (\bb. EVERY (\i. EVERY (\v. MEM v s.irs_used_vars)
    i.inst_outputs) bb.bb_instructions) blocks /\
  EVERY (\bb. calls_flagged bbs bb.bb_instructions) blocks /\
  LENGTH bbs = LENGTH bbs' /\
  (!n l. revert_path bbs n l ==> revert_path bbs' n l) ==>
  EVERY (\bb. calls_flagged bbs' bb.bb_instructions) blocks'
Proof
  Induct >- simp[sue_expand_blocks_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `sue_expand_block_supply dfg s h` >>
  rename1 `sue_expand_block_supply dfg s h = (bb,s1)` >>
  Cases_on `sue_expand_blocks_supply dfg s1 blocks` >>
  gvs[sue_expand_blocks_supply_def] >>
  drule_all sue_expand_block_supply_extends >> strip_tac >>
  drule sue_supply_extends_members >> strip_tac >>
  `ir_supply_inst_ok s1` by gvs[sue_supply_extends_def] >>
  conj_tac
  >- (qpat_x_assum `sue_expand_block_supply _ _ _ = _` mp_tac >>
      simp[sue_expand_block_supply_def, AllCaseEqs()] >> strip_tac >>
      gvs[] >> irule sue_expand_insts_supply_calls_flagged >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  gvs[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem sue_supply_call_checks_ok:
  ir_supply_inst_ok s /\ ir_supply_covers_fn s fn /\ call_checks_ok fn /\
  sue_expand_function_supply s fn = (fn',s') ==> call_checks_ok fn'
Proof
  strip_tac >>
  Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
  gvs[sue_expand_function_supply_def] >>
  drule sue_expand_blocks_supply_labels >> strip_tac >>
  `LENGTH q = LENGTH fn.fn_blocks` by metis_tac[listTheory.LENGTH_MAP] >>
  simp[call_checks_ok_def] >>
  irule sue_expand_blocks_supply_calls_flagged >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `fn.fn_blocks` >>
  simp[GSYM call_checks_ok_def] >> reverse conj_tac
  >- (gvs[venomFnScheduleRunnerTheory.ir_supply_covers_fn_def,
          venomFnScheduleRunnerTheory.list_subset_def,
          irSupplyTheory.fn_ir_vars_def,
          lambdify irSupplyTheory.block_ir_vars_def,
          lambdify irSupplyTheory.inst_ir_vars_def, listTheory.EVERY_MEM,
          listTheory.MEM_FLAT, listTheory.MEM_MAP, PULL_EXISTS] >>
      metis_tac[]) >>
  metis_tac[sue_expand_blocks_supply_revert_path]
QED

Theorem sue_supply_fn_shape_ok:
  ir_supply_inst_ok s /\ ir_supply_covers_fn s fn /\ fn_shape_ok fn /\
  sue_expand_function_supply s fn = (fn',s') ==> fn_shape_ok fn'
Proof
  strip_tac >>
  drule sue_expand_function_supply_identity >> strip_tac >>
  `MAP (\bb. bb.bb_label) fn'.fn_blocks = MAP (\bb. bb.bb_label) fn.fn_blocks` by
    (Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
     gvs[sue_expand_function_supply_def] >>
     metis_tac[sue_expand_blocks_supply_labels]) >>
  gvs[fn_shape_ok_def] >> rpt conj_tac
  >- metis_tac[sue_supply_opaque_use_ok]
  >- (`EVERY (\l. ~reserved_label l) (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
        simp[listTheory.EVERY_MAP] >>
      qpat_x_assum `MAP _ fn'.fn_blocks = _` (SUBST_ALL_TAC o SYM) >>
      gvs[listTheory.EVERY_MAP])
  >- metis_tac[sue_expand_function_supply_inst_shape] >>
  metis_tac[sue_supply_call_checks_ok]
QED

Theorem sue_supply_o1_fn_shape:
  ir_supply_inst_ok s /\ ir_supply_covers_fn s fn /\ o1_fn_shape ctx fn /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts fn) /\
  sue_expand_function_supply s fn = (fn',s') ==> o1_fn_shape ctx fn'
Proof
  strip_tac >>
  drule sue_expand_function_supply_identity >> strip_tac >>
  `!P. P ASSIGN /\ EVERY (\i. P i.inst_opcode) (fn_insts fn) ==>
       EVERY (\i. P i.inst_opcode) (fn_insts fn')` by
    metis_tac[sue_expand_function_supply_opcodes] >>
  gvs[o1_fn_shape_def] >> rpt conj_tac
  >- metis_tac[sue_expand_function_supply_wf_function]
  >- (irule sue_expand_function_supply_inst_wf >>
      goal_assum (drule_at Any) >> gvs[dretDesugarDefsTheory.no_dret_def,
        listTheory.EVERY_MEM] >> metis_tac[])
  >- metis_tac[sue_supply_fn_shape_ok]
  >- (irule sue_supply_first_block_no_preds >>
      goal_assum (drule_at Any) >> gvs[wf_function_def])
  >- (irule sue_supply_first_block_no_phi >>
      goal_assum (drule_at Any) >> gvs[wf_function_def])
  >- metis_tac[sue_supply_fn_invoke_ok]
  >- metis_tac[sue_supply_fn_label_refs_ok]
  >- (simp[dretDesugarDefsTheory.no_dret_def, GSYM listTheory.EVERY_MEM] >>
      first_x_assum (qspec_then `\opc. opc <> DRET` mp_tac) >>
      gvs[dretDesugarDefsTheory.no_dret_def, listTheory.EVERY_MEM])
  >- (strip_tac >> gvs[] >> conj_tac
      >- metis_tac[sue_supply_entry_fn_no_return] >>
      metis_tac[sue_supply_entry_fn_no_params]) >>
  strip_tac >>
  first_x_assum (qspec_then `\opc. opc <> STOP /\ opc <> RETURN` mp_tac) >>
  simp[]
QED

Theorem sue_step_elim[local]:
  fn_pass_step rpolicy (CFP_Simple VP_SingleUseExpansion) observed s fn out /\
  o1_ctx_shape observed.cu_context ==>
  o1_fn_shape observed.cu_context fn /\ ir_supply_covers_fn s fn /\
  sue_expand_function_supply s fn = (out.fpo_function,out.fpo_supply) /\
  out.fpo_label_map = []
Proof
  simp[fn_pass_step_def] >> strip_tac >>
  drule venomFnScheduleRunnerPropsTheory.lookup_unique_function_member >> strip_tac >>
  `o1_fn_shape observed.cu_context fn` by
    (gvs[o1_ctx_shape_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  Cases_on `sue_expand_function_supply s fn` >> gvs[] >>
  gvs[venomFnScheduleRunnerTheory.ir_supply_covers_unit_def,
      venomFnScheduleRunnerTheory.ir_supply_covers_fn_def,
      venomFnScheduleRunnerTheory.list_subset_def,
      irSupplyTheory.unit_ir_inst_ids_def, irSupplyTheory.unit_ir_vars_def,
      irSupplyTheory.unit_ir_labels_def, listTheory.EVERY_MEM,
      listTheory.MEM_FLAT, listTheory.MEM_MAP, PULL_EXISTS] >> metis_tac[]
QED

Theorem sue_step_contract:
  o1_step_contract_at 6 rpolicy (CFP_Simple VP_SingleUseExpansion)
Proof
  simp[o1_step_contract_at_def] >> rpt gen_tac >> strip_tac >>
  drule_all sue_step_elim >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts fn)` by
    gvs[o1_fn_row_def] >>
  `sue_supply_extends s out.fpo_supply` by
    metis_tac[sue_expand_function_supply_extends] >>
  `fn_labels out.fpo_function = fn_labels fn` by
    (Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
     gvs[sue_expand_function_supply_def, fn_labels_def] >>
     qpat_x_assum `_ = out.fpo_function` (SUBST1_TAC o SYM) >> simp[] >>
     metis_tac[sue_expand_blocks_supply_labels]) >>
  rpt conj_tac
  >- metis_tac[sue_supply_o1_fn_shape]
  >- (simp[fresh_names_ok_def] >>
      `ALL_DISTINCT (fn_ir_inst_ids fn)` by
        gvs[o1_fn_shape_def, wf_function_def, fn_inst_ids_distinct_def,
            irSupplyTheory.fn_ir_inst_ids_def,
            lambdify irSupplyTheory.block_ir_inst_ids_def] >>
      `EVERY (\id. MEM id s.irs_used_inst_ids) (fn_ir_inst_ids fn)` by
        gvs[venomFnScheduleRunnerTheory.ir_supply_covers_fn_def,
            venomFnScheduleRunnerTheory.list_subset_def] >>
      drule_all sue_expand_function_supply_ids_ok >>
      simp[sue_ids_supply_ok_def] >> metis_tac[])
  >- simp[label_map_sources_ok_def]
  >- gvs[sue_supply_extends_def] >>
  simp[o1_fn_row_def] >>
  drule_at (Pat `sue_expand_function_supply _ _ = _`)
    sue_expand_function_supply_opcodes >>
  disch_then (qspec_then `\opc. opc <> ALLOCA` mp_tac) >> simp[]
QED
