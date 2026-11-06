Theory o1MakeSsaRetpcShape
Ancestors
  o1MakeSsaRetpcTransport o1MakeSsaRequiredUses o1ContractMakeSsaPtrOk
  unitShapeDefs o1PassContract venomWf venomInst makeSsaCurrentNonDegenerate
  removeUnusedProofs cfgNormBase cfgWf list

Theorem mssa_retpc_return_syntax:
  (!i. MEM i (fn_insts g) ==> mssa_inst_origin orig fn i) /\
  all_reachable fn /\ reachable_fn g = g /\ retpc_shape_ok fn ==>
  !i. MEM i (fn_insts (reachable_fn g)) /\
      MEM i.inst_opcode [RET; RETFMP; DRET] ==>
      ?front x. i.inst_operands = front ++ [Var x]
Proof
  strip_tac >> rpt strip_tac >> gvs[] >>
  `mssa_inst_origin orig fn i` by metis_tac[] >>
  qpat_x_assum `mssa_inst_origin _ _ _` mp_tac >>
  pure_rewrite_tac[mssa_inst_origin_def] >> strip_tac >> gvs[] >>
  `MEM inst (fn_insts (reachable_fn fn))` by
    (simp[MEM_reachable_fn_insts] >>
     `?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions` by
       (fs[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
     qexistsl_tac [`bb`, `inst`] >>
     gvs[all_reachable_def, reachable_inst_def]) >>
  gvs[retpc_shape_ok_def] >>
  qpat_x_assum `!inst. MEM inst _ /\ _ ==> _` drule >> simp[] >> strip_tac >>
  `?ops last. i.inst_operands = ops ++ [last]` by
    (Cases_on `i.inst_operands` using SNOC_CASES >> gvs[]) >>
  gvs[MAP_APPEND] >> Cases_on `last` >> gvs[] >> metis_tac[]
QED

Theorem mssa_retpc_writers:
  (!i. MEM i (fn_insts g) ==> mssa_inst_origin orig fn i) /\
  retpc_shape_ok fn /\ fn_phis_non_degenerate g /\
  fn_defs_reach_uses g /\ wf_ssa g /\ fn_phis_cover_preds g /\ all_reachable g /\
  (!bb inst. MEM bb g.fn_blocks /\ MEM inst bb.bb_instructions /\
    fn_entry_label g = SOME bb.bb_label ==> inst.inst_opcode <> PHI) /\
  (!y. retpc_full_required g y ==> retpc_var g y) ==>
  !i x. MEM i (fn_insts g) /\ MEM x i.inst_outputs /\ retpc_var g x ==>
    i.inst_opcode = RETPC_PARAM \/
    (i.inst_opcode = ASSIGN /\ ?y. i.inst_operands = [Var y] /\ retpc_var g y) \/
    (i.inst_opcode = PHI /\ ?y. MEM (Var y) i.inst_operands /\ retpc_var g y)
Proof
  strip_tac >> rpt strip_tac >>
  `retpc_var fn (orig x)` by (irule mssa_retpc_origin_forward >> metis_tac[]) >>
  `mssa_inst_origin orig fn i` by metis_tac[] >>
  drule_all mssa_retpc_definition_cases >> strip_tac >> simp[]
  >- (irule mssa_retpc_operand_backward >> metis_tac[MEM]) >>
  `?w. i.inst_outputs = [w]` by
    (qpat_x_assum `mssa_inst_origin _ _ _` mp_tac >>
     pure_rewrite_tac[mssa_inst_origin_def] >> strip_tac >> gvs[]) >>
  fs[fn_phis_non_degenerate_def] >>
  qpat_x_assum `!inst out. _` drule_all >> strip_tac >>
  `MEM (Var v1) i.inst_operands` by metis_tac[phi_pairs_mem_var] >>
  qexists `v1` >> simp[] >> first_x_assum irule >>
  simp[retpc_full_required_def] >> qexistsl_tac [`i`, `x`] >> simp[]
QED

Theorem make_ssa_current_fn_retpc_shape_ok:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\ retpc_shape_ok fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (g,s') ==> retpc_shape_ok g
Proof
  strip_tac >>
  drule_all mssa_origin >> strip_tac >>
  drule_all mssa_wf_ssa >> strip_tac >>
  drule_all makeSsaCurrentInputOkTheory.make_ssa_current_fn_input_ok >> strip_tac >>
  drule_all make_ssa_current_fn_phis_non_degenerate >> strip_tac >>
  drule_all make_ssa_current_fn_retpc_required_exclusions >> strip_tac >>
  `!y. retpc_full_required g y ==> retpc_var g y` by
    (rpt strip_tac >> irule make_ssa_current_fn_retpc_full_required >> metis_tac[]) >>
  `reachable_fn g = g` by (irule mssa_reachable_output_identity >> metis_tac[]) >>
  `all_reachable fn` by fs[make_ssa_input_ok_def] >>
  `!bb inst. MEM bb g.fn_blocks /\ MEM inst bb.bb_instructions /\
    fn_entry_label g = SOME bb.bb_label ==> inst.inst_opcode <> PHI` by
    (rpt gen_tac >> strip_tac >> irule mssa_entry_no_phi >> metis_tac[]) >>
  `!i. MEM i (fn_insts (reachable_fn g)) /\
    MEM i.inst_opcode [RET; RETFMP; DRET] ==>
    ?front x. i.inst_operands = front ++ [Var x]` by
    (rpt strip_tac >> irule mssa_retpc_return_syntax >> metis_tac[]) >>
  `!i x. MEM i (fn_insts g) /\ MEM x i.inst_outputs /\ retpc_var g x ==>
    i.inst_opcode = RETPC_PARAM \/
    (i.inst_opcode = ASSIGN /\ ?y. i.inst_operands = [Var y] /\ retpc_var g y) \/
    (i.inst_opcode = PHI /\ ?y. MEM (Var y) i.inst_operands /\ retpc_var g y)` by
    (rpt strip_tac >> irule mssa_retpc_writers >> metis_tac[]) >>
  `!i j x. MEM i (fn_insts g) /\ MEM j (fn_insts g) /\
    MEM x i.inst_outputs /\ MEM x j.inst_outputs /\ retpc_var g x ==> i = j` by
    (fs[wf_ssa_def, fn_insts_def] >> metis_tac[ssa_outputs_same_inst]) >>
  irule retpc_required_certificate >> simp[] >>
  conj_tac >> first_assum ACCEPT_TAC
QED
