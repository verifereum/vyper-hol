(*
 * The generated assembly has the shape the frame simulation needs.
 *
 * TOP-LEVEL:
 *   codegen_assembly_frame_prog_ok
 *)

Theory codegenAsmProgOk
Ancestors
  asmFrameRel codegenEncodingWf codegen unitShapeDefs asmWf asmSem
  symbolResolve stackPlanGen stackPlanOps stackPlanTypes asmIR list rich_list
  arithmetic finite_map planExec venomInst

Theorem exec_stack_op_no_data[local]:
  EVERY (\i. ~is_data_inst i) (exec_stack_op fmp op)
Proof
  Cases_on `op` >> simp[exec_stack_op_def, is_data_inst_def, EVERY_REPLICATE] >>
  Cases_on `o'` >> simp[exec_stack_op_def, is_data_inst_def]
QED

Theorem execute_plan_no_data[local]:
  EVERY (\i. ~is_data_inst i) (execute_plan fmp ops)
Proof
  simp[execute_plan_def, EVERY_FLAT, EVERY_MAP, exec_stack_op_no_data]
QED

Theorem data_suffix_all_data[local]:
  EVERY is_data_inst (data_segment_asm segs ++ [AsmDataHeader "code_end"])
Proof
  simp[data_segment_asm_def, data_section_asm_def, EVERY_FLAT, EVERY_MAP,
       is_data_inst_def] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  Cases_on `di` >> simp[is_data_inst_def]
QED

Theorem data_suffix_no_op[local]:
  ~MEM (AsmOp name) (data_segment_asm segs ++ [AsmDataHeader "code_end"])
Proof
  mp_tac data_suffix_all_data >>
  simp[EVERY_MEM] >> metis_tac[is_data_inst_def]
QED

Theorem data_suffix_prefix_indices[local]:
  EVERY (\x. ~is_data_inst x) xs /\ EVERY is_data_inst ys ==>
  !i. i < LENGTH (xs ++ ys) /\ ~is_data_inst (EL i (xs ++ ys)) ==>
  !j. j <= i ==> ~is_data_inst (EL j (xs ++ ys))
Proof
  rpt strip_tac >>
  `i < LENGTH xs` by
    (spose_not_then assume_tac >>
     gvs[EL_APPEND, EVERY_EL] >>
     first_x_assum (qspec_then `i - LENGTH xs` mp_tac) >> simp[]) >>
  `j < LENGTH xs` by decide_tac >>
  gvs[EL_APPEND, EVERY_EL]
QED

Theorem cond_ne[local]:
  (if b then x else y) <> z <=>
  (b ==> x <> z) /\ (~b ==> y <> z)
Proof
  Cases_on `b` >> simp[]
QED

Theorem swap_name_no_forbidden[local]:
  MEM name ["DELEGATECALL"; "CREATE"; "CREATE2"; "SELFDESTRUCT"] ==>
  swap_name n <> name
Proof
  rewrite_tac[MEM] >> strip_tac >> gvs[] >>
  pure_rewrite_tac[swap_name_def, cond_ne] >>
  simp_tac (srw_ss()) []
QED

Theorem dup_name_no_forbidden[local]:
  MEM name ["DELEGATECALL"; "CREATE"; "CREATE2"; "SELFDESTRUCT"] ==>
  dup_name n <> name
Proof
  rewrite_tac[MEM] >> strip_tac >> gvs[] >>
  pure_rewrite_tac[dup_name_def, cond_ne] >>
  simp_tac (srw_ss()) []
QED

Theorem exec_stack_op_no_forbidden[local]:
  MEM name ["DELEGATECALL"; "CREATE"; "CREATE2"; "SELFDESTRUCT"] /\
  op <> SOEmit name ==> ~MEM (AsmOp name) (exec_stack_op fmp op)
Proof
  strip_tac >>
  `!n. swap_name n <> name /\ dup_name n <> name` by
    metis_tac[swap_name_no_forbidden, dup_name_no_forbidden] >>
  Cases_on `op`
  >- (Cases_on `o'` >> simp[exec_stack_op_def]) >>
  gvs[exec_stack_op_def, MEM_REPLICATE]
QED

Theorem execute_plan_no_forbidden[local]:
  MEM name ["DELEGATECALL"; "CREATE"; "CREATE2"; "SELFDESTRUCT"] /\
  ~MEM (SOEmit name) ops ==> ~MEM (AsmOp name) (execute_plan fmp ops)
Proof
  strip_tac >>
  simp[execute_plan_def, MEM_FLAT, MEM_MAP] >>
  metis_tac[exec_stack_op_no_forbidden]
QED

Theorem spill_fold_no_emit[local]:
  !items acc_ops offsets al ops offsets' al'.
  FOLDL (\(ops, offs, al) item.
    (\(off, al'). (ops ++ [SOSpill off], SNOC off offs, al'))
      (alloc_spill_slot al))
    (acc_ops, offsets, al) items = (ops, offsets', al') /\
  ~MEM (SOEmit name) acc_ops ==> ~MEM (SOEmit name) ops
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `alloc_spill_slot al` >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `acc_ops ++ [SOSpill q]` mp_tac) >>
  simp[] >> disch_then drule >> simp[]
QED

Theorem do_swap_no_emit[local]:
  do_swap dist ps = (ops, ps') ==> !name. ~MEM (SOEmit name) ops
Proof
  simp[do_swap_def] >>
  Cases_on `dist = 0` >- simp[] >>
  Cases_on `dist <= 16` >- (rw[] >> simp[]) >>
  simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  simp[MEM_MAP, PULL_EXISTS] >>
  rpt gen_tac >> drule spill_fold_no_emit >> simp[]
QED

Theorem popmany_fold_no_emit[local]:
  !xs acc_ops ps ops ps'.
  FOLDL (\(ops, ps) v.
    case stack_get_depth v ps.ps_stack of
      NONE => (ops, ps)
    | SOME dist =>
        (\(swap_ops, ps').
          (ops ++ swap_ops ++ [SOPop 1],
           ps' with ps_stack := stack_pop 1 ps'.ps_stack))
        (if dist = 0 then ([], ps) else do_swap dist ps))
    (acc_ops, ps) xs = (ops, ps') /\
  ~MEM (SOEmit name) acc_ops ==> ~MEM (SOEmit name) ops
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `stack_get_depth h ps.ps_stack` >> simp[]
  >- metis_tac[] >>
  Cases_on `x = 0` >> simp[]
  >- (strip_tac >>
      first_x_assum (qspec_then `acc_ops ++ [SOPop 1]` mp_tac) >>
      simp[] >> disch_then drule >> simp[]) >>
  Cases_on `do_swap x ps` >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `acc_ops ++ q ++ [SOPop 1]` mp_tac) >>
  simp[] >> disch_then drule >> drule do_swap_no_emit >> simp[]
QED

Theorem popmany_individual_no_emit[local]:
  popmany_individual to_pop ps = (ops, ps') ==>
  !name. ~MEM (SOEmit name) ops
Proof
  simp[popmany_individual_def] >> strip_tac >> rpt gen_tac >>
  drule popmany_fold_no_emit >> simp[]
QED

Theorem popmany_plan_no_emit[local]:
  popmany_plan to_pop ps = (ops, ps') ==> !name. ~MEM (SOEmit name) ops
Proof
  Cases_on `to_pop` >> simp[popmany_plan_def] >>
  rpt IF_CASES_TAC >> simp[]
  >- (pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      drule do_swap_no_emit >> simp[]) >>
  metis_tac[popmany_individual_no_emit]
QED

Theorem optimistic_swap_plan_no_emit[local]:
  optimistic_swap_plan dfg inst live term ps = (ops, ps') ==>
  !name. ~MEM (SOEmit name) ops
Proof
  simp[optimistic_swap_plan_def] >> rpt IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_depth (Var (LAST live)) ps.ps_stack` >> simp[] >>
  metis_tac[do_swap_no_emit]
QED

Theorem do_spill_tos_no_emit[local]:
  do_spill_tos ps = (ops, ps') ==> !name. ~MEM (SOEmit name) ops
Proof
  simp[do_spill_tos_def] >> pairarg_tac >> simp[] >> rw[] >> simp[]
QED

Theorem do_spill_at_no_emit[local]:
  do_spill_at dist ps = (ops, ps') ==> !name. ~MEM (SOEmit name) ops
Proof
  simp[do_spill_at_def] >> IF_CASES_TAC >> simp[]
  >- metis_tac[do_spill_tos_no_emit] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule do_spill_tos_no_emit >> simp[]
QED

Theorem do_restore_no_emit[local]:
  do_restore op ps = (ops, ps') ==> !name. ~MEM (SOEmit name) ops
Proof
  simp[do_restore_def] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >> simp[] >> rw[] >> simp[]
QED

Theorem restore_spilled_plan_no_emit[local]:
  !ops0 ps ops ps'.
  restore_spilled_plan ops0 ps = (ops, ps') ==>
  !name. ~MEM (SOEmit name) ops
Proof
  Induct >> simp[restore_spilled_plan_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  imp_res_tac do_restore_no_emit >> metis_tac[]
QED

Theorem do_dup_no_emit[local]:
  do_dup dist ps = (ops, ps') ==> !name. ~MEM (SOEmit name) ops
Proof
  simp[do_dup_def] >> IF_CASES_TAC >- (rw[] >> simp[]) >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rpt IF_CASES_TAC >> simp[] >> rpt gen_tac >>
  drule spill_fold_no_emit >> simp[]
QED

Theorem reduce_depth_plan_no_emit[local]:
  !fuel target_ops target_op f n ps ops ps'.
  reduce_depth_plan fuel target_ops target_op f n ps = (ops, ps') ==>
  !name. ~MEM (SOEmit name) ops
Proof
  Induct >> simp[reduce_depth_plan_def] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_unfixed_depth target_op f n ps.ps_stack` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `select_spill_candidate ps.ps_stack target_ops x n` >> simp[] >>
  pairarg_tac >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> metis_tac[do_spill_at_no_emit]
QED

Theorem reorder_one_no_emit[local]:
  reorder_one dfg target_ops idx op ps = (ops, ps') ==>
  !name. ~MEM (SOEmit name) ops
Proof
  simp[reorder_one_def] >> pairarg_tac >>
  `!name. ~MEM (SOEmit name) restore_ops` by
    (gvs[AllCaseEqs()] >> metis_tac[do_restore_no_emit]) >>
  gvs[] >> qpat_x_assum `_ = (restore_ops, ps1)` kall_tac >>
  Cases_on `stack_get_unfixed_depth op (LENGTH target_ops - (idx + 1))
              (LENGTH target_ops) ps1.ps_stack` >> simp[]
  >- (rw[] >> gvs[]) >>
  pairarg_tac >>
  `!name. ~MEM (SOEmit name) reduce_ops` by
    (gvs[AllCaseEqs()] >> metis_tac[reduce_depth_plan_no_emit]) >>
  gvs[] >> qpat_x_assum `_ = (reduce_ops, ps2)` kall_tac >>
  Cases_on `stack_get_unfixed_depth op (LENGTH target_ops - (idx + 1))
              (LENGTH target_ops) ps2.ps_stack` >> simp[]
  >- (rw[] >> gvs[]) >>
  rpt IF_CASES_TAC >> simp[] >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[do_swap_no_emit, MEM_APPEND]
QED

Theorem reorder_fold_no_emit[local]:
  !xs acc_ops ps ops ps'.
  FOLDL (\(ops, ps) (idx, op).
    (\(step_ops, ps'). (ops ++ step_ops, ps'))
      (reorder_one dfg target_ops idx op ps)) (acc_ops, ps) xs =
    (ops, ps') /\ ~MEM (SOEmit name) acc_ops ==>
  ~MEM (SOEmit name) ops
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >> simp[] >>
  Cases_on `reorder_one dfg target_ops h0 h1 ps` >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `acc_ops ++ q` mp_tac) >> simp[] >>
  disch_then drule >> drule reorder_one_no_emit >> simp[]
QED

Theorem reorder_plan_no_emit[local]:
  reorder_plan dfg target_ops ps = (ops, ps') ==>
  !name. ~MEM (SOEmit name) ops
Proof
  simp[reorder_plan_def] >> strip_tac >> rpt gen_tac >>
  drule reorder_fold_no_emit >> simp[]
QED

Theorem emit_one_input_no_emit[local]:
  emit_one_input opc live op ps = (ops, ps') ==>
  !name. ~MEM (SOEmit name) ops
Proof
  simp[emit_one_input_def] >> pairarg_tac >>
  `!name. ~MEM (SOEmit name) restore_ops` by
    (gvs[AllCaseEqs()] >> metis_tac[do_restore_no_emit]) >>
  gvs[] >> qpat_x_assum `_ = (restore_ops, ps1)` kall_tac >>
  Cases_on `op` >> simp[] >> rpt IF_CASES_TAC >> simp[] >>
  gvs[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> metis_tac[do_dup_no_emit]
QED

Theorem emit_input_plan_no_emit[local]:
  !operands ps ops ps'.
  emit_input_plan opc operands live ps = (ops, ps') ==>
  !name. ~MEM (SOEmit name) ops
Proof
  Induct >> simp[emit_input_plan_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[emit_one_input_no_emit, MEM_APPEND]
QED

Theorem generate_phi_plan_no_emit[local]:
  generate_phi_plan inst live halting ps = (ops, ps') ==>
  !name. ~MEM (SOEmit name) ops
Proof
  simp[generate_phi_plan_def] >>
  Cases_on `stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
              ps.ps_stack` >> simp[] >>
  Cases_on `MEM (operand_to_string (stack_peek x ps.ps_stack)) live` >>
  simp[] >> rpt (pairarg_tac >> gvs[]) >>
  rw[] >> rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac do_dup_no_emit >> imp_res_tac popmany_plan_no_emit >> gvs[]
QED
Theorem generate_offset_plan_no_emit[local]:
  generate_offset_plan inst ps = (ops, ps') ==>
  !name. ~MEM (SOEmit name) ops
Proof
  simp[generate_offset_plan_def] >>
  Cases_on `EL 1 inst.inst_operands` >> simp[] >> rw[] >> simp[]
QED

Theorem generate_emit_ops_no_forbidden[local]:
  generate_emit_ops inst topics ps = (ops, ps') /\
  ~MEM inst.inst_opcode [DELEGATECALL; CREATE; CREATE2; SELFDESTRUCT] ==>
  !name. MEM name ["DELEGATECALL"; "CREATE"; "CREATE2"; "SELFDESTRUCT"] ==>
    ~MEM (SOEmit name) ops
Proof
  simp[generate_emit_ops_def] >> rpt IF_CASES_TAC >>
  gvs[AllCaseEqs(), bump_emit_ops_def] >>
  rpt strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[venom_to_evm_name_def] >>
  Cases_on `inst.inst_opcode` >> gvs[venom_to_evm_name_def]
QED
Theorem generate_regular_inst_plan_no_forbidden[local]:
  generate_regular_inst_plan liveness dfg cfg fn inst live halting term cur ps =
    (ops, ps') /\
  ~MEM inst.inst_opcode [DELEGATECALL; CREATE; CREATE2; SELFDESTRUCT] ==>
  !name. MEM name ["DELEGATECALL"; "CREATE"; "CREATE2"; "SELFDESTRUCT"] ==>
    ~MEM (SOEmit name) ops
Proof
  strip_tac >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def] >> pairarg_tac >>
  `!name. ~MEM (SOEmit name) input_ops` by metis_tac[emit_input_plan_no_emit] >>
  gvs[] >> qpat_x_assum `_ = (input_ops, ps1)` kall_tac >> pairarg_tac >>
  `!name. ~MEM (SOEmit name) join_ops` by
    (gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
     metis_tac[reorder_plan_no_emit, restore_spilled_plan_no_emit]) >>
  gvs[] >> qpat_x_assum `_ = (join_ops, ps2)` kall_tac >> pairarg_tac >>
  `!name. ~MEM (SOEmit name) reorder_ops` by
    (gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
     gvs[AllCaseEqs()] >> metis_tac[reorder_plan_no_emit]) >>
  gvs[] >> qpat_x_assum `_ = (reorder_ops, ps4)` kall_tac >> pairarg_tac >>
  `!name. MEM name ["DELEGATECALL"; "CREATE"; "CREATE2"; "SELFDESTRUCT"] ==>
      ~MEM (SOEmit name) emit_ops` by
    (qmatch_asmsub_abbrev_tac `generate_emit_ops inst topics ps6` >>
     drule generate_emit_ops_no_forbidden >> simp[]) >>
  gvs[] >> qpat_x_assum `_ = (emit_ops, ps7)` kall_tac >>
  IF_CASES_TAC >> simp[] >- (rw[] >> gvs[]) >> pairarg_tac >>
  `!name. ~MEM (SOEmit name) pop_ops` by
    (gvs[AllCaseEqs()] >> metis_tac[popmany_plan_no_emit]) >>
  gvs[] >> qpat_x_assum `_ = (pop_ops, ps8)` kall_tac >> pairarg_tac >>
  `!name. ~MEM (SOEmit name) opt_ops` by
    (gvs[AllCaseEqs()] >> metis_tac[optimistic_swap_plan_no_emit]) >>
  gvs[] >> rw[] >> gvs[]
QED

Theorem generate_inst_plan_no_forbidden[local]:
  generate_inst_plan liveness dfg cfg fn inst live halting term cur ps =
    SOME (ops, ps') /\
  ~MEM inst.inst_opcode [DELEGATECALL; CREATE; CREATE2; SELFDESTRUCT] ==>
  !name. MEM name ["DELEGATECALL"; "CREATE"; "CREATE2"; "SELFDESTRUCT"] ==>
    ~MEM (SOEmit name) ops
Proof
  simp[generate_inst_plan_def] >> rpt IF_CASES_TAC >> simp[] >>
  metis_tac[generate_phi_plan_no_emit, generate_offset_plan_no_emit,
            generate_regular_inst_plan_no_forbidden, MEM]
QED

Theorem prepare_params_plan_no_emit[local]:
  prepare_params_plan liveness fn ps = (ops, ps') ==>
  !name. ~MEM (SOEmit name) ops
Proof
  simp[prepare_params_plan_def] >> IF_CASES_TAC >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[popmany_plan_no_emit, optimistic_swap_plan_no_emit, MEM_APPEND]
QED

Theorem clean_stack_plan_no_emit[local]:
  clean_stack_plan liveness cfg fn bb ps = (ops, ps') ==>
  !name. ~MEM (SOEmit name) ops
Proof
  simp[clean_stack_plan_def] >> gvs[AllCaseEqs()] >>
  rpt IF_CASES_TAC >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[popmany_plan_no_emit]
QED

Theorem generate_block_insts_plan_no_forbidden[local]:
  !insts i ps ops ps'.
  generate_block_insts_plan liveness dfg cfg fn bb_label halting
    n_params block_len i insts ps = SOME (ops, ps') /\
  EVERY (\inst. ~MEM inst.inst_opcode
    [DELEGATECALL; CREATE; CREATE2; SELFDESTRUCT]) insts ==>
  !name. MEM name ["DELEGATECALL"; "CREATE"; "CREATE2"; "SELFDESTRUCT"] ==>
    ~MEM (SOEmit name) ops
Proof
  Induct >> simp[generate_block_insts_plan_def] >> rpt gen_tac >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule generate_inst_plan_no_forbidden >> simp[] >>
  strip_tac >> metis_tac[]
QED

Theorem generate_block_plan_no_forbidden[local]:
  generate_block_plan liveness dfg cfg fn bb ps = SOME (ops, ps') /\
  EVERY (\inst. ~MEM inst.inst_opcode
    [DELEGATECALL; CREATE; CREATE2; SELFDESTRUCT]) bb.bb_instructions ==>
  !name. MEM name ["DELEGATECALL"; "CREATE"; "CREATE2"; "SELFDESTRUCT"] ==>
    ~MEM (SOEmit name) ops
Proof
  simp[generate_block_plan_def] >> pairarg_tac >>
  `!name. ~MEM (SOEmit name) param_ops` by
    (gvs[AllCaseEqs()] >> metis_tac[prepare_params_plan_no_emit]) >>
  gvs[] >> qpat_x_assum `_ = (param_ops, ps1)` kall_tac >> pairarg_tac >>
  `!name. ~MEM (SOEmit name) clean_ops` by
    (gvs[AllCaseEqs()] >> metis_tac[clean_stack_plan_no_emit]) >>
  gvs[] >> qpat_x_assum `_ = (clean_ops, ps2)` kall_tac >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  `EVERY (\inst. ~MEM inst.inst_opcode
    [DELEGATECALL; CREATE; CREATE2; SELFDESTRUCT]) (non_param_insts bb)` by
    (gvs[non_param_insts_def, EVERY_MEM, MEM_FILTER] >> metis_tac[]) >>
  drule generate_block_insts_plan_no_forbidden >> simp[] >>
  gvs[]
QED

Theorem lookup_block_every_insts[local]:
  !bbs. EVERY P (fn_insts_blocks bbs) /\ lookup_block lbl bbs = SOME bb ==>
    EVERY P bb.bb_instructions
Proof
  Induct >> simp[fn_insts_blocks_def, lookup_block_def, FIND_thm] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[] >> strip_tac >> gvs[lookup_block_def]
QED

Theorem fn_plan_aux_no_forbidden[local]:
  (!liveness dfg cfg fn worklist visited ps ops visited' ps'.
    generate_fn_plan_aux liveness dfg cfg fn worklist visited ps =
      SOME (ops, visited', ps') /\
    EVERY (\inst. ~MEM inst.inst_opcode
      [DELEGATECALL; CREATE; CREATE2; SELFDESTRUCT]) (fn_insts fn) ==>
    !name. MEM name ["DELEGATECALL"; "CREATE"; "CREATE2"; "SELFDESTRUCT"] ==>
      ~MEM (SOEmit name) ops) /\
  (!liveness dfg cfg fn ss sp succs visited ps ops visited' ps'.
    generate_succs_plan liveness dfg cfg fn ss sp succs visited ps =
      SOME (ops, visited', ps') /\
    EVERY (\inst. ~MEM inst.inst_opcode
      [DELEGATECALL; CREATE; CREATE2; SELFDESTRUCT]) (fn_insts fn) ==>
    !name. MEM name ["DELEGATECALL"; "CREATE"; "CREATE2"; "SELFDESTRUCT"] ==>
      ~MEM (SOEmit name) ops)
Proof
  ho_match_mp_tac generate_fn_plan_aux_ind >> rpt conj_tac
  >- (rpt gen_tac >> simp[Once generate_fn_plan_aux_def] >> rw[] >> simp[])
  >- (rpt gen_tac >> strip_tac >> simp[Once generate_fn_plan_aux_def] >>
      Cases_on `MEM lbl visited` >- (gvs[] >> metis_tac[]) >>
      gvs[] >> Cases_on `lookup_block lbl fn.fn_blocks`
      >- (gvs[] >> metis_tac[]) >>
      simp[AllCaseEqs()] >> rpt gen_tac >> strip_tac >> gvs[] >>
      `EVERY (\inst. ~MEM inst.inst_opcode
        [DELEGATECALL; CREATE; CREATE2; SELFDESTRUCT]) x.bb_instructions` by
        (irule lookup_block_every_insts >> gvs[fn_insts_def] >> metis_tac[]) >>
      drule generate_block_plan_no_forbidden >> simp[] >>
      gvs[] >> metis_tac[])
  >- (rpt gen_tac >> simp[Once generate_fn_plan_aux_def] >> rw[] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  simp[Once generate_fn_plan_aux_def, AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >> gvs[] >> metis_tac[MEM_APPEND]
QED

Theorem generate_fn_plan_with_cleanup_no_forbidden[local]:
  generate_fn_plan_with_cleanup ch growth fn spill_base lbl_ctr = SOME (ops, ps) /\
  EVERY (\inst. ~MEM inst.inst_opcode
    [DELEGATECALL; CREATE; CREATE2; SELFDESTRUCT]) (fn_insts fn) ==>
  !name. MEM name ["DELEGATECALL"; "CREATE"; "CREATE2"; "SELFDESTRUCT"] ==>
    ~MEM (SOEmit name) ops
Proof
  simp[generate_fn_plan_with_cleanup_def,
       generate_fn_plan_with_cleanup_analyzed_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  drule (cj 1 fn_plan_aux_no_forbidden) >> simp[] >> gvs[]
QED

Theorem generate_context_regions_no_forbidden[local]:
  !fns acc acc'.
  generate_context_regions gen fns acc = SOME acc' /\
  (!fn sb lc ops ps name.
    MEM fn fns /\ gen fn sb lc = SOME (ops, ps) /\
    MEM name ["DELEGATECALL"; "CREATE"; "CREATE2"; "SELFDESTRUCT"] ==>
      ~MEM (SOEmit name) ops) /\
  (!r name. MEM r acc.cpa_regions /\
    MEM name ["DELEGATECALL"; "CREATE"; "CREATE2"; "SELFDESTRUCT"] ==>
      ~MEM (SOEmit name) r.sr_plan) ==>
  !r name. MEM r acc'.cpa_regions /\
    MEM name ["DELEGATECALL"; "CREATE"; "CREATE2"; "SELFDESTRUCT"] ==>
      ~MEM (SOEmit name) r.sr_plan
Proof
  Induct >> simp[generate_context_regions_def] >>
  rpt gen_tac >> simp[AllCaseEqs()] >> rpt strip_tac >>
  (first_x_assum (drule_then (qspecl_then [`r`, `name`] mp_tac)) >>
   impl_tac >- (rw[MEM_SNOC] >> gvs[] >> metis_tac[]) >> simp[])
QED

Theorem generate_context_plan_no_forbidden[local]:
  generate_context_plan ctx = SOME cplan /\
  EVERY (\fn. EVERY (\inst. ~MEM inst.inst_opcode
    [DELEGATECALL; CREATE; CREATE2; SELFDESTRUCT]) (fn_insts fn)) ctx.ctx_functions ==>
  !name. MEM name ["DELEGATECALL"; "CREATE"; "CREATE2"; "SELFDESTRUCT"] ==>
    ~MEM (SOEmit name) (context_plan_ops cplan)
Proof
  simp[generate_context_plan_def, generate_context_plan_with_def, AllCaseEqs()] >>
  strip_tac >>
  `!r name. MEM r acc.cpa_regions /\
    MEM name ["DELEGATECALL"; "CREATE"; "CREATE2"; "SELFDESTRUCT"] ==>
      ~MEM (SOEmit name) r.sr_plan` by
    (rpt strip_tac >> drule generate_context_regions_no_forbidden >>
     disch_then (qspecl_then [`r`, `name`] mp_tac) >>
     impl_tac
     >- (simp[] >> rpt strip_tac >>
         drule generate_fn_plan_with_cleanup_no_forbidden >>
         gvs[EVERY_MEM] >> metis_tac[]) >> gvs[]) >>
  gvs[context_plan_ops_def, finish_context_plan_def,
      revert_postamble_def, MEM_FLAT, MEM_MAP] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem unit_shape_no_forbidden[local]:
  unit_shape_ok unit ==>
  EVERY (\fn. EVERY (\inst. ~MEM inst.inst_opcode
    [DELEGATECALL; CREATE; CREATE2; SELFDESTRUCT]) (fn_insts fn))
    unit.cu_context.ctx_functions
Proof
  simp[unit_shape_ok_def, fn_shape_ok_def, inst_shape_ok_def, EVERY_MEM] >>
  metis_tac[]
QED

Theorem codegen_assembly_no_forbidden[local]:
  codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit ==>
  !name. MEM name ["DELEGATECALL"; "CREATE"; "CREATE2"; "SELFDESTRUCT"] ==>
    ~MEM (AsmOp name) prog
Proof
  strip_tac >> drule unit_shape_no_forbidden >> strip_tac >>
  gvs[codegen_assembly_def, AllCaseEqs()] >>
  drule generate_context_plan_no_forbidden >> simp[] >>
  strip_tac >> rpt strip_tac >>
  gvs[] >>
  metis_tac[execute_plan_no_forbidden, data_suffix_no_op, MEM, MEM_APPEND]
QED



Theorem codegen_assembly_frame_prog_ok:
  codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit ==>
  asm_frame_prog_ok prog
Proof
  strip_tac >>
  `asm_encoding_wf prog` by
    metis_tac[codegen_assembly_asm_encoding_wf] >>
  `!name. MEM name ["DELEGATECALL"; "CREATE"; "CREATE2"; "SELFDESTRUCT"] ==>
    ~MEM (AsmOp name) prog` by metis_tac[codegen_assembly_no_forbidden] >>
  simp[asm_frame_prog_ok_def] >> conj_tac
  >- (qpat_x_assum `codegen_assembly _ _ = _` mp_tac >>
      simp[codegen_assembly_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
      qspecl_then [`execute_plan plan.cp_initial_fmp (context_plan_ops plan)`,
        `data_segment_asm unit.cu_data_segment ++ [AsmDataHeader "code_end"]`]
        mp_tac (Q.GENL [`xs`, `ys`] data_suffix_prefix_indices) >>
      simp[execute_plan_no_data, data_suffix_all_data]) >>
  rpt strip_tac >>
  `MEM (AsmOp name) prog` by metis_tac[EL_MEM] >>
  metis_tac[MEM]
QED
