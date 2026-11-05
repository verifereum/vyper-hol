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
  arithmetic finite_map planExec

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


Theorem codegen_assembly_frame_prog_ok:
  codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit ==>
  asm_frame_prog_ok prog
Proof
  cheat
QED
