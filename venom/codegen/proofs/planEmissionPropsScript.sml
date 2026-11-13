(* Syntactic provenance of administrative stack planning. *)
Theory planEmissionProps
Ancestors stackPlanGen stackPlanOps stackPlanTypes planExec stackOpSim asmRunBounded asmSem list rich_list

Definition plan_admin_op_def:
  plan_admin_op (SOEmit name) = F /\
  plan_admin_op (SOPushOfst lbl d) = F /\
  plan_admin_op _ = T
End

Theorem spill_fold_preserves:
  !items acc_ops offsets al ops offsets' al' P.
  FOLDL (\(ops, offs, al) item.
    (\(off, al'). (ops ++ [SOSpill off], SNOC off offs, al'))
      (alloc_spill_slot al))
    (acc_ops, offsets, al) items = (ops, offsets', al') /\
  EVERY P acc_ops /\ (!off. P (SOSpill off)) ==> EVERY P ops
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `alloc_spill_slot al` >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `acc_ops ++ [SOSpill q]` mp_tac) >>
  simp[] >> disch_then drule >> simp[]
QED

Theorem spill_fold_admin:
  !items acc_ops offsets al ops offsets' al'.
  FOLDL (\(ops, offs, al) item.
    (\(off, al'). (ops ++ [SOSpill off], SNOC off offs, al'))
      (alloc_spill_slot al))
    (acc_ops, offsets, al) items = (ops, offsets', al') /\
  EVERY plan_admin_op acc_ops ==> EVERY plan_admin_op ops
Proof
  metis_tac[spill_fold_preserves, plan_admin_op_def]
QED

Theorem do_swap_admin:
  do_swap dist ps = (ops, ps') ==> EVERY plan_admin_op ops
Proof
  simp[do_swap_def] >>
  Cases_on `dist = 0` >- simp[] >>
  Cases_on `dist <= 16` >- (rw[] >> simp[plan_admin_op_def]) >>
  simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  simp[EVERY_MAP, plan_admin_op_def] >>
  drule spill_fold_admin >> simp[]
QED

Theorem popmany_fold_preserves:
  !xs acc_ops ps ops ps' P.
  FOLDL (\(ops, ps) v.
    case stack_get_depth v ps.ps_stack of
      NONE => (ops, ps)
    | SOME dist =>
        (\(swap_ops, ps').
          (ops ++ swap_ops ++ [SOPop 1],
           ps' with ps_stack := stack_pop 1 ps'.ps_stack))
        (if dist = 0 then ([], ps) else do_swap dist ps))
    (acc_ops, ps) xs = (ops, ps') /\
  EVERY P acc_ops /\ P (SOPop 1) /\
  (!d s os s'. do_swap d s = (os,s') ==> EVERY P os) ==>
  EVERY P ops
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `stack_get_depth h ps.ps_stack` >> simp[]
  >- metis_tac[] >>
  Cases_on `x = 0` >> simp[]
  >- (strip_tac >>
      first_x_assum (qspec_then `acc_ops ++ [SOPop 1]` mp_tac) >>
      simp[] >> disch_then drule >> metis_tac[]) >>
  Cases_on `do_swap x ps` >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `acc_ops ++ q ++ [SOPop 1]` mp_tac) >>
  simp[] >> disch_then drule >> metis_tac[]
QED

Theorem popmany_fold_admin:
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
  EVERY plan_admin_op acc_ops ==> EVERY plan_admin_op ops
Proof
  metis_tac[popmany_fold_preserves, do_swap_admin, plan_admin_op_def]
QED

Theorem popmany_individual_admin:
  popmany_individual to_pop ps = (ops, ps') ==> EVERY plan_admin_op ops
Proof
  simp[popmany_individual_def] >> strip_tac >>
  drule popmany_fold_admin >> simp[]
QED

Theorem popmany_plan_admin:
  popmany_plan to_pop ps = (ops, ps') ==> EVERY plan_admin_op ops
Proof
  Cases_on `to_pop` >> simp[popmany_plan_def] >>
  rpt IF_CASES_TAC >> simp[]
  >- (pairarg_tac >> simp[] >> strip_tac >> gvs[plan_admin_op_def] >>
      drule do_swap_admin >> simp[]) >>
  metis_tac[popmany_individual_admin]
QED

Theorem optimistic_swap_plan_admin:
  optimistic_swap_plan dfg inst live term ps = (ops, ps') ==>
  EVERY plan_admin_op ops
Proof
  simp[optimistic_swap_plan_def] >> rpt IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_depth (Var (LAST live)) ps.ps_stack` >> simp[] >>
  metis_tac[do_swap_admin]
QED

Theorem do_spill_tos_admin:
  do_spill_tos ps = (ops, ps') ==> EVERY plan_admin_op ops
Proof
  simp[do_spill_tos_def] >> pairarg_tac >> simp[] >>
  rw[] >> simp[plan_admin_op_def]
QED

Theorem do_spill_at_admin:
  do_spill_at dist ps = (ops, ps') ==> EVERY plan_admin_op ops
Proof
  simp[do_spill_at_def] >> IF_CASES_TAC >> simp[]
  >- metis_tac[do_spill_tos_admin] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[plan_admin_op_def] >>
  drule do_spill_tos_admin >> simp[]
QED

Theorem do_restore_admin:
  do_restore op ps = (ops, ps') ==> EVERY plan_admin_op ops
Proof
  simp[do_restore_def] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >> simp[] >>
  rw[] >> simp[plan_admin_op_def]
QED

Theorem restore_spilled_plan_admin:
  !ops0 ps ops ps'.
  restore_spilled_plan ops0 ps = (ops, ps') ==> EVERY plan_admin_op ops
Proof
  Induct >> simp[restore_spilled_plan_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  imp_res_tac do_restore_admin >> simp[] >> metis_tac[]
QED

Theorem do_dup_admin:
  do_dup dist ps = (ops, ps') ==> EVERY plan_admin_op ops
Proof
  simp[do_dup_def] >> IF_CASES_TAC >- (rw[] >> simp[plan_admin_op_def]) >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  simp[EVERY_FLAT, EVERY_MAP] >>
  rpt IF_CASES_TAC >> simp[plan_admin_op_def] >>
  drule spill_fold_admin >> simp[]
QED

Theorem reduce_depth_plan_admin:
  !fuel target_ops target_op f n ps ops ps'.
  reduce_depth_plan fuel target_ops target_op f n ps = (ops, ps') ==>
  EVERY plan_admin_op ops
Proof
  Induct >> simp[reduce_depth_plan_def] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_unfixed_depth target_op f n ps.ps_stack` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `select_spill_candidate ps.ps_stack target_ops x n` >> simp[] >>
  pairarg_tac >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> metis_tac[do_spill_at_admin, EVERY_APPEND]
QED

Theorem reorder_one_admin:
  reorder_one dfg target_ops idx op ps = (ops, ps') ==>
  EVERY plan_admin_op ops
Proof
  simp[reorder_one_def] >> pairarg_tac >>
  `EVERY plan_admin_op restore_ops` by
    (gvs[AllCaseEqs()] >> metis_tac[do_restore_admin]) >>
  gvs[] >> qpat_x_assum `_ = (restore_ops, ps1)` kall_tac >>
  Cases_on `stack_get_unfixed_depth op (LENGTH target_ops - (idx + 1))
              (LENGTH target_ops) ps1.ps_stack` >> simp[]
  >- (rw[] >> gvs[]) >>
  pairarg_tac >>
  `EVERY plan_admin_op reduce_ops` by
    (gvs[AllCaseEqs()] >> metis_tac[reduce_depth_plan_admin]) >>
  gvs[] >> qpat_x_assum `_ = (reduce_ops, ps2)` kall_tac >>
  Cases_on `stack_get_unfixed_depth op (LENGTH target_ops - (idx + 1))
              (LENGTH target_ops) ps2.ps_stack` >> simp[]
  >- (rw[] >> gvs[]) >>
  rpt IF_CASES_TAC >> simp[] >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[do_swap_admin, EVERY_APPEND]
QED

Theorem reorder_fold_preserves:
  !xs acc_ops ps ops ps' P.
  FOLDL (\(ops, ps) (idx, op).
    (\(step_ops, ps'). (ops ++ step_ops, ps'))
      (reorder_one dfg target_ops idx op ps)) (acc_ops, ps) xs =
    (ops, ps') /\ EVERY P acc_ops /\
    (!idx op s os s'. reorder_one dfg target_ops idx op s = (os,s') ==>
       EVERY P os) ==> EVERY P ops
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >> simp[] >>
  Cases_on `reorder_one dfg target_ops h0 h1 ps` >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `acc_ops ++ q` mp_tac) >> simp[] >>
  disch_then drule >> metis_tac[]
QED

Theorem reorder_fold_admin:
  !xs acc_ops ps ops ps'.
  FOLDL (\(ops, ps) (idx, op).
    (\(step_ops, ps'). (ops ++ step_ops, ps'))
      (reorder_one dfg target_ops idx op ps)) (acc_ops, ps) xs =
    (ops, ps') /\ EVERY plan_admin_op acc_ops ==> EVERY plan_admin_op ops
Proof
  metis_tac[reorder_fold_preserves, reorder_one_admin]
QED

Theorem reorder_plan_admin:
  reorder_plan dfg target_ops ps = (ops, ps') ==> EVERY plan_admin_op ops
Proof
  simp[reorder_plan_def] >> strip_tac >>
  drule reorder_fold_admin >> simp[]
QED

Theorem emit_one_input_admin:
  emit_one_input opc live op ps = (ops, ps') ==> EVERY plan_admin_op ops
Proof
  simp[emit_one_input_def] >> pairarg_tac >>
  `EVERY plan_admin_op restore_ops` by
    (gvs[AllCaseEqs()] >> metis_tac[do_restore_admin]) >>
  gvs[] >> qpat_x_assum `_ = (restore_ops, ps1)` kall_tac >>
  Cases_on `op` >> simp[plan_admin_op_def] >>
  rpt IF_CASES_TAC >> simp[plan_admin_op_def] >>
  gvs[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[plan_admin_op_def]) >>
  simp[plan_admin_op_def] >> metis_tac[do_dup_admin, EVERY_APPEND]
QED

Theorem emit_input_plan_admin:
  !operands ps ops ps'.
  emit_input_plan opc operands live ps = (ops, ps') ==> EVERY plan_admin_op ops
Proof
  Induct >> simp[emit_input_plan_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[emit_one_input_admin, EVERY_APPEND]
QED

Theorem plan_admin_no_push_ofst:
  EVERY plan_admin_op ops ==> !lbl d. ~MEM (SOPushOfst lbl d) ops
Proof
  simp[EVERY_MEM] >> metis_tac[plan_admin_op_def]
QED

Theorem plan_admin_no_emit:
  EVERY plan_admin_op ops ==> !name. ~MEM (SOEmit name) ops
Proof
  simp[EVERY_MEM] >> metis_tac[plan_admin_op_def]
QED

Theorem generate_emit_ops_origin:
  generate_emit_ops inst topics ps = (ops, ps') ==>
  !op. MEM op ops ==>
    plan_admin_op op \/
    ?name. op = SOEmit name /\
      (venom_to_evm_name inst.inst_opcode = SOME name \/
       name = "LOG" ++ num_to_dec_string topics \/
       MEM name ["ADD"; "JUMPI"; "JUMP"; "ISZERO"; "INVALID"; "SWAP1"; "MSTORE"])
Proof
  simp[generate_emit_ops_def] >> rpt IF_CASES_TAC >>
  gvs[AllCaseEqs(), bump_emit_ops_def] >>
  rpt strip_tac >> gvs[plan_admin_op_def] >>
  pairarg_tac >> gvs[plan_admin_op_def]
QED

Theorem generate_phi_plan_admin:
  generate_phi_plan inst live halting ps = (ops, ps') ==>
  EVERY plan_admin_op ops
Proof
  simp[generate_phi_plan_def] >>
  Cases_on `stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
              ps.ps_stack` >> simp[] >>
  Cases_on `MEM (operand_to_string (stack_peek x ps.ps_stack)) live` >>
  simp[] >> rpt (pairarg_tac >> gvs[]) >>
  rw[] >> rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac do_dup_admin >> imp_res_tac popmany_plan_admin >>
  gvs[plan_admin_op_def]
QED

Theorem generate_regular_inst_plan_preserves:
  generate_regular_inst_plan liveness dfg cfg fn inst live halting term cur ps =
    (ops, ps') /\
  (!op. plan_admin_op op ==> P op) /\
  (!topics s os s'. generate_emit_ops inst topics s = (os,s') ==> EVERY P os)
  ==> EVERY P ops
Proof
  strip_tac >>
  `!os. EVERY plan_admin_op os ==> EVERY P os` by
    (simp[EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def] >> pairarg_tac >>
  `EVERY P input_ops` by metis_tac[emit_input_plan_admin] >>
  gvs[] >> qpat_x_assum `_ = (input_ops, ps1)` kall_tac >>
  pairarg_tac >>
  `EVERY P join_ops` by
    (gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
     metis_tac[reorder_plan_admin, restore_spilled_plan_admin]) >>
  gvs[] >> qpat_x_assum `_ = (join_ops, ps2)` kall_tac >>
  pairarg_tac >>
  `EVERY P reorder_ops` by
    (gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
     gvs[AllCaseEqs()] >> metis_tac[reorder_plan_admin]) >>
  gvs[] >> qpat_x_assum `_ = (reorder_ops, ps4)` kall_tac >>
  pairarg_tac >>
  `EVERY P emit_ops` by metis_tac[] >>
  gvs[] >> qpat_x_assum `_ = (emit_ops, ps7)` kall_tac >>
  IF_CASES_TAC >> simp[] >- (rw[] >> gvs[]) >>
  pairarg_tac >>
  `EVERY P pop_ops` by
    (gvs[AllCaseEqs()] >> metis_tac[popmany_plan_admin]) >>
  gvs[] >> qpat_x_assum `_ = (pop_ops, ps8)` kall_tac >>
  pairarg_tac >>
  `EVERY P opt_ops` by
    (gvs[AllCaseEqs()] >> metis_tac[optimistic_swap_plan_admin]) >>
  gvs[] >> rw[] >> gvs[]
QED

Theorem prepare_params_plan_admin:
  prepare_params_plan liveness fn ps = (ops, ps') ==> EVERY plan_admin_op ops
Proof
  simp[prepare_params_plan_def] >> IF_CASES_TAC >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[popmany_plan_admin, optimistic_swap_plan_admin, EVERY_APPEND]
QED

Theorem clean_stack_plan_admin:
  clean_stack_plan liveness cfg fn bb ps = (ops, ps') ==>
  EVERY plan_admin_op ops
Proof
  simp[clean_stack_plan_def] >> gvs[AllCaseEqs()] >>
  rpt IF_CASES_TAC >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[popmany_plan_admin]
QED

Theorem generate_emit_ops_no_forbidden:
  generate_emit_ops inst topics ps = (ops, ps') /\
  ~MEM inst.inst_opcode [CREATE; CREATE2; DELEGATECALL; SELFDESTRUCT] ==>
  !name. MEM (SOEmit name) ops ==>
    ~MEM name ["CREATE"; "CREATE2"; "DELEGATECALL"; "SELFDESTRUCT"]
Proof
  strip_tac >>
  `!name. venom_to_evm_name inst.inst_opcode = SOME name ==>
     ~MEM name ["CREATE"; "CREATE2"; "DELEGATECALL"; "SELFDESTRUCT"]` by
    (Cases_on `inst.inst_opcode` >>
     gvs[asmIRTheory.venom_to_evm_name_def]) >>
  qx_gen_tac `name` >> strip_tac >> drule generate_emit_ops_origin >>
  disch_then (qspec_then `SOEmit name` mp_tac) >>
  simp[plan_admin_op_def] >> strip_tac >> gvs[]
QED

Theorem generate_regular_inst_plan_no_forbidden:
  generate_regular_inst_plan liveness dfg cfg fn inst live halting term cur ps =
    (ops, ps') /\
  ~MEM inst.inst_opcode [CREATE; CREATE2; DELEGATECALL; SELFDESTRUCT] ==>
  !name. MEM (SOEmit name) ops ==>
    ~MEM name ["CREATE"; "CREATE2"; "DELEGATECALL"; "SELFDESTRUCT"]
Proof
  strip_tac >>
  `EVERY (\op. !name. op = SOEmit name ==>
      ~MEM name ["CREATE"; "CREATE2"; "DELEGATECALL"; "SELFDESTRUCT"]) ops` suffices_by
    (simp[EVERY_MEM] >> metis_tac[]) >>
  drule generate_regular_inst_plan_preserves >>
  disch_then (qspec_then `\op. !name. op = SOEmit name ==>
      ~MEM name ["CREATE"; "CREATE2"; "DELEGATECALL"; "SELFDESTRUCT"]` mp_tac) >>
  impl_tac >- (conj_tac
    >- (Cases >> simp[plan_admin_op_def]) >>
    rpt gen_tac >> strip_tac >> drule generate_emit_ops_no_forbidden >>
    simp[EVERY_MEM] >> metis_tac[]) >> simp[]
QED

Theorem generate_inst_plan_no_forbidden:
  generate_inst_plan liveness dfg cfg fn inst live halting term cur ps =
    SOME (ops, ps') /\
  ~MEM inst.inst_opcode [CREATE; CREATE2; DELEGATECALL; SELFDESTRUCT] ==>
  !name. MEM (SOEmit name) ops ==>
    ~MEM name ["CREATE"; "CREATE2"; "DELEGATECALL"; "SELFDESTRUCT"]
Proof
  simp[generate_inst_plan_def] >> rpt IF_CASES_TAC >> simp[]
  >- metis_tac[generate_phi_plan_admin, plan_admin_no_emit]
  >- (simp[generate_offset_plan_def, AllCaseEqs()] >> rw[] >> gvs[])
  >> strip_tac >> drule generate_regular_inst_plan_no_forbidden >> simp[]
QED

(* Administrative code has neither control transfers nor creation opcodes. *)
Theorem plan_admin_exec_safe:
  !op fmp. plan_admin_op op ==>
    EVERY (\i. i <> AsmOp "JUMP" /\ i <> AsmOp "JUMPI" /\
               !stk. create_safe i stk) (exec_stack_op fmp op)
Proof
  Cases >> simp[plan_admin_op_def, exec_stack_op_def, create_safe_def,
    EVERY_REPLICATE] >>
  rpt gen_tac
  >~ [`exec_stack_op fmp (SOPush operand)`]
  >- (Cases_on `operand` >> simp[exec_stack_op_def, create_safe_def])
  >~ [`swap_name n`]
  >- (qspec_then `n` mp_tac swap_name_prefix >> rpt strip_tac >> gvs[]) >>
  qspec_then `n` mp_tac dup_name_prefix >> rpt strip_tac >> gvs[]
QED

Theorem plan_admin_execute_safe:
  EVERY plan_admin_op ops ==>
  EVERY (\i. i <> AsmOp "JUMP" /\ i <> AsmOp "JUMPI" /\
             !stk. create_safe i stk) (execute_plan fmp ops)
Proof
  Induct_on `ops` >> simp[execute_plan_def] >>
  gvs[execute_plan_def] >> metis_tac[plan_admin_exec_safe]
QED

Theorem plan_admin_create_safe_prefix:
  EVERY plan_admin_op ops /\
  asm_block_at prog s.as_pc (execute_plan fmp ops) /\
  n <= LENGTH (execute_plan fmp ops) ==>
  create_safe_prefix lo o2pc prog n s
Proof
  strip_tac >> irule asm_block_create_safe_prefix >>
  goal_assum (drule_at Any) >> simp[plan_admin_execute_safe]
QED

Theorem generate_regular_forward_execute_safe:
  generate_regular_inst_plan lv dfg cfg fn inst live halting term cur ps =
    (ops, ps') /\ MEM inst.inst_opcode [ASSIGN; RETURNDATACOPY; REVERT; INITIAL_FMP; BUMP] ==>
  EVERY (\i. i <> AsmOp "JUMP" /\ i <> AsmOp "JUMPI" /\
             !stk. create_safe i stk) (execute_plan fmp ops)
Proof
  strip_tac >>
  `EVERY (\op. EVERY (\i. i <> AsmOp "JUMP" /\ i <> AsmOp "JUMPI" /\
    !stk. create_safe i stk) (exec_stack_op fmp op)) ops` suffices_by
    (simp[execute_plan_def, EVERY_FLAT, EVERY_MAP]) >>
  drule generate_regular_inst_plan_preserves >>
  disch_then (qspec_then `\op. EVERY (\i. i <> AsmOp "JUMP" /\
    i <> AsmOp "JUMPI" /\ !stk. create_safe i stk)
    (exec_stack_op fmp op)` mp_tac) >> simp[] >>
  impl_tac >- (conj_tac
    >- metis_tac[plan_admin_exec_safe] >>
    rpt gen_tac >> strip_tac >>
    gvs[generate_emit_ops_def, asmIRTheory.venom_to_evm_name_def,
        bump_emit_ops_def, exec_stack_op_def, create_safe_def,
        dup_name_def]) >> simp[]
QED
