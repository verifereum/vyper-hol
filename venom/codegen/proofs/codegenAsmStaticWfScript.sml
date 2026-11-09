(*
 * Codegen's assembly is statically well formed for the symbolic machine:
 * labels are unique and never also data headers, every referenced label is
 * defined, the data segment holds no code addresses and sits at the end,
 * and the encoding fits.
 *)
Theory codegenAsmStaticWf
Ancestors
  codegenSymRel codegenAsmProgOk codegenEncodingWf codegen asmSymSem asmWf
  asmOptimizer unitShapeDefs stackPlanGen venomWf fnPlanCover fnBlockBodyHelpers
  list rich_list planExec stackPlanTypes stackPlanOps finite_map

Definition plan_ref_def:
  plan_ref l ops <=>
    MEM (SOPushLabel l) ops \/ MEM (SOPush (Label l)) ops \/
    (?n. MEM (SOPushOfst l n) ops)
End

Theorem plan_ref_append:
  plan_ref l (xs ++ ys) <=> plan_ref l xs \/ plan_ref l ys
Proof
  simp[plan_ref_def, MEM_APPEND] >> metis_tac[]
QED

Theorem asm_label_refs_append:
  asm_label_refs (xs ++ ys) = asm_label_refs xs ++ asm_label_refs ys
Proof
  simp[asm_label_refs_def, MAP_APPEND, FLAT_APPEND]
QED

Theorem exec_stack_op_label_refs:
  MEM l (asm_label_refs (exec_stack_op fmp op)) <=> plan_ref l [op]
Proof
  Cases_on `op` >> simp[exec_stack_op_def, plan_ref_def,
    asm_label_refs_def, MEM_FLAT, MEM_MAP, MEM_REPLICATE] >>
  rename1 `SOPush operand` >> Cases_on `operand` >>
  simp[exec_stack_op_def, asm_label_refs_def]
QED

Theorem exec_stack_op_label:
  MEM (AsmLabel l) (exec_stack_op fmp op) <=> op = SOLabel l
Proof
  Cases_on `op` >> simp[exec_stack_op_def, MEM_REPLICATE, EQ_SYM_EQ] >>
  rename1 `SOPush operand` >> Cases_on `operand` >>
  simp[exec_stack_op_def]
QED

Theorem execute_plan_label_refs:
  MEM l (asm_label_refs (execute_plan fmp ops)) <=> plan_ref l ops
Proof
  Induct_on `ops`
  >- simp[execute_plan_def, asm_label_refs_def, plan_ref_def]
  >> gvs[execute_plan_def, asm_label_refs_append,
         exec_stack_op_label_refs, plan_ref_def]
  >> metis_tac[]
QED

Theorem execute_plan_label:
  MEM (AsmLabel l) (execute_plan fmp ops) <=> MEM (SOLabel l) ops
Proof
  simp[execute_plan_def, MEM_FLAT, MEM_MAP] >>
  metis_tac[exec_stack_op_label]
QED

Theorem plan_ref_closed_append:
  (!l. plan_ref l xs ==> MEM (SOLabel l) xs \/ A l) /\
  (!l. plan_ref l ys ==> MEM (SOLabel l) ys \/ A l) ==>
  !l. plan_ref l (xs ++ ys) ==> MEM (SOLabel l) (xs ++ ys) \/ A l
Proof
  simp[plan_ref_append, MEM_APPEND] >> metis_tac[]
QED

Theorem plan_ref_cons:
  plan_ref l (op::ops) <=> op = SOPushLabel l \/ op = SOPush (Label l) \/
    (?n. op = SOPushOfst l n) \/ plan_ref l ops
Proof
  simp[plan_ref_def] >> metis_tac[]
QED

Theorem plan_ref_nil:
  ~plan_ref l []
Proof
  simp[plan_ref_def]
QED

Theorem plan_ref_fst_cond:
  plan_ref l (FST (if guard then yes else no)) =
  (if guard then plan_ref l (FST yes) else plan_ref l (FST no))
Proof
  Cases_on `guard` >> simp[]
QED

Theorem plan_ref_fst_option:
  plan_ref l (FST (case opt of NONE => absent | SOME x => present x)) =
  (case opt of NONE => plan_ref l (FST absent)
   | SOME x => plan_ref l (FST (present x)))
Proof
  Cases_on `opt` >> simp[]
QED

Theorem do_spill_tos_fst_no_ref:
  ~plan_ref l (FST (do_spill_tos ps))
Proof
  simp[do_spill_tos_def, pairTheory.ELIM_UNCURRY, plan_ref_def]
QED

Theorem do_spill_tos_no_ref:
  do_spill_tos ps = (ops, ps') ==> !l. ~plan_ref l ops
Proof
  metis_tac[do_spill_tos_fst_no_ref, pairTheory.FST]
QED

Theorem do_spill_at_fst_no_ref:
  ~plan_ref l (FST (do_spill_at dist ps))
Proof
  simp[do_spill_at_def, pairTheory.ELIM_UNCURRY, plan_ref_fst_cond,
    plan_ref_append, plan_ref_cons, do_spill_tos_fst_no_ref]
QED

Theorem do_spill_at_no_ref:
  do_spill_at dist ps = (ops, ps') ==> !l. ~plan_ref l ops
Proof
  metis_tac[do_spill_at_fst_no_ref, pairTheory.FST]
QED

Theorem do_restore_fst_no_ref:
  ~plan_ref l (FST (do_restore operand ps))
Proof
  simp[do_restore_def, plan_ref_fst_option, plan_ref_cons, plan_ref_nil] >>
  simp[optionTheory.option_case_compute]
QED

Theorem do_restore_no_ref:
  do_restore operand ps = (ops, ps') ==> !l. ~plan_ref l ops
Proof
  metis_tac[do_restore_fst_no_ref, pairTheory.FST]
QED

Theorem restore_spilled_plan_fst_no_ref:
  !operands ps. ~plan_ref l (FST (restore_spilled_plan operands ps))
Proof
  Induct >> simp[restore_spilled_plan_def, pairTheory.ELIM_UNCURRY,
    plan_ref_append, plan_ref_nil, do_restore_fst_no_ref]
QED

Theorem restore_spilled_plan_no_ref:
  !operands ps ops ps'.
  restore_spilled_plan operands ps = (ops, ps') ==> !l. ~plan_ref l ops
Proof
  metis_tac[restore_spilled_plan_fst_no_ref, pairTheory.FST]
QED

(* A fold only needs a one-step accumulator invariant. *)
Theorem plan_ref_free_foldl:
  !xs initial ops rest.
  FOLDL advance initial xs = (ops, rest) /\
  (!acc x. ~plan_ref l (FST acc) ==> ~plan_ref l (FST (advance acc x))) /\
  ~plan_ref l (FST initial) ==> ~plan_ref l ops
Proof
  Induct >> simp[] >> metis_tac[]
QED

Theorem spill_accumulate_no_ref:
  ~plan_ref l acc_ops ==>
  ~plan_ref l (FST ((\(off, al').
    (acc_ops ++ [SOSpill off], SNOC off offsets, al')) (alloc_spill_slot al)))
Proof
  pairarg_tac >> simp[plan_ref_append, plan_ref_def]
QED

Theorem spill_fold_no_ref:
  !items acc_ops offsets al ops offsets' al'.
  FOLDL (\(ops, offs, al) item.
    (\(off, al'). (ops ++ [SOSpill off], SNOC off offs, al'))
      (alloc_spill_slot al))
    (acc_ops, offsets, al) items = (ops, offsets', al') /\
  ~plan_ref l acc_ops ==> ~plan_ref l ops
Proof
  rpt strip_tac >> drule_at Any plan_ref_free_foldl >>
  simp[pairTheory.FORALL_PROD, spill_accumulate_no_ref, SF SFY_ss]
QED

Theorem spill_fold_fst_no_ref:
  ~plan_ref l acc_ops ==>
  ~plan_ref l (FST (FOLDL (\(ops, offs, al) item.
    (\(off, al'). (ops ++ [SOSpill off], SNOC off offs, al'))
      (alloc_spill_slot al)) (acc_ops, offsets, al) items))
Proof
  Cases_on `FOLDL (\(ops, offs, al) item.
    (\(off, al'). (ops ++ [SOSpill off], SNOC off offs, al'))
      (alloc_spill_slot al)) (acc_ops, offsets, al) items` >>
  metis_tac[spill_fold_no_ref, pairTheory.FST, pairTheory.PAIR]
QED

Theorem do_swap_fst_no_ref:
  ~plan_ref l (FST (do_swap dist ps))
Proof
  simp[do_swap_def, pairTheory.ELIM_UNCURRY, plan_ref_fst_cond,
    plan_ref_append, plan_ref_cons, plan_ref_nil,
    SRULE [pairTheory.ELIM_UNCURRY] spill_fold_fst_no_ref] >>
  simp[plan_ref_def, MEM_MAP]
QED

Theorem do_swap_no_ref:
  do_swap dist ps = (ops, ps') ==> !l. ~plan_ref l ops
Proof
  metis_tac[do_swap_fst_no_ref, pairTheory.FST]
QED

Theorem do_dup_fst_no_ref:
  ~plan_ref l (FST (do_dup dist ps))
Proof
  simp[do_dup_def, pairTheory.ELIM_UNCURRY, plan_ref_fst_cond,
    plan_ref_append, plan_ref_cons, plan_ref_nil,
    SRULE [pairTheory.ELIM_UNCURRY] spill_fold_fst_no_ref] >>
  simp[plan_ref_def, MEM_FLAT, MEM_MAP, PULL_EXISTS,
    COND_RAND, COND_RATOR]
QED

Theorem do_dup_no_ref:
  do_dup dist ps = (ops, ps') ==> !l. ~plan_ref l ops
Proof
  metis_tac[do_dup_fst_no_ref, pairTheory.FST]
QED

(* Sequential generators concatenate their output chunks. *)
Theorem plan_pair_bind_no_ref:
  (!st chunk next_st. produce st = (chunk, next_st) ==> ~plan_ref l chunk) /\
  (!st chunk next_st. continue st = (chunk, next_st) ==> ~plan_ref l chunk) /\
  (\(first_ops, middle_st).
     (\(last_ops, final_st). (first_ops ++ last_ops, final_st))
       (continue middle_st)) (produce ps) = (ops, ps') ==>
  ~plan_ref l ops
Proof
  rpt (pairarg_tac >> gvs[]) >>
  simp[plan_ref_append] >> metis_tac[plan_ref_append]
QED

Theorem reduce_depth_plan_no_ref:
  !fuel target_ops target_op f n ps ops ps'.
  reduce_depth_plan fuel target_ops target_op f n ps = (ops, ps') ==>
  !l. ~plan_ref l ops
Proof
  Induct >- simp[reduce_depth_plan_def, plan_ref_def] >>
  rw[Once reduce_depth_plan_def, AllCaseEqs()] >>
  gvs[plan_ref_def] >>
  metis_tac[plan_pair_bind_no_ref, do_spill_at_no_ref, plan_ref_def]
QED

Theorem reduce_depth_plan_fst_no_ref:
  ~plan_ref l (FST (reduce_depth_plan fuel target_ops operand f n ps))
Proof
  Cases_on `reduce_depth_plan fuel target_ops operand f n ps` >>
  metis_tac[reduce_depth_plan_no_ref, pairTheory.FST]
QED

Theorem reorder_one_fst_no_ref:
  ~plan_ref l (FST (reorder_one dfg target_ops idx operand ps))
Proof
  simp[reorder_one_def, pairTheory.ELIM_UNCURRY,
    plan_ref_fst_cond, plan_ref_fst_option, plan_ref_nil,
    plan_ref_append, do_restore_fst_no_ref,
    do_swap_fst_no_ref, reduce_depth_plan_fst_no_ref] >>
  simp[optionTheory.option_case_compute]
QED

Theorem reorder_one_no_ref:
  reorder_one dfg target_ops idx operand ps = (ops, ps') ==>
  !l. ~plan_ref l ops
Proof
  metis_tac[reorder_one_fst_no_ref, pairTheory.FST]
QED

Theorem reorder_accumulate_no_ref:
  ~plan_ref l acc_ops ==>
  ~plan_ref l (FST ((\(step_ops, next_ps). (acc_ops ++ step_ops, next_ps))
    (reorder_one dfg target_ops idx operand ps)))
Proof
  pairarg_tac >> simp[plan_ref_append] >> metis_tac[reorder_one_no_ref]
QED

Theorem reorder_fold_no_ref:
  !xs acc_ops ps ops ps'.
  FOLDL (\(ops, ps) (idx, operand).
    (\(step_ops, ps'). (ops ++ step_ops, ps'))
      (reorder_one dfg target_ops idx operand ps)) (acc_ops, ps) xs =
    (ops, ps') /\ ~plan_ref l acc_ops ==> ~plan_ref l ops
Proof
  rpt strip_tac >> drule_at Any plan_ref_free_foldl >>
  simp[pairTheory.FORALL_PROD, reorder_accumulate_no_ref, SF SFY_ss]
QED

Theorem reorder_plan_no_ref:
  reorder_plan dfg target_ops ps = (ops, ps') ==> !l. ~plan_ref l ops
Proof
  rw[reorder_plan_def] >>
  drule reorder_fold_no_ref >> simp[plan_ref_nil]
QED

Theorem popmany_swap_accumulate_no_ref:
  ~plan_ref l acc_ops ==>
  ~plan_ref l (FST ((\(swap_ops, next_ps).
    (acc_ops ++ swap_ops ++ [SOPop 1],
     next_ps with ps_stack := stack_pop 1 next_ps.ps_stack))
    (if dist = 0 then ([], ps) else do_swap dist ps)))
Proof
  simp[pairTheory.ELIM_UNCURRY, plan_ref_fst_cond,
    plan_ref_append, plan_ref_cons, plan_ref_nil, do_swap_fst_no_ref]
QED

Theorem popmany_accumulate_no_ref:
  ~plan_ref l acc_ops ==>
  ~plan_ref l (FST (case stack_get_depth v ps.ps_stack of
    NONE => (acc_ops, ps)
  | SOME dist => (\(swap_ops, next_ps).
      (acc_ops ++ swap_ops ++ [SOPop 1],
       next_ps with ps_stack := stack_pop 1 next_ps.ps_stack))
      (if dist = 0 then ([], ps) else do_swap dist ps)))
Proof
  Cases_on `stack_get_depth v ps.ps_stack` >>
  simp[popmany_swap_accumulate_no_ref]
QED

Theorem popmany_fold_no_ref:
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
  ~plan_ref l acc_ops ==> ~plan_ref l ops
Proof
  rpt strip_tac >> drule_at Any plan_ref_free_foldl >>
  simp[pairTheory.FORALL_PROD, popmany_accumulate_no_ref, SF SFY_ss]
QED

Theorem popmany_individual_no_ref:
  popmany_individual to_pop ps = (ops, ps') ==> !l. ~plan_ref l ops
Proof
  rw[popmany_individual_def] >>
  drule popmany_fold_no_ref >> simp[plan_ref_nil]
QED

Theorem popmany_individual_fst_no_ref:
  ~plan_ref l (FST (popmany_individual to_pop ps))
Proof
  Cases_on `popmany_individual to_pop ps` >>
  metis_tac[popmany_individual_no_ref, pairTheory.FST]
QED

Theorem popmany_plan_fst_no_ref:
  ~plan_ref l (FST (popmany_plan to_pop ps))
Proof
  Cases_on `to_pop` >>
  simp[popmany_plan_def, pairTheory.ELIM_UNCURRY, plan_ref_fst_cond,
    plan_ref_append, plan_ref_cons, plan_ref_nil,
    popmany_individual_fst_no_ref, do_swap_fst_no_ref]
QED

Theorem popmany_plan_no_ref:
  popmany_plan to_pop ps = (ops, ps') ==> !l. ~plan_ref l ops
Proof
  metis_tac[popmany_plan_fst_no_ref, pairTheory.FST]
QED

Theorem emit_one_input_fst_refs:
  plan_ref l (FST (emit_one_input opc live operand ps)) ==>
  operand = Label l /\ opc <> INVOKE
Proof
  Cases_on `operand` >>
  simp[emit_one_input_def, pairTheory.ELIM_UNCURRY,
    plan_ref_fst_cond, plan_ref_fst_option, plan_ref_append,
    plan_ref_cons, plan_ref_nil, do_restore_fst_no_ref, do_dup_fst_no_ref] >>
  simp[optionTheory.option_case_compute]
QED

Theorem emit_one_input_refs:
  emit_one_input opc live operand ps = (ops, ps') /\ plan_ref l ops ==>
  operand = Label l /\ opc <> INVOKE
Proof
  metis_tac[emit_one_input_fst_refs, pairTheory.FST]
QED

Theorem emit_input_plan_fst_refs:
  !operands ps.
  plan_ref l (FST (emit_input_plan opc operands live ps)) ==>
  MEM (Label l) operands /\ opc <> INVOKE
Proof
  Induct >> simp[emit_input_plan_def, pairTheory.ELIM_UNCURRY,
    plan_ref_append, plan_ref_nil] >>
  metis_tac[emit_one_input_fst_refs]
QED

Theorem emit_input_plan_refs:
  emit_input_plan opc operands live ps = (ops, ps') /\ plan_ref l ops ==>
  MEM (Label l) operands /\ opc <> INVOKE
Proof
  metis_tac[emit_input_plan_fst_refs, pairTheory.FST]
QED

Theorem optimistic_swap_plan_fst_no_ref:
  ~plan_ref l (FST (optimistic_swap_plan dfg inst live term ps))
Proof
  simp[optimistic_swap_plan_def, plan_ref_fst_cond, plan_ref_fst_option,
    plan_ref_nil, do_swap_fst_no_ref] >>
  simp[optionTheory.option_case_compute]
QED

Theorem optimistic_swap_plan_no_ref:
  optimistic_swap_plan dfg inst live term ps = (ops, ps') ==>
  !l. ~plan_ref l ops
Proof
  metis_tac[optimistic_swap_plan_fst_no_ref, pairTheory.FST]
QED

Theorem generate_phi_plan_fst_no_ref:
  ~plan_ref l (FST (generate_phi_plan inst live halting ps))
Proof
  simp[generate_phi_plan_def, pairTheory.ELIM_UNCURRY,
    plan_ref_fst_option, plan_ref_fst_cond, plan_ref_append,
    plan_ref_cons, plan_ref_nil, do_dup_fst_no_ref, popmany_plan_fst_no_ref] >>
  simp[optionTheory.option_case_compute]
QED

Theorem generate_phi_plan_no_ref:
  generate_phi_plan inst live halting ps = (ops, ps') ==>
  !l. ~plan_ref l ops
Proof
  metis_tac[generate_phi_plan_fst_no_ref, pairTheory.FST]
QED

Theorem prepare_params_plan_fst_no_ref:
  ~plan_ref l (FST (prepare_params_plan liveness fn ps))
Proof
  simp[prepare_params_plan_def, pairTheory.ELIM_UNCURRY,
    plan_ref_fst_cond, plan_ref_append, plan_ref_nil,
    popmany_plan_fst_no_ref, optimistic_swap_plan_fst_no_ref]
QED

Theorem prepare_params_plan_no_ref:
  prepare_params_plan liveness fn ps = (ops, ps') ==>
  !l. ~plan_ref l ops
Proof
  metis_tac[prepare_params_plan_fst_no_ref, pairTheory.FST]
QED

Theorem clean_stack_plan_fst_no_ref:
  ~plan_ref l (FST (clean_stack_plan liveness cfg fn bb ps))
Proof
  simp[clean_stack_plan_def, list_case_compute, pairTheory.ELIM_UNCURRY,
    plan_ref_fst_cond, plan_ref_fst_option, plan_ref_append,
    plan_ref_nil, popmany_plan_fst_no_ref] >>
  simp[optionTheory.option_case_compute]
QED

Theorem clean_stack_plan_no_ref:
  clean_stack_plan liveness cfg fn bb ps = (ops, ps') ==>
  !l. ~plan_ref l ops
Proof
  metis_tac[clean_stack_plan_fst_no_ref, pairTheory.FST]
QED

Theorem invoke_operands_wf_hd_mem:
  invoke_operands_wf inst ==> MEM (HD inst.inst_operands) inst.inst_operands
Proof
  Cases_on `inst.inst_operands` >> simp[invoke_operands_wf_def]
QED

Theorem generate_emit_ops_refs:
  generate_emit_ops inst topics ps = (ops, ps') /\
  (inst.inst_opcode = INVOKE ==> invoke_operands_wf inst) /\
  plan_ref l ops ==>
  MEM (SOLabel l) ops \/ l = "revert" \/
  (MEM inst.inst_opcode [JMP; JNZ; INVOKE] /\ MEM (Label l) inst.inst_operands)
Proof
  rw[generate_emit_ops_def, bump_emit_ops_def,
    pairTheory.ELIM_UNCURRY, AllCaseEqs()] >>
  gvs[plan_ref_def] >>
  metis_tac[invoke_operands_wf_hd_mem, MEM_FILTER, MEM]
QED

Theorem label_positions_ok_add_refs:
  inst.inst_opcode = ADD /\ label_positions_ok inst /\
  MEM (Label l) inst.inst_operands ==> l = "code_end"
Proof
  rw[label_positions_ok_def, CasePreds ["list", "operand"]] >>
  gvs[EVERY_MEM, is_label_operand_def] >> metis_tac[is_label_operand_def]
QED

Theorem label_positions_ok_codecopy_refs:
  inst.inst_opcode = CODECOPY /\ label_positions_ok inst /\
  MEM (Label l) inst.inst_operands ==> l = "runtime_begin"
Proof
  rw[label_positions_ok_def, CasePreds ["list", "operand"]] >>
  gvs[EVERY_MEM, is_label_operand_def] >> metis_tac[is_label_operand_def]
QED

Theorem label_positions_ok_refs:
  label_positions_ok inst /\ inst.inst_opcode <> PHI /\
  MEM (Label l) inst.inst_operands ==>
  l = "code_end" \/ l = "runtime_begin" \/
  MEM inst.inst_opcode [JMP; JNZ; INVOKE]
Proof
  strip_tac >>
  Cases_on `MEM inst.inst_opcode [JMP; JNZ; PHI; INVOKE; ADD; CODECOPY]`
  >- (gvs[] >> metis_tac[label_positions_ok_add_refs,
        label_positions_ok_codecopy_refs]) >>
  drule_all label_positions_ok_other >>
  disch_then (qspec_then `Label l` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
  simp[is_label_operand_def]
QED

Theorem reorder_plan_fst_no_ref:
  ~plan_ref l (FST (reorder_plan dfg operands ps))
Proof
  Cases_on `reorder_plan dfg operands ps` >>
  metis_tac[reorder_plan_no_ref, pairTheory.FST]
QED

Theorem regular_join_fst_no_ref:
  ~plan_ref l (FST (if opc = JMP then
    case join_target_ops liveness fn bb inst of
      NONE => ([], ps)
    | SOME targets => (\(restore_ops, restored).
        (\(swap_ops, arranged). (restore_ops ++ swap_ops, arranged))
          (reorder_plan dfg targets restored))
        (restore_spilled_plan targets ps)
    else ([], ps)))
Proof
  simp[pairTheory.ELIM_UNCURRY, plan_ref_fst_cond, plan_ref_fst_option,
    plan_ref_append, plan_ref_nil, restore_spilled_plan_fst_no_ref,
    reorder_plan_fst_no_ref] >>
  simp[optionTheory.option_case_compute]
QED

Theorem generate_regular_inst_plan_refs:
  generate_regular_inst_plan liveness dfg cfg fn inst live halting term bb ps =
    (ops, ps') /\
  (inst.inst_opcode = INVOKE ==> invoke_operands_wf inst) /\
  plan_ref l ops ==>
  MEM (SOLabel l) ops \/ l = "revert" \/
  MEM (Label l) (compute_operands inst) \/
  (MEM inst.inst_opcode [JMP; JNZ; INVOKE] /\ MEM (Label l) inst.inst_operands)
Proof
  pure_rewrite_tac[generate_regular_inst_plan_def, LET_THM] >>
  rpt (pairarg_tac >> fs[]) >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `generate_emit_ops inst topics emit_ps = _` >>
  `~plan_ref l join_ops` by
    (qpat_x_assum `_ = (join_ops, ps2)`
       (mp_tac o AP_TERM ``FST : stack_op list # plan_state -> stack_op list``) >>
     simp_tac std_ss [] >>
     metis_tac[regular_join_fst_no_ref]) >>
  qpat_x_assum `Abbrev (topics = _)` kall_tac >>
  qpat_x_assum `Abbrev (emit_ps = _)` kall_tac >>
  qpat_x_assum `_ = (join_ops, ps2)` kall_tac >>
  imp_res_tac reorder_plan_no_ref >>
  `~plan_ref l reorder_ops` by
    (qpat_x_assum `_ = (reorder_ops, ps4)`
       (mp_tac o AP_TERM ``\p : stack_op list # plan_state. plan_ref l (FST p)``) >>
     simp[plan_ref_fst_cond]) >>
  `~plan_ref l pop_ops` by
    (qpat_x_assum `_ = (pop_ops, ps8)`
       (mp_tac o AP_TERM ``\p : stack_op list # plan_state. plan_ref l (FST p)``) >>
     simp[plan_ref_fst_cond, plan_ref_nil, popmany_plan_fst_no_ref]) >>
  `~plan_ref l opt_ops` by
    (qpat_x_assum `_ = (opt_ops, ps9)`
       (mp_tac o AP_TERM ``\p : stack_op list # plan_state. plan_ref l (FST p)``) >>
     simp[plan_ref_fst_cond, plan_ref_nil, optimistic_swap_plan_fst_no_ref]) >>
  qpat_x_assum `_ = (ops, ps')` mp_tac >>
  simp[CaseEq "bool"] >> strip_tac >>
  gvs[plan_ref_append, MEM_APPEND] >>
  metis_tac[emit_input_plan_refs, generate_emit_ops_refs, MEM]
QED

Theorem shaped_compute_operands_refs:
  inst_shape_ok inst /\ inst.inst_opcode <> PHI /\
  MEM (Label l) (compute_operands inst) ==>
  l = "code_end" \/
  (l = "runtime_begin" /\ MEM (Label "runtime_begin") inst.inst_operands)
Proof
  strip_tac >> drule compute_operands_labels >> strip_tac >>
  gvs[inst_shape_ok_def] >>
  drule_all label_positions_ok_refs >> simp[] >> metis_tac[]
QED

Theorem generate_inst_plan_refs:
  generate_inst_plan liveness dfg cfg fn inst live halting term bb ps =
    SOME (ops, ps') /\ inst_shape_ok inst /\ plan_ref l ops ==>
  MEM (SOLabel l) ops \/ l = "revert" \/
  (MEM inst.inst_opcode [JMP; JNZ; INVOKE] /\ MEM (Label l) inst.inst_operands) \/
  l = "code_end" \/
  (l = "runtime_begin" /\ MEM (Label "runtime_begin") inst.inst_operands)
Proof
  strip_tac >>
  `inst.inst_opcode <> OFFSET` by gvs[inst_shape_ok_def] >>
  gvs[generate_inst_plan_def, CaseEq "bool", plan_ref_nil] >>
  imp_res_tac generate_phi_plan_no_ref >> gvs[] >>
  drule_all generate_regular_inst_plan_refs >> simp[] >>
  metis_tac[shaped_compute_operands_refs]
QED

Theorem generate_block_insts_plan_refs:
  !insts i ps ops ps'.
  generate_block_insts_plan liveness dfg cfg fn bb_label halting
    n_params block_len i insts ps = SOME (ops, ps') /\
  EVERY inst_shape_ok insts /\ plan_ref l ops ==>
  MEM (SOLabel l) ops \/ l = "revert" \/
  (?inst. MEM inst insts /\ MEM inst.inst_opcode [JMP; JNZ; INVOKE] /\
          MEM (Label l) inst.inst_operands) \/
  l = "code_end" \/
  (l = "runtime_begin" /\
   ?inst. MEM inst insts /\ MEM (Label "runtime_begin") inst.inst_operands)
Proof
  Induct >- simp[generate_block_insts_plan_def, plan_ref_nil] >>
  rw[generate_block_insts_plan_def, AllCaseEqs()] >>
  gvs[plan_ref_append, MEM_APPEND] >>
  FIRST [drule_all generate_inst_plan_refs,
    first_x_assum (drule_at Any)] >>
  simp[] >> metis_tac[]
QED

Theorem generate_block_plan_refs:
  generate_block_plan liveness dfg cfg fn bb ps = SOME (ops, ps') /\
  EVERY inst_shape_ok bb.bb_instructions /\ plan_ref l ops ==>
  MEM (SOLabel l) ops \/ l = "revert" \/
  (?inst. MEM inst bb.bb_instructions /\
          MEM inst.inst_opcode [JMP; JNZ; INVOKE] /\
          MEM (Label l) inst.inst_operands) \/
  l = "code_end" \/
  (l = "runtime_begin" /\
   ?inst. MEM inst bb.bb_instructions /\
          MEM (Label "runtime_begin") inst.inst_operands)
Proof
  pure_rewrite_tac[generate_block_plan_def, LET_THM] >>
  rpt (pairarg_tac >> fs[]) >>
  strip_tac >>
  `~plan_ref l param_ops` by
    (qpat_x_assum `_ = (param_ops, ps1)`
       (mp_tac o AP_TERM ``\p : stack_op list # plan_state. plan_ref l (FST p)``) >>
     simp[plan_ref_fst_cond, plan_ref_nil, prepare_params_plan_fst_no_ref]) >>
  `~plan_ref l clean_ops` by
    (qpat_x_assum `_ = (clean_ops, ps2)`
       (mp_tac o AP_TERM ``\p : stack_op list # plan_state. plan_ref l (FST p)``) >>
     simp[plan_ref_fst_cond, plan_ref_nil, clean_stack_plan_fst_no_ref]) >>
  `EVERY inst_shape_ok (non_param_insts bb)` by
    (gvs[non_param_insts_def, EVERY_MEM, MEM_FILTER] >> metis_tac[]) >>
  qpat_x_assum `_ = (param_ops, ps1)` kall_tac >>
  qpat_x_assum `_ = (clean_ops, ps2)` kall_tac >>
  gvs[AllCaseEqs(), plan_ref_cons, plan_ref_append, MEM_APPEND] >>
  drule_all generate_block_insts_plan_refs >>
  simp[non_param_insts_def, MEM_FILTER] >> metis_tac[]
QED

Definition generated_block_ref_slice_def:
  generated_block_ref_slice lv dfg cfg fn l visited ops <=>
    ?lbl bb start chunk stop pre post.
      lookup_block lbl fn.fn_blocks = SOME bb /\ MEM lbl visited /\
      generate_block_plan lv dfg cfg fn bb start = SOME (chunk, stop) /\
      plan_ref l chunk /\ ops = pre ++ chunk ++ post
End

Theorem generated_block_ref_slice_self:
  lookup_block lbl fn.fn_blocks = SOME bb /\ MEM lbl visited /\
  generate_block_plan lv dfg cfg fn bb ps = SOME (ops, ps') /\ plan_ref l ops ==>
  generated_block_ref_slice lv dfg cfg fn l visited ops
Proof
  strip_tac >> simp[generated_block_ref_slice_def] >>
  qexistsl [`lbl`, `bb`, `ps`, `ops`, `ps'`, `[]`, `[]`] >> simp[]
QED

Theorem generated_block_ref_slice_transport:
  generated_block_ref_slice lv dfg cfg fn l visited ops /\
  set visited SUBSET set final ==>
  generated_block_ref_slice lv dfg cfg fn l final (before ++ ops ++ after)
Proof
  rw[generated_block_ref_slice_def, pred_setTheory.SUBSET_DEF] >>
  qexistsl [`lbl`, `bb`, `start`, `chunk`, `stop`, `before ++ pre`, `post ++ after`] >>
  simp[APPEND_ASSOC]
QED

Theorem generated_block_ref_slice_append:
  (!l. plan_ref l xs ==> generated_block_ref_slice lv dfg cfg fn l seen_x xs) /\
  (!l. plan_ref l ys ==> generated_block_ref_slice lv dfg cfg fn l seen_y ys) /\
  set seen_x SUBSET set final /\ set seen_y SUBSET set final ==>
  !l. plan_ref l (xs ++ ys) ==> generated_block_ref_slice lv dfg cfg fn l final (xs ++ ys)
Proof
  rw[plan_ref_append]
  >- (`generated_block_ref_slice lv dfg cfg fn l final ([] ++ xs ++ ys)`
        suffices_by simp[] >>
      irule generated_block_ref_slice_transport >> metis_tac[]) >>
  `generated_block_ref_slice lv dfg cfg fn l final (xs ++ ys ++ [])`
    suffices_by simp[] >>
  irule generated_block_ref_slice_transport >> metis_tac[]
QED

Theorem generated_block_ref_succ_append:
  generate_succs_plan lv dfg cfg fn ss sp succs seen ps = SOME (ys, final, ps') /\
  (!l. plan_ref l xs ==> generated_block_ref_slice lv dfg cfg fn l seen xs) /\
  (!l. plan_ref l ys ==> generated_block_ref_slice lv dfg cfg fn l final ys) ==>
  !l. plan_ref l (xs ++ ys) ==> generated_block_ref_slice lv dfg cfg fn l final (xs ++ ys)
Proof
  strip_tac >> drule generate_succs_plan_visited_mono >> strip_tac >>
  rpt strip_tac >> irule generated_block_ref_slice_append >>
  metis_tac[pred_setTheory.SUBSET_REFL]
QED

Theorem generated_block_ref_aux_append:
  generate_fn_plan_aux lv dfg cfg fn wl seen ps = SOME (ys, final, ps') /\
  (!l. plan_ref l xs ==> generated_block_ref_slice lv dfg cfg fn l seen xs) /\
  (!l. plan_ref l ys ==> generated_block_ref_slice lv dfg cfg fn l final ys) ==>
  !l. plan_ref l (xs ++ ys) ==> generated_block_ref_slice lv dfg cfg fn l final (xs ++ ys)
Proof
  strip_tac >> drule generate_fn_plan_aux_visited_mono >> strip_tac >>
  rpt strip_tac >> irule generated_block_ref_slice_append >>
  metis_tac[pred_setTheory.SUBSET_REFL]
QED

Theorem generated_block_ref_block_successors:
  lookup_block lbl fn.fn_blocks = SOME bb /\
  generate_block_plan lv dfg cfg fn bb ps = SOME (bops, pout) /\
  generate_succs_plan lv dfg cfg fn ss sp succs (lbl::visited) pout = SOME (sops, seen, pmid) /\
  (!l. plan_ref l sops ==> generated_block_ref_slice lv dfg cfg fn l seen sops) ==>
  !l. plan_ref l (bops ++ sops) ==>
    generated_block_ref_slice lv dfg cfg fn l seen (bops ++ sops)
Proof
  rpt strip_tac >> irule generated_block_ref_succ_append >>
  metis_tac[generated_block_ref_slice_self, MEM]
QED

Theorem generated_block_ref_block_continuation:
  lookup_block lbl fn.fn_blocks = SOME bb /\
  generate_block_plan lv dfg cfg fn bb ps = SOME (bops, pout) /\
  generate_succs_plan lv dfg cfg fn ss sp succs (lbl::visited) pout = SOME (sops, seen, pmid) /\
  generate_fn_plan_aux lv dfg cfg fn wl seen pmid = SOME (rops, final, pend) /\
  (!l. plan_ref l sops ==> generated_block_ref_slice lv dfg cfg fn l seen sops) /\
  (!l. plan_ref l rops ==> generated_block_ref_slice lv dfg cfg fn l final rops) ==>
  !l. plan_ref l (bops ++ sops ++ rops) ==>
    generated_block_ref_slice lv dfg cfg fn l final (bops ++ sops ++ rops)
Proof
  strip_tac >>
  `!l. plan_ref l (bops ++ sops) ==>
       generated_block_ref_slice lv dfg cfg fn l seen (bops ++ sops)` by
    metis_tac[generated_block_ref_block_successors] >>
  rpt strip_tac >> gvs[APPEND_ASSOC] >>
  irule generated_block_ref_aux_append >> metis_tac[]
QED

Theorem traversal_generated_block_ref_slice:
  (!lv dfg cfg fn wl visited ps ops final ps'.
    generate_fn_plan_aux lv dfg cfg fn wl visited ps = SOME (ops, final, ps') ==>
    !l. plan_ref l ops ==> generated_block_ref_slice lv dfg cfg fn l final ops) /\
  (!lv dfg cfg fn ss sp succs visited ps ops final ps'.
    generate_succs_plan lv dfg cfg fn ss sp succs visited ps = SOME (ops, final, ps') ==>
    !l. plan_ref l ops ==> generated_block_ref_slice lv dfg cfg fn l final ops)
Proof
  ho_match_mp_tac generate_fn_plan_aux_ind >> rpt conj_tac
  >- simp[Once generate_fn_plan_aux_def, plan_ref_nil]
  >- suspend "aux"
  >- simp[Once generate_fn_plan_aux_def, plan_ref_nil]
  >> suspend "succ"
QED

Resume traversal_generated_block_ref_slice[aux]:
  rw[Once generate_fn_plan_aux_def, AllCaseEqs()] >> gvs[] >>
  metis_tac[generated_block_ref_block_continuation]
QED

Resume traversal_generated_block_ref_slice[succ]:
  rw[Once (cj 4 generate_fn_plan_aux_def), AllCaseEqs()] >> gvs[] >>
  metis_tac[generated_block_ref_succ_append]
QED
Finalise traversal_generated_block_ref_slice

Theorem traversal_reference_block:
  (!lv dfg cfg fn wl visited ps ops final ps'.
    generate_fn_plan_aux lv dfg cfg fn wl visited ps = SOME (ops, final, ps') ==>
    !l. plan_ref l ops ==>
    ?lbl bb start chunk stop pre post.
      lookup_block lbl fn.fn_blocks = SOME bb /\ MEM lbl final /\
      generate_block_plan lv dfg cfg fn bb start = SOME (chunk, stop) /\
      plan_ref l chunk /\ ops = pre ++ chunk ++ post) /\
  (!lv dfg cfg fn ss sp succs visited ps ops final ps'.
    generate_succs_plan lv dfg cfg fn ss sp succs visited ps = SOME (ops, final, ps') ==>
    !l. plan_ref l ops ==>
    ?lbl bb start chunk stop pre post.
      lookup_block lbl fn.fn_blocks = SOME bb /\ MEM lbl final /\
      generate_block_plan lv dfg cfg fn bb start = SOME (chunk, stop) /\
      plan_ref l chunk /\ ops = pre ++ chunk ++ post)
Proof
  mp_tac traversal_generated_block_ref_slice >> simp[generated_block_ref_slice_def]
QED

Theorem entry_traversal_label_mem:
  generate_fn_plan_aux lv dfg cfg fn [entry] [] ps = SOME (ops, final, ps') /\
  fn_entry_label fn = SOME entry /\ MEM lbl final /\
  lookup_block lbl fn.fn_blocks = SOME bb ==>
  MEM (SOLabel lbl) ops
Proof
  strip_tac >> drule (cj 1 traversal_dfs_witness) >>
  disch_then (qspec_then `ps` mp_tac) >>
  simp[fnPlanLineageTheory.dfs_aux_call_rules] >>
  disch_then drule_all >> strip_tac >>
  drule_all fnPlanPlaceDfsBlockTheory.lookup_block_plan_leading_label >>
  strip_tac >> gvs[MEM_APPEND]
QED

Theorem block_jump_ref_successor:
  bb_well_formed bb /\ MEM inst bb.bb_instructions /\
  MEM inst.inst_opcode [JMP; JNZ] /\ MEM (Label l) inst.inst_operands ==>
  MEM l (bb_succs bb)
Proof
  strip_tac >>
  `is_terminator inst.inst_opcode` by gvs[venomInstTheory.is_terminator_def] >>
  drule_all simplifyCfgStructTheory.bb_well_formed_terminator_last >>
  strip_tac >>
  gvs[venomInstTheory.bb_succs_def, bb_well_formed_def,
      simplifyCfgStructTheory.get_successors_mem_label, MEM_nub] >>
  Cases_on `bb.bb_instructions` >>
  gvs[MEM_nub, simplifyCfgStructTheory.get_successors_mem_label]
QED

Theorem ready_fn_jump_edge:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM inst bb.bb_instructions /\ MEM inst.inst_opcode [JMP; JNZ] /\
  MEM (Label l) inst.inst_operands ==> fn_cfg_edge fn lbl l
Proof
  strip_tac >>
  drule simplifyCfgDefsTheory.lookup_block_member_label >> strip_tac >>
  `bb_well_formed bb` by metis_tac[genBlockSimTheory.bb_well_formed_from_ready] >>
  drule_all block_jump_ref_successor >> simp[fn_cfg_edge_def] >> metis_tac[]
QED

Theorem ready_fn_edge_target_lookup:
  codegen_ready_fn fn /\ fn_cfg_edge fn lbl l ==>
  ?target. lookup_block l fn.fn_blocks = SOME target
Proof
  rw[codegen_ready_fn_def, wf_function_def, fn_cfg_edge_def] >>
  `MEM l (fn_labels fn)` by metis_tac[fn_succs_closed_def] >>
  gvs[venomInstTheory.fn_labels_def] >>
  drule dfAnalyzeProofsTheory.lookup_block_exists >> metis_tac[]
QED

Theorem entry_traversal_edge_target:
  generate_fn_plan_aux lv dfg (cfg_analyze fn) fn [entry] [] ps = SOME (ops, final, ps') /\
  codegen_ready_fn fn /\ MEM lbl final /\ fn_cfg_edge fn lbl l ==>
  MEM l final /\ ?target. lookup_block l fn.fn_blocks = SOME target
Proof
  strip_tac >> drule_all ready_fn_cfg_edge >> strip_tac >>
  drule (cj 1 traversal_visited_closed) >> simp[] >> strip_tac >>
  conj_tac >- metis_tac[] >>
  metis_tac[ready_fn_edge_target_lookup]
QED

Theorem entry_traversal_jump_target:
  generate_fn_plan_aux lv dfg (cfg_analyze fn) fn [entry] [] ps = SOME (ops, final, ps') /\
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\ MEM lbl final /\
  MEM inst bb.bb_instructions /\ MEM inst.inst_opcode [JMP; JNZ] /\
  MEM (Label l) inst.inst_operands ==>
  MEM l final /\ ?target. lookup_block l fn.fn_blocks = SOME target
Proof
  strip_tac >>
  drule simplifyCfgDefsTheory.lookup_block_member_label >> strip_tac >>
  `bb_well_formed bb /\ fn_succs_closed fn` by
    (gvs[codegen_ready_fn_def, wf_function_def] >> metis_tac[]) >>
  drule_all block_jump_ref_successor >> strip_tac >>
  `fn_cfg_edge fn lbl l` by (simp[fn_cfg_edge_def] >> metis_tac[]) >>
  drule_all ready_fn_cfg_edge >> strip_tac >>
  drule (cj 1 traversal_visited_closed) >> simp[] >> strip_tac >>
  conj_tac >- metis_tac[] >>
  `MEM l (fn_labels fn)` by metis_tac[fn_succs_closed_def] >>
  gvs[venomInstTheory.fn_labels_def] >>
  drule dfAnalyzeProofsTheory.lookup_block_exists >> metis_tac[]
QED

Theorem entry_traversal_jump_label_mem:
  generate_fn_plan_aux lv dfg (cfg_analyze fn) fn [entry] [] ps = SOME (ops, final, ps') /\
  fn_entry_label fn = SOME entry /\ codegen_ready_fn fn /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ MEM lbl final /\
  MEM inst bb.bb_instructions /\ MEM inst.inst_opcode [JMP; JNZ] /\
  MEM (Label l) inst.inst_operands ==>
  MEM (SOLabel l) ops
Proof
  strip_tac >> drule_all entry_traversal_jump_target >> strip_tac >>
  irule entry_traversal_label_mem >> metis_tac[]
QED

Theorem entry_traversal_refs:
  generate_fn_plan_aux lv dfg (cfg_analyze fn) fn [entry] [] ps = SOME (ops, final, ps') /\
  fn_entry_label fn = SOME entry /\ fn_shape_ok fn /\ codegen_ready_fn fn /\
  plan_ref l ops ==>
  MEM (SOLabel l) ops \/ l = "revert" \/ l = "code_end" \/
  (l = "runtime_begin" /\
   ?inst. MEM inst (fn_insts fn) /\ MEM (Label "runtime_begin") inst.inst_operands) \/
  (?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
          MEM (Label l) inst.inst_operands)
Proof
  strip_tac >> drule (cj 1 traversal_reference_block) >>
  disch_then drule >> strip_tac >>
  drule simplifyCfgDefsTheory.lookup_block_member_label >> strip_tac >>
  `EVERY inst_shape_ok bb.bb_instructions` by
    (gvs[fn_shape_ok_def, EVERY_MEM, venomInstTheory.fn_insts_def,
         MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  drule_all generate_block_plan_refs >> strip_tac >>
  gvs[MEM_APPEND]
  >- (disj1_tac >> rewrite_tac[GSYM MEM_APPEND] >>
      irule entry_traversal_jump_label_mem >> simp[] >> metis_tac[])
  >- (disj1_tac >> rewrite_tac[GSYM MEM_APPEND] >>
      irule entry_traversal_jump_label_mem >> simp[] >> metis_tac[]) >>
  simp[venomInstTheory.fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]
QED

Theorem generate_fn_plan_with_cleanup_refs:
  generate_fn_plan_with_cleanup ch growth fn sb lc = SOME (ops, ps') /\
  fn_shape_ok fn /\ codegen_ready_fn fn /\ plan_ref l ops ==>
  MEM (SOLabel l) ops \/ l = "revert" \/ l = "code_end" \/
  (l = "runtime_begin" /\
   ?inst. MEM inst (fn_insts fn) /\ MEM (Label "runtime_begin") inst.inst_operands) \/
  (?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
          MEM (Label l) inst.inst_operands)
Proof
  strip_tac >>
  `fn_entry_label fn = SOME fn.fn_name` by gvs[fn_shape_ok_def] >>
  gvs[generate_fn_plan_with_cleanup_def] >>
  drule_all cleanup_plan_entry_call >> strip_tac >>
  drule_all entry_traversal_refs >> simp[]
QED

Theorem generate_fn_plan_with_cleanup_entry_label:
  generate_fn_plan_with_cleanup ch growth fn sb lc = SOME (ops, ps') /\
  fn_shape_ok fn ==>
  MEM (SOLabel fn.fn_name) ops
Proof
  strip_tac >>
  `fn_entry_label fn = SOME fn.fn_name` by gvs[fn_shape_ok_def] >>
  gvs[generate_fn_plan_with_cleanup_def] >>
  drule fnPlanPlaceFnRegionTheory.generate_fn_plan_with_cleanup_analyzed_leading_label >>
  strip_tac >> gvs[venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def,
                  AllCaseEqs()]
QED

Theorem codegen_asm_static_wf:
  codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
  sym_unit_static_ok unit /\ codegen_ready unit.cu_context ==>
  asm_static_wf prog
Proof
  cheat
QED
