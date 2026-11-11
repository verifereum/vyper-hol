Theory abiArgsObservation
Ancestors
  fragExec venomExecProps venomExecProofs venomExecSemantics venomState
  venomInstProofs1 venomInst

(* State-bearing results expose the immutable label environment. *)
Definition abi_result_labels_def:
  abi_result_labels labels r <=>
    case r of
      OK s => s.vs_labels = labels
    | Halt s => s.vs_labels = labels
    | Abort a s => s.vs_labels = labels
    | IntRet vals s => s.vs_labels = labels
    | Error e => T
End

Theorem abi_setup_callee_labels[local]:
  setup_callee fn args s = SOME t ==> t.vs_labels = s.vs_labels
Proof
  simp[setup_callee_def] >> IF_CASES_TAC >> simp[] >> strip_tac >> gvs[]
QED

Theorem abi_merge_callee_labels[local]:
  (merge_callee_state s t).vs_labels = s.vs_labels
Proof
  simp[merge_callee_state_def]
QED

Theorem abi_phis_labels[local]:
  eval_phis s insts = OK t ==> t.vs_labels = s.vs_labels
Proof
  strip_tac >> drule eval_phis_only_updates_vs_vars >>
  disch_then (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem abi_step_base_ok_labels[local]:
  step_inst_base inst s = OK t ==> t.vs_labels = s.vs_labels
Proof
  strip_tac >> drule step_inst_base_OK_not_INVOKE >> strip_tac >>
  `step_inst 0 ctx inst s = OK t` by
    simp[step_inst_non_invoke] >>
  metis_tac[step_inst_preserves_labels_always]
QED

(* Select one exported opcode equation; never simplify the whole dispatcher. *)
val abi_opcode_equations = CONJUNCTS step_inst_base_opcode_eqs;
fun abi_rewrite_opcode eq = let
  val opc = rhs (concl eq)
  fun matches th = aconv opc (rhs (fst (dest_imp (snd (strip_forall (concl th))))))
  val branch = valOf (List.find matches abi_opcode_equations)
in once_rewrite_tac [MATCH_MP branch eq] end;

val abi_result_shape_simp = let
  val test = ``abi_result_labels labels``
  val shapes = [``:operand list``, ``:operand``, ``:string list``, ``:256 word option``, ``:num # num``, ``:(num # num) option``]
  val distribute = map (fn ty =>
    BETA_RULE (ISPEC test (TypeBase.case_rand_of ty))) shapes
  val constants = map (fn ty => Prim_rec.prove_case_const_thm
    {case_def = TypeBase.case_def_of ty,
     nchotomy = TypeBase.nchotomy_of ty}) shapes
  val conditional = BETA_RULE
    (PART_MATCH (rator o lhs) COND_RAND test)
in simp_tac (srw_ss() ++ rewrites
     (distribute @ constants @ [conditional, abi_result_labels_def,
       update_var_def, halt_state_def, revert_state_def,
       set_returndata_def, jump_to_def, LET_THM,
       mstore_def, mstore8_def, sstore_def, tstore_def, istore_def,
       write_memory_with_expansion_def, mcopy_def])) [] end;

Theorem abi_delegatecall_labels[local]:
  abi_result_labels s.vs_labels (exec_delegatecall inst s gas addr ao az ro rz)
Proof
  simp[exec_delegatecall_def] >>
  Cases_on `inst.inst_outputs` >> abi_result_shape_simp
QED

Theorem abi_create_labels[local]:
  abi_result_labels s.vs_labels (exec_create inst s value offset sz salt_opt)
Proof
  simp[exec_create_def] >>
  Cases_on `inst.inst_outputs` >> abi_result_shape_simp
QED

Theorem abi_exec_gas_labels[local]:
  abi_result_labels s.vs_labels (exec_gas inst s)
Proof
  simp[exec_gas_def] >> rpt BasicProvers.TOP_CASE_TAC >>
  simp[abi_result_labels_def, update_var_def]
QED

Theorem abi_step_base_labels:
  abi_result_labels s.vs_labels (step_inst_base inst s)
Proof
  Cases_on `inst.inst_opcode` >>
  qpat_assum `inst.inst_opcode = _` abi_rewrite_opcode >>
  simp[exec_pure1_def, exec_pure2_def, exec_pure3_def,
       exec_read0_def, exec_read1_def, exec_write2_def,
       exec_alloca_def, exec_ext_call_def] >>
  abi_result_shape_simp >>
  simp[REWRITE_RULE [abi_result_labels_def] abi_exec_gas_labels,
       REWRITE_RULE [abi_result_labels_def] abi_delegatecall_labels,
       REWRITE_RULE [abi_result_labels_def] abi_create_labels] >>
  abi_result_shape_simp
  >- (strip_tac >>
      Cases_on `parse_dret_shape inst` >> simp[] >>
      PairCases_on `x` >> simp[] >>
      Cases_on `eval_operands inst.inst_operands s` >> simp[] >>
      Cases_on `pair_dret_words (TAKE (2 * x1) (DROP (x0 + 1) x))` >> simp[] >>
      pairarg_tac >> simp[] >>
      drule pack_dret_dynamic_preserves_non_memory >> simp[])
QED

Theorem abi_fold_outputs_labels[local]:
  !kvs s. (FOLDL (\s' (k,v). update_var k v s') s kvs).vs_labels = s.vs_labels
Proof
  Induct >- simp[] >>
  simp[pairTheory.FORALL_PROD] >> rpt gen_tac >>
  first_x_assum (qspec_then `update_var p_1 p_2 s` mp_tac) >>
  simp[update_var_def]
QED

Theorem abi_bind_labels[local]:
  bind_outputs outs vals s = SOME t ==> t.vs_labels = s.vs_labels
Proof
  simp[bind_outputs_def] >>
  strip_tac >> gvs[abi_fold_outputs_labels]
QED

Theorem abi_adopt_labels[local]:
  (adopt_return_fmp ret s).vs_labels = s.vs_labels
Proof
  Cases_on `ret.iret_adopt_fmp` >> simp[adopt_return_fmp_def]
QED

Theorem abi_run_labels:
  (!fuel ctx inst s. abi_result_labels s.vs_labels (step_inst fuel ctx inst s)) /\
  (!fuel ctx bb s. abi_result_labels s.vs_labels (exec_block fuel ctx bb s)) /\
  (!fuel ctx fn s. abi_result_labels s.vs_labels (run_blocks fuel ctx fn s))
Proof
  ho_match_mp_tac run_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "run"
QED

Resume abi_run_labels[step]:
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[step_inst_def] >>
  Cases_on `inst.inst_opcode = INVOKE` >- suspend "invoke" >>
  simp[abi_step_base_labels]
QED

Resume abi_run_labels[invoke]:
  simp[] >>
  Cases_on `decode_invoke inst` >- simp[abi_result_labels_def] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `lookup_function x0 ctx.ctx_functions` >- simp[abi_result_labels_def] >>
  Cases_on `eval_operands x1 s` >- simp[abi_result_labels_def] >>
  rename1 `lookup_function x0 ctx.ctx_functions = SOME callee` >>
  rename1 `eval_operands x1 s = SOME args` >>
  Cases_on `setup_callee callee args s` >- simp[abi_result_labels_def] >>
  rename1 `setup_callee callee args s = SOME cs` >>
  `cs.vs_labels = s.vs_labels` by metis_tac[abi_setup_callee_labels] >>
  `abi_result_labels cs.vs_labels (run_blocks fuel ctx callee cs)` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  Cases_on `run_blocks fuel ctx callee cs` >>
  gvs[abi_result_labels_def] >>
  Cases_on `bind_outputs inst.inst_outputs i.iret_values
    (adopt_return_fmp i (merge_callee_state s v))` >>
  gvs[abi_result_labels_def] >>
  drule abi_bind_labels >> simp[abi_adopt_labels, abi_merge_callee_labels]
QED

Resume abi_run_labels[block]:
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >- simp[abi_result_labels_def] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `abi_result_labels s.vs_labels (step_inst fuel ctx inst s)` by metis_tac[] >>
  Cases_on `step_inst fuel ctx inst s` >> gvs[abi_result_labels_def] >>
  IF_CASES_TAC >- (IF_CASES_TAC >> simp[abi_result_labels_def]) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Resume abi_run_labels[run]:
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[run_blocks_def] >>
  Cases_on `fuel` >- simp[abi_result_labels_def] >>
  simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >- simp[abi_result_labels_def] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs
  >- (simp[] >> suspend "run_ok") >>
  simp[abi_result_labels_def]
QED

Resume abi_run_labels[run_ok]:
  rename1 `eval_phis s bb.bb_instructions = OK sp` >>
  `sp.vs_labels = s.vs_labels` by metis_tac[abi_phis_labels] >>
  `abi_result_labels sp.vs_labels (exec_block n ctx bb
     (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))` by
    (gvs[] >> metis_tac[]) >>
  Cases_on `exec_block n ctx bb
     (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  gvs[abi_result_labels_def] >>
  IF_CASES_TAC >- simp[abi_result_labels_def] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Finalise abi_run_labels

Theorem abi_run_from_labels:
  abi_result_labels s.vs_labels (run_from fuel ctx fn s)
Proof
  simp[run_from_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >- simp[abi_result_labels_def] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  qspecl_then [`fuel`, `ctx`, `bb`, `s`] assume_tac (cj 2 abi_run_labels) >>
  Cases_on `exec_block fuel ctx bb s` >> gvs[abi_result_labels_def] >>
  IF_CASES_TAC >- simp[abi_result_labels_def] >>
  qspecl_then [`fuel`, `ctx`, `fn`, `v`] mp_tac (cj 3 abi_run_labels) >>
  simp[abi_result_labels_def]
QED

Theorem abi_run_from_halt_labels:
  run_from fuel ctx fn s = Halt t ==> t.vs_labels = s.vs_labels
Proof
  strip_tac >> mp_tac abi_run_from_labels >> simp[abi_result_labels_def]
QED

Theorem abi_frag_halting_observer:
  frag_exec ctx sa sb P Q (\r. F) /\
  fn_has_code sa sb observer /\ P s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!t. ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
       ?fuel u. run_from fuel ctx observer t = Halt u /\
                u.vs_labels = t.vs_labels) ==>
  ?t. Q t /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      t.vs_labels = s.vs_labels
Proof
  simp[frag_exec_def] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`observer`, `s`] mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `Q t` >>
  `?fuel u. run_from fuel ctx observer t = Halt u /\
            u.vs_labels = t.vs_labels` by metis_tac[] >>
  `?fuel'. run_from fuel' ctx observer s = Halt u` by
    (qpat_x_assum `!fuel. _` (qspec_then `fuel` mp_tac) >> simp[]) >>
  qexists_tac `t` >> simp[] >> metis_tac[abi_run_from_halt_labels]
QED

Theorem abi_stop_observer_contains:
  fn_has_code sa sb fn /\
  (!bb. MEM bb (emitted_blocks sa sb) ==> bb.bb_label <> sb.cs_current_bb) ==>
  fn_has_code sa sb
    (fn with fn_blocks :=
      <|bb_label := sb.cs_current_bb;
        bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|> :: fn.fn_blocks)
Proof
  simp[fn_has_code_def, lookup_block_def] >> rpt strip_tac
  >- (first_x_assum drule >> strip_tac >> simp[listTheory.FIND_thm] >> metis_tac[]) >>
  simp[listTheory.FIND_thm]
QED

Theorem abi_stop_observer_halt:
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  run_from fuel ctx
    (fn with fn_blocks :=
      <|bb_label := sb.cs_current_bb;
        bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|> :: fn.fn_blocks)
    t = Halt (halt_state (t with vs_returndata := []))
Proof
  strip_tac >> irule run_from_halt >>
  qexistsl_tac
    [`<|bb_label := sb.cs_current_bb;
        bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>`,
     `mk_inst id STOP [] []`] >>
  simp[lookup_block_def, listTheory.FIND_thm, get_instruction_def,
       rich_listTheory.EL_APPEND2, mk_inst_def] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> simp[mk_inst_def]
QED

Theorem abi_stop_observer_endpoint:
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?fuel u. run_from fuel ctx
    (fn with fn_blocks :=
      <|bb_label := sb.cs_current_bb;
        bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|> :: fn.fn_blocks)
    t = Halt u /\ u.vs_labels = t.vs_labels
Proof
  strip_tac >> qexistsl_tac [`0`, `halt_state (t with vs_returndata := [])`] >>
  simp[abi_stop_observer_halt, halt_state_def]
QED
