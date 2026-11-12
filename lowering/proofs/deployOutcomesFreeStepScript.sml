Theory deployOutcomesFreeStep
Ancestors
  contextCodegenRel dftCommutation venomState venomExecSemantics

Theorem outcomes_eval_operand[simp]:
  eval_operand op (s with vs_outcomes := os) = eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem outcomes_eval_operands[simp]:
  !ops s os. eval_operands ops (s with vs_outcomes := os) = eval_operands ops s
Proof
  Induct >> simp[eval_operands_def]
QED

Theorem outcomes_update_var[simp]:
  update_var x v (s with vs_outcomes := os) =
  (update_var x v s with vs_outcomes := os)
Proof
  simp[update_var_def]
QED

Theorem outcomes_active_inst[simp]:
  active_inst fn inst (s with vs_outcomes := os) = active_inst fn inst s
Proof
  simp[active_inst_def]
QED

Theorem outcomes_eval_one_phi[simp]:
  eval_one_phi (s with vs_outcomes := os) inst = eval_one_phi s inst
Proof
  simp[eval_one_phi_def]
QED

Theorem outcomes_eval_phis:
  !insts s os. eval_phis (s with vs_outcomes := os) insts =
    map_result_state (\t. t with vs_outcomes := os) (eval_phis s insts)
Proof
  Induct >> simp[eval_phis_def, map_result_state_def] >> rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  Cases_on `eval_one_phi s h` >> simp[map_result_state_def] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `eval_phis s insts` >> simp[map_result_state_def]
QED

Theorem map_result_state_OK[simp]:
  map_result_state f r = OK t <=> ?u. r = OK u /\ t = f u
Proof
  Cases_on `r` >> simp[map_result_state_def, EQ_SYM_EQ]
QED

Theorem outcomes_enters_block:
  enters_block fn (s with vs_outcomes := os) t <=>
  ?u. enters_block fn s u /\ t = (u with vs_outcomes := os)
Proof
  simp[enters_block_def, outcomes_eval_phis] >>
  eq_tac >> rpt strip_tac >> gvs[]
QED

Theorem outcomes_state_operations[simp]:
  (mload n (s with vs_outcomes := os) = mload n s) /\
  (sload k (s with vs_outcomes := os) = sload k s) /\
  (tload k (s with vs_outcomes := os) = tload k s) /\
  (mstore n v (s with vs_outcomes := os) = (mstore n v s with vs_outcomes := os)) /\
  (mstore8 n v (s with vs_outcomes := os) = (mstore8 n v s with vs_outcomes := os)) /\
  (sstore k v (s with vs_outcomes := os) = (sstore k v s with vs_outcomes := os)) /\
  (tstore k v (s with vs_outcomes := os) = (tstore k v s with vs_outcomes := os)) /\
  (write_memory_with_expansion n bs (s with vs_outcomes := os) =
    (write_memory_with_expansion n bs s with vs_outcomes := os)) /\
  (mcopy n m z (s with vs_outcomes := os) = (mcopy n m z s with vs_outcomes := os)) /\
  (istore n v (s with vs_outcomes := os) = (istore n v s with vs_outcomes := os)) /\
  (halt_state (s with vs_outcomes := os) = (halt_state s with vs_outcomes := os)) /\
  (revert_state (s with vs_outcomes := os) = (revert_state s with vs_outcomes := os)) /\
  (set_returndata bs (s with vs_outcomes := os) = (set_returndata bs s with vs_outcomes := os)) /\
  (jump_to lbl (s with vs_outcomes := os) = (jump_to lbl s with vs_outcomes := os))
Proof
  simp[mload_def, sload_def, tload_def, contract_storage_def,
       contract_transient_def, mstore_def, mstore8_def, sstore_def,
       tstore_def, write_memory_with_expansion_def, mcopy_def, istore_def,
       halt_state_def, revert_state_def, set_returndata_def, jump_to_def]
QED

Theorem outcomes_pack_dret_dynamic:
  !pairs cursor s os.
  pack_dret_dynamic cursor pairs (s with vs_outcomes := os) =
    (FST (pack_dret_dynamic cursor pairs s),
     FST (SND (pack_dret_dynamic cursor pairs s)),
     SND (SND (pack_dret_dynamic cursor pairs s)) with vs_outcomes := os)
Proof
  Induct >> simp[pack_dret_dynamic_def] >> rpt gen_tac >>
  PairCases_on `h` >> simp[pack_dret_dynamic_def] >>
  pairarg_tac >> simp[]
QED

Theorem outcomes_exec_pure1:
  exec_pure1 f inst (s with vs_outcomes := os) =
  map_result_state (\t. t with vs_outcomes := os) (exec_pure1 f inst s)
Proof
  simp[exec_pure1_def] >> rpt (BasicProvers.TOP_CASE_TAC >> simp[map_result_state_def])
QED

Theorem outcomes_exec_pure2:
  exec_pure2 f inst (s with vs_outcomes := os) =
  map_result_state (\t. t with vs_outcomes := os) (exec_pure2 f inst s)
Proof
  simp[exec_pure2_def] >> rpt (BasicProvers.TOP_CASE_TAC >> simp[map_result_state_def])
QED

Theorem outcomes_exec_pure3:
  exec_pure3 f inst (s with vs_outcomes := os) =
  map_result_state (\t. t with vs_outcomes := os) (exec_pure3 f inst s)
Proof
  simp[exec_pure3_def] >> rpt (BasicProvers.TOP_CASE_TAC >> simp[map_result_state_def])
QED

Theorem outcomes_exec_read0:
  (!s os. f (s with vs_outcomes := os) = f s) ==>
  exec_read0 f inst (s with vs_outcomes := os) =
  map_result_state (\t. t with vs_outcomes := os) (exec_read0 f inst s)
Proof
  strip_tac >> simp[exec_read0_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[map_result_state_def])
QED

Theorem outcomes_exec_read1:
  (!v s os. f v (s with vs_outcomes := os) = f v s) ==>
  exec_read1 f inst (s with vs_outcomes := os) =
  map_result_state (\t. t with vs_outcomes := os) (exec_read1 f inst s)
Proof
  strip_tac >> simp[exec_read1_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[map_result_state_def])
QED

Theorem outcomes_exec_write2:
  (!v w s os. f v w (s with vs_outcomes := os) = (f v w s with vs_outcomes := os)) ==>
  exec_write2 f inst (s with vs_outcomes := os) =
  map_result_state (\t. t with vs_outcomes := os) (exec_write2 f inst s)
Proof
  strip_tac >> simp[exec_write2_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[map_result_state_def])
QED

Theorem outcomes_exec_gas:
  exec_gas inst (s with vs_outcomes := os) =
  map_result_state (\t. t with vs_outcomes := os) (exec_gas inst s)
Proof
  simp[exec_gas_def] >> rpt (BasicProvers.TOP_CASE_TAC >> simp[map_result_state_def])
QED

Theorem outcomes_exec_alloca:
  exec_alloca inst (s with vs_outcomes := os) n =
  map_result_state (\t. t with vs_outcomes := os) (exec_alloca inst s n)
Proof
  simp[exec_alloca_def] >> rpt (BasicProvers.TOP_CASE_TAC >> simp[map_result_state_def])
QED

Theorem map_result_list_case[local]:
  map_result_state f (list_CASE xs a b) =
  list_CASE xs (map_result_state f a) (\h t. map_result_state f (b h t))
Proof
  Cases_on `xs` >> simp[]
QED

Theorem map_result_option_case[local]:
  map_result_state f (option_CASE x a b) =
  option_CASE x (map_result_state f a) (\y. map_result_state f (b y))
Proof
  Cases_on `x` >> simp[]
QED

Theorem map_result_pair_case[local]:
  map_result_state f (pair_CASE x g) =
  pair_CASE x (\a b. map_result_state f (g a b))
Proof
  Cases_on `x` >> simp[]
QED

Theorem map_result_if[local]:
  map_result_state f (if p then a else b) =
  if p then map_result_state f a else map_result_state f b
Proof
  Cases_on `p` >> simp[]
QED

Theorem map_result_operand_case[local]:
  map_result_state f (operand_CASE x a b c) =
  operand_CASE x (\v. map_result_state f (a v))
                 (\v. map_result_state f (b v))
                 (\v. map_result_state f (c v))
Proof
  Cases_on `x` >> simp[]
QED

(* Reduce only the discriminator and root of the large opcode case. *)
fun outcomes_opcode_conv th tm =
  let
    val (_, args) = strip_comb tm
    fun discriminator 1 = RAND_CONV (REWR_CONV th)
      | discriminator n = RATOR_CONV (discriminator (n - 1))
    val root = FIRST_CONV (map REWR_CONV
      (CONJUNCTS venomInstTheory.opcode_case_def))
  in
    (discriminator (length args) THENC root) tm
  end;

Theorem outcomes_step_inst_base:
  ~MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE] ==>
  step_inst_base inst (s with vs_outcomes := os) =
  map_result_state (\t. t with vs_outcomes := os) (step_inst_base inst s)
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >> gvs[] >>
  pure_once_rewrite_tac [step_inst_base_def] >>
  qpat_assum `inst.inst_opcode = _` (fn th =>
    CONV_TAC (LHS_CONV (outcomes_opcode_conv th) THENC
              RHS_CONV (RAND_CONV (outcomes_opcode_conv th)))) >>
  simp[outcomes_exec_pure1, outcomes_exec_pure2,
       outcomes_exec_pure3, outcomes_exec_gas, outcomes_exec_alloca] >>
  all_tac
  >>~- ([`exec_read0 _ _ _ = _`], irule outcomes_exec_read0 >> simp[])
  >>~- ([`exec_read1 _ _ _ = _`], irule outcomes_exec_read1 >> simp[])
  >>~- ([`exec_write2 _ _ _ = _`], irule outcomes_exec_write2 >> simp[]) >>
  all_tac
  >~ [`inst.inst_opcode = DRET`] >- suspend "dret"
  >~ [`inst.inst_opcode = SSTORE`] >- suspend "sstore"
  >~ [`inst.inst_opcode = TSTORE`] >- suspend "tstore" >>
  CONV_TAC (REDEPTH_CONV patternMatchesLib.PMATCH_ELIM_CONV) >>
  simp_tac bool_ss [map_result_list_case, map_result_option_case,
                   map_result_pair_case, map_result_operand_case,
                   map_result_if, map_result_state_def] >>
  simp[halt_state_def, revert_state_def, set_returndata_def]
QED
Resume outcomes_step_inst_base[dret]:
  simp[outcomes_pack_dret_dynamic] >>
  CONV_TAC (REDEPTH_CONV patternMatchesLib.PMATCH_ELIM_CONV) >>
  simp_tac bool_ss [map_result_list_case, map_result_option_case,
                   map_result_pair_case, map_result_operand_case,
                   map_result_if, map_result_state_def, pairTheory.ELIM_UNCURRY] >>
  simp[]
QED
Resume outcomes_step_inst_base[sstore]:
  IF_CASES_TAC >> simp[map_result_state_def, outcomes_exec_write2]
QED
Resume outcomes_step_inst_base[tstore]:
  IF_CASES_TAC >> simp[map_result_state_def, outcomes_exec_write2]
QED
Finalise outcomes_step_inst_base

Theorem outcomes_step_inst:
  ~MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE] ==>
  step_inst fuel ctx inst (s with vs_outcomes := os) =
  map_result_state (\t. t with vs_outcomes := os) (step_inst fuel ctx inst s)
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by gvs[] >>
  simp[Once step_inst_def, outcomes_step_inst_base] >>
  simp[Once step_inst_def]
QED

Theorem map_result_state_Halt[simp]:
  map_result_state f r = Halt t <=> ?u. r = Halt u /\ t = f u
Proof
  Cases_on `r` >> simp[map_result_state_def, EQ_SYM_EQ]
QED

Theorem map_result_state_Abort[simp]:
  map_result_state f r = Abort a t <=> ?u. r = Abort a u /\ t = f u
Proof
  Cases_on `r` >> simp[map_result_state_def, EQ_SYM_EQ]
QED

Theorem map_result_state_IntRet[simp]:
  map_result_state f r = IntRet vals t <=> ?u. r = IntRet vals u /\ t = f u
Proof
  Cases_on `r` >> simp[map_result_state_def, EQ_SYM_EQ]
QED

Theorem map_result_state_Error[simp]:
  map_result_state f r = Error e <=> r = Error e
Proof
  Cases_on `r` >> simp[map_result_state_def]
QED
