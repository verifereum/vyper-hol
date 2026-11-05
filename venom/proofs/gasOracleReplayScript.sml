(* A finite run can be replayed with an arbitrary unused GAS suffix.
   The consumed prefix includes zero readings after oracle exhaustion. *)
Theory gasOracleReplay
Ancestors
  stateEquiv venomExecSemantics venomState venomCallOracleDefs list rich_list arithmetic

Definition gas_prefix_def:
  gas_prefix n (gs : (256 word) list) = TAKE n (gs ++ REPLICATE n 0w)
End

Definition gas_replay_at_def:
  gas_replay_at n f s <=> !tail.
    lift_result
      (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
             b = (a with vs_gas_readings := tail))
      (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
             b = (a with vs_gas_readings := tail))
      (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
             b = (a with vs_gas_readings := tail))
      (f s) (f (s with vs_gas_readings :=
                        gas_prefix n s.vs_gas_readings ++ tail))
End

Definition gas_replay_def:
  gas_replay f s <=> ?n. gas_replay_at n f s
End

Theorem gas_prefix_zero[simp]:
  gas_prefix 0 gs = []
Proof
  simp[gas_prefix_def]
QED

Theorem gas_take_pad[local]:
  !n (gs:'a list) a b x.
    n <= LENGTH gs + a /\ n <= LENGTH gs + b ==>
    TAKE n (gs ++ REPLICATE a x) = TAKE n (gs ++ REPLICATE b x)
Proof
  rw[LIST_EQ_REWRITE, LENGTH_TAKE, LENGTH_APPEND, LENGTH_REPLICATE] >>
  rw[EL_TAKE, EL_APPEND_EQN, EL_REPLICATE, LENGTH_REPLICATE]
QED

Theorem gas_prefix_suc:
  (gas_prefix (SUC n) [] = 0w :: gas_prefix n []) /\
  (gas_prefix (SUC n) (g::gs) = g :: gas_prefix n gs)
Proof
  conj_tac
  >- simp[gas_prefix_def, TAKE_def] >>
  simp[gas_prefix_def, TAKE_def] >>
  `TAKE n (gs ++ REPLICATE (SUC n) 0w) =
   TAKE n (gs ++ REPLICATE n 0w)` by
    (irule gas_take_pad >> simp[]) >>
  gvs[]
QED

Theorem gas_prefix_add:
  !n gs m. gas_prefix (n + m) gs =
    gas_prefix n gs ++ gas_prefix m (DROP n gs)
Proof
  Induct_on `n`
  >- simp[]
  >> Cases_on `gs`
  >- (simp[ADD_CLAUSES, gas_prefix_suc] >>
      first_x_assum (qspec_then `[]` mp_tac) >> simp[ADD_COMM])
  >> simp[ADD_CLAUSES, gas_prefix_suc] >>
  first_x_assum (qspec_then `t` mp_tac) >> simp[ADD_COMM]
QED

Definition gas_bind_ok_def:
  gas_bind_ok r k = case r of OK t => k t | other => other
End

Theorem gas_replay_bind_ok:
  gas_replay f s /\ (!t. f s = OK t ==> gas_replay k t) ==>
  gas_replay (\u. gas_bind_ok (f u) k) s
Proof
  simp[gas_replay_def] >> strip_tac >>
  Cases_on `f s` >> gvs[]
  >- (qexists_tac `n + n'` >>
      simp[gas_replay_at_def, gas_prefix_add, APPEND_ASSOC] >>
      gen_tac >>
      qpat_x_assum `gas_replay_at n f s` mp_tac >>
      simp[gas_replay_at_def] >>
      disch_then (qspec_then
        `gas_prefix n' (DROP n s.vs_gas_readings) ++ tail` mp_tac) >>
      Cases_on `f (s with vs_gas_readings :=
        gas_prefix n s.vs_gas_readings ++
        (gas_prefix n' (DROP n s.vs_gas_readings) ++ tail))` >>
      simp[lift_result_def] >> strip_tac >> gvs[] >>
      qpat_x_assum `gas_replay_at n' k v` mp_tac >>
      simp[gas_replay_at_def] >>
      disch_then (qspec_then `tail` mp_tac) >>
      simp[gas_bind_ok_def, DROP_DROP_T, ADD_COMM])
  >> qexists_tac `n` >>
  qpat_x_assum `gas_replay_at n f s` mp_tac >>
  simp[gas_replay_at_def] >>
  disch_tac >> gen_tac >>
  first_x_assum (qspec_then `tail` mp_tac) >>
  Cases_on `f (s with vs_gas_readings :=
    gas_prefix n s.vs_gas_readings ++ tail)` >>
  simp[lift_result_def, gas_bind_ok_def]
QED

Theorem gas_eval_operand[simp]:
  eval_operand op (s with vs_gas_readings := gs) = eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem gas_eval_operands[simp]:
  !ops s gs. eval_operands ops (s with vs_gas_readings := gs) =
             eval_operands ops s
Proof
  Induct_on `ops` >> simp[eval_operands_def]
QED

Theorem gas_setup_callee:
  setup_callee fn args (s with vs_gas_readings := gs) =
    OPTION_MAP (\t. t with vs_gas_readings := gs) (setup_callee fn args s)
Proof
  simp[setup_callee_def] >> IF_CASES_TAC >> simp[]
QED

Theorem gas_setup_callee_readings:
  setup_callee fn args s = SOME t ==>
  t.vs_gas_readings = s.vs_gas_readings
Proof
  simp[setup_callee_def] >> IF_CASES_TAC >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem gas_merge_callee:
  merge_callee_state (s with vs_gas_readings := xs)
    (t with vs_gas_readings := ys) =
  (merge_callee_state s t with vs_gas_readings := ys)
Proof
  simp[merge_callee_state_def]
QED

Theorem gas_merge_callee_readings[simp]:
  (merge_callee_state s t).vs_gas_readings = t.vs_gas_readings
Proof
  simp[merge_callee_state_def]
QED

Theorem gas_adopt_return:
  adopt_return_fmp ir (s with vs_gas_readings := gs) =
    (adopt_return_fmp ir s with vs_gas_readings := gs)
Proof
  Cases_on `ir.iret_adopt_fmp` >> simp[adopt_return_fmp_def]
QED

Theorem gas_adopt_return_readings[simp]:
  (adopt_return_fmp ir s).vs_gas_readings = s.vs_gas_readings
Proof
  Cases_on `ir.iret_adopt_fmp` >> simp[adopt_return_fmp_def]
QED

Theorem gas_update_var[simp]:
  update_var out v (s with vs_gas_readings := gs) =
    (update_var out v s with vs_gas_readings := gs)
Proof
  simp[update_var_def]
QED

Theorem gas_update_var_readings[simp]:
  (update_var out v s).vs_gas_readings = s.vs_gas_readings
Proof
  simp[update_var_def]
QED

Theorem gas_fold_updates:
  !xs s gs.
    FOLDL (\s' (out,v). update_var out v s')
      (s with vs_gas_readings := gs) xs =
    (FOLDL (\s' (out,v). update_var out v s') s xs
      with vs_gas_readings := gs)
Proof
  Induct_on `xs` >> simp[] >> Cases_on `h` >> simp[]
QED

Theorem gas_fold_updates_readings:
  !xs s.
    (FOLDL (\s' (out,v). update_var out v s') s xs).vs_gas_readings =
      s.vs_gas_readings
Proof
  Induct_on `xs` >> simp[] >> Cases_on `h` >> simp[]
QED

Theorem gas_bind_outputs:
  bind_outputs outs vals (s with vs_gas_readings := gs) =
    OPTION_MAP (\t. t with vs_gas_readings := gs) (bind_outputs outs vals s)
Proof
  simp[bind_outputs_def, gas_fold_updates] >> IF_CASES_TAC >> simp[]
QED

Theorem gas_bind_outputs_readings:
  bind_outputs outs vals s = SOME t ==>
  t.vs_gas_readings = s.vs_gas_readings
Proof
  simp[bind_outputs_def] >> strip_tac >> gvs[gas_fold_updates_readings]
QED

Theorem gas_eval_one_phi[simp]:
  eval_one_phi (s with vs_gas_readings := gs) inst = eval_one_phi s inst
Proof
  simp[eval_one_phi_def]
QED

Theorem gas_eval_phis:
  !insts s. gas_replay_at 0 (\u. eval_phis u insts) s
Proof
  Induct_on `insts`
  >- simp[gas_replay_at_def, eval_phis_def, lift_result_def] >>
  rpt gen_tac >>
  first_x_assum (qspec_then `s` mp_tac) >>
  simp[gas_replay_at_def] >> disch_tac >> gen_tac >>
  first_x_assum (qspec_then `tail` mp_tac) >>
  simp[eval_phis_def] >>
  Cases_on `h.inst_opcode = PHI`
  >- (simp[] >> Cases_on `eval_one_phi s h` >> simp[lift_result_def] >>
      rename1 `SOME p` >> Cases_on `p` >> simp[] >>
      Cases_on `eval_phis s insts` >>
      Cases_on `eval_phis (s with vs_gas_readings := tail) insts` >>
      simp[lift_result_def] >> strip_tac >> gvs[]) >>
  simp[lift_result_def]
QED

Theorem gas_control_updates[simp]:
  (next_inst (s with vs_gas_readings := gs) =
     (next_inst s with vs_gas_readings := gs)) /\
  ((next_inst s).vs_gas_readings = s.vs_gas_readings) /\
  (jump_to lbl (s with vs_gas_readings := gs) =
     (jump_to lbl s with vs_gas_readings := gs)) /\
  ((jump_to lbl s).vs_gas_readings = s.vs_gas_readings) /\
  (halt_state (s with vs_gas_readings := gs) =
     (halt_state s with vs_gas_readings := gs)) /\
  ((halt_state s).vs_gas_readings = s.vs_gas_readings) /\
  (revert_state (s with vs_gas_readings := gs) =
     (revert_state s with vs_gas_readings := gs)) /\
  ((revert_state s).vs_gas_readings = s.vs_gas_readings)
Proof
  simp[next_inst_def, jump_to_def, halt_state_def, revert_state_def]
QED

Theorem gas_exec_gas:
  gas_replay_at 1 (exec_gas inst) s
Proof
  simp[gas_replay_at_def] >> gen_tac >>
  rewrite_tac[arithmeticTheory.ONE] >>
  Cases_on `s.vs_gas_readings` >>
  simp[gas_prefix_suc, exec_gas_def] >>
  Cases_on `inst.inst_outputs` >> simp[lift_result_def] >>
  qpat_x_assum `inst.inst_outputs = _` mp_tac >>
  rename1 `inst.inst_outputs = out::outs` >>
  Cases_on `outs` >> simp[lift_result_def]
QED

Theorem gas_exec_pure1:
  gas_replay_at 0 (exec_pure1 f inst) s
Proof
  simp[gas_replay_at_def, exec_pure1_def] >> gen_tac >>
  Cases_on `inst.inst_operands` >> simp[lift_result_def] >>
  rename1 `inst.inst_operands = op1::ops` >>
  Cases_on `ops` >> simp[lift_result_def] >>
  Cases_on `eval_operand op1 s` >> simp[lift_result_def] >>
  Cases_on `inst.inst_outputs` >> simp[lift_result_def] >>
  rename1 `inst.inst_outputs = out::outs` >>
  Cases_on `outs` >> simp[lift_result_def]
QED

Theorem gas_exec_pure2:
  gas_replay_at 0 (exec_pure2 f inst) s
Proof
  simp[gas_replay_at_def, exec_pure2_def] >> gen_tac >>
  namedCases_on `inst.inst_operands` ["", "op1 ops"] >> simp[lift_result_def] >>
  namedCases_on `ops` ["", "op2 rest"] >> simp[lift_result_def] >>
  Cases_on `rest` >> simp[lift_result_def] >>
  Cases_on `eval_operand op1 s` >> simp[lift_result_def] >>
  Cases_on `eval_operand op2 s` >> simp[lift_result_def] >>
  Cases_on `inst.inst_outputs` >> simp[lift_result_def] >>
  rename1 `inst.inst_outputs = out::outs` >>
  Cases_on `outs` >> simp[lift_result_def]
QED

Theorem gas_exec_pure3:
  gas_replay_at 0 (exec_pure3 f inst) s
Proof
  simp[gas_replay_at_def, exec_pure3_def] >> gen_tac >>
  namedCases_on `inst.inst_operands` ["", "op1 ops"] >> simp[lift_result_def] >>
  namedCases_on `ops` ["", "op2 rest"] >> simp[lift_result_def] >>
  namedCases_on `rest` ["", "op3 last"] >> simp[lift_result_def] >>
  Cases_on `last` >> simp[lift_result_def] >>
  Cases_on `eval_operand op1 s` >> simp[lift_result_def] >>
  Cases_on `eval_operand op2 s` >> simp[lift_result_def] >>
  Cases_on `eval_operand op3 s` >> simp[lift_result_def] >>
  Cases_on `inst.inst_outputs` >> simp[lift_result_def] >>
  rename1 `inst.inst_outputs = out::outs` >>
  Cases_on `outs` >> simp[lift_result_def]
QED

Theorem gas_exec_read0:
  (!u gs. f (u with vs_gas_readings := gs) = f u) ==>
  gas_replay_at 0 (exec_read0 f inst) s
Proof
  strip_tac >> simp[gas_replay_at_def, exec_read0_def] >> gen_tac >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >> simp[lift_result_def] >>
  Cases_on `outs` >> simp[lift_result_def]
QED

Theorem gas_exec_read1:
  (!v u gs. f v (u with vs_gas_readings := gs) = f v u) ==>
  gas_replay_at 0 (exec_read1 f inst) s
Proof
  strip_tac >> simp[gas_replay_at_def, exec_read1_def] >> gen_tac >>
  namedCases_on `inst.inst_operands` ["", "op1 ops"] >> simp[lift_result_def] >>
  Cases_on `ops` >> simp[lift_result_def] >>
  Cases_on `eval_operand op1 s` >> simp[lift_result_def] >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >> simp[lift_result_def] >>
  Cases_on `outs` >> simp[lift_result_def]
QED

Theorem gas_exec_write2:
  (!v w u gs. f v w (u with vs_gas_readings := gs) =
               (f v w u with vs_gas_readings := gs)) /\
  (!v w u. (f v w u).vs_gas_readings = u.vs_gas_readings) ==>
  gas_replay_at 0 (exec_write2 f inst) s
Proof
  strip_tac >> simp[gas_replay_at_def, exec_write2_def] >> gen_tac >>
  namedCases_on `inst.inst_operands` ["", "op1 ops"] >> simp[lift_result_def] >>
  namedCases_on `ops` ["", "op2 rest"] >> simp[lift_result_def] >>
  Cases_on `rest` >> simp[lift_result_def] >>
  Cases_on `eval_operand op1 s` >> simp[lift_result_def] >>
  Cases_on `eval_operand op2 s` >> simp[lift_result_def]
QED

Theorem gas_exec_alloca:
  gas_replay_at 0 (\u. exec_alloca inst u sz) s
Proof
  simp[gas_replay_at_def, exec_alloca_def] >> gen_tac >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >> simp[lift_result_def] >>
  Cases_on `outs` >> simp[lift_result_def] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id` >> simp[lift_result_def] >>
  Cases_on `x` >> simp[lift_result_def]
QED

Theorem gas_read_memory[simp]:
  read_memory off sz (s with vs_gas_readings := gs) = read_memory off sz s
Proof
  simp[read_memory_def]
QED

Theorem gas_write_memory_expansion[simp]:
  write_memory_with_expansion off bytes (s with vs_gas_readings := gs) =
  (write_memory_with_expansion off bytes s with vs_gas_readings := gs)
Proof
  simp[write_memory_with_expansion_def, write_memory_def]
QED

Theorem gas_call_request[simp]:
  venom_call_request (s with vs_gas_readings := gs) addr value off sz st =
  venom_call_request s addr value off sz st
Proof
  simp[venom_call_request_def]
QED

Theorem gas_consume_outcome[simp]:
  consume_call_outcome rq off sz (s with vs_gas_readings := gs) =
  (FST (consume_call_outcome rq off sz s),
   SND (consume_call_outcome rq off sz s) with vs_gas_readings := gs)
Proof
  simp[consume_call_outcome_eq]
QED

Theorem gas_consume_outcome_readings[simp]:
  (SND (consume_call_outcome rq off sz s)).vs_gas_readings = s.vs_gas_readings
Proof
  simp[consume_call_outcome_eq]
QED

Theorem gas_exec_ext_call:
  gas_replay_at 0
    (\u. exec_ext_call inst u gas addr value ao az ro rz st) s
Proof
  simp[gas_replay_at_def, exec_ext_call_def, Excl "consume_call_outcome_eq"] >>
  gen_tac >> pairarg_tac >> simp[Excl "consume_call_outcome_eq"] >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >> simp[lift_result_def] >>
  Cases_on `outs` >> simp[lift_result_def] >>
  metis_tac[gas_consume_outcome_readings, pairTheory.SND]
QED

Theorem gas_tx_params[simp]:
  venom_to_tx_params (s with vs_gas_readings := gs) = venom_to_tx_params s
Proof
  simp[venom_to_tx_params_def]
QED

Theorem gas_make_delegatecall[simp]:
  make_venom_delegatecall_state (s with vs_gas_readings := gs) a g d c st =
  make_venom_delegatecall_state s a g d c st
Proof
  simp[make_venom_delegatecall_state_def]
QED

Theorem gas_make_create[simp]:
  make_venom_create_state (s with vs_gas_readings := gs) a g v c =
  make_venom_create_state s a g v c
Proof
  simp[make_venom_create_state_def]
QED

Theorem gas_extract_result:
  extract_venom_result (s with vs_gas_readings := gs) v off sz res =
  OPTION_MAP (\(w,t). (w,t with vs_gas_readings := gs))
    (extract_venom_result s v off sz res)
Proof
  Cases_on `res` >> simp[extract_venom_result_def] >>
  PairCases_on `x` >> simp[] >>
  namedCases_on `x1.contexts` ["", "ct rest"] >> simp[] >>
  Cases_on `rest` >> simp[] >>
  PairCases_on `ct` >> simp[] >>
  Cases_on `x0` >> simp[] >>
  simp[venom_state_component_equality] >>
  Cases_on `y` >> simp[venom_state_component_equality]
QED

Theorem gas_extract_result_readings:
  extract_venom_result s v off sz res = SOME (w,t) ==>
  t.vs_gas_readings = s.vs_gas_readings
Proof
  Cases_on `res` >> simp[extract_venom_result_def] >>
  PairCases_on `x` >> simp[] >>
  namedCases_on `x1.contexts` ["", "ct rest"] >> simp[] >>
  Cases_on `rest` >> simp[] >>
  PairCases_on `ct` >> simp[] >>
  Cases_on `x0` >> simp[]
  >- (strip_tac >> gvs[]) >>
  Cases_on `y` >> simp[] >> strip_tac >> gvs[]
QED

Theorem gas_exec_delegatecall:
  gas_replay_at 0 (\u. exec_delegatecall inst u gas addr ao az ro rz) s
Proof
  simp[gas_replay_at_def, exec_delegatecall_def, gas_extract_result] >>
  gen_tac >>
  qmatch_goalsub_abbrev_tac `extract_venom_result s 1w (w2n ro) (w2n rz) res` >>
  Cases_on `extract_venom_result s 1w (w2n ro) (w2n rz) res` >>
  simp[lift_result_def] >>
  PairCases_on `x` >> simp[] >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >> simp[lift_result_def] >>
  Cases_on `outs` >> simp[lift_result_def] >>
  metis_tac[gas_extract_result_readings]
QED

Theorem gas_exec_create:
  gas_replay_at 0 (\u. exec_create inst u value off sz salt) s
Proof
  Cases_on `inst.inst_outputs` >>
  simp[gas_replay_at_def, exec_create_def, lift_result_def] >>
  Cases_on `t` >> simp[gas_replay_at_def, exec_create_def, lift_result_def] >>
  Cases_on `w2n sz > 2 * max_code_size` >>
  simp[gas_replay_at_def, exec_create_def, lift_result_def,
       venom_create_request_def, read_memory_def, update_var_def,
       halt_state_def, set_returndata_def]
QED

Theorem gas_state_observers[simp]:
  mload off (s with vs_gas_readings := gs) = mload off s /\
  sload key (s with vs_gas_readings := gs) = sload key s /\
  tload key (s with vs_gas_readings := gs) = tload key s
Proof
  simp[mload_def, sload_def, tload_def, contract_storage_def, contract_transient_def]
QED

Theorem gas_state_writes[simp]:
  mstore off v (s with vs_gas_readings := gs) =
    (mstore off v s with vs_gas_readings := gs) /\
  mstore8 off v (s with vs_gas_readings := gs) =
    (mstore8 off v s with vs_gas_readings := gs) /\
  sstore key v (s with vs_gas_readings := gs) =
    (sstore key v s with vs_gas_readings := gs) /\
  tstore key v (s with vs_gas_readings := gs) =
    (tstore key v s with vs_gas_readings := gs) /\
  mcopy dst src sz (s with vs_gas_readings := gs) =
    (mcopy dst src sz s with vs_gas_readings := gs) /\
  istore off v (s with vs_gas_readings := gs) =
    (istore off v s with vs_gas_readings := gs) /\
  jump_to lbl (s with vs_gas_readings := gs) =
    (jump_to lbl s with vs_gas_readings := gs) /\
  halt_state (s with vs_gas_readings := gs) =
    (halt_state s with vs_gas_readings := gs) /\
  revert_state (s with vs_gas_readings := gs) =
    (revert_state s with vs_gas_readings := gs) /\
  set_returndata rd (s with vs_gas_readings := gs) =
    (set_returndata rd s with vs_gas_readings := gs)
Proof
  simp[mstore_def, mstore8_def, sstore_def, tstore_def, mcopy_def,
       istore_def, jump_to_def, halt_state_def, revert_state_def, set_returndata_def]
QED

Theorem gas_state_writes_readings[simp]:
  (mstore off v s).vs_gas_readings = s.vs_gas_readings /\
  (mstore8 off v s).vs_gas_readings = s.vs_gas_readings /\
  (sstore key v s).vs_gas_readings = s.vs_gas_readings /\
  (tstore key v s).vs_gas_readings = s.vs_gas_readings /\
  (mcopy dst src sz s).vs_gas_readings = s.vs_gas_readings /\
  (istore off v s).vs_gas_readings = s.vs_gas_readings /\
  (write_memory_with_expansion off bytes s).vs_gas_readings = s.vs_gas_readings /\
  (jump_to lbl s).vs_gas_readings = s.vs_gas_readings /\
  (halt_state s).vs_gas_readings = s.vs_gas_readings /\
  (revert_state s).vs_gas_readings = s.vs_gas_readings /\
  (set_returndata rd s).vs_gas_readings = s.vs_gas_readings
Proof
  simp[mstore_def, mstore8_def, sstore_def, tstore_def, mcopy_def,
       istore_def, write_memory_with_expansion_def, jump_to_def,
       halt_state_def, revert_state_def, set_returndata_def]
QED

(* Select a single dispatch equation and abstract its state argument. *)
val gas_opcode_rewrites = let
  fun key th = let
    val (_, body) = strip_forall (concl th)
    val (guard, _) = dest_imp body
  in rhs guard end
in map (fn th => (key th, th))
  (CONJUNCTS venomExecSemanticsTheory.step_inst_base_opcode_eqs) end;

fun gas_opcode_rewrite eq = let
  val (_, th) = valOf (List.find
    (fn (key, _) => aconv key (rhs (concl eq))) gas_opcode_rewrites)
in PURE_ONCE_REWRITE_TAC [MATCH_MP th eq] end;

Theorem gas_pack_dret_transport:
  !pairs cursor s ptrs final_cursor t gs.
  pack_dret_dynamic cursor pairs s = (ptrs,final_cursor,t) ==>
  pack_dret_dynamic cursor pairs (s with vs_gas_readings := gs) =
    (ptrs,final_cursor,t with vs_gas_readings := gs)
Proof
  Induct_on `pairs` >- simp[pack_dret_dynamic_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[Once pack_dret_dynamic_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  simp[Once pack_dret_dynamic_def]
QED

Theorem gas_pack_dret_readings:
  !pairs cursor s ptrs final_cursor t.
  pack_dret_dynamic cursor pairs s = (ptrs,final_cursor,t) ==>
  t.vs_gas_readings = s.vs_gas_readings
Proof
  Induct_on `pairs` >- simp[pack_dret_dynamic_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[Once pack_dret_dynamic_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem gas_base_data_dispatch:
  MEM inst.inst_opcode
    [MCOPY; ISTORE; CALLDATACOPY; RETURNDATACOPY; SHA3; DLOADBYTES;
     CODECOPY; EXTCODECOPY; LOG; SELFDESTRUCT; CALL; STATICCALL;
     DELEGATECALL; CREATE; CREATE2; ALLOCA] ==>
  gas_replay_at 0 (step_inst_base inst) s
Proof
  simp[MEM] >> strip_tac >> rewrite_tac[gas_replay_at_def] >>
  qpat_assum `inst.inst_opcode = _` gas_opcode_rewrite >> gen_tac >> simp[]
  >~ [`inst.inst_opcode = MCOPY`] >- suspend "mcopy"
  >~ [`inst.inst_opcode = ISTORE`] >- suspend "istore"
  >~ [`inst.inst_opcode = CALLDATACOPY`] >- suspend "calldatacopy"
  >~ [`inst.inst_opcode = RETURNDATACOPY`] >- suspend "returndatacopy"
  >~ [`inst.inst_opcode = SHA3`] >- suspend "sha3"
  >~ [`inst.inst_opcode = DLOADBYTES`] >- suspend "dloadbytes"
  >~ [`inst.inst_opcode = CODECOPY`] >- suspend "codecopy"
  >~ [`inst.inst_opcode = EXTCODECOPY`] >- suspend "extcodecopy"
  >~ [`inst.inst_opcode = LOG`] >- suspend "log"
  >~ [`inst.inst_opcode = SELFDESTRUCT`] >- suspend "selfdestruct"
  >~ [`inst.inst_opcode = CALL`] >- suspend "call"
  >~ [`inst.inst_opcode = STATICCALL`] >- suspend "staticcall"
  >~ [`inst.inst_opcode = DELEGATECALL`] >- suspend "delegatecall"
  >~ [`inst.inst_opcode = CREATE`] >- suspend "create"
  >~ [`inst.inst_opcode = CREATE2`] >- suspend "create2"
  >> suspend "alloca"
QED

Resume gas_base_data_dispatch[mcopy]:
  namedCases_on `inst.inst_operands` ["", "a ops"] >> simp[lift_result_def] >>
  namedCases_on `ops` ["", "b rest"] >> simp[lift_result_def] >>
  namedCases_on `rest` ["", "c last"] >> simp[lift_result_def] >>
  Cases_on `last` >> simp[lift_result_def] >>
  Cases_on `eval_operand a s` >> simp[lift_result_def] >>
  Cases_on `eval_operand b s` >> simp[lift_result_def] >>
  Cases_on `eval_operand c s` >> simp[lift_result_def]
QED
Resume gas_base_data_dispatch[istore]:
  namedCases_on `inst.inst_operands` ["", "a ops"] >> simp[lift_result_def] >>
  namedCases_on `ops` ["", "b rest"] >> simp[lift_result_def] >>
  Cases_on `rest` >> simp[lift_result_def] >>
  Cases_on `eval_operand a s` >> simp[lift_result_def] >>
  Cases_on `eval_operand b s` >> simp[lift_result_def]
QED
Resume gas_base_data_dispatch[calldatacopy]:
  namedCases_on `inst.inst_operands` ["", "a ops"] >> simp[lift_result_def] >>
  namedCases_on `ops` ["", "b rest"] >> simp[lift_result_def] >>
  namedCases_on `rest` ["", "c last"] >> simp[lift_result_def] >>
  Cases_on `last` >> simp[lift_result_def] >>
  Cases_on `eval_operand a s` >> simp[lift_result_def] >>
  Cases_on `eval_operand b s` >> simp[lift_result_def] >>
  Cases_on `eval_operand c s` >> simp[lift_result_def]
QED
Resume gas_base_data_dispatch[returndatacopy]:
  namedCases_on `inst.inst_operands` ["", "a ops"] >> simp[lift_result_def] >>
  namedCases_on `ops` ["", "b rest"] >> simp[lift_result_def] >>
  namedCases_on `rest` ["", "c last"] >> simp[lift_result_def] >>
  Cases_on `last` >> simp[lift_result_def] >>
  Cases_on `eval_operand a s` >> simp[lift_result_def] >>
  Cases_on `eval_operand b s` >> simp[lift_result_def] >>
  Cases_on `eval_operand c s` >> simp[lift_result_def] >>
  IF_CASES_TAC >> simp[lift_result_def]
QED
Resume gas_base_data_dispatch[sha3]:
  namedCases_on `inst.inst_operands` ["", "a ops"] >> simp[lift_result_def] >>
  namedCases_on `ops` ["", "b rest"] >> simp[lift_result_def] >>
  Cases_on `rest` >> simp[lift_result_def] >>
  Cases_on `eval_operand a s` >> simp[lift_result_def] >>
  Cases_on `eval_operand b s` >> simp[lift_result_def] >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >> simp[lift_result_def] >>
  Cases_on `outs` >> simp[lift_result_def]
QED
Resume gas_base_data_dispatch[dloadbytes]:
  namedCases_on `inst.inst_operands` ["", "a ops"] >> simp[lift_result_def] >>
  namedCases_on `ops` ["", "b rest"] >> simp[lift_result_def] >>
  namedCases_on `rest` ["", "c last"] >> simp[lift_result_def] >>
  Cases_on `last` >> simp[lift_result_def] >>
  Cases_on `eval_operand a s` >> simp[lift_result_def] >>
  Cases_on `eval_operand b s` >> simp[lift_result_def] >>
  Cases_on `eval_operand c s` >> simp[lift_result_def]
QED
Resume gas_base_data_dispatch[codecopy]:
  namedCases_on `inst.inst_operands` ["", "a ops"] >> simp[lift_result_def] >>
  namedCases_on `ops` ["", "b rest"] >> simp[lift_result_def] >>
  namedCases_on `rest` ["", "c last"] >> simp[lift_result_def] >>
  Cases_on `last` >> simp[lift_result_def] >>
  Cases_on `eval_operand a s` >> simp[lift_result_def] >>
  Cases_on `eval_operand b s` >> simp[lift_result_def] >>
  Cases_on `eval_operand c s` >> simp[lift_result_def]
QED
Resume gas_base_data_dispatch[extcodecopy]:
  namedCases_on `inst.inst_operands` ["", "a ops"] >> simp[lift_result_def] >>
  namedCases_on `ops` ["", "b rest"] >> simp[lift_result_def] >>
  namedCases_on `rest` ["", "c last"] >> simp[lift_result_def] >>
  namedCases_on `last` ["", "d extra"] >> simp[lift_result_def] >>
  Cases_on `extra` >> simp[lift_result_def] >>
  Cases_on `eval_operand a s` >> simp[lift_result_def] >>
  Cases_on `eval_operand b s` >> simp[lift_result_def] >>
  Cases_on `eval_operand c s` >> simp[lift_result_def] >>
  Cases_on `eval_operand d s` >> simp[lift_result_def]
QED
Resume gas_base_data_dispatch[log]:
  IF_CASES_TAC >- simp[lift_result_def, halt_state_def, set_returndata_def] >>
  namedCases_on `inst.inst_operands` ["", "a ops"] >> simp[lift_result_def] >>
  Cases_on `a` >> simp[lift_result_def] >>
  IF_CASES_TAC >> simp[lift_result_def] >>
  Cases_on `eval_operand (HD (REVERSE ops)) s` >> simp[lift_result_def] >>
  Cases_on `eval_operand (EL 1 (REVERSE ops)) s` >> simp[lift_result_def] >>
  Cases_on `eval_operands (DROP 2 (REVERSE ops)) s` >> simp[lift_result_def]
QED
Resume gas_base_data_dispatch[selfdestruct]:
  IF_CASES_TAC >- simp[lift_result_def, halt_state_def, set_returndata_def] >>
  namedCases_on `inst.inst_operands` ["", "a ops"] >> simp[lift_result_def] >>
  Cases_on `ops` >> simp[lift_result_def] >>
  Cases_on `eval_operand a s` >> simp[lift_result_def, halt_state_def, set_returndata_def]
QED
Resume gas_base_data_dispatch[call]:
  namedCases_on `inst.inst_operands` ["", "a ops"] >> simp[lift_result_def] >>
  namedCases_on `ops` ["", "b r1"] >> simp[lift_result_def] >>
  namedCases_on `r1` ["", "c r2"] >> simp[lift_result_def] >>
  namedCases_on `r2` ["", "d r3"] >> simp[lift_result_def] >>
  namedCases_on `r3` ["", "e r4"] >> simp[lift_result_def] >>
  namedCases_on `r4` ["", "f r5"] >> simp[lift_result_def] >>
  namedCases_on `r5` ["", "g r6"] >> simp[lift_result_def] >>
  Cases_on `r6` >> simp[lift_result_def] >>
  Cases_on `eval_operand a s` >> simp[lift_result_def] >>
  Cases_on `eval_operand b s` >> simp[lift_result_def] >>
  Cases_on `eval_operand c s` >> simp[lift_result_def] >>
  Cases_on `eval_operand d s` >> simp[lift_result_def] >>
  Cases_on `eval_operand e s` >> simp[lift_result_def] >>
  Cases_on `eval_operand f s` >> simp[lift_result_def] >>
  Cases_on `eval_operand g s` >> simp[lift_result_def] >>
  IF_CASES_TAC >- simp[lift_result_def, halt_state_def, set_returndata_def] >>
  simp[] >> irule (SRULE [gas_replay_at_def] gas_exec_ext_call)
QED
Resume gas_base_data_dispatch[staticcall]:
  namedCases_on `inst.inst_operands` ["", "a ops"] >> simp[lift_result_def] >>
  namedCases_on `ops` ["", "b r1"] >> simp[lift_result_def] >>
  namedCases_on `r1` ["", "c r2"] >> simp[lift_result_def] >>
  namedCases_on `r2` ["", "d r3"] >> simp[lift_result_def] >>
  namedCases_on `r3` ["", "e r4"] >> simp[lift_result_def] >>
  namedCases_on `r4` ["", "f r5"] >> simp[lift_result_def] >>
  Cases_on `r5` >> simp[lift_result_def] >>
  Cases_on `eval_operand a s` >> simp[lift_result_def] >>
  Cases_on `eval_operand b s` >> simp[lift_result_def] >>
  Cases_on `eval_operand c s` >> simp[lift_result_def] >>
  Cases_on `eval_operand d s` >> simp[lift_result_def] >>
  Cases_on `eval_operand e s` >> simp[lift_result_def] >>
  Cases_on `eval_operand f s` >> simp[lift_result_def] >>
  irule (SRULE [gas_replay_at_def] gas_exec_ext_call)
QED
Resume gas_base_data_dispatch[delegatecall]:
  namedCases_on `inst.inst_operands` ["", "a ops"] >> simp[lift_result_def] >>
  namedCases_on `ops` ["", "b r1"] >> simp[lift_result_def] >>
  namedCases_on `r1` ["", "c r2"] >> simp[lift_result_def] >>
  namedCases_on `r2` ["", "d r3"] >> simp[lift_result_def] >>
  namedCases_on `r3` ["", "e r4"] >> simp[lift_result_def] >>
  namedCases_on `r4` ["", "f r5"] >> simp[lift_result_def] >>
  Cases_on `r5` >> simp[lift_result_def] >>
  Cases_on `eval_operand a s` >> simp[lift_result_def] >>
  Cases_on `eval_operand b s` >> simp[lift_result_def] >>
  Cases_on `eval_operand c s` >> simp[lift_result_def] >>
  Cases_on `eval_operand d s` >> simp[lift_result_def] >>
  Cases_on `eval_operand e s` >> simp[lift_result_def] >>
  Cases_on `eval_operand f s` >> simp[lift_result_def] >>
  irule (SRULE [gas_replay_at_def] gas_exec_delegatecall)
QED
Resume gas_base_data_dispatch[create]:
  IF_CASES_TAC >- simp[lift_result_def, halt_state_def, set_returndata_def] >>
  namedCases_on `inst.inst_operands` ["", "a ops"] >> simp[lift_result_def] >>
  namedCases_on `ops` ["", "b r1"] >> simp[lift_result_def] >>
  namedCases_on `r1` ["", "c r2"] >> simp[lift_result_def] >>
  Cases_on `r2` >> simp[lift_result_def] >>
  Cases_on `eval_operand a s` >> simp[lift_result_def] >>
  Cases_on `eval_operand b s` >> simp[lift_result_def] >>
  Cases_on `eval_operand c s` >> simp[lift_result_def] >>
  irule (SRULE [gas_replay_at_def] gas_exec_create)
QED
Resume gas_base_data_dispatch[create2]:
  IF_CASES_TAC >- simp[lift_result_def, halt_state_def, set_returndata_def] >>
  namedCases_on `inst.inst_operands` ["", "a ops"] >> simp[lift_result_def] >>
  namedCases_on `ops` ["", "b r1"] >> simp[lift_result_def] >>
  namedCases_on `r1` ["", "c r2"] >> simp[lift_result_def] >>
  namedCases_on `r2` ["", "d r3"] >> simp[lift_result_def] >>
  Cases_on `r3` >> simp[lift_result_def] >>
  Cases_on `eval_operand a s` >> simp[lift_result_def] >>
  Cases_on `eval_operand b s` >> simp[lift_result_def] >>
  Cases_on `eval_operand c s` >> simp[lift_result_def] >>
  Cases_on `eval_operand d s` >> simp[lift_result_def] >>
  irule (SRULE [gas_replay_at_def] gas_exec_create)
QED
Resume gas_base_data_dispatch[alloca]:
  namedCases_on `inst.inst_operands` ["", "a ops"] >> simp[lift_result_def] >>
  Cases_on `ops` >> simp[lift_result_def] >>
  Cases_on `a` >> simp[lift_result_def] >>
  irule (SRULE [gas_replay_at_def] gas_exec_alloca)
QED
Finalise gas_base_data_dispatch

Theorem gas_base_control_dispatch:
  MEM inst.inst_opcode
    [JMP; JNZ; DJMP; GETFMP; SETFMP; DALLOCA; INITIAL_FMP; BUMP;
     FMP_PARAM; RETPC_PARAM; PARAM; RET; RETFMP; DRET; STOP;
     RETURN; REVERT; SINK; ASSERT; ASSERT_UNREACHABLE; INVALID] ==>
  gas_replay_at 0 (step_inst_base inst) s
Proof
  simp[MEM] >> strip_tac >> rewrite_tac[gas_replay_at_def] >>
  qpat_assum `inst.inst_opcode = _` gas_opcode_rewrite >> gen_tac >>
  simp[lift_result_def]
  >~ [`inst.inst_opcode = JMP`] >- suspend "jmp"
  >~ [`inst.inst_opcode = JNZ`] >- suspend "jnz"
  >~ [`inst.inst_opcode = DJMP`] >- suspend "djmp"
  >~ [`inst.inst_opcode = GETFMP`] >- suspend "getfmp"
  >~ [`inst.inst_opcode = SETFMP`] >- suspend "setfmp"
  >~ [`inst.inst_opcode = DALLOCA`] >- suspend "dalloca"
  >~ [`inst.inst_opcode = INITIAL_FMP`] >- suspend "initial_fmp"
  >~ [`inst.inst_opcode = BUMP`] >- suspend "bump"
  >~ [`inst.inst_opcode = FMP_PARAM`] >- suspend "fmp_param"
  >~ [`inst.inst_opcode = RETPC_PARAM`] >- suspend "retpc_param"
  >~ [`inst.inst_opcode = PARAM`] >- suspend "param"
  >~ [`inst.inst_opcode = RET`] >- suspend "ret"
  >~ [`inst.inst_opcode = RETFMP`] >- suspend "retfmp"
  >~ [`inst.inst_opcode = DRET`] >- suspend "dret"
  >~ [`inst.inst_opcode = STOP`] >- simp[halt_state_def]
  >~ [`inst.inst_opcode = RETURN`] >- suspend "return"
  >~ [`inst.inst_opcode = REVERT`] >- suspend "revert"
  >~ [`inst.inst_opcode = ASSERT`] >- suspend "assert"
  >~ [`inst.inst_opcode = ASSERT_UNREACHABLE`] >- suspend "assert_unreachable"
QED
Resume gas_base_control_dispatch[jmp]:
  namedCases_on `inst.inst_operands` ["", "a ops"] >> simp[lift_result_def] >>
  Cases_on `ops` >> simp[lift_result_def] >>
  Cases_on `a` >> simp[lift_result_def]
QED
Resume gas_base_control_dispatch[jnz]:
  namedCases_on `inst.inst_operands` ["", "a ops"] >> simp[lift_result_def] >>
  namedCases_on `ops` ["", "b r1"] >> simp[lift_result_def] >>
  Cases_on `b` >> simp[lift_result_def] >>
  namedCases_on `r1` ["", "c r2"] >> simp[lift_result_def] >>
  Cases_on `c` >> simp[lift_result_def] >>
  Cases_on `r2` >> simp[lift_result_def] >>
  Cases_on `eval_operand a s` >> simp[lift_result_def] >>
  IF_CASES_TAC >> simp[lift_result_def]
QED
Resume gas_base_control_dispatch[djmp]:
  namedCases_on `inst.inst_operands` ["", "a ops"] >> simp[lift_result_def] >>
  Cases_on `eval_operand a s` >> simp[lift_result_def] >>
  Cases_on `extract_labels ops` >> simp[lift_result_def] >>
  IF_CASES_TAC >> simp[lift_result_def]
QED
Resume gas_base_control_dispatch[getfmp]:
  Cases_on `inst.inst_operands` >> simp[lift_result_def] >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >> simp[lift_result_def] >>
  Cases_on `outs` >> simp[lift_result_def]
QED
Resume gas_base_control_dispatch[setfmp]:
  namedCases_on `inst.inst_operands` ["", "a ops"] >> simp[lift_result_def] >>
  Cases_on `ops` >> simp[lift_result_def] >>
  Cases_on `inst.inst_outputs` >> simp[lift_result_def] >>
  Cases_on `eval_operand a s` >> simp[lift_result_def]
QED
Resume gas_base_control_dispatch[dalloca]:
  namedCases_on `inst.inst_operands` ["", "a ops"] >> simp[lift_result_def] >>
  Cases_on `ops` >> simp[lift_result_def] >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >> simp[lift_result_def] >>
  Cases_on `outs` >> simp[lift_result_def] >>
  Cases_on `eval_operand a s` >> simp[lift_result_def]
QED
Resume gas_base_control_dispatch[initial_fmp]:
  Cases_on `inst.inst_operands` >> simp[lift_result_def] >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >> simp[lift_result_def] >>
  Cases_on `outs` >> simp[lift_result_def]
QED
Resume gas_base_control_dispatch[bump]:
  namedCases_on `inst.inst_operands` ["", "a ops"] >> simp[lift_result_def] >>
  namedCases_on `ops` ["", "b r1"] >> simp[lift_result_def] >>
  Cases_on `r1` >> simp[lift_result_def] >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >> simp[lift_result_def] >>
  namedCases_on `outs` ["", "out2 rest"] >> simp[lift_result_def] >>
  Cases_on `rest` >> simp[lift_result_def] >>
  Cases_on `eval_operand a s` >> simp[lift_result_def] >>
  Cases_on `eval_operand b s` >> simp[lift_result_def]
QED
Resume gas_base_control_dispatch[fmp_param]:
  namedCases_on `inst.inst_operands` ["", "a ops"] >> simp[lift_result_def] >>
  Cases_on `a` >> simp[lift_result_def] >>
  Cases_on `ops` >> simp[lift_result_def] >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >> simp[lift_result_def] >>
  Cases_on `outs` >> simp[lift_result_def] >>
  IF_CASES_TAC >> simp[lift_result_def]
QED
Resume gas_base_control_dispatch[retpc_param]:
  namedCases_on `inst.inst_operands` ["", "a ops"] >> simp[lift_result_def] >>
  Cases_on `a` >> simp[lift_result_def] >>
  Cases_on `ops` >> simp[lift_result_def] >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >> simp[lift_result_def] >>
  Cases_on `outs` >> simp[lift_result_def]
QED
Resume gas_base_control_dispatch[param]:
  namedCases_on `inst.inst_operands` ["", "a ops"] >> simp[lift_result_def] >>
  Cases_on `a` >> simp[lift_result_def] >>
  Cases_on `ops` >> simp[lift_result_def] >>
  IF_CASES_TAC >> simp[lift_result_def] >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >> simp[lift_result_def] >>
  Cases_on `outs` >> simp[lift_result_def]
QED
Resume gas_base_control_dispatch[ret]:
  Cases_on `eval_operands inst.inst_operands s` >> simp[lift_result_def] >>
  Cases_on `x` >> simp[lift_result_def]
QED
Resume gas_base_control_dispatch[retfmp]:
  Cases_on `eval_operands inst.inst_operands s` >> simp[lift_result_def] >>
  Cases_on `x` >> simp[lift_result_def]
QED
Resume gas_base_control_dispatch[dret]:
  Cases_on `inst.inst_outputs = []` >> simp[lift_result_def] >>
  Cases_on `parse_dret_shape inst` >> simp[lift_result_def] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `eval_operands inst.inst_operands s` >> simp[lift_result_def] >>
  Cases_on `pair_dret_words (TAKE (2 * x1) (DROP (x0 + 1) x))` >>
  simp[lift_result_def] >>
  pairarg_tac >> gvs[] >>
  drule gas_pack_dret_transport >> disch_then (qspec_then `tail` assume_tac) >>
  rev_drule gas_pack_dret_readings >> simp[lift_result_def]
QED
Resume gas_base_control_dispatch[return]:
  namedCases_on `inst.inst_operands` ["", "a ops"] >> simp[lift_result_def] >>
  namedCases_on `ops` ["", "b rest"] >> simp[lift_result_def] >>
  Cases_on `rest` >> simp[lift_result_def] >>
  Cases_on `eval_operand a s` >> simp[lift_result_def] >>
  Cases_on `eval_operand b s` >> simp[lift_result_def]
QED
Resume gas_base_control_dispatch[revert]:
  namedCases_on `inst.inst_operands` ["", "a ops"] >> simp[lift_result_def] >>
  namedCases_on `ops` ["", "b rest"] >> simp[lift_result_def] >>
  Cases_on `rest` >> simp[lift_result_def] >>
  Cases_on `eval_operand a s` >> simp[lift_result_def] >>
  Cases_on `eval_operand b s` >> simp[lift_result_def]
QED
Resume gas_base_control_dispatch[assert]:
  namedCases_on `inst.inst_operands` ["", "a ops"] >> simp[lift_result_def] >>
  Cases_on `ops` >> simp[lift_result_def] >>
  Cases_on `eval_operand a s` >> simp[lift_result_def] >>
  IF_CASES_TAC >> simp[lift_result_def]
QED
Resume gas_base_control_dispatch[assert_unreachable]:
  namedCases_on `inst.inst_operands` ["", "a ops"] >> simp[lift_result_def] >>
  Cases_on `ops` >> simp[lift_result_def] >>
  Cases_on `eval_operand a s` >> simp[lift_result_def] >>
  IF_CASES_TAC >> simp[lift_result_def]
QED
Finalise gas_base_control_dispatch

Theorem gas_base_non_gas:
  inst.inst_opcode <> GAS ==> gas_replay_at 0 (step_inst_base inst) s
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >> gvs[] >>
  all_tac
  >~ [`inst.inst_opcode = MCOPY`] >- (irule gas_base_data_dispatch >> simp[])
  >~ [`inst.inst_opcode = ISTORE`] >- (irule gas_base_data_dispatch >> simp[])
  >~ [`inst.inst_opcode = CALLDATACOPY`] >- (irule gas_base_data_dispatch >> simp[])
  >~ [`inst.inst_opcode = RETURNDATACOPY`] >- (irule gas_base_data_dispatch >> simp[])
  >~ [`inst.inst_opcode = SHA3`] >- (irule gas_base_data_dispatch >> simp[])
  >~ [`inst.inst_opcode = DLOADBYTES`] >- (irule gas_base_data_dispatch >> simp[])
  >~ [`inst.inst_opcode = CODECOPY`] >- (irule gas_base_data_dispatch >> simp[])
  >~ [`inst.inst_opcode = EXTCODECOPY`] >- (irule gas_base_data_dispatch >> simp[])
  >~ [`inst.inst_opcode = LOG`] >- (irule gas_base_data_dispatch >> simp[])
  >~ [`inst.inst_opcode = SELFDESTRUCT`] >- (irule gas_base_data_dispatch >> simp[])
  >~ [`inst.inst_opcode = CALL`] >- (irule gas_base_data_dispatch >> simp[])
  >~ [`inst.inst_opcode = STATICCALL`] >- (irule gas_base_data_dispatch >> simp[])
  >~ [`inst.inst_opcode = DELEGATECALL`] >- (irule gas_base_data_dispatch >> simp[])
  >~ [`inst.inst_opcode = CREATE`] >- (irule gas_base_data_dispatch >> simp[])
  >~ [`inst.inst_opcode = CREATE2`] >- (irule gas_base_data_dispatch >> simp[])
  >~ [`inst.inst_opcode = ALLOCA`] >- (irule gas_base_data_dispatch >> simp[])
  >~ [`inst.inst_opcode = JMP`] >- (irule gas_base_control_dispatch >> simp[])
  >~ [`inst.inst_opcode = JNZ`] >- (irule gas_base_control_dispatch >> simp[])
  >~ [`inst.inst_opcode = DJMP`] >- (irule gas_base_control_dispatch >> simp[])
  >~ [`inst.inst_opcode = GETFMP`] >- (irule gas_base_control_dispatch >> simp[])
  >~ [`inst.inst_opcode = SETFMP`] >- (irule gas_base_control_dispatch >> simp[])
  >~ [`inst.inst_opcode = DALLOCA`] >- (irule gas_base_control_dispatch >> simp[])
  >~ [`inst.inst_opcode = INITIAL_FMP`] >- (irule gas_base_control_dispatch >> simp[])
  >~ [`inst.inst_opcode = BUMP`] >- (irule gas_base_control_dispatch >> simp[])
  >~ [`inst.inst_opcode = FMP_PARAM`] >- (irule gas_base_control_dispatch >> simp[])
  >~ [`inst.inst_opcode = RETPC_PARAM`] >- (irule gas_base_control_dispatch >> simp[])
  >~ [`inst.inst_opcode = PARAM`] >- (irule gas_base_control_dispatch >> simp[])
  >~ [`inst.inst_opcode = RET`] >- (irule gas_base_control_dispatch >> simp[])
  >~ [`inst.inst_opcode = RETFMP`] >- (irule gas_base_control_dispatch >> simp[])
  >~ [`inst.inst_opcode = DRET`] >- (irule gas_base_control_dispatch >> simp[])
  >~ [`inst.inst_opcode = STOP`] >- (irule gas_base_control_dispatch >> simp[])
  >~ [`inst.inst_opcode = RETURN`] >- (irule gas_base_control_dispatch >> simp[])
  >~ [`inst.inst_opcode = REVERT`] >- (irule gas_base_control_dispatch >> simp[])
  >~ [`inst.inst_opcode = SINK`] >- (irule gas_base_control_dispatch >> simp[])
  >~ [`inst.inst_opcode = ASSERT`] >- (irule gas_base_control_dispatch >> simp[])
  >~ [`inst.inst_opcode = ASSERT_UNREACHABLE`] >- (irule gas_base_control_dispatch >> simp[])
  >~ [`inst.inst_opcode = INVALID`] >- (irule gas_base_control_dispatch >> simp[]) >>
  rewrite_tac[gas_replay_at_def] >>
  qpat_assum `inst.inst_opcode = _` gas_opcode_rewrite >>
  rewrite_tac[GSYM gas_replay_at_def] >>
  simp[gas_exec_pure1, gas_exec_pure2, gas_exec_pure3] >>
  all_tac
  >>~- ([`gas_replay_at 0 (exec_read0 _ _) _`], irule gas_exec_read0 >> simp[])
  >>~- ([`gas_replay_at 0 (exec_read1 _ _) _`], irule gas_exec_read1 >> simp[])
  >>~- ([`gas_replay_at 0 (exec_write2 _ _) _`], irule gas_exec_write2 >> simp[]) >>
  simp[gas_replay_at_def, lift_result_def] >> gen_tac >>
  TRY (IF_CASES_TAC
       >- (simp[lift_result_def, halt_state_def, set_returndata_def] >> NO_TAC) >>
       simp[] >> irule (SRULE [gas_replay_at_def] gas_exec_write2) >> simp[] >>
       NO_TAC) >>
  namedCases_on `inst.inst_operands` ["", "a ops"] >> simp[lift_result_def] >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >> simp[lift_result_def] >>
  Cases_on `outs` >> simp[lift_result_def] >>
  Cases_on `ops` >> simp[lift_result_def] >>
  Cases_on `eval_operand a s` >> simp[lift_result_def]
QED

Theorem gas_step_inst:
  (!fn t. gas_replay (run_blocks fuel ctx fn) t) ==>
  gas_replay (step_inst fuel ctx inst) s
Proof
  strip_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- suspend "invoke" >>
  Cases_on `inst.inst_opcode = GAS`
  >- (rewrite_tac[gas_replay_def] >> qexists_tac `1` >>
      rewrite_tac[gas_replay_at_def] >>
      simp[step_inst_def] >>
      qpat_assum `inst.inst_opcode = GAS` gas_opcode_rewrite >>
      rewrite_tac[GSYM gas_replay_at_def] >> irule gas_exec_gas) >>
  rewrite_tac[gas_replay_def] >> qexists_tac `0` >>
  rewrite_tac[gas_replay_at_def] >> simp[step_inst_def] >>
  irule (SRULE [gas_replay_at_def] gas_base_non_gas) >> simp[]
QED
Resume gas_step_inst[invoke]:
  Cases_on `decode_invoke inst`
  >- simp[gas_replay_def, gas_replay_at_def, step_inst_def, lift_result_def] >>
  PairCases_on `x` >>
  Cases_on `lookup_function x0 ctx.ctx_functions`
  >- simp[gas_replay_def, gas_replay_at_def, step_inst_def, lift_result_def] >>
  rename1 `lookup_function x0 ctx.ctx_functions = SOME fn` >>
  Cases_on `eval_operands x1 s`
  >- simp[gas_replay_def, gas_replay_at_def, step_inst_def, lift_result_def] >>
  rename1 `eval_operands x1 s = SOME args` >>
  Cases_on `setup_callee fn args s`
  >- simp[gas_replay_def, gas_replay_at_def, step_inst_def,
          gas_setup_callee, lift_result_def] >>
  rename1 `setup_callee fn args s = SOME cs` >>
  first_x_assum (qspecl_then [`fn`, `cs`] mp_tac) >>
  rewrite_tac[gas_replay_def] >> strip_tac >> qexists_tac `n` >>
  qpat_x_assum `gas_replay_at n _ _` mp_tac >>
  simp[gas_replay_at_def, step_inst_def, gas_setup_callee] >>
  drule gas_setup_callee_readings >> strip_tac >>
  disch_tac >> gen_tac >>
  first_x_assum (qspec_then `tail` mp_tac) >>
  Cases_on `run_blocks fuel ctx fn cs` >>
  Cases_on `run_blocks fuel ctx fn
    (cs with vs_gas_readings := gas_prefix n s.vs_gas_readings ++ tail)` >>
  gvs[lift_result_def, gas_merge_callee, gas_adopt_return, gas_bind_outputs] >>
  strip_tac >> gvs[] >>
  Cases_on `bind_outputs inst.inst_outputs i.iret_values
    (adopt_return_fmp i (merge_callee_state s v))` >>
  simp[lift_result_def] >>
  drule gas_bind_outputs_readings >>
  simp[gas_adopt_return_readings]
QED
Finalise gas_step_inst

Theorem gas_replay_preupdate:
  (!u gs. h (u with vs_gas_readings := gs) =
             (h u with vs_gas_readings := gs)) /\
  (!u. (h u).vs_gas_readings = u.vs_gas_readings) /\
  gas_replay f (h s) ==>
  gas_replay (\u. f (h u)) s
Proof
  simp[gas_replay_def, gas_replay_at_def] >> rpt strip_tac >>
  qexists_tac `n` >> gvs[]
QED

Theorem gas_replay_halt_choice:
  (!u gs. b (u with vs_gas_readings := gs) = b u) /\
  gas_replay f s ==>
  gas_replay (\u. if b u then Halt u else f u) s
Proof
  strip_tac >> Cases_on `b s`
  >- (simp[gas_replay_def, gas_replay_at_def] >>
      qexists_tac `0` >> simp[lift_result_def]) >>
  gvs[gas_replay_def, gas_replay_at_def] >>
  qexists_tac `n` >> simp[]
QED

Theorem gas_replay_cong:
  f s = g s /\
  (!gs. f (s with vs_gas_readings := gs) =
        g (s with vs_gas_readings := gs)) /\
  gas_replay g s ==> gas_replay f s
Proof
  simp[gas_replay_def, gas_replay_at_def] >> metis_tac[]
QED

Theorem gas_exec_block_layer:
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  exec_block fuel ctx bb s =
    gas_bind_ok (step_inst fuel ctx inst s)
      (\t. if is_terminator inst.inst_opcode then
             (if t.vs_halted then Halt t else OK t)
           else exec_block fuel ctx bb
                  (t with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  simp[] >> Cases_on `step_inst fuel ctx inst s` >> simp[gas_bind_ok_def]
QED

Theorem gas_exec_block_compose:
  get_instruction bb s.vs_inst_idx = SOME inst /\
  gas_replay (step_inst fuel ctx inst) s /\
  (!t. step_inst fuel ctx inst s = OK t ==>
    gas_replay (\t. if is_terminator inst.inst_opcode then
                     (if t.vs_halted then Halt t else OK t)
                   else exec_block fuel ctx bb
                          (t with vs_inst_idx := SUC s.vs_inst_idx)) t) ==>
  gas_replay (exec_block fuel ctx bb) s
Proof
  strip_tac >> irule gas_replay_cong >>
  qexists_tac `\u. gas_bind_ok (step_inst fuel ctx inst u)
      (\t. if is_terminator inst.inst_opcode then
             (if t.vs_halted then Halt t else OK t)
           else exec_block fuel ctx bb
                  (t with vs_inst_idx := SUC s.vs_inst_idx))` >>
  conj_tac
  >- (gen_tac >>
      mp_tac (Q.INST [`s` |-> `s with vs_gas_readings := gs`]
        gas_exec_block_layer) >> simp[]) >>
  conj_tac >- (simp[] >> irule gas_exec_block_layer >> simp[]) >>
  irule gas_replay_bind_ok >> simp[]
QED

Theorem gas_exec_block:
  (!inst t. gas_replay (step_inst fuel ctx inst) t) ==>
  !s. gas_replay (exec_block fuel ctx bb) s
Proof
  strip_tac >> measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >> gvs[] >> rename1 `gas_replay _ s` >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (simp[gas_replay_def, gas_replay_at_def] >>
      qexists_tac `0` >> gen_tac >>
      pure_once_rewrite_tac[exec_block_def] >> simp[lift_result_def]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  suspend "compose"
QED
Resume gas_exec_block[compose]:
  irule gas_exec_block_compose >> simp[] >>
  gen_tac >> strip_tac >> Cases_on `is_terminator inst.inst_opcode`
  >- (simp[] >> irule gas_replay_halt_choice >> simp[] >>
      simp[gas_replay_def, gas_replay_at_def] >>
      qexists_tac `0` >> simp[lift_result_def]) >>
  simp[] >> irule gas_replay_preupdate >> simp[] >>
  first_x_assum irule >> simp[] >>
  gvs[venomInstTheory.get_instruction_def] >> decide_tac
QED
Finalise gas_exec_block

Theorem gas_run_block_layer:
  run_block fuel ctx bb s =
  gas_bind_ok (eval_phis s bb.bb_instructions)
    (\t. exec_block fuel ctx bb
      (t with vs_inst_idx := phi_prefix_length bb.bb_instructions))
Proof
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs >> simp[run_block_def, gas_bind_ok_def]
QED

Theorem gas_run_block:
  (!s. gas_replay (exec_block fuel ctx bb) s) ==>
  !s. gas_replay (run_block fuel ctx bb) s
Proof
  rpt strip_tac >> irule gas_replay_cong >>
  qexists_tac `\u. gas_bind_ok (eval_phis u bb.bb_instructions)
    (\t. exec_block fuel ctx bb
      (t with vs_inst_idx := phi_prefix_length bb.bb_instructions))` >>
  conj_tac >- simp[GSYM gas_run_block_layer] >>
  conj_tac >- simp[GSYM gas_run_block_layer] >>
  ho_match_mp_tac gas_replay_bind_ok >> conj_tac
  >- (simp[gas_replay_def] >> qexists_tac `0` >>
      irule gas_eval_phis) >>
  rpt strip_tac >> irule gas_replay_preupdate >> simp[]
QED

Theorem gas_run_blocks_layer:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
  run_blocks (SUC fuel) ctx fn s =
  gas_bind_ok (run_block fuel ctx bb s)
    (\t. if t.vs_halted then Halt t else run_blocks fuel ctx fn t)
Proof
  strip_tac >> CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [run_blocks_unfold])) >>
  simp[] >> Cases_on `run_block fuel ctx bb s` >> simp[gas_bind_ok_def]
QED

Theorem gas_run_blocks_suc:
  (!bb s. gas_replay (exec_block fuel ctx bb) s) /\
  (!fn s. gas_replay (run_blocks fuel ctx fn) s) ==>
  !fn s. gas_replay (run_blocks (SUC fuel) ctx fn) s
Proof
  strip_tac >> rpt gen_tac >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- (simp[gas_replay_def, gas_replay_at_def] >> qexists_tac `0` >>
      gen_tac >> pure_once_rewrite_tac[run_blocks_unfold] >>
      simp[lift_result_def]) >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  irule gas_replay_cong >>
  qexists_tac `\u. gas_bind_ok (run_block fuel ctx bb u)
    (\t. if t.vs_halted then Halt t else run_blocks fuel ctx fn t)` >>
  conj_tac
  >- (gen_tac >>
      mp_tac (Q.INST [`s` |-> `s with vs_gas_readings := gs`]
        gas_run_blocks_layer) >> simp[]) >>
  conj_tac >- (simp[] >> irule gas_run_blocks_layer >> simp[]) >>
  irule gas_replay_bind_ok >> conj_tac
  >- (rpt strip_tac >> irule gas_replay_halt_choice >> simp[]) >>
  irule gas_run_block >> simp[]
QED

Theorem gas_replay_fuel:
  !fuel ctx.
    (!fn s. gas_replay (run_blocks fuel ctx fn) s) /\
    (!inst s. gas_replay (step_inst fuel ctx inst) s) /\
    (!bb s. gas_replay (exec_block fuel ctx bb) s)
Proof
  Induct_on `fuel`
  >- (gen_tac >>
      `!fn s. gas_replay (run_blocks 0 ctx fn) s` by
        (rpt gen_tac >> simp[gas_replay_def, gas_replay_at_def] >>
         qexists_tac `0` >> gen_tac >>
         pure_once_rewrite_tac[run_blocks_def] >> simp[lift_result_def]) >>
      `!inst s. gas_replay (step_inst 0 ctx inst) s` by
        (rpt gen_tac >> irule gas_step_inst >> simp[]) >>
      simp[] >> rpt gen_tac >> irule gas_exec_block >> simp[]) >>
  gen_tac >> first_x_assum (qspec_then `ctx` strip_assume_tac) >>
  `!fn s. gas_replay (run_blocks (SUC fuel) ctx fn) s` by
    (irule gas_run_blocks_suc >> simp[]) >>
  `!inst s. gas_replay (step_inst (SUC fuel) ctx inst) s` by
    (rpt gen_tac >> irule gas_step_inst >> simp[]) >>
  simp[] >> rpt gen_tac >> irule gas_exec_block >> simp[]
QED

Theorem gas_oracle_replay:
  (!fuel ctx inst s.
     ?n. !tail.
       lift_result
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (step_inst fuel ctx inst s)
         (step_inst fuel ctx inst
           (s with vs_gas_readings :=
             TAKE n (s.vs_gas_readings ++ REPLICATE n 0w) ++ tail))) /\
  (!fuel ctx bb s.
     ?n. !tail.
       lift_result
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (exec_block fuel ctx bb s)
         (exec_block fuel ctx bb
           (s with vs_gas_readings :=
             TAKE n (s.vs_gas_readings ++ REPLICATE n 0w) ++ tail))) /\
  (!fuel ctx func s.
     ?n. !tail.
       lift_result
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (run_blocks fuel ctx func s)
         (run_blocks fuel ctx func
           (s with vs_gas_readings :=
             TAKE n (s.vs_gas_readings ++ REPLICATE n 0w) ++ tail)))
Proof
  mp_tac gas_replay_fuel >>
  pure_rewrite_tac[gas_replay_def, gas_replay_at_def, gas_prefix_def] >>
  metis_tac[]
QED
