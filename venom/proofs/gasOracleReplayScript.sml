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
  simp[gas_replay_at_def, exec_create_def, gas_extract_result] >>
  gen_tac >>
  qmatch_goalsub_abbrev_tac `extract_venom_result s v 0 0 res` >>
  Cases_on `extract_venom_result s v 0 0 res` >> simp[lift_result_def] >>
  PairCases_on `x` >> simp[] >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >> simp[lift_result_def] >>
  Cases_on `outs` >> simp[lift_result_def] >>
  metis_tac[gas_extract_result_readings]
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
  cheat
QED
