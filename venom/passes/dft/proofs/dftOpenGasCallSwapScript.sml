(* Local normal-return diamond; no cross-context or uniform-witness claim. *)
Theory dftOpenGasCallSwap
Ancestors
  dftOpenReservation dftOpenMachine dftCommutation venomState venomExecSemantics venomInst arithmetic

Theorem dft_call_operands_index:
  eval_operands ops (s with vs_inst_idx := i) = eval_operands ops s
Proof
  Induct_on `ops` >> simp[eval_operands_def] >>
  gen_tac >> Cases_on `h` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem dft_call_setup_index:
  setup_callee fn args (s with vs_inst_idx := i) = setup_callee fn args s
Proof
  simp[setup_callee_def, venom_state_component_equality]
QED

Theorem dft_call_setup_reserved:
  ~MEM (Var out) ops ==>
  eval_operands ops (update_var out v s with vs_inst_idx := i) =
    eval_operands ops s /\
  setup_callee fn args (update_var out v s with vs_inst_idx := i) =
    setup_callee fn args s
Proof
  simp[dft_call_operands_index, eval_operands_update_var,
       dft_call_setup_index, setup_callee_update_var]
QED

Theorem dft_call_adopt_reserved[local]:
  adopt_return_fmp ret (update_var out v s) =
  update_var out v (adopt_return_fmp ret s)
Proof
  Cases_on `ret.iret_adopt_fmp` >> simp[adopt_return_fmp_def, update_var_def]
QED

Theorem dft_call_return_reserved:
  ~MEM out outs /\
  bind_outputs outs vals (adopt_return_fmp ret (merge_callee_state s cr)) = SOME after ==>
  bind_outputs outs vals
    (adopt_return_fmp ret (merge_callee_state (update_var out v s) cr)) =
    SOME (update_var out v after)
Proof
  strip_tac >> simp[merge_callee_update_var, dft_call_adopt_reserved,
    bind_outputs_update_var]
QED

Theorem dft_call_fold_index[local]:
  !pairs s i.
  FOLDL (\st (x,v). update_var x v st) (s with vs_inst_idx := i) pairs =
  (FOLDL (\st (x,v). update_var x v st) s pairs) with vs_inst_idx := i
Proof
  Induct >> simp[pairTheory.FORALL_PROD] >> rpt gen_tac >>
  `update_var p_1 p_2 (s with vs_inst_idx := i) =
   update_var p_1 p_2 s with vs_inst_idx := i`
    by simp[update_var_def] >>
  asm_rewrite_tac[]
QED

Theorem dft_call_bind_index[local]:
  bind_outputs outs vals (s with vs_inst_idx := i) =
  OPTION_MAP (\st. st with vs_inst_idx := i) (bind_outputs outs vals s)
Proof
  simp[bind_outputs_def, dft_call_fold_index] >>
  IF_CASES_TAC >> simp[]
QED

Theorem dft_call_merge_index[local]:
  merge_callee_state (s with vs_inst_idx := i) cr =
  merge_callee_state s cr with vs_inst_idx := i
Proof
  simp[merge_callee_state_def, venom_state_component_equality]
QED

Theorem dft_call_adopt_index[local]:
  adopt_return_fmp ret (s with vs_inst_idx := i) =
  adopt_return_fmp ret s with vs_inst_idx := i
Proof
  Cases_on `ret.iret_adopt_fmp` >> simp[adopt_return_fmp_def]
QED

Theorem dft_call_return_reserved_index:
  ~MEM out outs /\
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s cr)) = SOME after ==>
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret
      (merge_callee_state (update_var out v s with vs_inst_idx := i) cr)) =
    SOME (update_var out v after with vs_inst_idx := i)
Proof
  strip_tac >>
  simp[dft_call_merge_index, dft_call_adopt_index, dft_call_bind_index] >>
  drule_all dft_call_return_reserved >> simp[]
QED

Theorem dft_call_adjacent_setup:
  bs.bb_instructions = pre ++ gas::call::post /\
  bt.bb_instructions = pre ++ call::gas::post /\
  s.vs_inst_idx = LENGTH pre /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [out] /\
  call.inst_opcode = INVOKE /\ decode_invoke call = SOME (nm,ops) /\
  ~MEM (Var out) ops /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  s1 = (update_var out (a q) s with vs_inst_idx := SUC s.vs_inst_idx) ==>
  dft_open_next a ctx (DftOpen (DftAt fn budget bt s) rest 0) =
    DftOpen (DftEnter callee budget cs) (DftCaller fn budget bt call s::rest) 0 /\
  FUNPOW (dft_open_next (dft_reserve_oracle q a) ctx) 2
    (DftOpen (DftAt fn budget bs s) rest 0) =
    DftOpen (DftEnter callee budget cs) (DftCaller fn budget bs call s1::rest) 1
Proof
  strip_tac >>
  `eval_operands ops s1 = SOME args /\ setup_callee callee args s1 = SOME cs`
    by gvs[dft_call_operands_index, eval_operands_update_var,
           dft_call_setup_index, setup_callee_update_var] >>
  `get_instruction bs s.vs_inst_idx = SOME gas /\
   get_instruction bs s1.vs_inst_idx = SOME call /\
   get_instruction bt s.vs_inst_idx = SOME call`
    by simp[get_instruction_def, listTheory.EL_APPEND_EQN] >>
  drule_all dft_reserve_gas_call_setup >> simp[]
QED

Theorem dft_call_adjacent_return:
  bt.bb_instructions = pre ++ call::gas::post /\
  s.vs_inst_idx = LENGTH pre /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [out] /\
  call.inst_opcode = INVOKE /\ ~MEM out call.inst_outputs /\
  LENGTH call.inst_outputs = LENGTH ret.iret_values /\
  s1 = (update_var out (a q) s with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?u. u.vs_inst_idx = LENGTH pre + 2 /\
    dft_open_next (dft_reserve_oracle q a) ctx
      (DftOpen (DftDone (IntRet ret cr)) (DftCaller fn budget bs call s1::rest) (SUC q)) =
      DftOpen (DftAt fn budget bs u) rest (SUC q) /\
    FUNPOW (dft_open_next a ctx) 2
      (DftOpen (DftDone (IntRet ret cr)) (DftCaller fn budget bt call s::rest) q) =
      DftOpen (DftAt fn budget bt u) rest (SUC q)
Proof
  strip_tac >>
  `?after. bind_outputs call.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s cr)) = SOME after`
    by simp[bind_outputs_def] >>
  `bind_outputs call.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s1 cr)) =
    SOME (update_var out (a q) after with vs_inst_idx := SUC s.vs_inst_idx)`
    by (gvs[] >> irule dft_call_return_reserved_index >> simp[]) >>
  qexists_tac `update_var out (a q) after with vs_inst_idx := LENGTH pre + 2` >>
  gvs[] >>
  `SUC (SUC (LENGTH pre)) = LENGTH pre + 2` by decide_tac >>
  conj_tac
  >- simp[dft_open_next_def, dft_open_return_def, dft_open_deliver_def,
          dft_open_continue_def, is_terminator_def] >>
  `dft_open_next a ctx
    (DftOpen (DftDone (IntRet ret cr)) (DftCaller fn budget bt call s::rest) q) =
    DftOpen (DftAt fn budget bt (after with vs_inst_idx := SUC s.vs_inst_idx)) rest q`
    by (irule dft_open_return_resume >> simp[]) >>
  simp[arithmeticTheory.FUNPOW_2] >>
  simp[dft_open_next_def, get_instruction_def, listTheory.EL_APPEND_EQN,
       dft_open_deliver_def, dft_open_continue_def, is_terminator_def,
       update_var_def]
QED

Theorem dft_call_protected_endpoint[local]:
  (!j. j <= t ==>
    FUNPOW (dft_open_next a ctx) j (DftOpen c0 (ft::rest) 0) =
      DftOpen (c j) (k j ++ ft::rest) (n j) /\ n j <= q) /\
  (!j. j < t ==> ~(k j = [] /\ ?r. c j = DftDone r)) /\
  c t = DftDone (IntRet ret cr) /\ k t = [] /\ n t = q ==>
  FUNPOW (dft_open_next (dft_reserve_oracle q a) ctx) t
    (DftOpen c0 (fs::rest) 1) =
    DftOpen (DftDone (IntRet ret cr)) (fs::rest) (SUC q)
Proof
  strip_tac >>
  `!j. j <= t ==> FUNPOW (dft_open_next (dft_reserve_oracle q a) ctx) j
      (DftOpen c0 (fs::rest) 1) =
      DftOpen (c j) (k j ++ fs::rest) (SUC (n j))`
    by (ho_match_mp_tac (Q.INST [`rt` |-> `rest`] dft_protected_prefixes) >> metis_tac[]) >>
  first_x_assum (qspec_then `t` mp_tac) >> simp[]
QED

(* Both executions join in caller STATE, not in the differently scheduled blocks.
   The segment hypothesis protects the saved caller at every interior prefix. *)
Theorem dft_open_gas_call_diamond:
  bs.bb_instructions = pre ++ gas::call::post /\
  bt.bb_instructions = pre ++ call::gas::post /\ bs.bb_label = bt.bb_label /\
  s.vs_inst_idx = LENGTH pre /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [out] /\
  call.inst_opcode = INVOKE /\ decode_invoke call = SOME (nm,ops) /\
  ~MEM (Var out) ops /\ ~MEM out call.inst_outputs /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  s1 = (update_var out (a q) s with vs_inst_idx := SUC s.vs_inst_idx) /\
  (!j. j <= t ==>
    FUNPOW (dft_open_next a ctx) j
      (DftOpen (DftEnter callee budget cs) (DftCaller fn budget bt call s::rest) 0) =
      DftOpen (c j) (k j ++ DftCaller fn budget bt call s::rest) (n j) /\ n j <= q) /\
  (!j. j < t ==> ~(k j = [] /\ ?r. c j = DftDone r)) /\
  c t = DftDone (IntRet ret cr) /\ k t = [] /\ n t = q /\
  LENGTH call.inst_outputs = LENGTH ret.iret_values ==>
  ?u. u.vs_inst_idx = LENGTH pre + 2 /\
    FUNPOW (dft_open_next (dft_reserve_oracle q a) ctx) (t+3)
      (DftOpen (DftAt fn budget bs s) rest 0) =
      DftOpen (DftAt fn budget bs u) rest (SUC q) /\
    FUNPOW (dft_open_next a ctx) (t+3)
      (DftOpen (DftAt fn budget bt s) rest 0) =
      DftOpen (DftAt fn budget bt u) rest (SUC q)
Proof
  strip_tac >>
  drule_all dft_call_adjacent_setup >>
  disch_then (qspecl_then [`rest`, `fn`, `budget`] strip_assume_tac) >>
  `FUNPOW (dft_open_next (dft_reserve_oracle q a) ctx) t
      (DftOpen (DftEnter callee budget cs) (DftCaller fn budget bs call s1::rest) 1) =
    DftOpen (DftDone (IntRet ret cr)) (DftCaller fn budget bs call s1::rest) (SUC q)`
    by metis_tac[dft_call_protected_endpoint] >>
  `FUNPOW (dft_open_next a ctx) t
      (DftOpen (DftEnter callee budget cs) (DftCaller fn budget bt call s::rest) 0) =
    DftOpen (DftDone (IntRet ret cr)) (DftCaller fn budget bt call s::rest) q`
    by (first_x_assum (qspec_then `t` mp_tac) >> simp[]) >>
  drule_all dft_call_adjacent_return >>
  disch_then (qspecl_then [`rest`, `fn`, `ctx`] mp_tac) >>
  disch_then (qspecl_then [`cr`, `budget`, `bs`] strip_assume_tac) >>
  qpat_x_assum `s1 = _` kall_tac >>
  qpat_x_assum `s.vs_inst_idx = _` kall_tac >>
  qexists_tac `u` >> simp[] >> conj_tac
  >- (`t+3 = 1+(t+2)` by decide_tac >>
      qpat_x_assum `t+3 = _` (fn th => pure_once_rewrite_tac[th]) >>
      pure_rewrite_tac[FUNPOW_ADD] >> asm_rewrite_tac[FUNPOW_1]) >>
  `t+3 = 2+(t+1)` by decide_tac >>
  qpat_x_assum `t+3 = _` (fn th => pure_once_rewrite_tac[th]) >>
  pure_rewrite_tac[FUNPOW_ADD] >> asm_rewrite_tac[FUNPOW_1]
QED
