Theory regularCallEmitSim
Ancestors
  regularMemorySim venomExecSemantics venomCallOracleDefs codegenRel asmSem
  stackPlanGen contextCodegenRel venomInst asmIR
  list rich_list arithmetic venomState strongPrefixSim spillSim emitSim stackModel instSimHelpers planSpillBounds

Theorem related_tx_params:
  venom_asm_rel lo ps vs st ==>
  asm_to_tx_params st = venom_to_tx_params vs
Proof
  simp[venom_asm_rel_def, asm_to_tx_params_def, venom_to_tx_params_def]
QED

Theorem related_call_state:
  venom_asm_rel lo ps vs st ==>
  make_asm_call_state st target gas value data code static =
  make_venom_call_state vs target gas value data code static
Proof
  strip_tac >> drule related_tx_params >>
  gvs[venom_asm_rel_def, make_asm_call_state_def, make_venom_call_state_def]
QED

Theorem related_delegatecall_state:
  venom_asm_rel lo ps vs st ==>
  make_asm_delegatecall_state st target gas data code static =
  make_venom_delegatecall_state vs target gas data code static
Proof
  strip_tac >> drule related_tx_params >>
  gvs[venom_asm_rel_def, make_asm_delegatecall_state_def,
      make_venom_delegatecall_state_def]
QED

Theorem related_create_state:
  venom_asm_rel lo ps vs st ==>
  make_asm_create_state st target gas value data =
  make_venom_create_state vs target gas value data
Proof
  strip_tac >> drule related_tx_params >>
  gvs[venom_asm_rel_def, make_asm_create_state_def, make_venom_create_state_def]
QED

Theorem related_call_input_bytes:
  venom_asm_rel lo ps vs st /\
  (len = 0 \/ off + len <= ps.ps_alloc.sa_spill_base \/
   ps.ps_alloc.sa_next_offset <= off) ==>
  read_memory off len vs =
  TAKE len (DROP off (asm_expand_memory (off + len) st.as_memory))
Proof
  strip_tac >> rewrite_tac[read_memory_def, venom_returndata_read_byte] >>
  simp_tac pure_ss [expanded_slice_padded_range, LESS_EQ_REFL] >>
  irule memory_rel_padded_range >> qexists_tac `ps.ps_alloc` >>
  gvs[venom_asm_rel_def]
QED

Theorem related_call_request:
  venom_asm_rel lo ps vs st /\
  (w2n sz = 0 \/ w2n off + w2n sz <= ps.ps_alloc.sa_spill_base \/
   ps.ps_alloc.sa_next_offset <= w2n off) ==>
  asm_call_request st addr value (w2n off) (w2n sz) static =
  venom_call_request vs addr value off sz static
Proof
  strip_tac >> drule related_call_input_bytes >>
  disch_then (qspecl_then [`w2n off`, `w2n sz`] mp_tac) >>
  gvs[asm_call_request_def, venom_call_request_def, venom_asm_rel_def]
QED

Theorem related_create_request[local]:
  venom_asm_rel lo ps vs st /\
  (w2n sz = 0 \/ w2n off + w2n sz <= ps.ps_alloc.sa_spill_base \/
   ps.ps_alloc.sa_next_offset <= w2n off) ==>
  asm_create_request st value (w2n off) (w2n sz) salt_opt =
  venom_create_request vs value off sz salt_opt
Proof
  strip_tac >> drule related_call_input_bytes >>
  disch_then (qspecl_then [`w2n off`, `w2n sz`] mp_tac) >>
  gvs[asm_create_request_def, venom_create_request_def, venom_asm_rel_def]
QED

Theorem asm_call_memory_read_byte:
  read_byte i (asm_call_memory ao asz ro rsz mem) = read_byte i mem
Proof
  simp[asm_call_memory_def] >>
  Cases_on `asz = 0` >> Cases_on `rsz = 0` >> simp[read_byte_expand]
QED

Theorem asm_call_memory_return_bound:
  0 < rsz ==> ro + rsz <= LENGTH (asm_call_memory ao asz ro rsz mem)
Proof
  simp[asm_call_memory_def] >> strip_tac >>
  Cases_on `asz = 0` >> simp[]
QED

Theorem asm_call_return_write_frame:
  ~(ro <= i /\ i < ro + rsz) ==>
  read_byte i
    (TAKE ro (asm_call_memory ao asz ro rsz mem) ++ TAKE rsz data ++
     DROP (ro + LENGTH (TAKE rsz data)) (asm_call_memory ao asz ro rsz mem)) =
  read_byte i mem
Proof
  strip_tac >> Cases_on `rsz = 0`
  >- simp[TAKE_DROP, asm_call_memory_read_byte] >>
  `ro + rsz <= LENGTH (asm_call_memory ao asz ro rsz mem)` by
    (irule asm_call_memory_return_bound >> decide_tac) >>
  drule_all short_return_write_frame >> simp[asm_call_memory_read_byte]
QED

Theorem read_byte_write_memory_with_expansion:
  read_byte i (write_memory_with_expansion off bytes vs).vs_memory =
  if off <= i /\ i < off + LENGTH bytes then EL (i - off) bytes
  else read_byte i vs.vs_memory
Proof
  simp[write_memory_with_expansion_def] >>
  qmatch_goalsub_abbrev_tac `TAKE off expanded` >>
  `off + LENGTH bytes <= LENGTH expanded` by
    (simp[Abbr `expanded`] >> IF_CASES_TAC >> simp[] >> decide_tac) >>
  asm_simp_tac bool_ss [read_byte_overwrite] >>
  `read_byte i expanded = read_byte i vs.vs_memory` by
    (simp[Abbr `expanded`] >> IF_CASES_TAC >> simp[] >>
     simp[read_byte_def, EL_APPEND_EQN, EL_REPLICATE] >>
     Cases_on `i < LENGTH vs.vs_memory` >> simp[]) >>
  simp[]
QED

Theorem memory_rel_call_return_write:
  memory_rel alloc vs.vs_memory mem ==>
  memory_rel alloc (write_memory_with_expansion ro (TAKE rs data) vs).vs_memory
    (TAKE ro (asm_call_memory ao az ro rs mem) ++ TAKE rs data ++
     DROP (ro + LENGTH (TAKE rs data)) (asm_call_memory ao az ro rs mem))
Proof
  strip_tac >> Cases_on `rs = 0`
  >- (simp[TAKE_DROP] >>
      rw[memory_rel_def, read_byte_write_memory_with_expansion,
         asm_call_memory_read_byte] >> fs[memory_rel_def]) >>
  `ro + rs <= LENGTH (asm_call_memory ao az ro rs mem)` by
    (irule asm_call_memory_return_bound >> decide_tac) >>
  `ro + LENGTH (TAKE rs data) <= LENGTH (asm_call_memory ao az ro rs mem)` by
    (simp[LENGTH_TAKE_EQ] >> decide_tac) >>
  rw[memory_rel_def] >>
  asm_simp_tac bool_ss [read_byte_write_memory_with_expansion, read_byte_overwrite] >>
  Cases_on `ro <= i /\ i < ro + LENGTH (TAKE rs data)` >>
  simp[asm_call_memory_read_byte] >> fs[memory_rel_def]
QED

Theorem plan_spill_rel_call_return_write:
  !lo vs ps mem base rs ro ao az data.
  plan_spill_rel lo vs ps.ps_spilled mem /\
  plan_slots_bounded base ps /\
  (rs = 0 \/ ro + rs <= ps.ps_alloc.sa_spill_base \/
   ps.ps_alloc.sa_next_offset <= ro) ==>
  plan_spill_rel lo vs ps.ps_spilled
    (TAKE ro (asm_call_memory ao az ro rs mem) ++ TAKE rs data ++
     DROP (ro + LENGTH (TAKE rs data)) (asm_call_memory ao az ro rs mem))
Proof
  rpt gen_tac >> strip_tac >> irule plan_spill_rel_matched_write_frame >>
  qexistsl_tac [`ps.ps_alloc`, `mem`, `rs`, `ro`, `vs`] >>
  simp[asm_call_memory_read_byte, asm_call_return_write_frame] >>
  gvs[plan_slots_bounded_def, alloc_slots_bounded_def]
QED

Theorem consume_call_outcome_venom_asm_rel:
  !lo ps vs st base rs ro rq result vb ao az stk.
  venom_asm_rel lo ps vs st /\
  plan_slots_bounded base ps /\
  (rs = 0 \/ ro + rs <= ps.ps_alloc.sa_spill_base \/
   ps.ps_alloc.sa_next_offset <= ro) /\
  consume_call_outcome rq ro rs vs = (result, vb) ==>
  ?ab.
    asm_consume_call_outcome rq ro rs stk
      (st with as_memory := asm_call_memory ao az ro rs st.as_memory) = AsmOK ab /\
    ab.as_stack = result :: stk /\ ab.as_pc = st.as_pc + 1 /\
    venom_asm_rel lo ps vb (ab with as_stack := st.as_stack)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `st.as_outcomes = vs.vs_outcomes /\
   st.as_accounts = vs.vs_accounts /\
   st.as_transient = vs.vs_transient /\ st.as_logs = vs.vs_logs` by
    fs[venom_asm_rel_def] >>
  qpat_x_assum `consume_call_outcome _ _ _ _ = _` mp_tac >>
  simp_tac std_ss [consume_call_outcome_def, LET_THM] >>
  pairarg_tac >> gnvs[] >> pairarg_tac >> gnvs[] >> strip_tac >>
  simp[asm_consume_call_outcome_def, LET_THM] >>
  gnvs[asm_next_def, venom_asm_rel_def] >>
  rename1 `plan_slots_bounded spill_base ps` >>
  rename1 `take_outcome rq vs.vs_outcomes = (outcome, rest)` >>
  qmatch_goalsub_abbrev_tac `plan_stack_rel lo completed` >>
  `!op. operand_val completed lo op = operand_val vs lo op` by
    (Cases >> simp[Abbr `completed`, operand_val_def]) >>
  conj_tac
  >- fs[plan_stack_rel_def] >>
  conj_tac
  >- (simp[plan_spill_rel_def] >>
      `plan_spill_rel lo vs ps.ps_spilled
        (TAKE ro (asm_call_memory ao az ro rs st.as_memory) ++ TAKE rs outcome.co_returnData ++
         DROP (ro + LENGTH (TAKE rs outcome.co_returnData))
           (asm_call_memory ao az ro rs st.as_memory))` suffices_by
        simp[plan_spill_rel_def] >>
      irule plan_spill_rel_call_return_write >> simp[] >>
      qexists_tac `spill_base` >> simp[]) >>
  irule memory_rel_call_return_write >> simp[]
QED

Theorem consume_create_outcome_venom_asm_rel[local]:
  !lo ps vs st rq result vb off sz stk.
  venom_asm_rel lo ps vs st /\
  consume_create_outcome rq vs = (result, vb) ==>
  ?ab.
    asm_consume_create_outcome rq stk
      (st with as_memory := asm_call_memory off sz 0 0 st.as_memory) = AsmOK ab /\
    ab.as_stack = result :: stk /\ ab.as_pc = st.as_pc + 1 /\
    venom_asm_rel lo ps vb (ab with as_stack := st.as_stack)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `st.as_outcomes = vs.vs_outcomes /\
   st.as_accounts = vs.vs_accounts /\
   st.as_transient = vs.vs_transient /\ st.as_logs = vs.vs_logs` by
    fs[venom_asm_rel_def] >>
  qpat_x_assum `consume_create_outcome _ _ = _` mp_tac >>
  simp_tac std_ss [consume_create_outcome_def, LET_THM] >>
  pairarg_tac >> gnvs[] >> pairarg_tac >> gnvs[] >> strip_tac >>
  simp[asm_consume_create_outcome_def, LET_THM] >>
  gnvs[asm_next_def, venom_asm_rel_def] >>
  qmatch_goalsub_abbrev_tac `plan_stack_rel lo completed` >>
  `!op. operand_val completed lo op = operand_val vs lo op` by
    (Cases >> simp[Abbr `completed`, operand_val_def]) >>
  conj_tac >- fs[plan_stack_rel_def] >>
  conj_tac
  >- (`plan_spill_rel lo vs ps.ps_spilled
         (asm_call_memory off sz 0 0 st.as_memory)` suffices_by
        simp[plan_spill_rel_def] >>
      Cases_on `sz = 0` >> simp[asm_call_memory_def] >>
      irule plan_spill_rel_expand >> simp[]) >>
  fs[memory_rel_def, asm_call_memory_read_byte] >> metis_tac[]
QED

Theorem memory_rel_expanded_return_write[local]:
  memory_rel alloc vs.vs_memory mem ==>
  memory_rel alloc (write_memory_with_expansion ro (TAKE rs data) vs).vs_memory
    (TAKE ro (asm_expand_memory (ro + rs) mem) ++ TAKE rs data ++
     DROP (ro + LENGTH (TAKE rs data)) (asm_expand_memory (ro + rs) mem))
Proof
  strip_tac >> Cases_on `rs = 0`
  >- (simp[TAKE_DROP] >>
      rw[memory_rel_def, read_byte_write_memory_with_expansion, read_byte_expand] >>
      fs[memory_rel_def]) >>
  `asm_expand_memory (ro + rs) mem = asm_call_memory 0 0 ro rs mem` by
    simp[asm_call_memory_def] >>
  asm_rewrite_tac[] >> irule memory_rel_call_return_write >> simp[]
QED

Theorem plan_spill_rel_expanded_return_write[local]:
  !lo vs ps mem sb rs ro data.
  plan_spill_rel lo vs ps.ps_spilled mem /\
  plan_slots_bounded sb ps /\
  (rs = 0 \/ ro + rs <= ps.ps_alloc.sa_spill_base \/
   ps.ps_alloc.sa_next_offset <= ro) ==>
  plan_spill_rel lo vs ps.ps_spilled
    (TAKE ro (asm_expand_memory (ro + rs) mem) ++ TAKE rs data ++
     DROP (ro + LENGTH (TAKE rs data)) (asm_expand_memory (ro + rs) mem))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `rs = 0`
  >- (simp[TAKE_DROP] >> irule plan_spill_rel_expand >> simp[]) >>
  `asm_expand_memory (ro + rs) mem = asm_call_memory 0 0 ro rs mem` by
    simp[asm_call_memory_def] >>
  asm_rewrite_tac[] >> irule plan_spill_rel_call_return_write >> simp[] >>
  qexists_tac `sb` >> simp[]
QED

Theorem extract_result_venom_asm_rel:
  !lo ps vs st sb rs ro output rr result vb.
  venom_asm_rel lo ps vs st /\ plan_slots_bounded sb ps /\
  (rs = 0 \/ ro + rs <= ps.ps_alloc.sa_spill_base \/
   ps.ps_alloc.sa_next_offset <= ro) /\
  extract_venom_result vs output ro rs rr = SOME (result, vb) ==>
  ?ab. extract_asm_result st output ro rs rr = SOME (result, ab) /\
       venom_asm_rel lo ps vb ab /\
       ab.as_stack = st.as_stack /\ ab.as_pc = st.as_pc
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `rr` >- fs[extract_venom_result_def] >>
  rename1 `extract_venom_result _ _ _ _ (SOME pair)` >>
  PairCases_on `pair` >>
  qpat_x_assum `extract_venom_result _ _ _ _ _ = _` mp_tac >>
  simp[extract_venom_result_def, AllCaseEqs()] >>
  strip_tac >>
  qpat_x_assum `_ = SOME (result, vb)` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >>
  `st.as_accounts = vs.vs_accounts /\ st.as_transient = vs.vs_transient /\
   st.as_logs = vs.vs_logs` by fs[venom_asm_rel_def] >>
  simp[extract_asm_result_def, LET_THM] >>
  gnvs[venom_asm_rel_def] >>
  rename1 `state.contexts = [(ctxt, tag)]` >>
  qmatch_goalsub_abbrev_tac `plan_stack_rel lo completed` >>
  `!op. operand_val completed lo op = operand_val vs lo op` by
    (Cases >> simp[Abbr `completed`, operand_val_def]) >>
  conj_tac >- fs[plan_stack_rel_def] >>
  conj_tac
  >- (simp[plan_spill_rel_def] >>
      `plan_spill_rel lo vs ps.ps_spilled
        (TAKE ro (asm_expand_memory (ro + rs) st.as_memory) ++ TAKE rs ctxt.returnData ++
         DROP (ro + LENGTH (TAKE rs ctxt.returnData))
           (asm_expand_memory (ro + rs) st.as_memory))` suffices_by
        simp[plan_spill_rel_def] >>
      irule plan_spill_rel_expanded_return_write >> simp[] >>
      qexists_tac `sb` >> simp[]) >>
  irule memory_rel_expanded_return_write >> simp[]
QED

(* CALL completion includes its PC advance; restore only the input stack
   for the output bridge, whose PC advance is irrelevant to the relation. *)
Theorem ext_call_emit_venom_asm_rel:
  venom_asm_rel lo ps vs st /\ plan_slots_bounded sb ps /\
  st.as_stack = (if with_value then
    gas :: addr :: value :: ao :: az :: ro :: rs :: stk
    else gas :: addr :: ao :: az :: ro :: rs :: stk) /\
  (~with_value ==> value = 0w /\ static) /\
  (w2n az = 0 \/ w2n ao + w2n az <= ps.ps_alloc.sa_spill_base \/
   ps.ps_alloc.sa_next_offset <= w2n ao) /\
  (w2n rs = 0 \/ w2n ro + w2n rs <= ps.ps_alloc.sa_spill_base \/
   ps.ps_alloc.sa_next_offset <= w2n ro) /\
  inst.inst_outputs = [out] /\
  EVERY (\op. case op of Var x => x <> out | _ => T) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
    case op of Var x => x <> out | _ => T) /\
  exec_ext_call inst vs gas addr value ao az ro rs static = OK vs' ==>
  ?ab. (if with_value then asm_exec_call static st
        else asm_exec_staticcall st) = AsmOK ab /\
    ab.as_pc = st.as_pc + 1 /\
    venom_asm_rel lo
      (ps with ps_stack := stack_push (Var out)
        (stack_pop (if with_value then 7 else 6) ps.ps_stack))
      vs' ab
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `exec_ext_call _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac std_ss [exec_ext_call_def, LET_THM] >> pairarg_tac >>
  pure_asm_rewrite_tac[] >> strip_tac >>
  rename1 `consume_call_outcome _ _ _ _ = (output, vb)` >>
  `asm_call_request st addr value (w2n ao) (w2n az) static =
   venom_call_request vs addr value ao az static` by
    (irule related_call_request >> qexistsl_tac [`lo`, `ps`] >> simp[]) >>
  drule_all consume_call_outcome_venom_asm_rel >>
  disch_then (qspecl_then [`w2n ao`, `w2n az`, `stk`] strip_assume_tac) >>
  qpat_x_assum `consume_call_outcome _ _ _ _ = _` kall_tac >>
  qexists_tac `ab` >> conj_tac
  >- (Cases_on `with_value` >> gvs[asm_exec_call_def, asm_exec_staticcall_def]) >>
  simp[] >>
  `(if with_value then 7 else 6) <= LENGTH ps.ps_stack` by
    (Cases_on `with_value` >> fs[venom_asm_rel_def, plan_stack_rel_def]) >>
  drule emit_output_venom_asm_rel >>
  disch_then (qspecl_then [`output`, `out`, `if with_value then 7 else 6`] mp_tac) >>
  Cases_on `with_value` >>
  gvs[asm_next_def, venom_asm_rel_def, update_var_def]
QED

Theorem delegatecall_emit_venom_asm_rel:
  venom_asm_rel lo ps vs st /\ plan_slots_bounded sb ps /\
  st.as_stack = gas :: addr :: ao :: az :: ro :: rs :: stk /\
  (w2n az = 0 \/ w2n ao + w2n az <= ps.ps_alloc.sa_spill_base \/
   ps.ps_alloc.sa_next_offset <= w2n ao) /\
  (w2n rs = 0 \/ w2n ro + w2n rs <= ps.ps_alloc.sa_spill_base \/
   ps.ps_alloc.sa_next_offset <= w2n ro) /\
  inst.inst_outputs = [out] /\
  EVERY (\op. case op of Var x => x <> out | _ => T) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
    case op of Var x => x <> out | _ => T) /\
  exec_delegatecall inst vs gas addr ao az ro rs = OK vs' ==>
  ?ab. asm_exec_delegatecall st = AsmOK ab /\
    ab.as_pc = st.as_pc + 1 /\
    venom_asm_rel lo
      (ps with ps_stack := stack_push (Var out) (stack_pop 6 ps.ps_stack))
      vs' ab
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `read_memory (w2n ao) (w2n az) vs =
    TAKE (w2n az) (DROP (w2n ao)
      (asm_expand_memory (w2n ao + w2n az) st.as_memory))` by
    (irule related_call_input_bytes >> qexistsl_tac [`lo`, `ps`] >> simp[]) >>
  `st.as_accounts = vs.vs_accounts /\ st.as_call_ctx = vs.vs_call_ctx` by
    fs[venom_asm_rel_def] >>
  drule related_delegatecall_state >> strip_tac >>
  qpat_x_assum `exec_delegatecall _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac std_ss [exec_delegatecall_def, LET_THM] >>
  simp_tac (srw_ss()) [AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `_ = (_, _)` SUBST_ALL_TAC >>
  drule_all extract_result_venom_asm_rel >> strip_tac >> gnvs[] >>
  `6 <= LENGTH ps.ps_stack` by
    fs[venom_asm_rel_def, plan_stack_rel_def] >>
  qexists_tac `asm_next (ab with as_stack := output :: stk)` >>
  conj_tac
  >- simp[asm_exec_delegatecall_def, LET_THM] >>
  simp[asm_next_def] >>
  drule emit_output_venom_asm_rel >>
  disch_then (qspecl_then [`output`, `out`, `6`] mp_tac) >>
  gvs[asm_next_def, venom_asm_rel_def, update_var_def]
QED

Theorem create_emit_venom_asm_rel:
  venom_asm_rel lo ps vs st /\ plan_slots_bounded sb ps /\
  st.as_stack = (case salt_opt of
    NONE => value :: off :: sz :: stk
    | SOME salt => value :: off :: sz :: salt :: stk) /\
  (w2n sz = 0 \/ w2n off + w2n sz <= ps.ps_alloc.sa_spill_base \/
   ps.ps_alloc.sa_next_offset <= w2n off) /\
  inst.inst_outputs = [out] /\
  EVERY (\op. case op of Var x => x <> out | _ => T) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
    case op of Var x => x <> out | _ => T) /\
  exec_create inst vs value off sz salt_opt = OK vs' ==>
  ?ab. (case salt_opt of NONE => asm_exec_create st
        | SOME salt => asm_exec_create2 st) = AsmOK ab /\
    ab.as_pc = st.as_pc + 1 /\
    venom_asm_rel lo
      (ps with ps_stack := stack_push (Var out)
        (stack_pop (case salt_opt of NONE => 3 | SOME salt => 4) ps.ps_stack))
      vs' ab
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `exec_create _ _ _ _ _ _ = _` mp_tac >>
  simp_tac std_ss [exec_create_def, LET_THM] >> pairarg_tac >>
  pure_asm_rewrite_tac[] >> strip_tac >>
  rename1 `consume_create_outcome _ _ = (output, vb)` >>
  `asm_create_request st value (w2n off) (w2n sz) salt_opt =
   venom_create_request vs value off sz salt_opt` by
    (irule related_create_request >> qexistsl_tac [`lo`, `ps`] >> simp[]) >>
  drule_all consume_create_outcome_venom_asm_rel >>
  disch_then (qspecl_then [`w2n off`, `w2n sz`, `stk`] strip_assume_tac) >>
  qpat_x_assum `consume_create_outcome _ _ = _` kall_tac >>
  qexists_tac `ab` >> conj_tac
  >- (Cases_on `salt_opt` >> gvs[asm_exec_create_def, asm_exec_create2_def]) >>
  simp[] >>
  `(case salt_opt of NONE => 3 | SOME salt => 4) <= LENGTH ps.ps_stack` by
    (Cases_on `salt_opt` >> fs[venom_asm_rel_def, plan_stack_rel_def]) >>
  drule emit_output_venom_asm_rel >>
  disch_then (qspecl_then [`output`, `out`,
    `case salt_opt of NONE => 3 | SOME salt => 4`] mp_tac) >>
  Cases_on `salt_opt` >>
  gvs[asm_next_def, venom_asm_rel_def, update_var_def]
QED

(* compute_operands is bottom-to-top for these opcodes: its reversal is
   the semantic argument list consumed by the assembly instruction. *)
Theorem call_arranged_emit_sim:
  inst.inst_opcode = CALL /\ inst.inst_outputs = [out] /\
  venom_asm_rel lo ps vs st /\ plan_slots_bounded sb ps /\
  ps.ps_stack = residual ++ compute_operands inst /\
  EVERY (\op. op <> dead_stack_marker) (compute_operands inst) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op vs = operand_val vs lo op) /\
  EVERY (\op. case op of Var x => x <> out | _ => T) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
    case op of Var x => x <> out | _ => T) /\
  EVERY (\(off,len). len = 0 \/ off + len <= ps.ps_alloc.sa_spill_base \/
    ps.ps_alloc.sa_next_offset <= off) (source_memory_read_ranges inst vs) /\
  inst_memory_safe ps.ps_alloc inst vs vs' /\
  step_inst fuel ctx inst vs = OK vs' ==>
  ?ab. asm_exec_call st.as_call_ctx.cc_static st = AsmOK ab /\
    ab.as_pc = st.as_pc + 1 /\
    venom_asm_rel lo
      (ps with ps_stack := stack_push (Var out) (stack_pop 7 ps.ps_stack))
      vs' ab
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >>
  gnvs[compute_operands_def, python_stack_operands_def,
       ir_specific_operand_order_def] >>
  rename1 `exec_ext_call inst vs gas addr value ao az ro rs _ = _` >>
  rename1 `inst.inst_operands = [gop; aop; vop; iop; izop; rop; rzop]` >>
  `eval_operands [gop; aop; vop; iop; izop; rop; rzop] vs =
    SOME [gas; addr; value; ao; az; ro; rs]` by simp[eval_operands_def] >>
  drule_at (Pat `eval_operands _ _ = _`) arranged_eval_operands_stack >>
  disch_then (qspecl_then [`st`, `residual`, `ps`, `lo`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  simp[] >> strip_tac >>
  `st.as_call_ctx = vs.vs_call_ctx` by fs[venom_asm_rel_def] >>
  `w2n az = 0 \/ w2n ao + w2n az <= ps.ps_alloc.sa_spill_base \/
    ps.ps_alloc.sa_next_offset <= w2n ao` by
    (qpat_x_assum `EVERY _ (source_memory_read_ranges _ _)` mp_tac >>
     simp[source_memory_read_ranges_def, memory_range_of_operands_def, ADD_COMM]) >>
  `w2n rs = 0 \/ w2n ro + w2n rs <= ps.ps_alloc.sa_spill_base \/
    ps.ps_alloc.sa_next_offset <= w2n ro` by
    (qpat_x_assum `inst_memory_safe _ _ _ _` mp_tac >>
     simp[inst_memory_safe_def, source_memory_writes_disjoint_def,
          source_memory_write_ranges_def, ADD_COMM]) >>
  qpat_assum `ps.ps_stack = _` (fn th => once_rewrite_tac [GSYM th]) >>
  irule (SRULE [] (Q.INST [`with_value` |-> `T`] ext_call_emit_venom_asm_rel)) >>
  (conj_tac >- simp[]) >>
  (conj_tac >- simp[]) >>
  (conj_tac >- (qexists_tac `sb` >> simp[])) >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`inst`, `vs`] >> fs[]
QED

Theorem external_arranged_emit_sim:
  MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  inst.inst_outputs = [out] /\
  venom_asm_rel lo ps vs st /\ plan_slots_bounded sb ps /\
  ps.ps_stack = residual ++ compute_operands inst /\
  EVERY (\op. op <> dead_stack_marker) (compute_operands inst) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op vs = operand_val vs lo op) /\
  EVERY (\op. case op of Var x => x <> out | _ => T) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
    case op of Var x => x <> out | _ => T) /\
  EVERY (\(off,len). len = 0 \/ off + len <= ps.ps_alloc.sa_spill_base \/
    ps.ps_alloc.sa_next_offset <= off) (source_memory_read_ranges inst vs) /\
  inst_memory_safe ps.ps_alloc inst vs vs' /\
  step_inst fuel ctx inst vs = OK vs' ==>
  ?ab. asm_step_op o2pc name st = AsmOK ab /\
    ab.as_pc = st.as_pc + 1 /\
    venom_asm_rel lo
      (ps with ps_stack := stack_push (Var out)
        (stack_pop (LENGTH (compute_operands inst)) ps.ps_stack)) vs' ab
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `MEM _ _` mp_tac >> simp[] >> strip_tac
  >- suspend "call"
  >- suspend "staticcall"
  >- suspend "delegatecall"
  >- suspend "create"
  >> suspend "create2"
QED

Resume external_arranged_emit_sim[call]:
  drule_all call_arranged_emit_sim >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >>
  fs[venom_to_evm_name_def, compute_operands_def, python_stack_operands_def,
     ir_specific_operand_order_def] >>
  qexists_tac `ab` >>
  simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def,
       asm_step_extcall_def] >>
  qpat_assum `ps.ps_stack = _` (fn th => once_rewrite_tac [GSYM th]) >>
  first_assum ACCEPT_TAC
QED
Resume external_arranged_emit_sim[staticcall]:
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >>
  gnvs[compute_operands_def, python_stack_operands_def,
       ir_specific_operand_order_def, venom_to_evm_name_def] >>
  rename1 `exec_ext_call inst vs gas addr _ ao az ro rs _ = _` >>
  rename1 `inst.inst_operands = [gop; aop; iop; izop; rop; rzop]` >>
  `eval_operands [gop; aop; iop; izop; rop; rzop] vs =
    SOME [gas; addr; ao; az; ro; rs]` by simp[eval_operands_def] >>
  drule_at (Pat `eval_operands _ _ = _`) arranged_eval_operands_stack >>
  disch_then (qspecl_then [`st`, `residual`, `ps`, `lo`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  simp[] >> strip_tac >>
  `w2n az = 0 \/ w2n ao + w2n az <= ps.ps_alloc.sa_spill_base \/
    ps.ps_alloc.sa_next_offset <= w2n ao` by
    (qpat_x_assum `EVERY _ (source_memory_read_ranges _ _)` mp_tac >>
     simp[source_memory_read_ranges_def, memory_range_of_operands_def, ADD_COMM]) >>
  `w2n rs = 0 \/ w2n ro + w2n rs <= ps.ps_alloc.sa_spill_base \/
    ps.ps_alloc.sa_next_offset <= w2n ro` by
    (qpat_x_assum `inst_memory_safe _ _ _ _` mp_tac >>
     simp[inst_memory_safe_def, source_memory_writes_disjoint_def,
          source_memory_write_ranges_def, ADD_COMM]) >>
  simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def,
       asm_step_extcall_def] >>
  qpat_assum `ps.ps_stack = _` (fn th => once_rewrite_tac [GSYM th]) >>
  irule (SRULE [] (Q.INST [`with_value` |-> `F`, `value` |-> `0w`,
    `static` |-> `T`] ext_call_emit_venom_asm_rel)) >>
  (conj_tac >- simp[]) >>
  (conj_tac >- simp[]) >>
  (conj_tac >- (qexists_tac `sb` >> simp[])) >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`inst`, `vs`] >> fs[]
QED
Resume external_arranged_emit_sim[delegatecall]:
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >>
  gnvs[compute_operands_def, python_stack_operands_def,
       ir_specific_operand_order_def, venom_to_evm_name_def] >>
  rename1 `exec_delegatecall inst vs gas addr ao az ro rs = _` >>
  rename1 `inst.inst_operands = [gop; aop; iop; izop; rop; rzop]` >>
  `eval_operands [gop; aop; iop; izop; rop; rzop] vs =
    SOME [gas; addr; ao; az; ro; rs]` by simp[eval_operands_def] >>
  drule_at (Pat `eval_operands _ _ = _`) arranged_eval_operands_stack >>
  disch_then (qspecl_then [`st`, `residual`, `ps`, `lo`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  simp[] >> strip_tac >>
  `w2n az = 0 \/ w2n ao + w2n az <= ps.ps_alloc.sa_spill_base \/
    ps.ps_alloc.sa_next_offset <= w2n ao` by
    (qpat_x_assum `EVERY _ (source_memory_read_ranges _ _)` mp_tac >>
     simp[source_memory_read_ranges_def, memory_range_of_operands_def, ADD_COMM]) >>
  `w2n rs = 0 \/ w2n ro + w2n rs <= ps.ps_alloc.sa_spill_base \/
    ps.ps_alloc.sa_next_offset <= w2n ro` by
    (qpat_x_assum `inst_memory_safe _ _ _ _` mp_tac >>
     simp[inst_memory_safe_def, source_memory_writes_disjoint_def,
          source_memory_write_ranges_def, ADD_COMM]) >>
  simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def,
       asm_step_extcall_def] >>
  qpat_assum `ps.ps_stack = _` (fn th => once_rewrite_tac [GSYM th]) >>
  irule delegatecall_emit_venom_asm_rel >>
  (conj_tac >- simp[]) >>
  (conj_tac >- simp[]) >>
  (conj_tac >- (qexists_tac `sb` >> simp[])) >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`inst`, `vs`] >> fs[]
QED
Resume external_arranged_emit_sim[create]:
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >>
  gnvs[compute_operands_def, python_stack_operands_def,
       ir_specific_operand_order_def, venom_to_evm_name_def] >>
  rename1 `exec_create inst vs value off sz NONE = _` >>
  rename1 `inst.inst_operands = [vop; oop; sop]` >>
  `eval_operands [vop; oop; sop] vs = SOME [value; off; sz]` by
    simp[eval_operands_def] >>
  drule_at (Pat `eval_operands _ _ = _`) arranged_eval_operands_stack >>
  disch_then (qspecl_then [`st`, `residual`, `ps`, `lo`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  simp[] >> strip_tac >>
  `w2n sz = 0 \/ w2n off + w2n sz <= ps.ps_alloc.sa_spill_base \/
    ps.ps_alloc.sa_next_offset <= w2n off` by
    (qpat_x_assum `EVERY _ (source_memory_read_ranges _ _)` mp_tac >>
     simp[source_memory_read_ranges_def, memory_range_of_operands_def, ADD_COMM]) >>
  simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def,
       asm_step_extcall_def] >>
  qpat_assum `ps.ps_stack = _` (fn th => once_rewrite_tac [GSYM th]) >>
  irule (SRULE [] (Q.INST [`salt_opt` |-> `NONE`] create_emit_venom_asm_rel)) >>
  (conj_tac >- simp[]) >>
  (conj_tac >- simp[]) >>
  (conj_tac >- (qexists_tac `sb` >> simp[])) >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`inst`, `vs`] >> fs[]
QED
Resume external_arranged_emit_sim[create2]:
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >>
  gnvs[compute_operands_def, python_stack_operands_def,
       ir_specific_operand_order_def, venom_to_evm_name_def] >>
  rename1 `exec_create inst vs value off sz (SOME salt) = _` >>
  rename1 `inst.inst_operands = [vop; oop; sop; salt_op]` >>
  `eval_operands [vop; oop; sop; salt_op] vs = SOME [value; off; sz; salt]` by
    simp[eval_operands_def] >>
  drule_at (Pat `eval_operands _ _ = _`) arranged_eval_operands_stack >>
  disch_then (qspecl_then [`st`, `residual`, `ps`, `lo`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  simp[] >> strip_tac >>
  `w2n sz = 0 \/ w2n off + w2n sz <= ps.ps_alloc.sa_spill_base \/
    ps.ps_alloc.sa_next_offset <= w2n off` by
    (qpat_x_assum `EVERY _ (source_memory_read_ranges _ _)` mp_tac >>
     simp[source_memory_read_ranges_def, memory_range_of_operands_def, ADD_COMM]) >>
  simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def,
       asm_step_extcall_def] >>
  qpat_assum `ps.ps_stack = _` (fn th => once_rewrite_tac [GSYM th]) >>
  irule (SRULE [] (Q.INST [`salt_opt` |-> `SOME salt`] create_emit_venom_asm_rel)) >>
  (conj_tac >- simp[]) >>
  (conj_tac >- simp[]) >>
  (conj_tac >- (qexists_tac `sb` >> simp[])) >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`inst`, `vs`] >> fs[]
QED
Finalise external_arranged_emit_sim
