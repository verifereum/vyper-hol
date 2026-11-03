Theory frameViewCall
Ancestors
  frameViewFacts frameViewMemory frameViewWrite frameRel venomState
  venomExecSemantics venomCallOracleDefs contextCodegenRel codegenRel list

Theorem venom_call_request_frame_view:
  read_memory (w2n argsOff) (w2n argsSize)
    (s with vs_memory := m) = read_memory (w2n argsOff) (w2n argsSize) s ==>
  venom_call_request (frame_view fn ra s with vs_memory := m)
    addr value argsOff argsSize is_static =
  venom_call_request s addr value argsOff argsSize is_static
Proof
  simp[venom_call_request_def, read_memory_def, frame_view_def]
QED

Theorem make_venom_delegatecall_state_frame_view:
  make_venom_delegatecall_state (frame_view fn ra s with vs_memory := m)
    target gas calldata code is_static =
  make_venom_delegatecall_state s target gas calldata code is_static
Proof
  simp[make_venom_delegatecall_state_def, venom_to_tx_params_def, frame_view_def]
QED

Theorem make_venom_create_state_frame_view:
  make_venom_create_state (frame_view fn ra s with vs_memory := m)
    addr gas value init_code =
  make_venom_create_state s addr gas value init_code
Proof
  simp[make_venom_create_state_def, venom_to_tx_params_def, frame_view_def]
QED

Theorem consume_call_outcome_frame_view:
  consume_call_outcome rq ro rs (frame_view fn ra s with vs_memory := m) =
  (FST (consume_call_outcome rq ro rs s),
   frame_view fn ra (SND (consume_call_outcome rq ro rs s)) with
     vs_memory := (SND (consume_call_outcome rq ro rs
                         (s with vs_memory := m))).vs_memory)
Proof
  simp[consume_call_outcome_eq, frame_view_def,
       write_memory_with_expansion_def]
QED

Theorem consume_call_outcome_byte_agreement:
  read_byte i m = read_byte i s.vs_memory ==>
  read_byte i (SND (consume_call_outcome rq ro rs
                     (s with vs_memory := m))).vs_memory =
  read_byte i (SND (consume_call_outcome rq ro rs s)).vs_memory
Proof
  simp[consume_call_outcome_eq, write_memory_byte_agreement]
QED

Theorem consume_call_outcome_byte_frame:
  ~(ro <= i /\ i < ro + rs) ==>
  read_byte i (SND (consume_call_outcome rq ro rs
                     (s with vs_memory := m))).vs_memory = read_byte i m
Proof
  strip_tac >>
  simp[consume_call_outcome_eq, read_byte_write_memory_with_expansion] >>
  IF_CASES_TAC >> gvs[LENGTH_TAKE_EQ]
QED

Theorem extract_venom_result_frame_view:
  extract_venom_result s output ro rs result = SOME (w, t) ==>
  extract_venom_result (frame_view fn ra s with vs_memory := m)
    output ro rs result =
  SOME (w, frame_view fn ra t with
    vs_memory := (write_memory_with_expansion ro
      (TAKE rs t.vs_returndata) (s with vs_memory := m)).vs_memory)
Proof
  simp[extract_venom_result_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  pairarg_tac >> fs[frame_view_def] >> gvs[] >>
  simp[write_memory_with_expansion_def]
QED

Theorem exec_ext_call_frame_view:
  ~retpc_var fn out /\ inst.inst_outputs = [out] /\
  read_memory (w2n argsOff) (w2n argsSize) (s with vs_memory := m) =
    read_memory (w2n argsOff) (w2n argsSize) s ==>
  exec_ext_call inst (frame_view fn ra s with vs_memory := m)
    gas addr value argsOff argsSize retOff retSize is_static =
  OK (frame_view fn ra
    (update_var out
      (FST (consume_call_outcome
        (venom_call_request s addr value argsOff argsSize is_static)
        (w2n retOff) (w2n retSize) s))
      (SND (consume_call_outcome
        (venom_call_request s addr value argsOff argsSize is_static)
        (w2n retOff) (w2n retSize) s))) with
    vs_memory := (SND (consume_call_outcome
      (venom_call_request s addr value argsOff argsSize is_static)
      (w2n retOff) (w2n retSize) (s with vs_memory := m))).vs_memory)
Proof
  strip_tac >>
  drule venom_call_request_frame_view >> strip_tac >>
  simp[exec_ext_call_def, consume_call_outcome_frame_view,
       frame_view_update_var, update_var_def]
QED

val opcode_equations = CONJUNCTS step_inst_base_opcode_eqs;
fun opcode_equation opc =
  valOf (List.find
    (fn th => aconv (rhs (fst (dest_imp (snd (strip_forall (concl th)))))) opc)
    opcode_equations);

Theorem oracle_call_base_frame_view:
  ssa_form fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode [CALL; STATICCALL] /\ step_inst_base inst s = OK s' /\
  (!i. source_memory_read_byte inst s i ==>
       read_byte i m = read_byte i s.vs_memory) ==>
  ?m'. step_inst_base inst (frame_view fn ra s with vs_memory := m) =
         OK (frame_view fn ra s' with vs_memory := m') /\
       (!i. read_byte i m = read_byte i s.vs_memory ==>
            read_byte i m' = read_byte i s'.vs_memory) /\
       (!i. EVERY (\r. ~byte_in_memory_range r i)
              (source_memory_write_ranges inst s) ==>
            read_byte i m' = read_byte i m)
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==>
    eval_operand op (frame_view fn ra s with vs_memory := m) = eval_operand op s`
    by (rpt strip_tac >> irule eval_operand_frame_view >> gen_tac >> disch_tac >>
        irule ordinary_operand_not_retpc >> simp[] >> qexists_tac `inst` >> gvs[]) >>
  qpat_x_assum `MEM inst.inst_opcode _` mp_tac >> simp[] >> strip_tac >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  simp[Once (opcode_equation ``CALL``), Once (opcode_equation ``STATICCALL``),
       AllCaseEqs(), Excl "consume_call_outcome_eq"] >> strip_tac >> gvs[] >>
  qpat_x_assum `exec_ext_call _ _ _ _ _ _ _ _ _ _ = OK s'` mp_tac >>
  simp[exec_ext_call_def, AllCaseEqs(), Excl "consume_call_outcome_eq"] >>
  pairarg_tac >> simp[AllCaseEqs(), Excl "consume_call_outcome_eq"] >>
  strip_tac >> gvs[Excl "consume_call_outcome_eq"] >>
  rename1 `consume_call_outcome
    (venom_call_request s target _ argOff argSize _) (w2n retOff) (w2n retSize) s = (w,t)` >>
  rename1 `inst.inst_outputs = [out]` >>
  `~retpc_var fn out` by
    (irule noncopy_output_not_retpc >> simp[] >> qexists_tac `inst` >> simp[]) >>
  `read_memory (w2n argOff) (w2n argSize) (s with vs_memory := m) =
   read_memory (w2n argOff) (w2n argSize) s` by
    (simp[read_memory_def] >> irule padded_memory_read_cong >>
     rpt strip_tac >> first_x_assum irule >>
     simp[source_memory_read_byte_def, source_memory_read_ranges_def,
          memory_range_of_operands_def, byte_in_memory_range_def]) >>
  qmatch_asmsub_abbrev_tac `consume_call_outcome rq (w2n retOff) (w2n retSize) s` >>
  qexists_tac `(SND (consume_call_outcome rq (w2n retOff) (w2n retSize)
                        (s with vs_memory := m))).vs_memory` >>
  (conj_tac
   >- (simp[opcode_equation ``CALL``, opcode_equation ``STATICCALL``,
            Excl "consume_call_outcome_eq"] >>
       drule venom_call_request_frame_view >> strip_tac >>
       simp[exec_ext_call_def, consume_call_outcome_frame_view,
            frame_view_update_var,
            Excl "consume_call_outcome_eq"] >>
       simp[Abbr `rq`, frame_view_def, update_var_def,
            Excl "consume_call_outcome_eq"]) >>
   conj_tac
   >- (rpt strip_tac >>
       drule (consume_call_outcome_byte_agreement) >>
       disch_then (qspecl_then [`w2n retSize`, `rq`, `w2n retOff`] mp_tac) >>
       simp[update_var_def, Excl "consume_call_outcome_eq"]) >>
   simp[source_memory_write_ranges_def, sized_source_write_range_def,
        byte_in_memory_range_def, Excl "consume_call_outcome_eq"] >>
   rpt strip_tac >> irule consume_call_outcome_byte_frame >> simp[])
QED

Theorem extract_venom_result_memory:
  extract_venom_result s output ro rs result = SOME (w,t) ==>
  t.vs_memory = (write_memory_with_expansion ro
    (TAKE rs t.vs_returndata) s).vs_memory
Proof
  simp[extract_venom_result_def, AllCaseEqs()] >>
  rpt strip_tac >> pairarg_tac >> gvs[]
QED

Theorem exec_delegatecall_frame_view:
  exec_delegatecall inst s gas addr argOff argSize retOff retSize = OK t /\
  inst.inst_outputs = [out] /\ ~retpc_var fn out /\
  read_memory (w2n argOff) (w2n argSize) (s with vs_memory := m) =
    read_memory (w2n argOff) (w2n argSize) s ==>
  ?bytes. LENGTH bytes <= w2n retSize /\
    t.vs_memory = (write_memory_with_expansion (w2n retOff) bytes s).vs_memory /\
    exec_delegatecall inst (frame_view fn ra s with vs_memory := m)
      gas addr argOff argSize retOff retSize =
    OK (frame_view fn ra t with vs_memory :=
      (write_memory_with_expansion (w2n retOff) bytes
        (s with vs_memory := m)).vs_memory)
Proof
  strip_tac >>
  qpat_x_assum `exec_delegatecall _ _ _ _ _ _ _ _ = OK t` mp_tac >>
  simp[exec_delegatecall_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `extract_venom_result s 1w _ _ _ = SOME (w,u)` >>
  qexists_tac `TAKE (w2n retSize) u.vs_returndata` >>
  drule extract_venom_result_memory >> strip_tac >>
  simp[LENGTH_TAKE_EQ, update_var_def] >>
  drule extract_venom_result_frame_view >>
  disch_then (qspecl_then [`ra`, `m`, `fn`] assume_tac) >>
  fs[read_memory_def] >>
  simp[exec_delegatecall_def, read_memory_def,
       make_venom_delegatecall_state_frame_view] >>
  fs[frame_view_def] >> simp[update_var_def, finite_mapTheory.FMAP_MAP2_FUPDATE]
QED
