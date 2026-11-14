Theory concretizePtrDallocaHaltSteps
Ancestors
  concretizePtrDallocaTerminalProbe opcodeClass ptrDiscipline
  venomExecSemantics venomState venomInst contextCodegenRel words list pred_set

(* These operational boundaries do not assume a source outgoing event.
   SELFDESTRUCT needs only staticness and defined beneficiary operands to halt;
   no balance equality is needed for existence or returned bytes. SINK keeps
   incoming returndata, so its clean-byte comparison is an explicit premise. *)
Theorem ptr_dalloca_nonreturn_halt_step:
  inst.inst_opcode = it.inst_opcode /\
  (it.inst_opcode = STOP \/ it.inst_opcode = SINK \/
   it.inst_opcode = SELFDESTRUCT) /\
  step_inst fuelt CT it t = Halt th /\
  (it.inst_opcode = SELFDESTRUCT ==>
    s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static /\
    eval_operands inst.inst_operands s = eval_operands it.inst_operands t) /\
  (it.inst_opcode = SINK ==> s.vs_returndata = t.vs_returndata) ==>
  ?sh. step_inst fuel CS inst s = Halt sh /\
       ret_taint un it t SUBSET ret_taint tn inst s /\
       LENGTH sh.vs_returndata = LENGTH th.vs_returndata /\
       (!i. i < LENGTH sh.vs_returndata /\ i NOTIN ret_taint tn inst s ==>
            EL i sh.vs_returndata = EL i th.vs_returndata)
Proof
  strip_tac
  >- (gvs[Once step_inst_non_invoke, step_inst_base_def,
          ret_taint_def, halt_state_def] >>
      simp[Once step_inst_non_invoke, step_inst_base_def, halt_state_def])
  >- (gvs[Once step_inst_non_invoke, step_inst_base_def,
          ret_taint_def, halt_state_def] >>
      simp[Once step_inst_non_invoke, step_inst_base_def, halt_state_def])
  >> gvs[] >>
  qpat_x_assum `step_inst fuelt CT it t = _` mp_tac >>
  simp[Once step_inst_non_invoke, step_inst_base_def] >>
  Cases_on `it.inst_operands`
  >- simp[AllCaseEqs()] >>
  rename1 `it.inst_operands = beneficiary::rest` >> Cases_on `rest`
  >- (Cases_on `eval_operand beneficiary t` >>
      simp[eval_operands_def, AllCaseEqs()] >> strip_tac >>
      gvs[eval_operands_def, AllCaseEqs()] >>
      Cases_on `inst.inst_operands` >> gvs[eval_operands_def] >>
      rename1 `inst.inst_operands = src::tail` >>
      Cases_on `tail` >> gvs[eval_operands_def, AllCaseEqs()] >>
      simp[Once step_inst_non_invoke, step_inst_base_def,
           ret_taint_def, halt_state_def, set_returndata_def])
  >- simp[AllCaseEqs()]
QED

Theorem ptr_dalloca_return_halt_step:
  inst.inst_opcode = RETURN /\ inst.inst_operands = [a;n] /\
  it.inst_opcode = RETURN /\ it.inst_operands = [a_t;n_t] /\
  eval_operand a s = SOME off /\ eval_operand n s = SOME sz /\
  eval_operand a_t t = SOME offt /\ eval_operand n_t t = SOME sz /\
  (!i. i < w2n sz /\ w2n offt + i IN un.t_mem ==>
       w2n off + i IN tn.t_mem) /\
  (!i. i < w2n sz /\ w2n off + i NOTIN tn.t_mem ==>
       read_byte (w2n off + i) s.vs_memory =
       read_byte (w2n offt + i) t.vs_memory) /\
  step_inst fuelt CT it t = Halt th ==>
  ?sh. step_inst fuel CS inst s = Halt sh /\
       ret_taint un it t SUBSET ret_taint tn inst s /\
       LENGTH sh.vs_returndata = LENGTH th.vs_returndata /\
       (!i. i < LENGTH sh.vs_returndata /\ i NOTIN ret_taint tn inst s ==>
            EL i sh.vs_returndata = EL i th.vs_returndata)
Proof
  strip_tac >>
  `step_inst fuel CS inst s =
     Halt (halt_state (set_returndata (read_memory (w2n off) (w2n sz) s) s))` by
    simp[Once step_inst_non_invoke, step_inst_base_def, read_memory_def] >>
  goal_assum drule >> irule ptr_dalloca_return_mask >>
  metis_tac[]
QED

(* Complete pre-state comparison list: same terminal opcode; relative RETURN
   offset witnesses, equal size, taint reflection and clean memory bytes;
   SELFDESTRUCT staticness and evaluated operands; SINK incoming returndata.
   This deliberately leaves persistent-state comparisons to the history join. *)
Theorem ptr_dalloca_halt_step:
  frame_reachable vs CS stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode = it.inst_opcode /\ it.inst_opcode <> INVOKE /\
  step_inst fuelt CT it t = Halt th /\
  (it.inst_opcode = RETURN ==>
    ?a n a_t n_t off offt sz.
      inst.inst_operands = [a;n] /\ it.inst_operands = [a_t;n_t] /\
      eval_operand a s = SOME off /\ eval_operand n s = SOME sz /\
      eval_operand a_t t = SOME offt /\ eval_operand n_t t = SOME sz /\
      (!i. i < w2n sz /\ w2n offt + i IN un.t_mem ==>
           w2n off + i IN tn.t_mem) /\
      (!i. i < w2n sz /\ w2n off + i NOTIN tn.t_mem ==>
           read_byte (w2n off + i) s.vs_memory =
           read_byte (w2n offt + i) t.vs_memory)) /\
  (it.inst_opcode = SELFDESTRUCT ==>
    s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static /\
    eval_operands inst.inst_operands s = eval_operands it.inst_operands t) /\
  (it.inst_opcode = SINK ==> s.vs_returndata = t.vs_returndata) ==>
  ?sh. step_inst fuel CS inst s = Halt sh /\
       final_taint vs CS sh (step_taint inst s sh tn) (ret_taint tn inst s) /\
       ret_taint un it t SUBSET ret_taint tn inst s /\
       LENGTH sh.vs_returndata = LENGTH th.vs_returndata /\
       (!i. i < LENGTH sh.vs_returndata /\ i NOTIN ret_taint tn inst s ==>
            EL i sh.vs_returndata = EL i th.vs_returndata)
Proof
  strip_tac >>
  `?sh. step_inst fuel CS inst s = Halt sh /\
        ret_taint un it t SUBSET ret_taint tn inst s /\
        LENGTH sh.vs_returndata = LENGTH th.vs_returndata /\
        (!i. i < LENGTH sh.vs_returndata /\ i NOTIN ret_taint tn inst s ==>
             EL i sh.vs_returndata = EL i th.vs_returndata)` by
    (Cases_on `it.inst_opcode = RETURN`
     >- (irule ptr_dalloca_return_halt_step >> gvs[] >> metis_tac[]) >>
     irule ptr_dalloca_nonreturn_halt_step >>
     drule step_inst_halt_opcodes >> simp[] >> metis_tac[]) >>
  qexists `sh` >> simp[] >>
  simp[final_taint_def] >> metis_tac[]
QED
