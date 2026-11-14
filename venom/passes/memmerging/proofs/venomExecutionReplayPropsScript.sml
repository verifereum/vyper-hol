(* Execution histories, trace transport and paired-run facts. *)
Theory venomExecutionReplayProps
Ancestors
  dftGasFromListTraceDefs unitMemInv o1PassLift allocaRemapSSA
  venomWf stateEquiv mmTraceProofs dftIndexedExec
  removeUnusedProofs analysisSimProofsBase venomFnInstsProofs venomInst
  venomExecSemantics venomExecProofs venomInstProofs venomInstProps
  venomWfProps stateFrame stateEquivProofs execEquivProofs
  instIdxIndep passSharedFrame contextCodegenRel o1ContractCfgNorm
  dfgCorrectnessProof rich_list list
Libs
  wordsLib finite_mapLib stepInstBaseLib

Theorem trace_step_every:
  reachability_closed Inv ctx ==>
  EVERY (\((p,d,id),f,i,t). p = [] ==> P f i t)
    (trace_step [] d fuel ctx fn inst s)
Proof
  strip_tac >> drule (cj 1 mm_trace_root_inv) >>
  disch_then (qspecl_then [`[]`, `d`, `fuel`, `fn`, `inst`, `s`] mp_tac) >>
  simp[EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]
QED

Theorem trace_visit_every:
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  (EVERY (\((p,d,id),f,i,t). p = [] ==> P f i t)
     (trace_block [] d fuel ctx fn bb s) <=>
   P fn inst s /\
   EVERY (\((p,d,id),f,i,t). p = [] ==> P f i t)
     (trace_step [] d fuel ctx fn inst s) /\
   (case step_inst fuel ctx inst s of
      OK u => is_terminator inst.inst_opcode \/
        EVERY (\((p,d,id),f,i,t). p = [] ==> P f i t)
          (trace_block [] d fuel ctx fn bb
            (u with vs_inst_idx := SUC s.vs_inst_idx))
    | _ => T))
Proof
  strip_tac >> drule trace_block_visit >> disch_then (fn th => once_rewrite_tac[th]) >>
  simp[EVERY_APPEND] >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[]
QED

Theorem trace_visit_root_every:
  reachability_closed Inv ctx /\
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  (EVERY (\((p,d,id),f,i,t). p = [] ==> P f i t)
     (trace_block [] d fuel ctx fn bb s) <=>
   P fn inst s /\
   (case step_inst fuel ctx inst s of
      OK u => is_terminator inst.inst_opcode \/
        EVERY (\((p,d,id),f,i,t). p = [] ==> P f i t)
          (trace_block [] d fuel ctx fn bb
            (u with vs_inst_idx := SUC s.vs_inst_idx))
    | _ => T))
Proof
  strip_tac >>
  `EVERY (\((p,d,id),f,i,t). p = [] ==> P f i t)
     (trace_step [] d fuel ctx fn inst s)` by
    (irule trace_step_every >> metis_tac[]) >>
  drule trace_visit_every >>
  disch_then (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem trace_enter_every:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s bb.bb_instructions = OK sp ==>
  (EVERY (\((p,d,id),f,i,t). p = [] ==> P f i t)
     (trace_blocks [] d (SUC fuel) ctx fn s) <=>
   EVERY (\((p,d,id),f,i,t). p = [] ==> P f i t)
     (trace_block [] (SUC d) fuel ctx fn bb
       (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)) /\
   (case exec_block fuel ctx bb
       (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) of
      OK u => u.vs_halted \/
        EVERY (\((p,d,id),f,i,t). p = [] ==> P f i t)
          (trace_blocks [] (SUC d) fuel ctx fn u)
    | _ => T))
Proof
  strip_tac >> drule_all trace_blocks_enter >> disch_then (fn th => once_rewrite_tac[th]) >>
  simp[EVERY_APPEND] >>
  Cases_on `exec_block fuel ctx bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >> simp[] >>
  rename1 `OK u` >> Cases_on `u.vs_halted` >> simp[]
QED

Theorem trace_function_every:
  EVERY (\((p,d,id),f,i,t). p = [] ==> P f i t)
    (trace_function fuel ctx fn s) <=>
  (case fn_entry_label fn of
     NONE => T
   | SOME lbl =>
     EVERY (\((p,d,id),f,i,t). p = [] ==> P f i t)
       (trace_blocks [] 0 fuel ctx fn
         (s with <|vs_current_bb := lbl; vs_inst_idx := 0|>)))
Proof
  Cases_on `fn_entry_label fn` >> simp[trace_function_def]
QED

Theorem alloca_memory_frame:
  i.inst_opcode = ALLOCA /\ step_inst fuel ctx i s = OK u ==>
  step_inst fuel ctx i (s with vs_memory := mem) = OK (u with vs_memory := mem)
Proof
  strip_tac >>
  gvs[venomExecSemanticsTheory.step_inst_non_invoke,
    venomExecSemanticsTheory.step_inst_base_opcode_eqs,
    venomExecSemanticsTheory.exec_alloca_def, AllCaseEqs()] >>
  gvs[venomStateTheory.update_var_def]
QED

Theorem state_non_ok:
  state_equiv excluded ((H n) with vs_inst_idx := pc) t /\
  (!v. MEM (Var v) i.inst_operands ==> v NOTIN excluded) /\
  ~is_terminator i.inst_opcode /\
  ~(?u. step_inst fuel ctx i (H n) = OK u) ==>
  lift_result (\_ _. F) (execution_equiv excluded) revert_equiv
    (step_inst fuel ctx i (H n)) (step_inst fuel ctx i t)
Proof
  strip_tac >>
  `result_equiv excluded
    (step_inst fuel ctx i ((H n) with vs_inst_idx := pc))
    (step_inst fuel ctx i t)` by
    (irule removeUnusedProofsTheory.step_inst_result_equiv_full >> simp[]) >>
  Cases_on `i.inst_opcode = INVOKE`
  >- (gvs[analysisSimProofsBaseTheory.invoke_step_inst_idx_OK_only] >>
      Cases_on `step_inst fuel ctx i (H n)` >>
      Cases_on `step_inst fuel ctx i t` >>
      gvs[result_equiv_def, lift_result_def, execution_equiv_def,
        revert_equiv_def, stateFrameTheory.execution_frame_def]) >>
  gvs[analysisSimProofsBaseTheory.step_inst_idx_indep] >>
  Cases_on `step_inst fuel ctx i (H n)` >>
  Cases_on `step_inst fuel ctx i t` >>
  gvs[instIdxIndepTheory.exec_result_map_def, result_equiv_def,
    lift_result_def, execution_equiv_def, revert_equiv_def,
    stateFrameTheory.execution_frame_def, venomStateTheory.lookup_var_def]
QED

Theorem source_stopping_history:
  !xs bb s h r.
  xs = DROP h bb.bb_instructions /\ h = s.vs_inst_idx /\
  h <= LENGTH bb.bb_instructions /\
  r = exec_block fuel ctx bb s /\ ~(?err. r = Error err) /\
  EVERY (\((p,d',id),f,i,t). p = [] ==> static_mem_ok eom ctx f i t)
    (trace_block [] d fuel ctx fn bb s) ==>
  ?n H. h <= n /\ n < LENGTH bb.bb_instructions /\ H h = s /\
    (!q. h <= q /\ q <= n ==> (H q).vs_inst_idx = q) /\
    (!q. h <= q /\ q < n ==>
      ~is_terminator (EL q bb.bb_instructions).inst_opcode /\
      ?u. step_inst fuel ctx (EL q bb.bb_instructions) (H q) = OK u /\
        H (SUC q) = u with vs_inst_idx := SUC q) /\
    (!q. h <= q /\ q <= n ==>
      static_mem_ok eom ctx fn (EL q bb.bb_instructions) (H q)) /\
    (is_terminator (EL n bb.bb_instructions).inst_opcode \/
      ~(?u. step_inst fuel ctx (EL n bb.bb_instructions) (H n) = OK u)) /\
    r = dft_exec_suffix fuel ctx [EL n bb.bb_instructions] (H n)
Proof
  Induct_on `xs`
  >- (rpt strip_tac >>
      `exec_block fuel ctx bb s = dft_exec_suffix fuel ctx [] s` by
        (irule dft_exec_suffix_boundary >> gvs[]) >>
      gvs[dft_exec_suffix_def]) >>
  map_every qx_gen_tac [`i`,`bb`,`s`,`j`,`r`] >> strip_tac >>
  `j < LENGTH bb.bb_instructions` by
    (qpat_x_assum `_::_ = DROP _ _` (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
     simp[LENGTH_DROP] >> decide_tac) >>
  `get_instruction bb s.vs_inst_idx = SOME i` by
    (simp[venomInstTheory.get_instruction_def] >>
     qpat_x_assum `_::_ = DROP _ _` (mp_tac o AP_TERM ``EL 0:instruction list -> instruction``) >>
     simp[EL_DROP]) >>
  `EL j bb.bb_instructions = i` by gvs[venomInstTheory.get_instruction_def] >>
  `exec_block fuel ctx bb s = dft_exec_suffix fuel ctx (i::xs) s` by
    (irule dft_exec_suffix_boundary >> gvs[]) >>
  drule dftGasFromListTraceDefsTheory.trace_block_visit >>
  disch_then (fn th => qpat_x_assum `EVERY _ _` (mp_tac o REWRITE_RULE [th])) >>
  simp[EVERY_APPEND] >> strip_tac >>
  Cases_on `is_terminator i.inst_opcode \/ ~(?u. step_inst fuel ctx i s = OK u)`
  >- (`r = dft_exec_suffix fuel ctx [i] s` by
        (qpat_x_assum `exec_block fuel ctx bb s = dft_exec_suffix _ _ _ _` mp_tac >>
         Cases_on `step_inst fuel ctx i s` >>
         simp[dft_exec_suffix_def] >> gvs[]) >>
      qexistsl [`j`,`\q. s`] >> simp[] >>
      simp[DECIDE ``(j:num) <= q /\ q <= j <=> q = j``] >>
      metis_tac[]) >>
  gvs[] >> rename1 `step_inst fuel ctx i s = OK u` >>
  `xs = DROP (SUC s.vs_inst_idx) bb.bb_instructions` by
    (qpat_x_assum `_::_ = DROP _ _`
      (mp_tac o AP_TERM ``DROP 1:instruction list -> instruction list``) >>
     simp[DROP_DROP,arithmeticTheory.ADD1]) >>
  `exec_block fuel ctx bb (u with vs_inst_idx := SUC s.vs_inst_idx) =
    dft_exec_suffix fuel ctx xs (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule dft_exec_suffix_boundary >> simp[]) >>
  `dft_exec_suffix fuel ctx (DROP s.vs_inst_idx bb.bb_instructions) s =
    exec_block fuel ctx bb (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (qpat_x_assum `_::_ = DROP _ _` (assume_tac o SYM) >>
     asm_rewrite_tac[dft_exec_suffix_def] >> simp[]) >>
  first_x_assum (qspecl_then [`bb`,`u with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
  simp[] >> (impl_tac >- gvs[]) >>
  strip_tac >>
  qexistsl [`n`,`\q. if q = s.vs_inst_idx then s else H q`] >>
  simp[] >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `q = s.vs_inst_idx` >>
  gvs[venomInstTheory.get_instruction_def] >>
  `SUC s.vs_inst_idx <= q` by decide_tac >>
  simp[] >> metis_tac[]
QED

Theorem source_history_label:
  (!q. h <= q /\ q < n ==>
    ~is_terminator (EL q is).inst_opcode /\
    ?u. step_inst fuel ctx (EL q is) (H q) = OK u /\
      H (SUC q) = u with vs_inst_idx := SUC q) ==>
  !q. h <= q /\ q <= n ==> (H q).vs_current_bb = (H h).vs_current_bb
Proof
  strip_tac >> Induct >> rpt strip_tac
  >- (`h = 0` by decide_tac >> gvs[]) >>
  Cases_on `SUC q = h` >- simp[] >>
  `h <= q /\ q < n` by decide_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule_all venomInstProofsTheory.step_preserves_control_flow >>
  simp[] >> metis_tac[]
QED

Theorem state_noninvoke_abort:
  state_equiv excluded
    ((H n) with <|vs_memory := t.vs_memory; vs_inst_idx := pc|>) t /\
  (!v. MEM (Var v) i.inst_operands ==> v NOTIN excluded) /\
  ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
  step_inst fuel ctx i (H n) = Abort a u ==>
  ?v. step_inst fuel ctx i t = Abort a v /\ revert_equiv u v
Proof
  strip_tac >>
  `(!v. MEM (Var v) i.inst_operands ==> lookup_var v (H n) = lookup_var v t) /\
   (H n).vs_returndata = t.vs_returndata /\
   (H n).vs_labels = t.vs_labels /\
   (H n).vs_call_ctx.cc_static = t.vs_call_ctx.cc_static` by
    (gvs[state_equiv_def, execution_equiv_def, venomStateTheory.lookup_var_def] >>
     metis_tac[]) >>
  `step_inst_base i (H n) = Abort a u` by
    gvs[venomExecSemanticsTheory.step_inst_non_invoke] >>
  drule_all passSharedFrameTheory.step_inst_base_abort_input_equiv >> strip_tac >>
  qexists `s2'` >>
  conj_tac >- gvs[venomExecSemanticsTheory.step_inst_non_invoke] >>
  metis_tac[passSharedFrameTheory.step_inst_base_abort_returndata, revert_equiv_def]
QED

Theorem state_terminator_result:
  state_equiv excluded ((H n) with vs_inst_idx := pc) t /\
  (!v. MEM (Var v) i.inst_operands ==> v NOTIN excluded) /\
  is_terminator i.inst_opcode ==>
  lift_result
    (\u v. state_equiv excluded (u with vs_inst_idx := 0) (v with vs_inst_idx := 0))
    (execution_equiv excluded) revert_equiv
    (dft_exec_suffix fuel ctx [i] (H n)) (dft_exec_suffix fuel ctx [i] t)
Proof
  strip_tac >>
  `i.inst_opcode <> INVOKE` by
    (Cases_on `i.inst_opcode` >> gvs[venomInstTheory.is_terminator_def]) >>
  `result_equiv excluded
    (step_inst fuel ctx i ((H n) with vs_inst_idx := pc))
    (step_inst fuel ctx i t)` by
    (gvs[venomExecSemanticsTheory.step_inst_non_invoke] >>
     irule execEquivProofsTheory.step_inst_result_equiv >> simp[]) >>
  `instIdxIndep$exec_result_map (\u. u with vs_inst_idx := 0)
      (step_inst_base i ((H n) with vs_inst_idx := pc)) =
   instIdxIndep$exec_result_map (\u. u with vs_inst_idx := 0)
      (step_inst_base i (H n))` by
    simp[instIdxIndepTheory.terminator_step_inst_base_idx_norm0] >>
  gvs[venomExecSemanticsTheory.step_inst_non_invoke] >>
  Cases_on `step_inst_base i (H n)` >>
  Cases_on `step_inst_base i ((H n) with vs_inst_idx := pc)` >>
  gvs[instIdxIndepTheory.exec_result_map_def] >>
  Cases_on `step_inst_base i t` >>
  gvs[result_equiv_def, lift_result_def] >>
  gvs[instIdxIndepTheory.exec_result_map_def, result_equiv_def, lift_result_def,
    dft_exec_suffix_def, venomExecSemanticsTheory.step_inst_non_invoke,
    venomStateTheory.venom_state_component_equality, state_equiv_def,
    execution_equiv_def, revert_equiv_def, stateFrameTheory.execution_frame_def,
    venomStateTheory.lookup_var_def] >>
  IF_CASES_TAC >> gvs[lift_result_def, execution_equiv_def,
    stateFrameTheory.execution_frame_def, venomStateTheory.lookup_var_def]
QED

Theorem payload_history_fields:
  !n h H is fuel ctx.
  (!q. h <= q /\ q < h+n ==>
    ~is_terminator (EL q is).inst_opcode /\
    ?u. step_inst fuel ctx (EL q is) (H q) = OK u /\
      H (SUC q) = u with vs_inst_idx := SUC q) ==>
  (H (h+n)).vs_call_ctx = (H h).vs_call_ctx /\
  (H (h+n)).vs_data_section = (H h).vs_data_section
Proof
  Induct_on `n` >- simp[] >> rpt gen_tac >> strip_tac >>
  `(H (h+n)).vs_call_ctx = (H h).vs_call_ctx /\
   (H (h+n)).vs_data_section = (H h).vs_data_section` by
    (first_x_assum irule >> qexistsl [`ctx`,`fuel`,`is`] >>
     qx_gen_tac `q` >> strip_tac >>
     `q < h + SUC n` by decide_tac >> metis_tac[]) >>
  `~is_terminator (EL (h+n) is).inst_opcode /\
   ?u. step_inst fuel ctx (EL (h+n) is) (H (h+n)) = OK u /\
    H (SUC (h+n)) = u with vs_inst_idx := SUC (h+n)` by
    (first_x_assum irule >> simp[]) >>
  `u.vs_call_ctx = (H (h+n)).vs_call_ctx /\
   u.vs_data_section = (H (h+n)).vs_data_section` by
    metis_tac[venomInstProofsTheory.step_preserves_call_ctx,
      venomInstProofsTheory.step_preserves_data_section] >>
  simp[arithmeticTheory.ADD_CLAUSES]
QED

Theorem run_block_pair:
  ~(?err. run_block fuel ctx bb s = Error err) /\
  (!sp. eval_phis s bb.bb_instructions = OK sp ==>
    ?tp. eval_phis t bb'.bb_instructions = OK tp /\
      lift_result R Rt Ra
        (exec_block fuel ctx bb
          (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
        (exec_block fuel ctx bb'
          (tp with vs_inst_idx := phi_prefix_length bb'.bb_instructions)) /\
      EVERY P (trace_block [] d fuel ctx fn' bb'
        (tp with vs_inst_idx := phi_prefix_length bb'.bb_instructions))) ==>
  lift_result R Rt Ra (run_block fuel ctx bb s) (run_block fuel ctx bb' t) /\
  EVERY P (case eval_phis t bb'.bb_instructions of
    OK tp => trace_block [] d fuel ctx fn' bb'
      (tp with vs_inst_idx := phi_prefix_length bb'.bb_instructions)
  | _ => [])
Proof
  strip_tac >>
  qspecl_then [`s`,`bb.bb_instructions`] strip_assume_tac
    venomExecSemanticsTheory.eval_phis_ok_or_error_defs
  >- (qpat_x_assum `!sp. _` drule >> strip_tac >>
      simp[venomExecSemanticsTheory.run_block_def]) >>
  gvs[venomExecSemanticsTheory.run_block_def]
QED

Theorem trace_blocks_run_block:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
  trace_blocks [] d (SUC fuel) ctx fn s =
    (case eval_phis s bb.bb_instructions of
       OK sp => trace_block [] (SUC d) fuel ctx fn bb
         (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)
     | _ => []) ++
    (case run_block fuel ctx bb s of
       OK u => if u.vs_halted then []
               else trace_blocks [] (SUC d) fuel ctx fn u
     | _ => [])
Proof
  strip_tac >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    venomExecSemanticsTheory.eval_phis_ok_or_error_defs >>
  simp[Once trace_defs, venomExecSemanticsTheory.run_block_def]
QED

Theorem blocks_pair:
  (!s t. R s t ==> s.vs_halted = t.vs_halted /\ Rt s t) /\
  (!fuel d s t bb.
    R s t /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    EVERY Q (trace_blocks [] d (SUC fuel) ctx fn s) /\
    ~(?err. run_block fuel ctx bb s = Error err) ==>
    ?bb'. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
      lift_result R Rt Ra (run_block fuel ctx bb s) (run_block fuel ctx bb' t) /\
      EVERY P (case eval_phis t bb'.bb_instructions of
        OK tp => trace_block [] (SUC d) fuel ctx fn' bb'
          (tp with vs_inst_idx := phi_prefix_length bb'.bb_instructions)
      | _ => [])) ==>
  !fuel d s t.
    R s t /\ EVERY Q (trace_blocks [] d fuel ctx fn s) /\
    ~(?err. run_blocks fuel ctx fn s = Error err) ==>
    lift_result R Rt Ra (run_blocks fuel ctx fn s) (run_blocks fuel ctx fn' t) /\
    EVERY P (trace_blocks [] d fuel ctx fn' t)
Proof
  strip_tac >> Induct_on `fuel`
  >- simp[venomExecSemanticsTheory.run_blocks_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- gvs[venomExecSemanticsTheory.run_blocks_unfold] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  `~(?err. run_block fuel ctx bb s = Error err)` by
    (Cases_on `run_block fuel ctx bb s` >>
     gvs[venomExecSemanticsTheory.run_blocks_unfold]) >>
  qpat_x_assum `!fuel d s t bb. _`
    (qspecl_then [`fuel`,`d`,`s`,`t`,`bb`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  `trace_blocks [] d (SUC fuel) ctx fn s =
    (case eval_phis s bb.bb_instructions of
       OK sp => trace_block [] (SUC d) fuel ctx fn bb
         (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)
     | _ => []) ++
    (case run_block fuel ctx bb s of
       OK u => if u.vs_halted then []
               else trace_blocks [] (SUC d) fuel ctx fn u
     | _ => [])` by
    (irule trace_blocks_run_block >> simp[]) >>
  `trace_blocks [] d (SUC fuel) ctx fn' t =
    (case eval_phis t bb'.bb_instructions of
       OK tp => trace_block [] (SUC d) fuel ctx fn' bb'
         (tp with vs_inst_idx := phi_prefix_length bb'.bb_instructions)
     | _ => []) ++
    (case run_block fuel ctx bb' t of
       OK u => if u.vs_halted then []
               else trace_blocks [] (SUC d) fuel ctx fn' u
     | _ => [])` by
    (irule trace_blocks_run_block >> simp[]) >>
  Cases_on `run_block fuel ctx bb s` >>
  Cases_on `run_block fuel ctx bb' t` >>
  gvs[lift_result_def, EVERY_APPEND,
    venomExecSemanticsTheory.run_blocks_unfold] >>
  qpat_x_assum `!s t. R s t ==> _`
    (qspecl_then [`v`,`v'`] mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  Cases_on `v.vs_halted` >> gvs[lift_result_def] >>
  qpat_x_assum `!d s t. _` (qspecl_then [`SUC d`,`v`,`v'`] mp_tac) >>
  simp[]
QED

Theorem function_pair:
  fn_entry_label fn' = fn_entry_label fn /\
  (!fuel d s t. R s t /\
    EVERY Q (trace_blocks [] d fuel ctx fn s) /\
    ~(?err. run_blocks fuel ctx fn s = Error err) ==>
    lift_result R Rt Ra (run_blocks fuel ctx fn s) (run_blocks fuel ctx fn' t) /\
    EVERY P (trace_blocks [] d fuel ctx fn' t)) /\
  (!s t lbl. R s t ==> R
    (s with <|vs_current_bb := lbl; vs_inst_idx := 0|>)
    (t with <|vs_current_bb := lbl; vs_inst_idx := 0|>)) ==>
  !fuel s t. R s t /\ EVERY Q (trace_function fuel ctx fn s) /\
    ~(?err. run_function fuel ctx fn s = Error err) ==>
    lift_result R Rt Ra (run_function fuel ctx fn s) (run_function fuel ctx fn' t) /\
    EVERY P (trace_function fuel ctx fn' t)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `fn_entry_label fn` >>
  gvs[venomExecSemanticsTheory.run_function_def, trace_function_def] >>
  qpat_x_assum `!fuel d s t. _`
    (qspecl_then [`fuel`,`0`,
      `s with <|vs_current_bb := x; vs_inst_idx := 0|>`,
      `t with <|vs_current_bb := x; vs_inst_idx := 0|>`] mp_tac) >>
  impl_tac >- metis_tac[] >> simp[]
QED

Theorem cds_step_value:
  fn_inst_wf fn /\ ssa_form fn /\ MEM inst (fn_insts fn) /\
  dfg_get_def (dfg_build_function fn) v = SOME producer /\
  producer.inst_opcode = CALLDATASIZE /\
  (!w. lookup_var v s = SOME w ==>
       w = n2w (LENGTH s.vs_call_ctx.cc_calldata)) /\
  step_inst fuel ctx inst s = OK t ==>
  !w. lookup_var v t = SOME w ==>
      w = n2w (LENGTH t.vs_call_ctx.cc_calldata)
Proof
  strip_tac >>
  `t.vs_call_ctx = s.vs_call_ctx` by
    (reverse (Cases_on `is_terminator inst.inst_opcode`)
     >- metis_tac[venomInstPropsTheory.step_preserves_call_ctx] >>
     qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     simp[Once venomExecSemanticsTheory.step_inst_def] >>
     Cases_on `inst.inst_opcode` >> fs[venomInstTheory.is_terminator_def] >>
     asm_simp_tac (srw_ss()) [venomExecSemanticsTheory.step_inst_base_opcode_eqs] >>
     simp[AllCaseEqs(), venomStateTheory.jump_to_def] >>
     rpt strip_tac >> gvs[] >> pairarg_tac >> gvs[]) >>
  `MEM producer (fn_insts fn) /\ MEM v producer.inst_outputs` by
    metis_tac[dfgCorrectnessProofTheory.dfg_build_function_correct_proof] >>
  Cases_on `MEM v inst.inst_outputs`
  >- (`inst = producer` by
        metis_tac[allocaRemapSSATheory.ssa_unique_output] >>
      `inst_wf producer` by
        (gvs[fn_inst_wf_def, venomInstTheory.fn_insts_def,
             venomWfPropsTheory.fn_insts_blocks_flat,
             MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
      gvs[inst_wf_def] >>
      qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
      simp[venomExecSemanticsTheory.step_inst_def, venomExecSemanticsTheory.step_inst_base_opcode_eqs, venomExecSemanticsTheory.exec_read0_def,
           AllCaseEqs()] >>
      rpt strip_tac >> gvs[venomStateTheory.lookup_var_def, venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  `lookup_var v t = lookup_var v s` by
    (Cases_on `is_terminator inst.inst_opcode`
     >- metis_tac[venomExecProofsTheory.step_terminator_preserves_vars] >>
     metis_tac[venomInstPropsTheory.step_preserves_non_output_vars]) >>
  metis_tac[]
QED

Theorem cds_enter_lookup:
  ssa_form fn /\
  dfg_get_def (dfg_build_function fn) v = SOME producer /\
  producer.inst_opcode = CALLDATASIZE /\ enters_block fn s t ==>
  lookup_var v t = lookup_var v s
Proof
  strip_tac >>
  `MEM producer (fn_insts fn) /\ MEM v producer.inst_outputs` by
    metis_tac[dfgCorrectnessProofTheory.dfg_build_function_correct_proof] >>
  fs[contextCodegenRelTheory.enters_block_def] >>
  `MEM bb fn.fn_blocks` by
    metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
  `!inst. MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI ==>
          ~MEM v inst.inst_outputs` by
    (rpt strip_tac >>
     `MEM inst (fn_insts fn)` by
       (irule venomFnInstsProofsTheory.MEM_fn_insts >> metis_tac[]) >>
     `inst = producer` by
       metis_tac[allocaRemapSSATheory.ssa_unique_output] >> gvs[]) >>
  `FLOOKUP s_phi.vs_vars v = FLOOKUP s.vs_vars v` by
    metis_tac[venomExecProofsTheory.eval_phis_flookup_not_phi_output] >>
  gvs[venomStateTheory.lookup_var_def]
QED

Theorem cds_entry:
  s.vs_vars = FEMPTY /\ s.vs_call_ctx.cc_calldata = cd ==>
  fn_entry_inv
    (\ctx f i t. t.vs_call_ctx.cc_calldata = cd /\
      (fn_inst_wf f /\ ssa_form f ==>
       !v producer w.
         dfg_get_def (dfg_build_function f) v = SOME producer /\
         producer.inst_opcode = CALLDATASIZE /\
         lookup_var v t = SOME w ==> w = n2w (LENGTH cd))) ctx fn s
Proof
  rewrite_tac[contextCodegenRelTheory.fn_entry_inv_def] >> BETA_TAC >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  `s1.vs_call_ctx = s.vs_call_ctx` by
    (fs[contextCodegenRelTheory.enters_block_def] >>
     drule venomExecProofsTheory.eval_phis_only_updates_vs_vars >>
     disch_then (fn th => once_rewrite_tac[th]) >> simp[]) >>
  simp[] >> rpt strip_tac >>
  `lookup_var v s1 = lookup_var v s` by
    metis_tac[cds_enter_lookup] >>
  gvs[venomStateTheory.lookup_var_def]
QED

Theorem cds_closed:
  reachability_closed
    (\ctx f i t. t.vs_call_ctx.cc_calldata = cd /\
      (fn_inst_wf f /\ ssa_form f ==>
       !v producer w.
         dfg_get_def (dfg_build_function f) v = SOME producer /\
         producer.inst_opcode = CALLDATASIZE /\
         lookup_var v t = SOME w ==> w = n2w (LENGTH cd))) ctx
Proof
  rewrite_tac[contextCodegenRelTheory.reachability_closed_def] >> BETA_TAC >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `s'.vs_call_ctx = s.vs_call_ctx` by
        metis_tac[venomInstPropsTheory.step_preserves_call_ctx] >>
      simp[] >> rpt strip_tac >>
      `MEM inst (fn_insts fn)` by
        (gvs[contextCodegenRelTheory.active_inst_def] >>
         irule venomFnInstsProofsTheory.MEM_fn_insts >> metis_tac[EL_MEM]) >>
      `!w. lookup_var v s = SOME w ==>
           w = n2w (LENGTH s.vs_call_ctx.cc_calldata)` by metis_tac[] >>
      `lookup_var v s' = SOME w` by
        fs[venomStateTheory.lookup_var_def] >>
      `w = n2w (LENGTH s'.vs_call_ctx.cc_calldata)` by
        metis_tac[cds_step_value] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
      `s'.vs_call_ctx = s.vs_call_ctx` by
        (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
         simp[Once venomExecSemanticsTheory.step_inst_def] >>
         Cases_on `inst.inst_opcode` >> fs[venomInstTheory.is_terminator_def] >>
         asm_simp_tac (srw_ss()) [venomExecSemanticsTheory.step_inst_base_opcode_eqs] >>
         simp[AllCaseEqs(), venomStateTheory.jump_to_def] >>
         rpt strip_tac >> gvs[] >> pairarg_tac >> gvs[]) >>
      `s1.vs_call_ctx = s'.vs_call_ctx` by
        (fs[contextCodegenRelTheory.enters_block_def] >>
         drule venomExecProofsTheory.eval_phis_only_updates_vs_vars >>
         disch_then (fn th => once_rewrite_tac[th]) >> simp[]) >>
      simp[] >> rpt strip_tac >>
      `lookup_var v s1 = lookup_var v s'` by
        metis_tac[cds_enter_lookup] >>
      `lookup_var v s' = lookup_var v s` by
        metis_tac[venomExecProofsTheory.step_terminator_preserves_vars] >>
      metis_tac[]) >>
  rpt gen_tac >> strip_tac >> irule cds_entry >>
  gvs[venomExecSemanticsTheory.setup_callee_def, AllCaseEqs()]
QED

Theorem cds_trace:
  fn_entry_state fn s /\
  MEM (([],d,id),f,i,t) (trace_function fuel ctx fn s) ==>
  f = fn /\
  t.vs_call_ctx.cc_calldata = s.vs_call_ctx.cc_calldata /\
  (fn_inst_wf f /\ ssa_form f ==>
   !v producer w.
     dfg_get_def (dfg_build_function f) v = SOME producer /\
     producer.inst_opcode = CALLDATASIZE /\ lookup_var v t = SOME w ==>
     w = n2w (LENGTH t.vs_call_ctx.cc_calldata))
Proof
  strip_tac >>
  qabbrev_tac `Inv = \(ctx:venom_context) f (i:instruction) t.
    t.vs_call_ctx.cc_calldata = s.vs_call_ctx.cc_calldata /\
    (fn_inst_wf f /\ ssa_form f ==>
     !v producer w.
       dfg_get_def (dfg_build_function f) v = SOME producer /\
       producer.inst_opcode = CALLDATASIZE /\
       lookup_var v t = SOME w ==>
       w = n2w (LENGTH s.vs_call_ctx.cc_calldata))` >>
  `reachability_closed Inv ctx` by
    simp[Abbr `Inv`, cds_closed] >>
  `fn_entry_inv Inv ctx fn s` by
    (simp[Abbr `Inv`] >> irule cds_entry >>
     fs[fn_entry_state_def]) >>
  `trace_function fuel ctx fn s = trace_blocks [] 0 fuel ctx fn s` by
    (gvs[fn_entry_state_def, trace_function_def] >>
     AP_TERM_TAC >> simp[venomStateTheory.venom_state_component_equality]) >>
  qspecl_then [`[]`,`0`,`fuel`,`ctx`,`fn`,`s`] mp_tac
    (cj 3 mmTraceProofsTheory.mm_trace_root_inv) >>
  simp[] >> simp[EVERY_MEM, pairTheory.FORALL_PROD] >>
  strip_tac >> `f = fn /\ Inv ctx fn i t` by metis_tac[] >>
  gvs[Abbr `Inv`] >> metis_tac[]
QED

Theorem cds_history_value:
  fn_inst_wf fn /\ ssa_form fn /\ MEM bb fn.fn_blocks /\
  is = bb.bb_instructions /\ h <= n /\ n < LENGTH is /\
  (!q. h <= q /\ q < n ==>
    ?u. step_inst fuel ctx (EL q is) (H q) = OK u /\
        H (SUC q) = u with vs_inst_idx := SUC q) /\
  (!v producer w.
    dfg_get_def (dfg_build_function fn) v = SOME producer /\
    producer.inst_opcode = CALLDATASIZE /\ lookup_var v (H h) = SOME w ==>
    w = n2w (LENGTH (H h).vs_call_ctx.cc_calldata)) ==>
  !j. h <= j /\ j <= n ==>
    (H j).vs_call_ctx.cc_calldata = (H h).vs_call_ctx.cc_calldata /\
    (!v producer w.
      dfg_get_def (dfg_build_function fn) v = SOME producer /\
      producer.inst_opcode = CALLDATASIZE /\ lookup_var v (H j) = SOME w ==>
      w = n2w (LENGTH (H j).vs_call_ctx.cc_calldata))
Proof
  strip_tac >> Induct_on `j`
  >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  strip_tac >> Cases_on `SUC j = h` >- (gvs[] >> metis_tac[]) >>
  `h <= j /\ j < n /\ j <= n` by decide_tac >>
  `(H j).vs_call_ctx.cc_calldata = (H h).vs_call_ctx.cc_calldata /\
   (!v producer w.
     dfg_get_def (dfg_build_function fn) v = SOME producer /\
     producer.inst_opcode = CALLDATASIZE /\ lookup_var v (H j) = SOME w ==>
     w = n2w (LENGTH (H j).vs_call_ctx.cc_calldata))` by metis_tac[] >>
  `?u. step_inst fuel ctx (EL j is) (H j) = OK u /\
       H (SUC j) = u with vs_inst_idx := SUC j` by metis_tac[] >>
  `u.vs_call_ctx = (H j).vs_call_ctx` by
    (reverse (Cases_on `is_terminator (EL j is).inst_opcode`)
     >- metis_tac[venomInstPropsTheory.step_preserves_call_ctx] >>
     qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     qpat_x_assum `is_terminator _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `(EL j is).inst_opcode` >>
     simp[venomInstTheory.is_terminator_def,
          Once venomExecSemanticsTheory.step_inst_def] >>
     asm_simp_tac (srw_ss()) [venomExecSemanticsTheory.step_inst_base_opcode_eqs] >>
     simp[AllCaseEqs(), venomStateTheory.jump_to_def] >>
     rpt strip_tac >> gvs[] >> pairarg_tac >> gvs[]) >>
  `j < LENGTH is` by decide_tac >>
  `MEM (EL j is) (fn_insts fn)` by
    (irule venomFnInstsProofsTheory.MEM_fn_insts >>
     qexists_tac `bb` >> metis_tac[EL_MEM]) >>
  simp[] >> rpt strip_tac >>
  `!w. lookup_var v (H j) = SOME w ==>
       w = n2w (LENGTH (H j).vs_call_ctx.cc_calldata)` by metis_tac[] >>
  `lookup_var v u = SOME w` by
    fs[venomStateTheory.lookup_var_def] >>
  `w = n2w (LENGTH u.vs_call_ctx.cc_calldata)` by
    metis_tac[cds_step_value] >> metis_tac[]
QED

Theorem function_forget_vars:
  lift_result R (execution_equiv excluded) revert_equiv
    (run_function fuel ctx fn s) (run_function fuel ctx fn' t) ==>
  lift_result (state_equiv UNIV) (execution_equiv UNIV) revert_equiv
    (run_function fuel ctx fn s) (run_function fuel ctx fn' t)
Proof
  `!u. run_function fuel ctx fn s <> OK u` by
    (Cases_on `fn_entry_label fn` >>
     simp[venomExecSemanticsTheory.run_function_def,
       o1PassLiftTheory.run_blocks_not_OK]) >>
  Cases_on `run_function fuel ctx fn s` >>
  Cases_on `run_function fuel ctx fn' t` >>
  gvs[lift_result_def] >>
  metis_tac[stateEquivProofsTheory.execution_equiv_subset, pred_setTheory.SUBSET_UNIV]
QED

Theorem eval_phis_idx:
  !insts s n.
    eval_phis (s with vs_inst_idx := n) insts =
    instIdxIndep$exec_result_map (\u. u with vs_inst_idx := n)
      (eval_phis s insts)
Proof
  Induct >> rpt gen_tac >>
  simp[venomExecSemanticsTheory.eval_phis_def,
       instIdxIndepTheory.exec_result_map_def] >>
  `eval_one_phi (s with vs_inst_idx := n) h = eval_one_phi s h` by
    simp[venomExecSemanticsTheory.eval_one_phi_def,
         instIdxIndepTheory.eval_op_inst_idx] >>
  simp[] >> Cases_on `h.inst_opcode = PHI` >> simp[] >>
  Cases_on `eval_one_phi s h` >> simp[instIdxIndepTheory.exec_result_map_def] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `eval_phis s insts` >>
  simp[instIdxIndepTheory.exec_result_map_def, venomStateTheory.update_var_def]
QED

Theorem phi_entry_pair:
  state_equiv excluded (s with vs_inst_idx := 0) (t with vs_inst_idx := 0) /\
  EVERY (\inst. inst.inst_opcode = PHI ==>
    !v. MEM (Var v) inst.inst_operands ==> v NOTIN excluded) insts /\
  eval_phis s insts = OK sp ==>
  ?tp. eval_phis t insts = OK tp /\
    state_equiv excluded (sp with vs_inst_idx := h) (tp with vs_inst_idx := h)
Proof
  strip_tac >>
  `eval_phis (s with vs_inst_idx := 0) insts = OK (sp with vs_inst_idx := 0)` by
    simp[eval_phis_idx, instIdxIndepTheory.exec_result_map_def] >>
  `?u. eval_phis (t with vs_inst_idx := 0) insts = OK u /\
       state_equiv excluded (sp with vs_inst_idx := 0) u` by
    metis_tac[venomExecProofsTheory.eval_phis_state_equiv] >>
  qspecl_then [`t`,`insts`] strip_assume_tac
    venomExecSemanticsTheory.eval_phis_ok_or_error_defs
  >- (rename1 `eval_phis t insts = OK tp` >>
      qexists_tac `tp` >> simp[] >>
      `u = tp with vs_inst_idx := 0` by
        fs[eval_phis_idx, instIdxIndepTheory.exec_result_map_def] >>
      gvs[state_equiv_def, execution_equiv_def,
          stateFrameTheory.execution_frame_def, venomStateTheory.lookup_var_def]) >>
  gvs[eval_phis_idx, instIdxIndepTheory.exec_result_map_def]
QED

Theorem same_block_static:
  state_equiv excluded s t /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb /\
  (!v. MEM (Var v) inst.inst_operands ==> v NOTIN excluded) /\
  static_mem_ok eom ctx fn inst s ==>
  static_mem_ok eom ctx fn' inst t
Proof
  strip_tac >>
  `s.vs_inst_idx = t.vs_inst_idx /\
   s.vs_call_entry_fmp = t.vs_call_entry_fmp` by
    fs[state_equiv_def, execution_equiv_def,
       stateFrameTheory.execution_frame_def] >>
  `inst_mem_ranges inst s = inst_mem_ranges inst t` by
    (irule o1ContractCfgNormTheory.supply_inst_mem_ranges_cong >> simp[] >>
     rpt strip_tac >> Cases_on `op` >>
     gvs[venomStateTheory.eval_operand_def, state_equiv_def,
         execution_equiv_def] >> metis_tac[]) >>
  `in_revert_forward fn s <=> in_revert_forward fn' t` by
    (gvs[contextCodegenRelTheory.in_revert_forward_def] >> metis_tac[]) >>
  gvs[unitMemInvTheory.static_mem_ok_def]
QED

Theorem same_block_exec_result:
  !fuel ctx excluded bb s t.
    state_equiv excluded s t /\
    (!inst. MEM inst bb.bb_instructions ==>
      !v. MEM (Var v) inst.inst_operands ==> v NOTIN excluded) ==>
    result_equiv excluded (exec_block fuel ctx bb s) (exec_block fuel ctx bb t)
Proof
  rpt gen_tac >> strip_tac >>
  pop_assum mp_tac >> pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [`t`,`s`,`bb`,`ctx`,`fuel`] >>
  ho_match_mp_tac (cj 2 venomExecSemanticsTheory.run_defs_ind) >>
  qexists_tac `\fuel ctx inst s. T` >>
  qexists_tac `\fuel ctx fn s. T` >> rw[] >>
  simp[Once venomExecSemanticsTheory.exec_block_def] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [venomExecSemanticsTheory.exec_block_def])) >>
  `s.vs_inst_idx = t.vs_inst_idx` by
    fs[state_equiv_def, execution_equiv_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >>
  gvs[result_equiv_def, revert_equiv_def] >>
  rename1 `get_instruction bb _ = SOME inst` >>
  `!v. MEM (Var v) inst.inst_operands ==> v NOTIN excluded` by
    (gvs[venomInstTheory.get_instruction_def] >> metis_tac[EL_MEM]) >>
  `result_equiv excluded (step_inst fuel ctx inst s) (step_inst fuel ctx inst t)` by
    (Cases_on `is_terminator inst.inst_opcode`
     >- (`inst.inst_opcode <> INVOKE` by
           (Cases_on `inst.inst_opcode` >> gvs[venomInstTheory.is_terminator_def]) >>
         simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
         irule execEquivProofsTheory.step_inst_result_equiv >> metis_tac[]) >>
     irule removeUnusedProofsTheory.step_inst_result_equiv_full >> metis_tac[]) >>
  Cases_on `step_inst fuel ctx inst s` >> Cases_on `step_inst fuel ctx inst t` >>
  gvs[result_equiv_def, revert_equiv_def] >>
  rename1 `step_inst fuel ctx inst s = OK u` >>
  rename1 `step_inst fuel ctx inst t = OK v` >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[]
  >- (`u.vs_halted = v.vs_halted` by fs[state_equiv_def, execution_equiv_def] >>
      Cases_on `u.vs_halted` >> gvs[result_equiv_def, revert_equiv_def] >>
      fs[state_equiv_def]) >>
  first_x_assum irule >> simp[] >>
  fs[state_equiv_def, execution_equiv_def] >>
  simp[venomStateTheory.lookup_var_def] >> metis_tac[venomStateTheory.lookup_var_def]
QED

Theorem same_block_trace:
  !s t.
    state_equiv excluded s t /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb /\
    (!inst v. MEM inst bb.bb_instructions /\
       MEM (Var v) inst.inst_operands ==> v NOTIN excluded) /\
    EVERY (\((p,d',id),f,i,u). p = [] ==> static_mem_ok eom ctx f i u)
      (trace_block [] d fuel ctx fn bb s) ==>
    EVERY (\((p,d',id),f,i,u). p = [] ==> static_mem_ok eom ctx f i u)
      (trace_block [] d fuel ctx fn' bb t)
Proof
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  `s.vs_inst_idx = t.vs_inst_idx` by fs[state_equiv_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (`get_instruction bb t.vs_inst_idx = NONE` by metis_tac[] >>
      PURE_ONCE_REWRITE_TAC [cj 2 dftGasFromListTraceDefsTheory.trace_defs] >>
      asm_rewrite_tac[] >>
      simp[optionTheory.option_case_def, listTheory.EVERY_DEF]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `!v. MEM (Var v) inst.inst_operands ==> v NOTIN excluded` by
    (gvs[venomInstTheory.get_instruction_def] >> metis_tac[EL_MEM]) >>
  `reachability_closed (\ctx fn inst s. T) ctx` by
    simp[contextCodegenRelTheory.reachability_closed_def,
         contextCodegenRelTheory.fn_entry_inv_def] >>
  drule_all trace_visit_root_every >>
  disch_then (fn th => qpat_x_assum `EVERY _ _` (mp_tac o REWRITE_RULE [th])) >>
  strip_tac >>
  `get_instruction bb t.vs_inst_idx = SOME inst` by metis_tac[] >>
  drule_all (Q.INST [`s` |-> `t`, `fn` |-> `fn'`] trace_visit_root_every) >>
  disch_then (fn th => rewrite_tac[th]) >> conj_tac
  >- (irule same_block_static >> metis_tac[]) >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (Cases_on `step_inst fuel ctx inst t` >> simp[]) >>
  `result_equiv excluded (step_inst fuel ctx inst s) (step_inst fuel ctx inst t)` by
    (irule removeUnusedProofsTheory.step_inst_result_equiv_full >> metis_tac[]) >>
  Cases_on `step_inst fuel ctx inst s` >> Cases_on `step_inst fuel ctx inst t` >>
  gvs[result_equiv_def] >>
  rename1 `step_inst fuel ctx inst s = OK u` >>
  rename1 `step_inst fuel ctx inst t = OK v` >>
  `u.vs_current_bb = s.vs_current_bb /\ v.vs_current_bb = t.vs_current_bb` by
    metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
  first_x_assum (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
  (impl_tac >- (gvs[venomInstTheory.get_instruction_def] >> decide_tac)) >>
  disch_then (qspec_then `u with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >>
  disch_then (qspec_then `v with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> disch_then irule >> simp[] >>
  fs[state_equiv_def, execution_equiv_def] >>
  simp[venomStateTheory.lookup_var_def] >> metis_tac[venomStateTheory.lookup_var_def]
QED

Theorem same_run_block_correct:
  state_equiv excluded (s with vs_inst_idx := 0) (t with vs_inst_idx := 0) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb /\
  (!inst v. MEM inst bb.bb_instructions /\
    MEM (Var v) inst.inst_operands ==> v NOTIN excluded) /\
  EVERY (\((p,d',id),f,i,u). p = [] ==> static_mem_ok eom ctx f i u)
    (trace_blocks [] d (SUC fuel) ctx fn s) ==>
  lift_result
    (\u v. state_equiv excluded (u with vs_inst_idx := 0) (v with vs_inst_idx := 0))
    (execution_equiv excluded) revert_equiv
    (run_block fuel ctx bb s) (run_block fuel ctx bb t) /\
  EVERY (\((p,d',id),f,i,u). p = [] ==> static_mem_ok eom ctx f i u)
    (case eval_phis t bb.bb_instructions of
      OK tp => trace_block [] (SUC d) fuel ctx fn' bb
        (tp with vs_inst_idx := phi_prefix_length bb.bb_instructions)
    | _ => [])
Proof
  strip_tac >>
  `EVERY (\inst. inst.inst_opcode = PHI ==>
    !v. MEM (Var v) inst.inst_operands ==> v NOTIN excluded) bb.bb_instructions` by
    (simp[EVERY_MEM] >> metis_tac[]) >>
  qspecl_then [`s`,`bb.bb_instructions`] strip_assume_tac
    venomExecSemanticsTheory.eval_phis_ok_or_error_defs
  >- (rename1 `eval_phis s bb.bb_instructions = OK sp` >>
      `?tp. eval_phis t bb.bb_instructions = OK tp /\
        state_equiv excluded
          (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)
          (tp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
        (irule phi_entry_pair >> metis_tac[]) >>
      `result_equiv excluded (run_block fuel ctx bb s) (run_block fuel ctx bb t)` by
        (simp[venomExecSemanticsTheory.run_block_def] >>
         irule same_block_exec_result >> metis_tac[]) >>
      conj_tac
      >- (Cases_on `run_block fuel ctx bb s` >> Cases_on `run_block fuel ctx bb t` >>
          gvs[result_equiv_def, lift_result_def, state_equiv_def,
              execution_equiv_def, revert_equiv_def,
              stateFrameTheory.execution_frame_def, venomStateTheory.lookup_var_def]) >>
      simp[] >>
      mp_tac (Q.INST [`p` |-> `[]`]
        dftGasFromListTraceDefsTheory.trace_blocks_enter) >>
      (impl_tac >- asm_rewrite_tac[]) >>
      disch_then (fn th =>
        qpat_x_assum `EVERY _ (trace_blocks _ _ _ _ _ _)`
          (mp_tac o REWRITE_RULE [th])) >>
      simp[EVERY_APPEND] >> strip_tac >>
      `sp.vs_current_bb = s.vs_current_bb /\ tp.vs_current_bb = t.vs_current_bb` by
        metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
      mp_tac (Q.SPECL
        [`sp with vs_inst_idx := phi_prefix_length bb.bb_instructions`,
         `tp with vs_inst_idx := phi_prefix_length bb.bb_instructions`]
        (Q.INST [`d` |-> `SUC d`] same_block_trace)) >>
      (impl_tac >- (asm_rewrite_tac[] >> simp[])) >> simp[]) >>
  qspecl_then [`t`,`bb.bb_instructions`] strip_assume_tac
    venomExecSemanticsTheory.eval_phis_ok_or_error_defs
  >- (`state_equiv excluded (t with vs_inst_idx := 0) (s with vs_inst_idx := 0)` by
        metis_tac[stateEquivProofsTheory.state_equiv_sym] >>
      `?sp. eval_phis s bb.bb_instructions = OK sp` by
        metis_tac[phi_entry_pair] >> gvs[]) >>
  simp[venomExecSemanticsTheory.run_block_def, lift_result_def]
QED


