(* Continuation-style transport in the actual execution semantics. *)
Theory functionInlinerSimulation
Ancestors
  functionInlinerOperational functionInlinerCallBoundary
  functionInlinerReturnTransport functionInlinerFuel functionInlinerSiteLayout
  functionInlinerPhiTransport functionInlinerFmp functionInlinerOpacity
  venomExecSemantics venomInstProofs venomExecProofs
  functionInlinerFrame functionInlinerDefs venomState venomInst venomWf list pred_set

(* Bookkeeping belongs to the saved caller, independently of clone frames. *)
Definition inline_caller_bookkeeping_def:
  inline_caller_bookkeeping d t <=>
    t.vs_params = d.vs_params /\
    t.vs_call_entry_fmp = d.vs_call_entry_fmp /\
    t.vs_return_pc_token = d.vs_return_pc_token /\
    t.vs_labels = d.vs_labels
End

Theorem inline_caller_bookkeeping_refl[simp]:
  inline_caller_bookkeeping s s
Proof
  simp[inline_caller_bookkeeping_def]
QED

Theorem inline_caller_bookkeeping_updates[simp]:
  inline_caller_bookkeeping d (s with vs_vars := vars) = inline_caller_bookkeeping d s /\
  inline_caller_bookkeeping d (s with vs_inst_idx := i) = inline_caller_bookkeeping d s /\
  inline_caller_bookkeeping d (jump_to l s) = inline_caller_bookkeeping d s /\
  inline_caller_bookkeeping d (adopt_return_fmp ir s) = inline_caller_bookkeeping d s /\
  inline_caller_bookkeeping d (merge_callee_state s u) = inline_caller_bookkeeping d s
Proof
  Cases_on `ir.iret_adopt_fmp` >>
  simp[inline_caller_bookkeeping_def, jump_to_def, adopt_return_fmp_def,
       merge_callee_state_def]
QED

Theorem inline_caller_bookkeeping_bind:
  bind_outputs outs vals s = SOME t ==>
  inline_caller_bookkeeping d t = inline_caller_bookkeeping d s
Proof
  simp[bind_outputs_def] >> strip_tac >> gvs[] >>
  qspec_then `\s. inline_caller_bookkeeping d s` mp_tac
    venomInstProofs1Theory.foldl_update_var_preserves >>
  simp[update_var_def]
QED

Theorem inline_caller_bookkeeping_phis:
  eval_phis s insts = OK t ==>
  inline_caller_bookkeeping d t = inline_caller_bookkeeping d s
Proof
  strip_tac >> drule eval_phis_only_updates_vs_vars >>
  disch_then SUBST1_TAC >> simp[]
QED

Theorem inline_caller_bookkeeping_step_nonterminator:
  step_inst fuel ctx inst s = OK t /\ ~is_terminator inst.inst_opcode ==>
  inline_caller_bookkeeping d t = inline_caller_bookkeeping d s
Proof
  rw[Once step_inst_def] >> gvs[AllCaseEqs()]
  >- (drule inline_caller_bookkeeping_bind >> simp[]) >>
  drule_all venomInstProofs1Theory.step_inst_base_preserves_all >>
  simp[inline_caller_bookkeeping_def]
QED

Theorem inline_caller_bookkeeping_terminator[local]:
  is_terminator inst.inst_opcode /\ step_inst_base inst s = OK t ==>
  inline_caller_bookkeeping d t = inline_caller_bookkeeping d s
Proof
  Cases_on `inst.inst_opcode` >> simp[is_terminator_def] >>
  strip_tac >> gvs[step_inst_base_opcode_eqs] >>
  gvs[AllCaseEqs(), jump_to_def, inline_caller_bookkeeping_def] >>
  pairarg_tac >> gvs[]
QED

Theorem inline_caller_bookkeeping_step:
  step_inst fuel ctx inst s = OK t ==>
  inline_caller_bookkeeping d t = inline_caller_bookkeeping d s
Proof
  strip_tac >> Cases_on `is_terminator inst.inst_opcode`
  >- (Cases_on `inst.inst_opcode = INVOKE` >- gvs[is_terminator_def] >>
      fs[Once step_inst_def] >>
      metis_tac[inline_caller_bookkeeping_terminator]) >>
  metis_tac[inline_caller_bookkeeping_step_nonterminator]
QED

Theorem inline_caller_bookkeeping_exec_block:
  !fuel ctx bb s t. exec_block fuel ctx bb s = OK t ==>
  inline_caller_bookkeeping d t = inline_caller_bookkeeping d s
Proof
  rpt gen_tac >>
  completeInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `exec_block fuel ctx bb s = OK t` mp_tac >>
  once_rewrite_tac[exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  rename1 `step_inst fuel ctx inst s = OK u` >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[]
  >- (Cases_on `u.vs_halted` >> simp[] >> strip_tac >> gvs[] >>
      metis_tac[inline_caller_bookkeeping_step]) >>
  strip_tac >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  `inline_caller_bookkeeping d t =
    inline_caller_bookkeeping d (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (first_x_assum irule >> qexists `bb` >> simp[]) >>
  metis_tac[inline_caller_bookkeeping_step, inline_caller_bookkeeping_updates]
QED

Theorem inline_caller_bookkeeping_run_block:
  run_block fuel ctx bb s = OK t ==>
  inline_caller_bookkeeping d t = inline_caller_bookkeeping d s
Proof
  strip_tac >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs >>
  gvs[run_block_def] >>
  imp_res_tac inline_caller_bookkeeping_exec_block >>
  imp_res_tac inline_caller_bookkeeping_phis >> gvs[]
QED

(* Erase the callee effects and FMP, retaining the complete caller residual. *)
Definition inline_caller_residual_def:
  inline_caller_residual s =
    inline_shared_frame
      ((merge_callee_state s (init_venom_state "")) with vs_fmp := 0w)
End

Theorem inline_caller_residual_normalize[simp]:
  inline_caller_residual (inline_shared_frame s) = inline_caller_residual s /\
  inline_caller_residual (inline_caller_residual s) = inline_caller_residual s
Proof
  simp[inline_caller_residual_def, inline_shared_frame_def,
       stateFrameTheory.execution_frame_def, merge_callee_state_def]
QED

Theorem inline_caller_residual_shared:
  inline_shared_frame s = inline_shared_frame t ==>
  inline_caller_residual s = inline_caller_residual t
Proof
  metis_tac[inline_caller_residual_normalize]
QED

Theorem inline_caller_residual_reconstruct:
  inline_caller_residual t = inline_caller_residual c /\ t.vs_fmp = f ==>
  inline_shared_frame t =
    inline_shared_frame ((merge_callee_state c t) with vs_fmp := f)
Proof
  simp[inline_caller_residual_def, inline_shared_frame_def,
       stateFrameTheory.execution_frame_def, merge_callee_state_def,
       venom_state_component_equality]
QED

Theorem inline_caller_residual_updates[simp]:
  inline_caller_residual (s with vs_vars := vars) = inline_caller_residual s /\
  inline_caller_residual (s with vs_current_bb := bb) = inline_caller_residual s /\
  inline_caller_residual (s with vs_inst_idx := i) = inline_caller_residual s /\
  inline_caller_residual (s with vs_prev_bb := prev) = inline_caller_residual s /\
  inline_caller_residual (s with vs_fmp := f) = inline_caller_residual s /\
  inline_caller_residual (jump_to l s) = inline_caller_residual s /\
  inline_caller_residual (adopt_return_fmp ir s) = inline_caller_residual s /\
  inline_caller_residual (merge_callee_state s u) = inline_caller_residual s
Proof
  Cases_on `ir.iret_adopt_fmp` >>
  simp[inline_caller_residual_def, inline_shared_frame_def,
       stateFrameTheory.execution_frame_def, merge_callee_state_def,
       jump_to_def, adopt_return_fmp_def]
QED

Theorem inline_caller_residual_bind:
  bind_outputs outs vals s = SOME t ==>
  inline_caller_residual t = inline_caller_residual s
Proof
  simp[bind_outputs_def] >> strip_tac >> gvs[] >>
  qspec_then `\u. inline_caller_residual u = inline_caller_residual s` mp_tac
    venomInstProofs1Theory.foldl_update_var_preserves >>
  simp[update_var_def]
QED

Theorem inline_caller_residual_phis:
  eval_phis s insts = OK t ==>
  inline_caller_residual t = inline_caller_residual s
Proof
  strip_tac >> drule eval_phis_only_updates_vs_vars >>
  disch_then SUBST1_TAC >> simp[]
QED

Theorem inline_caller_residual_step_nonterminator:
  step_inst fuel ctx inst s = OK t /\ ~is_terminator inst.inst_opcode ==>
  inline_caller_residual t = inline_caller_residual s
Proof
  rw[Once step_inst_def] >> gvs[AllCaseEqs()]
  >- (drule inline_caller_residual_bind >> simp[]) >>
  drule_all venomInstProofs1Theory.step_inst_base_preserves_all >>
  simp[inline_caller_residual_def, inline_shared_frame_def,
       stateFrameTheory.execution_frame_def, merge_callee_state_def,
       venom_state_component_equality]
QED

Theorem inline_caller_residual_terminator[local]:
  is_terminator inst.inst_opcode /\ step_inst_base inst s = OK t /\
  ~s.vs_halted /\ ~t.vs_halted ==>
  inline_caller_residual t = inline_caller_residual s
Proof
  Cases_on `inst.inst_opcode` >> simp[is_terminator_def] >>
  strip_tac >> gvs[step_inst_base_opcode_eqs] >>
  gvs[AllCaseEqs(), jump_to_def, inline_caller_residual_def,
      inline_shared_frame_def, stateFrameTheory.execution_frame_def,
      merge_callee_state_def] >>
  pairarg_tac >> gvs[]
QED

Theorem inline_caller_residual_step:
  step_inst fuel ctx inst s = OK t /\ ~s.vs_halted /\ ~t.vs_halted ==>
  inline_caller_residual t = inline_caller_residual s
Proof
  strip_tac >> Cases_on `is_terminator inst.inst_opcode`
  >- (Cases_on `inst.inst_opcode = INVOKE` >- gvs[is_terminator_def] >>
      fs[Once step_inst_def] >>
      metis_tac[inline_caller_residual_terminator]) >>
  metis_tac[inline_caller_residual_step_nonterminator]
QED

Theorem inline_caller_residual_exec_block:
  !fuel ctx bb s t. exec_block fuel ctx bb s = OK t /\
  ~s.vs_halted /\ ~t.vs_halted ==>
  inline_caller_residual t = inline_caller_residual s
Proof
  rpt gen_tac >>
  completeInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `exec_block fuel ctx bb s = OK t` mp_tac >>
  once_rewrite_tac[exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  rename1 `step_inst fuel ctx inst s = OK u` >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[]
  >- (Cases_on `u.vs_halted` >> simp[] >> strip_tac >> gvs[] >>
      metis_tac[inline_caller_residual_step]) >>
  strip_tac >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  `~u.vs_halted` by metis_tac[step_preserves_halted] >>
  `inline_caller_residual t =
    inline_caller_residual (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (first_x_assum irule >> simp[] >> qexists `bb` >> simp[]) >>
  metis_tac[inline_caller_residual_step, inline_caller_residual_updates]
QED

Theorem inline_caller_residual_run_block:
  run_block fuel ctx bb s = OK t /\ ~s.vs_halted /\ ~t.vs_halted ==>
  inline_caller_residual t = inline_caller_residual s
Proof
  strip_tac >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs >>
  gvs[run_block_def] >>
  drule eval_phis_only_updates_vs_vars >> disch_then SUBST_ALL_TAC >>
  drule inline_caller_residual_exec_block >> simp[]
QED

Definition inline_caller_data_def:
  inline_caller_data N opaque_caller c d <=>
    inline_shared_frame c = inline_shared_frame d /\
    inline_caller_bookkeeping c d /\
    (!x. x IN N DIFF opaque_caller ==> lookup_var x c = lookup_var x d) /\
    c.vs_labels = FEMPTY /\ d.vs_labels = FEMPTY
End

Theorem inline_caller_data_initial:
  s.vs_labels = FEMPTY ==> inline_caller_data N opaque_caller s s
Proof
  simp[inline_caller_data_def]
QED

Theorem inline_caller_data_setup:
  inline_caller_data N opaque_caller c d /\ setup_callee fn args c = SOME cs /\
  ~c.vs_halted ==>
  inline_opaque_frame_rel ren {} opaque d.vs_vars P cs d
Proof
  simp[inline_caller_data_def, inline_opaque_frame_rel_def, inline_frame_rel_def] >>
  metis_tac[inline_shared_frame_setup]
QED

(* The countdown is the number of ordinary instructions still to traverse.
   R owns the program points; Q owns all terminal and continuation results. *)
Theorem inline_exec_block_segment:
  !(n:num) R Q fuel ctx bb fuel' ctx' bb' s t.
    R n s t /\
    (!s t. R 0 s t ==>
      Q (exec_block fuel ctx bb s) (exec_block fuel' ctx' bb' t)) /\
    (!m s t. 0 < m /\ m <= n /\ R m s t ==>
      ?i j. get_instruction bb s.vs_inst_idx = SOME i /\
        get_instruction bb' t.vs_inst_idx = SOME j /\
        ~is_terminator i.inst_opcode /\ ~is_terminator j.inst_opcode /\
        (case step_inst fuel ctx i s of
           OK u => ?v. step_inst fuel' ctx' j t = OK v /\
             R (m - 1) (u with vs_inst_idx := SUC s.vs_inst_idx)
                       (v with vs_inst_idx := SUC t.vs_inst_idx)
         | IntRet vals u => F
         | Halt u => ?v. step_inst fuel' ctx' j t = Halt v /\
             Q (Halt u) (Halt v)
         | Abort a u => ?v. step_inst fuel' ctx' j t = Abort a v /\
             Q (Abort a u) (Abort a v)
         | Error e => ?e'. step_inst fuel' ctx' j t = Error e' /\
             Q (Error e) (Error e'))) ==>
    Q (exec_block fuel ctx bb s) (exec_block fuel' ctx' bb' t)
Proof
  Induct_on `n`
  >- (rpt strip_tac >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!m s t. _` (qspecl_then [`SUC n`, `s`, `t`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  once_rewrite_tac[exec_block_def] >> simp[] >>
  Cases_on `step_inst fuel ctx i s` >> gvs[] >>
  qpat_x_assum `!R Q fuel ctx bb fuel' ctx' bb' s t. _` irule >>
  qexists `R` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem inline_opaque_frame_indices[simp]:
  inline_opaque_frame_rel ren V opaque saved P
    (s with vs_inst_idx := i) (t with vs_inst_idx := j) <=>
  inline_opaque_frame_rel ren V opaque saved P s t
Proof
  simp[functionInlinerFrameTheory.inline_opaque_frame_rel_def,
    functionInlinerFrameTheory.inline_frame_rel_def,
    functionInlinerFrameTheory.inline_shared_frame_def,
    stateFrameTheory.execution_frame_def, venomStateTheory.lookup_var_def]
QED

(* Indexed clone consumer. supps records support after each successful prefix;
   terminal observations are deliberately independent of instruction indices.
   For pre ++ body ++ tail and pre' ++ MAP (clone_instruction p labels) body
   ++ tail', take n = LENGTH body, a = LENGTH pre, b = LENGTH pre', and
   instrs m = EL (n - m) body. The tails remain arbitrary continuations. *)
Theorem inline_clone_exec_block_segment:
  !n supps instrs Q ren opaque saved P p labels fuel ctx bb fuel' ctx' bb' a b s t.
    s.vs_inst_idx = a /\ t.vs_inst_idx = b /\
    inline_opaque_frame_rel ren (supps n) opaque saved P s t /\
    (!m. 0 < m /\ m <= n ==>
      get_instruction bb (a + n - m) = SOME (instrs m) /\
      get_instruction bb' (b + n - m) = SOME (clone_instruction p labels (instrs m)) /\
      inst_wf (instrs m) /\ inline_ordinary_opcode (instrs m).inst_opcode /\
      ~is_terminator (instrs m).inst_opcode /\
      supps (m - 1) = supps m UNION set (instrs m).inst_outputs /\
      (!u v. u IN supps m UNION set (instrs m).inst_outputs /\
             v IN supps m UNION set (instrs m).inst_outputs ==> (ren u = ren v <=> u = v)) /\
      (!x. MEM x (instrs m).inst_outputs ==> ren x NOTIN P /\ ren x = STRCAT p x)) /\
    (!m s t. 0 < m /\ m <= n /\
      s.vs_inst_idx = a + n - m /\ t.vs_inst_idx = b + n - m /\
      inline_opaque_frame_rel ren (supps m) opaque saved P s t ==>
      !op. MEM op (instrs m).inst_operands ==>
        eval_operand (clone_operand p labels op) t = eval_operand op s) /\
    (!s t. s.vs_inst_idx = a + n /\ t.vs_inst_idx = b + n /\
      inline_opaque_frame_rel ren (supps 0) opaque saved P s t ==>
      Q (exec_block fuel ctx bb s) (exec_block fuel' ctx' bb' t)) /\
    (!m s t. m <= n /\ inline_opaque_frame_rel ren (supps m) opaque saved P s t ==>
      Q (Halt s) (Halt t) /\ (!a. Q (Abort a s) (Abort a t))) /\
    (!e e'. Q (Error e) (Error e')) ==>
    Q (exec_block fuel ctx bb s) (exec_block fuel' ctx' bb' t)
Proof
  rpt gen_tac >> strip_tac >>
  irule inline_exec_block_segment >>
  qexistsl [`\m s t. s.vs_inst_idx = a + n - m /\
    t.vs_inst_idx = b + n - m /\
    inline_opaque_frame_rel ren (supps m) opaque saved P s t`, `n`] >>
  simp[] >> rpt gen_tac >> strip_tac >>
  rename1 `inline_opaque_frame_rel ren (supps m) opaque saved P ss tt` >>
  qpat_assum `!m. 0 < m /\ m <= n ==> _` (qspec_then `m` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  conj_tac >- simp[clone_instruction_def] >>
  `inline_ordinary_step_result ren (supps m) opaque saved P (instrs m)
    (step_inst fuel ctx (instrs m) ss)
    (step_inst fuel' ctx' (clone_instruction p labels (instrs m)) tt)` by
    (irule inline_ordinary_clone_step_result >> simp[] >> metis_tac[]) >>
  Cases_on `step_inst fuel ctx (instrs m) ss` >>
  gvs[inline_ordinary_step_result_def] >> metis_tac[]
QED

(* Error is deliberately excluded: consumers require source termination.
   J retains the clone-local return packet; it is not a terminal observation. *)
Definition inline_cps_result_def:
  inline_cps_result kont obs retk r q <=>
    case r of
      OK s => (?t. q = OK t /\ kont s t)
    | IntRet ir s => retk ir s q
    | Halt s => (?t. q = Halt t /\ obs s t)
    | Abort a s => (?t. q = Abort a t /\ obs s t)
    | Error e => F
End

(* Consume the producer at the actual rewritten suffix, not at block entry.
   C executes the suspended target continuation, with the full exit packet
   available (including the saved caller and local callee state). *)
Theorem inline_return_exit_cps:
  step_inst source_fuel ctx inst s = IntRet ir s' ==>
  (inst.inst_opcode = RET \/ inst.inst_opcode = RETFMP) /\
  inst.inst_operands = ops ++ [pc] /\
  raw_return_user_arity inst = SOME (LENGTH outs) /\
  EVERY (\op. (!v. op = Var v ==> v IN V /\ v NOTIN opaque) /\
    ~is_label_op op) ops /\
  (!x v. MEM x outs /\ v IN V ==> STRCAT p v <> x) /\
  inline_opaque_frame_rel (STRCAT p) V opaque caller.vs_vars P s t /\
  bb.bb_instructions = pre ++
    FST (rewrite_inline_inst args outs ret (clone_instruction p [] inst) param_idx) /\
  ~t.vs_halted /\
  (!q. inline_clone_exit p V opaque P outs caller ret ir s' q ==> C q) ==>
  inline_cps_result kont obs (inline_clone_exit p V opaque P outs caller ret)
    (IntRet ir s') (exec_block fuel ctx bb (t with vs_inst_idx := LENGTH pre)) /\
  C (exec_block fuel ctx bb (t with vs_inst_idx := LENGTH pre))
Proof
  strip_tac >> strip_tac >>
  drule inline_return_exit_packet >>
  disch_then (drule_at (Pat `inline_opaque_frame_rel _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `_ .bb_instructions = _`)) >>
  simp[] >> disch_then (qspec_then `fuel` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  simp[inline_cps_result_def]
QED

(* Actual raw-site continuation dispatch. The return block is entered once:
   run_block performs its parallel PHIs before the exec_block suffix.
   This boundary makes no claim about fix_inline_phis/renumber_fn_inst_ids. *)
Theorem inline_clone_exit_raw_continuation:
  inline_clone_exit p V opaque P outs caller ret ir s' (OK v) /\
  lookup_block lbl caller_fn.fn_blocks = SOME source_bb /\
  ~MEM ret (fn_labels caller_fn) /\
  rb = <|bb_label := ret;
         bb_instructions := DROP (i+1) source_bb.bb_instructions|> /\
  eval_phis v rb.bb_instructions = OK vphi /\
  exec_block f ctx rb
    (vphi with vs_inst_idx := phi_prefix_length rb.bb_instructions) = OK w /\
  ~w.vs_halted /\
  run_blocks g ctx (inline_call_site p ret caller_fn callee lbl i) w = res /\
  terminates res ==>
  ?h. run_blocks h ctx (inline_call_site p ret caller_fn callee lbl i) v = res
Proof
  strip_tac >>
  `v.vs_current_bb = ret` by
    (drule inline_clone_exit_control >> simp[]) >>
  irule inline_run_blocks_join >> conj_tac >- simp[] >>
  qexistsl [`rb`, `f`, `g`, `w`] >> simp[run_block_def] >>
  gvs[inline_call_site_lookup_return]
QED

(* Instantiation of the return lift by the actual raw-site dispatcher above.
   A producer such as inline_return_exit_cps supplies the first premise. *)
Theorem inline_clone_result_raw_continuation:
  inline_cps_result kont obs (inline_clone_exit p V opaque P outs caller ret)
    (IntRet ir s') q /\
  lookup_block lbl caller_fn.fn_blocks = SOME source_bb /\
  ~MEM ret (fn_labels caller_fn) /\
  rb = <|bb_label := ret;
         bb_instructions := DROP (i+1) source_bb.bb_instructions|> /\
  (!v. inline_clone_exit p V opaque P outs caller ret ir s' (OK v) ==>
    ?vphi f w g.
      eval_phis v rb.bb_instructions = OK vphi /\
      exec_block f ctx rb
        (vphi with vs_inst_idx := phi_prefix_length rb.bb_instructions) = OK w /\
      ~w.vs_halted /\
      run_blocks g ctx (inline_call_site p ret caller_fn callee lbl i) w = res /\
      terminates res) ==>
  ?v h. q = OK v /\
    run_blocks h ctx (inline_call_site p ret caller_fn callee lbl i) v = res
Proof
  simp[inline_cps_result_def] >> strip_tac >>
  drule inline_clone_exit_control >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  irule inline_clone_exit_raw_continuation >> simp[] >>
  metis_tac[]
QED

(* A genuine INVOKE resumes after the PHI prefix, so block entry of the
   generated continuation has no parallel assignments left to execute. *)
Theorem inline_clone_exit_invoke_continuation:
  inline_clone_exit p V opaque P outs caller ret ir s' (OK v) /\
  lookup_block lbl caller_fn.fn_blocks = SOME source_bb /\
  ~MEM ret (fn_labels caller_fn) /\
  bb_well_formed source_bb /\ i < LENGTH source_bb.bb_instructions /\
  (EL i source_bb.bb_instructions).inst_opcode = INVOKE /\
  rb = <|bb_label := ret;
         bb_instructions := DROP (i+1) source_bb.bb_instructions|> /\
  exec_block f ctx rb (v with vs_inst_idx := 0) = OK w /\
  ~w.vs_halted /\
  run_blocks g ctx (inline_call_site p ret caller_fn callee lbl i) w = res /\
  terminates res ==>
  ?h. run_blocks h ctx (inline_call_site p ret caller_fn callee lbl i) v = res
Proof
  strip_tac >> irule inline_clone_exit_raw_continuation >>
  simp[] >> conj_tac
  >- (qexistsl [`f`, `g`, `v`, `w`] >>
      simp[] >>
      metis_tac[inline_invoke_suffix_eval_phis, inline_invoke_suffix_phi_prefix]) >>
  metis_tac[]
QED

(* The source continuation is an exec_block suffix, not a second block entry.
   In particular, merge/adopt precede binding the returned values. *)
Theorem inline_invoke_exec_suffix:
  get_instruction bb s.vs_inst_idx = SOME call /\
  call.inst_opcode = INVOKE /\ decode_invoke call = SOME (name,ops) /\
  lookup_function name ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME vals /\ setup_callee callee vals s = SOME cs ==>
  exec_block n ctx bb s =
    case run_blocks n ctx callee cs of
      IntRet ir u =>
        (case bind_outputs call.inst_outputs ir.iret_values
                (adopt_return_fmp ir (merge_callee_state s u)) of
           NONE => Error "invoke: return arity mismatch"
         | SOME w => exec_block n ctx bb
             (w with vs_inst_idx := SUC s.vs_inst_idx))
    | Halt u => Halt u
    | Abort a u => Abort a u
    | Error e => Error e
    | OK u => Error "invoke: callee did not return"
Proof
  strip_tac >> CONV_TAC (LHS_CONV (REWR_CONV exec_block_def)) >>
  simp[Once step_inst_def] >>
  Cases_on `run_blocks n ctx callee cs` >> simp[] >>
  CASE_TAC >> simp[venomInstTheory.is_terminator_def]
QED

(* Final-layout continuation entry. No execution of the suffix is assumed. *)
Theorem inline_final_return_dispatch:
  find_invoke_site callee.fn_name caller.fn_blocks = SOME (lbl,i) /\
  p = inline_prefix ist.is_inline_count /\
  ret = return_block_label p ist.is_label_counter /\
  lookup_block lbl caller.fn_blocks = SOME bb /\
  ~MEM ret (fn_labels caller) /\ bb_well_formed bb /\
  i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode = INVOKE /\
  inline_one_site caller callee ist = SOME (final,ist') ==>
  ?rb. lookup_block ret final.fn_blocks = SOME rb /\
    MAP inline_inst_fields rb.bb_instructions =
      MAP inline_inst_fields (DROP (i+1) bb.bb_instructions) /\
    phi_prefix_length rb.bb_instructions = 0 /\
    (!v. eval_phis v rb.bb_instructions = OK v) /\
    (!v k ctx'. v.vs_current_bb = ret ==>
      run_blocks (SUC k) ctx' final v =
        case exec_block k ctx' rb (v with vs_inst_idx := 0) of
          OK w => if w.vs_halted then Halt w else run_blocks k ctx' final w
        | IntRet ir w => IntRet ir w
        | other => other)
Proof
  strip_tac >>
  `EVERY (\inst. inst.inst_opcode <> PHI) (DROP (i+1) bb.bb_instructions)` by
    (irule inline_invoke_suffix_nonphi >> simp[]) >>
  `lookup_block ret (inline_call_site p ret caller callee lbl i).fn_blocks =
     SOME <|bb_label := ret; bb_instructions := DROP (i+1) bb.bb_instructions|>` by
    (irule inline_call_site_lookup_return >> simp[]) >>
  drule_all inline_one_site_lookup_fields >> strip_tac >>
  `MAP (\inst. if inst.inst_opcode <> PHI then inst
           else subst_label_inst lbl ret inst) (DROP (i+1) bb.bb_instructions) =
     DROP (i+1) bb.bb_instructions` by
    (CONV_TAC (RHS_CONV (REWR_CONV (GSYM (cj 1 MAP_ID)))) >>
     irule MAP_CONG >> gvs[EVERY_MEM]) >>
  gvs[] >>
  `EVERY (\inst. inst.inst_opcode <> PHI) tb.bb_instructions` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     `MEM (inline_inst_fields inst) (MAP inline_inst_fields tb.bb_instructions)` by
       (simp[MEM_MAP] >> metis_tac[]) >>
     qpat_x_assum `MAP inline_inst_fields tb.bb_instructions = _`
       (fn th => RULE_ASSUM_TAC (PURE_ONCE_REWRITE_RULE [th])) >>
     gvs[MEM_MAP, inline_inst_fields_def, EVERY_MEM] >> metis_tac[]) >>
  `phi_prefix_length tb.bb_instructions = 0` by
    (Cases_on `tb.bb_instructions` >> gvs[phi_prefix_length_def]) >>
  `!v. eval_phis v tb.bb_instructions = OK v` by
    (gen_tac >> irule venomExecProofsTheory.eval_phis_no_phis >> simp[]) >>
  simp[] >> rpt strip_tac >>
  simp[Once run_blocks_def]
QED

Definition inline_source_resume_def:
  inline_source_resume n ctx bb caller outs ir u =
    case bind_outputs outs ir.iret_values
           (adopt_return_fmp ir (merge_callee_state caller u)) of
      NONE => Error "invoke: return arity mismatch"
    | SOME w => exec_block n ctx bb
        (w with vs_inst_idx := SUC caller.vs_inst_idx)
End

(* Join the suffix-IH witnesses under the final-function dispatcher. *)
Theorem inline_return_dispatch_cut:
  (!v k. v.vs_current_bb = ret ==>
    run_blocks (SUC k) ctx' final v =
      case exec_block k ctx' rb (v with vs_inst_idx := 0) of
        OK z => if z.vs_halted then Halt z else run_blocks k ctx' final z
      | IntRet ir z => IntRet ir z
      | other => other) /\
  (!r q. Q r q ==> terminates q) /\
  (!w v r. A w v /\
    exec_block n ctx bb (w with vs_inst_idx := SUC caller.vs_inst_idx) = r /\
    terminates r ==>
    ?k. case exec_block k ctx' rb (v with vs_inst_idx := 0) of
      OK z => if z.vs_halted then Q r (Halt z)
              else ?g. Q r (run_blocks g ctx' final z)
    | IntRet ir z => Q r (IntRet ir z)
    | Halt z => Q r (Halt z)
    | Abort a z => Q r (Abort a z)
    | Error e => F) /\
  A w v /\ v.vs_current_bb = ret /\
  exec_block n ctx bb (w with vs_inst_idx := SUC caller.vs_inst_idx) = r /\
  terminates r ==>
  ?h. Q r (run_blocks h ctx' final v)
Proof
  strip_tac >>
  qpat_x_assum `!w v r. _` drule_all >> strip_tac >>
  Cases_on `exec_block k ctx' rb (v with vs_inst_idx := 0)` >> gvs[]
  >- (Cases_on `v'.vs_halted` >> gvs[]
      >- (qexists `SUC k` >> simp[]) >>
      `terminates (run_blocks g ctx' final v')` by metis_tac[] >>
      `exec_block (g+k) ctx' rb (v with vs_inst_idx := 0) = OK v'` by
        (irule (cj 2 venomExecPropsTheory.fuel_mono) >>
         simp[] >> qexists `k` >> simp[]) >>
      `run_blocks (g+k) ctx' final v' = run_blocks g ctx' final v'` by
        (drule crossBlockSimPropsTheory.run_blocks_fuel_mono >>
         disch_then (qspec_then `k` mp_tac) >> simp[]) >>
      qexists `SUC (g+k)` >> simp[])
  >> qexists `SUC k` >> simp[]
QED

(* The layout supplies the dispatcher; the caller E occurrence supplies the
   universal suffix premise, at each related resumed source/target state. *)
Theorem inline_final_return_cut:
  find_invoke_site callee.fn_name caller_fn.fn_blocks = SOME (lbl,i) /\
  p = inline_prefix ist.is_inline_count /\
  ret = return_block_label p ist.is_label_counter /\
  lookup_block lbl caller_fn.fn_blocks = SOME bb /\
  ~MEM ret (fn_labels caller_fn) /\ bb_well_formed bb /\
  i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode = INVOKE /\
  inline_one_site caller_fn callee ist = SOME (final,ist') ==>
  (!r q. Q r q ==> terminates q) ==>
  (!rb w v r. lookup_block ret final.fn_blocks = SOME rb /\ A w v /\
    exec_block n ctx bb (w with vs_inst_idx := SUC caller.vs_inst_idx) = r /\
    terminates r ==>
    ?k. case exec_block k ctx' rb (v with vs_inst_idx := 0) of
      OK z => if z.vs_halted then Q r (Halt z)
              else ?g. Q r (run_blocks g ctx' final z)
    | IntRet ir z => Q r (IntRet ir z)
    | Halt z => Q r (Halt z)
    | Abort a z => Q r (Abort a z)
    | Error e => F) ==>
  A w v /\ v.vs_current_bb = ret /\
  exec_block n ctx bb (w with vs_inst_idx := SUC caller.vs_inst_idx) = r /\
  terminates r ==>
  ?h. Q r (run_blocks h ctx' final v)
Proof
  strip_tac >> drule_all inline_final_return_dispatch >> strip_tac >>
  rpt strip_tac >> irule inline_return_dispatch_cut >>
  metis_tac[]
QED

(* Packet and source binding are separate inputs to the bridge.  In
   particular no return-value equality is inferred from an opaque frame. *)
Theorem inline_clone_exit_final_cut:
  inline_clone_exit p V opaque P outs saved ret ir u (OK v) ==>
  find_invoke_site callee.fn_name caller_fn.fn_blocks = SOME (lbl,i) /\
  p = inline_prefix ist.is_inline_count /\
  ret = return_block_label p ist.is_label_counter /\
  lookup_block lbl caller_fn.fn_blocks = SOME bb /\
  ~MEM ret (fn_labels caller_fn) /\ bb_well_formed bb /\
  i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode = INVOKE /\
  inline_one_site caller_fn callee ist = SOME (final,ist') ==>
  (!ir u v w. inline_clone_exit p V opaque P outs saved ret ir u (OK v) ==>
    bind_outputs outs ir.iret_values
      (adopt_return_fmp ir (merge_callee_state caller u)) = SOME w ==>
    A w v) ==>
  (!r q. Q r q ==> terminates q) ==>
  (!rb w v r. lookup_block ret final.fn_blocks = SOME rb /\ A w v /\
    exec_block n ctx bb (w with vs_inst_idx := SUC caller.vs_inst_idx) = r /\
    terminates r ==>
    ?k. case exec_block k ctx' rb (v with vs_inst_idx := 0) of
      OK z => if z.vs_halted then Q r (Halt z)
              else ?g. Q r (run_blocks g ctx' final z)
    | IntRet ir z => Q r (IntRet ir z)
    | Halt z => Q r (Halt z)
    | Abort a z => Q r (Abort a z)
    | Error e => F) ==>
  inline_source_resume n ctx bb caller outs ir u = r /\ terminates r ==>
  ?h. Q r (run_blocks h ctx' final v)
Proof
  rpt strip_tac >>
  Cases_on `bind_outputs outs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state caller u))`
  >- gvs[inline_source_resume_def, passSimulationDefsTheory.terminates_def] >>
  fs[inline_source_resume_def] >>
  drule inline_clone_exit_control >> strip_tac >> gvs[] >>
  irule inline_final_return_cut >> simp[] >>
  metis_tac[]
QED


Theorem inline_caller_data_return:
  inline_caller_data N opaque_caller c d /\
  inline_clone_exit p V opaque P outs c ret ir u (OK v) /\
  (N DIFF opaque_caller) SUBSET P /\
  inline_caller_bookkeeping d v /\
  inline_caller_residual v = inline_caller_residual d /\
  inline_fmp_result c.vs_fmp (IntRet ir u) /\
  bind_outputs outs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state c u)) = SOME w ==>
  inline_caller_data N opaque_caller w v
Proof
  strip_tac >>
  drule_all inline_clone_exit_fmp_reentry >> strip_tac >>
  drule inline_return_bind_merge >>
  disch_then (qspecl_then [`u`, `ir`] assume_tac) >> gvs[] >>
  `inline_shared_frame caller' = inline_shared_frame c` by
    (irule venomInstProofs1Theory.bind_outputs_preserves >>
     simp[] >> goal_assum (drule_at Any)) >>
  `inline_caller_residual v = inline_caller_residual caller'` by
    metis_tac[inline_caller_residual_shared, inline_caller_data_def] >>
  drule inline_caller_residual_reconstruct >>
  disch_then (qspec_then `v.vs_fmp` mp_tac) >> simp[] >> strip_tac >>
  drule inline_caller_bookkeeping_bind >> strip_tac >>
  gvs[inline_clone_exit_def] >>
  drule inline_return_merge_effects >>
  disch_then (qspec_then `caller'` strip_assume_tac) >>
  Cases_on `ir.iret_adopt_fmp` >>
  gvs[inline_caller_data_def, inline_caller_bookkeeping_def,
      jump_to_def, adopt_return_fmp_def, merge_callee_state_def,
      inline_shared_frame_def, stateFrameTheory.execution_frame_def,
      venom_state_component_equality, SUBSET_DEF, lookup_var_def] >>
  metis_tac[]
QED

Theorem inline_caller_data_return_execution:
  inline_caller_data N opaque_caller c d /\
  exec_block fuel ctx bb d = OK v /\ ~d.vs_halted /\ ~v.vs_halted /\
  inline_clone_exit p V opaque P outs c ret ir u (OK v) /\
  (N DIFF opaque_caller) SUBSET P /\
  inline_fmp_result c.vs_fmp (IntRet ir u) /\
  bind_outputs outs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state c u)) = SOME w ==>
  inline_caller_data N opaque_caller w v
Proof
  strip_tac >> irule inline_caller_data_return >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[inline_caller_residual_exec_block,
            inline_caller_bookkeeping_exec_block, inline_caller_bookkeeping_refl]
QED

(* The target caller anchor is independent of the callee's local frame. *)
Definition inline_target_anchor_def:
  inline_target_anchor d t <=>
    inline_caller_bookkeeping d t /\
    inline_caller_residual t = inline_caller_residual d
End

Theorem inline_target_anchor_refl[simp]:
  inline_target_anchor d d
Proof
  simp[inline_target_anchor_def]
QED

Theorem inline_target_anchor_index[simp]:
  inline_target_anchor d (t with vs_inst_idx := j) = inline_target_anchor d t
Proof
  simp[inline_target_anchor_def]
QED

Theorem inline_target_anchor_exec_block:
  exec_block fuel ctx bb d = OK v /\ ~d.vs_halted /\ ~v.vs_halted ==>
  inline_target_anchor d v
Proof
  metis_tac[inline_target_anchor_def, inline_caller_bookkeeping_exec_block,
    inline_caller_bookkeeping_refl, inline_caller_residual_exec_block]
QED

Theorem inline_opaque_frame_saved_restrict:
  inline_opaque_frame_rel ren V opaque saved P s t /\
  (!x. x IN P ==> FLOOKUP saved x = FLOOKUP saved' x) ==>
  inline_opaque_frame_rel ren V opaque saved' P s t
Proof
  simp[inline_opaque_frame_rel_def, inline_frame_rel_def] >> metis_tac[]
QED

Theorem inline_caller_data_setup_source_saved:
  inline_caller_data N opaque_caller c d /\ setup_callee fn args c = SOME cs /\
  ~c.vs_halted ==>
  inline_opaque_frame_rel ren {} opaque c.vs_vars (N DIFF opaque_caller) cs d
Proof
  strip_tac >> irule inline_opaque_frame_saved_restrict >>
  qexists `d.vs_vars` >> reverse conj_tac
  >- metis_tac[inline_caller_data_setup] >>
  gvs[inline_caller_data_def, lookup_var_def] >> metis_tac[]
QED

Definition inline_site_exit_def:
  inline_site_exit N opaque_caller p V opaque outs c d ret ir u v <=>
    inline_clone_exit p V opaque (N DIFF opaque_caller) outs c ret ir u (OK v) /\
    inline_target_anchor d v /\ inline_fmp_result c.vs_fmp (IntRet ir u)
End

Theorem inline_site_exit_caller_data:
  inline_caller_data N opaque_caller c d /\
  inline_site_exit N opaque_caller p V opaque outs c d ret ir u v /\
  bind_outputs outs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state c u)) = SOME w ==>
  inline_caller_data N opaque_caller w v
Proof
  simp[inline_site_exit_def, inline_target_anchor_def] >>
  metis_tac[inline_caller_data_return, SUBSET_REFL]
QED

(* Instruction points are after entry PHIs; predecessor repair is not an
   instruction-point operation. *)
Definition inline_caller_point_def:
  inline_caller_point caller final lbl i ret N opaque_caller b j s t <=>
    inline_caller_data N opaque_caller s t /\
    s.vs_current_bb = b /\ s.vs_inst_idx = j /\
    t.vs_current_bb = (if b = lbl /\ i < j then ret else b) /\
    t.vs_inst_idx = (if b = lbl /\ i < j then j - (i+1) else j) /\
    (?bb tb. lookup_block b caller.fn_blocks = SOME bb /\
      lookup_block t.vs_current_bb final.fn_blocks = SOME tb /\
      j <= LENGTH bb.bb_instructions /\ t.vs_inst_idx <= LENGTH tb.bb_instructions)
End

Definition inline_clone_point_def:
  inline_clone_point caller callee final lbl i p ret N opaque_caller opaque
    c d V b j counter s t <=>
    inline_caller_data N opaque_caller c d /\
    inline_opaque_frame_rel (STRCAT p) V opaque c.vs_vars
      (N DIFF opaque_caller) s t /\ inline_target_anchor d t /\
    s.vs_current_bb = b /\ s.vs_inst_idx = j /\
    t.vs_current_bb = STRCAT p b /\
    (?call_bb cb tb.
      lookup_block lbl caller.fn_blocks = SOME call_bb /\
      lookup_block b callee.fn_blocks = SOME cb /\
      lookup_block (STRCAT p b) final.fn_blocks = SOME tb /\
      j <= LENGTH cb.bb_instructions /\
      let pre = rewrite_inline_insts
        (rotate_invoke_ops (EL i call_bb.bb_instructions).inst_operands)
        (EL i call_bb.bb_instructions).inst_outputs ret
        (MAP (clone_instruction p (fn_labels callee)) (TAKE j cb.bb_instructions)) 0
      in t.vs_inst_idx = LENGTH (FST pre) /\ counter = SND pre /\
         t.vs_inst_idx <= LENGTH tb.bb_instructions)
End

Theorem inline_caller_data_indices[simp]:
  inline_caller_data N opaque_caller (s with vs_inst_idx := j)
    (t with vs_inst_idx := k) = inline_caller_data N opaque_caller s t
Proof
  simp[inline_caller_data_def, inline_caller_bookkeeping_def,
       inline_shared_frame_def, stateFrameTheory.execution_frame_def, lookup_var_def]
QED

Theorem inline_site_exit_control:
  inline_site_exit N opaque_caller p V opaque outs c d ret ir u v ==>
  v.vs_current_bb = ret /\ v.vs_inst_idx = 0
Proof
  simp[inline_site_exit_def] >> strip_tac >>
  drule inline_clone_exit_control >> simp[]
QED

Theorem inline_site_exit_anchor:
  inline_site_exit N opaque_caller p V opaque outs c d ret ir u v ==>
  inline_target_anchor d v
Proof
  simp[inline_site_exit_def]
QED

Theorem inline_site_exit_packet:
  inline_site_exit N opaque_caller p V opaque outs c d ret ir u v ==>
  inline_clone_exit p V opaque (N DIFF opaque_caller) outs c ret ir u (OK v)
Proof
  simp[inline_site_exit_def]
QED

(* Expanded offsets advance by the whole rewrite, not one target instruction. *)
Theorem inline_clone_prefix_successor:
  j < LENGTH insts ==>
  let pre = rewrite_inline_insts args outs ret
        (MAP (clone_instruction p labs) (TAKE j insts)) 0;
      focus = rewrite_inline_inst args outs ret
        (clone_instruction p labs (EL j insts)) (SND pre);
      next = rewrite_inline_insts args outs ret
        (MAP (clone_instruction p labs) (TAKE (SUC j) insts)) 0
  in LENGTH (FST next) = LENGTH (FST pre) + LENGTH (FST focus) /\
     SND next = SND focus
Proof
  strip_tac >>
  `TAKE (SUC j) insts = TAKE j insts ++ [EL j insts]` by
    simp[arithmeticTheory.ADD1, rich_listTheory.TAKE_EL_SNOC, SNOC_APPEND] >>
  simp[MAP_APPEND, rewrite_inline_insts_append, rewrite_inline_insts_def,
       pairTheory.UNCURRY]
QED

Theorem inline_final_nonphi_getter:
  lookup_block l raw.fn_blocks = SOME bb /\
  lookup_block l (renumber_fn_inst_ids (fix_inline_phis old fresh rb raw)).fn_blocks = SOME tb /\
  k < LENGTH bb.bb_instructions /\ (EL k bb.bb_instructions).inst_opcode <> PHI ==>
  get_instruction tb k = SOME (EL k tb.bb_instructions) /\
  inline_inst_fields (EL k tb.bb_instructions) =
    inline_inst_fields (EL k bb.bb_instructions)
Proof
  strip_tac >> rev_drule inline_final_lookup_fields >>
  disch_then (qspecl_then [`rb`, `old`, `fresh`] strip_assume_tac) >> gvs[] >>
  `LENGTH tb.bb_instructions = LENGTH bb.bb_instructions` by
    (drule inline_fields_length >>
     Cases_on `MEM bb.bb_label (bb_succs rb)` >> simp[]) >>
  simp[get_instruction_def] >>
  qpat_x_assum `MAP inline_inst_fields _ = _` mp_tac >>
  simp[LIST_EQ_REWRITE] >> strip_tac >>
  qpat_x_assum `LENGTH _ = LENGTH (if _ then _ else _)` kall_tac >>
  first_x_assum (qspec_then `k` mp_tac) >>
  Cases_on `MEM bb.bb_label (bb_succs rb)` >>
  asm_simp_tac bool_ss [EL_MAP, LENGTH_MAP]
QED

Theorem inline_caller_point_prefix_getter:
  inline_caller_point caller final lbl i ret N opaque b j s t /\
  final = renumber_fn_inst_ids (fix_inline_phis lbl ret rb
    (inline_call_site p ret caller callee lbl i)) /\
  b = lbl /\ j < i /\
  lookup_block lbl caller.fn_blocks = SOME bb /\
  i <= LENGTH bb.bb_instructions /\
  (EL j bb.bb_instructions).inst_opcode <> PHI ==>
  ?tb. lookup_block t.vs_current_bb final.fn_blocks = SOME tb /\
    get_instruction tb t.vs_inst_idx = SOME (EL j tb.bb_instructions) /\
    inline_inst_fields (EL j tb.bb_instructions) =
      inline_inst_fields (EL j bb.bb_instructions)
Proof
  strip_tac >> gvs[inline_caller_point_def] >>
  drule inline_call_site_lookup_call >>
  disch_then (qspecl_then [`ret`, `p`, `i`, `callee`] assume_tac) >>
  drule inline_final_nonphi_getter >>
  simp[rich_listTheory.EL_APPEND1, rich_listTheory.EL_TAKE] >>
  disch_then drule >>
  disch_then (qspec_then `s.vs_inst_idx` mp_tac) >>
  simp[rich_listTheory.EL_APPEND1, rich_listTheory.EL_TAKE]
QED

Theorem inline_caller_point_suffix_getter:
  inline_caller_point caller final lbl i ret N opaque b j s t /\
  final = renumber_fn_inst_ids (fix_inline_phis lbl ret rb
    (inline_call_site p ret caller callee lbl i)) /\
  b = lbl /\ i < j /\
  lookup_block lbl caller.fn_blocks = SOME bb /\
  ~MEM ret (fn_labels caller) /\ j < LENGTH bb.bb_instructions /\
  (EL j bb.bb_instructions).inst_opcode <> PHI ==>
  ?tb. lookup_block t.vs_current_bb final.fn_blocks = SOME tb /\
    get_instruction tb t.vs_inst_idx = SOME (EL t.vs_inst_idx tb.bb_instructions) /\
    inline_inst_fields (EL t.vs_inst_idx tb.bb_instructions) =
      inline_inst_fields (EL j bb.bb_instructions)
Proof
  strip_tac >> gvs[inline_caller_point_def] >>
  drule_all inline_call_site_lookup_return >>
  disch_then (qspecl_then [`p`, `i`, `callee`] assume_tac) >>
  drule inline_final_nonphi_getter >> simp[] >>
  disch_then drule >>
  disch_then (qspec_then `s.vs_inst_idx - (i+1)` mp_tac) >>
  simp[rich_listTheory.EL_DROP]
QED


Theorem inline_clone_point_focus_getter:
  inline_clone_point caller callee final lbl i p ret N opaque_caller opaque
    c d V b j counter s t /\
  final = renumber_fn_inst_ids (fix_inline_phis lbl ret rb
    (inline_call_site p ret caller callee lbl i)) /\
  lookup_block lbl caller.fn_blocks = SOME call_bb /\
  lookup_block b callee.fn_blocks = SOME cb /\
  ~MEM (STRCAT p b) (fn_labels caller) /\ STRCAT p b <> ret /\
  cb.bb_instructions = pre ++ inst::post /\ j = LENGTH pre /\
  focus = FST (rewrite_inline_inst
    (rotate_invoke_ops (EL i call_bb.bb_instructions).inst_operands)
    (EL i call_bb.bb_instructions).inst_outputs ret
    (clone_instruction p (fn_labels callee) inst) counter) /\
  k < LENGTH focus /\ (EL k focus).inst_opcode <> PHI ==>
  ?tb. lookup_block t.vs_current_bb final.fn_blocks = SOME tb /\
    get_instruction tb (t.vs_inst_idx+k) =
      SOME (EL (t.vs_inst_idx+k) tb.bb_instructions) /\
    inline_inst_fields (EL (t.vs_inst_idx+k) tb.bb_instructions) =
      inline_inst_fields (EL k focus)
Proof
  strip_tac >> gvs[inline_clone_point_def, rich_listTheory.TAKE_LENGTH_APPEND] >>
  drule_all (SRULE [] inline_call_site_lookup_clone_focus) >>
  disch_then (qspec_then `i` (assume_tac o SRULE [LET_THM])) >>
  drule inline_final_nonphi_getter >> simp[] >>
  disch_then drule >>
  disch_then (qspec_then `t.vs_inst_idx+k` mp_tac) >>
  simp[rich_listTheory.EL_APPEND1, rich_listTheory.EL_APPEND2]
QED

Theorem inline_caller_point_other_getter:
  inline_caller_point caller final lbl i ret N opaque b j s t /\
  final = renumber_fn_inst_ids (fix_inline_phis lbl ret rb
    (inline_call_site p ret caller callee lbl i)) /\
  b <> lbl /\ lookup_block lbl caller.fn_blocks = SOME call_bb /\
  lookup_block b caller.fn_blocks = SOME bb /\
  j < LENGTH bb.bb_instructions /\ (EL j bb.bb_instructions).inst_opcode <> PHI ==>
  ?tb. lookup_block t.vs_current_bb final.fn_blocks = SOME tb /\
    get_instruction tb t.vs_inst_idx = SOME (EL j tb.bb_instructions) /\
    inline_inst_fields (EL j tb.bb_instructions) =
      inline_inst_fields (EL j bb.bb_instructions)
Proof
  strip_tac >> gvs[inline_caller_point_def] >>
  drule_all inline_call_site_lookup_other >>
  disch_then (qspecl_then [`ret`, `p`, `i`, `callee`] assume_tac) >>
  drule inline_final_nonphi_getter >>
  disch_then drule >>
  disch_then (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]
QED

Theorem inline_site_exit_suffix_point:
  inline_caller_data N opaque_caller c d /\
  inline_site_exit N opaque_caller p V opaque outs c d ret ir u v /\
  bind_outputs outs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state c u)) = SOME w /\
  c.vs_current_bb = lbl /\ lookup_block lbl caller.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\ ~MEM ret (fn_labels caller) /\
  final = renumber_fn_inst_ids (fix_inline_phis lbl ret rb
    (inline_call_site p ret caller callee lbl i)) ==>
  inline_caller_point caller final lbl i ret N opaque_caller lbl (SUC i)
    (w with vs_inst_idx := SUC i) (v with vs_inst_idx := 0)
Proof
  strip_tac >>
  `inline_caller_data N opaque_caller w v` by
    metis_tac[inline_site_exit_caller_data] >>
  `v.vs_current_bb = ret` by metis_tac[inline_site_exit_control] >>
  `w.vs_current_bb = lbl` by
    (qpat_x_assum `bind_outputs _ _ _ = SOME w` mp_tac >>
     simp[bind_outputs_def] >>
     Cases_on `ir.iret_adopt_fmp` >>
     simp[adopt_return_fmp_def, merge_callee_state_def, inline_writes_control] >>
     strip_tac >> gvs[inline_writes_control]) >>
  drule_all inline_call_site_lookup_return >>
  disch_then (qspecl_then [`p`, `i`, `callee`] assume_tac) >>
  drule inline_final_lookup_fields >>
  disch_then (qspecl_then [`rb`, `lbl`, `ret`] strip_assume_tac) >>
  drule inline_fields_length >> simp[] >>
  Cases_on `MEM ret (bb_succs rb)` >>
  simp[inline_caller_point_def, LENGTH_MAP] >> metis_tac[]
QED

(* Entry snapshots carry predecessor information separately from instruction
   points.  PHI reads are always from these original snapshots. *)
Definition inline_caller_entry_def:
  inline_caller_entry caller final lbl i ret N opaque (rb:basic_block) b s t <=>
    inline_caller_point caller final lbl i ret N opaque b 0 s t /\
    t.vs_prev_bb = OPTION_MAP (\l. if l = lbl then ret else l) s.vs_prev_bb /\
    (!l. s.vs_prev_bb = SOME l ==> MEM l (fn_labels caller))
End

Definition inline_clone_entry_def:
  inline_clone_entry caller callee final lbl i p ret N opaque_caller opaque
    c d V b s t <=>
    inline_clone_point caller callee final lbl i p ret N opaque_caller opaque
      c d V b 0 0 s t /\
    inline_defined_support V s /\
    t.vs_prev_bb = OPTION_MAP (STRCAT p) s.vs_prev_bb
End

Theorem inline_caller_entry_none:
  inline_caller_point caller final lbl i ret N opaque b 0 s t /\
  s.vs_prev_bb = NONE /\ t.vs_prev_bb = NONE ==>
  inline_caller_entry caller final lbl i ret N opaque rb b s t
Proof
  simp[inline_caller_entry_def]
QED

Theorem inline_clone_entry_none:
  inline_clone_point caller callee final lbl i p ret N opaque_caller opaque
    c d V b 0 0 s t /\ inline_defined_support V s /\
  s.vs_prev_bb = NONE /\ t.vs_prev_bb = NONE ==>
  inline_clone_entry caller callee final lbl i p ret N opaque_caller opaque
    c d V b s t
Proof
  simp[inline_clone_entry_def]
QED

Theorem inline_fields_eval_one_phi[local]:
  inline_inst_fields a = inline_inst_fields b ==>
  eval_one_phi s a = eval_one_phi s b
Proof
  simp[inline_inst_fields_def, eval_one_phi_def] >> metis_tac[]
QED

Theorem inline_fields_eval_phis:
  !xs ys s. MAP inline_inst_fields xs = MAP inline_inst_fields ys ==>
    eval_phis s xs = eval_phis s ys
Proof
  Induct_on `xs` >- (Cases_on `ys` >> simp[]) >>
  Cases_on `ys` >> simp[] >> rpt strip_tac >>
  `h.inst_opcode = h'.inst_opcode` by
    gvs[inline_inst_fields_def] >>
  `eval_one_phi s h = eval_one_phi s h'` by
    metis_tac[inline_fields_eval_one_phi] >>
  `eval_phis s xs = eval_phis s t` by metis_tac[] >>
  simp[eval_phis_def]
QED

Theorem inline_clone_entry_snapshot:
  inline_clone_entry caller callee final lbl i p ret N opaque_caller opaque
    c d V b s t /\
  (!inst prev l. MEM inst insts /\ s.vs_prev_bb = SOME prev /\
    resolve_phi prev inst.inst_operands = SOME (Label l) ==>
    FLOOKUP s.vs_labels l = FLOOKUP t.vs_labels (STRCAT p l)) /\
  (!inst prev y x a. MEM inst insts /\ s.vs_prev_bb = SOME prev /\
    eval_one_phi s inst = SOME (x,a) /\
    resolve_phi prev inst.inst_operands = SOME (Var y) /\ y IN opaque ==>
    x IN opaque) /\
  (!x. x IN inline_phi_outputs insts ==> STRCAT p x NOTIN (N DIFF opaque_caller)) /\
  eval_phis s insts = OK u ==>
  ?v. eval_phis t (MAP (inline_rename_inst (STRCAT p) (STRCAT p)) insts) = OK v /\
    inline_clone_point caller callee final lbl i p ret N opaque_caller opaque
      c d (V UNION inline_phi_outputs insts) b 0 0 u v /\
    inline_defined_support (V UNION inline_phi_outputs insts) u
Proof
  strip_tac >>
  `inline_supported_frame (STRCAT p) V opaque c.vs_vars
    (N DIFF opaque_caller) s t` by
    gvs[inline_clone_entry_def, inline_clone_point_def, inline_supported_frame_def] >>
  drule inline_supported_frame_eval_phis >>
  disch_then (qspecl_then [`u`, `STRCAT p`, `insts`] mp_tac) >>
  simp[] >>
  (impl_tac >- (gvs[inline_clone_entry_def] >> metis_tac[])) >>
  strip_tac >> qexists `t'` >>
  qpat_assum `eval_phis s _ = OK u` (mp_then Any assume_tac eval_phis_only_updates_vs_vars) >>
  qpat_assum `eval_phis t _ = OK t'` (mp_then Any assume_tac eval_phis_only_updates_vs_vars) >>
  gvs[inline_supported_frame_def, inline_clone_entry_def,
      inline_clone_point_def] >>
  qpat_x_assum `u = _ with vs_vars := _` SUBST1_TAC >>
  qpat_x_assum `t' = _ with vs_vars := _` SUBST1_TAC >>
  gvs[inline_target_anchor_def, inline_caller_residual_def,
      inline_caller_bookkeeping_def, merge_callee_state_def, inline_shared_frame_def,
      stateFrameTheory.execution_frame_def]
QED

Theorem inline_rewrite_phi[local]:
  inst.inst_opcode = PHI ==>
  rewrite_inline_inst args outs ret inst n = ([inst],n)
Proof
  simp[rewrite_inline_inst_def, is_param_opcode_def]
QED

Theorem inline_rewrite_nonphi_head:
  inst.inst_opcode <> PHI ==>
  ?h rest. FST (rewrite_inline_inst args outs ret inst n) = h::rest /\
    h.inst_opcode <> PHI
Proof
  strip_tac >> rw[rewrite_inline_inst_def] >> simp[] >>
  Cases_on `FILTER (\op. ~is_label_op op)
    (TAKE (LENGTH inst.inst_operands - 1) inst.inst_operands)` >> simp[]
QED

Theorem inline_rewrite_eval_phis:
  !insts n. eval_phis s (FST (rewrite_inline_insts args outs ret insts n)) =
    eval_phis s insts
Proof
  Induct_on `insts` >- simp[rewrite_inline_insts_def, eval_phis_def] >>
  rpt gen_tac >> Cases_on `h.inst_opcode = PHI`
  >- (simp[rewrite_inline_insts_def, inline_rewrite_phi, pairTheory.UNCURRY, eval_phis_def]) >>
  drule inline_rewrite_nonphi_head >>
  disch_then (qspecl_then [`ret`, `outs`, `n`, `args`] strip_assume_tac) >>
  simp[rewrite_inline_insts_def, pairTheory.UNCURRY, eval_phis_def]
QED

Theorem inline_clone_phi_inst[local]:
  EVERY (\op. !l. op = Label l ==> MEM l labs) inst.inst_operands ==>
  clone_instruction p labs inst = inline_rename_inst (STRCAT p) (STRCAT p) inst
Proof
  strip_tac >> simp[clone_instruction_inline_rename, inline_rename_inst_def] >>
  simp[venomInstTheory.instruction_component_equality] >>
  irule MAP_CONG >> simp[] >>
  rpt strip_tac >> Cases_on `x` >>
  gvs[inline_rename_operand_def, EVERY_MEM] >> metis_tac[]
QED

Theorem inline_clone_eval_phis:
  !insts. EVERY (\inst. inst.inst_opcode = PHI ==>
    EVERY (\op. !l. op = Label l ==> MEM l labs) inst.inst_operands) insts ==>
  eval_phis t (MAP (clone_instruction p labs) insts) =
  eval_phis t (MAP (inline_rename_inst (STRCAT p) (STRCAT p)) insts)
Proof
  Induct_on `insts` >- simp[] >> simp[] >> strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (simp[inline_clone_phi_inst, eval_phis_def, inline_rename_inst_def]) >>
  simp[eval_phis_def, clone_instruction_def, inline_rename_inst_def]
QED

(* Final clone entry layout has no edge repair: the saved caller suffix
   cannot have a callee-internal successor in the separated namespace. *)
Theorem inline_clone_layout_eval_phis:
  lookup_block l raw.fn_blocks = SOME clone_bb /\
  lookup_block l (renumber_fn_inst_ids (fix_inline_phis old fresh rb raw)).fn_blocks = SOME tb /\
  ~MEM clone_bb.bb_label (bb_succs rb) /\
  clone_bb.bb_instructions = FST (rewrite_inline_insts args outs ret
    (MAP (clone_instruction p labs) insts) n) /\
  EVERY (\inst. inst.inst_opcode = PHI ==>
    EVERY (\op. !l. op = Label l ==> MEM l labs) inst.inst_operands) insts ==>
  eval_phis t tb.bb_instructions =
    eval_phis t (MAP (inline_rename_inst (STRCAT p) (STRCAT p)) insts)
Proof
  strip_tac >>
  qpat_assum `lookup_block l raw.fn_blocks = SOME clone_bb`
    (mp_then Any mp_tac inline_final_lookup_fields) >>
  disch_then (qspecl_then [`rb`, `old`, `fresh`] strip_assume_tac) >>
  gvs[] >> drule inline_fields_eval_phis >>
  disch_then (qspec_then `t` mp_tac) >>
  simp[inline_rewrite_eval_phis, inline_clone_eval_phis]
QED

Theorem inline_clone_entry_phis:
  inline_clone_entry caller callee final lbl i p ret N opaque_caller opaque
    c d V b s t /\
  lookup_block b callee.fn_blocks = SOME cb /\
  lookup_block (STRCAT p b) raw.fn_blocks = SOME clone_bb /\
  lookup_block (STRCAT p b) final.fn_blocks = SOME tb /\
  final = renumber_fn_inst_ids (fix_inline_phis lbl ret rb raw) /\
  ~MEM clone_bb.bb_label (bb_succs rb) /\
  clone_bb.bb_instructions = FST (rewrite_inline_insts args outs ret
    (MAP (clone_instruction p (fn_labels callee)) cb.bb_instructions) n) /\
  EVERY (\inst. inst.inst_opcode = PHI ==>
    EVERY (\op. !l. op = Label l ==> MEM l (fn_labels callee)) inst.inst_operands)
    cb.bb_instructions /\
  (!inst prev l. MEM inst cb.bb_instructions /\ s.vs_prev_bb = SOME prev /\
    resolve_phi prev inst.inst_operands = SOME (Label l) ==>
    FLOOKUP s.vs_labels l = FLOOKUP t.vs_labels (STRCAT p l)) /\
  (!inst prev y x a. MEM inst cb.bb_instructions /\ s.vs_prev_bb = SOME prev /\
    eval_one_phi s inst = SOME (x,a) /\
    resolve_phi prev inst.inst_operands = SOME (Var y) /\ y IN opaque ==>
    x IN opaque) /\
  (!x. x IN inline_phi_outputs cb.bb_instructions ==>
    STRCAT p x NOTIN (N DIFF opaque_caller)) /\
  eval_phis s cb.bb_instructions = OK u ==>
  ?v. eval_phis t tb.bb_instructions = OK v /\
    inline_clone_point caller callee final lbl i p ret N opaque_caller opaque
      c d (V UNION inline_phi_outputs cb.bb_instructions) b 0 0 u v /\
    inline_defined_support (V UNION inline_phi_outputs cb.bb_instructions) u
Proof
  strip_tac >>
  `eval_phis t tb.bb_instructions = eval_phis t
     (MAP (inline_rename_inst (STRCAT p) (STRCAT p)) cb.bb_instructions)` by
    (irule inline_clone_layout_eval_phis >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  drule_all inline_clone_entry_snapshot >> metis_tac[]
QED

Theorem inline_caller_data_phi_write:
  inline_caller_data N opaque s t /\ (x NOTIN opaque ==> a = b) ==>
  inline_caller_data N opaque (update_var x a s) (update_var x b t)
Proof
  simp[inline_caller_data_def, inline_caller_bookkeeping_def,
       inline_shared_frame_def, stateFrameTheory.execution_frame_def,
       update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem inline_caller_phis_snapshot:
  !insts s t u.
  inline_caller_data N opaque s t /\
  (!inst x a. MEM inst insts /\ inst.inst_opcode = PHI /\
    eval_one_phi s inst = SOME (x,a) ==>
    ?b. eval_one_phi t inst = SOME (x,b) /\ (x NOTIN opaque ==> b = a)) /\
  eval_phis s insts = OK u ==>
  ?v. eval_phis t insts = OK v /\ inline_caller_data N opaque u v
Proof
  Induct_on `insts` >- simp[eval_phis_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `h.inst_opcode = PHI`
  >- (gvs[eval_phis_def, AllCaseEqs()] >>
      rename1 `eval_phis s insts = OK tail` >>
      `?b. eval_one_phi t h = SOME (out,b) /\ (out NOTIN opaque ==> b = v)` by
        metis_tac[MEM] >>
      `?z. eval_phis t insts = OK z /\ inline_caller_data N opaque tail z` by
        (first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      qexists `update_var out b z` >> simp[eval_phis_def] >>
      irule inline_caller_data_phi_write >> simp[] >> metis_tac[]) >>
  gvs[eval_phis_def] >> metis_tac[]
QED

Theorem inline_caller_eval_one_phi:
  inline_caller_data N opaque s t /\ t.vs_prev_bb = s.vs_prev_bb /\
  (!prev y. s.vs_prev_bb = SOME prev /\
    resolve_phi prev inst.inst_operands = SOME (Var y) ==>
    y IN N /\ (y IN opaque ==> x IN opaque) /\
    (y IN opaque ==> ?z. lookup_var y t = SOME z)) /\
  eval_one_phi s inst = SOME (x,a) ==>
  ?b. eval_one_phi t inst = SOME (x,b) /\ (x NOTIN opaque ==> b = a)
Proof
  simp[eval_one_phi_def, AllCaseEqs()] >> strip_tac >>
  rename1 `resolve_phi prev inst.inst_operands = SOME op` >>
  Cases_on `op` >>
  gvs[eval_operand_def, inline_caller_data_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem inline_caller_eval_phis:
  inline_caller_data N opaque s t /\ t.vs_prev_bb = s.vs_prev_bb /\
  (!inst x a prev y. MEM inst insts /\ inst.inst_opcode = PHI /\
    eval_one_phi s inst = SOME (x,a) /\ s.vs_prev_bb = SOME prev /\
    resolve_phi prev inst.inst_operands = SOME (Var y) ==>
    y IN N /\ (y IN opaque ==> x IN opaque) /\
    (y IN opaque ==> ?z. lookup_var y t = SOME z)) /\
  eval_phis s insts = OK u ==>
  ?v. eval_phis t insts = OK v /\ inline_caller_data N opaque u v
Proof
  strip_tac >> irule inline_caller_phis_snapshot >>
  goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >> irule inline_caller_eval_one_phi >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem inline_caller_data_prev[simp]:
  inline_caller_data N opaque (s with vs_prev_bb := a) (t with vs_prev_bb := b) =
    inline_caller_data N opaque s t
Proof
  simp[inline_caller_data_def, inline_caller_bookkeeping_def,
       inline_shared_frame_def, stateFrameTheory.execution_frame_def, lookup_var_def]
QED

Theorem inline_caller_repaired_phis:
  inline_caller_data N opaque s t /\
  t.vs_prev_bb = OPTION_MAP (\l. if l = old then fresh else l) s.vs_prev_bb /\
  inliner_phi_labels_closed fn /\ fn_inst_wf fn /\ MEM bb fn.fn_blocks /\
  ~MEM fresh (fn_labels fn) /\
  (!l. s.vs_prev_bb = SOME l ==> MEM l (fn_labels fn)) /\
  (!inst x a prev y. MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
    eval_one_phi s inst = SOME (x,a) /\ s.vs_prev_bb = SOME prev /\
    resolve_phi prev inst.inst_operands = SOME (Var y) ==>
    y IN N /\ (y IN opaque ==> x IN opaque) /\
    (y IN opaque ==> ?z. lookup_var y t = SOME z)) /\
  eval_phis s bb.bb_instructions = OK u ==>
  ?v. eval_phis t
      (MAP (\inst. if inst.inst_opcode <> PHI then inst
                   else subst_label_inst old fresh inst) bb.bb_instructions) = OK v /\
    inline_caller_data N opaque u v
Proof
  strip_tac >>
  qabbrev_tac `t0 = t with vs_prev_bb := s.vs_prev_bb` >>
  `?v0. eval_phis t0 bb.bb_instructions = OK v0 /\ inline_caller_data N opaque u v0` by
    (irule inline_caller_eval_phis >> goal_assum (drule_at Any) >>
     gvs[Abbr `t0`, inline_caller_data_def, inline_caller_bookkeeping_def,
         inline_shared_frame_def, stateFrameTheory.execution_frame_def, lookup_var_def] >>
     metis_tac[]) >>
  drule_all inline_eval_phis_optional_repair >>
  disch_then (qspecl_then [`t0`, `old`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists `v0 with vs_prev_bb := t.vs_prev_bb` >>
  `t with vs_prev_bb := OPTION_MAP (\l. if l = old then fresh else l) s.vs_prev_bb = t` by
    metis_tac[venom_state_fupdselfid] >>
  gvs[Abbr `t0`, inline_caller_data_def, inline_caller_bookkeeping_def,
      inline_shared_frame_def, stateFrameTheory.execution_frame_def, lookup_var_def]
QED

Theorem inline_eval_phis_split_prefix:
  !i insts. i < LENGTH insts /\ (EL i insts).inst_opcode <> PHI /\
    next.inst_opcode <> PHI ==>
    eval_phis s (TAKE i insts ++ [next]) = eval_phis s insts
Proof
  Induct_on `i`
  >- (Cases_on `insts` >> simp[eval_phis_def]) >>
  Cases_on `insts` >> simp[] >> strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[eval_phis_def]
QED

Theorem inline_eval_phis_repaired_split:
  i < LENGTH insts /\ (EL i insts).inst_opcode = INVOKE /\
  next.inst_opcode <> PHI ==>
  eval_phis s
    (MAP (\inst. if inst.inst_opcode <> PHI then inst
                 else subst_label_inst old fresh inst) (TAKE i insts ++ [next])) =
  eval_phis s
    (MAP (\inst. if inst.inst_opcode <> PHI then inst
                 else subst_label_inst old fresh inst) insts)
Proof
  strip_tac >> simp[MAP_APPEND, MAP_TAKE] >>
  irule inline_eval_phis_split_prefix >>
  simp[EL_MAP, cfgTransformTheory.subst_label_inst_def]
QED

Theorem inline_caller_layout_eval_phis:
  lookup_block lbl caller.fn_blocks = SOME call_bb /\
  lookup_block b caller.fn_blocks = SOME bb /\
  lookup_block b final.fn_blocks = SOME tb /\
  final = renumber_fn_inst_ids (fix_inline_phis lbl ret rb
    (inline_call_site p ret caller callee lbl i)) /\
  i < LENGTH call_bb.bb_instructions /\
  (EL i call_bb.bb_instructions).inst_opcode = INVOKE ==>
  eval_phis t tb.bb_instructions =
    eval_phis t (if MEM b (bb_succs rb) then
      MAP (\inst. if inst.inst_opcode <> PHI then inst
                  else subst_label_inst lbl ret inst) bb.bb_instructions
      else bb.bb_instructions)
Proof
  strip_tac >>
  `bb.bb_label = b` by
    (qpat_x_assum `lookup_block b caller.fn_blocks = SOME bb` mp_tac >>
     simp[lookup_block_def] >> strip_tac >>
     drule venomExecProofsTheory.FIND_P >> simp[]) >>
  Cases_on `b = lbl`
  >- (gvs[] >>
      qpat_assum `lookup_block b caller.fn_blocks = SOME bb`
        (mp_then Any mp_tac inline_call_site_lookup_call) >>
      disch_then (qspecl_then [`ret`, `p`, `i`, `callee`] assume_tac) >>
      qpat_assum `lookup_block b (inline_call_site _ _ _ _ _ _).fn_blocks = SOME _`
        (mp_then Any mp_tac inline_final_lookup_fields) >>
      disch_then (qspecl_then [`rb`, `bb.bb_label`, `ret`] strip_assume_tac) >>
      gvs[] >> drule inline_fields_eval_phis >>
      disch_then (qspec_then `t` mp_tac) >>
      Cases_on `MEM bb.bb_label (bb_succs rb)` >>
      simp[] >> strip_tac >>
      rewrite_tac[MAP_TAKE] >>
      irule inline_eval_phis_split_prefix >>
      simp[EL_MAP, cfgTransformTheory.subst_label_inst_def]) >>
  qpat_assum `lookup_block lbl caller.fn_blocks = SOME call_bb`
    (mp_then Any mp_tac inline_call_site_lookup_other) >>
  disch_then (qspecl_then [`ret`, `p`, `bb`, `b`, `i`, `callee`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_assum `lookup_block b (inline_call_site _ _ _ _ _ _).fn_blocks = SOME _`
    (mp_then Any mp_tac inline_final_lookup_fields) >>
  disch_then (qspecl_then [`rb`, `lbl`, `ret`] strip_assume_tac) >>
  gvs[] >> drule inline_fields_eval_phis >>
  disch_then (qspec_then `t` mp_tac) >> simp[]
QED

Theorem inline_caller_entry_phis:
  inline_caller_entry caller final lbl i ret N opaque rb b s t /\
  lookup_block lbl caller.fn_blocks = SOME call_bb /\
  lookup_block b caller.fn_blocks = SOME bb /\
  lookup_block b final.fn_blocks = SOME tb /\
  final = renumber_fn_inst_ids (fix_inline_phis lbl ret rb
    (inline_call_site p ret caller callee lbl i)) /\
  i < LENGTH call_bb.bb_instructions /\
  (EL i call_bb.bb_instructions).inst_opcode = INVOKE /\
  inliner_phi_labels_closed caller /\ fn_inst_wf caller /\
  ~MEM ret (fn_labels caller) /\
  (s.vs_prev_bb = SOME lbl ==> MEM b (bb_succs rb)) /\
  (!inst x a prev y. MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
    eval_one_phi s inst = SOME (x,a) /\ s.vs_prev_bb = SOME prev /\
    resolve_phi prev inst.inst_operands = SOME (Var y) ==>
    y IN N /\ (y IN opaque ==> x IN opaque) /\
    (y IN opaque ==> ?z. lookup_var y t = SOME z)) /\
  eval_phis s bb.bb_instructions = OK u ==>
  ?v. eval_phis t tb.bb_instructions = OK v /\
    inline_caller_point caller final lbl i ret N opaque b 0 u v
Proof
  strip_tac >>
  `eval_phis t tb.bb_instructions = eval_phis t
    (if MEM b (bb_succs rb) then
       MAP (\inst. if inst.inst_opcode <> PHI then inst
                    else subst_label_inst lbl ret inst) bb.bb_instructions
     else bb.bb_instructions)` by
    (irule inline_caller_layout_eval_phis >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  `?v. eval_phis t tb.bb_instructions = OK v /\ inline_caller_data N opaque u v` by
    (Cases_on `MEM b (bb_succs rb)`
     >- (fs[] >> irule inline_caller_repaired_phis >>
         goal_assum (drule_at Any) >>
         gvs[inline_caller_entry_def, inline_caller_point_def] >>
         qpat_assum `lookup_block _ caller.fn_blocks = SOME bb`
           (mp_then Any assume_tac phiTransformTheory.lookup_block_MEM) >>
         qexists `caller` >> simp[] >> metis_tac[]) >>
     `t.vs_prev_bb = s.vs_prev_bb` by
       (gvs[inline_caller_entry_def] >> Cases_on `s.vs_prev_bb` >> gvs[] >>
        IF_CASES_TAC >> gvs[]) >>
     fs[] >> irule inline_caller_eval_phis >>
     goal_assum (drule_at Any) >>
     gvs[inline_caller_entry_def, inline_caller_point_def] >> metis_tac[]) >>
  qexists `v` >> simp[] >>
  qpat_assum `eval_phis s _ = OK u`
    (mp_then Any assume_tac eval_phis_only_updates_vs_vars) >>
  qpat_assum `eval_phis t _ = OK v`
    (mp_then Any assume_tac eval_phis_only_updates_vs_vars) >>
  gvs[inline_caller_entry_def, inline_caller_point_def] >>
  qpat_x_assum `u = _ with vs_vars := _` SUBST1_TAC >>
  qpat_x_assum `v = _ with vs_vars := _` SUBST1_TAC >> simp[] >> metis_tac[]
QED

Theorem inline_phi_selected_output:
  eval_one_phi s inst = SOME (x,a) ==> MEM x inst.inst_outputs
Proof
  simp[eval_one_phi_def, AllCaseEqs()] >> rpt strip_tac >> simp[]
QED

Theorem inline_phi_selected_read:
  eval_one_phi s inst = SOME (x,a) /\ s.vs_prev_bb = SOME prev /\
  resolve_phi prev inst.inst_operands = SOME (Var y) ==>
  lookup_var y s = SOME a
Proof
  simp[eval_one_phi_def, AllCaseEqs(), eval_operand_def] >>
  rpt strip_tac >> gvs[venomStateTheory.eval_operand_def]
QED

Theorem inline_phi_selected_static:
  inline_opacity_ok fn opaque /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = PHI /\
  (!ins y. MEM ins (fn_insts fn) /\ MEM (Var y) ins.inst_operands ==> y IN N) /\
  eval_one_phi s inst = SOME (x,a) /\ s.vs_prev_bb = SOME prev /\
  resolve_phi prev inst.inst_operands = SOME (Var y) ==>
  y IN N /\ (y IN opaque ==> x IN opaque)
Proof
  strip_tac >>
  `MEM (Var y) inst.inst_operands` by
    (drule execEquivParamBaseTheory.resolve_phi_MEM >> simp[]) >>
  `MEM x inst.inst_outputs` by metis_tac[inline_phi_selected_output] >>
  metis_tac[inline_opacity_phi]
QED

Theorem inline_phi_block_static:
  inline_opacity_ok fn opaque /\ MEM bb fn.fn_blocks /\
  (!ins y. MEM ins (fn_insts fn) /\ MEM (Var y) ins.inst_operands ==> y IN N) ==>
  !inst x a prev y. MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
    eval_one_phi s inst = SOME (x,a) /\ s.vs_prev_bb = SOME prev /\
    resolve_phi prev inst.inst_operands = SOME (Var y) ==>
    y IN N /\ (y IN opaque ==> x IN opaque)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  irule inline_phi_selected_static >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Definition inline_opaque_available_def:
  inline_opaque_available opaque s t <=>
    !x a. x IN opaque /\ lookup_var x s = SOME a ==>
      ?b. lookup_var x t = SOME b
End

Theorem inline_opaque_available_refl[simp]:
  inline_opaque_available opaque s s
Proof
  simp[inline_opaque_available_def]
QED

Theorem inline_opaque_available_control[simp]:
  inline_opaque_available opaque (s with vs_prev_bb := a) (t with vs_prev_bb := b) =
    inline_opaque_available opaque s t /\
  inline_opaque_available opaque (s with vs_inst_idx := i) (t with vs_inst_idx := j) =
    inline_opaque_available opaque s t /\
  inline_opaque_available opaque (jump_to l s) (jump_to k t) =
    inline_opaque_available opaque s t
Proof
  simp[inline_opaque_available_def, lookup_var_def, jump_to_def]
QED

Theorem inline_opaque_available_write:
  inline_opaque_available opaque s t ==>
  inline_opaque_available opaque (update_var x a s) (update_var x b t)
Proof
  simp[inline_opaque_available_def, lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `x' = x` >> gvs[] >> metis_tac[]
QED

Theorem inline_caller_available_snapshot:
  !insts s t u.
  inline_caller_data N opaque s t /\ inline_opaque_available opaque s t /\
  (!inst x a. MEM inst insts /\ inst.inst_opcode = PHI /\
    eval_one_phi s inst = SOME (x,a) ==>
    ?b. eval_one_phi t inst = SOME (x,b) /\ (x NOTIN opaque ==> b = a)) /\
  eval_phis s insts = OK u ==>
  ?v. eval_phis t insts = OK v /\ inline_caller_data N opaque u v /\
    inline_opaque_available opaque u v
Proof
  Induct_on `insts` >- simp[eval_phis_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `h.inst_opcode = PHI`
  >- (gvs[eval_phis_def, AllCaseEqs()] >>
      rename1 `eval_phis s insts = OK tail` >>
      `?b. eval_one_phi t h = SOME (out,b) /\ (out NOTIN opaque ==> b = v)` by
        metis_tac[MEM] >>
      `?z. eval_phis t insts = OK z /\ inline_caller_data N opaque tail z /\
           inline_opaque_available opaque tail z` by
        (first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      qexists `update_var out b z` >> simp[eval_phis_def] >>
      conj_tac >- (irule inline_caller_data_phi_write >> simp[] >> metis_tac[]) >>
      irule inline_opaque_available_write >> simp[]) >>
  gvs[eval_phis_def] >> metis_tac[]
QED

Theorem inline_caller_available_phis:
  inline_caller_data N opaque s t /\ inline_opaque_available opaque s t /\
  t.vs_prev_bb = s.vs_prev_bb /\ inline_opacity_ok fn opaque /\
  MEM bb fn.fn_blocks /\
  (!ins y. MEM ins (fn_insts fn) /\ MEM (Var y) ins.inst_operands ==> y IN N) /\
  eval_phis s bb.bb_instructions = OK u ==>
  ?v. eval_phis t bb.bb_instructions = OK v /\ inline_caller_data N opaque u v /\
    inline_opaque_available opaque u v
Proof
  strip_tac >> irule inline_caller_available_snapshot >>
  goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
  irule inline_caller_eval_one_phi >> goal_assum (drule_at Any) >> simp[] >>
  qexists `N` >> simp[] >> rpt strip_tac >>
  `y IN N /\ (y IN opaque ==> x IN opaque)` by
    (drule_all inline_phi_block_static >> metis_tac[]) >> simp[] >>
  `lookup_var y s = SOME a` by metis_tac[inline_phi_selected_read] >>
  gvs[inline_opaque_available_def] >> metis_tac[]
QED

Theorem inline_caller_available_repaired_phis:
  inline_caller_data N opaque s t /\ inline_opaque_available opaque s t /\
  t.vs_prev_bb = OPTION_MAP (\l. if l = old then fresh else l) s.vs_prev_bb /\
  inline_opacity_ok fn opaque /\ inliner_phi_labels_closed fn /\ fn_inst_wf fn /\
  MEM bb fn.fn_blocks /\ ~MEM fresh (fn_labels fn) /\
  (!l. s.vs_prev_bb = SOME l ==> MEM l (fn_labels fn)) /\
  (!ins y. MEM ins (fn_insts fn) /\ MEM (Var y) ins.inst_operands ==> y IN N) /\
  eval_phis s bb.bb_instructions = OK u ==>
  ?v. eval_phis t
      (MAP (\inst. if inst.inst_opcode <> PHI then inst
                   else subst_label_inst old fresh inst) bb.bb_instructions) = OK v /\
    inline_caller_data N opaque u v /\ inline_opaque_available opaque u v
Proof
  strip_tac >> qabbrev_tac `t0 = t with vs_prev_bb := s.vs_prev_bb` >>
  `?v0. eval_phis t0 bb.bb_instructions = OK v0 /\
        inline_caller_data N opaque u v0 /\ inline_opaque_available opaque u v0` by
    (irule inline_caller_available_phis >> conj_tac
     >- (qexists `fn` >> simp[] >> gvs[]) >>
     qexists `s` >>
     gvs[Abbr `t0`, inline_caller_data_def, inline_caller_bookkeeping_def,
         inline_shared_frame_def, stateFrameTheory.execution_frame_def, lookup_var_def,
         inline_opaque_available_def]) >>
  drule_all inline_eval_phis_optional_repair >>
  disch_then (qspecl_then [`t0`, `old`] mp_tac) >> simp[] >> strip_tac >>
  qexists `v0 with vs_prev_bb := t.vs_prev_bb` >>
  `t with vs_prev_bb := OPTION_MAP (\l. if l = old then fresh else l) s.vs_prev_bb = t` by
    metis_tac[venom_state_fupdselfid] >>
  gvs[Abbr `t0`, inline_caller_data_def, inline_caller_bookkeeping_def,
      inline_shared_frame_def, stateFrameTheory.execution_frame_def, lookup_var_def,
      inline_opaque_available_def]
QED

Theorem inline_caller_available_entry_phis:
  inline_caller_entry caller final lbl i ret N opaque rb b s t /\
  inline_opaque_available opaque s t /\
  lookup_block lbl caller.fn_blocks = SOME call_bb /\
  lookup_block b caller.fn_blocks = SOME bb /\
  lookup_block b final.fn_blocks = SOME tb /\
  final = renumber_fn_inst_ids (fix_inline_phis lbl ret rb
    (inline_call_site p ret caller callee lbl i)) /\
  i < LENGTH call_bb.bb_instructions /\
  (EL i call_bb.bb_instructions).inst_opcode = INVOKE /\
  inline_opacity_ok caller opaque /\
  inliner_phi_labels_closed caller /\ fn_inst_wf caller /\
  ~MEM ret (fn_labels caller) /\
  (s.vs_prev_bb = SOME lbl ==> MEM b (bb_succs rb)) /\
  (!ins y. MEM ins (fn_insts caller) /\ MEM (Var y) ins.inst_operands ==> y IN N) /\
  eval_phis s bb.bb_instructions = OK u ==>
  ?v. eval_phis t tb.bb_instructions = OK v /\
    inline_caller_point caller final lbl i ret N opaque b 0 u v /\
    inline_opaque_available opaque u v
Proof
  strip_tac >>
  `eval_phis t tb.bb_instructions = eval_phis t
    (if MEM b (bb_succs rb) then
       MAP (\inst. if inst.inst_opcode <> PHI then inst
                    else subst_label_inst lbl ret inst) bb.bb_instructions
     else bb.bb_instructions)` by
    (irule inline_caller_layout_eval_phis >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  `MEM bb caller.fn_blocks` by metis_tac[phiTransformTheory.lookup_block_MEM] >>
  `?v. eval_phis t tb.bb_instructions = OK v /\ inline_caller_data N opaque u v /\
       inline_opaque_available opaque u v` by
    (Cases_on `MEM b (bb_succs rb)`
     >- (fs[] >> irule inline_caller_available_repaired_phis >>
         qexistsl [`caller`, `s`] >>
         gvs[inline_caller_entry_def, inline_caller_point_def] >> gvs[]) >>
     `t.vs_prev_bb = s.vs_prev_bb` by
       (gvs[inline_caller_entry_def] >> Cases_on `s.vs_prev_bb` >> gvs[] >>
        IF_CASES_TAC >> gvs[]) >>
     fs[] >> irule inline_caller_available_phis >>
     conj_tac >- (qexists `caller` >> simp[] >> gvs[]) >>
     qexists `s` >> gvs[inline_caller_entry_def, inline_caller_point_def]) >>
  qexists `v` >> simp[] >>
  qpat_assum `eval_phis s _ = OK u`
    (mp_then Any assume_tac eval_phis_only_updates_vs_vars) >>
  qpat_assum `eval_phis t _ = OK v`
    (mp_then Any assume_tac eval_phis_only_updates_vs_vars) >>
  gvs[inline_caller_entry_def, inline_caller_point_def] >>
  qpat_x_assum `u = _ with vs_vars := _` SUBST1_TAC >>
  qpat_x_assum `v = _ with vs_vars := _` SUBST1_TAC >> simp[] >> metis_tac[]
QED

Theorem inline_opaque_available_fdom:
  inline_opaque_available opaque s t <=>
    opaque INTER FDOM s.vs_vars SUBSET FDOM t.vs_vars
Proof
  simp[inline_opaque_available_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]
QED

Theorem inline_opaque_available_bind:
  inline_opaque_available opaque s t /\
  bind_outputs outs vals s = SOME u /\
  bind_outputs outs vals' t = SOME v ==>
  inline_opaque_available opaque u v
Proof
  strip_tac >>
  qpat_assum `bind_outputs outs vals s = SOME u`
    (mp_then Any assume_tac bind_outputs_fdom) >>
  qpat_assum `bind_outputs outs vals' t = SOME v`
    (mp_then Any assume_tac bind_outputs_fdom) >>
  gvs[inline_opaque_available_fdom] >> ASM_SET_TAC[]
QED

Theorem inline_opaque_available_merge_adopt[simp]:
  inline_opaque_available opaque
    (adopt_return_fmp ir (merge_callee_state s u))
    (adopt_return_fmp jr (merge_callee_state t v)) =
  inline_opaque_available opaque s t
Proof
  Cases_on `ir.iret_adopt_fmp` >> Cases_on `jr.iret_adopt_fmp` >>
  simp[inline_opaque_available_def, lookup_var_def, adopt_return_fmp_def,
       merge_callee_state_def]
QED

Theorem inline_opaque_available_step:
  inline_opaque_available opaque s t /\ inst_wf inst /\
  step_inst f ctx inst s = OK u /\ step_inst g ctx' inst t = OK v ==>
  inline_opaque_available opaque u v
Proof
  strip_tac >> Cases_on `is_terminator inst.inst_opcode`
  >- (imp_res_tac step_terminator_preserves_vars >>
      gvs[inline_opaque_available_def] >> metis_tac[]) >>
  `inst.inst_opcode <> PHI` by metis_tac[step_inst_ok_imp_not_phi] >>
  `FDOM u.vs_vars = FDOM s.vs_vars UNION set inst.inst_outputs` by
    metis_tac[step_inst_fdom] >>
  `FDOM v.vs_vars = FDOM t.vs_vars UNION set inst.inst_outputs` by
    metis_tac[step_inst_fdom] >>
  gvs[inline_opaque_available_fdom] >> ASM_SET_TAC[]
QED

Theorem inline_merge_adopt_lookup[simp]:
  lookup_var x (adopt_return_fmp ir (merge_callee_state s u)) = lookup_var x s
Proof
  Cases_on `ir.iret_adopt_fmp` >>
  simp[lookup_var_def, adopt_return_fmp_def, merge_callee_state_def]
QED

Theorem inline_opaque_available_call_bind:
  inline_opaque_available opaque s t /\
  bind_outputs outs ir.iret_values (adopt_return_fmp ir (merge_callee_state s u)) = SOME s' /\
  bind_outputs outs jr.iret_values (adopt_return_fmp jr (merge_callee_state t v)) = SOME t' ==>
  inline_opaque_available opaque s' t'
Proof
  strip_tac >> irule inline_opaque_available_bind >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

Theorem inline_opaque_available_return:
  inline_opaque_available opaque c d /\
  (!x. x IN opaque ==> lookup_var x v = lookup_var x d) /\
  (!x. MEM x outs ==> x NOTIN opaque) /\
  bind_outputs outs ir.iret_values (adopt_return_fmp ir (merge_callee_state c u)) = SOME w ==>
  inline_opaque_available opaque w v
Proof
  strip_tac >> drule bind_outputs_fdom >>
  Cases_on `ir.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def, merge_callee_state_def] >> strip_tac >>
  gvs[inline_opaque_available_fdom, SUBSET_DEF] >>
  rpt strip_tac >> irule lookup_var_fdom >> qexists `d` >> simp[] >> metis_tac[]
QED

(* Output-only framing deliberately imposes no restriction on parameter reads:
   arguments may read an opaque caller token without writing it. *)
Theorem inline_rewrite_outputs_disjoint:
  !inst args outs ret pi ri P.
    EVERY (\x. x NOTIN P) inst.inst_outputs /\
    EVERY (\x. x NOTIN P) outs /\
    ((inst.inst_opcode = RET \/ inst.inst_opcode = RETFMP) ==>
      raw_return_user_arity inst = SOME (LENGTH outs)) /\
    MEM ri (FST (rewrite_inline_inst args outs ret inst pi)) ==>
    EVERY (\x. x NOTIN P) ri.inst_outputs
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `is_param_opcode inst.inst_opcode`
  >- gvs[rewrite_inline_inst_def, SF boolSimps.COND_elim_ss] >>
  Cases_on `inst.inst_opcode = RET \/ inst.inst_opcode = RETFMP`
  >- (simp[EVERY_MEM] >> rpt strip_tac >>
      `MEM x outs` by
        (irule functionInlinerReturnBoundaryTheory.inline_return_static_write_boundary >>
         goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      gvs[EVERY_MEM]) >>
  gvs[rewrite_inline_inst_def]
QED

Theorem inline_rewrite_insts_outputs_disjoint:
  !insts args outs ret pi ris pi' P.
    EVERY (\inst. EVERY (\x. x NOTIN P) inst.inst_outputs) insts /\
    EVERY (\x. x NOTIN P) outs /\
    (!inst. MEM inst insts /\
      (inst.inst_opcode = RET \/ inst.inst_opcode = RETFMP) ==>
      raw_return_user_arity inst = SOME (LENGTH outs)) /\
    rewrite_inline_insts args outs ret insts pi = (ris,pi') ==>
    EVERY (\inst. EVERY (\x. x NOTIN P) inst.inst_outputs) ris
Proof
  Induct >> simp[rewrite_inline_insts_def] >> rpt gen_tac >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  conj_tac
  >- (pure_once_rewrite_tac[EVERY_MEM] >> gen_tac >> disch_tac >> BETA_TAC >>
      irule inline_rewrite_outputs_disjoint >> metis_tac[pairTheory.FST]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem inline_rewrite_blocks_outputs_disjoint:
  !bbs args outs ret pi bbs' pi' P.
    EVERY (\bb. EVERY (\inst. EVERY (\x. x NOTIN P) inst.inst_outputs)
      bb.bb_instructions) bbs /\
    EVERY (\x. x NOTIN P) outs /\
    (!bb inst. MEM bb bbs /\ MEM inst bb.bb_instructions /\
      (inst.inst_opcode = RET \/ inst.inst_opcode = RETFMP) ==>
      raw_return_user_arity inst = SOME (LENGTH outs)) /\
    rewrite_inline_blocks args outs ret bbs pi = (bbs',pi') ==>
    EVERY (\bb. EVERY (\inst. EVERY (\x. x NOTIN P) inst.inst_outputs)
      bb.bb_instructions) bbs'
Proof
  Induct >> simp[rewrite_inline_blocks_def] >> rpt gen_tac >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  conj_tac
  >- (qpat_x_assum `rewrite_inline_block _ _ _ _ _ = _` mp_tac >>
      simp[rewrite_inline_block_def] >> pairarg_tac >> simp[] >>
      strip_tac >> gvs[] >> irule inline_rewrite_insts_outputs_disjoint >>
      metis_tac[]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem inline_clone_outputs_disjoint:
  (!x. STRCAT p x NOTIN P) ==>
  EVERY (\bb. EVERY (\inst. EVERY (\x. x NOTIN P) inst.inst_outputs)
    bb.bb_instructions) (clone_function p callee).fn_blocks
Proof
  simp[clone_function_def, clone_basic_block_def, clone_instruction_def,
       EVERY_MAP, EVERY_MEM, MEM_MAP] >> rpt strip_tac >> gvs[] >>
  gvs[clone_basic_block_def, MEM_MAP, clone_instruction_def]
QED

Theorem inline_clone_rewrite_outputs_disjoint:
  !p P outs callee args ret pi bbs pi'.
  (!x. STRCAT p x NOTIN P) /\ EVERY (\x. x NOTIN P) outs /\
  (!r. MEM r (fn_insts callee) /\
    (r.inst_opcode = RET \/ r.inst_opcode = RETFMP) ==>
    raw_return_user_arity r = SOME (LENGTH outs)) /\
  rewrite_inline_blocks args outs ret (clone_function p callee).fn_blocks pi = (bbs,pi') ==>
  EVERY (\bb. EVERY (\inst. EVERY (\x. x NOTIN P) inst.inst_outputs)
    bb.bb_instructions) bbs
Proof
  rpt gen_tac >> strip_tac >> irule inline_rewrite_blocks_outputs_disjoint >>
  goal_assum (drule_at Any) >> simp[inline_clone_outputs_disjoint] >>
  metis_tac[functionInlinerNamespaceTheory.clone_blocks_return_arity]
QED

Theorem inline_protected_exec_block:
  exec_block fuel ctx bb t = OK v /\
  EVERY (\inst. EVERY (\x. x NOTIN P) inst.inst_outputs) bb.bb_instructions /\
  (!x. x IN P ==> lookup_var x t = lookup_var x d) ==>
  !x. x IN P ==> lookup_var x v = lookup_var x d
Proof
  strip_tac >> gen_tac >> strip_tac >>
  `~MEM x (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))` by
    (gvs[EVERY_MEM, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  metis_tac[exec_block_preserves_non_output_vars]
QED

Theorem inline_qualified_clone_outputs_disjoint:
  !ctx0 n caller callee opaque call args ret pi bbs pi'.
  qualified_origin ctx0 n caller /\ qualified_origin ctx0 n callee /\
  opaque SUBSET set (cfgTransform$fn_all_vars caller) /\
  inline_opacity_ok caller opaque /\ MEM call (fn_insts caller) /\
  call.inst_opcode = INVOKE /\ call.inst_operands = Label callee.fn_name::args /\
  rewrite_inline_blocks (rotate_invoke_ops call.inst_operands) call.inst_outputs ret
    (clone_function (inline_prefix n) callee).fn_blocks pi = (bbs,pi') ==>
  EVERY (\bb. EVERY (\inst. EVERY (\x. x NOTIN opaque) inst.inst_outputs)
      bb.bb_instructions) bbs
Proof
  rpt gen_tac >> strip_tac >>
  (`!z. STRCAT (inline_prefix n) z NOTIN opaque` by
       (qpat_assum `qualified_origin ctx0 n caller`
          (mp_then Any mp_tac functionInlinerNamespaceTheory.qualified_origin_clone_disjoint) >>
        gvs[SUBSET_DEF] >> metis_tac[]) >>
     `EVERY (\z. z NOTIN opaque) call.inst_outputs` by
       (simp[EVERY_MEM] >> metis_tac[inline_opacity_invoke_output]) >>
     `!r. MEM r (fn_insts callee) /\
         (r.inst_opcode = RET \/ r.inst_opcode = RETFMP) ==>
         raw_return_user_arity r = SOME (LENGTH call.inst_outputs)` by
       (rpt strip_tac >>
        irule functionInlinerOriginTheory.qualified_origin_call_return_arity >>
        goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
     irule inline_clone_rewrite_outputs_disjoint >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[])
QED

Theorem inline_site_exit_caller_available:
  inline_caller_data N opaque_caller c d /\
  inline_opaque_available opaque_caller c d /\
  inline_site_exit N opaque_caller p V opaque outs c d ret ir u v /\
  (!x. x IN opaque_caller ==> lookup_var x v = lookup_var x d) /\
  (!x. MEM x outs ==> x NOTIN opaque_caller) /\
  bind_outputs outs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state c u)) = SOME w ==>
  inline_caller_data N opaque_caller w v /\
  inline_opaque_available opaque_caller w v
Proof
  strip_tac >> conj_tac
  >- (irule inline_site_exit_caller_data >> metis_tac[]) >>
  irule inline_opaque_available_return >> metis_tac[]
QED

Theorem inline_protected_phis:
  !insts t v P.
  EVERY (\inst. EVERY (\x. x NOTIN P) inst.inst_outputs) insts /\
  eval_phis t insts = OK v ==>
  !x. x IN P ==> lookup_var x v = lookup_var x t
Proof
  Induct >> simp[eval_phis_def] >> rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >> strip_tac >>
  gvs[AllCaseEqs()] >> rpt strip_tac >>
  rename1 `eval_one_phi t h = SOME (out,a)` >>
  `MEM out h.inst_outputs` by metis_tac[inline_phi_selected_output] >>
  gvs[EVERY_MEM, lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem inline_protected_run_block:
  run_block fuel ctx bb t = OK v /\
  EVERY (\inst. EVERY (\x. x NOTIN P) inst.inst_outputs) bb.bb_instructions /\
  (!x. x IN P ==> lookup_var x t = lookup_var x d) ==>
  !x. x IN P ==> lookup_var x v = lookup_var x d
Proof
  strip_tac >>
  qspecl_then [`t`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs >>
  gvs[run_block_def] >> gen_tac >> strip_tac >>
  irule inline_protected_exec_block >> qexists `P` >>
  goal_assum (drule_at (Pat `exec_block _ _ _ _ = _`)) >>
  simp[lookup_var_def] >>
  metis_tac[inline_protected_phis, lookup_var_def]
QED

(* Producer, not a target-prefix assumption: both retained and split caller
   blocks are fetched from the actual final one-edit assembly. *)
Theorem inline_caller_produced_phis:
  lookup_block lbl caller.fn_blocks = SOME call_bb /\
  lookup_block b caller.fn_blocks = SOME bb /\
  i < LENGTH call_bb.bb_instructions /\
  (EL i call_bb.bb_instructions).inst_opcode = INVOKE ==>
  ?tb. lookup_block b
      (renumber_fn_inst_ids (fix_inline_phis lbl ret rb
        (inline_call_site p ret caller callee lbl i))).fn_blocks = SOME tb /\
    eval_phis t tb.bb_instructions =
      eval_phis t (if MEM b (bb_succs rb) then
        MAP (\inst. if inst.inst_opcode <> PHI then inst
                    else subst_label_inst lbl ret inst) bb.bb_instructions
        else bb.bb_instructions)
Proof
  strip_tac >>
  `?raw_bb. lookup_block b
      (inline_call_site p ret caller callee lbl i).fn_blocks = SOME raw_bb` by
    (Cases_on `b = lbl` >> gvs[]
     >- metis_tac[inline_call_site_lookup_call] >>
     metis_tac[inline_call_site_lookup_other]) >>
  drule inline_final_lookup_fields >>
  disch_then (qspecl_then [`rb`, `lbl`, `ret`] strip_assume_tac) >>
  qexists `tb` >> simp[] >>
  irule inline_caller_layout_eval_phis >> simp[] >> metis_tac[]
QED

Theorem inline_clone_produced_phis:
  lookup_block lbl caller.fn_blocks = SOME call_bb /\
  lookup_block b callee.fn_blocks = SOME cb /\
  ~MEM (STRCAT p b) (fn_labels caller) /\ STRCAT p b <> ret /\
  (!l. MEM l (bb_succs rb) ==> MEM l (fn_labels caller)) /\
  inliner_phi_labels_closed callee ==>
  ?tb. lookup_block (STRCAT p b)
      (renumber_fn_inst_ids (fix_inline_phis lbl ret rb
        (inline_call_site p ret caller callee lbl i))).fn_blocks = SOME tb /\
    eval_phis t tb.bb_instructions =
      eval_phis t (MAP (inline_rename_inst (STRCAT p) (STRCAT p))
        cb.bb_instructions)
Proof
  strip_tac >>
  drule_all inline_call_site_lookup_clone >>
  disch_then (qspec_then `i` assume_tac) >>
  qpat_assum `lookup_block (STRCAT p b) (inline_call_site _ _ _ _ _ _).fn_blocks = _`
    (mp_then Any mp_tac inline_final_lookup_fields) >>
  disch_then (qspecl_then [`rb`, `lbl`, `ret`] strip_assume_tac) >>
  qexists `tb` >> simp[] >>
  `~MEM (STRCAT p b) (bb_succs rb)` by metis_tac[] >>
  `cb.bb_label = b` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
  gvs[rewrite_inline_block_label, clone_basic_block_def] >>
  drule inline_fields_eval_phis >> disch_then (qspec_then `t` mp_tac) >>
  simp[rewrite_inline_block_def, pairTheory.UNCURRY,
       inline_rewrite_eval_phis] >>
  disch_then SUBST1_TAC >> irule inline_clone_eval_phis >>
  gvs[functionInlinerOriginTheory.inliner_phi_labels_closed_def, EVERY_MEM] >>
  metis_tac[venomExecPropsTheory.lookup_block_MEM,
            unitShapeDefsTheory.MEM_fn_insts_blocks_iff,
            venomInstTheory.fn_insts_def]
QED

Theorem inline_one_site_final_assembly:
  find_invoke_site callee.fn_name caller.fn_blocks = SOME (lbl,i) /\
  lookup_block lbl caller.fn_blocks = SOME call_bb /\
  ~MEM (return_block_label (inline_prefix ist.is_inline_count)
    ist.is_label_counter) (fn_labels caller) /\
  inline_one_site caller callee ist = SOME (final,ist') ==>
  final = renumber_fn_inst_ids (fix_inline_phis lbl
    (return_block_label (inline_prefix ist.is_inline_count) ist.is_label_counter)
    <|bb_label := return_block_label (inline_prefix ist.is_inline_count) ist.is_label_counter;
      bb_instructions := DROP (i+1) call_bb.bb_instructions|>
    (inline_call_site (inline_prefix ist.is_inline_count)
      (return_block_label (inline_prefix ist.is_inline_count) ist.is_label_counter)
      caller callee lbl i))
Proof
  strip_tac >> drule_all inline_call_site_lookup_return >>
  disch_then (qspecl_then [`inline_prefix ist.is_inline_count`, `i`, `callee`]
    assume_tac) >>
  gvs[inline_one_site_def]
QED

Theorem inline_caller_produced_optional_phis:
  lookup_block lbl caller.fn_blocks = SOME call_bb /\
  lookup_block b caller.fn_blocks = SOME bb /\
  i < LENGTH call_bb.bb_instructions /\
  (EL i call_bb.bb_instructions).inst_opcode = INVOKE /\
  inliner_phi_labels_closed caller /\ fn_inst_wf caller /\
  ~MEM ret (fn_labels caller) /\
  (!prev. prev_bb = SOME prev ==> MEM prev (fn_labels caller)) /\
  eval_phis (s with vs_prev_bb := prev_bb) bb.bb_instructions = OK u ==>
  ?tb. lookup_block b
      (renumber_fn_inst_ids (fix_inline_phis lbl ret rb
        (inline_call_site p ret caller callee lbl i))).fn_blocks = SOME tb /\
    eval_phis (s with vs_prev_bb :=
      (if MEM b (bb_succs rb) then
        OPTION_MAP (\l. if l = lbl then ret else l) prev_bb else prev_bb))
      tb.bb_instructions =
    OK (u with vs_prev_bb := (if MEM b (bb_succs rb) then
        OPTION_MAP (\l. if l = lbl then ret else l) prev_bb else prev_bb))
Proof
  strip_tac >> drule_all inline_caller_produced_phis >>
  disch_then (qspecl_then [`s with vs_prev_bb :=
    (if MEM b (bb_succs rb) then
      OPTION_MAP (\l. if l = lbl then ret else l) prev_bb else prev_bb)`,
    `ret`, `rb`, `p`, `callee`] strip_assume_tac) >>
  qexists `tb` >> simp[] >> Cases_on `MEM b (bb_succs rb)` >> gvs[]
  >- (drule inline_eval_phis_optional_repair >>
      disch_then (qspecl_then [`s`, `prev_bb`, `lbl`, `ret`, `bb`] mp_tac) >>
      simp[] >> metis_tac[venomExecPropsTheory.lookup_block_MEM]) >>
  drule eval_phis_only_updates_vs_vars >> simp[] >> strip_tac >>
  qpat_x_assum `u = _` SUBST1_TAC >> simp[]
QED

Theorem inline_saved_suffix_succs_closed:
  fn_succs_closed caller /\ lookup_block lbl caller.fn_blocks = SOME bb /\
  i + 1 < LENGTH bb.bb_instructions ==>
  !l. MEM l (bb_succs <|bb_label := ret;
      bb_instructions := DROP (i+1) bb.bb_instructions|>) ==>
    MEM l (fn_labels caller)
Proof
  strip_tac >> simp[functionInlinerWfTheory.inline_return_succs] >>
  metis_tac[fn_succs_closed_def, venomExecPropsTheory.lookup_block_MEM]
QED

Theorem inline_one_site_clone_produced_phis:
  find_invoke_site callee.fn_name caller.fn_blocks = SOME (lbl,i) /\
  lookup_block lbl caller.fn_blocks = SOME call_bb /\
  lookup_block b callee.fn_blocks = SOME cb /\
  p = inline_prefix ist.is_inline_count /\
  ret = return_block_label p ist.is_label_counter /\
  ~MEM ret (fn_labels caller) /\ ~MEM (STRCAT p b) (fn_labels caller) /\
  STRCAT p b <> ret /\ fn_succs_closed caller /\
  i + 1 < LENGTH call_bb.bb_instructions /\
  inliner_phi_labels_closed callee /\
  inline_one_site caller callee ist = SOME (final,ist') ==>
  ?tb. lookup_block (STRCAT p b) final.fn_blocks = SOME tb /\
    eval_phis t tb.bb_instructions =
      eval_phis t (MAP (inline_rename_inst (STRCAT p) (STRCAT p))
        cb.bb_instructions)
Proof
  strip_tac >> gvs[] >>
  drule_all inline_one_site_final_assembly >> strip_tac >>
  gvs[] >> irule inline_clone_produced_phis >> simp[] >>
  metis_tac[inline_saved_suffix_succs_closed]
QED

Theorem inline_one_site_caller_produced_phis:
  find_invoke_site callee.fn_name caller.fn_blocks = SOME (lbl,i) /\
  lookup_block lbl caller.fn_blocks = SOME call_bb /\
  lookup_block b caller.fn_blocks = SOME bb /\
  p = inline_prefix ist.is_inline_count /\
  ret = return_block_label p ist.is_label_counter /\
  rb = <|bb_label := ret;
    bb_instructions := DROP (i+1) call_bb.bb_instructions|> /\
  i < LENGTH call_bb.bb_instructions /\
  (EL i call_bb.bb_instructions).inst_opcode = INVOKE /\
  inliner_phi_labels_closed caller /\ fn_inst_wf caller /\
  ~MEM ret (fn_labels caller) /\
  (!prev. prev_bb = SOME prev ==> MEM prev (fn_labels caller)) /\
  eval_phis (s with vs_prev_bb := prev_bb) bb.bb_instructions = OK u /\
  inline_one_site caller callee ist = SOME (final,ist') ==>
  ?tb. lookup_block b final.fn_blocks = SOME tb /\
    eval_phis (s with vs_prev_bb :=
      (if MEM b (bb_succs rb) then
        OPTION_MAP (\l. if l = lbl then ret else l) prev_bb else prev_bb))
      tb.bb_instructions =
    OK (u with vs_prev_bb := (if MEM b (bb_succs rb) then
        OPTION_MAP (\l. if l = lbl then ret else l) prev_bb else prev_bb))
Proof
  strip_tac >> gvs[] >>
  drule_all inline_one_site_final_assembly >> strip_tac >> gvs[] >>
  irule inline_caller_produced_optional_phis >> simp[] >> metis_tac[]
QED

Theorem inline_rewrite_phi_prefix_contents:
  !insts n.
  TAKE (phi_prefix_length (FST (rewrite_inline_insts args outs ret insts n)))
    (FST (rewrite_inline_insts args outs ret insts n)) =
  TAKE (phi_prefix_length insts) insts
Proof
  Induct_on `insts` >- simp[rewrite_inline_insts_def, phi_prefix_length_def] >>
  rpt gen_tac >> Cases_on `h.inst_opcode = PHI`
  >- simp[rewrite_inline_insts_def, inline_rewrite_phi, pairTheory.UNCURRY,
          phi_prefix_length_def] >>
  drule inline_rewrite_nonphi_head >>
  disch_then (qspecl_then [`ret`, `outs`, `n`, `args`] strip_assume_tac) >>
  simp[rewrite_inline_insts_def, pairTheory.UNCURRY, phi_prefix_length_def]
QED

Theorem inline_clone_phi_prefix_contents:
  !insts. EVERY (\inst. inst.inst_opcode = PHI ==>
    EVERY (\op. !l. op = Label l ==> MEM l labs) inst.inst_operands) insts ==>
  TAKE (phi_prefix_length (MAP (clone_instruction p labs) insts))
    (MAP (clone_instruction p labs) insts) =
  MAP (inline_rename_inst (STRCAT p) (STRCAT p))
    (TAKE (phi_prefix_length insts) insts)
Proof
  Induct_on `insts` >- simp[] >> simp[] >> strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- simp[inline_clone_phi_inst, inline_rename_inst_def, phi_prefix_length_def] >>
  simp[clone_instruction_def, phi_prefix_length_def]
QED

Theorem inline_clone_produced_phi_prefix_fields:
  lookup_block lbl caller.fn_blocks = SOME call_bb /\
  lookup_block b callee.fn_blocks = SOME cb /\
  ~MEM (STRCAT p b) (fn_labels caller) /\ STRCAT p b <> ret /\
  (!l. MEM l (bb_succs rb) ==> MEM l (fn_labels caller)) /\
  inliner_phi_labels_closed callee ==>
  ?tb. lookup_block (STRCAT p b)
      (renumber_fn_inst_ids (fix_inline_phis lbl ret rb
        (inline_call_site p ret caller callee lbl i))).fn_blocks = SOME tb /\
    MAP inline_inst_fields (TAKE (phi_prefix_length tb.bb_instructions) tb.bb_instructions) =
    MAP inline_inst_fields (MAP (inline_rename_inst (STRCAT p) (STRCAT p))
      (TAKE (phi_prefix_length cb.bb_instructions) cb.bb_instructions))
Proof
  strip_tac >> drule_all inline_call_site_lookup_clone >>
  disch_then (qspec_then `i` assume_tac) >>
  qpat_assum `lookup_block (STRCAT p b) (inline_call_site _ _ _ _ _ _).fn_blocks = _`
    (mp_then Any mp_tac inline_final_lookup_fields) >>
  disch_then (qspecl_then [`rb`, `lbl`, `ret`] strip_assume_tac) >>
  qexists `tb` >> simp[] >>
  `~MEM (STRCAT p b) (bb_succs rb)` by metis_tac[] >>
  `cb.bb_label = b` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
  gvs[rewrite_inline_block_label, clone_basic_block_def] >>
  drule inline_fields_phi_prefix_contents >>
  simp[rewrite_inline_block_def, pairTheory.UNCURRY,
       inline_rewrite_phi_prefix_contents] >>
  disch_then SUBST1_TAC >>
  `EVERY (\inst. inst.inst_opcode = PHI ==>
    EVERY (\op. !l. op = Label l ==> MEM l (fn_labels callee)) inst.inst_operands)
    cb.bb_instructions` by
    (gvs[functionInlinerOriginTheory.inliner_phi_labels_closed_def, EVERY_MEM] >>
     metis_tac[venomExecPropsTheory.lookup_block_MEM,
       unitShapeDefsTheory.MEM_fn_insts_blocks_iff, venomInstTheory.fn_insts_def]) >>
  drule inline_clone_phi_prefix_contents >> simp[]
QED
