(* Continuation-style transport in the actual execution semantics. *)
Theory functionInlinerSimulation
Ancestors
  functionInlinerOperational functionInlinerCallBoundary
  functionInlinerReturnTransport functionInlinerFuel functionInlinerSiteLayout
  functionInlinerPhiTransport functionInlinerFmp
  venomExecSemantics
  functionInlinerFrame functionInlinerDefs venomState venomInst venomWf list pred_set

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
