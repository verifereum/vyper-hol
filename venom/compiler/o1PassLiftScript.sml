(*
 * Lifting per-function pass facts to the O1 stage contract.
 *
 * A pass that keeps the calling convention (it changes no INVOKE target,
 * argument value or return value, and leaves every state field but the
 * frame's variables and control position alone) is proved one function
 * at a time, in an arbitrary context.  This theory turns such facts into
 * the stage part of the pass contract (o1PassContract) between two stage
 * contexts C and C' related function by function:
 *
 *   - fn_bisim fn fn': terminating runs of fn and fn' from a frame entry
 *     state correspond, in both directions, in any context.  Runs are
 *     compared by frame_result_rel: equal return values and equal states
 *     outside the frame's variables and control position.  Every function
 *     pair related by fn_bisim gives ctx_bisim C C' (an induction on
 *     fuel through INVOKE), and that gives ctx_sim (ctx_bisim_ctx_sim).
 *
 *   - frame_sim L C C' fn fn': every state a frame of fn' reaches in C'
 *     corresponds to one a frame of fn reaches in C from the same entry
 *     state, with the same alloca frame and the same memory ranges, or
 *     none (an inserted instruction that touches no memory).  Every
 *     function pair related by frame_sim transports the shared memory
 *     invariant for any memory fact closed under that correspondence
 *     (frame_sim_mem_inv), which every phase fact is.
 *)
Theory o1PassLift
Ancestors
  o1PassContract unitMemInv contextRawReachable contextCodegenRel
  unitTransformDefs passSimulationDefs stateEquiv stateFrame
  venomExecSemantics venomExecProps venomInst venomMemDefs venomState list finite_map

(* ===== Run correspondence ===== *)

(* The state a frame of fn starts in: the context entry (run_context) and a
   callee (setup_callee) both start this way. *)
Definition fn_entry_state_def:
  fn_entry_state fn s <=>
    s.vs_vars = FEMPTY /\ s.vs_inst_idx = 0 /\ s.vs_prev_bb = NONE /\
    ~s.vs_halted /\ fn_entry_label fn = SOME s.vs_current_bb
End

(* Terminal results of a frame that its caller can't tell apart. *)
Definition frame_result_rel_def:
  frame_result_rel r r' <=>
    case (r, r') of
      (IntRet v s, IntRet v' s') =>
        v' = v /\ execution_frame s' = execution_frame s
    | (Halt s, Halt s') => execution_frame s' = execution_frame s
    | (Abort a s, Abort a' s') =>
        a' = a /\ execution_frame s' = execution_frame s
    | _ => F
End

(* One step's results: a continuing step reaches the same state. *)
Definition step_result_rel_def:
  step_result_rel r r' <=>
    case (r, r') of
      (OK s, OK s') => s' = s
    | _ => frame_result_rel r r'
End

(* fn and its transform fn' have corresponding terminating runs from every
   frame entry state, in any context. *)
Definition fn_bisim_def:
  fn_bisim fn fn' <=>
    fn'.fn_name = fn.fn_name /\ fn_entry_label fn' = fn_entry_label fn /\
    !ctx s. fn_entry_state fn s ==>
      (!fuel. terminates (run_blocks fuel ctx fn s) ==>
         ?fuel'. frame_result_rel (run_blocks fuel ctx fn s)
                                  (run_blocks fuel' ctx fn' s)) /\
      (!fuel'. terminates (run_blocks fuel' ctx fn' s) ==>
         ?fuel. frame_result_rel (run_blocks fuel ctx fn s)
                                 (run_blocks fuel' ctx fn' s))
End

(* The same, between the functions of two contexts, each run in its own
   context. *)
Definition ctx_bisim_def:
  ctx_bisim C C' <=>
    ctx_fn_names C' = ctx_fn_names C /\
    !name fn.
      lookup_function name C.ctx_functions = SOME fn ==>
      ?fn'. lookup_function name C'.ctx_functions = SOME fn' /\
            fn_entry_label fn' = fn_entry_label fn /\
            !s. fn_entry_state fn s ==>
              (!fuel. terminates (run_blocks fuel C fn s) ==>
                 ?fuel'. frame_result_rel (run_blocks fuel C fn s)
                                          (run_blocks fuel' C' fn' s)) /\
              (!fuel'. terminates (run_blocks fuel' C' fn' s) ==>
                 ?fuel. frame_result_rel (run_blocks fuel C fn s)
                                         (run_blocks fuel' C' fn' s))
End

Theorem frame_result_rel_sym:
  frame_result_rel r r' ==> frame_result_rel r' r
Proof
  Cases_on `r` >> Cases_on `r'` >> simp[frame_result_rel_def] >> metis_tac[]
QED

Theorem frame_result_rel_trans:
  frame_result_rel r r' /\ frame_result_rel r' r'' ==> frame_result_rel r r''
Proof
  Cases_on `r` >> Cases_on `r'` >> Cases_on `r''` >>
  simp[frame_result_rel_def] >> metis_tac[]
QED

Theorem frame_result_rel_terminates:
  frame_result_rel r r' ==> terminates r /\ terminates r'
Proof
  Cases_on `r` >> Cases_on `r'` >> simp[frame_result_rel_def, terminates_def]
QED

Theorem step_result_rel_sym:
  step_result_rel r r' ==> step_result_rel r' r
Proof
  Cases_on `r` >> Cases_on `r'` >>
  simp[step_result_rel_def, frame_result_rel_def] >> metis_tac[]
QED

Theorem step_result_rel_trans:
  step_result_rel r r' /\ step_result_rel r' r'' ==> step_result_rel r r''
Proof
  Cases_on `r` >> Cases_on `r'` >> Cases_on `r''` >>
  simp[step_result_rel_def, frame_result_rel_def] >> metis_tac[]
QED

Theorem step_result_rel_terminates:
  step_result_rel r r' ==> terminates r /\ terminates r'
Proof
  Cases_on `r` >> Cases_on `r'` >>
  simp[step_result_rel_def, frame_result_rel_def, terminates_def]
QED

Theorem execution_frame_observable:
  execution_frame s' = execution_frame s ==> observable_equiv s s'
Proof
  simp[execution_frame_eq_reconstruct] >> strip_tac >>
  pop_assum (SUBST1_TAC o SYM) >> simp[observable_equiv_def]
QED

Theorem execution_frame_merge_callee:
  execution_frame t' = execution_frame t ==>
  merge_callee_state s t' = merge_callee_state s t
Proof
  simp[execution_frame_eq_reconstruct] >> strip_tac >>
  pop_assum (SUBST1_TAC o SYM) >> simp[merge_callee_state_def]
QED

Theorem frame_result_rel_unit:
  frame_result_rel r r' /\ (!v t. r <> IntRet v t) ==> unit_result_rel r r'
Proof
  Cases_on `r` >> Cases_on `r'` >>
  simp[frame_result_rel_def, unit_result_rel_def, observable_equiv_def]
QED

(* The result-consumption boundary of INVOKE, independent of lookup/fuel. *)
Definition invoke_result_def:
  invoke_result outs s r =
    case r of
      IntRet ret t =>
        (case bind_outputs outs ret.iret_values
                (adopt_return_fmp ret (merge_callee_state s t)) of
           SOME u => OK u
         | NONE => Error "invoke: return arity mismatch")
    | Halt t => Halt t
    | Abort a t => Abort a t
    | Error e => Error e
    | OK t => Error "invoke: callee did not return"
End

Theorem frame_result_rel_invoke:
  frame_result_rel r r' ==>
  terminates (invoke_result outs s r) ==>
  step_result_rel (invoke_result outs s r) (invoke_result outs s r')
Proof
  Cases_on `r` >> Cases_on `r'` >>
  simp_tac pure_ss [frame_result_rel_def, pairTheory.pair_case_def,
                    exec_result_case_def] >> strip_tac >>
  drule execution_frame_merge_callee >>
  disch_then (qspec_then `s` assume_tac) >>
  asm_rewrite_tac[invoke_result_def] >>
  gvs[step_result_rel_def, frame_result_rel_def, AllCaseEqs(), terminates_def] >>
  Cases_on `bind_outputs outs i.iret_values
    (adopt_return_fmp i (merge_callee_state s v))` >> simp[]
QED

Theorem list_rel_lookup_function:
  !xs ys. LIST_REL R xs ys /\
    (!f g. R f g ==> g.fn_name = f.fn_name) ==>
    !name. OPTREL R (lookup_function name xs) (lookup_function name ys)
Proof
  Induct_on `xs` >> Cases_on `ys` >>
  simp[lookup_function_def, FIND_thm] >> rpt strip_tac >>
  `h.fn_name = h'.fn_name` by metis_tac[] >>
  Cases_on `h'.fn_name = name` >>
  simp[lookup_function_def, FIND_thm] >>
  metis_tac[lookup_function_def]
QED

Theorem list_rel_function_names:
  !xs ys. LIST_REL R xs ys /\
    (!f g. R f g ==> g.fn_name = f.fn_name) ==>
    MAP (\f. f.fn_name) ys = MAP (\f. f.fn_name) xs
Proof
  Induct_on `xs` >> Cases_on `ys` >> simp[] >> metis_tac[]
QED

Theorem list_rel_lookup_failure:
  LIST_REL R xs ys /\
  (!f g. R f g ==> g.fn_name = f.fn_name) ==>
  (lookup_function name xs = NONE <=> lookup_function name ys = NONE)
Proof
  strip_tac >> drule_all list_rel_lookup_function >>
  disch_then (qspec_then `name` mp_tac) >>
  Cases_on `lookup_function name xs` >>
  Cases_on `lookup_function name ys` >> simp[]
QED

Theorem setup_callee_entry_label:
  fn_entry_label f = fn_entry_label g ==>
  setup_callee f args s = setup_callee g args s
Proof
  simp[fn_entry_label_def, entry_block_def, setup_callee_def] >>
  Cases_on `NULL f.fn_blocks` >> Cases_on `NULL g.fn_blocks` >> simp[]
QED

Theorem setup_callee_execution_frame:
  execution_frame s' = execution_frame s /\
  fn_entry_label g = fn_entry_label f ==>
  setup_callee g args s' = setup_callee f args s
Proof
  strip_tac >>
  `setup_callee g args s' = setup_callee f args s'`
    by metis_tac[setup_callee_entry_label] >>
  asm_rewrite_tac[] >>
  qpat_x_assum `execution_frame _ = _` mp_tac >>
  simp[execution_frame_eq_reconstruct] >> strip_tac >>
  pop_assum (SUBST1_TAC o SYM) >> simp[setup_callee_def]
QED

Theorem setup_callee_fn_entry_state:
  setup_callee f args s = SOME cs ==> fn_entry_state f cs
Proof
  simp[setup_callee_def] >>
  Cases_on `NULL f.fn_blocks` >> simp[] >> strip_tac >>
  gvs[fn_entry_state_def, fn_entry_label_def, entry_block_def]
QED

Theorem context_fn_entry_state:
  s.vs_vars = FEMPTY /\ ~s.vs_halted /\ fn_entry_label f = SOME lbl ==>
  fn_entry_state f (s with <|vs_prev_bb := NONE; vs_current_bb := lbl;
                             vs_inst_idx := 0|>)
Proof
  simp[fn_entry_state_def]
QED

Definition bounded_call_agree_def:
  bounded_call_agree n A B <=>
    !name f s k.
      k < n /\ lookup_function name A.ctx_functions = SOME f /\
      fn_entry_state f s /\ terminates (run_blocks k A f s) ==>
      ?g j. lookup_function name B.ctx_functions = SOME g /\
            fn_entry_label g = fn_entry_label f /\
            frame_result_rel (run_blocks k A f s) (run_blocks j B g s)
End

Theorem terminates_not_error:
  terminates r <=> !e. r <> Error e
Proof
  Cases_on `r` >> simp[terminates_def]
QED

Theorem step_inst_terminates_mono:
  terminates (step_inst n C i s) /\ n <= m ==>
  step_inst m C i s = step_inst n C i s
Proof
  simp[terminates_not_error] >> metis_tac[cj 1 venomExecPropsTheory.fuel_mono]
QED

Theorem exec_block_terminates_mono:
  terminates (exec_block n C b s) /\ n <= m ==>
  exec_block m C b s = exec_block n C b s
Proof
  simp[terminates_not_error] >> metis_tac[cj 2 venomExecPropsTheory.fuel_mono]
QED

Theorem run_blocks_terminates_mono:
  terminates (run_blocks n C f s) /\ n <= m ==>
  run_blocks m C f s = run_blocks n C f s
Proof
  simp[terminates_not_error] >> metis_tac[cj 3 venomExecPropsTheory.fuel_mono]
QED

Theorem bounded_call_agree_step_inst:
  bounded_call_agree n A B /\ k < n /\ terminates (step_inst k A inst s) ==>
  ?j. step_result_rel (step_inst k A inst s) (step_inst j B inst s)
Proof
  strip_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- (qpat_x_assum `terminates _` mp_tac >>
      simp[Once step_inst_def] >>
      Cases_on `decode_invoke inst` >> simp[terminates_def] >>
      PairCases_on `x` >>
      Cases_on `lookup_function x0 A.ctx_functions` >> simp[terminates_def] >>
      Cases_on `eval_operands x1 s` >> simp[terminates_def] >>
      rename1 `lookup_function x0 A.ctx_functions = SOME f` >>
      rename1 `eval_operands x1 s = SOME args` >>
      Cases_on `setup_callee f args s` >> simp[terminates_def] >>
      rename1 `setup_callee f args s = SOME cs` >>
      pure_rewrite_tac[GSYM invoke_result_def] >>
      pure_rewrite_tac[GSYM terminates_def] >> strip_tac >>
      `terminates (run_blocks k A f cs)` by
        (Cases_on `run_blocks k A f cs` >>
         gvs[invoke_result_def, terminates_def]) >>
      `fn_entry_state f cs` by metis_tac[setup_callee_fn_entry_state] >>
      qpat_x_assum `bounded_call_agree _ _ _` mp_tac >>
      pure_rewrite_tac[bounded_call_agree_def] >>
      disch_then (qspecl_then [`x0`, `f`, `cs`, `k`] mp_tac) >>
      asm_rewrite_tac[] >> strip_tac >>
      `setup_callee g args s = SOME cs` by
        metis_tac[setup_callee_entry_label] >>
      qexists_tac `j` >>
      asm_simp_tac pure_ss [step_inst_def] >>
      pure_rewrite_tac[GSYM invoke_result_def] >>
      simp[] >>
      irule frame_result_rel_invoke >> asm_rewrite_tac[]) >>
  qexists_tac `k` >>
  gvs[step_inst_non_invoke] >>
  Cases_on `step_inst_base inst s` >>
  gvs[terminates_def, step_result_rel_def, frame_result_rel_def]
QED

Theorem bounded_call_agree_exec_block:
  bounded_call_agree n A B /\ k < n /\ terminates (exec_block k A bb s) ==>
  ?j. step_result_rel (exec_block k A bb s) (exec_block j B bb s)
Proof
  qid_spec_tac `s` >>
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `terminates _` mp_tac >>
  simp[Once exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[terminates_def] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  strip_tac >>
  `terminates (step_inst k A inst s)` by
    (Cases_on `step_inst k A inst s` >> gvs[terminates_def]) >>
  drule_all bounded_call_agree_step_inst >> strip_tac >>
  Cases_on `step_inst k A inst s` >>
  Cases_on `step_inst j B inst s` >>
  qpat_x_assum `step_result_rel _ _`
    (mp_tac o PURE_REWRITE_RULE [step_result_rel_def, frame_result_rel_def,
      pairTheory.pair_case_def, exec_result_case_def]) >>
  strip_tac >> gvs[]
  >- suspend "continuing_step"
  >> qexists_tac `j` >>
  CONV_TAC (BINOP_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  simp[step_result_rel_def, frame_result_rel_def]
QED

Resume bounded_call_agree_exec_block[continuing_step]:
  Cases_on `is_terminator inst.inst_opcode`
  >- (qexists_tac `j` >>
      CONV_TAC (BINOP_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
      simp[step_result_rel_def, frame_result_rel_def] >>
      Cases_on `v'.vs_halted` >> simp[step_result_rel_def, frame_result_rel_def]) >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  `terminates (exec_block k A bb (v' with vs_inst_idx := SUC s.vs_inst_idx))`
    by gvs[terminates_def] >>
  first_x_assum (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
  simp[] >>
  disch_then (qspec_then `v' with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> strip_tac >>
  `terminates (exec_block j' B bb (v' with vs_inst_idx := SUC s.vs_inst_idx))`
    by metis_tac[step_result_rel_terminates] >>
  `step_inst (MAX j j') B inst s = OK v'` by
    ( `terminates (step_inst j B inst s)` by simp[terminates_def] >>
      drule step_inst_terminates_mono >>
      disch_then (qspec_then `MAX j j'` mp_tac) >> simp[]) >>
  `exec_block (MAX j j') B bb (v' with vs_inst_idx := SUC s.vs_inst_idx) =
   exec_block j' B bb (v' with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule exec_block_terminates_mono >> simp[]) >>
  qexists_tac `MAX j j'` >>
  CONV_TAC (BINOP_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  simp[]
QED

Finalise bounded_call_agree_exec_block

Theorem run_blocks_not_OK:
  !n s t. run_blocks n C f s <> OK t
Proof
  Induct_on `n` >- simp[Once run_blocks_def] >>
  rpt gen_tac >> simp[run_blocks_unfold] >>
  Cases_on `lookup_block s.vs_current_bb f.fn_blocks` >> simp[] >>
  Cases_on `run_block n C x s` >> simp[] >>
  Cases_on `v.vs_halted` >> simp[]
QED

Theorem bounded_call_agree_mono:
  bounded_call_agree n A B /\ m <= n ==> bounded_call_agree m A B
Proof
  rw[bounded_call_agree_def] >> first_x_assum irule >> simp[] >>
  metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Theorem bounded_call_agree_run_blocks:
  !n f s. bounded_call_agree n A B /\ terminates (run_blocks n A f s) ==>
  ?j. frame_result_rel (run_blocks n A f s) (run_blocks j B f s)
Proof
  Induct_on `n` >- simp[Once run_blocks_def, terminates_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `terminates _` mp_tac >>
  simp[run_blocks_unfold] >>
  Cases_on `lookup_block s.vs_current_bb f.fn_blocks` >> simp[terminates_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  mp_tac (Q.SPECL [`s`, `bb.bb_instructions`] eval_phis_ok_or_error_defs) >>
  strip_tac >> simp[run_block_def, terminates_def] >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `exec_block n A bb ps` >>
  `terminates (exec_block n A bb ps)` by
    (Cases_on `exec_block n A bb ps` >> gvs[terminates_def]) >>
  `n < SUC n` by simp[] >>
  drule_all bounded_call_agree_exec_block >> strip_tac >>
  Cases_on `exec_block n A bb ps` >>
  Cases_on `exec_block j B bb ps` >>
  qpat_x_assum `step_result_rel _ _`
    (mp_tac o PURE_REWRITE_RULE [step_result_rel_def, frame_result_rel_def,
      pairTheory.pair_case_def, exec_result_case_def]) >>
  strip_tac >> gvs[]
  >- suspend "run_continuation"
  >> qexists_tac `SUC j` >>
  gvs[run_blocks_unfold, run_block_def, Abbr `ps`, frame_result_rel_def]
QED

Resume bounded_call_agree_run_blocks[run_continuation]:
  Cases_on `v.vs_halted`
  >- (qexists_tac `SUC j` >>
      gvs[run_blocks_unfold, run_block_def, Abbr `ps`, frame_result_rel_def]) >>
  `bounded_call_agree n A B` by
    (irule bounded_call_agree_mono >> qexists_tac `SUC n` >> simp[]) >>
  `terminates (run_blocks n A f v)` by gvs[terminates_def] >>
  first_x_assum (qspecl_then [`f`, `v`] mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  rename1 `frame_result_rel (run_blocks n A f v) (run_blocks tail B f v)` >>
  `terminates (run_blocks tail B f v)` by metis_tac[frame_result_rel_terminates] >>
  `exec_block (MAX j tail) B bb ps = OK v` by
    (`terminates (exec_block j B bb ps)` by simp[terminates_def] >>
     drule exec_block_terminates_mono >>
     disch_then (qspec_then `MAX j tail` mp_tac) >> simp[]) >>
  `run_blocks (MAX j tail) B f v = run_blocks tail B f v` by
    (irule run_blocks_terminates_mono >> simp[]) >>
  qexists_tac `SUC (MAX j tail)` >>
  gvs[run_blocks_unfold, run_block_def, Abbr `ps`]
QED

Finalise bounded_call_agree_run_blocks

Theorem fn_bisim_sym:
  fn_bisim f g ==> fn_bisim g f
Proof
  rw[fn_bisim_def] >>
  `fn_entry_state f s` by gvs[fn_entry_state_def] >>
  first_x_assum (qspecl_then [`ctx`, `s`] mp_tac) >>
  simp[] >> metis_tac[frame_result_rel_sym]
QED

Theorem fn_bisim_bounded_call_agree:
  LIST_REL fn_bisim A.ctx_functions B.ctx_functions ==>
  !n. bounded_call_agree n A B
Proof
  strip_tac >> Induct
  >- simp[bounded_call_agree_def] >>
  rw[bounded_call_agree_def] >>
  `bounded_call_agree k A B` by
    (irule bounded_call_agree_mono >> qexists_tac `n` >> simp[]) >>
  drule_all bounded_call_agree_run_blocks >> strip_tac >>
  `OPTREL fn_bisim (lookup_function name A.ctx_functions)
                    (lookup_function name B.ctx_functions)` by
    (irule list_rel_lookup_function >> simp[fn_bisim_def]) >>
  Cases_on `lookup_function name B.ctx_functions` >> gvs[] >>
  rename1 `fn_bisim f g` >>
  `terminates (run_blocks j B f s)` by metis_tac[frame_result_rel_terminates] >>
  qpat_x_assum `fn_bisim _ _` mp_tac >>
  pure_rewrite_tac[fn_bisim_def] >> strip_tac >>
  first_x_assum (qspecl_then [`B`, `s`] mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  first_x_assum (qspec_then `j` mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  metis_tac[frame_result_rel_trans]
QED

Theorem list_rel_fn_bisim_sym:
  !xs ys. LIST_REL fn_bisim xs ys ==> LIST_REL fn_bisim ys xs
Proof
  Induct_on `xs` >> Cases_on `ys` >> simp[] >> metis_tac[fn_bisim_sym]
QED

(* Forward: fn in C matches fn in C' (induction on fuel; a callee runs on
   less fuel), then fn_bisim at C'.  Backward: fn' in C' matches fn' in C,
   then fn_bisim at C. *)
Theorem fn_bisim_ctx_bisim:
  LIST_REL fn_bisim C.ctx_functions C'.ctx_functions ==> ctx_bisim C C'
Proof
  strip_tac >>
  `!n. bounded_call_agree n C C'` by metis_tac[fn_bisim_bounded_call_agree] >>
  `!n. bounded_call_agree n C' C` by
    metis_tac[fn_bisim_bounded_call_agree, list_rel_fn_bisim_sym] >>
  rw[ctx_bisim_def]
  >- (simp[ctx_fn_names_def] >> irule list_rel_function_names >>
      qexists_tac `fn_bisim` >> simp[fn_bisim_def]) >>
  `OPTREL fn_bisim (lookup_function name C.ctx_functions)
                    (lookup_function name C'.ctx_functions)` by
    (irule list_rel_lookup_function >> simp[fn_bisim_def]) >>
  Cases_on `lookup_function name C'.ctx_functions` >> gvs[] >>
  rename1 `fn_bisim fn fn'` >>
  `fn_entry_label fn' = fn_entry_label fn` by gvs[fn_bisim_def] >>
  simp[] >> rpt strip_tac
  >- (qpat_x_assum `!n. bounded_call_agree n C C'`
        (qspec_then `SUC fuel` mp_tac) >>
      rw[bounded_call_agree_def] >>
      first_x_assum (qspecl_then [`name`, `fn`, `s`, `fuel`] mp_tac) >>
      simp[] >> metis_tac[]) >>
  `fn_entry_state fn' s` by gvs[fn_entry_state_def] >>
  qpat_x_assum `!n. bounded_call_agree n C' C`
    (qspec_then `SUC fuel'` mp_tac) >>
  rw[bounded_call_agree_def] >>
  first_x_assum (qspecl_then [`name`, `fn'`, `s`, `fuel'`] mp_tac) >>
  simp[] >> metis_tac[frame_result_rel_sym]
QED

Theorem ctx_bisim_sym:
  ctx_bisim A B ==> ctx_bisim B A
Proof
  strip_tac >>
  qpat_x_assum `ctx_bisim _ _` mp_tac >>
  rw[ctx_bisim_def] >>
  `?f. lookup_function name A.ctx_functions = SOME f` by
    (Cases_on `lookup_function name A.ctx_functions` >> simp[] >>
     drule lookup_function_not_mem >>
     drule lookup_function_mem >>
     gvs[ctx_fn_names_def]) >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  `fn_entry_label f = fn_entry_label fn` by simp[] >>
  simp[] >> rpt strip_tac >>
  `fn_entry_state f s` by gvs[fn_entry_state_def] >>
  first_x_assum (qspec_then `s` mp_tac) >>
  simp[] >> metis_tac[frame_result_rel_sym]
QED

Theorem ctx_bisim_bounded_call_agree:
  ctx_bisim A B ==> bounded_call_agree n A B
Proof
  rw[ctx_bisim_def, bounded_call_agree_def] >>
  first_x_assum drule >> strip_tac >>
  first_x_assum (qspec_then `s` mp_tac) >> simp[] >>
  metis_tac[]
QED

(* One instruction, run in the two contexts. *)
Theorem ctx_bisim_step_inst:
  ctx_bisim C C' ==>
  (!fuel inst s.
     terminates (step_inst fuel C inst s) ==>
     ?fuel'. step_result_rel (step_inst fuel C inst s)
                             (step_inst fuel' C' inst s)) /\
  (!fuel' inst s.
     terminates (step_inst fuel' C' inst s) ==>
     ?fuel. step_result_rel (step_inst fuel C inst s)
                            (step_inst fuel' C' inst s))
Proof
  strip_tac >> conj_tac >> rpt strip_tac
  >- (irule bounded_call_agree_step_inst >> simp[] >>
      qexists_tac `SUC fuel` >> simp[] >>
      metis_tac[ctx_bisim_bounded_call_agree]) >>
  `bounded_call_agree (SUC fuel') C' C` by
    metis_tac[ctx_bisim_sym, ctx_bisim_bounded_call_agree] >>
  `fuel' < SUC fuel'` by simp[] >>
  drule_all bounded_call_agree_step_inst >>
  metis_tac[step_result_rel_sym]
QED

(* A context run that never ends in an internal return (its entry function
   has no RET, RETFMP or DRET) is simulated. *)
Theorem ctx_bisim_ctx_sim:
  ctx_bisim C C' /\ C'.ctx_entry = C.ctx_entry /\
  (!fuel v t. run_context fuel C vs <> IntRet v t) /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted ==>
  ctx_sim C C' vs vs
Proof
  strip_tac >> rw[ctx_sim_def] >>
  Cases_on `C.ctx_entry` >>
  gvs[run_context_def, terminates_def] >>
  Cases_on `lookup_function x C.ctx_functions` >>
  gvs[terminates_def] >>
  rename1 `lookup_function x C.ctx_functions = SOME fn` >>
  fs[ctx_bisim_def] >>
  first_x_assum drule >> strip_tac >>
  Cases_on `fn_entry_label fn` >>
  gvs[run_function_def, terminates_def] >>
  `fn_entry_state fn
     (vs with <|vs_prev_bb := NONE; vs_current_bb := x'; vs_inst_idx := 0|>)` by
    (irule context_fn_entry_state >> simp[]) >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  qexists_tac `fuel'` >>
  irule frame_result_rel_unit >> simp[]
QED

(* ===== Reachable-state correspondence ===== *)

(* The states a frame of fn reaches from its entry state s0 without
   leaving the frame: raw_reachable's entry, next and block rules. *)
Inductive frame_reach:
[~start:]
  (!ctx fn s0 inst s1.
     enters_block fn s0 s1 /\ active_inst fn inst s1 ==>
     frame_reach ctx fn s0 inst s1)
[~next:]
  (!ctx fn s0 inst inst' s s' fuel.
     frame_reach ctx fn s0 inst s /\
     ~is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK s' /\
     active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
     frame_reach ctx fn s0 inst' (s' with vs_inst_idx := SUC s.vs_inst_idx))
[~block:]
  (!ctx fn s0 inst inst' s s' s1 fuel.
     frame_reach ctx fn s0 inst s /\
     is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK s' /\
     ~s'.vs_halted /\ enters_block fn s' s1 /\ active_inst fn inst' s1 ==>
     frame_reach ctx fn s0 inst' s1)
End

Theorem frame_reach_active:
  !ctx fn s0 inst s.
    frame_reach ctx fn s0 inst s ==> active_inst fn inst s
Proof
  ho_match_mp_tac frame_reach_ind >> simp[]
QED

Theorem frame_reach_raw_reachable:
  !ctx fn s0 inst s.
    frame_reach ctx fn s0 inst s ==>
    !vs. (!i t. enters_block fn s0 t /\ active_inst fn i t ==>
                  raw_reachable vs ctx fn i t) ==>
         raw_reachable vs ctx fn inst s
Proof
  ho_match_mp_tac frame_reach_strongind >> rpt conj_tac >> rpt strip_tac
  >- metis_tac[]
  >- (irule (cj 2 raw_reachable_rules) >>
      metis_tac[frame_reach_active])
  >> irule (cj 3 raw_reachable_rules) >>
  metis_tac[frame_reach_active]
QED

Theorem frame_reach_entry:
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  frame_reach ctx fn
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
    inst s ==>
  raw_reachable vs ctx fn inst s
Proof
  strip_tac >> drule frame_reach_raw_reachable >>
  disch_then irule >> metis_tac[raw_reachable_rules]
QED

Theorem frame_reach_callee:
  raw_reachable vs ctx caller callinst s /\ active_inst caller callinst s /\
  callinst.inst_opcode = INVOKE /\ decode_invoke callinst = SOME (nm, ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  frame_reach ctx callee cs inst t ==>
  raw_reachable vs ctx callee inst t
Proof
  strip_tac >> drule frame_reach_raw_reachable >>
  disch_then irule >> metis_tac[raw_reachable_rules]
QED

(* What the memory facts see of a state: the alloca frame, the initial
   free-memory pointer and the instruction's memory ranges.  An inserted
   instruction that touches no memory corresponds to any instruction. *)
Definition mem_corr_def:
  mem_corr inst s inst' s' <=>
    s'.vs_alloca_next = s.vs_alloca_next /\
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_initial_fmp = s.vs_initial_fmp /\
    (inst_mem_ranges inst' s' = [] \/
     inst_mem_ranges inst' s' = inst_mem_ranges inst s)
End

(* An INVOKE corresponds to an INVOKE of the same callee with the same
   argument values from a state that differs only in the frame, so both
   callee frames start in the same state. *)
Definition call_corr_def:
  call_corr inst s inst' s' <=>
    (inst'.inst_opcode = INVOKE ==>
       inst.inst_opcode = INVOKE /\
       execution_frame s' = execution_frame s /\
       ?nm ops ops'. decode_invoke inst = SOME (nm,ops) /\
                     decode_invoke inst' = SOME (nm,ops') /\
                     eval_operands ops' s' = eval_operands ops s)
End

(* Every state a frame of fn' reaches in C' corresponds to one a frame of
   fn reaches in C from the same entry state, for entry states whose label
   table is L.  Every frame of a context run shares the run's label table,
   so L is the initial state's. *)
Definition frame_sim_def:
  frame_sim L C C' fn fn' <=>
    !s0 inst' s'.
      fn_entry_state fn s0 /\ s0.vs_labels = L /\
      frame_reach C' fn' s0 inst' s' ==>
      ?inst s. frame_reach C fn s0 inst s /\
               mem_corr inst s inst' s' /\ call_corr inst s inst' s'
End

(* A memory fact that sees a state only through mem_corr. *)
Definition mem_corr_closed_def:
  mem_corr_closed M <=>
    !ctx fn inst s ctx' fn' inst' s'.
      M ctx fn inst s /\ mem_corr inst s inst' s' ==> M ctx' fn' inst' s'
End

Theorem raw_reachable_labels:
  !vs C fn inst s. raw_reachable vs C fn inst s ==> s.vs_labels = vs.vs_labels
Proof
  ho_match_mp_tac raw_reachable_ind >>
  rw[contextCodegenRelTheory.enters_block_def, setup_callee_def] >>
  imp_res_tac venomExecPropsTheory.eval_phis_preserves_labels >>
  imp_res_tac venomExecPropsTheory.step_inst_preserves_labels_always >>
  gvs[setup_callee_def, AllCaseEqs()]
QED

Definition frame_origin_def:
  frame_origin vs C C' fn' inst' s' <=>
    ?fn s0. fn_entry_state fn s0 /\ s0.vs_labels = vs.vs_labels /\
      frame_sim vs.vs_labels C C' fn fn' /\
      frame_reach C' fn' s0 inst' s' /\
      (!i t. enters_block fn s0 t /\ active_inst fn i t ==>
             raw_reachable vs C fn i t)
End

Theorem frame_origin_correspondence:
  frame_origin vs C C' fn' inst' s' ==>
  ?fn inst s. raw_reachable vs C fn inst s /\ active_inst fn inst s /\
              mem_corr inst s inst' s' /\ call_corr inst s inst' s'
Proof
  rw[frame_origin_def] >>
  fs[frame_sim_def] >>
  first_x_assum (qspecl_then [`s0`, `inst'`, `s'`] mp_tac) >>
  simp[] >> strip_tac >>
  metis_tac[frame_reach_raw_reachable, frame_reach_active]
QED

Theorem frame_sim_raw_origins:
  !vs C' fn' inst' s'. raw_reachable vs C' fn' inst' s' ==>
  !C. LIST_REL (\fn fn'. fn'.fn_name = fn.fn_name /\
                         fn_entry_label fn' = fn_entry_label fn /\
                         frame_sim vs.vs_labels C C' fn fn')
               C.ctx_functions C'.ctx_functions /\
      C'.ctx_entry = C.ctx_entry /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted ==>
      frame_origin vs C C' fn' inst' s'
Proof
  ho_match_mp_tac raw_reachable_ind >> rpt conj_tac
  >- (rpt strip_tac >>
      drule list_rel_lookup_function >> simp[] >>
      disch_then (qspec_then `name` mp_tac) >>
      Cases_on `lookup_function name C.ctx_functions` >> simp[] >>
      strip_tac >> rw[frame_origin_def] >>
      qexistsl_tac [`x`,
        `vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>`] >>
      simp[] >> conj_tac
      >- metis_tac[context_fn_entry_state]
      >> conj_tac
      >- metis_tac[frame_reach_rules]
      >> metis_tac[raw_reachable_rules])
  >- (rpt strip_tac >> first_x_assum drule >> simp[] >>
      rw[frame_origin_def] >> qexistsl_tac [`fn`, `s0`] >>
      simp[] >> metis_tac[cj 2 frame_reach_rules])
  >- (rpt strip_tac >> first_x_assum drule >> simp[] >>
      rw[frame_origin_def] >> qexistsl_tac [`fn`, `s0`] >>
      simp[] >> metis_tac[cj 3 frame_reach_rules])
  >> rpt strip_tac >> first_x_assum drule >> simp[] >>
  strip_tac >> drule frame_origin_correspondence >> strip_tac >>
  drule list_rel_lookup_function >> simp[] >>
  disch_then (qspec_then `nm` mp_tac) >>
  Cases_on `lookup_function nm C.ctx_functions` >> simp[] >> strip_tac >>
  qpat_x_assum `call_corr _ _ _ _` mp_tac >>
  pure_rewrite_tac[call_corr_def] >> asm_rewrite_tac[] >> strip_tac >>
  `setup_callee fn'' args s' = setup_callee x args s` by
    (irule setup_callee_execution_frame >> asm_rewrite_tac[]) >>
  `setup_callee x args s = SOME cs` by metis_tac[] >>
  gvs[] >>
  `cs.vs_labels = vs.vs_labels` by
    (imp_res_tac raw_reachable_labels >>
     qpat_x_assum `setup_callee x args s = SOME cs` mp_tac >>
     rw[setup_callee_def] >> simp[]) >>
  rw[frame_origin_def] >> qexistsl_tac [`x`, `cs`] >> simp[] >>
  conj_tac >- metis_tac[setup_callee_fn_entry_state] >>
  conj_tac >- metis_tac[frame_reach_rules] >>
  metis_tac[cj 4 raw_reachable_rules]
QED

Theorem frame_sim_raw_correspondence:
  LIST_REL (\fn fn'. fn'.fn_name = fn.fn_name /\
                     fn_entry_label fn' = fn_entry_label fn /\
                     frame_sim vs.vs_labels C C' fn fn')
           C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  raw_reachable vs C' fn' inst' s' ==>
  ?fn inst s. raw_reachable vs C fn inst s /\ mem_corr inst s inst' s'
Proof
  strip_tac >> drule frame_sim_raw_origins >>
  disch_then drule >> simp[] >>
  metis_tac[frame_origin_correspondence]
QED

Theorem frame_sim_mem_inv:
  LIST_REL (\fn fn'. fn'.fn_name = fn.fn_name /\
                     fn_entry_label fn' = fn_entry_label fn /\
                     frame_sim vs.vs_labels C C' fn fn')
           C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  mem_corr_closed M /\ mem_inv M C vs ==>
  mem_inv M C' vs
Proof
  strip_tac >> fs[mem_inv_raw_reachable] >> conj_tac
  >- (drule list_rel_lookup_function >> simp[] >>
      disch_then (qspec_then `name` mp_tac) >>
      Cases_on `lookup_function name C'.ctx_functions` >> simp[] >>
      strip_tac >> metis_tac[]) >>
  rpt strip_tac >> drule_all frame_sim_raw_correspondence >> strip_tac >>
  fs[mem_corr_closed_def] >> metis_tac[]
QED

Theorem mem_corr_closed_raw_mem_ok:
  mem_corr_closed raw_mem_ok
Proof
  `!inst s. inst_mem_below_frontier inst s <=>
            EVERY (\(off,len). len = 0 \/ off + len <= s.vs_alloca_next)
              (inst_mem_ranges inst s)`
    by simp_tac std_ss [inst_mem_below_frontier_def, inst_mem_ranges_def] >>
  pop_assum (fn th => rw[mem_corr_closed_def, mem_corr_def, raw_mem_ok_def,
                         th]) >>
  fs[]
QED

Theorem mem_corr_closed_static_mem_ok:
  mem_corr_closed (static_mem_ok eom)
Proof
  rw[mem_corr_closed_def, mem_corr_def, static_mem_ok_def] >> fs[]
QED

Theorem mem_corr_closed_lowered_mem_fact:
  mem_corr_closed (lowered_mem_fact eom)
Proof
  rw[mem_corr_closed_def, mem_corr_def, lowered_mem_fact_def,
     lowered_mem_ok_def] >> fs[]
QED
