(* Exact list interface for exec_block, including instruction indices. *)
Theory dftIndexedExec
Ancestors
  venomExecSemantics venomInst venomState list rich_list arithmetic

(* Unlike run_insts, this evaluator accounts for the index after each
   successful non-terminator, and for early termination. *)
Definition dft_exec_suffix_def:
  dft_exec_suffix fuel ctx [] s = Error "block not terminated" /\
  dft_exec_suffix fuel ctx (i::is) s =
    case step_inst fuel ctx i s of
      OK s' =>
        if is_terminator i.inst_opcode then
          if s'.vs_halted then Halt s' else OK s'
        else dft_exec_suffix fuel ctx is
               (s' with vs_inst_idx := SUC s.vs_inst_idx)
    | other => other
End

Theorem dft_exec_suffix_boundary:
  !is fuel ctx bb s.
    DROP s.vs_inst_idx bb.bb_instructions = is ==>
    exec_block fuel ctx bb s = dft_exec_suffix fuel ctx is s
Proof
  Induct_on `is`
  >- (rpt strip_tac >>
      `LENGTH bb.bb_instructions <= s.vs_inst_idx` by
        (qpat_x_assum `DROP _ _ = []` (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
         simp[LENGTH_DROP]) >>
      once_rewrite_tac[exec_block_def] >>
      simp[get_instruction_def, dft_exec_suffix_def]) >>
  rpt strip_tac >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (qpat_x_assum `DROP _ _ = _::_` (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
     simp[LENGTH_DROP]) >>
  `EL s.vs_inst_idx bb.bb_instructions = h` by
    (qpat_x_assum `DROP _ _ = _::_` (mp_tac o AP_TERM ``EL 0:instruction list -> instruction``) >>
     simp[EL_DROP]) >>
  once_rewrite_tac[exec_block_def] >>
  simp[get_instruction_def, dft_exec_suffix_def] >>
  Cases_on `step_inst fuel ctx h s` >> simp[] >>
  IF_CASES_TAC >- simp[] >> simp[] >>
  first_x_assum irule >> simp[] >>
  qpat_x_assum `DROP _ _ = _::_` (mp_tac o AP_TERM ``DROP 1:instruction list -> instruction list``) >>
  simp[DROP_DROP, ADD1]
QED

(* Probe the exact Halt state, not just an observational state relation. *)
Definition dft_probe_stop_fn_def:
  dft_probe_stop_fn = mk_raw_function "callee"
    [<|bb_label := "entry";
       bb_instructions := [mk_inst 3 STOP [] []]|>]
End

Theorem dft_probe_stop_run:
  !ctx s.
    s.vs_current_bb = "entry" ==>
    run_blocks 1 ctx dft_probe_stop_fn s =
      Halt (halt_state (s with <|vs_inst_idx := 0; vs_returndata := []|>))
Proof
  rpt strip_tac >>
  simp[Once run_blocks_def, dft_probe_stop_fn_def,
       mk_raw_function_def, lookup_block_def, FIND_def, INDEX_FIND_def] >>
  simp[run_block_def, eval_phis_def, phi_prefix_length_def, mk_inst_def] >>
  simp[Once exec_block_def, get_instruction_def] >>
  simp[Once step_inst_def] >>
  simp[step_inst_base_def]
QED

Theorem dft_probe_invoke_halt:
  !s.
    dft_exec_suffix 1 (mk_venom_context [dft_probe_stop_fn] NONE)
      [mk_inst 0 ASSIGN [Lit 7w] ["x"];
       mk_inst 1 INVOKE [Label "callee"] [];
       mk_inst 2 STOP [] []] s =
    dft_exec_suffix 1 (mk_venom_context [dft_probe_stop_fn] NONE)
      [mk_inst 1 INVOKE [Label "callee"] [];
       mk_inst 0 ASSIGN [Lit 7w] ["x"];
       mk_inst 2 STOP [] []] s
Proof
  gen_tac >>
  simp[mk_inst_def] >>
  simp[Once dft_exec_suffix_def] >>
  simp[Once step_inst_def] >>
  simp[Once step_inst_base_def, eval_operand_def] >>
  simp[is_terminator_def] >>
  simp[dft_exec_suffix_def] >>
  simp[step_inst_def, decode_invoke_def] >>
  simp[mk_venom_context_def, lookup_function_def, FIND_def, INDEX_FIND_def,
       dft_probe_stop_fn_def, mk_raw_function_def] >>
  simp[eval_operands_def, setup_callee_def, update_var_def] >>
  simp[SRULE [dft_probe_stop_fn_def, mk_raw_function_def] dft_probe_stop_run]
QED

(* One step with an explicit continuation; not another recursive evaluator. *)
Definition dft_exec_cons_def:
  dft_exec_cons fuel ctx i k s =
    case step_inst fuel ctx i s of
      OK t => if is_terminator i.inst_opcode then
                if t.vs_halted then Halt t else OK t
              else k (t with vs_inst_idx := SUC s.vs_inst_idx)
    | other => other
End

Theorem dft_exec_suffix_cons:
  dft_exec_suffix f C (i::is) s =
    dft_exec_cons f C i (dft_exec_suffix f C is) s
Proof
  simp[dft_exec_suffix_def, dft_exec_cons_def]
QED

Theorem dft_exec_suffix_append:
  !xs ys f C s.
    dft_exec_suffix f C (xs ++ ys) s =
      FOLDR (dft_exec_cons f C) (dft_exec_suffix f C ys) xs s
Proof
  Induct >> simp[dft_exec_suffix_cons, dft_exec_cons_def]
QED

Theorem dft_exec_suffix_prefix_cong:
  (!s. dft_exec_suffix f C xs s = dft_exec_suffix f C ys s) ==>
  !s. dft_exec_suffix f C (pre ++ xs) s =
      dft_exec_suffix f C (pre ++ ys) s
Proof
  strip_tac >>
  `dft_exec_suffix f C xs = dft_exec_suffix f C ys` by simp[FUN_EQ_THM] >>
  simp[dft_exec_suffix_append]
QED

Theorem dft_exec_suffix_swap_lift:
  (!s. dft_exec_suffix f C (x::y::tail) s =
       dft_exec_suffix f C (y::x::tail) s) ==>
  !s. dft_exec_suffix f C (pre ++ x::y::tail) s =
      dft_exec_suffix f C (pre ++ y::x::tail) s
Proof
  strip_tac >> irule dft_exec_suffix_prefix_cong >> first_assum ACCEPT_TAC
QED

Theorem dft_exec_cons_ok:
  ~is_terminator i.inst_opcode /\ step_inst f C i s = OK t ==>
  dft_exec_cons f C i k s = k (t with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  simp[dft_exec_cons_def]
QED

Definition dft_probe_revert_fn_def:
  dft_probe_revert_fn = mk_raw_function "callee"
    [<|bb_label := "entry";
       bb_instructions := [mk_inst 3 REVERT [Lit 0w; Lit 0w] []]|>]
End

Theorem dft_probe_revert_run:
  !ctx s.
    s.vs_current_bb = "entry" ==>
    ?t. run_blocks 1 ctx dft_probe_revert_fn s = Abort Revert_abort t
Proof
  rpt strip_tac >>
  simp[Once run_blocks_def, dft_probe_revert_fn_def,
       mk_raw_function_def, lookup_block_def, FIND_def, INDEX_FIND_def] >>
  simp[eval_phis_def, phi_prefix_length_def, mk_inst_def] >>
  simp[Once exec_block_def, get_instruction_def] >>
  simp[Once step_inst_def] >>
  simp[step_inst_base_def, eval_operand_def]
QED

Theorem dft_probe_invoke_revert:
  !s.
    (?t. dft_exec_suffix 1 (mk_venom_context [dft_probe_revert_fn] NONE)
      [mk_inst 0 ASSIGN [Lit 7w] ["x"];
       mk_inst 1 INVOKE [Label "callee"] [];
       mk_inst 2 STOP [] []] s = Abort Revert_abort t) /\
    (?t. dft_exec_suffix 1 (mk_venom_context [dft_probe_revert_fn] NONE)
      [mk_inst 1 INVOKE [Label "callee"] [];
       mk_inst 0 ASSIGN [Lit 7w] ["x"];
       mk_inst 2 STOP [] []] s = Abort Revert_abort t)
Proof
  gen_tac >>
  simp[mk_inst_def] >>
  simp[Once dft_exec_suffix_def] >>
  simp[Once step_inst_def] >>
  simp[Once step_inst_base_def, eval_operand_def] >>
  simp[is_terminator_def] >>
  simp[dft_exec_suffix_def] >>
  simp[step_inst_def, decode_invoke_def] >>
  simp[mk_venom_context_def, lookup_function_def, FIND_def, INDEX_FIND_def,
       dft_probe_revert_fn_def, mk_raw_function_def] >>
  simp[eval_operands_def, setup_callee_def, update_var_def] >>
  qmatch_goalsub_abbrev_tac `run_blocks 1 ctx fn st` >>
  `?t. run_blocks 1 ctx fn st = Abort Revert_abort t` by
    (simp[Abbr `fn`] >>
     irule (SRULE [dft_probe_revert_fn_def, mk_raw_function_def]
              dft_probe_revert_run) >>
     simp[Abbr `st`]) >>
  gvs[]
QED
