(* TOP-LEVEL: entry-to-common execution and continuation composition.
   Initialization uses the fragment judgment, so it may contain branches,
   decoder loops and stateful internal calls. The jump preserves its effects.
   Decoder/expression simulation supplies the initialization fragment. *)
Theory externalEntryProps
Ancestors
  fragExec moduleLowering emitHelperProps exprLoweringProps
  venomExecSemantics venomExecProofs venomState venomInst
  compileEnv emitHelper list rich_list

Theorem run_from_jump_common:
  lookup_block ss.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb ss.vs_inst_idx =
    SOME (mk_inst id JMP [Label common] []) /\
  ~ss.vs_halted ==>
  run_from fuel ctx func ss =
    run_blocks fuel ctx func (jump_to common ss)
Proof
  simp[run_from_def, Once exec_block_def, step_inst_non_invoke,
       mk_inst_def, step_jmp_behavior, is_terminator_def, jump_to_def]
QED

Theorem jump_common_continuation:
  lookup_block ss.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb ss.vs_inst_idx =
    SOME (mk_inst id JMP [Label common] []) /\
  ~ss.vs_halted /\
  lookup_block common func.fn_blocks = SOME common_bb /\
  phi_prefix_length common_bb.bb_instructions = 0 ==>
  run_from (SUC fuel) ctx func ss =
    run_from fuel ctx func (jump_to common ss)
Proof
  strip_tac >> drule_all run_from_jump_common >> strip_tac >>
  mp_tac (Q.SPECL [`fuel`,`ctx`,`func`,`jump_to common ss`,`common_bb`]
    run_blocks_run_from_no_phi) >>
  simp[jump_to_def]
QED

Theorem compile_entry_point_kwargs_tail:
  compile_init_kwargs cenv descriptors offset k (Lit 0w) st = ((),initialized) ==>
  compile_entry_point_kwargs cenv descriptors offset k common st =
    emit_inst JMP [Label common] [] initialized
Proof
  simp[compile_entry_point_kwargs_def, comp_ignore_bind_def, comp_bind_def]
QED

Theorem emitted_jump_common_instruction:
  emit_inst JMP [Label common] [] initialized = ((),finished) /\
  fn_has_code initialized finished func ==>
  ?bb. lookup_block initialized.cs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH initialized.cs_current_insts) =
      SOME (mk_inst initialized.cs_next_id JMP [Label common] [])
Proof
  strip_tac >> drule emit_inst_extends >> strip_tac >>
  fs[fn_has_code_def] >>
  qpat_x_assum `isPREFIX _ _` mp_tac >>
  simp[IS_PREFIX_APPEND, get_instruction_def] >> strip_tac >>
  gvs[] >> PURE_REWRITE_TAC[GSYM APPEND_ASSOC] >> simp[EL_LENGTH_APPEND]
QED

(* This result uses the actual emitted jump in an enclosing function. Its
   target is the separately emitted common body, whose first instruction is
   not a PHI. It does not assemble an artificial standalone entry function. *)
Theorem compile_entry_point_kwargs_jump:
  compile_init_kwargs cenv descriptors offset k (Lit 0w) st = ((),initialized) /\
  compile_entry_point_kwargs cenv descriptors offset k common st = ((),finished) /\
  fn_has_code initialized finished func /\
  ss.vs_current_bb = initialized.cs_current_bb /\
  ss.vs_inst_idx = LENGTH initialized.cs_current_insts /\
  ~ss.vs_halted /\
  lookup_block common func.fn_blocks = SOME common_bb /\
  phi_prefix_length common_bb.bb_instructions = 0 ==>
  run_from (SUC fuel) ctx func ss =
    run_from fuel ctx func (jump_to common ss)
Proof
  strip_tac >>
  `emit_inst JMP [Label common] [] initialized = ((),finished)` by
    metis_tac[compile_entry_point_kwargs_tail] >>
  drule_all emitted_jump_common_instruction >> strip_tac >>
  irule jump_common_continuation >> simp[] >> metis_tac[]
QED

Theorem jump_common_preserves_initialized_state:
  (jump_to common ss).vs_vars = ss.vs_vars /\
  (jump_to common ss).vs_memory = ss.vs_memory /\
  (jump_to common ss).vs_accounts = ss.vs_accounts /\
  (jump_to common ss).vs_transient = ss.vs_transient /\
  (jump_to common ss).vs_logs = ss.vs_logs /\
  (jump_to common ss).vs_allocas = ss.vs_allocas /\
  (jump_to common ss).vs_alloca_next = ss.vs_alloca_next /\
  (jump_to common ss).vs_call_ctx = ss.vs_call_ctx
Proof
  simp[jump_to_def]
QED

(* Compose any proved initialization fragment with the real common-body
   continuation, starting in a non-halted state as frag_exec requires.
   R covers initialization exits; result_ok covers body exits. *)
Theorem compile_entry_point_kwargs_continuation:
  compile_init_kwargs cenv descriptors offset k (Lit 0w) st = ((),initialized) /\
  compile_entry_point_kwargs cenv descriptors offset k common st = ((),finished) /\
  cs_extends st initialized /\
  frag_exec ctx st initialized P Q R /\
  fn_has_code st finished func /\
  lookup_block common func.fn_blocks = SOME common_bb /\
  phi_prefix_length common_bb.bb_instructions = 0 /\
  P ss /\ ~ss.vs_halted /\ ss.vs_current_bb = st.cs_current_bb /\
  ss.vs_inst_idx = LENGTH st.cs_current_insts /\
  (!ss1. Q ss1 ==> ~ss1.vs_halted /\
    ?fuel r. run_from fuel ctx func (jump_to common ss1) = r /\
      exit_result r /\ result_ok r) ==>
  ?fuel r. run_from fuel ctx func ss = r /\ exit_result r /\ (R r \/ result_ok r)
Proof
  strip_tac >>
  `emit_inst JMP [Label common] [] initialized = ((),finished)` by
    metis_tac[compile_entry_point_kwargs_tail] >>
  `cs_extends initialized finished` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` mp_tac >>
  simp[frag_exec_def] >>
  disch_then (qspecl_then [`func`,`ss`] mp_tac) >> simp[] >> strip_tac
  >- (rename1 `Q ss1` >> first_x_assum drule >> strip_tac >>
      `run_from (SUC fuel) ctx func ss1 = r` by
        (drule_all compile_entry_point_kwargs_jump >> simp[]) >>
      `!e. r <> Error e` by metis_tac[exit_result_not_error] >>
      metis_tac[]) >>
  metis_tac[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
        List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("external entry theorem is not kernel closed: " ^ name)
  end) (DB.thms "externalEntryProps");
