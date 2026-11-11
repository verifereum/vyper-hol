(* Actual body boundary synchronized with the invoked function's PHI phase. *)
Theory bodyIntCallPackageBoundary
Ancestors
  bodyIntCallPackageBodyCode bodyIntCallPackageControl bodyIntCallEntryPhi
  bodyIntCallInvokeEntry bodySim intCallCallee compileEnv fragExec venomInst
  loweringPosts moduleLowering

Theorem selected_internal_body_boundary:
  body_inv tops ctx caller_ce cx /\
  lookup_function label ctx.ctx_functions = SOME callee /\
  new_block label before = (old,entry) /\
  compile_internal_function ce params has_rb F nkey trans view ctor ilen
    ss rt entry = ((),final) /\ fn_has_code entry final callee /\
  setup_callee callee argv caller = SOME setup /\
  lookup_block setup.vs_current_bb callee.fn_blocks = SOME first /\
  eval_phis setup first.bb_instructions = OK phi_state /\
  entered = phi_state with vs_inst_idx :=
    phi_prefix_length first.bb_instructions ==>
  ?ce2 pc imm body_start body_env body_end.
    compile_internal_function_entry ce params has_rb ctor ilen rt entry =
      ((ce2,pc,imm),body_start) /\
    stmts_env (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>)
      NoLoop (case rt of SOME ty => ty | NONE => BaseT BoolT) ss body_start =
      (body_env,body_end) /\
    (if block_is_terminated body_end then ((),body_end)
     else case rt of NONE => emit_inst RET [pc] [] body_end
                   | SOME ty => emit_inst INVALID [] [] body_end) = ((),final) /\
    fn_has_code entry body_start callee /\
    fn_has_code body_start body_end callee /\ fn_has_code body_end final callee /\
    entry.cs_current_insts = [] /\
    entry.cs_current_bb = (HD callee.fn_blocks).bb_label /\ entered = setup
Proof
  strip_tac >> drule_all internal_function_body_code >> strip_tac >>
  drule_all body_inv_function_entry_label >> strip_tac >>
  `entry.cs_current_insts = [] /\
   entry.cs_current_bb = (HD callee.fn_blocks).bb_label` by
    gvs[new_block_def] >>
  `entered = setup` by (irule internal_entry_phi_landing >> metis_tac[]) >>
  goal_assum (drule_at (Pat `compile_internal_function_entry _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `stmts_env _ _ _ _ _ = _`)) >> simp[]
QED
