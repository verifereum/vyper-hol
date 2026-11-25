(* Constructor-free deployment executes the installed three-instruction entry. *)
Theory linkedEmptyDeployTarget
Ancestors
  linkedEmptyDeployCode simpleDeployRaw ctorDeployMemoryRunMemNoCtor
  vyperCompiler venomExecSemantics venomInst venomState fragGasPathMem
  memSafeRun ptrDiscipline finite_map rich_list list words arithmetic

Theorem linked_empty_deploy_target:
  lower_vyper_deploy_unit_mods mods exps rp runtime_bc = SOME unit /\
  classify_functions_unit mods exps = (exts,ints,fb,NONE,imp_ctors) /\
  vs.vs_allocas = FEMPTY /\ ~vs.vs_halted /\
  vs.vs_alloca_next = imm_len_mods mods /\
  LENGTH runtime_bc + imm_len_mods mods < dimword (:256) /\ off < dimword (:256) /\
  FLOOKUP vs.vs_labels "runtime_begin" = SOME (n2w off) /\
  DROP off vs.vs_code = runtime_bc ==>
  ?fn post.
    unit.cu_context.ctx_entry = SOME "__deploy" /\
    venomInst$lookup_function "__deploy" unit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME "__deploy" /\ ~ctx_has_dalloca unit.cu_context /\
    run_context 1 unit.cu_context vs = Halt post /\
    post.vs_returndata = runtime_bc ++ REPLICATE (imm_len_mods mods) 0w /\
    post.vs_accounts = vs.vs_accounts /\ post.vs_transient = vs.vs_transient /\
    post.vs_logs = vs.vs_logs /\ post.vs_pending_deletions = vs.vs_pending_deletions /\
    post.vs_requests = vs.vs_requests /\
    gas_path_mem unit.cu_context fn
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>)
      0 (Halt post) /\
    (!fuel. mem_safe_blocks fuel unit.cu_context fn
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>)) /\
    (!D fuel. ptr_safe_blocks D (imm_len_mods mods) fuel unit.cu_context fn
      [] FEMPTY entry_taint
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all lower_vyper_deploy_unit_no_ctor_shape_mods >>
  disch_then assume_tac >>
  qabbrev_tac `bs = runtime_bc ++ REPLICATE (imm_len_mods mods) (0w:word8)` >>
  `LENGTH bs = LENGTH runtime_bc + imm_len_mods mods` by simp[Abbr `bs`] >>
  `TAKE (LENGTH bs) (DROP off vs.vs_code ++ REPLICATE (LENGTH bs) 0w) = bs` by
    (qpat_assum `DROP off vs.vs_code = runtime_bc` (PURE_REWRITE_TAC o single) >>
     simp[Abbr `bs`, TAKE_APPEND, TAKE_LENGTH_TOO_LONG] >>
     simp[LIST_EQ_REWRITE, LENGTH_TAKE, EL_TAKE, EL_REPLICATE]) >>
  qabbrev_tac `fn = mk_raw_function "__deploy" [<|bb_label := "__deploy";
    bb_instructions :=
      [mk_inst 0 ALLOCA [Lit (n2w (LENGTH bs))] ["%0"];
       mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit (n2w (LENGTH bs))] [];
       mk_inst 2 RETURN [Var "%0"; Lit (n2w (LENGTH bs))] []]|>]` >>
  `unit.cu_context = install_immutable_reservation (imm_len_mods mods)
      (mk_venom_context [fn] (SOME "__deploy"))` by
    simp[Abbr `fn`] >>
  `unit.cu_context.ctx_entry = SOME "__deploy" /\
    lookup_function "__deploy" unit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME "__deploy"` by
    simp[Abbr `fn`, install_immutable_reservation_def, mk_venom_context_def,
         lookup_function_def, FIND_def, INDEX_FIND_def, mk_raw_function_def,
         fn_entry_label_def, entry_block_def] >>
  `~ctx_has_dalloca unit.cu_context` by
    simp[ctx_has_dalloca_def, install_immutable_reservation_def, mk_venom_context_def,
         mk_raw_function_def, fn_insts_def, fn_insts_blocks_def,
         combinTheory.o_DEF, Abbr `fn`, mk_inst_def] >>
  `vs.vs_alloca_next < dimword (:256)` by decide_tac >>
  mp_tac (Q.INST [`ctx` |-> `unit.cu_context`, `imm` |-> `imm_len_mods mods`,
      `vs` |-> `vs`, `fn` |-> `fn`, `bs` |-> `bs`, `off` |-> `off`]
    (SPEC_ALL simple_deploy_raw_execution)) >>
  impl_tac >- simp[Abbr `fn`] >>
  disch_then (qx_choose_then `post` strip_assume_tac) >>
  qexistsl_tac [`fn`, `post`] >>
  qunabbrev_tac `bs` >> asm_rewrite_tac[] >>
  gen_tac >>
  simp[Abbr `fn`] >>
  irule simple_deploy_entry_mem_safe >>
  simp[]
QED
