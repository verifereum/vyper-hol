(* The selector prefix of a linked entry ends before its argument checks. *)
Theory linkedLinearDispatchPath
Ancestors
  sourceUnitExecutionMods e2eModsDefs e2eDefs loweringStateRelDefs
  entryPrefixPtr entryDispatchPtr entryDispatchProps acceptedContextPhi
  moduleLoweringProps fragGasOriginPtr
  fragExec actualEntryAllocationFrame vyperLoweringCorrect vyperCompiler
  ptrDiscipline venomState venomInst venomWf venomInstIdsProps
  compileEnv finite_map list words
Theorem linked_linear_dispatch_entry_path:
  lowering_context_ok ctx /\
  ctx.ctx_entry = SOME "__entry" /\
  venomInst$lookup_function "__entry" ctx.ctx_functions = SOME fn /\
  call_tx_well_typed tx /\ initial_venom_state_rel_mods mods am tx vs /\
  compile_selector_dispatch_linear sels fl ds = ((),de) /\
  fn_has_code ds de fn /\
  EVERY (\(sel,lbl). sel < 2 ** 32) sels /\
  ds.cs_current_bb = "__entry" /\ ds.cs_current_insts = [] /\ ds.cs_next_var = 0 ==>
  ?s G tn.
    entry_prov fn
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                 vs_inst_idx := 0|>) FEMPTY = FEMPTY /\
    entry_taint_vars fn
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                 vs_inst_idx := 0|>) entry_taint = entry_taint /\
    (!D explicit. gas_origin_ptr_path (D,0,explicit,ctx,fn,[])
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                 vs_inst_idx := 0|>,FEMPTY,entry_taint) [] (OK s,G,tn)) /\
    vars_pc_only vs s /\ fresh_vars_wrt de s /\ ~s.vs_halted /\
    s.vs_current_bb = linear_dispatch_target vs.vs_call_ctx.cc_calldata sels fl /\
    s.vs_inst_idx = 0 /\ s.vs_call_ctx = vs.vs_call_ctx /\
    LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\ allocas_from 0 s /\
    allocas_below_fmp s /\
    tn.t_mem = {} /\ tn.t_stor = {} /\ tn.t_trans = {} /\ tn.t_imm = {}
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `ss =
    vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>` >>
  `LENGTH ss.vs_call_ctx.cc_calldata < dimword (:256)` by
    (simp[Abbr `ss`] >>
     gvs[initial_venom_state_rel_mods_def, venom_env_rel_def] >>
     drule_all_then ACCEPT_TAC call_ctx_rel_calldata_length) >>
  `fresh_vars_wrt ds ss /\ ~ss.vs_halted /\ allocas_from 0 ss /\
   allocas_below_fmp ss` by
    gvs[Abbr `ss`, initial_venom_state_rel_mods_def, fresh_vars_wrt_def,
        allocas_from_def, allocas_below_fmp_def] >>
  `!bb. lookup_block
      (linear_dispatch_target ss.vs_call_ctx.cc_calldata sels fl)
      fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >>
     `MEM fn ctx.ctx_functions` by (drule_then ACCEPT_TAC lookup_function_MEM) >>
     drule_all_then ACCEPT_TAC lowering_context_ok_block_phi) >>
  mp_tac (Q.INST [`selectors` |-> `sels`, `fallback` |-> `fl`,
     `st` |-> `ds`, `st'` |-> `de`, `ss` |-> `ss`,
     `ctx` |-> `ctx`, `fn` |-> `fn`, `lo` |-> `0`,
     `PG` |-> `[]`, `G` |-> `FEMPTY`, `tn` |-> `entry_taint`]
     (SPEC_ALL compile_selector_dispatch_linear_ptr_endpoint)) >>
  (impl_tac >- simp[Abbr `ss`]) >>
  disch_then (qx_choosel_then [`s`,`G`,`tn`] strip_assume_tac) >>
  drule_all compile_selector_dispatch_linear_layout >> strip_tac >>
  `entry_prov fn ss FEMPTY = FEMPTY /\
   entry_taint_vars fn ss entry_taint = entry_taint` by
    (Cases_on `b0.bb_instructions` >>
     gvs[get_instruction_def, mk_inst_def, entry_prov_def, entry_taint_vars_def,
         phis_prov_def, phis_taint_def, Abbr `ss`]) >>
  `vars_pc_only vs s` by
    (irule vars_pc_only_trans >> qexists_tac `ss` >>
     simp[Abbr `ss`, vars_pc_only_def]) >>
  `s.vs_call_ctx = ss.vs_call_ctx` by
    (qpat_assum `vars_pc_only ss s` (ACCEPT_TAC o cj 1 o
      MATCH_MP vars_pc_only_fields)) >>
  `s.vs_allocas = FEMPTY` by
    (drule vars_pc_only_allocas >> simp[Abbr `ss`] >>
     fs[initial_venom_state_rel_mods_def]) >>
  qexistsl_tac [`s`,`G`,`tn`] >>
  fs[Abbr `ss`, allocas_from_def, allocas_below_fmp_def, entry_taint_def] >>
  qpat_assum `vars_pc_only vs s`
    (mp_tac o Q.AP_TERM `\st. (st.vs_initial_fmp,st.vs_fmp)` o
     REWRITE_RULE [vars_pc_only_def]) >> simp[]
QED
