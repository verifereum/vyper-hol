(* Compose the linked hash, selector, and optional output allocation. *)
Theory bodyMethodIdRuntimeSuffixMods
Ancestors
  bodyMethodIdRuntimeInputMods bodyMethodIdHashDynamicMods bodyMethodIdHashFixedMods
  bodyMethodIdScratchFrameMods bodyMethodIdSelectorMods bodyMethodIdOutputBufferMods
  bodyMethodIdRuntimePostsMods bodyMemBiMethodIdEndpoint bodyFullUnwrapRun
  bodyFullShadowBodyInv bodyFullPostsMods bodyInvSplit bodyPtrDefs exprSimHash
  exprSimMemDefs exprSimVVFrame exprLoweringProps emitHelperProps valueEncoding
  fragGasOriginPtrLoop storageCopyBodyPtr loweringPosts stateRelProj compileEnv freshWrites rich_list
  vyperAST vyperTypeSystem vyperValue vyperState vyperInterpreter vyperStorageTrace
  vyperStorageFootprint venomMemDefs venomState venomInst list finite_map pred_set words arithmetic
  bodyFullHashKeccakFixed[qualified,ignore_grammar]

Theorem method_horizon_extract[local]:
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==> P H) ==>
  P (storage_trace_horizon mid.storage_trace)
Proof
  simp[storage_trace_domain_def]
QED

Theorem method_clean_keep[local]:
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  sa.cs_next_var <= sk.cs_next_var /\
  (!q. not_fresh_at sk q ==> lookup_var q z = lookup_var q s /\
       FLOOKUP G' q = FLOOKUP G q /\ op_taint tn' (Var q) = op_taint tn (Var q)) /\
  tn'.t_mem SUBSET tn.t_mem ==>
  ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'
Proof
  strip_tac >> irule ghost_kept_at_clean_suffix >>
  qexistsl_tac [`G`, `tn`] >> simp[] >> metis_tac[not_fresh_at_mono]
QED

Theorem method_cursor_join[local]:
  k1.cs_current_insts = k0.cs_current_insts ++ emitted_insts k0 k1 /\
  k2.cs_current_insts = k1.cs_current_insts ++ emitted_insts k1 k2 /\
  run_inst_seq (emitted_insts k0 k1) s = OK raw /\
  u = (raw with vs_inst_idx := LENGTH k1.cs_current_insts) /\
  run_inst_seq (emitted_insts k1 k2) u = OK raw' /\
  z = (raw' with vs_inst_idx := LENGTH k2.cs_current_insts) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts k1 k2) ==>
  ?t. run_inst_seq (emitted_insts k0 k2) s = OK t /\
      z = (t with vs_inst_idx := LENGTH k2.cs_current_insts)
Proof
  strip_tac >> drule_all emitted_insts_append >> disch_then SUBST1_TAC >>
  irule run_inst_seq_cursor_append >> metis_tac[]
QED

Theorem method_selector_layout[local]:
  emit_op SHR [Lit 224w; hash] sh = (sel,sn) /\
  emit_op SHL [Lit 224w; sel] sn = (word,sp) ==>
  sp.cs_current_insts = sh.cs_current_insts ++ emitted_insts sh sp /\
  sh.cs_next_var <= sp.cs_next_var /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sh sp)
Proof
  strip_tac >>
  qpat_assum `emit_op SHR _ _ = _` (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
  qpat_assum `emit_op SHL _ _ = _` (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
  `?xs ys. sn.cs_current_insts = sh.cs_current_insts ++ [xs] /\
    sp.cs_current_insts = sn.cs_current_insts ++ [ys] /\
    ~is_terminator xs.inst_opcode /\ ~is_terminator ys.inst_opcode` by
    (qexistsl_tac [`mk_inst sh.cs_next_id SHR [Lit 224w;hash] [STRING #"%" (toString sh.cs_next_var)]`,
                   `mk_inst sn.cs_next_id SHL [Lit 224w;sel] [STRING #"%" (toString sn.cs_next_var)]`] >>
     asm_rewrite_tac[] >> simp[mk_inst_def, is_terminator_def]) >>
  `sh.cs_next_var <= sp.cs_next_var` by decide_tac >>
  `sp.cs_current_insts = sh.cs_current_insts ++ [xs;ys]` by
    (qpat_assum `sp.cs_current_insts = sn.cs_current_insts ++ [ys]`
       (once_rewrite_tac o single) >>
     qpat_assum `sn.cs_current_insts = sh.cs_current_insts ++ [xs]`
       (once_rewrite_tac o single) >>
     pure_once_rewrite_tac[GSYM APPEND_ASSOC] >> simp[]) >>
  `emitted_insts sh sp = [xs;ys]` by
    (pure_rewrite_tac[emitted_insts_def] >> pop_assum (once_rewrite_tac o single) >>
     simp[DROP_LENGTH_APPEND]) >>
  asm_rewrite_tac[EVERY_DEF] >> BETA_TAC >> asm_rewrite_tac[]
QED
