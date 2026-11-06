(* Code and control boundary for the encoder's allocation prefix. *)
Theory revertReasonPrefixCodePtr
Ancestors
  revertReasonPrefixBoundaryPtr revertReasonPrefixPtr revertReasonPrefixFramePtr
  revertReasonRuns revertReasonLayout fragExec context compileEnv
  bodyPtrDefs ghostPcTransportPtr entrySinkExtraction exprLoweringProps
  venomInst venomState words arithmetic list rich_list finite_map

Theorem revert_reason_prefix_code:
  fn_has_code sa sm fn /\ sm.cs_current_bb = sa.cs_current_bb /\
  sm.cs_current_insts = sa.cs_current_insts ++
    revert_reason_prefix sa.cs_next_id sa.cs_next_var ms ==>
  ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (revert_reason_prefix sa.cs_next_id sa.cs_next_var ms)
      (DROP (LENGTH sa.cs_current_insts) bb.bb_instructions) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (64+ms))]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
    MEM (mk_inst (sa.cs_next_id+3) ALLOCA [Lit (n2w ms)]
      [STRING #"%" (toString (sa.cs_next_var+2))]) (fn_insts fn)
Proof
  simp[fn_has_code_def] >> strip_tac >> gvs[IS_PREFIX_APPEND] >>
  simp[NoAsms, DROP_APPEND1] >> conj_tac >>
  irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
  simp[revert_reason_prefix_def]
QED

Theorem compile_revert_reason_prefix_code:
  compile_revert_with_reason cenv vv mt ms sa = ((),sb) /\ fn_has_code sa sb fn ==>
  ?sm sn op.
    unwrap_value cenv vv sm = (op,sn) /\
    fn_has_code sa sm fn /\ fn_has_code sm sn fn /\ fn_has_code sn sb fn /\
    same_blocks sa sm /\ same_blocks sn sb /\
    cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn sb /\
    sm.cs_next_var = sa.cs_next_var+3 /\ sm.cs_next_id = sa.cs_next_id+4 /\
    sm.cs_current_insts = sa.cs_current_insts ++
      revert_reason_prefix sa.cs_next_id sa.cs_next_var ms /\
    sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
    sb.cs_current_insts = sn.cs_current_insts ++
      (revert_reason_copy sn.cs_next_id sn.cs_next_var
        (Var (STRING #"%" (toString (sa.cs_next_var+2)))) op ++
       revert_reason_suffix sn.cs_next_id sn.cs_next_var
        (Var (STRING #"%" (toString sa.cs_next_var)))
        (Var (STRING #"%" (toString (sa.cs_next_var+1))))
        (Var (STRING #"%" (toString (sa.cs_next_var+2)))))
Proof
  strip_tac >> drule compile_revert_reason_chunks >> strip_tac >>
  `cs_extends sm sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sm fn /\ fn_has_code sm sb fn` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code sm sn fn /\ fn_has_code sn sb fn` by
    metis_tac[fn_has_code_split] >>
  qexistsl_tac [`sm`,`sn`,`op`] >> asm_rewrite_tac[]
QED

Theorem revert_reason_prefix_at_compile_endpoint_ptr:
  fn_has_code sa sm fn /\ sm.cs_current_bb = sa.cs_current_bb /\
  sm.cs_current_insts = sa.cs_current_insts ++
    revert_reason_prefix sa.cs_next_id sa.cs_next_var ms /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  (!k. k < 3 ==> not_local_ptr cenv es.scopes
    (STRING #"%" (toString (sa.cs_next_var+k)))) /\
  64+ms < dimword(:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    run_inst_seq (revert_reason_prefix sa.cs_next_id sa.cs_next_var ms) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn
      (revert_reason_prefix sa.cs_next_id sa.cs_next_var ms) s Gf tnf /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
      (OK (t with vs_inst_idx := s.vs_inst_idx+4)) /\
    ~(t with vs_inst_idx := s.vs_inst_idx+4).vs_halted /\
    (t with vs_inst_idx := s.vs_inst_idx+4).vs_current_bb = sm.cs_current_bb /\
    (t with vs_inst_idx := s.vs_inst_idx+4).vs_inst_idx = LENGTH sm.cs_current_insts /\
    stmt_state_rel ctx fn cenv cx es (t with vs_inst_idx := s.vs_inst_idx+4) /\
    ptr_covers Gf tnf (STRING #"%" (toString sa.cs_next_var))
      (t with vs_inst_idx := s.vs_inst_idx+4) (64+ms) /\
    ptr_covers Gf tnf (STRING #"%" (toString (sa.cs_next_var+1)))
      (t with vs_inst_idx := s.vs_inst_idx+4) (32+ms) /\
    ptr_covers Gf tnf (STRING #"%" (toString (sa.cs_next_var+2)))
      (t with vs_inst_idx := s.vs_inst_idx+4) ms
Proof
  strip_tac >> drule_all revert_reason_prefix_code >> strip_tac >>
  `?t. run_inst_seq (revert_reason_prefix sa.cs_next_id sa.cs_next_var ms) s = OK t`
    by metis_tac[revert_reason_prefix_run] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (revert_reason_prefix sa.cs_next_id sa.cs_next_var ms)
     (DROP s.vs_inst_idx bb.bb_instructions)` by asm_rewrite_tac[] >>
  drule_all revert_reason_prefix_checked_path >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  `!k. k < 2 ==> not_local_ptr cenv es.scopes
    (STRING #"%" (toString (sa.cs_next_var+k)))` by simp[] >>
  drule_all revert_reason_prefix_covers >> strip_tac >>
  drule_all revert_reason_prefix_state_rel >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (revert_reason_prefix sa.cs_next_id sa.cs_next_var ms)` by
    simp[NoAsms, revert_reason_prefix_def, mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >>
  simp[stmt_state_rel_inst_idx]
QED
