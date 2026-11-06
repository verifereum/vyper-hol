Theory bodyPtrPrecompileBuiltinsStagedOutput
Ancestors bodyPtrPrecompileBuiltinsFullOutputFrame
          bodyPtrPrecompileBuiltinsRecoveryResidual bodyPtrPrecompileBuiltinsPrefixFrames
          bodyPtrPrecompileBuiltinsContinuationFrame
          exprSimPtrLiteralBuffer ghostPcTransportPtr fragGasPathPtr fragGasSeqPtr
          exprSimDefs exprSimProps compileEnv venomState venomInst venomExecSemantics
          rich_list list bodyPtrDefs wordArgsPtr stmtSimDeclPath exprSimWordArgs
          venomCallOracleDefs extCallOracle exprLoweringProps

(* Runtime effects and counted paths share the same staged endpoint. *)
Theorem arithmetic_staging_continuation:
  EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
    i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE) pre /\
  run_inst_seq pre s = OK t /\
  (!k. inst_seq_ptr D 0 ctx fn PG G tn pre
    (s with vs_inst_idx := k) Gf tnf) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (pre ++ post) (DROP s.vs_inst_idx bb.bb_instructions) /\
  u = t with vs_inst_idx := s.vs_inst_idx + LENGTH pre ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK u) /\
  ~u.vs_halted /\ lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX post (DROP u.vs_inst_idx bb.bb_instructions) /\
  u.vs_outcomes = s.vs_outcomes /\
  u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
  u.vs_transient = s.vs_transient /\
  tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm
Proof
  strip_tac >>
  `isPREFIX pre (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]) >>
  drule_all staging_counted_prefix >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) pre` by
    (gvs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i pre ==> _ \/ _` drule >> strip_tac >>
     gvs[is_terminator_def]) >>
  drule_all straightline_continuation_placement >> strip_tac >>
  drule_all staging_sequence_outcomes >> strip_tac >>
  drule_all staging_prefix_nonmemory_frames >> strip_tac >> gvs[]
QED

Theorem precompile_local_region_cursor[simp]:
  local_region cenv scopes (s with vs_inst_idx := k) name b sz <=>
  local_region cenv scopes s name b sz
Proof
  simp[local_region_def, lookup_var_def]
QED

(* All extent parameters remain in the same w2n normal form as the suffix
   interface.  u names the actual continuation, not an independent run. *)
Theorem staged_full_output_paths:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL
        [gas; Lit target; Var src; Lit insz; Var dst; Lit outsz];
      emit_void ASSERT [success]; return (Var dst) od) sm = (Var dst,sl) /\
  EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
    i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE) pre /\
  run_inst_seq pre s = OK t /\
  (!k. inst_seq_ptr D 0 ctx fn PG G tn pre
    (s with vs_inst_idx := k) Gf tnf) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (pre ++ emitted_insts sm sl) (DROP s.vs_inst_idx bb.bb_instructions) /\
  u = t with vs_inst_idx := s.vs_inst_idx + LENGTH pre /\
  not_fresh_at sm src /\ not_fresh_at sm dst /\
  eval_operand (Var src) t = SOME wi /\ eval_operand (Var dst) t = SOME wo /\
  computed_precompile (venom_call_request u target 0w wi insz T) /\
  ptr_covers Gf tnf src t (w2n insz) /\ ptr_covers Gf tnf dst t (w2n outsz) /\
  (!i. w2n wi <= i /\ i < w2n wi + w2n insz ==> i NOTIN tnf.t_mem) /\
  ~ctx_has_dalloca ctx /\
  tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
    (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
    (s.vs_transient s.vs_call_ctx.cc_address) /\
  ghost_inv d cenv cx es Gf tnf t /\ stmt_state_rel ctx fn cenv cx es t /\
  ghost_kept cenv es sf G tn s Gf tnf /\ wb_frame cenv es sf s t /\
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sf /\
  local_ptrs_reserved cenv sm /\ sf.cs_next_var <= sm.cs_next_var /\
  sf.cs_next_id <= sm.cs_next_id /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!name b sz. local_region cenv es.scopes t name b sz ==>
     regions_disjoint (w2n wo) (w2n outsz) b sz) /\
  (!aid b sz. aid < sf.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,sz) ==>
     regions_disjoint (w2n wo) (w2n outsz) b sz) /\
  (cenv.ce_is_ctor ==> !name tv iv off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
     regions_disjoint (w2n wo) (w2n outsz) off (type_memory_size tv)) ==>
  ?G2 tn2.
    (!data. precompile_result (venom_call_request u target 0w wi insz T).cr_target
        (venom_call_request u target 0w wi insz T).cr_data = SOME (SOME data) /\
      (?co rest. s.vs_outcomes = co::rest /\ co.co_success) /\
      w2n outsz <= LENGTH data ==>
      ?q. gas_path_ptr D 0 ctx fn PG G tn s 1 G2 tn2 (OK q) /\
        eval_operand (Var dst) q = SOME wo /\ q.vs_allocas = t.vs_allocas /\
        q.vs_memory = (write_memory_with_expansion (w2n wo) (TAKE (w2n outsz) data) u).vs_memory /\
        ptr_covers G2 tn2 dst q (w2n outsz) /\
        (!i. w2n wo <= i /\ i < w2n wo + w2n outsz ==> i NOTIN tn2.t_mem) /\
        ghost_inv d cenv cx (es with outcomes := SOME (DROP 1 s.vs_outcomes)) G2 tn2 q /\
        ghost_kept cenv es sf G tn s G2 tn2 /\
        stmt_state_rel ctx fn cenv cx (es with outcomes := SOME (DROP 1 s.vs_outcomes)) q /\
        wb_frame cenv es sf s q /\
        (!name b sz. local_region cenv es.scopes q name b sz ==>
          regions_disjoint (w2n wo) (w2n outsz) b sz)) /\
    ((precompile_result (venom_call_request u target 0w wi insz T).cr_target
        (venom_call_request u target 0w wi insz T).cr_data = SOME NONE \/
      s.vs_outcomes = [] \/ ?co rest. s.vs_outcomes = co::rest /\ ~co.co_success) ==>
      ?q n. gas_path_ptr D 0 ctx fn PG G tn s n G2 tn2 (Abort Revert_abort q))
Proof
  strip_tac >> drule_all arithmetic_staging_continuation >> strip_tac >>
  suspend "entry"
QED

Resume staged_full_output_paths[entry]:
  `eval_operand (Var src) u = SOME wi /\ eval_operand (Var dst) u = SOME wo /\
   ptr_covers Gf tnf src u (w2n insz) /\ ptr_covers Gf tnf dst u (w2n outsz) /\
   stmt_state_rel ctx fn cenv cx es u /\ wb_frame cenv es sf s u` by
    simp[stmt_state_rel_inst_idx, precompile_frame_cursor] >>
  `ghost_inv d cenv cx es Gf tnf u` by
    simp[SRULE [] (Q.INST [`gs` |-> `es.gas_obs`] literal_ptr_ghost_inv_normalize)] >>
  `local_ptrs_rel fn cenv es.scopes u` by
    (qpat_assum `stmt_state_rel ctx fn cenv cx es u` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[stmt_state_rel_def, state_rel_def]) >>
  `(!name b sz. local_region cenv es.scopes u name b sz ==>
     regions_disjoint (w2n wo) (w2n outsz) b sz) /\
   (!aid b sz. aid < sf.cs_next_id /\ FLOOKUP u.vs_allocas aid = SOME (b,sz) ==>
     regions_disjoint (w2n wo) (w2n outsz) b sz)` by
    (conj_tac
     >- (map_every qx_gen_tac [`name`,`b0`,`len`] >> strip_tac >>
         `local_region cenv es.scopes t name b0 len` by
           gvs[local_region_def, lookup_var_def] >> metis_tac[]) >>
     simp[] >> first_assum ACCEPT_TAC) >>
  `allocas_from 0 u /\
   tnf.t_stor SUBSET D.d_stor u.vs_call_ctx.cc_address
     (u.vs_accounts u.vs_call_ctx.cc_address).storage /\
   tnf.t_trans SUBSET D.d_trans u.vs_call_ctx.cc_address
     (u.vs_transient u.vs_call_ctx.cc_address)` by simp[] >>
  qpat_assum `_ sm = (Var dst,sl)`
    (mp_then Any drule_all computed_full_output_framed_paths) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  suspend "compose"
QED

Resume staged_full_output_paths[compose]:
  qexistsl [`G2`,`tn2`] >> reverse conj_tac
  >- (disch_tac >>
      qpat_x_assum `_ ==> ?q n j. _` mp_tac >>
      (impl_tac >- metis_tac[]) >> strip_tac >>
      drule_all gas_path_ptr_then >> strip_tac >>
      goal_assum (drule_at Any) >> simp[]) >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!data. _` (qspec_then `data` mp_tac) >>
  (impl_tac >- (simp[] >> qexistsl [`co`,`rest`] >> simp[])) >> strip_tac >>
  `sf.cs_next_var <= sf.cs_next_var /\ sf.cs_next_id <= sf.cs_next_id /\
   MAP FDOM es.scopes = MAP FDOM es.scopes` by simp[] >>
  drule_all ghost_kept_wb_trans >> strip_tac >>
  qpat_assum `wb_frame cenv es sf u q`
    (mp_then Any mp_tac (Q.INST [`es1` |-> `es`] wb_frame_local_regions)) >>
  disch_then drule_all >> strip_tac >>
  `!name b sz. local_region cenv es.scopes q name b sz ==>
      regions_disjoint (w2n wo) (w2n outsz) b sz` by metis_tac[] >>
  drule_all wb_frame_trans >> strip_tac >>
  drule_all gas_path_ptr_then >> strip_tac >>
  qpat_assum `u.vs_outcomes = s.vs_outcomes` (fn eq =>
    rule_assum_tac (REWRITE_RULE [eq])) >>
  `q.vs_allocas = t.vs_allocas` by simp[] >>
  qexists `q with vs_inst_idx := u.vs_inst_idx+3` >>
  conj_tac >- (fs[] >> first_assum ACCEPT_TAC) >>
  simp[NoAsms, stmt_state_rel_inst_idx, precompile_frame_cursor,
       SRULE [] (Q.INST [`gs` |-> `es.gas_obs`] literal_ptr_ghost_inv_normalize)] >>
  qpat_assum `!i. w2n wo <= i /\ i < w2n wo + w2n outsz ==> _`
    (assume_tac o SRULE [arithmeticTheory.ADD_COMM]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise staged_full_output_paths
