(* The exhausted Range takes only the header comparison and the exit jump. *)
Theory bodyForRangeNilMods
Ancestors
  bodyForRangeHeaderMods bodyForRangeScalarFrameMods bodyFullShared
  bodyMemoryDefs bodyPtrBopInLiteralSuffix exprPtrUnwrapCondition
  fragGasSeqPtr decoderNavigationPtr instMemFrontier
  exprLoweringProps exprSimOperands exprSimWordArgs stmtSimDefs
  allocaHistory vyperStorageFootprint stmtSimAppendStorageCompose
  bodyFullShadowBodyInv venomExecSemantics venomExecProps venomInstProps
  venomInst venomState ptrDiscipline ptrSafeRun unitTransformDefs memSafeRun
  codegenRel contextCodegenRel finite_map fragGasOriginPtr fragExec
  loweringPosts compileEnv loweringStateRelDefs freshWrites bodySimFull stmtSimProps

val _ = Parse.hide "body";

Theorem range_nil_path[local]:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst eid EQ [Var cv; Var ev] [dv]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst jid JNZ [Var dv; Label exit_lbl; Label body_lbl] []) /\
  ~s.vs_halted /\ eval_operand (Var cv) s = SOME w /\
  eval_operand (Var ev) s = SOME w /\
  op_taint tn (Var cv) = {} /\ op_taint tn (Var ev) = {} /\
  op_prov G (Var cv) = NONE /\ op_prov G (Var ev) = NONE /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  let i = mk_inst eid EQ [Var cv; Var ev] [dv]; u = update_var dv 1w s in
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (jump_to exit_lbl u),step_prov PG G i u,step_taint i s u tn)
Proof
  strip_tac >> simp[] >>
  qabbrev_tac `i = mk_inst eid EQ [Var cv; Var ev] [dv]` >>
  qabbrev_tac `u = update_var dv 1w s` >>
  qabbrev_tac `v = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G1 = step_prov PG G i u` >>
  qabbrev_tac `tn1 = step_taint i s u tn` >>
  `step_inst_base i s = OK u` by
    simp[Abbr `i`, Abbr `u`, step_inst_base_opcode_eqs, mk_inst_def,
         exec_pure2_def, bool_to_word_def] >>
  `ptr_inst_ok D lo 0 ctx func G tn i s` by
    (simp[Abbr `i`, ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
          source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke, Abbr `u`, update_var_def] >>
     rpt strip_tac >> gvs[op_prov_def, FLOOKUP_DEF] >> metis_tac[]) >>
  `inst_mem_below_frontier i s /\ inst_dload_in_section i s /\
   i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
   (ctx_has_dalloca ctx ==> dalloca_no_wrap i s)` by
    simp[Abbr `i`, mk_inst_def, is_terminator_def, inst_mem_below_frontier_def,
         inst_dload_in_section_def, source_memory_read_ranges_def,
         source_memory_write_ranges_def] >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK v,G1,tn1)` by
    (drule_all straight_line_origin_ptr_edge >>
     simp[Abbr `v`, Abbr `G1`, Abbr `tn1`, Abbr `i`, mk_inst_def]) >>
  `tn1 = tn with t_var := tn.t_var |+ (dv,{})` by
    simp[Abbr `tn1`, Abbr `i`, Abbr `u`, membership_scalar_ghost_frame] >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (v,G1,tn1) []
      (OK (jump_to exit_lbl u),G1,tn1)` by
    (`lookup_block v.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb v.vs_inst_idx =
        SOME (mk_inst jid JNZ [Var dv; Label exit_lbl; Label body_lbl] []) /\
      ~v.vs_halted /\ eval_operand (Var dv) v = SOME 1w /\
      op_taint tn1 (Var dv) = {} /\ allocas_from lo v /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp v)` by
        simp[Abbr `v`, Abbr `u`, update_var_def, eval_operand_def,
             lookup_var_def, allocas_from_def, allocas_below_fmp_def,
             op_taint_def, FLOOKUP_UPDATE] >>
     drule_all decoderNavigationPtrTheory.jnz_origin_ptr_path >>
     simp[Abbr `v`, jump_to_def]) >>
  drule (cj 2 gas_origin_ptr_path_rules) >> disch_then drule >> simp[]
QED

Theorem range_nil_exit_mods:
  local_ptrs_reserved cenv sa /\ ~not_fresh_at sa dv /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  sb0.cs_next_var <= sb.cs_next_var /\
  sb.cs_current_bb = exit_lbl /\ sb.cs_current_insts = [] /\
  lookup_block cond_lbl func.fn_blocks = SOME
    <|bb_label := cond_lbl; bb_instructions :=
      [mk_inst eid EQ [Var cv; Var ev] [dv];
       mk_inst jid JNZ [Var dv; Label exit_lbl; Label body_lbl] []]|> ==>
  !es s G tn.
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      range_header_mods mods DF lo d ctx func cenv cx env id tyv st0
        sa sb0 es0 s0 G0 tn0 n1 n2 bound cond_lbl cv ev p aid sz w
        H [] es G tn s) ==>
    ?t G1 tn1. !H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G1,tn1) /\
      range_done_mods DF lo d ctx func cenv cx lctx sa sb es0 s0 G0 tn0
        H (es with gas_obs := []) G1 tn1 t
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `i = mk_inst eid EQ [Var cv; Var ev] [dv]` >>
  qabbrev_tac `u = update_var dv 1w s` >>
  qabbrev_tac `t = jump_to exit_lbl u` >>
  qabbrev_tac `G1 = step_prov PG G i u` >>
  qabbrev_tac `tn1 = step_taint i s u tn` >>
  qexistsl [`t`, `G1`, `tn1`] >> qx_gen_tac `H` >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _` (drule_then assume_tac) >>
  `lookup_var cv s = lookup_var ev s` by (drule range_header_test_mods >> simp[]) >>
  qhdtm_x_assum `range_header_mods` mp_tac >>
  simp[range_header_mods_def] >> strip_tac >>
  `allocas_from lo s` by fs[ghost_inv_at_mods_def] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by fs[range_outer_frame_mods_def] >>
  conj_asm1_tac >-
    (simp[Abbr `t`, Abbr `G1`, Abbr `tn1`, Abbr `u`, Abbr `i`] >>
     irule (SIMP_RULE (srw_ss()) [LET_THM] range_nil_path) >>
     simp[eval_operand_def, get_instruction_def] >>
     qexistsl [`body_lbl`, `jid`] >> simp[]) >>
  `!x. not_fresh_at sa x ==> x <> dv` by metis_tac[] >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> `x <> dv` by metis_tac[] >>
     simp[Abbr `G1`, Abbr `tn1`, Abbr `t`, Abbr `u`, Abbr `i`,
          SRULE [] copy_eq_jump_frames, jump_to_def, update_var_def,
          lookup_var_def, FLOOKUP_UPDATE]) >>
  `tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
   tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm` by
    simp[Abbr `tn1`, Abbr `u`, Abbr `i`, membership_scalar_ghost_frame] >>
  `t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
   t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_inst_idx = 0 /\ t.vs_current_bb = sb.cs_current_bb /\ ~t.vs_halted /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables` by
    simp[Abbr `t`, Abbr `u`, jump_to_def, update_var_def] >>
  `not_local_ptr cenv es.scopes dv` by
    (irule fresh_not_local_ptr >> qexists `sa` >> simp[]) >>
  simp[range_done_mods_def, stmt_lands_def, block_is_terminated_def,
       cenv_top_ext_refl] >>
  conj_tac >-
    (simp[Abbr `t`, Abbr `u`, stmt_state_rel_jump_to] >>
     irule stmt_state_rel_update_var >> simp[]) >>
  conj_tac >-
    (irule immutable_frame_mods_exterior_frame >>
     goal_assum (drule_at (Pat `immutable_frame_mods _ _ _ _ _`)) >>
     qexists `sa` >> simp[]) >>
  conj_tac >-
    (qpat_x_assum `storage_well_formed_on _ _ _` mp_tac >>
     simp[NoAsms, storage_well_formed_on_def, get_storage_gas_obs]) >>
  conj_tac >- suspend "buffer" >>
  conj_tac >- suspend "sep" >>
  conj_tac >-
    (irule ghost_inv_at_mods_exterior_frame >>
     goal_assum (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
     qexists `sa` >> simp[]) >>
  suspend "outer_frame"
QED

Resume range_nil_exit_mods[buffer]:
  Cases_on `d` >- fs[return_buf_frame_def] >>
  PairCases_on `x` >> fs[return_buf_frame_def] >>
  irule not_fresh_at_mono >> qexists_tac `sb0` >> simp[]
QED

Resume range_nil_exit_mods[sep]:
  rewrite_tac [return_buf_sep_gas_obs] >>
  `!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) t` by
    (rpt strip_tac >> gvs[return_buf_sep_def, allocas_from_def] >>
     first_assum ACCEPT_TAC) >>
  irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >> simp[] >>
  goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  qexists `sa` >> simp[]
QED

Resume range_nil_exit_mods[outer_frame]:
  qhdtm_x_assum `range_outer_frame_mods` mp_tac >>
  simp[range_outer_frame_mods_def] >> strip_tac >>
  `alloca_frame cenv es0 sa s0 cenv es u` by
    (simp[Abbr `u`] >> irule alloca_frame_update_var >> simp[]) >>
  `alloca_frame cenv es0 sa s0 cenv es t` by
    (irule alloca_frame_same_state >> qexists `u` >>
     simp[Abbr `t`, jump_to_def] >> simp[Abbr `u`, update_var_def]) >>
  `alloca_history func t` by
    (irule alloca_history_jump >> simp[] >> qexists `s` >> simp[]) >>
  `allocas_below_fmp t = allocas_below_fmp s` by
    simp[Abbr `t`, Abbr `u`, jump_to_def, update_var_def, allocas_below_fmp_def] >>
  simp[] >> first_assum ACCEPT_TAC
QED

Finalise range_nil_exit_mods
