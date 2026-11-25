(* The exhausted Array takes the header comparison and the exit jump. *)
Theory bodyForArrayNilExitMods
Ancestors
  bodyForArrayControlMods bodyForArrayHeaderMods bodyForArrayTestPathMods
  bodyForRangeHeaderMods bodyForRangeScalarFrameMods bodyFullShared bodyMemoryDefs
  exprLoweringProps exprSimOperands stmtSimDefs stmtSimProps allocaHistory
  vyperStorageFootprint venomExecSemantics venomState venomInst ptrDiscipline
  finite_map fragGasOriginPtr fragExec loweringPosts compileEnv loweringStateRelDefs
  stmtSimAppendStorageCompose

val _ = Parse.hide "body";

Theorem for_array_nil_exit_mods:
  local_ptrs_reserved cenv sa /\ ~not_fresh_at sa dv /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  sa.cs_next_var <= sb.cs_next_var /\
  sb.cs_current_bb = exit_lbl /\ sb.cs_current_insts = [] /\
  lookup_block cond_lbl func.fn_blocks = SOME
    <|bb_label := cond_lbl; bb_instructions :=
      [mk_inst eid EQ [Var idx;len_op] [dv];
       mk_inst jid JNZ [Var dv; Label exit_lbl; Label body_lbl] []]|> ==>
  !es s G tn.
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      for_array_header_mods mods DF lo d ctx func cenv cx env id st0
        (es0,sa,s0,G0,tn0) (em,saExpr,saLen,u,tu) item
        vs (base_op,bw,len_op,idx) cond_lbl Route H [] es G tn s) ==>
    ?t G1 tn1. !H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK t,G1,tn1) /\
      for_array_done_mods DF lo d ctx func cenv cx lctx sa sb es0 s0 G0 tn0
        H (es with gas_obs := []) G1 tn1 t
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `u1 = update_var dv 1w s` >>
  qabbrev_tac `t = jump_to exit_lbl u1` >>
  qabbrev_tac `G1 = DRESTRICT G (COMPL {dv})` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (dv,{})` >>
  qexistsl [`t`,`G1`,`tn1`] >> qx_gen_tac `H` >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _` (drule_then assume_tac) >>
  `lookup_var idx s = eval_operand len_op s` by
    (drule for_array_control_nil_mods >> simp[]) >>
  qhdtm_x_assum `for_array_header_mods` mp_tac >>
  simp[for_array_header_mods_def] >> strip_tac >>
  conj_tac >- suspend "path" >>
  `!x. not_fresh_at sa x ==> x <> dv` by metis_tac[] >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> `x <> dv` by metis_tac[] >>
     simp[Abbr `G1`, Abbr `tn1`, Abbr `t`, Abbr `u1`,
          jump_to_def, update_var_def, op_taint_def,
          lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
  `tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
   tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm` by
    simp[Abbr `tn1`] >>
  `t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
   t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_inst_idx = 0 /\ t.vs_current_bb = sb.cs_current_bb /\ ~t.vs_halted /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables` by
    simp[Abbr `t`, Abbr `u1`, jump_to_def, update_var_def] >>
  `not_local_ptr cenv es.scopes dv` by
    (irule fresh_not_local_ptr >> qexists `sa` >> simp[]) >>
  simp[for_array_done_mods_def, stmt_lands_def, block_is_terminated_def,
       cenv_top_ext_refl] >>
  conj_tac >-
    (simp[Abbr `t`, Abbr `u1`, stmt_state_rel_jump_to] >>
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
  suspend "outer"
QED

Resume for_array_nil_exit_mods[path]:
  qmatch_asmsub_abbrev_tac `lookup_block cond_lbl func.fn_blocks = SOME bb` >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `get_instruction bb s.vs_inst_idx = SOME (mk_inst eid EQ [Var idx;len_op] [dv]) /\
   get_instruction bb (SUC s.vs_inst_idx) =
     SOME (mk_inst jid JNZ [Var dv;Label exit_lbl;Label body_lbl] [])` by
    simp[Abbr `bb`, get_instruction_def] >>
  `eval_operand (Var idx) s = SOME (n2w (LENGTH vs))` by
    simp[eval_operand_def, lookup_var_def] >>
  `op_prov G (Var idx) = NONE` by simp[op_prov_def] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by
    fs[for_array_outer_frame_mods_def,range_outer_frame_mods_def] >>
  drule_all for_array_eq_jnz_path_mods >>
  simp[Abbr `t`, Abbr `G1`, Abbr `tn1`, Abbr `u1`]
QED

Resume for_array_nil_exit_mods[buffer]:
  irule return_buf_frame_frame >>
  goal_assum (drule_at (Pat `return_buf_frame _ _ _ _`)) >> simp[]
QED

Resume for_array_nil_exit_mods[sep]:
  rewrite_tac [return_buf_sep_gas_obs] >>
  `!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) t` by
    (rpt strip_tac >> gvs[bodySimFullTheory.return_buf_sep_def, allocas_from_def] >>
     first_assum ACCEPT_TAC) >>
  irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >> simp[] >>
  goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  qexists `sa` >> simp[]
QED

Resume for_array_nil_exit_mods[outer]:
  qhdtm_x_assum `for_array_outer_frame_mods` mp_tac >>
  simp[for_array_outer_frame_mods_def,range_outer_frame_mods_def] >> strip_tac >>
  `alloca_frame cenv es0 sa s0 cenv es u1` by
    (simp[Abbr `u1`] >> irule alloca_frame_update_var >> simp[]) >>
  `alloca_frame cenv es0 sa s0 cenv es t` by
    (irule alloca_frame_same_state >> qexists `u1` >>
     simp[Abbr `t`, jump_to_def] >> simp[Abbr `u1`, update_var_def]) >>
  `alloca_history func t` by
    (irule alloca_history_jump >> simp[] >> qexists `s` >> simp[]) >>
  `allocas_below_fmp t = allocas_below_fmp s` by
    simp[Abbr `t`, Abbr `u1`, jump_to_def, update_var_def, allocas_below_fmp_def] >>
  simp[] >> first_assum ACCEPT_TAC
QED

Finalise for_array_nil_exit_mods
