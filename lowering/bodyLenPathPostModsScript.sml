(* A linked Len post at the endpoint of an already checked read-only path. *)
Theory bodyLenPathPostMods
Ancestors
  bodyLenVvPostMods bodyFullPostsMods bodyFullUnwrapRun
  bodyForRangeScalarFrameMods bodyPtrSignedConvertSourceFrame
  bodyFullHashKeccakFixed exprSimUnwrap exprSimMemDefs freshWrites
  loweringPosts loweringStateRelDefs bodyPtrDefs fragGasOriginPtr
  allocaHistory compileEnv vyperInterpreter vyperState venomState finite_map list

Theorem len_path_post_mods:
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv vv t /\
  alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK z,G2,tn2) /\
  eval_operand op z = SOME (n2w n) /\ op_taint tn2 op = {} /\ op_prov G2 op = NONE /\
  ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
  z.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (alloca_history func t ==> alloca_history func z) /\
  z = t with <|vs_vars := z.vs_vars; vs_inst_idx := z.vs_inst_idx|> /\
  (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x t /\
    FLOOKUP G2 x = FLOOKUP G x /\ op_taint tn2 (Var x) = op_taint tn (Var x)) /\
  tn2.t_mem = tn.t_mem /\ tn2.t_stor = tn.t_stor /\
  tn2.t_trans = tn.t_trans /\ tn2.t_imm = tn.t_imm ==>
  gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK z,G2,tn2) /\
  expr_post_mods H ctx func cenv cx (Builtin (BaseT (UintT 256)) Len [e])
    es sa sb s0 ee (IntV (&n)) op z /\
  expr_store_bound cx (BaseT (UintT 256)) (IntV (&n)) op z /\
  z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
  s0.vs_alloca_next <= z.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G2 tn2 z /\
  ptr_val_ok cx (BaseT (UintT 256)) (IntV (&n)) op G2 tn2 z /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2
Proof
  strip_tac >>
  qpat_x_assum `z = t with <|vs_vars := _; vs_inst_idx := _|>` (mk_asm "readonly") >>
  `z.vs_memory = t.vs_memory /\ z.vs_allocas = t.vs_allocas /\
   z.vs_alloca_next = t.vs_alloca_next /\ z.vs_data_section = t.vs_data_section /\
   z.vs_call_ctx = t.vs_call_ctx /\ z.vs_accounts = t.vs_accounts /\
   z.vs_transient = t.vs_transient /\ z.vs_immutables = t.vs_immutables` by
    (asm "readonly" (mp_tac o SIMP_RULE (srw_ss()) [venom_state_component_equality]) >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx ee t /\ immutable_frame_mods func cenv cx ee t` by
    fs[vv_post_mods_def] >>
  `stmt_state_rel H ctx func cenv cx ee z` by
    (irule stmt_state_rel_readonly_vars_pc >> qexistsl_tac [`t`,`sm`] >>
     rpt conj_tac >> (asm "readonly" ACCEPT_TAC ORELSE simp[])) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ z`
      (mp_tac o MATCH_MP stmt_state_rel_allocas_below_fmp) >> simp[]) >>
  `expr_post_mods H ctx func cenv cx (Builtin (BaseT (UintT 256)) Len [e])
      es sa sb s0 ee (IntV (&n)) op z` by
    (pure_rewrite_tac[expr_post_mods_def] >> conj_tac
     >- (irule expr_post_of_vv_post_stack >> qexists_tac `BaseT (UintT 256)` >>
         irule len_vv_post_load_mods >> simp[] >> qexistsl_tac [`t`,`sm`,`tv`,`vv`] >> simp[]) >>
     irule immutable_frame_mods_exterior_frame >> qexistsl_tac [`ee`,`t`,`sm`] >> simp[]) >>
  `ghost_inv_at_mods (DF H) lo d cenv cx ee G2 tn2 z` by
    (irule ghost_inv_at_mods_exterior_frame >> qexistsl_tac [`G`,`ee`,`t`,`sm`,`tn`] >> simp[]) >>
  simp[expr_store_bound_word, ptr_val_ok_def, is_word_type_def] >>
  irule ghost_kept_at_clean_suffix >> qexistsl_tac [`G`,`tn`] >>
  simp[] >> rpt strip_tac >>
  `not_fresh_at sm x` by (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  simp[]
QED
