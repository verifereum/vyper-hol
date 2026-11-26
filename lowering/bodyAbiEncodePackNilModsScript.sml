(* Empty positional ABI arguments leave the physical endpoint unchanged. *)
Theory bodyAbiEncodePackNilMods
Ancestors
  bodyAbiEncodePackedPostMods bodyBranchCellFrameMods gasOutcomeFullPostMods
  vyperStorageFootprint exprSimWordArgs wordArgsPtr fragGasOriginPtr
  loweringStateRelDefs bodyInvSplit ptrDiscipline context bodyFullPostsMods
  bodyFullShadowBodyInv exprLowering exprLoweringProps compileEnv
  bodyWriteSubscriptSourceMods

Theorem abi_encode_pack_nil_mods:
  compile_abi_encode_args compile_expr cenv [] sa = (svs,sb) /\
  expr_sim_inv_mods mods cenv cx env es /\
  body_const_cells_agree_mods mods cx env es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s0 /\
       immutable_frame_mods func cenv cx es s0 /\
       storage_well_formed_on cx es (FST H) /\
       ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (eval_exprs cx []) (es,s0,G0,tn0)
    (abi_encode_packed_post_mods mods DF lo d ctx func cenv cx env
      [] svs sa sb es s0 G0 tn0) R
Proof
  simp[compile_abi_encode_args_def, compile_ext_call_args_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`G0`, `es`, `INL []`, `s0`, `tn0`] >>
  simp[eval_exprs_nil, gas_origin_ptr_path_rules, abi_encode_packed_post_mods_def,
       ghost_kept_at_refl, wb_frame_refl] >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `(immutable_frame_mods func cenv cx (es with gas_obs := []) s0 <=>
    immutable_frame_mods func cenv cx es s0)` by
    simp[NoAsms, immutable_frame_mods_def, immutables_rel_mods_def,
         immutable_alloca_sep_mods_def, immutable_alloca_sep_def, immutables_rel_def] >>
  `(storage_well_formed_on cx (es with gas_obs := []) (FST H) <=>
    storage_well_formed_on cx es (FST H))` by
    (irule storage_well_formed_on_backends >> simp[]) >>
  `(ghost_inv_at_mods (DF H) lo d cenv cx (es with gas_obs := []) G0 tn0 s0 <=>
    ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0)` by
    simp[NoAsms, ghost_inv_at_mods_def] >>
  simp[]
QED
