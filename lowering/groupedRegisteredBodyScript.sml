Theory groupedRegisteredBody
Ancestors
  groupedPositionalRegistration groupedDefaultState groupedDefaultHorizon
  selectedAcceptedFold fragGasOriginPtr fragFuel exprLoweringProps
  loweringStateRelDefs compileEnv moduleLowering ptrDiscipline venomState
  allocaFrontierBound vyperState sourceUnitExecution loweringPosts
  selectedAcceptedInterfaces abiDecoderCoherence vyperCalldata valueEncoding
  venomExecSemantics venomWf finite_map words list

Theorem grouped_register_body_arguments:
  LENGTH kw = LENGTH kwtvs /\ LENGTH kw = LENGTH kwvals /\
  LENGTH pos = LENGTH ptvs /\ LENGTH pos = LENGTH pvals /\
  ALL_DISTINCT (MAP FST (pos ++ kw)) /\
  (!c arg tv. MEM (arg,tv) (ZIP (pos ++ kw,ptvs ++ kwtvs)) /\
    c = ce with ce_vars := c.ce_vars ==>
      selected_slot_accepts c env c.ce_struct_fields (SND arg) tv /\
      abi_decoder_coherent c env c.ce_struct_fields (SND arg) tv) /\
  EVERY (\tv. type_memory_size tv < dimword (:256)) (ptvs ++ kwtvs) /\
  LIST_REL (\(name,ty) tv. ?loc. FLOOKUP ce.ce_vars name = SOME loc /\
    var_location_memory_size loc = SOME (type_memory_size tv)) pos ptvs /\
  compile_register_positional_args ce (build_positional_args ce pos) 4
    entry = (cf,last) /\ fn_has_code entry last fn /\ fn_inst_ids_distinct fn /\
  (!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  calldata_decode_args s.vs_call_ctx.cc_calldata ptvs 0 = SOME pvals /\
  4+SUM (MAP tv_abi_size ptvs) < dimword (:256) /\
  selected_registration_owners fn (MAP FST kw) kwtvs kwvals (LENGTH kw) ce entry s G tn /\
  selected_registration_resources ctx fn site 0 entry s /\
  unit_alloca_budget ctx < dimword (:256) /\ fresh_vars_wrt last s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) /\
  bind_arguments env (pos ++ kw) (pvals ++ kwvals) = SOME envb /\
  LIST_REL (\ty tv. evaluate_type env ty = SOME tv) (MAP SND (pos ++ kw)) (ptvs ++ kwtvs) /\
  (!k. ~MEM k (MAP FST (pos ++ kw)) ==> FLOOKUP cf.ce_vars k = NONE) /\
  local_ptrs_reserved cf last /\
  stmt_state_rel ([],[]) ctx fn (cf with ce_vars := FEMPTY) cx es s /\
  ~cf.ce_is_ctor /\ cf.ce_imm_alloca = NONE /\
  cf.ce_return_pc = NONE /\ cf.ce_return_buf = NONE /\
  tn.t_stor = {} /\ tn.t_trans = {} /\ tn.t_imm = {} ==>
  ?t J tz.
    at_point last t /\ fresh_vars_wrt last t /\
    return_buf_frame NONE cf last t /\
    (!H:(bool # bytes32 # type_value) list # num list. stmt_state_rel H ctx fn cf cx (es with scopes := [envb]) t /\
      ghost_inv_at (cx_dead H cx) 0 NONE cf cx (es with scopes := [envb]) J tz t) /\
    !D explicit. gas_origin_ptr_path (D,0,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,J,tz)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`lo` |-> `0`] (SPEC_ALL grouped_register_positional_suffix)) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`t`,`J`,`tz`] (map_every assume_tac o CONJUNCTS)) >>
  `stmt_state_rel ([],[]) ctx fn cf cx (es with scopes := [envb]) t` by
    (qpat_assum `!D explicit. gas_origin_ptr_path _ _ [] (OK t,J,tz)`
       (qspecl_then [`cx_dead ([],[]) cx`,`K F`] assume_tac) >>
     drule_all_then ACCEPT_TAC grouped_positional_state_frame) >>
  `at_point last t /\ alloca_inv t /\ t.vs_alloca_next < dimword (:256)` by
    (fs[at_point_def, selected_registration_resources_def, alloca_frontier_inv_def] >>
     decide_tac) >>
  `tz.t_stor = {} /\ tz.t_trans = {} /\ tz.t_imm = {}` by
    fs[selected_registration_frame_def] >>
  qexistsl_tac [`t`,`J`,`tz`] >> asm_rewrite_tac[return_buf_frame_def] >>
  qx_gen_tac `H` >> conj_tac >- metis_tac[grouped_default_empty_mask_state] >>
  mp_tac (Q.INST [`tenv` |-> `env`,`args` |-> `pos ++ kw`,
    `vals` |-> `pvals ++ kwvals`,`tvs` |-> `ptvs ++ kwtvs`,
    `ce` |-> `cf`,`st` |-> `last`,`s` |-> `t`,`G` |-> `J`,`tn` |-> `tz`,
    `D` |-> `cx_dead (H:(bool # bytes32 # type_value) list # num list) cx`,`es` |-> `es with scopes := [envb]`]
    (SPEC_ALL grouped_registered_owners_ghost)) >>
  simp[]
QED
