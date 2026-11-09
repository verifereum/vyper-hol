(* Header-load safety for captured len operands, including empty payloads. *)
Theory bodyMemBiLenSafety
Ancestors
  exprSimLen exprSimSource exprSimProps exprSimHypsDefs exprSimDefs
  loweringPosts list fragExec exprSimHyps exprSimWordBuiltins exprBopLowering
  exprLowering exprLoweringProps builtinSimple emitHelper compileEnv
  accountsRelProps valueEncoding venomExecSemantics venomInst venomState
  vyperAST vyperInterpreter vyperState vyperContext vyperTypeSystem
  vyperTypeBuiltins vyperValue vyperTyping vyperStorage builtinProps
  vyperTypeInvariants context freshWrites loweringSlice emitHelperProps
  exprSimUnwrap exprSimCopy vyperTypeExprResult vyperTypeExprSoundness
  vyperExprNoControl gasContext gasOutcome gasSummary gasSummaryCompose
  gasExemptCert fragGasMode fragGasPath exprSimBopRestWordLoadSafety
  exprSimMemDefs words

Theorem len_sized_store_header:
  is_sized_type t /\ evaluate_type tenv t = SOME vt ==>
  32 <= val_store_size vt v /\ 32 <= type_memory_size vt /\ ~is_word_type t
Proof
  strip_tac >> drule sized_type_cases >> strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs(), type_memory_size_def, is_word_type_def] >>
  Cases_on `v` >> simp[val_store_size_def, type_memory_size_def]
QED

(* Trunk copies of the exprSimLen widening lemmas (local there). *)
Theorem len_mem_sized_memory_header_widens[local]:
  !tenv pt t pvt tvt v a mem cx es.
    type_widens_to tenv pt t /\ is_sized_type t /\
    evaluate_type tenv pt = SOME pvt /\
    evaluate_type tenv t = SOME tvt /\ value_has_type tvt v /\
    val_in_memory pvt v a mem ==>
    ?n. result_array_length cx (Value v) es = (INL n,es) /\
        mem_word_at a mem = n2w n
Proof
  rpt gen_tac >> strip_tac >>
  gvs[type_widens_to_def]
  >- metis_tac[sized_memory_header] >>
  drule sized_type_cases >> strip_tac >>
  Cases_on `pt` >>
  gvs[arg_type_fits_def, evaluate_type_def, AllCaseEqs()] >>
  TRY (rename1 `arg_type_fits (ArrayT _ bd) _` >>
       Cases_on `bd` >> gvs[arg_type_fits_def]) >>
  Cases_on `v` >>
  gvs[value_has_type_def, val_in_memory_def, result_array_length_def,
      read_result_def, bind_def, return_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >>
  gvs[value_has_type_def, val_in_memory_def, result_array_length_def,
      read_result_def, bind_def, return_def]
QED

Theorem len_mem_read_result_memory_header_widens[local]:
  !env cx pt t pvt tvt r es v w mem n.
    type_widens_to (get_tenv cx) pt t /\
    evaluate_type (get_tenv cx) pt = SOME pvt /\
    evaluate_type (get_tenv cx) t = SOME tvt /\ is_sized_type t /\
    env.type_defs = get_tenv cx /\
    eval_result_typed (env,cx,es) r (Type t) /\
    read_result cx r es = (INL v,es) /\ value_has_type tvt v /\
    val_in_memory pvt v w mem /\
    result_array_length cx r es = (INL n,es) ==>
    mem_word_at w mem = n2w n
Proof
  rpt gen_tac >> strip_tac >>
  `evaluate_type env.type_defs t = SOME tvt` by simp[] >>
  drule_all sized_read_result_length >> strip_tac >>
  drule_all len_mem_sized_memory_header_widens >>
  disch_then (qspecl_then [`cx`, `es`] strip_assume_tac) >> gvs[]
QED

Theorem len_mem_sized_type_widens_source[local]:
  type_widens_to tenv pt t /\ is_sized_type t ==> is_sized_type pt
Proof
  strip_tac >> gvs[type_widens_to_def] >>
  drule sized_type_cases >> strip_tac >> Cases_on `pt` >>
  gvs[arg_type_fits_def, is_sized_type_def]
  >~ [`arg_type_fits (ArrayT _ bd) _`]
  >- (Cases_on `bd` >> gvs[arg_type_fits_def, is_sized_type_def]) >>
  rename1 `arg_type_fits (BaseT bt) _` >>
  Cases_on `bt` >> gvs[arg_type_fits_def, is_sized_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[arg_type_fits_def, is_sized_type_def]
QED

Theorem len_mem_storage_holds_header_widens[local]:
  !env cx tr pt t pvt tvt tv w es s n.
    storage_holds cx tr pt tv w es s /\
    type_widens_to (get_tenv cx) pt t /\
    evaluate_type (get_tenv cx) pt = SOME pvt /\
    evaluate_type (get_tenv cx) t = SOME tvt /\ is_sized_type t /\
    env.type_defs = get_tenv cx /\
    eval_result_typed (env,cx,es) tv (Type t) /\
    (!v. read_result cx tv es = (INL v,es) ==> value_has_type tvt v) /\
    result_array_length cx tv es = (INL n, es) ==>
    lookup_storage w
      (if tr then lookup_transient_storage cx.txn.target es.tStorage
       else (lookup_account cx.txn.target es.accounts).storage) = n2w n /\
    storage_range_agree (get_storage cx es tr)
      (if tr then contract_transient s else contract_storage s) w pvt /\
    0 < type_slot_size pvt
Proof
  rpt gen_tac >> simp[storage_holds_def] >> strip_tac >> gvs[] >>
  `is_sized_type pt` by metis_tac[len_mem_sized_type_widens_source] >>
  `0 < type_slot_size pvt` by
    (drule sized_type_cases >> strip_tac >>
     gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
         vyperValueTheory.type_slot_size_def]) >>
  `value_has_type tvt v` by metis_tac[] >>
  `evaluate_type env.type_defs t = SOME tvt` by simp[] >>
  drule_all sized_read_result_length >> strip_tac >>
  Cases_on `tr` >>
  gvs[read_storage_slot_def, get_storage_backend_def,
      get_transient_storage_def, get_accounts_def, bind_def, return_def] >>
  qmatch_asmsub_abbrev_tac `lift_option dv` >> Cases_on `dv` >>
  gvs[lift_option_def, raise_def, return_def] >>
  drule_all sized_decode_header >>
  disch_then (qspecl_then [`cx`, `es`] strip_assume_tac) >>
  gvs[read_slot_def]
QED

Theorem len_mem_immutable_holds_memory[local]:
  !func cenv cx es s t tv w ctx.
    stmt_state_rel ctx func cenv cx es s /\ cenv.ce_is_ctor /\
    immutable_holds cenv cx t tv w es s ==>
    ?tvt v. evaluate_type (get_tenv cx) t = SOME tvt /\
            read_result cx tv es = (INL v, es) /\
            val_in_memory tvt v (w2n w) s.vs_memory
Proof
  rw[immutable_holds_def, stmt_state_rel_def, state_rel_def,
     immutables_rel_def]
  >~ [`sub_layout`]
  >- (gvs[] >> first_x_assum drule_all >> strip_tac >>
      gvs[sub_layout_def] >> first_x_assum drule >> strip_tac >>
      `off + k < dimword (:256)` by DECIDE_TAC >>
      gvs[arithmeticTheory.ADD_COMM]) >>
  `off + k < dimword (:256)` by DECIDE_TAC >> gvs[] >> metis_tac[]
QED

Theorem len_mem_vv_holds_len_header_widens:
  !env func cenv cx es s pt t pvt tvt tv vv n ctx.
    stmt_state_rel ctx func cenv cx es s /\ vv_holds cenv cx pt tv vv es s /\
    type_widens_to env.type_defs pt t /\
    is_sized_type t /\ evaluate_type (get_tenv cx) t = SOME tvt /\
    evaluate_type (get_tenv cx) pt = SOME pvt /\
    env.type_defs = get_tenv cx /\
    eval_result_typed (env,cx,es) tv (Type t) /\
    (!v. read_result cx tv es = (INL v,es) ==> value_has_type tvt v) /\
    result_array_length cx tv es = (INL n, es) ==>
    ?w. eval_operand (vv_operand vv) s = SOME w /\
        ptr_load_val cenv.ce_is_ctor
          (case vv_location vv of SOME l => l | NONE => LocMemory) w s = n2w n
Proof
  rpt gen_tac >> strip_tac >>
  `is_sized_type pt` by metis_tac[len_mem_sized_type_widens_source] >>
  `evaluate_type env.type_defs pt = SOME pvt /\
   evaluate_type env.type_defs t = SOME tvt` by simp[] >>
  Cases_on `vv` >> gvs[vv_holds_def, vv_operand_def, vv_location_def]
  >~ [`expr_val_rel cx pt v op s`]
  >- (gvs[expr_val_rel_def] >>
      `~is_word_type pt` by
        (drule sized_type_cases >> strip_tac >> gvs[is_word_type_def]) >>
      gvs[] >>
      drule_all len_mem_read_result_memory_header_widens >> strip_tac >>
      gvs[ptr_load_val_def, mload_def, mem_word_at_def]) >>
  rename1 `p.ptr_location` >> Cases_on `p.ptr_location` >> gvs[]
  >~ [`val_in_memory _ _ _ _`]
  >- (drule_all len_mem_read_result_memory_header_widens >>
      simp[ptr_load_val_def, mload_def, mem_word_at_def])
  >~ [`immutable_holds`]
  >- (Cases_on `cenv.ce_is_ctor`
      >- (drule_all len_mem_immutable_holds_memory >> strip_tac >> gvs[] >>
          drule_all len_mem_read_result_memory_header_widens >>
          simp[ptr_load_val_def, mload_def, mem_word_at_def]) >>
      drule_all immutable_holds_data >> strip_tac >> gvs[] >>
      drule_all len_mem_read_result_memory_header_widens >>
      simp[ptr_load_val_def, mem_word_at_def])
  >>~- ([`val_in_memory _ _ _ _`],
        drule_all len_mem_read_result_memory_header_widens >>
        simp[ptr_load_val_def, mload_def, mem_word_at_def]) >>
  drule_all len_mem_storage_holds_header_widens >> strip_tac >>
  drule_all storage_range_agree_head >>
  gvs[ptr_load_val_def, sload_def, tload_def,
      vyperStorageBackendTheory.get_storage_def,
      vfmExecutionTheory.lookup_transient_storage_def,
      vfmStateTheory.lookup_account_def]
QED

Theorem len_mem_vv_holds_sized_length_success_widens:
  !env cenv cx pt t r vv es s tvt.
    vv_holds cenv cx pt r vv es s /\ is_sized_type t /\
    evaluate_type (get_tenv cx) t = SOME tvt /\
    env.type_defs = get_tenv cx /\
    eval_result_typed (env,cx,es) r (Type t) /\
    (!v. read_result cx r es = (INL v,es) ==> value_has_type tvt v) ==>
    ?n. result_array_length cx r es = (INL n,es)
Proof
  rpt gen_tac >> strip_tac >>
  `?v. read_result cx r es = (INL v,es)` by
    (Cases_on `vv` >> gvs[vv_holds_def] >>
     Cases_on `p.ptr_location` >>
     gvs[storage_holds_def, immutable_holds_def] >> metis_tac[]) >>
  `value_has_type tvt v` by metis_tac[] >>
  irule sized_read_result_length_success >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem len_vv_memory_header_bound:
  vv_holds cenv cx pt tv vv es s /\ vv_store_bound cx t lt es tv vv s /\
  is_sized_type t /\ evaluate_type (get_tenv cx) t = SOME vt /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) ==>
  ?w. eval_operand (vv_operand vv) s = SOME w /\
      w2n w + 32 <= s.vs_alloca_next
Proof
  strip_tac >>
  `!v. 32 <= val_store_size vt v /\ ~is_word_type t` by
    metis_tac[len_sized_store_header] >>
  Cases_on `vv` >>
  gvs[vv_location_def, vv_operand_def, vv_holds_def, expr_val_rel_def,
      vv_store_bound_def] >>
  first_x_assum (qspec_then `v` strip_assume_tac) >> decide_tac
QED

Theorem len_load_mem_ok:
  compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca (vv_operand vv)
    (case vv_location vv of SOME l => l | NONE => LocMemory) sm = (op,sb) /\
  vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
  type_widens_to (get_tenv cx) (post_value_type cenv e) (expr_type e) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME pvt /\
  vv_store_bound cx (expr_type e) lt es' tv vv s /\
  is_sized_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME vt ==>
  run_inst_seq_mem_ok (emitted_insts sm sb) s
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es' s /\
   vv_holds cenv cx (post_value_type cenv e) tv vv es' s` by fs[vv_post_def] >>
  `32 <= type_memory_size vt /\ ~is_word_type (expr_type e)` by
    metis_tac[len_sized_store_header] >>
  `(vv_location vv = NONE \/ vv_location vv = SOME LocMemory) ==>
    ?w. eval_operand (vv_operand vv) s = SOME w /\
        w2n w + 32 <= s.vs_alloca_next` by
    (strip_tac >> metis_tac[len_vv_memory_header_bound]) >>
  gvs[compile_builtin_len_def] >>
  Cases_on `vv`
  >- (gvs[vv_location_def] >>
      irule (Q.INST [`loc` |-> `LocMemory`] rest_word_ptr_load_mem_ok) >>
      simp[] >> fs[vv_operand_def] >> metis_tac[]) >>
  gvs[vv_location_def, vv_operand_def, vv_holds_def] >>
  Cases_on `p.ptr_location` >> gvs[]
  >>~- ([`p.ptr_location = LocMemory`],
        irule (Q.INST [`loc` |-> `LocMemory`] rest_word_ptr_load_mem_ok) >>
        simp[] >> metis_tac[])
  >- (irule (Q.INST [`loc` |-> `LocStorage`] rest_word_ptr_load_mem_ok) >>
      simp[] >> metis_tac[])
  >- (irule (Q.INST [`loc` |-> `LocTransient`] rest_word_ptr_load_mem_ok) >>
      simp[] >> metis_tac[]) >>
  `is_sized_type (post_value_type cenv e)` by
    metis_tac[len_mem_sized_type_widens_source] >>
  `32 <= type_memory_size pvt` by metis_tac[len_sized_store_header] >>
  mp_tac (Q.INST [`es` |-> `es'`, `ty` |-> `post_value_type cenv e`,
                  `vt` |-> `pvt`] rest_word_immutable_region_bound) >>
  impl_tac >- simp[] >> strip_tac >>
  `(cenv.ce_is_ctor /\ cenv.ce_imm_alloca <> NONE ==>
    eval_operand (THE cenv.ce_imm_alloca) s = SOME 0w)` by
    (fs[stmt_state_rel_def, immutable_base_zero_def] >>
     Cases_on `cenv.ce_imm_alloca` >> gvs[]) >>
  mp_tac (Q.INST [`loc` |-> `LocCode`, `ctor` |-> `cenv.ce_is_ctor`,
                  `imm` |-> `cenv.ce_imm_alloca`, `addr` |-> `p.ptr_operand`,
                  `a` |-> `w`, `sa` |-> `sm`] rest_word_ptr_load_mem_ok) >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     Cases_on `cenv.ce_is_ctor` >> gvs[] >> decide_tac) >>
  simp[]
QED

Theorem len_vv_not_calldata:
  vv_holds cenv cx t tv vv es s ==>
  (case vv_location vv of SOME l => l | NONE => LocMemory) <> LocCalldata
Proof
  Cases_on `vv` >> simp[vv_location_def, vv_holds_def] >>
  Cases_on `p.ptr_location` >> simp[]
QED
