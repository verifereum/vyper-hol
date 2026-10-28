(*
 * Expression simulation: len (#636, Builtins row 1)
 *
 * len(x) lowers x to its value_vv, a pointer, and loads the word at it
 * from x's location (compile_builtin_len): the length word of a dynamic
 * array, bytes or string in memory, storage or transient storage.  The
 * source reads the same length (toplevel_array_length).  An operand in
 * code, an immutable, is left to exprSimBuiltins' compile_len_code_sim.
 *
 * TOP-LEVEL:
 *   compile_len_loc_sim — expr_vv_ok of Len, for an operand not in code
 *
 * Also exported, the length word of a sized value: sized_memory_header,
 *   materialised_memory_header, storage_holds_header, vv_holds_len_header,
 *   materialise_array_length,
 *   sized_materialise_length, sized_decode_header, slots_to_bytes_length_exact,
 *   read_slots_length, sized_toplevel_length; and expr_sim_pre_runtime_typed,
 *   sized_expr_vv_res_ok.
 *)

Theory exprSimLen
Ancestors
  list fragExec exprSim exprSimHyps exprSimWordBuiltins exprBopLowering exprLowering
  exprLoweringProps builtinSimple emitHelper compileEnv valueEncoding
  venomExecSemantics venomInst venomState vyperAST vyperInterpreter vyperState
  vyperContext vyperTypeSystem vyperTypeBuiltins vyperValue vyperTyping vyperStorage
  builtinProps vyperTypeInvariants context freshWrites loweringSlice emitHelperProps
  exprSimUnwrap vyperTypeExprResult vyperTypeExprSoundness vyperExprNoControl

Theorem len_pre_args[local]:
  !cenv cx env ann args es.
    expr_sim_pre cenv cx env (Builtin ann Len args) es ==>
    ?e. args = [e] /\ ann = BaseT (UintT 256) /\
        is_sized_type (expr_type e)
Proof
  rpt gen_tac >>
  simp[expr_sim_pre_def, well_typed_expr_def,
       well_typed_builtin_app_def] >> strip_tac >>
  Cases_on `args` >> gvs[] >>
  rename1 `LENGTH rest = 0` >>
  Cases_on `rest` >> gvs[]
QED

Theorem names_builtin_len[local]:
  !args. ~names_builtin Len args
Proof
  `!bt args. names_builtin bt args ==> bt <> Len` suffices_by
    metis_tac[] >>
  ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]
QED

Theorem compile_expr_len[local]:
  !cenv ty ann e st.
    compile_expr cenv ty (Builtin ann Len [e]) st =
    (let (vv, st1) = compile_expr cenv ty e st in
       as_stack_val ann
         (compile_builtin_len cenv.ce_is_ctor (vv_operand vv)
           (case vv_location vv of SOME l => l | NONE => LocMemory) st1))
Proof
  rpt gen_tac >>
  simp[compile_expr_builtin_dispatch, names_builtin_len] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def]
QED

Theorem eval_expr_len[local]:
  !cx ann e es.
    eval_expr cx (Builtin ann Len [e]) es =
    (do tv <- eval_expr cx e;
        n <- toplevel_array_length cx tv;
        return (Value (IntV (&n))) od) es
Proof
  rpt gen_tac >>
  simp[Once evaluate_def, builtin_args_length_ok_def, type_check_def,
       assert_def, bind_def, ignore_bind_def, return_def] >>
  Cases_on `eval_expr cx e es` >>
  rename1 `(res, es1)` >> Cases_on `res` >> simp[bind_def] >>
  rename1 `toplevel_array_length cx tv es1` >>
  Cases_on `toplevel_array_length cx tv es1` >>
  rename1 `(res, es2)` >> Cases_on `res` >> simp[bind_def, return_def]
QED

Theorem sized_type_cases[local]:
  !t. is_sized_type t ==>
    (?et k. t = ArrayT et (Dynamic k)) \/
    (?k. t = BaseT (StringT k)) \/
    (?k. t = BaseT (BytesT (Dynamic k)))
Proof
  Cases >> gvs[is_sized_type_def]
  >~ [`is_sized_type (BaseT bt)`]
  >- (Cases_on `bt` >> gvs[is_sized_type_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >> gvs[]) >>
  rename1 `ArrayT et bd` >> Cases_on `bd` >> gvs[]
QED

Theorem sized_memory_header:
  !tenv t tvt v a mem cx es.
    evaluate_type tenv t = SOME tvt /\ is_sized_type t /\
    value_has_type tvt v /\ val_in_memory tvt v a mem ==>
    ?n. toplevel_array_length cx (Value v) es = (INL n, es) /\
        mem_word_at a mem = n2w n
Proof
  rpt gen_tac >> strip_tac >>
  drule sized_type_cases >> strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >>
  gvs[value_has_type_def, val_in_memory_def, toplevel_array_length_def,
      return_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >>
  gvs[value_has_type_def, val_in_memory_def, toplevel_array_length_def,
      return_def]
QED

Theorem materialise_array_length:
  !cx tr slot et k es v.
    materialise cx (ArrayRef tr slot et (Dynamic k)) es = (INL v, es) ==>
    toplevel_array_length cx (Value v) es =
    toplevel_array_length cx (ArrayRef tr slot et (Dynamic k)) es
Proof
  rpt gen_tac >> Cases_on `tr` >>
  simp[materialise_def, read_storage_slot_def, get_storage_backend_def,
       get_transient_storage_def, get_accounts_def, bind_def, return_def] >>
  qmatch_goalsub_abbrev_tac `lift_option dv` >>
  Cases_on `dv` >> simp[lift_option_def, raise_def, return_def, bind_def] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `decode_value _ _ _ = _` mp_tac >>
  simp[Once decode_value_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  drule vyperTypeStatePreservationTheory.decode_dyn_array_length >> strip_tac >>
  gvs[read_slot_def] >>
  simp[toplevel_array_length_def, get_storage_backend_def,
       get_transient_storage_def, get_accounts_def, bind_def, return_def,
       read_slot_def, arithmeticTheory.MIN_DEF]
QED

Theorem slots_to_bytes_length_exact:
  !slots n. LENGTH (slots_to_bytes n slots) = MIN n (32 * LENGTH slots)
Proof
  Induct >> gen_tac >> Cases_on `n` >>
  simp[slots_to_bytes_def, byteTheory.word_to_bytes_be_def,
       byteTheory.LENGTH_word_to_bytes] >>
  simp[arithmeticTheory.MIN_DEF] >> rpt IF_CASES_TAC >> gvs[]
QED

Theorem read_slots_length:
  !n storage off. LENGTH (read_slots storage off n) = n
Proof
  Induct >> simp[read_slots_def]
QED

Theorem sized_decode_header:
  !tenv t tvt storage off v cx es.
    evaluate_type tenv t = SOME tvt /\ is_sized_type t /\
    decode_value storage off tvt = SOME v ==>
    ?n. toplevel_array_length cx (Value v) es = (INL n, es) /\
        read_slot storage off = n2w n
Proof
  rpt gen_tac >> strip_tac >>
  drule sized_type_cases >> strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  qpat_x_assum `decode_value _ _ _ = _` mp_tac >>
  simp[Once decode_value_def, AllCaseEqs()] >> strip_tac >> gvs[]
  >~ [`decode_dyn_array _ _ _ _ = SOME _`]
  >- (drule vyperTypeStatePreservationTheory.decode_dyn_array_length >> strip_tac >>
      simp[toplevel_array_length_def, return_def] >>
      `MIN (w2n (read_slot storage off)) k = w2n (read_slot storage off)` by
        simp[arithmeticTheory.MIN_DEF] >>
      simp[wordsTheory.n2w_w2n]) >>
  gvs[decode_dyn_bytes_def] >>
  simp[toplevel_array_length_def, return_def, slots_to_bytes_length_exact,
       read_slots_length] >>
  qspec_then `w2n (lookup_storage (n2w off) storage)` mp_tac le_word_size_mul >>
  rw[arithmeticTheory.MIN_DEF, read_slot_def, wordsTheory.n2w_w2n] >>
  `32 * word_size (w2n (lookup_storage (n2w off) storage)) =
   w2n (lookup_storage (n2w off) storage)` by decide_tac >>
  simp[wordsTheory.n2w_w2n]
QED

Theorem sized_materialise_length:
  !cx t tvt tv es v.
    evaluate_type (get_tenv cx) t = SOME tvt /\ is_sized_type t /\
    toplevel_value_typed tv tvt /\ materialise cx tv es = (INL v, es) ==>
    toplevel_array_length cx (Value v) es = toplevel_array_length cx tv es
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `tv` >> gvs[materialise_def, return_def, raise_def]
  >~ [`toplevel_value_typed (ArrayRef _ _ _ _) _`]
  >- (gvs[toplevel_value_typed_def] >>
      drule sized_type_cases >> strip_tac >>
      gvs[evaluate_type_def, AllCaseEqs()] >>
      irule materialise_array_length >> simp[materialise_def]) >>
  drule sized_type_cases >> strip_tac >>
  gvs[toplevel_value_typed_def, evaluate_type_def, AllCaseEqs()]
QED

Theorem materialised_memory_header:
  !cx t tvt tv es v w mem n.
    evaluate_type (get_tenv cx) t = SOME tvt /\ is_sized_type t /\
    toplevel_value_typed tv tvt /\ materialise cx tv es = (INL v, es) /\
    val_in_memory tvt v w mem /\
    toplevel_array_length cx tv es = (INL n, es) ==>
    mem_word_at w mem = n2w n
Proof
  rpt gen_tac >> strip_tac >>
  drule_all sized_materialise_length >> strip_tac >>
  Cases_on `tv` >> gvs[materialise_def, return_def, raise_def]
  >~ [`toplevel_value_typed (Value _) _`]
  >- (gvs[toplevel_value_typed_def] >>
      drule_all sized_memory_header >>
      disch_then (qspecl_then [`cx`, `es`] strip_assume_tac) >> gvs[]) >>
  drule sized_type_cases >> strip_tac >>
  gvs[toplevel_value_typed_def, evaluate_type_def, AllCaseEqs()] >>
  rename1 `read_storage_slot cx tr slot _` >> Cases_on `tr` >>
  gvs[read_storage_slot_def, get_storage_backend_def,
      get_transient_storage_def, get_accounts_def, bind_def, return_def] >>
  qmatch_asmsub_abbrev_tac `lift_option dv` >>
  Cases_on `dv` >>
  gvs[lift_option_def, raise_def, return_def, bind_def] >>
  qpat_x_assum `decode_value _ _ _ = _` mp_tac >>
  simp[Once decode_value_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  gvs[val_in_memory_def, toplevel_array_length_def, return_def, raise_def]
QED

Theorem storage_holds_header:
  !cx tr t tvt tv w es n.
    storage_holds cx tr t tv w es /\
    evaluate_type (get_tenv cx) t = SOME tvt /\ is_sized_type t /\
    toplevel_value_typed tv tvt /\
    toplevel_array_length cx tv es = (INL n, es) ==>
    lookup_storage w
      (if tr then lookup_transient_storage cx.txn.target es.tStorage
       else (lookup_account cx.txn.target es.accounts).storage) = n2w n
Proof
  rpt gen_tac >> simp[storage_holds_def] >> strip_tac >> gvs[] >>
  drule_all sized_materialise_length >> strip_tac >>
  Cases_on `tr` >>
  gvs[read_storage_slot_def, get_storage_backend_def,
      get_transient_storage_def, get_accounts_def, bind_def, return_def] >>
  qmatch_asmsub_abbrev_tac `lift_option dv` >> Cases_on `dv` >>
  gvs[lift_option_def, raise_def, return_def] >>
  drule_all sized_decode_header >>
  disch_then (qspecl_then [`cx`, `es`] strip_assume_tac) >>
  gvs[read_slot_def]
QED

Theorem vv_holds_len_header:
  !func cenv cx es s t tvt tv vv n.
    stmt_state_rel func cenv cx es s /\ vv_holds cenv cx t tv vv es s /\
    is_sized_type t /\ evaluate_type (get_tenv cx) t = SOME tvt /\
    toplevel_value_typed tv tvt /\ vv_location vv <> SOME LocCode /\
    toplevel_array_length cx tv es = (INL n, es) ==>
    ?w. eval_operand (vv_operand vv) s = SOME w /\
        ptr_load_val cenv.ce_is_ctor
          (case vv_location vv of SOME l => l | NONE => LocMemory) w s = n2w n
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `vv` >> gvs[vv_holds_def, vv_operand_def, vv_location_def]
  >~ [`expr_val_rel cx t v op s`]
  >- (gvs[expr_val_rel_def] >>
      `~is_word_type t` by
        (drule sized_type_cases >> strip_tac >> gvs[is_word_type_def]) >>
      gvs[toplevel_value_typed_def] >> drule_all sized_memory_header >>
      disch_then (qspecl_then [`cx`, `es`] strip_assume_tac) >>
      gvs[ptr_load_val_def, mload_def, mem_word_at_def]) >>
  rename1 `p.ptr_location` >> Cases_on `p.ptr_location` >> gvs[]
  >~ [`val_in_memory _ _ _ _`]
  >- (drule_all materialised_memory_header >>
      simp[ptr_load_val_def, mload_def, mem_word_at_def]) >>
  drule_all storage_holds_header >>
  gvs[stmt_state_rel_def, state_rel_def, storage_rel_def, transient_rel_def,
      ptr_load_val_def, sload_def, tload_def,
      vfmExecutionTheory.lookup_transient_storage_def]
QED

Theorem len_vv_post_load[local]:
  !func cenv cx e es sa sm sb s0 es' tv vv s1 op s n.
    vv_post func cenv cx e es sa sm s0 es' tv vv s1 /\
    sa.cs_next_var <= sm.cs_next_var /\
    stmt_state_rel func cenv cx es' s /\ eval_operand op s = SOME (n2w n) /\
    (!x w. not_fresh_at sm x /\ lookup_var x s1 = SOME w ==>
           lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s1.vs_allocas aid = SOME b ==>
             FLOOKUP s.vs_allocas aid = SOME b) /\ s.vs_memory = s1.vs_memory ==>
    vv_post func cenv cx (Builtin (BaseT (UintT 256)) Len [e]) es
      sa sb s0 es' (Value (IntV (&n))) (StackValue (BaseT (UintT 256)) op) s
Proof
  rw[vv_post_def]
  >~ [`vv_holds`]
  >- simp[vv_holds_def, expr_val_rel_def, expr_type_def, is_word_type_def,
          evaluate_type_def, typed_val_to_w256_def, val_to_w256_def,
          integer_wordTheory.i2w_def]
  >~ [`vv_at`]
  >- simp[vv_at_def, expr_val_at_def, expr_type_def, is_word_type_def]
  >~ [`lookup_var x s`]
  >- (fs[vv_post_def] >> metis_tac[not_fresh_at_mono])
  >~ [`FLOOKUP s.vs_allocas`] >- (fs[vv_post_def] >> metis_tac[]) >>
  fs[vv_post_def] >> metis_tac[]
QED

Theorem len_load_frag[local]:
  !ctx func cenv cx es is_ctor pop loc sm op sb s0 w R.
    compile_builtin_len is_ctor pop loc sm = (op, sb) /\
    loc <> LocCode /\ loc <> LocCalldata /\ local_ptrs_reserved cenv sm /\
    eval_operand pop s0 = SOME w ==>
    frag_exec ctx sm sb (\s. s = s0 /\ stmt_state_rel func cenv cx es s)
      (\s. stmt_state_rel func cenv cx es s /\
           eval_operand op s = SOME (ptr_load_val is_ctor loc w s0) /\
           (!x w'. not_fresh_at sm x /\ lookup_var x s0 = SOME w' ==>
                   lookup_var x s = SOME w') /\
           (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                    FLOOKUP s.vs_allocas aid = SOME b) /\
           s.vs_memory = s0.vs_memory) R
Proof
  rpt gen_tac >> strip_tac >> Cases_on `loc` >>
  gvs[compile_builtin_len_def, compile_ptr_load_def, ptr_load_val_def] >>
  irule emit_op_frag >> (reverse conj_tac >- simp[])
  >~ [`emit_op MLOAD [pop] sm = _`]
  >- (qexistsl [`[pop]`, `MLOAD`] >> simp[is_terminator_def] >>
      rpt strip_tac >> simp[step_inst_base_def, exec_read1_def])
  >~ [`emit_op SLOAD [pop] sm = _`]
  >- (qexistsl [`[pop]`, `SLOAD`] >> simp[is_terminator_def] >>
      rpt strip_tac >> simp[step_inst_base_def, exec_read1_def]) >>
  qexistsl [`[pop]`, `TLOAD`] >> simp[is_terminator_def] >>
  rpt strip_tac >> simp[step_inst_base_def, exec_read1_def]
QED

Theorem compile_len_vv_frag[local]:
  !ctx func cenv cx e es sa sm sb s0 es' tv vv op n tvt R.
    compile_builtin_len cenv.ce_is_ctor (vv_operand vv)
      (case vv_location vv of SOME l => l | NONE => LocMemory) sm = (op,sb) /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    is_sized_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    toplevel_value_typed tv tvt /\ vv_location vv <> SOME LocCode /\
    toplevel_array_length cx tv es' = (INL n, es') ==>
    frag_exec ctx sm sb (vv_post func cenv cx e es sa sm s0 es' tv vv)
      (vv_post func cenv cx (Builtin (BaseT (UintT 256)) Len [e]) es
        sa sb s0 es' (Value (IntV (&n)))
        (StackValue (BaseT (UintT 256)) op)) R
Proof
  rpt gen_tac >> strip_tac >> irule frag_exec_pointwise >>
  qx_gen_tac `s1` >> strip_tac >>
  `stmt_state_rel func cenv cx es' s1 /\
   vv_holds cenv cx (expr_type e) tv vv es' s1` by fs[vv_post_def] >>
  drule_all vv_holds_len_header >> strip_tac >>
  ` (case vv_location vv of SOME l => l | NONE => LocMemory) <> LocCalldata` by
    (Cases_on `vv` >> gvs[vv_location_def, vv_holds_def] >>
     Cases_on `p.ptr_location` >> gvs[]) >>
  `(case vv_location vv of SOME l => l | NONE => LocMemory) <> LocCode` by
    (Cases_on `vv_location vv` >> gvs[]) >>
  drule_all len_load_frag >>
  disch_then (qspecl_then [`ctx`, `func`, `cx`, `es'`, `R`] assume_tac) >>
  irule frag_exec_conseq >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >> irule len_vv_post_load >>
  simp[] >> qexistsl [`s1`, `sm`, `tv`, `vv`] >> simp[]
QED

Theorem len_load_extends[local]:
  !ctor pop loc sa op sb.
    compile_builtin_len ctor pop loc sa = (op,sb) /\
    loc <> LocCode ==> cs_extends sa sb
Proof
  rpt gen_tac >> strip_tac >> Cases_on `loc` >>
  gvs[compile_builtin_len_def, compile_ptr_load_def] >>
  drule emitted_insts_emit_op >> drule emit_op_extends >> rpt strip_tac >>
  irule cs_extends_same_block >> gvs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND3]
QED

Theorem expr_sim_pre_runtime_typed:
  !cenv cx env e es tv es'.
    expr_sim_pre cenv cx env e es /\ eval_expr cx e es = (INL tv,es') ==>
    ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
          toplevel_value_typed tv tvt
Proof
  rpt gen_tac >> strip_tac >> drule_all expr_sim_pre_eval >>
  simp[expr_result_typed_def, expr_runtime_typed_def] >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  metis_tac[]
QED

Theorem sized_expr_vv_res_ok:
  !cenv cx env e es res es'.
    expr_sim_pre cenv cx env e es /\ is_sized_type (expr_type e) /\
    eval_expr cx e es = (res,es') ==> expr_vv_res_ok res
Proof
  rpt gen_tac >> strip_tac >> Cases_on `res`
  >- (drule_all expr_sim_pre_runtime_typed >> strip_tac >>
      drule sized_type_cases >> strip_tac >>
      Cases_on `x` >>
      gvs[expr_vv_res_ok_def, expr_res_ok_def, evaluate_type_def,
          toplevel_value_typed_def, AllCaseEqs()]) >>
  drule_all expr_sim_pre_eval >> strip_tac >>
  drule (cj 1 eval_expr_no_control) >>
  rename1 `INR exc` >> Cases_on `exc` >>
  gvs[expr_vv_res_ok_def, expr_res_ok_def, no_control_exc_def,
      no_type_error_result_def] >>
  rename1 `Error err` >> Cases_on `err` >> gvs[]
QED

Theorem sized_toplevel_length:
  !tenv t tvt tv cx es.
    is_sized_type t /\ evaluate_type tenv t = SOME tvt /\
    toplevel_value_typed tv tvt ==>
    ?n. toplevel_array_length cx tv es = (INL n,es)
Proof
  rpt gen_tac >> strip_tac >> drule sized_type_cases >> strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs()] >> Cases_on `tv` >>
  gvs[toplevel_value_typed_def]
  >~ [`value_has_type _ v`]
  >- (Cases_on `v` >>
      gvs[value_has_type_def, toplevel_array_length_def, return_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >>
      gvs[value_has_type_def, toplevel_array_length_def, return_def])
  >~ [`value_has_type (BaseTV (StringT k)) v`]
  >- (Cases_on `v` >> gvs[value_has_type_def, toplevel_array_length_def, return_def])
  >~ [`value_has_type (BaseTV (BytesT (Dynamic k))) v`]
  >- (Cases_on `v` >> gvs[value_has_type_def, toplevel_array_length_def, return_def]) >>
  rename1 `ArrayRef tr slot etv (Dynamic k)` >> Cases_on `tr` >>
  simp[toplevel_array_length_def, get_storage_backend_def,
       get_transient_storage_def, get_accounts_def, bind_def, return_def]
QED

Theorem compile_len_singleton_sim[local]:
  !cenv e. expr_vv_ok cenv e /\
    (!ty st. vv_location (FST (compile_expr cenv ty e st)) <> SOME LocCode) ==>
    expr_vv_ok cenv (Builtin (BaseT (UintT 256)) Len [e])
Proof
  rpt gen_tac >> strip_tac >> rw[expr_vv_ok_def] >>
  `is_sized_type (expr_type e)` by (drule len_pre_args >> simp[]) >>
  `expr_sim_pre cenv cx env e es` by
    (drule expr_sim_pre_builtin_arg >>
     disch_then (qspecl_then [`e`, `es`] mp_tac) >> fs[expr_sim_pre_def]) >>
  `expr_vv_sim ctx func cenv cx ty e es` by metis_tac[expr_vv_ok_def] >>
  simp[expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
  gvs[compile_expr_len] >> pairarg_tac >> gvs[] >>
  rename1 `compile_expr cenv ty e sa = (evv, sm)` >>
  Cases_on `compile_builtin_len cenv.ce_is_ctor (vv_operand evv)
    (case vv_location evv of SOME l => l | NONE => LocMemory) sm` >>
  gvs[as_stack_val_def] >>
  `vv_location evv <> SOME LocCode` by
    (first_x_assum (qspecl_then [`ty`, `sa`] mp_tac) >> simp[]) >>
  `(case vv_location evv of SOME l => l | NONE => LocMemory) <> LocCode` by
    (Cases_on `vv_location evv` >> gvs[]) >>
  drule_all len_load_extends >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  Cases_on `eval_expr cx e es` >> rename1 `_ = (er, es1)` >>
  `expr_vv_res_ok er` by (drule_all sized_expr_vv_res_ok >> simp[]) >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _` mp_tac >>
  simp[expr_vv_sim_def] >>
  disch_then drule_all >> disch_then (qspec_then `s0` assume_tac) >>
  Cases_on `er` >> gvs[eval_expr_len, bind_def, return_def]
  >- (rename1 `eval_expr cx e es = (INL etv, _)` >>
      drule_all expr_sim_pre_runtime_typed >> strip_tac >>
      drule_all sized_toplevel_length >>
      disch_then (qspecl_then [`cx`, `es1`] strip_assume_tac) >> gvs[] >>
      irule frag_exec_seq >>
      qexistsl_tac [`\s. vv_post func cenv cx e es sa sm s0 es' etv evv s`, `sm`] >>
      simp[expr_exit_def] >>
      conj_tac >- (irule frag_exec_conseq >> goal_assum (drule_at Any) >> simp[expr_exit_def]) >>
      simp[SF ETA_ss] >> irule compile_len_vv_frag >> goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[]) >>
  irule frag_exec_exit_prefix >> goal_assum (drule_at Any) >> simp[]
QED

Theorem compile_len_loc_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) /\
    (!ty st. vv_location (FST (compile_expr cenv ty (HD args) st)) <>
             SOME LocCode) ==>
    expr_vv_ok cenv (Builtin ann Len args)
Proof
  rpt gen_tac >> strip_tac >> rw[expr_vv_ok_def] >>
  drule len_pre_args >> strip_tac >> gvs[] >>
  `expr_ok cenv e` by fs[expr_sim_below_def] >>
  `expr_vv_ok cenv (Builtin (BaseT (UintT 256)) Len [e])` by
    (irule compile_len_singleton_sim >> fs[expr_ok_def]) >>
  metis_tac[expr_vv_ok_def]
QED
