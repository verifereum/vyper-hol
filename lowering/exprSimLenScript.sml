(*
 * Expression simulation: len (#636, Builtins row 1)
 *
 * len(x) lowers x to its value_vv, a pointer, and loads the word at it
 * from x's location (compile_builtin_len): the length word of a dynamic
 * array, bytes or string in memory, storage or transient storage, or, at
 * runtime, in the data section for an immutable (DLOAD), where
 * immutables_rel lays it out as in memory.  The source reads the same
 * length (result_array_length).  An operand in code in the constructor
 * is left to exprSimBuiltins' compile_len_ctor_code_case.
 *
 * TOP-LEVEL:
 *   compile_len_vv_case — expr_vv_case of Len, but for an operand in code
 *                         in the constructor
 *
 * The captured operand is read only at the length boundary. Successful
 * reads supply decoded-value typing; storage decoding additionally relates
 * the raw header to that decoded length. The header and fragment lemmas
 * preserve this distinction for memory, storage and transient operands.
 *)

Theory exprSimLen
Ancestors
  list fragExec exprSim exprSimHyps exprSimWordBuiltins exprBopLowering exprLowering
  exprLoweringProps builtinSimple emitHelper compileEnv accountsRelProps
  valueEncoding
  venomExecSemantics venomInst venomState vyperAST vyperInterpreter vyperState
  vyperContext vyperTypeSystem vyperTypeBuiltins vyperValue vyperTyping vyperStorage
  builtinProps vyperTypeInvariants context freshWrites loweringSlice emitHelperProps
  exprSimUnwrap vyperTypeExprResult vyperTypeExprSoundness vyperExprNoControl

Theorem len_pre_args[local]:
  !cenv cx env ann args es.
    expr_body_pre cenv cx env (Builtin ann Len args) es ==>
    ?e. args = [e] /\ ann = BaseT (UintT 256) /\
        is_sized_type (expr_type e)
Proof
  rpt gen_tac >>
  simp[expr_body_pre_def, well_typed_expr_def,
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
         (compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca (vv_operand vv)
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
        n <- result_array_length cx tv;
        return (Value (IntV (&n))) od) es
Proof
  rpt gen_tac >>
  simp[Once evaluate_def, builtin_args_length_ok_def, type_check_def,
       assert_def, bind_def, ignore_bind_def, return_def] >>
  Cases_on `eval_expr cx e es` >>
  rename1 `(res, es1)` >> Cases_on `res` >> simp[bind_def] >>
  rename1 `result_array_length cx tv es1` >>
  Cases_on `result_array_length cx tv es1` >>
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
    ?n. result_array_length cx (Value v) es = (INL n, es) /\
        mem_word_at a mem = n2w n
Proof
  rpt gen_tac >> strip_tac >>
  drule sized_type_cases >> strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >>
  gvs[value_has_type_def, val_in_memory_def, result_array_length_def, read_result_def, bind_def,
      return_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >>
  gvs[value_has_type_def, val_in_memory_def, result_array_length_def, read_result_def, bind_def,
      return_def]
QED

Theorem read_storage_array_length:
  !cx tr slot et k es v.
    read_result cx (PlaceR (StoragePlace tr slot (ArrayTV et (Dynamic k)))) es = (INL v, es) ==>
    result_array_length cx (Value v) es =
    result_array_length cx (PlaceR (StoragePlace tr slot (ArrayTV et (Dynamic k)))) es
Proof
  rpt gen_tac >> Cases_on `tr` >>
  simp[read_result_def, read_place_def, read_storage_slot_def, get_storage_backend_def,
       get_transient_storage_def, get_accounts_def, bind_def, return_def] >>
  qmatch_goalsub_abbrev_tac `lift_option dv` >>
  Cases_on `dv` >> simp[lift_option_def, raise_def, return_def, bind_def] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `decode_value _ _ _ = _` mp_tac >>
  simp[Once decode_value_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  drule vyperTypeStatePreservationTheory.decode_dyn_array_length >> strip_tac >>
  gvs[read_slot_def] >>
  simp[result_array_length_def, read_result_def, bind_def, get_storage_backend_def,
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
    ?n. result_array_length cx (Value v) es = (INL n, es) /\
        read_slot storage off = n2w n
Proof
  rpt gen_tac >> strip_tac >>
  drule sized_type_cases >> strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  qpat_x_assum `decode_value _ _ _ = _` mp_tac >>
  simp[Once decode_value_def, AllCaseEqs()] >> strip_tac >> gvs[]
  >~ [`decode_dyn_array _ _ _ _ = SOME _`]
  >- (drule vyperTypeStatePreservationTheory.decode_dyn_array_length >> strip_tac >>
      simp[result_array_length_def, read_result_def, bind_def, return_def] >>
      `MIN (w2n (read_slot storage off)) k = w2n (read_slot storage off)` by
        simp[arithmeticTheory.MIN_DEF] >>
      simp[wordsTheory.n2w_w2n]) >>
  gvs[decode_dyn_bytes_def] >>
  simp[result_array_length_def, read_result_def, bind_def, return_def, slots_to_bytes_length_exact,
       read_slots_length] >>
  qspec_then `w2n (lookup_storage (n2w off) storage)` mp_tac le_word_size_mul >>
  rw[arithmeticTheory.MIN_DEF, read_slot_def, wordsTheory.n2w_w2n] >>
  `32 * word_size (w2n (lookup_storage (n2w off) storage)) =
   w2n (lookup_storage (n2w off) storage)` by decide_tac >>
  simp[wordsTheory.n2w_w2n]
QED

Theorem sized_read_result_length:
  !env cx t tvt r es v.
    evaluate_type env.type_defs t = SOME tvt /\ is_sized_type t /\
    eval_result_typed (env,cx,es) r (Type t) /\
    read_result cx r es = (INL v,es) /\ value_has_type tvt v ==>
    result_array_length cx (Value v) es = result_array_length cx r es
Proof
  rpt gen_tac >> strip_tac >>
  gvs[eval_result_typed_def] >>
  Cases_on `r` >> gvs[read_result_def, return_def, raise_def] >>
  rename1 `runtime_place_typed cx es p tvt` >> Cases_on `p`
  >- (gvs[runtime_place_typed_def, place_type_value_def, return_def] >>
      drule sized_type_cases >> strip_tac >>
      gvs[evaluate_type_def, AllCaseEqs()]
      >- (irule read_storage_array_length >> simp[read_result_def]) >>
      gvs[result_array_length_def, read_result_def, return_def, bind_def, read_place_def]) >>
  gvs[result_array_length_def, read_result_def, return_def, bind_def]
QED

Theorem read_result_memory_header:
  !env cx t tvt r es v w mem n.
    evaluate_type env.type_defs t = SOME tvt /\ is_sized_type t /\
    eval_result_typed (env,cx,es) r (Type t) /\
    read_result cx r es = (INL v,es) /\ value_has_type tvt v /\
    val_in_memory tvt v w mem /\
    result_array_length cx r es = (INL n,es) ==>
    mem_word_at w mem = n2w n
Proof
  rpt gen_tac >> strip_tac >>
  drule_all sized_read_result_length >> strip_tac >>
  drule_all sized_memory_header >>
  disch_then (qspecl_then [`cx`, `es`] strip_assume_tac) >> gvs[]
QED

Theorem sized_read_result_length_success:
  !env cx t tvt r es v.
    evaluate_type env.type_defs t = SOME tvt /\ is_sized_type t /\
    eval_result_typed (env,cx,es) r (Type t) /\
    read_result cx r es = (INL v,es) /\ value_has_type tvt v ==>
    ?n. result_array_length cx r es = (INL n,es)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all sized_read_result_length >> strip_tac >>
  `?n. result_array_length cx (Value v) es = (INL n,es)` suffices_by metis_tac[] >>
  qpat_x_assum `result_array_length cx (Value v) es = _` kall_tac >>
  drule sized_type_cases >> strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs()] >> Cases_on `v` >>
  gvs[value_has_type_def, result_array_length_def, read_result_def, bind_def, return_def] >>
  rename1 `value_has_type _ (ArrayV av)` >> Cases_on `av` >>
  gvs[value_has_type_def, result_array_length_def, read_result_def, bind_def, return_def]
QED

Theorem expr_body_pre_runtime_typed:
  !cenv cx env e es r es'.
    expr_body_pre cenv cx env e es /\ eval_expr cx e es = (INL r,es') ==>
    ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
          eval_result_typed (env,cx,es') r (Type (expr_type e)) /\
          (!v. read_result cx r es' = (INL v,es') ==> value_has_type tvt v)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all expr_body_pre_eval_result >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  `?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt` by
    (gvs[eval_result_typed_def] >> Cases_on `r` >> gvs[]) >>
  qexists_tac `tvt` >> simp[] >> rpt strip_tac >>
  `(do result <- eval_expr cx e; read_result cx result od) es = (INL v,es')` by
    simp[bind_def] >>
  drule_all expr_body_pre_eval >> strip_tac >>
  gvs[expr_result_typed_def, expr_runtime_typed_def, value_runtime_typed_def,
      value_result_typed_def]
QED

Theorem expr_sim_pre_runtime_typed:
  !cenv cx env e es r es'.
    expr_sim_pre cenv cx env e es /\ eval_expr cx e es = (INL r,es') ==>
    ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
          eval_result_typed (env,cx,es') r (Type (expr_type e)) /\
          (!v. read_result cx r es' = (INL v,es') ==> value_has_type tvt v)
Proof
  metis_tac[expr_body_pre_runtime_typed, expr_sim_pre_body_pre]
QED

Theorem storage_holds_header:
  !env cx tr t tvt tv w es n.
    storage_holds cx tr t tv w es /\
    evaluate_type (get_tenv cx) t = SOME tvt /\ is_sized_type t /\
    env.type_defs = get_tenv cx /\
    eval_result_typed (env,cx,es) tv (Type t) /\
    (!v. read_result cx tv es = (INL v,es) ==> value_has_type tvt v) /\
    result_array_length cx tv es = (INL n, es) ==>
    lookup_storage w
      (if tr then lookup_transient_storage cx.txn.target es.tStorage
       else (lookup_account cx.txn.target es.accounts).storage) = n2w n /\
    storage_read_live cx tr (get_storage cx es tr) w tvt /\
    0 < type_slot_size tvt
Proof
  rpt gen_tac >> simp[storage_holds_def] >> strip_tac >> gvs[] >>
  `0 < type_slot_size tvt` by
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

(* At runtime the value at an immutable's code pointer is in the data
   section, laid out as in memory. *)
Theorem immutable_holds_data[local]:
  !func cenv cx es s t tv w.
    stmt_state_rel func cenv cx es s /\ ~cenv.ce_is_ctor /\
    immutable_holds cenv cx t tv w es ==>
    ?tvt v. evaluate_type (get_tenv cx) t = SOME tvt /\
            read_result cx tv es = (INL v, es) /\
            val_in_memory tvt v (w2n w) s.vs_data_section
Proof
  rw[immutable_holds_def, stmt_state_rel_def, state_rel_def,
     immutables_rel_def] >>
  gvs[] >> first_x_assum drule_all >> strip_tac >>
  gvs[sub_layout_def] >> first_x_assum drule >> strip_tac >>
  `off + k < dimword (:256)` by DECIDE_TAC >>
  gvs[arithmeticTheory.ADD_COMM]
QED

Theorem vv_holds_len_header:
  !env func cenv cx es s t tvt tv vv n.
    stmt_state_rel func cenv cx es s /\ vv_holds cenv cx t tv vv es s /\
    is_sized_type t /\ evaluate_type (get_tenv cx) t = SOME tvt /\
    env.type_defs = get_tenv cx /\
    eval_result_typed (env,cx,es) tv (Type t) /\
    (!v. read_result cx tv es = (INL v,es) ==> value_has_type tvt v) /\
    (vv_location vv = SOME LocCode ==> ~cenv.ce_is_ctor) /\
    result_array_length cx tv es = (INL n, es) ==>
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
      gvs[] >>
      `evaluate_type env.type_defs t = SOME tvt` by simp[] >>
      drule_all read_result_memory_header >> strip_tac >>
      gvs[ptr_load_val_def, mload_def, mem_word_at_def]) >>
  rename1 `p.ptr_location` >> Cases_on `p.ptr_location` >> gvs[]
  >~ [`val_in_memory _ _ _ _`]
  >- (`evaluate_type env.type_defs t = SOME tvt` by simp[] >>
      `value_has_type tvt v` by metis_tac[] >>
      drule_all read_result_memory_header >>
      simp[ptr_load_val_def, mload_def, mem_word_at_def])
  >~ [`immutable_holds`]
  >- (drule_all immutable_holds_data >> strip_tac >> gvs[] >>
      `evaluate_type env.type_defs t = SOME tvt` by simp[] >>
      `value_has_type tvt v` by metis_tac[] >>
      drule_all read_result_memory_header >>
      simp[ptr_load_val_def, mem_word_at_def]) >>
  drule_all storage_holds_header >> strip_tac >>
  `s.vs_call_ctx.cc_address = cx.txn.target` by
    gvs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  gvs[stmt_state_rel_def, state_rel_def, storage_rel_def, transient_rel_def,
      ptr_load_val_def, sload_def, tload_def, contract_storage_def,
      contract_transient_def, vyperStorageBackendTheory.get_storage_def,
      vfmExecutionTheory.lookup_transient_storage_def,
      vfmStateTheory.lookup_account_def] >>
  drule_all storage_agree_read_head >> simp[]
QED

Theorem vv_holds_sized_length_success:
  !env cenv cx t r vv es s tvt.
    vv_holds cenv cx t r vv es s /\ is_sized_type t /\
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
  >- simp[vv_holds_def, read_result_def, return_def, expr_val_rel_def, expr_type_def, is_word_type_def,
          evaluate_type_def, typed_val_to_w256_def, val_to_w256_def,
          integer_wordTheory.i2w_def]
  >~ [`vv_at`]
  >- simp[vv_at_def, expr_val_at_def, expr_type_def, is_word_type_def]
  >~ [`lookup_var x s`]
  >- (fs[vv_post_def] >> metis_tac[not_fresh_at_mono])
  >~ [`FLOOKUP s.vs_allocas`] >- (fs[vv_post_def] >> metis_tac[])
  >~ [`locals_kept`]
  >- (fs[vv_post_def] >> metis_tac[locals_kept_mem_tail]) >>
  fs[vv_post_def] >> metis_tac[]
QED

Theorem len_load_frag[local]:
  !ctx func cenv cx es is_ctor imm pop loc sm op sb s0 w R.
    compile_builtin_len is_ctor imm pop loc sm = (op, sb) /\
    (loc = LocCode ==> ~is_ctor) /\ loc <> LocCalldata /\
    local_ptrs_reserved cenv sm /\
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
  gvs[compile_builtin_len_def, compile_ptr_load_def,
      compile_imm_load_word_runtime, ptr_load_val_def] >>
  irule emit_op_frag >> (reverse conj_tac >- simp[])
  >~ [`emit_op MLOAD [pop] sm = _`]
  >- (qexistsl [`[pop]`, `MLOAD`] >> simp[is_terminator_def] >>
      rpt strip_tac >> simp[step_inst_base_def, exec_read1_def])
  >~ [`emit_op SLOAD [pop] sm = _`]
  >- (qexistsl [`[pop]`, `SLOAD`] >> simp[is_terminator_def] >>
      rpt strip_tac >> simp[step_inst_base_def, exec_read1_def])
  >~ [`emit_op DLOAD [pop] sm = _`]
  >- (qexistsl [`[pop]`, `DLOAD`] >> simp[is_terminator_def] >>
      rpt strip_tac >> simp[step_inst_base_def, exec_read1_def]) >>
  qexistsl [`[pop]`, `TLOAD`] >> simp[is_terminator_def] >>
  rpt strip_tac >> simp[step_inst_base_def, exec_read1_def]
QED

Theorem compile_len_vv_frag[local]:
  !env ctx func cenv cx e es sa sm sb s0 es' tv vv op tvt R.
    compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca (vv_operand vv)
      (case vv_location vv of SOME l => l | NONE => LocMemory) sm = (op,sb) /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    is_sized_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    env.type_defs = get_tenv cx /\
    eval_result_typed (env,cx,es') tv (Type (expr_type e)) /\
    (!v. read_result cx tv es' = (INL v,es') ==> value_has_type tvt v) /\
    (vv_location vv = SOME LocCode ==> ~cenv.ce_is_ctor) ==>
    frag_exec ctx sm sb (vv_post func cenv cx e es sa sm s0 es' tv vv)
      (\s. ?n. result_array_length cx tv es' = (INL n,es') /\
        vv_post func cenv cx (Builtin (BaseT (UintT 256)) Len [e]) es
          sa sb s0 es' (Value (IntV (&n)))
          (StackValue (BaseT (UintT 256)) op) s) R
Proof
  rpt gen_tac >> strip_tac >> irule frag_exec_pointwise >>
  qx_gen_tac `s1` >> strip_tac >>
  `stmt_state_rel func cenv cx es' s1 /\
   vv_holds cenv cx (expr_type e) tv vv es' s1` by fs[vv_post_def] >>
  drule_all vv_holds_sized_length_success >> strip_tac >>
  drule_all vv_holds_len_header >> strip_tac >>
  ` (case vv_location vv of SOME l => l | NONE => LocMemory) <> LocCalldata` by
    (Cases_on `vv` >> gvs[vv_location_def, vv_holds_def] >>
     Cases_on `p.ptr_location` >> gvs[]) >>
  `(case vv_location vv of SOME l => l | NONE => LocMemory) = LocCode ==>
   ~cenv.ce_is_ctor` by
    (Cases_on `vv_location vv` >> gvs[]) >>
  drule_all len_load_frag >>
  disch_then (qspecl_then [`ctx`, `func`, `cx`, `es'`, `R`] assume_tac) >>
  irule frag_exec_conseq >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >>
  irule len_vv_post_load >>
  simp[] >> qexistsl [`s1`, `sm`, `tv`, `vv`] >> simp[]
QED

Theorem len_load_extends[local]:
  !ctor imm pop loc sa op sb.
    compile_builtin_len ctor imm pop loc sa = (op,sb) /\
    (loc = LocCode ==> ~ctor) ==> cs_extends sa sb
Proof
  rpt gen_tac >> strip_tac >> Cases_on `loc` >>
  gvs[compile_builtin_len_def, compile_ptr_load_def,
      compile_imm_load_word_runtime] >>
  drule emitted_insts_emit_op >> drule emit_op_extends >> rpt strip_tac >>
  irule cs_extends_same_block >> gvs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND3]
QED


Theorem compile_len_singleton_sim[local]:
  !ctx func cenv cx env ty e es.
    expr_body_pre cenv cx env (Builtin (BaseT (UintT 256)) Len [e]) es /\
    expr_vv_sim ctx func cenv cx ty e es /\
    (!ty st. vv_location (FST (compile_expr cenv ty e st)) = SOME LocCode ==>
             ~cenv.ce_is_ctor) ==>
    expr_vv_sim ctx func cenv cx ty (Builtin (BaseT (UintT 256)) Len [e]) es
Proof
  rpt gen_tac >> strip_tac >>
  `is_sized_type (expr_type e)` by (drule len_pre_args >> simp[]) >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >>
     disch_then (qspecl_then [`e`, `es`] mp_tac) >> fs[expr_body_pre_def]) >>
  simp[expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
  gvs[compile_expr_len] >> pairarg_tac >> gvs[] >>
  rename1 `compile_expr cenv ty e sa = (evv, sm)` >>
  Cases_on `compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca (vv_operand evv)
    (case vv_location evv of SOME l => l | NONE => LocMemory) sm` >>
  gvs[as_stack_val_def] >>
  `(case vv_location evv of SOME l => l | NONE => LocMemory) = LocCode ==>
   ~cenv.ce_is_ctor` by
    (Cases_on `vv_location evv` >> gvs[] >>
     first_x_assum (qspecl_then [`ty`, `sa`] mp_tac) >> simp[]) >>
  drule_all len_load_extends >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  Cases_on `eval_expr cx e es` >> rename1 `_ = (er, es1)` >>
  `expr_vv_res_ok er` by (drule_all expr_body_pre_vv_res_ok >> simp[]) >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _` mp_tac >>
  simp[expr_vv_sim_def] >>
  disch_then drule_all >> disch_then (qspec_then `s0` assume_tac) >>
  Cases_on `er` >> gvs[eval_expr_len, bind_def, return_def]
  >- (rename1 `eval_expr cx e es = (INL etv, _)` >>
      drule_all expr_body_pre_runtime_typed >> strip_tac >>
      `env.type_defs = get_tenv cx` by
        fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
           env_context_consistent_def] >>
      Cases_on `result_array_length cx etv es1` >>
      rename1 `result_array_length cx etv es1 = (lr,ls)` >>
      `ls = es1` by metis_tac[vyperStatePreservationTheory.result_array_length_state] >>
      gvs[] >>
      irule frag_exec_seq >>
      qexistsl_tac [`\s. vv_post func cenv cx e es sa sm s0 es1 etv evv s`, `sm`] >>
      simp[expr_exit_def] >>
      conj_tac >- (irule frag_exec_conseq >> goal_assum (drule_at Any) >> simp[expr_exit_def]) >>
      `vv_location evv = SOME LocCode ==> ~cenv.ce_is_ctor` by
        (first_x_assum (qspecl_then [`ty`, `sa`] mp_tac) >> simp[]) >>
      drule_all compile_len_vv_frag >>
      disch_then (qspecl_then [`ctx`, `func`, `es`, `s0`, `expr_exit res`] mp_tac) >>
      disch_then (fn th => irule frag_exec_conseq >> irule_at Any th) >>
      simp[expr_exit_def] >> rpt strip_tac >>
      Cases_on `lr` >> gvs[]) >>
  irule frag_exec_exit_prefix >> goal_assum (drule_at Any) >> simp[]
QED

Theorem compile_len_vv_case:
  !nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args /\
    (!ty st. vv_location (FST (compile_expr cenv ty (HD args) st)) =
             SOME LocCode ==> ~cenv.ce_is_ctor) ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann Len args)
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[expr_vv_case_def] >>
  rpt strip_tac >> drule len_pre_args >> strip_tac >> gvs[exprs_case_def] >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >> disch_then irule >>
     gvs[expr_body_pre_def]) >>
  `expr_vv_sim ctx func cenv cx ty e es` by
    (qpat_x_assum `expr_vv_case _ _ _ _ _ _`
       (qspecl_then [`env`, `ty`, `es`] irule o REWRITE_RULE [expr_vv_case_def]) >>
     metis_tac[int_calls_builtin_arg, listTheory.MEM]) >>
  irule compile_len_singleton_sim >> simp[] >> metis_tac[]
QED
