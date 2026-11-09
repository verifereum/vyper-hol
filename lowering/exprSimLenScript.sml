(*
 * Expression simulation: len (#636, Builtins row 1)
 *
 * len(x) lowers x to its value_vv, a pointer, and loads the word at it
 * from x's location (compile_builtin_len): the length word of a dynamic
 * array, bytes or string in memory, storage or transient storage, or of an
 * immutable, laid out by immutables_rel as in memory: at runtime in the
 * data section (DLOAD), in the constructor in the staged memory (ILOAD at
 * the offset plus the immutable base, which holds 0).  The source reads the
 * same length (result_array_length).
 *
 * TOP-LEVEL:
 *   compile_len_vv_case — expr_vv_case of Len
 *
 * The captured operand is read only at the length boundary. Successful
 * reads supply decoded-value typing; storage decoding additionally relates
 * the raw header to that decoded length. The header and fragment lemmas
 * preserve this distinction for memory, storage and transient operands.
 *)

Theory exprSimLen
Ancestors
  exprSimSource
  exprSimProps
  exprSimHypsDefs
  exprSimDefs
  loweringPosts
  list fragExec  exprSimHyps exprSimWordBuiltins exprBopLowering exprLowering
  exprLoweringProps builtinSimple emitHelper compileEnv accountsRelProps
  valueEncoding
  venomExecSemantics venomInst venomState vyperAST vyperInterpreter vyperState
  vyperContext vyperTypeSystem vyperTypeBuiltins vyperValue vyperTyping vyperStorage
  builtinProps vyperTypeInvariants context freshWrites loweringSlice emitHelperProps
  exprSimUnwrap exprSimCopy vyperTypeExprResult vyperTypeExprSoundness vyperExprNoControl

open gasContextTheory gasOutcomeTheory gasSummaryTheory gasSummaryComposeTheory
     gasExemptCertTheory fragGasModeTheory fragGasPathTheory;

Theorem len_pre_args:
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

Theorem names_builtin_len:
  !args. ~names_builtin Len args
Proof
  `!bt args. names_builtin bt args ==> bt <> Len` suffices_by
    metis_tac[] >>
  ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]
QED

Theorem compile_expr_len:
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

Theorem eval_expr_len:
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

Theorem sized_type_cases:
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
  !env cx tr t tvt tv w es s n.
    storage_holds cx tr t tv w es s /\
    evaluate_type (get_tenv cx) t = SOME tvt /\ is_sized_type t /\
    env.type_defs = get_tenv cx /\
    eval_result_typed (env,cx,es) tv (Type t) /\
    (!v. read_result cx tv es = (INL v,es) ==> value_has_type tvt v) /\
    result_array_length cx tv es = (INL n, es) ==>
    lookup_storage w
      (if tr then lookup_transient_storage cx.txn.target es.tStorage
       else (lookup_account cx.txn.target es.accounts).storage) = n2w n /\
    storage_range_agree (get_storage cx es tr)
      (if tr then contract_transient s else contract_storage s) w tvt /\
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

(* In the constructor the value at an immutable's code pointer is in the
   staged memory. *)
Theorem immutable_holds_memory[local]:
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

Theorem vv_holds_len_header:
  !env func cenv cx es s t tvt tv vv n ctx.
    stmt_state_rel ctx func cenv cx es s /\ vv_holds cenv cx t tv vv es s /\
    is_sized_type t /\ evaluate_type (get_tenv cx) t = SOME tvt /\
    env.type_defs = get_tenv cx /\
    eval_result_typed (env,cx,es) tv (Type t) /\
    (!v. read_result cx tv es = (INL v,es) ==> value_has_type tvt v) /\
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
  >- (Cases_on `cenv.ce_is_ctor`
      >- (drule_all immutable_holds_memory >> strip_tac >> gvs[] >>
          `evaluate_type env.type_defs t = SOME tvt` by simp[] >>
          `value_has_type tvt v` by metis_tac[] >>
          drule_all read_result_memory_header >>
          simp[ptr_load_val_def, mload_def, mem_word_at_def]) >>
      drule_all immutable_holds_data >> strip_tac >> gvs[] >>
      `evaluate_type env.type_defs t = SOME tvt` by simp[] >>
      `value_has_type tvt v` by metis_tac[] >>
      drule_all read_result_memory_header >>
      simp[ptr_load_val_def, mem_word_at_def]) >>
  drule_all storage_holds_header >> strip_tac >>
  drule_all storage_range_agree_head >>
  gvs[ptr_load_val_def, sload_def, tload_def,
      vyperStorageBackendTheory.get_storage_def,
      vfmExecutionTheory.lookup_transient_storage_def,
      vfmStateTheory.lookup_account_def]
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

Theorem len_vv_post_load:
  !func cenv cx e es sa sm sb s0 es' tv vv s1 op s n ctx.
    vv_post ctx func cenv cx e es sa sm s0 es' tv vv s1 /\
    sa.cs_next_var <= sm.cs_next_var /\
    stmt_state_rel ctx func cenv cx es' s /\ eval_operand op s = SOME (n2w n) /\
    (!x w. not_fresh_at sm x /\ lookup_var x s1 = SOME w ==>
           lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s1.vs_allocas aid = SOME b ==>
             FLOOKUP s.vs_allocas aid = SOME b) /\ s.vs_memory = s1.vs_memory ==>
    vv_post ctx func cenv cx (Builtin (BaseT (UintT 256)) Len [e]) es
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
  >- (fs[vv_post_def] >> metis_tac[locals_kept_mem_tail])
  >~ [`pure_frame`]
  >- (match_mp_tac pure_frame_mem_tail >> qexists_tac `s1` >>
      fs[vv_post_def, expr_has_effect_thm]) >>
  fs[vv_post_def] >> metis_tac[]
QED

Theorem len_load_frag[local]:
  !ctx func cenv cx es is_ctor pop loc sm op sb s0 w R.
    compile_builtin_len is_ctor cenv.ce_imm_alloca pop loc sm = (op, sb) /\
    loc <> LocCalldata /\ local_ptrs_reserved cenv sm /\
    eval_operand pop s0 = SOME w ==>
    frag_exec ctx sm sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. stmt_state_rel ctx func cenv cx es s /\
           eval_operand op s = SOME (ptr_load_val is_ctor loc w s0) /\
           (!x w'. not_fresh_at sm x /\ lookup_var x s0 = SOME w' ==>
                   lookup_var x s = SOME w') /\
           (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                    FLOOKUP s.vs_allocas aid = SOME b) /\
           s.vs_memory = s0.vs_memory) R
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `loc = LocCode /\ is_ctor`
  >- (gvs[compile_builtin_len_def, compile_ptr_load_def, ptr_load_val_def] >>
      irule compile_imm_load_word_ctor_frag >> simp[] >>
      qexists_tac `pop` >> simp[]) >>
  Cases_on `loc` >>
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
    (!v. read_result cx tv es' = (INL v,es') ==> value_has_type tvt v) ==>
    frag_exec ctx sm sb (vv_post ctx func cenv cx e es sa sm s0 es' tv vv)
      (\s. ?n. result_array_length cx tv es' = (INL n,es') /\
        vv_post ctx func cenv cx (Builtin (BaseT (UintT 256)) Len [e]) es
          sa sb s0 es' (Value (IntV (&n)))
          (StackValue (BaseT (UintT 256)) op) s) R
Proof
  rpt gen_tac >> strip_tac >> irule frag_exec_pointwise >>
  qx_gen_tac `s1` >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es' s1 /\
   vv_holds cenv cx (expr_type e) tv vv es' s1` by fs[vv_post_def] >>
  drule_all vv_holds_sized_length_success >> strip_tac >>
  drule_all vv_holds_len_header >> strip_tac >>
  ` (case vv_location vv of SOME l => l | NONE => LocMemory) <> LocCalldata` by
    (Cases_on `vv` >> gvs[vv_location_def, vv_holds_def] >>
     Cases_on `p.ptr_location` >> gvs[]) >>
  drule_all len_load_frag >>
  disch_then (qspecl_then [`ctx`, `func`, `cx`, `es'`, `R`] assume_tac) >>
  irule frag_exec_conseq >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >>
  irule len_vv_post_load >>
  simp[] >> qexistsl [`s1`, `sm`, `tv`, `vv`] >> simp[]
QED

Theorem len_load_extends:
  !ctor imm pop loc sa op sb.
    compile_builtin_len ctor imm pop loc sa = (op,sb) ==> cs_extends sa sb
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `loc = LocCode /\ ctor`
  >- (gvs[compile_builtin_len_def, compile_ptr_load_def] >>
      metis_tac[compile_imm_load_word_appends, cs_appends_def]) >>
  Cases_on `loc` >>
  gvs[compile_builtin_len_def, compile_ptr_load_def,
      compile_imm_load_word_runtime] >>
  drule emitted_insts_emit_op >> drule emit_op_extends >> rpt strip_tac >>
  irule cs_extends_same_block >> gvs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND3]
QED


Theorem len_step_ILOAD[local]:
  !id a out s w.
    eval_operand a s = SOME w ==>
    step_inst_base (mk_inst id ILOAD [a] [out]) s =
    OK (update_var out (mload (w2n w) s) s)
Proof
  simp[step_inst_base_def, exec_read1_def, mk_inst_def]
QED
Theorem len_step_ADD_imm_base[local]:
  !ctx func cenv cx es id pop ib out s w.
    stmt_state_rel ctx func cenv cx es s /\
    cenv.ce_imm_alloca = SOME ib /\ eval_operand pop s = SOME w ==>
    step_inst_base (mk_inst id ADD [pop; ib] [out]) s =
    OK (update_var out w s)
Proof
  rpt strip_tac >>
  `eval_operand ib s = SOME 0w` by
    gvs[exprLoweringPropsTheory.stmt_state_rel_def, immutable_base_zero_def] >>
  simp[step_inst_base_def, exec_pure2_def, mk_inst_def, wordsTheory.WORD_ADD_0]
QED
Theorem len_emit_op_path[local]:
  !ctx func cenv cx es opc args sa op sb s0 w.
    emit_op opc args sa = (op, sb) /\ local_ptrs_reserved cenv sa /\
    fn_has_code sa sb func /\
    opc <> INVOKE /\ opc <> GAS /\ ~is_terminator opc /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (!out. step_inst_base (mk_inst sa.cs_next_id opc args [out]) s0 =
           OK (update_var out w s0)) ==>
    ?s. gas_path ctx func s0 0 (OK s) /\
        s.vs_current_bb = sb.cs_current_bb /\
        s.vs_inst_idx = LENGTH sb.cs_current_insts /\
        stmt_state_rel ctx func cenv cx es s /\ eval_operand op s = SOME w /\
        (!x w'. not_fresh_at sa x /\ lookup_var x s0 = SOME w' ==>
                lookup_var x s = SOME w') /\
        (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                 FLOOKUP s.vs_allocas aid = SOME b) /\
        s.vs_memory = s0.vs_memory
Proof
  rpt strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  qexists_tac `update_var out w s0 with vs_inst_idx := SUC s0.vs_inst_idx` >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `not_local_ptr cenv es.scopes out` by
    (qunabbrev_tac `out` >> irule local_ptrs_reserved_fresh >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `op = Var out /\ sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    gvs[Abbr `out`, emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  rpt conj_tac
  >- (qunabbrev_tac `out` >> irule emitHelperPropsTheory.emit_op_zero_path >>
      simp[] >> metis_tac[])
  >- simp[update_var_def]
  >- simp[update_var_def]
  >- (simp[stmt_state_rel_inst_idx] >> irule stmt_state_rel_update_var >>
      simp[])
  >- simp[eval_operand_def, lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
  >- (rpt strip_tac >> res_tac >>
      gvs[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE])
  >- simp[update_var_def] >>
  simp[update_var_def]
QED
Theorem len_emit_op_cs_extends[local]:
  !opc args sm op sb. emit_op opc args sm = (op, sb) ==> cs_extends sm sb
Proof
  rpt strip_tac >>
  `cs_appends (emit_op opc args)` by simp[cs_appends_emit_helpers] >>
  fs[cs_appends_def] >> first_x_assum drule >> simp[]
QED

Theorem len_imm_ctor_path[local]:
  !ctx func cenv cx es pop sm op sb s0 w.
    compile_imm_load_word T cenv.ce_imm_alloca pop sm = (op, sb) /\
    local_ptrs_reserved cenv sm /\ fn_has_code sm sb func /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sm.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sm.cs_current_insts /\
    eval_operand pop s0 = SOME w ==>
    ?s. gas_path ctx func s0 0 (OK s) /\
        s.vs_current_bb = sb.cs_current_bb /\
        s.vs_inst_idx = LENGTH sb.cs_current_insts /\
        stmt_state_rel ctx func cenv cx es s /\
        eval_operand op s = SOME (mload (w2n w) s0) /\
        (!x w'. not_fresh_at sm x /\ lookup_var x s0 = SOME w' ==>
                lookup_var x s = SOME w') /\
        (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                 FLOOKUP s.vs_allocas aid = SOME b) /\
        s.vs_memory = s0.vs_memory
Proof
  rpt strip_tac >> Cases_on `cenv.ce_imm_alloca` >>
  gvs[contextTheory.compile_imm_load_word_def]
  >- (drule len_emit_op_path >>
      disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `s0`,
        `mload (w2n w) s0`] mp_tac) >>
      impl_tac
      >- (simp[is_terminator_def] >> rpt strip_tac >> irule len_step_ILOAD >>
          simp[]) >>
      strip_tac >> goal_assum drule >> simp[]) >>
  rename1 `cenv.ce_imm_alloca = SOME ib` >>
  qpat_x_assum `comp_bind _ _ _ = _` mp_tac >>
  simp[comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `emit_op ADD [pop; ib] sm = (addr, sm1)` >>
  `cs_extends sm sm1 /\ cs_extends sm1 sb` by metis_tac[len_emit_op_cs_extends] >>
  `fn_has_code sm sm1 func /\ fn_has_code sm1 sb func` by
    metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved cenv sm1` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sm` >>
     gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
         comp_ignore_bind_def, comp_return_def, emit_def]) >>
  qpat_x_assum `emit_op ADD _ _ = _` assume_tac >>
  drule len_emit_op_path >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `s0`, `w`]
    mp_tac) >>
  impl_tac
  >- (simp[is_terminator_def] >> rpt strip_tac >>
      irule len_step_ADD_imm_base >> metis_tac[]) >>
  strip_tac >> rename1 `gas_path _ _ s0 0 (OK s1)` >>
  `~s1.vs_halted` by metis_tac[fragGasPathTheory.gas_path_normal] >>
  qpat_x_assum `emit_op ILOAD _ _ = _` assume_tac >>
  drule len_emit_op_path >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `s1`,
    `mload (w2n w) s1`] mp_tac) >>
  impl_tac
  >- (simp[is_terminator_def] >> rpt strip_tac >> irule len_step_ILOAD >>
      simp[]) >>
  strip_tac >> rename1 `gas_path _ _ s1 0 (OK s2)` >>
  qexists_tac `s2` >> gvs[mload_def] >>
  conj_tac
  >- (`0 = 0 + 0` by simp[] >> pop_assum SUBST1_TAC >>
      irule fragGasPathTheory.gas_path_then >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum irule >> conj_tac
  >- (first_x_assum irule >> simp[]) >>
  gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
      comp_ignore_bind_def, comp_return_def, emit_def, not_fresh_at_def]
QED

Theorem len_step_TLOAD[local]:
  !op1 v1 id out ss.
    eval_operand op1 ss = SOME v1 ==>
    step_inst_base (mk_inst id TLOAD [op1] [out]) ss =
      OK (update_var out (tload v1 ss) ss)
Proof
  rw[step_inst_base_def, exec_read1_def]
QED

Theorem len_load_path[local]:
  !ctx func cenv cx es is_ctor pop loc sm op sb s0 w.
    compile_builtin_len is_ctor cenv.ce_imm_alloca pop loc sm = (op, sb) /\
    loc <> LocCalldata /\ local_ptrs_reserved cenv sm /\ fn_has_code sm sb func /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sm.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sm.cs_current_insts /\
    eval_operand pop s0 = SOME w ==>
    ?s. gas_path ctx func s0 0 (OK s) /\
        s.vs_current_bb = sb.cs_current_bb /\
        s.vs_inst_idx = LENGTH sb.cs_current_insts /\
        stmt_state_rel ctx func cenv cx es s /\
        eval_operand op s = SOME (ptr_load_val is_ctor loc w s0) /\
        (!x w'. not_fresh_at sm x /\ lookup_var x s0 = SOME w' ==>
                lookup_var x s = SOME w') /\
        (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                 FLOOKUP s.vs_allocas aid = SOME b) /\
        s.vs_memory = s0.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `loc = LocCode /\ is_ctor`
  >- (gvs[compile_builtin_len_def, compile_ptr_load_def, ptr_load_val_def] >>
      drule_all len_imm_ctor_path >> simp[]) >>
  Cases_on `loc` >>
  gvs[compile_builtin_len_def, compile_ptr_load_def,
      compile_imm_load_word_runtime, ptr_load_val_def] >>
  drule len_emit_op_path >> disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `s0`] mp_tac) >>
  simp[is_terminator_def] >>
  disch_then irule >>
  rpt strip_tac >> metis_tac[step_MLOAD, step_SLOAD, step_DLOAD, len_step_TLOAD]
QED

Theorem len_option_rator[local]:
  !x f g s. (case (x : 'a option) of NONE => f | SOME v => g v) s =
            (case x of NONE => f s | SOME v => g v s)
Proof
  Cases >> simp[]
QED

Theorem len_gsb_obs:
  !cx tr st g.
    get_storage_backend cx tr (st with gas_obs := g) =
    (FST (get_storage_backend cx tr st), SND (get_storage_backend cx tr st) with gas_obs := g)
Proof
  Cases_on `tr` >>
  simp[get_storage_backend_def, bind_def, get_accounts_def,
       get_transient_storage_def, return_def]
QED

Theorem len_rss_obs:
  !cx tr sl tv st g.
    read_storage_slot cx tr sl tv (st with gas_obs := g) =
    (FST (read_storage_slot cx tr sl tv st),
     SND (read_storage_slot cx tr sl tv st) with gas_obs := g)
Proof
  rpt gen_tac >> simp[read_storage_slot_def, bind_def, len_gsb_obs] >>
  Cases_on `get_storage_backend cx tr st` >> Cases_on `q` >>
  simp[lift_option_def, return_def, raise_def] >>
  Cases_on `decode_value x (w2n sl) tv` >> simp[raise_def, return_def]
QED

Theorem len_rp_obs:
  !cx p st g.
    read_place cx p (st with gas_obs := g) =
    (FST (read_place cx p st), SND (read_place cx p st) with gas_obs := g)
Proof
  Cases_on `p`
  >- simp[read_place_def, len_rss_obs]
  >- (rpt gen_tac >>
      simp[read_place_def, bind_def, get_scopes_def, lift_option_type_def,
           lift_sum_def, return_def, raise_def] >>
      Cases_on `lookup_scopes s st.scopes` >> simp[raise_def] >>
      Cases_on `read_memory_path x l` >> simp[return_def, raise_def])
  >- (rpt gen_tac >>
      simp[read_place_def, bind_def, get_immutables_def, get_address_immutables_def,
           lift_option_type_def, lift_sum_def, return_def, raise_def] >>
      Cases_on `ALOOKUP st.immutables cx.txn.target` >> simp[raise_def] >>
      Cases_on `FLOOKUP (get_source_immutables o' x) s` >> simp[raise_def] >>
      Cases_on `evaluate_subscripts (FST x') (SND x') l` >> simp[return_def, raise_def])
QED

Theorem len_bind_obs:
  !m f.
    (!st g. m (st with gas_obs := g) = (FST (m st), SND (m st) with gas_obs := g)) /\
    (!v st g. f v (st with gas_obs := g) = (FST (f v st), SND (f v st) with gas_obs := g)) ==>
    !st g. bind m f (st with gas_obs := g) =
           (FST (bind m f st), SND (bind m f st) with gas_obs := g)
Proof
  rpt strip_tac >> simp[bind_def] >>
  Cases_on `m st` >> Cases_on `q` >> simp[]
QED

Theorem len_rr_obs:
  !cx res st g.
    read_result cx res (st with gas_obs := g) =
    (FST (read_result cx res st), SND (read_result cx res st) with gas_obs := g)
Proof
  Cases_on `res` >> simp[read_result_def, len_rp_obs, return_def, raise_def]
QED

Theorem len_tail_obs:
  !v st g.
    (case v of
       ArrayV (DynArrayV vs) => return (LENGTH vs)
     | ArrayV (SArrayV vs) => return (LENGTH vs)
     | ArrayV (TupleV vs) => return (LENGTH vs)
     | BytesV bs => return (LENGTH bs)
     | StringV bs => return (STRLEN bs)
     | _ => raise (Error (TypeError "result_array_length"))) (st with gas_obs := g) =
    (FST ((case v of
       ArrayV (DynArrayV vs) => return (LENGTH vs)
     | ArrayV (SArrayV vs) => return (LENGTH vs)
     | ArrayV (TupleV vs) => return (LENGTH vs)
     | BytesV bs => return (LENGTH bs)
     | StringV bs => return (STRLEN bs)
     | _ => raise (Error (TypeError "result_array_length"))) st),
     SND ((case v of
       ArrayV (DynArrayV vs) => return (LENGTH vs)
     | ArrayV (SArrayV vs) => return (LENGTH vs)
     | ArrayV (TupleV vs) => return (LENGTH vs)
     | BytesV bs => return (LENGTH bs)
     | StringV bs => return (STRLEN bs)
     | _ => raise (Error (TypeError "result_array_length"))) st) with gas_obs := g)
Proof
  Cases >> TRY (rename1 `ArrayV a` >> Cases_on `a`) >>
  simp[return_def, raise_def]
QED

Theorem len_ral_gas_obs0:
  !cx tv st g.
    result_array_length cx tv (st with gas_obs := g) =
    (FST (result_array_length cx tv st),
     SND (result_array_length cx tv st) with gas_obs := g)
Proof
  gen_tac >> gen_tac >>
  Cases_on `tv` >> TRY (rename1 `PlaceR p` >> Cases_on `p`) >>
  TRY (rename1 `StoragePlace tr sl tvv` >> Cases_on `tvv` >>
       TRY (rename1 `ArrayTV tv0 bd` >> Cases_on `bd`)) >>
  simp[result_array_length_def, return_def] >>
  TRY (irule len_bind_obs >> simp[len_rr_obs, len_tail_obs, return_def, raise_def] >> NO_TAC) >>
  rpt gen_tac >> simp[bind_def, len_gsb_obs] >>
  Cases_on `get_storage_backend cx tr st` >> Cases_on `q` >> simp[return_def]
QED

Theorem len_ral_gas_obs:
  !cx tv st g r.
    result_array_length cx tv st = (r, st) ==>
    result_array_length cx tv (st with gas_obs := g) = (r, st with gas_obs := g)
Proof
  rpt strip_tac >> simp[len_ral_gas_obs0]
QED

Theorem len_vv_path[local]:
  !env ctx func cenv cx e es sa sm sb s0 es' tv vv op tvt t.
    compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca (vv_operand vv)
      (case vv_location vv of SOME l => l | NONE => LocMemory) sm = (op,sb) /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    is_sized_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    env.type_defs = get_tenv cx /\
    eval_result_typed (env,cx,es') tv (Type (expr_type e)) /\
    (!v. read_result cx tv es' = (INL v,es') ==> value_has_type tvt v) /\
    fn_has_code sm sb func /\ ~t.vs_halted /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    vv_post ctx func cenv cx e es sa sm s0 es' tv vv t ==>
    ?t' n. gas_path ctx func t 0 (OK t') /\
      t'.vs_current_bb = sb.cs_current_bb /\
      t'.vs_inst_idx = LENGTH sb.cs_current_insts /\
      result_array_length cx tv es' = (INL n,es') /\
      vv_post ctx func cenv cx (Builtin (BaseT (UintT 256)) Len [e]) es
        sa sb s0 es' (Value (IntV (&n)))
        (StackValue (BaseT (UintT 256)) op) t'
Proof
  rpt gen_tac >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es' t /\
   vv_holds cenv cx (expr_type e) tv vv es' t` by fs[vv_post_def] >>
  drule_all vv_holds_sized_length_success >> strip_tac >>
  drule_all vv_holds_len_header >> strip_tac >>
  ` (case vv_location vv of SOME l => l | NONE => LocMemory) <> LocCalldata` by
    (Cases_on `vv` >> gvs[vv_location_def, vv_holds_def] >>
     Cases_on `p.ptr_location` >> gvs[]) >>
  drule_all len_load_path >> strip_tac >>
  qexistsl_tac [`s`, `n`] >> simp[] >>
  irule len_vv_post_load >>
  simp[] >> qexistsl [`t`, `sm`, `tv`, `vv`] >> simp[]
QED

Theorem len_source:
  !cx ann e.
    eval_expr cx (Builtin ann Len [e]) =
    bind (eval_expr cx e)
      (\tv. bind (result_array_length cx tv) (\n. return (Value (IntV (&n)))))
Proof
  rpt gen_tac >> simp[FUN_EQ_THM, eval_expr_len]
QED

Theorem len_operand_admissible:
  !cenv cx env e es.
    expr_body_pre cenv cx env e es ==>
    gas_admissible (eval_expr cx e) expr_vv_res_ok es
Proof
  rpt strip_tac >> simp[gas_admissible_def] >> rpt strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  metis_tac[expr_body_pre_vv_res_ok]
QED

Theorem len_exempt_cert:
  !memory tops p cx ann e start marks out endpoint.
    gas_exempt_cert memory tops p (ignore_bind (eval_expr cx e) (return ()))
      start marks out endpoint ==>
    gas_exempt_cert memory tops p
      (ignore_bind (eval_expr cx (Builtin ann Len [e])) (return ()))
      start marks out endpoint
Proof
  rpt strip_tac >> simp[len_source] >>
  PairCases_on `p` >> PairCases_on `start` >>
  PairCases_on `out` >> PairCases_on `endpoint` >>
  `ignore_bind
    (bind (eval_expr cx e)
      (\tv. bind (result_array_length cx tv) (\n. return (Value (IntV (&n))))))
    (return ()) =
   bind (eval_expr cx e)
     (\tv. ignore_bind (bind (result_array_length cx tv)
              (\n. return (Value (IntV (&n))))) (return ()))` by
    (simp[FUN_EQ_THM, ignore_bind_def, bind_def] >> gen_tac >>
     Cases_on `eval_expr cx e x` >> Cases_on `q` >> simp[] >>
     Cases_on `bind (result_array_length cx x') (\n. return (Value (IntV (&n)))) r` >>
     simp[]) >>
  pop_assum SUBST1_TAC >> irule gas_exempt_cert_error_result >> simp[]
QED

Theorem compile_len_singleton_sim[local]:
  !ctx func cenv cx env ty e es.
    expr_body_pre cenv cx env (Builtin (BaseT (UintT 256)) Len [e]) es /\
    expr_vv_sim ctx func cenv cx ty e es ==>
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
  drule_all len_load_extends >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  rename1 `compile_builtin_len _ _ _ _ _ = (lop, lsb)` >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[len_operand_admissible] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_def]) >>
  disch_then (qspecl_then [`sa`,`sm`,`evv`,`s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [gas_summary_at_def]) >>
      strip_tac
      >- (gvs[] >>
          rename1 `gas_marked_exec _ _ _ _ marks (INL tv) fe (OK t)` >>
          `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
             (INL tv, fe with gas_obs := [])` by
            (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
               (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
             strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
          `~t.vs_halted` by
            metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
          mp_tac (Q.SPECL [`cenv`,`cx`,`env`,`e`,
                    `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
                    `tv`,`fe with gas_obs := []`] expr_body_pre_runtime_typed) >>
          simp[] >> strip_tac >>
          mp_tac (Q.SPECL [`env`,`ctx`,`func`,`cenv`,`cx`,`e`,`es`,`sa`,`sm`,`lsb`,`s0`,
                    `fe with gas_obs := []`,`tv`,`evv`,`lop`,`tvt`,`t`] len_vv_path) >>
          (impl_tac >- simp[]) >> strip_tac >>
          `!tail. result_array_length cx tv (fe with gas_obs := tail) =
                  (INL n, fe with gas_obs := tail)` by
            (gen_tac >> drule len_ral_gas_obs >>
             disch_then (qspec_then `tail` mp_tac) >> simp[]) >>
          simp[gas_summary_at_def] >>
          qexistsl_tac [`INL (Value (IntV (&n)))`, `fe`, `OK t'`] >>
          conj_tac
          >- (rewrite_tac[len_source] >>
              irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
                       |> REWRITE_RULE [APPEND_NIL]) >>
              qexistsl_tac [`fe`,`t`,`tv`] >> simp[] >>
              simp[gas_marked_exec_def, gas_marked_path_def, bind_def, return_def,
                   gas_explicit_def]) >>
          simp[] >> metis_tac[]) >>
      Cases_on `res` >- gvs[] >>
      simp[gas_summary_at_def] >>
      rename1 `gas_marked_exec _ _ _ _ marks (INR exn) fe fr` >>
      qexistsl_tac [`INR exn`,`fe`,`fr`] >>
      simp[] >> conj_tac
      >- (rewrite_tac[len_source] >> irule gas_marked_exec_bind_exception >> simp[]) >>
      gvs[]) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  irule len_exempt_cert >> simp[]
QED

Theorem compile_len_vv_case:
  !nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
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
  irule compile_len_singleton_sim >> metis_tac[]
QED
