Theory exprSimHashes
Ancestors
  arithmetic list rich_list words exprSimHyps exprLowering exprLoweringProps
  compileEnv vyperAST vyperInterpreter vyperContext vyperTypeSystem vyperTypeInvariants vyperTyping
  vyperState vyperValue exprBopLowering valueEncoding valueEncodingProofs byte keccak
  venomExecSemantics venomInst venomState emitHelper builtinHashing
Libs
  pairLib supportedEvalLib cv_transLib

val () = supportedEvalLib.configure ();

Theorem well_typed_keccak256_args:
  !ann args.
    well_typed_builtin_app ann Keccak256 (MAP expr_type args) ==>
    ?e. args = [e] /\ ann = BaseT (BytesT (Fixed 32)) /\
        ((?m. expr_type e = BaseT (BytesT (Fixed m))) \/
         (?n. expr_type e = BaseT (BytesT (Dynamic n))) \/
         (?n. expr_type e = BaseT (StringT n)))
Proof
  rpt gen_tac >> simp[well_typed_builtin_app_def] >> strip_tac >>
  Cases_on `args` >> gvs[] >>
  rename1 `is_bytes_or_string_type (expr_type e)` >>
  Cases_on `expr_type e` >> gvs[] >>
  rename1 `is_bytes_or_string_type (BaseT bt)` >>
  Cases_on `bt` >> gvs[] >>
  rename1 `BytesT bd` >> Cases_on `bd` >> simp[]
QED

Theorem eval_expr_keccak256_cases:
  !cx ann e es res es'.
    eval_expr cx (Builtin ann Keccak256 [e]) es = (res, es') ==>
    (?exc. eval_expr cx e es = (INR exc, es') /\ res = INR exc) \/
    (?tv es1. eval_expr cx e es = (INL tv, es1) /\ !v. tv <> Value v) \/
    ?v. eval_expr cx e es = (INL (Value v), es') /\
        res = (case evaluate_builtin cx es'.accounts ann Keccak256 [expr_type e] [v] of
                 INL w => INL (Value w)
               | INR err => INR (Error err))
Proof
  rpt gen_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, builtin_args_length_ok_def] >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `_ = (r1, es1)` >>
  Cases_on `r1` >> simp[] >>
  rename1 `materialise cx tv es1` >>
  Cases_on `?v. tv = Value v` >> gvs[] >>
  simp[materialise_def, return_def] >>
  simp[Once evaluate_def, return_def, lift_sum_def, get_accounts_def] >>
  Cases_on `evaluate_builtin cx es1.accounts ann Keccak256 [expr_type e] [v]` >>
  simp[return_def, raise_def] >> rw[] >> gvs[]
QED

Definition keccak256_tail_def:
  keccak256_tail ty x =
    if is_bytestring_type ty then compile_keccak256_bytes x
    else case ty of
      BaseT (BytesT (Fixed m)) => compile_keccak256_bytesm x m
    | _ => compile_keccak256_word x
End

Theorem compile_expr_keccak256:
  !cenv ty ann e st.
    compile_expr cenv ty (Builtin ann Keccak256 [e]) st =
    compile_builtin_dispatch cenv ann ty Keccak256 [e] st
Proof
  rpt gen_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def)] >>
  Cases_on `e` >> simp[compile_expr_body_def, expr_size_def,
    list_size_def, expr_type_def]
QED

Theorem lower_value_keccak256:
  !cenv ty ann e sa op sb.
    lower_value compile_expr cenv ty (Builtin ann Keccak256 [e]) sa =
      (op, sb) ==>
    ?x s1.
      lower_value compile_expr cenv (expr_type e) e sa = (x, s1) /\
      keccak256_tail (expr_type e) x s1 = (op, sb)
Proof
  rpt strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[Once lower_value_def, comp_bind_def, compile_expr_keccak256] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[lower_value_child_call, vyperASTTheory.expr_size_def,
       listTheory.list_size_def, keccak256_tail_def] >>
  Cases_on `is_bytestring_type (expr_type e)` >> simp[]
  >- (rpt (pairarg_tac >> gvs[]) >>
      rw[] >> gvs[as_stack_val_pair, unwrap_value_def, comp_return_def]) >>
  Cases_on `expr_type e` >> simp[] >>
  TRY (rename1 `BaseT bt` >> Cases_on `bt` >> simp[]) >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd` >> simp[]) >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[as_stack_val_pair, unwrap_value_def, comp_return_def]
QED

Theorem fixed_bytes_encoding_readback:
  !bd bs.
    LENGTH bs <= 32 ==>
    TAKE (LENGTH bs)
      (word_to_bytes_be (typed_val_to_w256 (BaseTV (BytesT bd)) (BytesV bs))) = bs
Proof
  simp[typed_val_to_w256_def, word_of_bytes_be_pad_right,
       TAKE_word_to_bytes_be_word_of_bytes_be]
QED

Theorem keccak256_encoding:
  !bd bs.
    typed_val_to_w256 (BaseTV (BytesT bd)) (BytesV (Keccak_256_w64 bs)) =
    word_of_bytes T (0w : bytes32) (Keccak_256_w64 bs)
Proof
  simp[typed_val_to_w256_def, word_of_bytes_be_pad_right,
       word_of_bytes_be_def]
QED

Theorem hash_pointer_wrap_probe:
  w2n ((n2w (dimword(:256) - 32) : bytes32) + 32w) = 0 /\
  dimword(:256) - 32 + 32 = dimword(:256)
Proof
  simp[dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  wordsLib.WORD_DECIDE_TAC
QED

Definition hash_wrap_memory_def:
  hash_wrap_memory : byte list =
    0w :: (REPLICATE (dimword(:256) - 2) 0w ++ [1w; 1w])
End

Theorem hash_wrap_payload_probe:
  mem_bytes_at (dimword(:256)) 1 hash_wrap_memory = [1w] /\
  mem_bytes_at 0 1 hash_wrap_memory = [0w]
Proof
  simp[hash_wrap_memory_def, mem_bytes_at_def, DROP_APPEND,
       DROP_REPLICATE, TAKE_APPEND, EL_APPEND_EQN,

       dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``]
QED

Theorem hash_wrap_value_probe:
  val_in_memory (BaseTV (BytesT (Dynamic 1))) (BytesV [1w])
    (dimword(:256) - 32) hash_wrap_memory
Proof
  simp[val_in_memory_def] >> conj_tac
  >- (simp[hash_wrap_memory_def, mem_word_at_def, DROP_APPEND,
           DROP_REPLICATE, dimword_def,
           fcpLib.INDEX_CONV ``dimindex(:256)``] >> EVAL_TAC) >>
  simp[hash_wrap_memory_def, mem_bytes_at_def, DROP_APPEND,
       DROP_REPLICATE, TAKE_APPEND, EL_APPEND_EQN,
       dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``]
QED

Theorem hash_wrap_hashes_probe:
  word_of_bytes T (0w : bytes32) (Keccak_256_w64 [0w]) <>
  word_of_bytes T (0w : bytes32) (Keccak_256_w64 [1w])
Proof
  CONV_TAC (RAND_CONV (BINOP_CONV (RAND_CONV cv_eval))) >> EVAL_TAC
QED

Theorem hash_wrap_instruction_probe:
  !s.
    s.vs_memory = hash_wrap_memory ==>
    run_inst_seq
      [mk_inst 0 MLOAD [Lit (n2w (dimword(:256) - 32))] ["%0"];
       mk_inst 1 ADD [Lit (n2w (dimword(:256) - 32)); Lit 32w] ["%1"];
       mk_inst 2 SHA3 [Var "%1"; Var "%0"] ["%2"]] s =
    OK (update_var "%2" (word_of_bytes T 0w (Keccak_256_w64 [0w]))
          (update_var "%1" 0w (update_var "%0" 1w s)))
Proof
  rpt strip_tac >>
  `mload (dimword(:256) - 32) s = 1w` by
    (mp_tac hash_wrap_value_probe >>
     simp[val_in_memory_def, mem_word_at_def, mload_def]) >>
  pure_rewrite_tac[run_inst_seq_def, mk_inst_def] >>
  simp[Once step_inst_base_def, exec_read1_def, eval_operand_def] >>
  gvs[dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  simp[Once step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  simp[Once step_inst_base_def, eval_operand_def, lookup_var_def,
       update_var_def] >>
  simp[finite_mapTheory.FLOOKUP_UPDATE, hash_wrap_memory_def]
QED

Theorem hash_wrap_compiler_probe:
  !cs op cs'.
    cs.cs_next_id = 0 /\ cs.cs_next_var = 0 /\ cs.cs_current_insts = [] /\
    compile_keccak256_bytes (Lit (n2w (dimword(:256) - 32))) cs = (op, cs') ==>
    op = Var "%2" /\
    cs'.cs_current_insts =
      [mk_inst 0 MLOAD [Lit (n2w (dimword(:256) - 32))] ["%0"];
       mk_inst 1 ADD [Lit (n2w (dimword(:256) - 32)); Lit 32w] ["%1"];
       mk_inst 2 SHA3 [Var "%1"; Var "%0"] ["%2"]]
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_keccak256_bytes_def, emit_op_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
      emit_def] >> EVAL_TAC
QED

Theorem hash_wrap_compiled_run_probe:
  !cs op cs' s.
    cs.cs_next_id = 0 /\ cs.cs_next_var = 0 /\ cs.cs_current_insts = [] /\
    compile_keccak256_bytes (Lit (n2w (dimword(:256) - 32))) cs = (op, cs') /\
    s.vs_memory = hash_wrap_memory ==>
    run_inst_seq cs'.cs_current_insts s =
      OK (update_var "%2" (word_of_bytes T 0w (Keccak_256_w64 [0w]))
            (update_var "%1" 0w (update_var "%0" 1w s)))
Proof
  rpt strip_tac >> drule_all hash_wrap_compiler_probe >> strip_tac >>
  asm_rewrite_tac[] >> irule hash_wrap_instruction_probe >> asm_rewrite_tac[]
QED

Theorem hash_wrap_operand_size_probe:
  list_size expr_size [Name (BaseT (BytesT (Dynamic 1))) ""] = 6
Proof
  EVAL_TAC
QED

Theorem hash_wrap_small_expression_audit:
  expr_size (Name (BaseT BoolT) "") < 6 /\
  expr_size (TopLevelName (BaseT BoolT) (NONE, "")) < 6 /\
  expr_size (Builtin (BaseT BoolT) Len []) < 6
Proof
  EVAL_TAC
QED

Theorem hash_small_toplevel_size:
  !src. (src = NONE \/ src = SOME 0 \/ src = SOME 1) ==>
    expr_size (TopLevelName (BaseT BoolT) (src, "")) < 6
Proof
  rpt strip_tac >> gvs[expr_size_def, type_size_def, base_type_size_def]
QED

Theorem hash_toplevel_missing_compile:
  !cenv ty ann nsid st.
    FLOOKUP cenv.ce_vars (module_var_key nsid) = NONE ==>
    compile_expr cenv ty (TopLevelName ann nsid) st =
      (StackValue ann (Lit 0w), SND (emit_inst INVALID [] [] st))
Proof
  rpt strip_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def,
       expr_type_def] >> pairarg_tac >> simp[]
QED

Theorem hash_toplevel_immutable_eval:
  !cx ann src id es ts imms tv v.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = NONE /\
    get_immutables cx src es = (INL imms, es) /\
    FLOOKUP imms id = SOME (tv, v) ==>
    eval_expr cx (TopLevelName ann (src, id)) es = (INL (Value v), es)
Proof
  rpt strip_tac >> simp[Once evaluate_def, lookup_global_def,
    bind_def, lift_option_type_def, return_def]
QED

Theorem hash_small_other_module:
  !src. ?other.
    other <> src /\
    expr_size (TopLevelName (BaseT BoolT) (other, "")) < 6
Proof
  gen_tac >> Cases_on `src = NONE`
  >- (qexists_tac `SOME 0` >> gvs[] >> EVAL_TAC) >>
  qexists_tac `NONE` >> simp[] >> EVAL_TAC
QED

Definition observed_immutables_def:
  observed_immutables addr src imms =
    (case ALOOKUP imms addr of
       NONE => FEMPTY
     | SOME mods => get_source_immutables src mods)
End

Theorem stmt_state_rel_immutables_projection:
  !func cenv cx es ss imms.
    observed_immutables cx.txn.target cenv.ce_module imms =
      observed_immutables cx.txn.target cenv.ce_module es.immutables ==>
    (stmt_state_rel func cenv cx (es with immutables := imms) ss <=>
     stmt_state_rel func cenv cx es ss)
Proof
  rpt strip_tac >>
  gvs[observed_immutables_def, stmt_state_rel_def, state_rel_def,
      storage_rel_def, transient_rel_def, immutables_rel_def, logs_rel_def]
QED

Theorem observed_immutables_source_case:
  !addr src imms.
    observed_immutables addr src imms =
      get_source_immutables src
        (case ALOOKUP imms addr of SOME mods => mods | NONE => [])
Proof
  rpt gen_tac >> Cases_on `ALOOKUP imms addr` >>
  simp[observed_immutables_def, get_source_immutables_def]
QED

Theorem env_immutables_consistent_type_support:
  !env cx es imms.
    (!src id tv.
      (?v. FLOOKUP (observed_immutables cx.txn.target src imms) id = SOME (tv,v)) <=>
      (?v. FLOOKUP (observed_immutables cx.txn.target src es.immutables) id = SOME (tv,v))) /\
    env_immutables_consistent env cx es ==>
    env_immutables_consistent env cx (es with immutables := imms)
Proof
  rpt gen_tac >>
  simp[env_immutables_consistent_def, GSYM observed_immutables_source_case,
       optionTheory.IS_SOME_EXISTS, pairTheory.EXISTS_PROD] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem expr_sim_inv_immutables_type_support:
  !cenv cx env es imms.
    (!src id tv.
      (?v. FLOOKUP (observed_immutables cx.txn.target src imms) id = SOME (tv,v)) <=>
      (?v. FLOOKUP (observed_immutables cx.txn.target src es.immutables) id = SOME (tv,v))) /\
    EVERY (\(addr,mods). imms_well_typed mods) imms /\
    expr_sim_inv cenv cx env es ==>
    expr_sim_inv cenv cx env (es with immutables := imms)
Proof
  rpt gen_tac >> strip_tac >>
  `env_immutables_consistent env cx (es with immutables := imms)` by
    (irule env_immutables_consistent_type_support >>
     gvs[expr_sim_inv_def, env_consistent_def]) >>
  gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def,
      state_well_typed_def] >> metis_tac[]
QED

Theorem expr_sim_pre_immutables_type_support:
  !cenv cx env e es imms.
    (!src id tv.
      (?v. FLOOKUP (observed_immutables cx.txn.target src imms) id = SOME (tv,v)) <=>
      (?v. FLOOKUP (observed_immutables cx.txn.target src es.immutables) id = SOME (tv,v))) /\
    EVERY (\(addr,mods). imms_well_typed mods) imms /\
    expr_sim_pre cenv cx env e es ==>
    expr_sim_pre cenv cx env e (es with immutables := imms)
Proof
  simp[expr_sim_pre_def] >> rpt strip_tac >>
  irule expr_sim_inv_immutables_type_support >>
  asm_rewrite_tac[]
QED

Definition overwrite_bool_immutable_def:
  overwrite_bool_immutable id b m =
    if ?old. FLOOKUP m id = SOME (BaseTV BoolT, old) then
      m |+ (id, (BaseTV BoolT, BoolV b))
    else m
End

Theorem overwrite_bool_immutable_lookup:
  !id b m key.
    FLOOKUP (overwrite_bool_immutable id b m) key =
      if key = id /\ (?old. FLOOKUP m id = SOME (BaseTV BoolT, old)) then
        SOME (BaseTV BoolT, BoolV b)
      else FLOOKUP m key
Proof
  rpt gen_tac >> simp[overwrite_bool_immutable_def] >>
  Cases_on `?old. FLOOKUP m id = SOME (BaseTV BoolT,old)` >>
  simp[finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem overwrite_bool_immutable_type_support:
  !id b m key tv.
    (?v. FLOOKUP (overwrite_bool_immutable id b m) key = SOME (tv,v)) <=>
    (?v. FLOOKUP m key = SOME (tv,v))
Proof
  rpt gen_tac >> simp[overwrite_bool_immutable_lookup] >>
  IF_CASES_TAC >> gvs[] >> metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ]
QED

Definition overwrite_module_bool_def:
  overwrite_module_bool src id b mods =
    MAP (\(s,m). (s, if s = src then overwrite_bool_immutable id b m else m)) mods
End

Definition overwrite_state_bool_def:
  overwrite_state_bool src id b imms =
    MAP (\(addr,mods). (addr, overwrite_module_bool src id b mods)) imms
End

Theorem overwrite_module_bool_lookup:
  !mods src id b other.
    ALOOKUP (overwrite_module_bool src id b mods) other =
      OPTION_MAP (\m. if other = src then overwrite_bool_immutable id b m else m)
        (ALOOKUP mods other)
Proof
  Induct >> simp[overwrite_module_bool_def] >>
  rpt gen_tac >> PairCases_on `h` >> gvs[overwrite_module_bool_def,
    overwrite_state_bool_def] >> IF_CASES_TAC >> simp[overwrite_module_bool_def]
QED

Theorem overwrite_state_bool_lookup:
  !imms src id b addr.
    ALOOKUP (overwrite_state_bool src id b imms) addr =
      OPTION_MAP (overwrite_module_bool src id b) (ALOOKUP imms addr)
Proof
  Induct >> simp[overwrite_state_bool_def] >>
  rpt gen_tac >> PairCases_on `h` >> gvs[overwrite_module_bool_def,
    overwrite_state_bool_def] >> IF_CASES_TAC >> simp[overwrite_module_bool_def]
QED

Theorem observed_immutables_overwrite_bool:
  !addr other src id b imms.
    observed_immutables addr other (overwrite_state_bool src id b imms) =
      if other = src then
        overwrite_bool_immutable id b (observed_immutables addr other imms)
      else observed_immutables addr other imms
Proof
  rpt gen_tac >>
  simp[observed_immutables_def, overwrite_state_bool_lookup] >>
  Cases_on `ALOOKUP imms addr` >> simp[overwrite_bool_immutable_def] >>
  simp[get_source_immutables_def, overwrite_module_bool_lookup] >>
  rename1 `ALOOKUP mods other` >> Cases_on `ALOOKUP mods other` >>
  simp[overwrite_bool_immutable_def] >> Cases_on `other = src` >> gvs[]
QED

Theorem observed_immutables_overwrite_bool_type_support:
  !addr other src id b imms key tv.
    (?v. FLOOKUP (observed_immutables addr other
       (overwrite_state_bool src id b imms)) key = SOME (tv,v)) <=>
    (?v. FLOOKUP (observed_immutables addr other imms) key = SOME (tv,v))
Proof
  rpt gen_tac >> simp[observed_immutables_overwrite_bool] >>
  Cases_on `other = src` >> simp[overwrite_bool_immutable_type_support]
QED

Theorem observed_immutables_overwrite_bool_other:
  !addr other src id b imms.
    other <> src ==>
    observed_immutables addr other (overwrite_state_bool src id b imms) =
    observed_immutables addr other imms
Proof
  simp[observed_immutables_overwrite_bool]
QED

Theorem observed_immutables_overwrite_bool_value:
  !addr src id b imms old.
    FLOOKUP (observed_immutables addr src imms) id = SOME (BaseTV BoolT, old) ==>
    FLOOKUP (observed_immutables addr src (overwrite_state_bool src id b imms)) id =
      SOME (BaseTV BoolT, BoolV b)
Proof
  simp[observed_immutables_overwrite_bool, overwrite_bool_immutable_lookup] >>
  metis_tac[]
QED

Theorem overwrite_bool_immutable_typed:
  !id b m.
    (!key tv v. FLOOKUP m key = SOME (tv,v) ==>
      value_has_type tv v /\ well_formed_type_value tv) ==>
    !key tv v. FLOOKUP (overwrite_bool_immutable id b m) key = SOME (tv,v) ==>
      value_has_type tv v /\ well_formed_type_value tv
Proof
  rpt gen_tac >> strip_tac >>
  simp[overwrite_bool_immutable_lookup] >> rpt gen_tac >>
  IF_CASES_TAC >> rpt strip_tac >>
  gvs[value_has_type_def, well_formed_type_value_def] >>
  metis_tac[]
QED

Theorem overwrite_module_bool_typed:
  !src id b mods.
    imms_well_typed mods ==>
    imms_well_typed (overwrite_module_bool src id b mods)
Proof
  rpt gen_tac >> simp[imms_well_typed_def, overwrite_module_bool_lookup] >>
  strip_tac >> rpt gen_tac >>
  namedCases_on `ALOOKUP mods src_id_opt` ["", "entries"] >> simp[] >>
  `!key tv v. FLOOKUP entries key = SOME (tv,v) ==>
     value_has_type tv v /\ well_formed_type_value tv` by metis_tac[] >>
  Cases_on `src_id_opt = src` >> simp[] >>
  metis_tac[overwrite_bool_immutable_typed]
QED

Theorem overwrite_state_bool_typed:
  !imms src id b.
    EVERY (\(addr,mods). imms_well_typed mods) imms ==>
    EVERY (\(addr,mods). imms_well_typed mods) (overwrite_state_bool src id b imms)
Proof
  Induct >> simp[overwrite_state_bool_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  gvs[overwrite_state_bool_def] >>
  metis_tac[overwrite_module_bool_typed]
QED

Theorem expr_sim_pre_overwrite_bool:
  !cenv cx env e es src id b.
    expr_sim_pre cenv cx env e es ==>
    expr_sim_pre cenv cx env e
      (es with immutables := overwrite_state_bool src id b es.immutables)
Proof
  rpt strip_tac >> irule expr_sim_pre_immutables_type_support >>
  simp[observed_immutables_overwrite_bool_type_support] >>
  irule overwrite_state_bool_typed >>
  gvs[expr_sim_pre_def, expr_sim_inv_def, state_well_typed_def]
QED

Theorem stmt_state_rel_overwrite_bool:
  !func cenv cx es ss src id b.
    src <> cenv.ce_module ==>
    (stmt_state_rel func cenv cx
       (es with immutables := overwrite_state_bool src id b es.immutables) ss <=>
     stmt_state_rel func cenv cx es ss)
Proof
  rpt strip_tac >> irule stmt_state_rel_immutables_projection >>
  simp[observed_immutables_overwrite_bool_other]
QED

Theorem module_var_key_name_injective:
  !src x y. module_var_key (src,x) = module_var_key (src,y) <=> x = y
Proof
  Cases >> simp[module_var_key_def, nsid_to_string_def]
QED

Theorem module_var_names_finite:
  !src m. FINITE {name | module_var_key (src,name) IN FDOM m}
Proof
  rpt gen_tac >>
  irule (pred_setTheory.FINITE_INJ |> INST_TYPE [beta |-> ``:string``]) >>
  qexistsl_tac [`\name. module_var_key (src,name)`, `FDOM m`] >>
  simp[pred_setTheory.INJ_DEF, module_var_key_name_injective]
QED

Definition compiler_slot_layout_def:
  compiler_slot_layout src m transient =
    MAP (\key. (key, case FLOOKUP m (module_var_key key) of
                      SOME (StorageLoc w) => if transient then 0 else w2n w
                    | SOME (TransientLoc w) => if transient then w2n w else 0
                    | _ => 0))
      (MAP (\name. (src,name))
        (SET_TO_LIST {name | module_var_key (src,name) IN FDOM m}))
End

Theorem compiler_slot_layout_lookup:
  !src m name w transient.
    FLOOKUP m (module_var_key (src,name)) =
      SOME (if transient then TransientLoc w else StorageLoc w) ==>
    ALOOKUP (compiler_slot_layout src m transient) (src,name) = SOME (w2n w)
Proof
  rpt gen_tac >> strip_tac >>
  `MEM (src,name) (MAP (\n. (src,n))
      (SET_TO_LIST {n | module_var_key (src,n) IN FDOM m}))` by
    (simp[MEM_MAP, module_var_names_finite] >>
     gvs[finite_mapTheory.FLOOKUP_DEF, AllCaseEqs()]) >>
  Cases_on `transient` >>
  simp[compiler_slot_layout_def, alistTheory.ALOOKUP_TABULATE]
QED

Theorem compile_env_layouts_exist:
  !cenv cx. ?lays.
    storage_vars_rel cenv (cx with layouts := lays) /\
    transient_vars_rel cenv (cx with layouts := lays)
Proof
  rpt gen_tac >>
  qexists_tac `[(cx.txn.target,
    (compiler_slot_layout cenv.ce_module cenv.ce_vars F,
     compiler_slot_layout cenv.ce_module cenv.ce_vars T))]` >>
  simp[storage_vars_rel_def, transient_vars_rel_def,
       lookup_var_slot_from_layout_def] >>
  conj_tac >> rpt strip_tac >> qexists_tac `w2n slot` >>
  simp[compiler_slot_layout_lookup]
QED

Definition hash_bool_context_def:
  hash_bool_context other lays = empty_evaluation_context with
    <| stk := [(NONE,"")]; sources := [(empty_call_txn.target,
         [(other,[VariableDecl Private Immutable "" (BaseT BoolT) NONE])])];
       layouts := lays |>
End

Definition hash_bool_env_def:
  hash_bool_env other =
    <| current_src := NONE; var_types := FEMPTY; var_assignable := FEMPTY;
       bare_globals := FEMPTY |+ ((other,""),BaseT BoolT);
       bare_global_assignable := FEMPTY |+ ((other,""),BaseT BoolT);
       toplevel_vtypes := FEMPTY |+ ((other,""),Type (BaseT BoolT));
       type_defs := FEMPTY; fn_sigs := FEMPTY; flag_members := FEMPTY |>
End

Definition hash_bool_state_def:
  hash_bool_state other b = empty_state with
    <| scopes := [FEMPTY];
       immutables := [(empty_call_txn.target,
         [(other,FEMPTY |+ ("",(BaseTV BoolT,BoolV b)))])] |>
End

Theorem hash_bool_module_code:
  !other lays src.
    get_module_code (hash_bool_context other lays) src =
      if src = other then SOME [VariableDecl Private Immutable "" (BaseT BoolT) NONE]
      else NONE
Proof
  simp[hash_bool_context_def, empty_evaluation_context_def, get_module_code_def,
       EQ_SYM_EQ]
QED

Theorem hash_bool_expr_typed:
  !other. well_typed_expr (hash_bool_env other)
    (TopLevelName (BaseT BoolT) (other,""))
Proof
  simp[hash_bool_env_def, well_typed_expr_def, well_formed_type_def,
       finite_mapTheory.FLOOKUP_UPDATE, evaluate_type_def]
QED

Theorem hash_bool_tenv:
  !other lays. get_tenv (hash_bool_context other lays) = FEMPTY
Proof
  rpt gen_tac >> EVAL_TAC >> simp[]
QED

Theorem hash_bool_env_context:
  !other lays.
    env_context_consistent (hash_bool_env other) (hash_bool_context other lays)
Proof
  rpt gen_tac >>
  simp[env_context_consistent_def, hash_bool_env_def, hash_bool_tenv,
       hash_bool_context_def, empty_evaluation_context_def, current_module_def,
       fn_sigs_consistent_def, fn_sigs_declared_complete_def,
       toplevel_vtypes_complete_def, bare_globals_complete_def,
       bare_global_assignable_complete_def, flag_members_complete_def,
       get_module_code_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[lookup_flag_def, is_bare_global_decl_def, find_var_decl_by_name_def,
       is_immutable_decl_def, well_formed_vtype_def, well_formed_type_def,
       evaluate_type_def]
QED

Theorem hash_bool_env_scopes:
  !other lays b.
    env_scopes_consistent (hash_bool_env other) (hash_bool_context other lays)
      (hash_bool_state other b)
Proof
  simp[env_scopes_consistent_def, hash_bool_env_def, hash_bool_state_def,
       lookup_scopes_def]
QED

Theorem hash_bool_env_immutables:
  !other lays b.
    env_immutables_consistent (hash_bool_env other) (hash_bool_context other lays)
      (hash_bool_state other b)
Proof
  simp[env_immutables_consistent_def, hash_bool_env_def, hash_bool_state_def,
       hash_bool_context_def, empty_evaluation_context_def, hash_bool_tenv,
       get_source_immutables_def, get_module_code_def,
       finite_mapTheory.FLOOKUP_UPDATE, find_var_decl_by_name_def,
       evaluate_type_def]
QED

Theorem hash_bool_state_typed:
  !other b. state_well_typed (hash_bool_state other b)
Proof
  simp[state_well_typed_def, hash_bool_state_def, scope_well_typed_def,
       imms_well_typed_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[value_has_type_def, well_formed_type_value_def]
QED

Theorem hash_bool_context_typed:
  !other lays. context_well_typed (hash_bool_context other lays)
Proof
  rpt gen_tac >> EVAL_TAC
QED

Theorem hash_bool_no_callable:
  !other lays src ts fn.
    get_module_code (hash_bool_context other lays) src = SOME ts ==>
    lookup_callable_function (hash_bool_context other lays).in_deploy fn ts = NONE
Proof
  simp[hash_bool_module_code] >> rpt strip_tac >>
  gvs[AllCaseEqs(), hash_bool_context_def, empty_evaluation_context_def,
      lookup_callable_function_def, lookup_function_def] >> EVAL_TAC
QED

Theorem hash_bool_functions_typed:
  !other lays. functions_well_typed (hash_bool_context other lays)
Proof
  rpt gen_tac >> simp[functions_well_typed_def] >>
  rpt gen_tac >> disch_tac >> rpt gen_tac >> strip_tac >>
  drule hash_bool_no_callable >> disch_then (qspec_then `fn` mp_tac) >> simp[]
QED

Theorem hash_bool_call_safe:
  !other lays. call_evaluation_safe (hash_bool_context other lays) []
Proof
  rpt gen_tac >>
  simp[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_def] >>
  qexists_tac `[]` >>
  `functions_follow_call_graph [] (hash_bool_context other lays)` suffices_by
    (simp[vyperTypeCallStackSoundnessTheory.call_stack_follows_def,
          vyperTypeCallGraphSoundnessTheory.call_edge_rel_def,
          hash_bool_context_def, empty_evaluation_context_def,
          relationTheory.TC_DEF, relationTheory.irreflexive_def] >>
     strip_tac >> gen_tac >> qexists_tac `\x y. F` >> simp[]) >>
  simp[vyperTypeCallStackSoundnessTheory.functions_follow_call_graph_def] >>
  rpt strip_tac >> drule hash_bool_no_callable >>
  disch_then (qspec_then `fn` mp_tac) >> simp[]
QED

Theorem hash_bool_source_pre:
  !cenv other lays b.
    expr_sim_pre cenv (hash_bool_context other lays) (hash_bool_env other)
      (TopLevelName (BaseT BoolT) (other,"")) (hash_bool_state other b)
Proof
  rpt gen_tac >>
  simp[expr_sim_pre_def, expr_sim_inv_def, hash_bool_expr_typed,
       hash_bool_state_typed, hash_bool_context_typed, hash_bool_functions_typed,
       hash_bool_call_safe, vyperTypeCallGraphTheory.int_calls_expr_def] >>
  simp[env_consistent_def, hash_bool_env_context, hash_bool_env_scopes,
       hash_bool_env_immutables, hash_bool_env_def, hash_bool_state_def,
       empty_state_def, accounts_well_typed_def] >>
  conj_tac >- (gen_tac >> EVAL_TAC) >>
  simp[hash_bool_module_code] >> rpt strip_tac >>
  gvs[AllCaseEqs(), lookup_flag_def]
QED

Theorem expr_sim_pre_outcomes:
  !cenv cx env e es outs.
    expr_sim_pre cenv cx env e (es with outcomes := outs) <=>
    expr_sim_pre cenv cx env e es
Proof
  simp[expr_sim_pre_def, expr_sim_inv_def, env_consistent_def,
       env_scopes_consistent_def, env_immutables_consistent_def,
       state_well_typed_def]
QED

Theorem hash_bool_target_model:
  !cenv other func lbl lays.
    other <> cenv.ce_module /\
    storage_vars_rel cenv (hash_bool_context other lays) /\
    transient_vars_rel cenv (hash_bool_context other lays) ==>
    !b. stmt_state_rel func cenv (hash_bool_context other lays)
      ((hash_bool_state other b) with outcomes := SOME []) (init_venom_state lbl)
Proof
  rpt strip_tac >>
  simp[stmt_state_rel_def, state_rel_def] >>
  simp[local_ptrs_rel_def, local_region_def, hash_bool_state_def,
       lookup_scopes_def, storage_rel_def, transient_rel_def,
       immutables_rel_def, hash_bool_context_def, empty_evaluation_context_def,
       get_source_immutables_def, logs_rel_def, call_ctx_rel_def,
       init_venom_state_def, empty_state_def] >>
  simp[contract_storage_def, contract_transient_def, venomMemDefsTheory.alloca_inv_def,
       empty_call_context_def, empty_tx_context_def, empty_block_context_def,
       empty_call_txn_def, venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def]
QED

Theorem hash_bool_shared_model:
  !cenv other. other <> cenv.ce_module ==>
    ?lays. !b func lbl.
      expr_sim_pre cenv (hash_bool_context other lays) (hash_bool_env other)
        (TopLevelName (BaseT BoolT) (other,""))
        ((hash_bool_state other b) with outcomes := SOME []) /\
      stmt_state_rel func cenv (hash_bool_context other lays)
        ((hash_bool_state other b) with outcomes := SOME []) (init_venom_state lbl)
Proof
  rpt strip_tac >>
  qspecl_then [`cenv`, `hash_bool_context other []`] strip_assume_tac
    compile_env_layouts_exist >>
  `storage_vars_rel cenv (hash_bool_context other lays) /\
   transient_vars_rel cenv (hash_bool_context other lays)` by
    gvs[hash_bool_context_def] >>
  qexists_tac `lays` >> rpt gen_tac >> conj_tac
  >- simp[expr_sim_pre_outcomes, hash_bool_source_pre] >>
  irule hash_bool_target_model >> simp[]
QED
