(*
 * self.x = e for a storage or transient variable x of a non-word type.
 *
 * The lowering evaluates e into a memory buffer and copies the buffer's
 * words over x's whole storage region (compile_assign_value's bulk branch:
 * compile_memory_to_storage, or one MLOAD and SSTORE for a one-word value);
 * an empty bytestring value is stored as a zero length word.  The source
 * writes x's encoding (encode_value).  The storages agree afterwards up to
 * the bytes the new value leaves dead (storageCopyLive).
 *
 * Main theorem:
 *   compile_assign_storage_copy_stmt_frag — self.x = e for a storage or
 *     transient x of a non-word, non-DynArray type and e of that type,
 *     every outcome
 *)

Theory stmtSimAssignStorageCopy
Ancestors
  list rich_list finite_map pred_set
  fragExec exprSim exprSimLeaves exprSimOps stmtSim stmtSimAssign stmtSimAssignMem
  stmtSimAssignStorage exprSimHash exprOperandVar stmtSimDecl vyperExprNoControl
  stmtSimStoreCopy storageCopyLive accountsRelProps
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  context compileEnv valueEncoding stmtLoweringMono
  vyperContext vyperAST vyperInterpreter vyperState vyperStorage vyperStorageBackend vyperValue
  vyperTyping vyperStorageLayoutSafety vyperStorageFrame
  venomExecSemantics venomInst venomState
Libs
  monadsyntax

(* A typed source value always has a successful storage write. *)
Theorem typed_storage_copy_write[local]:
  !cx tr slot tvt v es.
    value_has_type tvt v ==>
    ?writes.
      encode_value tvt v = SOME writes /\
      write_storage_slot cx tr slot tvt v es =
        (INL (), set_storage cx es tr
          (apply_writes slot writes (get_storage cx es tr)))
Proof
  rpt gen_tac >> strip_tac >>
  `IS_SOME (encode_value tvt v)` by
    metis_tac[value_has_type_equiv] >>
  Cases_on `encode_value tvt v` >> gvs[write_storage_slot_eq]
QED

(* The empty shortcut does not evaluate the RHS in generated code. *)
Theorem assign_storage_empty_code[local]:
  !cenv lctx ty nsid e sa sf c tr slot.
    stmt_env cenv lctx ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e)
      sa = (c, sf) /\
    FLOOKUP cenv.ce_module_vars nsid =
      SOME (if tr then TransientLoc slot else StorageLoc slot) /\
    cenv.ce_hashmap_info nsid = NONE /\
    has_length_word (expr_type e) /\ is_empty_value_expr e ==>
    c = cenv /\
    emit_void (if tr then TSTORE else SSTORE) [Lit slot; Lit 0w] sa =
      ((), sf)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_get_target_ptr_toplevel >> strip_tac >>
  drule stmt_env_assign >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  Cases_on `tr` >>
  simp[compile_stmt_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, compile_store_at_loc_def]
QED

Theorem storage_copy_no_dyn_info[local]:
  (!elem n. typ <> ArrayT elem (Dynamic n)) ==>
  (case typ of ArrayT elem (Dynamic n) => SOME (f elem) | _ => NONE) = NONE
Proof
  strip_tac >> Cases_on `typ` >> simp[] >>
  rename1 `ArrayT elem bound` >> Cases_on `bound` >> simp[] >> metis_tac[]
QED

(* Expose the RHS prefix independently of the later assignment dispatch.
   In particular this interface remains valid when RHS evaluation fails. *)
Theorem assign_storage_copy_code_parts[local]:
  !cenv lctx ty nsid e sa sf c tr slot vtyp.
    stmt_env cenv lctx ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e)
      sa = (c, sf) /\
    FLOOKUP cenv.ce_module_vars nsid =
      SOME (if tr then TransientLoc slot else StorageLoc slot) /\
    cenv.ce_hashmap_info nsid = NONE /\
    cenv.ce_module_var_type nsid = SOME vtyp /\
    ~(has_length_word (expr_type e) /\ is_empty_value_expr e) ==>
    c = cenv /\
    ?vv sV sB op.
      compile_expr cenv (expr_type e) e sa = (vv, sV) /\
      unwrap_value cenv vv sV = (op, sB) /\
      lower_value compile_expr cenv (expr_type e) e sa = (op, sB) /\
      compile_assign_value cenv (Lit slot)
        (if tr then LocTransient else LocStorage) op (is_word_type vtyp)
        (vv_location vv) vtyp (lowered_value_type cenv e)
        (case vtyp of ArrayT elem_ty (Dynamic _) =>
           SOME ((type_memory_bytes cenv elem_ty + 31) DIV 32,
                 type_memory_bytes cenv elem_ty) | _ => NONE)
        (type_memory_bytes cenv vtyp) sB = ((), sf)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_get_target_ptr_toplevel >> strip_tac >>
  drule stmt_env_assign >> strip_tac >>
  qpat_x_assum `c = cenv` SUBST_ALL_TAC >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss())
    [Once compile_stmt_def, comp_bind_def, comp_ignore_bind_def,
     comp_return_def, LET_THM] >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `compile_expr _ _ _ _ = (vv, sV)` >>
  Cases_on `unwrap_value cenv vv sV` >>
  rename1 `unwrap_value _ _ _ = (op, sB)` >>
  simp[] >> strip_tac >>
  simp[lower_value_def, comp_bind_def]
QED

(* Literal bounds can differ, but only within the bytestring family.
   ABI encoding is the sole remaining exceptional expression constructor. *)
Theorem storage_copy_lowered_type[local]:
  !cenv e.
    (!ann ensure mid t args.
      e <> TypeBuiltin ann (AbiEncode ensure mid) t args) ==>
    lowered_value_type cenv e = expr_type e \/
    (is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e))
Proof
  rpt gen_tac >> strip_tac >> Cases_on `e` >>
  simp[lowered_value_type_def]
  >- (rename1 `Literal t lit` >>
      Cases_on `t` >> simp[lowered_value_type_def] >>
      rename1 `BaseT bt` >> Cases_on `bt` >>
      simp[lowered_value_type_def] >>
      Cases_on `lit` >> simp[lowered_value_type_def, expr_type_def, is_bytestring_type_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      simp[lowered_value_type_def, expr_type_def, is_bytestring_type_def]) >>
  rename1 `TypeBuiltin ann tb t args` >> Cases_on `tb` >>
  gvs[lowered_value_type_def]
QED

(* Fixed bytes are word types whenever their type evaluates. *)
Theorem storage_copy_bytes_type[local]:
  !tenv typ tvt bs.
    evaluate_type tenv typ = SOME tvt /\ ~is_word_type typ /\
    value_has_type tvt (BytesV bs) ==>
    is_bytestring_type typ
Proof
  rpt gen_tac >> strip_tac >> Cases_on `typ` >>
  gvs[evaluate_type_def, value_has_type_def, is_bytestring_type_def,
      is_word_type_def, AllCaseEqs()] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[evaluate_type_def, value_has_type_def, is_bytestring_type_def,
      is_word_type_def, AllCaseEqs()] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[evaluate_type_def, value_has_type_def, is_bytestring_type_def,
      is_word_type_def, AllCaseEqs()]
QED

Theorem storage_copy_abi_value[local]:
  !cx ensure mid t tys vs v.
    evaluate_type_builtin cx (AbiEncode ensure mid) t tys vs = INL v ==>
    ?bs. v = BytesV bs
Proof
  rpt gen_tac >>
  simp[Once evaluate_type_builtin_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac
    `(case encoded of INL bs => INL (BytesV (pre ++ bs))
      | INR str => INR (RuntimeError str))` >>
  Cases_on `encoded` >> simp[] >> metis_tac[]
QED

Theorem storage_copy_abi_eval[local]:
  !cx ann ensure mid t args es v es1.
    (do result <- eval_expr cx (TypeBuiltin ann (AbiEncode ensure mid) t args);
        read_result cx result od) es = (INL v, es1) ==>
    ?bs. v = BytesV bs
Proof
  rpt gen_tac >>
  simp[Once evaluate_def, bind_def, type_check_def, assert_def,
       return_def, raise_def] >>
  simp[bind_def, ignore_bind_def, assert_def, return_def, raise_def] >>
  Cases_on `type_builtin_args_length_ok (AbiEncode ensure mid) (LENGTH args)` >>
  simp[] >>
  Cases_on `eval_exprs cx args es` >> rename1 `eval_exprs _ _ _ = (rs, st)` >>
  Cases_on `rs` >> simp[] >>
  simp[lift_sum_def, bind_def, return_def, raise_def] >>
  qmatch_goalsub_rename_tac `evaluate_type_builtin _ _ _ _ vs` >>
  Cases_on `evaluate_type_builtin cx (AbiEncode ensure mid) t (MAP expr_type args) vs` >>
  simp[read_result_def, return_def, raise_def] >> strip_tac >> gvs[] >>
  drule storage_copy_abi_value >> simp[]
QED

(* Typed successful evaluation excludes the only non-bytestring
   annotation mismatch introduced by lowered_value_type. *)
Theorem storage_copy_success_compatible[local]:
  !cx cenv e es v es1 tvt.
    (do result <- eval_expr cx e; read_result cx result od) es =
      (INL v, es1) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    ~is_word_type (expr_type e) /\ value_has_type tvt v ==>
    lowered_value_type cenv e = expr_type e \/
    (is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `?ann ensure mid t args.
    e = TypeBuiltin ann (AbiEncode ensure mid) t args`
  >- (gvs[] >> drule storage_copy_abi_eval >> strip_tac >> gvs[] >>
      drule_all storage_copy_bytes_type >> strip_tac >>
      simp[lowered_value_type_def, is_bytestring_type_def, LET_THM]) >>
  irule storage_copy_lowered_type >> metis_tac[]
QED

(* Once source layout compatibility is known, only the size dispatch
   remains. No dynamic-array path or normalization can be selected. *)
Theorem assign_storage_copy_suffix[local]:
  !cenv dst src tr loc typ src_ty mem_size.
    ~is_word_type typ /\
    (typ = src_ty \/
     (is_bytestring_type typ /\ is_bytestring_type src_ty)) ==>
    compile_assign_value cenv dst
      (if tr then LocTransient else LocStorage) src F loc
      typ src_ty NONE mem_size =
    (if mem_size <= 32 then
       do loaded <- emit_op MLOAD [src];
          emit_void (if tr then TSTORE else SSTORE) [dst; loaded]
       od
     else
       do (if tr then compile_memory_to_transient src dst (mem_size DIV 32)
           else compile_memory_to_storage src dst (mem_size DIV 32));
          return ()
       od)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `tr` >>
  simp[FUN_EQ_THM, compile_assign_value_def, comp_bind_def, comp_return_def]
QED

Theorem storage_copy_loop_open[local]:
  !src dst n loc ctor sa u sb.
    compile_word_copy_loop src dst n LocMemory loc ctor sa = (u,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_word_copy_loop_def, comp_ignore_bind_def, comp_bind_def] >>
  ntac 4 (pairarg_tac >> simp[]) >>
  ntac 4 (pairarg_tac >> simp[]) >>
  ntac 4 (pairarg_tac >> simp[]) >>
  ntac 4 (pairarg_tac >> simp[]) >>
  pairarg_tac >> simp[] >>
  strip_tac >> pop_assum mp_tac >>
  simp[new_block_def, block_is_terminated_def] >> strip_tac >> gvs[]
QED

Theorem assign_storage_copy_suffix_open[local]:
  !cenv dst src tr loc typ src_ty mem_size sa sb.
    compile_assign_value cenv dst (if tr then LocTransient else LocStorage)
      src F loc typ src_ty NONE mem_size sa = ((),sb) /\
    ~is_word_type typ /\
    (typ = src_ty \/ (is_bytestring_type typ /\ is_bytestring_type src_ty)) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  dep_rewrite.DEP_REWRITE_TAC[assign_storage_copy_suffix] >> simp[] >>
  Cases_on `mem_size <= 32`
  >- (simp[comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
      drule stmtSimDeclMemTheory.emit_void_nonterminator_open >>
      Cases_on `tr` >> simp[is_terminator_def]) >>
  simp[compile_memory_to_storage_def, compile_memory_to_transient_def,
       comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  irule storage_copy_loop_open >> Cases_on `tr` >> metis_tac[]
QED

Theorem storage_copy_dyn_live_word[local]:
  !st base cap len i b.
    w2n (lookup_storage (n2w base) st) = len /\
    i < 1 + word_size cap /\ b < 32 /\
    ~dyn_bytes_dead st base cap (base + i) b ==>
    32 * i < 32 + 32 * word_size len
Proof
  rpt gen_tac >> strip_tac >>
  `len <= 32 * word_size len` by simp[le_word_size_mul] >>
  fs[dyn_bytes_dead_def] >> decide_tac
QED

Theorem storage_copy_word_address[local]:
  !w:bytes32 i len.
    w2n w + len < dimword (:256) /\ 32 * i < len ==>
    w2n (w + n2w i * 32w) = w2n w + 32 * i
Proof
  Cases >> rpt gen_tac >> strip_tac >>
  gvs[wordsTheory.word_add_n2w, wordsTheory.word_mul_n2w,
      wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  `n + i * 32 < dimword (:256)` by decide_tac >>
  simp[arithmeticTheory.LESS_MOD]
QED

Theorem storage_copy_length_type[local]:
  !typ.
    has_length_word typ /\ (!elem n. typ <> ArrayT elem (Dynamic n)) ==>
    (?n. typ = BaseT (BytesT (Dynamic n))) \/
    (?n. typ = BaseT (StringT n))
Proof
  gen_tac >> strip_tac >> Cases_on `typ` >>
  gvs[has_length_word_def, is_bytestring_type_def]
  >- (rename1 `is_bytestring_type (BaseT bt)` >>
      Cases_on `bt` >> gvs[is_bytestring_type_def] >>
      rename1 `is_bytestring_type (BaseT (BytesT bd))` >>
      Cases_on `bd` >> gvs[is_bytestring_type_def]) >>
  rename1 `has_length_word (ArrayT elem bd)` >>
  Cases_on `bd` >> gvs[has_length_word_def, is_bytestring_type_def]
QED

(* The repaired Empty branch evaluates only its type, not any operands. *)
Theorem storage_copy_empty_eval[local]:
  !cx ann typ args tvt es.
    evaluate_type (get_tenv cx) typ = SOME tvt ==>
    (do result <- eval_expr cx (TypeBuiltin ann Empty typ args);
        read_result cx result od) es =
    (if args = [] then (INL (default_value tvt), es)
     else (INR (Error (TypeError "TypeBuiltin args")), es))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `args` >>
  simp[Once evaluate_def, type_builtin_args_length_ok_def, type_check_def,
       assert_def, bind_def, ignore_bind_def, return_def, raise_def,
       lift_sum_def, evaluate_type_builtin_def, read_result_def] >>
  simp[evaluate_def, bind_def, return_def, read_result_def]
QED

Theorem storage_copy_empty_rhs[local]:
  !cx e typ tvt es r es1.
    has_length_word (expr_type e) /\ is_empty_value_expr e /\
    expr_type e = typ /\ (!elem n. typ <> ArrayT elem (Dynamic n)) /\
    (!ann t args. e = TypeBuiltin ann Empty t args ==> t = typ) /\
    evaluate_type (get_tenv cx) typ = SOME tvt /\
    (!v st. (do result <- eval_expr cx e; read_result cx result od) es =
       (INL v,st) ==> value_has_type tvt v) /\
    (do result <- eval_expr cx e; read_result cx result od) es = (r,es1) ==>
    es1 = es /\
    ((?v. r = INL v /\ encode_value tvt v = SOME [(0,0w)]) \/
     (?msg. r = INR (Error (TypeError msg))))
Proof
  rpt gen_tac >> strip_tac >>
  `(?n. typ = BaseT (BytesT (Dynamic n))) \/
   (?n. typ = BaseT (StringT n))` by
    (irule storage_copy_length_type >> metis_tac[]) >>
  Cases_on `e` >>
  qpat_x_assum `is_empty_value_expr _` mp_tac >>
  simp[is_empty_value_expr_def] >> strip_tac
  >>~- ([`Literal t lit`],
      Cases_on `lit` >> gvs[is_empty_value_expr_def] >>
      rename1 `BytesL bs` >> Cases_on `bs` >>
      gvs[is_empty_value_expr_def, expr_type_def, evaluate_type_def, AllCaseEqs(),
          evaluate_def, bind_def, return_def, read_result_def,
          vyperValueOperationTheory.evaluate_literal_def, encode_value_def, encode_dyn_bytes_slots_def,
          value_has_type_def, bytes_to_slots_def, bytes_to_slots_aux_def])
  >>~- ([`TypeBuiltin ann tb t args`],
      Cases_on `tb` >>
      qpat_x_assum `is_empty_value_expr _` mp_tac >>
      simp[is_empty_value_expr_def] >>
      qpat_x_assum `typ = _` SUBST_ALL_TAC >>
      qpat_x_assum `!ann' t' args'. _` mp_tac >>
      simp[] >> strip_tac >> gvs[expr_type_def] >>
      qmatch_asmsub_abbrev_tac `TypeBuiltin at Empty tt args` >>
      drule storage_copy_empty_eval >>
      disch_then (qspecl_then [`at`, `args`, `es`] assume_tac) >>
      Cases_on `args` >> unabbrev_all_tac >>
      gvs[evaluate_type_def, AllCaseEqs(), default_value_def,
          encode_value_def, encode_dyn_bytes_slots_def, bytes_to_slots_def,
          bytes_to_slots_aux_def]) >>
  rename1 `Builtin t b args` >> Cases_on `b` >>
  fs[is_empty_value_expr_def] >>
  rename1 `MakeArray ot bd` >> Cases_on `ot` >>
  fs[is_empty_value_expr_def] >>
  rename1 `MakeArray (SOME elem_ty) bd` >> Cases_on `args` >>
  gvs[is_empty_value_expr_def, expr_type_def] >>
  gvs[Once evaluate_def, builtin_args_length_ok_def, type_check_def,
      assert_def, bind_def, ignore_bind_def, return_def, raise_def] >>
  gvs[evaluate_def, bind_def, return_def, get_accounts_def,
      lift_sum_def, evaluate_builtin_def, read_result_def,
      evaluate_type_def, AllCaseEqs(), value_has_type_def] >>
  Cases_on `evaluate_type (get_tenv cx) elem_ty` >>
  gvs[return_def, raise_def, value_has_type_def]
QED

Theorem storage_copy_length_head[local]:
  !base tv v len tail st.
    encode_value tv v = SOME ((0,n2w len)::tail) /\
    value_has_type tv v /\
    (!off w. MEM (off,w) tail ==> 0 < off) /\
    base + type_slot_size tv <= dimword (:256) /\
    len < dimword (:256) /\ base < dimword (:256) ==>
    w2n (lookup_storage (n2w base)
      (apply_writes (n2w base) ((0,n2w len)::tail) st)) = len
Proof
  rpt gen_tac >> strip_tac >> rename1 `kk + type_slot_size tv <= _` >>
  `!off. MEM off (MAP FST tail) ==> off < type_slot_size tv` by
    (drule (cj 1 vyperEncodeDecodeTheory.encode_writes_bounded) >>
     simp[] >> metis_tac[]) >>
  simp[Once apply_writes_def, wordsTheory.w2n_n2w,
       arithmeticTheory.LESS_MOD] >>
  `lookup_storage (n2w kk)
      (apply_writes (n2w kk) tail
        (update_storage (n2w kk) (n2w len) st)) =
   lookup_storage (n2w kk) (update_storage (n2w kk) (n2w len) st)` by
    (mp_tac (Q.SPECL [`tail`, `kk`,
       `update_storage (n2w kk) (n2w len) st`, `0`]
       vyperEncodeDecodeTheory.apply_writes_lookup_miss_num) >>
     simp[] >> disch_then irule >> rpt strip_tac >>
     `0 < off` by (fs[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
     `kk + off < dimword (:256)` by (res_tac >> decide_tac) >>
     gvs[wordsTheory.n2w_11, arithmeticTheory.LESS_MOD]) >>
  simp[vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
       combinTheory.APPLY_UPDATE_THM, wordsTheory.w2n_n2w,
       arithmeticTheory.LESS_MOD]
QED

Theorem storage_copy_dyn_head[local]:
  !tv v cap bs writes k st.
    encode_value tv v = encode_dyn_bytes_slots cap bs /\
    encode_value tv v = SOME writes /\ value_has_type tv v /\
    k + type_slot_size tv <= dimword (:256) /\
    k < dimword (:256) /\ LENGTH bs < dimword (:256) ==>
    w2n (lookup_storage (n2w k) (apply_writes (n2w k) writes st)) = LENGTH bs
Proof
  rpt gen_tac >> strip_tac >>
  gvs[encode_dyn_bytes_slots_def, AllCaseEqs()] >>
  irule storage_copy_length_head >>
  conj_tac
  >- (simp[indexedListsTheory.MEM_MAPi] >> rpt strip_tac >> gvs[]) >>
  simp[] >> qexistsl_tac [`tv`, `v`] >> simp[]
QED

Theorem storage_copy_dyn_footprint[local]:
  !tv v cap bs writes k st i b.
    encode_value tv v = encode_dyn_bytes_slots cap bs /\
    value_has_type tv v /\ encode_value tv v = SOME writes /\
    k + type_slot_size tv <= dimword (:256) /\
    k < dimword (:256) /\ LENGTH bs < dimword (:256) /\
    i < 1 + word_size cap /\ b < 32 /\
    ~dyn_bytes_dead (apply_writes (n2w k) writes st) k cap (k+i) b ==>
    32*i < 32 + 32 * word_size (LENGTH bs)
Proof
  rpt gen_tac >> strip_tac >>
  `w2n (lookup_storage (n2w k) (apply_writes (n2w k) writes st)) = LENGTH bs` by
    (irule storage_copy_dyn_head >> simp[] >>
     qexistsl_tac [`cap`, `tv`, `v`] >> gvs[]) >>
  irule storage_copy_dyn_live_word >> metis_tac[]
QED

Theorem storage_copy_live_footprint[local]:
  !tv v writes k st i b.
    well_formed_type_value tv /\ value_has_type tv v /\
    encode_value tv v = SOME writes /\
    k + type_slot_size tv <= dimword (:256) /\ k < dimword (:256) /\
    i < type_slot_size tv /\ b < 32 /\
    ~dead_bytes (apply_writes (n2w k) writes st) k tv (k+i) b ==>
    32*i < val_footprint tv v
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `val_footprint tv v = type_memory_size tv`
  >- (gvs[exprSimAttributeFieldsTheory.type_memory_size_slots] >> decide_tac) >>
  Cases_on `v` >> fs[val_footprint_def] >>
  Cases_on `tv` >> fs[] >>
  rename1 `BaseTV bt` >> Cases_on `bt` >> fs[]
  >- (`encode_value (BaseTV (StringT n)) (StringV s) =
         encode_dyn_bytes_slots n (MAP (n2w o ORD) s)` by simp[NoAsms, encode_value_def] >>
      `LENGTH (MAP (n2w o ORD) s : word8 list) < dimword (:256)` by
        (gvs[value_has_type_def, well_formed_type_value_def] >> decide_tac) >>
      drule storage_copy_dyn_footprint >>
      simp[dead_bytes_def, type_slot_size_def] >> disch_then irule >>
      gvs[encode_value_def, type_slot_size_def, dead_bytes_def] >>
      qexistsl_tac [`b`, `k`, `st`] >> simp[] >> decide_tac) >>
  rename1 `BytesT bd` >> Cases_on `bd` >> fs[] >>
  rename1 `BytesV bs` >>
  `encode_value (BaseTV (BytesT (Dynamic n))) (BytesV bs) =
     encode_dyn_bytes_slots n bs` by simp[NoAsms, encode_value_def] >>
  `LENGTH bs < dimword (:256)` by
    (gvs[value_has_type_def, well_formed_type_value_def] >> decide_tac) >>
  drule storage_copy_dyn_footprint >>
  simp[dead_bytes_def, type_slot_size_def] >> disch_then irule >>
  gvs[encode_value_def, type_slot_size_def, dead_bytes_def] >>
  qexistsl_tac [`b`, `k`, `st`] >> simp[] >> decide_tac
QED

Theorem storage_copy_live_memory_word[local]:
  !tv v writes k st i b (w:bytes32) s.
    well_formed_type_value tv /\ value_has_type tv v /\
    encode_value tv v = SOME writes /\
    k + type_slot_size tv <= dimword (:256) /\ k < dimword (:256) /\
    i < type_slot_size tv /\ b < 32 /\
    ~dead_bytes (apply_writes (n2w k) writes st) k tv (k+i) b /\
    w2n w + val_footprint tv v < dimword (:256) ==>
    mload (w2n (w + n2w i * 32w)) s =
      mem_word_at (w2n w + 32*i) s.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  `32*i < val_footprint tv v` by (drule_all storage_copy_live_footprint >> simp[]) >>
  drule_all storage_copy_word_address >>
  simp[valueEncodingPropsTheory.mem_word_at_eq_mload]
QED

Theorem storage_copy_capacity_bound[local]:
  !n. n < dimword (:256) ==> 1 + word_size n < dimword (:256)
Proof
  rpt strip_tac >> Cases_on `n < 2`
  >- (`n = 0 \/ n = 1` by decide_tac >>
      gvs[vfmConstantsTheory.word_size_def, wordsTheory.dimword_def] >> EVAL_TAC) >>
  `0 < n` by decide_tac >>
  drule vyperArithTheory.word_size_le >> strip_tac >>
  `word_size n < n` by
    (spose_not_then assume_tac >>
     drule_all vyperArithTheory.word_size_not_lt_self >> decide_tac) >>
  decide_tac
QED

Theorem storage_copy_count_bound[local]:
  !tv v.
    well_formed_type_value tv /\ val_footprint tv v < dimword (:256) ==>
    type_slot_size tv < dimword (:256)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `val_footprint tv v = type_memory_size tv`
  >- (gvs[exprSimAttributeFieldsTheory.type_memory_size_slots] >> decide_tac) >>
  Cases_on `v` >> fs[val_footprint_def] >>
  Cases_on `tv` >> fs[] >>
  rename1 `BaseTV bt` >> Cases_on `bt` >> fs[]
  >- (fs[well_formed_type_value_def, type_slot_size_def] >>
      qspec_then `n` mp_tac storage_copy_capacity_bound >> simp[]) >>
  rename1 `BytesT bd` >> Cases_on `bd` >> fs[] >>
  fs[well_formed_type_value_def, type_slot_size_def] >>
  qspec_then `n` mp_tac storage_copy_capacity_bound >> simp[]
QED

Theorem storage_copy_post_words[local]:
  !ctx func cenv cx e es sa sm s0 es1 v op s tv w writes k st.
    expr_post ctx func cenv cx e es sa sm s0 es1 v op s /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    ~is_word_type (expr_type e) /\ eval_operand op s = SOME w /\
    value_has_type tv v /\ encode_value tv v = SOME writes /\
    k + type_slot_size tv <= dimword (:256) /\ k < dimword (:256) ==>
    type_slot_size tv < dimword (:256) /\
    (!i. i < type_slot_size tv /\
         (?b. b < 32 /\
              ~dead_bytes (apply_writes (n2w k) writes st) k tv (k+i) b) ==>
         mload (w2n (w + n2w i * 32w)) s =
           mem_word_at (w2n w + 32*i) s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all hash_post_footprint_bound >> strip_tac >>
  `well_formed_type_value tv` by
    (drule vyperTypeValuesTheory.evaluate_type_well_formed_type_value >> simp[]) >>
  conj_tac
  >- (irule storage_copy_count_bound >> simp[] >> qexists_tac `v` >> decide_tac) >>
  rpt strip_tac >> irule storage_copy_live_memory_word >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  qexists_tac `v` >> simp[]
QED

Theorem storage_copy_backend_fold[local]:
  !is k ws s tr.
    FOLDL (\t i. (if tr then tstore else sstore) (k+n2w i) (ws i) t) s is =
    if tr then
      s with vs_transient :=
        (s.vs_call_ctx.cc_address =+
          FOLDL (\t i. update_storage (k+n2w i) (ws i) t)
            (contract_transient s) is) s.vs_transient
    else
      s with vs_accounts :=
        (s.vs_call_ctx.cc_address =+
          (lookup_account s.vs_call_ctx.cc_address s.vs_accounts with storage :=
            FOLDL (\t i. update_storage (k+n2w i) (ws i) t)
              (contract_storage s) is)) s.vs_accounts
Proof
  Induct >> rpt gen_tac >> Cases_on `tr` >>
  simp[FOLDL, sstore_def, tstore_def, contract_storage_def,
       contract_transient_def, vfmStateTheory.lookup_account_def,
       combinTheory.APPLY_UPDATE_THM, combinTheory.APPLY_UPDATE_ID]
QED

Theorem storage_copy_accounts_fold[local]:
  !cx es s tr k ws is stor.
    accounts_rel cx es s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
    storage_agree (storage_dead cx tr stor) stor
      (FOLDL (\t i. update_storage (k+n2w i) (ws i) t)
        (if tr then contract_transient s else contract_storage s) is) ==>
    accounts_rel cx (set_storage cx es tr stor)
      (FOLDL (\t i. (if tr then tstore else sstore) (k+n2w i) (ws i) t) s is)
Proof
  rpt gen_tac >> strip_tac >>
  simp[storage_copy_backend_fold] >> Cases_on `tr` >> gvs[]
  >- (irule accounts_rel_set_transient >>
      qexistsl_tac [`es`, `s`, `stor`] >>
      simp[set_storage_backend_eq] >> goal_assum (drule_at Any) >> simp[]) >>
  irule accounts_rel_set_storage >>
  qexistsl_tac [`es`, `s`, `stor`] >>
  simp[set_storage_backend_eq] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem storage_copy_state_fold[local]:
  !ctx func cenv cx es s tr k ws is stor.
    stmt_state_rel ctx func cenv cx es s /\
    storage_agree (storage_dead cx tr stor) stor
      (FOLDL (\t i. update_storage (k+n2w i) (ws i) t)
        (if tr then contract_transient s else contract_storage s) is) ==>
    stmt_state_rel ctx func cenv cx (set_storage cx es tr stor)
      (FOLDL (\t i. (if tr then tstore else sstore) (k+n2w i) (ws i) t) s is)
Proof
  rpt gen_tac >> strip_tac >>
  `s.vs_call_ctx.cc_address = cx.txn.target /\ accounts_rel cx es s` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  drule_all storage_copy_accounts_fold >> strip_tac >>
  qmatch_asmsub_abbrev_tac `accounts_rel cx es1 s1` >>
  drule accounts_rel_storage_transient >> strip_tac >>
  `state_rel func cenv cx es1 s1` by
    (Cases_on `tr` >> gvs[Abbr `s1`, Abbr `es1`, storage_copy_backend_fold] >>
     fs[stmt_state_rel_def, state_rel_def, set_storage_def,
        local_ptrs_rel_def, local_backed_def, local_region_def, lookup_var_def,
        immutables_rel_def, logs_rel_def] >> gvs[] >> metis_tac[]) >>
  `immutable_alloca_sep func cenv cx es1 s1` by
    (`immutable_alloca_sep func cenv cx es s` by fs[stmt_state_rel_def] >>
     irule immutable_alloca_sep_fields >> qexistsl_tac [`s`, `es`] >>
     simp[] >> Cases_on `tr` >>
     simp[Abbr `s1`, Abbr `es1`, storage_copy_backend_fold,
          set_storage_def, local_region_def, lookup_var_def] >> metis_tac[]) >>
  irule stmt_state_rel_allocas_frame >> simp[] >>
  qexistsl_tac [`es`, `s`] >> simp[] >> Cases_on `tr` >>
  simp[Abbr `s1`, storage_copy_backend_fold]
QED

Theorem storage_copy_initial_agree[local]:
  !ctx func cenv cx es s tr.
    stmt_state_rel ctx func cenv cx es s ==>
    storage_agree (storage_dead cx tr (get_storage cx es tr))
      (get_storage cx es tr)
      (if tr then contract_transient s else contract_storage s)
Proof
  rpt strip_tac >> Cases_on `tr` >>
  fs[stmt_state_rel_def, state_rel_def, storage_rel_def,
     transient_rel_def, get_storage_def, vfmStateTheory.lookup_account_def]
QED

Theorem storage_copy_state_region[local]:
  !ctx func cenv cx es s tr mid id subs k tv v writes off mem ws res es'.
    stmt_state_rel ctx func cenv cx es s /\
    declared_storage_region cx mid id subs = SOME (tr, k, tv) /\
    w2n k + type_slot_size tv <= dimword (:256) /\
    (!mid' id' subs' k' tv'.
       declared_storage_region cx mid' id' subs' = SOME (tr, k', tv') /\
       (k', tv') <> (k, tv) ==>
       ranges_disjoint (w2n k) (type_slot_size tv)
                       (w2n k') (type_slot_size tv')) /\
    well_formed_type_value tv /\ value_has_type tv v /\
    val_in_memory tv v off mem /\ encode_value tv v = SOME writes /\
    (!i. i < type_slot_size tv /\
         (?b. b < 32 /\
              ~dead_bytes (apply_writes k writes (get_storage cx es tr))
                (w2n k) tv (w2n k + i) b) ==>
         ws i = mem_word_at (off + 32 * i) mem) /\
    write_storage_slot cx tr k tv v es = (res, es') ==>
    res = INL () /\
    stmt_state_rel ctx func cenv cx es'
      (FOLDL (\t i. (if tr then tstore else sstore) (k+n2w i) (ws i) t)
        s (COUNT_LIST (type_slot_size tv)))
Proof
  rpt gen_tac >> strip_tac >>
  drule_then (qspec_then `tr` assume_tac) storage_copy_initial_agree >>
  drule_all storage_agree_copy_region >> strip_tac >>
  gvs[write_storage_slot_eq] >>
  irule storage_copy_state_fold >> simp[]
QED

Theorem storage_copy_state_zero[local]:
  !ctx func cenv cx es s tr k.
    stmt_state_rel ctx func cenv cx es s ==>
    stmt_state_rel ctx func cenv cx
      (set_storage cx es tr (update_storage k 0w (get_storage cx es tr)))
      ((if tr then tstore else sstore) k 0w s)
Proof
  rpt gen_tac >> strip_tac >>
  drule_then (qspec_then `tr` assume_tac) storage_copy_initial_agree >>
  `storage_agree
     (storage_dead cx tr (update_storage k 0w (get_storage cx es tr)))
     (update_storage k 0w (get_storage cx es tr))
     (update_storage k 0w
       (if tr then contract_transient s else contract_storage s))` by
    (irule storage_agree_update >> goal_assum (drule_at Any) >>
     metis_tac[storage_dead_update_zero]) >>
  drule storage_copy_state_fold >>
  disch_then (qspecl_then [`tr`, `k`, `\i. 0w`, `[0]`] mp_tac) >>
  simp[wordsTheory.WORD_ADD_0] >> disch_then irule >> simp[]
QED

Theorem storage_copy_control_frame[local]:
  !ctx func cenv cx es s V bb ix prev.
    stmt_state_rel ctx func cenv cx es
      (s with <|vs_vars := V; vs_current_bb := bb;
                vs_inst_idx := ix; vs_prev_bb := prev|>) =
    stmt_state_rel ctx func cenv cx es (s with vs_vars := V)
Proof
  simp[stmt_state_rel_def, state_rel_def, accounts_rel_def, local_ptrs_rel_def,
       local_region_def, local_backed_def, lookup_var_def, storage_rel_def,
       transient_rel_def, immutables_rel_def, logs_rel_def, call_ctx_rel_def,
       contract_storage_def, contract_transient_def, venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def, alloca_room_def,
       pending_alloca_size_def, immutable_alloca_sep_def]
QED

Theorem storage_copy_normalized_state[local]:
  !ctx func cenv cx es s t sa.
    stmt_state_rel ctx func cenv cx es
      (t with <|vs_vars := s.vs_vars; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx; vs_prev_bb := s.vs_prev_bb|>) /\
    local_ptrs_reserved cenv sa /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
    stmt_state_rel ctx func cenv cx es t
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
  simp[storage_copy_control_frame] >>
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es
     ((t with vs_vars := s.vs_vars) with vs_vars := t.vs_vars)` suffices_by simp[] >>
  irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac >>
  fs[local_ptrs_reserved_def, lookup_var_def] >> metis_tac[]
QED

Theorem storage_copy_bulk_run[local]:
  !ctx func cenv cx es' tr src k n sa sb u s b.
    compile_word_copy_loop src (Lit k) n LocMemory
      (if tr then LocTransient else LocStorage) F sa = (u,sb) /\
    n < dimword (:256) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME b /\
    fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    stmt_state_rel ctx func cenv cx es'
      (FOLDL (\t i. (if tr then tstore else sstore)
        (k+n2w i) (mload (w2n (b+n2w i*32w)) s) t) s (COUNT_LIST n)) ==>
    ?t. stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==>
                  FLOOKUP t.vs_allocas aid = SOME ent) /\
      !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
               ?fuel'. run_from fuel' ctx func s = r
Proof
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `compile_word_copy_loop _ _ _ _ _ _ _ = _`)
    compile_store_copy_frag >>
  simp[eval_operand_def] >>
  disch_then (qspecl_then [`ctx`, `s`, `b`, `\r. F`] mp_tac) >>
  (impl_tac >- (Cases_on `tr` >> simp[])) >> strip_tac >>
  drule stmtSimDeclTheory.frag_exec_no_exit_run >> disch_then drule >>
  disch_then (qspec_then `s` mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  qmatch_asmsub_abbrev_tac `norm = FOLDL _ _ _` >>
  `stmt_state_rel ctx func cenv cx es' norm` by
    (Cases_on `tr` >> gvs[Abbr `norm`]) >>
  `stmt_state_rel ctx func cenv cx es' t` by
    (irule storage_copy_normalized_state >>
     qexistsl_tac [`s`, `sa`] >> fs[Abbr `norm`] >>
     Cases_on `tr` >> gvs[]) >>
  simp[] >>
  `(if (if tr then LocTransient else LocStorage) = LocStorage
     then sstore else tstore) = (if tr then tstore else sstore)` by
    (Cases_on `tr` >> simp[]) >>
  qpat_x_assum `norm = _`
    (mp_tac o AP_TERM ``\t:venom_state. t.vs_allocas``) >>
  simp[Abbr `norm`, storage_copy_backend_fold] >>
  Cases_on `tr` >> simp[] >> metis_tac[]
QED

Theorem storage_copy_one_run[local]:
  !ctx func cenv cx es' tr src k sa sm sb op s b.
    emit_op MLOAD [src] sa = (op,sm) /\
    emit_void (if tr then TSTORE else SSTORE) [Lit k;op] sm = ((),sb) /\
    eval_operand src s = SOME b /\ local_ptrs_reserved cenv sa /\
    fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    stmt_state_rel ctx func cenv cx es'
      ((if tr then tstore else sstore) k (mload (w2n b) s) s) ==>
    ?t. stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==>
                  FLOOKUP t.vs_allocas aid = SOME ent) /\
      !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
               ?fuel'. run_from fuel' ctx func s = r
Proof
  rpt gen_tac >> strip_tac >>
  `frag_exec ctx sa sb (\t. t = s)
     (\t. stmt_state_rel ctx func cenv cx es' t /\
       (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
       (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==>
                   FLOOKUP t.vs_allocas aid = SOME ent)) (\r. F)` by
    (imp_res_tac emitted_insts_emit_op >> imp_res_tac emit_op_extends >>
     imp_res_tac emitted_insts_emit_void >> imp_res_tac emit_void_extends >>
     drule_all emitted_insts_append >> strip_tac >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
        (emitted_insts sa sb)` by
       (Cases_on `tr` >> gvs[mk_inst_def, is_terminator_def]) >>
     irule frag_exec_run_inst_seq >>
     fs[same_blocks_def, IS_PREFIX_APPEND3] >>
          reverse conj_tac >-
       (pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[IS_PREFIX_APPEND3]) >>
     rpt strip_tac >> gvs[] >>
     qmatch_goalsub_abbrev_tac `Var out` >>
     `step_inst_base (mk_inst sa.cs_next_id MLOAD [src] [out]) s =
        OK (update_var out (mload (w2n b) s) s)` by
       (irule step_MLOAD >> simp[]) >>
     `not_local_ptr cenv es'.scopes out` by
       (simp[Abbr `out`] >> irule local_ptrs_reserved_fresh >>
        metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
     `!x. not_fresh_at sa x ==> x <> out` by
       (simp[not_fresh_at_def, Abbr `out`] >>
        metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
     `stmt_state_rel ctx func cenv cx es'
        (update_var out (mload (w2n b) s)
          ((if tr then tstore else sstore) k (mload (w2n b) s) s))` by
       (irule stmt_state_rel_update_var >> simp[]) >>
     Cases_on `tr` >>
     simp[run_inst_seq_def, step_inst_base_def, exec_write2_def,
          mk_inst_def, eval_operand_def, lookup_var_def, update_var_def,
          FLOOKUP_UPDATE, stmt_state_rel_inst_idx] >>
     qpat_x_assum `stmt_state_rel _ _ _ _ _ (update_var _ _ _)` mp_tac >>
     simp[update_var_def, sstore_def, tstore_def, LET_THM,
          FLOOKUP_UPDATE] >> metis_tac[]) >>
  drule stmtSimDeclTheory.frag_exec_no_exit_run >> disch_then drule >>
  disch_then (qspec_then `s` mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `t` >> simp[]
QED

Theorem storage_copy_suffix_run[local]:
  !ctx func cenv cx es' tr src k n typ src_ty loc sa sb s b.
    compile_assign_value cenv (Lit k)
      (if tr then LocTransient else LocStorage) src F loc
      typ src_ty NONE (32 * n) sa = ((),sb) /\
    ~is_word_type typ /\
    (typ = src_ty \/ (is_bytestring_type typ /\ is_bytestring_type src_ty)) /\
    0 < n /\ n < dimword (:256) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME b /\
    fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    stmt_state_rel ctx func cenv cx es'
      (FOLDL (\t i. (if tr then tstore else sstore)
        (k+n2w i) (mload (w2n (b+n2w i*32w)) s) t) s (COUNT_LIST n)) ==>
    ?t. stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==>
                  FLOOKUP t.vs_allocas aid = SOME ent) /\
      !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
               ?fuel'. run_from fuel' ctx func s = r
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
    dep_rewrite.DEP_REWRITE_TAC[assign_storage_copy_suffix] >> simp[] >>
  Cases_on `32 * n <= 32`
  >- (`n = 1` by decide_tac >> gvs[] >>
      simp[comp_bind_def, AllCaseEqs()] >> strip_tac >>
      Cases_on `emit_op MLOAD [src] sa` >> gvs[] >>
      `COUNT_LIST 1 = [0]` by EVAL_TAC >>
      fs[wordsTheory.WORD_ADD_0, wordsTheory.WORD_MULT_CLAUSES] >>
      drule_all storage_copy_one_run >> simp[]) >>
  simp[compile_memory_to_storage_def, compile_memory_to_transient_def,
       comp_bind_def, comp_return_def, AllCaseEqs()] >> strip_tac >>
  fs[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  rename1 `_ sa = (u,sf)` >>
  `compile_word_copy_loop src (Lit k) n LocMemory
     (if tr then LocTransient else LocStorage) F sa = (u,sf)` by
    (Cases_on `tr` >> gvs[]) >>
  drule_all storage_copy_bulk_run >> simp[]
QED

Theorem storage_copy_post_region[local]:
  !ctx func cenv cx e es sa sm s0 es1 v op s tv tr mid id slot es'.
    expr_post ctx func cenv cx e es sa sm s0 es1 v op s /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    ~is_word_type (expr_type e) /\ value_has_type tv v /\
    declared_storage_region cx mid id [] = SOME (tr,n2w slot,tv) /\
    0 < type_slot_size tv /\ slot + type_slot_size tv <= dimword (:256) /\
    (!mid' id' subs' k' tv'.
       declared_storage_region cx mid' id' subs' = SOME (tr,k',tv') /\
       (k',tv') <> (n2w slot,tv) ==>
       ranges_disjoint slot (type_slot_size tv) (w2n k') (type_slot_size tv')) /\
    write_storage_slot cx tr (n2w slot) tv v es1 = (INL (),es') ==>
    ?w. eval_operand op s = SOME w /\ type_slot_size tv < dimword (:256) /\
      stmt_state_rel ctx func cenv cx es'
        (FOLDL (\t i. (if tr then tstore else sstore)
          (n2w slot+n2w i) (mload (w2n (w+n2w i*32w)) s) t)
          s (COUNT_LIST (type_slot_size tv)))
Proof
  rpt gen_tac >> strip_tac >>
  `slot < dimword (:256)` by decide_tac >>
  `IS_SOME (encode_value tv v)` by metis_tac[value_has_type_equiv] >>
  Cases_on `encode_value tv v` >> gvs[] >>
  rename1 `encode_value tv v = SOME writes` >>
  `stmt_state_rel ctx func cenv cx es1 s /\
   expr_val_rel cx (expr_type e) v op s` by fs[expr_post_def] >>
  qpat_x_assum `expr_val_rel _ _ _ _ _` mp_tac >>
  simp[expr_val_rel_def] >> strip_tac >>
  `well_formed_type_value tv` by
    (drule vyperTypeValuesTheory.evaluate_type_well_formed_type_value >> simp[]) >>
  `slot < dimword (:256)` by decide_tac >>
  drule_all storage_copy_post_words >>
  disch_then (qspec_then `get_storage cx es1 tr` strip_assume_tac) >>
  qexists_tac `w` >> simp[] >>
  ho_match_mp_tac (cj 2 storage_copy_state_region) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  qexistsl_tac [`mid`, `id`, `[]`] >> simp[] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem storage_copy_success_run[local]:
  !ctx func cenv cx e es es1 es' v tv tr mid id slot sa sm sf op loc s0.
    (do result <- eval_expr cx e; read_result cx result od) es = (INL v,es1) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    ~is_word_type (expr_type e) /\ value_has_type tv v /\
    declared_storage_region cx mid id [] = SOME (tr,n2w slot,tv) /\
    0 < type_slot_size tv /\ slot + type_slot_size tv <= dimword (:256) /\
    (!mid' id' subs' k' tv'.
       declared_storage_region cx mid' id' subs' = SOME (tr,k',tv') /\
       (k',tv') <> (n2w slot,tv) ==>
       ranges_disjoint slot (type_slot_size tv) (w2n k') (type_slot_size tv')) /\
    write_storage_slot cx tr (n2w slot) tv v es1 = (INL (),es') /\
    expr_sim ctx func cenv cx (expr_type e) e es /\
    lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
    compile_assign_value cenv (Lit (n2w slot))
      (if tr then LocTransient else LocStorage) op F loc
      (expr_type e) (lowered_value_type cenv e) NONE (type_memory_size tv) sm = ((),sf) /\
    fn_has_code sa sm func /\ fn_has_code sm sf func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
      t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
             lookup_var x t = SOME u) /\
      (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==>
                  FLOOKUP t.vs_allocas aid = SOME ent) /\
      !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
               ?fuel'. run_from fuel' ctx func s0 = r
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_lower_value_var >> simp[] >> disch_tac >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  drule_all storage_copy_success_compatible >> disch_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `op`, `INL v`, `es1`, `s0`] mp_tac) >>
  (impl_tac >- simp[expr_res_ok_def]) >>
  simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
  (impl_tac >- simp[]) >> simp[] >> strip_tac >>
  rename1 `expr_post ctx _ _ _ _ _ _ _ _ _ _ _ s1` >>
  drule_all storage_copy_post_region >> strip_tac >>
  RULE_ASSUM_TAC (REWRITE_RULE [exprSimAttributeFieldsTheory.type_memory_size_slots]) >>
  drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)
    storage_copy_suffix_run >>
  disch_then (qspecl_then [`ctx`, `func`, `cx`, `es'`, `s1`, `w`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[ci_mono_def]) >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  qpat_x_assum `!fuel r. run_from fuel _ _ t = r /\ _ ==> _`
    (qspecl_then [`fuel`, `run_from fuel ctx func t`] mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  qpat_x_assum `!fuel. _ ==> ?fuel'. run_from fuel' _ _ s0 = _`
    (qspec_then `fuel'` mp_tac) >>
  simp[]
QED

Theorem assign_storage_empty_stmt_frag[local]:
  !ctx func cx lctx RetQ cenv ty src id e es res es' ts tr typ id_str slot tvt.
    eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src,id))) e) es =
      (res,es') /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    has_length_word (expr_type e) /\ is_empty_value_expr e /\
    expr_type e = typ /\ (!elem n. typ <> ArrayT elem (Dynamic n)) /\
    (!ann t args. e = TypeBuiltin ann Empty t args ==> t = typ) /\
    evaluate_type (get_tenv cx) typ = SOME tvt /\
    cenv.ce_hashmap_info (src,id) = NONE /\
    (!v st. (do result <- eval_expr cx e; read_result cx result od) es =
       (INL v,st) ==> value_has_type tvt v) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
        (Assign (BaseTarget (TopLevelNameTarget (src,id))) e)) es res es'
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def] >> rpt gen_tac >> strip_tac >>
  drule_all eval_assign_toplevel >> strip_tac >>
  drule_all storage_copy_empty_rhs >> strip_tac >> gvs[]
  >- (qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >>
      simp[write_storage_slot_eq, apply_writes_def, wordsTheory.WORD_ADD_0] >>
      strip_tac >> gvs[] >>
      `FLOOKUP cenv.ce_module_vars (src,id) =
         SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))` by
        (irule toplevel_storage_ce_vars >>
         gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
      drule_all assign_storage_empty_code >> strip_tac >> gvs[] >>
      drule_then (qspecl_then [`tr`, `n2w slot`] assume_tac)
        storage_copy_state_zero >>
      `eval_operand (Lit 0w) s0 = SOME 0w` by simp[eval_operand_def] >>
      `stmt_state_rel ctx func cenv cx
         (set_storage cx es tr (update_storage (n2w slot) 0w (get_storage cx es tr)))
         (if tr then tstore (n2w slot) 0w s0 else sstore (n2w slot) 0w s0)` by
        (Cases_on `tr` >> gvs[]) >>
      drule_all assign_storage_store_run >> strip_tac >>
      disj1_tac >> qexists_tac `t` >>
      simp[stmt_lands_def, cenv_top_ext_refl, wordsTheory.n2w_mod] >>
      Cases_on `tr` >> gvs[] >> drule stmtSimDeclMemTheory.emit_void_nonterminator_open >>
      simp[is_terminator_def]) >>
  gvs[stmt_res_ok_def]
QED

(* self.x = e for a storage or transient variable x whose declared type typ
   is not held in one word and is not a DynArray, with e of type typ.  The
   premises on x's region are what storage_layout_safe gives: it fits the
   slot space and is apart from every other declared region.  An empty(t)
   right-hand side has t = typ, as type_builtin_result_ok requires; the
   lowering stores only a zero length word for it. *)
Theorem compile_assign_storage_copy_stmt_frag:
  !ctx func cx lctx RetQ cenv ty src id e es res es' ts tr typ id_str slot
   tvt.
    eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src, id))) e) es =
      (res, es') /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    expr_type e = typ /\ ~is_word_type typ /\
    (!elem n. typ <> ArrayT elem (Dynamic n)) /\
    (!ann t args. e = TypeBuiltin ann Empty t args ==> t = typ) /\
    evaluate_type (get_tenv cx) typ = SOME tvt /\
    0 < type_slot_size tvt /\
    type_memory_bytes cenv typ = type_memory_size tvt /\
    cenv.ce_hashmap_info (src, id) = NONE /\
    cenv.ce_module_var_type (src, id) = SOME typ /\
    slot + type_slot_size tvt <= dimword (:256) /\
    (!mid' n' subs' k' tv'.
       declared_storage_region cx mid' n' subs' = SOME (tr, k', tv') /\
       (k', tv') <> (n2w slot, tvt) ==>
       ranges_disjoint slot (type_slot_size tvt)
                       (w2n k') (type_slot_size tv')) /\
    (!v es1.
       (do result <- eval_expr cx e; read_result cx result od) es =
         (INL v, es1) ==>
       value_has_type tvt v) /\
    expr_sim ctx func cenv cx (expr_type e) e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assign (BaseTarget (TopLevelNameTarget (src, id))) e)) es res es'
Proof
  gen_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `has_length_word (expr_type e) /\ is_empty_value_expr e`
  >- (irule assign_storage_empty_stmt_frag >> metis_tac[]) >>
  simp[stmt_frag_def] >> rpt gen_tac >> strip_tac >>
  `FLOOKUP cenv.ce_module_vars (src,id) =
     SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))` by
    (irule toplevel_storage_ce_vars >>
     gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  drule_all assign_storage_copy_code_parts >> strip_tac >>
  qpat_x_assum `~(has_length_word _ /\ _)` kall_tac >> gvs[] >>
  drule (INST_TYPE [alpha |-> ``:num # num``] storage_copy_no_dyn_info) >>
  disch_then (qspec_then
    `\elem. ((type_memory_bytes cenv elem + 31) DIV 32,
             type_memory_bytes cenv elem)` assume_tac) >>
  fs[] >>
  `cs_extends sa sB` by metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends sB sb` by
    metis_tac[cj 1 ci_mono_stmt_helpers, ci_mono_def, pairTheory.SND] >>
  `fn_has_code sa sB func /\ fn_has_code sB sb func` by
    metis_tac[fn_has_code_split] >>
  drule_all eval_assign_toplevel >> strip_tac >>
  Cases_on `r` >> gvs[]
  >- (drule typed_storage_copy_write >>
      disch_then (qspecl_then [`cx`, `tr`, `n2w slot`, `es1`] strip_assume_tac) >>
      gvs[] >>
      `declared_storage_region cx src id [] = SOME (tr,n2w slot,tvt)` by
        simp[vyperStorageLayoutSafetyTheory.declared_storage_region_def] >>
      drule_all (SRULE [] storage_copy_success_run) >> strip_tac >>
      disj1_tac >> qexists_tac `t` >>
      simp[stmt_lands_def, cenv_top_ext_refl] >>
      drule_all storage_copy_success_compatible >>
      disch_then (qspec_then `cenv` mp_tac) >>
      strip_tac >> irule assign_storage_copy_suffix_open >> metis_tac[]) >>
  rename1 `(INR err : value + exception, es1)` >>
  `expr_res_ok (INR err : value + exception)` by
    (qpat_x_assum `stmt_res_ok _ _` mp_tac >>
     simp[stmt_res_ok_def, expr_res_ok_def, no_control_exc_def] >>
     rpt strip_tac >> gvs[no_control_exc_def]) >>
  drule_all expr_sim_error_run >> strip_tac >>
  drule exit_result_not_error >> strip_tac >>
  disj2_tac >> qexists_tac `fuel` >>
  qpat_x_assum `run_from fuel _ _ s0 = r`
    (fn th => rewrite_tac[th]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  pure_rewrite_tac[stmt_exit_def] >> disj1_tac >> first_assum ACCEPT_TAC
QED
