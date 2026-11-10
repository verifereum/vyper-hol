(* Storage assignment compiler and semantic boundaries for the memory proof. *)
Theory bodyMemAssignTopCopySem
Ancestors
  exprSimHashBoundary
  bodyMemAssignTopCopyFacts stmtSimAssignStorageCopy stmtSimStoreCopy
  stmtSimDeclMem stmtSimAssignMem stmtSimAssignStorage stmtSimAssign exprLoweringProps
  stmtLowering exprLowering emitHelper emitHelperProps context compileEnv loweringStateRelDefs
  vyperStorage vyperStorageBackend vyperValue vyperTyping
  accountsRelProps exprSimHash exprSimProps stmtSimProps loweringPosts storageCopyLive
  words arithmetic
  venomState valueEncodingProps venomInst list rich_list finite_map
Libs
  monadsyntax

Theorem topcopy_typed_storage_write:
  !cx tr slot tvt v es.
    value_has_type tvt v /\ ~cx.txn.is_static ==>
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

Theorem topcopy_no_dyn_info:
  (!elem n. typ <> ArrayT elem (Dynamic n)) ==>
  (case typ of ArrayT elem (Dynamic n) => SOME (f elem) | _ => NONE) = NONE
Proof
  strip_tac >> Cases_on `typ` >> simp[] >>
  rename1 `ArrayT elem bound` >> Cases_on `bound` >> simp[] >> metis_tac[]
QED

Theorem topcopy_code_parts:
  !cenv lctx ty nsid e sa sf c tr slot vtyp.
    stmt_env cenv lctx ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e)
      sa = (c, sf) /\
    FLOOKUP cenv.ce_module_vars nsid =
      SOME (if tr then TransientLoc slot else StorageLoc slot) /\
    cenv.ce_hashmap_info nsid = NONE /\
    cenv.ce_module_var_type nsid = SOME vtyp /\
    ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    lowered_value_type cenv e = expr_type e ==>
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

Theorem topcopy_suffix:
  !cenv dst src tr loc typ src_ty mem_size.
    ~is_word_type typ /\
    typ = src_ty /\ type_memory_bytes cenv typ = mem_size ==>
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
  rpt gen_tac >> strip_tac >> gvs[] >> Cases_on `tr` >>
  simp[FUN_EQ_THM, compile_assign_value_def, comp_bind_def, comp_return_def]
QED

Theorem topcopy_loop_open:
  !src dst n loc ctor sa u sb.
    compile_word_copy_loop src dst n LocMemory loc ctor sa = (u,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_word_copy_loop_def, compile_word_copy_loop_op_def, compile_word_copy_loop_base_def, comp_ignore_bind_def, comp_bind_def] >>
  ntac 4 (pairarg_tac >> simp[]) >>
  ntac 4 (pairarg_tac >> simp[]) >>
  ntac 4 (pairarg_tac >> simp[]) >>
  ntac 4 (pairarg_tac >> simp[]) >>
  pairarg_tac >> simp[] >>
  strip_tac >> pop_assum mp_tac >>
  simp[new_block_def, block_is_terminated_def] >> strip_tac >> gvs[]
QED

Theorem topcopy_suffix_open:
  !cenv dst src tr loc typ src_ty mem_size sa sb.
    compile_assign_value cenv dst (if tr then LocTransient else LocStorage)
      src F loc typ src_ty NONE mem_size sa = ((),sb) /\
    ~is_word_type typ /\
    typ = src_ty /\ type_memory_bytes cenv typ = mem_size ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  dep_rewrite.DEP_REWRITE_TAC[topcopy_suffix] >> simp[] >>
  Cases_on `mem_size <= 32`
  >- (simp[comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
      drule stmtSimDeclMemTheory.emit_void_nonterminator_open >>
      Cases_on `tr` >> simp[is_terminator_def]) >>
  simp[compile_memory_to_storage_def, compile_memory_to_transient_def,
       comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  irule topcopy_loop_open >> Cases_on `tr` >> metis_tac[]
QED

Theorem topcopy_backend_fold:
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

Theorem topcopy_accounts_fold:
  !cx es s tr k ws is stor.
    accounts_rel cx es s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
    storage_agree (storage_dead cx tr stor) stor
      (FOLDL (\t i. update_storage (k+n2w i) (ws i) t)
        (if tr then contract_transient s else contract_storage s) is) ==>
    accounts_rel cx (set_storage cx es tr stor)
      (FOLDL (\t i. (if tr then tstore else sstore) (k+n2w i) (ws i) t) s is)
Proof
  rpt gen_tac >> strip_tac >>
  simp[topcopy_backend_fold] >> Cases_on `tr` >> gvs[]
  >- (irule accounts_rel_set_transient >>
      qexistsl_tac [`es`, `s`, `stor`] >>
      simp[set_storage_backend_eq] >> goal_assum (drule_at Any) >> simp[]) >>
  irule accounts_rel_set_storage >>
  qexistsl_tac [`es`, `s`, `stor`] >>
  simp[set_storage_backend_eq] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem topcopy_state_fold:
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
  drule_all topcopy_accounts_fold >> strip_tac >>
  qmatch_asmsub_abbrev_tac `accounts_rel cx es1 s1` >>
  drule accounts_rel_storage_transient >> strip_tac >>
  `state_rel func cenv cx es1 s1` by
    (Cases_on `tr` >> gvs[Abbr `s1`, Abbr `es1`, topcopy_backend_fold] >>
     fs[stmt_state_rel_def, state_rel_def, set_storage_def,
        local_ptrs_rel_def, local_backed_def, local_region_def, lookup_var_def,
        immutables_rel_def, logs_rel_def] >> gvs[] >> metis_tac[]) >>
  `immutable_alloca_sep func cenv cx es1 s1` by
    (`immutable_alloca_sep func cenv cx es s` by fs[stmt_state_rel_def] >>
     irule immutable_alloca_sep_fields >> qexistsl_tac [`s`, `es`] >>
     simp[] >> Cases_on `tr` >>
     simp[Abbr `s1`, Abbr `es1`, topcopy_backend_fold,
          set_storage_def, local_region_def, lookup_var_def] >> metis_tac[]) >>
  `immutable_base_zero cenv s1` by
    (`immutable_base_zero cenv s` by fs[stmt_state_rel_def] >>
     irule immutable_base_zero_frame >> qexists_tac `s` >>
     Cases_on `tr` >> simp[Abbr `s1`, topcopy_backend_fold, lookup_var_def]) >>
  irule stmt_state_rel_allocas_frame >>
  qpat_assum `immutable_base_zero cenv _` (irule_at Any) >> simp[] >>
  qexistsl_tac [`s`, `es`] >> simp[] >> Cases_on `tr` >>
  simp[Abbr `s1`, topcopy_backend_fold]
QED

Theorem topcopy_initial_agree:
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

Theorem topcopy_state_region:
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
  drule_then (qspec_then `tr` assume_tac) topcopy_initial_agree >>
  drule_all storage_agree_copy_region >> strip_tac >>
  `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  gvs[write_storage_slot_eq] >>
  irule topcopy_state_fold >> simp[]
QED

Theorem topcopy_control_frame:
  !ctx func cenv cx es s V bb ix prev.
    stmt_state_rel ctx func cenv cx es
      (s with <|vs_vars := V; vs_current_bb := bb;
                vs_inst_idx := ix; vs_prev_bb := prev|>) =
    stmt_state_rel ctx func cenv cx es (s with vs_vars := V)
Proof
  rpt gen_tac >>
  `fmp_room ctx func
     (s with <|vs_vars := V; vs_current_bb := bb;
               vs_inst_idx := ix; vs_prev_bb := prev|>) =
   fmp_room ctx func (s with vs_vars := V)` by
    (irule fmp_room_fields_cong >> simp[]) >>
  simp[stmt_state_rel_def, state_rel_def, accounts_rel_def, local_ptrs_rel_def,
       local_region_def, local_backed_def, immutable_base_zero_alt,
       lookup_var_def, storage_rel_def,
       transient_rel_def, immutables_rel_def, logs_rel_def, call_ctx_rel_def,
       contract_storage_def, contract_transient_def, venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def, alloca_room_def,
       pending_alloca_size_def, immutable_alloca_sep_def]
QED

Theorem topcopy_normalized_state:
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
  simp[topcopy_control_frame] >>
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es
     ((t with vs_vars := s.vs_vars) with vs_vars := t.vs_vars)` suffices_by simp[] >>
  irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac >>
  fs[local_ptrs_reserved_def, lookup_var_def] >> metis_tac[]
QED

Theorem topcopy_val_footprint:
  ~is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv ==>
  val_footprint tv v = type_memory_size tv
Proof
  rpt strip_tac >> Cases_on `v` >> simp[val_footprint_def] >>
  Cases_on `tv` >> simp[] >>
  rename1 `BaseTV b` >> Cases_on `b` >> simp[] >>
  Cases_on `ty` >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(), is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(), is_bytestring_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(), is_bytestring_type_def]
QED

Theorem topcopy_word_address:
  !w i bytes.
    w2n w + bytes < dimword (:256) /\ 32*i < bytes ==>
    w2n (w + n2w i * 32w : 256 word) = w2n w + 32*i
Proof
  rpt strip_tac >>
  `w + n2w i * 32w = n2w (w2n w + 32*i)` by
    simp[GSYM word_add_n2w, GSYM word_mul_n2w, MULT_COMM, WORD_MULT_COMM] >>
  asm_rewrite_tac[] >>
  `w2n w + 32*i < dimword (:256)` by decide_tac >> simp[w2n_n2w]
QED

Theorem topcopy_post_words:
  !ctx func cenv cx e es sa sm s0 es1 v op s tv w.
    expr_post ctx func cenv cx e es sa sm s0 es1 v op s /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
    eval_operand op s = SOME w ==>
    type_slot_size tv < dimword (:256) /\
    (!i. i < type_slot_size tv ==>
         mload (w2n (w + n2w i * 32w)) s =
           mem_word_at (w2n w + 32*i) s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all hash_post_footprint_bound >> strip_tac >>
  drule_all topcopy_val_footprint >> disch_then (qspec_then `v` assume_tac) >>
  gvs[type_memory_size_slots] >>
  rpt strip_tac >>
  `w2n (w + n2w i * 32w) = w2n w + 32*i` by
    (irule topcopy_word_address >> qexists_tac `32 * type_slot_size tv` >>
     simp[] >> decide_tac) >>
  simp[valueEncodingPropsTheory.mem_word_at_eq_mload]
QED

Theorem topcopy_post_region:
  !ctx func cenv cx e es sa sm s0 es1 v op s tv tr mid id slot es'.
    expr_post ctx func cenv cx e es sa sm s0 es1 v op s /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
    value_has_type tv v /\
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
  drule_all topcopy_post_words >> strip_tac >>
  qexists_tac `w` >> simp[] >>
  ho_match_mp_tac (cj 2 topcopy_state_region) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  qexistsl_tac [`mid`, `id`, `[]`] >> simp[] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED
