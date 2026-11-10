(*
 * Statement simulation: Assign to a storage or transient variable (#637)
 *
 * self.x = e for a module variable x in storage or transient storage that
 * the lowering holds in one word (its ce_var_type is a word type), with e
 * of a word type.  The source evaluates e, looks x up (lookup_global: a
 * StoragePlace at x's layout slot), reads e's value and writes its
 * encoding at x's declared type at the slot (write_storage_slot).  The
 * lowering evaluates e, takes x's slot as a literal (no code), unwraps the
 * value and stores it with one SSTORE or TSTORE.  Storage and transient
 * storage agree on both sides but at dead bytes (accounts_rel); a write of
 * the word encode_value gives to a one-slot declared region keeps them so,
 * since it leaves the dead bytes as they are.
 *
 * TOP-LEVEL:
 *   eval_assign_toplevel             — the source run: the forced value of
 *                                      e, then write_storage_slot at x's
 *                                      slot
 *   encode_value_word_typed          — a value of a word type encodes as
 *                                      its typed word, in one slot
 *   stmt_state_rel_write_storage_word — a one-slot write on both sides
 *                                      that keeps the dead bytes keeps
 *                                      stmt_state_rel
 *   compile_assign_storage_stmt_frag — self.x = e for a storage or
 *                                      transient x held in one word and a
 *                                      word-typed e whose word is x's
 *                                      encoding of e's value, every outcome
 *   compile_assign_storage_typed_stmt_frag — the same when e has x's
 *                                      declared word type and its values
 *                                      are of that type
 *
 * Helpers: compile_get_target_ptr_toplevel, assign_storage_word_code_parts,
 *   assign_storage_store_run, assign_storage_word_success_run
 *)

Theory stmtSimAssignStorage
Ancestors
  stmtSimForced stmtSimDeclPath gasContext fragGasMode
  stmtSimProps
  stmtSimDefs
  exprSimDefs
  loweringPosts
  list rich_list finite_map pred_set
  fragExec exprSimLeaves stmtSimDecl stmtSimDeclMem storageStoreFrame
  stmtSimAssign stmtSimAssignMem accountsRelProps exprSimTopLevelProps
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv loweringStateRelDefs valueEncoding valueEncodingProofs
  vyperInterpreter vyperState vyperStorage vyperStorageBackend vyperValue
  vyperTyping vyperExprNoControl
  venomExecSemantics venomInst venomState
Libs
  monadsyntax

(* ===== The source ===== *)

(* self.x = e for a storage or transient variable x: e's forced value r,
   and on an error that error, on a value v the write of v at x's slot. *)
Theorem eval_assign_toplevel:
  !cx src id e es res es' ts tr typ id_str slot tvt.
    eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src, id))) e) es =
      (res, es') /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) typ = SOME tvt ==>
    ?r es1.
      (do result <- eval_expr cx e; read_result cx result od) es = (r, es1) /\
      (!ex. r = INR ex ==> res = INR ex /\ es' = es1 /\ no_control_exc ex) /\
      (!v. r = INL v ==>
           write_storage_slot cx tr (n2w slot) tvt v es1 = (res, es'))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `eval_expr cx e es = (r1, es1)` >>
  Cases_on `r1` >> simp[]
  >- (simp[Once evaluate_def, bind_def] >>
      simp[Once evaluate_def, lookup_global_def, bind_def,
           lift_option_type_def, return_def, LET_THM, get_place_def] >>
      Cases_on `read_result cx x es1` >>
      rename1 `read_result cx x es1 = (r2, es2)` >>
      Cases_on `r2` >> simp[write_place_def] >> strip_tac >> gvs[] >>
      drule read_result_no_control >> simp[]) >>
  strip_tac >> gvs[] >>
  imp_res_tac (cj 1 eval_expr_no_control) >> simp[]
QED

(* A value of a word type encodes, in one slot, as the word typed_val_to_w256
   gives it. *)
Theorem encode_value_word_typed:
  !tenv t tv v.
    is_word_type t /\ evaluate_type tenv t = SOME tv /\
    value_has_type tv v ==>
    encode_value tv v = SOME [(0, typed_val_to_w256 tv v)]
Proof
  rpt gen_tac >> strip_tac >>
  `(?n. t = BaseT (UintT n)) \/ (?n. t = BaseT (IntT n)) \/
   t = BaseT BoolT \/ t = BaseT AddressT \/ t = BaseT DecimalT \/
   (?m. t = BaseT (BytesT (Fixed m)) /\ m <= 32) \/ (?n. t = FlagT n)` by
    (Cases_on `t` >> fs[is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> fs[is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> fs[is_word_type_def]) >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >>
  gvs[value_has_type_def, encode_value_def, encode_base_to_slot_def,
      typed_val_to_w256_def, val_to_w256_def, word_of_bytes_be_pad_right,
      bool_to_slot_def]
QED

Theorem local_ptrs_rel_storage_fields[local]:
  !func cenv sc s a t.
    local_ptrs_rel func cenv sc (s with <|vs_accounts := a|>) =
      local_ptrs_rel func cenv sc s /\
    local_ptrs_rel func cenv sc (s with <|vs_transient := t|>) =
      local_ptrs_rel func cenv sc s
Proof
  simp[local_ptrs_rel_def, local_backed_def, local_region_def,
       lookup_var_def]
QED

(* The source writes the one-slot encoding w of v at slot, a declared
   region of one slot, and Venom stores w there: stmt_state_rel holds after
   both. *)
Theorem stmt_state_rel_write_storage_word:
  !func cenv cx es s tr slot tvt v w res es' ctx.
    stmt_state_rel ctx func cenv cx es s /\
    (!u st. storage_dead cx tr (update_storage slot u st) =
            storage_dead cx tr st) /\
    write_storage_slot cx tr slot tvt v es = (res, es') /\
    encode_value tvt v = SOME [(0, w)] ==>
    res = INL () /\
    stmt_state_rel ctx func cenv cx es'
      (if tr then tstore slot w s else sstore slot w s)
Proof
  rpt gen_tac >> strip_tac >>
  `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  gvs[write_storage_slot_eq, apply_writes_def, LET_THM] >>
  `s.vs_call_ctx.cc_address = cx.txn.target /\ accounts_rel cx es s` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  qmatch_goalsub_abbrev_tac `stmt_state_rel ctx _ _ _ es1 s1` >>
  `accounts_rel cx es1 s1` by
    (Cases_on `tr` >> gvs[Abbr `s1`, Abbr `es1`]
     >- (irule accounts_rel_tstore >>
         simp[] >> qexists_tac `es` >>
         gvs[set_storage_backend_eq, get_storage_def, vfmStateTheory.lookup_account_def]) >>
     irule accounts_rel_sstore >>
     simp[] >>
     qexists_tac `es` >>
     gvs[set_storage_backend_eq, get_storage_def, vfmStateTheory.lookup_account_def]) >>
  `s1.vs_call_ctx = s.vs_call_ctx` by
    (Cases_on `tr` >> simp[Abbr `s1`, sstore_def, tstore_def, LET_THM]) >>
  drule accounts_rel_storage_transient >> strip_tac >>
  `state_rel func cenv cx es1 s1` by
    (Cases_on `tr` >> gvs[Abbr `s1`, Abbr `es1`] >>
     fs[stmt_state_rel_def, state_rel_def, sstore_def, tstore_def, LET_THM,
        set_storage_def, local_ptrs_rel_storage_fields, immutables_rel_def,
        logs_rel_def] >> gvs[] >> metis_tac[]) >>
  `immutable_alloca_sep func cenv cx es1 s1` by
    (`immutable_alloca_sep func cenv cx es s` by fs[stmt_state_rel_def] >>
     irule immutable_alloca_sep_fields >> qexistsl [`s`, `es`] >>
     simp[] >> Cases_on `tr` >>
     simp[Abbr `s1`, Abbr `es1`, sstore_def, tstore_def, LET_THM,
          set_storage_def, local_region_def, lookup_var_def] >>
     metis_tac[]) >>
  `immutable_base_zero cenv s1` by
    (`immutable_base_zero cenv s` by fs[stmt_state_rel_def] >>
     irule immutable_base_zero_frame >> qexists_tac `s` >>
     Cases_on `tr` >> simp[Abbr `s1`, sstore_def, tstore_def, LET_THM, lookup_var_def]) >>
  irule stmt_state_rel_allocas_frame >>
  qpat_assum `immutable_base_zero cenv _` (irule_at Any) >> simp[] >>
  qexistsl [`s`, `es`] >> simp[] >>
  Cases_on `tr` >> simp[Abbr `s1`, sstore_def, tstore_def, LET_THM]
QED

(* ===== The lowering ===== *)

(* A storage or transient variable's target pointer is its slot, and no
   code. *)
Theorem compile_get_target_ptr_toplevel:
  !cenv nsid tr slot st.
    FLOOKUP cenv.ce_module_vars nsid =
      SOME (if tr then TransientLoc slot else StorageLoc slot) /\
    cenv.ce_hashmap_info nsid = NONE ==>
    compile_get_target_ptr compile_expr cenv (TopLevelNameTarget nsid) st =
      ((Lit slot, SOME (if tr then LocTransient else LocStorage),
        OPTION_MAP ValPT (cenv.ce_module_var_type nsid)), st)
Proof
  Cases_on `tr` >> simp[compile_get_target_ptr_def, comp_return_def]
QED

(* The code of self.x = e for a storage or transient x the lowering holds
   in one word and word-typed e: e's value, then one SSTORE or TSTORE at
   x's slot. *)
Theorem assign_storage_word_code_parts:
  !cenv lctx ty nsid e sa sf c func tr slot vtyp.
    stmt_env cenv lctx ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e)
      sa = (c, sf) /\
    FLOOKUP cenv.ce_module_vars nsid =
      SOME (if tr then TransientLoc slot else StorageLoc slot) /\
    cenv.ce_hashmap_info nsid = NONE /\
    cenv.ce_module_var_type nsid = SOME vtyp /\ is_word_type vtyp /\
    is_word_type (expr_type e) /\ fn_has_code sa sf func ==>
    c = cenv /\
    ?sb op.
      lower_value compile_expr cenv (expr_type e) e sa = (op, sb) /\
      emit_void (if tr then TSTORE else SSTORE) [Lit slot; op] sb = ((), sf) /\
      cs_extends sa sb /\ cs_extends sb sf /\
      fn_has_code sa sb func /\ fn_has_code sb sf func
Proof
  rpt gen_tac >> strip_tac >>
  `~has_length_word (expr_type e)` by
    metis_tac[is_word_type_no_length_word] >>
  drule_all compile_get_target_ptr_toplevel >> strip_tac >>
  `?st2 src_vv sb op.
     compile_expr cenv (expr_type e) e sa = (src_vv, st2) /\
     unwrap_value cenv src_vv st2 = (op, sb) /\
     emit_void (if tr then TSTORE else SSTORE) [Lit slot; op] sb = ((), sf) /\
     c = cenv` by
    (drule stmt_env_assign >> strip_tac >>
     qpat_x_assum `c = cenv` SUBST_ALL_TAC >>
     qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
     asm_simp_tac (srw_ss())
       [compile_stmt_def, compile_assign_value_def, comp_bind_def,
        comp_ignore_bind_def, comp_return_def, LET_THM] >>
     Cases_on `compile_expr cenv (expr_type e) e sa` >>
     rename1 `compile_expr _ _ _ _ = (src_vv, st2)` >>
     Cases_on `unwrap_value cenv src_vv st2` >>
     rename1 `unwrap_value _ _ _ = (op, sb)` >>
     Cases_on `tr` >> simp[]
     >- (Cases_on `emit_void TSTORE [Lit slot; op] sb` >>
         rename1 `emit_void _ _ _ = (u, sc)` >> Cases_on `u` >>
         simp[] >> strip_tac >> gvs[comp_bind_def, comp_return_def]) >>
     Cases_on `emit_void SSTORE [Lit slot; op] sb` >>
     rename1 `emit_void _ _ _ = (u, sc)` >> Cases_on `u` >>
     simp[] >> strip_tac >> gvs[comp_bind_def, comp_return_def]) >>
  `lower_value compile_expr cenv (expr_type e) e sa = (op, sb)` by
    simp[lower_value_def, comp_bind_def] >>
  `cs_extends sa sb` by
    metis_tac[cj 2 exprLoweringPropsTheory.compile_expr_grows] >>
  `cs_extends sb sf` by metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa sb func /\ fn_has_code sb sf func` by
    metis_tac[fn_has_code_split] >>
  metis_tac[]
QED

(* The SSTORE or TSTORE of w at slot, run: it reaches its end, related at
   es' when the store is, with every variable and allocation kept. *)
Theorem assign_storage_store_run:
  !ctx func cenv cx es' s tr slot op w st st'.
    emit_void (if tr then TSTORE else SSTORE) [Lit slot; op] st = ((), st') /\
    fn_has_code st st' func /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    eval_operand op s = SOME w /\
    stmt_state_rel ctx func cenv cx es'
      (if tr then tstore slot w s else sstore slot w s) ==>
    ?t. stmt_state_rel ctx func cenv cx es' t /\
        ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
        t.vs_inst_idx = LENGTH st'.cs_current_insts /\
        (!x. lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s = r
Proof
  rpt strip_tac >>
  `eval_operand (Lit slot) s = SOME slot` by simp[eval_operand_def] >>
  drule_all storage_emit_frame_run >> metis_tac[]
QED

(* As an action, self.x = e is e's forced value written at x's slot:
   looking x up reads only cx. *)
Theorem eval_assign_toplevel_action:
  !cx src id e ts tr typ id_str slot tvt.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) typ = SOME tvt ==>
    eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src, id))) e) =
    bind (bind (eval_expr cx e) (read_result cx))
      (write_storage_slot cx tr (n2w slot) tvt)
Proof
  rpt gen_tac >> strip_tac >> simp[FUN_EQ_THM] >> gen_tac >>
  simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e x` >> rename1 `eval_expr cx e x = (r1, es1)` >>
  Cases_on `r1` >> simp[] >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, lookup_global_def, bind_def,
       lift_option_type_def, return_def, LET_THM, get_place_def] >>
  Cases_on `read_result cx x' es1` >>
  rename1 `read_result cx _ es1 = (r2, es2)` >>
  Cases_on `r2` >> simp[write_place_def]
QED

(* A storage write reads no gas. *)
Theorem write_storage_slot_gas_obs:
  !cx tr slot tv v es g.
    write_storage_slot cx tr slot tv v (es with gas_obs := g) =
    (FST (write_storage_slot cx tr slot tv v es),
     SND (write_storage_slot cx tr slot tv v es) with gas_obs := g)
Proof
  rpt gen_tac >> simp[write_storage_slot_eq] >>
  Cases_on `cx.txn.is_static` >> Cases_on `encode_value tv v` >>
  Cases_on `tr` >> simp[set_storage_def, get_storage_def]
QED

(* The SSTORE or TSTORE of e's word at x's slot reads no gas. *)
Theorem assign_storage_store_path:
  !ctx func s tr slot op w st st'.
    emit_void (if tr then TSTORE else SSTORE) [Lit slot; op] st = ((), st') /\
    fn_has_code st st' func /\ ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    eval_operand op s = SOME w ==>
    gas_marked_path F ctx func s 0
      (OK ((if tr then tstore slot w s else sstore slot w s)
             with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt strip_tac >> irule emit_inst_zero_marked_path >> simp[] >>
  qexistsl_tac [`[Lit slot; op]`, `if tr then TSTORE else SSTORE`, `[]`,
                `st`, `st'`] >>
  Cases_on `tr` >> gvs[emit_void_def, emit_inst_def, is_terminator_def] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  fs[mk_inst_def, exec_write2_def, eval_operand_def]
QED

(* From e's post at a value whose word is x's encoding of it: the write
   at x's slot and the store keep stmt_state_rel, and land past the
   store. *)
Theorem assign_storage_word_suffix:
  !ctx func cx lctx cenv e es ee v op t sa sb sf s0 src id ts tr typ id_str
   slot tvt etv.
    expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
    stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
    MAP FDOM ee.scopes = MAP FDOM es.scopes /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) typ = SOME tvt /\ type_slot_size tvt = 1 /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    is_word_type (expr_type e) /\
    encode_value tvt v = SOME [(0, typed_val_to_w256 etv v)] /\
    emit_void (if tr then TSTORE else SSTORE) [Lit (n2w slot); op] sb =
      ((), sf) /\
    fn_has_code sb sf func /\ ~t.vs_halted /\ ee.gas_obs = [] ==>
    ?ee' r.
      (!tail. write_storage_slot cx tr (n2w slot) tvt v
                (ee with gas_obs := tail) = (INL (), ee' with gas_obs := tail)) /\
      gas_marked_path F ctx func t 0 r /\
      ?t'. r = OK t' /\
           stmt_post ctx func cx lctx cenv cenv sa sf es s0 (INL ())
             (ee' with gas_obs := []) t'
Proof
  rpt gen_tac >> strip_tac >>
  drule_all expr_post_alloca_frame >> strip_tac >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `eval_operand op t = SOME (typed_val_to_w256 etv v)` by
    (gvs[expr_val_rel_def] >> metis_tac[]) >>
  `declared_storage_region cx src id [] = SOME (tr, n2w slot, tvt)` by
    simp[vyperStorageLayoutSafetyTheory.declared_storage_region_def] >>
  drule_all storage_dead_update_word_region >> strip_tac >>
  Cases_on `write_storage_slot cx tr (n2w slot) tvt v ee` >>
  rename1 `_ = (res, ee')` >>
  `~t.vs_call_ctx.cc_static /\ ~cx.txn.is_static` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule_all stmt_state_rel_write_storage_word >> strip_tac >> gvs[] >>
  drule_all assign_storage_store_path >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `ee'.gas_obs = [] /\ ee'.scopes = ee.scopes` by
    (qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >>
     simp[write_storage_slot_eq] >> Cases_on `tr` >>
     simp[set_storage_def] >> strip_tac >> gvs[]) >>
  `ee' with gas_obs := [] = ee'` by
    simp[evaluation_state_component_equality] >>
  `alloca_frame cenv es sa s0 cenv ee'
     ((if tr then tstore (n2w slot) (typed_val_to_w256 etv v) t
       else sstore (n2w slot) (typed_val_to_w256 etv v) t)
      with vs_inst_idx := SUC t.vs_inst_idx)` by
    (irule alloca_frame_same_state >> qexists_tac `t` >>
     Cases_on `tr` >> simp[sstore_def, tstore_def, LET_THM] >>
     qpat_x_assum `alloca_frame _ _ _ _ _ ee t` mp_tac >>
     simp[alloca_frame_def]) >>
  qexistsl_tac [`ee'`,
    `OK ((if tr then tstore (n2w slot) (typed_val_to_w256 etv v) t
          else sstore (n2w slot) (typed_val_to_w256 etv v) t)
         with vs_inst_idx := SUC t.vs_inst_idx)`] >>
  conj_tac >- fs[write_storage_slot_gas_obs] >>
  `sf.cs_current_bb = sb.cs_current_bb /\
   LENGTH sf.cs_current_insts = SUC (LENGTH sb.cs_current_insts)` by
    (Cases_on `tr` >>
     gvs[emit_void_def, comp_bind_def, fresh_id_def,
         comp_ignore_bind_def, comp_return_def, emit_def]) >>
  `~block_is_terminated sf` by
    (Cases_on `tr` >> gvs[] >> drule emit_void_nonterminator_open >>
     simp[is_terminator_def]) >>
  simp[stmt_post_def, stmt_lands_def, cenv_top_ext_refl,
       stmt_state_rel_inst_idx] >>
  Cases_on `tr` >>
  gvs[sstore_def, tstore_def, lookup_var_def, LET_THM]
QED

(* self.x = e for a storage or transient variable x the lowering holds in
   one word (is_word_type vtyp) and e of a word type, for every outcome:
   e's errors exit, and on a value its word is stored at x's slot.  x's
   declared type tvt is constrained only by the encoding premise: e's word
   is how tvt encodes e's value, at whatever readings e runs on.
   compile_assign_storage_typed_stmt_frag discharges it when e has x's
   declared type. *)
Theorem compile_assign_storage_stmt_frag:
  !ctx func cx lctx RetQ cenv ty src id e es ts tr typ id_str slot
   tvt vtyp etv.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) typ = SOME tvt /\ type_slot_size tvt = 1 /\
    cenv.ce_hashmap_info (src, id) = NONE /\
    cenv.ce_module_var_type (src, id) = SOME vtyp /\
    is_word_type vtyp /\ is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    (!gs v es1.
       (do result <- eval_expr cx e; read_result cx result od)
         (es with gas_obs := gs) = (INL v, es1) ==>
       encode_value tvt v = SOME [(0, typed_val_to_w256 etv v)]) /\
    expr_sim ctx func cenv cx (expr_type e) e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assign (BaseTarget (TopLevelNameTarget (src, id))) e))
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src, id))) e))
      es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  `FLOOKUP cenv.ce_module_vars (src, id) =
     SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))` by
    (irule toplevel_storage_ce_vars >>
     gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  drule_all assign_storage_word_code_parts >> strip_tac >>
  rename1 `lower_value _ _ _ _ sa = (op, sB)` >> gvs[] >>
  drule_all eval_assign_toplevel_action >>
  disch_then (qspec_then `e` assume_tac) >>
  irule forced_then_stmt_outcome >>
  qexistsl_tac [
    `\v ee t. expr_post ctx func cenv cx e es sa sB s0 ee v op t /\
              t.vs_current_bb = sB.cs_current_bb /\
              t.vs_inst_idx = LENGTH sB.cs_current_insts`,
    `e`, `write_storage_slot cx tr (n2w slot) tvt`] >>
  reverse conj_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      qpat_x_assum `expr_sim _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_sim_def]) >>
      disch_then (qspecl_then [`sa`, `sB`, `op`, `s0`] mp_tac) >>
      impl_tac >- (fs[] >> metis_tac[forced_then_admissible]) >>
      simp[]) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  `encode_value tvt v = SOME [(0, typed_val_to_w256 etv v)]` by
    (qpat_x_assum `!gs v es1. _ ==> encode_value _ _ = _` irule >>
     fs[ETA_THM] >> metis_tac[]) >>
  `MAP FDOM ee.scopes = MAP FDOM es.scopes` by
    (qpat_x_assum `_ (es with gas_obs := gs) = (INL v, ee)`
       (mp_tac o MATCH_MP stmtSimDefsTheory.eval_read_preserves_scopes_dom) >>
     simp[]) >>
  drule_all assign_storage_word_suffix >>
  disch_then (qspec_then `lctx` strip_assume_tac) >>
  qexistsl_tac [`INL ()`, `ee'`, `r`] >> simp[]
QED

(* self.x = e when e has x's declared word type typ and its values are of
   that type: the encoding premise is encode_value_word_typed. *)
Theorem compile_assign_storage_typed_stmt_frag:
  !ctx func cx lctx RetQ cenv ty src id e es ts tr typ id_str slot
   tvt vtyp.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    expr_type e = typ /\ is_word_type typ /\
    evaluate_type (get_tenv cx) typ = SOME tvt /\
    cenv.ce_hashmap_info (src, id) = NONE /\
    cenv.ce_module_var_type (src, id) = SOME vtyp /\
    is_word_type vtyp /\
    (!gs v es1.
       (do result <- eval_expr cx e; read_result cx result od)
         (es with gas_obs := gs) = (INL v, es1) ==>
       value_has_type tvt v) /\
    expr_sim ctx func cenv cx (expr_type e) e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assign (BaseTarget (TopLevelNameTarget (src, id))) e))
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src, id))) e))
      es
Proof
  rpt strip_tac >>
  `!gs v es1.
     (do result <- eval_expr cx e; read_result cx result od)
       (es with gas_obs := gs) = (INL v, es1) ==>
     encode_value tvt v = SOME [(0, typed_val_to_w256 tvt v)]` by
    (rpt strip_tac >> irule encode_value_word_typed >> metis_tac[]) >>
  drule_all exprSimUnwrapTheory.word_type_slot_size >> strip_tac >>
  gvs[] >> drule_all compile_assign_storage_stmt_frag >> simp[]
QED
