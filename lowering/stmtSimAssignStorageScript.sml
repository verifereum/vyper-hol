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
  stmtSimAssign stmtSimAssignMem accountsRelProps
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding valueEncodingProofs
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
  cheat
QED

(* A value of a word type encodes, in one slot, as the word typed_val_to_w256
   gives it. *)
Theorem encode_value_word_typed:
  !tenv t tv v.
    is_word_type t /\ evaluate_type tenv t = SOME tv /\
    value_has_type tv v ==>
    encode_value tv v = SOME [(0, typed_val_to_w256 tv v)]
Proof
  cheat
QED

Theorem local_ptrs_rel_storage_fields[local]:
  !func cenv sc s a t.
    local_ptrs_rel func cenv sc (s with <|vs_accounts := a|>) =
      local_ptrs_rel func cenv sc s /\
    local_ptrs_rel func cenv sc (s with <|vs_transient := t|>) =
      local_ptrs_rel func cenv sc s
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
QED

(* A storage write reads no gas. *)
Theorem write_storage_slot_gas_obs:
  !cx tr slot tv v es g.
    write_storage_slot cx tr slot tv v (es with gas_obs := g) =
    (FST (write_storage_slot cx tr slot tv v es),
     SND (write_storage_slot cx tr slot tv v es) with gas_obs := g)
Proof
  cheat
QED

(* The SSTORE or TSTORE of e's word at x's slot reads no gas. *)
Theorem assign_storage_store_path:
  !ctx func s tr slot op w st st'.
    emit_void (if tr then TSTORE else SSTORE) [Lit slot; op] st = ((), st') /\
    fn_has_code st st' func /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    eval_operand op s = SOME w ==>
    gas_marked_path F ctx func s 0
      (OK ((if tr then tstore slot w s else sstore slot w s)
             with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  cheat
QED

(* From e's post at a value whose word is x's encoding of it: the write
   at x's slot and the store keep stmt_state_rel, and land past the
   store. *)
Theorem assign_storage_word_suffix:
  !ctx func cx lctx cenv e es ee v op t sa sb sf s0 src id ts tr typ id_str
   slot tvt etv.
    expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
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
           stmt_post ctx func cx lctx cenv cenv sa sf s0 (INL ())
             (ee' with gas_obs := []) t'
Proof
  cheat
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
  cheat
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
  cheat
QED
