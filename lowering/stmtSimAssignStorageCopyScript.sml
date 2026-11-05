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
  valueEncodingProps
  stmtSimProps
  exprSimProps
  stmtSimDefs
  exprSimDefs
  loweringPosts
  list rich_list finite_map pred_set
  fragExec  exprSimLeaves exprSimOps  stmtSimAssign stmtSimAssignMem
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
    ~cx.txn.is_static /\ value_has_type tvt v ==>
    ?writes.
      encode_value tvt v = SOME writes /\
      write_storage_slot cx tr slot tvt v es =
        (INL (), set_storage cx es tr
          (apply_writes slot writes (get_storage cx es tr)))
Proof
  cheat
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
  cheat
QED

Theorem storage_copy_no_dyn_info[local]:
  (!elem n. typ <> ArrayT elem (Dynamic n)) ==>
  (case typ of ArrayT elem (Dynamic n) => SOME (f elem) | _ => NONE) = NONE
Proof
  cheat
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
  cheat
QED

(* Once source layout compatibility is known, only the size dispatch
   remains. No dynamic-array path or normalization can be selected. *)
Theorem assign_storage_copy_suffix[local]:
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
  cheat
QED

Theorem storage_copy_loop_open[local]:
  !src dst n loc ctor sa u sb.
    compile_word_copy_loop src dst n LocMemory loc ctor sa = (u,sb) ==>
    ~block_is_terminated sb
Proof
  cheat
QED

Theorem assign_storage_copy_suffix_open[local]:
  !cenv dst src tr loc typ src_ty mem_size sa sb.
    compile_assign_value cenv dst (if tr then LocTransient else LocStorage)
      src F loc typ src_ty NONE mem_size sa = ((),sb) /\
    ~is_word_type typ /\
    typ = src_ty /\ type_memory_bytes cenv typ = mem_size ==>
    ~block_is_terminated sb
Proof
  cheat
QED

Theorem storage_copy_dyn_live_word[local]:
  !st base cap len i b.
    w2n (lookup_storage (n2w base) st) = len /\
    i < 1 + word_size cap /\ b < 32 /\
    ~dyn_bytes_dead st base cap (base + i) b ==>
    32 * i < 32 + len
Proof
  cheat
QED

Theorem storage_copy_word_address[local]:
  !w:bytes32 i len.
    w2n w + len < dimword (:256) /\ 32 * i < len ==>
    w2n (w + n2w i * 32w) = w2n w + 32 * i
Proof
  cheat
QED

Theorem storage_copy_length_type[local]:
  !typ.
    has_length_word typ /\ (!elem n. typ <> ArrayT elem (Dynamic n)) ==>
    (?n. typ = BaseT (BytesT (Dynamic n))) \/
    (?n. typ = BaseT (StringT n))
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
QED

Theorem storage_copy_dyn_head[local]:
  !tv v cap bs writes k st.
    encode_value tv v = encode_dyn_bytes_slots cap bs /\
    encode_value tv v = SOME writes /\ value_has_type tv v /\
    k + type_slot_size tv <= dimword (:256) /\
    k < dimword (:256) /\ LENGTH bs < dimword (:256) ==>
    w2n (lookup_storage (n2w k) (apply_writes (n2w k) writes st)) = LENGTH bs
Proof
  cheat
QED

Theorem storage_copy_dyn_footprint[local]:
  !tv v cap bs writes k st i b.
    encode_value tv v = encode_dyn_bytes_slots cap bs /\
    value_has_type tv v /\ encode_value tv v = SOME writes /\
    k + type_slot_size tv <= dimword (:256) /\
    k < dimword (:256) /\ LENGTH bs < dimword (:256) /\
    i < 1 + word_size cap /\ b < 32 /\
    ~dyn_bytes_dead (apply_writes (n2w k) writes st) k cap (k+i) b ==>
    32*i < 32 + LENGTH bs
Proof
  cheat
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
  cheat
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
  cheat
QED

Theorem storage_copy_capacity_bound[local]:
  !n. n < dimword (:256) ==> 1 + word_size n < dimword (:256)
Proof
  cheat
QED

Theorem storage_copy_count_bound[local]:
  !tv v.
    well_formed_type_value tv /\ val_footprint tv v < dimword (:256) ==>
    type_slot_size tv < dimword (:256)
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
QED

Theorem storage_copy_initial_agree[local]:
  !ctx func cenv cx es s tr.
    stmt_state_rel ctx func cenv cx es s ==>
    storage_agree (storage_dead cx tr (get_storage cx es tr))
      (get_storage cx es tr)
      (if tr then contract_transient s else contract_storage s)
Proof
  cheat
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
  cheat
QED

Theorem storage_copy_state_zero[local]:
  !ctx func cenv cx es s tr k.
    stmt_state_rel ctx func cenv cx es s ==>
    stmt_state_rel ctx func cenv cx
      (set_storage cx es tr (update_storage k 0w (get_storage cx es tr)))
      ((if tr then tstore else sstore) k 0w s)
Proof
  cheat
QED

Theorem storage_copy_control_frame[local]:
  !ctx func cenv cx es s V bb ix prev.
    stmt_state_rel ctx func cenv cx es
      (s with <|vs_vars := V; vs_current_bb := bb;
                vs_inst_idx := ix; vs_prev_bb := prev|>) =
    stmt_state_rel ctx func cenv cx es (s with vs_vars := V)
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
QED

Theorem storage_copy_suffix_run[local]:
  !ctx func cenv cx es' tr src k n typ src_ty loc sa sb s b.
    compile_assign_value cenv (Lit k)
      (if tr then LocTransient else LocStorage) src F loc
      typ src_ty NONE (32 * n) sa = ((),sb) /\
    ~is_word_type typ /\
    typ = src_ty /\ type_memory_bytes cenv typ = 32 * n /\
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
  cheat
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
  cheat
QED

Theorem storage_copy_success_run[local]:
  !ctx func cenv cx e es es1 es' v tv tr mid id slot sa sm sf op loc s0.
    (do result <- eval_expr cx e; read_result cx result od) es = (INL v,es1) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    ~is_word_type (expr_type e) /\ value_has_type tv v /\
    lowered_value_type cenv e = expr_type e /\
    type_memory_bytes cenv (expr_type e) = type_memory_size tv /\
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
      (expr_type e) (expr_type e) NONE (type_memory_size tv) sm = ((),sf) /\
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
  cheat
QED

Theorem assign_storage_empty_stmt_frag[local]:
  !ctx func cx lctx RetQ cenv ty src id e es ts tr typ id_str slot tvt.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    has_length_word (expr_type e) /\ is_empty_value_expr e /\
    expr_type e = typ /\ (!elem n. typ <> ArrayT elem (Dynamic n)) /\
    (!ann t args. e = TypeBuiltin ann Empty t args ==> t = typ) /\
    evaluate_type (get_tenv cx) typ = SOME tvt /\
    cenv.ce_hashmap_info (src,id) = NONE /\
    (!gs v st. (do result <- eval_expr cx e; read_result cx result od)
       (es with gas_obs := gs) = (INL v,st) ==> value_has_type tvt v) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
        (Assign (BaseTarget (TopLevelNameTarget (src,id))) e))
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src,id))) e)) es
Proof
  cheat
QED

(* self.x = e for a storage or transient variable x whose declared type typ
   is not held in one word and is not a DynArray, with e of type typ.  The
   premises on x's region are what storage_layout_safe gives: it fits the
   slot space and is apart from every other declared region.  An empty(t)
   right-hand side has t = typ, as type_builtin_result_ok requires; the
   lowering stores only a zero length word for it. *)
Theorem compile_assign_storage_copy_stmt_frag:
  !ctx func cx lctx RetQ cenv ty src id e es ts tr typ id_str slot
   tvt.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    expr_type e = typ /\ lowered_value_type cenv e = expr_type e /\
    ~is_word_type typ /\
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
