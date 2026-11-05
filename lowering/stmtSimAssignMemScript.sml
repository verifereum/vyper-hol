(*
 * Statement simulation: Assign to a memory-backed local (#637)
 *
 * x = e for a local x already in scope whose type is not a word type (an
 * aggregate, a bytestring).  compile_assign_value copies e's bytes into
 * x's region, staged through a buffer of its own when e's value is in
 * memory (so x = x and values that overlap x copy correctly), as for a
 * declaration (stmtSimDeclMem).  When e is the empty value of a type with
 * a length word, the lowering only zeroes x's length word.
 *
 * TOP-LEVEL:
 *   stmt_env_assign                        — Assign declares nothing
 *   local_memory_store_run                 — compile_store_memory into a
 *                                            live local
 *   compile_assign_local_memory_stmt_frag  — x = e for a memory-backed
 *                                            local x, e lowered at x's
 *                                            type, every outcome
 *   compile_assign_local_memory_widen_stmt_frag — the same where x and e
 *                                            are bytestrings and e's
 *                                            bound may be narrower
 *   compile_assign_local_empty_stmt_frag   — x = e for e the empty value
 *                                            of a type with a length word
 *)

Theory stmtSimAssignMem
Ancestors
  stmtSimProps
  exprSimProps
  stmtSimDefs
  exprSimDefs
  loweringPosts
  list rich_list finite_map pred_set
  fragExec localPtrsProps  loweringSlice  stmtSimDeclStore
  stmtSimDecl stmtSimDeclMem stmtSimAssignStore stmtSimAssign
  valueCopy valueCopySource valueCopyBytes exprOperandVar freshWrites
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding
  vyperInterpreter vyperState vyperValue vyperLookup vyperExprNoControl
  venomExecSemantics venomExecProofs venomInst venomState
Libs
  monadsyntax

Theorem stmt_env_assign:
  !cenv lctx ty g e sa c sf.
    stmt_env cenv lctx ty (Assign g e) sa = (c, sf) ==>
    c = cenv /\ compile_stmt cenv lctx ty (Assign g e) sa = ((), sf)
Proof
  cheat
QED

(* The code of x = e for a memory-backed local x: e's value, then
   compile_assign_value into x's pointer at x's type. *)
Theorem assign_local_memory_code_parts:
  !cenv lctx ty id e sa sf c func p sz vtyp.
    stmt_env cenv lctx ty (Assign (BaseTarget (NameTarget id)) e) sa =
      (c, sf) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME vtyp /\ ~is_word_type vtyp /\
    ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    lowered_value_type cenv e = vtyp /\ fn_has_code sa sf func ==>
    c = cenv /\
    ?vv sV sB op.
      compile_expr cenv (expr_type e) e sa = (vv, sV) /\
      unwrap_value cenv vv sV = (op, sB) /\
      lower_value compile_expr cenv (expr_type e) e sa = (op, sB) /\
      compile_assign_value cenv (Var p) LocMemory op F (vv_location vv)
        vtyp vtyp
        (case vtyp of ArrayT elem_ty (Dynamic _) =>
           SOME ((type_memory_bytes cenv elem_ty + 31) DIV 32,
                 type_memory_bytes cenv elem_ty) | _ => NONE)
        (type_memory_bytes cenv vtyp) sB = ((), sf) /\
      cs_extends sa sB /\ cs_extends sB sf /\
      fn_has_code sa sB func /\ fn_has_code sB sf func
Proof
  cheat
QED

(* A write within a live local is disjoint from initialized immutables. *)
Theorem local_copy_immutables[local]:
  stmt_state_rel ctx func cenv cx es s /\
  local_region cenv es.scopes s id b sz /\ n <= sz /\
  t.vs_data_section = s.vs_data_section /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (!a len. a + len <= b \/ b + n <= a ==>
     mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) ==>
  immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t
Proof
  cheat
QED

(* compile_store_memory at ty of a value of the local's type, held in
   memory at src, into a live local: it reaches its end related at the
   scopes write_place leaves. *)
Theorem local_memory_store_run_framed:
  !ctx func cenv cx es s id p sz pre env entry rest v src ty sa sb sw tyv sty stv.
    compile_store_memory cenv src (Var p) ty sty sa = ((), sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\
    ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tyv /\
    entry.type = tyv /\ value_has_type tyv v /\ val_wf tyv v /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
    (ty = sty \/ is_bytestring_type ty /\ is_bytestring_type sty) /\
    type_memory_bytes cenv ty = type_memory_size tyv /\
    type_memory_size tyv + 64 < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?dw t. lookup_var p s = SOME dw /\
        stmt_state_rel ctx func cenv cx
          (es with scopes :=
             pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) ::
             rest) t /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        (!a len. a + len <= w2n dw \/
           w2n dw + MIN (type_memory_size stv) (type_memory_size tyv) <= a ==>
           mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s = r
Proof
  cheat
QED

Theorem local_memory_store_run:
  !ctx func cenv cx es s id p sz pre env entry rest v src ty sa sb sw tyv.
    compile_store_memory cenv src (Var p) ty ty sa = ((), sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\
    ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tyv /\
    entry.type = tyv /\ value_has_type tyv v /\ val_wf tyv v /\
    val_in_memory tyv v (w2n sw) s.vs_memory /\
    type_memory_bytes cenv ty = type_memory_size tyv /\
    type_memory_size tyv + 64 < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. stmt_state_rel ctx func cenv cx
          (es with scopes :=
             pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) ::
             rest) t /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s = r
Proof
  cheat
QED

(* compile_assign_value at the local's memory type: staged through a fresh
   buffer when the source is in memory, then compile_store_memory. *)
Theorem local_memory_assign_run:
  !ctx func cenv cx es s id p sz pre env entry rest v src ty sa sb sw tyv
   loc info bytes.
    compile_assign_value cenv (Var p) LocMemory src F loc ty ty info bytes sa =
      ((), sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\
    ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tyv /\
    entry.type = tyv /\ value_has_type tyv v /\ val_wf tyv v /\
    val_in_memory tyv v (w2n sw) s.vs_memory /\
    type_memory_bytes cenv ty = type_memory_size tyv /\
    0 < type_memory_size tyv /\ type_memory_size tyv + 64 < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. stmt_state_rel ctx func cenv cx
          (es with scopes :=
             pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) ::
             rest) t /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s = r
Proof
  cheat
QED

(* On a value: e's fragment ends in expr_post with the value in memory at
   its operand, and the assignment writes it into x. *)
Theorem assign_local_memory_success_run:
  !ctx func cenv cx id e es es' tyv sa sb sf op p sz s0 loc info bytes.
    eval_stmt cx (Assign (BaseTarget (NameTarget id)) e) es = (INL (), es') /\
    ~is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
    (!v es1 entry.
       (do result <- eval_expr cx e; read_result cx result od) es =
         (INL v, es1) /\
       lookup_scopes id es1.scopes = SOME entry ==>
       entry.type = tyv /\ value_has_type tyv v) /\
    expr_sim ctx func cenv cx (expr_type e) e es /\
    lower_value compile_expr cenv (expr_type e) e sa = (op, sb) /\
    compile_assign_value cenv (Var p) LocMemory op F loc
      (expr_type e) (expr_type e) info bytes sb = ((), sf) /\
    fn_has_code sa sb func /\ fn_has_code sb sf func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    type_memory_bytes cenv (expr_type e) = type_memory_size tyv /\
    0 < type_memory_size tyv /\ type_memory_size tyv + 64 < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
        t.vs_current_bb = sf.cs_current_bb /\
        t.vs_inst_idx = LENGTH sf.cs_current_insts /\
        (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
               lookup_var x t = SOME u) /\
        (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s0 = r
Proof
  cheat
QED

(* x = e for a local x whose type T is not a word type, where e has type T,
   is lowered at T (lowered_value_type, so not a bytestring literal of
   another length) and is not the empty-value form the lowering stores as
   a zero length word, and e's value has the type of x's scope entry.  The
   size conditions are compile_annassign_memory_stmt_frag's: T's buffer is
   type_memory_bytes of T, the size val_in_memory lays a value of T out
   in, not 0, and 64 bytes below 2 ** 256.  expr_type e = T leaves out
   assignments that widen e's value to T. *)
Theorem compile_assign_local_memory_stmt_frag:
  !ctx func cx lctx RetQ cenv ty id e es p sz vtyp tyv.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME vtyp /\ ~is_word_type vtyp /\
    ~(has_length_word vtyp /\ is_empty_value_expr e) /\
    expr_type e = vtyp /\ lowered_value_type cenv e = vtyp /\
    evaluate_type (get_tenv cx) vtyp = SOME tyv /\
    type_memory_bytes cenv vtyp = type_memory_size tyv /\
    0 < type_memory_size tyv /\ type_memory_size tyv + 64 < dimword (:256) /\
    (!gs v es1 entry.
       (do result <- eval_expr cx e; read_result cx result od)
         (es with gas_obs := gs) = (INL v, es1) /\
       lookup_scopes id es1.scopes = SOME entry ==>
       entry.type = tyv /\ value_has_type tyv v) /\
    expr_sim ctx func cenv cx (expr_type e) e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assign (BaseTarget (NameTarget id)) e))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  cheat
QED

Theorem assign_local_memory_widen_code_parts:
  !cenv lctx ty id e sa sf c func p sz vtyp.
    stmt_env cenv lctx ty (Assign (BaseTarget (NameTarget id)) e) sa = (c, sf) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME vtyp /\ ~is_word_type vtyp /\
    ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    (lowered_value_type cenv e = vtyp \/ is_bytestring_type vtyp) /\
    fn_has_code sa sf func ==>
    c = cenv /\
    ?vv sV sB op.
      compile_expr cenv (expr_type e) e sa = (vv, sV) /\
      unwrap_value cenv vv sV = (op, sB) /\
      lower_value compile_expr cenv (expr_type e) e sa = (op, sB) /\
      compile_assign_value cenv (Var p) LocMemory op F (vv_location vv)
        vtyp (lowered_value_type cenv e)
        (case vtyp of ArrayT elem_ty (Dynamic _) =>
           SOME ((type_memory_bytes cenv elem_ty + 31) DIV 32,
                 type_memory_bytes cenv elem_ty) | _ => NONE)
        (type_memory_bytes cenv vtyp) sB = ((), sf) /\
      cs_extends sa sB /\ cs_extends sB sf /\
      fn_has_code sa sB func /\ fn_has_code sB sf func
Proof
  cheat
QED

Theorem local_memory_assign_widen_run:
  !ctx func cenv cx es s id p sz pre env entry rest v src ty sty sa sb sw tyv
   loc info bytes.
    compile_assign_value cenv (Var p) LocMemory src F loc ty sty info bytes sa = ((), sb) /\
    (sty = ty \/ is_bytestring_type ty) /\
    0 < type_memory_bytes cenv sty /\ type_memory_bytes cenv sty < dimword (:256) /\
    val_footprint tyv v <= type_memory_bytes cenv sty /\
    (!x. src = Var x ==> not_fresh_at sa x) /\ eval_operand src s = SOME sw /\
    ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tyv /\
    entry.type = tyv /\ value_has_type tyv v /\ val_wf tyv v /\
    val_in_memory tyv v (w2n sw) s.vs_memory /\
    type_memory_bytes cenv ty = type_memory_size tyv /\
    0 < type_memory_size tyv /\ type_memory_size tyv + 64 < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. stmt_state_rel ctx func cenv cx
          (es with scopes :=
             pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s = r
Proof
  cheat
QED



Theorem assign_local_memory_widen_success_run:
  !ctx func cenv cx id e es es' vtyp sty etv tyv sa sb sf op p sz s0 loc info bytes.
    eval_stmt cx (Assign (BaseTarget (NameTarget id)) e) es = (INL (), es') /\
    ~is_word_type vtyp /\
    (expr_type e = vtyp \/ is_bytestring_type vtyp /\ is_bytestring_type (expr_type e)) /\
    (sty = vtyp \/ is_bytestring_type vtyp) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    evaluate_type (get_tenv cx) vtyp = SOME tyv /\
    (!v es1 entry.
       (do result <- eval_expr cx e; read_result cx result od) es = (INL v, es1) /\
       lookup_scopes id es1.scopes = SOME entry ==>
       entry.type = tyv /\ value_has_type tyv v /\
       val_footprint tyv v <= type_memory_bytes cenv sty) /\
    0 < type_memory_bytes cenv sty /\ type_memory_bytes cenv sty < dimword (:256) /\
    expr_sim ctx func cenv cx (expr_type e) e es /\
    lower_value compile_expr cenv (expr_type e) e sa = (op, sb) /\
    compile_assign_value cenv (Var p) LocMemory op F loc vtyp sty info bytes sb = ((), sf) /\
    fn_has_code sa sb func /\ fn_has_code sb sf func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    type_memory_bytes cenv vtyp = type_memory_size tyv /\
    0 < type_memory_size tyv /\ type_memory_size tyv + 64 < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
        t.vs_current_bb = sf.cs_current_bb /\ t.vs_inst_idx = LENGTH sf.cs_current_insts /\
        (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==> lookup_var x t = SOME u) /\
        (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s0 = r
Proof
  cheat
QED

Theorem compile_assign_local_memory_widen_stmt_frag:
  !ctx func cx lctx RetQ cenv ty id e es res es' p sz vtyp etv tyv.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME vtyp /\ ~is_word_type vtyp /\
    ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    (expr_type e = vtyp \/ is_bytestring_type vtyp /\ is_bytestring_type (expr_type e)) /\
    (lowered_value_type cenv e = vtyp \/ is_bytestring_type vtyp) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    evaluate_type (get_tenv cx) vtyp = SOME tyv /\
    type_memory_bytes cenv vtyp = type_memory_size tyv /\
    0 < type_memory_size tyv /\ type_memory_size tyv + 64 < dimword (:256) /\
    0 < type_memory_bytes cenv (lowered_value_type cenv e) /\
    type_memory_bytes cenv (lowered_value_type cenv e) < dimword (:256) /\
    (!v es1 entry.
       (do result <- eval_expr cx e; read_result cx result od) es = (INL v, es1) /\
       lookup_scopes id es1.scopes = SOME entry ==>
       entry.type = tyv /\ value_has_type tyv v /\
       val_footprint tyv v <= type_memory_bytes cenv (lowered_value_type cenv e)) /\
    expr_sim ctx func cenv cx (expr_type e) e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assign (BaseTarget (NameTarget id)) e))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  cheat
QED

(* A header-sized write into a live local: the value representation may
   occupy a larger buffer, but only the header needs to be overwritten. *)
Theorem local_header_store_state:
  !func cenv cx es s id p sz w pre env entry rest v wd.
    stmt_state_rel ctx func cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\ 32 <= type_memory_size entry.type /\
    val_wf entry.type v /\
    val_in_memory entry.type v (w2n w) (mstore (w2n w) wd s).vs_memory ==>
    stmt_state_rel ctx func cenv cx
      (es with scopes := pre ++
        (env |+ (id, entry with <|value := v; popped := []|>)) :: rest)
      (mstore (w2n w) wd s)
Proof
  cheat
QED

Theorem assign_local_empty_code_parts:
  !cenv lctx ty id e sa sf c p sz.
    stmt_env cenv lctx ty (Assign (BaseTarget (NameTarget id)) e) sa = (c, sf) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    has_length_word (expr_type e) /\ is_empty_value_expr e ==>
    c = cenv /\ emit_void MSTORE [Var p; Lit 0w] sa = ((), sf)
Proof
  cheat
QED

Theorem local_header_store_frag:
  !ctx func cenv cx es s id p sz w pre env entry rest v wd sa sb R.
    emit_void MSTORE [Var p; Lit wd] sa = ((), sb) /\
    stmt_state_rel ctx func cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\ 32 <= type_memory_size entry.type /\
    val_wf entry.type v /\
    val_in_memory entry.type v (w2n w) (mstore (w2n w) wd s).vs_memory ==>
    frag_exec ctx sa sb (\t. t = s)
      (\t. stmt_state_rel ctx func cenv cx
         (es with scopes := pre ++
           (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t /\
         (!x. lookup_var x t = lookup_var x s) /\
         (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                  FLOOKUP t.vs_allocas aid = SOME b)) R
Proof
  cheat
QED

Theorem compile_assign_local_empty_stmt_frag:
  !ctx func cx lctx RetQ cenv ty id e es p sz vtyp tyv.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    has_length_word (expr_type e) /\ is_empty_value_expr e /\
    has_length_word vtyp /\ evaluate_type (get_tenv cx) vtyp = SOME tyv /\
    (!gs. (do result <- eval_expr cx e; read_result cx result od)
            (es with gas_obs := gs) =
          (INL (default_value tyv), es with gas_obs := gs)) /\
    (!entry. lookup_scopes id es.scopes = SOME entry ==> entry.type = tyv) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assign (BaseTarget (NameTarget id)) e))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  cheat
QED
