(*
 * Statement simulation: a declaration initialised with the empty value
 * (#637)
 *
 * x: T = e for a type T with a length word (a bytestring or a dynamic
 * array) and e the empty value (empty(T), b"", an empty list): the
 * lowering runs e's code, drops its value_vv, and stores a zero length
 * word at the local's buffer, which lays out T's default value.
 *
 * TOP-LEVEL:
 *   compile_annassign_empty_stmt_frag — the declaration, for every outcome
 *                                       of its right-hand side
 *)

Theory stmtSimDeclEmpty
Ancestors
  stmtSimProps
  stmtSimDefs
  exprSimDefs
  loweringPosts
  list rich_list finite_map pred_set
  fragExec localPtrsProps  loweringSlice  stmtSimDeclStore
  stmtSimDecl stmtSimDeclMem valueCopyBytes
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding valueEncodingProps
  vyperInterpreter vyperState vyperValue vyperTyping
  venomExecSemantics venomInst venomState
Libs
  monadsyntax

Theorem annassign_empty_store_run[local]:
  !ctx func cenv cx es s id p sz w inst t tyv sc rest a st st' tenv.
    emit_void MSTORE [Var p; Lit 0w] st = ((), st') /\
    fn_has_code st st' func /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ lookup_var p s = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    has_length_word t /\ evaluate_type tenv t = SOME tyv /\
    type_memory_size tyv <= sz ==>
    ?u. stmt_state_rel ctx func cenv cx
          (es with scopes :=
             (sc |+ (id, <|assignable := a; type := tyv;
                           value := default_value tyv; popped := []|>)) :: rest) u /\
        ~u.vs_halted /\ u.vs_current_bb = st'.cs_current_bb /\
        u.vs_inst_idx = LENGTH st'.cs_current_insts /\
        (!x. lookup_var x u = lookup_var x s) /\
        (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                     FLOOKUP u.vs_allocas aid = SOME entry) /\
        !fuel r. run_from fuel ctx func u = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s = r
Proof
  cheat
QED

Theorem annassign_empty_store_post_run[local]:
  !ctx func cenv cx e es es1 s0 s sa sb sf tv vv id p sz w inst t tyv sc rest a tenv.
    vv_post ctx func cenv cx e es sa sb s0 es1 tv vv s /\
    emit_void MSTORE [Var p; Lit 0w] sb = ((), sf) /\ fn_has_code sb sf func /\
    ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts /\ fn_inst_ids_distinct func /\
    es1.scopes = sc :: rest /\ lookup_scopes id es1.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es1.scopes p /\ not_fresh_at sa p /\
    lookup_var p s0 = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP s0.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    has_length_word t /\ evaluate_type tenv t = SOME tyv /\
    type_memory_size tyv <= sz ==>
    ?u. stmt_state_rel ctx func cenv cx
          (es1 with scopes :=
             (sc |+ (id, <|assignable := a; type := tyv;
                           value := default_value tyv; popped := []|>)) :: rest) u /\
        ~u.vs_halted /\ u.vs_current_bb = sf.cs_current_bb /\
        u.vs_inst_idx = LENGTH sf.cs_current_insts /\
        (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
               lookup_var x u = SOME v) /\
        (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
                     FLOOKUP u.vs_allocas aid = SOME entry) /\
        !fuel r. run_from fuel ctx func u = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s = r
Proof
  cheat
QED

Theorem annassign_empty_success_run[local]:
  !ctx func cenv cx id vtyp e es es' tyv sa sb sf vv p sz s0 w inst.
    eval_stmt cx (AnnAssign id vtyp e) es = (INL (), es') /\
    has_length_word vtyp /\ evaluate_type (get_tenv cx) vtyp = SOME tyv /\
    (!tv es1. eval_expr cx e es = (INL tv, es1) ==>
              tv = Value (default_value tyv)) /\
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    compile_expr cenv (expr_type e) e sa = (vv, sb) /\
    emit_void MSTORE [Var p; Lit 0w] sb = ((), sf) /\
    fn_has_code sa sb func /\ fn_has_code sb sf func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ not_fresh_at sa p /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    lookup_var p s0 = SOME w /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP s0.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    type_memory_size tyv <= sz ==>
    ?t. stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
        t.vs_current_bb = sf.cs_current_bb /\ t.vs_inst_idx = LENGTH sf.cs_current_insts /\
        (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==> lookup_var x t = SOME u) /\
        (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
                     FLOOKUP t.vs_allocas aid = SOME entry) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s0 = r
Proof
  cheat
QED

Theorem expr_vv_sim_error_run[local]:
  !ctx func cenv cx ty e es ex es' sa sb vv s0.
    expr_vv_sim ctx func cenv cx ty e es /\
    eval_expr cx e es = (INR ex, es') /\
    expr_res_ok (INR ex : value + exception) /\
    compile_expr cenv ty e sa = (vv, sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?fuel r. run_from fuel ctx func s0 = r /\ exit_result r /\
             expr_exit (INR ex : unit + exception) r
Proof
  cheat
QED

Theorem compile_annassign_empty_parts[local]:
  !cenv lctx ty id vtyp e st sf p sz.
    compile_stmt cenv lctx ty (AnnAssign id vtyp e) st = ((), sf) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    has_length_word vtyp /\ is_empty_value_expr e ==>
    ?sA vv sB.
      emit_inst ALLOCA [Lit (n2w sz)] [p] st = ((), sA) /\
      compile_expr cenv (expr_type e) e sA = (vv, sB) /\
      emit_void MSTORE [Var p; Lit 0w] sB = ((), sf)
Proof
  cheat
QED

Theorem annassign_empty_code_parts[local]:
  !cenv lctx ty id vtyp e sa sf c func.
    stmt_env cenv lctx ty (AnnAssign id vtyp e) sa = (c, sf) /\
    cenv.ce_alloca_locals /\ has_length_word vtyp /\ is_empty_value_expr e /\
    fn_has_code sa sf func /\ local_ptrs_reserved cenv sa /\
    (!st0 c st1. declare_local cenv id vtyp st0 = (c, st1) ==>
       !a b vv. compile_expr c (expr_type e) e a = (vv, b) ==> cs_extends a b) ==>
    ?st sA sB vv p.
      declare_local cenv id vtyp sa = (c, st) /\
      FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes cenv vtyp)) /\
      emit_inst ALLOCA [Lit (n2w (type_memory_bytes cenv vtyp))] [p] st = ((), sA) /\
      compile_expr c (expr_type e) e sA = (vv, sB) /\
      emit_void MSTORE [Var p; Lit 0w] sB = ((), sf) /\
      local_ptrs_reserved c st /\ local_ptrs_reserved c sA /\ not_fresh_at sA p /\
      cs_extends st sA /\ cs_extends sA sB /\ cs_extends sB sf /\
      fn_has_code st sA func /\ fn_has_code sA sB func /\ fn_has_code sB sf func /\
      MEM (mk_inst st.cs_next_id ALLOCA
             [Lit (n2w (type_memory_bytes cenv vtyp))] [p]) (fn_insts func)
Proof
  cheat
QED

(* x: T = e for a type T with a length word, where e is the empty value
   and its values are T's default value.  The lowering keeps e's code
   (e's judgment is expr_vv_sim, as e's value_vv is never unwrapped) and
   stores a zero length word at the local's buffer of type_memory_bytes of
   T, the size val_in_memory lays a value of T out in. *)
(* Why it holds.  As compile_annassign_memory_stmt_frag: the relation at
   the declared environment c, the local's ALLOCA, then e's fragment,
   which exits on an error or ends in vv_post; then the MSTORE of 0 at the
   local's buffer, whose region misses every other live local's, lays out
   T's default value (memory_length_word_layout). *)
Theorem compile_annassign_empty_stmt_frag:
  !ctx func cx lctx RetQ cenv ty id vtyp e es tyv.
    cenv.ce_alloca_locals /\
    has_length_word vtyp /\ is_empty_value_expr e /\
    lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    evaluate_type (get_tenv cx) vtyp = SOME tyv /\
    type_memory_bytes cenv vtyp = type_memory_size tyv /\
    type_memory_size tyv < dimword (:256) /\
    (!tv es1. eval_expr cx e es = (INL tv, es1) ==>
              tv = Value (default_value tyv)) /\
    (!st0 c st1. declare_local cenv id vtyp st0 = (c, st1) ==>
       expr_vv_sim ctx func c cx (expr_type e) e es /\
       !sa sb vv. compile_expr c (expr_type e) e sa = (vv, sb) ==>
                  cs_extends sa sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (AnnAssign id vtyp e))
      (eval_stmt cx (AnnAssign id vtyp e)) es
Proof
  cheat
QED


