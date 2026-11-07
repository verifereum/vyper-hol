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
  vyperTypeInitialState

open gasContextTheory gasOutcomeTheory gasSummaryTheory gasSummaryComposeTheory
     gasExemptCertTheory fragGasModeTheory fragGasPathTheory;

Theorem len_pre_args[local]:
  !cenv cx env ann args es.
    expr_body_pre cenv cx env (Builtin ann Len args) es ==>
    ?e. args = [e] /\ ann = BaseT (UintT 256) /\
        is_sized_type (expr_type e)
Proof
  cheat
QED

Theorem names_builtin_len[local]:
  !args. ~names_builtin Len args
Proof
  cheat
QED

Theorem compile_expr_len[local]:
  !cenv ty ann e st.
    compile_expr cenv ty (Builtin ann Len [e]) st =
    (let (vv, st1) = compile_expr cenv ty e st in
       as_stack_val ann
         (compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca (vv_operand vv)
           (case vv_location vv of SOME l => l | NONE => LocMemory) st1))
Proof
  cheat
QED

Theorem eval_expr_len[local]:
  !cx ann e es.
    eval_expr cx (Builtin ann Len [e]) es =
    (do tv <- eval_expr cx e;
        n <- result_array_length cx tv;
        return (Value (IntV (&n))) od) es
Proof
  cheat
QED

Theorem sized_type_cases[local]:
  !t. is_sized_type t ==>
    (?et k. t = ArrayT et (Dynamic k)) \/
    (?k. t = BaseT (StringT k)) \/
    (?k. t = BaseT (BytesT (Dynamic k)))
Proof
  cheat
QED

Theorem sized_memory_header:
  !tenv t tvt v a mem cx es.
    evaluate_type tenv t = SOME tvt /\ is_sized_type t /\
    value_has_type tvt v /\ val_in_memory tvt v a mem ==>
    ?n. result_array_length cx (Value v) es = (INL n, es) /\
        mem_word_at a mem = n2w n
Proof
  cheat
QED

Theorem sized_memory_header_widens[local]:
  !tenv pt t pvt tvt v a mem cx es.
    type_widens_to tenv pt t /\ is_sized_type t /\
    evaluate_type tenv pt = SOME pvt /\
    evaluate_type tenv t = SOME tvt /\ value_has_type tvt v /\
    val_in_memory pvt v a mem ==>
    ?n. result_array_length cx (Value v) es = (INL n,es) /\
        mem_word_at a mem = n2w n
Proof
  cheat
QED

Theorem read_storage_array_length:
  !cx tr slot et k es v.
    read_result cx (PlaceR (StoragePlace tr slot (ArrayTV et (Dynamic k)))) es = (INL v, es) ==>
    result_array_length cx (Value v) es =
    result_array_length cx (PlaceR (StoragePlace tr slot (ArrayTV et (Dynamic k)))) es
Proof
  cheat
QED

Theorem slots_to_bytes_length_exact:
  !slots n. LENGTH (slots_to_bytes n slots) = MIN n (32 * LENGTH slots)
Proof
  cheat
QED

Theorem read_slots_length:
  !n storage off. LENGTH (read_slots storage off n) = n
Proof
  cheat
QED

Theorem sized_decode_header:
  !tenv t tvt storage off v cx es.
    evaluate_type tenv t = SOME tvt /\ is_sized_type t /\
    decode_value storage off tvt = SOME v ==>
    ?n. result_array_length cx (Value v) es = (INL n, es) /\
        read_slot storage off = n2w n
Proof
  cheat
QED

Theorem sized_read_result_length:
  !env cx t tvt r es v.
    evaluate_type env.type_defs t = SOME tvt /\ is_sized_type t /\
    eval_result_typed (env,cx,es) r (Type t) /\
    read_result cx r es = (INL v,es) /\ value_has_type tvt v ==>
    result_array_length cx (Value v) es = result_array_length cx r es
Proof
  cheat
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
  cheat
QED

Theorem read_result_memory_header_widens[local]:
  !env cx pt t pvt tvt r es v w mem n.
    type_widens_to (get_tenv cx) pt t /\
    evaluate_type (get_tenv cx) pt = SOME pvt /\
    evaluate_type (get_tenv cx) t = SOME tvt /\ is_sized_type t /\
    env.type_defs = get_tenv cx /\
    eval_result_typed (env,cx,es) r (Type t) /\
    read_result cx r es = (INL v,es) /\ value_has_type tvt v /\
    val_in_memory pvt v w mem /\
    result_array_length cx r es = (INL n,es) ==>
    mem_word_at w mem = n2w n
Proof
  cheat
QED

Theorem sized_read_result_length_success:
  !env cx t tvt r es v.
    evaluate_type env.type_defs t = SOME tvt /\ is_sized_type t /\
    eval_result_typed (env,cx,es) r (Type t) /\
    read_result cx r es = (INL v,es) /\ value_has_type tvt v ==>
    ?n. result_array_length cx r es = (INL n,es)
Proof
  cheat
QED



Theorem expr_sim_pre_runtime_typed:
  !cenv cx env e es r es'.
    expr_sim_pre cenv cx env e es /\ eval_expr cx e es = (INL r,es') ==>
    ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
          eval_result_typed (env,cx,es') r (Type (expr_type e)) /\
          (!v. read_result cx r es' = (INL v,es') ==> value_has_type tvt v)
Proof
  cheat
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
  cheat
QED

Theorem sized_type_widens_source[local]:
  type_widens_to tenv pt t /\ is_sized_type t ==> is_sized_type pt
Proof
  cheat
QED

Theorem storage_holds_header_widens[local]:
  !env cx tr pt t pvt tvt tv w es s n.
    storage_holds cx tr pt tv w es s /\
    type_widens_to (get_tenv cx) pt t /\
    evaluate_type (get_tenv cx) pt = SOME pvt /\
    evaluate_type (get_tenv cx) t = SOME tvt /\ is_sized_type t /\
    env.type_defs = get_tenv cx /\
    eval_result_typed (env,cx,es) tv (Type t) /\
    (!v. read_result cx tv es = (INL v,es) ==> value_has_type tvt v) /\
    result_array_length cx tv es = (INL n, es) ==>
    lookup_storage w
      (if tr then lookup_transient_storage cx.txn.target es.tStorage
       else (lookup_account cx.txn.target es.accounts).storage) = n2w n /\
    storage_range_agree (get_storage cx es tr)
      (if tr then contract_transient s else contract_storage s) w pvt /\
    0 < type_slot_size pvt
Proof
  cheat
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
  cheat
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
  cheat
QED

Theorem vv_holds_len_header_widens[local]:
  !env func cenv cx es s pt t pvt tvt tv vv n ctx.
    stmt_state_rel ctx func cenv cx es s /\ vv_holds cenv cx pt tv vv es s /\
    type_widens_to env.type_defs pt t /\
    is_sized_type t /\ evaluate_type (get_tenv cx) t = SOME tvt /\
    evaluate_type (get_tenv cx) pt = SOME pvt /\
    env.type_defs = get_tenv cx /\
    eval_result_typed (env,cx,es) tv (Type t) /\
    (!v. read_result cx tv es = (INL v,es) ==> value_has_type tvt v) /\
    result_array_length cx tv es = (INL n, es) ==>
    ?w. eval_operand (vv_operand vv) s = SOME w /\
        ptr_load_val cenv.ce_is_ctor
          (case vv_location vv of SOME l => l | NONE => LocMemory) w s = n2w n
Proof
  cheat
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
  cheat
QED

Theorem vv_holds_sized_length_success_widens[local]:
  !env cenv cx pt t r vv es s tvt.
    vv_holds cenv cx pt r vv es s /\ is_sized_type t /\
    evaluate_type (get_tenv cx) t = SOME tvt /\
    env.type_defs = get_tenv cx /\
    eval_result_typed (env,cx,es) r (Type t) /\
    (!v. read_result cx r es = (INL v,es) ==> value_has_type tvt v) ==>
    ?n. result_array_length cx r es = (INL n,es)
Proof
  cheat
QED

Theorem len_vv_post_load[local]:
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
  cheat
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
  cheat
QED

Theorem compile_len_vv_frag[local]:
  !env ctx func cenv cx e es sa sm sb s0 es' tv vv op tvt pvt R.
    type_widens_to (get_tenv cx) (post_value_type cenv e) (expr_type e) /\
    evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME pvt /\
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
  cheat
QED

Theorem len_load_extends[local]:
  !ctor imm pop loc sa op sb.
    compile_builtin_len ctor imm pop loc sa = (op,sb) ==> cs_extends sa sb
Proof
  cheat
QED


Theorem len_step_ILOAD[local]:
  !id a out s w.
    eval_operand a s = SOME w ==>
    step_inst_base (mk_inst id ILOAD [a] [out]) s =
    OK (update_var out (mload (w2n w) s) s)
Proof
  cheat
QED
Theorem len_step_ADD_imm_base[local]:
  !ctx func cenv cx es id pop ib out s w.
    stmt_state_rel ctx func cenv cx es s /\
    cenv.ce_imm_alloca = SOME ib /\ eval_operand pop s = SOME w ==>
    step_inst_base (mk_inst id ADD [pop; ib] [out]) s =
    OK (update_var out w s)
Proof
  cheat
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
  cheat
QED
Theorem len_emit_op_cs_extends[local]:
  !opc args sm op sb. emit_op opc args sm = (op, sb) ==> cs_extends sm sb
Proof
  cheat
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
  cheat
QED

Theorem len_step_TLOAD[local]:
  !op1 v1 id out ss.
    eval_operand op1 ss = SOME v1 ==>
    step_inst_base (mk_inst id TLOAD [op1] [out]) ss =
      OK (update_var out (tload v1 ss) ss)
Proof
  cheat
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
  cheat
QED

Theorem len_option_rator[local]:
  !x f g s. (case (x : 'a option) of NONE => f | SOME v => g v) s =
            (case x of NONE => f s | SOME v => g v s)
Proof
  cheat
QED

Theorem len_gsb_obs:
  !cx tr st g.
    get_storage_backend cx tr (st with gas_obs := g) =
    (FST (get_storage_backend cx tr st), SND (get_storage_backend cx tr st) with gas_obs := g)
Proof
  cheat
QED

Theorem len_rss_obs:
  !cx tr sl tv st g.
    read_storage_slot cx tr sl tv (st with gas_obs := g) =
    (FST (read_storage_slot cx tr sl tv st),
     SND (read_storage_slot cx tr sl tv st) with gas_obs := g)
Proof
  cheat
QED

Theorem len_rp_obs[local]:
  !cx p st g.
    read_place cx p (st with gas_obs := g) =
    (FST (read_place cx p st), SND (read_place cx p st) with gas_obs := g)
Proof
  cheat
QED

Theorem len_bind_obs[local]:
  !m f.
    (!st g. m (st with gas_obs := g) = (FST (m st), SND (m st) with gas_obs := g)) /\
    (!v st g. f v (st with gas_obs := g) = (FST (f v st), SND (f v st) with gas_obs := g)) ==>
    !st g. bind m f (st with gas_obs := g) =
           (FST (bind m f st), SND (bind m f st) with gas_obs := g)
Proof
  cheat
QED

Theorem len_rr_obs[local]:
  !cx res st g.
    read_result cx res (st with gas_obs := g) =
    (FST (read_result cx res st), SND (read_result cx res st) with gas_obs := g)
Proof
  cheat
QED

Theorem len_tail_obs[local]:
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
  cheat
QED

Theorem len_ral_gas_obs0[local]:
  !cx tv st g.
    result_array_length cx tv (st with gas_obs := g) =
    (FST (result_array_length cx tv st),
     SND (result_array_length cx tv st) with gas_obs := g)
Proof
  cheat
QED

Theorem len_ral_gas_obs[local]:
  !cx tv st g r.
    result_array_length cx tv st = (r, st) ==>
    result_array_length cx tv (st with gas_obs := g) = (r, st with gas_obs := g)
Proof
  cheat
QED

Theorem len_vv_path[local]:
  !env ctx func cenv cx e es sa sm sb s0 es' tv vv op tvt t pvt.
    type_widens_to (get_tenv cx) (post_value_type cenv e) (expr_type e) /\
    evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME pvt /\
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
  cheat
QED

Theorem len_source[local]:
  !cx ann e.
    eval_expr cx (Builtin ann Len [e]) =
    bind (eval_expr cx e)
      (\tv. bind (result_array_length cx tv) (\n. return (Value (IntV (&n)))))
Proof
  cheat
QED

Theorem len_operand_admissible[local]:
  !cenv cx env e es.
    expr_body_pre cenv cx env e es ==>
    gas_admissible (eval_expr cx e) expr_vv_res_ok es
Proof
  cheat
QED

Theorem len_exempt_cert[local]:
  !memory tops p cx ann e start marks out endpoint.
    gas_exempt_cert memory tops p (ignore_bind (eval_expr cx e) (return ()))
      start marks out endpoint ==>
    gas_exempt_cert memory tops p
      (ignore_bind (eval_expr cx (Builtin ann Len [e])) (return ()))
      start marks out endpoint
Proof
  cheat
QED

Theorem compile_len_singleton_sim[local]:
  !ctx func cenv cx env ty e es.
    expr_body_pre cenv cx env (Builtin (BaseT (UintT 256)) Len [e]) es /\
    expr_vv_sim ctx func cenv cx ty e es ==>
    expr_vv_sim ctx func cenv cx ty (Builtin (BaseT (UintT 256)) Len [e]) es
Proof
  cheat
QED

Theorem compile_len_vv_case:
  !nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann Len args)
Proof
  cheat
QED
