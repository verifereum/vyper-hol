(*
 * Statement simulation: a memory-backed local's declaration (#637)
 *
 * AnnAssign over stmt_frag (stmtSim) for a local whose type is not a word
 * type (an aggregate, a bytestring): the right-hand side's errors exit; on
 * a value the local's ALLOCA runs and compile_assign_value copies the
 * value's bytes into the local's buffer, staged through a buffer of its
 * own when the value is in memory, so the buffer holds the value as
 * val_in_memory lays it out.
 *
 * TOP-LEVEL:
 *   compile_annassign_memory_widen_stmt_frag — a memory-backed local's
 *                                              declaration, for every
 *                                              outcome of its right-hand
 *                                              side (a value or a place
 *                                              read by read_result),
 *                                              lowered at the declared
 *                                              type or both bytestrings
 *   compile_annassign_memory_stmt_frag — the same, where the right-hand
 *                                        side is lowered at the declared
 *                                        type
 *   memory_length_word_layout — a zero length word lays out the default
 *                               value of a type with a length word
 *)

Theory stmtSimDeclMem
Ancestors
  stmtSimProps
  exprSimProps
  stmtSimDefs
  exprSimDefs
  loweringPosts
  list rich_list finite_map pred_set
  fragExec localPtrsProps  loweringSlice  stmtSimDeclStore
  stmtSimDecl valueCopy valueCopyBytes intCallResult exprOperandVar freshWrites
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  context compileEnv valueEncoding valueTypingMemoryProps exprSimBufferStore
  vyperInterpreter vyperState vyperValue vyperTyping vyperExprNoControl
  venomExecSemantics venomExecProofs venomInst venomState
Libs
  monadsyntax intLib

(* Declaration changes only the name-indexed parts of the environment;
   layout and the expression's lowered type are unaffected. *)
Theorem declare_local_memory_types[local]:
  !cenv id vtyp sa c st.
    declare_local cenv id vtyp sa = (c, st) /\ cenv.ce_alloca_locals ==>
    (!ty. type_memory_bytes c ty = type_memory_bytes cenv ty) /\
    (!e. lowered_value_type c e = lowered_value_type cenv e)
Proof
  cheat
QED

Theorem compile_assign_memory_appends:
  !cenv dst src loc ty info sz.
    cs_appends (compile_assign_value cenv dst LocMemory src F loc ty ty info sz)
Proof
  cheat
QED

(* The lowering's buffer for e's value, at e's lowered type, holds the
   value whose layout at the declared type is copied. *)
Theorem annassign_widen_footprint[local]:
  !tenv cenv e vtyp tyv ltv v.
    (expr_type e = vtyp \/
     is_bytestring_type vtyp /\ is_bytestring_type (expr_type e)) /\
    (lowered_value_type cenv e = vtyp \/ is_bytestring_type vtyp) /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) /\
    evaluate_type tenv vtyp = SOME tyv /\
    evaluate_type tenv (lowered_value_type cenv e) = SOME ltv /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size ltv /\
    value_has_type tyv v /\ value_has_type ltv v ==>
    val_footprint tyv v <= type_memory_bytes cenv (lowered_value_type cenv e)
Proof
  cheat
QED

Theorem compile_assign_memory_widen_appends:
  !cenv dst src loc dty sty info sz.
    sty = dty \/ is_bytestring_type dty ==>
    cs_appends (compile_assign_value cenv dst LocMemory src F loc dty sty info sz)
Proof
  cheat
QED

Theorem compile_annassign_memory_parts[local]:
  !cenv lctx ty id vtyp e st sf p sz.
    compile_stmt cenv lctx ty (AnnAssign id vtyp e) st = ((), sf) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    ~is_word_type vtyp /\ ~(has_length_word vtyp /\ is_empty_value_expr e) ==>
    ?sA sV sB vv op.
      emit_inst ALLOCA [Lit (n2w sz)] [p] st = ((), sA) /\
      compile_expr cenv (expr_type e) e sA = (vv, sV) /\
      unwrap_value cenv vv sV = (op, sB) /\
      lower_value compile_expr cenv (expr_type e) e sA = (op, sB) /\
      compile_assign_value cenv (Var p) LocMemory op F (vv_location vv)
        vtyp (lowered_value_type cenv e)
        (case vtyp of ArrayT elem_ty (Dynamic _) =>
           SOME ((type_memory_bytes cenv elem_ty + 31) DIV 32,
                 type_memory_bytes cenv elem_ty) | _ => NONE)
        (type_memory_bytes cenv vtyp) sB = ((), sf)
Proof
  cheat
QED

(* A declaration's step: declare_local, then the statement's code under the
   extended environment. *)
Theorem stmt_env_annassign:
  !cenv lctx ty id vtyp e sa c sf.
    stmt_env cenv lctx ty (AnnAssign id vtyp e) sa = (c, sf) ==>
    ?st. declare_local cenv id vtyp sa = (c, st) /\
         compile_stmt c lctx ty (AnnAssign id vtyp e) st = ((), sf)
Proof
  cheat
QED

(* The ALLOCA of a declared local's buffer, emitted from st to sA ahead of
   the rest of the declaration's code up to sf: the local's pointer is
   handed out before sA, the pointers stay reserved, and the ALLOCA is an
   instruction of func. *)
Theorem annassign_alloca_code:
  !cenv c id vtyp sa st sA sf func.
    declare_local cenv id vtyp sa = (c, st) /\ cenv.ce_alloca_locals /\
    local_ptrs_reserved cenv sa /\
    emit_inst ALLOCA [Lit (n2w (type_memory_bytes cenv vtyp))]
      [STRING #"%" (toString sa.cs_next_var)] st = ((), sA) /\
    cs_extends sA sf /\ fn_has_code st sf func ==>
    local_ptrs_reserved c st /\ local_ptrs_reserved c sA /\
    not_fresh_at sA (STRING #"%" (toString sa.cs_next_var)) /\
    cs_extends st sA /\ fn_has_code st sA func /\ fn_has_code sA sf func /\
    MEM (mk_inst st.cs_next_id ALLOCA
           [Lit (n2w (type_memory_bytes cenv vtyp))]
           [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)
Proof
  cheat
QED

Theorem annassign_memory_code_parts[local]:
  !cenv lctx ty id vtyp e sa sf c func.
    stmt_env cenv lctx ty (AnnAssign id vtyp e) sa = (c, sf) /\
    cenv.ce_alloca_locals /\ ~is_word_type vtyp /\
    ~(has_length_word vtyp /\ is_empty_value_expr e) /\
    (lowered_value_type cenv e = vtyp \/ is_bytestring_type vtyp) /\
    fn_has_code sa sf func /\ local_ptrs_reserved cenv sa /\
    (!st0 c st1. declare_local cenv id vtyp st0 = (c, st1) ==>
       !a b op. lower_value compile_expr c (expr_type e) e a = (op, b) ==>
                cs_extends a b) ==>
    ?st sA sV sB vv op p.
      declare_local cenv id vtyp sa = (c, st) /\
      FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes cenv vtyp)) /\
      emit_inst ALLOCA [Lit (n2w (type_memory_bytes cenv vtyp))] [p] st = ((), sA) /\
      compile_expr c (expr_type e) e sA = (vv, sV) /\
      unwrap_value c vv sV = (op, sB) /\
      lower_value compile_expr c (expr_type e) e sA = (op, sB) /\
      compile_assign_value c (Var p) LocMemory op F (vv_location vv) vtyp
        (lowered_value_type cenv e)
        (case vtyp of ArrayT elem_ty (Dynamic _) =>
           SOME ((type_memory_bytes c elem_ty + 31) DIV 32,
                 type_memory_bytes c elem_ty) | _ => NONE)
        (type_memory_bytes c vtyp) sB = ((), sf) /\
      local_ptrs_reserved c st /\ local_ptrs_reserved c sA /\ not_fresh_at sA p /\
      cs_extends st sA /\ cs_extends sA sB /\ cs_extends sB sf /\
      fn_has_code st sA func /\ fn_has_code sA sB func /\ fn_has_code sB sf func /\
      MEM (mk_inst st.cs_next_id ALLOCA
             [Lit (n2w (type_memory_bytes cenv vtyp))] [p]) (fn_insts func)
Proof
  cheat
QED


Theorem mcopy_alloca_framed_frag[local]:
  !ctx func cenv cx es sa sb s inst p dw sw src sz tv v.
    emit_void MCOPY [Var p; src; Lit (n2w sz)] sa = ((), sb) /\
    lookup_var p s = SOME dw /\ eval_operand src s = SOME sw /\
    sz < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    not_local_ptr cenv es.scopes p /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw, sz) /\
    val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
    val_footprint tv v <= sz ==>
    frag_exec ctx sa sb (\t. t = s)
      (\t. stmt_state_rel ctx func cenv cx es t /\
           val_in_memory tv v (w2n dw) t.vs_memory /\
           (!q. lookup_var q t = lookup_var q s) /\
           t.vs_allocas = s.vs_allocas) (\r. F)
Proof
  cheat
QED

Theorem alloc_copy_memory_owned_run:
  !ctx func cenv cx es sa sm sb s0 p src sz sw tv v.
    emit_inst ALLOCA [Lit (n2w sz)] [p] sa = ((), sm) /\
    emit_void MCOPY [Var p; src; Lit (n2w sz)] sm = ((), sb) /\
    stmt_state_rel ctx func cenv cx es s0 /\ fn_inst_ids_distinct func /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) (fn_insts func) /\
    not_local_ptr cenv es.scopes p /\ sz < dimword (:256) /\
    src <> Var p /\ eval_operand src s0 = SOME sw /\
    val_in_memory tv v (w2n sw) s0.vs_memory /\ val_wf tv v /\
    val_footprint tv v <= sz /\
    fn_has_code sa sm func /\ fn_has_code sm sb func /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?s2 w. lookup_var p s2 = SOME w /\
      FLOOKUP s2.vs_allocas sa.cs_next_id = SOME (w2n w, sz) /\
      stmt_state_rel ctx func cenv cx es s2 /\
      val_in_memory tv v (w2n w) s2.vs_memory /\
      (!x. x <> p ==> lookup_var x s2 = lookup_var x s0) /\
      (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
                   FLOOKUP s2.vs_allocas aid = SOME entry) /\
      ~s2.vs_halted /\ s2.vs_current_bb = sb.cs_current_bb /\
      s2.vs_inst_idx = LENGTH sb.cs_current_insts /\
      !fuel r. run_from fuel ctx func s2 = r /\ (!e. r <> Error e) ==>
               ?fuel'. run_from fuel' ctx func s0 = r
Proof
  cheat
QED

Theorem alloc_copy_memory_framed_run:
  !ctx func cenv cx es sa sm sb s0 p src sz sw tv v.
    emit_inst ALLOCA [Lit (n2w sz)] [p] sa = ((), sm) /\
    emit_void MCOPY [Var p; src; Lit (n2w sz)] sm = ((), sb) /\
    stmt_state_rel ctx func cenv cx es s0 /\ fn_inst_ids_distinct func /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) (fn_insts func) /\
    not_local_ptr cenv es.scopes p /\ sz < dimword (:256) /\
    src <> Var p /\ eval_operand src s0 = SOME sw /\
    val_in_memory tv v (w2n sw) s0.vs_memory /\ val_wf tv v /\
    val_footprint tv v <= sz /\
    fn_has_code sa sm func /\ fn_has_code sm sb func /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?s2 w. lookup_var p s2 = SOME w /\
      stmt_state_rel ctx func cenv cx es s2 /\
      val_in_memory tv v (w2n w) s2.vs_memory /\
      (!x. x <> p ==> lookup_var x s2 = lookup_var x s0) /\
      (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
                   FLOOKUP s2.vs_allocas aid = SOME entry) /\
      ~s2.vs_halted /\ s2.vs_current_bb = sb.cs_current_bb /\
      s2.vs_inst_idx = LENGTH sb.cs_current_insts /\
      !fuel r. run_from fuel ctx func s2 = r /\ (!e. r <> Error e) ==>
               ?fuel'. run_from fuel' ctx func s0 = r
Proof
  cheat
QED

Theorem stmt_state_rel_declare_store_frame[local]:
  !func cenv cx es s t sa id p sz w inst v tyv sc rest a ctx.
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ lookup_var p s = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    local_ptrs_reserved cenv sa /\ not_fresh_at sa p /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!b n. b + n <= w2n w \/ w2n w + type_memory_size tyv <= b ==>
           mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    type_memory_size tyv <= sz /\ val_wf tyv v /\
    val_in_memory tyv v (w2n w) t.vs_memory ==>
    stmt_state_rel ctx func cenv cx
      (es with scopes :=
        (sc |+ (id, <|assignable := a; type := tyv; value := v; popped := []|>)) :: rest) t
Proof
  cheat
QED
Theorem annassign_memory_store_run[local]:
  !ctx func cenv cx es s id p sz w inst v tyv sc rest a src ty sa sb sw.
    compile_store_memory cenv src (Var p) ty ty sa = ((), sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\ not_fresh_at sa p /\
    eval_operand src s = SOME sw /\ lookup_var p s = SOME w /\
    ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tyv /\
    value_has_type tyv v /\ val_wf tyv v /\
    val_in_memory tyv v (w2n sw) s.vs_memory /\
    type_memory_bytes cenv ty = type_memory_size tyv /\
    type_memory_size tyv <= sz /\ type_memory_size tyv + 64 < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. stmt_state_rel ctx func cenv cx
          (es with scopes :=
            (sc |+ (id, <|assignable := a; type := tyv; value := v; popped := []|>)) :: rest) t /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                     FLOOKUP t.vs_allocas aid = SOME entry) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s = r
Proof
  cheat
QED

(* Split the overlap-safe assignment into its allocation, flat copy and
   typed store. The allocation and the flat copy have the source's size;
   the store is the one at the destination type, which for a bytestring
   destination copies the runtime length whatever the source's bound.  The
   allocation output is fresh at the assignment entry. *)
Theorem annassign_staged_memory_widen_parts:
  !cenv dst src dty sty info bytes sa sb func.
    compile_assign_value cenv dst LocMemory src F (SOME LocMemory)
      dty sty info bytes sa = ((),sb) /\
    (sty = dty \/ is_bytestring_type dty) /\
    0 < type_memory_bytes cenv sty /\ fn_has_code sa sb func ==>
    ?sx sm sn tmp.
      sx = sa with cs_next_var := sa.cs_next_var + 1 /\
      ~not_fresh_at sa tmp /\ not_fresh_at sn tmp /\
      sa.cs_next_var <= sn.cs_next_var /\
      emit_inst ALLOCA [Lit (n2w (type_memory_bytes cenv sty))] [tmp]
        sx = ((),sm) /\
      emit_void MCOPY [Var tmp; src; Lit (n2w (type_memory_bytes cenv sty))]
        sm = ((),sn) /\
      compile_store_memory cenv (Var tmp) dst dty dty sn = ((),sb) /\
      cs_extends sa sx /\ cs_extends sx sm /\ cs_extends sm sn /\ cs_extends sn sb /\
      fn_has_code sx sm func /\ fn_has_code sm sn func /\
      fn_has_code sn sb func
Proof
  cheat
QED

Theorem annassign_staged_memory_parts:
  !cenv dst src ty info bytes sa sb func.
    compile_assign_value cenv dst LocMemory src F (SOME LocMemory)
      ty ty info bytes sa = ((),sb) /\
    0 < type_memory_bytes cenv ty /\ fn_has_code sa sb func ==>
    ?sx sm sn tmp.
      sx = sa with cs_next_var := sa.cs_next_var + 1 /\
      ~not_fresh_at sa tmp /\ not_fresh_at sn tmp /\
      sa.cs_next_var <= sn.cs_next_var /\
      emit_inst ALLOCA [Lit (n2w (type_memory_bytes cenv ty))] [tmp]
        sx = ((),sm) /\
      emit_void MCOPY [Var tmp; src; Lit (n2w (type_memory_bytes cenv ty))]
        sm = ((),sn) /\
      compile_store_memory cenv (Var tmp) dst ty ty sn = ((),sb) /\
      cs_extends sa sx /\ cs_extends sx sm /\ cs_extends sm sn /\ cs_extends sn sb /\
      fn_has_code sx sm func /\ fn_has_code sm sn func /\
      fn_has_code sn sb func
Proof
  cheat
QED

Theorem annassign_memory_assign_run[local]:
  !ctx func cenv cx es s id p sz w inst v tyv sc rest a src ty sty sa sb sw loc info bytes.
    compile_assign_value cenv (Var p) LocMemory src F loc ty sty info bytes sa = ((),sb) /\
    (sty = ty \/ is_bytestring_type ty) /\
    0 < type_memory_bytes cenv sty /\ type_memory_bytes cenv sty < dimword (:256) /\
    val_footprint tyv v <= type_memory_bytes cenv sty /\
    (!x. src = Var x ==> not_fresh_at sa x) /\ not_fresh_at sa p /\
    eval_operand src s = SOME sw /\ lookup_var p s = SOME w /\
    ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tyv /\
    value_has_type tyv v /\ val_wf tyv v /\
    val_in_memory tyv v (w2n sw) s.vs_memory /\
    type_memory_bytes cenv ty = type_memory_size tyv /\
    0 < type_memory_size tyv /\ type_memory_size tyv <= sz /\
    type_memory_size tyv + 64 < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. stmt_state_rel ctx func cenv cx
          (es with scopes :=
            (sc |+ (id, <|assignable := a; type := tyv; value := v; popped := []|>)) :: rest) t /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                     FLOOKUP t.vs_allocas aid = SOME entry) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s = r
Proof
  cheat
QED

Theorem annassign_memory_store_post_run[local]:
  !ctx func cenv cx e es es1 s0 s sa sb sf op id p sz w inst v etv tyv vtyp sty
   sc rest a loc info bytes.
    expr_post ctx func cenv cx e es sa sb s0 es1 v op s /\
    lower_value compile_expr cenv (expr_type e) e sa = (op,sb) /\
    cs_extends sa sb /\ local_ptrs_reserved cenv sa /\
    ~is_word_type vtyp /\
    (expr_type e = vtyp \/
     is_bytestring_type vtyp /\ is_bytestring_type (expr_type e)) /\
    (sty = vtyp \/ is_bytestring_type vtyp) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    evaluate_type (get_tenv cx) vtyp = SOME tyv /\
    value_has_type tyv v /\
    type_memory_bytes cenv vtyp = type_memory_size tyv /\
    0 < type_memory_size tyv /\ type_memory_size tyv <= sz /\
    type_memory_size tyv + 64 < dimword (:256) /\
    0 < type_memory_bytes cenv sty /\ type_memory_bytes cenv sty < dimword (:256) /\
    val_footprint tyv v <= type_memory_bytes cenv sty /\
    compile_assign_value cenv (Var p) LocMemory op F loc
      vtyp sty info bytes sb = ((),sf) /\
    fn_has_code sb sf func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts /\
    es1.scopes = sc :: rest /\ lookup_scopes id es1.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es1.scopes p /\ not_fresh_at sa p /\
    lookup_var p s0 = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP s0.vs_allocas inst.inst_id = SOME (w2n w,sz) ==>
    ?t. stmt_state_rel ctx func cenv cx
          (es1 with scopes :=
             (sc |+ (id, <|assignable := a; type := tyv; value := v; popped := []|>)) :: rest) t /\
        ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
        t.vs_inst_idx = LENGTH sf.cs_current_insts /\
        (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
               lookup_var x t = SOME u) /\
        (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
                     FLOOKUP t.vs_allocas aid = SOME entry) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s = r
Proof
  cheat
QED

(* A type with a length word has a default value laid out by a zero word,
   in at least one word. *)
Theorem memory_length_word_layout:
  !tenv ty tv off mem.
    has_length_word ty /\ evaluate_type tenv ty = SOME tv /\
    mem_word_at off mem = 0w ==>
    val_in_memory tv (default_value tv) off mem /\
    val_wf tv (default_value tv) /\ 32 <= type_memory_size tv
Proof
  cheat
QED

Theorem annassign_memory_read_success_run:
  !ctx func cenv cx id vtyp e es es' etv tyv sty sa sb sf op p sz s0 w inst loc info bytes.
    eval_stmt cx (AnnAssign id vtyp e) es = (INL (),es') /\
    ~is_word_type vtyp /\
    (expr_type e = vtyp \/
     is_bytestring_type vtyp /\ is_bytestring_type (expr_type e)) /\
    (sty = vtyp \/ is_bytestring_type vtyp) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    evaluate_type (get_tenv cx) vtyp = SOME tyv /\
    (!v es1. (do tv <- eval_expr cx e; read_result cx tv od) es = (INL v,es1) ==>
       value_has_type tyv v /\ val_footprint tyv v <= type_memory_bytes cenv sty) /\
    0 < type_memory_bytes cenv sty /\ type_memory_bytes cenv sty < dimword (:256) /\
    expr_sim ctx func cenv cx (expr_type e) e es /\
    lower_value compile_expr cenv (expr_type e) e sa = (op,sb) /\ cs_extends sa sb /\
    compile_assign_value cenv (Var p) LocMemory op F loc vtyp sty info bytes sb = ((),sf) /\
    fn_has_code sa sb func /\ fn_has_code sb sf func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ not_fresh_at sa p /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    lookup_var p s0 = SOME w /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP s0.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
    type_memory_bytes cenv vtyp = type_memory_size tyv /\
    0 < type_memory_size tyv /\ type_memory_size tyv <= sz /\
    type_memory_size tyv + 64 < dimword (:256) ==>
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

Theorem emit_void_nonterminator_open:
  !opc args sa sb.
    emit_void opc args sa = ((),sb) /\ ~is_terminator opc ==>
    ~block_is_terminated sb
Proof
  cheat
QED

Theorem compile_store_memory_same_open[local]:
  !cenv src dst ty sa sb.
    0 < type_memory_bytes cenv ty /\
    compile_store_memory cenv src dst ty ty sa = ((),sb) ==>
    ~block_is_terminated sb
Proof
  cheat
QED

Theorem compile_assign_value_memory_widen_open:
  !cenv dst src loc dty sty info bytes sa sb.
    0 < type_memory_bytes cenv dty /\ (sty = dty \/ is_bytestring_type dty) /\
    compile_assign_value cenv dst LocMemory src F loc dty sty info bytes sa = ((),sb) ==>
    ~block_is_terminated sb
Proof
  cheat
QED

Theorem compile_assign_value_memory_same_open:
  !cenv dst src loc ty info bytes sa sb.
    0 < type_memory_bytes cenv ty /\
    compile_assign_value cenv dst LocMemory src F loc ty ty info bytes sa = ((),sb) ==>
    ~block_is_terminated sb
Proof
  cheat
QED

(* x: T = e for a type T that is not a word type, where e is not the
   empty-value form the lowering stores as a zero length word, and e's
   values (read through read_result when e is a place) have type T.  Either e has type T and is lowered at T, or T is a
   bytestring type and so is e's type: then e's value is widened to T's
   bound (or e is a literal, lowered at its own length), which keeps its
   layout.  The local's buffer is type_memory_bytes of T, the size
   val_in_memory lays a value of T out in, and that size is not 0 (Vyper
   has no empty structs or arrays; the copy then emits an instruction, so
   the block stays open) and leaves the 64 bytes compile_store_memory_run's
   bytestring copy rounds up by below 2 ** 256.  e's values have its
   lowered type too, whose size is type_memory_bytes of it: a value staged
   through a buffer of that size fits. *)
(* Why it holds.  As compile_annassign_stmt_frag: the relation at the
   declared environment c, the local's ALLOCA, then e's fragment, which
   exits on an error or ends in expr_post with e's operand holding its
   value in memory (expr_val_rel at a type that is not a word type, laid
   out as at T: bytestring_val_in_memory_transfer).  When e's value_vv is
   in memory, compile_assign_value allocates a buffer of e's lowered type's
   size (a fresh ALLOCA, whose region misses the live locals' and the new
   local's) and copies the value there (mcopy_val_in_memory, the copy
   covering the value's footprint: annassign_widen_footprint); either way
   compile_store_memory at T then copies it into the local's buffer (for a
   bytestring T the same copy whatever the source's bound;
   compile_store_memory_run, whose address bound needs only the size: its
   bytestring copy needs the length plus 64 below 2 ** 256, its other
   copies the size).  The local's region misses every other live local's
   (local_ptrs_rel_alloca_disjoint), so the writes keep their bytes, and
   local_ptrs_rel_write_local binds the local, as
   stmt_state_rel_declare_store does for one word. *)
Theorem compile_annassign_memory_widen_stmt_frag:
  !ctx func cx lctx RetQ cenv ty id vtyp e es etv tyv ltv.
    cenv.ce_alloca_locals /\
    ~is_word_type vtyp /\ ~(has_length_word vtyp /\ is_empty_value_expr e) /\
    lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    (expr_type e = vtyp \/
     is_bytestring_type vtyp /\ is_bytestring_type (expr_type e)) /\
    (lowered_value_type cenv e = vtyp \/ is_bytestring_type vtyp) /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    evaluate_type (get_tenv cx) vtyp = SOME tyv /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME ltv /\
    type_memory_bytes cenv vtyp = type_memory_size tyv /\
    0 < type_memory_size tyv /\ type_memory_size tyv + 64 < dimword (:256) /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size ltv /\
    0 < type_memory_size ltv /\ type_memory_size ltv < dimword (:256) /\
    (!gs v es1.
       (do tv <- eval_expr cx e; read_result cx tv od) (es with gas_obs := gs) =
         (INL v, es1) ==>
       value_has_type tyv v /\ value_has_type ltv v) /\
    (!st0 c st1. declare_local cenv id vtyp st0 = (c, st1) ==>
       expr_sim ctx func c cx (expr_type e) e es /\
       !sa sb op. lower_value compile_expr c (expr_type e) e sa = (op, sb) ==>
                  cs_extends sa sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (AnnAssign id vtyp e))
      (eval_stmt cx (AnnAssign id vtyp e)) es
Proof
  cheat
QED




(* x: T = e for a type T that is not a word type, where e has type T, is
   lowered at T (lowered_value_type, so not a bytestring literal of another
   length) and is not the empty-value form; the sizes as
   compile_annassign_memory_widen_stmt_frag. *)
Theorem compile_annassign_memory_stmt_frag:
  !ctx func cx lctx RetQ cenv ty id vtyp e es tyv.
    cenv.ce_alloca_locals /\
    ~is_word_type vtyp /\ ~(has_length_word vtyp /\ is_empty_value_expr e) /\
    lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    expr_type e = vtyp /\ lowered_value_type cenv e = vtyp /\
    evaluate_type (get_tenv cx) vtyp = SOME tyv /\
    type_memory_bytes cenv vtyp = type_memory_size tyv /\
    0 < type_memory_size tyv /\ type_memory_size tyv + 64 < dimword (:256) /\
    (!gs tv es1. eval_expr cx e (es with gas_obs := gs) = (INL tv, es1) ==>
                 ?v. tv = Value v /\ value_has_type tyv v) /\
    (!st0 c st1. declare_local cenv id vtyp st0 = (c, st1) ==>
       expr_sim ctx func c cx (expr_type e) e es /\
       !sa sb op. lower_value compile_expr c (expr_type e) e sa = (op, sb) ==>
                  cs_extends sa sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (AnnAssign id vtyp e))
      (eval_stmt cx (AnnAssign id vtyp e)) es
Proof
  cheat
QED
