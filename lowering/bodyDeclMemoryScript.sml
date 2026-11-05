(* Declaration store: source-state and memory continuation boundaries. *)
Theory bodyDeclMemory
Ancestors
  loweringPosts
  bodyNameMemoryFacts
  bodyCopyMemory bodyMemoryDefs stmtSimDeclMem localPtrsProps stmtSimDeclStore
  stmtSimDecl valueCopy valueCopyBytes exprOperandVar freshWrites
  valueTypingMemoryProps vyperTyping exprSimDefs stmtSimDefs venomState
  valueEncoding valueEncodingProofs intCallResult compileEnv exprLoweringProps
  loweringSlice exprLowering exprSimBufferStore valueEncodingProofs
  words venomExecSemantics stmtLowering context fragExec fragExecMem
  allocaHistoryFragment list rich_list emitHelper emitHelperProps venomInst
  exprSimLiteralBuffer exprSimAlloc exprSimBuffer finite_map bodySimDeclCases allocLimits
  bodySim exprSimHyps vyperTypeSystem vyperTypeInvariants memoryLocalRhsProps
  supportedStmtTraverse supportedExprTraverse vyperTypeCallGraph vyperTypeCallStackSoundness
  vyperInterpreter vyperState

Theorem body_stmt_state_rel_declare_store_frame:
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

Theorem body_typed_store_memory_mem_ok:
  compile_store_memory ce src dst ann ann sa = ((),sb) /\
  ~is_word_type ann /\ evaluate_type tenv ann = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n w) s.vs_memory /\
  type_memory_bytes ce ann = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  eval_operand src s = SOME w /\ eval_operand dst s = SOME d /\
  w2n w + type_memory_size tv <= s.vs_alloca_next /\
  w2n d + type_memory_size tv <= s.vs_alloca_next /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  cheat
QED

Theorem body_store_memory_history[local]:
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  cheat
QED

Theorem body_decl_frag_at_cursor[local]:
  !ctx st st' P Q R.
    st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
    isPREFIX st.cs_current_insts st'.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st st') /\
    (!s. P s /\ ~s.vs_halted /\
       s.vs_current_bb = st.cs_current_bb /\
       s.vs_inst_idx = LENGTH st.cs_current_insts ==>
       run_inst_seq_mem_ok (emitted_insts st st') s /\
       ?t. run_inst_seq (emitted_insts st st') s = OK t /\
           Q (t with vs_inst_idx := LENGTH st'.cs_current_insts)) ==>
    frag_exec_mem ctx st st' P Q R
Proof
  cheat
QED

Theorem annassign_memory_store_body_frag_mem:
  !ctx func cenv cx es s id p sz w inst v tyv sc rest a src ty sa sb sw d R.
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
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
    w2n sw + type_memory_size tyv <= s.vs_alloca_next /\
    w2n w + type_memory_size tyv <= s.vs_alloca_next /\
    alloca_history func s /\ return_buf_frame d cenv sa s ==>
    frag_exec_mem ctx sa sb (\u. u = s)
      (\t. stmt_state_rel ctx func cenv cx
          (es with scopes :=
            (sc |+ (id, <|assignable := a; type := tyv; value := v; popped := []|>)) :: rest) t /\
        alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
        return_buf_frame d cenv sb t /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)) R
Proof
  cheat
QED

(* Scratch copy preserves all source-level live regions. *)
Theorem body_stmt_state_rel_mcopy_alloca:
  !func cenv cx es s inst p dst src sz ctx.
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    not_local_ptr cenv es.scopes p /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (dst, sz) ==>
    stmt_state_rel ctx func cenv cx es (mcopy dst src sz s)
Proof
  cheat
QED

Theorem body_scratch_alloc_operand[local]:
  compile_alloc_buffer n sa = (buf,sm) ==>
  buf.buf_operand = Var (STRING #"%" (toString sa.cs_next_var))
Proof
  cheat
QED

Theorem body_scratch_copy_state[local]:
  compile_alloc_buffer n sa = (buf,sm) /\ fn_has_code sa sm func /\
  stmt_state_rel ctx func ce cx es a /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  FLOOKUP a.vs_allocas sa.cs_next_id = SOME (w2n w,n) /\
  run_inst_seq (emitted_insts sm sn) a = OK t /\
  compile_copy_memory buf.buf_operand src n sm = ((),sn) /\
  eval_operand buf.buf_operand a = SOME w /\ eval_operand src a = SOME sw /\
  n < dimword (:256) ==>
  stmt_state_rel ctx func ce cx es t
Proof
  cheat
QED

Theorem body_scratch_prefix_run[local]:
  compile_alloc_buffer n sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand src n sm = ((),sn) /\
  fn_has_code sa sm func /\ stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ n < dimword (:256) /\
  w2n sw + n <= s.vs_alloca_next /\
  val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= n ==>
  ?a t w. run_inst_seq (emitted_insts sa sm) s = OK a /\
    run_inst_seq (emitted_insts sm sn) a = OK t /\
    run_inst_seq_mem_ok (emitted_insts sa sm) s /\
    run_inst_seq_mem_ok (emitted_insts sm sn) a /\
    stmt_state_rel ctx func ce cx es t /\
    eval_operand buf.buf_operand t = SOME w /\
    val_in_memory tv v (w2n w) t.vs_memory /\
    w2n w + n <= t.vs_alloca_next /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)
Proof
  cheat
QED

Theorem body_scratch_prefix_shape[local]:
  compile_alloc_buffer n sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand src n sm = ((),sn) ==>
  same_blocks sa sn /\
  sn.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sn /\
  emitted_insts sa sn = emitted_insts sa sm ++ emitted_insts sm sn /\
  cs_extends sa sm /\ cs_extends sm sn /\
  sa.cs_next_var <= sn.cs_next_var /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sn)
Proof
  cheat
QED

Theorem compile_scratch_prefix_body_frag_mem:
  !ctx func ce cx es s sa sm sn buf src n sw tv v d R.
    compile_alloc_buffer n sa = (buf,sm) /\
    compile_copy_memory buf.buf_operand src n sm = ((),sn) /\
    fn_has_code sa sn func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s /\
    alloca_history func s /\ return_buf_frame d ce sa s /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ n < dimword (:256) /\
    w2n sw + n <= s.vs_alloca_next /\
    val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
    val_footprint tv v <= n ==>
    frag_exec_mem ctx sa sn (\u. u = s)
      (\t. stmt_state_rel ctx func ce cx es t /\ alloca_history func t /\
        return_buf_frame d ce sn t /\ s.vs_alloca_next <= t.vs_alloca_next /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        val_wf tv v /\ ?w. eval_operand buf.buf_operand t = SOME w /\
          val_in_memory tv v (w2n w) t.vs_memory /\
          w2n w + n <= t.vs_alloca_next) R
Proof
  cheat
QED

Theorem annassign_memory_assign_body_frag_mem:
  !ctx func cenv cx es s id p sz w inst v tyv sc rest a src ty sa sb sw d R info bytes.
    compile_assign_value cenv (Var p) LocMemory src F (SOME LocMemory)
      ty ty info bytes sa = ((), sb) /\
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
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
    w2n sw + type_memory_size tyv <= s.vs_alloca_next /\
    w2n w + type_memory_size tyv <= s.vs_alloca_next /\
    alloca_history func s /\ return_buf_frame d cenv sa s ==>
    frag_exec_mem ctx sa sb (\u. u = s)
      (\t. stmt_state_rel ctx func cenv cx
          (es with scopes :=
            (sc |+ (id, <|assignable := a; type := tyv; value := v; popped := []|>)) :: rest) t /\
        alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
        return_buf_frame d cenv sb t /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)) R
Proof
  cheat
QED

Theorem annassign_setup_shape:
  declare_local ce id ty sa = (c,st) /\ ce.ce_alloca_locals /\
  lookup_scopes id es.scopes = NONE /\
  (!l. FLOOKUP ce.ce_vars id = SOME l ==> ?q sz. l = PtrVar q sz) /\
  p = STRING #"%" (toString sa.cs_next_var) /\
  emit_inst ALLOCA [Lit (n2w (type_memory_bytes ce ty))] [p] st = ((),sA) /\
  fn_has_code sa sA func /\ local_ptrs_reserved ce sa ==>
  st = sa with cs_next_var := sa.cs_next_var + 1 /\
  FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes ce ty)) /\
  c.ce_return_buf = ce.ce_return_buf /\
  not_local_ptr c es.scopes p /\
  (!x. not_fresh_at sa x ==> x <> p) /\
  local_ptrs_reserved c sA /\ not_fresh_at sA p /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes ce ty))] [p])
    (fn_insts func)
Proof
  cheat
QED

Theorem body_decl_alloca_run[local]:
  stmt_state_rel ctx func c cx es s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit (n2w sz)] /\ inst.inst_outputs = [p] /\
  not_local_ptr c es.scopes p /\ sz < dimword (:256) ==>
  ?t w. exec_alloca inst s (n2w sz : bytes32) = OK t /\
    stmt_state_rel ctx func c cx es t /\ lookup_var p t = SOME w /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
    w2n w + sz <= t.vs_alloca_next /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (!x. x <> p ==> lookup_var x t = lookup_var x s) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)
Proof
  cheat
QED

Theorem annassign_setup_body_frag_mem:
  !ctx func ce c cx es s sa st sA id ty p d R.
    declare_local ce id ty sa = (c,st) /\ ce.ce_alloca_locals /\
    lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP ce.ce_vars id = SOME l ==> ?q sz. l = PtrVar q sz) /\
    p = STRING #"%" (toString sa.cs_next_var) /\
    emit_inst ALLOCA [Lit (n2w (type_memory_bytes ce ty))] [p] st = ((),sA) /\
    type_memory_bytes ce ty < dimword (:256) /\
    fn_has_code sa sA func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s /\
    alloca_history func s /\ return_buf_frame d ce sa s ==>
    frag_exec_mem ctx sa sA (\u. u = s)
      (\t. stmt_state_rel ctx func c cx es t /\ alloca_history func t /\
        return_buf_frame d c sA t /\ s.vs_alloca_next <= t.vs_alloca_next /\
        local_ptrs_reserved c sA /\ not_fresh_at sA p /\
        FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes ce ty)) /\
        not_local_ptr c es.scopes p /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
        ?w. lookup_var p t = SOME w /\
          FLOOKUP t.vs_allocas st.cs_next_id = SOME (w2n w,type_memory_bytes ce ty) /\
          w2n w + type_memory_bytes ce ty <= t.vs_alloca_next) R
Proof
  cheat
QED

Theorem annassign_name_rhs_body_frag_mem:
  !ctx func cenv cx env source_id es s id p sz w inst v tyv sc rest a src ty sa sm sb d R info bytes.
    lower_value compile_expr cenv ty (Name ty source_id) sa = (src,sm) /\
    expr_sim_pre cenv cx env (Name ty source_id) es /\
    (do result <- eval_expr cx (Name ty source_id); read_result cx result od) es = (INL v,es) /\
    compile_assign_value cenv (Var p) LocMemory src F (SOME LocMemory)
      ty ty info bytes sm = ((), sb) /\
    not_fresh_at sa p /\ lookup_var p s = SOME w /\
    ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tyv /\
    type_memory_bytes cenv ty = type_memory_size tyv /\
    type_memory_size tyv <= sz /\ type_memory_size tyv + 64 < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
    w2n w + type_memory_size tyv <= s.vs_alloca_next /\
    alloca_history func s /\ return_buf_frame d cenv sa s ==>
    frag_exec_mem ctx sa sb (\u. u = s)
      (\t. stmt_state_rel ctx func cenv cx
          (es with scopes :=
            (sc |+ (id, <|assignable := a; type := tyv; value := v; popped := []|>)) :: rest) t /\
        alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
        return_buf_frame d cenv sb t /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)) R
Proof
  cheat
QED

Theorem body_annassign_name_compiler_parts[local]:
  !c lctx ret_ty id typ source_id p sz st sb.
    compile_stmt c lctx ret_ty (AnnAssign id typ (Name typ source_id)) st = ((),sb) /\
    FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) sz) /\ ~is_word_type typ ==>
    ?sA sV sB vv op.
      emit_inst ALLOCA [Lit (n2w sz)] [p] st = ((),sA) /\
      compile_expr c typ (Name typ source_id) sA = (vv,sV) /\
      unwrap_value c vv sV = (op,sB) /\
      lower_value compile_expr c typ (Name typ source_id) sA = (op,sB) /\
      compile_assign_value c (Var p) LocMemory op F (vv_location vv)
        typ (lowered_value_type c (Name typ source_id))
        (case typ of ArrayT elem_ty (Dynamic _) =>
          SOME ((type_memory_bytes c elem_ty + 31) DIV 32,type_memory_bytes c elem_ty)
        | _ => NONE) (type_memory_bytes c typ) sB = ((),sb)
Proof
  cheat
QED

Theorem body_name_nonword_compile[local]:
  expr_sim_pre ce cx env (Name ty name) es /\ ~is_word_type ty ==>
  ?p sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\
    !sa. lower_value compile_expr ce ty (Name ty name) sa = (Var p,sa)
Proof
  cheat
QED

Theorem body_annassign_read_eval[local]:
  evaluate_type (get_tenv cx) ty = SOME tyv /\
  (do tv <- eval_expr cx e; read_result cx tv od) es = (INL v,es) /\
  lookup_scopes id es.scopes = NONE /\ es.scopes = sc :: rest ==>
  eval_stmt cx (AnnAssign id ty e) es =
    (INL (), es with scopes :=
      (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest)
Proof
  cheat
QED

Theorem body_annassign_name_exec[local]:
  declare_local ce id ty sa = (c,st) /\ ce.ce_alloca_locals /\
  lookup_scopes id es.scopes = NONE /\ FLOOKUP ce.ce_vars id = NONE /\
  p = STRING #"%" (toString sa.cs_next_var) /\
  emit_inst ALLOCA [Lit (n2w (type_memory_bytes ce ty))] [p] st = ((),sA) /\
  (!u. lower_value compile_expr c ty (Name ty source_id) u = (src,u)) /\
  compile_assign_value c (Var p) LocMemory src F (SOME LocMemory)
    ty ty info bytes sA = ((),sb) /\
  expr_sim_pre c cx env (Name ty source_id) es /\
  (do result <- eval_expr cx (Name ty source_id); read_result cx result od) es = (INL v,es) /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tyv /\
  type_memory_bytes c ty = type_memory_size tyv /\
  type_memory_bytes ce ty = type_memory_size tyv /\
  type_memory_size tyv + 64 < dimword (:256) /\ es.scopes = sc :: rest /\
  fn_has_code sa sA func /\ fn_has_code sA sb func /\
  cs_extends sa sA /\ cs_extends sA sb /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s /\
  alloca_history func s /\ return_buf_frame d ce sa s ==>
  frag_exec_mem ctx sa sb (\u. u = s)
    (\t. stmt_state_rel ctx func c cx
        (es with scopes :=
          (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest) t /\
      alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
      return_buf_frame d c sb t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)) R
Proof
  cheat
QED

Theorem body_annassign_name_prepare[local]:
  body_inv tops ctx ce cx /\
  supported_stmt tops bindings (AnnAssign id ty (Name ty source_id)) /\
  expr_sim_inv ce cx env es /\ ce_locals_declared ce env /\
  locals_alloc_ok ce env /\
  type_stmt env ret_ty (AnnAssign id ty (Name ty source_id)) = SOME env' /\
  stmt_exprs_ok ce (AnnAssign id ty (Name ty source_id)) /\
  call_evaluation_safe cx (int_calls_stmt (AnnAssign id ty (Name ty source_id))) /\
  eval_stmt cx (AnnAssign id ty (Name ty source_id)) es = (res,es') /\
  ~is_word_type ty /\ 0 < type_memory_bytes ce ty /\
  stmt_env ce lctx ret_ty (AnnAssign id ty (Name ty source_id)) sa = (c,sb) ==>
  ?tyv v sc rest st sA src info.
    res = INL () /\
    es' = es with scopes :=
      (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest /\
    es.scopes = sc :: rest /\ cenv_top_ext ce c es'.scopes /\
    ce.ce_alloca_locals /\ FLOOKUP ce.ce_vars id = NONE /\
    lookup_scopes id es.scopes = NONE /\
    declare_local ce id ty sa = (c,st) /\
    emit_inst ALLOCA [Lit (n2w (type_memory_bytes ce ty))]
      [STRING #"%" (toString sa.cs_next_var)] st = ((),sA) /\
    (!u. lower_value compile_expr c ty (Name ty source_id) u = (src,u)) /\
    compile_assign_value c (Var (STRING #"%" (toString sa.cs_next_var)))
      LocMemory src F (SOME LocMemory) ty ty info (type_memory_bytes ce ty) sA = ((),sb) /\
    expr_sim_pre c cx env (Name ty source_id) es /\
    (do result <- eval_expr cx (Name ty source_id); read_result cx result od) es = (INL v,es) /\
    evaluate_type (get_tenv cx) ty = SOME tyv /\
    type_memory_bytes c ty = type_memory_size tyv /\
    type_memory_bytes ce ty = type_memory_size tyv /\
    type_memory_size tyv + 64 < dimword (:256)
Proof
  cheat
QED

Theorem body_annassign_name_code[local]:
  declare_local ce id ty sa = (c,st) /\ ce.ce_alloca_locals /\
  FLOOKUP ce.ce_vars id = NONE /\ local_ptrs_reserved ce sa /\
  emit_inst ALLOCA [Lit (n2w (type_memory_bytes ce ty))]
    [STRING #"%" (toString sa.cs_next_var)] st = ((),sA) /\
  compile_assign_value c (Var (STRING #"%" (toString sa.cs_next_var)))
    LocMemory src F (SOME LocMemory) ty ty info bytes sA = ((),sb) /\
  0 < type_memory_bytes c ty /\ fn_has_code sa sb func ==>
  cs_extends sa sA /\ cs_extends sA sb /\
  fn_has_code sa sA func /\ fn_has_code sA sb func /\ ~block_is_terminated sb
Proof
  cheat
QED

Theorem body_decl_normal_landing[local]:
  frag_exec_mem ctx sa sb (\u. u = s0)
    (\s. stmt_state_rel ctx func c cx es' s /\ alloca_history func s /\
      s0.vs_alloca_next <= s.vs_alloca_next /\ return_buf_frame d c sb s /\
      (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x s0) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b)) (\r. F) /\
  fn_has_code sa sb func /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~block_is_terminated sb /\ cenv_top_ext ce c es'.scopes ==>
  ?s c'. stmt_lands lctx sb (INL ()) s /\ ~s.vs_halted /\
    (~block_is_terminated sb /\ c' = c) /\
    cenv_top_ext ce c' es'.scopes /\ stmt_state_rel ctx func c' cx es' s /\
    alloca_history func s /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
    return_buf_frame d c' sb s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    !fuel r. run_from fuel ctx func s = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx func s0 = r /\
        (mem_safe_run fuel ctx func s ==> mem_safe_run fuel' ctx func s0)
Proof
  cheat
QED

Theorem body_annassign_name_mem:
  !d tops bindings ctx func cenv cx env env' ret_ty lctx RetQ id typ source_id es.
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AnnAssign id typ (Name typ source_id)) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AnnAssign id typ (Name typ source_id)) = SOME env' /\
    stmt_exprs_ok cenv (AnnAssign id typ (Name typ source_id)) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ (Name typ source_id))) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    ~is_word_type typ /\ 0 < type_memory_bytes cenv typ ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ (Name typ source_id)))
      (eval_stmt cx (AnnAssign id typ (Name typ source_id))) es
Proof
  cheat
QED

