(* Shared allocated staging payload for both nonvoid return modes. *)
Theory bodyIntCallFamCallIntEntryAllocatedEndpoint
Ancestors
  bodyIntCallFamCallIntEntryHeadStage bodyIntCallJointContract
  fnFrameBoundaryGenRet

val completed = ``\cx start current ty flag v op s.
  ?tv w. evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_operand op s = SOME w /\
    (!x. op = Var x ==> not_fresh_at current x) /\
    (if flag then is_word_type ty /\ w = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n w) s.vs_memory /\
       ?aid len. FLOOKUP s.vs_allocas aid = SOME (w2n w,len) /\
         start.cs_next_id <= aid /\ aid < current.cs_next_id /\
         type_memory_size tv <= len /\ w2n w + len <= s.vs_alloca_next /\
         w2n w + len < dimword (:256))``;
val completed_prefix = ``\cx start current tys flags values ops s.
  LENGTH flags = LENGTH tys /\ LENGTH values = LENGTH tys /\
  LENGTH ops = LENGTH tys /\ !i. i < LENGTH tys ==>
    ^completed cx start current (EL i tys) (EL i flags)
      (EL i values) (EL i ops) s``;
val deferred = ``\fp ce e vv r b es s.
  ?a. vv_holds ce fp.jc_cx (post_value_type ce e) r vv es s /\
    vv_at ce fp.jc_cx (post_value_type ce e) a b es r vv s /\
    (post_value_type ce e <> expr_type e ==>
      vv_own ce fp.jc_cx (post_value_type ce e) a b es r vv s) /\
    vv_storage_live fp.jc_cx vv es s /\
    (!x. vv_operand vv = Var x ==> not_fresh_at b x) /\
    (post_value_type ce e <> NoneT /\
     ~is_word_type (post_value_type ce e) /\
     ~is_bytestring_type (post_value_type ce e) /\
     (case vv of StackValue _ _ => T
               | LocatedValue _ p => p.ptr_location = LocMemory) ==>
     !tv. evaluate_type (get_tenv fp.jc_cx) (post_value_type ce e) = SOME tv ==>
       ?w off len. eval_operand (vv_operand vv) s = SOME w /\
         off <= w2n w /\ w2n w + type_memory_size tv <= off + len /\
         off + len < dimword (:256) /\
         (fp.jc_lo <= off \/
          ?base size. fp.jc_staged base size /\ base <= off /\
                      off + len <= base + size))``;
val deferred_list = ``\fp ce ds vs rs b es s.
  LENGTH ds = LENGTH vs /\ LENGTH ds = LENGTH rs /\
  !i. i < LENGTH ds ==>
    ^deferred fp ce (EL i ds) (EL i vs) (EL i rs) b es s``;
val staged_regions = ``\cx ds flags ops s.
  !i j ti tj w z. i < j /\ j < LENGTH ds /\ ~EL i flags /\ ~EL j flags /\
    evaluate_type (get_tenv cx) (expr_type (EL i ds)) = SOME ti /\
    evaluate_type (get_tenv cx) (expr_type (EL j ds)) = SOME tj /\
    eval_operand (EL i ops) s = SOME w /\ eval_operand (EL j ops) s = SOME z ==>
    regions_disjoint (w2n w) (type_memory_size ti) (w2n z) (type_memory_size tj)``;
val allocation_origin = ``\func start bound op tv s.
  ?aid len inst w. eval_operand op s = SOME w /\
    FLOOKUP s.vs_allocas aid = SOME (w2n w,len) /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = aid /\ start.cs_next_id <= aid /\ aid < bound.cs_next_id /\
    type_memory_size tv <= len``;

Theorem intcall_allocated_staged_endpoint:
  compile_alloc_buffer sz a = (buf,b) /\
  compile_stage_intcall_args ce vs flags (MAP expr_type ds) b = (ops,c) /\
  LENGTH vs = LENGTH ds /\ LENGTH rs = LENGTH ds /\
  LENGTH values = LENGTH ds /\ LENGTH flags = LENGTH ds /\
  ^deferred_list fp ce ds vs rs a es t /\
  (!i. i < LENGTH ds ==>
    post_value_type ce (EL i ds) = expr_type (EL i ds) /\
    vv_type (EL i vs) = expr_type (EL i ds) /\
    read_result fp.jc_cx (EL i rs) es = (INL (EL i values),es) /\
    (EL i flags ==> is_word_type (expr_type (EL i ds))) /\
    ?tv. evaluate_type (get_tenv fp.jc_cx) (expr_type (EL i ds)) = SOME tv /\
      type_memory_bytes ce (expr_type (EL i ds)) = type_memory_size tv /\
      type_memory_size tv < 2**64 /\ value_has_type tv (EL i values) /\
      (~EL i flags ==> val_wf tv (EL i values))) /\
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es a t /\
  fn_has_code a b fp.jc_func /\ fn_has_code b c fp.jc_func /\
  fn_inst_ids_distinct fp.jc_func /\ sz < dimword (:256) /\
  sa.cs_next_id <= a.cs_next_id /\ c.cs_next_id <= sb.cs_next_id /\
  ~t.vs_halted /\ t.vs_current_bb = a.cs_current_bb /\
  t.vs_inst_idx = LENGTH a.cs_current_insts ==>
  LENGTH ops = LENGTH ds /\
  ?u w argv. gas_marked_path F fp.jc_ctx fp.jc_func t 0 (OK u) /\
    intcall_expr_cont fp ce env es a t es c u /\
    ^staged_regions fp.jc_cx ds flags ops u /\
    ^completed_prefix fp.jc_cx a c (MAP expr_type ds) flags values ops u /\
    (!i tv. i < LENGTH ds /\ ~EL i flags /\
      evaluate_type (get_tenv fp.jc_cx) (expr_type (EL i ds)) = SOME tv ==>
      ^allocation_origin fp.jc_func b c (EL i ops) tv u /\
      ^allocation_origin fp.jc_func sa sb (EL i ops) tv u) /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas a.cs_next_id = SOME (w2n w,sz) /\
    fp.jc_lo <= w2n w /\ w2n w + sz < dimword (:256) /\
    a.cs_next_id < b.cs_next_id /\ buf.buf_size = sz /\
    w2n w + sz <= u.vs_alloca_next /\
    (?inst. MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id = a.cs_next_id) /\
    (!aid q len p k. b.cs_next_id <= aid /\
      FLOOKUP u.vs_allocas aid = SOME (q,len) /\ q <= p /\ p+k <= q+len ==>
      regions_disjoint (w2n w) sz p k) /\
    eval_operands ops u = SOME argv /\ LENGTH argv = LENGTH ds /\
    (!i z. i < LENGTH ds /\ eval_operand (EL i ops) u = SOME z ==>
      EL i argv = z)
Proof
  strip_tac >> drule_all intcall_allocated_list_stage_endpoint >> strip_tac >>
  `alloca_inv u` by
    fs[intcall_expr_cont_def, intcall_expr_res_def,
       exprLoweringPropsTheory.stmt_state_rel_def] >>
  drule_all intcall_allocated_buffer_geometry >> strip_tac >>
  `w2n w + sz <= u.vs_alloca_next` by
    metis_tac[venomMemDefsTheory.alloca_inv_def,
              venomMemDefsTheory.alloca_next_valid_def] >>
  drule intcall_completed_operands >> simp[] >> strip_tac >>
  RULE_ASSUM_TAC BETA_RULE >>
  qexistsl_tac [`u`, `w`, `argv`] >> BETA_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qpat_x_assum `LENGTH flags = LENGTH (MAP expr_type ds) /\ _`
        (mp_tac o cj 4) >>
      simp_tac std_ss [listTheory.LENGTH_MAP,
        AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!i tv. _ ==> _` (drule_all_then strip_assume_tac) >>
      conj_tac >- metis_tac[] >>
      rename1 `origin.inst_id = aid` >>
      qexistsl_tac [`len`, `origin`, `w'`] >>
      asm_simp_tac std_ss [] >> decide_tac) >>
  RULE_ASSUM_TAC (SIMP_RULE std_ss
    [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- metis_tac[] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

(* Operand prefixing is independent of the return convention.  In particular,
   [] handles stack returns and [buf.buf_operand] handles buffer returns. *)
Theorem intcall_staged_operand_prefix:
  eval_operands prefix u = SOME heads /\
  eval_operands ops u = SOME tail /\ LENGTH tail = n /\
  (!i z. i < n /\ eval_operand (EL i ops) u = SOME z ==> EL i tail = z) ==>
  eval_operands (prefix ++ ops) u = SOME (heads ++ tail) /\
  LENGTH (heads ++ tail) = LENGTH prefix + n /\
  (!i z. i < n /\ eval_operand (EL i ops) u = SOME z ==>
    EL (LENGTH prefix + i) (heads ++ tail) = z)
Proof
  strip_tac >>
  `LENGTH heads = LENGTH prefix` by
    metis_tac[tupleLoadPropsTheory.eval_operands_length] >>
  simp[fnFrameBoundaryGenRetTheory.eval_operands_append,
       listTheory.EL_APPEND_EQN]
QED

Theorem intcall_buffer_operand_prefix:
  eval_operand buf.buf_operand u = SOME w /\
  eval_operands ops u = SOME tail /\ LENGTH tail = n /\
  (!i z. i < n /\ eval_operand (EL i ops) u = SOME z ==> EL i tail = z) /\
  buf.buf_size = sz /\ type_memory_size rtv <= sz /\
  w2n w + sz <= u.vs_alloca_next ==>
  eval_operands ([buf.buf_operand] ++ ops) u = SOME (w::tail) /\
  LENGTH (w::tail) = LENGTH [buf.buf_operand] + n /\
  (!i z. i < n /\ eval_operand (EL i ops) u = SOME z ==>
    EL (LENGTH [buf.buf_operand] + i) (w::tail) = z) /\
  HD (w::tail) = n2w (w2n w) /\
  type_memory_size rtv <= buf.buf_size /\
  w2n (HD (w::tail)) + type_memory_size rtv <= u.vs_alloca_next
Proof
  strip_tac >>
  `eval_operands [buf.buf_operand] u = SOME [w]` by
    simp[venomStateTheory.eval_operands_def] >>
  drule_all intcall_staged_operand_prefix >>
  simp[] >> decide_tac
QED
