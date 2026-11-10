(* Consumer interface probes, not a staging execution theorem. *)
Theory bodyIntCallFamCallIntStageInterface
Ancestors
  bodyIntCallFamCallIntForcingTransport bodyIntCallFamCallIntStageAdapters
  bodyIntCallFamCallIntFlags placeMemoryStaging abiCallerAllocation
  bodyIntCallJointContract

(* ML abbreviations only.  start is the start of the ENTIRE staging list,
   not the start of the most recent allocation or forcing fragment. *)
val completed = ``\cx start current ty flag v op s.
  ?tv w. evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_operand op s = SOME w /\
    (!x. op = Var x ==> not_fresh_at current x) /\
    (if flag then is_word_type ty /\ w = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n w) s.vs_memory /\
       ?aid len. FLOOKUP s.vs_allocas aid = SOME (w2n w,len) /\
         start.cs_next_id <= aid /\ aid < current.cs_next_id /\
         type_memory_size tv <= len /\
         w2n w + len <= s.vs_alloca_next /\
         w2n w + len < dimword (:256))``;

val completed_prefix = ``\cx start current tys flags values ops s.
  LENGTH flags = LENGTH tys /\ LENGTH values = LENGTH tys /\
  LENGTH ops = LENGTH tys /\
  !i. i < LENGTH tys ==>
    ^completed cx start current (EL i tys) (EL i flags)
      (EL i values) (EL i ops) s``;

Theorem intcall_completed_empty:
  ^completed_prefix cx start current [] [] [] [] s
Proof
  simp[]
QED

(* No wordness is inferred from vv_holds here.  Calling convention supplies
   wordness of ty separately (intcall_argument_flags). *)
Theorem intcall_completed_stack_singleton:
  evaluate_type (get_tenv cx) ty = SOME tv /\ is_word_type ty /\
  eval_operand op s = SOME (typed_val_to_w256 tv v) /\
  (!x. op = Var x ==> not_fresh_at current x) ==>
  ^completed_prefix cx start current [ty] [T] [v] [op] s
Proof
  simp[] >> strip_tac >> qexists `tv` >> simp[]
QED

(* Allocation supplies len=MAX 32 size, not len=size.  alloca_inv gives
   the non-strict frontier bound; the allocator gives the strict word bound.
   Value representation is supplied at the SAME endpoint by the store. *)
Theorem intcall_completed_memory_singleton:
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand op s = SOME w /\
  (!x. op = Var x ==> not_fresh_at current x) /\
  val_in_memory tv v (w2n w) s.vs_memory /\
  FLOOKUP s.vs_allocas aid = SOME (w2n w,MAX 32 (type_memory_size tv)) /\
  alloca_inv s /\ start.cs_next_id <= aid /\ aid < current.cs_next_id /\
  w2n w + MAX 32 (type_memory_size tv) < dimword (:256) ==>
  ^completed_prefix cx start current [ty] [F] [v] [op] s
Proof
  simp[] >> strip_tac >> qexistsl [`aid`, `MAX 32 (type_memory_size tv)`] >>
  simp[arithmeticTheory.ADD_COMM] >> irule abi_caller_allocation_end >>
  simp[] >> qexistsl [`MAX 32 (type_memory_size tv)`, `aid`, `w2n w`] >> simp[]
QED

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

(* Candidate only: a parsed HOL term, NOT an asserted theorem.
   Premise provenance, with outstanding proof obligations made explicit:
   - compiler equality/code/distinct/entry: decomposition of the outer Call;
   - frame/body/joint: outer producer and deferred traversal endpoint;
   - deferred_list: intcall_deferred_traverse (endpoint certificates);
   - read_results: the successful source Call branch, at fixed es;
   - flags/wordness: intcall_argument_flags, exact declaration/actual types;
   - MAP vv_type: intcall_pure_multi_vvs_tags, retained from evaluation;
   - per-member layout/value facts below: STILL TO BE PACKAGED from source
     typing, body_inv and vv_holds/read_result. They are not consequences
     of W alone, and this quotation does not pretend to prove them.
     In particular both post and declared sizes need the 2**64 bound.
   - metadata: body_inv/supported_program; no new invariant is postulated
     at each recursive execution. The unequal-layout store needs this.
   - Win: old allocation witnesses are supplied by the caller; completed
     output allocations are added only during the induction.
   The probes above validate only the completed-prefix representation.
   They do not validate availability of all premises or full execution. *)
val staging_candidate = ``
  compile_stage_intcall_args ce vs flags (MAP expr_type ds) sa = (ops,sb) /\
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  intcall_expr_res fp ce env es sa s /\
  ^deferred_list fp ce ds vs rs sa es s /\
  read_results fp.jc_cx rs es = (INL values,es) /\
  LENGTH flags = LENGTH ds /\ MAP vv_type vs = MAP expr_type ds /\
  (!i. i < LENGTH ds /\ EL i flags ==> is_word_type (expr_type (EL i ds))) /\
  (!i. i < LENGTH ds ==> ?stv dtv.
    evaluate_type (get_tenv fp.jc_cx) (post_value_type ce (EL i ds)) = SOME stv /\
    evaluate_type (get_tenv fp.jc_cx) (expr_type (EL i ds)) = SOME dtv /\
    type_memory_bytes ce (post_value_type ce (EL i ds)) = type_memory_size stv /\
    type_memory_bytes ce (expr_type (EL i ds)) = type_memory_size dtv /\
    type_memory_size stv < 2**64 /\ type_memory_size dtv < 2**64 /\
    value_has_type stv (EL i values) /\ value_has_type dtv (EL i values) /\
    val_wf stv (EL i values) /\ val_wf dtv (EL i values) /\
    type_widens_to (get_tenv fp.jc_cx) (post_value_type ce (EL i ds))
      (expr_type (EL i ds))) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv fp.jc_cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv.
      evaluate_type (get_tenv fp.jc_cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  (!ty tv. evaluate_type (get_tenv fp.jc_cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!p k. Win p k ==> ?aid b len. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= p /\ p+k <= b+len) ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    intcall_expr_cont fp ce env es sa s es sb u /\ LENGTH ops = LENGTH ds /\
    ^completed_prefix fp.jc_cx sa sb (MAP expr_type ds) flags values ops u /\
    (!p k. Win p k ==>
      mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory)``;

Theorem intcall_stage_empty_endpoint:
  intcall_expr_res fp ce env es sa s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  compile_stage_intcall_args ce [] [] [] sa = ([],sa) /\
  gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK s) /\
  intcall_expr_cont fp ce env es sa s es sa s /\
  ^completed_prefix fp.jc_cx sa sa [] [] [] [] s /\
  (!p k. Win p k ==> mem_bytes_at p k s.vs_memory = mem_bytes_at p k s.vs_memory)
Proof
  simp[exprLoweringTheory.compile_stage_intcall_args_def,
       compileEnvTheory.comp_return_def, fragGasModeTheory.gas_marked_path_def,
       intcall_expr_cont_def, loweringPostsTheory.locals_kept_def] >>
  metis_tac[fragGasPathTheory.gas_path_rules]
QED
