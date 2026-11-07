(*
 * Hashing builtins (#636)
 *
 * keccak256, sha256 and method_id read a bytestring operand through its
 * pointer and hash it into a buffer of their own: SHA3, a STATICCALL to
 * the sha256 precompile, or keccak then a SHR/SHL by 224 for method_id.
 * The code runs, keeps stmt_state_rel and changes no memory but its own
 * buffers.  A literal method_id signature is folded to a bytes literal.
 *
 * Composing the operand's fragment with that code needs its operand to
 * survive, which exprOperandVar's compile_lower_value_var gives.
 *
 * TOP-LEVEL:
 *   hash_builtin_types — a well-typed keccak256, sha256 or method_id has
 *     one bytes or string argument and the expected result type
 *   compile_expr_method_id_literal, eval_expr_method_id_literal — a
 *     literal signature compiles and evaluates to its 4-byte selector
 *   compile_keccak256_typed_vv_sim, compile_sha256_typed_vv_sim,
 *   compile_method_id_other_typed_vv_sim — expr_vv_sim of the three,
 *     given expr_body_pre and the argument's expr_sim (exprSimBuiltins'
 *     case lemmas)
 *
 * Helpers: byte views of val_in_memory, memory frames, the SHA3 and
 *   STATICCALL steps, and the per-builtin runs.
 *)
Theory exprSimHash
Ancestors
  exprBopSimProps
  exprSimVVFrame
  exprSimSource
  exprSimProps
  exprSimHypsDefs
  exprSimDefs
  loweringPosts
  exprSimAlloc
  allocLimits
  list rich_list byte words fragExec ASCIInumbers
  venomExecSemantics venomInst venomState emitHelper emitHelperProps
  builtinHashing exprLoweringProps compileEnv
   exprSimHyps exprSimLiteralBuffer exprSimWordArgs
  vyperTypeSystem valueEncoding valueEncodingProofs extCallOracle
  vyperAST vyperValue exprLowering vyperInterpreter vyperContext
  vyperValueOperation vyperState exprSimWordBuiltins
  vyperTypeInvariants vyperTypeExprResult vyperTypeExprSoundness
  exprOperandVar
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext
  fragGasMode fragGasPath fragGasSeq fragGasSeqAbort

Theorem hash_builtin_types:
  (b = Keccak256 \/ b = Sha256 \/ b = MethodId) /\
  well_typed_builtin_app ty b ts ==>
  ?t. ts = [t] /\ is_bytes_or_string_type t /\
      (if b = MethodId then
         ty = BaseT (BytesT (Dynamic 4)) \/ ty = BaseT (BytesT (Fixed 4))
       else ty = BaseT (BytesT (Fixed 32)))
Proof
  cheat
QED

Theorem sha256_computed_request:
  rq.cr_kind = MessageCall /\ rq.cr_target = 2w /\ rq.cr_value = 0 ==>
  computed_precompile rq /\
  take_outcome rq os =
    (if ?outcome rest. os = outcome::rest /\ outcome.co_success then
       failed_outcome rq with
         <| co_success := T;
            co_returnData := word_to_bytes (SHA_256_bytes rq.cr_data) T |>
     else failed_outcome rq, DROP 1 os) /\
  record_request rq rqs = rqs
Proof
  cheat
QED

(* Covers partial words, including the empty byte sequence. *)
Theorem typed_bytes_prefix:
  LENGTH bs <= 32 ==>
  TAKE (LENGTH bs)
    (word_to_bytes_be
      (typed_val_to_w256 (BaseTV (BytesT bd)) (BytesV bs))) = bs
Proof
  cheat
QED

Theorem expr_val_rel_memory:
  expr_val_rel cx t v op s /\ ~is_word_type t /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  eval_operand op s = SOME w ==>
  val_in_memory tv v (w2n w) s.vs_memory
Proof
  cheat
QED

Theorem expr_val_at_footprint:
  expr_val_at cenv cx t sa sb es v op s /\
  evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t /\
  eval_operand op s = SOME w ==>
  val_wf tv v /\
  ((?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b, sz) /\
      sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
      b <= w2n w /\ w2n w + val_footprint tv v <= b + sz) \/
   (?n b sz. local_region cenv es.scopes s n b sz /\
      b <= w2n w /\ w2n w + val_footprint tv v <= b + sz) \/
   val_footprint tv v = 0)
Proof
  cheat
QED

(* A write contained in one region cannot change any disjoint region. *)
Theorem mstore_region_frame:
  b <= a /\ a + 32 <= b + sz /\ regions_disjoint b sz off len ==>
  mem_bytes_at off len (mstore a w s).vs_memory =
  mem_bytes_at off len s.vs_memory
Proof
  cheat
QED

(* The operand's counted outcome composes with a continuation: every
   successful operand endpoint, reached under some replacement of the gas
   observations, has a counted summary of the continuation, and operand
   exceptions exit as the continuation's R allows. *)
Theorem expr_sim_suffix:
  expr_sim ctx func cenv cx ty e es /\
  lower_value compile_expr cenv ty e sa = (op, sm) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!exc ee r. expr_exit (INR exc : value + exception) r ==> R (INR exc) ee r) /\
  (!gs v ee t.
     bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
       (INL v, ee) /\ ee.gas_obs = [] /\
     expr_post ctx func cenv cx e es sa sm s0 ee v op t /\ ~t.vs_halted /\
     t.vs_current_bb = sm.cs_current_bb /\
     t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
     ?marks. gas_summary_at F (ctx, func) marks (k v) (ee, t) Q R) ==>
  gas_outcome F (cx_tops cx) (ctx, func)
    (bind (bind (eval_expr cx e) (read_result cx)) k) (es, s0) Q R
Proof
  cheat
QED

(* A straight-line run of the emitted code is an actual counted path. *)
Theorem hash_run_path:
  fn_has_code sa sb func /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) insts /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq insts s = OK t ==>
  gas_marked_path F ctx func s (LENGTH (FILTER (\i. i.inst_opcode = GAS) insts))
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb
Proof
  cheat
QED

(* An aborting straight-line run of the emitted code is an actual counted
   path to that abort. *)
Theorem hash_abort_path:
  fn_has_code sa sb func /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) insts /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq insts s = Abort a t ==>
  ?n j. gas_marked_path F ctx func s n (Abort a (t with vs_inst_idx := j))
Proof
  cheat
QED

Theorem step_SHA3_bytes:
  eval_operand ptr_op s = SOME p /\ eval_operand len s = SOME n /\
  mem_bytes_at (w2n p) (w2n n) s.vs_memory = bs ==>
  step_inst_base (mk_inst iid SHA3 [ptr_op; len] [out]) s =
  OK (update_var out (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) s)
Proof
  cheat
QED

Theorem emit_SHA3_bytes_run:
  emit_op SHA3 [ptr_op; len] sa = (op, sb) /\
  eval_operand ptr_op s = SOME p /\ eval_operand len s = SOME n /\
  mem_bytes_at (w2n p) (w2n n) s.vs_memory = bs ==>
  ?out. op = Var out /\
    run_inst_seq (emitted_insts sa sb) s =
      OK (update_var out
        (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) s) /\
    out = STRING #"%" (toString sa.cs_next_var)
Proof
  cheat
QED

Theorem compile_keccak256_bytes_run:
  compile_keccak256_bytes ptr_op sa = (op, sb) /\
  (!x. ptr_op = Var x ==> not_fresh_at sa x) /\
  eval_operand ptr_op s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
  b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME
      (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  cheat
QED

(* Read-only suffixes need only preserve the reserved pointer variables. *)
Theorem hash_readonly_state_rel:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (t with vs_vars := s.vs_vars) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
  stmt_state_rel ctx func cenv cx es t
Proof
  cheat
QED

Theorem compile_keccak256_bytes_frame:
  compile_keccak256_bytes ptr_op sa = (op, sb) /\
  (!x. ptr_op = Var x ==> not_fresh_at sa x) /\
  eval_operand ptr_op s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
  b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME
      (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
    stmt_state_rel ctx func cenv cx es t /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  cheat
QED

Theorem hash_mstore_prefix:
  LENGTH bs <= 32 /\ TAKE (LENGTH bs) (word_to_bytes_be w) = bs ==>
  mem_bytes_at a (LENGTH bs) (mstore a w s).vs_memory = bs
Proof
  cheat
QED

Theorem emit_SHA3_bytes_frame:
  emit_op SHA3 [ptr_op; len] sa = (op, sb) /\
  eval_operand ptr_op s = SOME p /\ eval_operand len s = SOME n /\
  mem_bytes_at (w2n p) (w2n n) s.vs_memory = bs ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME
      (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  cheat
QED

(* Allocate and stage one word, protecting every earlier allocation. *)
Theorem hash_alloc_mstore_frame:
  compile_alloc_buffer 32 sa = (buf, sm) /\
  emit_void MSTORE [buf.buf_operand; val_op] sm = ((), sh) /\
  (!x. val_op = Var x ==> not_fresh_at sa x) /\
  eval_operand val_op s = SOME w /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
  ?t addr. run_inst_seq (emitted_insts sa sh) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\
    eval_operand buf.buf_operand t = SOME addr /\
    t.vs_memory = (mstore (w2n addr) w s).vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
    sh.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sh /\
    sh.cs_next_var = sa.cs_next_var + 1 /\
    sh.cs_next_id = sa.cs_next_id + 2 /\
    local_ptrs_reserved cenv sh /\
    (!x. buf.buf_operand = Var x ==> not_fresh_at sh x) /\
    (!n b sz. local_region cenv es.scopes s n b sz ==>
      mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory)
Proof
  cheat
QED



Theorem compile_keccak256_bytesm_frame:
  compile_keccak256_bytesm val_op (LENGTH bs) sa = (op, sb) /\
  (!x. val_op = Var x ==> not_fresh_at sa x) /\
  eval_operand val_op s = SOME w /\
  LENGTH bs <= 32 /\ TAKE (LENGTH bs) (word_to_bytes_be w) = bs /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME
      (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
    stmt_state_rel ctx func cenv cx es t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
    (!n b sz. local_region cenv es.scopes s n b sz ==>
      mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory)
Proof
  cheat
QED

(* Observational frames include zero-filled windows beyond allocated memory. *)
Theorem hash_write_memory_disjoint:
  off + len <= dst \/ dst + LENGTH bytes <= off ==>
  mem_bytes_at off len (write_memory_with_expansion dst bytes s).vs_memory =
  mem_bytes_at off len s.vs_memory
Proof
  cheat
QED

Theorem hash_write_memory_read_self:
  mem_bytes_at dst (LENGTH bytes)
    (write_memory_with_expansion dst bytes s).vs_memory = bytes
Proof
  cheat
QED

Theorem sha256_consume_outcome:
  rq.cr_kind = MessageCall /\ rq.cr_target = 2w /\ rq.cr_value = 0 /\ rq.cr_static /\
  s.vs_outcomes = outcome::rest /\ outcome.co_success ==>
  consume_call_outcome rq ro 32 s =
    (1w, (write_memory_with_expansion ro
       (word_to_bytes (SHA_256_bytes rq.cr_data) T) s) with
       <| vs_returndata := word_to_bytes (SHA_256_bytes rq.cr_data) T;
          vs_outcomes := rest |>)
Proof
  cheat
QED

Theorem sha256_consume_outcome_fail:
  rq.cr_kind = MessageCall /\ rq.cr_target = 2w /\ rq.cr_value = 0 /\ rq.cr_static /\
  ~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) ==>
  consume_call_outcome rq ro 32 s =
    (0w, (write_memory_with_expansion ro [] s) with
      <| vs_returndata := []; vs_outcomes := DROP 1 s.vs_outcomes |> )
Proof
  cheat
QED

Theorem sha256_exec_ext_call:
  read_memory (w2n args_off) (w2n args_size) s = bs /\
  s.vs_outcomes = outcome::rest /\ outcome.co_success ==>
  exec_ext_call (mk_inst iid STATICCALL ops [out]) s gas 2w 0w
    args_off args_size ret_off (32w:bytes32) T =
  OK (update_var out 1w
      ((write_memory_with_expansion (w2n ret_off)
         (word_to_bytes (SHA_256_bytes bs) T) s) with
         <| vs_returndata := word_to_bytes (SHA_256_bytes bs) T;
            vs_outcomes := rest |>))
Proof
  cheat
QED

Theorem sha256_exec_ext_call_fail:
  ~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) ==>
  exec_ext_call (mk_inst iid STATICCALL ops [out]) s gas 2w 0w
    args_off args_size ret_off (32w:bytes32) T =
  OK (update_var out 0w
    ((write_memory_with_expansion (w2n ret_off) [] s) with
      <| vs_returndata := []; vs_outcomes := DROP 1 s.vs_outcomes |>))
Proof
  cheat
QED

Theorem hash_returndata_immutable_alloca_sep[local]:
  immutable_alloca_sep func cenv cx es (s with vs_returndata := data) <=>
  immutable_alloca_sep func cenv cx es s
Proof
  cheat
QED

Theorem hash_returndata_state_rel:
  stmt_state_rel ctx func cenv cx es (s with vs_returndata := data) <=>
  stmt_state_rel ctx func cenv cx es s
Proof
  cheat
QED

Theorem hash_gas_readings_immutable_alloca_sep[local]:
  immutable_alloca_sep func cenv cx es (s with vs_gas_readings := rs) <=>
  immutable_alloca_sep func cenv cx es s
Proof
  cheat
QED

Theorem hash_gas_readings_state_rel:
  stmt_state_rel ctx func cenv cx es (s with vs_gas_readings := rs) <=>
  stmt_state_rel ctx func cenv cx es s
Proof
  cheat
QED

(* GAS pops the next reading, or reads 0w once the readings run out. *)
Theorem step_GAS:
  step_inst_base (mk_inst iid GAS [] [out]) s =
  OK (update_var out (HD (s.vs_gas_readings ++ [0w]))
        (s with vs_gas_readings := DROP 1 s.vs_gas_readings))
Proof
  cheat
QED

Theorem step_STATICCALL_sha256:
  eval_operand gas_op s = SOME gas /\
  eval_operand args_op s = SOME args_off /\
  eval_operand size_op s = SOME args_size /\
  eval_operand ret_op s = SOME ret_off /\
  read_memory (w2n args_off) (w2n args_size) s = bs /\
  s.vs_outcomes = outcome::rest /\ outcome.co_success ==>
  step_inst_base
    (mk_inst iid STATICCALL [gas_op; Lit 2w; args_op; size_op; ret_op; Lit 32w] [out]) s =
  OK (update_var out 1w
      ((write_memory_with_expansion (w2n ret_off)
         (word_to_bytes (SHA_256_bytes bs) T) s) with
         <| vs_returndata := word_to_bytes (SHA_256_bytes bs) T;
            vs_outcomes := rest |>))
Proof
  cheat
QED

Theorem step_STATICCALL_sha256_fail:
  eval_operand gas_op s = SOME gas /\
  eval_operand args_op s = SOME args_off /\
  eval_operand size_op s = SOME args_size /\
  eval_operand ret_op s = SOME ret_off /\
  ~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) ==>
  step_inst_base
    (mk_inst iid STATICCALL [gas_op; Lit 2w; args_op; size_op; ret_op; Lit 32w] [out]) s =
  OK (update_var out 0w
    ((write_memory_with_expansion (w2n ret_off) [] s) with
      <| vs_returndata := []; vs_outcomes := DROP 1 s.vs_outcomes |>))
Proof
  cheat
QED

Theorem hash_outcomes_state_rel:
  stmt_state_rel ctx func cenv cx es s ==>
  stmt_state_rel ctx func cenv cx
    (es with outcomes := SOME (DROP 1 s.vs_outcomes))
    (s with vs_outcomes := DROP 1 s.vs_outcomes)
Proof
  cheat
QED

Theorem hash_mload_write_word:
  mload dst (write_memory_with_expansion dst (word_to_bytes (w:bytes32) T) s) = w
Proof
  cheat
QED

(* Shared computed-precompile tail, independent of input representation. *)
Theorem sha256_tail_run:
  eval_operand ptr_op s = SOME p /\
  eval_operand len_op s = SOME n /\
  eval_operand ret_op s = SOME r /\
  (!x. ptr_op = Var x \/ len_op = Var x \/ ret_op = Var x ==> x <> gas_var) /\
  (!x. ret_op = Var x ==> x <> success_var) /\
  mem_bytes_at (w2n p) (w2n n) s.vs_memory = bs /\
  s.vs_outcomes = outcome::rest /\ outcome.co_success ==>
  run_inst_seq
    [mk_inst i0 GAS [] [gas_var];
     mk_inst i1 STATICCALL [Var gas_var; Lit 2w; ptr_op; len_op; ret_op; Lit 32w]
       [success_var];
     mk_inst i2 ASSERT [Var success_var] [];
     mk_inst i3 MLOAD [ret_op] [out]] s =
  OK (update_var out (SHA_256_bytes bs)
    (update_var success_var 1w
      ((write_memory_with_expansion (w2n r)
          (word_to_bytes (SHA_256_bytes bs) T)
          (update_var gas_var (HD (s.vs_gas_readings ++ [0w]))
             (s with vs_gas_readings := DROP 1 s.vs_gas_readings))) with
        <| vs_returndata := word_to_bytes (SHA_256_bytes bs) T;
           vs_outcomes := rest |>)))
Proof
  cheat
QED

Theorem sha256_tail_fail:
  eval_operand ptr_op s = SOME p /\
  eval_operand len_op s = SOME n /\
  eval_operand ret_op s = SOME r /\
  (!x. ptr_op = Var x \/ len_op = Var x \/ ret_op = Var x ==> x <> gas_var) /\
  ~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) ==>
  ?t. run_inst_seq
    [mk_inst i0 GAS [] [gas_var];
     mk_inst i1 STATICCALL [Var gas_var; Lit 2w; ptr_op; len_op; ret_op; Lit 32w]
       [success_var];
     mk_inst i2 ASSERT [Var success_var] [];
     mk_inst i3 MLOAD [ret_op] [out]] s = Abort Revert_abort t
Proof
  cheat
QED

Theorem sha256_tail_frame:
  eval_operand ptr_op s = SOME p /\ eval_operand len_op s = SOME n /\
  eval_operand ret_op s = SOME r /\
  (!x. ptr_op = Var x \/ len_op = Var x \/ ret_op = Var x ==> x <> gas_var) /\
  (!x. ret_op = Var x ==> x <> success_var) /\
  mem_bytes_at (w2n p) (w2n n) s.vs_memory = bs /\
  s.vs_outcomes = outcome::rest /\ outcome.co_success /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> x <> gas_var /\ x <> success_var /\ x <> out) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     b + sz <= w2n r \/ w2n r + 32 <= b) /\
  (cenv.ce_is_ctor ==> !name tv v off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
       SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name =
       SOME (tv,v) ==>
     regions_disjoint off (type_memory_size tv) (w2n r) 32) ==>
  ?t. run_inst_seq
    [mk_inst i0 GAS [] [gas_var];
     mk_inst i1 STATICCALL [Var gas_var; Lit 2w; ptr_op; len_op; ret_op; Lit 32w]
       [success_var];
     mk_inst i2 ASSERT [Var success_var] [];
     mk_inst i3 MLOAD [ret_op] [out]] s = OK t /\
    eval_operand (Var out) t = SOME (SHA_256_bytes bs) /\
    stmt_state_rel ctx func cenv cx (es with outcomes := SOME rest) t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\
    (!b len. b + len <= w2n r \/ w2n r + 32 <= b ==>
       mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory)
Proof
  cheat
QED

Theorem emitted_insts_sha256_tail:
  emit_op GAS [] sa = (gas_op, sg) /\
  emit_op STATICCALL [gas_op; Lit 2w; ptr_op; len_op; ret_op; Lit 32w] sg =
    (success_op, sc) /\
  emit_void ASSERT [success_op] sc = ((), sh) /\
  emit_op MLOAD [ret_op] sh = (op, sb) ==>
  ?gv sv ov.
    gas_op = Var gv /\ success_op = Var sv /\ op = Var ov /\
    gv = STRING #"%" (toString sa.cs_next_var) /\
    sv = STRING #"%" (toString (sa.cs_next_var + 1)) /\
    ov = STRING #"%" (toString (sa.cs_next_var + 2)) /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id GAS [] [gv];
       mk_inst (sa.cs_next_id + 1) STATICCALL
         [Var gv; Lit 2w; ptr_op; len_op; ret_op; Lit 32w] [sv];
       mk_inst (sa.cs_next_id + 2) ASSERT [Var sv] [];
       mk_inst (sa.cs_next_id + 3) MLOAD [ret_op] [ov]] /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    sb.cs_next_var = sa.cs_next_var + 3
Proof
  cheat
QED

Theorem emit_sha256_tail_fail:
  emit_op GAS [] sa = (gas_op, sg) /\
  emit_op STATICCALL [gas_op; Lit 2w; ptr_op; len_op; ret_op; Lit 32w] sg =
    (success_op, sc) /\
  emit_void ASSERT [success_op] sc = ((), sh) /\
  emit_op MLOAD [ret_op] sh = (op, sb) /\
  eval_operand ptr_op s = SOME p /\ eval_operand len_op s = SOME n /\
  eval_operand ret_op s = SOME r /\
  (!x. ptr_op = Var x \/ len_op = Var x \/ ret_op = Var x ==> not_fresh_at sa x) /\
  ~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
Proof
  cheat
QED

Theorem emit_sha256_tail_frame:
  emit_op GAS [] sa = (gas_op, sg) /\
  emit_op STATICCALL [gas_op; Lit 2w; ptr_op; len_op; ret_op; Lit 32w] sg =
    (success_op, sc) /\
  emit_void ASSERT [success_op] sc = ((), sh) /\
  emit_op MLOAD [ret_op] sh = (op, sb) /\
  eval_operand ptr_op s = SOME p /\ eval_operand len_op s = SOME n /\
  eval_operand ret_op s = SOME r /\
  (!x. ptr_op = Var x \/ len_op = Var x \/ ret_op = Var x ==> not_fresh_at sa x) /\
  mem_bytes_at (w2n p) (w2n n) s.vs_memory = bs /\
  s.vs_outcomes = outcome::rest /\ outcome.co_success /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     b + sz <= w2n r \/ w2n r + 32 <= b) /\
  (cenv.ce_is_ctor ==> !name tv v off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
       SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name =
       SOME (tv,v) ==>
     regions_disjoint off (type_memory_size tv) (w2n r) 32) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (SHA_256_bytes bs) /\
    stmt_state_rel ctx func cenv cx (es with outcomes := SOME rest) t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\
    (!b len. b + len <= w2n r \/ w2n r + 32 <= b ==>
       mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory)
Proof
  cheat
QED

Theorem hash_alloc_sha256_tail_fail:
  compile_alloc_buffer 32 sa = (buf,sn) /\
  emit_op GAS [] sn = (gas_op,sg) /\
  emit_op STATICCALL [gas_op; Lit 2w; ptr_op; len_op; buf.buf_operand; Lit 32w]
    sg = (success_op,sc) /\
  emit_void ASSERT [success_op] sc = ((),sh) /\
  emit_op MLOAD [buf.buf_operand] sh = (op,sb) /\
  eval_operand ptr_op s = SOME p /\ eval_operand len_op s = SOME n /\
  (!x. ptr_op = Var x \/ len_op = Var x ==> not_fresh_at sa x) /\
  ~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
Proof
  cheat
QED

Theorem hash_alloc_sha256_tail_frame:
  compile_alloc_buffer 32 sa = (buf,sn) /\
  emit_op GAS [] sn = (gas_op,sg) /\
  emit_op STATICCALL [gas_op; Lit 2w; ptr_op; len_op; buf.buf_operand; Lit 32w]
    sg = (success_op,sc) /\
  emit_void ASSERT [success_op] sc = ((),sh) /\
  emit_op MLOAD [buf.buf_operand] sh = (op,sb) /\
  eval_operand ptr_op s = SOME p /\ eval_operand len_op s = SOME n /\
  (!x. ptr_op = Var x \/ len_op = Var x ==> not_fresh_at sa x) /\
  mem_bytes_at (w2n p) (w2n n) s.vs_memory = bs /\
  s.vs_outcomes = outcome::rest /\ outcome.co_success /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (SHA_256_bytes bs) /\
    stmt_state_rel ctx func cenv cx (es with outcomes := SOME rest) t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid base len. aid < sa.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (base,len) ==>
       mem_bytes_at base len t.vs_memory = mem_bytes_at base len s.vs_memory) /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    (!n b sz. local_region cenv es.scopes s n b sz ==>
      mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory)
Proof
  cheat
QED



(* Length-header/data-pointer prefix shared by memory-backed hashes. *)
Theorem hash_data_prefix_run:
  emit_op MLOAD [ptr_op] sa = (len_op, sl) /\
  emit_op ADD [ptr_op; Lit 32w] sl = (data_op, sm) /\
  (!x. ptr_op = Var x ==> not_fresh_at sa x) /\
  eval_operand ptr_op s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w len /\ b < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts sa sm) s = OK t /\
    eval_operand len_op t = SOME (n2w len) /\
    eval_operand data_op t = SOME (n2w (b + 32)) /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!x. len_op = Var x \/ data_op = Var x ==> not_fresh_at sm x) /\
    sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
    sm.cs_next_var = sa.cs_next_var + 2 /\ sm.cs_next_id = sa.cs_next_id + 2
Proof
  cheat
QED

Theorem compile_sha256_bytes_fail:
  compile_sha256_bytes ptr_op sa = (op, sb) /\
  (!x. ptr_op = Var x ==> not_fresh_at sa x) /\
  eval_operand ptr_op s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w len /\ b < dimword (:256) /\
  ~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst (sa.cs_next_id + 2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (sa.cs_next_var + 2))]) (fn_insts func) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
Proof
  cheat
QED

Theorem compile_sha256_bytes_frame:
  compile_sha256_bytes ptr_op sa = (op, sb) /\
  (!x. ptr_op = Var x ==> not_fresh_at sa x) /\
  eval_operand ptr_op s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
  b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  s.vs_outcomes = outcome::rest /\ outcome.co_success /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst (sa.cs_next_id + 2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (sa.cs_next_var + 2))]) (fn_insts func) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (SHA_256_bytes bs) /\
    stmt_state_rel ctx func cenv cx (es with outcomes := SOME rest) t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid base len. aid < sa.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (base,len) ==>
       mem_bytes_at base len t.vs_memory = mem_bytes_at base len s.vs_memory) /\
    (!nm base sz. local_region cenv es.scopes s nm base sz ==>
      mem_bytes_at base sz t.vs_memory = mem_bytes_at base sz s.vs_memory)
Proof
  cheat
QED

Theorem compile_sha256_bytesm_fail:
  compile_sha256_bytesm val_op len sa = (op, sb) /\
  (!x. val_op = Var x ==> not_fresh_at sa x) /\
  eval_operand val_op s = SOME w /\
  ~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
  MEM (mk_inst (sa.cs_next_id + 2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (sa.cs_next_var + 1))]) (fn_insts func) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
Proof
  cheat
QED

Theorem compile_sha256_bytesm_frame:
  compile_sha256_bytesm val_op (LENGTH bs) sa = (op, sb) /\
  (!x. val_op = Var x ==> not_fresh_at sa x) /\
  eval_operand val_op s = SOME w /\
  LENGTH bs <= 32 /\ TAKE (LENGTH bs) (word_to_bytes_be w) = bs /\
  s.vs_outcomes = outcome::rest /\ outcome.co_success /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
  MEM (mk_inst (sa.cs_next_id + 2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (sa.cs_next_var + 1))]) (fn_insts func) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (SHA_256_bytes bs) /\
    stmt_state_rel ctx func cenv cx (es with outcomes := SOME rest) t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
    (!nm lb sz. local_region cenv es.scopes s nm lb sz ==>
      mem_bytes_at lb sz t.vs_memory = mem_bytes_at lb sz s.vs_memory)
Proof
  cheat
QED



Theorem hash_take_word_to_bytes:
  n <= dimindex (:'a) DIV 8 ==>
  TAKE n (word_to_bytes (w:'a word) be) = word_to_bytes_aux n w be
Proof
  cheat
QED

Theorem method_id_word_mask:
  ((w:bytes32) >>> 224) << 224 =
  typed_val_to_w256 (BaseTV (BytesT (Fixed 4)))
    (BytesV (TAKE 4 (word_to_bytes w T)))
Proof
  cheat
QED

(* The selector mask is a read-only two-instruction suffix. *)
Theorem method_id_mask_run:
  emit_op SHR [Lit 224w; hash_op] sa = (sel_op, sm) /\
  emit_op SHL [Lit 224w; sel_op] sm = (word_op, sb) /\
  eval_operand hash_op s = SOME w ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand word_op t = SOME ((w >>> 224) << 224) /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  cheat
QED

Theorem method_id_mask_frame:
  emit_op SHR [Lit 224w; hash_op] sa = (sel_op, sm) /\
  emit_op SHL [Lit 224w; sel_op] sm = (word_op, sb) /\
  eval_operand hash_op s = SOME w /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand word_op t = SOME
      (typed_val_to_w256 (BaseTV (BytesT (Fixed 4)))
        (BytesV (TAKE 4 (word_to_bytes w T)))) /\
    stmt_state_rel ctx func cenv cx es t /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  cheat
QED

(* A length header followed by a single data word, used for short buffers. *)
Theorem hash_single_word_buffer_run:
  emit_void MSTORE [ptr_op; Lit (n2w n)] sa = ((), sh) /\
  emit_op ADD [ptr_op; Lit 32w] sh = (data_ptr, sd) /\
  emit_void MSTORE [data_ptr; val_op] sd = ((), sb) /\
  eval_operand ptr_op s = SOME (n2w b) /\
  eval_operand val_op s = SOME v /\
  (!x. val_op = Var x ==> not_fresh_at sa x) /\
  b + 32 < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    t.vs_memory = (mstore (b + 32) v (mstore b (n2w n) s)).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  cheat
QED

Theorem hash_single_word_buffer_frame:
  emit_void MSTORE [ptr_op; Lit (n2w n)] sa = ((), sh) /\
  emit_op ADD [ptr_op; Lit 32w] sh = (data_ptr, sd) /\
  emit_void MSTORE [data_ptr; val_op] sd = ((), sb) /\
  eval_operand ptr_op s = SOME (n2w b) /\ eval_operand val_op s = SOME v /\
  (!x. val_op = Var x ==> not_fresh_at sa x) /\ b + 32 < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!name off len. local_region cenv es.scopes s name off len ==>
     regions_disjoint b 64 off len) /\
  (cenv.ce_is_ctor ==> !name tv iv off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
       SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name =
       SOME (tv,iv) ==>
     regions_disjoint b 64 off (type_memory_size tv)) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\
    t.vs_memory = (mstore (b + 32) v (mstore b (n2w n) s)).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!off len. regions_disjoint b 64 off len ==>
       mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory)
Proof
  cheat
QED

Theorem hash_single_word_buffer_contents:
  LENGTH bs <= 32 /\ TAKE (LENGTH bs) (word_to_bytes_be v) = bs ==>
  val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) b
    (mstore (b + 32) v (mstore b (n2w (LENGTH bs)) s)).vs_memory
Proof
  cheat
QED

Theorem hash_alloc_single_word_buffer_frame:
  compile_alloc_buffer 64 sa = (buf, sm) /\
  emit_void MSTORE [buf.buf_operand; Lit (n2w (LENGTH bs))] sm = ((), sh) /\
  emit_op ADD [buf.buf_operand; Lit 32w] sh = (data_ptr, sd) /\
  emit_void MSTORE [data_ptr; val_op] sd = ((), sb) /\
  eval_operand val_op s = SOME v /\
  (!x. val_op = Var x ==> not_fresh_at sa x) /\
  LENGTH bs <= 32 /\ TAKE (LENGTH bs) (word_to_bytes_be v) = bs /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
  ?t p. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\
    eval_operand buf.buf_operand t = SOME p /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n p, 64) /\
    w2n p + 64 < dimword (:256) /\
    val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) (w2n p) t.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid off len. aid < sa.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
      mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (!n b sz. local_region cenv es.scopes s n b sz ==>
      mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory) /\
    (!n b sz. local_region cenv es.scopes t n b sz ==>
      regions_disjoint (w2n p) 64 b sz)
Proof
  cheat
QED



Theorem method_id_mask_prefix:
  TAKE 4 (word_to_bytes_be (((w:bytes32) >>> 224) << 224)) =
  TAKE 4 (word_to_bytes w T)
Proof
  cheat
QED

Theorem method_id_dynamic_suffix_frame:
  emit_op SHR [Lit 224w; hash_op] sa = (sel_op, sm) /\
  emit_op SHL [Lit 224w; sel_op] sm = (word_op, sn) /\
  compile_alloc_buffer 64 sn = (buf, sp) /\
  emit_void MSTORE [buf.buf_operand; Lit 4w] sp = ((), sh) /\
  emit_op ADD [buf.buf_operand; Lit 32w] sh = (data_ptr, sd) /\
  emit_void MSTORE [data_ptr; word_op] sd = ((), sb) /\
  eval_operand hash_op s = SOME w /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst sn.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sn.cs_next_var)]) (fn_insts func) ==>
  ?t p. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\
    eval_operand buf.buf_operand t = SOME p /\
    FLOOKUP t.vs_allocas sn.cs_next_id = SOME (w2n p,64) /\
    w2n p + 64 < dimword (:256) /\
    val_in_memory (BaseTV (BytesT (Dynamic 4)))
      (BytesV (TAKE 4 (word_to_bytes w T))) (w2n p) t.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid off len. aid < sa.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
       mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (!nm lb sz. local_region cenv es.scopes s nm lb sz ==>
      mem_bytes_at lb sz t.vs_memory = mem_bytes_at lb sz s.vs_memory) /\
    (!n b sz. local_region cenv es.scopes t n b sz ==>
      regions_disjoint (w2n p) 64 b sz)
Proof
  cheat
QED



Theorem eval_exprs_single_literal:
  !cx la l es. eval_exprs cx [Literal la l] es = (INL [evaluate_literal l], es)
Proof
  cheat
QED

(* A literal signature is folded to the literal selector (#711). *)
Theorem compile_expr_method_id_literal:
  !cenv ty ann la l bs st.
    method_id_literal (Literal la l) = SOME bs ==>
    compile_expr cenv ty (Builtin ann MethodId [Literal la l]) st =
    compile_literal_vv ann (BytesL (TAKE 4 (Keccak_256_w64 bs))) st
Proof
  cheat
QED

(* The source hashes a literal signature to the selector the lowering
   folds it to. *)
Theorem eval_expr_method_id_literal:
  !cx ann la l bs es res es'.
    method_id_literal (Literal la l) = SOME bs /\
    eval_expr cx (Builtin ann MethodId [Literal la l]) es = (res, es') ==>
    es' = es /\ res = INL (Value (BytesV (TAKE 4 (Keccak_256_w64 bs))))
Proof
  cheat
QED

Theorem compile_method_id_literal_dynamic_vv_sim:
  !cenv la l. IS_SOME (method_id_literal (Literal la l)) ==>
    expr_vv_ok cenv (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [Literal la l])
Proof
  cheat
QED

(* Typed postconditions expose the representation needed by hash suffixes. *)
Theorem hash_fixed_post_view:
  expr_post ctx func cenv cx e es sa sm s0 es' (BytesV bs) op s /\
  expr_type e = BaseT (BytesT (Fixed m)) /\
  value_has_type (BaseTV (BytesT (Fixed m))) (BytesV bs) /\ m <= 32 ==>
  ?w. eval_operand op s = SOME w /\ LENGTH bs = m /\
      TAKE (LENGTH bs) (word_to_bytes_be w) = bs
Proof
  cheat
QED

Theorem hash_live_footprint_bound:
  stmt_state_rel ctx func cenv cx es s /\
  ((?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
      b <= p /\ p + n <= b + sz) \/
   (?name b sz. local_region cenv es.scopes s name b sz /\
      b <= p /\ p + n <= b + sz)) ==>
  p + n < dimword (:256)
Proof
  cheat
QED

Theorem hash_post_footprint_bound:
  post_value_type cenv e = expr_type e /\
  expr_post ctx func cenv cx e es sa sm s0 es' v op s /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  ~is_word_type (expr_type e) /\ eval_operand op s = SOME p ==>
  w2n p + val_footprint tv v < dimword (:256)
Proof
  cheat
QED

Theorem hash_dynamic_post_view:
  expr_post ctx func cenv cx e es sa sm s0 es' (BytesV bs) op s /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) (expr_type e) =
    SOME (BaseTV (BytesT (Dynamic cap))) ==>
  ?b. eval_operand op s = SOME (n2w b) /\
    mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
    b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256)
Proof
  cheat
QED

Theorem hash_string_post_view:
  expr_post ctx func cenv cx e es sa sm s0 es' (StringV str) op s /\
  expr_type e = BaseT (StringT cap) /\
  evaluate_type (get_tenv cx) (expr_type e) =
    SOME (BaseTV (StringT cap)) ==>
  ?b. eval_operand op s = SOME (n2w b) /\
    mem_word_at b s.vs_memory = n2w (LENGTH str) /\
    mem_bytes_at (b + 32) (LENGTH str) s.vs_memory = MAP (n2w o ORD) str /\
    b + 32 < dimword (:256) /\ LENGTH str < dimword (:256)
Proof
  cheat
QED

(* Containment is independent of the particular straight-line suffix. *)
Theorem hash_emitted_inst_mem:
  fn_has_code sa sb func /\ MEM inst (emitted_insts sa sb) ==>
  MEM inst (fn_insts func)
Proof
  cheat
QED

Theorem compile_hash_singleton:
  (bt = Keccak256 \/ bt = Sha256) ==>
  compile_expr cenv ty (Builtin ann bt [e]) sa =
    (let (v,sm) = lower_value compile_expr cenv (expr_type e) e sa in
     as_stack_val ann
       (if is_bytestring_type (expr_type e) then
          (if bt = Keccak256 then compile_keccak256_bytes v sm
           else compile_sha256_bytes v sm)
        else case expr_type e of
          BaseT (BytesT (Fixed m)) =>
            (if bt = Keccak256 then compile_keccak256_bytesm v m sm
             else compile_sha256_bytesm v m sm)
        | _ => (if bt = Keccak256 then compile_keccak256_word v sm
                else compile_sha256_word v sm)))
Proof
  cheat
QED

Theorem compile_method_id_singleton_runtime:
  method_id_literal e = NONE ==>
  compile_expr cenv ty (Builtin ann MethodId [e]) sa =
    (let (v,sm) = lower_value compile_expr cenv (expr_type e) e sa in
     if ann = BaseT (BytesT (Fixed 4)) then
       as_stack_val ann (compile_method_id_runtime (expr_type e) v T sm)
     else as_ptr_val ann LocMemory
       (compile_method_id_runtime (expr_type e) v F sm))
Proof
  cheat
QED

Theorem hash_suffix_appends:
  (!v. cs_appends (compile_keccak256_bytes v)) /\
  (!v m. cs_appends (compile_keccak256_bytesm v m)) /\
  (!v. cs_appends (compile_sha256_bytes v)) /\
  (!v m. cs_appends (compile_sha256_bytesm v m)) /\
  (!ty v fixed. cs_appends (compile_method_id_runtime ty v fixed))
Proof
  cheat
QED

Theorem hash_fixed_alloca_code:
  (if sha then compile_sha256_bytesm v m sa
   else compile_keccak256_bytesm v m sa) = (op,sb) /\
  fn_has_code sa sb func ==>
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
  (sha ==> MEM (mk_inst (sa.cs_next_id + 2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (sa.cs_next_var + 1))]) (fn_insts func))
Proof
  cheat
QED

Theorem hash_sha256_memory_alloca_code:
  compile_sha256_bytes v sa = (op,sb) /\ fn_has_code sa sb func ==>
  MEM (mk_inst (sa.cs_next_id + 2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (sa.cs_next_var + 2))]) (fn_insts func)
Proof
  cheat
QED

Theorem hash_unary_suffix_cut:
  lower_value compile_expr cenv ty e sa = (v,sm) /\
  cs_appends code /\ code sm = (op,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa ==>
  cs_extends sa sm /\ cs_extends sm sb /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  local_ptrs_reserved cenv sm
Proof
  cheat
QED

Theorem hash_method_id_runtime_cut:
  compile_method_id_runtime ty v fixed sa = (op,sb) ==>
  ?hash sm sel sn word sp.
    compile_method_id_hash ty v sa = (hash,sm) /\
    emit_op SHR [Lit 224w; hash] sm = (sel,sn) /\
    emit_op SHL [Lit 224w; sel] sn = (word,sp) /\
    (if fixed then op = word /\ sb = sp
     else ?buf sh data sd st.
       compile_alloc_buffer 64 sp = (buf,sh) /\
       emit_void MSTORE [buf.buf_operand; Lit 4w] sh = ((),st) /\
       emit_op ADD [buf.buf_operand; Lit 32w] st = (data,sd) /\
       emit_void MSTORE [data; word] sd = ((),sb) /\
       op = buf.buf_operand)
Proof
  cheat
QED

Theorem hash_method_id_hash_appends:
  cs_appends (compile_method_id_hash ty v)
Proof
  cheat
QED

Theorem hash_method_id_hash_cut:
  compile_method_id_runtime ty v fixed sa = (op,sb) /\
  compile_method_id_hash ty v sa = (hash,sm) /\
  fn_has_code sa sb func ==>
  cs_extends sa sm /\ cs_extends sm sb /\
  fn_has_code sa sm func /\ fn_has_code sm sb func
Proof
  cheat
QED

Theorem hash_method_id_output_alloca_code:
  compile_alloc_buffer 64 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; Lit 4w] sm = ((),sn) /\
  emit_op ADD [buf.buf_operand; Lit 32w] sn = (data,sp) /\
  emit_void MSTORE [data; word] sp = ((),sb) /\
  fn_has_code sa sb func ==>
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)
Proof
  cheat
QED

Theorem hash_method_id_mask_cut:
  emit_op SHR [Lit 224w; hash] sa = (sel,sm) /\
  emit_op SHL [Lit 224w; sel] sm = (word,sn) /\
  compile_alloc_buffer 64 sn = (buf,sp) /\
  emit_void MSTORE [buf.buf_operand; Lit 4w] sp = ((),sh) /\
  emit_op ADD [buf.buf_operand; Lit 32w] sh = (data,sd) /\
  emit_void MSTORE [data; word] sd = ((),sb) /\
  fn_has_code sa sb func ==>
  fn_has_code sa sn func /\ fn_has_code sn sb func /\
  MEM (mk_inst sn.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sn.cs_next_var)]) (fn_insts func)
Proof
  cheat
QED

(* A straight-line suffix protects every older allocation, a stronger frame
   than the expression judgment needs. *)
Theorem wb_frame_allocating_tail:
  wb_frame cenv es sa s0 s /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
     FLOOKUP t.vs_allocas aid = SOME entry) /\
  (!aid b sz. aid < sm.cs_next_id /\
     FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
     mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory) /\
  local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM scopes /\
  (!n b sz. local_region cenv scopes s n b sz ==>
     mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory) ==>
  wb_frame cenv es sa s0 t
Proof
  cheat
QED

Theorem vv_post_frame_intro:
  post_value_type cenv e = expr_type e /\
  stmt_state_rel ctx func cenv cx es' t /\
  vv_holds cenv cx (expr_type e) tv vv es' t /\
  vv_at cenv cx (expr_type e) sa sb es' tv vv t /\
  (~expr_has_effect e ==> vv_storage_live cx vv es' t) /\
  wb_frame cenv es sa s0 t ==>
  vv_post ctx func cenv cx e es sa sb s0 es' tv vv t
Proof
  cheat
QED

Theorem vv_post_word_intro:
  stmt_state_rel ctx func cenv cx es' s /\ is_word_type (expr_type e) /\
  (?w. eval_operand op s = SOME w /\
    !tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
         w = typed_val_to_w256 tv v) /\
  wb_frame cenv es sa s0 s ==>
  vv_post ctx func cenv cx e es sa sb s0 es' (Value v) (StackValue ty op) s
Proof
  cheat
QED

Theorem hash_run_frag:
  same_blocks sa sb /\ sb.cs_current_insts = sa.cs_current_insts ++ insts /\
  emitted_insts sa sb = insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) insts /\
  (!s. P s ==> ?t. run_inst_seq insts s = OK t /\
     Q (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
  frag_exec ctx sa sb P Q R
Proof
  cheat
QED

(* Runtime errors accept any abort; no successful post-state is required. *)
Theorem hash_abort_frag:
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  (!s. P s ==> ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t) ==>
  frag_exec ctx sa sb P Q
    (expr_exit (INR (Error (RuntimeError "precompile failed"))))
Proof
  cheat
QED

Theorem vv_post_allocated_memory_intro:
  post_value_type cenv e = expr_type e /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  val_wf tv v /\ val_in_memory tv v (w2n w) s.vs_memory /\
  stmt_state_rel ctx func cenv cx es' s /\
  p.ptr_location = LocMemory /\ eval_operand p.ptr_operand s = SOME w /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  b <= w2n w /\ w2n w + val_footprint tv v <= b + sz /\
  (!n lb lsz. local_region cenv es'.scopes s n lb lsz ==>
     b + sz <= lb \/ lb + lsz <= b) /\
  wb_frame cenv es sa s0 s ==>
  vv_post ctx func cenv cx e es sa sb s0 es' (Value v)
    (LocatedValue (expr_type e) p) s
Proof
  cheat
QED

(* Forced base-typed operands have the corresponding value type. *)
Theorem expr_body_pre_base_result:
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT bt /\
  (do r <- eval_expr cx e; read_result cx r od) es = (res,es') ==>
  expr_sim_inv cenv cx env es' /\ expr_res_ok res /\
  !v. res = INL v ==> value_has_type (BaseTV bt) v
Proof
  cheat
QED

Theorem eval_expr_unary_builtin_cases:
  ~precompile_builtin bt /\ bt <> Len /\ builtin_args_length_ok bt 1 /\
  eval_expr cx (Builtin ann bt [e]) es = (res,es') ==>
  (?exc. (do r <- eval_expr cx e; read_result cx r od) es = (INR exc,es') /\ res = INR exc) \/
  ?v. (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') /\
    res = (case builtin_result cx es'.accounts ann bt [expr_type e] [v] of
             INL v => INL (Value v) | INR exc => INR exc)
Proof
  cheat
QED

Theorem eval_expr_sha256_cases:
  eval_expr cx (Builtin ann Sha256 [e]) es = (res,es') ==>
  (?exc. (do r <- eval_expr cx e; read_result cx r od) es = (INR exc,es') /\ res = INR exc) \/
  ?v es1. (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es1) /\
    (case builtin_result cx es1.accounts ann Sha256 [expr_type e] [v] of
       INR exc => res = INR exc /\ es' = es1
     | INL w => (do precompile_call_success Sha256; return (Value w) od) es1 = (res,es'))
Proof
  cheat
QED

Theorem sha256_source_outcome_step:
  precompile_call_success Sha256 es =
    case es.outcomes of
      NONE => (INL (),es)
    | SOME [] => (INR (Error (RuntimeError "precompile failed")),es)
    | SOME (outcome::rest) =>
        (if call_outcome_success outcome then INL ()
         else INR (Error (RuntimeError "precompile failed")),
         es with outcomes := SOME rest)
Proof
  cheat
QED

Theorem sha256_typed_builtin_result:
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v ==>
  ?r. builtin_result cx accounts (BaseT (BytesT (Fixed 32)))
    Sha256 [expr_type e] [v] = INL r
Proof
  cheat
QED

Theorem eval_expr_unary_builtin_action:
  ~precompile_builtin bt /\ bt <> Len /\ builtin_args_length_ok bt 1 ==>
  eval_expr cx (Builtin ann bt [e]) =
  bind (bind (eval_expr cx e) (read_result cx))
    (\v es. ((case builtin_result cx es.accounts ann bt [expr_type e] [v] of
                INL w => INL (Value w) | INR exc => INR exc), es))
Proof
  cheat
QED

Theorem eval_expr_sha256_action:
  eval_expr cx (Builtin ann Sha256 [e]) =
  bind (bind (eval_expr cx e) (read_result cx))
    (\v es1. case builtin_result cx es1.accounts ann Sha256 [expr_type e] [v] of
       INR exc => (INR exc, es1)
     | INL w => (do precompile_call_success Sha256; return (Value w) od) es1)
Proof
  cheat
QED

(* The sha256 continuation reads the outcomes, never the gas observations. *)
Theorem sha256_continuation_gas_obs:
  (case builtin_result cx es1.accounts ann Sha256 tys [v] of
     INR exc => (INR exc, es1)
   | INL w => (do precompile_call_success Sha256; return (Value w) od) es1) =
    (res, es2) ==>
  !tail. (case builtin_result cx es1.accounts ann Sha256 tys [v] of
     INR exc => (INR exc, es1 with gas_obs := tail)
   | INL w => (do precompile_call_success Sha256; return (Value w) od)
                (es1 with gas_obs := tail)) =
    (res, es2 with gas_obs := tail)
Proof
  cheat
QED

Theorem expr_exit_INR_cast[local]:
  expr_exit (INR exc : value + exception) r ==>
  expr_exit (INR exc : eval_result + exception) r
Proof
  cheat
QED

(* Unary composition keeps the complete argument postcondition available to
   the suffix, including the footprint and protected-allocation frame. The
   suffix is an actual counted target path from every operand endpoint. *)
Theorem compile_typed_unary_builtin_vv_sim:
  expr_body_pre cenv cx env (Builtin ann bt [e]) es /\
  expr_sim ctx func cenv cx (expr_type e) e es /\ expr_type e = BaseT bty /\
  ~precompile_builtin bt /\ bt <> Len /\ builtin_args_length_ok bt 1 /\
  (!sa sb vv. compile_expr cenv ty (Builtin ann bt [e]) sa = (vv,sb) ==>
    ?x sm. lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
      code x sm = (vv,sb)) /\
  (!x. cs_appends (code x)) /\
  (!sa sm sb x vv s0 v gs es' s.
    lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
    code x sm = (vv,sb) /\ fn_has_code sm sb func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    local_ptrs_reserved cenv sm /\
    bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
      (INL v,es') /\
    value_has_type (BaseTV bty) v /\ expr_sim_inv cenv cx env es' /\
    expr_res_ok (builtin_result cx es'.accounts ann bt [expr_type e] [v]) /\
    expr_post ctx func cenv cx e es sa sm s0 es' v x s /\ ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?n r. gas_marked_path F ctx func s n r /\
      ((?t rv. r = OK t /\
          builtin_result cx es'.accounts ann bt [expr_type e] [v] = INL rv /\
          vv_post ctx func cenv cx (Builtin ann bt [e]) es sa sb s0 es'
            (Value rv) vv t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts) \/
       (exit_result r /\
        expr_exit (builtin_result cx es'.accounts ann bt [expr_type e] [v]) r))) ==>
  expr_vv_sim ctx func cenv cx ty (Builtin ann bt [e]) es
Proof
  cheat
QED

(* The sha256 composition: the operand, then the digest's precompile call,
   whose outcome the source consumes. *)
Theorem compile_typed_sha256_unary_vv_sim:
  expr_body_pre cenv cx env (Builtin ann Sha256 [e]) es /\
  expr_sim ctx func cenv cx (expr_type e) e es /\ expr_type e = BaseT bty /\
  (!sa sb vv. compile_expr cenv ty (Builtin ann Sha256 [e]) sa = (vv,sb) ==>
    ?x sm. lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
      code x sm = (vv,sb)) /\
  (!x. cs_appends (code x)) /\
  (!sa sm sb x vv s0 v gs es1 s res es2.
    lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
    code x sm = (vv,sb) /\ fn_has_code sm sb func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    local_ptrs_reserved cenv sm /\
    bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
      (INL v,es1) /\
    value_has_type (BaseTV bty) v /\ expr_sim_inv cenv cx env es1 /\
    expr_vv_res_ok res /\
    (case builtin_result cx es1.accounts ann Sha256 [expr_type e] [v] of
       INR exc => (INR exc,es1)
     | INL w => (do precompile_call_success Sha256; return (Value w) od) es1) =
       (res,es2) /\
    expr_post ctx func cenv cx e es sa sm s0 es1 v x s /\ ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?n r. gas_marked_path F ctx func s n r /\
      ((?t rv. r = OK t /\ res = INL rv /\
          vv_post ctx func cenv cx (Builtin ann Sha256 [e]) es sa sb s0 es2
            rv vv t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts) \/
       (exit_result r /\ expr_exit res r))) ==>
  expr_vv_sim ctx func cenv cx ty (Builtin ann Sha256 [e]) es
Proof
  cheat
QED

Theorem hash_eval_operand_inst_idx[simp]:
  eval_operand op (s with vs_inst_idx := n) = eval_operand op s
Proof
  cheat
QED

Theorem hash_buffer_suffix_shape:
  (compile_keccak256_bytes x sa = (op,sb) \/
   compile_keccak256_bytesm x m sa = (op,sb) \/
   compile_sha256_bytes x sa = (op,sb) \/
   compile_sha256_bytesm x m sa = (op,sb)) ==>
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  cheat
QED

Theorem keccak_suffix_shape:
  (compile_keccak256_bytes x sa = (op,sb) \/
   compile_keccak256_bytesm x m sa = (op,sb)) ==>
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  cheat
QED

Theorem keccak_word_vv_post:
  stmt_state_rel ctx func cenv cx es' s /\
  eval_operand op s = SOME (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
  wb_frame cenv es sa s0 s ==>
  vv_post ctx func cenv cx (Builtin (BaseT (BytesT (Fixed 32))) bt [e])
    es sa sb s0 es' (Value (BytesV (Keccak_256_w64 bs)))
    (StackValue (BaseT (BytesT (Fixed 32))) op) s
Proof
  cheat
QED

Theorem keccak_fixed_post_run:
  expr_post ctx func cenv cx e es sa sm s0 es' (BytesV bs) x s /\
  expr_type e = BaseT (BytesT (Fixed m)) /\
  value_has_type (BaseTV (BytesT (Fixed m))) (BytesV bs) /\ m <= 32 /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_keccak256_bytesm x m sm = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    vv_post ctx func cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Keccak256 [e])
      es sa sb s0 es' (Value (BytesV (Keccak_256_w64 bs)))
      (StackValue (BaseT (BytesT (Fixed 32))) op) t
Proof
  cheat
QED

Theorem keccak_memory_post_run:
  expr_post ctx func cenv cx e es sa sm s0 es' v x s /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_keccak256_bytes x sm = (op,sb) /\
  eval_operand x s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
  b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    vv_post ctx func cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Keccak256 [e])
      es sa sb s0 es' (Value (BytesV (Keccak_256_w64 bs)))
      (StackValue (BaseT (BytesT (Fixed 32))) op) t
Proof
  cheat
QED

Theorem keccak_typed_post_run:
  expr_post ctx func cenv cx e es sa sm s0 es' v x s /\
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  (if is_bytestring_type (expr_type e) then compile_keccak256_bytes x sm
   else case expr_type e of
     BaseT (BytesT (Fixed m)) => compile_keccak256_bytesm x m sm
   | _ => compile_keccak256_word x sm) = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    ?r. builtin_result cx es'.accounts (BaseT (BytesT (Fixed 32)))
      Keccak256 [expr_type e] [v] = INL r /\
    vv_post ctx func cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Keccak256 [e])
      es sa sb s0 es' (Value r) (StackValue (BaseT (BytesT (Fixed 32))) op) t
Proof
  cheat
QED

Theorem cs_appends_stack_value:
  cs_appends code ==> cs_appends (\s. as_stack_val ty (code s))
Proof
  cheat
QED

Theorem keccak_typed_suffix_shape:
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  (if is_bytestring_type (expr_type e) then compile_keccak256_bytes x sm
   else case expr_type e of
     BaseT (BytesT (Fixed m)) => compile_keccak256_bytesm x m sm
   | _ => compile_keccak256_word x sm) = (op,sb) ==>
  same_blocks sm sb /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sm sb)
Proof
  cheat
QED

(* Stack-result specialization: discharge type evaluation and turn a checked
   straight-line post-run boundary into the unary continuation interface. *)
Theorem compile_typed_stack_unary_builtin_vv_sim:
  expr_body_pre cenv cx env (Builtin ann bt [e]) es /\
  expr_sim ctx func cenv cx (expr_type e) e es /\ expr_type e = BaseT bty /\
  ~precompile_builtin bt /\ bt <> Len /\ builtin_args_length_ok bt 1 /\
  (!sa sb vv. compile_expr cenv ty (Builtin ann bt [e]) sa = (vv,sb) ==>
     ?x sm. lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
       as_stack_val ann (code x sm) = (vv,sb)) /\
  (!x. cs_appends (code x)) /\
  (!x sm op sb. code x sm = (op,sb) ==>
     same_blocks sm sb /\
     sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
     EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
       (emitted_insts sm sb)) /\
  (!sa sm sb x op s0 v es' s.
     lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
     code x sm = (op,sb) /\ fn_has_code sm sb func /\
     fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
     local_ptrs_reserved cenv sm /\ value_has_type (BaseTV bty) v /\
     evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
     expr_post ctx func cenv cx e es sa sm s0 es' v x s /\
     MAP FDOM es.scopes = MAP FDOM es'.scopes ==>
     ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
       ?r. builtin_result cx es'.accounts ann bt [expr_type e] [v] = INL r /\
       vv_post ctx func cenv cx (Builtin ann bt [e]) es sa sb s0 es' (Value r)
         (StackValue ann op) t) ==>
  expr_vv_sim ctx func cenv cx ty (Builtin ann bt [e]) es
Proof
  cheat
QED

Theorem compile_keccak256_typed_vv_sim:
  expr_body_pre cenv cx env (Builtin ann Keccak256 [e]) es /\
  expr_sim ctx func cenv cx (expr_type e) e es ==>
  expr_vv_sim ctx func cenv cx ty (Builtin ann Keccak256 [e]) es
Proof
  cheat
QED

Theorem hash_digest_word_vv_post:
  stmt_state_rel ctx func cenv cx es' s /\
  eval_operand op s = SOME w /\
  wb_frame cenv es sa s0 s ==>
  vv_post ctx func cenv cx (Builtin (BaseT (BytesT (Fixed 32))) bt [e])
    es sa sb s0 es' (Value (BytesV (word_to_bytes w T)))
    (StackValue (BaseT (BytesT (Fixed 32))) op) s
Proof
  cheat
QED

Theorem sha256_fixed_fail_frag:
  compile_sha256_bytesm x len sa = (op,sb) /\
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\ eval_operand x s = SOME w /\
  ~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
  MEM (mk_inst (sa.cs_next_id + 2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (sa.cs_next_var + 1))]) (fn_insts func) ==>
  frag_exec ctx sa sb (\t. t = s) Q
    (expr_exit (INR (Error (RuntimeError "precompile failed"))))
Proof
  cheat
QED

Theorem sha256_memory_fail_frag:
  compile_sha256_bytes x sa = (op,sb) /\
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w len /\ b < dimword (:256) /\
  ~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst (sa.cs_next_id + 2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (sa.cs_next_var + 2))]) (fn_insts func) ==>
  frag_exec ctx sa sb (\t. t = s) Q
    (expr_exit (INR (Error (RuntimeError "precompile failed"))))
Proof
  cheat
QED

Theorem sha256_fixed_post_run:
  s.vs_outcomes = outcome::rest /\ outcome.co_success /\
  expr_post ctx func cenv cx e es sa sm s0 es' (BytesV bs) x s /\
  expr_type e = BaseT (BytesT (Fixed m)) /\
  value_has_type (BaseTV (BytesT (Fixed m))) (BytesV bs) /\ m <= 32 /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_sha256_bytesm x m sm = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    vv_post ctx func cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e])
      es sa sb s0 (es' with outcomes := SOME rest)
      (Value (BytesV (word_to_bytes (SHA_256_bytes bs) T)))
      (StackValue (BaseT (BytesT (Fixed 32))) op) t
Proof
  cheat
QED

Theorem sha256_memory_post_run:
  s.vs_outcomes = outcome::rest /\ outcome.co_success /\
  expr_post ctx func cenv cx e es sa sm s0 es' v x s /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_sha256_bytes x sm = (op,sb) /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\
  eval_operand x s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
  b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    vv_post ctx func cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e])
      es sa sb s0 (es' with outcomes := SOME rest)
      (Value (BytesV (word_to_bytes (SHA_256_bytes bs) T)))
      (StackValue (BaseT (BytesT (Fixed 32))) op) t
Proof
  cheat
QED

Theorem sha256_typed_post_run:
  s.vs_outcomes = outcome::rest /\ outcome.co_success /\
  expr_post ctx func cenv cx e es sa sm s0 es' v x s /\
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  (if is_bytestring_type (expr_type e) then compile_sha256_bytes x sm
   else case expr_type e of
     BaseT (BytesT (Fixed m)) => compile_sha256_bytesm x m sm
   | _ => compile_sha256_word x sm) = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    ?r. builtin_result cx es'.accounts (BaseT (BytesT (Fixed 32)))
      Sha256 [expr_type e] [v] = INL r /\
    vv_post ctx func cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e])
      es sa sb s0 (es' with outcomes := SOME rest)
      (Value r) (StackValue (BaseT (BytesT (Fixed 32))) op) t
Proof
  cheat
QED

Theorem sha256_typed_suffix_shape:
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  (if is_bytestring_type (expr_type e) then compile_sha256_bytes x sm
   else case expr_type e of
     BaseT (BytesT (Fixed m)) => compile_sha256_bytesm x m sm
   | _ => compile_sha256_word x sm) = (op,sb) ==>
  same_blocks sm sb /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sm sb)
Proof
  cheat
QED

Theorem sha256_typed_fail_frag:
  ~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) /\
  expr_post ctx func cenv cx e es sa sm s0 es' v x s /\
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  (if is_bytestring_type (expr_type e) then compile_sha256_bytes x sm
   else case expr_type e of
     BaseT (BytesT (Fixed m)) => compile_sha256_bytesm x m sm
   | _ => compile_sha256_word x sm) = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes ==>
  frag_exec ctx sm sb (\t. t = s) Q
    (expr_exit (INR (Error (RuntimeError "precompile failed"))))
Proof
  cheat
QED

Theorem sha256_typed_effectful_suffix:
  expr_post ctx func cenv cx e es sa sm s0 es1 v x s /\
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  (if is_bytestring_type (expr_type e) then compile_sha256_bytes x sm
   else case expr_type e of
     BaseT (BytesT (Fixed m)) => compile_sha256_bytesm x m sm
   | _ => compile_sha256_word x sm) = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  (do precompile_call_success Sha256; return (Value r) od) es1 = (res,es2) /\
  builtin_result cx es1.accounts (BaseT (BytesT (Fixed 32)))
    Sha256 [expr_type e] [v] = INL r ==>
  frag_exec ctx sm sb (\t. t = s)
    (\t. ?rv. res = INL rv /\
      vv_post ctx func cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e])
        es sa sb s0 es2 rv (StackValue (BaseT (BytesT (Fixed 32))) op) t)
    (expr_exit res)
Proof
  cheat
QED

Theorem sha256_typed_fail_run:
  ~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) /\
  expr_post ctx func cenv cx e es sa sm s0 es' v x s /\
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  (if is_bytestring_type (expr_type e) then compile_sha256_bytes x sm
   else case expr_type e of
     BaseT (BytesT (Fixed m)) => compile_sha256_bytesm x m sm
   | _ => compile_sha256_word x sm) = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = Abort Revert_abort t
Proof
  cheat
QED

Theorem sha256_typed_fail_path:
  ~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) /\
  expr_post ctx func cenv cx e es sa sm s0 es' v x s /\
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  (if is_bytestring_type (expr_type e) then compile_sha256_bytes x sm
   else case expr_type e of
     BaseT (BytesT (Fixed m)) => compile_sha256_bytesm x m sm
   | _ => compile_sha256_word x sm) = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?n a t. gas_marked_path F ctx func s n (Abort a t)
Proof
  cheat
QED

(* The digest suffix as an actual counted path: its one GAS site, then the
   precompile call whose outcome the source consumes. *)
Theorem sha256_typed_effectful_path:
  expr_post ctx func cenv cx e es sa sm s0 es1 v x s /\
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  (if is_bytestring_type (expr_type e) then compile_sha256_bytes x sm
   else case expr_type e of
     BaseT (BytesT (Fixed m)) => compile_sha256_bytesm x m sm
   | _ => compile_sha256_word x sm) = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  (do precompile_call_success Sha256; return (Value r) od) es1 = (res,es2) /\
  builtin_result cx es1.accounts (BaseT (BytesT (Fixed 32)))
    Sha256 [expr_type e] [v] = INL r /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?n rr. gas_marked_path F ctx func s n rr /\
    ((?t rv. rr = OK t /\ res = INL rv /\
        vv_post ctx func cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e])
          es sa sb s0 es2 rv (StackValue (BaseT (BytesT (Fixed 32))) op) t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts) \/
     (exit_result rr /\ expr_exit res rr))
Proof
  cheat
QED

Theorem compile_sha256_typed_vv_sim:
  expr_body_pre cenv cx env (Builtin ann Sha256 [e]) es /\
  expr_sim ctx func cenv cx (expr_type e) e es ==>
  expr_vv_sim ctx func cenv cx ty (Builtin ann Sha256 [e]) es
Proof
  cheat
QED

(* The selector's word representation is independent of the hash producer. *)
Theorem method_id_fixed_post_run:
  emit_op SHR [Lit 224w; hash] sm = (sel,sn) /\
  emit_op SHL [Lit 224w; sel] sn = (op,sb) /\
  eval_operand hash s = SOME w /\
  stmt_state_rel ctx func cenv cx es' s /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ wb_frame cenv es sa s0 s ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    vv_post ctx func cenv cx (Builtin (BaseT (BytesT (Fixed 4))) MethodId [e])
      es sa sb s0 es' (Value (BytesV (TAKE 4 (word_to_bytes w T))))
      (StackValue (BaseT (BytesT (Fixed 4))) op) t
Proof
  cheat
QED

Theorem method_id_dynamic_post_run:
  emit_op SHR [Lit 224w; hash] sm = (sel,sn) /\
  emit_op SHL [Lit 224w; sel] sn = (word,sp) /\
  compile_alloc_buffer 64 sp = (buf,sh) /\
  emit_void MSTORE [buf.buf_operand; Lit 4w] sh = ((),st) /\
  emit_op ADD [buf.buf_operand; Lit 32w] st = (data,sd) /\
  emit_void MSTORE [data; word] sd = ((),sb) /\
  eval_operand hash s = SOME w /\
  stmt_state_rel ctx func cenv cx es' s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm /\ fn_has_code sm sb func /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  wb_frame cenv es sa s0 s /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    vv_post ctx func cenv cx (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [e])
      es sa sb s0 es' (Value (BytesV (TAKE 4 (word_to_bytes w T))))
      (LocatedValue (BaseT (BytesT (Dynamic 4)))
        <|ptr_location := LocMemory; ptr_operand := buf.buf_operand|>) t
Proof
  cheat
QED

Theorem method_id_of_keccak_result:
  builtin_result cx acc (BaseT (BytesT (Fixed 32))) Keccak256 [ty] [v] = INL r ==>
  ?bs. r = BytesV bs /\ LENGTH bs = 32 /\
    !ann. builtin_result cx acc ann MethodId [ty] [v] =
      INL (BytesV (TAKE 4 bs))
Proof
  cheat
QED

Theorem hash_full_bytes_roundtrip:
  LENGTH bs = 32 ==>
  word_to_bytes (typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) (BytesV bs)) T = bs
Proof
  cheat
QED

Theorem method_id_hash_as_keccak:
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) ==>
  compile_method_id_hash (expr_type e) x sm =
    (if is_bytestring_type (expr_type e) then compile_keccak256_bytes x sm
     else case expr_type e of
       BaseT (BytesT (Fixed m)) => compile_keccak256_bytesm x m sm
     | _ => compile_keccak256_word x sm)
Proof
  cheat
QED

(* method_id hashes as keccak256 does; only the use of the word differs. *)
Theorem method_id_hash_typed_post_run:
  expr_post ctx func cenv cx e es sa sm s0 es' v x s /\
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_method_id_hash (expr_type e) x sm = (hash,sh) /\
  fn_has_code sm sh func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes ==>
  ?t bs. run_inst_seq (emitted_insts sm sh) s = OK t /\
    LENGTH bs = 32 /\
    eval_operand hash t = SOME
      (typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) (BytesV bs)) /\
    stmt_state_rel ctx func cenv cx es' t /\ wb_frame cenv es sa s0 t /\
    !ann. builtin_result cx es'.accounts ann MethodId [expr_type e] [v] =
      INL (BytesV (TAKE 4 bs))
Proof
  cheat
QED

Theorem method_id_hash_grows:
  compile_method_id_hash ty x sa = (op,sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id
Proof
  cheat
QED

Theorem method_id_tail_shape:
  compile_method_id_runtime ty x fixed sa = (op,sb) /\
  compile_method_id_hash ty x sa = (hash,sm) ==>
  same_blocks sm sb /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sm sb)
Proof
  cheat
QED

Theorem method_id_runtime_typed_post_run:
  expr_post ctx func cenv cx e es sa sm s0 es' v x s /\
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_method_id_runtime (expr_type e) x fixed sm = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes ==>
  ?t r. run_inst_seq (emitted_insts sm sb) s = OK t /\
    builtin_result cx es'.accounts
      (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4)))
      MethodId [expr_type e] [v] = INL r /\
    vv_post ctx func cenv cx
      (Builtin (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4))) MethodId [e])
      es sa sb s0 es' (Value r)
      (if fixed then StackValue (BaseT (BytesT (Fixed 4))) op else
       LocatedValue (BaseT (BytesT (Dynamic 4)))
         <|ptr_location := LocMemory; ptr_operand := op|>) t
Proof
  cheat
QED




Theorem method_id_typed_suffix_shape:
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  compile_method_id_runtime (expr_type e) x fixed sa = (op,sb) ==>
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  cheat
QED

Theorem vv_post_pointer_cong:
  p.ptr_operand = q.ptr_operand /\ p.ptr_location = q.ptr_location /\
  vv_post ctx func cenv cx e es sa sb s0 es' r (LocatedValue ty p) t ==>
  vv_post ctx func cenv cx e es sa sb s0 es' r (LocatedValue ty q) t
Proof
  cheat
QED

Theorem compile_method_id_runtime_typed_vv_sim:
  expr_body_pre cenv cx env (Builtin ann MethodId [e]) es /\
  expr_sim ctx func cenv cx (expr_type e) e es /\ method_id_literal e = NONE ==>
  expr_vv_sim ctx func cenv cx ty (Builtin ann MethodId [e]) es
Proof
  cheat
QED





Theorem compile_method_id_other_typed_vv_sim:
  expr_body_pre cenv cx env (Builtin ann MethodId [e]) es /\
  expr_sim ctx func cenv cx (expr_type e) e es /\
  ~(ann = BaseT (BytesT (Fixed 4)) /\
    ?la l. e = Literal la l /\ IS_SOME (method_id_literal (Literal la l))) ==>
  expr_vv_sim ctx func cenv cx ty (Builtin ann MethodId [e]) es
Proof
  cheat
QED
