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
  list rich_list byte words fragExec ASCIInumbers
  venomExecSemantics venomInst venomState emitHelper emitHelperProps
  builtinHashing exprLoweringProps compileEnv
  exprSim exprSimHyps exprSimLiteralBuffer exprSimWordArgs
  vyperTypeSystem valueEncoding valueEncodingProofs extCallOracle
  vyperAST vyperValue exprLowering vyperInterpreter vyperContext
  vyperValueOperation vyperState exprSimWordBuiltins
  vyperTypeInvariants vyperTypeExprResult vyperTypeExprSoundness
  exprOperandVar

Theorem hash_builtin_types:
  (b = Keccak256 \/ b = Sha256 \/ b = MethodId) /\
  well_typed_builtin_app ty b ts ==>
  ?t. ts = [t] /\ is_bytes_or_string_type t /\
      (if b = MethodId then
         ty = BaseT (BytesT (Dynamic 4)) \/ ty = BaseT (BytesT (Fixed 4))
       else ty = BaseT (BytesT (Fixed 32)))
Proof
  strip_tac >> gvs[well_typed_builtin_app_def] >>
  Cases_on `ts` >> gvs[] >> rename1 `LENGTH rest = 0` >>
  Cases_on `rest` >> gvs[]
QED

Theorem sha256_computed_request:
  rq.cr_target = 2w /\ rq.cr_value = 0 ==>
  computed_precompile rq /\
  take_outcome rq os =
    (failed_outcome rq with
       <| co_success := T;
          co_returnData := word_to_bytes (SHA_256_bytes rq.cr_data) T |>, os) /\
  record_request rq rqs = rqs
Proof
  strip_tac >>
  simp[computed_precompile_def, take_outcome_def, record_request_def]
QED

(* Covers partial words, including the empty byte sequence. *)
Theorem typed_bytes_prefix:
  LENGTH bs <= 32 ==>
  TAKE (LENGTH bs)
    (word_to_bytes_be
      (typed_val_to_w256 (BaseTV (BytesT bd)) (BytesV bs))) = bs
Proof
  strip_tac >> simp[typed_val_to_w256_def] >>
  `LENGTH (PAD_RIGHT (0w:word8) 32 bs) = 32` by
    simp[PAD_RIGHT, LENGTH_GENLIST] >>
  qspec_then `PAD_RIGHT (0w:word8) 32 bs` mp_tac
    TAKE_word_to_bytes_be_word_of_bytes_be >>
  impl_tac >- simp[] >>
  disch_then (mp_tac o Q.AP_TERM `TAKE (LENGTH bs)`) >>
  Cases_on `LENGTH bs < 32` >>
  simp[TAKE_TAKE_MIN, arithmeticTheory.MIN_DEF, PAD_RIGHT, TAKE_APPEND] >>
  `LENGTH bs = 32` by decide_tac >> gvs[]
QED

Theorem expr_val_rel_memory:
  expr_val_rel cx t v op s /\ ~is_word_type t /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  eval_operand op s = SOME w ==>
  val_in_memory tv v (w2n w) s.vs_memory
Proof
  strip_tac >> gvs[expr_val_rel_def] >>
  first_x_assum drule >> simp[]
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
  strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >>
  rw[] >> metis_tac[]
QED

(* A write contained in one region cannot change any disjoint region. *)
Theorem mstore_region_frame:
  b <= a /\ a + 32 <= b + sz /\ regions_disjoint b sz off len ==>
  mem_bytes_at off len (mstore a w s).vs_memory =
  mem_bytes_at off len s.vs_memory
Proof
  strip_tac >>
  irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
  gvs[compileEnvTheory.regions_disjoint_def] >> decide_tac
QED

(* The continuation sees the complete operand postcondition, not just a word.
   Q can in particular be a vv_post for either result representation. *)
Theorem expr_sim_suffix:
  expr_sim ctx func cenv cx ty e es /\
  lower_value compile_expr cenv ty e sa = (op, sm) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (res, es') /\ expr_res_ok res /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  cs_extends sa sm /\ cs_extends sm sb /\
  (!r. expr_exit res r ==> R r) /\
  (!v t. res = INL v /\
     expr_post func cenv cx e es sa sm s0 es' v op t ==>
     frag_exec ctx sm sb (\s. s = t) Q R) ==>
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel func cenv cx es s) Q R
Proof
  strip_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_def] >>
  disch_then drule_all >>
  disch_then (qspec_then `s0` mp_tac) >>
  disch_then (mp_then Any mp_tac frag_exec_weaken) >>
  disch_then (qspecl_then
    [`\s. s = s0 /\ stmt_state_rel func cenv cx es s`,
     `\s. ?v. res = INL v /\
          expr_post func cenv cx e es sa sm s0 es' v op s`, `R`] mp_tac) >>
  simp[] >>
  disch_then (mp_then Any irule frag_exec_then) >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem step_SHA3_bytes:
  eval_operand ptr_op s = SOME p /\ eval_operand len s = SOME n /\
  mem_bytes_at (w2n p) (w2n n) s.vs_memory = bs ==>
  step_inst_base (mk_inst iid SHA3 [ptr_op; len] [out]) s =
  OK (update_var out (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) s)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomInstTheory.mk_inst_def, mem_bytes_at_def]
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
  strip_tac >> drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  drule_all step_SHA3_bytes >> simp[exprLoweringPropsTheory.run_inst_seq_def]
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
  simp[compile_keccak256_bytes_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[Once run_inst_seq_def] >>
  simp[Once step_inst_base_def, mk_inst_def, exec_read1_def] >>
  `eval_operand ptr_op
     (update_var (STRING #"%" (toString sa.cs_next_var)) (mload b s) s) =
     SOME (n2w b)` by
    (Cases_on `ptr_op` >> gvs[eval_operand_def, lookup_var_update_var] >>
     gvs[not_fresh_at_def]) >>
  simp[Once run_inst_seq_def] >>
  simp[Once step_inst_base_def, exec_pure2_def, eval_operand_def,
       bind_outputs_def] >>
  simp[Once run_inst_seq_def] >>
  simp[Once step_inst_base_def, eval_operand_def, lookup_var_update_var,
       toString_inj] >>
  `b < dimword (:256)` by
    gvs[dimword_def, fcpTheory.index_bit0, fcpTheory.finite_bit0,
        fcpTheory.index_one, fcpTheory.finite_one] >>
  `mload b s = n2w (LENGTH bs)` by
    gvs[mload_def, mem_word_at_def] >>
  simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       toString_inj, word_add_n2w,
       GSYM mem_bytes_at_def, run_inst_seq_def] >>
  rpt strip_tac >> gvs[not_fresh_at_def] >>
  first_assum (qspec_then `sa.cs_next_var + 2` assume_tac) >>
  first_assum (qspec_then `sa.cs_next_var + 1` assume_tac) >>
  first_assum (qspec_then `sa.cs_next_var` assume_tac) >> gvs[]
QED

(* Read-only suffixes need only preserve the reserved pointer variables. *)
Theorem hash_readonly_state_rel:
  stmt_state_rel func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (t with vs_vars := s.vs_vars) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
  stmt_state_rel func cenv cx es t
Proof
  strip_tac >>
  `t = s with vs_vars := t.vs_vars` by
    (qpat_x_assum `_ with vs_vars := _ = _`
       (mp_tac o Q.AP_TERM `\z. z with vs_vars := t.vs_vars`) >> simp[]) >>
  `t.vs_memory = s.vs_memory` by
    (qpat_x_assum `_ with vs_vars := _ = _`
       (mp_tac o Q.AP_TERM `\z. z.vs_memory`) >> simp[]) >>
  irule literal_state_memory_frame >> qexists_tac `s` >>
  simp[] >> rpt strip_tac >> first_x_assum irule >>
  gvs[local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem compile_keccak256_bytes_frame:
  compile_keccak256_bytes ptr_op sa = (op, sb) /\
  (!x. ptr_op = Var x ==> not_fresh_at sa x) /\
  eval_operand ptr_op s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
  b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  stmt_state_rel func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME
      (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
    stmt_state_rel func cenv cx es t /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule_all compile_keccak256_bytes_run >> strip_tac >>
  qexists_tac `t` >> simp[] >> irule hash_readonly_state_rel >>
  goal_assum drule >> simp[]
QED

Theorem hash_mstore_prefix:
  LENGTH bs <= 32 /\ TAKE (LENGTH bs) (word_to_bytes_be w) = bs ==>
  mem_bytes_at a (LENGTH bs) (mstore a w s).vs_memory = bs
Proof
  strip_tac >> irule LIST_EQ >> simp[LENGTH_mem_bytes_at_proof] >>
  rpt strip_tac >>
  qspec_then `a` (qspec_then `w` (qspec_then `s` mp_tac))
    valueEncodingPropsTheory.mem_bytes_at_mstore_same >>
  disch_then (mp_tac o Q.AP_TERM `\xs. EL x xs`) >>
  simp[EL_mem_bytes_at] >>
  qpat_x_assum `TAKE _ _ = _` (mp_tac o Q.AP_TERM `\xs. EL x xs`) >>
  simp[EL_TAKE, word_to_bytes_be_def]
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
  strip_tac >> drule_all emit_SHA3_bytes_run >> strip_tac >>
  qexists_tac `update_var out
      (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) s` >>
  simp[eval_operand_def, lookup_var_update_var, update_var_def] >>
  rpt strip_tac >> gvs[not_fresh_at_def, lookup_var_def,
                       finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem hash_alloc_buffer_labels[local]:
  compile_alloc_buffer sz sa = (buf,sm) /\
  run_inst_seq (emitted_insts sa sm) s = OK t ==>
  t.vs_labels = s.vs_labels
Proof
  simp[contextTheory.compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_return_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >> gvs[emitted_insts_def,
       rich_listTheory.DROP_LENGTH_APPEND, run_inst_seq_def,
       step_inst_base_def, mk_inst_def, exec_alloca_def, AllCaseEqs()] >>
  gvs[update_var_def]
QED

(* Allocate and stage one word, protecting every earlier allocation. *)
Theorem hash_alloc_mstore_frame:
  compile_alloc_buffer 32 sa = (buf, sm) /\
  emit_void MSTORE [buf.buf_operand; val_op] sm = ((), sh) /\
  (!x. val_op = Var x ==> not_fresh_at sa x) /\
  eval_operand val_op s = SOME w /\
  stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
  ?t addr. run_inst_seq (emitted_insts sa sh) s = OK t /\
    stmt_state_rel func cenv cx es t /\
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
  strip_tac >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `eval_operand buf.buf_operand allocated = SOME addr` >>
  `allocated.vs_labels = s.vs_labels` by
    (drule_all hash_alloc_buffer_labels >> simp[]) >>
  `eval_operand val_op allocated = SOME w` by
    (Cases_on `val_op` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts sm sh) allocated =
     OK (mstore (w2n addr) w allocated)` by
    (irule literal_emit_mstore_run >>
     qexistsl_tac [`buf.buf_operand`, `val_op`] >> simp[]) >>
  `stmt_state_rel func cenv cx es (mstore (w2n addr) w allocated)` by
    (irule literal_mstore_state_rel >> simp[] >>
     qexistsl_tac [`w2n addr`,
       `mk_inst sa.cs_next_id ALLOCA [Lit 32w]
          [STRING #"%" (toString sa.cs_next_var)]`, `32`] >>
     simp[mk_inst_def] >> rpt strip_tac >>
     first_x_assum drule >> simp[regions_disjoint_def]) >>
  suspend "compose"
QED

Resume hash_alloc_mstore_frame[compose]:
  `sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
   sh.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sh /\
   sh.cs_next_var = sa.cs_next_var + 1 /\
   sh.cs_next_id = sa.cs_next_id + 2 /\
   (!x. buf.buf_operand = Var x ==> not_fresh_at sh x)` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> rpt strip_tac >>
     gvs[emitted_insts_def, not_fresh_at_def, toString_inj,
       rich_listTheory.DROP_LENGTH_APPEND, rich_listTheory.DROP_APPEND1,
       rich_listTheory.DROP_APPEND2]) >>
  `local_ptrs_reserved cenv sh` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `run_inst_seq (emitted_insts sa sh) s =
     run_inst_seq (emitted_insts sm sh) allocated` by
    (irule (cj 1 run_inst_seq_chain) >> simp[]) >>
  `sh.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sh` by
    (irule (cj 2 run_inst_seq_chain) >> goal_assum drule >> simp[]) >>
  `eval_operand buf.buf_operand (mstore (w2n addr) w allocated) = SOME addr` by
    gvs[mstore_def, eval_operand_def, lookup_var_def] >>
  `!aid b len. aid < sa.cs_next_id /\
     FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
     mem_bytes_at b len (mstore (w2n addr) w allocated).vs_memory =
     mem_bytes_at b len s.vs_memory` by
    (rpt strip_tac >>
     `mem_bytes_at b len (mstore (w2n addr) w allocated).vs_memory =
      mem_bytes_at b len allocated.vs_memory` by
       (irule mstore_region_frame >> qexistsl_tac [`w2n addr`, `32`] >>
        simp[] >> qpat_x_assum `!aid b len. aid < sa.cs_next_id /\ _ ==> _` irule >>
        qexists_tac `aid` >> simp[]) >> simp[]) >>
  `!n b sz. local_region cenv es.scopes s n b sz ==>
    mem_bytes_at b sz (mstore (w2n addr) w allocated).vs_memory =
    mem_bytes_at b sz s.vs_memory` by
    (match_mp_tac exprSimOpsTheory.local_regions_memory_tail >>
     qexistsl [`sa`, `es.scopes`, `allocated`] >> simp[] >>
     rpt strip_tac >>
     qpat_x_assum `allocated.vs_memory = s.vs_memory`
       (fn th => pure_rewrite_tac[GSYM th]) >>
     irule mstore_region_frame >>
     qexistsl [`w2n addr`, `32`] >> simp[] >>
     qpat_x_assum `!name b len. local_region _ _ allocated _ _ _ ==> _` drule >> simp[]) >>
  qexistsl_tac [`mstore (w2n addr) w allocated`, `addr`] >>
  simp[] >> gvs[mstore_def, lookup_var_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Finalise hash_alloc_mstore_frame

Theorem compile_keccak256_bytesm_frame:
  compile_keccak256_bytesm val_op (LENGTH bs) sa = (op, sb) /\
  (!x. val_op = Var x ==> not_fresh_at sa x) /\
  eval_operand val_op s = SOME w /\
  LENGTH bs <= 32 /\ TAKE (LENGTH bs) (word_to_bytes_be w) = bs /\
  stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME
      (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
    stmt_state_rel func cenv cx es t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
    (!n b sz. local_region cenv es.scopes s n b sz ==>
      mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory)
Proof
  strip_tac >>
  qpat_x_assum `compile_keccak256_bytesm _ _ _ = _` mp_tac >>
  simp_tac (bool_ss ++ pairSimps.PAIR_ss)
    [compile_keccak256_bytesm_def, LET_THM, comp_bind_def, comp_ignore_bind_def,
     comp_return_def] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  strip_tac >> gvs[] >>
  rename1 `compile_alloc_buffer 32 sa = (buf,sm)` >>
  rename1 `emit_void MSTORE [buf.buf_operand; val_op] sm = (u,sh)` >>
  Cases_on `u` >>
  drule_all hash_alloc_mstore_frame >> strip_tac >>
  `LENGTH bs < dimword (:256)` by (simp[dimword_def] >> decide_tac) >>
  rename1 `run_inst_seq (emitted_insts sa sh) s = OK staged` >>
  `eval_operand (Lit (n2w (LENGTH bs))) staged = SOME (n2w (LENGTH bs))` by
    simp[eval_operand_def] >>
  `mem_bytes_at (w2n addr) (w2n (n2w (LENGTH bs):bytes32)) staged.vs_memory = bs` by
    (simp[] >> irule hash_mstore_prefix >> simp[]) >>
  drule_all emit_SHA3_bytes_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sh sb) staged = OK final` >>
  `stmt_state_rel func cenv cx es final` by
    (irule hash_readonly_state_rel >> goal_assum drule >> simp[]) >>
  `final.vs_memory = staged.vs_memory /\ final.vs_allocas = staged.vs_allocas` by
    (qpat_x_assum `final with vs_vars := _ = _`
       (mp_tac o Q.AP_TERM `\z. (z.vs_memory, z.vs_allocas)`) >> simp[]) >>
  `sb.cs_current_insts = sh.cs_current_insts ++ emitted_insts sh sb` by
    (qpat_x_assum `emit_op SHA3 _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
       fresh_var_def, emit_def] >> strip_tac >>
     gvs[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND]) >>
  `run_inst_seq (emitted_insts sa sb) s =
     run_inst_seq (emitted_insts sh sb) staged` by
    (irule (cj 1 run_inst_seq_chain) >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x final = lookup_var x s` by
    (rpt strip_tac >>
     `not_fresh_at sh x` by gvs[not_fresh_at_def] >>
     qpat_x_assum `!x. not_fresh_at sh x ==> _` drule >>
     qpat_x_assum `!x. not_fresh_at sa x ==> _` drule >> simp[]) >>
  qexists_tac `final` >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!aid b len. aid < sa.cs_next_id /\ _ ==> _` drule >> simp[]) >>
  metis_tac[]
QED

(* Observational frames include zero-filled windows beyond allocated memory. *)
Theorem hash_write_memory_disjoint:
  off + len <= dst \/ dst + LENGTH bytes <= off ==>
  mem_bytes_at off len (write_memory_with_expansion dst bytes s).vs_memory =
  mem_bytes_at off len s.vs_memory
Proof
  strip_tac >> irule LIST_EQ >> simp[LENGTH_mem_bytes_at_proof] >>
  rpt strip_tac >> Cases_on `dst + LENGTH bytes > LENGTH s.vs_memory` >>
  simp[write_memory_with_expansion_def, LET_THM, EL_mem_bytes_at,
       EL_APPEND_EQN, LENGTH_TAKE, rich_listTheory.LENGTH_REPLICATE,
       EL_TAKE, EL_DROP, EL_REPLICATE] >>
  rpt IF_CASES_TAC >> gvs[EL_APPEND_EQN, EL_REPLICATE]
QED

Theorem hash_write_memory_read_self:
  mem_bytes_at dst (LENGTH bytes)
    (write_memory_with_expansion dst bytes s).vs_memory = bytes
Proof
  mp_tac venomMemPropsTheory.write_memory_with_expansion_read_self >>
  disch_then (qspecl_then [`dst`, `bytes`, `s`] assume_tac) >>
  `LENGTH (DROP dst (write_memory_with_expansion dst bytes s).vs_memory) >=
   LENGTH bytes` by
    (qpat_x_assum `TAKE _ _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[LENGTH_TAKE_EQ] >>
     rpt IF_CASES_TAC >> simp[] >> decide_tac) >>
  gvs[mem_bytes_at_def, TAKE_APPEND, arithmeticTheory.MIN_DEF]
QED

Theorem sha256_consume_outcome:
  rq.cr_target = 2w /\ rq.cr_value = 0 /\ rq.cr_static ==>
  consume_call_outcome rq ro 32 s =
    (1w, (write_memory_with_expansion ro
       (word_to_bytes (SHA_256_bytes rq.cr_data) T) s) with
       vs_returndata := word_to_bytes (SHA_256_bytes rq.cr_data) T)
Proof
  strip_tac >> drule_all sha256_computed_request >> strip_tac >>
  simp[venomCallOracleDefsTheory.consume_call_outcome_eq,
       failed_outcome_def, TAKE_LENGTH_TOO_LONG, LENGTH_word_to_bytes,
       write_memory_with_expansion_def, LET_THM,
       venom_state_component_equality]
QED

Theorem sha256_exec_ext_call:
  read_memory (w2n args_off) (w2n args_size) s = bs ==>
  exec_ext_call (mk_inst iid STATICCALL ops [out]) s gas 2w 0w
    args_off args_size ret_off (32w:bytes32) T =
  OK (update_var out 1w
      ((write_memory_with_expansion (w2n ret_off)
         (word_to_bytes (SHA_256_bytes bs) T) s) with
         vs_returndata := word_to_bytes (SHA_256_bytes bs) T))
Proof
  strip_tac >>
  `(w2w (2w:bytes32):address) = 2w` by
    simp[w2w_n2w, fcpTheory.index_bit0, fcpTheory.index_bit1,
         fcpTheory.finite_bit0, fcpTheory.finite_bit1,
         fcpTheory.index_one, fcpTheory.finite_one] >>
  `consume_call_outcome
     (venom_call_request s 2w 0w args_off args_size T) (w2n ret_off) 32 s =
   (1w, (write_memory_with_expansion (w2n ret_off)
         (word_to_bytes (SHA_256_bytes bs) T) s) with
         vs_returndata := word_to_bytes (SHA_256_bytes bs) T)` by
    (qspecl_then [`venom_call_request s 2w 0w args_off args_size T`,
                    `w2n ret_off`, `s`] mp_tac
       (Q.GENL [`rq`, `ro`, `s`] sha256_consume_outcome) >>
     simp[venomCallOracleDefsTheory.venom_call_request_def,
          w2w_n2w, Excl "consume_call_outcome_eq"] ) >>
  simp[exec_ext_call_def, mk_inst_def, Excl "consume_call_outcome_eq",
       dimword_def, fcpTheory.index_bit0, fcpTheory.finite_bit0,
       fcpTheory.index_one, fcpTheory.finite_one]
QED

Theorem hash_returndata_immutable_alloca_sep[local]:
  immutable_alloca_sep func cenv cx es (s with vs_returndata := data) <=>
  immutable_alloca_sep func cenv cx es s
Proof
  simp[immutable_alloca_sep_def, local_region_def, lookup_var_def]
QED

Theorem hash_returndata_state_rel:
  stmt_state_rel func cenv cx es (s with vs_returndata := data) <=>
  stmt_state_rel func cenv cx es s
Proof
  simp[stmt_state_rel_def, state_rel_def,
       hash_returndata_immutable_alloca_sep,
       local_ptrs_rel_def, local_region_def, local_backed_def,
       lookup_var_def, storage_rel_def, transient_rel_def, immutables_rel_def,
       logs_rel_def, call_ctx_rel_def, accounts_rel_def,
       contract_storage_def, contract_transient_def,
       venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def,
       alloca_room_def, pending_alloca_size_def]
QED

Theorem step_STATICCALL_sha256:
  eval_operand gas_op s = SOME gas /\
  eval_operand args_op s = SOME args_off /\
  eval_operand size_op s = SOME args_size /\
  eval_operand ret_op s = SOME ret_off /\
  read_memory (w2n args_off) (w2n args_size) s = bs ==>
  step_inst_base
    (mk_inst iid STATICCALL [gas_op; Lit 2w; args_op; size_op; ret_op; Lit 32w] [out]) s =
  OK (update_var out 1w
      ((write_memory_with_expansion (w2n ret_off)
         (word_to_bytes (SHA_256_bytes bs) T) s) with
         vs_returndata := word_to_bytes (SHA_256_bytes bs) T))
Proof
  strip_tac >> simp[Once step_inst_base_def, mk_inst_def, eval_operand_def] >>
  irule (SRULE [mk_inst_def] sha256_exec_ext_call) >> simp[]
QED

Theorem hash_mload_write_word:
  mload dst (write_memory_with_expansion dst (word_to_bytes (w:bytes32) T) s) = w
Proof
  qspecl_then [`dst`, `word_to_bytes (w:bytes32) T`, `s`] mp_tac
    (Q.GENL [`dst`, `bytes`, `s`] hash_write_memory_read_self) >>
  simp[LENGTH_word_to_bytes, mload_def, read_memory_def,
       GSYM mem_bytes_at_def, word_of_bytes_word_to_bytes]
QED

(* Shared computed-precompile tail, independent of input representation. *)
Theorem sha256_tail_run:
  eval_operand ptr_op s = SOME p /\
  eval_operand len_op s = SOME n /\
  eval_operand ret_op s = SOME r /\
  (!x. ptr_op = Var x \/ len_op = Var x \/ ret_op = Var x ==> x <> gas_var) /\
  (!x. ret_op = Var x ==> x <> success_var) /\
  mem_bytes_at (w2n p) (w2n n) s.vs_memory = bs ==>
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
          (update_var gas_var (n2w s.vs_call_ctx.cc_gas) s)) with
        vs_returndata := word_to_bytes (SHA_256_bytes bs) T)))
Proof
  strip_tac >>
  `eval_operand ptr_op (update_var gas_var (n2w s.vs_call_ctx.cc_gas) s) = SOME p /\
   eval_operand len_op (update_var gas_var (n2w s.vs_call_ctx.cc_gas) s) = SOME n /\
   eval_operand ret_op (update_var gas_var (n2w s.vs_call_ctx.cc_gas) s) = SOME r` by
    (rpt conj_tac >> Cases_on `ptr_op` >> Cases_on `len_op` >> Cases_on `ret_op` >>
     gvs[eval_operand_def, lookup_var_update_var]) >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
       exec_read0_def, bind_outputs_def] >>
  `read_memory (w2n p) (w2n n)
     (update_var gas_var (n2w s.vs_call_ctx.cc_gas) s) = bs` by
    simp[read_memory_def, update_var_def, GSYM mem_bytes_at_def] >>
  `eval_operand (Var gas_var) (update_var gas_var (n2w s.vs_call_ctx.cc_gas) s) =
     SOME (n2w s.vs_call_ctx.cc_gas)` by simp[eval_operand_def, lookup_var_update_var] >>
  `step_inst_base
    (mk_inst i1 STATICCALL [Var gas_var; Lit 2w; ptr_op; len_op; ret_op; Lit 32w]
      [success_var]) (update_var gas_var (n2w s.vs_call_ctx.cc_gas) s) =
   OK (update_var success_var 1w
     ((write_memory_with_expansion (w2n r) (word_to_bytes (SHA_256_bytes bs) T)
       (update_var gas_var (n2w s.vs_call_ctx.cc_gas) s)) with
       vs_returndata := word_to_bytes (SHA_256_bytes bs) T))` by
    (irule step_STATICCALL_sha256 >> simp[] >> goal_assum drule >> simp[]) >>
  fs[mk_inst_def] >> simp[Once run_inst_seq_def] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, eval_operand_def,
       lookup_var_update_var] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq _ final` >>
  `eval_operand ret_op final = SOME r` by
    (Cases_on `ret_op` >>
     gvs[Abbr `final`, eval_operand_def, lookup_var_update_var,
         write_memory_with_expansion_def, LET_THM, update_var_def, lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE]) >>
  `mload (w2n r) final = SHA_256_bytes bs` by
    (simp[Abbr `final`, mload_def, update_var_def] >>
     mp_tac (Q.SPECL [`w2n (r:bytes32)`, `SHA_256_bytes bs`, `s`]
       (Q.GENL [`dst`, `w`, `s`] hash_mload_write_word)) >>
     simp[mload_def, write_memory_with_expansion_def, LET_THM]) >>
  simp[run_inst_seq_def, Once step_inst_base_def, exec_read1_def,
       bind_outputs_def, Abbr `final`]
QED

Theorem sha256_tail_frame:
  eval_operand ptr_op s = SOME p /\ eval_operand len_op s = SOME n /\
  eval_operand ret_op s = SOME r /\
  (!x. ptr_op = Var x \/ len_op = Var x \/ ret_op = Var x ==> x <> gas_var) /\
  (!x. ret_op = Var x ==> x <> success_var) /\
  mem_bytes_at (w2n p) (w2n n) s.vs_memory = bs /\
  stmt_state_rel func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> x <> gas_var /\ x <> success_var /\ x <> out) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     b + sz <= w2n r \/ w2n r + 32 <= b) /\
  (cenv.ce_is_ctor ==> !name tv v off.
     FLOOKUP cenv.ce_vars (module_var_key (cenv.ce_module,name)) =
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
    stmt_state_rel func cenv cx es t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\
    (!b len. b + len <= w2n r \/ w2n r + 32 <= b ==>
       mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory)
Proof
  strip_tac >>
  drule_all sha256_tail_run >>
  disch_then (qspecl_then [`out`, `i3`, `i2`, `i1`, `i0`] mp_tac) >>
  qmatch_goalsub_abbrev_tac `run_inst_seq _ s = OK final` >>
  strip_tac >> qexists_tac `final` >> simp[] >>
  `!x. not_fresh_at sa x ==> lookup_var x final = lookup_var x s` by
    (rpt strip_tac >> first_x_assum drule >>
     simp[Abbr `final`, update_var_def, lookup_var_def,
          write_memory_with_expansion_def, LET_THM, finite_mapTheory.FLOOKUP_UPDATE]) >>
  `final.vs_allocas = s.vs_allocas /\
   final.vs_memory = (write_memory_with_expansion (w2n r)
     (word_to_bytes (SHA_256_bytes bs) T) s).vs_memory` by
    simp[Abbr `final`, update_var_def, write_memory_with_expansion_def, LET_THM] >>
  `eval_operand (Var out) final = SOME (SHA_256_bytes bs)` by
    simp[Abbr `final`, eval_operand_def, lookup_var_update_var] >>
  simp[] >> reverse conj_tac
  >- (rpt strip_tac >> irule hash_write_memory_disjoint >> simp[]) >>
  `stmt_state_rel func cenv cx es (final with vs_returndata := s.vs_returndata)` suffices_by
    (simp[hash_returndata_state_rel]) >>
  irule literal_state_memory_frame >> qexists_tac `s` >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> irule hash_write_memory_disjoint >> simp[] >>
      first_x_assum drule >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> rename1 `PtrVar (Var name_var) sz` >>
      `not_fresh_at sa name_var` by
        (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
      qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x final = _` drule >>
      simp[lookup_var_def]) >>
  simp[Abbr `final`, update_var_def, LET_THM] >>
  conj_tac
  >- simp[immutableMemoryFrameTheory.immutable_write_memory_capacity, arithmeticTheory.MAX_DEF] >>
  conj_tac
  >- simp[write_memory_with_expansion_def, LET_THM] >>
  rpt strip_tac >> irule hash_write_memory_disjoint >>
  simp[] >> metis_tac[regions_disjoint_def]
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
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND]
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
  stmt_state_rel func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     b + sz <= w2n r \/ w2n r + 32 <= b) /\
  (cenv.ce_is_ctor ==> !name tv v off.
     FLOOKUP cenv.ce_vars (module_var_key (cenv.ce_module,name)) =
       SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name =
       SOME (tv,v) ==>
     regions_disjoint off (type_memory_size tv) (w2n r) 32) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (SHA_256_bytes bs) /\
    stmt_state_rel func cenv cx es t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\
    (!b len. b + len <= w2n r \/ w2n r + 32 <= b ==>
       mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory)
Proof
  strip_tac >> drule_all emitted_insts_sha256_tail >> strip_tac >> gvs[] >>
  irule sha256_tail_frame >> simp[] >>
  conj_tac >- metis_tac[] >>
  `!k. sa.cs_next_var <= k ==>
     ptr_op <> Var (STRING #"%" (toString k)) /\
     len_op <> Var (STRING #"%" (toString k)) /\
     ret_op <> Var (STRING #"%" (toString k))` by
    (rpt strip_tac >>
     qpat_x_assum `!x. _ ==> not_fresh_at sa x`
       (qspec_then `STRING #"%" (toString k)` mp_tac) >>
     simp[not_fresh_at_def] >> metis_tac[]) >>
  simp[] >> rpt strip_tac >> gvs[not_fresh_at_def] >> metis_tac[]
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
  stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (SHA_256_bytes bs) /\
    stmt_state_rel func cenv cx es t /\
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
  strip_tac >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sn) s = OK allocated` >>
  `allocated.vs_labels = s.vs_labels` by
    (drule_all hash_alloc_buffer_labels >> simp[]) >>
  `eval_operand ptr_op allocated = SOME p /\
   eval_operand len_op allocated = SOME n` by
    (Cases_on `ptr_op` >> Cases_on `len_op` >>
     gvs[eval_operand_def] >> metis_tac[]) >>
  `sn.cs_next_var = sa.cs_next_var + 1 /\
   sn.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sn` by
    (qpat_x_assum `compile_alloc_buffer 32 sa = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[contextTheory.compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
       emit_def] >> strip_tac >> gvs[emitted_insts_def,
       rich_listTheory.DROP_LENGTH_APPEND]) >>
  `local_ptrs_reserved cenv sn` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!x. ptr_op = Var x \/ len_op = Var x \/ buf.buf_operand = Var x ==>
       not_fresh_at sn x` by
    (rpt strip_tac >> gvs[] >> gvs[not_fresh_at_def] >> metis_tac[]) >>
  `!name base len. local_region cenv es.scopes allocated name base len ==>
     base + len <= w2n w \/ w2n w + 32 <= base` by
    (rpt strip_tac >> first_x_assum drule >> simp[regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at (w2n p) (w2n n) allocated.vs_memory = bs` by simp[] >>
  `(cenv.ce_is_ctor ==> !name tv v off.
     FLOOKUP cenv.ce_vars (module_var_key (cenv.ce_module,name)) =
       SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name =
       SOME (tv,v) ==>
     regions_disjoint off (type_memory_size tv) (w2n w) 32)` by
    (rpt strip_tac >>
     qpat_assum `stmt_state_rel func cenv cx es allocated` mp_tac >>
     pure_rewrite_tac[stmt_state_rel_def, immutable_alloca_sep_def] >> strip_tac >>
     qpat_x_assum `cenv.ce_is_ctor ==> _` drule >>
     disch_then drule_all >> strip_tac >>
     qpat_x_assum `!inst b sz. MEM inst _ /\ _ ==> _`
       (qspec_then `mk_inst sa.cs_next_id ALLOCA [Lit 32w]
         [STRING #"%" (toString sa.cs_next_var)]` mp_tac) >>
     simp[mk_inst_def]) >>
  drule_all emit_sha256_tail_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sn sb) allocated = OK final` >>
  suspend "compose"
QED

Resume hash_alloc_sha256_tail_frame[compose]:
  `sb.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sb` by
    (drule_all emitted_insts_sha256_tail >> strip_tac >> simp[]) >>
  `run_inst_seq (emitted_insts sa sb) s =
     run_inst_seq (emitted_insts sn sb) allocated` by
    (irule (cj 1 run_inst_seq_chain) >> simp[]) >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (irule (cj 2 run_inst_seq_chain) >> goal_assum drule >> simp[]) >>
  `!nm b sz. local_region cenv es.scopes s nm b sz ==>
    mem_bytes_at b sz final.vs_memory = mem_bytes_at b sz s.vs_memory` by
    (match_mp_tac exprSimOpsTheory.local_regions_memory_tail >>
     qexistsl [`sa`, `es.scopes`, `allocated`] >> simp[] >>
     rpt strip_tac >>
     qpat_x_assum `!b len. _ \/ _ ==> mem_bytes_at b len final.vs_memory = _`
       (qspecl_then [`b`, `sz`] mp_tac) >>
     impl_tac >- metis_tac[regions_disjoint_def] >> simp[]) >>
  qexists_tac `final` >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sn x` by gvs[not_fresh_at_def] >>
      qpat_x_assum `!x. not_fresh_at sn x ==> _` drule >>
      qpat_x_assum `!x. not_fresh_at sa x ==> _` drule >> simp[]) >>
  reverse conj_tac >- metis_tac[] >>
  rpt strip_tac >> rename1 `FLOOKUP s.vs_allocas aid = SOME (region_base,len)` >>
  `regions_disjoint (w2n w) 32 region_base len` by
    (qpat_x_assum `!aid b len. aid < sa.cs_next_id /\ _ ==> _` irule >>
     qexists_tac `aid` >> simp[]) >>
  qpat_x_assum `!b len. _ \/ _ ==> mem_bytes_at b len final.vs_memory = _`
    (qspecl_then [`region_base`, `len`] mp_tac) >>
  gvs[regions_disjoint_def] >> decide_tac
QED

Finalise hash_alloc_sha256_tail_frame

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
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
       fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  `eval_operand ptr_op
     (update_var (STRING #"%" (toString sa.cs_next_var)) (mload b s) s) =
   SOME (n2w b)` by
    (Cases_on `ptr_op` >> gvs[eval_operand_def, lookup_var_update_var,
                            not_fresh_at_def]) >>
  `mload b s = n2w len` by gvs[mload_def, mem_word_at_def] >>
  simp[emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND, Once run_inst_seq_def] >>
  simp[Once step_inst_base_def, mk_inst_def, exec_read1_def] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
       exec_pure2_def, eval_operand_def, bind_outputs_def] >>
  fs[update_var_def] >>
  simp[run_inst_seq_def, eval_operand_def, lookup_var_update_var,
       word_add_n2w, toString_inj, update_var_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE, not_fresh_at_def] >>
  rpt strip_tac >> gvs[toString_inj] >>
  first_assum (qspec_then `sa.cs_next_var` assume_tac) >>
  first_assum (qspec_then `sa.cs_next_var + 1` assume_tac) >> gvs[]
QED

Theorem compile_sha256_bytes_frame:
  compile_sha256_bytes ptr_op sa = (op, sb) /\
  (!x. ptr_op = Var x ==> not_fresh_at sa x) /\
  eval_operand ptr_op s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
  b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst (sa.cs_next_id + 2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (sa.cs_next_var + 2))]) (fn_insts func) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (SHA_256_bytes bs) /\
    stmt_state_rel func cenv cx es t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid base len. aid < sa.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (base,len) ==>
       mem_bytes_at base len t.vs_memory = mem_bytes_at base len s.vs_memory) /\
    (!nm base sz. local_region cenv es.scopes s nm base sz ==>
      mem_bytes_at base sz t.vs_memory = mem_bytes_at base sz s.vs_memory)
Proof
  strip_tac >>
  qpat_x_assum `compile_sha256_bytes _ _ = _` mp_tac >>
  simp_tac (bool_ss ++ pairSimps.PAIR_ss)
    [compile_sha256_bytes_def, LET_THM, comp_bind_def, comp_ignore_bind_def,
     comp_return_def] >>
  ntac 6 (pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) []) >>
  strip_tac >> gvs[] >>
  rename1 `emit_op MLOAD [ptr_op] sa = (length_op, sl)` >>
  rename1 `emit_op ADD [ptr_op; Lit 32w] sl = (data_op, sm)` >>
  rename1 `compile_alloc_buffer 32 sm = (buf, sn)` >>
  rename1 `emit_op GAS [] sn = (gas_op, sg)` >>
  rename1 `emit_op STATICCALL _ sg = (success_op, sc)` >>
  rename1 `emit_void ASSERT [success_op] sc = (u, sh)` >> Cases_on `u` >>
  `b < dimword (:256)` by
    gvs[dimword_def, fcpTheory.index_bit0, fcpTheory.finite_bit0,
        fcpTheory.index_one, fcpTheory.finite_one] >>
  drule_all hash_data_prefix_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK prefix` >>
  `stmt_state_rel func cenv cx es prefix` by
    (irule hash_readonly_state_rel >> goal_assum drule >> simp[]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit 32w]
     [STRING #"%" (toString sm.cs_next_var)]) (fn_insts func)` by simp[] >>
  `prefix.vs_memory = s.vs_memory /\ prefix.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `prefix with vs_vars := _ = _`
       (mp_tac o Q.AP_TERM `\z. (z.vs_memory,z.vs_allocas)`) >> simp[]) >>
  `mem_bytes_at (w2n (n2w (b + 32):bytes32))
     (w2n (n2w (LENGTH bs):bytes32)) prefix.vs_memory = bs` by simp[] >>
  `!x. data_op = Var x \/ length_op = Var x ==> not_fresh_at sm x` by
    metis_tac[] >>
  drule_all hash_alloc_sha256_tail_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sm sb) prefix = OK final` >>
  `run_inst_seq (emitted_insts sa sb) s =
     run_inst_seq (emitted_insts sm sb) prefix` by
    (irule (cj 1 run_inst_seq_chain) >> simp[]) >>
  `!nm lb sz. local_region cenv es.scopes s nm lb sz ==>
    mem_bytes_at lb sz final.vs_memory = mem_bytes_at lb sz s.vs_memory` by
    (match_mp_tac exprSimOpsTheory.local_regions_memory_tail >>
     qexistsl [`sa`, `es.scopes`, `prefix`] >> gvs[] >> metis_tac[]) >>
  qexists_tac `final` >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sm x` by gvs[not_fresh_at_def] >>
      qpat_x_assum `!x. not_fresh_at sm x ==> _` drule >>
      qpat_x_assum `!x. not_fresh_at sa x ==> _` drule >> simp[]) >>
  reverse conj_tac >- metis_tac[] >>
  rpt strip_tac >> rename1 `FLOOKUP s.vs_allocas aid = SOME (region_base,len)` >>
  qpat_x_assum `!aid base len. aid < sm.cs_next_id /\ _ ==> _`
    (qspecl_then [`aid`, `region_base`, `len`] mp_tac) >> simp[]
QED

Theorem compile_sha256_bytesm_frame:
  compile_sha256_bytesm val_op (LENGTH bs) sa = (op, sb) /\
  (!x. val_op = Var x ==> not_fresh_at sa x) /\
  eval_operand val_op s = SOME w /\
  LENGTH bs <= 32 /\ TAKE (LENGTH bs) (word_to_bytes_be w) = bs /\
  stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
  MEM (mk_inst (sa.cs_next_id + 2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (sa.cs_next_var + 1))]) (fn_insts func) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (SHA_256_bytes bs) /\
    stmt_state_rel func cenv cx es t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
    (!nm lb sz. local_region cenv es.scopes s nm lb sz ==>
      mem_bytes_at lb sz t.vs_memory = mem_bytes_at lb sz s.vs_memory)
Proof
  strip_tac >>
  qpat_x_assum `compile_sha256_bytesm _ _ _ = _` mp_tac >>
  simp_tac (bool_ss ++ pairSimps.PAIR_ss)
    [compile_sha256_bytesm_def, LET_THM, comp_bind_def, comp_ignore_bind_def,
     comp_return_def] >>
  ntac 6 (pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) []) >>
  strip_tac >> gvs[] >>
  rename1 `compile_alloc_buffer 32 sa = (in_buf,sm)` >>
  rename1 `emit_void MSTORE [in_buf.buf_operand; val_op] sm = (u,sd)` >>
  rename1 `compile_alloc_buffer 32 sd = (out_buf,sn)` >>
  rename1 `emit_op GAS [] sn = (gas_op,sg)` >>
  rename1 `emit_op STATICCALL _ sg = (success_op,sc)` >>
  rename1 `emit_void ASSERT [success_op] sc = (v,sh)` >>
  Cases_on `v` >>
  drule_all hash_alloc_mstore_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sd) s = OK staged` >>
  `LENGTH bs < dimword (:256)` by (simp[dimword_def] >> decide_tac) >>
  `eval_operand (Lit (n2w (LENGTH bs))) staged = SOME (n2w (LENGTH bs))` by
    simp[eval_operand_def] >>
  `mem_bytes_at (w2n addr) (w2n (n2w (LENGTH bs):bytes32)) staged.vs_memory = bs` by
    (simp[] >> irule hash_mstore_prefix >> simp[]) >>
  `!x. in_buf.buf_operand = Var x \/ Lit (n2w (LENGTH bs)) = Var x ==>
       not_fresh_at sd x` by simp[] >>
  `MEM (mk_inst sd.cs_next_id ALLOCA [Lit 32w]
     [STRING #"%" (toString sd.cs_next_var)]) (fn_insts func)` by simp[] >>
  drule_all hash_alloc_sha256_tail_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sd sb) staged = OK final` >>
  suspend "compose"
QED

Resume compile_sha256_bytesm_frame[compose]:
  `run_inst_seq (emitted_insts sa sb) s =
     run_inst_seq (emitted_insts sd sb) staged` by
    (irule (cj 1 run_inst_seq_chain) >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x final = lookup_var x s` by
    (rpt strip_tac >>
     `not_fresh_at sd x` by gvs[not_fresh_at_def] >>
     qpat_x_assum `!x. not_fresh_at sd x ==> _` drule >>
     qpat_x_assum `!x. not_fresh_at sa x ==> _` drule >> simp[]) >>
  `!nm lb sz. local_region cenv es.scopes s nm lb sz ==>
    mem_bytes_at lb sz final.vs_memory = mem_bytes_at lb sz s.vs_memory` by
    (match_mp_tac exprSimOpsTheory.local_regions_memory_tail >>
     qexistsl [`sa`, `es.scopes`, `staged`] >> simp[] >> metis_tac[]) >>
  qexists_tac `final` >> simp[] >> reverse conj_tac
  >- metis_tac[] >> rpt strip_tac >>
  `FLOOKUP staged.vs_allocas aid = SOME (b,len)` by metis_tac[] >>
  qpat_x_assum `!aid base len. aid < sd.cs_next_id /\ _ ==> _`
    (qspecl_then [`aid`, `b`, `len`] mp_tac) >>
  qpat_x_assum `!aid b len. aid < sa.cs_next_id /\ _ ==> _`
    (qspecl_then [`aid`, `b`, `len`] mp_tac) >> simp[]
QED

Finalise compile_sha256_bytesm_frame

Theorem hash_take_word_to_bytes:
  n <= dimindex (:'a) DIV 8 ==>
  TAKE n (word_to_bytes (w:'a word) be) = word_to_bytes_aux n w be
Proof
  strip_tac >> irule LIST_EQ >> simp[LENGTH_TAKE_EQ] >>
  rpt strip_tac >> simp[EL_TAKE, word_to_bytes_def, EL_word_to_bytes_aux]
QED

Theorem method_id_word_mask:
  ((w:bytes32) >>> 224) << 224 =
  typed_val_to_w256 (BaseTV (BytesT (Fixed 4)))
    (BytesV (TAKE 4 (word_to_bytes w T)))
Proof
  simp[typed_val_to_w256_def, word_of_bytes_be_pad_right,
       word_of_bytes_be_def, hash_take_word_to_bytes] >>
  `word_of_bytes T (0w:bytes32) (word_to_bytes_aux 4 w T) =
     word_slice_alt 256 224 w` by
    (mp_tac (Q.SPECL [`4`, `w`] (Q.GENL [`n`, `w`]
        (INST_TYPE [alpha |-> ``:256``] word_of_bytes_word_to_bytes_aux_be))) >>
     simp[]) >>
  simp[] >>
  simp[word_slice_alt_def, fcpTheory.FCP_BETA] >>
  simp[fcpTheory.CART_EQ, word_lsl_def, word_lsr_def,
       fcpTheory.FCP_BETA] >> rpt strip_tac >>
  Cases_on `224 <= i` >> simp[]
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
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[run_inst_seq_def, step_SHR, step_SHL, mk_inst_def,
       eval_operand_def, lookup_var_update_var, bind_outputs_def] >>
  simp[step_inst_base_def, exec_pure2_def, eval_operand_def,
       bind_outputs_def, lookup_var_update_var] >>
  simp[dimword_def, update_var_def] >> rpt strip_tac >>
  gvs[not_fresh_at_def] >>
  first_assum (qspec_then `sa.cs_next_var + 1` assume_tac) >>
  first_assum (qspec_then `sa.cs_next_var` assume_tac) >> gvs[]
QED

Theorem method_id_mask_frame:
  emit_op SHR [Lit 224w; hash_op] sa = (sel_op, sm) /\
  emit_op SHL [Lit 224w; sel_op] sm = (word_op, sb) /\
  eval_operand hash_op s = SOME w /\
  stmt_state_rel func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand word_op t = SOME
      (typed_val_to_w256 (BaseTV (BytesT (Fixed 4)))
        (BytesV (TAKE 4 (word_to_bytes w T)))) /\
    stmt_state_rel func cenv cx es t /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule_all method_id_mask_run >> strip_tac >>
  qexists_tac `t` >> simp[GSYM method_id_word_mask] >>
  irule hash_readonly_state_rel >> goal_assum drule >> simp[]
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
  simp[emit_void_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[Once run_inst_seq_def, step_inst_base_def, mk_inst_def,
       eval_operand_def] >>
  `b < dimword (:256)` by decide_tac >>
  simp[exec_write2_def, eval_operand_def, w2n_n2w] >>
  `eval_operand ptr_op (mstore b (n2w n) s) = SOME (n2w b)` by
    (Cases_on `ptr_op` >> gvs[eval_operand_def, mstore_def, lookup_var_def]) >>
  simp[Once run_inst_seq_def, step_inst_base_def, exec_pure2_def,
       eval_operand_def, bind_outputs_def] >>
  `eval_operand val_op
     (update_var (STRING #"%" (toString sa.cs_next_var)) (n2w b + 32w)
       (mstore b (n2w n) s)) = SOME v` by
    (Cases_on `val_op` >>
     gvs[eval_operand_def, lookup_var_update_var, not_fresh_at_def,
         mstore_def, lookup_var_def]) >>
  fs[word_add_n2w] >>
  simp[run_inst_seq_def, step_inst_base_def, exec_write2_def,
       eval_operand_def, lookup_var_update_var, w2n_n2w] >>
  simp_tac (srw_ss()) [mstore_def, update_var_def, LET_THM] >>
  rpt strip_tac >>
  gvs[not_fresh_at_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  first_x_assum (qspec_then `sa.cs_next_var` mp_tac) >> simp[]
QED

Theorem hash_single_word_buffer_frame:
  emit_void MSTORE [ptr_op; Lit (n2w n)] sa = ((), sh) /\
  emit_op ADD [ptr_op; Lit 32w] sh = (data_ptr, sd) /\
  emit_void MSTORE [data_ptr; val_op] sd = ((), sb) /\
  eval_operand ptr_op s = SOME (n2w b) /\ eval_operand val_op s = SOME v /\
  (!x. val_op = Var x ==> not_fresh_at sa x) /\ b + 32 < dimword (:256) /\
  stmt_state_rel func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!name off len. local_region cenv es.scopes s name off len ==>
     regions_disjoint b 64 off len) /\
  (cenv.ce_is_ctor ==> !name tv iv off.
     FLOOKUP cenv.ce_vars (module_var_key (cenv.ce_module,name)) =
       SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name =
       SOME (tv,iv) ==>
     regions_disjoint b 64 off (type_memory_size tv)) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel func cenv cx es t /\
    t.vs_memory = (mstore (b + 32) v (mstore b (n2w n) s)).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!off len. regions_disjoint b 64 off len ==>
       mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory)
Proof
  strip_tac >> drule_all hash_single_word_buffer_run >> strip_tac >>
  `!off len. regions_disjoint b 64 off len ==>
     mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory` by
    (rpt strip_tac >> simp[] >>
     `mem_bytes_at off len (mstore (b+32) v (mstore b (n2w n) s)).vs_memory =
      mem_bytes_at off len (mstore b (n2w n) s).vs_memory` by
       (irule mstore_region_frame >> qexistsl_tac [`b`, `64`] >> simp[]) >>
     simp[] >> irule mstore_region_frame >>
     qexistsl_tac [`b`, `64`] >> simp[]) >>
  qexists_tac `t` >> simp[] >> irule literal_state_memory_frame >>
  qexists_tac `s` >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `t.vs_memory = _` (fn th => rewrite_tac[GSYM th]) >>
      qpat_x_assum `!off len. regions_disjoint b 64 off len ==> _` irule >>
      first_x_assum irule >> goal_assum drule) >>
  conj_tac
  >- (rpt strip_tac >> qpat_x_assum `!x. not_fresh_at sa x ==> _` irule >>
      gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  conj_tac
  >- simp[immutableMemoryFrameTheory.immutable_mstore_capacity,
          arithmeticTheory.MAX_DEF] >>
  rpt strip_tac >>
  qpat_x_assum `t.vs_memory = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `!off len. regions_disjoint b 64 off len ==> _` irule >>
  metis_tac[]
QED

Theorem hash_single_word_buffer_contents:
  LENGTH bs <= 32 /\ TAKE (LENGTH bs) (word_to_bytes_be v) = bs ==>
  val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) b
    (mstore (b + 32) v (mstore b (n2w (LENGTH bs)) s)).vs_memory
Proof
  strip_tac >> simp[val_in_memory_def] >> conj_tac
  >- simp[valueEncodingPropsTheory.mstore_mem_word_at_disjoint,
          valueEncodingPropsTheory.mstore_mem_word_at_same] >>
  irule hash_mstore_prefix >> simp[]
QED

Theorem hash_alloc_single_word_buffer_frame:
  compile_alloc_buffer 64 sa = (buf, sm) /\
  emit_void MSTORE [buf.buf_operand; Lit (n2w (LENGTH bs))] sm = ((), sh) /\
  emit_op ADD [buf.buf_operand; Lit 32w] sh = (data_ptr, sd) /\
  emit_void MSTORE [data_ptr; val_op] sd = ((), sb) /\
  eval_operand val_op s = SOME v /\
  (!x. val_op = Var x ==> not_fresh_at sa x) /\
  LENGTH bs <= 32 /\ TAKE (LENGTH bs) (word_to_bytes_be v) = bs /\
  stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
  ?t p. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel func cenv cx es t /\
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
  strip_tac >>
  `64 < dimword (:256)` by simp[dimword_def] >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `eval_operand buf.buf_operand allocated = SOME addr` >>
  `allocated.vs_labels = s.vs_labels` by
    (drule_all hash_alloc_buffer_labels >> simp[]) >>
  `eval_operand val_op allocated = SOME v` by
    (Cases_on `val_op` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `sm.cs_next_var = sa.cs_next_var + 1 /\
   sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
   sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     qpat_x_assum `emit_void MSTORE [data_ptr; val_op] _ = _` mp_tac >>
     qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     qpat_x_assum `emit_void MSTORE [buf.buf_operand; _] _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_id_def, fresh_var_def, emit_def] >>
     rpt strip_tac >> gvs[emitted_insts_def,
          rich_listTheory.DROP_LENGTH_APPEND, rich_listTheory.DROP_APPEND1,
          rich_listTheory.DROP_APPEND2, APPEND_ASSOC]) >>
  `local_ptrs_reserved cenv sm` by
    (gvs[local_ptrs_reserved_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_ADD]) >>
  `!x. val_op = Var x ==> not_fresh_at sm x` by
    gvs[not_fresh_at_def] >>
  `w2n addr + 32 < dimword (:256)` by decide_tac >>
  `eval_operand buf.buf_operand allocated = SOME (n2w (w2n addr))` by simp[] >>
  `(cenv.ce_is_ctor ==> !name tv iv off.
     FLOOKUP cenv.ce_vars (module_var_key (cenv.ce_module,name)) =
       SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name =
       SOME (tv,iv) ==>
     regions_disjoint (w2n addr) 64 off (type_memory_size tv))` by
    (rpt strip_tac >>
     qpat_assum `stmt_state_rel func cenv cx es allocated` mp_tac >>
     pure_rewrite_tac[stmt_state_rel_def, immutable_alloca_sep_def] >> strip_tac >>
     qpat_x_assum `cenv.ce_is_ctor ==> _` drule >>
     disch_then drule_all >> strip_tac >>
     qpat_x_assum `!inst b sz. MEM inst _ /\ _ ==> _`
       (qspec_then `mk_inst sa.cs_next_id ALLOCA [Lit 64w]
         [STRING #"%" (toString sa.cs_next_var)]` mp_tac) >>
     simp[mk_inst_def, regions_disjoint_def] >> decide_tac) >>
  drule_all hash_single_word_buffer_frame >> strip_tac >>
  suspend "compose"
QED

Resume hash_alloc_single_word_buffer_frame[compose]:
  `run_inst_seq (emitted_insts sa sb) s =
     run_inst_seq (emitted_insts sm sb) allocated` by
    (irule (cj 1 run_inst_seq_chain) >> simp[]) >>
  `t.vs_allocas = allocated.vs_allocas` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = _`
      (mp_tac o Q.AP_TERM `\z. z.vs_allocas`) >> simp[]) >>
  `eval_operand buf.buf_operand t = SOME addr` by
    gvs[eval_operand_def] >>
  `val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs)
     (w2n addr) t.vs_memory` by
    (simp[] >> irule hash_single_word_buffer_contents >> simp[]) >>
  `!n b sz. local_region cenv es.scopes s n b sz ==>
    mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
    (match_mp_tac exprSimOpsTheory.local_regions_memory_tail >>
     qexistsl [`sa`, `es.scopes`, `allocated`] >> simp[] >>
     rpt strip_tac >>
     qpat_x_assum `t.vs_memory = _` (fn th => rewrite_tac[GSYM th]) >>
     qpat_x_assum `allocated.vs_memory = _`
       (fn th => once_rewrite_tac[GSYM th]) >>
     qpat_x_assum `!off len. regions_disjoint _ _ off len ==> _` irule >>
     metis_tac[]) >>
  `!n b sz. local_region cenv es.scopes t n b sz ==>
     regions_disjoint (w2n addr) 64 b sz` by
    (rpt strip_tac >>
     `local_region cenv es.scopes allocated n b sz` by
       (irule exprSimOpsTheory.local_region_frame >> conj_tac
        >- (qexists_tac `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
        qexistsl [`sm`, `es.scopes`, `t`] >> simp[] >> metis_tac[]) >>
     qpat_x_assum `!name b len. local_region _ _ allocated _ _ _ ==> _`
       drule >> simp[]) >>
  qexistsl_tac [`t`, `addr`] >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sm x` by gvs[not_fresh_at_def] >>
      qpat_x_assum `!x. not_fresh_at sm x ==> _` drule >>
      qpat_x_assum `!x. not_fresh_at sa x ==> _` drule >> simp[]) >>
  reverse conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  qpat_x_assum `t.vs_memory = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `allocated.vs_memory = _` (fn th => once_rewrite_tac[GSYM th]) >>
  qpat_x_assum `!off len. regions_disjoint _ _ off len ==> _` irule >>
  qpat_x_assum `!aid b len. aid < sa.cs_next_id /\ _ ==> _` irule >>
  qexists_tac `aid` >> simp[]
QED

Finalise hash_alloc_single_word_buffer_frame

Theorem method_id_mask_prefix:
  TAKE 4 (word_to_bytes_be (((w:bytes32) >>> 224) << 224)) =
  TAKE 4 (word_to_bytes w T)
Proof
  rewrite_tac[method_id_word_mask] >>
  mp_tac (Q.SPECL [`TAKE 4 (word_to_bytes (w:bytes32) T)`, `Fixed 4`]
    (Q.GENL [`bs`, `bd`] typed_bytes_prefix)) >> simp[]
QED

Theorem method_id_dynamic_suffix_frame:
  emit_op SHR [Lit 224w; hash_op] sa = (sel_op, sm) /\
  emit_op SHL [Lit 224w; sel_op] sm = (word_op, sn) /\
  compile_alloc_buffer 64 sn = (buf, sp) /\
  emit_void MSTORE [buf.buf_operand; Lit 4w] sp = ((), sh) /\
  emit_op ADD [buf.buf_operand; Lit 32w] sh = (data_ptr, sd) /\
  emit_void MSTORE [data_ptr; word_op] sd = ((), sb) /\
  eval_operand hash_op s = SOME w /\
  stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst sn.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sn.cs_next_var)]) (fn_insts func) ==>
  ?t p. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel func cenv cx es t /\
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
  strip_tac >> drule_all method_id_mask_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sn) s = OK masked` >>
  `sn.cs_next_var = sa.cs_next_var + 2 /\
   sn.cs_next_id = sa.cs_next_id + 2 /\
   sn.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sn /\
   sb.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sb /\
   (!x. word_op = Var x ==> not_fresh_at sn x)` by
    (qpat_x_assum `emit_op SHR _ _ = _` mp_tac >>
     qpat_x_assum `emit_op SHL _ _ = _` mp_tac >>
     qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     qpat_x_assum `emit_void MSTORE [data_ptr; word_op] _ = _` mp_tac >>
     qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     qpat_x_assum `emit_void MSTORE [buf.buf_operand; _] _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_id_def, fresh_var_def, emit_def] >> rpt strip_tac >>
     gvs[emitted_insts_def, not_fresh_at_def, toString_inj,
         rich_listTheory.DROP_LENGTH_APPEND, rich_listTheory.DROP_APPEND1,
         rich_listTheory.DROP_APPEND2, APPEND_ASSOC]) >>
  `local_ptrs_reserved cenv sn` by
    (gvs[local_ptrs_reserved_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_ADD]) >>
  suspend "buffer"
QED

Resume method_id_dynamic_suffix_frame[buffer]:
  `masked.vs_allocas = s.vs_allocas /\ masked.vs_memory = s.vs_memory` by
    (qpat_x_assum `masked with vs_vars := _ = _`
      (mp_tac o Q.AP_TERM `\z. (z.vs_allocas,z.vs_memory)`) >> simp[]) >>
  `emit_void MSTORE
     [buf.buf_operand; Lit (n2w (LENGTH (TAKE 4 (word_to_bytes w T))))]
     sp = ((), sh)` by simp[] >>
  `LENGTH (TAKE 4 (word_to_bytes w T)) <= 32` by simp[] >>
  `TAKE (LENGTH (TAKE 4 (word_to_bytes w T)))
     (word_to_bytes_be
       (typed_val_to_w256 (BaseTV (BytesT (Fixed 4)))
         (BytesV (TAKE 4 (word_to_bytes w T))))) =
     TAKE 4 (word_to_bytes w T)` by
    simp[GSYM method_id_word_mask, method_id_mask_prefix] >>
  drule_all hash_alloc_single_word_buffer_frame >>
  disch_then (qspec_then `4` strip_assume_tac) >>
  `run_inst_seq (emitted_insts sa sb) s =
     run_inst_seq (emitted_insts sn sb) masked` by
    (irule (cj 1 run_inst_seq_chain) >> simp[]) >>
  `!nm lb sz. local_region cenv es.scopes s nm lb sz ==>
    mem_bytes_at lb sz t.vs_memory = mem_bytes_at lb sz s.vs_memory` by
    (match_mp_tac exprSimOpsTheory.local_regions_memory_tail >>
     qexistsl [`sa`, `es.scopes`, `masked`] >> gvs[] >> metis_tac[]) >>
  qexistsl_tac [`t`, `p`] >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sn x` by gvs[not_fresh_at_def] >>
      qpat_x_assum `!x. not_fresh_at sn x ==> _` drule >>
      qpat_x_assum `!x. not_fresh_at sa x ==> _` drule >> simp[]) >>
  reverse conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  qpat_x_assum `!aid off len. aid < sn.cs_next_id /\ _ ==> _`
    (qspecl_then [`aid`, `off`, `len`] mp_tac) >> simp[]
QED

Finalise method_id_dynamic_suffix_frame

Theorem eval_exprs_single_literal:
  !cx la l es. eval_exprs cx [Literal la l] es = (INL [evaluate_literal l], es)
Proof
  rpt gen_tac >>
  rpt (simp[Once evaluate_def, bind_def, return_def, read_result_def])
QED

(* A literal signature is folded to the literal selector (#711). *)
Theorem compile_expr_method_id_literal:
  !cenv ty ann la l bs st.
    method_id_literal (Literal la l) = SOME bs ==>
    compile_expr cenv ty (Builtin ann MethodId [Literal la l]) st =
    compile_literal_vv ann (BytesL (TAKE 4 (Keccak_256_w64 bs))) st
Proof
  rpt strip_tac >>
  simp[compile_expr_builtin_dispatch, names_builtin_def] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def]
QED

(* The source hashes a literal signature to the selector the lowering
   folds it to. *)
Theorem eval_expr_method_id_literal:
  !cx ann la l bs es res es'.
    method_id_literal (Literal la l) = SOME bs /\
    eval_expr cx (Builtin ann MethodId [Literal la l]) es = (res, es') ==>
    es' = es /\ res = INL (Value (BytesV (TAKE 4 (Keccak_256_w64 bs))))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, builtin_args_length_ok_def, eval_exprs_single_literal,
       bind_def, ignore_bind_def, type_check_def, assert_def, return_def,
       get_accounts_def, lift_sum_def, raise_def] >>
  Cases_on `l` >>
  gvs[method_id_literal_def, evaluate_literal_def, evaluate_builtin_def,
      return_def, raise_def]
QED

Theorem compile_method_id_literal_dynamic_vv_sim:
  !cenv la l. IS_SOME (method_id_literal (Literal la l)) ==>
    expr_vv_ok cenv (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [Literal la l])
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `method_id_literal (Literal la l)` >> gvs[] >>
  rename1 `method_id_literal (Literal la l) = SOME bs` >>
  rw[expr_vv_ok_def] >>
  `expr_sim_pre cenv cx env
     (Literal (BaseT (BytesT (Dynamic 4)))
       (BytesL (TAKE 4 (Keccak_256_w64 bs)))) es` by
    (gvs[expr_sim_pre_def] >>
     simp[well_typed_expr_def, well_typed_literal_def,
       well_formed_type_def, byte_widths_expr_def, alloc_limits_expr_def,
       literal_alloc_ok_def, vyperTypeCallGraphTheory.int_calls_expr_def,
       supportedExprTraverseTheory.expr_has_evm_run_thm, type_bits_def,
       vfmConstantsTheory.word_size_def, vyperValueTheory.evaluate_type_def,
       vyperValueTheory.compatible_bound_def, vyperValueTheory.type_slot_size_def,
       wordsTheory.dimword_def, LENGTH_TAKE,
       vyperTypeBytesCryptoTheory.LENGTH_Keccak_256_w64]) >>
  `expr_vv_ok cenv (Literal (BaseT (BytesT (Dynamic 4)))
     (BytesL (TAKE 4 (Keccak_256_w64 bs))))` by
    (irule compile_literal_other_vv_sim >> simp[is_word_type_def]) >>
  qpat_x_assum `expr_vv_ok _ _` (mp_tac o REWRITE_RULE [expr_vv_ok_def]) >>
  disch_then drule >> disch_then (qspecl_then [`ctx`, `func`, `ty`] mp_tac) >>
  rw[expr_vv_sim_def] >>
  drule_all eval_expr_method_id_literal >> strip_tac >> gvs[] >>
  qpat_x_assum `!sa sb vv res es' s0. _` (qspecl_then
    [`sa`, `sb`, `vv`, `INL (Value (BytesV (TAKE 4 (Keccak_256_w64 bs))))`,
     `es`, `s0`] mp_tac) >>
  gvs[compile_expr_method_id_literal, compile_expr_def,
      vv_post_def, expr_type_def] >>
  simp[Once evaluate_def, return_def, evaluate_literal_def]
QED

(* Typed postconditions expose the representation needed by hash suffixes. *)
Theorem hash_fixed_post_view:
  expr_post func cenv cx e es sa sm s0 es' (BytesV bs) op s /\
  expr_type e = BaseT (BytesT (Fixed m)) /\
  value_has_type (BaseTV (BytesT (Fixed m))) (BytesV bs) /\ m <= 32 ==>
  ?w. eval_operand op s = SOME w /\ LENGTH bs = m /\
      TAKE (LENGTH bs) (word_to_bytes_be w) = bs
Proof
  strip_tac >>
  `LENGTH bs = m` by gvs[vyperTypingTheory.value_has_type_def] >>
  gvs[expr_post_def, expr_val_rel_def, is_word_type_def,
      vyperValueTheory.evaluate_type_def] >>
  irule typed_bytes_prefix >> simp[]
QED

Theorem hash_live_footprint_bound:
  stmt_state_rel func cenv cx es s /\
  ((?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
      b <= p /\ p + n <= b + sz) \/
   (?name b sz. local_region cenv es.scopes s name b sz /\
      b <= p /\ p + n <= b + sz)) ==>
  p + n < dimword (:256)
Proof
  strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by
    (irule alloca_room_next_lt >> qexists_tac `func` >>
     gvs[stmt_state_rel_def]) >>
  gvs[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def,
      venomMemDefsTheory.alloca_next_valid_def]
  >- (first_x_assum drule >> decide_tac) >>
  gvs[local_region_def, state_rel_def, local_ptrs_rel_def] >>
  first_x_assum drule_all >> strip_tac >> gvs[] >> decide_tac
QED

Theorem hash_post_footprint_bound:
  expr_post func cenv cx e es sa sm s0 es' v op s /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  ~is_word_type (expr_type e) /\ eval_operand op s = SOME p ==>
  w2n p + val_footprint tv v < dimword (:256)
Proof
  strip_tac >>
  Cases_on `val_footprint tv v = 0` >- simp[wordsTheory.w2n_lt] >>
  `stmt_state_rel func cenv cx es' s /\
   expr_val_at cenv cx (expr_type e) sa sm es' v op s` by
    gvs[expr_post_def] >>
  drule_all expr_val_at_footprint >> strip_tac >>
  TRY (gvs[] >> NO_TAC) >>
  irule hash_live_footprint_bound >> goal_assum (drule_at Any) >>
  metis_tac[]
QED

Theorem hash_dynamic_post_view:
  expr_post func cenv cx e es sa sm s0 es' (BytesV bs) op s /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) (expr_type e) =
    SOME (BaseTV (BytesT (Dynamic cap))) ==>
  ?b. eval_operand op s = SOME (n2w b) /\
    mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
    b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256)
Proof
  strip_tac >>
  `expr_val_rel cx (expr_type e) (BytesV bs) op s` by gvs[expr_post_def] >>
  `?p. eval_operand op s = SOME p` by gvs[expr_val_rel_def] >>
  `evaluate_type (get_tenv cx) (expr_type e) =
     SOME (BaseTV (BytesT (Dynamic cap))) /\ ~is_word_type (expr_type e)` by
    simp[vyperValueTheory.evaluate_type_def, is_word_type_def] >>
  drule_all expr_val_rel_memory >>
  disch_then (strip_assume_tac o SRULE [val_in_memory_def, LET_THM]) >>
  drule_all hash_post_footprint_bound >>
  simp[val_footprint_def] >> strip_tac >>
  `w2n p + 32 + LENGTH bs < dimword (:256)` by
    (irule (cj 1 literal_buffer_range) >> simp[] >> decide_tac) >>
  qexists_tac `w2n p` >> simp[] >> decide_tac
QED

Theorem hash_string_post_view:
  expr_post func cenv cx e es sa sm s0 es' (StringV str) op s /\
  expr_type e = BaseT (StringT cap) /\
  evaluate_type (get_tenv cx) (expr_type e) =
    SOME (BaseTV (StringT cap)) ==>
  ?b. eval_operand op s = SOME (n2w b) /\
    mem_word_at b s.vs_memory = n2w (LENGTH str) /\
    mem_bytes_at (b + 32) (LENGTH str) s.vs_memory = MAP (n2w o ORD) str /\
    b + 32 < dimword (:256) /\ LENGTH str < dimword (:256)
Proof
  strip_tac >>
  `expr_val_rel cx (expr_type e) (StringV str) op s` by gvs[expr_post_def] >>
  `?p. eval_operand op s = SOME p` by gvs[expr_val_rel_def] >>
  `~is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_all expr_val_rel_memory >>
  disch_then (strip_assume_tac o SRULE [val_in_memory_def, LET_THM]) >>
  drule_all hash_post_footprint_bound >>
  simp[val_footprint_def] >> strip_tac >>
  `w2n p + 32 + LENGTH str < dimword (:256)` by
    (irule (cj 1 literal_buffer_range) >> simp[] >> decide_tac) >>
  qexists_tac `w2n p` >> simp[] >> decide_tac
QED

(* Containment is independent of the particular straight-line suffix. *)
Theorem hash_emitted_inst_mem:
  fn_has_code sa sb func /\ MEM inst (emitted_insts sa sb) ==>
  MEM inst (fn_insts func)
Proof
  strip_tac >>
  gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
  irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
  gvs[emitted_insts_def, MEM_APPEND] >>
  metis_tac[rich_listTheory.MEM_DROP_IMP]
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
  strip_tac >> gvs[] >>
  `~names_builtin Keccak256 [e] /\ ~names_builtin Sha256 [e]` by
    (Cases_on `e` >> simp[names_builtin_def]) >>
  simp[compile_expr_builtin_dispatch] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[exprBopLoweringTheory.lower_value_child_call, vyperASTTheory.expr_size_def, list_size_def,
       basicSizeTheory.option_size_def] >>
  Cases_on `is_bytestring_type (expr_type e)` >> simp[] >>
  Cases_on `expr_type e` >> simp[] >>
  rename1 `expr_type e = BaseT b` >> Cases_on `b` >> simp[] >>
  rename1 `expr_type e = BaseT (BytesT bd)` >> Cases_on `bd` >> simp[]
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
  strip_tac >>
  `~names_builtin MethodId [e]` by (Cases_on `e` >> simp[names_builtin_def]) >>
  simp[compile_expr_builtin_dispatch] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[exprBopLoweringTheory.lower_value_child_call,
       vyperASTTheory.expr_size_def, list_size_def, basicSizeTheory.option_size_def] >>
  pairarg_tac >> simp[] >> Cases_on `ann = BaseT (BytesT (Fixed 4))` >> simp[]
QED

Theorem hash_suffix_appends:
  (!v. cs_appends (compile_keccak256_bytes v)) /\
  (!v m. cs_appends (compile_keccak256_bytesm v m)) /\
  (!v. cs_appends (compile_sha256_bytes v)) /\
  (!v m. cs_appends (compile_sha256_bytesm v m)) /\
  (!ty v fixed. cs_appends (compile_method_id_runtime ty v fixed))
Proof
  `!n. cs_appends (compile_alloc_buffer n)` by
    (rw[contextTheory.compile_alloc_buffer_def] >>
     irule cs_appends_bind >> simp[cs_appends_emit_helpers, cs_appends_return]) >>
  `!v. cs_appends (compile_keccak256_word v)` by
    (rw[compile_keccak256_word_def] >>
     rpt (FIRST [irule cs_appends_bind, irule cs_appends_ignore_bind] >>
          rw[cs_appends_emit_helpers, cs_appends_return])) >>
  rpt conj_tac >> rpt gen_tac >>
  rw[compile_keccak256_bytes_def, compile_keccak256_bytesm_def,
     compile_sha256_bytes_def, compile_sha256_bytesm_def,
     compile_method_id_runtime_def, compile_method_id_hash_def] >>
  rpt (FIRST [irule cs_appends_bind, irule cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return]) >>
  Cases_on `ty` >> simp[compile_method_id_hash_def, compile_keccak256_bytes_def] >>
  rpt (FIRST [irule cs_appends_bind, irule cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return]) >>
  Cases_on `b` >> simp[compile_method_id_hash_def, compile_keccak256_bytes_def] >>
  rpt (FIRST [irule cs_appends_bind, irule cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return]) >>
  Cases_on `b'` >> simp[compile_method_id_hash_def,
    compile_keccak256_bytes_def, compile_keccak256_bytesm_def] >>
  rpt (FIRST [irule cs_appends_bind, irule cs_appends_ignore_bind] >>
       rw[cs_appends_emit_helpers, cs_appends_return])
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
  strip_tac >> Cases_on `sha` >> gvs[] >>
  qpat_x_assum `_ = (op,sb)` mp_tac >>
  simp[compile_sha256_bytesm_def, compile_keccak256_bytesm_def,
    contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  rpt strip_tac >> irule hash_emitted_inst_mem >>
  goal_assum (drule_at Any) >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]
QED

Theorem hash_sha256_memory_alloca_code:
  compile_sha256_bytes v sa = (op,sb) /\ fn_has_code sa sb func ==>
  MEM (mk_inst (sa.cs_next_id + 2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (sa.cs_next_var + 2))]) (fn_insts func)
Proof
  strip_tac >> qpat_x_assum `compile_sha256_bytes _ _ = _` mp_tac >>
  simp[compile_sha256_bytes_def, contextTheory.compile_alloc_buffer_def,
    emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >> irule hash_emitted_inst_mem >>
  goal_assum (drule_at Any) >> simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]
QED

Theorem hash_unary_suffix_cut:
  lower_value compile_expr cenv ty e sa = (v,sm) /\
  cs_appends code /\ code sm = (op,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa ==>
  cs_extends sa sm /\ cs_extends sm sb /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  local_ptrs_reserved cenv sm
Proof
  strip_tac >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `cs_extends sm sb` by metis_tac[cs_appends_def] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var] >>
  simp[]
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
  simp[compile_method_id_runtime_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `fixed` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[comp_return_def] >>
  metis_tac[]
QED

Theorem hash_method_id_hash_appends:
  cs_appends (compile_method_id_hash ty v)
Proof
  Cases_on `ty` >> simp[compile_method_id_hash_def, hash_suffix_appends] >>
  rename1 `compile_method_id_hash (BaseT bty) v` >> Cases_on `bty` >>
  simp[compile_method_id_hash_def, hash_suffix_appends] >>
  rename1 `compile_method_id_hash (BaseT (BytesT bd)) v` >> Cases_on `bd` >>
  simp[compile_method_id_hash_def, hash_suffix_appends]
QED

Theorem hash_method_id_hash_cut:
  compile_method_id_runtime ty v fixed sa = (op,sb) /\
  compile_method_id_hash ty v sa = (hash,sm) /\
  fn_has_code sa sb func ==>
  cs_extends sa sm /\ cs_extends sm sb /\
  fn_has_code sa sm func /\ fn_has_code sm sb func
Proof
  strip_tac >>
  `cs_extends sa sm` by
    metis_tac[hash_method_id_hash_appends, cs_appends_def] >>
  `cs_extends sm sb` by
    (qpat_x_assum `compile_method_id_runtime _ _ _ _ = _` mp_tac >>
     simp[compile_method_id_runtime_def, comp_bind_def] >>
     rpt (pairarg_tac >> gvs[]) >> Cases_on `fixed` >>
     simp[contextTheory.compile_alloc_buffer_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
     gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, fresh_id_def, fresh_var_def, emit_def,
         cs_extends_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[IS_PREFIX_APPEND]) >>
  metis_tac[fn_has_code_split]
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
  strip_tac >> irule hash_emitted_inst_mem >>
  goal_assum (drule_at Any) >>
  gvs[contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def, emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]
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
  strip_tac >>
  `cs_extends sa sn /\ cs_extends sn sb` by
    (gvs[contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
         comp_bind_def, comp_ignore_bind_def, comp_return_def,
         fresh_id_def, fresh_var_def, emit_def, cs_extends_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[IS_PREFIX_APPEND]) >>
  `fn_has_code sa sn func /\ fn_has_code sn sb func` by
    metis_tac[fn_has_code_split] >> simp[] >>
  drule_all hash_method_id_output_alloca_code >> simp[]
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
  simp[wb_frame_def] >> strip_tac >> conj_tac
  >- (rpt strip_tac >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  reverse conj_tac
  >- ((* the locals: their regions at s0 are their regions at s *)
      irule locals_kept_regions_tail >> qexists_tac `s` >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      rpt strip_tac >> rename1 `local_region _ _ _ nm lb lsz` >>
      qpat_x_assum `!n b sz. local_region _ _ _ n b sz ==> _` irule >>
      qexists_tac `nm` >>
      irule exprSimOpsTheory.local_region_frame_fwd >>
      qexistsl [`s0`, `sa`, `es.scopes`] >> simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  `FLOOKUP s.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
  `aid < sm.cs_next_id` by decide_tac >>
  metis_tac[]
QED

Theorem vv_post_frame_intro:
  stmt_state_rel func cenv cx es' t /\
  vv_holds cenv cx (expr_type e) tv vv es' t /\
  vv_at cenv cx (expr_type e) sa sb es' tv vv t /\
  wb_frame cenv es sa s0 t ==>
  vv_post func cenv cx e es sa sb s0 es' tv vv t
Proof
  simp[vv_post_def, wb_frame_def] >> metis_tac[]
QED

Theorem vv_post_word_intro:
  stmt_state_rel func cenv cx es' s /\ is_word_type (expr_type e) /\
  (?w. eval_operand op s = SOME w /\
    !tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
         w = typed_val_to_w256 tv v) /\
  wb_frame cenv es sa s0 s ==>
  vv_post func cenv cx e es sa sb s0 es' (Value v) (StackValue ty op) s
Proof
  strip_tac >> irule vv_post_frame_intro >>
  simp[vv_holds_def, vv_at_def, expr_val_rel_def, expr_val_at_def,
       read_result_def, return_def] >>
  metis_tac[]
QED

Theorem hash_run_frag:
  same_blocks sa sb /\ sb.cs_current_insts = sa.cs_current_insts ++ insts /\
  emitted_insts sa sb = insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) insts /\
  (!s. P s ==> ?t. run_inst_seq insts s = OK t /\
     Q (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
  frag_exec ctx sa sb P Q R
Proof
  strip_tac >> irule frag_exec_run_inst_seq >>
  gvs[same_blocks_def, IS_PREFIX_APPEND] >> metis_tac[]
QED

Theorem vv_post_allocated_memory_intro:
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  val_wf tv v /\ val_in_memory tv v (w2n w) s.vs_memory /\
  stmt_state_rel func cenv cx es' s /\
  p.ptr_location = LocMemory /\ eval_operand p.ptr_operand s = SOME w /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  b <= w2n w /\ w2n w + val_footprint tv v <= b + sz /\
  (!n lb lsz. local_region cenv es'.scopes s n lb lsz ==>
     b + sz <= lb \/ lb + lsz <= b) /\
  wb_frame cenv es sa s0 s ==>
  vv_post func cenv cx e es sa sb s0 es' (Value v)
    (LocatedValue (expr_type e) p) s
Proof
  strip_tac >> irule vv_post_frame_intro >>
  simp[vv_holds_def, vv_at_def, read_result_def, return_def] >>
  disj1_tac >> qexistsl [`aid`, `b`, `sz`] >> simp[] >>
  first_assum ACCEPT_TAC
QED

(* Forced base-typed operands have the corresponding value type. *)
Theorem expr_body_pre_base_result:
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT bt /\
  (do r <- eval_expr cx e; read_result cx r od) es = (res,es') ==>
  expr_sim_inv cenv cx env es' /\ expr_res_ok res /\
  !v. res = INL v ==> value_has_type (BaseTV bt) v
Proof
  strip_tac >> drule_all expr_body_pre_eval >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
        env_context_consistent_def] >>
  drule_all expr_body_pre_res_ok >> strip_tac >> simp[] >>
  rpt strip_tac >> first_x_assum drule >>
  simp[expr_result_typed_def, expr_runtime_typed_def,
       value_result_typed_def, value_runtime_typed_def,
       vyperValueTheory.evaluate_type_def] >>
  Cases_on `bt` >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem eval_expr_unary_builtin_cases:
  bt <> Len /\ builtin_args_length_ok bt 1 /\
  eval_expr cx (Builtin ann bt [e]) es = (res,es') ==>
  (?exc. (do r <- eval_expr cx e; read_result cx r od) es = (INR exc,es') /\ res = INR exc) \/
  ?v. (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') /\
    res = (case builtin_result cx es'.accounts ann bt [expr_type e] [v] of
             INL v => INL (Value v) | INR exc => INR exc)
Proof
  strip_tac >>
  `bt <> Env MsgGas` by (strip_tac >> gvs[builtin_args_length_ok_def]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def] >>
  Cases_on `eval_exprs cx [e] es` >>
  rename1 `eval_exprs cx [e] es = (rr, es1)` >>
  drule eval_exprs_cons_cases >> strip_tac >> gvs[eval_exprs_nil] >>
  simp[bind_def, return_def, get_accounts_def, lift_sum_def,
       builtin_result_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[bind_def, AllCaseEqs()] >>
  Cases_on `evaluate_builtin cx es1.accounts ann bt [expr_type e] [v]` >>
  gvs[return_def, raise_def] >> metis_tac[]
QED

(* Unary composition keeps the complete argument postcondition available to
   the suffix, including the footprint and protected-allocation frame. *)
Theorem compile_typed_unary_builtin_vv_sim:
  expr_body_pre cenv cx env (Builtin ann bt [e]) es /\
  expr_sim ctx func cenv cx (expr_type e) e es /\ expr_type e = BaseT bty /\
  bt <> Len /\ builtin_args_length_ok bt 1 /\
  (!sa sb vv. compile_expr cenv ty (Builtin ann bt [e]) sa = (vv,sb) ==>
    ?x sm. lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
      code x sm = (vv,sb)) /\
  (!x. cs_appends (code x)) /\
  (!sa sm sb x vv s0 v es' s.
    lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
    code x sm = (vv,sb) /\ fn_has_code sm sb func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    local_ptrs_reserved cenv sm /\
    (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') /\
    value_has_type (BaseTV bty) v /\ expr_sim_inv cenv cx env es' /\
    expr_res_ok (builtin_result cx es'.accounts ann bt [expr_type e] [v]) /\
    expr_post func cenv cx e es sa sm s0 es' v x s ==>
    frag_exec ctx sm sb (\t. t = s)
      (\t. ?r. builtin_result cx es'.accounts ann bt [expr_type e] [v] = INL r /\
        vv_post func cenv cx (Builtin ann bt [e]) es sa sb s0 es' (Value r) vv t)
      (expr_exit (builtin_result cx es'.accounts ann bt [expr_type e] [v]))) ==>
  expr_vv_sim ctx func cenv cx ty (Builtin ann bt [e]) es
Proof
  strip_tac >> rewrite_tac[expr_vv_sim_def] >> rpt strip_tac >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >>
     disch_then irule >> gvs[expr_body_pre_def]) >>
  qpat_x_assum `!sa sb vv. _` drule >> strip_tac >>
  `cs_appends (code x)` by simp[] >>
  drule_all hash_unary_suffix_cut >> strip_tac >>
  `!ar es1. (do r <- eval_expr cx e; read_result cx r od) es = (ar,es1) ==>
     expr_sim_inv cenv cx env es1 /\ expr_res_ok ar /\
     !v. ar = INL v ==> value_has_type (BaseTV bty) v` by
    (rpt strip_tac >> drule_all expr_body_pre_base_result >> simp[]) >>
  drule_at (Pos last) eval_expr_unary_builtin_cases >> simp[] >>
  strip_tac
  >- (gvs[] >> irule expr_sim_suffix >>
      goal_assum (drule_at Any) >> simp[] >>
      first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
      first_assum (irule_at (Pat `bind _ _ _ = _`)) >>
      simp[] >> rpt strip_tac >>
      Cases_on `exc` >> Cases_on `r` >> gvs[expr_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >> gvs[expr_exit_def]) >>
  Cases_on `builtin_result cx es'.accounts ann bt [expr_type e] [v]` >>
  gvs[] >> irule expr_sim_suffix >>
  goal_assum (drule_at Any) >> simp[] >>
  first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `bind _ _ _ = _`)) >>
  simp[] >> rpt strip_tac >>
  gvs[expr_vv_res_ok_def, expr_res_ok_def] >>
  qpat_x_assum `!sa sm sb x vv s0 s. _` drule_all >>
  strip_tac >> irule frag_exec_conseq >>
  first_x_assum (irule_at Any) >> simp[] >> rpt gen_tac >>
  Cases_on `r` >> gvs[expr_exit_def] >>
  rename1 `INR exc` >> Cases_on `exc` >> gvs[expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> gvs[expr_exit_def]
QED

Theorem hash_eval_operand_inst_idx[simp]:
  eval_operand op (s with vs_inst_idx := n) = eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem vv_post_inst_idx[simp]:
  vv_post func cenv cx e es sa sb s0 es' tv vv (s with vs_inst_idx := n) <=>
  vv_post func cenv cx e es sa sb s0 es' tv vv s
Proof
  Cases_on `vv` >>
  simp[vv_post_def, stmt_state_rel_inst_idx, vv_holds_def, vv_at_def,
       expr_val_rel_def, expr_val_at_def, lookup_var_def, local_region_def]
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
  strip_tac >>
  gvs[compile_keccak256_bytes_def, compile_keccak256_bytesm_def,
      compile_sha256_bytes_def, compile_sha256_bytesm_def,
      contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
      fresh_var_def, emit_def, same_blocks_def, emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[is_terminator_def, mk_inst_def]
QED

Theorem keccak_suffix_shape:
  (compile_keccak256_bytes x sa = (op,sb) \/
   compile_keccak256_bytesm x m sa = (op,sb)) ==>
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  strip_tac >> irule hash_buffer_suffix_shape >>
  qexistsl [`m`, `op`, `x`] >> simp[]
QED

Theorem keccak_word_vv_post:
  stmt_state_rel func cenv cx es' s /\
  eval_operand op s = SOME (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
  wb_frame cenv es sa s0 s ==>
  vv_post func cenv cx (Builtin (BaseT (BytesT (Fixed 32))) bt [e])
    es sa sb s0 es' (Value (BytesV (Keccak_256_w64 bs)))
    (StackValue (BaseT (BytesT (Fixed 32))) op) s
Proof
  strip_tac >> irule vv_post_word_intro >>
  simp[vyperASTTheory.expr_type_def, is_word_type_def,
       vyperValueTheory.evaluate_type_def, typed_val_to_w256_def,
       PAD_RIGHT, vyperTypeBytesCryptoTheory.LENGTH_Keccak_256_w64,
       word_of_bytes_be_def]
QED

Theorem keccak_fixed_post_run:
  expr_post func cenv cx e es sa sm s0 es' (BytesV bs) x s /\
  expr_type e = BaseT (BytesT (Fixed m)) /\
  value_has_type (BaseTV (BytesT (Fixed m))) (BytesV bs) /\ m <= 32 /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_keccak256_bytesm x m sm = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    vv_post func cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Keccak256 [e])
      es sa sb s0 es' (Value (BytesV (Keccak_256_w64 bs)))
      (StackValue (BaseT (BytesT (Fixed 32))) op) t
Proof
  strip_tac >> drule_all hash_fixed_post_view >> strip_tac >>
  `!z. x = Var z ==> not_fresh_at sm z` by
    (drule_at (Pos hd) compile_lower_value_var >> simp[]) >>
  `stmt_state_rel func cenv cx es' s` by metis_tac[expr_post_state] >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sm.cs_next_var)]) (fn_insts func)` by
    (irule (SRULE [] (Q.INST [`sha` |-> `F`] hash_fixed_alloca_code)) >>
     metis_tac[]) >>
  qpat_x_assum `LENGTH bs = m` (SUBST_ALL_TAC o SYM) >>
  drule_at (Pos hd) compile_keccak256_bytesm_frame >> simp[] >>
  disch_then (drule_at (Pos hd)) >> simp[] >>
  disch_then drule_all >> strip_tac >>
  qexists `t` >> simp[] >> irule keccak_word_vv_post >> simp[] >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  irule wb_frame_allocating_tail >> simp[] >>
  qexistsl [`s`, `es'.scopes`, `sm`] >> simp[] >>
  metis_tac[expr_post_frame]
QED

Theorem keccak_memory_post_run:
  expr_post func cenv cx e es sa sm s0 es' v x s /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_keccak256_bytes x sm = (op,sb) /\
  eval_operand x s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
  b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    vv_post func cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Keccak256 [e])
      es sa sb s0 es' (Value (BytesV (Keccak_256_w64 bs)))
      (StackValue (BaseT (BytesT (Fixed 32))) op) t
Proof
  strip_tac >>
  `!z. x = Var z ==> not_fresh_at sm z` by
    (drule_at (Pos hd) compile_lower_value_var >> simp[]) >>
  `stmt_state_rel func cenv cx es' s` by metis_tac[expr_post_state] >>
  drule_at (Pos hd) compile_keccak256_bytes_frame >> simp[] >>
  disch_then (drule_at (Pos hd)) >> simp[] >>
  disch_then (drule_at (Pat `mem_bytes_at _ _ _ = _`)) >> simp[] >>
  disch_then drule_all >> strip_tac >>
  qexists `t` >> simp[] >> irule keccak_word_vv_post >> simp[] >>
  `t.vs_memory = s.vs_memory` by
    (qpat_x_assum `_ with vs_vars := _ = _`
      (mp_tac o Q.AP_TERM `\z. z.vs_memory`) >> simp[]) >>
  `t.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `_ with vs_vars := _ = _`
      (mp_tac o Q.AP_TERM `\z. z.vs_allocas`) >> simp[]) >>
  irule wb_frame_readonly_tail >> qexistsl [`sm`, `s`] >> simp[] >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  metis_tac[expr_post_frame]
QED

Theorem keccak_typed_post_run:
  expr_post func cenv cx e es sa sm s0 es' v x s /\
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
    vv_post func cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Keccak256 [e])
      es sa sb s0 es' (Value r) (StackValue (BaseT (BytesT (Fixed 32))) op) t
Proof
  strip_tac >> Cases_on `bty` >>
  gvs[is_bytes_or_string_type_def] >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
  gvs[is_bytestring_type_def, builtin_result_def, evaluate_builtin_def]
  >~ [`expr_type e = BaseT (BytesT bd)`]
  >- (Cases_on `bd` >>
      gvs[is_bytestring_type_def]
      >- (irule keccak_fixed_post_run >> goal_assum (drule_at Any) >>
          simp[vyperTypingTheory.value_has_type_def] >>
          gvs[vyperValueTheory.evaluate_type_def,
              vyperTypingTheory.value_has_type_def]) >>
      drule_at (Pos hd) hash_dynamic_post_view >> simp[] >> strip_tac >>
      irule keccak_memory_post_run >> goal_assum (drule_at Any) >>
      metis_tac[]) >>
  drule_at (Pos hd) hash_string_post_view >> simp[] >> strip_tac >>
  irule keccak_memory_post_run >> goal_assum (drule_at Any) >>
  simp[] >> qexistsl [`b`, `StringV s'`] >> simp[] >>
  `b < dimword (:256)` by decide_tac >> simp[]
QED

Theorem cs_appends_stack_value:
  cs_appends code ==> cs_appends (\s. as_stack_val ty (code s))
Proof
  simp[cs_appends_def] >> rpt strip_tac >>
  rename1 `as_stack_val ty (code s) = _` >>
  Cases_on `code s` >> gvs[as_stack_val_def] >> metis_tac[]
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
  strip_tac >> Cases_on `bty` >> gvs[is_bytes_or_string_type_def,
    is_bytestring_type_def]
  >~ [`expr_type e = BaseT (BytesT bd)`]
  >- (Cases_on `bd` >> gvs[is_bytestring_type_def] >>
      irule keccak_suffix_shape >> qexistsl [`n`, `op`, `x`] >> simp[]) >>
  irule keccak_suffix_shape >> qexistsl [`0`, `op`, `x`] >> simp[]
QED

(* Stack-result specialization: discharge type evaluation and turn a checked
   straight-line post-run boundary into the unary continuation interface. *)
Theorem compile_typed_stack_unary_builtin_vv_sim:
  expr_body_pre cenv cx env (Builtin ann bt [e]) es /\
  expr_sim ctx func cenv cx (expr_type e) e es /\ expr_type e = BaseT bty /\
  bt <> Len /\ builtin_args_length_ok bt 1 /\
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
     expr_post func cenv cx e es sa sm s0 es' v x s /\
     MAP FDOM es.scopes = MAP FDOM es'.scopes ==>
     ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
       ?r. builtin_result cx es'.accounts ann bt [expr_type e] [v] = INL r /\
       vv_post func cenv cx (Builtin ann bt [e]) es sa sb s0 es' (Value r)
         (StackValue ann op) t) ==>
  expr_vv_sim ctx func cenv cx ty (Builtin ann bt [e]) es
Proof
  strip_tac >> irule compile_typed_unary_builtin_vv_sim >> simp[] >>
  qexistsl [`\x sm. as_stack_val ann (code x sm)`, `env`] >> simp[] >>
  reverse conj_tac
  >- (conj_tac >- metis_tac[] >>
      gen_tac >> ho_match_mp_tac cs_appends_stack_value >> simp[SF ETA_ss]) >>
  rpt strip_tac >>
  qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
  Cases_on `code x sm` >> simp[as_stack_val_def] >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env e es'` by
    (irule expr_body_pre_builtin_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ _ _`)) >> simp[]) >>
  `evaluate_type (get_tenv cx) (BaseT bty) = SOME (BaseTV bty)` by
    (drule expr_body_pre_type_evaluates >>
     simp[vyperValueTheory.evaluate_type_def] >>
     Cases_on `bty` >> gvs[AllCaseEqs()] >>
     rename1 `expr_type e = BaseT (BytesT bd)` >>
     Cases_on `bd` >> gvs[AllCaseEqs()]) >>
  drule exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom >> strip_tac >>
  qpat_x_assum `!sa sm sb x op s0 v es' s. _` drule_all >>
  simp[] >> strip_tac >>
  qpat_x_assum `!x sm op sb. _` drule >> strip_tac >>
  irule hash_run_frag >> simp[] >> metis_tac[]
QED

Theorem compile_keccak256_typed_vv_sim:
  expr_body_pre cenv cx env (Builtin ann Keccak256 [e]) es /\
  expr_sim ctx func cenv cx (expr_type e) e es ==>
  expr_vv_sim ctx func cenv cx ty (Builtin ann Keccak256 [e]) es
Proof
  strip_tac >>
  `is_bytes_or_string_type (expr_type e) /\ ann = BaseT (BytesT (Fixed 32))` by
    (irule (SRULE [] (Q.INST [`b` |-> `Keccak256`,
       `ts` |-> `[expr_type e]`] hash_builtin_types)) >>
     gvs[expr_body_pre_def, well_typed_expr_def]) >>
  `?bty. expr_type e = BaseT bty` by
    (Cases_on `expr_type e` >> gvs[is_bytes_or_string_type_def]) >>
  irule compile_typed_stack_unary_builtin_vv_sim >>
  simp[builtin_args_length_ok_def] >>
  reverse conj_tac >- (qexists `env` >> gvs[]) >>
  qexists `\x sm.
    (if is_bytestring_type (expr_type e) then compile_keccak256_bytes x sm
     else case expr_type e of
       BaseT (BytesT (Fixed m)) => compile_keccak256_bytesm x m sm
     | _ => compile_keccak256_word x sm)` >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> drule_at (Pos hd) keccak_typed_post_run >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
      simp[compile_hash_singleton] >> pairarg_tac >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_at (Pos hd) keccak_typed_suffix_shape >> simp[] >>
      disch_then drule >> simp[]) >>
  gen_tac >> Cases_on `bty` >> gvs[is_bytes_or_string_type_def,
    is_bytestring_type_def, hash_suffix_appends, SF ETA_ss] >>
  rename1 `expr_type e = BaseT (BytesT bd)` >>
  Cases_on `bd` >> gvs[is_bytestring_type_def, hash_suffix_appends, SF ETA_ss]
QED

Theorem hash_digest_word_vv_post:
  stmt_state_rel func cenv cx es' s /\
  eval_operand op s = SOME w /\
  wb_frame cenv es sa s0 s ==>
  vv_post func cenv cx (Builtin (BaseT (BytesT (Fixed 32))) bt [e])
    es sa sb s0 es' (Value (BytesV (word_to_bytes w T)))
    (StackValue (BaseT (BytesT (Fixed 32))) op) s
Proof
  strip_tac >> irule vv_post_word_intro >>
  simp[vyperASTTheory.expr_type_def, is_word_type_def,
       vyperValueTheory.evaluate_type_def, typed_val_to_w256_def,
       PAD_RIGHT, word_of_bytes_be_def, word_of_bytes_word_to_bytes]
QED

Theorem sha256_fixed_post_run:
  expr_post func cenv cx e es sa sm s0 es' (BytesV bs) x s /\
  expr_type e = BaseT (BytesT (Fixed m)) /\
  value_has_type (BaseTV (BytesT (Fixed m))) (BytesV bs) /\ m <= 32 /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_sha256_bytesm x m sm = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    vv_post func cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e])
      es sa sb s0 es' (Value (BytesV (word_to_bytes (SHA_256_bytes bs) T)))
      (StackValue (BaseT (BytesT (Fixed 32))) op) t
Proof
  strip_tac >> drule_all hash_fixed_post_view >> strip_tac >>
  `!z. x = Var z ==> not_fresh_at sm z` by
    (drule_at (Pos hd) compile_lower_value_var >> simp[]) >>
  `stmt_state_rel func cenv cx es' s` by metis_tac[expr_post_state] >>
  drule_all (SRULE [] (Q.INST [`sha` |-> `T`] hash_fixed_alloca_code)) >>
  strip_tac >>
  qpat_x_assum `LENGTH bs = m` (SUBST_ALL_TAC o SYM) >>
  drule_at (Pos hd) compile_sha256_bytesm_frame >> simp[] >>
  disch_then (drule_at (Pos hd)) >> simp[] >>
  disch_then drule_all >> strip_tac >>
  qexists `t` >> simp[] >> irule hash_digest_word_vv_post >> simp[] >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  irule wb_frame_allocating_tail >> simp[] >>
  qexistsl [`s`, `es'.scopes`, `sm`] >> simp[] >>
  metis_tac[expr_post_frame]
QED

Theorem sha256_memory_post_run:
  expr_post func cenv cx e es sa sm s0 es' v x s /\
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
    vv_post func cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e])
      es sa sb s0 es' (Value (BytesV (word_to_bytes (SHA_256_bytes bs) T)))
      (StackValue (BaseT (BytesT (Fixed 32))) op) t
Proof
  strip_tac >>
  `!z. x = Var z ==> not_fresh_at sm z` by
    (drule_at (Pos hd) compile_lower_value_var >> simp[]) >>
  `stmt_state_rel func cenv cx es' s` by metis_tac[expr_post_state] >>
  drule_all hash_sha256_memory_alloca_code >> strip_tac >>
  drule_at (Pos hd) compile_sha256_bytes_frame >> simp[] >>
  disch_then (drule_at (Pos hd)) >> simp[] >>
  disch_then (drule_at (Pat `mem_bytes_at _ _ _ = _`)) >> simp[] >>
  disch_then drule_all >> strip_tac >>
  qexists `t` >> simp[] >> irule hash_digest_word_vv_post >> simp[] >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  irule wb_frame_allocating_tail >> simp[] >>
  qexistsl [`s`, `es'.scopes`, `sm`] >> simp[] >>
  metis_tac[expr_post_frame]
QED

Theorem sha256_typed_post_run:
  expr_post func cenv cx e es sa sm s0 es' v x s /\
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
    vv_post func cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e])
      es sa sb s0 es' (Value r) (StackValue (BaseT (BytesT (Fixed 32))) op) t
Proof
  strip_tac >> Cases_on `bty` >>
  gvs[is_bytes_or_string_type_def] >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
  gvs[is_bytestring_type_def, builtin_result_def, evaluate_builtin_def]
  >~ [`expr_type e = BaseT (BytesT bd)`]
  >- (Cases_on `bd` >>
      gvs[is_bytestring_type_def]
      >- (irule sha256_fixed_post_run >> goal_assum (drule_at Any) >>
          simp[vyperTypingTheory.value_has_type_def] >>
          gvs[vyperValueTheory.evaluate_type_def,
              vyperTypingTheory.value_has_type_def]) >>
      drule_at (Pos hd) hash_dynamic_post_view >> simp[] >> strip_tac >>
      irule sha256_memory_post_run >> goal_assum (drule_at Any) >>
      metis_tac[]) >>
  drule_at (Pos hd) hash_string_post_view >> simp[] >> strip_tac >>
  irule sha256_memory_post_run >> goal_assum (drule_at Any) >>
  simp[] >> qexistsl [`b`, `StringV s'`] >> simp[] >>
  `b < dimword (:256)` by decide_tac >> simp[]
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
  strip_tac >> Cases_on `bty` >> gvs[is_bytes_or_string_type_def,
    is_bytestring_type_def]
  >~ [`expr_type e = BaseT (BytesT bd)`]
  >- (Cases_on `bd` >> gvs[is_bytestring_type_def] >>
      irule hash_buffer_suffix_shape >> qexistsl [`n`, `op`, `x`] >> simp[]) >>
  irule hash_buffer_suffix_shape >> qexistsl [`0`, `op`, `x`] >> simp[]
QED

Theorem compile_sha256_typed_vv_sim:
  expr_body_pre cenv cx env (Builtin ann Sha256 [e]) es /\
  expr_sim ctx func cenv cx (expr_type e) e es ==>
  expr_vv_sim ctx func cenv cx ty (Builtin ann Sha256 [e]) es
Proof
  strip_tac >>
  `is_bytes_or_string_type (expr_type e) /\ ann = BaseT (BytesT (Fixed 32))` by
    (irule (SRULE [] (Q.INST [`b` |-> `Sha256`,
       `ts` |-> `[expr_type e]`] hash_builtin_types)) >>
     gvs[expr_body_pre_def, well_typed_expr_def]) >>
  `?bty. expr_type e = BaseT bty` by
    (Cases_on `expr_type e` >> gvs[is_bytes_or_string_type_def]) >>
  irule compile_typed_stack_unary_builtin_vv_sim >>
  simp[builtin_args_length_ok_def] >>
  reverse conj_tac >- (qexists `env` >> gvs[]) >>
  qexists `\x sm.
    (if is_bytestring_type (expr_type e) then compile_sha256_bytes x sm
     else case expr_type e of
       BaseT (BytesT (Fixed m)) => compile_sha256_bytesm x m sm
     | _ => compile_sha256_word x sm)` >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> drule_at (Pos hd) sha256_typed_post_run >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
      simp[compile_hash_singleton] >> pairarg_tac >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_at (Pos hd) sha256_typed_suffix_shape >> simp[] >>
      disch_then drule >> simp[]) >>
  gen_tac >> Cases_on `bty` >> gvs[is_bytes_or_string_type_def,
    is_bytestring_type_def, hash_suffix_appends, SF ETA_ss] >>
  rename1 `expr_type e = BaseT (BytesT bd)` >>
  Cases_on `bd` >> gvs[is_bytestring_type_def, hash_suffix_appends, SF ETA_ss]
QED

(* The selector's word representation is independent of the hash producer. *)
Theorem method_id_fixed_post_run:
  emit_op SHR [Lit 224w; hash] sm = (sel,sn) /\
  emit_op SHL [Lit 224w; sel] sn = (op,sb) /\
  eval_operand hash s = SOME w /\
  stmt_state_rel func cenv cx es' s /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ wb_frame cenv es sa s0 s ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    vv_post func cenv cx (Builtin (BaseT (BytesT (Fixed 4))) MethodId [e])
      es sa sb s0 es' (Value (BytesV (TAKE 4 (word_to_bytes w T))))
      (StackValue (BaseT (BytesT (Fixed 4))) op) t
Proof
  strip_tac >> drule_all method_id_mask_frame >> strip_tac >>
  qexists `t` >> simp[] >> irule vv_post_word_intro >>
  simp[vyperASTTheory.expr_type_def, is_word_type_def,
       vyperValueTheory.evaluate_type_def] >>
  irule wb_frame_readonly_tail >> qexistsl [`sm`, `s`] >> simp[] >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `_ with vs_vars := _ = _`
       (mp_tac o Q.AP_TERM `\z. (z.vs_memory,z.vs_allocas)`) >> simp[]) >>
  simp[]
QED

Theorem method_id_dynamic_post_run:
  emit_op SHR [Lit 224w; hash] sm = (sel,sn) /\
  emit_op SHL [Lit 224w; sel] sn = (word,sp) /\
  compile_alloc_buffer 64 sp = (buf,sh) /\
  emit_void MSTORE [buf.buf_operand; Lit 4w] sh = ((),st) /\
  emit_op ADD [buf.buf_operand; Lit 32w] st = (data,sd) /\
  emit_void MSTORE [data; word] sd = ((),sb) /\
  eval_operand hash s = SOME w /\
  stmt_state_rel func cenv cx es' s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm /\ fn_has_code sm sb func /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  wb_frame cenv es sa s0 s /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    vv_post func cenv cx (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [e])
      es sa sb s0 es' (Value (BytesV (TAKE 4 (word_to_bytes w T))))
      (LocatedValue (BaseT (BytesT (Dynamic 4)))
        <|ptr_location := LocMemory; ptr_operand := buf.buf_operand|>) t
Proof
  strip_tac >> drule_all hash_method_id_mask_cut >> strip_tac >>
  drule_all method_id_dynamic_suffix_frame >> strip_tac >>
  `sm.cs_next_id <= sp.cs_next_id /\ sp.cs_next_id < sb.cs_next_id` by
    (qpat_x_assum `emit_op SHR _ _ = _` mp_tac >>
     qpat_x_assum `emit_op SHL _ _ = _` mp_tac >>
     qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     qpat_x_assum `emit_void MSTORE [data; word] _ = _` mp_tac >>
     qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     qpat_x_assum `emit_void MSTORE [buf.buf_operand; _] _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> rpt strip_tac >> gvs[]) >>
  qexists `t` >> simp[] >>
  irule (SRULE [vyperASTTheory.expr_type_def]
    (Q.INST [`e` |-> `Builtin (BaseT (BytesT (Dynamic 4))) MethodId [e]`]
      vv_post_allocated_memory_intro)) >>
  simp[vyperASTTheory.expr_type_def, is_word_type_def,
       vyperValueTheory.evaluate_type_def] >>
  conj_tac
  >- (qexistsl [`sp.cs_next_id`, `w2n p`, `64`] >>
      simp[val_wf_def, val_footprint_def, type_slot_size_def,
           vfmConstantsTheory.word_size_def, type_memory_size_def, dimword_def] >>
      rpt strip_tac >>
      qpat_x_assum `!n b sz. local_region _ _ t _ _ _ ==> regions_disjoint _ _ _ _`
        drule >> simp[regions_disjoint_def]) >>
  irule wb_frame_allocating_tail >> simp[] >>
  qexistsl [`s`, `es'.scopes`, `sm`] >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >>
  qpat_x_assum `!aid off len. _ /\ FLOOKUP s.vs_allocas aid = SOME (off,len) ==> _` irule >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem method_id_of_keccak_result:
  builtin_result cx acc (BaseT (BytesT (Fixed 32))) Keccak256 [ty] [v] = INL r ==>
  ?bs. r = BytesV bs /\ LENGTH bs = 32 /\
    !ann. builtin_result cx acc ann MethodId [ty] [v] =
      INL (BytesV (TAKE 4 bs))
Proof
  Cases_on `v` >>
  simp[builtin_result_def, evaluate_builtin_def,
       vyperTypeBytesCryptoTheory.LENGTH_Keccak_256_w64] >>
  strip_tac >> gvs[] >>
  simp[vyperTypeBytesCryptoTheory.LENGTH_Keccak_256_w64]
QED

Theorem hash_full_bytes_roundtrip:
  LENGTH bs = 32 ==>
  word_to_bytes (typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) (BytesV bs)) T = bs
Proof
  strip_tac >>
  mp_tac (Q.INST [`bd` |-> `Fixed 32`] typed_bytes_prefix) >>
  simp[word_to_bytes_be_def, TAKE_LENGTH_TOO_LONG, LENGTH_word_to_bytes]
QED

Theorem method_id_hash_as_keccak:
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) ==>
  compile_method_id_hash (expr_type e) x sm =
    (if is_bytestring_type (expr_type e) then compile_keccak256_bytes x sm
     else case expr_type e of
       BaseT (BytesT (Fixed m)) => compile_keccak256_bytesm x m sm
     | _ => compile_keccak256_word x sm)
Proof
  strip_tac >> Cases_on `bty` >> gvs[is_bytes_or_string_type_def,
    is_bytestring_type_def, compile_method_id_hash_def] >>
  rename1 `expr_type e = BaseT (BytesT bd)` >> Cases_on `bd` >>
  gvs[is_bytestring_type_def, compile_method_id_hash_def]
QED

(* method_id hashes as keccak256 does; only the use of the word differs. *)
Theorem method_id_hash_typed_post_run:
  expr_post func cenv cx e es sa sm s0 es' v x s /\
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
    stmt_state_rel func cenv cx es' t /\ wb_frame cenv es sa s0 t /\
    !ann. builtin_result cx es'.accounts ann MethodId [expr_type e] [v] =
      INL (BytesV (TAKE 4 bs))
Proof
  strip_tac >>
  `(if is_bytestring_type (expr_type e) then compile_keccak256_bytes x sm
    else case expr_type e of
      BaseT (BytesT (Fixed m)) => compile_keccak256_bytesm x m sm
    | _ => compile_keccak256_word x sm) = (hash,sh)` by
    (drule_all method_id_hash_as_keccak >> disch_then (qspecl_then [`x`, `sm`] mp_tac) >>
     gvs[]) >>
  drule_all keccak_typed_post_run >> strip_tac >>
  drule_all method_id_of_keccak_result >> strip_tac >> gvs[] >>
  qexists `bs` >> simp[] >>
  gvs[vv_post_def, vv_holds_def, expr_val_rel_def,
      vyperASTTheory.expr_type_def, vyperValueTheory.evaluate_type_def,
      wb_frame_def, is_word_type_def, read_result_def, return_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[] >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  qexists `aid` >> simp[]
QED

Theorem method_id_hash_grows:
  compile_method_id_hash ty x sa = (op,sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id
Proof
  metis_tac[ci_mono_compile_method_id_hash, ci_mono_def, pairTheory.SND]
QED

Theorem method_id_tail_shape:
  compile_method_id_runtime ty x fixed sa = (op,sb) /\
  compile_method_id_hash ty x sa = (hash,sm) ==>
  same_blocks sm sb /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sm sb)
Proof
  simp[compile_method_id_runtime_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  Cases_on `fixed` >>
  gvs[contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def] >>
  gvs[same_blocks_def, emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem method_id_runtime_typed_post_run:
  expr_post func cenv cx e es sa sm s0 es' v x s /\
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
    vv_post func cenv cx
      (Builtin (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4))) MethodId [e])
      es sa sb s0 es' (Value r)
      (if fixed then StackValue (BaseT (BytesT (Fixed 4))) op else
       LocatedValue (BaseT (BytesT (Dynamic 4)))
         <|ptr_location := LocMemory; ptr_operand := op|>) t
Proof
  strip_tac >> drule_all hash_method_id_runtime_cut >> strip_tac >>
  drule_all hash_method_id_hash_cut >> strip_tac >>
  drule_all method_id_hash_typed_post_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sm sm') s = OK hashed` >>
  `sa.cs_next_var <= sm'.cs_next_var /\ sa.cs_next_id <= sm'.cs_next_id` by
    (drule (cj 2 compile_expr_grows) >> strip_tac >>
     drule_all method_id_hash_grows >> strip_tac >> decide_tac) >>
  `local_ptrs_reserved cenv sm'` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `sm'.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sm' /\
   sb.cs_current_insts = sm'.cs_current_insts ++ emitted_insts sm' sb` by
    (drule_all method_id_tail_shape >> strip_tac >>
     drule_all method_id_hash_as_keccak >>
     disch_then (qspecl_then [`x`, `sm`] SUBST_ALL_TAC) >>
     drule_all keccak_typed_suffix_shape >> simp[]) >>
  Cases_on `fixed` >> gvs[]
  >- suspend "fixed"
  >> suspend "dynamic"
QED

Resume method_id_runtime_typed_post_run[fixed]:
  drule_all method_id_fixed_post_run >>
  disch_then (qspec_then `e` strip_assume_tac) >>
  `run_inst_seq (emitted_insts sm sb) s =
     run_inst_seq (emitted_insts sm' sb) hashed` by
    (irule (cj 1 run_inst_seq_chain) >> simp[]) >>
  qexists `t` >> gvs[hash_full_bytes_roundtrip]
QED

Resume method_id_runtime_typed_post_run[dynamic]:
  drule_all method_id_dynamic_post_run >>
  disch_then (qspec_then `e` strip_assume_tac) >>
  `run_inst_seq (emitted_insts sm sb) s =
     run_inst_seq (emitted_insts sm' sb) hashed` by
    (irule (cj 1 run_inst_seq_chain) >> simp[]) >>
  qexists `t` >> gvs[hash_full_bytes_roundtrip]
QED

Finalise method_id_runtime_typed_post_run

Theorem method_id_typed_suffix_shape:
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  compile_method_id_runtime (expr_type e) x fixed sa = (op,sb) ==>
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  strip_tac >> drule_all hash_method_id_runtime_cut >> strip_tac >>
  drule_all method_id_tail_shape >> strip_tac >>
  drule_all method_id_hash_as_keccak >>
  disch_then (qspecl_then [`x`, `sa`] SUBST_ALL_TAC) >>
  drule_all keccak_typed_suffix_shape >> strip_tac >>
  drule_all emitted_insts_append >> strip_tac >>
  gvs[same_blocks_def]
QED

Theorem vv_post_pointer_cong:
  p.ptr_operand = q.ptr_operand /\ p.ptr_location = q.ptr_location /\
  vv_post func cenv cx e es sa sb s0 es' r (LocatedValue ty p) t ==>
  vv_post func cenv cx e es sa sb s0 es' r (LocatedValue ty q) t
Proof
  strip_tac >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  asm_rewrite_tac[vv_post_def, vv_holds_def, vv_at_def]
QED

Theorem compile_method_id_runtime_typed_vv_sim:
  expr_body_pre cenv cx env (Builtin ann MethodId [e]) es /\
  expr_sim ctx func cenv cx (expr_type e) e es /\ method_id_literal e = NONE ==>
  expr_vv_sim ctx func cenv cx ty (Builtin ann MethodId [e]) es
Proof
  strip_tac >>
  `is_bytes_or_string_type (expr_type e) /\
    (ann <> BaseT (BytesT (Dynamic 4)) ==> ann = BaseT (BytesT (Fixed 4)))` by
    (mp_tac (SRULE [] (Q.INST [`b` |-> `MethodId`,
       `ty` |-> `ann`, `ts` |-> `[expr_type e]`] hash_builtin_types)) >>
     (impl_tac >- gvs[expr_body_pre_def, well_typed_expr_def]) >> metis_tac[]) >>
  `?bty. expr_type e = BaseT bty` by
    (Cases_on `expr_type e` >> gvs[is_bytes_or_string_type_def]) >>
  qabbrev_tac `fixed = (ann = BaseT (BytesT (Fixed 4)))` >>
  `ann = BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4))` by
    (gvs[Abbr `fixed`] >> metis_tac[]) >>
  irule compile_typed_unary_builtin_vv_sim >>
  simp[builtin_args_length_ok_def] >>
  qexistsl [`\x sm. let (op,sb) =
      compile_method_id_runtime (expr_type e) x fixed sm in
      ((if fixed then StackValue ann op else
        LocatedValue ann (mk_ptr op LocMemory)),sb)`, `env`] >> simp[] >>
  reverse conj_tac
  >- (conj_tac >- suspend "compile" >> suspend "appends") >>
  suspend "continuation"
QED

Resume compile_method_id_runtime_typed_vv_sim[compile]:
  rpt strip_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_method_id_singleton_runtime] >>
  pairarg_tac >> simp[] >>
  Cases_on `compile_method_id_runtime (expr_type e) v fixed sm` >>
  Cases_on `fixed` >> gvs[as_stack_val_def, as_ptr_val_def] >>
  metis_tac[]
QED

Resume compile_method_id_runtime_typed_vv_sim[appends]:
  reverse conj_tac >- gvs[] >>
  gen_tac >> simp[cs_appends_def] >> rpt gen_tac >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule (SRULE [cs_appends_def] (cj 5 hash_suffix_appends)) >> simp[]
QED

Resume compile_method_id_runtime_typed_vv_sim[continuation]:
  rpt strip_tac >> pairarg_tac >> gvs[] >>
  `expr_body_pre cenv cx env e es'` by
    (irule expr_body_pre_builtin_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ _ _`)) >> simp[]) >>
  `evaluate_type (get_tenv cx) (BaseT bty) = SOME (BaseTV bty)` by
    (drule expr_body_pre_type_evaluates >>
     simp[vyperValueTheory.evaluate_type_def] >>
     Cases_on `bty` >> gvs[AllCaseEqs()] >>
     rename1 `expr_type e = BaseT (BytesT bd)` >>
     Cases_on `bd` >> gvs[AllCaseEqs()]) >>
  drule exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom >> strip_tac >>
  drule_at (Pos hd) method_id_runtime_typed_post_run >> simp[] >>
  disch_then drule_all >> strip_tac >>
  drule_at (Pos hd) method_id_typed_suffix_shape >> simp[] >>
  disch_then drule_all >> strip_tac >>
  irule hash_run_frag >> simp[] >>
  Cases_on `fixed` >> gvs[contextTheory.mk_ptr_def] >>
  irule vv_post_pointer_cong >> goal_assum (drule_at Any) >> simp[]
QED

Finalise compile_method_id_runtime_typed_vv_sim

Theorem compile_method_id_other_typed_vv_sim:
  expr_body_pre cenv cx env (Builtin ann MethodId [e]) es /\
  expr_sim ctx func cenv cx (expr_type e) e es /\
  ~(ann = BaseT (BytesT (Fixed 4)) /\
    ?la l. e = Literal la l /\ IS_SOME (method_id_literal (Literal la l))) ==>
  expr_vv_sim ctx func cenv cx ty (Builtin ann MethodId [e]) es
Proof
  strip_tac >> Cases_on `method_id_literal e = NONE`
  >- (irule compile_method_id_runtime_typed_vv_sim >> simp[] >>
      qexists `env` >> simp[]) >>
  `is_bytes_or_string_type (expr_type e) /\
    (ann <> BaseT (BytesT (Dynamic 4)) ==> ann = BaseT (BytesT (Fixed 4)))` by
    (mp_tac (SRULE [] (Q.INST [`b` |-> `MethodId`,
       `ty` |-> `ann`, `ts` |-> `[expr_type e]`] hash_builtin_types)) >>
     (impl_tac >- gvs[expr_body_pre_def, well_typed_expr_def]) >> metis_tac[]) >>
  `?la l. e = Literal la l` by
    (Cases_on `e` >> gvs[method_id_literal_def] >>
     rename1 `method_id_literal (Literal la l)` >> Cases_on `l` >>
     gvs[method_id_literal_def]) >> gvs[] >>
  `IS_SOME (method_id_literal (Literal la l))` by
    (Cases_on `method_id_literal (Literal la l)` >> gvs[]) >>
  drule compile_method_id_literal_dynamic_vv_sim >>
  rw[expr_vv_ok_def] >> first_x_assum irule >> qexists `env` >>
  gvs[expr_sim_pre_body, vyperTypeCallGraphTheory.int_calls_expr_def]
QED
