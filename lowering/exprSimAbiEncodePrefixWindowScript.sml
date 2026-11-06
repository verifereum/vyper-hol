Theory exprSimAbiEncodePrefixWindow
Ancestors
  exprSimHash exprSimAlloc exprSimLiteralBuffer loweringPosts
  exprSimBufferStore abiValueEncoding
  abiBuiltinAllocation exprSimAbiEncodeConcreteResources
  valueEncodingProps compileEnv exprLoweringProps emitHelperProps
  venomMemDefs venomInst venomState words finite_map list arithmetic

(* The actual singleton word staging prefix keeps its allocation certificate.
   In particular this also covers re-entry, where the site already exists. *)
Theorem abi_encode_word_staging:
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; op] sm = ((),sh) /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  eval_operand op s = SOME w /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
  ?allocated addr.
    run_inst_seq (emitted_insts sa sm) s = OK allocated /\
    run_inst_seq (emitted_insts sm sh) allocated =
      OK (mstore (w2n addr) w allocated) /\
    stmt_state_rel ctx func cenv cx es (mstore (w2n addr) w allocated) /\
    eval_operand buf.buf_operand allocated = SOME addr /\
    eval_operand op allocated = SOME w /\
    FLOOKUP allocated.vs_allocas sa.cs_next_id = SOME (w2n addr,32) /\
    w2n addr + 32 < dimword (:256) /\
    mem_bytes_at (w2n addr) 32 (mstore (w2n addr) w allocated).vs_memory =
      word_to_bytes_be w
Proof
  strip_tac >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `eval_operand buf.buf_operand allocated = SOME addr` >>
  `allocated.vs_labels = s.vs_labels` by
    (drule_all hash_alloc_buffer_labels >> simp[]) >>
  `eval_operand op allocated = SOME w` by
    (Cases_on `op` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts sm sh) allocated =
     OK (mstore (w2n addr) w allocated)` by
    (irule literal_emit_mstore_run >>
     qexistsl_tac [`buf.buf_operand`, `op`] >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es (mstore (w2n addr) w allocated)` by
    (irule literal_mstore_state_rel >> simp[] >>
     qexistsl_tac [`w2n addr`,
       `mk_inst sa.cs_next_id ALLOCA [Lit 32w]
          [STRING #"%" (toString sa.cs_next_var)]`, `32`] >>
     simp[mk_inst_def] >> rpt strip_tac >>
     first_x_assum drule >> simp[compileEnvTheory.regions_disjoint_def]) >>
  qexistsl_tac [`allocated`, `addr`] >>
  simp[mem_bytes_at_mstore_same, byteTheory.word_to_bytes_be_def]
QED

(* Resource-only view of a real ALLOCA site. No execution or scratch budget
   is assumed: both the reuse size and fresh room come from stmt_state_rel. *)
Theorem abi_encode_allocate_resources:
  stmt_state_rel ctx func cenv cx es s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit (n2w sz)] /\ sz < dimword (:256) ==>
  let a = abi_builtin_allocate_state inst.inst_id sz s in
  alloca_inv a /\ alloca_room ctx func a /\
  ?p. FLOOKUP a.vs_allocas inst.inst_id = SOME (p,sz) /\
      p+sz <= a.vs_alloca_next /\ a.vs_alloca_next < dimword (:256)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `alloca_inv s /\ alloca_room ctx func s` by fs[stmt_state_rel_def] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (`inst.inst_id NOTIN FDOM s.vs_allocas` by fs[FLOOKUP_DEF] >>
      drule_all alloca_room_fresh >> strip_tac >>
      simp[abi_builtin_allocate_state_def, FLOOKUP_UPDATE] >>
      conj_tac
      >- (gvs[alloca_inv_def, allocas_non_overlapping_def,
              alloca_next_valid_def] >>
          rw[FLOOKUP_UPDATE] >> gvs[] >> res_tac >> gvs[]) >>
      gvs[w2n_n2w, ADD_COMM]) >>
  rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME entry` >>
  PairCases_on `entry` >>
  `entry1 = sz` by
    (fs[stmt_state_rel_def] >> first_x_assum drule_all >> simp[]) >>
  simp[abi_builtin_allocate_state_def] >>
  conj_tac
  >- (gvs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  metis_tac[alloca_room_next_lt]
QED

Theorem abi_encode_word_output_resources:
  stmt_state_rel ctx func cenv cx es s /\
  FLOOKUP s.vs_allocas source_id = SOME (sb,32) /\
  source_id <> inst.inst_id /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit (n2w outsz)] /\ outsz < dimword (:256) /\
  offset + 32 <= outsz ==>
  let a = abi_builtin_allocate_state inst.inst_id outsz s in
  alloca_inv a /\ alloca_room ctx func a /\
  sb+32 <= a.vs_alloca_next /\
  ?p. FLOOKUP a.vs_allocas inst.inst_id = SOME (p,outsz) /\
      p+offset+32 <= a.vs_alloca_next /\
      venomMemDefs$regions_disjoint (sb,32) (p+offset,32)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_encode_allocate_resources >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `alloca_inv a` >>
  `FLOOKUP a.vs_allocas source_id = SOME (sb,32)` by
    simp[Abbr `a`, abiEncodeWindowBuiltinTheory.abi_window_allocate_other_row] >>
  `sb+32 <= a.vs_alloca_next` by
    (fs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  `sb+32 <= p \/ p+outsz <= sb` by
    (fs[alloca_inv_def, allocas_non_overlapping_def] >>
     first_x_assum drule_all >> simp[]) >>
  simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

(* Typed source representation at the very same staging endpoint. The type
   and conversion premises are the successful source builtin's checks. *)
Theorem abi_encode_word_expr_post:
  expr_post ctx func cenv cx e es origin sa s0 es' v op s /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av /\
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; op] sm = ((),sh) /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
  ?allocated addr.
    run_inst_seq (emitted_insts sa sm) s = OK allocated /\
    run_inst_seq (emitted_insts sm sh) allocated =
      OK (mstore (w2n addr) (typed_val_to_w256 tv v) allocated) /\
    stmt_state_rel ctx func cenv cx es'
      (mstore (w2n addr) (typed_val_to_w256 tv v) allocated) /\
    eval_operand buf.buf_operand allocated = SOME addr /\
    FLOOKUP allocated.vs_allocas sa.cs_next_id = SOME (w2n addr,32) /\
    w2n addr+32 < dimword (:256) /\
    mem_bytes_at (w2n addr) 32
      (mstore (w2n addr) (typed_val_to_w256 tv v) allocated).vs_memory =
      enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av /\
    LENGTH (enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av) = 32
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es' s /\
   eval_operand op s = SOME (typed_val_to_w256 tv v)` by
    (gvs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  drule_all abi_encode_word_staging >> strip_tac >>
  drule_all (SRULE [] buffer_store_word_encoding) >> strip_tac >> gvs[] >>
  `w2n addr + 32 <= LENGTH
      (mstore (w2n addr) (typed_val_to_w256 tv v) allocated).vs_memory` by
    (simp[mstore_def, byteTheory.LENGTH_word_to_bytes, LENGTH_TAKE] >>
     rw[] >> simp[]) >>
  drule_all abi_word_memory >> strip_tac >> metis_tac[]
QED
