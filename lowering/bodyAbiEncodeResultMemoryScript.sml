(* Same-endpoint packaging for the ABI encoder's memory execution. *)
Theory bodyAbiEncodeResultMemory
Ancestors
  bodyAbiEncodeRegisteredFrame
  abiEncoderWindowMemFrame abiEncoderWindowPhase exprSimHash exprSimMemDefs
  localPtrsProps loweringSlice exprSimProps abiEncoderWindowContract
  exprLoweringProps compileEnv abiEncoderRegisteredEffect arithmetic venomState exprSimHyps
  loweringPosts loweringStateRelDefs exprLowering vyperState vyperInterpreter valueEncoding context

Theorem abi_encode_result_state:
  stmt_state_rel ctx func ce cx ee s /\
  window_phase ctx func st en ids outs s t /\
  window_mem_frame ctx func s t /\
  (!name entry p sz. lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p t = lookup_var p s) /\
  (!p. ce.ce_imm_alloca = SOME (Var p) ==> lookup_var p t = lookup_var p s) /\
  (!name b sz. local_region ce ee.scopes s name b sz ==>
    mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory) /\
  (!name b sz. local_region ce ee.scopes t name b sz ==>
    local_region ce ee.scopes s name b sz) /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    mem_bytes_at off (type_memory_size tv) t.vs_memory =
    mem_bytes_at off (type_memory_size tv) s.vs_memory) /\
  (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\ inst.inst_id IN ids /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) ==>
  stmt_state_rel ctx func ce cx ee t
Proof
  strip_tac >>
  `local_ptrs_rel func ce ee.scopes t` by
    (irule local_ptrs_rel_mem_agree >> qexists `s` >>
     fs[stmt_state_rel_def, state_rel_def, window_phase_def,
        window_alloca_growth_def, abi_encoder_registered_effect_def] >> metis_tac[]) >>
  `immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor ee t` by
    (irule immutables_rel_mem_agree >> qexists `s` >>
     fs[stmt_state_rel_def, state_rel_def, window_mem_frame_def] >>
     first_assum ACCEPT_TAC) >>
  `immutable_base_zero ce t` by
    (irule immutable_base_zero_frame >> qexists `s` >>
     fs[stmt_state_rel_def, window_phase_def]) >>
  `immutable_alloca_sep func ce cx ee t` by
    (irule immutable_alloca_sep_frame >> qexistsl [`s`, `ee`] >>
     fs[stmt_state_rel_def, window_phase_def, window_alloca_growth_def,
        abi_encoder_registered_effect_def] >>
     conj_tac
     >- (rpt strip_tac >> disj1_tac >> qexists `id` >> first_x_assum irule >> simp[]) >>
     rpt strip_tac >> Cases_on `FLOOKUP s.vs_allocas aid`
     >- (disj2_tac >> first_x_assum irule >> goal_assum drule >> simp[]) >>
     PairCases_on `x` >> disj1_tac >>
     first_x_assum drule >> simp[]) >>
  fs[stmt_state_rel_def, window_phase_def, window_mem_frame_def,
     abi_encoder_registered_effect_def, state_rel_def,
     storage_rel_def, transient_rel_def, accounts_rel_def, logs_rel_def,
     contract_storage_def, contract_transient_def] >>
  rpt strip_tac >> Cases_on `inst.inst_id IN ids` >> metis_tac[]
QED

(* The semantic bytes annotation and the allocated lowering capacity can differ. *)
Theorem abi_encode_allocated_bytes_result:
  expr_type e = BaseT (BytesT (Dynamic declared)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic declared))) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) =
    SOME (BaseTV (BytesT (Dynamic capacity))) /\
  val_wf (BaseTV (BytesT (Dynamic declared))) (BytesV bytes) /\
  val_in_memory (BaseTV (BytesT (Dynamic declared))) (BytesV bytes) b t.vs_memory /\
  LENGTH bytes <= capacity /\ sz = 32 + 32 * word_size capacity /\
  b + sz < dimword (:256) /\ b + sz <= t.vs_alloca_next /\
  stmt_state_rel ctx func ce cx ee t /\
  eval_operand out t = SOME (n2w b) /\
  FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  (!name lb lsz. local_region ce ee.scopes t name lb lsz ==>
    b + sz <= lb \/ lb + lsz <= b) /\
  wb_frame ce es ee sa s0 t /\
  post_value_type ce e = expr_type e /\
  (~expr_has_effect e ==> pure_frame ce func es sa s0 t) ==>
  vv_post ctx func ce cx e es sa sb s0 ee (Value (BytesV bytes))
    (LocatedValue (expr_type e) (mk_ptr out LocMemory)) t /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee
    (Value (BytesV bytes)) (LocatedValue (expr_type e) (mk_ptr out LocMemory)) t
Proof
  strip_tac >>
  `b < dimword (:256)` by decide_tac >>
  `LENGTH bytes <= 32 * word_size capacity` by
    metis_tac[le_word_size_mul, LESS_EQ_TRANS] >>
  conj_tac
  >- (irule vv_post_allocated_memory_intro >>
      simp[mk_ptr_def, is_word_type_def] >>
      qexistsl [`aid`, `b`, `sz`] >>
      simp[mk_ptr_def, is_word_type_def, val_footprint_def] >>
      metis_tac[ADD_COMM]) >>
  `word_size (LENGTH bytes) <= word_size capacity` by
    metis_tac[exprSimHypsTheory.word_size_monotone] >>
  simp[vv_store_bound_def, mk_ptr_def, read_result_def, return_def,
       vyperValueTheory.evaluate_type_def, val_store_size_def, type_memory_size_def] >>
  decide_tac
QED
