(* Continuing scalar event encoder frame; allocation resources live below the runner. *)
Theory stmtSimLogEncodeFrame
Ancestors
  stmtSimLogScalarEncode stmtSimLogAllocResource stmtSimLogEncodeFields
  stmtSimLogExecFields localPtrsProps loweringSlice abiDecoderFrame
  valueEncodingProps compileEnv exprLoweringProps venomState venomMemProps
  venomExecSemantics venomInst venomMemDefs abiBuiltinAllocation finite_map words list arithmetic

Theorem log_encode_local_frame[local]:
  local_ptrs_rel func ce scopes s /\
  (!name entry p sz. lookup_scopes name scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p t = lookup_var p s) /\
  (!aid r. FLOOKUP s.vs_allocas aid = SOME r ==>
    FLOOKUP t.vs_allocas aid = SOME r) /\
  (!aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
    FLOOKUP s.vs_allocas aid = NONE ==> s.vs_alloca_next <= b) /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  abi_decode_footprint_frame fp s t /\
  (!name lo sz. local_region ce scopes s name lo sz ==>
    abi_footprint_disjoint lo sz fp) ==>
  local_ptrs_rel func ce scopes t
Proof
  cheat
QED

Theorem log_encode_immutable_frame[local]:
  immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor es s /\
  abi_decode_footprint_frame fp s t /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    abi_footprint_disjoint off (type_memory_size tv) fp) ==>
  immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor es t
Proof
  cheat
QED

Theorem log_encode_step_memory_mono[local]:
  log_encode_safe_opcode i.inst_opcode /\ step_inst_base i s = OK t ==>
  LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  cheat
QED

Theorem log_encode_run_memory_mono:
  !code s t. EVERY (\i. log_encode_safe_opcode i.inst_opcode) code /\
  run_inst_seq code s = OK t ==> LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  cheat
QED

Theorem log_encode_state_frame[local]:
  state_rel func ce cx es s /\ log_encode_external t = log_encode_external s /\
  (!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p t = lookup_var p s) /\
  (!aid r. FLOOKUP s.vs_allocas aid = SOME r ==>
    FLOOKUP t.vs_allocas aid = SOME r) /\
  (!aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
    FLOOKUP s.vs_allocas aid = NONE ==> s.vs_alloca_next <= b) /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  abi_decode_footprint_frame fp s t /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (!name lo sz. local_region ce es.scopes s name lo sz ==>
    abi_footprint_disjoint lo sz fp) /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    abi_footprint_disjoint off (type_memory_size tv) fp) ==>
  state_rel func ce cx es t
Proof
  cheat
QED

Theorem log_encode_local_region_frame[local]:
  (!name entry p sz. lookup_scopes name scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p t = lookup_var p s) ==>
  (local_region ce scopes t name lo sz <=> local_region ce scopes s name lo sz)
Proof
  cheat
QED

Theorem log_encode_immutable_sep_frame[local]:
  immutable_alloca_sep func ce cx es s /\
  (!name lo sz. local_region ce es.scopes t name lo sz ==>
    local_region ce es.scopes s name lo sz) /\
  (!aid r. FLOOKUP s.vs_allocas aid = SOME r ==>
    FLOOKUP t.vs_allocas aid = SOME r) /\
  (!aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
    FLOOKUP s.vs_allocas aid = NONE ==> s.vs_alloca_next <= b) /\
  s.vs_alloca_next <= t.vs_alloca_next ==>
  immutable_alloca_sep func ce cx es t
Proof
  cheat
QED

Theorem log_encode_allocate_metadata[local]:
  !site n s. (abi_builtin_allocate_state site n s).vs_alloca_next >= s.vs_alloca_next /\
  (!id r. FLOOKUP s.vs_allocas id = SOME r ==>
    FLOOKUP (abi_builtin_allocate_state site n s).vs_allocas id = SOME r) /\
  (!id b sz. FLOOKUP (abi_builtin_allocate_state site n s).vs_allocas id = SOME (b,sz) /\
    FLOOKUP s.vs_allocas id = NONE ==> s.vs_alloca_next <= b)
Proof
  cheat
QED

Theorem log_encode_allocate_inv[local]:
  alloca_inv s ==> alloca_inv (abi_builtin_allocate_state site n s)
Proof
  cheat
QED

Theorem log_encode_allocate_sizes[local]:
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit (n2w n)] /\ n < dimword (:256) ==>
  !i v b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit v] /\
    FLOOKUP (abi_builtin_allocate_state inst.inst_id n s).vs_allocas i.inst_id = SOME (b,sz) ==>
    sz = w2n v
Proof
  cheat
QED

Theorem log_encode_allocation_frame[local]:
  stmt_state_rel ctx func ce cx es s /\ state_rel func ce cx es t /\
  immutable_alloca_sep func ce cx es t /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit (n2w n)] /\ n < dimword (:256) /\
  t.vs_allocas = (abi_builtin_allocate_state inst.inst_id n s).vs_allocas /\
  t.vs_alloca_next = (abi_builtin_allocate_state inst.inst_id n s).vs_alloca_next /\
  t.vs_fmp = s.vs_fmp /\ immutable_base_zero ce t ==>
  stmt_state_rel ctx func ce cx es t
Proof
  cheat
QED

Theorem log_encode_continuation:
  stmt_state_rel ctx func ce cx es s /\
  log_encode_external t = log_encode_external s /\
  (!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p t = lookup_var p s) /\
  (!x. ce.ce_imm_alloca = SOME (Var x) ==> lookup_var x t = lookup_var x s) /\
  abi_decode_footprint_frame fp s t /\ LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (!name lo sz. local_region ce es.scopes s name lo sz ==>
    abi_footprint_disjoint lo sz fp) /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    abi_footprint_disjoint off (type_memory_size tv) fp) /\
  t.vs_allocas = (if dyn then abi_builtin_allocate_state site n s else s).vs_allocas /\
  t.vs_alloca_next = (if dyn then abi_builtin_allocate_state site n s else s).vs_alloca_next /\
  (dyn ==> fn_inst_ids_distinct func /\
    ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_operands = [Lit (n2w n)] /\ inst.inst_id = site /\ n < dimword (:256)) ==>
  stmt_state_rel ctx func ce cx es t
Proof
  cheat
QED

Theorem log_encode_local_operands[local]:
  stmt_state_rel ctx func ce cx es s /\
  (!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    abi_decoder_operand_live nv (Var p)) /\
  (!op w. abi_decoder_operand_live nv op /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w) ==>
  !name entry p sz. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p t = lookup_var p s
Proof
  cheat
QED

Theorem log_scalar_tuple_continue:
  compile_abi_encode_to_buf dst src ei st = (out,end_st) /\
  abi_encoder_input ei (Tuple ats) (ListV avs) sb cap initial.vs_memory /\
  ((?n. ei = AbiCopy n /\ n < dimword (:256)) \/
   (?infos. ei = AbiComplex infos /\ EXISTS (\(_,_,_,dyn). dyn) infos /\
     EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos)) /\
  LENGTH (enc (Tuple ats) (ListV avs)) <= outcap /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w db) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  sb+cap < dimword (:256) /\ db+outcap < dimword (:256) /\
  (sb+cap <= db \/ db+outcap <= sb) /\
  fresh_vars_wrt limit_st initial /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  ((?infos. ei = AbiComplex infos) ==>
    ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
      FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,32)) /\
    p < dimword (:256) /\ (sb+cap <= p \/ p+32 <= sb) /\
    (db+outcap <= p \/ p+32 <= db)) /\
  stmt_state_rel ctx func ce cx es initial /\
  (!name entry v sz. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var v) sz) ==>
    abi_decoder_operand_live st.cs_next_var (Var v)) /\
  (!x. ce.ce_imm_alloca = SOME (Var x) ==>
    abi_decoder_operand_live st.cs_next_var (Var x)) /\
  (!name lo sz. local_region ce es.scopes initial name lo sz ==>
    abi_footprint_disjoint lo sz
      ((db,outcap)::(if (?infos. ei = AbiComplex infos) then [(p,32)] else []))) /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    abi_footprint_disjoint off (type_memory_size tv)
      ((db,outcap)::(if (?infos. ei = AbiComplex infos) then [(p,32)] else []))) /\
  ((?infos. ei = AbiComplex infos) ==> fn_inst_ids_distinct func /\
    ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_operands = [Lit (n2w 32)] /\ inst.inst_id = st.cs_next_id) ==>
  ?actual. run_inst_seq (emitted_insts st end_st) initial = OK actual /\
    inst_extends st end_st /\ fresh_vars_wrt limit_st actual /\
    mem_bytes_at db (LENGTH (enc (Tuple ats) (ListV avs))) actual.vs_memory =
      enc (Tuple ats) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple ats) (ListV avs)))) /\
    stmt_state_rel ctx func ce cx es actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w)
Proof
  cheat
QED
