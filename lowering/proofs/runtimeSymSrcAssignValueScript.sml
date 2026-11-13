Theory runtimeSymSrcAssignValue
Ancestors
  runtimeSymSrcInterfaces runtimeSymSrcEmission stmtLowering compileEnv
  context venomInst stackPlanTypes

(* Literal external boundary ledger: every primitive below belongs to
   C1.1.3.2 (context memory and typed-copy boundaries). No implementation
   theorem is imported: the enclosing join discharges these implications.
   The immutable allocation premise is essential even for word stores. *)
Theorem runtime_sym_assign_normalize[local]:
  (!n s b s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_alloc_buffer n s = (b,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand b.buf_operand) /\
  (!b dt v st s u s'. ~is_label_operand b /\ ~is_label_operand v /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_store_memory_typed ce b dt v st s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  !guard n dt st v s op s'.
    ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
    (if guard then
       do b <- compile_alloc_buffer n;
          compile_store_memory_typed ce b.buf_operand dt v st;
          return b.buf_operand od
     else return v) s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  strip_tac >> rpt gen_tac >> Cases_on `guard` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def]
  >- (rpt (pairarg_tac >> simp[]) >> rpt strip_tac >> gvs[] >>
      first_assum drule_all >> strip_tac >>
      first_assum drule_all >> simp[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem runtime_sym_compile_assign_value:
  (!n s b s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_alloc_buffer n s = (b,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand b.buf_operand) /\
  (!d v n s u s'. ~is_label_operand d /\ ~is_label_operand v /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_copy_memory d v n s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!v d dt st s u s'. ~is_label_operand v /\ ~is_label_operand d /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_store_memory ce v d dt st s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!d dt v st s u s'. ~is_label_operand d /\ ~is_label_operand v /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_store_memory_typed ce d dt v st s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!v d ew em tr s u s'. ~is_label_operand v /\ ~is_label_operand d /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_dynarray_to_storage v d ew em tr s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!v d n s u s'. ~is_label_operand v /\ ~is_label_operand d /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_memory_to_storage v d n s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!v d n s u s'. ~is_label_operand v /\ ~is_label_operand d /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_memory_to_transient v d n s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!d v s u s'. ~is_label_operand d /\ ~is_label_operand v /\
    (!b. ce.ce_imm_alloca = SOME b ==> ~is_label_operand b) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_imm_store_word ce.ce_imm_alloca d v s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!v d s u s'. ~is_label_operand v /\ ~is_label_operand d /\
    (!b. ce.ce_imm_alloca = SOME b ==> ~is_label_operand b) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_store_immutable_bytestring ce.ce_imm_alloca v d s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!v d n off s u s'. ~is_label_operand v /\ ~is_label_operand d /\
    (!b. ce.ce_imm_alloca = SOME b ==> ~is_label_operand b) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_imm_store_words ce.ce_imm_alloca v d n off s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  !dst loc value prim srcLoc dstTy srcTy da sz s u s'.
    ~is_label_operand dst /\ ~is_label_operand value /\
    (!b. ce.ce_imm_alloca = SOME b ==> ~is_label_operand b) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_assign_value ce dst loc value prim srcLoc dstTy srcTy da sz s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "alloc")
    (CONJUNCTS_THEN2 (mk_asm "copy")
    (CONJUNCTS_THEN2 (mk_asm "store")
    (CONJUNCTS_THEN2 (mk_asm "typed")
    (CONJUNCTS_THEN2 (mk_asm "dyn")
    (CONJUNCTS_THEN2 (mk_asm "storage")
    (CONJUNCTS_THEN2 (mk_asm "transient")
    (CONJUNCTS_THEN2 (mk_asm "imm")
    (CONJUNCTS_THEN2 (mk_asm "bytes")
      (mk_asm "words")))))))))) >>
  rpt gen_tac >> Cases_on `loc`
  >- suspend "memory"
  >- suspend "storage"
  >- suspend "transient"
  >- suspend "code"
  >> suspend "calldata"
QED

Resume runtime_sym_compile_assign_value[memory]:
  Cases_on `prim` >> simp[NoAsms, compile_assign_value_def]
  >- (strip_tac >> drule_at (Pat `emit_void _ _ _ = _`)
        runtime_sym_emit_void >> simp[]) >>
  Cases_on `srcLoc = SOME LocMemory` >> simp[]
  >- (simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> simp[]) >> rpt strip_tac >> gvs[] >>
      asm "alloc" drule_all >> strip_tac >>
      asm "copy" drule_all >> strip_tac >>
      asm "store" drule_all >> simp[]) >>
  strip_tac >> asm "store" drule_all >> simp[]
QED

Resume runtime_sym_compile_assign_value[storage]:
  simp[NoAsms, compile_assign_value_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> rpt strip_tac >>
  asm "alloc" assume_tac >> asm "typed" assume_tac >>
  dxrule_all runtime_sym_assign_normalize >> strip_tac >>
  Cases_on `prim` >> gvs[]
  >- (drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >> simp[]) >>
  Cases_on `da` >> gvs[]
  >- (Cases_on `(if is_bytestring_type dstTy then type_memory_bytes ce srcTy else sz) <= 32` >>
      gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> gvs[])
      >- (drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
          simp[] >> strip_tac >>
          drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >> simp[]) >>
      asm "storage" drule_all >> simp[]) >>
  PairCases_on `x` >> gvs[] >> asm "dyn" drule_all >> simp[]
QED

Resume runtime_sym_compile_assign_value[transient]:
  simp[NoAsms, compile_assign_value_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> rpt strip_tac >>
  asm "alloc" assume_tac >> asm "typed" assume_tac >>
  dxrule_all runtime_sym_assign_normalize >> strip_tac >>
  Cases_on `prim` >> gvs[]
  >- (drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >> simp[]) >>
  Cases_on `da` >> gvs[]
  >- (Cases_on `(if is_bytestring_type dstTy then type_memory_bytes ce srcTy else sz) <= 32` >>
      gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> gvs[])
      >- (drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
          simp[] >> strip_tac >>
          drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >> simp[]) >>
      asm "transient" drule_all >> simp[]) >>
  PairCases_on `x` >> gvs[] >> asm "dyn" drule_all >> simp[]
QED

Resume runtime_sym_compile_assign_value[code]:
  simp[NoAsms, compile_assign_value_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> rpt strip_tac >>
  asm "alloc" assume_tac >> asm "typed" assume_tac >>
  dxrule_all runtime_sym_assign_normalize >> strip_tac >>
  Cases_on `prim` >> gvs[]
  >- (asm "imm" drule_all >> simp[]) >>
  Cases_on `is_bytestring_type dstTy` >> gvs[]
  >- (asm "bytes" drule_all >> simp[]) >>
  Cases_on `sz <= 32` >> gvs[comp_bind_def]
  >- (pairarg_tac >> gvs[] >>
      drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
      simp[] >> strip_tac >> asm "imm" drule_all >> simp[]) >>
  asm "words" drule_all >> simp[]
QED

Resume runtime_sym_compile_assign_value[calldata]:
  simp[NoAsms, compile_assign_value_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> pairarg_tac >> simp[] >> rpt strip_tac >> gvs[] >>
  drule_at (Pat `emit_inst _ _ _ _ = _`) runtime_sym_emit_inst >>
  simp[runtime_sym_inst_def, mk_inst_def]
QED

Finalise runtime_sym_compile_assign_value
