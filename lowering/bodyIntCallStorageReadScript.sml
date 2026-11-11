(* Actual allocation-site credit for arbitrary storage/transient reads. *)
Theory bodyIntCallStorageRead
Ancestors
  bodyIntCallConsumerProbe exprSimStorageCopy exprLowering loweringHalt fragExec
  compileEnv emitHelper venomInst words list
Libs
  monadsyntax

Theorem storage_unwrap_site_reserve:
  unwrap_value ce (LocatedValue ty p) sa = (op,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  ~is_word_type ty /\ fn_has_code sa sb func /\
  type_memory_bytes ce ty < dimword (:256) /\
  sa.cs_next_id NOTIN FDOM s.vs_allocas /\
  alloca_room ctx func s /\ fn_directly_calls ctx func.fn_name name /\
  MEM func ctx.ctx_functions /\ margin <= type_memory_bytes ce ty ==>
  ?buf mid.
    compile_alloc_buffer (type_memory_bytes ce ty) sa = (buf,mid) /\
    op = buf.buf_operand /\
    (if (type_memory_bytes ce ty + 31) DIV 32 = 1 then
       do v <- emit_op (if p.ptr_location = LocStorage then SLOAD else TLOAD)
                 [p.ptr_operand];
          emit_void MSTORE [buf.buf_operand; v] od
     else do compile_word_copy_loop p.ptr_operand buf.buf_operand
               ((type_memory_bytes ce ty + 31) DIV 32)
               p.ptr_location LocMemory F;
             return () od) mid = ((),sb) /\
    fn_has_code sa mid func /\ fn_has_code mid sb func /\
    cs_extends sa mid /\ cs_extends mid sb /\
    s.vs_alloca_next + type_memory_bytes ce ty + margin < dimword (:256)
Proof
  strip_tac >>
  `unwrap_value ce (LocatedValue ty p) =
   compile_ensure_in_memory p.ptr_operand p.ptr_location
     (type_memory_bytes ce ty) ((type_memory_bytes ce ty + 31) DIV 32)
     ce.ce_is_ctor ce.ce_imm_alloca` by
    (Cases_on `p.ptr_location` >> gvs[unwrap_value_def]) >>
  gvs[ensure_storage_memory_layout, comp_bind_def,
      comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_alloc_buffer (type_memory_bytes ce ty) sa` >>
  rename1 `compile_alloc_buffer (type_memory_bytes ce ty) sa = (buf,mid)` >>
  gvs[] >> pairarg_tac >> gvs[] >> rename1 `fn_has_code sa sb func` >>
  `cs_extends sa mid` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends mid sb` by
    (irule storage_copy_suffix_extends >>
     qexistsl_tac [`buf.buf_operand`, `p.ptr_location`,
       `(type_memory_bytes ce ty + 31) DIV 32`, `p.ptr_operand`] >>
     gvs[comp_ignore_bind_def, comp_bind_def]) >>
  `fn_has_code sa mid func /\ fn_has_code mid sb func` by
    metis_tac[fn_has_code_split] >>
  drule_all alloc_buffer_own_site_reserve >> simp[]
QED
