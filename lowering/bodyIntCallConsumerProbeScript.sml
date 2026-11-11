(* Consumer probes use actual ALLOCA sites, not interval-id budgets. *)
Theory bodyIntCallConsumerProbe
Ancestors
  bodyIntCallReserveProbe bodyIntCallCapacityProbe bodyIntCallHeldArgs loweringPosts context exprLowering
  compileEnv emitHelper venomInst words list exprSimStorageCopy loweringHalt fragExec
Libs
  monadsyntax

Theorem alloc_buffer_own_site_reserve:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
  n < dimword (:256) /\ sa.cs_next_id NOTIN FDOM s.vs_allocas /\
  alloca_room ctx func s /\ fn_directly_calls ctx func.fn_name name /\
  MEM func ctx.ctx_functions /\ margin <= n ==>
  s.vs_alloca_next + n + margin < dimword (:256)
Proof
  strip_tac >>
  `margin <= unit_alloca_frame ctx` by
    (irule alloc_buffer_site_margin >> metis_tac[]) >>
  drule_all alloc_buffer_call_reserve >> simp[]
QED

(* Equal static element strides suffice, independently of array bounds
   and of equality between the element annotations. *)
Theorem fixed_array_annotation_store:
  acyclic_struct_metadata ce.ce_struct_fields /\
  type_memory_bytes ce de = type_memory_bytes ce se /\
  ~is_abi_dynamic ce.ce_struct_fields de ==>
  compile_store_memory ce src dst (ArrayT de (Fixed n))
    (ArrayT se (Fixed m)) =
  compile_copy_memory dst src (n * type_memory_bytes ce de)
Proof
  strip_tac >>
  simp[compile_store_memory_def, is_word_type_def, is_bytestring_type_def] >>
  Cases_on `de = se /\ n = m`
  >- (gvs[] >> simp[Once type_memory_bytes_def]) >>
  simp[Once compile_store_memory_typed_def,
       is_word_type_def, is_bytestring_type_def] >>
  simp[Once compile_store_memory_typed_def] >> gvs[]
QED

(* Actual storage unwrap followed by the compiler's memory staging branch. *)
Theorem storage_pair_stage_path_probe:
  let sa = <|cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
             cs_current_bb := "entry"; cs_current_insts := [];
             cs_blocks := []; cs_data_sections := []|> in
  let sb = SND (compile_stage_intcall_args ce
    [LocatedValue (ArrayT (BaseT (UintT 256)) (Fixed 2))
      <|ptr_location := LocStorage; ptr_operand := Lit 0w;
        ptr_buf := NONE|>] [F]
    [ArrayT (BaseT (UintT 256)) (Fixed 2)] sa) in
  let code = FLAT (MAP (\bb. bb.bb_instructions) sb.cs_blocks) ++
             sb.cs_current_insts in
    MAP (\i. i.inst_operands)
      (FILTER (\i. i.inst_opcode = ALLOCA) code) =
        [[Lit 64w]; [Lit 64w]] /\
    LENGTH (FILTER (\i. i.inst_opcode = MCOPY) code) = 1
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def,
    fcpLib.INDEX_CONV ``dimindex (:256)``]
QED

Theorem storage_pair_unwrap_allocation:
  unwrap_value ce
    (LocatedValue (ArrayT (BaseT (UintT 256)) (Fixed 2))
      <|ptr_location := LocStorage; ptr_operand := pop;
        ptr_buf := NONE|>) sa = (op,sb) ==>
  ?buf sm. compile_alloc_buffer 64 sa = (buf,sm) /\ cs_extends sm sb
Proof
  simp[unwrap_value_def, is_word_type_def, type_memory_bytes_def,
       compile_ensure_in_memory_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  Cases_on `compile_alloc_buffer 64 sa` >>
  rename1 `compile_alloc_buffer 64 sa = (buf,sm)` >>
  Cases_on `compile_storage_to_memory pop buf.buf_operand 2 sm` >>
  simp[] >> strip_tac >> gvs[] >>
  irule storage_copy_suffix_extends >>
  qexistsl_tac [`buf.buf_operand`, `LocStorage`, `2`, `pop`] >>
  gvs[compile_storage_to_memory_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def]
QED

(* The +64 required by the unwrap comes from its own emitted ALLOCA. *)
Theorem storage_pair_unwrap_site_room:
  unwrap_value ce
    (LocatedValue (ArrayT (BaseT (UintT 256)) (Fixed 2))
      <|ptr_location := LocStorage; ptr_operand := pop;
        ptr_buf := NONE|>) sa = (op,sb) /\
  fn_has_code sa sb func /\ MEM func ctx.ctx_functions /\
  sa.cs_next_id NOTIN FDOM s.vs_allocas /\
  alloca_room ctx func s /\ fn_directly_calls ctx func.fn_name name ==>
  s.vs_alloca_next + 64 + 64 < dimword (:256)
Proof
  strip_tac >> drule storage_pair_unwrap_allocation >> strip_tac >>
  `cs_extends sa sm` by metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
  `fn_has_code sa sm func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  irule alloc_buffer_own_site_reserve >>
  simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  metis_tac[]
QED

(* The held semantics describe the destination type, regardless of the
   StackValue annotation. For static equal strides that is exactly what
   the real compiler store needs; no source-annotation equality is used. *)
Theorem held_fixed_array_store_input:
  intcall_held_args ce cx a sm es s H /\
  MEM (ArrayT de (Fixed n),raw,StackValue (ArrayT se (Fixed m)) src) H /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  type_memory_bytes ce de = type_memory_bytes ce se /\
  ~is_abi_dynamic ce.ce_struct_fields de ==>
  compile_store_memory ce src dst (ArrayT de (Fixed n))
    (ArrayT se (Fixed m)) = compile_copy_memory dst src (n * type_memory_bytes ce de) /\
  ?v. read_result cx raw es = (INL v,es) /\
      expr_val_rel cx (ArrayT de (Fixed n)) v src s
Proof
  strip_tac >> drule_all intcall_held_args_member >> strip_tac >>
  conj_tac >- (irule fixed_array_annotation_store >> simp[]) >>
  gvs[vv_holds_def]
QED
