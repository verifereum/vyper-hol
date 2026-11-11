Theory bodyPtrIntCallStageArgument
Ancestors exprLowering compileEnv context list
  bodyPtrIntCallStagingFrame assignTuplePtrBoundary
  bodyPtrTypeBuiltinsTransport bodyPtrDefs loweringPosts
  exprBopLowering abiBuiltinDispatchCorrect

(* Expose precisely the head segment, without executing the recursive tail.
   Destination and source annotations remain distinct in the typed store. *)
Theorem intcall_stage_memory_cons_decompose:
  compile_stage_intcall_args ce (vv::vals) (F::flags) (ty::tys) sa =
    (ops,sb) <=>
  ?src sm allocation sn su rest.
    unwrap_value ce vv sa = (src,sm) /\
    compile_alloc_buffer (MAX 32 (type_memory_bytes ce ty)) sm =
      (allocation,sn) /\
    (if is_word_type ty then
       emit_void MSTORE [allocation.buf_operand;src]
     else if (case ty of BaseT (BytesT (Dynamic _)) => T
                        | BaseT (StringT _) => T | _ => F) then
       do compile_store_bytestring src allocation.buf_operand;
          return () od
     else compile_store_memory ce src allocation.buf_operand ty (vv_type vv)) sn =
      ((),su) /\
    compile_stage_intcall_args ce vals flags tys su = (rest,sb) /\
    ops = allocation.buf_operand::rest
Proof
  Cases_on `unwrap_value ce vv sa` >>
  rename1 `unwrap_value ce vv sa = (src,sm)` >>
  Cases_on `compile_alloc_buffer (MAX 32 (type_memory_bytes ce ty)) sm` >>
  simp[Once compile_stage_intcall_args_def, comp_ignore_bind_def,
       comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> gvs[] >> metis_tac[]
QED

(* Pending located values keep their physical type and their original
   expression interval.  A staging write only needs to miss their owned
   footprint; padding and address age are irrelevant. *)
Theorem intcall_located_ptr_confined_write:
  vv_at ce cx ty sa sb es raw (LocatedValue ann p) s /\
  ptr_vv_ok cx ty raw (LocatedValue ann p) es G tn s /\
  p.ptr_location = LocMemory /\
  read_result cx raw es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand p.ptr_operand s = SOME w /\
  eval_operand p.ptr_operand q = eval_operand p.ptr_operand s /\
  op_taint un p.ptr_operand = op_taint tn p.ptr_operand /\
  (!x. p.ptr_operand = Var x ==> FLOOKUP H x = FLOOKUP G x) /\
  (!aid a k. aid < sb.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (a,k) ==> regions_disjoint b n a k) /\
  (!name a k. local_region ce es.scopes s name a k ==>
    regions_disjoint b n a k) /\
  (!i. ~(b <= i /\ i < b+n) ==>
    mem_bytes_at i 1 q.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
  (!i. ~(b <= i /\ i < b+n) ==> (i IN un.t_mem <=> i IN tn.t_mem)) ==>
  ptr_vv_ok cx ty raw (LocatedValue ann p) es H un q
Proof
  strip_tac >>
  drule_all intcall_located_footprint_separation >> strip_tac >>
  `ptr_mem_ok cx ty v p.ptr_operand H un q` by
    (irule ptr_mem_ok_exterior_frame >>
     conj_tac >- gvs[] >>
     qexistsl_tac [`G`, `s`, `tn`, `{i | b <= i /\ i < b+n}`] >>
     simp[] >>
     gvs[ptr_vv_ok_def]) >>
  gvs[ptr_vv_ok_def]
QED

(* Dispatch wrappers determine result tags independently of child values. *)
Theorem type_builtin_body_result_tag:
  compile_type_builtin_dispatch_body cfn ce ann ty tb ret args sa = (vv,sb) ==>
  vv_type vv = ann
Proof
  Cases_on `tb` >>
  simp[compile_type_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> simp[]) >>
  rpt IF_CASES_TAC >>
  gvs[as_stack_val_def, as_ptr_val_def, vv_type_def] >>
  rpt (pairarg_tac >> gvs[as_stack_val_def, as_ptr_val_def, vv_type_def]) >>
  rpt strip_tac >>
  gvs[AllCaseEqs(), as_stack_val_pair, vv_type_def] >>
  drule as_ptr_val_result >> strip_tac >> gvs[vv_type_def]
QED

Theorem literal_vv_result_tag:
  compile_literal_vv ann lit sa = (vv,sb) ==> vv_type vv = ann
Proof
  Cases_on `lit` >>
  gvs[AllCaseEqs()] >>
  simp[compile_literal_vv_def, comp_bind_def, comp_return_def] >>
  rpt strip_tac >>
  gvs[AllCaseEqs(), vv_type_def] >>
  rpt (pairarg_tac >> gvs[comp_return_def, vv_type_def])
  >~ [`BoolL b`] >- (Cases_on `b` >> gvs[compile_literal_vv_def, comp_return_def, vv_type_def]) >>
  Cases_on `ann` >> gvs[comp_return_def, vv_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> gvs[comp_return_def, vv_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[comp_bind_def, comp_return_def, vv_type_def] >>
  pairarg_tac >> gvs[vv_type_def]
QED

Theorem builtin_body_result_tag:
  compile_builtin_dispatch_body cfn ce ann ty bi args sa = (vv,sb) ==>
  vv_type vv = ann
Proof
  Cases_on `bi` >>
  simp[compile_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> simp[]) >>
  rpt IF_CASES_TAC >>
  gvs[as_stack_val_pair, vv_type_def] >>
  rpt (pairarg_tac >> gvs[as_stack_val_pair, vv_type_def]) >>
  rpt strip_tac >>
  gvs[AllCaseEqs(), as_stack_val_pair, vv_type_def]
  >>~- ([`as_ptr_val _ _ _ = _`],
    drule as_ptr_val_result >> strip_tac >> gvs[vv_type_def]) >>
  rpt (pairarg_tac >> gvs[vv_type_def]) >>
  drule literal_vv_result_tag >> simp[]
QED

Theorem name_vv_result_tag:
  compile_name_vv ce ann id sa = (vv,sb) ==> vv_type vv = ann
Proof
  Cases_on `FLOOKUP ce.ce_vars id` >>
  simp[compile_name_vv_def, comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[vv_type_def] >>
  rpt (pairarg_tac >> gvs[vv_type_def]) >>
  rename1 `SOME vl` >> Cases_on `vl` >>
  gvs[comp_ignore_bind_def, comp_bind_def, comp_return_def, vv_type_def] >>
  pairarg_tac >> gvs[comp_return_def, vv_type_def]
QED

Theorem attribute_result_tag:
  compile_attribute cfn ce ann ty base_e fld sa = (vv,sb) ==> vv_type vv = ann
Proof
  simp[compile_attribute_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >>
  strip_tac >> gvs[vv_type_def]
QED

Theorem subscript_result_tag:
  compile_subscript cfn ce ann ty base_e idx sa = (vv,sb) ==> vv_type vv = ann
Proof
  simp[compile_subscript_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >>
  strip_tac >> Cases_on `place_type ce base_e` >>
  gvs[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[comp_return_def, vv_type_def]) >>
  rename1 `ValPT vt` >> Cases_on `vt` >>
  gvs[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[comp_return_def, vv_type_def])
QED
