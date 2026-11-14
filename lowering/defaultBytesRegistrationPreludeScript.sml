(* Actual guarded dynamic positional-registration compilation boundary. *)
Theory defaultBytesRegistrationPrelude
Ancestors calldataRegistrationExec moduleLowering compileEnv emitHelper finite_map
  ctorDeployMemoryRunPtrPrefixRegisterAlloc ctorDeployMemoryRunPtrPrefixRegisterAddress
  fragGasOriginPtr ptrSafeRun ptrDiscipline venomState venomExecSemantics venomInst
  codegenRel contextCodegenRel unitTransformDefs words list arithmetic
  exprLoweringProps fragExec context
  ctorDeployLoweringEntryRegisterRun ctorDeployMemoryRunMemEntryRegistration
  abiDecoderReentry freshWrites bodyPtrDefs localPtrsProps allocaFrontierBound

Theorem default_bytes_registration_split:
  compile_register_positional_args ce
    ((name,F,T,sz,DecBytestring maxn)::rest) off st = (cef,final) /\
  FLOOKUP ce.ce_vars name = SOME loc /\
  var_location_memory_size loc = SOME cap ==>
  ?buf allocated ce1 head after_head offset after_load src after_src first decoded.
    compile_alloc_buffer cap st = (buf,allocated) /\
    ce1 = (ce with ce_vars := ce.ce_vars |+ (name,PtrVar buf.buf_operand cap)) /\
    emit_op ADD [Lit (n2w 4); Lit (n2w (off-4))] allocated = (head,after_head) /\
    emit_op CALLDATALOAD [head] after_head = (offset,after_load) /\
    emit_op ADD [Lit (n2w 4);offset] after_load = (src,after_src) /\
    compile_abi_arg_ptr_guard CALLDATALOAD src (Lit 4w) after_src = ((),first) /\
    compile_abi_decode_to_buf buf.buf_operand src CALLDATALOAD (Lit 0w) (Lit 0w)
      (DecBytestring maxn) first = ((),decoded) /\
    compile_register_positional_args ce1 rest (off+sz) decoded = (cef,final)
Proof
  strip_tac >>
  qpat_x_assum `compile_register_positional_args _ _ _ _ = _` mp_tac >>
  simp[Once compile_register_positional_args_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  Cases_on `_0` >>
  `var_location_decode_operand (PtrVar buf.buf_operand cap) =
     SOME buf.buf_operand` by simp[var_location_decode_operand_def] >>
  drule registration_decoder_prelude >>
  simp[FLOOKUP_UPDATE] >>
  disch_then strip_assume_tac >>
  qexistsl_tac [`head`, `after_head`, `offset`, `after_load`, `src`, `after_src`, `first`, `cs''`] >> gvs[] >>
  `ce with ce_vars := ce.ce_vars |+ (name,PtrVar buf.buf_operand cap) =
   ce with ce_vars updated_by (\m. m |+ (name,PtrVar buf.buf_operand cap))` by
    simp[compile_env_component_equality] >>
  pop_assum SUBST1_TAC >> simp[]
QED

(* Capacity-polymorphic allocation origin, without a source-state invariant. *)
Theorem default_bytes_alloc_origin:
  compile_alloc_buffer cap st = (buf,allocated) /\
  fn_has_code st allocated fn /\
  FLOOKUP s.vs_allocas st.cs_next_id = NONE /\ cap < dimword (:256) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  let p = STRING #"%" (toString st.cs_next_var);
      a = (update_var p (n2w s.vs_alloca_next)
        (s with <|vs_allocas := s.vs_allocas |+
          (st.cs_next_id,(s.vs_alloca_next,cap));
          vs_alloca_next := s.vs_alloca_next+cap|>))
        with vs_inst_idx := LENGTH allocated.cs_current_insts;
      H = G |+ (p,(s.vs_alloca_next,cap));
      u = tn with <|t_var := tn.t_var |+ (p,{});
        t_mem := tn.t_mem UNION
          {j | s.vs_alloca_next <= j /\ j < s.vs_alloca_next+cap}|>
  in !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (OK a,H,u)
Proof
  strip_tac >> simp_tac bool_ss [LET_THM] >> rpt gen_tac >>
  `emit_op ALLOCA [Lit (n2w cap)] st = (buf.buf_operand,allocated)` by
    (gvs[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> gvs[]) >>
  irule prefix_register_address_emit_origin >> simp[] >>
  qexistsl_tac [`ALLOCA`,`[Lit (n2w cap)]`,`buf.buf_operand`,`st`] >>
  drule_all prefix_register_alloc_pair >>
  disch_then (qspecl_then [`STRING #"%" (toString st.cs_next_var)`,
    `tn`,`0`,`fn`,`PG`,`G`,`D`] mp_tac) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  simp[run_inst_seq_def, mk_inst_def, is_terminator_def,
    inst_mem_below_frontier_def, source_memory_read_ranges_def,
    source_memory_write_ranges_def]
QED
