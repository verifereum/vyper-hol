(* Resource containment and control-flow containment are independent. *)
Theory abiMalformedContainmentProbe
Ancestors
  abiMalformedIndexState abiDecoderIndexInit exprSimAlloc
  fragExec compileEnv context emitHelper emitHelperProps exprLowering exprLoweringProps
  venomState venomInst venomMemDefs valueEncoding valueEncodingDefs words list rich_list arithmetic

Theorem abi_malformed_index_resource_code:
  abi_decode_index_init st = (ip,en) /\ fn_has_code st en func ==>
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)
Proof
  strip_tac >> drule abi_decode_index_init_trace >> strip_tac >>
  `cs_extends st allocation_st /\ cs_extends allocation_st en` by
    (conj_tac
     >- (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
         simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
         pairarg_tac >> strip_tac >> gvs[] >>
         qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
         simp[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
              emit_def, comp_ignore_bind_def, comp_return_def] >> strip_tac >> gvs[] >>
         irule cs_extends_same_block >> simp[]) >>
     qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, fresh_id_def, emit_def,
          comp_return_def] >> strip_tac >> gvs[] >>
     irule cs_extends_same_block >> simp[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all buffer_alloc_code >> simp[]
QED

Theorem abi_malformed_index_resource_fragment:
  abi_decode_index_init st = (ip,en) /\ fn_has_code st en func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv st ==>
  frag_exec ctx st en
    (\s. stmt_state_rel ctx func cenv cx es s)
    (\t. stmt_state_rel ctx func cenv cx es t /\
      ?p. eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
          p + 32 < dimword (:256) /\
          FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,32))
    (\r. F)
Proof
  strip_tac >> drule_all abi_malformed_index_resource_code >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >>
  fs[inst_extends_def] >> rpt strip_tac >>
  drule_all abi_malformed_index_state >> strip_tac >>
  qexists_tac `t` >> simp[stmt_state_rel_inst_idx] >>
  fs[eval_operand_def, lookup_var_def, mload_def, mem_bytes_at_def]
QED
