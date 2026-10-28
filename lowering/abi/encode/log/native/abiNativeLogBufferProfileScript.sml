(* TOP-LEVEL: the real Log data and output allocations are outside the
   encoder's new allocation profile. Pure compiler structure and unique
   function instruction IDs establish the exclusions. *)
Theory abiNativeLogBufferProfile
Ancestors
  compileAllocaIdentity compileAllocaProfiles compileAllocaProvenance
  abiLogCode abiEncoderStructure abiBufferAllocationCode sourceBufferFrames logStoreComposition abiStaticLoopCode
  exprLoweringProps emitHelperProps compileEnv fragExec venomInst list rich_list words

Theorem compile_log_abi_emit_extends:
  !dst src info topics cs cs'.
    compile_log_abi_emit dst src info topics cs = ((),cs') ==> cs_extends cs cs'
Proof
  rpt gen_tac >> DISCH_TAC >>
  qpat_x_assum `compile_log_abi_emit _ _ _ _ _ = _`
    (mp_tac o REWRITE_RULE [compile_log_abi_emit_split]) >>
  disch_then (qx_choose_then `size_op` (qx_choose_then `mid` strip_assume_tac)) >>
  `cs_extends cs mid` by (drule_all compile_abi_encode_extends >> simp[]) >>
  `cs_extends mid cs'` by
    (irule cs_extends_same_block >> drule emit_inst_extends >> simp[IS_PREFIX_APPEND]) >>
  irule cs_extends_trans >> qexists_tac `mid` >> simp[]
QED

Theorem compile_log_buffers_outside_encoder_profile:
  !data_capacity cs data_buf store_cut cenv ops tys field_offset ret packed_cut
    capacity abi_buf encode_cut info topics cs' func.
    compile_alloc_buffer data_capacity cs = (data_buf,store_cut) /\ fn_has_code cs store_cut func /\
    compile_log_store_data cenv ops tys data_buf.buf_operand field_offset store_cut = (ret,packed_cut) /\
    compile_alloc_buffer capacity packed_cut = (abi_buf,encode_cut) /\ fn_has_code packed_cut encode_cut func /\
    compile_log_abi_emit abi_buf.buf_operand data_buf.buf_operand info topics encode_cut = ((),cs') /\
    fn_has_code encode_cut cs' func /\ fn_inst_ids_distinct func ==>
    ~MEM cs.cs_next_id (compiler_alloca_ids encode_cut cs') /\
    ~MEM packed_cut.cs_next_id (compiler_alloca_ids encode_cut cs')
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `data_inst = mk_inst cs.cs_next_id ALLOCA [Lit (n2w data_capacity)] [compiler_var_name cs.cs_next_var 0]` >>
  qabbrev_tac `output_inst = mk_inst packed_cut.cs_next_id ALLOCA [Lit (n2w capacity)]
    [compiler_var_name packed_cut.cs_next_var 0]` >>
  `MEM data_inst (fn_insts func)` by
    (qspecl_then [`data_capacity`, `cs`, `data_buf`, `store_cut`, `func`]
       mp_tac compile_buffer_allocation_member >> simp[Abbr`data_inst`]) >>
  `MEM output_inst (fn_insts func)` by
    (qspecl_then [`capacity`, `packed_cut`, `abi_buf`, `encode_cut`, `func`]
       mp_tac compile_buffer_allocation_member >> simp[Abbr`output_inst`]) >>
  qspecl_then [`data_capacity`, `cs`, `data_buf`, `store_cut`] mp_tac compile_alloc_buffer_code >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`capacity`, `packed_cut`, `abi_buf`, `encode_cut`] mp_tac compile_alloc_buffer_code >>
  impl_tac >- simp[] >> strip_tac >>
  `compiler_instruction_member store_cut data_inst /\ compiler_instruction_member encode_cut output_inst` by
    simp[compiler_instruction_member_def, Abbr`data_inst`, Abbr`output_inst`, compiler_var_name_def] >>
  `cs_extends store_cut packed_cut` by (drule_all compile_log_store_data_extends >> simp[]) >>
  `cs_extends packed_cut encode_cut` by
    (irule cs_extends_same_block >> fs[same_blocks_def, IS_PREFIX_APPEND]) >>
  `compiler_instruction_member packed_cut data_inst` by
    (qspecl_then [`store_cut`, `packed_cut`, `data_inst`] mp_tac compiler_instruction_member_extends >> simp[]) >>
  `compiler_instruction_member encode_cut data_inst` by
    (qspecl_then [`packed_cut`, `encode_cut`, `data_inst`] mp_tac compiler_instruction_member_extends >> simp[]) >>
  `cs_extends encode_cut cs'` by (drule_all compile_log_abi_emit_extends >> simp[]) >>
  qspecl_then [`encode_cut`, `cs'`, `func`, `data_inst`] mp_tac compiler_old_instruction_outside_alloca_profile >>
  impl_tac >- simp[] >>
  qspecl_then [`encode_cut`, `cs'`, `func`, `output_inst`] mp_tac compiler_old_instruction_outside_alloca_profile >>
  impl_tac >- simp[] >> simp[Abbr`data_inst`, Abbr`output_inst`, mk_inst_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual Log buffer profile exclusions: " ^ name)
  end) (DB.thms "abiNativeLogBufferProfile")
