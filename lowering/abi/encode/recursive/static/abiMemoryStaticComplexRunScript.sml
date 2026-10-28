(* TOP-LEVEL: finish the native all-static aggregate branch from its actual
   field traversal. Its returned size is the physical contiguous byte length;
   no parent allocation, load or counter-cell hypothesis is introduced.
   Helper: exact compiler decomposition, including the empty aggregate. *)
Theory abiMemoryStaticComplexRun
Ancestors
  abiMemoryStaticFieldsState abiMemoryFieldsLayout abiMemoryFieldsState abiMemoryLeafRun
  abiMemoryEncoding abiFieldLayoutDefs abiMemoryFrame abiFieldOperands abiStateFrame
  abiEncoder abiComplexStructure compileEnv context fragExec fragBlockPath
  venomState list pair words arithmetic
Libs pairLib

Theorem compile_abi_complex_static_split:
  !dst src entries cs ret cs'.
    ~EXISTS (\(_,_,_,flag). flag) entries ==>
    (compile_abi_encode_to_buf dst src (AbiComplex entries) cs = (ret,cs') <=>
      ret = Lit (n2w (SUM (MAP (\(_,head_size,_,_). head_size) entries))) /\
      ?traversal_ret. compile_abi_encode_complex_elems dst src entries 0 0 (Lit 0w) cs = (traversal_ret,cs'))
Proof
  rpt gen_tac >> DISCH_TAC >> Cases_on `entries`
  >- simp[Once compile_abi_encode_child_def, abi_complex_fields_nil, comp_return_def] >>
  rename1 `compile_abi_encode_to_buf dst src (AbiComplex (entry::rest)) cs = _` >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [compile_abi_encode_child_def])) >>
  asm_simp_tac bool_ss [LET_THM, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_abi_encode_complex_elems dst src (entry::rest) 0 0 (Lit 0w) cs` >> simp[EQ_SYM_EQ]
QED

Theorem abi_memory_static_complex_result:
  !ctx func dst src entries cs ret cs' ss out full dst_addr root_addr source_capacity
      source_offset head_offset scratch.
    compile_abi_encode_to_buf dst src (AbiComplex entries) cs = (ret,cs') /\
    ~EXISTS (\(_,_,_,flag). flag) entries /\
    abi_memory_fields entries (w2n root_addr) source_capacity ss.vs_memory full /\
    abi_memory_static_fields_state full dst src dst_addr root_addr source_capacity
      [] source_offset head_offset cs' out /\
    fragment_path ctx func ss out /\
    out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
    abi_memory_frame
      ((w2n dst_addr,LENGTH (abi_field_bytes (abi_field_head_size full) full))::scratch) ss out /\
    (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss) /\
    abi_state_frame ss out ==>
    abi_encoding_result ctx func cs cs' ret dst_addr
      (abi_field_bytes (abi_field_head_size full) full) scratch ss out
Proof
  rpt gen_tac >> strip_tac >>
  `ret = Lit (n2w (SUM (MAP (\(_,head_size,_,_). head_size) entries)))` by
    (qspecl_then [`dst`, `src`, `entries`, `cs`, `ret`, `cs'`]
       mp_tac compile_abi_complex_static_split >>
     impl_tac >- first_assum MATCH_ACCEPT_TAC >>
     asm_simp_tac bool_ss [] >> strip_tac >> first_assum MATCH_ACCEPT_TAC) >>
  drule abi_memory_fields_head_size >> DISCH_TAC >>
  drule abi_memory_static_fields_complete >> strip_tac >>
  `SUM (MAP (\(_,head_size,_,_). head_size) entries) =
    LENGTH (abi_field_bytes (abi_field_head_size full) full)` by decide_tac >>
  `eval_operand ret out = SOME (n2w (LENGTH (abi_field_bytes (abi_field_head_size full) full)))` by
    (qpat_x_assum `ret = _` (fn ret_th =>
       qpat_x_assum `SUM _ = LENGTH _` (fn size_th =>
         simp_tac (srw_ss()) [ret_th, size_th, eval_operand_def]))) >>
  PURE_REWRITE_TAC [abi_encoding_result_def] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed native all-static aggregate completion: " ^ name)
  end) (DB.thms "abiMemoryStaticComplexRun")
