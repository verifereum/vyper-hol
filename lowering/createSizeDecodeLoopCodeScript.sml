(* Branch confinement for the ABI decoder's dynamic-array loop. *)
Theory createSizeDecodeLoopCode
Ancestors
  createSizeSarrayCopyCode createSizeCutCode abiDecoderLoopSetup abiDecoderIndexedAddress
  abiEncoder emitHelper compileEnv pair list

fun decode_loop_steps ths =
  rpt (FIRST [CHANGED_TAC (simp ths),
              irule create_cut_code_bind, irule create_cut_code_ignore_bind,
              irule create_cut_code_emit_op, irule create_cut_code_emit_void,
              CHANGED_TAC (simp[create_cut_targets_def]),
              conj_tac, IF_CASES_TAC]);

Theorem create_decode_loop_addr:
  create_cut_code {} a (SND (compile_abi_dec_addr base_op src a))
Proof
  decode_loop_steps [compile_abi_dec_addr_def]
QED

Theorem create_decode_loop_range:
  create_cut_code {} a (SND (compile_abi_decode_range_check start_op end_op hi a))
Proof
  decode_loop_steps [compile_abi_decode_range_check_def]
QED

Theorem create_decode_loop_ptr[local]:
  (!ops. create_cut_targets load_opc ops = []) ==>
  create_cut_code {} a (SND (compile_abi_decode_dyn_elem_ptr load_opc
                          base_op elem_src src_data hi asz a))
Proof
  strip_tac >> decode_loop_steps [compile_abi_decode_dyn_elem_ptr_def,
                                 create_decode_loop_addr, create_decode_loop_range]
QED

Theorem create_decode_loop_setup[local]:
  (!ops. create_cut_targets load_opc ops = []) ==>
  create_cut_code {} a (SND (abi_decode_array_element_setup ip src dst
                              load_opc base_op hi ei asz msz a))
Proof
  strip_tac >> decode_loop_steps [abi_decode_array_element_setup_def,
                                 abi_decode_indexed_address_def, create_decode_loop_ptr]
QED

Theorem create_decode_dyn_loop_case:
  (!ops. create_cut_targets load_opc ops = []) /\
  (!d s a. create_cut_code {} a
     (SND (compile_abi_decode_to_buf d s load_opc base_op hi ei a))) ==>
  !a. create_cut_code {} a
    (SND (compile_abi_decode_dyn_loop dst src load_opc base_op hi ei asz msz ip cnt a))
Proof
  strip_tac >>
  qabbrev_tac `test = do idx <- emit_op MLOAD [ip];
                        addr <- compile_abi_dec_addr base_op src;
                        count <- emit_op load_opc [addr];
                        cmp <- emit_op LT [idx; count];
                        emit_op ISZERO [cmp]
                     od` >>
  qabbrev_tac `loop_body =
    do ops <- abi_decode_array_element_setup ip src dst load_opc base_op hi ei asz msz;
       compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) load_opc base_op hi ei;
       new_idx <- emit_op ADD [FST ops; Lit 1w];
       emit_void MSTORE [ip; new_idx]
    od` >>
  `!a. create_cut_code {} a (SND (test a))` by
    (gen_tac >> decode_loop_steps [Abbr `test`] >> irule create_decode_loop_addr) >>
  `!a. create_cut_code {} a (SND (loop_body a))` by
    (gen_tac >> decode_loop_steps [Abbr `loop_body`] >>
     irule create_decode_loop_setup >> simp[]) >>
  `compile_abi_decode_dyn_loop dst src load_opc base_op hi ei asz msz ip cnt =
    do h <- fresh_label "dec_dyn_hdr";
       b <- fresh_label "dec_dyn_body";
       x <- fresh_label "dec_dyn_exit";
       emit_inst JMP [Label h] [];
       new_block h;
       cond <- test;
       emit_inst JNZ [cond; Label x; Label b] [];
       new_block b;
       loop_body;
       emit_inst JMP [Label h] [];
       _ <- new_block x;
       return ()
    od` by
    simp[abi_decode_dyn_loop_setup, Abbr `test`, Abbr `loop_body`,
         comp_bind_assoc, comp_ignore_bind_def] >>
  simp[] >> gen_tac >> ntac 3 (irule create_cut_code_bind >> simp[]) >>
  irule create_sarray_loop >> simp[]
QED
