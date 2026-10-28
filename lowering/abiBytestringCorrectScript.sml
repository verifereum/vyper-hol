(* TOP-LEVEL: actual bytestring ABI compilation writes the specified ABI
   bytes and returns their size. The same result holds inside its containing
   function, including when loop iterations reuse generated SSA outputs.
   Helpers state the memory layout, word bounds and preliminary-store frame. *)
Theory abiBytestringCorrect
Ancestors
  abiBytestringProps abiBytestringMemory abiBytestringExec abiBytestringCode
  memoryReadProps valueEncoding valueEncodingProps vyperValue vyperAST
  fragBlockPath fragExec abiEncoder compileEnv exprLoweringProps
  venomState venomExecSemantics venomInst contractABI list words arithmetic

Definition bytestring_abi_pre_def:
  bytestring_abi_pre (dst_addr:bytes32) (src_addr:bytes32) bs ss <=>
    mload (w2n src_addr) ss = n2w (LENGTH bs) /\
    read_memory (w2n src_addr + 32) (LENGTH bs) ss = bs /\
    32 + ceil32 (LENGTH bs) < dimword(:256) /\
    w2n dst_addr + ceil32 (LENGTH bs) < dimword(:256) /\
    (w2n src_addr + 32 + LENGTH bs <= w2n dst_addr + ceil32 (LENGTH bs) \/
     w2n dst_addr + ceil32 (LENGTH bs) + 32 <= w2n src_addr)
End

Theorem bytestring_abi_pre_bytes:
  !dst_addr src_addr bs ss source_cap.
    val_in_memory (BaseTV (BytesT (Dynamic source_cap))) (vyperValue$BytesV bs)
      (w2n src_addr) ss.vs_memory /\
    32 + ceil32 (LENGTH bs) < dimword(:256) /\
    w2n dst_addr + ceil32 (LENGTH bs) < dimword(:256) /\
    (w2n src_addr + 32 + LENGTH bs <= w2n dst_addr + ceil32 (LENGTH bs) \/
     w2n dst_addr + ceil32 (LENGTH bs) + 32 <= w2n src_addr) ==>
    bytestring_abi_pre dst_addr src_addr bs ss
Proof
  simp[bytestring_abi_pre_def, val_in_memory_def,
    read_memory_eq_mem_bytes_at, GSYM mem_word_at_eq_mload]
QED

Theorem bytestring_abi_pre_string:
  !dst_addr src_addr text ss source_cap.
    val_in_memory (BaseTV (StringT source_cap)) (StringV text)
      (w2n src_addr) ss.vs_memory /\
    32 + ceil32 (LENGTH text) < dimword(:256) /\
    w2n dst_addr + ceil32 (LENGTH text) < dimword(:256) /\
    (w2n src_addr + 32 + LENGTH text <= w2n dst_addr + ceil32 (LENGTH text) \/
     w2n dst_addr + ceil32 (LENGTH text) + 32 <= w2n src_addr) ==>
    bytestring_abi_pre dst_addr src_addr (MAP (n2w o ORD) text) ss
Proof
  simp[bytestring_abi_pre_def, val_in_memory_def, LET_THM,
    read_memory_eq_mem_bytes_at, GSYM mem_word_at_eq_mload]
QED

Theorem bytestring_abi_string_encoding:
  !bs. enc String (contractABI$BytesV bs) = enc (Bytes NONE) (contractABI$BytesV bs)
Proof
  simp[enc_def, LET_THM]
QED

Theorem bytestring_execution_encoding:
  !dst_addr src_addr bs ss out op.
    bytestring_abi_pre dst_addr src_addr bs ss /\
    out.vs_memory = (bytestring_copy_state dst_addr src_addr ss).vs_memory /\
    eval_operand op out =
      SOME (32w + bytestring_round_word (mload (w2n src_addr) ss)) ==>
    eval_operand op out =
      SOME (n2w (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)))) /\
    read_memory (w2n dst_addr) (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs))) out =
      enc (Bytes NONE) (contractABI$BytesV bs) /\
    (!offset read_len.
      offset + read_len <= w2n dst_addr \/
      w2n dst_addr + ceil32 (LENGTH bs) + 32 <= offset ==>
      read_memory offset read_len out = read_memory offset read_len ss)
Proof
  rpt gen_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  qpat_x_assum `bytestring_abi_pre _ _ _ _` mp_tac >>
  PURE_REWRITE_TAC[bytestring_abi_pre_def] >>
  disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  `eval_operand op out =
    SOME (n2w (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs))))` by
    (drule_all bytestring_encoded_size_word >> simp[]) >>
  `read_memory (w2n dst_addr) (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs))) out =
    enc (Bytes NONE) (contractABI$BytesV bs)` by
    (drule_all bytestring_copy_state_encoded >>
     simp[bytestring_encoded_size, read_memory_def]) >>
  simp[] >> rpt gen_tac >> DISCH_TAC >>
  `read_memory offset read_len out =
    read_memory offset read_len (bytestring_copy_state dst_addr src_addr ss)` by
    simp[read_memory_def] >> pop_assum SUBST1_TAC >>
  mp_tac (Q.SPECL [`offset`, `read_len`, `dst_addr`, `src_addr`, `ss`,
    `LENGTH (bs:word8 list)`] bytestring_copy_state_frame) >> simp[]
QED

Theorem compile_abi_bytestring_correct:
  !dst src cap cs op cs' ss dst_addr src_addr bs.
    compile_abi_encode_to_buf dst src (AbiBytestring cap) cs = (op,cs') /\
    EVERY (\name. src <> Var name /\ dst <> Var name)
      (compiler_var_names cs.cs_next_var 8) /\
    eval_operand src ss = SOME src_addr /\ eval_operand dst ss = SOME dst_addr /\
    bytestring_abi_pre dst_addr src_addr bs ss ==>
    ?out.
      run_inst_seq (emitted_insts cs cs') ss = OK out /\
      eval_operand op out =
        SOME (n2w (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)))) /\
      read_memory (w2n dst_addr) (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs))) out =
        enc (Bytes NONE) (contractABI$BytesV bs) /\
      out with vs_vars := ss.vs_vars = bytestring_copy_state dst_addr src_addr ss /\
      LENGTH ss.vs_memory <= LENGTH out.vs_memory /\
      (fresh_vars_wrt cs' out <=> fresh_vars_wrt cs' ss) /\
      same_blocks cs cs' /\
      cs'.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs cs' /\
      (!arg_op. EVERY (\name. arg_op <> Var name)
        (compiler_var_names cs.cs_next_var 8) ==>
        eval_operand arg_op out = eval_operand arg_op ss) /\
      (!offset read_len.
        offset + read_len <= w2n dst_addr \/
        w2n dst_addr + ceil32 (LENGTH bs) + 32 <= offset ==>
        read_memory offset read_len out = read_memory offset read_len ss)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_abi_bytestring_execution >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs cs') ss = OK out` >>
  `out.vs_memory = (bytestring_copy_state dst_addr src_addr ss).vs_memory` by
    (qpat_x_assum `out with vs_vars := _ = _`
       (mp_tac o AP_TERM ``\s:venom_state. s.vs_memory``) >> simp[]) >>
  drule_all bytestring_execution_encoding >> strip_tac >>
  `LENGTH ss.vs_memory <= LENGTH out.vs_memory` by
    (mp_tac (Q.SPECL [`dst_addr`, `src_addr`, `ss`]
       bytestring_copy_state_memory_length) >> simp[]) >>
  drule_all compile_abi_bytestring_fresh >> DISCH_TAC >>
  qexists_tac `out` >> simp[] >> rpt gen_tac >> DISCH_TAC >>
  first_x_assum irule >> decide_tac
QED

Theorem compile_abi_bytestring_correct_path:
  !ctx func dst src cap cs op cs' ss dst_addr src_addr bs.
    compile_abi_encode_to_buf dst src (AbiBytestring cap) cs = (op,cs') /\
    EVERY (\name. src <> Var name /\ dst <> Var name)
      (compiler_var_names cs.cs_next_var 8) /\
    eval_operand src ss = SOME src_addr /\ eval_operand dst ss = SOME dst_addr /\
    bytestring_abi_pre dst_addr src_addr bs ss /\ fn_has_code cs cs' func /\
    ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\
      out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      eval_operand op out =
        SOME (n2w (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)))) /\
      read_memory (w2n dst_addr) (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs))) out =
        enc (Bytes NONE) (contractABI$BytesV bs) /\
      out with vs_vars := ss.vs_vars =
        (bytestring_copy_state dst_addr src_addr ss)
          with vs_inst_idx := LENGTH cs'.cs_current_insts /\
      LENGTH ss.vs_memory <= LENGTH out.vs_memory /\
      (fresh_vars_wrt cs' out <=> fresh_vars_wrt cs' ss) /\
      (!arg_op. EVERY (\name. arg_op <> Var name)
        (compiler_var_names cs.cs_next_var 8) ==>
        eval_operand arg_op out = eval_operand arg_op ss) /\
      (!offset read_len.
        offset + read_len <= w2n dst_addr \/
        w2n dst_addr + ceil32 (LENGTH bs) + 32 <= offset ==>
        read_memory offset read_len out = read_memory offset read_len ss)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all_then (qspec_then `ctx` strip_assume_tac) compile_abi_bytestring_path >>
  rename1 `fragment_path ctx func ss out` >>
  `out.vs_memory = (bytestring_copy_state dst_addr src_addr ss).vs_memory` by
    (qpat_x_assum `out with vs_vars := _ = _`
       (mp_tac o AP_TERM ``\s:venom_state. s.vs_memory``) >> simp[]) >>
  drule_all bytestring_execution_encoding >> strip_tac >>
  `LENGTH ss.vs_memory <= LENGTH out.vs_memory` by
    (mp_tac (Q.SPECL [`dst_addr`, `src_addr`, `ss`]
       bytestring_copy_state_memory_length) >> simp[]) >>
  drule_all compile_abi_bytestring_fresh >> DISCH_TAC >>
  qexists_tac `out` >> simp[] >> rpt gen_tac >> DISCH_TAC >>
  first_x_assum irule >> decide_tac
QED

Theorem compile_abi_bytestring_frag:
  !ctx dst src cap cs op cs' dst_addr src_addr bs R.
    compile_abi_encode_to_buf dst src (AbiBytestring cap) cs = (op,cs') /\
    EVERY (\name. src <> Var name /\ dst <> Var name)
      (compiler_var_names cs.cs_next_var 8) ==>
    frag_exec ctx cs cs'
      (\ss. eval_operand src ss = SOME src_addr /\
        eval_operand dst ss = SOME dst_addr /\
        bytestring_abi_pre dst_addr src_addr bs ss /\ fresh_vars_wrt cs' ss)
      (\out. eval_operand op out =
          SOME (n2w (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)))) /\
        read_memory (w2n dst_addr) (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs))) out =
          enc (Bytes NONE) (contractABI$BytesV bs) /\
        eval_operand dst out = SOME dst_addr /\ fresh_vars_wrt cs' out)
      R
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\name. dst <> Var name) (compiler_var_names cs.cs_next_var 8)` by
    fs[EVERY_CONJ] >>
  irule frag_exec_fragment_path >> MAP_EVERY qx_gen_tac [`func`, `ss`] >>
  simp_tac bool_ss [] >> strip_tac >>
  drule_all_then (qspec_then `ctx` strip_assume_tac)
    compile_abi_bytestring_correct_path >>
  rename1 `fragment_path ctx func ss out` >>
  `eval_operand dst out = SOME dst_addr` by
    (qpat_x_assum `!arg_op. _` (qspec_then `dst` mp_tac) >> simp[]) >>
  qexists_tac `out` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed ABI bytestring correctness theorem: " ^ name)
  end)
  (DB.thms "abiBytestringCorrect")
