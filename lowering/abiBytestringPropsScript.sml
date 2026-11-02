(* TOP-LEVEL: the actual bytestring ABI compiler executes with the exact
   store-before-copy memory effect, both as a sequence and inside its real
   containing function. Generated output names may already be defined. *)
Theory abiBytestringProps
Ancestors
  abiBytestringCode abiBytestringExec ssaOperandFrame fragBlockPath fragExec
  abiEncoder compileEnv exprLoweringProps emitHelperProps instIdxIndep
  venomState venomExecSemantics venomInst list rich_list finite_map

Theorem compile_abi_bytestring_execution:
  !dst src cap cs op cs' ss dst_addr src_addr.
    compile_abi_encode_to_buf dst src (AbiBytestring cap) cs = (op,cs') /\
    EVERY (\name. src <> Var name /\ dst <> Var name)
      (compiler_var_names cs.cs_next_var 8) /\
    eval_operand src ss = SOME src_addr /\ eval_operand dst ss = SOME dst_addr ==>
    ?out.
      run_inst_seq (emitted_insts cs cs') ss = OK out /\
      eval_operand op out =
        SOME (32w + bytestring_round_word (mload (w2n src_addr) ss)) /\
      out with vs_vars := ss.vs_vars = bytestring_copy_state dst_addr src_addr ss /\
      same_blocks cs cs' /\
      cs'.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs cs' /\
      (!arg_op. EVERY (\name. arg_op <> Var name)
         (compiler_var_names cs.cs_next_var 8) ==>
         eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> strip_tac >> drule compile_abi_bytestring_code >> strip_tac >>
  mp_tac (Q.SPECL [`cs.cs_next_id`, `compiler_var_names cs.cs_next_var 8`,
    `dst`, `src`, `ss`, `dst_addr`, `src_addr`] bytestring_encoder_execution) >>
  simp[compiler_var_names_distinct]
QED

Theorem compile_abi_bytestring_path:
  !ctx func dst src cap cs op cs' ss dst_addr src_addr.
    compile_abi_encode_to_buf dst src (AbiBytestring cap) cs = (op,cs') /\
    EVERY (\name. src <> Var name /\ dst <> Var name)
      (compiler_var_names cs.cs_next_var 8) /\
    eval_operand src ss = SOME src_addr /\ eval_operand dst ss = SOME dst_addr /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\
      out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      eval_operand op out =
        SOME (32w + bytestring_round_word (mload (w2n src_addr) ss)) /\
      out with vs_vars := ss.vs_vars =
        (bytestring_copy_state dst_addr src_addr ss)
          with vs_inst_idx := LENGTH cs'.cs_current_insts /\
      (!arg_op. EVERY (\name. arg_op <> Var name)
         (compiler_var_names cs.cs_next_var 8) ==>
         eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_abi_bytestring_execution >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs cs') ss = OK raw_out` >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts cs cs')` by
    (drule compile_abi_bytestring_code >> simp[bytestring_encoder_straight]) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs`, `cs'`, `ss`, `raw_out`]
    fragment_path_emitted) >> impl_tac >- simp[] >> strip_tac >>
  `((raw_out with vs_inst_idx := LENGTH cs'.cs_current_insts)
      with vs_vars := ss.vs_vars) =
    (bytestring_copy_state dst_addr src_addr ss)
      with vs_inst_idx := LENGTH cs'.cs_current_insts` by
    (qpat_x_assum `raw_out with vs_vars := ss.vs_vars = _`
       (mp_tac o AP_TERM ``\s:venom_state.
         s with vs_inst_idx := LENGTH cs'.cs_current_insts``) >> simp[]) >>
  qexists_tac `raw_out with vs_inst_idx := LENGTH cs'.cs_current_insts` >>
  simp[eval_op_inst_idx]
QED

Theorem compiler_var_names_avoid_operand:
  !cs ss count arg_op word.
    fresh_vars_wrt cs ss /\ eval_operand arg_op ss = SOME word ==>
    EVERY (\name. arg_op <> Var name) (compiler_var_names cs.cs_next_var count)
Proof
  rpt gen_tac >> strip_tac >>
  simp[compiler_var_names_def, EVERY_GENLIST] >> qx_gen_tac `var_index` >> strip_tac >>
  strip_tac >>
  mp_tac (Q.SPECL [`cs`, `ss`, `arg_op`, `word`,
    `STRING #"%" (toString (cs.cs_next_var + var_index))`,
    `cs.cs_next_var + var_index`]
      fresh_vars_wrt_eval_operand) >> simp[]
QED

Theorem fresh_bytestring_input_names:
  !cs ss src dst src_addr dst_addr.
    fresh_vars_wrt cs ss /\ eval_operand src ss = SOME src_addr /\
    eval_operand dst ss = SOME dst_addr ==>
    EVERY (\name. src <> Var name /\ dst <> Var name)
      (compiler_var_names cs.cs_next_var 8)
Proof
  rpt gen_tac >> strip_tac >> simp[EVERY_CONJ] >> conj_tac >>
  irule compiler_var_names_avoid_operand >> goal_assum drule >> simp[]
QED

Theorem fresh_vars_wrt_operand_frame:
  !cs base num_names ss out.
    base + num_names <= cs.cs_next_var /\
    (!arg_op. EVERY (\name. arg_op <> Var name)
      (compiler_var_names base num_names) ==>
      eval_operand arg_op out = eval_operand arg_op ss) ==>
    (fresh_vars_wrt cs out <=> fresh_vars_wrt cs ss)
Proof
  rpt gen_tac >> strip_tac >>
  `!n. n >= cs.cs_next_var ==>
    eval_operand (Var (STRING #"%" (toString n))) out =
    eval_operand (Var (STRING #"%" (toString n))) ss` by
    (rpt gen_tac >> strip_tac >> first_x_assum irule >>
     irule compiler_var_names_later >> decide_tac) >>
  qpat_x_assum `!n. n >= cs.cs_next_var ==> _` mp_tac >>
  simp_tac bool_ss [eval_operand_def, lookup_var_def] >> DISCH_TAC >>
  simp_tac bool_ss [fresh_vars_wrt_def,
    GSYM (CONJUNCT1 (SPEC_ALL flookup_thm))] >>
  asm_simp_tac bool_ss []
QED

Theorem compile_abi_bytestring_fresh:
  !dst src cap cs op cs' ss out.
    compile_abi_encode_to_buf dst src (AbiBytestring cap) cs = (op,cs') /\
    (!arg_op. EVERY (\name. arg_op <> Var name)
      (compiler_var_names cs.cs_next_var 8) ==>
      eval_operand arg_op out = eval_operand arg_op ss) ==>
    (fresh_vars_wrt cs' out <=> fresh_vars_wrt cs' ss)
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_abi_bytestring_code >> strip_tac >>
  mp_tac (Q.SPECL [`cs'`, `cs.cs_next_var`, `8`, `ss`, `out`]
    fresh_vars_wrt_operand_frame) >> simp[]
QED
