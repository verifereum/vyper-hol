(* TOP-LEVEL: the two actual field-address actions preserve the root
   operands and produce both child pointers, including zero offsets. *)
Theory typedFieldsAddress
Ancestors
  typedCopyStateFrame typedCopyOffset typedCopyOperandFrames typedSArrayDynInvariant abiBytestringCode abiStaticLoopCode
  compileEnv fragExec fragBlockPath venomState venomInst list words arithmetic

Theorem typed_copy_field_addresses_path:
  !ctx func dst src dst_off src_off cs dst_ptr after_dst src_ptr after_src ss dst_addr src_addr.
    compile_with_byte_offset dst dst_off cs = (dst_ptr,after_dst) /\
    compile_with_byte_offset src src_off after_dst = (src_ptr,after_src) /\
    fn_has_code cs after_dst func /\ fn_has_code after_dst after_src func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    EVERY (\name. dst <> Var name /\ src <> Var name)
      (compiler_var_names cs.cs_next_var (after_src.cs_next_var - cs.cs_next_var)) ==>
    ?out. fragment_path ctx func ss out /\ out.vs_current_bb = after_src.cs_current_bb /\
      out.vs_inst_idx = LENGTH after_src.cs_current_insts /\ out.vs_halted = ss.vs_halted /\
      out.vs_memory = ss.vs_memory /\ copy_state_frame ss out /\
      eval_operand dst_ptr out = SOME (dst_addr + n2w dst_off) /\
      eval_operand src_ptr out = SOME (src_addr + n2w src_off) /\
      (!arg_op. EVERY (\name. arg_op <> Var name)
        (compiler_var_names cs.cs_next_var (after_src.cs_next_var - cs.cs_next_var)) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> strip_tac >>
  `cs.cs_next_var <= after_dst.cs_next_var` by (first_assum (ACCEPT_TAC o MATCH_MP compile_with_byte_offset_next_var)) >>
  `after_dst.cs_next_var <= after_src.cs_next_var` by (first_assum (ACCEPT_TAC o MATCH_MP compile_with_byte_offset_next_var)) >>
  qpat_assum `EVERY _ (compiler_var_names cs.cs_next_var _)` (strip_assume_tac o SIMP_RULE bool_ss [EVERY_CONJ]) >>
  `EVERY (\name. src <> Var name) (compiler_var_names cs.cs_next_var (after_dst.cs_next_var - cs.cs_next_var))` by
    (mp_tac (Q.SPECL [`src`, `cs.cs_next_var`, `cs.cs_next_var`, `after_dst.cs_next_var`, `after_src.cs_next_var`]
       compiler_operand_avoid_interval) >> impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, decide_tac]) >> simp[]) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `dst_off`, `cs`, `dst_ptr`, `after_dst`, `ss`, `dst_addr`]
    compile_with_byte_offset_path) >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `dst_ss` strip_assume_tac) >>
  `eval_operand src dst_ss = SOME src_addr` by
    (qpat_x_assum `!arg_op. _ ==> eval_operand _ dst_ss = _` (qspec_then `src` mp_tac) >>
     impl_tac >- first_assum MATCH_ACCEPT_TAC >> simp[]) >>
  `EVERY (\name. dst_ptr <> Var name) (compiler_var_names after_dst.cs_next_var (after_src.cs_next_var - after_dst.cs_next_var))` by
    (mp_tac (Q.SPECL [`dst`, `dst_off`, `cs`, `dst_ptr`, `after_dst`, `after_dst.cs_next_var`, `after_src.cs_next_var`]
       compile_with_byte_offset_result_avoids) >>
     impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, decide_tac]) >> simp[]) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `src`, `src_off`, `after_dst`, `src_ptr`, `after_src`, `dst_ss`, `src_addr`]
    compile_with_byte_offset_path) >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `src_ss` strip_assume_tac) >>
  `eval_operand dst_ptr src_ss = SOME (dst_addr + n2w dst_off)` by
    (qpat_x_assum `!arg_op. _ ==> eval_operand _ src_ss = _` (qspec_then `dst_ptr` mp_tac) >>
     impl_tac >- first_assum MATCH_ACCEPT_TAC >> simp[]) >>
  mp_tac (Q.SPECL [`cs.cs_next_var`, `after_dst.cs_next_var`, `after_src.cs_next_var`, `ss`, `dst_ss`, `src_ss`]
    compiler_operands_frame_intervals) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  `fragment_path ctx func ss src_ss` by
    (irule fragment_path_trans >> qexists_tac `dst_ss` >> simp[]) >>
  `copy_state_frame ss src_ss` by
    (irule copy_state_frame_trans >> qexists_tac `dst_ss` >> simp[]) >>
  qexists_tac `src_ss` >> asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED
