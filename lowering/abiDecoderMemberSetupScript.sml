(* Execute the source and destination setup shared by complex members.
   TOP-LEVEL: abi_decode_member_setup_reentry, abi_decode_complex_member_phases.
   Helpers: setup definition and its counter/operand facts. *)
Theory abiDecoderMemberSetup
Ancestors
  abiDecoderReentryMember abiDecoderReentryAddress abiDecoderDynamicLoopSetup
  abiDecoderReentry abiDecoderGuards abiDecoderContract abiDecoderDynamic
  abiEncoder emitHelperProps exprLoweringProps compileEnv emitHelper
  venomExecSemantics venomState venomInst words list rich_list arithmetic

Definition abi_decode_member_setup_def:
  abi_decode_member_setup dst src opc hi dyn ao vo =
    do child_src <- compile_getelemptr_abi src dyn ao opc hi;
       child_dst <- emit_op ADD [dst; Lit (n2w vo)];
       return (child_src,child_dst)
    od
End

Theorem abi_decode_complex_member_phases:
  compile_abi_decode_complex_elems dst src opc hi ((di,asz,msz)::rest) ao vo =
    do ops <- abi_decode_member_setup dst src opc hi (dec_info_needs_offset di) ao vo;
       compile_abi_decode_to_buf (SND ops) (FST ops) opc hi di;
       compile_abi_decode_complex_elems dst src opc hi rest (ao + asz) (vo + msz)
    od
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [compile_abi_decode_to_buf_def])) >>
  Cases_on `di` >>
  simp[FUN_EQ_THM, abi_decode_member_setup_def, dec_info_needs_offset_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_decode_member_setup_counters:
  abi_decode_member_setup dst src opc hi dyn ao vo st = (ops,st') ==>
  st'.cs_next_var = st.cs_next_var + (if dyn then if hi = Lit 0w then 4 else 6 else 2) /\
  abi_decoder_operand_live st'.cs_next_var (FST ops) /\
  abi_decoder_operand_live st'.cs_next_var (SND ops)
Proof
  simp[abi_decode_member_setup_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `compile_getelemptr_abi src dyn ao opc hi st = (child_src,middle)` >>
  rename1 `emit_op ADD [dst; Lit (n2w vo)] middle = (child_dst,st')` >>
  imp_res_tac abi_decoder_member_pointer_counters >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac abi_decoder_operand_live_emit >>
  `middle.cs_next_var <= st'.cs_next_var` by simp[] >>
  conj_tac >- (Cases_on `dyn` >> Cases_on `hi = Lit 0w` >> gvs[]) >>
  metis_tac[abi_decoder_operand_live_mono]
QED

Theorem abi_decode_member_setup_reentry:
  abi_decode_member_setup dst src opc hi dyn ao vo st = (ops,st') /\
  abi_decode_source_opcode opc /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  (dyn ==> abi_decode_load opc (n2w (sb + ao) : bytes32) s = n2w payload_off /\
    sb + payload_off < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand (FST ops) t = SOME (n2w (sb + if dyn then payload_off else ao)) /\
    eval_operand (SND ops) t = SOME (n2w (d + vo)) /\
    abi_decoder_operand_live st'.cs_next_var (FST ops) /\
    abi_decoder_operand_live st'.cs_next_var (SND ops) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
    inst_extends st st'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decode_member_setup_counters >> strip_tac >>
  qpat_x_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_member_setup_def, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `compile_getelemptr_abi src dyn ao opc hi st = (child_src,middle)` >>
  rename1 `emit_op ADD [dst; Lit (n2w vo)] middle = (child_dst,st')` >>
  drule abi_decoder_member_pointer_counters >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `st.cs_next_var <= middle.cs_next_var /\ middle.cs_next_var <= limit_st.cs_next_var`
    by (Cases_on `dyn` >> Cases_on `hi = Lit 0w` >> gvs[]) >>
  mp_tac (Q.INST [`off` |-> `ao:num`, `st'` |-> `middle`,
    `member_op` |-> `child_src`, `initial` |-> `s:venom_state`]
    abi_decoder_member_pointer_reentry) >>
  impl_tac >- asm_simp_tac bool_ss [ADD_COMM] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st middle) s = OK prepared` >>
  `eval_operand dst prepared = SOME (n2w d)` by metis_tac[] >>
  `eval_operand (Lit (n2w vo)) prepared = SOME (n2w vo)` by simp[eval_operand_def] >>
  mp_tac (SIMP_RULE bool_ss [] (Q.INST [`opc` |-> `ADD`, `st` |-> `middle`,
    `s` |-> `prepared:venom_state`, `lhs` |-> `dst`, `rhs` |-> `Lit (n2w vo)`,
    `out` |-> `child_dst`, `a` |-> `n2w d:bytes32`, `b` |-> `n2w vo:bytes32`]
    abi_decoder_binary_reentry)) >>
  impl_tac >- (Cases_on `dyn` >> Cases_on `hi = Lit 0w` >> gvs[]) >>
  strip_tac >> rename1 `run_inst_seq (emitted_insts middle st') prepared = OK t` >>
  `eval_operand child_src t = SOME (n2w (sb + if dyn then payload_off else ao))` by metis_tac[] >>
  `abi_decoder_address_frame st.cs_next_var s prepared /\
   abi_decoder_address_frame middle.cs_next_var prepared t` by
    (simp[abi_decoder_address_frame_def] >> metis_tac[]) >>
  `abi_decoder_address_frame st.cs_next_var s t` by
    (irule abi_decoder_address_frame_trans >> qexistsl_tac [`middle.cs_next_var`, `prepared`] >> simp[]) >>
  `run_inst_seq (emitted_insts st st') s = OK t /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`prepared`, `middle`] >> simp[]) >>
  qexists_tac `t` >> gvs[word_add_n2w]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_MEMBER_SETUP_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI member setup not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderMemberSetup");
