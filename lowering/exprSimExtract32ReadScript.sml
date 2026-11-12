(* Read-only straight-line compiler actions, with both freshness bounds. *)
Theory exprSimExtract32Read
Ancestors
  freshWrites fragExec varsExt exprSimProps exprLowering emitHelper emitHelperProps
  exprLoweringProps compileEnv loweringStateRelDefs builtinBytes venomExecSemantics venomInst venomState
  list rich_list finite_map ASCIInumbers valueEncoding valueEncodingDefs
Libs
  monadsyntax

Theorem extract32_step_frame[local]:
  !i s u.
    (fresh_write_op i.inst_opcode \/ i.inst_opcode = MLOAD) /\
    step_inst_base i s = OK u ==>
    u = s with vs_vars := u.vs_vars /\
    !x. ~MEM x i.inst_outputs ==>
      FLOOKUP u.vs_vars x = FLOOKUP s.vs_vars x
Proof
  rpt gen_tac >> strip_tac
  >- (drule_all step_fresh_write_op >> simp[]) >>
  gvs[step_inst_base_opcode_eqs, exec_read1_def, AllCaseEqs()] >>
  gvs[update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
      venom_state_component_equality]
QED

Theorem extract32_run_frame[local]:
  !is sa sb s u.
    EVERY (\i. (fresh_write_op i.inst_opcode \/ i.inst_opcode = MLOAD) /\
      EVERY (\x. ~not_fresh_at sa x /\ not_fresh_at sb x) i.inst_outputs) is /\
    run_inst_seq is s = OK u ==>
    (u with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (fresh_vars_wrt sb s ==> fresh_vars_wrt sb u)
Proof
  Induct
  >- simp[run_inst_seq_def] >>
  rpt gen_tac >> simp[run_inst_seq_def] >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  rename1 `step_inst_base h s = OK mid` >>
  `mid = s with vs_vars := mid.vs_vars /\
   !x. ~MEM x h.inst_outputs ==>
     FLOOKUP mid.vs_vars x = FLOOKUP s.vs_vars x` by
    metis_tac[extract32_step_frame] >>
  first_x_assum (qspecl_then [`sa`, `sb`, `mid`, `u`] mp_tac) >>
  simp[] >> strip_tac >>
  (conj_tac >- fs[venom_state_component_equality]) >>
  (conj_tac
   >- (rpt strip_tac >>
       `~MEM x h.inst_outputs` by (fs[EVERY_MEM] >> metis_tac[]) >>
       fs[lookup_var_def] >> metis_tac[])) >>
  strip_tac >> qpat_x_assum `fresh_vars_wrt sb mid ==> _` irule >>
  fs[fresh_vars_wrt_def] >> rpt strip_tac >>
  `~MEM (STRING #"%" (toString n)) h.inst_outputs` by
    (strip_tac >>
     qpat_x_assum `EVERY _ h.inst_outputs`
       (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `STRING #"%" (toString n)` mp_tac) >>
     simp[not_fresh_at_def] >> disch_then (qspec_then `n` mp_tac) >> simp[]) >>
  qpat_x_assum `!x. ~MEM x h.inst_outputs ==> _` drule >>
  simp[finite_mapTheory.FLOOKUP_DEF] >> metis_tac[]
QED

Definition extract32_straight_read_frame_def:
  extract32_straight_read_frame (m : 'a compiler) <=>
    !sa r sb. m sa = (r,sb) ==>
      sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
      sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
      sa.cs_next_var <= sb.cs_next_var /\
      EVERY (\i. (fresh_write_op i.inst_opcode \/ i.inst_opcode = MLOAD) /\
        EVERY (\x. ~not_fresh_at sa x /\ not_fresh_at sb x) i.inst_outputs)
        (emitted_insts sa sb)
End

Theorem extract32_read_return:
  !r. extract32_straight_read_frame (comp_return r)
Proof
  rw[extract32_straight_read_frame_def, comp_return_def, emitted_insts_refl]
QED

Theorem extract32_read_emit_op:
  !opc ops. (fresh_write_op opc \/ opc = MLOAD) ==>
    extract32_straight_read_frame (emit_op opc ops)
Proof
  rw[extract32_straight_read_frame_def] >>
  imp_res_tac emit_op_extends >> imp_res_tac emitted_insts_emit_op >>
  fs[same_blocks_def, mk_inst_def, not_fresh_at_def] >>
  rpt strip_tac >> fs[ASCIInumbersTheory.toString_inj]
QED

Theorem extract32_read_emit_void:
  !opc ops. (fresh_write_op opc \/ opc = MLOAD) ==>
    extract32_straight_read_frame (emit_void opc ops)
Proof
  rw[extract32_straight_read_frame_def] >>
  imp_res_tac emit_void_extends >> imp_res_tac emitted_insts_emit_void >>
  fs[same_blocks_def, mk_inst_def]
QED

Theorem extract32_read_bind:
  !mm ff. extract32_straight_read_frame mm /\
    (!a. extract32_straight_read_frame (ff a)) ==>
    extract32_straight_read_frame (comp_bind mm ff)
Proof
  rewrite_tac[extract32_straight_read_frame_def, comp_bind_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `mm sa` >> simp[] >> strip_tac >>
  rename1 `mm sa = (a,mid)` >>
  qpat_x_assum `!sa r sb. mm sa = _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!a sa r sb. ff a sa = _ ==> _`
    (drule_then strip_assume_tac) >>
  `emitted_insts sa sb = emitted_insts sa mid ++ emitted_insts mid sb` by
    (irule emitted_insts_append >> simp[]) >>
  simp[] >> fs[EVERY_MEM] >> metis_tac[not_fresh_at_mono]
QED

Theorem extract32_read_ignore_bind:
  !mm ff. extract32_straight_read_frame mm /\
    extract32_straight_read_frame ff ==>
    extract32_straight_read_frame (comp_ignore_bind mm ff)
Proof
  rw[comp_ignore_bind_def] >> irule extract32_read_bind >> simp[]
QED

Theorem extract32_read_mload:
  !ops. extract32_straight_read_frame (emit_op MLOAD ops)
Proof
  simp[extract32_read_emit_op]
QED

Theorem extract32_read_assert:
  !ops. extract32_straight_read_frame (emit_void ASSERT ops)
Proof
  irule extract32_read_emit_void >> simp[fresh_write_op_def]
QED

(* Shared deterministic structural step; no search or fallback. *)
val extract32_read_op_step =
  irule extract32_read_bind >> reverse conj_tac
  >- (irule extract32_read_emit_op >> simp[fresh_write_op_def]) >>
  gen_tac >> BETA_TAC;

Theorem extract32_read_bounds:
  !start len src.
    extract32_straight_read_frame (compile_assert_slice_bounds start len src)
Proof
  rpt gen_tac >> rewrite_tac[builtinBytesTheory.compile_assert_slice_bounds_def] >>
  ntac 5 extract32_read_op_step >>
  irule extract32_read_emit_void >> simp[fresh_write_op_def]
QED

Theorem extract32_read_load:
  !len dp off. extract32_straight_read_frame (compile_extract32_load len dp off)
Proof
  rpt gen_tac >> rewrite_tac[builtinBytesTheory.compile_extract32_load_def] >>
  irule extract32_read_ignore_bind >> conj_tac
  >- simp[extract32_read_bounds] >>
  irule extract32_read_bind >> reverse conj_tac
  >- (irule extract32_read_emit_op >> simp[fresh_write_op_def]) >>
  simp[extract32_read_mload]
QED

Theorem extract32_read_clamp:
  !v ty. extract32_straight_read_frame (compile_clamp v ty)
Proof
  rpt gen_tac >> rewrite_tac[compile_clamp_def] >>
  Cases_on `type_bounds ty` >> simp[] >>
  Cases_on `is_signed_type ty` >> simp[] >>
  rpt extract32_read_op_step >>
  irule extract32_read_emit_void >> simp[fresh_write_op_def]
QED

Theorem extract32_read_clamp_return:
  !v ty. extract32_straight_read_frame (clamp_and_return v ty)
Proof
  simp[clamp_and_return_def, extract32_read_ignore_bind,
       extract32_read_clamp, extract32_read_return]
QED

Theorem extract32_read_clamp_basetype:
  !v ty. extract32_straight_read_frame (compile_clamp_basetype v ty)
Proof
  gen_tac >> Cases_on `ty` >>
  simp[compile_clamp_basetype_def, extract32_read_return] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[compile_clamp_basetype_def, extract32_read_return]
  >- (IF_CASES_TAC >> simp[extract32_read_clamp_return, extract32_read_return])
  >- (IF_CASES_TAC >> simp[extract32_read_clamp_return, extract32_read_return])
  >- (Cases_on `b` >> simp[compile_clamp_basetype_def, extract32_read_return] >>
      IF_CASES_TAC >> simp[extract32_read_return] >>
      ntac 2 extract32_read_op_step >>
      irule extract32_read_ignore_bind >>
      simp[extract32_read_assert, extract32_read_return]) >>
  ntac 2 extract32_read_op_step >>
  irule extract32_read_ignore_bind >>
  simp[extract32_read_assert, extract32_read_return]
QED

Theorem extract32_read_extends:
  !m sa r sb.
    extract32_straight_read_frame m /\ m sa = (r,sb) ==>
    sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    sa.cs_next_var <= sb.cs_next_var
Proof
  simp[extract32_straight_read_frame_def] >> metis_tac[]
QED

Theorem extract32_read_success_frame:
  !m sa r sb s u.
    extract32_straight_read_frame m /\ m sa = (r,sb) /\
    fresh_vars_wrt sa s /\ run_inst_seq (emitted_insts sa sb) s = OK u ==>
    fresh_vars_wrt sb u /\ (u with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `extract32_straight_read_frame _`
    (mp_tac o REWRITE_RULE [extract32_straight_read_frame_def]) >>
  disch_then drule >> strip_tac >>
  `fresh_vars_wrt sb s` by
    (fs[fresh_vars_wrt_def] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  drule_all extract32_run_frame >> simp[]
QED

Theorem extract32_load_success_frame:
  !len dp off sa op sb s u.
    compile_extract32_load len dp off sa = (op,sb) /\
    fresh_vars_wrt sa s /\ run_inst_seq (emitted_insts sa sb) s = OK u ==>
    fresh_vars_wrt sb u /\ (u with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)
Proof
  rpt gen_tac >> strip_tac >>
  irule (INST_TYPE [``:'a`` |-> ``:operand``] extract32_read_success_frame) >> simp[] >>
  qexistsl_tac [`compile_extract32_load len dp off`, `op`] >>
  simp[extract32_read_load]
QED

Theorem extract32_clamp_success_frame:
  !raw ty sa op sb s u.
    compile_clamp_basetype raw ty sa = (op,sb) /\
    fresh_vars_wrt sa s /\ run_inst_seq (emitted_insts sa sb) s = OK u ==>
    fresh_vars_wrt sb u /\ (u with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)
Proof
  rpt gen_tac >> strip_tac >>
  irule (INST_TYPE [``:'a`` |-> ``:operand``] extract32_read_success_frame) >> simp[] >>
  qexistsl_tac [`compile_clamp_basetype raw ty`, `op`] >>
  simp[extract32_read_clamp_basetype]
QED

Theorem extract32_read_prepare:
  !ptr. extract32_straight_read_frame (compile_bytestring_src ptr)
Proof
  gen_tac >> rewrite_tac[builtinBytesTheory.compile_bytestring_src_def] >>
  irule extract32_read_bind >> reverse conj_tac
  >- simp[extract32_read_mload] >> gen_tac >> BETA_TAC >>
  irule extract32_read_bind >> reverse conj_tac
  >- (irule extract32_read_emit_op >> simp[fresh_write_op_def]) >>
  simp[extract32_read_return]
QED

Theorem extract32_prepare_run:
  !src_op sa len dp sb s p l.
  compile_bytestring_src src_op sa = ((len,dp),sb) /\
  eval_operand src_op s = SOME (n2w p) /\ p + 32 < dimword (:256) /\
  mem_word_at p s.vs_memory = n2w l /\ fresh_vars_wrt sa s ==>
  ?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
      eval_operand src_op u = SOME (n2w p) /\
      eval_operand len u = SOME (n2w l) /\
      eval_operand dp u = SOME (n2w (p+32)) /\
      fresh_vars_wrt sb u /\ (u with vs_vars := s.vs_vars) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)
Proof
  rpt gen_tac >> strip_tac >>
  `extract32_straight_read_frame (compile_bytestring_src src_op)` by simp[extract32_read_prepare] >>
  `?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
       eval_operand src_op u = SOME (n2w p) /\
       eval_operand len u = SOME (n2w l) /\
       eval_operand dp u = SOME (n2w (p+32))` by
    (gvs[builtinBytesTheory.compile_bytestring_src_def, comp_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >>
     drule_all emit_op_MLOAD_correct >>
     simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD,
          mload_def, mem_word_at_def, mem_bytes_at_def] >>
     disch_then (qx_choose_then `s1` strip_assume_tac) >>
     `eval_operand src_op s1 = SOME (n2w p)` by metis_tac[] >>
     `eval_operand (Lit 32w) s1 = SOME 32w` by simp[eval_operand_lit] >>
     drule_all emit_op_ADD_correct >>
     disch_then (qx_choose_then `s2` strip_assume_tac) >>
     `eval_operand len s1 = SOME (n2w l)` by gvs[mem_word_at_def, mem_bytes_at_def] >>
     imp_res_tac emit_op_extends >>
     `run_inst_seq (emitted_insts sa cs'') s = OK s2` by
       (drule_all run_inst_seq_chain >> simp[]) >>
     qexists_tac `s2` >> simp[wordsTheory.word_add_n2w] >> metis_tac[]) >>
  drule_all extract32_read_success_frame >> strip_tac >>
  qexists_tac `u` >> simp[]
QED

(* One structural interface serves preparation and the load/clamp tail. *)
Theorem extract32_read_code_shape:
  extract32_straight_read_frame m /\ m sa = (op,sb) ==>
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             ~is_ext_call_op i.inst_opcode /\ i.inst_opcode <> GAS)
    (emitted_insts sa sb)
Proof
  simp[extract32_straight_read_frame_def] >> strip_tac >>
  first_x_assum drule >> simp[IS_PREFIX_APPEND, EVERY_MEM] >>
  strip_tac >> rpt strip_tac >> first_x_assum drule >>
  Cases_on `i.inst_opcode` >>
  gvs[fresh_write_op_def, is_terminator_def, is_ext_call_op_def]
QED

Theorem extract32_tail_straight_noext:
  compile_extract32_load len dp off sa = (raw,sm) /\
  compile_clamp_basetype raw t sm = (op,sb) ==>
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             ~is_ext_call_op i.inst_opcode /\ i.inst_opcode <> GAS)
    (emitted_insts sa sb)
Proof
  strip_tac >>
  irule (INST_TYPE [``:'a`` |-> ``:operand``] extract32_read_code_shape) >>
  qexistsl_tac [`comp_bind (compile_extract32_load len dp off)
                   (\r. compile_clamp_basetype r t)`, `op`] >>
  simp[comp_bind_def] >> irule extract32_read_bind >>
  simp[extract32_read_load, extract32_read_clamp_basetype]
QED

Theorem extract32_read_success_frame_any:
  !m sa r sb s u.
    extract32_straight_read_frame m /\ m sa = (r,sb) /\
    run_inst_seq (emitted_insts sa sb) s = OK u ==>
    (u with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `extract32_straight_read_frame _`
    (mp_tac o REWRITE_RULE [extract32_straight_read_frame_def]) >>
  disch_then drule >> strip_tac >>
  drule_all extract32_run_frame >> simp[]
QED
