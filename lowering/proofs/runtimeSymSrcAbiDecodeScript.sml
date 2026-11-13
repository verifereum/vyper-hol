Theory runtimeSymSrcAbiDecode
Ancestors
  runtimeSymSrcAbiCalls abiEncoder runtimeSymSrcContext runtimeSymSrcEmission
  runtimeSymSrcInterfaces compileEnv emitHelper loweringShapeDefs venomInst list
  stackPlanTypes

Theorem decode_op[local]:
  emit_op opc ops s = (v,s') ==>
  opc <> CODESIZE /\ opc <> CODECOPY /\
  EVERY (\op. ~is_label_operand op) ops /\
  EVERY runtime_sym_inst (state_insts s) ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  metis_tac[runtime_sym_emit_op]
QED

Theorem decode_void[local]:
  emit_void opc ops s = (u,s') ==>
  opc <> CODESIZE /\ opc <> CODECOPY /\
  EVERY (\op. ~is_label_operand op) ops /\
  EVERY runtime_sym_inst (state_insts s) ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  metis_tac[runtime_sym_emit_void]
QED

Theorem decode_head[local]:
  ~is_label_operand src /\ ~is_label_operand hi /\
  EVERY runtime_sym_inst (state_insts s) /\
  (if hi = Lit 0w then comp_return (Lit 0w)
   else do hd <- emit_op ADD [src; Lit 32w];
           compile_abi_decode_range_check src hd hi;
           comp_return hd od) s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Cases_on `hi = Lit 0w` >>
  simp[comp_return_def, comp_bind_def, comp_ignore_bind_def]
  >- (rpt strip_tac >> gvs[is_label_operand_def]) >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  rev_dxrule decode_op >> simp[is_label_operand_def] >> strip_tac >>
  drule_all runtime_sym_abi_decode_range_check >> simp[]
QED

Theorem decode_array_bound[local]:
  ~is_label_operand start /\ ~is_label_operand cnt /\ ~is_label_operand hi /\
  EVERY runtime_sym_inst (state_insts s) /\
  (if hi = Lit 0w then comp_return ()
   else do sz <- emit_op MUL [cnt; Lit (n2w n)];
           ep <- emit_op ADD [start; sz];
           compile_abi_decode_range_check start ep hi od) s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Cases_on `hi = Lit 0w` >>
  simp[comp_return_def, comp_bind_def]
  >- (rpt strip_tac >> gvs[]) >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  ntac 2 (rev_dxrule decode_op >> simp[is_label_operand_def] >> strip_tac) >>
  drule_all runtime_sym_abi_decode_range_check >> simp[]
QED

Theorem runtime_sym_abi_decode_mutual:
  (!dst src opc bop hi info s u s'.
    ~is_label_operand dst /\ ~is_label_operand src /\
    ~is_label_operand bop /\ ~is_label_operand hi /\
    opc <> CODESIZE /\ opc <> CODECOPY /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_decode_to_buf dst src opc bop hi info s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!dst src opc bop hi elems ao vo s u s'.
    ~is_label_operand dst /\ ~is_label_operand src /\
    ~is_label_operand bop /\ ~is_label_operand hi /\
    opc <> CODESIZE /\ opc <> CODECOPY /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_decode_complex_elems dst src opc bop hi elems ao vo s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!dst src opc bop hi ei asz msz ip cnt s u s'.
    ~is_label_operand dst /\ ~is_label_operand src /\
    ~is_label_operand bop /\ ~is_label_operand hi /\
    ~is_label_operand ip /\ ~is_label_operand cnt /\
    opc <> CODESIZE /\ opc <> CODECOPY /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_decode_dyn_loop dst src opc bop hi ei asz msz ip cnt s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s'))
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >> rpt conj_tac
  >- suspend "prim"
  >- suspend "bytes"
  >- suspend "array"
  >- suspend "complex"
  >- suspend "nil"
  >- suspend "cons"
  >> suspend "loop"
QED

Resume runtime_sym_abi_decode_mutual[prim]:
  rpt gen_tac >>
  simp[Once compile_abi_decode_to_buf_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  drule_all runtime_sym_abi_dec_addr >> strip_tac >>
  gvs[compile_abi_decode_static_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rev_dxrule decode_op >> simp[] >> strip_tac >>
  drule_all runtime_sym_abi_clamp_basetype >> strip_tac >>
  rev_dxrule decode_void >> simp[]
QED
Resume runtime_sym_abi_decode_mutual[bytes]:
  rpt gen_tac >>
  simp[Once compile_abi_decode_to_buf_def, Once comp_bind_def] >>
  pairarg_tac >> first_assum SUBST1_TAC >> simp[NoAsms] >>
  simp[comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule_all decode_head >> strip_tac >>
  drule_all runtime_sym_abi_dec_addr >> strip_tac >>
  ntac 3 (rev_dxrule decode_op >> simp[is_label_operand_def] >> strip_tac) >>
  rev_dxrule decode_void >> simp[] >> strip_tac >>
  rename1 `(if _ then comp_return () else _) _ = (_,bound_state)` >>
  `EVERY runtime_sym_inst (state_insts bound_state)` by
    (qpat_x_assum `(if _ then comp_return () else _) _ = _` mp_tac >>
     Cases_on `hi = Lit 0w` >>
     simp[comp_return_def, comp_bind_def] >- (strip_tac >> gvs[]) >>
     pairarg_tac >> simp[] >> strip_tac >>
     rev_dxrule decode_op >> simp[] >> strip_tac >>
     drule_all runtime_sym_abi_decode_range_check >> simp[]) >>
  Cases_on `bop = Lit 0w`
  >- (Cases_on `opc` >> gvs[] >> rev_dxrule decode_void >> simp[is_label_operand_def]) >>
  gvs[comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  ntac 4 (rev_dxrule decode_op >> simp[is_label_operand_def] >> strip_tac) >>
  rev_dxrule decode_void >> simp[is_label_operand_def] >> strip_tac >>
  rev_dxrule decode_op >> simp[is_label_operand_def] >> strip_tac >>
  rev_dxrule decode_void >> simp[is_label_operand_def]
QED
Resume runtime_sym_abi_decode_mutual[array]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[Once compile_abi_decode_to_buf_def, Once comp_bind_def, NoAsms] >>
  pairarg_tac >> first_assum SUBST1_TAC >> simp[NoAsms] >>
  simp[comp_bind_def, comp_ignore_bind_def, NoAsms] >>
  rpt (pairarg_tac >> first_assum SUBST1_TAC >> simp[NoAsms]) >>
  strip_tac >> drule_all decode_head >> strip_tac >>
  drule_all runtime_sym_abi_dec_addr >> strip_tac >>
  ntac 3 (rev_dxrule decode_op >>
    (impl_tac >- (simp[NoAsms, is_label_operand_def] >> rpt conj_tac >>
      first_assum (MATCH_ACCEPT_TAC o REWRITE_RULE [is_label_operand_def]))) >> strip_tac) >>
  rev_dxrule decode_void >>
  (impl_tac >- (simp[NoAsms] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC)) >>
  strip_tac >>
  drule_all decode_array_bound >> strip_tac >>
  rev_dxrule decode_op >>
  (impl_tac >- (simp[NoAsms] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC)) >> strip_tac >>
  rev_dxrule decode_void >>
  (impl_tac >- (simp[NoAsms] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC)) >> strip_tac >>
  Cases_on `~elem_is_dyn /\ ~dec_info_needs_clamp ei`
  >- (qpat_x_assum `!can_bulk_copy ip i_ptr_alloc cnt. _` kall_tac >>
      gvs[comp_bind_def, comp_ignore_bind_def] >>
      rpt (pairarg_tac >> gvs[]) >>
      ntac 2 (rev_dxrule decode_op >> simp[is_label_operand_def] >> strip_tac) >>
      drule_all runtime_sym_abi_dec_addr >> strip_tac >>
      rev_dxrule decode_op >> simp[is_label_operand_def] >> strip_tac >>
      Cases_on `opc` >> gvs[] >> rev_dxrule decode_void >> simp[]) >>
  qpat_x_assum `!can_bulk_copy ip i_ptr_alloc cnt. _`
    (qspec_then `F` mp_tac) >>
  simp[NoAsms] >>
  (impl_tac >- gvs[]) >> strip_tac >>
  qpat_x_assum `(if ~elem_is_dyn /\ _ then _ else _) _ = _` mp_tac >>
  qpat_assum `~(~elem_is_dyn /\ _)` (fn th => rewrite_tac[th]) >>
  simp[comp_bind_def, comp_ignore_bind_def, NoAsms] >>
  rpt (pairarg_tac >> first_assum SUBST1_TAC >> simp[NoAsms]) >> strip_tac >>
  drule_all runtime_sym_alloc_buffer >> strip_tac >>
  rev_dxrule decode_void >>
  (impl_tac >- (simp[NoAsms, is_label_operand_def] >> rpt conj_tac >>
    first_assum (MATCH_ACCEPT_TAC o REWRITE_RULE [is_label_operand_def]))) >> strip_tac >>
  first_x_assum drule_all >> simp[NoAsms]
QED
Resume runtime_sym_abi_decode_mutual[complex]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[Once compile_abi_decode_to_buf_def, NoAsms] >>
  IF_CASES_TAC >>
  simp[comp_bind_def, comp_ignore_bind_def, NoAsms]
  >- (strip_tac >>
      qpat_x_assum `!sz. _ /\ hi = _ ==> _`
        (qspec_then `FOLDR (\(_,a,_) n. a+n) 0 elems` mp_tac) >>
      simp[] >> disch_then drule_all >> simp[]) >>
  ntac 2 (pairarg_tac >> first_assum SUBST1_TAC >> simp[NoAsms]) >> strip_tac >>
  rev_dxrule decode_op >>
  (impl_tac >- (simp[NoAsms, is_label_operand_def] >> conj_tac >>
    first_assum (MATCH_ACCEPT_TAC o REWRITE_RULE [is_label_operand_def]))) >>
  strip_tac >>
  drule_all runtime_sym_abi_decode_range_check >> strip_tac >>
  qpat_x_assum `!sz. _ /\ hi <> _ ==> _`
    (qspec_then `FOLDR (\(_,a,_) n. a+n) 0 elems` mp_tac) >>
  simp[] >> disch_then drule_all >> simp[]
QED
Resume runtime_sym_abi_decode_mutual[nil]:
  simp[Once compile_abi_decode_to_buf_def, comp_return_def] >>
  rpt strip_tac >> gvs[]
QED
Resume runtime_sym_abi_decode_mutual[cons]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[Once compile_abi_decode_to_buf_def, comp_bind_def, comp_ignore_bind_def, NoAsms] >>
  rpt (pairarg_tac >> first_assum SUBST1_TAC >> simp[NoAsms]) >> strip_tac >>
  drule_all runtime_sym_getelemptr_abi >> strip_tac >>
  rev_dxrule decode_op >>
  (impl_tac >- (simp[NoAsms, is_label_operand_def] >> conj_tac >>
    first_assum (MATCH_ACCEPT_TAC o REWRITE_RULE [is_label_operand_def]))) >>
  strip_tac >> Cases_on `_0` >>
  qpat_x_assum `!is_dyn dst src. _` (qspec_then `dec_info_needs_offset info` mp_tac) >>
  simp[NoAsms] >> disch_then drule_all >> strip_tac >>
  qpat_x_assum `!is_dyn. _` (qspec_then `dec_info_needs_offset info` mp_tac) >>
  simp[NoAsms, arithmeticTheory.ADD_SYM] >> disch_then drule_all >> simp[NoAsms]
QED
Resume runtime_sym_abi_decode_mutual[loop]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[Once compile_abi_decode_to_buf_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, NoAsms] >>
  rpt (pairarg_tac >> first_assum SUBST1_TAC >> simp[NoAsms]) >> strip_tac >>
  qpat_x_assum `!is_dyn_elem dst src. _` mp_tac >>
  ntac 3 (rev_dxrule runtime_sym_fresh_label >> strip_tac) >>
  gvs[] >>
  rename [`emit_inst JMP [Label hdr_lbl] [] pre = ((),jumped)`,
          `new_block hdr_lbl jumped = (bu,blocked)`] >>
  `EVERY runtime_sym_inst (state_insts pre)` by metis_tac[] >>
  drule_all runtime_sym_jump >> strip_tac >>
  rename1 `new_block hdr_lbl jumped = (bu,blocked)` >>
  `EVERY runtime_sym_inst (state_insts blocked)` by
    metis_tac[runtimeSymSrcEmissionProbeTheory.runtime_sym_new_block, pairTheory.SND] >>
  rev_dxrule decode_op >> simp[is_label_operand_def] >> strip_tac >>
  drule_all runtime_sym_abi_dec_addr >> strip_tac >>
  ntac 3 (rev_dxrule decode_op >> simp[is_label_operand_def] >> strip_tac) >>
  drule_all runtime_sym_jnz >> strip_tac >>
  rename1 `new_block body_lbl bs = (bu2,body_state)` >>
  `EVERY runtime_sym_inst (state_insts body_state)` by
    metis_tac[runtimeSymSrcEmissionProbeTheory.runtime_sym_new_block, pairTheory.SND] >>
  ntac 4 (rev_dxrule decode_op >> simp[is_label_operand_def] >> strip_tac) >>
  rename1 `(if dec_info_needs_offset ei then _ else _) nav_s = (actual_src,nav_t)` >>
  `EVERY runtime_sym_inst (state_insts nav_t) /\ ~is_label_operand actual_src` by
    (Cases_on `dec_info_needs_offset ei` >> gvs[comp_return_def] >>
     drule_at (Pat `compile_abi_decode_dyn_elem_ptr _ _ _ _ _ _ _ = _`)
       runtime_sym_abi_decode_dyn_elem_ptr >> simp[]) >>
  ntac 3 (rev_dxrule decode_op >> simp[is_label_operand_def] >> strip_tac) >>
  disch_then drule_all >> strip_tac >>
  rev_dxrule decode_op >> simp[is_label_operand_def] >> strip_tac >>
  rev_dxrule decode_void >> simp[is_label_operand_def] >> strip_tac >>
  drule_all runtime_sym_jump >> strip_tac >>
  metis_tac[runtimeSymSrcEmissionProbeTheory.runtime_sym_new_block, pairTheory.SND]
QED
Finalise runtime_sym_abi_decode_mutual

Theorem runtime_sym_abi_decode_to_buf:
  ~is_label_operand dst /\ ~is_label_operand src /\
  ~is_label_operand bop /\ ~is_label_operand hi /\
  opc <> CODESIZE /\ opc <> CODECOPY /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_abi_decode_to_buf dst src opc bop hi info s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  MATCH_ACCEPT_TAC (cj 1 runtime_sym_abi_decode_mutual)
QED

Theorem runtime_sym_abi_decode_complex_elems:
  ~is_label_operand dst /\ ~is_label_operand src /\
  ~is_label_operand bop /\ ~is_label_operand hi /\
  opc <> CODESIZE /\ opc <> CODECOPY /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_abi_decode_complex_elems dst src opc bop hi elems ao vo s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  MATCH_ACCEPT_TAC (cj 2 runtime_sym_abi_decode_mutual)
QED

Theorem runtime_sym_abi_decode_dyn_loop:
  ~is_label_operand dst /\ ~is_label_operand src /\
  ~is_label_operand bop /\ ~is_label_operand hi /\
  ~is_label_operand ip /\ ~is_label_operand cnt /\
  opc <> CODESIZE /\ opc <> CODECOPY /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_abi_decode_dyn_loop dst src opc bop hi ei asz msz ip cnt s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  MATCH_ACCEPT_TAC (cj 3 runtime_sym_abi_decode_mutual)
QED
