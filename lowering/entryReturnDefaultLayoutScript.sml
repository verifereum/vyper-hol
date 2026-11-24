(* Static confinement of the default-capable external return fragment. *)
Theory entryReturnDefaultLayout
Ancestors
  createSizeExternalReturnCode createSizeTypedCopyCode createSizeDecodeCode
  extcallReturnDefaultRouting emitHelperProps fragExec exprSimAbiGasBridge
  createSizeCutCode createSizeCutOpens compileEnv context exprLowering venomInst pair list
  loweringExtCallOpcodes loweringShapeDefs fragObserverCodeProps
  ctorCallFreeRules ctorCallFreeOps ctorCallFreeABIDecode ctorCallFreeValues
  deploySymSrcBlockFrame deploySymSrcFrameABI deploySymSrcFrameContext
  deploySymSrcFrameExprHelpers exprSimAbiDecodeSiteCoverage
  exprLoweringProps emitHelper rich_list arithmetic entryCreateIntervalLayout

Theorem extcall_default_return_closed[local]:
  comp_bind (compile_alloc_buffer n)
    (\r. compile_default_return_path ce rt dt buf r.buf_operand
      def addr skip lo hi info) sr = (result,sb) ==>
  create_cut_code {} sr sb
Proof
  strip_tac >>
  `create_cut_code {} sr (SND (comp_bind (compile_alloc_buffer n)
     (\r. compile_default_return_path ce rt dt buf r.buf_operand
       def addr skip lo hi info) sr))` suffices_by simp[] >>
  irule create_cut_code_bind >>
  simp[create_alloc_buffer_cut_code, create_cut_targets_def,
       create_default_return_path_cut_code,
       create_store_memory_cut_code, create_decode_to_buf_cut_code]
QED

Theorem extcall_default_return_empty[local]:
  comp_bind (compile_alloc_buffer n)
    (\r. compile_default_return_path ce rt dt buf r.buf_operand
      def addr skip lo hi info) sr = (result,sb) ==>
  sb.cs_current_insts = []
Proof
  simp[comp_bind_def, UNCURRY_VAR] >>
  disch_then (strip_assume_tac o MATCH_MP return_default_path_intervals) >>
  drule new_block_props >> simp[]
QED

(* Changing only the history of completed blocks leaves the fragment unchanged. *)
Theorem default_frag_history[local]:
  frag_code (a with cs_blocks := a.cs_blocks ++ B)
            (b with cs_blocks := b.cs_blocks ++ B) = frag_code a b
Proof
  simp[frag_code_def, emitted_insts_def, emitted_blocks_def,
       TAKE_APPEND1]
QED

Definition default_layout_tail_def:
  default_layout_tail ce def dst rt dt skip addr xl cl lo hi buf info = do
    compile_store_memory ce def dst rt dt;
    (if skip then comp_return () else compile_extcodesize_check addr);
    emit_inst JMP [Label xl] [];
    new_block cl;
    sz <- compile_return_value_decode lo hi;
    compile_abi_decode_to_buf dst (Lit 0w) MLOAD buf sz info;
    emit_inst JMP [Label xl] [];
    new_block xl
  od
End

Theorem default_tail_static[local]:
  let m = default_layout_tail ce def dst rt dt skip addr xl cl lo hi buf info in
  deploy_blocks_frame m /\
  ((!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\
           opc <> CREATE2 ==> P opc) /\ P MLOAD ==>
    !a. EVERY (\i. P i.inst_opcode) (state_insts a) ==>
        EVERY (\i. P i.inst_opcode) (state_insts (SND (m a))))
Proof
  simp[default_layout_tail_def] >> conj_tac
  >- (Cases_on `skip` >>
      rpt (FIRST [ho_match_mp_tac deploy_blocks_frame_ignore_bind >> conj_tac,
                  ho_match_mp_tac deploy_blocks_frame_bind >> conj_tac,
                  gen_tac,
                  CHANGED_TAC (simp[deploy_blocks_frame_extcodesize_check,
                                   deploy_blocks_frame_return_value_decode])])) >>
  strip_tac >> Cases_on `skip` >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
              ho_match_mp_tac every_state_insts_bind >> conj_tac,
              CHANGED_TAC (simp[UNDISCH opcode_every_store_memory,
                UNDISCH opcode_every_extcodesize_check,
                UNDISCH opcode_every_return_value_decode,
                UNDISCH opcode_every_abi_decode_opcode, opcode_every_emit_inst,
                every_state_insts_new_block, every_state_insts_return]), gen_tac])
QED

Theorem default_history_opcode[local]:
  deploy_blocks_frame m /\
  (!s. EVERY P (state_insts s) ==> EVERY P (state_insts (SND (m s)))) /\
  a.cs_current_insts = [] /\ m a = (x,b) ==>
  EVERY P (frag_code a b)
Proof
  strip_tac >> qabbrev_tac `s = a with cs_blocks := []` >>
  Cases_on `m s` >> rename1 `m s = (y,t)` >>
  `a = s with cs_blocks := s.cs_blocks ++ a.cs_blocks` by simp[Abbr `s`] >>
  qpat_x_assum `deploy_blocks_frame m` mp_tac >>
  simp[deploy_blocks_frame_def] >>
  disch_then (qspecl_then [`s`, `a.cs_blocks`] mp_tac) >> simp[] >>
  strip_tac >>
  `EVERY P (state_insts t)` by
    (qpat_x_assum `!s. EVERY P _ ==> _` (qspec_then `s` mp_tac) >>
     simp[Abbr `s`, state_insts_def, all_blocks_def]) >>
  `b = t with cs_blocks := t.cs_blocks ++ a.cs_blocks` by
    (qpat_x_assum `m (s with cs_blocks := _) = _` mp_tac >>
     qpat_assum `a = s with cs_blocks := _`
       (fn th => once_rewrite_tac [GSYM th]) >> simp[]) >>
  `frag_code a b = frag_code s t` by metis_tac[default_frag_history] >>
  fs[EVERY_MEM] >> metis_tac[frag_code_in_state_insts]
QED

Theorem default_shell_opcode[local]:
  emit_op RETURNDATASIZE [] a = (rds,a1) /\
  emit_op ISZERO [rds] a1 = (iz,a2) /\
  fresh_label "extcall_default" a2 = (dl,a3) /\
  fresh_label "extcall_decode" a3 = (cl,a4) /\
  fresh_label "extcall_exit" a4 = (xl,a5) /\
  emit_inst JNZ [iz; Label dl; Label cl] [] a5 = ((),a6) /\
  new_block dl a6 = (old,ds) ==>
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code a ds)
Proof
  simp[emit_op_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, fresh_label_def, emit_def,
       new_block_def] >>
  strip_tac >> gvs[] >>
  simp[frag_code_def, emitted_blocks_def, mk_inst_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]
QED

Theorem default_path_opcode[local]:
  compile_default_return_path ce rt dt buf dst def addr skip lo hi info a = (r,b) ==>
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code a b)
Proof
  strip_tac >> drule return_default_path_intervals >> strip_tac >>
  `EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code a ds)` by
    (irule default_shell_opcode >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code ds b)` by
    (irule (INST_TYPE [alpha |-> ``:string``] default_history_opcode) >>
     conj_tac >- (qpat_assum `new_block _ _ = (_,ds)` (mp_tac o MATCH_MP new_block_props) >> simp[]) >>
     qexistsl_tac [`default_layout_tail ce def dst rt dt skip addr xl cl lo hi buf info`, `old3`] >>
     conj_tac >-
       (mp_tac (Q.INST [`P` |-> `\opc. ~MEM opc [INVOKE; CREATE; CREATE2]`]
                       default_tail_static) >> simp[]) >>
     conj_tac >-
       (mp_tac (Q.INST [`P` |-> `\opc. T`] default_tail_static) >> simp[]) >>
     simp[default_layout_tail_def, comp_bind_def, comp_ignore_bind_def]) >>
  `cs_extends a ds /\ cs_extends ds b` by
    (imp_res_tac cs_extends_fresh_label >> imp_res_tac cs_extends_emit_inst >>
     imp_res_tac cs_extends_new_block >>
     `cs_extends a a1 /\ cs_extends a1 a2` by metis_tac[ci_mono_emit_op, ci_mono_def, SND] >>
     `cs_extends ds de` by metis_tac[ci_mono_compile_store_memory, ci_mono_def, SND] >>
     `cs_extends de ck` by
       (Cases_on `skip` >- gvs[comp_return_def, cs_extends_refl] >>
        gvs[compile_extcodesize_check_def, comp_bind_def] >> pairarg_tac >> gvs[] >>
        metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def, SND, cs_extends_trans]) >>
     `cs_extends cs hs` by metis_tac[ci_mono_compile_return_value_decode, ci_mono_def, SND] >>
     `cs_extends hs he` by metis_tac[cj 1 ci_mono_compile_abi_decode, ci_mono_def, SND] >>
     metis_tac[cs_extends_trans]) >>
  drule_all abi_decode_frag_code_compose >>
  strip_tac >> fs[EVERY_MEM] >> metis_tac[]
QED

Theorem default_alloc_layout[local]:
  compile_alloc_buffer n sr = (r,a) ==>
  cs_extends sr a /\ a.cs_current_bb = sr.cs_current_bb /\
  a.cs_next_label = sr.cs_next_label /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code sr a)
Proof
  simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[cs_extends_def, frag_code_same_blocks, mk_inst_def, DROP_LENGTH_APPEND]
QED

Theorem extcall_default_return_opcode[local]:
  comp_bind (compile_alloc_buffer n)
    (\r. compile_default_return_path ce rt dt buf r.buf_operand
      def addr skip lo hi info) sr = (result,sb) ==>
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code sr sb)
Proof
  simp[comp_bind_def, UNCURRY_VAR] >>
  Cases_on `compile_alloc_buffer n sr` >> simp[] >> strip_tac >>
  drule default_alloc_layout >> strip_tac >>
  drule default_path_opcode >> strip_tac >>
  rename1 `compile_alloc_buffer _ _ = (alloc,ac)` >>
  `cs_extends ac sb` by
    metis_tac[externalEntryShapeTheory.compile_default_return_path_labels,SND] >>
  drule_all abi_decode_frag_code_compose >>
  strip_tac >> fs[EVERY_MEM] >> metis_tac[]
QED

Theorem default_return_exit_separation[local]:
  cs_extends sr sb /\ create_layout sr sb ==>
  ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks sr sb)) /\
  (sr.cs_current_bb = sb.cs_current_bb ==>
     LENGTH sr.cs_current_insts <= LENGTH sb.cs_current_insts)
Proof
  simp[create_layout_def, cs_extends_def] >> strip_tac >>
  `emitted_blocks sr sb = new` by metis_tac[emitted_blocks_append] >>
  fs[] >> Cases_on `new = []` >- fs[IS_PREFIX_LENGTH] >>
  fs[] >> metis_tac[MEM_MAP, MEM_LAST_NOT_NIL]
QED

Theorem extcall_default_return_layout:
  comp_bind (compile_alloc_buffer n)
    (\r. compile_default_return_path ce rt dt buf r.buf_operand
      def addr skip lo hi info) sr = (result,sb) ==>
  cs_extends sr sb /\ create_cut_code {} sr sb /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code sr sb) /\
  sb.cs_current_insts = [] /\
  (create_layout sr sb ==>
    ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks sr sb)) /\
    (sr.cs_current_bb = sb.cs_current_bb ==>
       LENGTH sr.cs_current_insts <= LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  drule extcall_default_return_closed >> strip_tac >>
  drule extcall_default_return_opcode >> strip_tac >>
  drule extcall_default_return_empty >> strip_tac >>
  `cs_extends sr sb` by fs[create_cut_code_def] >>
  simp[] >> strip_tac >>
  drule_all default_return_exit_separation >> simp[]
QED
