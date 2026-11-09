(* Generated instruction witnesses, specialized to constructor DLOAD decoding.
   Adapted from the shape-coverage interface of EntryResourceRegister, without
   depending on that theory's unrelated general-opcode coverage proof. *)
Theory ctorDeployMemoryRunPtrPrefixEntryDecoderShape
Ancestors
  abiDecoderCode actualDecoderSites actualDecoderPackaging fragExec venomWf compileEnv emitHelper
  venomInst abiEncoder context localPtrsProps abiEncoderProps ctorAbiActualSites

Theorem entry_shape_member_extends[local]:
  cs_extends st last /\ abi_decoder_code_member inst st ==>
  abi_decoder_code_member inst last
Proof
  metis_tac[decoder_code_member_prefix, decoder_code_member_state_insts]
QED

Theorem entry_shape_current_member[local]:
  fn_has_code st last func /\ MEM inst last.cs_current_insts ==>
  MEM inst (fn_insts func)
Proof
  simp[fn_has_code_def] >> strip_tac >>
  irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
  gvs[rich_listTheory.IS_PREFIX_APPEND] >> simp[]
QED

Theorem entry_shape_emission_extends[local]:
  (!st. cs_extends st (SND (emit_op opc ops st)) /\
    st.cs_next_id <= (SND (emit_op opc ops st)).cs_next_id) /\
  (!st. cs_extends st (SND (emit_void opc ops st)) /\
    st.cs_next_id <= (SND (emit_void opc ops st)).cs_next_id) /\
  (!st. cs_extends st (SND (emit_inst opc ops outs st)) /\
    st.cs_next_id <= (SND (emit_inst opc ops outs st)).cs_next_id)
Proof
  simp[emit_op_def, emit_void_def, emit_inst_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
    emit_def, cs_extends_def, rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem entry_shape_no_id_extends[local]:
  (!st. cs_extends st (SND (comp_return v st)) /\
    st.cs_next_id <= (SND (comp_return v st)).cs_next_id) /\
  (!st. cs_extends st (SND (fresh_label name st)) /\
    st.cs_next_id <= (SND (fresh_label name st)).cs_next_id) /\
  (!st. cs_extends st (SND (new_block name st)) /\
    st.cs_next_id <= (SND (new_block name st)).cs_next_id)
Proof
  simp[comp_return_def, fresh_label_def, new_block_def, cs_extends_def,
    rich_listTheory.IS_PREFIX_APPEND] >>
  gen_tac >> qexists `[<|bb_label := st.cs_current_bb;
    bb_instructions := st.cs_current_insts|>]` >> simp[]
QED

Theorem entry_shape_coverage_bind[local]:
  (!st. cs_extends st (SND (f st)) /\
    st.cs_next_id <= (SND (f st)).cs_next_id) /\
  (!v st. cs_extends st (SND (g v st))) /\
  (!st func aid. fn_has_code st (SND (f st)) func /\
    st.cs_next_id <= aid /\ aid < (SND (f st)).cs_next_id ==>
    ?inst. inst.inst_id = aid /\ abi_decoder_code_member inst (SND (f st)) /\
      MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst) /\
  (!v st func aid. fn_has_code st (SND (g v st)) func /\
    st.cs_next_id <= aid /\ aid < (SND (g v st)).cs_next_id ==>
    ?inst. inst.inst_id = aid /\ abi_decoder_code_member inst (SND (g v st)) /\
      MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst) ==>
  !st func aid. fn_has_code st (SND (comp_bind f g st)) func /\
    st.cs_next_id <= aid /\ aid < (SND (comp_bind f g st)).cs_next_id ==>
    ?inst. inst.inst_id = aid /\
      abi_decoder_code_member inst (SND (comp_bind f g st)) /\
      MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst
Proof
  strip_tac >> rpt gen_tac >> simp[comp_bind_def] >> pairarg_tac >>
  simp[] >> strip_tac >> rename1 `f st = (v,mid)` >>
  `cs_extends st mid /\ st.cs_next_id <= mid.cs_next_id` by metis_tac[pairTheory.SND] >>
  `cs_extends mid (SND (g v mid))` by metis_tac[] >>
  `fn_has_code st mid func /\ fn_has_code mid (SND (g v mid)) func` by
    metis_tac[fn_has_code_split] >>
  Cases_on `aid < mid.cs_next_id`
  >- (qpat_x_assum `!st func aid. fn_has_code st (SND (f st)) func /\ _ ==> _`
        (qspecl_then [`st`, `func`, `aid`] mp_tac) >>
      asm_simp_tac (srw_ss()) [] >> strip_tac >>
      qexists `inst` >> metis_tac[entry_shape_member_extends]) >>
  `mid.cs_next_id <= aid` by decide_tac >> metis_tac[]
QED

Theorem entry_shape_emit_op[local]:
  !opc ops. (opc = ALLOCA ==> ops = [Lit 32w]) ==>
  !st func aid.
    fn_has_code st (SND (emit_op opc ops st)) func /\
    st.cs_next_id <= aid /\ aid < (SND (emit_op opc ops st)).cs_next_id ==>
    ?inst. inst.inst_id = aid /\
      abi_decoder_code_member inst (SND (emit_op opc ops st)) /\
      MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_var_def, fresh_id_def, emit_def] >> strip_tac >>
  `aid = st.cs_next_id` by decide_tac >>
  qexists `mk_inst st.cs_next_id opc ops
    [STRING #"%" (toString st.cs_next_var)]` >>
  simp[mk_inst_def, abi_decoder_code_member_def, abi_decoder_alloc_shape_def] >>
  irule entry_shape_current_member >> goal_assum (drule_at Any) >> simp[mk_inst_def]
QED

Theorem entry_shape_emit_void[local]:
  !opc ops. opc <> ALLOCA ==>
  !st func aid.
    fn_has_code st (SND (emit_void opc ops st)) func /\
    st.cs_next_id <= aid /\ aid < (SND (emit_void opc ops st)).cs_next_id ==>
    ?inst. inst.inst_id = aid /\
      abi_decoder_code_member inst (SND (emit_void opc ops st)) /\
      MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, emit_def] >> strip_tac >>
  `aid = st.cs_next_id` by decide_tac >>
  qexists `mk_inst st.cs_next_id opc ops []` >>
  simp[mk_inst_def, abi_decoder_code_member_def, abi_decoder_alloc_shape_def] >>
  irule entry_shape_current_member >> goal_assum (drule_at Any) >> simp[mk_inst_def]
QED

Theorem entry_shape_emit_inst[local]:
  !opc ops outs. (opc = ALLOCA ==> ops = [Lit 32w] /\ ?out. outs = [out]) ==>
  !st func aid.
    fn_has_code st (SND (emit_inst opc ops outs st)) func /\
    st.cs_next_id <= aid /\ aid < (SND (emit_inst opc ops outs st)).cs_next_id ==>
    ?inst. inst.inst_id = aid /\
      abi_decoder_code_member inst (SND (emit_inst opc ops outs st)) /\
      MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, emit_def] >> strip_tac >>
  `aid = st.cs_next_id` by decide_tac >>
  qexists `mk_inst st.cs_next_id opc ops outs` >>
  simp[mk_inst_def, abi_decoder_code_member_def, abi_decoder_alloc_shape_def] >>
  irule entry_shape_current_member >> goal_assum (drule_at Any) >> simp[mk_inst_def]
QED

Theorem entry_shape_return[local]:
  !v st func aid.
    fn_has_code st (SND (comp_return v st)) func /\
    st.cs_next_id <= aid /\ aid < (SND (comp_return v st)).cs_next_id ==>
    ?inst. inst.inst_id = aid /\
      abi_decoder_code_member inst (SND (comp_return v st)) /\
      MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst
Proof
  simp[comp_return_def]
QED

Theorem entry_shape_fresh_label[local]:
  !name st func aid.
    fn_has_code st (SND (fresh_label name st)) func /\
    st.cs_next_id <= aid /\ aid < (SND (fresh_label name st)).cs_next_id ==>
    ?inst. inst.inst_id = aid /\
      abi_decoder_code_member inst (SND (fresh_label name st)) /\
      MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst
Proof
  simp[fresh_label_def]
QED

Theorem entry_shape_new_block[local]:
  !name st func aid.
    fn_has_code st (SND (new_block name st)) func /\
    st.cs_next_id <= aid /\ aid < (SND (new_block name st)).cs_next_id ==>
    ?inst. inst.inst_id = aid /\
      abi_decoder_code_member inst (SND (new_block name st)) /\
      MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst
Proof
  simp[new_block_def]
QED

Theorem entry_shape_bind[local]:
  (!st. cs_extends st (SND (f st)) /\
    st.cs_next_id <= (SND (f st)).cs_next_id /\
    !func aid. fn_has_code st (SND (f st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (f st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\ abi_decoder_code_member inst (SND (f st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst) /\
  (!v st. cs_extends st (SND (g v st)) /\
    st.cs_next_id <= (SND (g v st)).cs_next_id /\
    !func aid. fn_has_code st (SND (g v st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (g v st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\ abi_decoder_code_member inst (SND (g v st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst) ==>
  !st. cs_extends st (SND (comp_bind f g st)) /\
    st.cs_next_id <= (SND (comp_bind f g st)).cs_next_id /\
    !func aid. fn_has_code st (SND (comp_bind f g st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (comp_bind f g st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (comp_bind f g st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst
Proof
  strip_tac >> gen_tac >> reverse conj_tac
  >- (reverse conj_tac
      >- (qid_spec_tac `st` >> ho_match_mp_tac entry_shape_coverage_bind >> metis_tac[]) >>
      simp[comp_bind_def] >> pairarg_tac >> simp[] >>
      metis_tac[pairTheory.SND, arithmeticTheory.LESS_EQ_TRANS]) >>
  simp[comp_bind_def] >> pairarg_tac >> simp[] >>
  metis_tac[pairTheory.SND, cs_extends_trans]
QED

Theorem entry_shape_ignore_bind[local]:
  (!st. cs_extends st (SND (f st)) /\
    st.cs_next_id <= (SND (f st)).cs_next_id /\
    !func aid. fn_has_code st (SND (f st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (f st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\ abi_decoder_code_member inst (SND (f st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst) /\
  (!st. cs_extends st (SND (g st)) /\
    st.cs_next_id <= (SND (g st)).cs_next_id /\
    !func aid. fn_has_code st (SND (g st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (g st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\ abi_decoder_code_member inst (SND (g st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst) ==>
  !st. cs_extends st (SND (comp_ignore_bind f g st)) /\
    st.cs_next_id <= (SND (comp_ignore_bind f g st)).cs_next_id /\
    !func aid. fn_has_code st (SND (comp_ignore_bind f g st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (comp_ignore_bind f g st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (comp_ignore_bind f g st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst
Proof
  strip_tac >> rewrite_tac[comp_ignore_bind_def] >>
  ho_match_mp_tac entry_shape_bind >> simp[]
QED

val shape_simps = [entry_shape_emission_extends, entry_shape_no_id_extends,
  entry_shape_emit_op, entry_shape_emit_void, entry_shape_emit_inst,
  entry_shape_return, entry_shape_fresh_label, entry_shape_new_block];
val shape_db = fn t => ho_match_mp_tac entry_shape_bind >>
  conj_tac >- simp (t::shape_simps) >> gen_tac;
val shape_dib = fn t => ho_match_mp_tac entry_shape_ignore_bind >>
  conj_tac >- simp (t::shape_simps);

Theorem entry_shape_alloc_buffer[local]:
  !st. cs_extends st (SND (compile_alloc_buffer 32 st)) /\
    st.cs_next_id <= (SND (compile_alloc_buffer 32 st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_alloc_buffer 32 st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_alloc_buffer 32 st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_alloc_buffer 32 st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst
Proof
  rewrite_tac[compile_alloc_buffer_def] >>
  shape_db entry_shape_emit_op >> simp shape_simps
QED

Theorem entry_shape_clamp[local]:
  !c v st. cs_extends st (SND (compile_abi_clamp_basetype v c st)) /\
    st.cs_next_id <= (SND (compile_abi_clamp_basetype v c st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_abi_clamp_basetype v c st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_abi_clamp_basetype v c st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_abi_clamp_basetype v c st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst
Proof
  Cases >> simp[compile_abi_clamp_basetype_def,
    compile_abi_int_clamp_def, compile_abi_bytes_clamp_def]
  >- simp shape_simps
  >- (gen_tac >> IF_CASES_TAC >> simp_tac pure_ss [LET_THM] >>
      ntac 2 (shape_db entry_shape_emit_op) >> simp shape_simps)
  >- (gen_tac >> ntac 2 (shape_db entry_shape_emit_op) >> simp shape_simps) >>
  gen_tac >> ntac 2 (shape_db entry_shape_emit_op) >> simp shape_simps
QED

Theorem entry_shape_static[local]:
  opc <> ALLOCA /\
  (!v st. cs_extends st (SND (clamp v st)) /\
    st.cs_next_id <= (SND (clamp v st)).cs_next_id /\
    !func aid. fn_has_code st (SND (clamp v st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (clamp v st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\ abi_decoder_code_member inst (SND (clamp v st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst) ==>
  !st. cs_extends st (SND (compile_abi_decode_static src dst opc clamp st)) /\
    st.cs_next_id <= (SND (compile_abi_decode_static src dst opc clamp st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_abi_decode_static src dst opc clamp st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_abi_decode_static src dst opc clamp st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_abi_decode_static src dst opc clamp st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst
Proof
  strip_tac >> rewrite_tac[compile_abi_decode_static_def] >>
  shape_db entry_shape_emit_op >>
  shape_dib entry_shape_return >> simp shape_simps
QED

Theorem entry_shape_getelemptr[local]:
  !src dyn off opc hi. opc <> ALLOCA ==> !st.
    cs_extends st (SND (compile_getelemptr_abi src dyn off opc hi st)) /\
    st.cs_next_id <= (SND (compile_getelemptr_abi src dyn off opc hi st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_getelemptr_abi src dyn off opc hi st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_getelemptr_abi src dyn off opc hi st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_getelemptr_abi src dyn off opc hi st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst
Proof
  ntac 5 gen_tac >> strip_tac >> rewrite_tac[compile_getelemptr_abi_def] >>
  shape_db entry_shape_emit_op >> Cases_on `dyn` >>
  simp shape_simps >> ntac 2 (shape_db entry_shape_emit_op) >>
  ho_match_mp_tac entry_shape_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp shape_simps >>
      ntac 2 (shape_db entry_shape_emit_op) >> simp shape_simps) >>
  simp shape_simps
QED

Theorem entry_shape_dyn_elem_ptr[local]:
  !opc src data hi sz. opc <> ALLOCA ==> !st.
    cs_extends st (SND (compile_abi_decode_dyn_elem_ptr opc src data hi sz st)) /\
    st.cs_next_id <= (SND (compile_abi_decode_dyn_elem_ptr opc src data hi sz st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_abi_decode_dyn_elem_ptr opc src data hi sz st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_abi_decode_dyn_elem_ptr opc src data hi sz st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_abi_decode_dyn_elem_ptr opc src data hi sz st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst
Proof
  ntac 5 gen_tac >> strip_tac >> rewrite_tac[compile_abi_decode_dyn_elem_ptr_def] >>
  ntac 2 (shape_db entry_shape_emit_op) >>
  ho_match_mp_tac entry_shape_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp shape_simps >>
      ntac 2 (shape_db entry_shape_emit_op) >>
      shape_dib entry_shape_emit_void >>
      ntac 3 (shape_db entry_shape_emit_op) >> simp shape_simps) >>
  simp shape_simps
QED

Theorem prefix_entry_shape_decoder_mutual:
  (!dst src opc hi info. opc = DLOAD ==>
    !st. cs_extends st (SND (compile_abi_decode_to_buf dst src opc hi info st)) /\
    st.cs_next_id <= (SND (compile_abi_decode_to_buf dst src opc hi info st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_abi_decode_to_buf dst src opc hi info st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_abi_decode_to_buf dst src opc hi info st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_abi_decode_to_buf dst src opc hi info st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst) /\
  (!dst src opc hi elems ao vo. opc = DLOAD ==>
    !st. cs_extends st (SND (compile_abi_decode_complex_elems dst src opc hi elems ao vo st)) /\
    st.cs_next_id <= (SND (compile_abi_decode_complex_elems dst src opc hi elems ao vo st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_abi_decode_complex_elems dst src opc hi elems ao vo st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_abi_decode_complex_elems dst src opc hi elems ao vo st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_abi_decode_complex_elems dst src opc hi elems ao vo st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst) /\
  (!dst src opc hi ei asz msz ip cnt. opc = DLOAD ==>
    !st. cs_extends st (SND (compile_abi_decode_dyn_loop dst src opc hi ei asz msz ip cnt st)) /\
    st.cs_next_id <= (SND (compile_abi_decode_dyn_loop dst src opc hi ei asz msz ip cnt st)).cs_next_id /\
    !func aid. fn_has_code st (SND (compile_abi_decode_dyn_loop dst src opc hi ei asz msz ip cnt st)) func /\
      st.cs_next_id <= aid /\ aid < (SND (compile_abi_decode_dyn_loop dst src opc hi ei asz msz ip cnt st)).cs_next_id ==>
      ?inst. inst.inst_id = aid /\
        abi_decoder_code_member inst (SND (compile_abi_decode_dyn_loop dst src opc hi ei asz msz ip cnt st)) /\
        MEM inst (fn_insts func) /\ abi_decoder_alloc_shape inst)
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt (disch_then strip_assume_tac) >> gvs[]
  >- suspend "word"
  >- suspend "bytes"
  >- suspend "array"
  >- suspend "complex"
  >- suspend "nil"
  >- suspend "cons"
  >> suspend "loop"
QED

Resume prefix_entry_shape_decoder_mutual[word]:
  once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  irule entry_shape_static >> simp[entry_shape_clamp]
QED
Resume prefix_entry_shape_decoder_mutual[bytes]:
  once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  ntac 3 (shape_db entry_shape_emit_op) >>
  shape_dib entry_shape_emit_void >>
  ho_match_mp_tac entry_shape_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp shape_simps >>
      ntac 4 (shape_db entry_shape_emit_op) >> simp shape_simps) >>
  simp shape_simps
QED
Resume prefix_entry_shape_decoder_mutual[array]:
  once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  ntac 3 (shape_db entry_shape_emit_op) >>
  shape_dib entry_shape_emit_void >>
  ho_match_mp_tac entry_shape_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp shape_simps >>
      ntac 5 (shape_db entry_shape_emit_op) >> simp shape_simps) >>
  shape_db entry_shape_emit_op >>
  shape_dib entry_shape_emit_void >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC >> gvs[]
  >- (ntac 3 (shape_db entry_shape_emit_op) >> simp shape_simps) >>
  shape_db entry_shape_alloc_buffer >> shape_dib entry_shape_emit_void >>
  first_x_assum irule >> simp[]
QED
Resume prefix_entry_shape_decoder_mutual[complex]:
  once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC
  >- simp[] >>
  ntac 3 (shape_db entry_shape_emit_op) >> shape_dib entry_shape_emit_void >>
  simp[]
QED
Resume prefix_entry_shape_decoder_mutual[nil]:
  once_rewrite_tac[compile_abi_decode_to_buf_def] >> simp shape_simps
QED
Resume prefix_entry_shape_decoder_mutual[cons]:
  once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  shape_db entry_shape_getelemptr >> shape_db entry_shape_emit_op >>
  ho_match_mp_tac entry_shape_ignore_bind >> conj_tac
  >- (first_x_assum (irule o SRULE[]) >> simp[]) >>
  simp[]
QED
Resume prefix_entry_shape_decoder_mutual[loop]:
  once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  ntac 3 (shape_db entry_shape_fresh_label) >>
  shape_dib entry_shape_emit_inst >> shape_dib entry_shape_new_block >>
  ntac 4 (shape_db entry_shape_emit_op) >>
  shape_dib entry_shape_emit_inst >> shape_dib entry_shape_new_block >>
  ntac 4 (shape_db entry_shape_emit_op) >>
  ho_match_mp_tac entry_shape_bind >> conj_tac
  >- (IF_CASES_TAC >> simp (entry_shape_dyn_elem_ptr::shape_simps)) >>
  gen_tac >> ntac 3 (shape_db entry_shape_emit_op) >>
  ho_match_mp_tac entry_shape_ignore_bind >> conj_tac
  >- (first_x_assum (irule o SRULE[]) >> simp[]) >>
  shape_db entry_shape_emit_op >>
  shape_dib entry_shape_emit_void >> shape_dib entry_shape_emit_inst >>
  shape_dib entry_shape_new_block >> simp shape_simps
QED
Finalise prefix_entry_shape_decoder_mutual

Theorem prefix_entry_decoder_alloca_shape:
  compile_abi_decode_to_buf dst src DLOAD hi info st = ((),last) /\
  fn_has_code st last func /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  st.cs_next_id <= inst.inst_id /\ inst.inst_id < last.cs_next_id ==>
  inst.inst_operands = [Lit 32w]
Proof
  strip_tac >>
  mp_tac (cj 1 prefix_entry_shape_decoder_mutual |> Q.SPECL
    [`dst`, `src`, `DLOAD`, `hi`, `info`] |> SRULE []) >>
  disch_then (qspec_then `st` mp_tac) >> simp[] >> strip_tac >>
  `?site. site.inst_id = inst.inst_id /\ MEM site (fn_insts func) /\
    abi_decoder_alloc_shape site` by metis_tac[pairTheory.SND] >>
  `site = inst` by metis_tac[fn_inst_ids_distinct_inj] >>
  gvs[abi_decoder_alloc_shape_def]
QED
