(* Retain the same ABI cursor and ghosts, with both emitted steps confined. *)
Theory entryCreateAbiInitScope
Ancestors
  abiEncodeValuesCursorInit abiEncoderWindowPhase exprSimAbiEncodeExecFrame
  createExprSizeExitDefs abiEncoderProps fragGasOrigin fragGasOriginPtr fragExec
  entryDecodeStructure emitHelper compileEnv ptrDiscipline
  venomExecSemantics venomInst venomState venomMemDefs
  relation finite_map pred_set list arithmetic words

Theorem cursor_init_confined_step[local]:
  s.vs_inst_idx < LENGTH en.cs_current_insts /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\ i.inst_id IN frag_ids st en /\
  gas_origin_edge F explicit ctx func s [] (OK t) ==>
  create_expr_prefix st en explicit ctx func s [] t
Proof
  strip_tac >> simp[create_expr_prefix_def] >> irule RTC_SINGLE >> simp[] >>
  map_every qexists_tac [`bb`, `i`] >> simp[] >> decide_tac
QED

Theorem cursor_init_confined_append[local]:
  create_expr_prefix st en explicit ctx func s [] v /\
  create_expr_prefix st en explicit ctx func v [] t ==>
  create_expr_prefix st en explicit ctx func s [] t
Proof
  simp[create_expr_prefix_def] >> metis_tac[RTC_TRANS]
QED

Theorem create_abi_cursor_init_confined:
  emit_op ALLOCA [Lit 32w] st = (cursor,mid) /\
  emit_void MSTORE [cursor; Lit (n2w hl)] mid = ((),en) /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32) /\
  FLOOKUP s.vs_allocas dst_site = SOME (dst_base,capacity) /\ dst_site < st.cs_next_id /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
     s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t slot p G' tn'.
    create_expr_prefix st en explicit ctx func s [] t /\
    cursor = Var p /\ not_fresh_at en p /\
    eval_operand cursor t = SOME (n2w slot) /\ ptr_covers G' tn' p t 32 /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (slot,32) /\ st.cs_next_id < en.cs_next_id /\
    FLOOKUP t.vs_allocas dst_site = SOME (dst_base,capacity) /\
    venomMemDefs$regions_disjoint (dst_base,capacity) (slot,32) /\
    slot + 32 <= t.vs_alloca_next /\ mem_word_at slot t.vs_memory = n2w hl /\
    (!i. slot <= i /\ i < slot + 32 ==> i NOTIN tn'.t_mem) /\
    window_phase ctx func st en {st.cs_next_id} [] s t /\ abi_encode_exec_frame func s t /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t /\
      t.vs_alloca_next + pending_alloca_size func t <= w2n t.vs_initial_fmp) /\
    (!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
      lookup_var x t = SOME w) /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem DIFF {i | slot <= i /\ i < slot + 32} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')
Proof
  strip_tac >> drule_all abi_encode_values_cursor_init_edges >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choose_then `t` (qx_choose_then `slot`
      (qx_choose_then `p` (qx_choose_then `G'` (qx_choose_then `tn'` strip_assume_tac)))))) >>
  drule emit_op_next_id >> drule emit_void_next_id >> rpt strip_tac >>
  rename1 `gas_origin_edge F explicit ctx func s [] (OK u)` >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME ai` >>
  rename1 `get_instruction bb u.vs_inst_idx = SOME si` >>
  `ai.inst_id IN frag_ids st en /\ si.inst_id IN frag_ids st en` by
    (simp[frag_ids_def] >> decide_tac) >>
  `s.vs_inst_idx < LENGTH en.cs_current_insts /\
   u.vs_inst_idx < LENGTH en.cs_current_insts` by
    (simp[ADD1] >> decide_tac) >>
  qexistsl_tac [`t`,`slot`,`p`,`G'`,`tn'`] >> asm_rewrite_tac[] >>
  irule cursor_init_confined_append >> qexists_tac `u` >>
  conj_tac >-
    (irule cursor_init_confined_step >> conj_tac >- first_assum ACCEPT_TAC >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`bb`, `ai`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  irule cursor_init_confined_step >> conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`bb`, `si`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
