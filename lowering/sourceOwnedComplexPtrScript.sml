(* Repeat-compatible navigation for the owned complex decoder fold. *)
Theory sourceOwnedComplexPtr
Ancestors sourceRecursiveComplexPtr sourceOwnedArrayConstructorPtr
  canonicalMemberTraversalPtr
  venomExecSemantics venomState abiDecoderMemberSetup abiDecoderContract
  decoderMemberPrefixPtr abiDecoderDynamicLoopSetup fragExec abiDecoderFrame emitHelper venomInst
  exprLoweringProps bodyPtrDefs list abiDecoderMemberCode abiDecoderLoop compileEnv arithmetic finite_map abiDecoderMemberCons
  abiDecoderCode abiEncoder emitHelperProps rich_list abiDecoderOffset
  abiDecoderOffsetHead abiDecoderCoherence vyperValue sourceEncodingLayout
  sourceEncodingWindows abiDecoderOffsetHead abiEncoderInput abiDecoderReentry
  venomMemDefs allocaFrontierBound actualAllocCredit calldataDynOwned
  abiEncoderSourceTransport abiDecoderMemberSlice decoderGhostFramePtr ptrDiscipline

Theorem member_navigation_opcode_frame[local]:
  MEM ins.inst_opcode [ADD; CALLDATALOAD] /\ step_inst_base ins s = OK t ==>
  t = s with vs_vars := t.vs_vars
Proof
  simp[] >> strip_tac
  >- metis_tac[step_pure_opcode_frame, MEM]
  >> gvs[step_inst_base_def, exec_read1_def, AllCaseEqs(), update_var_def] >>
     simp[venom_state_component_equality]
QED

Theorem member_navigation_opcodes[local]:
  abi_decode_member_setup dst src CALLDATALOAD (Lit 0w) (Lit 0w) dyn ao vo st = (ops,st') ==>
  EVERY (\i. MEM i.inst_opcode [ADD; CALLDATALOAD]) (emitted_insts st st')
Proof
  Cases_on `dyn` >>
  simp[abi_decode_member_setup_def, compile_getelemptr_abi_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    emit_void_def, fresh_var_def, fresh_id_def, emit_def, emitted_insts_def] >>
  strip_tac >> gvs[] >> pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  gvs[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem owned_member_navigation_ptr:
  abi_decode_member_setup (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    dyn ao vo sa = (ops,mid) /\
  lookup_var root s = SOME (n2w d) /\ d < dimword (:256) /\ not_fresh_at sa root /\
  abi_decoder_operand_live sa.cs_next_var src /\
  abi_decoder_operand_live sa.cs_next_var (Var root) /\
  (!q. src = Var q ==> not_fresh_at sa q) /\
  eval_operand src s = SOME (n2w srcpos) /\
  (dyn ==> abi_decode_load CALLDATALOAD (n2w (srcpos + ao) : bytes32) s = n2w off /\
    srcpos + off < dimword (:256)) /\
  ptr_covers G tn root s cap /\ op_taint tn src = {} /\ op_prov G src = NONE /\
  vo + C <= cap /\ d + vo < dimword (:256) /\
  mid.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s /\
  fn_has_code sa mid fn /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r H u q.
    abi_decode_sim ctx fn s r /\
    r.vs_current_bb = mid.cs_current_bb /\ r.vs_inst_idx = LENGTH mid.cs_current_insts /\
    abi_decoder_address_frame sa.cs_next_var s r /\ fresh_vars_wrt limit r /\
    (!op. abi_decoder_operand_live sa.cs_next_var op ==> eval_operand op r = eval_operand op s) /\
    abi_decoder_operand_live mid.cs_next_var (FST ops) /\
    abi_decoder_operand_live mid.cs_next_var (SND ops) /\
    SND ops = Var q /\ eval_operand (SND ops) r = SOME (n2w (d + vo)) /\
    eval_operand (FST ops) r = SOME (n2w (srcpos + if dyn then off else ao)) /\
    ptr_covers H u q r C /\ op_taint u (FST ops) = {} /\ op_prov H (FST ops) = NONE /\
    (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u r) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  `eval_operand (Var root) s = SOME (n2w d)` by simp[eval_operand_def] >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_member_setup_reentry >> strip_tac >>
  `t = s with vs_vars := t.vs_vars` by
    (`EVERY (\i. MEM i.inst_opcode [ADD; CALLDATALOAD]) (emitted_insts sa mid)` by
       metis_tac[member_navigation_opcodes] >>
     qspecl_then [`emitted_insts sa mid`, `K F`, `s`, `t`] mp_tac
       run_inst_seq_protected_frame >>
     (impl_tac >- (simp[] >> rpt strip_tac >>
       irule member_navigation_opcode_frame >>
       gvs[EVERY_MEM] >> metis_tac[])) >> simp[]) >>
  `w2n (n2w d : bytes32) + vo < dimword (:256)` by simp[] >>
  drule_all calldata_member_setup_endpoint_ptr_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  `frag_exec ctx sa mid (\s'. s' = s)
     (\r. r = t with vs_inst_idx := LENGTH mid.cs_current_insts) (K F)` by
    (irule frag_exec_run_inst_seq >> simp[] >>
     fs[EVERY_CONJ] >> metis_tac[]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> strip_tac >>
  `!op. abi_decoder_operand_live sa.cs_next_var op ==> eval_operand op t = eval_operand op s` by
    (qpat_assum `t = s with vs_vars := _` mp_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x t = _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> Cases_on `op` >>
     gvs[eval_operand_def, calldata_operand_live_not_fresh, venom_state_component_equality] >>
     metis_tac[]) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH mid.cs_current_insts`, `H`, `u`, `q`] >>
  gvs[abi_decoder_address_frame_def, fresh_vars_wrt_def, lookup_var_def,
    ptr_covers_def, eval_operand_def] >>
  `s with vs_inst_idx := LENGTH sa.cs_current_insts = s` by
    simp[venom_state_component_equality] >>
  qpat_x_assum `!D. (!fuel. ptr_safe_run D _ _ _ _ _ _ _ _) ==> _` mp_tac >>
  qpat_x_assum `s with vs_inst_idx := _ = s` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[ADD1, ADD_ASSOC, ADD_COMM]
QED

(* Interval composition is independent of decoder syntax.  P records the
   code-site certificate; the frontier bound is transported monotonically. *)
Theorem scratch_interval_chain:
  l <= m /\ m <= h /\ bnext <= cnext /\
  (!id p k. FLOOKUP a id = SOME (p,k) ==> FLOOKUP b id = SOME (p,k)) /\
  (!id p k. FLOOKUP b id = SOME (p,k) ==> FLOOKUP c id = SOME (p,k)) /\
  (!id. id < l \/ m <= id ==> FLOOKUP b id = FLOOKUP a id) /\
  (!id. id < m \/ h <= id ==> FLOOKUP c id = FLOOKUP b id) /\
  (!id p k. l <= id /\ id < m /\ FLOOKUP b id = SOME (p,k) ==>
    P id p k /\ p+k <= bnext) /\
  (!id p k. m <= id /\ id < h /\ FLOOKUP c id = SOME (p,k) ==>
    P id p k /\ p+k <= cnext) /\
  (!p k. MEM (p,k) fp ==> ?id. l <= id /\ id < m /\ FLOOKUP b id = SOME (p,k)) /\
  (!p k. MEM (p,k) gp ==> ?id. m <= id /\ id < h /\ FLOOKUP c id = SOME (p,k)) ==>
  (!id p k. FLOOKUP a id = SOME (p,k) ==> FLOOKUP c id = SOME (p,k)) /\
  (!id. id < l \/ h <= id ==> FLOOKUP c id = FLOOKUP a id) /\
  (!id p k. l <= id /\ id < h /\ FLOOKUP c id = SOME (p,k) ==>
    P id p k /\ p+k <= cnext) /\
  (!p k. MEM (p,k) (fp ++ gp) ==> ?id. l <= id /\ id < h /\ FLOOKUP c id = SOME (p,k))
Proof
  strip_tac >> conj_tac >- metis_tac[] >>
  conj_tac
  >- (gen_tac >> strip_tac >>
      `id < m \/ h <= id` by decide_tac >>
      `id < l \/ m <= id` by decide_tac >> metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> Cases_on `id < m`
      >- (`FLOOKUP b id = SOME (p,k)` by metis_tac[] >>
          `P id p k /\ p+k <= bnext` by metis_tac[] >>
          metis_tac[LESS_EQ_TRANS]) >>
      `m <= id` by decide_tac >> metis_tac[]) >>
  simp[MEM_APPEND] >> rpt gen_tac >> strip_tac
  >- (qpat_x_assum `!p k. MEM (p,k) fp ==> _` drule >> strip_tac >>
      qexists_tac `id` >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  qpat_x_assum `!p k. MEM (p,k) gp ==> _` drule >> strip_tac >>
  qexists_tac `id` >> metis_tac[LESS_EQ_TRANS]
QED

(* The owned fold carries semantic member sizes, not member_infos.  Its
   successor-code argument therefore works for arbitrary compiled triples. *)
Theorem complex_elems_child_exit_phi:
  compile_abi_decode_to_buf childdst childsrc opc (Lit 0w) hi di middle = ((),end_st) /\
  compile_abi_decode_complex_elems dst src opc (Lit 0w) hi elems ao vo end_st = ((),final) /\
  middle.cs_blocks = st.cs_blocks /\ abi_decode_source_opcode opc /\
  fn_has_code end_st final func /\
  (st.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) ==>
  middle.cs_blocks = end_st.cs_blocks \/
  !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  Cases_on `elems`
  >- (simp[Once compile_abi_decode_to_buf_def, comp_return_def] >> metis_tac[]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  PairCases_on `h` >>
  qpat_x_assum `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  rewrite_tac[abi_decode_complex_member_phases] >>
  simp_tac bool_ss [comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  drule_all abi_decoder_member_cons_code >> strip_tac >>
  drule_all abi_decoder_member_exit_phi >> simp[]
QED

(* The same endpoint carries source values, actual allocation ownership and
   the ghost.  Only future-limit freshness is required, including on reentry. *)
Theorem source_owned_complex_suffix_ptr:
  (!i mid en q childsrc r H u e srcpos.
    i < LENGTH tys /\
    compile_abi_decode_to_buf (Var q) childsrc CALLDATALOAD (Lit 0w) (Lit 0w)
      (type_to_abi_dec_info sf ce (EL i tys)) mid = ((),en) /\
    abi_decoder_coherent ce env sf (EL i tys) (EL i tvs) /\
    value_has_type (EL i tvs) (EL i vs) /\
    vyper_to_abi env (EL i tys) (EL i vs) = SOME (EL i avs) /\
    mem_bytes_at srcpos (LENGTH (enc (vyper_to_abi_type env (EL i tys)) (EL i avs)))
      r.vs_call_ctx.cc_calldata = enc (vyper_to_abi_type env (EL i tys)) (EL i avs) /\
    srcpos + LENGTH (enc (vyper_to_abi_type env (EL i tys)) (EL i avs)) < dimword (:256) /\
    eval_operand childsrc r = SOME (n2w srcpos) /\
    lookup_var q r = SOME (n2w e) /\ lookup_var root r = SOME (n2w d) /\
    abi_decoder_operand_live mid.cs_next_var childsrc /\
    abi_decoder_operand_live mid.cs_next_var (Var q) /\
    abi_decoder_operand_live mid.cs_next_var (Var root) /\
    ptr_covers H u q r (type_memory_size (EL i tvs)) /\
    ptr_covers H u root r cap /\ op_taint u childsrc = {} /\ op_prov H childsrc = NONE /\
    alloca_inv r /\ alloca_frontier_inv ctx fn site r /\
    unit_alloca_budget ctx < dimword (:256) /\
    FLOOKUP r.vs_allocas oid = SOME (base_addr,owner_cap) /\
    (oid < mid.cs_next_id \/ en.cs_next_id <= oid) /\
    base_addr <= e /\ e + type_memory_size (EL i tvs) <= base_addr + owner_cap /\
    e + type_memory_size (EL i tvs) < dimword (:256) /\
    (!id p sz. mid.cs_next_id <= id /\ id < en.cs_next_id /\
      FLOOKUP r.vs_allocas id = SOME (p,sz) ==>
      sz = 32 /\ p < dimword (:256) /\ p+32 <= r.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    fn_has_code mid en fn /\ fn_inst_ids_distinct fn /\
    (mid.cs_blocks = en.cs_blocks \/
      !bb. lookup_block en.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    en.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit r /\
    allocas_from lo r /\ lo <= r.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
    ~r.vs_halted /\ r.vs_current_bb = mid.cs_current_bb /\
    r.vs_inst_idx = LENGTH mid.cs_current_insts ==>
    ?t J v fp.
      abi_decode_sim ctx fn r t /\
      ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
      t.vs_inst_idx = LENGTH en.cs_current_insts /\ fresh_vars_wrt limit t /\
      val_in_memory (EL i tvs) (EL i vs) e t.vs_memory /\
      (!mem. mem_agree_outside v.t_mem t.vs_memory mem ==>
        val_in_memory (EL i tvs) (EL i vs) e mem) /\
      abi_decode_footprint_frame ((e,type_memory_size (EL i tvs))::fp) r t /\
      abi_footprint_disjoint base_addr owner_cap fp /\
      alloca_inv t /\ alloca_frontier_inv ctx fn site t /\ allocas_from lo t /\
      r.vs_alloca_next <= t.vs_alloca_next /\
      FLOOKUP t.vs_allocas oid = SOME (base_addr,owner_cap) /\
      (!id p sz. FLOOKUP r.vs_allocas id = SOME (p,sz) ==>
        FLOOKUP t.vs_allocas id = SOME (p,sz)) /\
      (!id. id < mid.cs_next_id \/ en.cs_next_id <= id ==>
        FLOOKUP t.vs_allocas id = FLOOKUP r.vs_allocas id) /\
      (!id p sz. mid.cs_next_id <= id /\ id < en.cs_next_id /\
        FLOOKUP t.vs_allocas id = SOME (p,sz) ==>
        sz = 32 /\ p < dimword (:256) /\ p+32 <= t.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      (!p sz. MEM (p,sz) fp ==> ?id. mid.cs_next_id <= id /\
        id < en.cs_next_id /\ FLOOKUP t.vs_allocas id = SOME (p,sz)) /\
      ptr_covers J v q t (type_memory_size (EL i tvs)) /\ ptr_covers J v root t cap /\
      (!op. abi_decoder_operand_live mid.cs_next_var op ==> eval_operand op t = eval_operand op r) /\
      (!x. not_fresh_at mid x ==> FLOOKUP J x = FLOOKUP H x /\
        op_taint v (Var x) = op_taint u (Var x)) /\
      v.t_mem SUBSET u.t_mem /\ v.t_stor = u.t_stor /\
      v.t_trans = u.t_trans /\ v.t_imm = u.t_imm /\
      (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG J v t) ==>
        !fuel. ptr_safe_run D lo fuel ctx fn PG H u r)) ==>
  !n k sa s G tn.
    LENGTH tys - k = n /\ k <= LENGTH tys /\
    LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
    LIST_REL value_has_type tvs vs /\ vyper_to_abi_list env tys vs = SOME avs /\
    ats = MAP (vyper_to_abi_type env) tys /\ LENGTH elems = LENGTH tys /\
    (!i. i < LENGTH tys ==>
      EL i elems = (type_to_abi_dec_info sf ce (EL i tys),
        abi_member_head_size (EL i ats), type_memory_size (EL i tvs))) /\
    compile_abi_decode_complex_elems (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
      (DROP k elems) (SUM (MAP abi_member_head_size (TAKE k ats)))
      (SUM (MAP type_memory_size (TAKE k tvs))) sa = ((),sb) /\
    mem_bytes_at cdsbase (LENGTH (enc (Tuple ats) (ListV avs))) s.vs_call_ctx.cc_calldata =
      enc (Tuple ats) (ListV avs) /\
    cdsbase + LENGTH (enc (Tuple ats) (ListV avs)) < dimword (:256) /\
    (!i. i < LENGTH tys ==> cdsbase + abi_tuple_child_offset ats avs i < dimword (:256)) /\
    lookup_var root s = SOME (n2w d) /\ not_fresh_at sa root /\
    abi_decoder_operand_live sa.cs_next_var src /\
    abi_decoder_operand_live sa.cs_next_var (Var root) /\
    (!q. src = Var q ==> not_fresh_at sa q) /\
    eval_operand src s = SOME (n2w cdsbase) /\ ptr_covers G tn root s cap /\
    op_taint tn src = {} /\ op_prov G src = NONE /\
    SUM (MAP type_memory_size tvs) <= cap /\ d + cap < dimword (:256) /\
    alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
    unit_alloca_budget ctx < dimword (:256) /\
    FLOOKUP s.vs_allocas oid = SOME (base_addr,owner_cap) /\
    (oid < sa.cs_next_id \/ sb.cs_next_id <= oid) /\
    base_addr <= d /\ d+cap <= base_addr+owner_cap /\
    (!id p sz. sa.cs_next_id <= id /\ id < sb.cs_next_id /\
      FLOOKUP s.vs_allocas id = SOME (p,sz) ==>
      sz = 32 /\ p < dimword (:256) /\ p+32 <= s.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
    (sa.cs_blocks = sb.cs_blocks \/
      !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    sb.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (!i. i < k ==> !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory (EL i tvs) (EL i vs)
        (d + SUM (MAP type_memory_size (TAKE i tvs))) mem) ==>
    ?t H u fp.
      abi_decode_sim ctx fn s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ fresh_vars_wrt limit t /\
      (!i. i < LENGTH tys ==>
        val_in_memory (EL i tvs) (EL i vs)
          (d + SUM (MAP type_memory_size (TAKE i tvs))) t.vs_memory /\
        (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
          val_in_memory (EL i tvs) (EL i vs)
            (d + SUM (MAP type_memory_size (TAKE i tvs))) mem)) /\
      abi_decode_footprint_frame ((d,cap)::fp) s t /\
      abi_footprint_disjoint base_addr owner_cap fp /\
      alloca_inv t /\ alloca_frontier_inv ctx fn site t /\ allocas_from lo t /\
      s.vs_alloca_next <= t.vs_alloca_next /\
      FLOOKUP t.vs_allocas oid = SOME (base_addr,owner_cap) /\
      (!id p sz. FLOOKUP s.vs_allocas id = SOME (p,sz) ==>
        FLOOKUP t.vs_allocas id = SOME (p,sz)) /\
      (!id. id < sa.cs_next_id \/ sb.cs_next_id <= id ==>
        FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
      (!id p sz. sa.cs_next_id <= id /\ id < sb.cs_next_id /\
        FLOOKUP t.vs_allocas id = SOME (p,sz) ==>
        sz = 32 /\ p < dimword (:256) /\ p+32 <= t.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      (!p sz. MEM (p,sz) fp ==> ?id. sa.cs_next_id <= id /\
        id < sb.cs_next_id /\ FLOOKUP t.vs_allocas id = SOME (p,sz)) /\
      ptr_covers H u root t cap /\
      (!op. abi_decoder_operand_live sa.cs_next_var op ==> eval_operand op t = eval_operand op s) /\
      (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
        op_taint u (Var x) = op_taint tn (Var x)) /\
      u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
      u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
      (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
        !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  disch_then (mk_asm "child") >> Induct
  >- (asm_x "child" kall_tac >> rpt gen_tac >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      `k = LENGTH tys /\ DROP k elems = []` by simp[DROP_EQ_NIL] >>
      `sa = sb` by
        (qpat_x_assum `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ _ = _` mp_tac >>
         asm_simp_tac bool_ss [Once compile_abi_decode_to_buf_def, comp_return_def,
           pairTheory.PAIR_EQ]) >>
      qpat_x_assum `sa = sb` SUBST_ALL_TAC >>
      qexistsl_tac [`s`, `G`, `tn`, `[]`] >>
      simp[NoAsms, abi_decode_sim_refl, abi_decode_footprint_frame_refl,
        abi_footprint_disjoint_def] >>
      map_every (fn pat => qpat_assum pat mp_tac)
        [`~s.vs_halted`, `s.vs_current_bb = _`, `s.vs_inst_idx = _`,
         `fresh_vars_wrt limit s`, `alloca_inv s`, `alloca_frontier_inv ctx fn site s`,
         `allocas_from lo s`, `FLOOKUP s.vs_allocas oid = _`,
         `ptr_covers G tn root s cap`, `k = LENGTH tys`, `!i. i < k ==> _`] >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
      simp[] >> conj_tac
      >- (rpt strip_tac >>
          qpat_x_assum `!i. i < k ==> _` (qspec_then `i` mp_tac) >>
          simp[mem_agree_outside_def]) >>
      rpt strip_tac >> gvs[]) >>
  suspend "step"
QED

Resume source_owned_complex_suffix_ptr[step]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!k sa s G tn. _` (mk_asm "ih") >>
  `k < LENGTH tys /\ SUC k <= LENGTH tys /\ LENGTH tys - SUC k = n` by decide_tac >>
  `LENGTH tvs = LENGTH tys /\ LENGTH ats = LENGTH tys` by
    (qpat_assum `LIST_REL (abi_decoder_coherent ce env sf) tys tvs` mp_tac >>
     qpat_assum `ats = _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[LIST_REL_LENGTH, LENGTH_MAP]) >>
  `DROP k elems = EL k elems :: DROP (SUC k) elems` by metis_tac[DROP_CONS_EL] >>
  `EL k elems = (type_to_abi_dec_info sf ce (EL k tys),
    abi_member_head_size (EL k ats), type_memory_size (EL k tvs))` by simp[] >>
  `abi_decoder_coherent ce env sf (EL k tys) (EL k tvs)` by
    (qpat_assum `LIST_REL (abi_decoder_coherent ce env sf) tys tvs` mp_tac >>
     simp[NoAsms, LIST_REL_EL_EQN] >> metis_tac[]) >>
  `dec_info_needs_offset (type_to_abi_dec_info sf ce (EL k tys)) = is_dynamic (EL k ats)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`abi_decoder_coherent ce env sf (EL k tys) (EL k tvs)`,
        `k < LENGTH tys`, `ats = _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     drule abi_decoder_nonempty_type_offset >>
     (impl_tac >-
       (`evaluate_type env (EL k tys) = SOME (EL k tvs)` by
          metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
        spose_not_then assume_tac >>
        `?elem. EL k tys = ArrayT elem (Fixed 0)` by
          metis_tac[abi_decoder_zero_array_type] >>
        gvs[evaluate_type_def, AllCaseEqs()])) >>
     simp[EL_MAP]) >>
  qpat_x_assum `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_assum `DROP k elems = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `EL k elems = _` (fn th => pure_rewrite_tac[th]) >>
  rewrite_tac[abi_decode_complex_member_phases] >>
  simp_tac bool_ss [comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> pop_assum (fn th => assume_tac th >> simp_tac std_ss [th]) >>
  pairarg_tac >> pop_assum (fn th => assume_tac th >> simp_tac std_ss [th]) >>
  strip_tac >>
  rename1 `abi_decode_member_setup (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w) _ _ _ sa = (ops,mid)` >>
  rename1 `compile_abi_decode_to_buf _ _ CALLDATALOAD (Lit 0w) (Lit 0w) _ mid = (z,en)` >>
  Cases_on `z` >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_member_cons_code >> strip_tac >>
  `fn_has_code sa mid fn /\ fn_has_code mid en fn` by
    (asm_x "child" kall_tac >> asm_x "ih" kall_tac >> metis_tac[fn_has_code_split]) >>
  suspend "navigate"
QED

Resume source_owned_complex_suffix_ptr[navigate]:
  qpat_x_assum `ats = _` SUBST_ALL_TAC >>
  qabbrev_tac `ats = MAP (vyper_to_abi_type env) tys` >>
  `SUM (MAP type_memory_size (TAKE k tvs)) + type_memory_size (EL k tvs) <= cap` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`SUM (MAP type_memory_size tvs) <= cap`, `k < LENGTH tys`,
        `LENGTH tvs = LENGTH tys`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     qspec_then `type_memory_size` mp_tac abi_encoder_prefix_sum_bound >>
     disch_then (qspecl_then [`tvs`, `k`] mp_tac) >> simp[]) >>
  `d < dimword (:256) /\ d + SUM (MAP type_memory_size (TAKE k tvs)) < dimword (:256) /\
   mid.cs_next_var <= limit.cs_next_var` by decide_tac >>
  drule_all coherent_source_list_head_lengths >> strip_tac >>
  `k < LENGTH ats` by simp[Abbr `ats`] >>
  `is_dynamic (EL k ats) ==>
    abi_decode_load CALLDATALOAD
      (n2w (cdsbase + SUM (MAP abi_member_head_size (TAKE k ats))) : bytes32) s =
      n2w (abi_tuple_child_offset ats avs k) /\
    cdsbase + abi_tuple_child_offset ats avs k < dimword (:256)` by
    (asm_x "child" kall_tac >> asm_x "ih" kall_tac >>
     strip_tac >> conj_tac >- (irule structural_tuple_indexed_offset_load >>
       metis_tac[abi_decode_source_def]) >> simp[]) >>
  qpat_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_assum `dec_info_needs_offset _ = _` (fn th => pure_rewrite_tac[th]) >> strip_tac >>
  drule_all owned_member_navigation_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  suspend "source_window"
QED

Resume source_owned_complex_suffix_ptr[source_window]:
  qpat_assum `abi_decoder_address_frame _ s r`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  `eval_operand (FST ops) r = SOME (n2w (cdsbase + abi_tuple_child_offset ats avs k))` by
    (qpat_assum `eval_operand (FST ops) r = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `is_dynamic (EL k ats)` >> simp[abi_tuple_child_offset_def]) >>
  `mem_bytes_at cdsbase (LENGTH (enc (Tuple ats) (ListV avs))) r.vs_call_ctx.cc_calldata =
    enc (Tuple ats) (ListV avs)` by
    (qpat_assum `r.vs_call_ctx = s.vs_call_ctx` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `LIST_REL (\ty av. ~is_dynamic ty ==> LENGTH (enc ty av) = abi_member_head_size ty) ats avs` by
    metis_tac[] >>
  drule_all structural_tuple_indexed_source >> strip_tac >>
  `ptr_covers H u root r cap` by
    (asm_x "child" kall_tac >> asm_x "ih" kall_tac >> metis_tac[ptr_covers_frame]) >>
  `alloca_inv r /\ alloca_frontier_inv ctx fn site r` by
    (asm_x "child" kall_tac >> asm_x "ih" kall_tac >>
     metis_tac[calldata_alloca_invariants_fields]) >>
  `allocas_from lo r /\ ~r.vs_halted /\ lo <= r.vs_alloca_next /\
    FLOOKUP r.vs_allocas oid = SOME (base_addr,owner_cap)` by
    (asm_x "child" kall_tac >> asm_x "ih" kall_tac >>
     metis_tac[allocas_from_def]) >>
  `lookup_var q r = SOME (n2w (d + SUM (MAP type_memory_size (TAKE k tvs)))) /\
    lookup_var root r = SOME (n2w d)` by
    (asm_x "child" kall_tac >> asm_x "ih" kall_tac >>
     metis_tac[eval_operand_def]) >>
  `abi_decoder_operand_live mid.cs_next_var (Var root)` by
    (asm_x "child" kall_tac >> asm_x "ih" kall_tac >>
     metis_tac[abi_decoder_operand_live_mono]) >>
  `value_has_type (EL k tvs) (EL k vs)` by
    (qpat_assum `LIST_REL value_has_type tvs vs` mp_tac >>
     qpat_assum `k < LENGTH tys` mp_tac >>
     qpat_assum `LENGTH tvs = LENGTH tys` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[LIST_REL_EL_EQN]) >>
  `vyper_to_abi env (EL k tys) (EL k vs) = SOME (EL k avs)` by
    (asm_x "child" kall_tac >> asm_x "ih" kall_tac >>
     drule abi_encoder_list_conversion >> strip_tac >> first_x_assum irule >> simp[]) >>
  suspend "child_resources"
QED

Resume source_owned_complex_suffix_ptr[child_resources]:
  `compile_abi_decode_to_buf (Var q) (FST ops) CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce (EL k tys)) mid = ((),en)` by
    (qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ mid = _` mp_tac >>
     qpat_assum `SND ops = Var q` (fn th => pure_rewrite_tac[th]) >>
     disch_then ACCEPT_TAC) >>
  `mem_bytes_at (cdsbase + abi_tuple_child_offset ats avs k)
    (LENGTH (enc (vyper_to_abi_type env (EL k tys)) (EL k avs))) r.vs_call_ctx.cc_calldata =
      enc (vyper_to_abi_type env (EL k tys)) (EL k avs) /\
   cdsbase + abi_tuple_child_offset ats avs k +
      LENGTH (enc (vyper_to_abi_type env (EL k tys)) (EL k avs)) < dimword (:256)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`mem_bytes_at (cdsbase + abi_tuple_child_offset ats avs k) _ _ = _`,
        `abi_tuple_child_offset ats avs k + _ <= _`,
        `cdsbase + LENGTH (enc (Tuple ats) (ListV avs)) < _`,
        `k < LENGTH tys`, `Abbrev (ats = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     gvs[Abbr `ats`, EL_MAP, Excl "enc_def"] >> decide_tac) >>
  `oid < mid.cs_next_id \/ en.cs_next_id <= oid` by decide_tac >>
  `base_addr <= d + SUM (MAP type_memory_size (TAKE k tvs)) /\
   d + SUM (MAP type_memory_size (TAKE k tvs)) + type_memory_size (EL k tvs) <=
     base_addr + owner_cap /\
   d + SUM (MAP type_memory_size (TAKE k tvs)) + type_memory_size (EL k tvs) < dimword (:256) /\
   en.cs_next_var <= limit.cs_next_var` by decide_tac >>
  `!id p sz. mid.cs_next_id <= id /\ id < en.cs_next_id /\
    FLOOKUP r.vs_allocas id = SOME (p,sz) ==>
    sz = 32 /\ p < dimword (:256) /\ p+32 <= r.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]` by
    (asm_x "child" kall_tac >> asm_x "ih" kall_tac >>
     rpt gen_tac >> strip_tac >>
     `sa.cs_next_id <= id /\ id < sb.cs_next_id` by decide_tac >>
     `FLOOKUP s.vs_allocas id = SOME (p,sz)` by metis_tac[] >>
     qpat_x_assum `!id p sz. sa.cs_next_id <= id /\ _ ==> _` (qspecl_then [`id`,`p`,`sz`] mp_tac) >>
     asm_simp_tac bool_ss []) >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  `mid.cs_blocks = en.cs_blocks \/
    !bb. lookup_block en.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0` by
    (asm_x "child" kall_tac >> asm_x "ih" kall_tac >>
     irule complex_elems_child_exit_phi >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at (Pat `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ _ = _`)) >>
     asm_rewrite_tac[]) >>
  `abi_decoder_operand_live mid.cs_next_var (Var q)` by
    (asm_x "child" kall_tac >> asm_x "ih" kall_tac >> metis_tac[]) >>
  asm "child" (qspec_then `k` (drule_at (Pos (el 2)))) >>
  disch_then (qspecl_then [`r`,`H`,`u`,
    `d + SUM (MAP type_memory_size (TAKE k tvs))`,
    `cdsbase + abi_tuple_child_offset ats avs k`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> suspend "prefix"
QED

Resume source_owned_complex_suffix_ptr[prefix]:
  markerLib.RESUME_TAC >>
  `abi_decode_footprint_frame
    ((d + SUM (MAP type_memory_size (TAKE k tvs)), type_memory_size (EL k tvs))::fp) s t` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`abi_decode_footprint_frame _ r t`, `r.vs_memory = s.vs_memory`,
        `r.vs_call_ctx = s.vs_call_ctx`, `r.vs_data_section = s.vs_data_section`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[abi_decode_footprint_frame_def]) >>
  `abi_footprint_disjoint d cap fp` by
    (qpat_assum `abi_footprint_disjoint base_addr owner_cap fp` mp_tac >>
     qpat_assum `base_addr <= d` mp_tac >>
     qpat_assum `d+cap <= base_addr+owner_cap` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[abi_footprint_disjoint_def] >>
     rpt strip_tac >> first_x_assum drule >> decide_tac) >>
  `abi_footprint_disjoint d (SUM (MAP type_memory_size (TAKE k tvs)))
    ((d + SUM (MAP type_memory_size (TAKE k tvs)), type_memory_size (EL k tvs))::fp)` by
    (qpat_assum `abi_footprint_disjoint d cap fp` mp_tac >>
     qpat_assum `SUM (MAP type_memory_size (TAKE k tvs)) + _ <= cap` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[abi_footprint_disjoint_def] >>
     rpt strip_tac >- simp[] >> first_x_assum drule >> decide_tac) >>
  `v.t_mem SUBSET tn.t_mem` by
    (asm_x "child" kall_tac >> asm_x "ih" kall_tac >> metis_tac[]) >>
  `!i. i < k ==>
    val_in_memory (EL i tvs) (EL i vs)
      (d + SUM (MAP type_memory_size (TAKE i tvs))) t.vs_memory /\
    (!mem. mem_agree_outside v.t_mem t.vs_memory mem ==>
      val_in_memory (EL i tvs) (EL i vs)
        (d + SUM (MAP type_memory_size (TAKE i tvs))) mem)` by
    (asm_x "child" kall_tac >> asm_x "ih" kall_tac >>
     gen_tac >> disch_tac >> irule decoded_tuple_prefix_footprint_frame >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`((d + SUM (MAP type_memory_size (TAKE k tvs)),
       type_memory_size (EL k tvs))::fp)`, `k`, `s`, `tn`] >>
     asm_rewrite_tac[] >> decide_tac) >>
  `!i. i < SUC k ==> !mem. mem_agree_outside v.t_mem t.vs_memory mem ==>
    val_in_memory (EL i tvs) (EL i vs)
      (d + SUM (MAP type_memory_size (TAKE i tvs))) mem` by
    (asm_x "child" kall_tac >> asm_x "ih" kall_tac >>
     rpt strip_tac >> Cases_on `i < k` >- metis_tac[] >>
     `i = k` by decide_tac >> metis_tac[]) >>
  suspend "tail"
QED


Resume source_owned_complex_suffix_ptr[tail]:
  markerLib.RESUME_TAC >>
  `!op. abi_decoder_operand_live sa.cs_next_var op ==>
    eval_operand op t = eval_operand op s` by
    (asm_x "child" kall_tac >> asm_x "ih" kall_tac >> rpt strip_tac >>
     qpat_assum `!op. abi_decoder_operand_live mid.cs_next_var op ==> _`
       (qspec_then `op` mp_tac) >>
     (impl_tac >- metis_tac[abi_decoder_operand_live_mono]) >>
     qpat_assum `!op. abi_decoder_operand_live sa.cs_next_var op ==> _`
       (qspec_then `op` mp_tac) >>
     qpat_assum `abi_decoder_operand_live sa.cs_next_var op` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> FLOOKUP J x = FLOOKUP G x /\
    op_taint v (Var x) = op_taint tn (Var x)` by
    (asm_x "child" kall_tac >> asm_x "ih" kall_tac >> rpt strip_tac >>
     `not_fresh_at mid x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     qpat_assum `!x. not_fresh_at mid x ==> _` (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x r = _ /\ _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  `lookup_var root t = SOME (n2w d) /\ eval_operand src t = SOME (n2w cdsbase)` by
    (asm_x "child" kall_tac >> asm_x "ih" kall_tac >>
     qpat_assum `!op. abi_decoder_operand_live sa.cs_next_var op ==> eval_operand op t = _`
       (fn th => mp_tac (Q.SPEC `Var root` th) >> mp_tac (Q.SPEC `src` th)) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`abi_decoder_operand_live sa.cs_next_var src`,
        `abi_decoder_operand_live sa.cs_next_var (Var root)`,
        `lookup_var root s = _`, `eval_operand src s = _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[eval_operand_def]) >>
  suspend "tail_resources"
QED

Resume source_owned_complex_suffix_ptr[tail_resources]:
  markerLib.RESUME_TAC >>
  `sa.cs_next_var <= en.cs_next_var` by decide_tac >>
  `not_fresh_at en root /\ (!q. src = Var q ==> not_fresh_at en q)` by
    (asm_x "child" kall_tac >> asm_x "ih" kall_tac >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `abi_decoder_operand_live en.cs_next_var src /\
   abi_decoder_operand_live en.cs_next_var (Var root)` by
    (asm_x "child" kall_tac >> asm_x "ih" kall_tac >>
     metis_tac[abi_decoder_operand_live_mono]) >>
  `op_taint v src = {} /\ op_prov J src = NONE` by
    (qpat_assum `!x. not_fresh_at sa x ==> FLOOKUP J x = _ /\ _` mp_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`!q. src = Var q ==> not_fresh_at sa q`, `op_taint tn src = _`, `op_prov G src = _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `src` >>
     simp[op_taint_def, op_prov_def] >> metis_tac[]) >>
  `mem_bytes_at cdsbase (LENGTH (enc (Tuple ats) (ListV avs))) t.vs_call_ctx.cc_calldata =
    enc (Tuple ats) (ListV avs)` by
    (qpat_assum `abi_decode_footprint_frame _ s t` mp_tac >>
     qpat_assum `mem_bytes_at cdsbase _ s.vs_call_ctx.cc_calldata = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[abi_decode_footprint_frame_def]) >>
  `en.cs_blocks = sb.cs_blocks \/
    !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0` by
    (asm_x "child" kall_tac >> asm_x "ih" kall_tac >>
     irule abi_decoder_members_tail_phi >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> first_assum ACCEPT_TAC) >>
  `oid < en.cs_next_id \/ sb.cs_next_id <= oid` by decide_tac >>
  `lo <= t.vs_alloca_next` by decide_tac >>
  suspend "tail_slots"
QED

Resume source_owned_complex_suffix_ptr[tail_slots]:
  markerLib.RESUME_TAC >>
  `!id p sz. en.cs_next_id <= id /\ id < sb.cs_next_id /\
    FLOOKUP t.vs_allocas id = SOME (p,sz) ==>
    sz = 32 /\ p < dimword (:256) /\ p+32 <= t.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]` by
    (asm_x "child" kall_tac >> asm_x "ih" kall_tac >>
     rpt gen_tac >> strip_tac >>
     `sa.cs_next_id <= id /\ en.cs_next_id <= id` by decide_tac >>
     `FLOOKUP s.vs_allocas id = SOME (p,sz)` by
       (qpat_assum `!id. id < mid.cs_next_id \/ en.cs_next_id <= id ==> _`
          (qspec_then `id` mp_tac) >>
        qpat_assum `r.vs_allocas = s.vs_allocas` mp_tac >>
        qpat_assum `FLOOKUP t.vs_allocas id = _` mp_tac >>
        qpat_assum `en.cs_next_id <= id` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
     qpat_assum `!id p sz. sa.cs_next_id <= id /\ _ ==> _`
       (qspecl_then [`id`,`p`,`sz`] mp_tac) >>
     (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
     asm_rewrite_tac[] >> conj_tac >- decide_tac >>
     qexists_tac `ins` >> asm_rewrite_tac[]) >>
  `SUM (MAP abi_member_head_size (TAKE (SUC k) ats)) =
     SUM (MAP abi_member_head_size (TAKE k ats)) + abi_member_head_size (EL k ats) /\
   SUM (MAP type_memory_size (TAKE (SUC k) tvs)) =
     SUM (MAP type_memory_size (TAKE k tvs)) + type_memory_size (EL k tvs)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`k < LENGTH tys`, `LENGTH ats = LENGTH tys`, `LENGTH tvs = LENGTH tys`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     simp[TAKE_SUC_BY_TAKE, MAP_SNOC, SUM_SNOC]) >>
  asm "ih" (qspec_then `SUC k` mp_tac) >>
  disch_then (qspecl_then [`en`, `t`, `J`, `v`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> simp[Abbr `ats`])) >> strip_tac >>
  suspend "compose"
QED

Resume source_owned_complex_suffix_ptr[compose]:
  markerLib.RESUME_TAC >>
  asm_x "child" kall_tac >> asm_x "ih" kall_tac >>
  `abi_decode_footprint_frame ((d,cap)::(fp ++ fp')) s t` by
    (irule abi_decode_footprint_frame_weaken >>
     qexists_tac `((d + SUM (MAP type_memory_size (TAKE k tvs)),
       type_memory_size (EL k tvs))::fp)` >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     simp[NoAsms] >>
     rpt gen_tac >> strip_tac
     >- (qexistsl_tac [`d`, `cap`] >> simp[NoAsms] >> decide_tac) >>
     qexistsl_tac [`d'`, `sz`] >> simp[NoAsms, MEM_APPEND] >>
     metis_tac[]) >>
  `abi_decode_footprint_frame ((d,cap)::(fp ++ fp')) t t'` by
    (irule abi_decode_footprint_frame_weaken >>
     qexists_tac `((d,cap)::fp')` >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     simp[NoAsms] >>
     rpt gen_tac >> strip_tac
     >- (qexistsl_tac [`d`, `cap`] >> simp[NoAsms] >> decide_tac) >>
     qexistsl_tac [`d'`, `sz`] >> simp[NoAsms, MEM_APPEND] >>
     metis_tac[]) >>
  suspend "compose_resources"
QED

Resume source_owned_complex_suffix_ptr[compose_resources]:
  markerLib.RESUME_TAC >>
  `!id p sz. FLOOKUP s.vs_allocas id = SOME (p,sz) ==>
    FLOOKUP t.vs_allocas id = SOME (p,sz)` by
    (rpt strip_tac >>
     qpat_assum `!id p sz. FLOOKUP r.vs_allocas id = _ ==> _` irule >>
     qpat_assum `r.vs_allocas = s.vs_allocas` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `!id. id < sa.cs_next_id \/ en.cs_next_id <= id ==>
    FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id` by
    (rpt strip_tac >>
     `id < mid.cs_next_id \/ en.cs_next_id <= id` by decide_tac >>
     qpat_assum `!id. id < mid.cs_next_id \/ en.cs_next_id <= id ==> _`
       (qspec_then `id` mp_tac) >>
     (impl_tac >- decide_tac) >>
     qpat_assum `r.vs_allocas = s.vs_allocas` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  suspend "interval"
QED

Resume source_owned_complex_suffix_ptr[interval]:
  markerLib.RESUME_TAC >>
  `!id p sz. sa.cs_next_id <= id /\ id < en.cs_next_id /\
    FLOOKUP t.vs_allocas id = SOME (p,sz) ==>
    sz = 32 /\ p < dimword (:256) /\ p+32 <= t.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]` by
    (rpt gen_tac >> strip_tac >> Cases_on `mid.cs_next_id <= id`
     >- (qpat_assum `!id p sz. mid.cs_next_id <= id /\ _ ==> _` irule >>
         asm_rewrite_tac[]) >>
     `id < mid.cs_next_id /\ id < sb.cs_next_id` by decide_tac >>
     `FLOOKUP s.vs_allocas id = SOME (p,sz)` by
       (qpat_assum `!id. id < mid.cs_next_id \/ en.cs_next_id <= id ==> _`
          (qspec_then `id` mp_tac) >>
        (impl_tac >- decide_tac) >>
        qpat_assum `r.vs_allocas = s.vs_allocas` mp_tac >>
        qpat_assum `FLOOKUP t.vs_allocas id = _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
     qpat_assum `!id p sz. sa.cs_next_id <= id /\ _ ==> _`
       (qspecl_then [`id`,`p`,`sz`] mp_tac) >>
     (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
     asm_rewrite_tac[] >> conj_tac >- decide_tac >>
     qexists_tac `ins` >> asm_rewrite_tac[]) >>
  suspend "chain"
QED

Resume source_owned_complex_suffix_ptr[chain]:
  markerLib.RESUME_TAC >>
  `!p sz. MEM (p,sz) fp ==> ?id. sa.cs_next_id <= id /\
    id < en.cs_next_id /\ FLOOKUP t.vs_allocas id = SOME (p,sz)` by
    (rpt strip_tac >>
     qpat_assum `!p sz. MEM (p,sz) fp ==> _` drule >> strip_tac >>
     qexists_tac `id` >> asm_rewrite_tac[] >> decide_tac) >>
  `(!id p sz. FLOOKUP s.vs_allocas id = SOME (p,sz) ==>
      FLOOKUP t'.vs_allocas id = SOME (p,sz)) /\
   (!id. id < sa.cs_next_id \/ sb.cs_next_id <= id ==>
      FLOOKUP t'.vs_allocas id = FLOOKUP s.vs_allocas id) /\
   (!id p sz. sa.cs_next_id <= id /\ id < sb.cs_next_id /\
      FLOOKUP t'.vs_allocas id = SOME (p,sz) ==>
      (sz = 32 /\ p < dimword (:256) /\
       ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
         ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      p+sz <= t'.vs_alloca_next) /\
   (!p sz. MEM (p,sz) (fp ++ fp') ==> ?id. sa.cs_next_id <= id /\
      id < sb.cs_next_id /\ FLOOKUP t'.vs_allocas id = SOME (p,sz))` by
    (ho_match_mp_tac (Q.INST
       [`m` |-> `en.cs_next_id`, `b` |-> `t.vs_allocas`,
        `bnext` |-> `t.vs_alloca_next`] scratch_interval_chain) >>
     asm_rewrite_tac[] >> conj_tac >- decide_tac >>
     conj_tac
     >- (rpt gen_tac >> strip_tac >>
         qpat_assum `!id p sz. sa.cs_next_id <= id /\ _ ==> _` drule_all >>
         strip_tac >> asm_rewrite_tac[] >> qexists_tac `ins` >> asm_rewrite_tac[]) >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `!id p sz. en.cs_next_id <= id /\ _ ==> _` drule_all >>
     strip_tac >> asm_rewrite_tac[] >> qexists_tac `ins` >> asm_rewrite_tac[]) >>
  suspend "endpoint"
QED

Resume source_owned_complex_suffix_ptr[endpoint]:
  rpt (CHANGED_TAC markerLib.RESUME_TAC) >> (
  qexistsl_tac [`t'`, `H'`, `u'`, `fp ++ fp'`] >>
  conj_tac
  >- (irule abi_decode_sim_trans >> qexists_tac `t` >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      irule abi_decode_sim_trans >> qexists_tac `r` >>
      asm_rewrite_tac[]) >>
  asm_rewrite_tac[] >>
  conj_tac
  >- (irule abi_decode_footprint_frame_trans >> qexists_tac `t` >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (map_every (fn pat => qpat_assum pat mp_tac)
        [`abi_footprint_disjoint base_addr owner_cap fp`,
         `abi_footprint_disjoint base_addr owner_cap fp'`] >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp[abi_footprint_disjoint_def, MEM_APPEND] >> metis_tac[]) >>
  conj_tac >- decide_tac >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!id p sz. sa.cs_next_id <= id /\ _ ==> (_ /\ _) /\ _`
        drule_all >> strip_tac >> asm_rewrite_tac[] >>
      conj_tac >- decide_tac >> qexists_tac `ins` >> asm_rewrite_tac[]) >>
  suspend "frames")
QED

Resume source_owned_complex_suffix_ptr[frames]:
  rpt (CHANGED_TAC markerLib.RESUME_TAC) >> (
  conj_tac
  >- (rpt strip_tac >>
      `abi_decoder_operand_live mid.cs_next_var op /\
       abi_decoder_operand_live en.cs_next_var op` by
        metis_tac[abi_decoder_operand_live_mono] >>
      qpat_assum `!op. abi_decoder_operand_live en.cs_next_var op ==> _`
        (qspec_then `op` mp_tac) >>
      qpat_assum `!op. abi_decoder_operand_live mid.cs_next_var op ==> _`
        (qspec_then `op` mp_tac) >>
      qpat_assum `!op. abi_decoder_operand_live sa.cs_next_var op ==> _`
        (qspec_then `op` mp_tac) >>
      asm_rewrite_tac[] >> metis_tac[]) >>
  suspend "ghost_frames")
QED

