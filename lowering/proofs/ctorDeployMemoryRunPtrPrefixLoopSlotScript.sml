(* Same-endpoint index-slot allocation and initialization boundaries. *)
Theory ctorDeployMemoryRunPtrPrefixLoopSlot
Ancestors
  ctorDeployMemoryRunPtrPrefixAllocationFloor
  ctorDeployMemoryRunPtrPrefixSteps ctorDeployMemoryRunPtrPrefixBoolBody
  ctorDeployMemoryRunPtrPrefixSequence
  abiDecoderArrayLoopInit abiDecoderFrame venomMemProps valueEncodingProps instIdxIndep exprLoweringProps
  ptrSafeRun ptrDiscipline venomState venomExecSemantics venomInst
  finite_map words arithmetic pred_set list memLocDefs codegenRel

Theorem prefix_loop_slot_reuse_ghost:
  FLOOKUP s.vs_allocas aid = SOME (p,32) ==>
  let i = mk_inst aid ALLOCA [Lit 32w] [ip];
      a = update_var ip (n2w p) s
  in step_inst_base i s = OK a /\
     ghost_step fuel ctx PG G tn i s =
       (G |+ (ip,(p,32)),step_taint i s a tn)
Proof
  strip_tac >>
  simp[step_inst_base_def, mk_inst_def, exec_alloca_def, eval_operand_def,
    ghost_step_def, step_inst_non_invoke, step_prov_def, set_prov_def,
    out_prov_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem prefix_loop_slot_reuse_taint:
  let i = mk_inst aid ALLOCA [Lit 32w] [ip];
      a = update_var ip (n2w p) s
  in step_taint i s a tn = tn with t_var := tn.t_var |+ (ip,{})
Proof
  simp[step_taint_def, mk_inst_def, set_var_taint_def, out_taint_def,
    mem_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
    new_site_bytes_def, step_writes_def, written_taint_def,
    source_memory_write_ranges_def, range_bytes_def, update_var_def,
    eval_operand_def, EXTENSION, taint_component_equality, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem prefix_loop_slot_fresh_taint:
  FLOOKUP s.vs_allocas aid = NONE ==>
  let i = mk_inst aid ALLOCA [Lit 32w] [ip];
      a = update_var ip (n2w s.vs_alloca_next)
        (s with <|vs_allocas := s.vs_allocas |+
          (aid,(s.vs_alloca_next,32));
          vs_alloca_next := s.vs_alloca_next+32|>)
  in step_taint i s a tn =
    tn with <|t_var := tn.t_var |+ (ip,{});
      t_mem := tn.t_mem UNION {j | s.vs_alloca_next <= j /\ j < s.vs_alloca_next+32}|>
Proof
  strip_tac >>
  simp[step_taint_def, mk_inst_def, set_var_taint_def, out_taint_def,
    mem_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
    new_site_bytes_def, step_writes_def, written_taint_def,
    source_memory_write_ranges_def, range_bytes_def, update_var_def,
    eval_operand_def, EXTENSION, taint_component_equality, FLOOKUP_UPDATE] >>
  fs[FLOOKUP_DEF] >> simp[AllCaseEqs()] >> metis_tac[]
QED

Theorem prefix_loop_slot_zero_pair:
  eval_operand (Var ip) a = SOME (n2w p) /\ p < dimword (:256) /\
  FLOOKUP H ip = SOME (p,32) /\ op_taint q (Var ip) = {} /\
  allocas_from lo a /\ lo <= a.vs_alloca_next /\ ~ctx_has_dalloca ctx ==>
  let j = mk_inst iid MSTORE [Var ip;Lit 0w] [];
      t = mstore p 0w a;
      qt = step_taint j a t q
  in step_inst_base j a = OK t /\
     ghost_step fuel ctx PG H q j a = (H,qt) /\
     ptr_safe_step D lo fuel ctx fn PG H q j a /\
     eval_operand (Var ip) t = SOME (n2w p) /\
     op_taint qt (Var ip) = {} /\
     qt.t_mem = q.t_mem DIFF {b | p <= b /\ b < p+32} /\
     qt.t_stor = q.t_stor /\ qt.t_trans = q.t_trans /\ qt.t_imm = q.t_imm /\
     allocas_from lo t /\ lo <= t.vs_alloca_next /\
     (!v. op_taint qt (Var v) = op_taint q (Var v))
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  `step_inst_base (mk_inst iid MSTORE [Var ip;Lit 0w] []) a = OK (mstore p 0w a)` by
    (drule prefix_mstore_step >>
     disch_then (qspecl_then [`iid`,`Lit 0w`,`0w`] mp_tac) >>
     simp[eval_operand_def]) >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac >-
    (irule prefix_mstore_ghost_step >> simp[step_inst_non_invoke, mk_inst_def] >>
     pure_rewrite_tac[GSYM mk_inst_def] >> asm_rewrite_tac[]) >>
  conj_tac >-
    (irule prefix_mstore_ptr_step >>
     fs[op_taint_def, eval_operand_def] >> metis_tac[w2n_n2w]) >>
  `!v. op_taint (step_taint (mk_inst iid MSTORE [Var ip;Lit 0w] [])
       a (mstore p 0w a) q) (Var v) = op_taint q (Var v)` by
    simp[SRULE [LET_THM] prefix_mstore_taint_frame, op_taint_def] >>
  `((step_taint (mk_inst iid MSTORE [Var ip;Lit 0w] [])
       a (mstore p 0w a) q).t_mem) = q.t_mem DIFF {b | p <= b /\ b < p+32}` by
    (mp_tac prefix_mstore_mem_taint >>
     disch_then (qspecl_then [`iid`,`Var ip`,`Lit 0w`,`a`,`n2w p`,`0w`,`q`] mp_tac) >>
     simp[eval_operand_def, op_taint_def]) >>
  simp[SRULE [LET_THM] prefix_mstore_taint_frame, mstore_def, write_memory_def,
    allocas_from_def, eval_operand_def, lookup_var_def] >>
  fs[eval_operand_def, lookup_var_def, allocas_from_def] >> metis_tac[]
QED

Theorem prefix_loop_slot_alloc_pair:
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst aid ALLOCA [Lit 32w] [ip]) s = OK a /\
  FLOOKUP a.vs_allocas aid = SOME (p,32) ==>
  let i = mk_inst aid ALLOCA [Lit 32w] [ip];
      H = G |+ (ip,(p,32));
      q = step_taint i s a tn
  in ghost_step fuel ctx PG G tn i s = (H,q) /\
     ptr_safe_step D lo fuel ctx fn PG G tn i s /\
     eval_operand (Var ip) a = SOME (n2w p) /\
     op_taint q (Var ip) = {} /\
     allocas_from lo a /\ lo <= a.vs_alloca_next /\ lo <= p /\
     q.t_mem SUBSET tn.t_mem UNION {b | p <= b /\ b < p+32} /\
     q.t_stor = tn.t_stor /\ q.t_trans = tn.t_trans /\ q.t_imm = tn.t_imm /\
     (!v. v <> ip ==> FLOOKUP H v = FLOOKUP G v /\
       eval_operand (Var v) a = eval_operand (Var v) s /\
       op_taint q (Var v) = op_taint tn (Var v)) /\
     a.vs_memory = s.vs_memory
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  conj_tac >-
    (simp[ghost_step_def, step_inst_non_invoke, mk_inst_def] >>
     pure_rewrite_tac[GSYM mk_inst_def] >> asm_rewrite_tac[] >>
     simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def]) >>
  conj_tac >- (irule prefix_alloca_ptr_step >> simp[]) >>
  Cases_on `FLOOKUP s.vs_allocas aid`
  >- (`32 < dimword (:256)` by (CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> EVAL_TAC) >>
      gvs[prefix_alloca_step] >>
      simp[SRULE [LET_THM] prefix_loop_slot_fresh_taint] >>
      gvs[update_var_def, FLOOKUP_UPDATE] >>
      simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
        op_taint_def, SUBSET_DEF, allocas_from_def] >>
      rpt strip_tac >> gvs[] >>
      fs[allocas_from_def, AllCaseEqs()] >> metis_tac[]) >>
  PairCases_on `x` >>
  gvs[step_inst_base_def, mk_inst_def, exec_alloca_def, eval_operand_def,
    update_var_def, FLOOKUP_UPDATE] >>
  pure_rewrite_tac[GSYM update_var_def, GSYM mk_inst_def] >>
  simp[SRULE [LET_THM] prefix_loop_slot_reuse_taint] >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
    op_taint_def, SUBSET_DEF, allocas_from_def] >>
  fs[allocas_from_def] >> metis_tac[]
QED

Theorem prefix_loop_slot_taint_idx:
  MEM i.inst_opcode [ALLOCA;MSTORE] ==>
  step_taint i (s with vs_inst_idx := k) (t with vs_inst_idx := k) tn =
  step_taint i s t tn
Proof
  strip_tac >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
    written_taint_def, out_taint_def, store_taint_def, imm_taint_def,
    source_memory_write_ranges_def, fixed_source_write_range_def,
    eval_op_inst_idx]
QED

Theorem prefix_loop_slot_zero_block:
  eval_operand (Var ip) a = SOME (n2w p) /\ p < dimword (:256) /\
  FLOOKUP H ip = SOME (p,32) /\ op_taint q (Var ip) = {} /\
  allocas_from lo a /\ lo <= a.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  get_instruction bb a.vs_inst_idx = SOME (mk_inst iid MSTORE [Var ip;Lit 0w] []) ==>
  (ptr_safe_block D lo fuel ctx fn PG H
     (step_taint (mk_inst iid MSTORE [Var ip;Lit 0w] []) a (mstore p 0w a) q)
     bb ((mstore p 0w a) with vs_inst_idx := SUC a.vs_inst_idx) ==>
   ptr_safe_block D lo fuel ctx fn PG H q bb a)
Proof
  strip_tac >>
  drule_all prefix_loop_slot_zero_pair >>
  disch_then (qspecl_then [`iid`,`fuel`,`fn`,`PG`,`D`] mp_tac) >>
  simp[] >> strip_tac >>
  `step_inst fuel ctx (mk_inst iid MSTORE [Var ip;Lit 0w] []) a =
     OK (mstore p 0w a)` by
    (simp[step_inst_non_invoke, mk_inst_def] >>
     pure_rewrite_tac[GSYM mk_inst_def] >> asm_rewrite_tac[]) >>
  `~is_terminator (mk_inst iid MSTORE [Var ip;Lit 0w] []).inst_opcode` by
    simp[mk_inst_def,is_terminator_def] >>
  drule_all ptr_safe_block_step >> simp[]
QED

Theorem prefix_loop_index_slot_pair:
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  run_inst_seq [mk_inst aid ALLOCA [Lit 32w] [ip];
    mk_inst (aid+1) MSTORE [Var ip;Lit 0w] []] s = OK t /\
  FLOOKUP t.vs_allocas aid = SOME (p,32) /\ p < dimword (:256) ==>
  ?H qt.
    FLOOKUP H ip = SOME (p,32) /\
    eval_operand (Var ip) t = SOME (n2w p) /\ op_taint qt (Var ip) = {} /\
    DISJOINT qt.t_mem {b | p <= b /\ b < p+32} /\ qt.t_mem SUBSET tn.t_mem /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\ lo <= p /\
    (!v. v <> ip ==> FLOOKUP H v = FLOOKUP G v /\
      eval_operand (Var v) t = eval_operand (Var v) s /\
      op_taint qt (Var v) = op_taint tn (Var v)) /\
    mload p t = 0w /\
    (!b n. b+n <= p \/ p+32 <= b ==>
      mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory) /\
    t.vs_current_bb = s.vs_current_bb /\
    (!fuel bb.
      get_instruction bb s.vs_inst_idx = SOME (mk_inst aid ALLOCA [Lit 32w] [ip]) /\
      get_instruction bb (SUC s.vs_inst_idx) =
        SOME (mk_inst (aid+1) MSTORE [Var ip;Lit 0w] []) ==>
      ptr_safe_block D lo fuel ctx fn PG H qt bb (t with vs_inst_idx := s.vs_inst_idx+2) ==>
      ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  strip_tac >>
  fs[run_inst_seq_def, AllCaseEqs()] >> rename1 `step_inst_base _ s = OK a` >>
  `eval_operand (Var ip) a = SOME (n2w p) /\
   FLOOKUP a.vs_allocas aid = SOME (p,32)` by suspend "allocation_lookup" >>
  drule_all prefix_loop_slot_alloc_pair >>
  disch_then (qspecl_then [`tn`,`fuel`,`fn`,`PG`,`G`,`D`] mp_tac) >>
  simp[] >> strip_tac >>
  qabbrev_tac `H = G |+ (ip,(p,32))` >>
  qabbrev_tac `q = step_taint (mk_inst aid ALLOCA [Lit 32w] [ip]) s a tn` >>
  `t = mstore p 0w a` by suspend "store_endpoint" >>
  `FLOOKUP H ip = SOME (p,32)` by simp[Abbr `H`,FLOOKUP_UPDATE] >>
  drule_all (SRULE [] prefix_loop_slot_zero_pair) >>
  disch_then (qspecl_then [`aid+1`,`fuel`,`fn`,`PG`,`D`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`H`,`step_taint (mk_inst (aid+1) MSTORE [Var ip;Lit 0w] []) a t q`] >>
  reverse conj_tac >- suspend "continuation" >>
  suspend "observations"
QED

Resume prefix_loop_index_slot_pair[allocation_lookup]:
  qpat_x_assum `step_inst_base (mk_inst _ MSTORE _ _) _ = _` mp_tac >>
  simp[step_inst_base_def, mk_inst_def, exec_write2_def,
    eval_operand_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[mstore_def, write_memory_def] >>
  Cases_on `FLOOKUP s.vs_allocas aid`
  >- gvs[prefix_alloca_step, update_var_def, FLOOKUP_UPDATE,
          eval_operand_def, lookup_var_def] >>
  PairCases_on `x` >>
  gvs[step_inst_base_def, mk_inst_def, exec_alloca_def, eval_operand_def,
    update_var_def, FLOOKUP_UPDATE, lookup_var_def]
QED

Resume prefix_loop_index_slot_pair[store_endpoint]:
  drule prefix_mstore_step >>
  disch_then (qspecl_then [`aid+1`,`Lit 0w`,`0w`] mp_tac) >>
  simp[eval_operand_def] >> strip_tac >> gvs[]
QED

Resume prefix_loop_index_slot_pair[observations]:
  asm_rewrite_tac[]
QED

Resume prefix_loop_index_slot_pair[continuation]:
  asm_rewrite_tac[] >>
  conj_tac >- SET_TAC[] >>
  conj_tac >- (fs[SUBSET_DEF] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- simp[mload_mstore_same] >>
  conj_tac >-
    (rpt strip_tac >>
     `mem_bytes_at b n (mstore p 0w a).vs_memory = mem_bytes_at b n a.vs_memory` by
       (irule mstore_mem_bytes_at_disjoint >> simp[]) >>
     simp[]) >>
  conj_tac >-
    (qpat_x_assum `step_inst_base (mk_inst _ ALLOCA _ _) _ = _` mp_tac >>
     simp[step_inst_base_def,mk_inst_def,exec_alloca_def,eval_operand_def] >>
     Cases_on `FLOOKUP s.vs_allocas aid`
     >- (simp[update_var_def,mstore_def,write_memory_def] >> strip_tac >> gvs[]) >>
     PairCases_on `x` >> simp[update_var_def,mstore_def,write_memory_def] >>
     strip_tac >> gvs[]) >>
  map_every qx_gen_tac [`f`,`bb`] >> strip_tac >> strip_tac >>
  `step_inst f ctx (mk_inst aid ALLOCA [Lit 32w] [ip]) s = OK a` by
    (simp[step_inst_non_invoke,mk_inst_def] >>
     pure_rewrite_tac[GSYM mk_inst_def] >> asm_rewrite_tac[]) >>
  `ghost_step f ctx PG G tn (mk_inst aid ALLOCA [Lit 32w] [ip]) s = (H,q)` by
    (qpat_x_assum `ghost_step _ _ _ _ _ (mk_inst _ ALLOCA _ _) _ = _` mp_tac >>
     simp[ghost_step_def,step_inst_non_invoke,mk_inst_def]) >>
  `ptr_safe_step D lo f ctx fn PG G tn (mk_inst aid ALLOCA [Lit 32w] [ip]) s` by
    (irule prefix_alloca_ptr_step >> simp[]) >>
  `~is_terminator (mk_inst aid ALLOCA [Lit 32w] [ip]).inst_opcode` by
    simp[mk_inst_def,is_terminator_def] >>
  drule_all ptr_safe_block_step >>
  disch_then (fn th => once_rewrite_tac[th]) >> asm_rewrite_tac[] >>
  irule (Q.INST [`p` |-> `p`, `iid` |-> `aid+1`] prefix_loop_slot_zero_block) >>
  simp[eval_op_inst_idx, allocas_from_def] >>
  conj_tac >- fs[allocas_from_def] >>
  qexistsl_tac [`aid`,`ip`,`p`] >>
  simp[] >>
  `!k. mstore p 0w (a with vs_inst_idx := k) =
       (mstore p 0w a) with vs_inst_idx := k` by
    simp[mstore_def,write_memory_def] >>
  asm_rewrite_tac[] >>
  simp[prefix_loop_slot_taint_idx,mk_inst_def,ADD1] >>
  fs[mk_inst_def]
QED

Finalise prefix_loop_index_slot_pair


Theorem prefix_loop_index_slot_run:
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  run_inst_seq [mk_inst aid ALLOCA [Lit 32w] [ip];
    mk_inst (aid+1) MSTORE [Var ip;Lit 0w] []] s = OK t /\
  FLOOKUP t.vs_allocas aid = SOME (p,32) /\ p < dimword (:256) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst aid ALLOCA [Lit 32w] [ip]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst (aid+1) MSTORE [Var ip;Lit 0w] []) ==>
  ?H qt.
    FLOOKUP H ip = SOME (p,32) /\
    eval_operand (Var ip) t = SOME (n2w p) /\ op_taint qt (Var ip) = {} /\
    DISJOINT qt.t_mem {b | p <= b /\ b < p+32} /\ qt.t_mem SUBSET tn.t_mem /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\ lo <= p /\
    (!v. v <> ip ==> FLOOKUP H v = FLOOKUP G v /\
      eval_operand (Var v) t = eval_operand (Var v) s /\
      op_taint qt (Var v) = op_taint tn (Var v)) /\
    mload p t = 0w /\
    (!b n. b+n <= p \/ p+32 <= b ==>
      mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory) /\
    t.vs_current_bb = s.vs_current_bb /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG H qt
       (t with vs_inst_idx := s.vs_inst_idx+2)) ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule_all prefix_loop_index_slot_pair >>
  disch_then (qspecl_then [`tn`,`fn`,`PG`,`G`,`D`] mp_tac) >>
  strip_tac >> qexistsl_tac [`H`,`qt`] >>
  asm_rewrite_tac[] >> strip_tac >> gen_tac >>
  `ptr_safe_block D lo fuel ctx fn PG H qt bb
      (t with vs_inst_idx := s.vs_inst_idx+2)` by
    (qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ _ _ _`
      (qspec_then `fuel` mp_tac) >>
     simp[ptr_safe_run_def]) >>
  `ptr_safe_block D lo fuel ctx fn PG G tn bb s` by metis_tac[] >>
  simp[ptr_safe_run_def]
QED
