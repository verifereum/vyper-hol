(* Same-state checked boundaries for the dynamic-array backedge. *)
Theory ctorDeployMemoryRunPtrPrefixLoopBackedge
Ancestors
  ghostPcTransportPtr
  slotCopyExecution
  ctorDeployMemoryRunPtrPrefixLoopSetup ctorDeployMemoryRunPtrPrefixBoolBody
  ctorDeployMemoryRunPtrPrefixSteps exprLoweringProps instIdxIndep
  ctorAbiActualArrayBody ctorAbiActualArrayInvariant ctorAbiActualFrame
  abiDecoderExecution abiDecoderContract abiDecoderArrayBackedge abiDecoderReentry
  venomMemDefs valueEncodingProps
  ptrSafeRun ptrDiscipline venomExecSemantics venomState venomInst
  emitHelper codegenRel contextCodegenRel memLocDefs fragGasOriginPtrLoop
  words arithmetic list finite_map pred_set

Theorem prefix_loop_increment_steps:
  ip <> fresh /\
  eval_operand (Var ip) s = SOME (n2w slot) /\
  eval_operand (Var iv) s = SOME (n2w j) /\
  FLOOKUP G ip = SOME (slot,32) /\
  op_taint tn (Var ip) = {} /\ op_taint tn (Var iv) = {} /\
  slot < dimword(:256) /\ allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  let a = mk_inst iid ADD [Var iv;Lit 1w] [fresh];
      k = mk_inst (iid+1) MSTORE [Var ip;Var fresh] [];
      u = update_var fresh (n2w (SUC j)) s;
      t = mstore slot (n2w (SUC j)) u;
      H = set_prov G [fresh] (first_prov G [Var iv;Lit 1w]);
      q = step_taint a s u tn;
      qt = step_taint k u t q
  in step_inst_base a s = OK u /\ step_inst_base k u = OK t /\
    (!fuel. ptr_safe_step D lo fuel ctx fn PG G tn a s /\
      ghost_step fuel ctx PG G tn a s = (H,q) /\
      ptr_safe_step D lo fuel ctx fn PG H q k u /\
      ghost_step fuel ctx PG H q k u = (H,qt)) /\
    qt.t_mem = tn.t_mem DIFF {p | slot <= p /\ p < slot+32} /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!x. x <> fresh ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint qt (Var x) = op_taint tn (Var x)) /\
    op_taint qt (Var fresh) = {}
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qabbrev_tac `a = mk_inst iid ADD [Var iv;Lit 1w] [fresh]` >>
  qabbrev_tac `k = mk_inst (iid+1) MSTORE [Var ip;Var fresh] []` >>
  qabbrev_tac `u = update_var fresh (n2w (SUC j)) s` >>
  qabbrev_tac `t = mstore slot (n2w (SUC j)) u` >>
  qabbrev_tac `H = set_prov G [fresh] (first_prov G [Var iv;Lit 1w])` >>
  qabbrev_tac `q = step_taint a s u tn` >>
  qabbrev_tac `qt = step_taint k u t q` >>
  `eval_operand (Var ip) u = SOME (n2w slot) /\
   eval_operand (Var fresh) u = SOME (n2w (SUC j)) /\ allocas_from lo u` by
    (simp[Abbr `u`,eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE] >>
     gvs[allocas_from_def,update_var_def,eval_operand_def,lookup_var_def] >> metis_tac[]) >>
  `step_inst_base a s = OK u` by
    (simp[Abbr `a`,Abbr `u`,ADD1,GSYM word_add_n2w] >>
     irule slotCopyExecutionTheory.slot_copy_step_add >> simp[eval_operand_lit_local]) >>
  `step_inst_base k u = OK t` by
    (qpat_assum `eval_operand (Var ip) u = SOME _`
      (mp_then Any mp_tac slotCopyExecutionTheory.slot_copy_step_store) >> disch_then drule >>
     disch_then (qspec_then `iid+1` mp_tac) >>
     simp[Abbr `k`,Abbr `t`,w2n_n2w]) >>
  `q.t_mem = tn.t_mem /\ q.t_stor = tn.t_stor /\
   q.t_trans = tn.t_trans /\ q.t_imm = tn.t_imm /\
   (!x. x <> fresh ==> op_taint q (Var x) = op_taint tn (Var x)) /\
   op_taint q (Var fresh) = {}` by
    (mp_tac (Q.INST [`opc` |-> `ADD`, `t` |-> `u`, `x` |-> `fresh`,
       `a` |-> `Var iv`, `b` |-> `Lit 1w`] prefix_bool_body_arith_taint_frame) >>
     simp[Abbr `u`,Abbr `q`,Abbr `a`,update_var_def,op_taint_def]) >>
  simp[] >> conj_tac >- suspend "steps" >> suspend "frames"
QED

Resume prefix_loop_increment_steps[steps]:
  gen_tac >> conj_tac
  >- (simp[Abbr `a`] >> irule prefix_bool_body_arith_ptr_step >> simp[op_taint_def]) >>
  conj_tac
  >- (simp[Abbr `H`,Abbr `q`,Abbr `a`,Abbr `u`,ADD1,GSYM word_add_n2w] >>
      irule (SRULE [LET_THM] prefix_bool_body_add_ghost) >> simp[eval_operand_lit_local]) >>
  `FLOOKUP H ip = SOME (slot,32)` by
    (simp[Abbr `H`,set_prov_def] >> Cases_on `first_prov G [Var iv;Lit 1w]` >>
     simp[FLOOKUP_DRESTRICT,FLOOKUP_UPDATE]) >>
  conj_tac
  >- (simp[Abbr `k`] >> irule prefix_mstore_ptr_step >> simp[] >>
      qexistsl [`n2w slot:bytes32`,`slot`,`32`] >> simp[w2n_n2w]) >>
  simp[Abbr `qt`,Abbr `k`] >> irule prefix_mstore_ghost_step >>
  simp[step_inst_non_invoke]
QED

Resume prefix_loop_increment_steps[frames]:
  `qt.t_mem = q.t_mem DIFF {p | slot <= p /\ p < slot+32}` by
    (qpat_assum `eval_operand (Var ip) u = SOME _`
      (mp_then Any mp_tac prefix_mstore_mem_taint) >> disch_then drule >>
     simp[Abbr `qt`,Abbr `k`,Abbr `t`,w2n_n2w]) >>
  `qt.t_var = q.t_var /\ qt.t_stor = q.t_stor /\
   qt.t_trans = q.t_trans /\ qt.t_imm = q.t_imm` by
    simp[Abbr `qt`,Abbr `k`,SRULE [LET_THM] prefix_mstore_taint_frame] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> simp[op_taint_def] >>
      simp[Abbr `H`,set_prov_def] >> Cases_on `first_prov G [Var iv;Lit 1w]` >>
      simp[FLOOKUP_DRESTRICT,FLOOKUP_UPDATE] >> gvs[op_taint_def]) >>
  gvs[op_taint_def]
QED

Finalise prefix_loop_increment_steps


Theorem prefix_loop_increment_run:
  ip <> fresh /\
  eval_operand (Var ip) s = SOME (n2w slot) /\
  eval_operand (Var iv) s = SOME (n2w j) /\
  FLOOKUP G ip = SOME (slot,32) /\
  op_taint tn (Var ip) = {} /\ op_taint tn (Var iv) = {} /\
  slot < dimword(:256) /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts iid iv fresh (Var ip) hdr /\
  s.vs_inst_idx = LENGTH prefix /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 ==>
  let a = mk_inst iid ADD [Var iv;Lit 1w] [fresh];
      k = mk_inst (iid+1) MSTORE [Var ip;Var fresh] [];
      u = update_var fresh (n2w (SUC j)) s;
      t = mstore slot (n2w (SUC j)) u;
      H = set_prov G [fresh] (first_prov G [Var iv;Lit 1w]);
      q = step_taint a s u tn;
      qt = step_taint k u t q
  in ((!fuel. ptr_safe_run D lo fuel ctx fn PG H qt (jump_to hdr t)) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  drule_all (Q.INST [`iv` |-> `iv`, `j` |-> `j`] prefix_loop_increment_steps) >>
  disch_then (qspecl_then [`iid`,`fn`,`PG`,`D`] mp_tac) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qabbrev_tac `a = mk_inst iid ADD [Var iv;Lit 1w] [fresh]` >>
  qabbrev_tac `k = mk_inst (iid+1) MSTORE [Var ip;Var fresh] []` >>
  qabbrev_tac `u = update_var fresh (n2w (SUC j)) s` >>
  qabbrev_tac `t = mstore slot (n2w (SUC j)) u` >>
  qabbrev_tac `H = set_prov G [fresh] (first_prov G [Var iv;Lit 1w])` >>
  qabbrev_tac `q = step_taint a s u tn` >>
  qabbrev_tac `qt = step_taint k u t q` >>
  qabbrev_tac `u1 = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `t2 = t with vs_inst_idx := s.vs_inst_idx+2` >>
  `u.vs_current_bb = s.vs_current_bb /\ t.vs_current_bb = s.vs_current_bb /\
   ~u.vs_halted /\ ~t.vs_halted /\ allocas_from lo u1 /\ allocas_from lo t2` by
    (simp[Abbr `u`,Abbr `t`,Abbr `u1`,Abbr `t2`,update_var_def,mstore_def,
      allocas_from_def,write_memory_with_expansion_def] >>
     gvs[allocas_from_def] >> metis_tac[]) >>
  `get_instruction bb s.vs_inst_idx = SOME a /\
   get_instruction bb u1.vs_inst_idx = SOME k /\
   get_instruction bb t2.vs_inst_idx = SOME (mk_inst (iid+2) JMP [Label hdr] [])` by
    simp[get_instruction_def,Abbr `a`,Abbr `k`,Abbr `u1`,Abbr `t2`,
      abi_decode_backedge_insts_def,EL_APPEND_EQN] >>
  `eval_operand (Var ip) u1 = SOME (n2w slot) /\
   eval_operand (Var fresh) u1 = SOME (n2w (SUC j))` by
    (simp[Abbr `u1`,Abbr `u`,eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE] >>
     gvs[eval_operand_def,lookup_var_def]) >>
  `FLOOKUP H ip = SOME (slot,32) /\ op_taint q (Var ip) = {} /\
   op_taint q (Var fresh) = {}` by
    (simp[Abbr `q`,Abbr `a`,Abbr `u`,SRULE [LET_THM] prefix_bool_body_arith_taint_frame,
      update_var_def,op_taint_def] >>
     simp[step_taint_def,mk_inst_def,set_var_taint_def,adopt_reset_def,
       out_taint_def,op_taint_def,FLOOKUP_UPDATE,Abbr `H`,set_prov_def] >>
     Cases_on `first_prov G [Var iv;Lit 1w]` >> simp[FLOOKUP_DRESTRICT,FLOOKUP_UPDATE]) >>
  strip_tac >>
  `!fuel. ptr_safe_run D lo fuel ctx fn PG H qt t2` by
    (irule prefix_loop_entry_jump_run >>
     simp[Abbr `t2`] >> qexistsl [`hdr`,`hdr_bb`,`iid+2`] >>
     gs[jump_to_def] >> metis_tac[]) >>
  gen_tac >>
  `step_inst fuel ctx a s = OK u` by
    (simp[Abbr `a`,step_inst_non_invoke] >> asm_rewrite_tac[]) >>
  `step_inst fuel ctx k u1 = OK (t with vs_inst_idx := SUC s.vs_inst_idx)` by
    (qpat_assum `eval_operand (Var ip) u1 = SOME _`
       (mp_then Any mp_tac prefix_mstore_endpoint) >> disch_then drule >>
     disch_then (qspecl_then [`iid+1`,`fuel`,`ctx`] mp_tac) >>
     simp[Abbr `k`,Abbr `t`,Abbr `u1`,w2n_n2w,mstore_def,write_memory_with_expansion_def]) >>
  `ptr_safe_step D lo fuel ctx fn PG H q k u1` by
    (simp[Abbr `k`] >> irule prefix_mstore_ptr_step >> simp[] >>
     qexistsl [`n2w slot:bytes32`,`slot`,`32`] >> simp[w2n_n2w]) >>
  `ghost_step fuel ctx PG H q k u1 = (H,qt)` by
    (simp[Abbr `k`] >>
     drule_then mp_tac prefix_mstore_ghost_step >>
     simp[Abbr `qt`,Abbr `u1`,ghostPcTransportPtrTheory.step_taint_inst_idx,mk_inst_def]) >>
  qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ _ _ t2`
    (qspec_then `fuel` mp_tac) >>
  simp[ptr_safe_run_def,Abbr `t2`] >> strip_tac >>
  `~is_terminator k.inst_opcode /\ ~is_terminator a.inst_opcode` by
    simp[Abbr `k`,Abbr `a`,mk_inst_def,is_terminator_def] >>
  `ptr_safe_block D lo fuel ctx fn PG H q bb u1` by
    (drule_all ptr_safe_block_step >>
     gs[Abbr `u1`,ADD1] >> metis_tac[]) >>
  simp[ptr_safe_run_def,Once ptr_safe_block_def] >>
  gs[Abbr `u1`] >> metis_tac[]
QED

(* Forward twin of prefix_loop_increment_run: the ADD/MSTORE/JMP backedge is
   one zero-mark joint gas-origin pointer path from the same ghost. *)
Theorem prefix_loop_increment_path:
  ip <> fresh /\
  eval_operand (Var ip) s = SOME (n2w slot) /\
  eval_operand (Var iv) s = SOME (n2w j) /\
  FLOOKUP G ip = SOME (slot,32) /\
  op_taint tn (Var ip) = {} /\ op_taint tn (Var iv) = {} /\
  slot < dimword(:256) /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts iid iv fresh (Var ip) hdr /\
  s.vs_inst_idx = LENGTH prefix /\
  run_inst_seq_mem_ok (TAKE 2 (abi_decode_backedge_insts iid iv fresh (Var ip) hdr)) s ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (jump_to hdr (mstore slot (n2w (SUC j)) (update_var fresh (n2w (SUC j)) s))),
     set_prov G [fresh] (first_prov G [Var iv;Lit 1w]),
     step_taint (mk_inst (iid+1) MSTORE [Var ip;Var fresh] [])
       (update_var fresh (n2w (SUC j)) s)
       (mstore slot (n2w (SUC j)) (update_var fresh (n2w (SUC j)) s))
       (step_taint (mk_inst iid ADD [Var iv;Lit 1w] [fresh]) s
          (update_var fresh (n2w (SUC j)) s) tn))
Proof
  strip_tac >>
  drule_all (Q.INST [`iv` |-> `iv`, `j` |-> `j`] prefix_loop_increment_steps) >>
  disch_then (qspecl_then [`iid`,`func`,`PG`,`D`] mp_tac) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qabbrev_tac `a = mk_inst iid ADD [Var iv;Lit 1w] [fresh]` >>
  qabbrev_tac `k = mk_inst (iid+1) MSTORE [Var ip;Var fresh] []` >>
  qabbrev_tac `u = update_var fresh (n2w (SUC j)) s` >>
  qabbrev_tac `t = mstore slot (n2w (SUC j)) u` >>
  qabbrev_tac `H = set_prov G [fresh] (first_prov G [Var iv;Lit 1w])` >>
  qabbrev_tac `q = step_taint a s u tn` >>
  qabbrev_tac `qt = step_taint k u t q` >>
  `s with vs_inst_idx := s.vs_inst_idx = s` by
    simp[venom_state_component_equality] >>
  `u with vs_inst_idx := s.vs_inst_idx = u` by
    simp[Abbr `u`,update_var_def,venom_state_component_equality] >>
  `t.vs_current_bb = s.vs_current_bb /\ ~t.vs_halted /\
   allocas_from lo (u with vs_inst_idx := s.vs_inst_idx + 1) /\
   allocas_from lo (t with vs_inst_idx := s.vs_inst_idx + 2)` by
    (simp[Abbr `u`,Abbr `t`,update_var_def,mstore_def,
      allocas_from_def,write_memory_with_expansion_def] >>
     gvs[allocas_from_def] >> metis_tac[]) >>
  `eval_operand (Var ip) (u with vs_inst_idx := s.vs_inst_idx + 1) = SOME (n2w slot) /\
   eval_operand (Var fresh) (u with vs_inst_idx := s.vs_inst_idx + 1) =
     SOME (n2w (SUC j))` by
    (simp[Abbr `u`,eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE] >>
     gvs[eval_operand_def,lookup_var_def]) >>
  `FLOOKUP H ip = SOME (slot,32) /\ op_taint q (Var ip) = {} /\
   op_taint q (Var fresh) = {}` by
    (simp[Abbr `q`,Abbr `a`,Abbr `u`,SRULE [LET_THM] prefix_bool_body_arith_taint_frame,
      update_var_def,op_taint_def] >>
     simp[step_taint_def,mk_inst_def,set_var_taint_def,adopt_reset_def,
       out_taint_def,op_taint_def,FLOOKUP_UPDATE,Abbr `H`,set_prov_def] >>
     Cases_on `first_prov G [Var iv;Lit 1w]` >> simp[FLOOKUP_DRESTRICT,FLOOKUP_UPDATE]) >>
  `step_inst 0 ctx a s = OK u` by
    (simp[Abbr `a`,step_inst_non_invoke] >> asm_rewrite_tac[]) >>
  `step_inst 0 ctx k (u with vs_inst_idx := s.vs_inst_idx + 1) =
     OK (t with vs_inst_idx := s.vs_inst_idx + 1)` by
    (qspecl_then [`iid+1`,`Var ip`,`Var fresh`,
       `u with vs_inst_idx := s.vs_inst_idx + 1`,`n2w slot`,`n2w (SUC j)`,`0`,`ctx`]
       mp_tac prefix_mstore_endpoint >>
     simp[Abbr `k`,Abbr `t`,w2n_n2w,mstore_idx]) >>
  `ptr_safe_step D lo 0 ctx func PG H q k (u with vs_inst_idx := s.vs_inst_idx + 1)` by
    (simp[Abbr `k`] >> irule prefix_mstore_ptr_step >> simp[] >>
     qexistsl [`n2w slot:bytes32`,`slot`,`32`] >> simp[w2n_n2w]) >>
  `ghost_step 0 ctx PG H q k (u with vs_inst_idx := s.vs_inst_idx + 1) = (H,qt)` by
    (qpat_x_assum `step_inst 0 ctx k _ = _` mp_tac >>
     simp[Abbr `k`,Abbr `qt`] >> strip_tac >>
     drule prefix_mstore_ghost_step >> simp[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (t with vs_inst_idx := s.vs_inst_idx + 2), H, qt)` by
    (qspecl_then [`[a;k]`,`bb`,`s`,`G`,`tn`,
        `\n. if n = 0 then s else if n = 1 then u else t`,
        `\n. if n = 0 then G else H`,
        `\n. if n = 0 then tn else if n = 1 then q else qt`]
       mp_tac prefix_trace_origin_ptr_path >>
     impl_tac >- suspend "trace" >> simp[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (t with vs_inst_idx := s.vs_inst_idx + 2, H, qt) []
     (OK (jump_to hdr (t with vs_inst_idx := s.vs_inst_idx + 2)), H, qt)` by
    (mp_tac (Q.INST [`s` |-> `t with vs_inst_idx := s.vs_inst_idx + 2`,
       `iid` |-> `iid+2`, `lbl` |-> `hdr`, `G` |-> `H`, `tn` |-> `qt`]
       jmp_origin_ptr_path) >>
     simp[get_instruction_def,abi_decode_backedge_insts_def,EL_APPEND_EQN]) >>
  `jump_to hdr (t with vs_inst_idx := s.vs_inst_idx + 2) = jump_to hdr t` by
    simp[jump_to_def] >>
  drule_all gas_origin_ptr_path_trans >> gvs[]
QED

Resume prefix_loop_increment_path[trace]:
  rpt conj_tac
  >- simp[]
  >- simp[]
  >- simp[Abbr `a`,Abbr `k`,abi_decode_backedge_insts_def,DROP_LENGTH_APPEND,
       listTheory.isPREFIX_THM]
  >- simp[] >- simp[] >- simp[]
  >- simp[Abbr `a`,Abbr `k`,mk_inst_def,is_terminator_def]
  >- (qpat_x_assum `run_inst_seq_mem_ok _ s` mp_tac >>
      simp_tac (srw_ss()) [Abbr `a`,Abbr `k`,abi_decode_backedge_insts_def,TAKE_def]) >>
  Cases >> simp[] >> Cases_on `n` >> simp[]
QED

Finalise prefix_loop_increment_path

Theorem prefix_loop_backedge_pair:
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial (SUC j) j s /\
  slot_id IN ctor_actual_sites func ids /\ all_have_type tv vs /\
  32 + LENGTH vs * type_memory_size tv <= outsz /\
  venomMemDefs$regions_disjoint (slot,32) (d,outsz) /\
  next <= nv /\ nv < limit_st.cs_next_var /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv
    (STRING #"%" (toString nv)) ip hdr /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w j) /\
  eval_operand ip s = SOME (n2w slot) /\ abi_decoder_operand_live next ip /\
  slot < dimword (:256) /\ j < LENGTH vs /\ LENGTH vs < dimword (:256) /\
  ip = Var slot_var /\ FLOOKUP G slot_var = SOME (slot,32) /\
  op_taint tn ip = {} /\ op_taint tn (Var iv) = {} /\ lo <= slot /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  FLOOKUP G dst = SOME (b,sz) /\ op_taint tn (Var dst) = {} /\
  abi_decoder_operand_live next (Var dst) /\
  DISJOINT tn.t_mem {a | d <= a /\ a < d + 32 + SUC j * type_memory_size tv}
  ==>
  ?t H qt.
    ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
      tv vs slot_id slot initial (SUC j) (SUC j) t /\
    ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    abi_decode_sim ctx func s t /\
    FLOOKUP H slot_var = SOME (slot,32) /\ FLOOKUP H dst = SOME (b,sz) /\
    op_taint qt ip = {} /\ op_taint qt (Var dst) = {} /\
    qt.t_mem SUBSET tn.t_mem /\
    DISJOINT qt.t_mem {a | slot <= a /\ a < slot+32} /\
    DISJOINT qt.t_mem {a | d <= a /\ a < d + 32 + SUC j * type_memory_size tv} /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    (!x. abi_decoder_older_vars next x ==>
      FLOOKUP H x = FLOOKUP G x /\ op_taint qt (Var x) = op_taint tn (Var x)) /\
    ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt t) ==>
     !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn s)
Proof
  strip_tac >>
  qabbrev_tac `fresh = STRING #"%" (toString nv)` >>
  `ip <> Var fresh /\ Var dst <> Var fresh` by
    metis_tac[abi_decoder_live_excludes_output] >>
  `!x. abi_decoder_older_vars next x ==> x <> fresh` by
    (simp[Abbr `fresh`,abi_decoder_older_vars_def] >> metis_tac[]) >>
  drule_all abi_decode_backedge_sim >> disch_then (qspec_then `ctx` mp_tac) >>
  simp[w2n_n2w] >> disch_tac >>
  drule_all ctor_actual_array_observation_backedge >>
  disch_then (qspec_then `hdr` (strip_assume_tac o BETA_RULE)) >>
  gvs[] >>
  qabbrev_tac `a = mk_inst id ADD [Var iv;Lit 1w] [fresh]` >>
  qabbrev_tac `k = mk_inst (id+1) MSTORE [Var slot_var;Var fresh] []` >>
  qabbrev_tac `u = update_var fresh (n2w (SUC j)) s` >>
  qabbrev_tac `raw = mstore slot (n2w (SUC j)) u` >>
  qabbrev_tac `H = set_prov G [fresh] (first_prov G [Var iv;Lit 1w])` >>
  qabbrev_tac `q = step_taint a s u tn` >>
  qabbrev_tac `qt = step_taint k u raw q` >>
  qabbrev_tac `t = jump_to hdr raw` >>
  qpat_assum `eval_operand (Var iv) s = SOME (n2w j)`
    (mp_then (Pos (el 3)) mp_tac prefix_loop_increment_steps) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`id`,`func`,`PG`,`Ddead`] mp_tac) >>
  simp_tac (srw_ss()) [LET_THM] >> strip_tac >>
  qexistsl [`t`,`H`,`qt`] >>
  conj_tac >- (simp[Abbr `t`,Abbr `raw`,Abbr `u`] >> first_assum ACCEPT_TAC) >>
  `~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
   allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (simp[Abbr `t`,Abbr `raw`,Abbr `u`,jump_to_def,mstore_def,update_var_def,
      write_memory_with_expansion_def,allocas_from_def] >>
     gvs[allocas_from_def] >> metis_tac[]) >>
  asm_simp_tac bool_ss [] >> suspend "remaining"
QED

Resume prefix_loop_backedge_pair[remaining]:
  reverse (rpt conj_tac)
  >- (simp[Abbr `t`,Abbr `raw`,Abbr `u`,Abbr `H`,Abbr `qt`,Abbr `q`,Abbr `a`,Abbr `k`] >>
      drule_all prefix_loop_increment_run >> simp[LET_THM]) >>
  gs[Abbr `H`,Abbr `qt`,Abbr `q`,Abbr `a`,Abbr `k`,Abbr `raw`,Abbr `u`] >>
  rpt strip_tac >> simp[] >>
  gvs[SUBSET_DEF,DISJOINT_DEF,EXTENSION] >> metis_tac[]
QED

Finalise prefix_loop_backedge_pair
