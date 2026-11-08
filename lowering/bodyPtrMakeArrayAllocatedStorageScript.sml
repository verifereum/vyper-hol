Theory bodyPtrMakeArrayAllocatedStorage
Ancestors
  bodyPtrMakeArrayAllocatedOne bodyPtrMakeArrayStorageEndpoint
  bodyPtrMakeArrayAllocCursor bodyPtrMakeArrayCopyStateFrame bodyPtrMakeArrayExternalPost bodyPtrMakeArrayBufferPost
  bodyPtrMakeArrayMaterialiseFrame bodyPtrDefs valueEncodingProofs
  exprSimCopy exprSimStorageCopy ptrDiscipline fragGasPathPtr
  emitHelperProps emitHelper context compileEnv venomState finite_map pred_set words list

Theorem allocated_storage_loop_endpoint_frame:
  compile_alloc_buffer (32*n) sa = (buf,sm) /\ buf.buf_operand = Var dst /\
  compile_word_copy_loop src (Var dst) n (if tr then LocTransient else LocStorage)
    LocMemory F sm = (u,sb) /\ fn_has_code sm sb func /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ 32*n < dimword(:256) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (32*n))]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  copy_old_operand sa src /\ op_taint tn src = {} /\ eval_operand src s = SOME key /\
  well_formed_type_value tv /\ slots_in_range st (w2n key) tv /\
  decode_value st (w2n key) tv = SOME v /\ type_slot_size tv <= n /\
  storage_range_agree st (if tr then contract_transient s else contract_storage s) key tv /\
  (!k j. w2n key <= w2n k /\ w2n k < w2n key+type_slot_size tv /\
    j < 32 /\ j IN key_taint (if tr then tn.t_trans else tn.t_stor) k ==>
    dead_bytes (if tr then contract_transient s else contract_storage s)
      (w2n key) tv (w2n k) j) /\
  ghost_inv d cenv cx es G tn s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?z H tm b.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK z) /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    stmt_state_rel ctx func cenv cx es z /\
    lookup_var dst z = SOME (n2w b) /\ ptr_covers H tm dst z (32*n) /\
    (!m. mem_agree_outside tm.t_mem z.vs_memory m ==> val_in_memory tv v b m) /\
    ghost_inv d cenv cx es H tm z /\ ghost_kept cenv es sa G tn s H tm /\
    (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
    (!esi si e raw vv base.
      vv_post ctx func cenv cx e esi si sa base es raw vv s /\
      read_result cx raw es = (INL v,es) /\
      MAP FDOM esi.scopes = MAP FDOM es.scopes /\
      local_ptrs_reserved cenv si /\
      si.cs_next_var <= sa.cs_next_var /\ si.cs_next_id <= sa.cs_next_id /\
      ~is_word_type (expr_type e) /\
      evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
      val_wf tv v /\ val_footprint tv v <= 32*n ==>
      expr_post ctx func cenv cx e esi si sb base es v (Var dst) z /\
      (type_memory_size tv <= 32*n /\
       type_memory_bytes cenv (lowered_value_type cenv e) <= 32*n ==>
       ptr_val_ok cx (expr_type e) v (Var dst) H tm z /\
       ptr_buf_ok cenv e (Var dst) H z))
Proof
  strip_tac >>
  drule_all (SRULE [] literal_alloc_buffer_cursor_run) >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  drule literal_alloc_buffer_cursor_shape >> strip_tac >>
  `eval_operand src a = SOME key /\ op_taint tm src = {}` by
    (Cases_on `src` >> gvs[copy_old_operand_def, eval_operand_def,
       op_taint_def, lookup_var_def] >> metis_tac[]) >>
  `copy_old_operand sm src` by
    (fs[copy_old_operand_def] >> metis_tac[]) >>
  `lookup_var dst a = SOME (n2w (w2n w)) /\ ptr_covers H tm dst a (32*n) /\
   not_fresh_at sm dst` by
    (gvs[eval_operand_def] >> metis_tac[wordsTheory.n2w_w2n]) >>
  `contract_storage a = contract_storage s /\
   contract_transient a = contract_transient s` by
    simp[contract_storage_def, contract_transient_def] >>
  `storage_range_agree st (if tr then contract_transient a else contract_storage a) key tv` by
    simp[] >>
  `!k j. w2n key <= w2n k /\ w2n k < w2n key+type_slot_size tv /\
    j < 32 /\ j IN key_taint (if tr then tm.t_trans else tm.t_stor) k ==>
    dead_bytes (if tr then contract_transient a else contract_storage a)
      (w2n key) tv (w2n k) j` by simp[] >>
  `allocas_from 0 a` by simp[allocas_from_def] >>
  `a.vs_current_bb = sm.cs_current_bb /\ a.vs_inst_idx = LENGTH sm.cs_current_insts` by simp[] >>
  drule_all storage_copy_robust_ptr_endpoint >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx func PG H tm a 0 H2 tm2 (OK z)` >>
  suspend "post"
QED

Resume allocated_storage_loop_endpoint_frame[post]:
  `stmt_state_rel ctx func cenv cx es z` by
    (irule literal_copy_window_stmt_state_rel >>
     qexistsl_tac [`sa.cs_next_id`, `w2n w`, `32*n`,
       `STRING #"%" (toString sa.cs_next_var)`, `sa`, `sm`, `a`] >>
     simp[] >> conj_tac >- metis_tac[] >>
     rpt strip_tac >> irule literal_copy_exterior_bytes >>
     qexistsl_tac [`w2n w`, `32*n`] >> gvs[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x a = lookup_var x s` by metis_tac[] >>
  `!x. not_fresh_at sa x ==>
    lookup_var x z = lookup_var x s /\ FLOOKUP H2 x = FLOOKUP G x /\
    op_taint tm2 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `not_fresh_at sm x` by metis_tac[] >>
     qpat_x_assum `!x. not_fresh_at sm x ==> _` (qspec_then `x` mp_tac) >>
     qpat_x_assum `!x. not_fresh_at sa x ==> _ /\ _ /\ _` (qspec_then `x` mp_tac) >>
     simp[op_prov_def]) >>
  `!i. i < w2n w \/ w2n w+32*n <= i ==>
    mem_bytes_at i 1 z.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tm2.t_mem <=> i IN tn.t_mem)` by
    (fs[mem_agree_outside_def] >> gen_tac >> disch_tac >>
     conj_tac >- (qpat_x_assum `!i. _ ==> mem_bytes_at i 1 _ = _`
       (qspec_then `i` mp_tac) >> simp[] >> decide_tac) >>
     qpat_x_assum `!i. _ ==> (_ IN tm2.t_mem <=> _)` (qspec_then `i` mp_tac) >>
     qpat_x_assum `!i. _ ==> (_ IN tm.t_mem <=> _)` (qspec_then `i` mp_tac) >> simp[]) >>
  drule copy_static_fields >> strip_tac >>
  `z.vs_call_ctx = s.vs_call_ctx /\ z.vs_accounts = s.vs_accounts /\
   z.vs_transient = s.vs_transient /\ tm2.t_stor = tn.t_stor /\
   tm2.t_trans = tn.t_trans /\ tm2.t_imm = tn.t_imm` by simp[] >>
  `ghost_inv d cenv cx es H2 tm2 z /\ ghost_kept cenv es sa G tn s H2 tm2` by
    (irule literal_allocated_copy_ghost_post >>
     simp[IgnAsm `tm2.t_mem = _`] >> conj_tac
     >- (qexistsl_tac [`w2n w`, `32*n`, `a`] >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- (rpt strip_tac >>
           qpat_x_assum `!aid b len. _ /\ FLOOKUP s.vs_allocas aid = _ ==> _` irule >>
           qexists_tac `aid` >> simp[]) >>
         first_assum ACCEPT_TAC) >>
     qexistsl_tac [`ctx`, `func`] >> simp[]) >>
  qexistsl_tac [`z`, `H2`, `tm2`, `w2n w`] >>
  simp[IgnAsm `tm2.t_mem = _`] >>
  conj_tac >- (drule_all gas_path_ptr_then >> simp[]) >> suspend "semantic"
QED

Resume allocated_storage_loop_endpoint_frame[semantic]:
  rpt gen_tac >> strip_tac >>
  reverse conj_tac >-
    (strip_tac >> `lookup_var dst z = SOME w` by simp[] >>
     drule_all literal_buffer_pointer_post >> simp[]) >>
  `val_in_memory tv v (w2n w) z.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `ci_mono sa sm` by
    (qspecl_then [`32*n`, `sa`] mp_tac exprLoweringPropsTheory.ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono sm sb` by
    (qspecl_then [`src`, `Var dst`, `n`, `if tr then LocTransient else LocStorage`,
       `LocMemory`, `F`, `sm`] mp_tac exprLoweringPropsTheory.ci_mono_compile_word_copy_loop >> simp[]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id` by
    fs[exprLoweringPropsTheory.ci_mono_def] >>
  `sa.cs_next_id < sb.cs_next_id` by decide_tac >>
  `!off len. off + len <= w2n w \/ w2n w + 32*n <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len a.vs_memory` by
    (rpt strip_tac >> irule literal_copy_exterior_bytes >>
     qexistsl_tac [`w2n w`, `32*n`] >> simp[]) >>
  `?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = sa.cs_next_id` by
    (qexists_tac `mk_inst sa.cs_next_id ALLOCA [Lit (n2w (32*n))]
       [STRING #"%" (toString sa.cs_next_var)]` >> simp[venomInstTheory.mk_inst_def]) >>
  `(!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x a) /\
    eval_operand (Var dst) z = SOME w` by
    (simp[eval_operand_def] >> metis_tac[]) >>
  drule_all copy_buffer_read_post_transport >> simp[]
QED

Finalise allocated_storage_loop_endpoint_frame

Theorem allocated_storage_loop_endpoint:
  compile_alloc_buffer (32*n) sa = (buf,sm) /\ buf.buf_operand = Var dst /\
  compile_word_copy_loop src (Var dst) n (if tr then LocTransient else LocStorage)
    LocMemory F sm = (u,sb) /\ fn_has_code sm sb func /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ 32*n < dimword(:256) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (32*n))]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  copy_old_operand sa src /\ op_taint tn src = {} /\ eval_operand src s = SOME key /\
  well_formed_type_value tv /\ slots_in_range st (w2n key) tv /\
  decode_value st (w2n key) tv = SOME v /\ type_slot_size tv <= n /\
  storage_range_agree st (if tr then contract_transient s else contract_storage s) key tv /\
  (!k j. w2n key <= w2n k /\ w2n k < w2n key+type_slot_size tv /\
    j < 32 /\ j IN key_taint (if tr then tn.t_trans else tn.t_stor) k ==>
    dead_bytes (if tr then contract_transient s else contract_storage s)
      (w2n key) tv (w2n k) j) /\
  ghost_inv d cenv cx es G tn s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?z H tm b.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK z) /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    stmt_state_rel ctx func cenv cx es z /\
    lookup_var dst z = SOME (n2w b) /\ ptr_covers H tm dst z (32*n) /\
    (!m. mem_agree_outside tm.t_mem z.vs_memory m ==> val_in_memory tv v b m) /\
    ghost_inv d cenv cx es H tm z /\ ghost_kept cenv es sa G tn s H tm
Proof
  strip_tac >> drule_all allocated_storage_loop_endpoint_frame >> metis_tac[]
QED
