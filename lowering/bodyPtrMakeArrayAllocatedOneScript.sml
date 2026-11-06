Theory bodyPtrMakeArrayAllocatedOne
Ancestors
  bodyPtrMakeArrayAllocCursor bodyPtrMakeArrayCopyStateFrame
  bodyPtrMakeArrayOneSlotRuntime bodyPtrMakeArrayMaterialiseFrame
  bodyPtrDefs valueEncodingProofs exprSimCopy exprSimStorageCopy ptrDiscipline fragGasPathPtr
  emitHelperProps emitHelper context compileEnv venomState finite_map pred_set words list

Theorem literal_copy_exterior_bytes:
  mem_agree_outside {i | b <= i /\ i < b+n} m1 m2 /\
  (a+len <= b \/ b+n <= a) ==>
  mem_bytes_at a len m1 = mem_bytes_at a len m2
Proof
  strip_tac >> irule LIST_EQ >> simp[EL_mem_bytes_at] >>
  rpt strip_tac >> rename1 `i < len` >>
  `mem_bytes_at (a+i) 1 m1 = mem_bytes_at (a+i) 1 m2` by
    (fs[mem_agree_outside_def] >> first_x_assum irule >> simp[] >> decide_tac) >>
  pop_assum (mp_tac o AP_TERM ``EL 0 : word8 list -> word8``) >>
  simp[EL_mem_bytes_at]
QED

Theorem literal_alloc_buffer_cursor_shape:
  compile_alloc_buffer n sa = (buf,sm) ==>
  sm.cs_current_bb = sa.cs_current_bb /\
  LENGTH sm.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
  (!x. not_fresh_at sa x ==> not_fresh_at sm x)
Proof
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def,
       emit_op_def, fresh_var_def, emit_inst_def, fresh_id_def, emit_def,
       comp_ignore_bind_def] >>
  strip_tac >> gvs[not_fresh_at_def] >> decide_tac
QED

Theorem allocated_one_slot_endpoint:
  compile_alloc_buffer 32 sa = (buf,sm) /\ buf.buf_operand = Var dst /\
  emit_op (if tr then TLOAD else SLOAD) [src] sm = (Var tmp,sl) /\
  emit_void MSTORE [Var dst; Var tmp] sl = ((),sb) /\ fn_has_code sm sb func /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w 32)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  copy_old_operand sa src /\ op_taint tn src = {} /\ eval_operand src s = SOME key /\
  well_formed_type_value tv /\ slots_in_range st (w2n key) tv /\
  decode_value st (w2n key) tv = SOME v /\ type_slot_size tv <= 1 /\
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
    lookup_var dst z = SOME (n2w b) /\ ptr_covers H tm dst z 32 /\
    (!m. mem_agree_outside tm.t_mem z.vs_memory m ==> val_in_memory tv v b m) /\
    ghost_inv d cenv cx es H tm z /\ ghost_kept cenv es sa G tn s H tm
Proof
  strip_tac >>
  `32 < dimword(:256)` by simp[dimword_def] >>
  drule_all (SRULE [] literal_alloc_buffer_cursor_run) >>
  simp[] >> disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  drule literal_alloc_buffer_cursor_shape >> strip_tac >>
  `eval_operand src a = SOME key /\ op_taint tm src = {}` by
    (Cases_on `src` >> gvs[copy_old_operand_def, eval_operand_def,
       op_taint_def, lookup_var_def] >> metis_tac[]) >>
  `copy_old_operand sm src` by
    (fs[copy_old_operand_def] >> metis_tac[]) >>
  `lookup_var dst a = SOME (n2w (w2n w)) /\ ptr_covers H tm dst a 32 /\
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
  drule_all external_one_slot_runtime_endpoint >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx func PG H tm a 0 H2 tm2 (OK z)` >>
  suspend "post"
QED

Resume allocated_one_slot_endpoint[post]:
  `stmt_state_rel ctx func cenv cx es z` by
    (irule literal_copy_window_stmt_state_rel >>
     qexistsl_tac [`sa.cs_next_id`, `w2n w`, `32`,
       `STRING #"%" (toString sa.cs_next_var)`, `sa`, `sm`, `a`] >>
     simp[] >> conj_tac >- metis_tac[] >>
     rpt strip_tac >> irule literal_copy_exterior_bytes >>
     qexistsl_tac [`w2n w`, `32`] >> gvs[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x a = lookup_var x s` by metis_tac[] >>
  `!x. not_fresh_at sa x ==>
    lookup_var x z = lookup_var x s /\ FLOOKUP H2 x = FLOOKUP G x /\
    op_taint tm2 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `not_fresh_at sm x` by metis_tac[] >>
     qpat_x_assum `!x. not_fresh_at sm x ==> _` (qspec_then `x` mp_tac) >>
     qpat_x_assum `!x. not_fresh_at sa x ==> _ /\ _ /\ _` (qspec_then `x` mp_tac) >>
     simp[op_prov_def]) >>
  `!i. i < w2n w \/ w2n w+32 <= i ==>
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
     >- (qexistsl_tac [`w2n w`, `32`, `a`] >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- (rpt strip_tac >>
           qpat_x_assum `!aid b len. _ /\ FLOOKUP s.vs_allocas aid = _ ==> _` irule >>
           qexists_tac `aid` >> simp[]) >>
         first_assum ACCEPT_TAC) >>
     qexistsl_tac [`ctx`, `func`] >> simp[]) >>
  qexistsl_tac [`z`, `H2`, `tm2`, `w2n w`] >>
  simp[IgnAsm `tm2.t_mem = _`] >>
  drule_all gas_path_ptr_then >> simp[]
QED

Finalise allocated_one_slot_endpoint
