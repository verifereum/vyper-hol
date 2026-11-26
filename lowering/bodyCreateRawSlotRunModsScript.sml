(* The RawCreate slot copy starts at the existing ALLOCA endpoint. *)
Theory bodyCreateRawSlotRunMods
Ancestors
  bodyFullForStorage copyExecution stmtLowering exprLowering exprPtrUnwrapLoopInvariant
  exprPtrUnwrapRuntimeFrame exprPtrUnwrapCopyPost exprPtrUnwrapStoragePost
  exprSimStorageCopy exprSimConvertFromBytes createSourceCallback fragGasOriginPtr
  representationCleanPtr typedMemoryCopy slotCopyExecution bodyPtrDefs ptrDiscipline
  abiValueEncoding memoryReadProps valueEncodingProps loweringPosts fragExec
  vyperStorageFootprint context compileEnv venomState venomExecSemantics words finite_map
  pred_set list arithmetic vyperAST

Theorem raw_slot_live_bytes[local]:
  storage_holds cx tr (BaseT (BytesT (Dynamic k))) (Value (BytesV bs)) key ee j /\
  ptr_vv_ok cx (BaseT (BytesT (Dynamic k))) (Value (BytesV bs))
    (LocatedValue tag p) ee Gj tj j /\
  p.ptr_location = slot_loc tr /\ eval_operand p.ptr_operand j = SOME key /\
  n = type_slot_size (BaseTV (BytesT (Dynamic k))) /\
  pbase < dimword (:256) /\
  (!i. i < n ==> mem_word_at (pbase+32*i) u.vs_memory =
     slot_copy_word (if tr then TLOAD else SLOAD) j (key+n2w i)) /\
  (!i r. i < n /\ r < 32 /\ pbase+32*i+r IN tu.t_mem ==>
     r IN key_taint (if tr then tj.t_trans else tj.t_stor) (key+n2w i)) ==>
  mload pbase u = n2w (LENGTH bs) /\ read_memory (pbase+32) (LENGTH bs) u = bs /\
  (!i. pbase <= i /\ i < pbase+32+LENGTH bs ==> i NOTIN tu.t_mem)
Proof
  strip_tac >> qpat_x_assum `n = type_slot_size _` SUBST_ALL_TAC >>
  `evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) =
     SOME (BaseTV (BytesT (Dynamic k)))` by
    (qpat_assum `storage_holds _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [storage_holds_def]) >>
     drule evaluate_type_base_result >> strip_tac >> simp[]) >>
  `w2n (n2w pbase : bytes32) = pbase` by simp[w2n_n2w] >>
  `?v. read_result cx (Value (BytesV bs)) ee = (INL v,ee) /\
       !mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
             val_in_memory (BaseTV (BytesT (Dynamic k))) v
               (w2n (n2w pbase : bytes32)) mem` by
    (irule unwrap_storage_copied_robust >>
     qpat_assum `ptr_vv_ok _ _ _ _ _ _ _ _` (irule_at Any) >>
     qexistsl [`key`,`tr`] >> asm_rewrite_tac[] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `w2n (n2w pbase : bytes32) = pbase` (fn eq =>
    qpat_x_assum `!mem. mem_agree_outside _ _ mem ==> _`
      (assume_tac o REWRITE_RULE [eq])) >>
  `v = BytesV bs` by fs[vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  qpat_x_assum `v = BytesV bs` SUBST_ALL_TAC >>
  `val_in_memory (BaseTV (BytesT (Dynamic k))) (BytesV bs) pbase u.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `mload pbase u = n2w (LENGTH bs) /\ read_memory (pbase+32) (LENGTH bs) u = bs` by
    (qpat_assum `val_in_memory _ _ _ _` mp_tac >>
     pure_rewrite_tac[dynamic_bytes_memory_boundary,mem_word_at_eq_mload,
                      read_memory_eq_mem_bytes_at] >> simp[]) >>
  asm_rewrite_tac[] >>
  drule robust_val_in_memory_bytes_clean >> simp[] >>
  disch_then strip_assume_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `i < pbase+32` >> simp[] >>
  `pbase+32 <= i` by decide_tac >> simp[]
QED

(* Reuse the physical slot loop with no protected snapshot rows. *)
Theorem raw_slot_execute[local]:
  compile_slot_to_memory src (Var owner) n (slot_loc tr) m = (lab,b) /\
  fn_has_code m b func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp j) /\
  allocas_from lo j /\ not_fresh_at m owner /\
  (!x. src = Var x ==> not_fresh_at m x) /\
  eval_operand src j = SOME key /\ op_taint tj src = {} /\
  lookup_var owner j = SOME (n2w pbase) /\ ptr_covers Gj tj owner j (32*n) /\
  pbase+32*n < dimword (:256) /\ pbase+32*n <= j.vs_alloca_next /\
  ~j.vs_halted /\ j.vs_current_bb = m.cs_current_bb /\
  j.vs_inst_idx = LENGTH m.cs_current_insts ==>
  ?u Gu tu.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (j,Gj,tj) [] (OK u,Gu,tu)) /\
    ~u.vs_halted /\ u.vs_current_bb = b.cs_current_bb /\
    u.vs_inst_idx = LENGTH b.cs_current_insts /\
    slot_copy_inv m (if tr then TLOAD else SLOAD) j key (n2w pbase : bytes32) n [] n u /\
    slot_copy_ghost_inv m (if tr then TLOAD else SLOAD)
       key (n2w pbase : bytes32) owner n Gj tj n Gu tu u /\
    slot_copy_runtime_frame m (n2w pbase : bytes32) n j u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_slot_to_memory src (Var owner) n (slot_loc tr) m =
    (slot_copy_body m,slot_copy_final m src (Var owner) n (if tr then TLOAD else SLOAD))` by
    (Cases_on `tr` >> simp[NoAsms,slot_loc_def,compile_slot_to_memory_shape]) >>
  `lab = slot_copy_body m /\ b = slot_copy_final m src (Var owner) n (if tr then TLOAD else SLOAD)` by
    metis_tac[pairTheory.PAIR_EQ] >>
  qpat_x_assum `lab = slot_copy_body m` SUBST_ALL_TAC >>
  `fn_has_code m (slot_copy_final m src (Var owner) n (if tr then TLOAD else SLOAD)) func` by
    metis_tac[] >>
  drule slot_copy_lookup >> strip_tac >>
  `slot_copy_external m src /\ slot_copy_external m (Var owner)` by
    (conj_tac >- (Cases_on `src` >> fs[slot_copy_external_def] >>
                  metis_tac[slot_copy_not_fresh_external,slot_copy_external_def]) >>
     simp[slot_copy_not_fresh_external]) >>
  `n < 2**256 /\ pbase < dimword (:256)` by (fs[dimword_def] >> decide_tac) >>
  `w2n (n2w pbase : bytes32) = pbase` by simp[w2n_n2w] >>
  `compile_iter_elem_copy ARB src (Var owner) n (slot_loc tr) T ARB ARB m = ((),b)` by
    (simp[compile_iter_elem_copy_def,comp_ignore_bind_def,comp_bind_def,comp_return_def] >> metis_tac[]) >>
  (* The generic execution theorem carries an unused TopLevelName equation. *)
  `?ce ty ann nid ca place cb. compile_expr ce ty (TopLevelName ann nid) ca = (place,cb)` by
    (qexistsl [`ARB`,`ARB`,`ARB`,`ARB`,`ARB`] >>
     Cases_on `compile_expr ARB ARB (TopLevelName ARB ARB) ARB` >> simp[]) >>
  `w2n (n2w pbase : bytes32) + 32*n < 2**256` by
    (qpat_x_assum `pbase + 32*n < dimword (:256)` mp_tac >>
     simp[w2n_n2w,arithmeticTheory.X_MOD_Y_EQ_X,dimword_def] >>
     intLib.COOPER_TAC) >>
  drule_at (Pat `compile_expr _ _ _ _ = _`) for_storage_element_copy_run >>
  disch_then (drule_at (Pat `compile_iter_elem_copy _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
  disch_then (qspecl_then [`lo`,`ctx`,`func`,`PG`,`Gj`,`tj`,`n2w pbase`,`[]`] mp_tac) >>
  (impl_tac >-
    (qpat_assum `w2n (n2w pbase : bytes32) + 32*n < 2**256` mp_tac >>
     simp[create_memory_snapshot_def,GSYM dimword_def])) >>
  disch_then (qx_choosel_then [`u`,`Gu`,`tu`] strip_assume_tac) >>
  qexistsl [`u`,`Gu`,`tu`] >> rpt conj_tac
  >- qpat_assum `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (j,Gj,tj) [] (OK u,Gu,tu)` ACCEPT_TAC
  >- qpat_assum `~u.vs_halted` ACCEPT_TAC
  >- qpat_assum `u.vs_current_bb = b.cs_current_bb` ACCEPT_TAC
  >- qpat_assum `u.vs_inst_idx = LENGTH b.cs_current_insts` ACCEPT_TAC
  >- qpat_assum `slot_copy_inv m (if tr then TLOAD else SLOAD) j key
       (n2w pbase : bytes32) n [] n u` ACCEPT_TAC
  >- qpat_assum `slot_copy_ghost_inv m (if tr then TLOAD else SLOAD)
       key (n2w pbase : bytes32) owner n Gj tj n Gu tu u` ACCEPT_TAC
  >- qpat_assum `slot_copy_runtime_frame m (n2w pbase : bytes32) n j u` ACCEPT_TAC
QED

Theorem raw_create_slot_run_mods:
  compile_slot_to_memory p.ptr_operand (Var owner)
    (type_slot_size (BaseTV (BytesT (Dynamic k)))) p.ptr_location m = (lab,b) /\
  p.ptr_location = slot_loc tr /\
  cap = 32 * type_slot_size (BaseTV (BytesT (Dynamic k))) /\
  storage_holds cx tr (BaseT (BytesT (Dynamic k))) (Value (BytesV bs)) key ee j /\
  ptr_vv_ok cx (BaseT (BytesT (Dynamic k))) (Value (BytesV bs))
    (LocatedValue tag p) ee Gj tj j /\
  eval_operand p.ptr_operand j = SOME key /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at m x) /\
  fn_has_code m b func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp j) /\
  allocas_from lo j /\ not_fresh_at m owner /\
  lookup_var owner j = SOME (n2w pbase) /\ ptr_covers Gj tj owner j cap /\
  FLOOKUP j.vs_allocas site.inst_id = SOME (pbase,cap) /\
  pbase+cap < dimword (:256) /\ pbase+cap <= j.vs_alloca_next /\
  ~j.vs_halted /\ j.vs_current_bb = m.cs_current_bb /\
  j.vs_inst_idx = LENGTH m.cs_current_insts ==>
  ?u Gu tu.
    ~u.vs_halted /\ u.vs_current_bb = b.cs_current_bb /\
    u.vs_inst_idx = LENGTH b.cs_current_insts /\
    FLOOKUP u.vs_allocas site.inst_id = SOME (pbase,cap) /\
    lookup_var owner u = SOME (n2w pbase) /\ ptr_covers Gu tu owner u cap /\
    mload pbase u = n2w (LENGTH bs) /\ read_memory (pbase+32) (LENGTH bs) u = bs /\
    (!i. pbase <= i /\ i < pbase+32+LENGTH bs ==> i NOTIN tu.t_mem) /\
    typed_copy_frame pbase cap j.vs_memory u.vs_memory /\
    (!i. i < pbase \/ pbase+cap <= i ==> (i IN tu.t_mem <=> i IN tj.t_mem)) /\
    (!x. not_fresh_at m x ==> lookup_var x u = lookup_var x j /\
       FLOOKUP Gu x = FLOOKUP Gj x /\ op_taint tu (Var x) = op_taint tj (Var x)) /\
    copy_static u = copy_static j /\
    u.vs_allocas = j.vs_allocas /\ u.vs_alloca_next = j.vs_alloca_next /\
    u.vs_data_section = j.vs_data_section /\ u.vs_accounts = j.vs_accounts /\
    u.vs_call_ctx = j.vs_call_ctx /\ u.vs_transient = j.vs_transient /\
    u.vs_immutables = j.vs_immutables /\ u.vs_fmp = j.vs_fmp /\
    u.vs_labels = j.vs_labels /\ u.vs_requests = j.vs_requests /\
    tu.t_stor = tj.t_stor /\ tu.t_trans = tj.t_trans /\ tu.t_imm = tj.t_imm /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (j,Gj,tj) [] (OK u,Gu,tu))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `n = type_slot_size (BaseTV (BytesT (Dynamic k)))` >>
  `compile_slot_to_memory p.ptr_operand (Var owner) n (slot_loc tr) m = (lab,b)` by
    metis_tac[] >>
  `op_taint tj p.ptr_operand = {}` by fs[ptr_vv_ok_def] >>
  `pbase < dimword (:256) /\ pbase+32*n < dimword (:256) /\
   pbase+32*n <= j.vs_alloca_next /\ ptr_covers Gj tj owner j (32*n)` by
    gvs[] >>
  `w2n (n2w pbase : bytes32) = pbase` by simp[w2n_n2w] >>
  drule_all raw_slot_execute >>
  disch_then (qspec_then `PG` (qx_choosel_then [`u`,`Gu`,`tu`] strip_assume_tac)) >>
  drule_then assume_tac copy_prefix_words >> drule_then assume_tac copy_prefix_taint >>
  `!i r. i < n /\ r < 32 /\ pbase+32*i+r IN tu.t_mem ==>
     r IN key_taint (if tr then tj.t_trans else tj.t_stor) (key+n2w i)` by
    (Cases_on `tr` >> fs[]) >>
  `n = type_slot_size (BaseTV (BytesT (Dynamic k)))` by simp[Abbr `n`] >>
  qpat_assum `w2n (n2w pbase : bytes32) = pbase`
    (fn eq => rule_assum_tac (REWRITE_RULE [eq])) >>
  drule_all raw_slot_live_bytes >> strip_tac >>
  qpat_assum `slot_copy_runtime_frame _ _ _ j u`
    (strip_assume_tac o REWRITE_RULE [slot_copy_runtime_frame_def]) >>
  qpat_assum `slot_copy_ghost_inv _ _ _ _ _ _ Gj tj _ Gu tu u`
    (strip_assume_tac o REWRITE_RULE [slot_copy_ghost_inv_def]) >>
  `!x. not_fresh_at m x ==> lookup_var x u = lookup_var x j /\
       FLOOKUP Gu x = FLOOKUP Gj x /\ op_taint tu (Var x) = op_taint tj (Var x)` by
    (gen_tac >> disch_tac >> drule slot_copy_not_fresh_external >> strip_tac >>
     conj_tac
     >- (qpat_assum `!op. slot_copy_external m op ==> eval_operand op u = _`
           (qspec_then `Var x` drule) >> simp_tac bool_ss [eval_operand_def])
     >> qpat_assum `!v. slot_copy_external m (Var v) ==> _`
          (qspec_then `x` drule) >> simp_tac bool_ss []) >>
  `u with <|vs_vars := j.vs_vars;vs_memory := j.vs_memory;vs_prev_bb := j.vs_prev_bb;
            vs_current_bb := j.vs_current_bb;vs_inst_idx := j.vs_inst_idx|> = j` by
    (qpat_assum `copy_static u = copy_static j` mp_tac >>
     simp[NoAsms,copy_static_def,venom_state_component_equality]) >>
  `u.vs_data_section = j.vs_data_section /\ u.vs_immutables = j.vs_immutables /\
   u.vs_fmp = j.vs_fmp /\ u.vs_labels = j.vs_labels /\ u.vs_requests = j.vs_requests` by
    (qpat_assum `u with <|vs_vars := _;vs_memory := _;vs_prev_bb := _;
                     vs_current_bb := _;vs_inst_idx := _|> = j`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `lookup_var owner u = SOME (n2w pbase)` by
    (qpat_assum `!x. not_fresh_at m x ==> lookup_var x u = _ /\ _`
       (qspec_then `owner` drule) >> asm_simp_tac bool_ss []) >>
  `w2n (n2w pbase : bytes32) = pbase` by simp[w2n_n2w] >>
  qpat_x_assum `w2n (n2w pbase : bytes32) = pbase`
    (fn eq => rule_assum_tac (REWRITE_RULE [eq])) >>
  qpat_x_assum `cap = 32 * n` SUBST_ALL_TAC >>
  qpat_x_assum `n = type_slot_size _` kall_tac >>
  qexistsl [`u`,`Gu`,`tu`] >>
  asm_rewrite_tac[typed_copy_frame_def] >>
  gen_tac >> disch_tac >> first_x_assum irule >>
  asm_rewrite_tac[DE_MORGAN_THM, arithmeticTheory.NOT_LESS_EQUAL,
                  arithmeticTheory.NOT_LESS]
QED
