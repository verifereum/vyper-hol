(* One complete tuple cell: destination, delayed read, and typed store. *)
Theory exprExtRequestTupleCapturedHead
Ancestors
  exprExtRequestTupleHead exprExtRequestTupleStore exprExtRequestHistoryCompose
  exprExtRequestJointUnwrap exprExtRequestReconstruct exprOperandVar
  exprSafeOperand exprLoweringProps exprSimProps exprLowering context
  loweringPosts compileEnv loweringStateRelDefs venomState venomMemDefs gasSummary fragGasMode
  valueTypingMemoryProps valueEncodingProps valueCopyBytes freshWrites fragExec fragGasPath
Libs wordsLib

Theorem extrequest_head_path_nonhalting[local]:
  !ctx fn s n r. gas_path ctx fn s n r ==> !t. r = OK t ==> ~t.vs_halted
Proof
  Induct_on `gas_path` >> rw[] >> gvs[exit_result_def]
QED

Theorem extrequest_tuple_captured_head:
  emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
  unwrap_value cenv vv sn = (op,su) /\
  (if is_word_type ty then emit_void MSTORE [dst;op]
   else if is_bytestring_type ty then compile_store_bytestring op dst
   else emit_void MCOPY [dst;op;Lit (n2w (type_memory_bytes cenv ty))])
      su = ((),sb) /\
  post_value_type cenv e = expr_type e /\
  vv_post ctx func cenv cx e es sa sc s0 ec r vv tc /\
  extrequest_history_frame cenv cx ec sc tc ee sm s /\
  stmt_state_rel ctx func cenv cx ec tc /\
  stmt_state_rel ctx func cenv cx ee s /\
  (case vv of StackValue aty a => safe_operand sc a
   | LocatedValue aty p => safe_operand sc p.ptr_operand) /\
  (!aty p tr w tv.
     vv = LocatedValue aty p /\ p.ptr_location = slot_loc tr /\
     eval_operand p.ptr_operand tc = SOME w /\
     evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
     storage_read_live cx tr (get_storage cx ec tr) w tv) /\
  local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id /\
  fn_has_code sm su func /\ fn_has_code su sb func /\ fn_inst_ids_distinct func /\
  (!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
         ~is_word_type (expr_type e) ==>
         type_memory_bytes cenv (expr_type e) = type_memory_size tv /\
         type_memory_size tv < 2**64) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME stv /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  (ty = expr_type e \/ is_bytestring_type ty /\ is_bytestring_type (expr_type e)) /\
  read_result cx r ee = (INL v,ee) /\ ee.gas_obs = [] /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  eval_operand buf s = SOME w /\
  FLOOKUP s.vs_allocas live = SOME (tuple_base,sz) /\
  sc.cs_next_id <= live /\ live < sm.cs_next_id /\
  tuple_base <= w2n (w + n2w off) /\
  w2n (w + n2w off) + type_memory_size tv <= tuple_base + sz /\
  (!name b len. local_region cenv ee.scopes s name b len ==>
     regions_disjoint tuple_base sz b len) /\
  (cenv.ce_is_ctor ==> !name itv iv io.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv)
       (w2n (w + n2w off)) (type_memory_size tv)) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?q. gas_marked_exec F (ctx,func) (read_result cx r) (ee,s)
      [] (INL v) ee (OK q) /\
    stmt_state_rel ctx func cenv cx ee q /\
    val_in_memory tv v (w2n (w + n2w off)) q.vs_memory /\
    extrequest_history_frame cenv cx ec sc tc ee sb q /\
    FLOOKUP q.vs_allocas live = SOME (tuple_base,sz) /\
    (!a k. tuple_base <= a /\ a + k <= tuple_base + sz /\
       regions_disjoint a k (w2n (w + n2w off)) (type_memory_size tv) ==>
       mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
    (!x z. not_fresh_at sm x /\ lookup_var x s = SOME z ==>
       lookup_var x q = SOME z) /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
       FLOOKUP q.vs_allocas aid = SOME row) /\
    (!aid p k. aid < sm.cs_next_id /\ aid <> live /\ 
       FLOOKUP s.vs_allocas aid = SOME (p,k) ==>
       mem_bytes_at p k q.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!eb cb tb.
       stmt_state_rel ctx func cenv cx eb tb /\
       extrequest_history_frame cenv cx eb cb tb ee sm s /\
       cb.cs_next_id <= live ==>
       extrequest_history_frame cenv cx eb cb tb ee sb q)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all extrequest_tuple_head_read >> strip_tac >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `v' = v` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[NoAsms, gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[] >>
     fs[vyperStateTheory.evaluation_state_component_equality]) >>
  qpat_x_assum `v' = v` SUBST_ALL_TAC >>
  `stmt_state_rel ctx func cenv cx ee u /\
   expr_val_rel cx (expr_type e) v op u` by
    (fs[expr_post_def] >> metis_tac[]) >>
  `expr_val_rel cx ty v op u` by
    (qpat_x_assum `ty = expr_type e \/ _` DISJ_CASES_TAC >- gvs[] >>
     `~is_word_type ty /\ ~is_word_type (expr_type e)` by
       metis_tac[is_bytestring_word_type] >>
     fs[expr_val_rel_def] >> simp[expr_val_rel_def] >>
     irule bytestring_val_in_memory_transfer >> simp[] >>
     qexistsl_tac [`expr_type e`, `ty`, `get_tenv cx`, `stv`] >> simp[]) >>
  suspend "store"
QED

Resume extrequest_tuple_captured_head[store]:
  `ci_mono sm sn` by
    (qspecl_then [`ADD`, `[buf; Lit (n2w off)]`, `sm`] mp_tac
       ci_mono_emit_op >> simp[]) >>
  `sc.cs_next_var <= sn.cs_next_var` by
    (fs[exprExtRequestHistoryTheory.extrequest_history_frame_def, ci_mono_def] >>
     decide_tac) >>
  `!x. op = Var x \/ dst = Var x ==> not_fresh_at su x` by
    (rpt strip_tac
     >- (irule compiler_unwrap_value_var >>
         qexistsl_tac [`cenv`, `op`, `sn`, `vv`] >> simp[] >>
         Cases_on `vv` >> fs[safe_operand_def] >> rpt strip_tac >>
         irule not_fresh_at_mono >> qexists_tac `sc` >> simp[]) >>
     fs[safe_operand_def]) >>
  `local_ptrs_reserved cenv su /\
   sm.cs_next_var <= su.cs_next_var /\ sm.cs_next_id <= su.cs_next_id` by
    fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >>
  `!name b len. local_region cenv ee.scopes u name b len ==>
     b + len <= w2n (w + n2w off) \/
     w2n (w + n2w off) + type_memory_size tv <= b` by
    (rpt strip_tac >>
     `local_region cenv ee.scopes s name b len` by
       metis_tac[exprExtRequestHistoryTheory.extrequest_history_local_regions] >>
     `regions_disjoint tuple_base sz b len` by metis_tac[] >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `~u.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def, gas_marked_path_def] >>
     metis_tac[extrequest_head_path_nonhalting]) >>
  drule_all extrequest_store_cell_path >> strip_tac >>
  suspend "history_and_finish"
QED

Resume extrequest_tuple_captured_head[history_and_finish]:
  `ci_mono su sb` by
    (qpat_x_assum `(if is_word_type ty then _ else _) su = _` mp_tac >>
     Cases_on `is_word_type ty` >> simp[]
     >- (strip_tac >> qspecl_then [`MSTORE`, `[dst;op]`, `su`]
           mp_tac ci_mono_emit_void >> simp[]) >>
     Cases_on `is_bytestring_type ty` >> simp[]
     >- (strip_tac >> qspecl_then [`op`, `dst`, `su`]
           mp_tac ci_mono_compile_store_bytestring >> simp[]) >>
     strip_tac >>
     qspecl_then [`MCOPY`, `[dst;op;Lit (n2w (type_memory_bytes cenv ty))]`, `su`]
       mp_tac ci_mono_emit_void >> simp[]) >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `su` >> fs[ci_mono_def]) >>
  `FLOOKUP u.vs_allocas live = SOME (tuple_base,sz)` by
    (fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
  `allocas_non_overlapping u` by
    fs[stmt_state_rel_def, state_rel_def, alloca_inv_def] >>
  `extrequest_history_frame cenv cx ec sc tc ee sb
     (q with vs_inst_idx := u.vs_inst_idx)` by
    (irule extrequest_history_store_alloca >>
     conj_tac >- simp[] >>
     conj_tac >- (qexistsl_tac [`ctx`, `func`] >> simp[]) >>
     qexistsl_tac [`w2n (w + n2w off)`, `live`, `type_memory_size tv`,
       `su`, `sz`, `u`, `tuple_base`] >>
     simp[ci_mono_def, loweringStateRelDefsTheory.regions_disjoint_def,
          venomStateTheory.lookup_var_def] >>
     fs[venomStateTheory.lookup_var_def, ci_mono_def,
        loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  `extrequest_history_frame cenv cx ec sc tc ee sb q` by
    (qpat_x_assum `extrequest_history_frame _ _ _ _ _ _ _ (_ with vs_inst_idx := _)`
       mp_tac >>
     simp[exprExtRequestHistoryTheory.extrequest_history_frame_def,
          venomStateTheory.lookup_var_def] >> metis_tac[]) >>
  qexists_tac `q` >> simp[] >>
  conj_tac
  >- (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
      simp[gas_marked_exec_def] >> strip_tac >>
      drule_all gas_marked_path_then >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `q with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = u`
        mp_tac >> simp[venomStateTheory.venom_state_component_equality]) >>
  conj_tac
  >- (rpt strip_tac >>
      `mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory` by
        (irule extrequest_history_alloc_window >>
         first_assum (irule_at (Pat `extrequest_history_frame _ _ _ _ _ _ _ _`)) >>
         first_assum (irule_at (Pat `FLOOKUP _ live = _`)) >>
         fs[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
      fs[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at su x` by (irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
      fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
  conj_tac
  >- (`q.vs_allocas = u.vs_allocas` by
        (qpat_x_assum `q with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = u` mp_tac >>
         simp[venomStateTheory.venom_state_component_equality]) >>
      qpat_x_assum `extrequest_history_frame _ _ ee sm s ee su u` mp_tac >>
      simp[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
  conj_tac
  >- (map_every qx_gen_tac [`aid`, `old_base`, `old_size`] >> strip_tac >>
      `FLOOKUP u.vs_allocas aid = SOME (old_base,old_size)` by
        (fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
      `old_base + old_size <= tuple_base \/ tuple_base + sz <= old_base` by
        (qpat_x_assum `allocas_non_overlapping u` mp_tac >>
         rewrite_tac[venomMemDefsTheory.allocas_non_overlapping_def] >>
         disch_then (qspecl_then [`aid`, `live`, `old_base`, `old_size`, `tuple_base`, `sz`] mp_tac) >>
         simp[]) >>
      `regions_disjoint old_base old_size (w2n (w + n2w off)) (type_memory_size tv)` by
        (simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
      fs[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  rpt strip_tac >>
  `extrequest_history_frame cenv cx eb cb tb ee su u` by
    (irule extrequest_history_frame_trans >>
     first_assum (irule_at (Pat `extrequest_history_frame _ _ eb cb tb _ _ _`)) >>
     metis_tac[]) >>
  suspend "arbitrary_root"
QED

Resume extrequest_tuple_captured_head[arbitrary_root]:
  `extrequest_history_frame cenv cx eb cb tb ee sb
     (q with vs_inst_idx := u.vs_inst_idx)` by
    (irule extrequest_history_store_alloca >>
     conj_tac >- simp[] >>
     conj_tac >- (qexistsl_tac [`ctx`, `func`] >> simp[]) >>
     qexistsl_tac [`w2n (w + n2w off)`, `live`, `type_memory_size tv`,
       `su`, `sz`, `u`, `tuple_base`] >>
     simp[ci_mono_def, loweringStateRelDefsTheory.regions_disjoint_def,
          venomStateTheory.lookup_var_def] >>
     fs[venomStateTheory.lookup_var_def, ci_mono_def,
        loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  qpat_x_assum `extrequest_history_frame _ _ eb cb tb _ _ (_ with vs_inst_idx := _)`
    mp_tac >>
  simp[exprExtRequestHistoryTheory.extrequest_history_frame_def,
       venomStateTheory.lookup_var_def] >> metis_tac[]
QED

Finalise extrequest_tuple_captured_head
