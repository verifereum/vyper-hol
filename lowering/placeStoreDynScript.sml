(*
 * place_store_value_run (placeStore) of a DynArray at a slot in storage or
 * transient storage: the value laid out at the place's type in memory
 * (through a fresh buffer when the value's type differs), then
 * compile_dynarray_to_storage: the length word, then the live elements.
 *
 * TOP-LEVEL: place_store_value_dyn_run
 *)

Theory placeStoreDyn
Ancestors
  stmtSimDefs exprSimHypsDefs typedCopyDomain vyperStoragePlaceProvenance
  loweringPosts fragGasMode placeStoreStatePatch placeStoreAllocPath placeTypedCopyPath
  stmtLowering exprLowering compileEnv
  vyperInterpreter vyperState vyperValue vyperTypeSystem
  venomState placeDynCompile placeDynLayout placeStoreCopyPath
  placeStoreDynPrepare placeDynStoreState placeDynStoragePath placeDynExecutionLayout
  vyperTypeArgFits exprSimProps typedMemoryCopy vyperTyping placeDynStorageEmptyPath

(* compile_assign_value of a DynArray into (transient) storage. *)
Theorem place_store_value_dyn_run:
  !ctx func cenv cx env ee ff s p w loc dst_op op src_loc dty sty stv v sa sb.
    (loc = LocStorage \/ loc = LocTransient) /\
    (?et n. dty = ArrayT et (Dynamic n)) /\
    compile_assign_value cenv dst_op loc op (is_word_type dty) src_loc dty sty
      (case dty of
         ArrayT et (Dynamic _) =>
           SOME ((type_memory_bytes cenv et + 31) DIV 32,
                 type_memory_bytes cenv et)
       | _ => NONE)
      (type_memory_bytes cenv dty) sa = ((), sb) /\
    eval_operand dst_op s = SOME w /\
    place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
    (!x. dst_op = Var x ==> not_fresh_at sa x) /\
    (!x. op = Var x ==> not_fresh_at sa x) /\
    type_widens_to (get_tenv cx) sty dty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
    expr_val_rel cx sty v op s /\ cenv.ce_target CapMcopy /\
    (loc = LocMemory /\ src_loc <> SOME LocMemory /\ ~is_word_type dty /\
     ~is_bytestring_type dty /\ dty <> sty ==>
     !sw dtv. eval_operand op s = SOME sw /\
              evaluate_type (get_tenv cx) dty = SOME dtv ==>
              type_memory_size stv = 0 \/
              w2n sw + type_memory_size stv <= w2n w \/
              w2n w + type_memory_size dtv <= w2n sw \/
              sw = w /\ stv = dtv) /\
    expr_sim_inv cenv cx env ee /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    local_ptrs_reserved cenv sa /\ storage_place_region cx p /\
    (!id path entry t0.
       p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
       cenv.ce_var_type id = SOME t0 ==>
       evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
    (~is_word_type sty ==>
     !sw. eval_operand op s = SOME sw ==>
          w2n sw + type_memory_size stv <= s.vs_alloca_next /\
          !aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
                     sa.cs_next_id <= aid ==>
                     w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw) /\
    (loc = LocMemory ==>
     !dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==>
           w2n w + type_memory_size dtv + 64 < dimword (:256)) /\
    (!dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==>
           0 < type_slot_size dtv) /\
    (dty <> sty /\ ~(is_bytestring_type dty /\ is_bytestring_type sty) ==>
     type_alloc_ok cenv dty) /\
    stmt_state_rel ctx func cenv cx ee s /\
    write_place cx p v ee = (INL (), ff) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
        stmt_state_rel ctx func cenv cx ff t /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  drule_all type_widens_to_value_has_type >> strip_tac >>
  qpat_x_assum `dty = ArrayT _ _` SUBST_ALL_TAC >>
  `is_word_type (ArrayT et (Dynamic n)) = F` by simp[is_word_type_def] >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [] >> disch_tac >>
  drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)
    place_dyn_assign_compile_cut >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  drule_all typed_copy_array_source >> strip_tac >>
  `~is_word_type sty` by simp[is_word_type_def] >>
  `?etv. tu = ArrayTV etv (Dynamic n) /\
          evaluate_type (get_tenv cx) et = SOME etv` by
    (qpat_x_assum `evaluate_type _ (ArrayT et _) = SOME tu` mp_tac >>
     simp[evaluate_type_def, AllCaseEqs()] >> metis_tac[]) >>
  `?vs. v = ArrayV (DynArrayV vs)` by
    (qpat_x_assum `value_has_type tu v` mp_tac >>
     qpat_assum `tu = _` SUBST1_TAC >>
     Cases_on `v` >> simp_tac (srw_ss()) [Once value_has_type_def] >>
     rename1 `ArrayV av` >> Cases_on `av` >> simp_tac (srw_ss()) [Once value_has_type_def]) >>
  qpat_assum `expr_val_rel _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >>
  `val_in_memory stv v (w2n w') s.vs_memory` by metis_tac[] >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by
    metis_tac[expr_sim_inv_def] >>
  `!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
       sz = type_memory_size tv) fields` by metis_tac[expr_sim_inv_def] >>
  `type_memory_bytes cenv (ArrayT et (Dynamic n)) = type_memory_size tu` by
    (irule typed_copy_memory_size >> qexists_tac `get_tenv cx` >> simp[] >> metis_tac[]) >>
  `w2n w' + type_memory_size stv <= s.vs_alloca_next` by metis_tac[] >>
  `w2n w' + type_memory_size stv < dimword (:256)` by
    ( `s.vs_alloca_next < dimword (:256)` by
        metis_tac[exprLoweringPropsTheory.stmt_state_rel_def, exprLoweringPropsTheory.alloca_room_next_lt] >> decide_tac) >>
  `type_memory_size tu < dimword (:256)` by
    (Cases_on `ArrayT et (Dynamic n) = sty`
     >- (qpat_x_assum `ArrayT _ _ = sty` (SUBST_ALL_TAC o SYM) >>
         `stv = tu` by
           (qpat_x_assum `evaluate_type _ (ArrayT _ _) = SOME tu` mp_tac >>
            qpat_x_assum `evaluate_type _ (ArrayT _ _) = SOME stv` mp_tac >>
            simp[]) >>
         pop_assum SUBST_ALL_TAC >> decide_tac) >>
     qpat_x_assum `_ ==> type_alloc_ok _ _` mp_tac >>
     simp[allocLimitsTheory.type_alloc_ok_def, wordsTheory.dimword_def,
          is_bytestring_type_def] >>
     decide_tac) >>
  `val_wf stv v /\ val_wf tu v` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  `?q pw. gas_marked_path F ctx func s 0 (OK q) /\
     stmt_state_rel ctx func cenv cx ee q /\
     eval_operand prepared q = SOME pw /\
     val_in_memory tu v (w2n pw) q.vs_memory /\
     w2n pw + type_memory_size tu < dimword (:256) /\
     eval_operand dst_op q = SOME w /\
     (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
     (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
         FLOOKUP q.vs_allocas aid = SOME entry) /\
     contract_storage q = contract_storage s /\
     contract_transient q = contract_transient s /\
     ~q.vs_halted /\ q.vs_current_bb = mid.cs_current_bb /\
     q.vs_inst_idx = LENGTH mid.cs_current_insts` by
   (Cases_on `ArrayT et (Dynamic n) = sty`
    >- (qpat_x_assum `(if _ then _ else _) sa = _` mp_tac >>
        simp[comp_return_def] >> strip_tac >>
        `tu = stv` by
          (qpat_x_assum `evaluate_type _ sty = _` mp_tac >>
           qpat_x_assum `ArrayT et (Dynamic n) = sty` (fn th => rewrite_tac[GSYM th]) >>
           qpat_x_assum `evaluate_type _ (ArrayT et (Dynamic n)) = _` (fn th => rewrite_tac[th]) >>
           simp[]) >>
        qexistsl_tac [`s`, `w'`] >>
        gvs[gas_marked_path_def] >>
        irule (cj 1 fragGasPathTheory.gas_path_rules) >> simp[]) >>
    qpat_x_assum `(if _ then _ else _) sa = _` mp_tac >>
    asm_simp_tac (srw_ss()) [comp_bind_def, comp_return_def] >>
    Cases_on `compile_alloc_buffer (type_memory_size (ArrayTV etv (Dynamic n))) sa` >>
    rename1 `compile_alloc_buffer _ sa = (buf,sm)` >>
    Cases_on `compile_store_memory_typed cenv buf.buf_operand (ArrayT et (Dynamic n)) op (ArrayT se sb') sm` >>
    rename1 `compile_store_memory_typed _ _ _ _ _ sm = (unitv,sc)` >>
    Cases_on `unitv` >> simp[] >> strip_tac >>
    qpat_x_assum `buf.buf_operand = prepared` (SUBST_ALL_TAC o SYM) >>
    qpat_x_assum `sc = mid` SUBST_ALL_TAC >>
    `cs_extends sa sm` by metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
    `cs_extends sm mid` by
      metis_tac[cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family,
        exprLoweringPropsTheory.ci_mono_def, pairTheory.SND] >>
    `cs_extends mid sb` by
      metis_tac[cj 7 stmtLoweringMonoTheory.ci_mono_context_helpers,
        exprLoweringPropsTheory.ci_mono_def, pairTheory.SND] >>
    `cs_extends sm sb` by metis_tac[compileEnvTheory.cs_extends_trans] >>
    `fn_has_code sa sm func /\ fn_has_code sm mid func` by
      metis_tac[fragExecTheory.fn_has_code_split] >>
    qpat_x_assum `tu = _` SUBST_ALL_TAC >>
    drule_all place_alloc_buffer_source_path >> strip_tac >>
    rename1 `eval_operand buf.buf_operand u = SOME bw` >>
    drule loweringHaltTheory.compile_alloc_buffer_parts >> strip_tac >>
    `w2n w' + type_memory_size stv <= w2n bw \/
     w2n bw + type_memory_size (ArrayTV etv (Dynamic n)) <= w2n w'` by
      (qpat_x_assum `stmt_state_rel _ _ _ _ _ u` kall_tac >>
       irule place_alloca_source_disjoint >> simp[] >>
       goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
       qexistsl_tac [
         `mk_inst sa.cs_next_id ALLOCA
           [Lit (n2w (type_memory_size (ArrayTV etv (Dynamic n))))]
           [STRING #"%" (toString sa.cs_next_var)]`,
         `STRING #"%" (toString sa.cs_next_var)`, `raw`] >>
       gvs[exprLoweringPropsTheory.run_inst_seq_def, venomInstTheory.mk_inst_def,
         venomExecSemanticsTheory.step_inst_base_def,
         venomStateTheory.eval_operands_def, venomStateTheory.eval_operand_def,
         venomStateTheory.lookup_var_def, AllCaseEqs()] >>
       rpt strip_tac >>
       qpat_x_assum `!aid b sz. _ /\ sa.cs_next_id <= aid ==> _` drule >> simp[]) >>
    qpat_x_assum `run_inst_seq _ _ = _` kall_tac >>
    qpat_x_assum `u = raw with vs_inst_idx := _` kall_tac >>
    `!x. op = Var x ==> not_fresh_at sm x` by metis_tac[] >>
    `!x. dst_op = Var x ==> not_fresh_at sm x` by metis_tac[] >>
    `!x. buf.buf_operand = Var x ==> not_fresh_at sm x` by simp[] >>
    `local_ptrs_reserved cenv sm` by
      (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
       qexists_tac `sa` >> simp[]) >>
    `val_in_memory stv v (w2n w') u.vs_memory` by
      (qpat_x_assum `u.vs_memory = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
    qpat_assum `sty = _` (fn th =>
      qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _`
        (mp_tac o REWRITE_RULE [GSYM th])) >> disch_tac >>
    drule placeTypedCopyRecursivePathTheory.compile_store_memory_typed_forward_run >>
    disch_then (qspec_then `get_tenv cx` mp_tac) >>
    disch_then (drule_at (Pat `val_in_memory _ _ _ u.vs_memory`)) >>
    disch_then (drule_at (Pat `fn_has_code sm mid _`)) >>
    disch_then (drule_at (Pat `evaluate_type _ (ArrayT et (Dynamic n)) = _`)) >>
    disch_then (drule_at (Pat `eval_operand buf.buf_operand u = _`)) >>
    disch_then (qspec_then `ctx` mp_tac) >>
    simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
    drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
    `stmt_state_rel ctx func cenv cx ee t` by
      (irule place_typed_copy_alloca_state_frame >>
       goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >>
       qexistsl_tac [`type_memory_size (ArrayTV etv (Dynamic n))`,
         `mk_inst sa.cs_next_id ALLOCA
           [Lit (n2w (type_memory_size (ArrayTV etv (Dynamic n))))]
           [STRING #"%" (toString sa.cs_next_var)]`] >>
       simp[venomInstTheory.mk_inst_def] >>
       rpt conj_tac >> first_assum ACCEPT_TAC) >>
    `gas_marked_path F ctx func s 0 (OK t)` by
      (irule (gas_marked_path_then |> Q.INST [`n` |-> `0`, `m` |-> `0`]
         |> SIMP_RULE (srw_ss()) []) >>
       qexists_tac `u` >> simp[gas_marked_path_def]) >>
    `eval_operand buf.buf_operand t = SOME bw` by
      (drule typedMemoryCopyTheory.typed_copy_state_frame_operand >>
       disch_then (qspec_then `buf.buf_operand` mp_tac) >> simp[]) >>
    `eval_operand dst_op u = SOME w` by
      (Cases_on `dst_op` >> gvs[venomStateTheory.eval_operand_def]) >>
    `eval_operand dst_op t = SOME w` by
      (drule typedMemoryCopyTheory.typed_copy_state_frame_operand >>
       disch_then (qspec_then `dst_op` mp_tac) >> simp[]) >>
    qpat_x_assum `typed_copy_state_frame _ _ _ _ _` mp_tac >>
    simp[typedMemoryCopyTheory.typed_copy_state_frame_def,
      venomStateTheory.venom_state_component_equality] >> strip_tac >>
    qexistsl_tac [`t`, `bw`] >> simp[] >>
    gvs[venomStateTheory.contract_storage_def, venomStateTheory.contract_transient_def] >>
    rpt strip_tac >>
    qpat_x_assum `!x. not_fresh_at sm x ==> _` (qspec_then `x` mp_tac) >> simp[]) >>
  `cs_extends sa mid /\ sa.cs_next_var <= mid.cs_next_var /\
   (!x. prepared = Var x ==> not_fresh_at mid x)` by
   (Cases_on `ArrayT et (Dynamic n) = sty`
    >- (qpat_x_assum `(if _ then _ else _) sa = _` mp_tac >>
        simp[comp_return_def] >> strip_tac >> gvs[compileEnvTheory.cs_extends_refl]) >>
    qpat_x_assum `(if _ then _ else _) sa = _` mp_tac >>
    asm_simp_tac (srw_ss()) [comp_bind_def, comp_return_def] >>
    Cases_on `compile_alloc_buffer (type_memory_size (ArrayTV etv (Dynamic n))) sa` >>
    rename1 `compile_alloc_buffer _ sa = (buf,sm)` >>
    Cases_on `compile_store_memory_typed cenv buf.buf_operand (ArrayT et (Dynamic n)) op (ArrayT se sb') sm` >>
    rename1 `compile_store_memory_typed _ _ _ _ _ sm = (unitv,sc)` >>
    Cases_on `unitv` >> simp[] >> strip_tac >>
    drule loweringHaltTheory.compile_alloc_buffer_parts >> strip_tac >>
    `cs_extends sa sm` by metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
    qpat_x_assum `sc = mid` SUBST_ALL_TAC >>
    `ci_mono sm mid` by
      (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
       rpt (pop_assum kall_tac) >> strip_tac >>
       metis_tac[cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family, pairTheory.SND]) >>
    gvs[] >> conj_tac
    >- metis_tac[exprLoweringPropsTheory.ci_mono_def, compileEnvTheory.cs_extends_trans] >>
    conj_tac
    >- (gvs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
    metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh]) >>
  `cs_extends mid sb` by
    metis_tac[cj 7 stmtLoweringMonoTheory.ci_mono_context_helpers,
      exprLoweringPropsTheory.ci_mono_def, pairTheory.SND] >>
  `fn_has_code mid sb func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  `!x. not_fresh_at sa x ==> not_fresh_at mid x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `!x. prepared = Var x \/ dst_op = Var x ==> not_fresh_at mid x` by metis_tac[] >>
  `local_ptrs_reserved cenv mid` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sa` >> simp[compileEnvTheory.cs_extends_def]) >>
  `type_memory_bytes cenv et = 32 * type_slot_size etv /\
   (type_memory_bytes cenv et + 31) DIV 32 = type_slot_size etv` by
    (irule place_dyn_element_layout >> qexists_tac `get_tenv cx` >>
     simp[] >> metis_tac[]) >>
  `well_formed_type_value tu` by metis_tac[vyperTypingTheory.evaluate_type_well_formed] >>
  qpat_x_assum `tu = _` SUBST_ALL_TAC >>
  qpat_x_assum `v = _` SUBST_ALL_TAC >>
  `place_ptr_rel cenv cx q (PlaceR p) w (SOME loc) (Type (ArrayT et (Dynamic n)))` by
    (Cases_on `p` >> gvs[place_ptr_rel_def]) >>
  `mload (w2n pw) q = n2w (LENGTH vs)` by
    (drule place_dyn_memory_header >>
     simp[venomStateTheory.mload_def, valueEncodingDefsTheory.mem_word_at_def]) >>
  `LENGTH vs < dimword (:256)` by
    gvs[well_formed_type_value_def, value_has_type_def] >>
  `type_slot_size etv = 1 ==> 32 * type_slot_size etv = 32` by simp[] >>
  `~q.vs_call_ctx.cc_static` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ q` mp_tac >>
     pure_rewrite_tac[exprLoweringPropsTheory.stmt_state_rel_def,
                      loweringStateRelDefsTheory.state_rel_def] >>
     strip_tac >> asm_rewrite_tac[]) >>
  qpat_x_assum `compile_dynarray_to_storage _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [] >> disch_tac >>
  `?t. gas_marked_path F ctx func q 0 (OK t) /\
       (!x. not_fresh_at mid x ==> lookup_var x t = lookup_var x q) /\
       store_copy_normalize q t =
         (if loc = LocTransient then tstore else sstore) w (n2w (LENGTH vs))
           (place_dyn_prefix loc pw w (type_slot_size etv)
             (32 * type_slot_size etv) q (LENGTH vs)) /\
       ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (Cases_on `LENGTH vs = 0`
     >- (`mload (w2n pw) q = 0w` by simp[] >>
         drule_all place_dyn_storage_empty_path >>
         disch_then (qspec_then `ctx` strip_assume_tac) >> qexists_tac `t` >>
         gvs[place_dyn_prefix_eqs]) >>
     `type_slot_size etv < dimword (:256)` by
       (gvs[well_formed_type_value_def, value_has_type_def,
            type_slot_size_def] >>
        `0 < n` by (Cases_on `n` >> gvs[]) >>
        `type_slot_size etv <= n * type_slot_size etv` by
          simp[] >>
        qpat_x_assum `n * type_slot_size etv + 1 <= _` mp_tac >>
        qpat_x_assum `type_slot_size etv <= n * type_slot_size etv` mp_tac >>
        decide_tac) >>
     drule_all place_dyn_storage_path >>
     disch_then (qspec_then `ctx` strip_assume_tac) >>
     qexists_tac `t` >> Cases_on `loc` >> gvs[]) >>
  `w2n pw + 32 * (1 + n * type_slot_size etv) <= dimword (:256)` by
    (qpat_assum `w2n pw + type_memory_size _ < _` mp_tac >>
     pure_rewrite_tac[cj 1 valueEncodingPropsTheory.type_memory_size_slots,
                      vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  `store_copy_normalize q t =
    (if loc = LocStorage then sstore else tstore) w
      (n2w (w2n (n2w (LENGTH vs):bytes32)))
      (place_dyn_prefix loc pw w (type_slot_size etv)
        (32 * type_slot_size etv) q (w2n (n2w (LENGTH vs):bytes32)))` by
    (Cases_on `loc` >> gvs[]) >>
  `stmt_state_rel ctx func cenv cx ff t` by
    (irule place_dyn_normalized_write_state >>
     goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >>
     asm_rewrite_tac[] >>
     qexistsl_tac [`ArrayT et (Dynamic n)`, `ee`, `env`, `p`] >>
     gvs[]) >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  `t.vs_allocas = q.vs_allocas` by
    (qpat_assum `store_copy_normalize q t =
       (if loc = LocTransient then _ else _) _ _ _` mp_tac >>
     disch_then (mp_tac o AP_TERM ``\r. r.vs_allocas``) >>
     simp_tac (srw_ss())
       [stmtSimStoreCopyTheory.store_copy_normalize_def,
        place_dyn_prefix_fields, venomStateTheory.sstore_def,
        venomStateTheory.tstore_def] >>
     Cases_on `loc = LocTransient` >>
     gvs[venomStateTheory.sstore_def, venomStateTheory.tstore_def,
         place_dyn_prefix_fields]) >>
  qexists_tac `t` >> simp[] >> metis_tac[]
QED
