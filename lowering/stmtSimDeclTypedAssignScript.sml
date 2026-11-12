(* Typed assignment execution and declaration registration. *)
Theory stmtSimDeclTypedAssign
Ancestors
  stmtSimDeclCopyFrame stmtSimDeclTypedCode typedMemoryCopy exprSimHash
  stmtSimDeclMem stmtSimDeclStore exprSimStorageCopy localPtrsProps
  loweringPosts loweringStateRelDefs valueEncoding compileEnv
  exprLoweringProps loweringSlice fragExec context
  finite_map venomState venomInst typedCopySameBlock exprSimAbiGasBridgeEdge
  exprSimAbiGasBridge exprSimAbiEncodeObliviousCode
  exprSimAbiEncodeObliviousContext venomMemDefs
  placeMemoryStaging externalNormalizePremises exprSimCopy stmtLowering
  loweringHalt abiTupleProps exprSimAlloc rich_list

Theorem typed_store_declare_frag[local]:
  compile_store_memory_typed cenv (Var p) dty src sty sa = ((),sb) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname, fty, sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  (!x. src = Var x ==> not_fresh_at sa x) /\ not_fresh_at sa p /\
  eval_operand src s = SOME sw /\ lookup_var p s = SOME w /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n w + type_memory_size dtv < dimword (:256) /\
  (w2n sw + type_memory_size stv <= w2n w \/
   w2n w + type_memory_size dtv <= w2n sw) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr cenv es.scopes p /\ MEM inst (fn_insts func) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
  local_ptrs_reserved cenv sa /\ type_memory_size dtv <= sz ==>
  frag_exec ctx sa sb (\z. z = s)
    (\t. stmt_state_rel ctx func cenv cx
       (es with scopes :=
         (sc |+ (id, <|assignable := a; type := dtv; value := v; popped := []|>)) :: rest) t /\
       (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
       (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
          FLOOKUP t.vs_allocas aid = SOME entry)) R
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
  drule typed_return_store_frag >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (drule_at (Pat `sfields_tenv_consistent _ _`)) >>
  disch_then (drule_at (Pat `eval_operand (Var _) _ = _`)) >>
  disch_then (qspecl_then [`dtv`, `ctx`, `R`,
    `\t. (!off len. off + len <= w2n w \/ w2n w + type_memory_size dtv <= off ==>
           mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
         LENGTH s.vs_memory <= LENGTH t.vs_memory`] mp_tac) >>
  impl_tac
  >- (simp[] >> conj_tac >- metis_tac[] >>
      rpt strip_tac >> simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  disch_then (mp_then Any mp_tac frag_exec_weaken) >>
  disch_then irule >> simp[] >> gen_tac >> strip_tac >> conj_tac
  >- (irule stmt_state_rel_declare_copy_frame >> simp[] >>
      qexistsl_tac [`inst`, `s`, `sa`, `w`] >>
      simp[] >> conj_tac
      >- (map_every qx_gen_tac [`b`, `n`] >> strip_tac >>
          qpat_x_assum `!off len. _` (qspecl_then [`b`, `n`] mp_tac) >>
          simp[arithmeticTheory.ADD_COMM]) >>
      gvs[]) >>
  drule copy_static_fields >> simp[]
QED

(* Observer instrumentation changes no field used by the declaration relation. *)
Theorem stmt_state_rel_observer_fields[local]:
  (stmt_state_rel ctx func cenv cx es (s with vs_current_bb := b) <=>
   stmt_state_rel ctx func cenv cx es s) /\
  (stmt_state_rel ctx func cenv cx es (s with vs_prev_bb := p) <=>
   stmt_state_rel ctx func cenv cx es s) /\
  (stmt_state_rel ctx func cenv cx es (s with vs_returndata := rd) <=>
   stmt_state_rel ctx func cenv cx es s)
Proof
  simp[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def,
       local_region_def, local_backed_def, lookup_var_def, storage_rel_def,
       transient_rel_def, immutables_rel_def, logs_rel_def, call_ctx_rel_def,
       contract_storage_def, contract_transient_def, alloca_inv_def,
       allocas_non_overlapping_def, alloca_next_valid_def, alloca_room_def,
       fmp_room_def, pending_alloca_size_def, immutable_alloca_sep_def,
       immutable_decl_sep_alt, immutable_base_zero_alt, accounts_rel_def]
QED

(* Compose the two observer interfaces without exposing compiler-shape premises
   to the declaration continuation. *)
Theorem typed_copy_frag_path[local]:
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  (!l. dst <> Label l /\ src <> Label l) /\
  frag_exec ctx sa sb (\z. z = s) Q (\r. F) /\
  (!L ids. LENGTH ids = LENGTH sa.cs_current_insts ==>
    frag_exec ctx (start_relabel L ids sa) (start_swap sa L ids sb)
      (\z. z = s with vs_current_bb := L) Q (\r. F)) /\
  (!t rd. Q t ==> Q (t with vs_returndata := rd)) /\
  (!t p. Q t ==> Q (t with vs_prev_bb := p)) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qspec_then `\opc. opc <> GAS /\ opc <> INVOKE /\ opc <> PHI /\
                        opc <> STOP /\ opc <> RETURN` mp_tac typedCopyGasOpsTheory.typed_copy_code_family >>
  simp[] >> strip_tac >>
  `cs_extends sa sb /\ frag_ops_free sa sb /\
   ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa sb))` by
    (irule code_step_frag_facts >>
     metis_tac[code_action_def]) >>
  Cases_on `sa.cs_blocks = sb.cs_blocks`
  >- (`frag_gas_free sa sb` by
        (irule compile_store_memory_typed_same_block_gas_free >> metis_tac[]) >>
      drule frag_exec_gas_path >> simp[] >> disch_then irule >> simp[]) >>
  irule (SRULE [] (Q.INST [`R` |-> `\r. F`] (SPEC_ALL frag_exec_gas_path_relabel_edge))) >>
  simp[] >> qexists_tac `sa` >> simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!L ids. _` (qspecl_then [`L`, `ids`] mp_tac) >>
      simp[frag_exec_def] >>
      disch_then (qspec_then `fn'` mp_tac) >>
      simp[start_relabel_def, start_swap_fields] >>
      metis_tac[]) >>
  metis_tac[typedCopyGasControlTheory.compile_store_memory_typed_gas_boundary]
QED

Theorem typed_store_declare_path[local]:
  compile_store_memory_typed cenv (Var p) dty src sty sa = ((),sb) /\
  (!l. src <> Label l) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname, fty, sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  (!x. src = Var x ==> not_fresh_at sa x) /\ not_fresh_at sa p /\
  eval_operand src s = SOME sw /\ lookup_var p s = SOME w /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n w + type_memory_size dtv < dimword (:256) /\
  (w2n sw + type_memory_size stv <= w2n w \/
   w2n w + type_memory_size dtv <= w2n sw) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr cenv es.scopes p /\ MEM inst (fn_insts func) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
  local_ptrs_reserved cenv sa /\ type_memory_size dtv <= sz /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      (stmt_state_rel ctx func cenv cx
        (es with scopes :=
          (sc |+ (id, <|assignable := a; type := dtv; value := v; popped := []|>)) :: rest) t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry)) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  ho_match_mp_tac (Q.INST [`dst` |-> `Var p`] typed_copy_frag_path) >>
  simp[] >> rpt conj_tac
  >- (irule typed_store_declare_frag >> metis_tac[])
  >- (map_every qx_gen_tac [`L`, `ids`] >> strip_tac >>
      `!x. not_fresh_at (start_relabel L ids sa) x <=> not_fresh_at sa x` by
        simp[not_fresh_at_def, start_relabel_def] >>
      mp_tac (Q.INST [`sa` |-> `start_relabel L ids sa`,
                      `sb` |-> `start_swap sa L ids sb`,
                      `R` |-> `\r. F`,
                      `s` |-> `s with vs_current_bb := L`]
                    typed_store_declare_frag) >>
      impl_tac
      >- (conj_tac
          >- (irule (SRULE [frag_start_oblivious_def]
                 typedCopyGasControlTheory.compile_store_memory_typed_start_oblivious) >>
              simp[]) >>
          fs[stmt_state_rel_observer_fields, local_ptrs_reserved_def,
             start_relabel_def, not_fresh_at_def, lookup_var_def] >>
          Cases_on `src` >> gvs[eval_operand_def, lookup_var_def] >>
          metis_tac[]) >>
      simp[lookup_var_def])
  >- (rpt strip_tac >>
      gvs[stmt_state_rel_observer_fields, lookup_var_def]) >>
  rpt strip_tac >>
  gvs[stmt_state_rel_observer_fields, lookup_var_def]
QED

Theorem compile_assign_value_typed_path:
  compile_assign_value cenv (Var p) LocMemory src F src_loc dty sty dyninfo mem_size sa = ((),sb) /\
  (!l. src <> Label l) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname, fty, sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  (!x. src = Var x ==> not_fresh_at sa x) /\ not_fresh_at sa p /\
  eval_operand src s = SOME sw /\ lookup_var p s = SOME w /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n w + type_memory_size dtv < dimword (:256) /\
  (src_loc <> SOME LocMemory ==>
    w2n sw + type_memory_size stv <= w2n w \/
    w2n w + type_memory_size dtv <= w2n sw) /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\ sty <> dty /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  type_memory_size stv < dimword (:256) /\
  expr_val_at cenv cx sty se sa es v src s /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr cenv es.scopes p /\ MEM inst (fn_insts func) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
  local_ptrs_reserved cenv sa /\ type_memory_size dtv <= sz /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      (stmt_state_rel ctx func cenv cx
        (es with scopes :=
          (sc |+ (id, <|assignable := a; type := dtv; value := v; popped := []|>)) :: rest) t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry)) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  Cases_on `src_loc = SOME LocMemory`
  >- (gvs[compile_assign_value_def, compile_store_memory_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> gvs[]) >>
      rename1 `compile_alloc_buffer _ sa = (buf,sm)` >>
      rename1 `compile_copy_memory _ src _ sm = ((),sn)` >>
      `cs_extends sa sm` by metis_tac[compile_alloc_buffer_extends] >>
      `cs_extends sm sn` by
        (drule_all compile_copy_memory_extends >> strip_tac >>
         gvs[same_blocks_def] >> irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
      `ci_mono sn sb` by
        (mp_tac (cj 1 ci_mono_typed_memory_family) >>
         disch_then (qspecl_then [`cenv`, `Var p`, `dty`, `buf.buf_operand`, `sty`, `sn`] mp_tac) >>
         simp[]) >>
      `cs_extends sn sb` by fs[ci_mono_def] >>
      `fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func` by
        metis_tac[fn_has_code_split, cs_extends_trans] >>
      `~is_word_type sty /\ ~is_bytestring_type sty` by
        metis_tac[normalize_return_source_kinds] >>
      `0 < type_memory_size stv` by metis_tac[normalize_return_source_positive] >>
      `val_footprint stv v = type_memory_size stv` by
        metis_tac[normalize_nonbytes_footprint] >>
      `w2n sw + type_memory_size stv <= s.vs_alloca_next` by
        (drule_all normalize_source_window >> strip_tac >> gvs[] >>
         metis_tac[optionTheory.SOME_11]) >>
      drule_all buffer_alloc_code >> strip_tac >>
      `type_memory_size stv < dimword (:256)` by decide_tac >>
      drule_all compile_alloc_buffer_forward >>
      disch_then (qx_choosel_then [`r`, `tw`]
        (MAP_EVERY assume_tac o CONJUNCTS)) >>
      qpat_x_assum `?q. buf.buf_operand = Var q /\ _` strip_assume_tac >>
      `w2n sw + type_memory_size stv <= w2n tw \/
       w2n tw + type_memory_size stv <= w2n sw` by
        (qpat_x_assum `(_ /\ w2n tw = s.vs_alloca_next) \/ _` strip_assume_tac
         >- decide_tac >>
         `not_local_ptr cenv es.scopes (STRING #"%" (toString sa.cs_next_var))` by
           (irule local_ptrs_reserved_fresh >> goal_assum (drule_at Any) >> simp[]) >>
         drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)
           externalReturnNormalizeMemTheory.normalize_alloca_source_separate >>
         disch_then (drule_at (Pat `MEM _ _`)) >>
         simp[venomInstTheory.mk_inst_def] >>
         metis_tac[]) >>
      `eval_operand src r = SOME sw` by
        (Cases_on `src` >> gvs[eval_operand_def] >> metis_tac[]) >>
      drule_all placeMemoryTypedPrimitiveTheory.compile_copy_memory_forward >>
      disch_then (qspec_then `ctx` (qx_choose_then `u` (MAP_EVERY assume_tac o CONJUNCTS))) >>
      `val_in_memory stv v (w2n tw) u.vs_memory` by
        (irule valueCopyTheory.val_in_memory_relocate >> simp[] >>
         qexistsl_tac [`w2n sw`, `type_memory_size stv`, `s.vs_memory`] >> simp[]) >>
      `copy_static u = copy_static r` by
        (gvs[copy_static_def, venom_state_component_equality]) >>
      `stmt_state_rel ctx func cenv cx es u` by
        (irule copy_buffer_state_rel_frame >>
         qexistsl_tac [`w2n tw`,
           `mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_size stv))]
             [STRING #"%" (toString sa.cs_next_var)]`,
           `r`, `sa`, `type_memory_size stv`] >>
         simp[] >> conj_tac
         >- (rpt strip_tac >>
             qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> _`
               (qspecl_then [`name`, `lb`, `len`] mp_tac) >>
             simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
         conj_tac
         >- (rpt strip_tac >>
             qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ u.vs_memory = _`
               (qspecl_then [`off`, `len`] mp_tac) >> simp[]) >>
         gvs[venomInstTheory.mk_inst_def]) >>
      `inst.inst_id <> sa.cs_next_id` by
        (strip_tac >>
         `inst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_size stv))]
           [STRING #"%" (toString sa.cs_next_var)]` by
           (irule localPtrsPropsTheory.fn_inst_ids_distinct_inj >>
            simp[venomInstTheory.mk_inst_def] >>
            qexists_tac `func` >> gvs[venomInstTheory.mk_inst_def]) >>
         fs[venomInstTheory.mk_inst_def, not_fresh_at_def] >>
         qpat_x_assum `!n. sa.cs_next_var <= n ==> p <> _`
           (qspec_then `sa.cs_next_var` mp_tac) >> simp[]) >>
      `FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n w,sz)` by metis_tac[] >>
      `w2n tw + type_memory_size stv <= w2n w \/
       w2n w + type_memory_size dtv <= w2n tw` by
        (`allocas_non_overlapping u` by fs[stmt_state_rel_def, alloca_inv_def] >>
         fs[allocas_non_overlapping_def] >>
         first_x_assum (qspecl_then [`sa.cs_next_id`, `inst.inst_id`,
           `w2n tw`, `type_memory_size stv`, `w2n w`, `sz`] mp_tac) >>
         simp[] >> decide_tac) >>
      `not_fresh_at sn p /\ not_fresh_at sn p' /\ local_ptrs_reserved cenv sn` by
        (`ci_mono sa sm /\ ci_mono sm sn` by
           metis_tac[exprLoweringPropsTheory.ci_mono_compile_alloc_buffer,
                     exprLoweringPropsTheory.ci_mono_compile_copy_memory, pairTheory.SND] >>
         `sa.cs_next_var <= sn.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var` by
           (fs[ci_mono_def] >> decide_tac) >>
         metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var,
                   loweringShapeDefsTheory.not_fresh_at_mono]) >>
      `lookup_var p u = SOME w /\ eval_operand buf.buf_operand u = SOME tw` by
        (fs[eval_operand_def] >> metis_tac[]) >>
      drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)
        typed_store_declare_path >>
      disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ u`)) >>
      disch_then (drule_at (Pat `val_in_memory _ _ (w2n tw) _`)) >>
      simp[] >>
      disch_then (qspecl_then [`sz`, `inst`, `id`, `a`] mp_tac) >>
      (impl_tac >- metis_tac[]) >>
      disch_then (qx_choose_then `t` strip_assume_tac) >>
      `gas_marked_path F ctx func s (0 + 0) (OK u)` by
        metis_tac[fragGasModeTheory.gas_marked_path_then] >>
      `gas_marked_path F ctx func s 0 (OK t)` by
        metis_tac[fragGasModeTheory.gas_marked_path_then, arithmeticTheory.ADD] >>
      `sa.cs_next_var <= sn.cs_next_var` by
        (mp_tac (Q.SPECL [`type_memory_size stv`, `sa`]
           exprLoweringPropsTheory.ci_mono_compile_alloc_buffer) >>
         mp_tac (Q.SPECL [`buf.buf_operand`, `src`, `type_memory_size stv`, `sm`]
           exprLoweringPropsTheory.ci_mono_compile_copy_memory) >>
         simp[] >> simp[ci_mono_def] >> decide_tac) >>
      qexists_tac `t` >> simp[] >>
      metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
  `compile_store_memory_typed cenv (Var p) dty src sty sa = ((),sb)` by
    gvs[compile_assign_value_def, compile_store_memory_def] >>
  irule typed_store_declare_path >> metis_tac[]
QED
