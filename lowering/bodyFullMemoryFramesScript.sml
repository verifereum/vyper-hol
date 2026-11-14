(* Constructor-compatible frames for local overwrites and buffer allocation. *)
Theory bodyFullMemoryFrames
Ancestors
  bodySim exprSimHyps structFieldsProps bodyStorageMetadata compileVyper immutableLocationProps
  vyperTypeInvariants vyperTypeSystem vyperTypeContract vyperTypeContractStaticMaps
  exprSimHypsDefs gasContext immSectionDead
  assignTuplePtrLocalCopyGhost assignTuplePtrStoreWord assignTuplePtrCopyLen
  bodyPtrDefs robustCopyTransportPtr localPtrsProps compileEnv loweringStateRelDefs
  storageNormalizationOwnershipPtr reasonAllocationFramePtr exprSimAlloc
  assignTuplePtrAlloc exprSimPtrLiteralBuffer
  loweringHalt exprLoweringProps bodyFullUnwrapRun fragExecPtr ptrSafetyTransport
  fragGasOriginPtr fragGasSeqPtr fragExec emitHelper emitHelperProps
  unitTransformDefs memSafeRun contextCodegenRel codegenRel fragExecMem
  context ptrDiscipline ptrSafeRun venomInst venomInstProofs venomExecSemantics
  venomState vyperState vyperLookup finite_map pred_set list rich_list words

(* A positive local cannot sit inside the contiguous immutable prefix. *)
Theorem immutable_intervals_lower_bound[local]:
  !tops off b n.
    off <= b /\ 0 < n /\
    (!pre vis name ty slot post.
      tops = pre ++ VariableDecl vis Immutable name ty slot :: post ==>
      regions_disjoint (off + compute_immutables_len sft pre)
        (type_mem_bytes sft ty) b n) ==>
    off + compute_immutables_len sft tops <= b
Proof
  Induct >- simp[compute_immutables_len_def] >> rpt gen_tac >> strip_tac >>
  `!pre vis name ty slot post.
    tops = pre ++ VariableDecl vis Immutable name ty slot :: post ==>
    regions_disjoint (off + compute_immutables_len sft [h] +
      compute_immutables_len sft pre) (type_mem_bytes sft ty) b n` by
    (rpt strip_tac >>
     qpat_x_assum `!pre vis name ty slot post. _`
       (qspecl_then [`h::pre`,`vis`,`name`,`ty`,`slot`,`post`] mp_tac) >>
     ONCE_REWRITE_TAC [immutable_len_cons] >>
     asm_simp_tac bool_ss [CONJUNCT1 compute_immutables_len_def,
       APPEND, arithmeticTheory.ADD_CLAUSES, arithmeticTheory.ADD_ASSOC]) >>
  `off + compute_immutables_len sft [h] <= b` by
    (Cases_on `h` >> simp[compute_immutables_len_def] >>
     CASE_TAC >> gvs[compute_immutables_len_def] >>
     qpat_x_assum `!pre vis name ty slot post. h::tops = _ ==> _`
       (qspec_then `[]` mp_tac) >>
     simp[compute_immutables_len_def,regions_disjoint_def] >> decide_tac) >>
  ONCE_REWRITE_TAC [immutable_len_cons] >>
  first_x_assum (qspecl_then [`off + compute_immutables_len sft [h]`,`b`,`n`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  rewrite_tac[arithmeticTheory.ADD_ASSOC]
QED

Theorem body_full_local_region_lower_bound:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es0 /\
  stmt_state_rel H ctx func cenv cx es s /\
  local_region cenv es.scopes s id b n /\ 0 < n /\
  dead_lo_ok H D lo cenv cx ==> lo <= b
Proof
  strip_tac >> reverse (Cases_on `cenv.ce_is_ctor`) >- gvs[dead_lo_ok_def] >>
  `env_context_consistent env cx` by
    fs[expr_sim_inv_def,env_consistent_def] >>
  `get_module_code cx NONE = SOME tops /\
   cenv.ce_module = NONE /\
   cenv.ce_struct_fields = make_struct_fields_map tops /\
   cenv.ce_module_vars = add_immutable_locations
     (get_struct_fields (make_struct_fields_map tops))
     tops 0 (add_module_var_locations tops FEMPTY) /\
   cenv.ce_module_var_type = build_var_type_map tops /\
   ALL_DISTINCT (FLAT (MAP
     (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
    fs[body_inv_def,cenv_module_pins_def] >>
  `!pre vis name ty slot post.
    tops = pre ++ VariableDecl vis Immutable name ty slot :: post ==>
    regions_disjoint
      (compute_immutables_len (get_struct_fields cenv.ce_struct_fields) pre)
      (type_mem_bytes (get_struct_fields cenv.ce_struct_fields) ty) b n` by
    suspend "intervals" >>
  `compute_immutables_len (get_struct_fields cenv.ce_struct_fields) tops <= b` by
    (qspecl_then [`tops`,`0`,`b`,`n`] mp_tac
      (Q.INST [`sft` |-> `get_struct_fields cenv.ce_struct_fields`]
        immutable_intervals_lower_bound) >>
     PURE_REWRITE_TAC [arithmeticTheory.ADD_CLAUSES] >>
     (impl_tac >-
       (conj_tac >- decide_tac >> conj_tac >> first_assum ACCEPT_TAC)) >>
     simp_tac bool_ss []) >>
  qpat_assum `cenv.ce_struct_fields = _` (fn th =>
    qpat_x_assum `compute_immutables_len _ tops <= b`
      (assume_tac o REWRITE_RULE [th])) >>
  fs[dead_lo_ok_def,cx_tops_def,imm_len_def]
QED

Resume body_full_local_region_lower_bound[intervals]:
  rpt gen_tac >> strip_tac >>
  `MEM (VariableDecl vis Immutable name ty slot) tops` by simp[] >>
  `~MEM (NONE,name)
    (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) post))` by
    (qpat_x_assum `ALL_DISTINCT _` mp_tac >>
     qpat_assum `tops = _` (fn th => REWRITE_TAC [th]) >>
     simp[ALL_DISTINCT_APPEND,toplevel_vtype_keys_toplevel_def]) >>
  `!v nm t sl. MEM (VariableDecl v Immutable nm t sl) post ==> nm <> name` by
    metis_tac[module_toplevel_vtype_key_MEM_Variable] >>
  `FLOOKUP cenv.ce_module_vars (NONE,name) = SOME (ImmutableLoc
    (compute_immutables_len (get_struct_fields cenv.ce_struct_fields) pre))` by
    (qpat_assum `cenv.ce_struct_fields = _` (fn sf =>
       qpat_assum `cenv.ce_module_vars = _` (fn vs =>
         PURE_REWRITE_TAC [REWRITE_RULE [GSYM sf] vs])) >>
     qpat_assum `tops = _` (fn th => PURE_REWRITE_TAC [th]) >>
     irule (SIMP_RULE bool_ss [arithmeticTheory.ADD_CLAUSES]
       (Q.INST [`off` |-> `0`] add_immutable_locations_declaration_lookup)) >>
     metis_tac[]) >>
  `cenv.ce_module_var_type (NONE,name) = SOME ty` by
    metis_tac[build_maps_variable] >>
  `FLOOKUP env.bare_globals (NONE,name) = SOME ty` by
    (fs[env_context_consistent_def,bare_globals_complete_def] >> metis_tac[]) >>
  `?tv. evaluate_type (get_tenv cx) ty = SOME tv` by suspend "type" >>
  `type_mem_bytes (get_struct_fields cenv.ce_struct_fields) ty =
    type_memory_size tv` by
    metis_tac[type_mem_bytes_type_memory_bytes,expr_sim_inv_memory_size] >>
  `immutable_decl_sep cenv cx es.scopes s.vs_vars s.vs_allocas s.vs_alloca_next` by
    fs[stmt_state_rel_def,immutable_alloca_sep_def] >>
  fs[immutable_decl_sep_alt] >> metis_tac[]
QED

Resume body_full_local_region_lower_bound[type]:
  `FLOOKUP env.toplevel_vtypes (NONE,name) = SOME (Type ty)` by
    metis_tac[env_context_consistent_bare_global_find_NONE] >>
  qpat_assum `env_context_consistent _ _`
    (strip_assume_tac o REWRITE_RULE [env_context_consistent_def]) >>
  qpat_x_assum `!src id vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt ==> _`
    (qspecl_then [`NONE`,`name`,`Type ty`] mp_tac) >>
  simp[well_formed_vtype_def,well_formed_type_def,optionTheory.IS_SOME_EXISTS]
QED

Finalise body_full_local_region_lower_bound

Theorem body_full_local_scope_ghost_post:
  ghost_inv_at D lo d cenv cx es G tn s /\
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME dst /\
  local_ptrs_rel func cenv es.scopes s /\ local_ptrs_reserved cenv sa /\
  local_region cenv es.scopes s id (w2n dst) sz /\ n <= sz /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
    val_in_memory entry.type v (w2n dst) mem) /\
  (!i. ~(w2n dst <= i /\ i < w2n dst+n) ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tf.t_mem <=> i IN tn.t_mem)) /\
  stor_taint_ok_at D tf t /\
  mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
  (!i. i < lo /\ i IN tf.t_mem ==> i IN tn.t_mem) /\
  allocas_from lo t /\ lo <= t.vs_alloca_next ==>
  ghost_inv_at D lo d cenv cx
    (es with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest)
    Gf tf t
Proof
  strip_tac >>
  `!name x cap. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var x) cap) ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)` by
    (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  rewrite_tac[ghost_inv_at_def] >> conj_tac >- suspend "locals" >>
  `return_buf_ptr d cenv Gf tf t` by
    (Cases_on `d` >> simp[return_buf_ptr_def] >> PairCases_on `x` >>
     fs[ghost_inv_at_def,return_buf_ptr_def] >>
     irule ptr_covers_lookup_frame >> goal_assum (drule_at Any) >> simp[]) >>
  simp[] >> fs[ghost_inv_at_def] >> metis_tac[local_ptrs_reserved_def]
QED

Resume body_full_local_scope_ghost_post[locals]:
  rpt gen_tac >> strip_tac >> fs[] >>
  drule_all local_copy_scope_lookup_ptr >> strip_tac >>
  `lookup_var p' t = lookup_var p' s /\ FLOOKUP Gf p' = FLOOKUP G p' /\
   op_taint tf (Var p') = op_taint tn (Var p')` by metis_tac[] >>
  conj_tac
  >- (irule ptr_covers_lookup_frame >> goal_assum (drule_at Any) >>
      fs[ghost_inv_at_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> Cases_on `name = id`
  >- (gvs[] >> metis_tac[]) >>
  `lookup_var p' s = SOME w` by metis_tac[] >> gvs[] >>
  drule_all local_region_other_footprint_ptr >> strip_tac >>
  irule robust_val_in_memory_exterior_frame >> simp[] >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`s.vs_memory`,`t.vs_memory`,`tn.t_mem`,`tf.t_mem`] >>
  simp[] >> fs[ghost_inv_at_def] >> metis_tac[]
QED

Finalise body_full_local_scope_ghost_post

Theorem body_full_memory_ghost_frame:
  ghost_inv_at D lo d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!name entry p sz w.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w ==>
    val_wf entry.type entry.value /\
    (!i. w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
      i NOTIN writes)) /\
  (!i. i NOTIN writes ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tf.t_mem <=> i IN tn.t_mem)) /\
  mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
  (!i. i < lo /\ i IN tf.t_mem ==> i IN tn.t_mem) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables /\
  allocas_from lo t /\ lo <= t.vs_alloca_next ==>
  ghost_inv_at D lo d cenv cx es Gf tf t
Proof
  strip_tac >>
  `!p sz. not_fresh_at sa p /\ ptr_covers G tn p s sz ==>
    ptr_covers Gf tf p t sz` by
    (rw[ptr_covers_def] >> metis_tac[]) >>
  fs[ghost_inv_at_def,stor_taint_ok_at_def] >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      conj_tac >- metis_tac[] >>
      rpt gen_tac >> strip_tac >>
      irule robust_val_in_memory_exterior_frame >>
      conj_tac >- metis_tac[] >>
      qexistsl_tac [`s.vs_memory`,`t.vs_memory`,`tn.t_mem`,`tf.t_mem`,`writes`] >>
      metis_tac[])
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME rb)` >> PairCases_on `rb` >>
      gvs[return_buf_ptr_def] >> metis_tac[])
  >- (rpt strip_tac >> fs[local_ptrs_reserved_def] >> metis_tac[])
QED

Theorem body_full_alloc_buffer_path:
  stmt_state_rel H ctx func cenv cx es s /\
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
  local_ptrs_reserved cenv sa /\ fn_inst_ids_distinct func /\
  n < dimword (:256) /\ ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u root b G1 tn1.
    buf.buf_operand = Var root /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,G1,tn1)) /\
    (!H'. stmt_state_rel H' ctx func cenv cx es s ==>
      stmt_state_rel H' ctx func cenv cx es u) /\
    (!D d. ghost_inv_at D lo d cenv cx es G tn s ==>
      ghost_inv_at D lo d cenv cx es G1 tn1 u) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (b,n) /\
    lo <= b /\ b+n < dimword (:256) /\ lookup_var root u = SOME (n2w b) /\
    ptr_covers G1 tn1 root u n /\
    (!name a len. local_region cenv es.scopes u name a len ==>
      regions_disjoint b n a len) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
      regions_disjoint b n a len) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
      op_taint tn1 (Var x) = op_taint tn (Var x)) /\
    (!x cap. not_fresh_at sa x /\ ptr_covers G tn x s cap ==>
      ptr_covers G1 tn1 x u cap) /\
    not_fresh_at sb root /\
    (!x. not_fresh_at sa x ==> not_fresh_at sb x) /\
    allocas_from lo u /\ lo <= u.vs_alloca_next /\
    u.vs_memory = s.vs_memory /\ u.vs_labels = s.vs_labels /\
    u.vs_accounts = s.vs_accounts /\ u.vs_call_ctx = s.vs_call_ctx /\
    u.vs_transient = s.vs_transient /\ u.vs_immutables = s.vs_immutables /\
    (!i. ~(b <= i /\ i < b+n) ==> (i IN tn1.t_mem <=> i IN tn.t_mem)) /\
    tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all normalization_alloc_buffer_ownership >>
  disch_then (qspecl_then [`PG`,`G`,`tn`] strip_assume_tac) >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `p = STRING #"%" (toString sa.cs_next_var)` by
    (qpat_x_assum `buf.buf_operand = Var p` mp_tac >> simp[]) >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [p]` >>
  qabbrev_tac `G1 = step_prov PG G inst t` >>
  qabbrev_tac `tn1 = step_taint inst s t tn` >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ [inst] /\
   sb.cs_blocks = sa.cs_blocks` by suspend "code" >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (irule step_inst_allocas_from >>
     qexistsl_tac [`ctx`,`0`,`inst`,`s`] >>
     simp[Abbr `inst`,step_inst_non_invoke,mk_inst_def]) >>
  `lo <= w2n w` by (fs[allocas_from_def] >> metis_tac[]) >>
  `~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
   t.vs_labels = s.vs_labels /\ t.vs_accounts = s.vs_accounts /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_transient = s.vs_transient /\
   t.vs_immutables = s.vs_immutables` by suspend "fields" >>
  `(!i. ~(w2n w <= i /\ i < w2n w+n) ==> (i IN tn1.t_mem <=> i IN tn.t_mem)) /\
   tn1.t_stor = tn.t_stor /\
   tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm` by suspend "taints" >>
  `!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
    op_taint tn1 (Var x) = op_taint tn (Var x)` by suspend "old" >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sb.cs_current_insts`,
    `p`,`w2n w`,`G1`,`tn1`] >>
  simp[lookup_var_def] >>
  conj_tac >- suspend "path" >>
  conj_tac >- suspend "state" >>
  conj_tac >- suspend "ghost" >>
  conj_tac >- (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- gvs[eval_operand_def,lookup_var_def] >>
  conj_tac >- (qpat_x_assum `!name a len. local_region _ _ t _ _ _ ==> _` mp_tac >>
    simp[local_region_def,lookup_var_def]) >>
  suspend "post"
QED

Resume body_full_alloc_buffer_path[post]:
  rpt conj_tac
  >- (rpt strip_tac >> metis_tac[])
  >- (rpt strip_tac >> fs[lookup_var_def] >> metis_tac[])
  >- (rpt strip_tac >> irule ptr_covers_lookup_frame >>
      goal_assum (drule_at Any) >> fs[lookup_var_def]) >>
  fs[allocas_from_def] >> rpt strip_tac >> metis_tac[]
QED

Resume body_full_alloc_buffer_path[code]:
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[compile_alloc_buffer_def,emit_op_def,comp_bind_def,comp_ignore_bind_def,
    comp_return_def,fresh_var_def,fresh_id_def,emit_def,Abbr `inst`] >>
  strip_tac >> gvs[]
QED

Resume body_full_alloc_buffer_path[fields]:
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[Abbr `inst`,step_inst_base_opcode_eqs,mk_inst_def,exec_alloca_def,
    AllCaseEqs(),update_var_def] >>
  rpt strip_tac >> gvs[]
QED

Resume body_full_alloc_buffer_path[taints]:
  conj_tac
  >- (qunabbrev_tac `inst` >> qpat_x_assum `p = _` SUBST_ALL_TAC >>
      drule_all alloca_step_exterior_ghost_ptr >>
      disch_then (qspecl_then [`tn`,`PG`,`G`] strip_assume_tac) >>
      fs[Abbr `tn1`] >> first_assum ACCEPT_TAC) >>
  simp[Abbr `tn1`,Abbr `inst`,normalization_alloca_key_taints]
QED

Resume body_full_alloc_buffer_path[ghost]:
  rpt strip_tac >> irule body_full_memory_ghost_frame >>
  fs[allocas_from_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G`,`s`,`sa`,`tn`,`{i | w2n w <= i /\ i < w2n w+n}`] >>
  simp[] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p'` by metis_tac[local_ptrs_reserved_def] >>
      `lookup_var p' t = SOME w'` by metis_tac[] >>
      drule_all literal_ptr_local_footprint_exterior >> simp[])
  >- (rpt strip_tac >> fs[lookup_var_def] >> metis_tac[])
  >- (rpt strip_tac >>
      `~(w2n w <= i /\ i < w2n w+n)` by decide_tac >> metis_tac[]) >>
  fs[lookup_var_def] >> rpt strip_tac >>
  qpat_x_assum `!j. _ ==> (j IN tn1.t_mem <=> j IN tn.t_mem)`
    (qspec_then `i` mp_tac) >>
  `~(w2n w <= i)` by decide_tac >> simp[]
QED

Resume body_full_alloc_buffer_path[old]:
  rpt strip_tac >>
  `x <> p` by metis_tac[] >>
  simp[] >> qunabbrev_tac `inst` >>
  qpat_x_assum `p = _` SUBST_ALL_TAC >>
  drule_all reason_alloca_old_metadata >>
  disch_then (qspecl_then [`PG`,`G`,`tn`] mp_tac) >>
  simp[Abbr `G1`,Abbr `tn1`] >> metis_tac[]
QED

Resume body_full_alloc_buffer_path[path]:
  gen_tac >>
  `inst_seq_ptr D lo ctx func PG G tn [inst] s G1 tn1` by
    (simp[inst_seq_ptr_def,Abbr `G1`,Abbr `tn1`,Abbr `inst`] >>
     irule ptr_inst_ok_lower_bound_transport >> simp[] >> qexists_tac `0` >>
     simp[ptr_inst_ok_alloca]) >>
  qspecl_then [`[inst]`,`sa`,`sb`,`s`,`t`,`G`,`tn`,`G1`,`tn1`]
    mp_tac emitted_origin_ptr_path >>
  simp[Abbr `inst`,mk_inst_def,is_terminator_def,run_inst_seq_def,
    run_inst_seq_mem_ok_def,inst_mem_below_frontier_def,inst_dload_in_section_def,
    source_memory_write_ranges_def,source_memory_read_ranges_def]
QED

Resume body_full_alloc_buffer_path[state]:
  rpt strip_tac >>
  qpat_x_assum `stmt_state_rel H ctx func cenv cx es s` kall_tac >>
  qpat_x_assum `stmt_state_rel H ctx func cenv cx es t` kall_tac >>
  drule_all normalization_alloc_buffer_ownership >>
  disch_then (qspecl_then [`PG`,`G`,`tn`] strip_assume_tac) >>
  gvs[Abbr `inst`,stmt_state_rel_inst_idx]
QED

Finalise body_full_alloc_buffer_path
