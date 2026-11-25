(* The immutable-array length slice changes only the cursor and fresh registers. *)
Theory bodyForArrayImmutableLengthMods
Ancestors
  bodyForArrayRouteMods bodyFullTargetArrayLoad augAssignFullImmutableValidLoad
  immutableRegionFrameProps immutableRegionTypingProps bodyInvMetadataProps
  exprBodyPreTypingProps vyperTypeEvalStoragePreservation vyperPlaceTyping vyperArray
  exprSimUnwrap exprPtrUnwrapCodeEdges valueEncodingProps stateFrame targetSubscriptMemory
  forNestedArrayCapture bodyPtrBopInRepresentation bodyFullHashKeccakFixed
  emitHelperProps exprLoweringProps compileEnv context ptrDiscipline words arithmetic
  valueEncodingDefs codegenRel contextCodegenRel memSafeRun unitTransformDefs
  venomInst venomState bodyPtrDefs fragGasOriginPtr fragGasOriginPtrDead
  loweringShapeRules bodyInvSplit loweringStateRelDefs bodyFullPostsMods loweringPosts
  exprBodyPreProps exprBodyPreCallSafetyProps exprSimHypsDefs vyperTypeEvalSoundness
  vyperTypeInvariants vyperState vyperBareGlobalName vyperContext vyperValueOperation
  bodyPtrBopInMemoryContents vyperTyping exprSimCopy vyperTypeValues list finite_map
  valueEncoding exprLowering vyperAST bodyFullShadowBodyInv vyperValue
  logValueFramePtr valueEncodingTyping

Theorem immutable_array_runtime_loader[local]:
  compile_ptr_load F imm LocCode addr sa = (len,sb) /\
  eval_operand addr s = SOME a /\ op_taint tn addr = {} /\
  w2n a <= LENGTH s.vs_data_section /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  mem_word_at (w2n a) s.vs_data_section = w ==>
  ?t G' tn'. array_length_loader_ok F imm LocCode addr w sa len sb lo ctx func PG
    s G tn t G' tn' /\ op_prov G' len = NONE /\ op_taint tn' len = {}
Proof
  simp[compile_ptr_load_def,compile_imm_load_word_runtime] >> strip_tac >>
  `?out. len = Var out` by (drule emitted_insts_emit_op >> simp[]) >> gvs[] >>
  qabbrev_tac `i = mk_inst sa.cs_next_id DLOAD [addr] [out]` >>
  qabbrev_tac `u = update_var out (mem_word_at (w2n a) s.vs_data_section) s` >>
  `array_length_step_ok lo ctx func DLOAD [addr] (mem_word_at (w2n a) s.vs_data_section)
     sa out sb s G tn` by
    (simp[array_length_step_ok_def] >> conj_tac
     >- simp[Abbr `i`,Abbr `u`,exprSimUnwrapTheory.step_DLOAD,mem_word_at_def] >>
     simp[Abbr `i`,access_ok_def,taint_ok_def,source_memory_read_ranges_def,
          source_memory_write_ranges_def,inst_mem_below_frontier_def,
          inst_dload_in_section_def,mk_inst_def]) >>
  qexistsl [`u with vs_inst_idx := LENGTH sb.cs_current_insts`, `step_prov PG G i u`,
            `step_taint i s u tn`] >>
  conj_tac
  >- (simp[array_length_loader_ok_def,compile_ptr_load_def,compile_imm_load_word_runtime] >>
      qexists `DLOAD` >> simp[Abbr `i`,Abbr `u`]) >>
  simp[Abbr `i`,runtime_code_load_clean] >> irule step_prov_out_none >>
  simp[mk_inst_def] >> irule out_prov_other_none >> simp[mk_inst_def]
QED

Theorem immutable_array_length_run[local]:
  (if dyn then compile_ptr_load ctor imm LocCode addr
   else comp_return (Lit (n2w cnt))) sa = (len,sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ copy_old_operand sa addr /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (dyn ==> eval_operand addr s = SOME a /\
    op_taint tn addr = {} /\ op_prov G addr = NONE /\
    (if ctor then
      w2n a + 32 <= lo /\ mload (w2n a) s = n2w cnt /\
      mem_word_taint tn.t_mem (w2n a) = {} /\
      (!rb. imm = SOME rb ==> eval_operand rb s = SOME 0w /\
        copy_old_operand sa rb /\ op_taint tn rb = {} /\ op_prov G rb = NONE)
    else w2n a <= LENGTH s.vs_data_section /\
      mem_word_at (w2n a) s.vs_data_section = n2w cnt)) ==>
  ?t G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    eval_operand len t = SOME (n2w cnt) /\ op_prov G' len = NONE /\ op_taint tn' len = {} /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  Cases_on `dyn` >> simp[] >> strip_tac
  >- (Cases_on `ctor` >> gvs[]
      >- (fs[compile_ptr_load_def] >> drule_all augassign_ctor_word_load_at >>
          disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
          qexistsl [`u`,`G1`,`tn1`] >> fs[state_frame_def]) >>
      `?t G' tn'. array_length_loader_ok F imm LocCode addr (n2w cnt)
         sa len sb lo ctx func PG s G tn t G' tn'` suffices_by
        (disch_then assume_tac >>
         drule_all (SIMP_RULE bool_ss [COND_CLAUSES,TRUTH]
           (Q.SPEC `T` (GEN ``dyn:bool`` array_length_joint))) >>
         disch_then (qspecl_then [`explicit`,
           `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`]
             strip_assume_tac) >>
         qexistsl [`t`,`G'`,`tn'`] >> simp[] >> conj_tac
         >- (gen_tac >> irule gas_origin_ptr_path_from_no_dead >> first_assum ACCEPT_TAC) >>
         `op_prov G' len = NONE /\ op_taint tn' len = {}` by
           (qpat_x_assum `array_length_loader_ok F _ _ _ _ _ _ _ _ _ _ _ _ _ _ t G' tn'`
               (strip_assume_tac o SIMP_RULE (srw_ss()) [array_length_loader_ok_def,compile_ptr_load_def,
                                                compile_imm_load_word_runtime]) >>
             `opc = DLOAD` by
               (qpat_x_assum `emit_op DLOAD _ = emit_op opc _` (mp_tac o C AP_THM ``sa:compile_state``) >>
                simp[emit_op_eq,compile_state_component_equality,mk_inst_def,
                     instruction_component_equality]) >>
             gvs[runtime_code_load_clean] >> irule step_prov_out_none >>
             simp[mk_inst_def] >> irule out_prov_other_none >> simp[mk_inst_def]) >>
         fs[array_length_frame_def,op_taint_def,venom_state_component_equality]) >>
      drule_all immutable_array_runtime_loader >>
      disch_then (qspecl_then [`func`,`PG`,`G`] strip_assume_tac) >>
      goal_assum drule >> simp[]) >>
  gvs[comp_return_def] >> qexistsl [`s`,`G`,`tn`] >>
  simp[eval_operand_def,op_prov_def,op_taint_def,state_frame_def,gas_origin_ptr_path_rules]
QED

(* The physical representation is read at the captured address, not by
   replaying the expression or assuming the active module owns the bytes. *)
Theorem immutable_array_selected_bytes[local]:
  contract_inv mods exps ctx c cx /\ expr_sim_inv_mods mods c cx env em /\
  immutable_frame_mods func c cx em s /\ dead_lo_ok_mods H D lo c cx /\
  ghost_inv_at_mods D lo d c cx em G tn s /\
  immutable_holds_mods c cx ty raw bw em s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ read_result cx raw em = (INL v,em) ==>
  (if c.ce_is_ctor then w2n bw + type_memory_size tv <= lo /\
     (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n bw) m)
   else w2n bw + type_memory_size tv <= LENGTH s.vs_data_section /\
     val_in_memory tv v (w2n bw) s.vs_data_section)
Proof
  strip_tac >>
  qhdtm_x_assum `immutable_holds_mods`
    (strip_assume_tac o REWRITE_RULE [immutable_holds_mods_def,immutable_holds_def]) >>
  Cases_on `ALOOKUP em.immutables cx.txn.target` >>
  gvs[compile_env_accfupds,sub_layout_def] >>
  `immutables_rel_mods c cx.txn.target c.ce_is_ctor em s` by fs[immutable_frame_mods_def] >>
  Cases_on `c.ce_is_ctor` >> simp[]
  >- (drule_all (SIMP_RULE bool_ss []
        (Q.INST [`entry` |-> `em`, `es` |-> `em`] qualified_immutable_ctor_frame_mods)) >>
      strip_tac >> conj_tac >- decide_tac >>
      rpt strip_tac >> once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
      first_x_assum irule >> simp[]) >>
  `immutables_rel c cx.txn.target src F em s` by fs[immutables_rel_mods_def] >>
  qhdtm_x_assum `immutables_rel` mp_tac >> simp[immutables_rel_def] >>
  disch_then (drule_all_then strip_assume_tac) >>
  conj_tac >- decide_tac >> once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  first_x_assum irule >> simp[]
QED

Theorem immutable_array_header_word[local]:
  value_has_type (ArrayTV et (Dynamic cap)) (ArrayV av) /\
  (if ctor then type_memory_size (ArrayTV et (Dynamic cap)) + a <= lo /\
     (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
          val_in_memory (ArrayTV et (Dynamic cap)) (ArrayV av) a m)
   else type_memory_size (ArrayTV et (Dynamic cap)) + a <= LENGTH s.vs_data_section /\
     val_in_memory (ArrayTV et (Dynamic cap)) (ArrayV av) a s.vs_data_section) ==>
  if ctor then a + 32 <= lo /\ mload a s = n2w (array_length (ArrayTV et (Dynamic cap)) av) /\
     mem_word_taint tn.t_mem a = {}
  else a <= LENGTH s.vs_data_section /\
     mem_word_at a s.vs_data_section = n2w (array_length (ArrayTV et (Dynamic cap)) av)
Proof
  Cases_on `av` >> simp[value_has_type_def] >> Cases_on `ctor` >>
  simp[type_memory_size_def] >> strip_tac
  >- (`a + 32 <= lo` by decide_tac >> simp[] >> conj_tac
      >- (first_x_assum (qspec_then `s.vs_memory` mp_tac) >>
          simp[mem_agree_outside_def,val_in_memory_dynarray,mem_word_at_eq_mload,array_length_def]) >>
      drule dynarray_memory_header_clean >> simp[]) >>
  `a <= LENGTH s.vs_data_section` by decide_tac >> fs[val_in_memory_dynarray,array_length_def]
QED

Theorem immutable_array_length_count[local]:
  value_has_type (ArrayTV et bd) (ArrayV av) ==>
  LENGTH (array_elements (ArrayTV et bd) av) = array_length (ArrayTV et bd) av
Proof
  Cases_on `bd` >> Cases_on `av` >>
  simp[value_has_type_def,array_elements_length_sarray,array_elements_length_dyn]
QED

Theorem immutable_array_base_preserved[local]:
  copy_old_operand sa addr /\ t.vs_labels = s.vs_labels /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
  eval_operand addr s = SOME a ==>
  eval_operand addr t = SOME a /\ op_prov G' addr = op_prov G addr /\
  op_taint tn' addr = op_taint tn addr
Proof
  Cases_on `addr` >> simp[copy_old_operand_def,eval_operand_def,op_prov_def,op_taint_def]
QED

(* The item allocation can change memory above lo and remove taint. It
   need not preserve the entire immutable root, only this selected window. *)
Theorem immutable_array_above_lo[local]:
  val_wf (ArrayTV et bd) (ArrayV av) /\
  type_memory_size (ArrayTV et bd) + a <= lo /\
  (!m. mem_agree_outside old_taint old_mem m ==>
       val_in_memory (ArrayTV et bd) (ArrayV av) a m) /\
  (!i. i < lo ==> mem_bytes_at i 1 new_mem = mem_bytes_at i 1 old_mem) /\
  (!i. i < lo /\ i IN new_taint ==> i IN old_taint) ==>
  !m. mem_agree_outside new_taint new_mem m ==>
      val_in_memory (ArrayTV et bd) (ArrayV av) a m
Proof
  strip_tac >>
  `mem_bytes_at a (val_footprint (ArrayTV et bd) (ArrayV av)) new_mem =
   mem_bytes_at a (val_footprint (ArrayTV et bd) (ArrayV av)) old_mem` by
    (simp[val_footprint_def] >> irule abiDecodeStaticPropsTheory.mem_bytes_at_bytewise >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `!i. a <= i /\ i < a + val_footprint (ArrayTV et bd) (ArrayV av) /\ i IN new_taint ==>
       i IN old_taint` by
    (simp[val_footprint_def] >> rpt strip_tac >> first_x_assum irule >> simp[] >> decide_tac) >>
  rpt strip_tac >> irule robust_val_in_memory_footprint_frame >>
  simp[] >> qexistsl [`old_mem`,`new_mem`,`old_taint`,`new_taint`] >> simp[]
QED

Theorem for_array_immutable_length_ready_mods:
  expr_body_pre_mods mods c cx env e es /\ contract_inv mods exps ctx c cx /\
  expr_sim_inv_mods mods c cx env em /\ expr_type e = ArrayT elem bd /\
  post_value_type c e = expr_type e /\ bound_length bd <= n /\
  eval_expr cx e es = (INL (PlaceR (ImmutablePlace src name path)),em) /\
  vv_post_mods H ctx func c cx e es sa u0 s0 em (PlaceR (ImmutablePlace src name path)) vv s /\
  ptr_vv_ok cx (post_value_type c e) (PlaceR (ImmutablePlace src name path)) vv em G tn s /\
  dead_lo_ok_mods H D lo c cx /\ ghost_inv_at_mods D lo d c cx em G tn s /\
  local_ptrs_reserved c u0 /\ copy_old_operand u0 (vv_operand vv) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (case bd of
     Fixed k => comp_return (Lit (n2w k))
   | Dynamic k => compile_ptr_load c.ce_is_ctor c.ce_imm_alloca LocCode (vv_operand vv))
      u0 = (len_op,saL) /\ fn_has_code u0 saL func /\
  ~s.vs_halted /\ s.vs_current_bb = u0.cs_current_bb /\ s.vs_inst_idx = LENGTH u0.cs_current_insts ==>
  ?p tops off itv iv delta tv et av vs t G' tn'.
    vv = LocatedValue (ArrayT elem bd) p /\ p.ptr_location = LocCode /\
    ALOOKUP c.ce_modules src = SOME tops /\
    FLOOKUP c.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
    lookup_immutable cx em src name = SOME (itv,iv) /\
    mem_path_offset itv path = SOME (delta,tv) /\
    read_result cx (PlaceR (ImmutablePlace src name path)) em = (INL (ArrayV av),em) /\
    evaluate_type (get_tenv cx) elem = SOME et /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV et bd) /\
    value_has_type (ArrayTV et bd) (ArrayV av) /\ well_formed_type_value (ArrayTV et bd) /\
    val_wf (ArrayTV et bd) (ArrayV av) /\
    eval_iterator cx (Array e) es = (INL vs,em) /\
    vs = MAP Value (array_elements (ArrayTV et bd) av) /\
    compatible_bound (Dynamic n) (LENGTH vs) /\ LENGTH vs < dimword (:256) /\
    (!tail. array_iterator_results cx (expr_type e) (PlaceR (ImmutablePlace src name path))
       (em with gas_obs := tail) = (INL vs,em with gas_obs := tail)) /\
    (!D'. gas_origin_ptr_path (D',lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    eval_operand len_op t = SOME (n2w (LENGTH vs)) /\
    op_prov G' len_op = NONE /\ op_taint tn' len_op = {} /\
    eval_operand p.ptr_operand t = SOME (n2w (off+delta)) /\
    op_prov G' p.ptr_operand = NONE /\ op_taint tn' p.ptr_operand = {} /\
    ~t.vs_halted /\ t.vs_current_bb = saL.cs_current_bb /\ t.vs_inst_idx = LENGTH saL.cs_current_insts /\
    state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at u0 x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (if c.ce_is_ctor then w2n (n2w (off+delta):bytes32) + type_memory_size (ArrayTV et bd) <= lo /\
       (!m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
            val_in_memory (ArrayTV et bd) (ArrayV av) (w2n (n2w (off+delta):bytes32)) m) /\
       (!mem taint. (!i. i < lo ==> mem_bytes_at i 1 mem = mem_bytes_at i 1 t.vs_memory) /\
          (!i. i < lo /\ i IN taint ==> i IN tn'.t_mem) ==>
          !m. mem_agree_outside taint mem m ==>
              val_in_memory (ArrayTV et bd) (ArrayV av) (w2n (n2w (off+delta):bytes32)) m)
     else w2n (n2w (off+delta):bytes32) + type_memory_size (ArrayTV et bd) <= LENGTH t.vs_data_section /\
       val_in_memory (ArrayTV et bd) (ArrayV av) (w2n (n2w (off+delta):bytes32)) t.vs_data_section)
Proof
  strip_tac >>
  `~is_word_type (post_value_type c e)` by simp[is_word_type_def] >>
  drule_all_then strip_assume_tac for_array_immutable_operand_mods >>
  `!tr slot et b. PlaceR (ImmutablePlace src name path) <>
                  PlaceR (StoragePlace tr slot (ArrayTV et b))` by simp[] >>
  drule_all_then strip_assume_tac for_array_nonslot_vv_capture_mods >>
  drule_all_then assume_tac for_array_nonslot_result_replay_mods >>
  `evaluate_type (get_tenv cx) (ArrayT elem bd) = SOME (ArrayTV et bd)` by metis_tac[] >>
  `LENGTH vs = array_length (ArrayTV et bd) av` by simp[immutable_array_length_count] >>
  `LENGTH vs < dimword (:256)` by
    (drule_all target_memory_array_length_bound >> simp[]) >>
  `well_formed_type_value (ArrayTV et bd)` by
    (drule_then ACCEPT_TAC evaluate_type_well_formed_type_value) >>
  `stmt_state_rel H ctx func c cx em s /\ immutable_frame_mods func c cx em s /\
   immutable_holds_mods c cx (ArrayT elem bd) (PlaceR (ImmutablePlace src name path))
     (n2w (off+delta)) em s` by
    (`post_value_type c e = ArrayT elem bd` by metis_tac[] >>
     qpat_x_assum `post_value_type c e = expr_type e` kall_tac >>
     fs[vv_post_mods_def,vv_holds_mods_def]) >>
  drule_all_then assume_tac immutable_array_selected_bytes >>
  `op_taint tn p.ptr_operand = {} /\ op_prov G p.ptr_operand = NONE` by fs[ptr_vv_ok_def] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  qabbrev_tac `dyn = (case bd of Fixed _ => F | Dynamic _ => T)` >>
  `(if dyn then compile_ptr_load c.ce_is_ctor c.ce_imm_alloca LocCode p.ptr_operand
    else comp_return (Lit (n2w (LENGTH vs)))) u0 = (len_op,saL)` by
    (Cases_on `bd` >> fs[Abbr `dyn`,vv_operand_def,compatible_bound_def] >>
     Cases_on `av` >> gvs[value_has_type_def,array_length_def]) >>
  `copy_old_operand u0 p.ptr_operand` by fs[vv_operand_def] >>
  `(dyn ==> eval_operand p.ptr_operand s = SOME (n2w (off+delta)) /\
      op_taint tn p.ptr_operand = {} /\ op_prov G p.ptr_operand = NONE /\
      if c.ce_is_ctor then
      w2n (n2w (off+delta):bytes32) + 32 <= lo /\
      mload (w2n (n2w (off+delta):bytes32)) s = n2w (LENGTH vs) /\
      mem_word_taint tn.t_mem (w2n (n2w (off+delta):bytes32)) = {} /\
      (!rb. c.ce_imm_alloca = SOME rb ==> eval_operand rb s = SOME 0w /\
        copy_old_operand u0 rb /\ op_taint tn rb = {} /\ op_prov G rb = NONE)
    else w2n (n2w (off+delta):bytes32) <= LENGTH s.vs_data_section /\
      mem_word_at (w2n (n2w (off+delta):bytes32)) s.vs_data_section = n2w (LENGTH vs))` by
    (Cases_on `bd` >> fs[Abbr `dyn`] >>
     drule_all_then assume_tac immutable_array_header_word >>
     Cases_on `c.ce_is_ctor` >> fs[] >>
     rpt strip_tac >> `lo <> 0` by decide_tac >>
     drule_all_then assume_tac membership_immutable_base_value >>
     Cases_on `rb` >> fs[copy_old_operand_def,op_taint_def,op_prov_def,ghost_inv_at_mods_def] >>
     drule_all local_ptrs_reserved_imm_base >> simp[]) >>
  drule_all immutable_array_length_run >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
   t.vs_labels = s.vs_labels /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next` by fs[state_frame_def] >>
  `allocas_from lo t` by
    (simp[allocas_from_def] >> qpat_assum `allocas_from lo s`
      (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `val_wf (ArrayTV et bd) (ArrayV av)` by
    (drule (CONJUNCT1 valueEncodingTypingTheory.value_has_type_val_wf) >> simp[]) >>
  drule_all_then strip_assume_tac immutable_array_base_preserved >>
  qexistsl [`p`,`tops`,`off`,`itv`,`iv`,`delta`,`tv`,`et`,`av`,`vs`,`t`,`G'`,`tn'`] >>
  simp[] >> Cases_on `c.ce_is_ctor` >> fs[] >>
  rpt strip_tac >> drule_all immutable_array_above_lo >> simp[]
QED
