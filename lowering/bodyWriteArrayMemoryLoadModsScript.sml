(* Load the length of the current local array, after the index read. *)
Theory bodyWriteArrayMemoryLoadMods
Ancestors
  bodyWriteArrayPacketMods bodyFullTargetArrayLoad bodyFullShadowBodyInv
  bodyFullPostsMods bodyInvSplit bodyPtrBopInMemoryContents bodyPtrDefs
  targetSubscriptMemory loweringPosts loweringStateRelDefs stateRelProj
  exprSimProps exprLoweringProps exprSimHypsDefs vyperTypeInvariants
  vyperValueOperation vyperTyping vyperValue vyperState
  valueEncoding valueEncodingDefs valueEncodingProps words finite_map arithmetic
  context compileEnv emitHelperProps venomState venomInst venomExecSemantics
  ptrDiscipline memLocDefs contextCodegenRel codegenRel unitTransformDefs memSafeRun

Theorem write_array_local_root_type[local]:
  expr_sim_inv_mods mods cenv cx env es /\
  lookup_scopes id es.scopes = SOME entry /\ cenv.ce_var_type id = SOME ty ==>
  evaluate_type (get_tenv cx) ty = SOME entry.type
Proof
  simp[expr_sim_inv_mods_def, env_consistent_def, env_scopes_consistent_def,
       optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  `?vty. FLOOKUP env.var_types id = SOME vty` by
    (qpat_assum `!id entry. lookup_scopes id es.scopes = SOME entry ==> _` drule >> simp[]) >>
  `cenv.ce_var_type id = SOME vty` by simp[] >>
  `evaluate_type (get_tenv cx) vty = SOME entry.type` by
    (qpat_assum `!id ty entry. _ ==> evaluate_type _ ty = SOME entry.type`
       (qspecl_then [`id`,`vty`,`entry`] mp_tac) >> simp[]) >>
  gvs[]
QED

Theorem write_array_dynamic_local_header[local]:
  expr_sim_inv_mods mods cenv cx env mid /\
  stmt_state_rel H ctx func cenv cx mid t /\
  ghost_inv_at_mods D lo d cenv cx mid G tn t /\
  place_ptr_rel cenv cx t (PlaceR (MemoryPlace id path)) b (SOME LocMemory)
    (Type (ArrayT et (Dynamic cap))) /\
  evaluate_type (get_tenv cx) (ArrayT et (Dynamic cap)) = SOME (ArrayTV etv (Dynamic cap)) /\
  lookup_scopes id mid.scopes = SOME entry /\
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV vs)) /\
  (!p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) ==>
          op_prov G bop = FLOOKUP G p) ==>
  mload (w2n b) t = n2w (LENGTH vs) /\ mem_word_taint tn.t_mem (w2n b) = {} /\
  w2n b + 32 <= t.vs_alloca_next /\
  ?base bytes. op_prov G bop = SOME (base,bytes) /\
    base <= w2n b /\ w2n b + 32 <= base + bytes
Proof
  strip_tac >> drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  drule_then (mp_then Any assume_tac alloca_room_next_lt) stmt_state_rel_alloca_room >>
  qpat_x_assum `place_ptr_rel _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [place_ptr_rel_def]) >> gvs[] >>
  drule_all_then assume_tac write_array_local_root_type >> gvs[] >>
  qpat_x_assum `local_ptrs_rel _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
  qpat_x_assum `!name entry p sz. _ ==> ?w. _` drule_all >> strip_tac >> gvs[] >>
  qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
  qpat_x_assum `!name entry p sz. _ ==> ptr_covers _ _ _ _ _ /\ _` drule_all >>
  strip_tac >>
  drule_then strip_assume_tac mem_path_offset_sound >>
  rename1 `lookup_var p t = SOME root_addr` >>
  rename1 `mem_path_offset entry.type path = SOME (off,_)` >>
  `w2n root_addr + off + 32 <= t.vs_alloca_next /\ w2n root_addr + off < dimword (:256)` by
    (fs[type_memory_size_def] >> decide_tac) >>
  `w2n (root_addr + n2w off) = w2n root_addr + off` by
    (`off < dimword (:256)` by decide_tac >> simp[w2n_add_2, w2n_n2w, LESS_MOD]) >>
  `!m. mem_agree_outside tn.t_mem t.vs_memory m ==>
       val_in_memory (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n root_addr + off) m` by
    (rpt strip_tac >> irule mem_path_offset_current_value >>
     goal_assum (drule_at Any) >> simp[] >> qexists `entry.value` >> simp[] >>
     qpat_assum `!w m. _ ==> val_in_memory _ _ _ _` drule_all >> simp[]) >>
  `val_in_memory (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV vs))
     (w2n root_addr + off) t.vs_memory` by simp[mem_agree_outside_def] >>
  `mem_word_taint tn.t_mem (w2n root_addr + off) = {}` by
    (drule dynarray_memory_header_clean >> simp[]) >>
  simp[] >> conj_tac
  >- fs[val_in_memory_def, GSYM mem_word_at_eq_mload] >>
  gvs[ptr_covers_def, type_memory_size_def] >> decide_tac
QED

Theorem write_array_mload_packet[local]:
  compile_ptr_load ctor imm LocMemory bop sn = (len,sl) /\
  eval_operand bop t = SOME b /\ op_prov G bop = SOME (pbase,psz) /\
  pbase <= w2n b /\ w2n b + 32 <= pbase + psz /\ w2n b + 32 <= t.vs_alloca_next /\
  op_taint tn bop = {} /\ mem_word_taint tn.t_mem (w2n b) = {} /\
  allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) ==>
  ?ul Gl tl. array_length_loader_ok ctor imm LocMemory bop (mload (w2n b) t)
      sn len sl lo ctx func PG t G tn ul Gl tl /\
    op_prov Gl len = NONE /\ op_taint tl len = {}
Proof
  simp[compile_ptr_load_def] >> strip_tac >>
  drule_then strip_assume_tac emitted_insts_emit_op >>
  qpat_x_assum `len = _` SUBST_ALL_TAC >>
  qmatch_goalsub_abbrev_tac `Var out` >>
  qabbrev_tac `inst = mk_inst sn.cs_next_id MLOAD [bop] [out]` >>
  qabbrev_tac `u = update_var out (mload (w2n b) t) t` >>
  qexistsl [`u with vs_inst_idx := LENGTH sl.cs_current_insts`,
            `step_prov PG G inst u`, `step_taint inst t u tn`] >>
  rewrite_tac[array_length_loader_ok_def] >> simp[] >>
  conj_tac
  >- (qexists `MLOAD` >> simp[compile_ptr_load_def, Abbr `inst`, Abbr `u`] >>
      simp[array_length_step_ok_def, mk_inst_def, step_inst_base_def, exec_read1_def,
           access_ok_def, source_memory_read_ranges_def, source_memory_write_ranges_def,
           mem_read_ops_def, mem_write_ops_def,
           taint_ok_def, inst_mem_below_frontier_def, inst_dload_in_section_def] >>
      Cases_on `bop` >> gvs[op_prov_def, op_taint_def]) >>
  simp[Abbr `inst`, op_taint_def, op_prov_def, step_taint_def, step_prov_def,
       mk_inst_def, set_prov_def, set_var_taint_def, FLOOKUP_UPDATE, mem_taint_def,
       mem_read_ops_def, mem_write_ops_def, out_taint_def, out_prov_def, FLOOKUP_DRESTRICT]
QED

Theorem write_array_memory_load_from_current_mods:
  write_array_reached_mods
    ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
     (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
     (st0,es,sa,s0,G0,tn0),
     (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
     (base_gas,mid1,PlaceR (MemoryPlace id path),t1,G1,tn1),
     (index_gas,mid2,v,t2,G2,tn2)) /\
  valid_horizon cx st0 H mid2.storage_trace /\
  lookup_scopes id mid2.scopes = SOME entry /\
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV av) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  value_has_type (ArrayTV etv bd) (ArrayV av) /\
  place_ptr_rel cenv cx t2 (PlaceR (MemoryPlace id path)) b (SOME LocMemory)
    (Type (ArrayT et bd)) /\
  eval_operand (FST rb) t2 = SOME b /\ op_taint tn2 (FST rb) = {} /\
  (!p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) ==>
          op_prov G2 (FST rb) = FLOOKUP G2 p) ==>
  let nw = n2w (array_length (ArrayTV etv bd) av) in
    (!n. bd = Fixed n ==> nw = n2w n) /\
    (!cap len sl. bd = Dynamic cap /\
      compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory (FST rb) sn = (len,sl) ==>
      ?ul Gl tl. array_length_loader_ok cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory
          (FST rb) nw sn len sl lo ctx func PG t2 G2 tn2 ul Gl tl /\
        op_prov Gl len = NONE /\ op_taint tl len = {})
Proof
  simp[LET_THM] >> strip_tac >> Cases_on `bd` >> Cases_on `av` >>
  gvs[value_has_type_def, array_length_def] >> rpt strip_tac >>
  drule_all_then strip_assume_tac write_array_reached_posts_mods >>
  `stmt_state_rel H ctx func cenv cx mid2 t2` by fs[expr_post_mods_def, expr_post_def] >>
  `expr_sim_inv_mods mods cenv cx env mid2` by
    (qpat_assum `write_array_reached_mods _`
       (strip_assume_tac o REWRITE_RULE [write_array_reached_mods_def]) >> simp[]) >>
  drule_then assume_tac bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >>
  drule_all_then strip_assume_tac write_array_dynamic_local_header >>
  `allocas_from lo t2` by fs[ghost_inv_at_mods_def] >>
  drule_all write_array_mload_packet >> simp[]
QED
