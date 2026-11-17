(* Install a reserved new source binding after the joint Store endpoint. *)
Theory bodyFullAnnAssignMemoryPost
Ancestors
  bodyFullLocalCopy annassignRelayoutFrame bodyFullMemoryFrames
  nameLoweringProps robustCopyTransportPtr vyperLookup
  fragGasOriginPtr fragGasOrigin fragGasMode bodyPtrDefs
  placeMemoryCopyEffect typedMemoryCopy venomState memSafeRun
  loweringStateRelDefs localPtrsProps compileEnv exprLoweringProps
  codegenRel ptrDiscipline vyperState finite_map assignTuplePtrCopyLen arithmetic

Theorem body_full_annassign_memory_post:
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK t,Gf,tf) /\
  typed_copy_state_frame sa (w2n dst) (type_memory_size tyv) s t /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  stmt_state_rel H ctx func cenv cx es s /\
  ghost_inv_at D lo d cenv cx es G tn s /\
  fn_inst_ids_distinct func /\ es.scopes = sc :: rest /\
  lookup_scopes id es.scopes = NONE /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\
  not_local_ptr cenv es.scopes p /\ lookup_var p s = SOME dst /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [p] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dst,cap) /\
  (!q. q = p \/ ~not_local_ptr cenv es.scopes q ==> not_fresh_at sa q) /\
  local_ptrs_reserved cenv sa /\ ptr_covers G tn p s cap /\
  type_memory_size tyv <= cap /\ lo <= w2n dst /\
  val_wf tyv v /\ value_has_type tyv v /\
  val_in_memory tyv v (w2n dst) t.vs_memory /\
  (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
    val_in_memory tyv v (w2n dst) mem) /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==>
    not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==>
    not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  (!i. ~(w2n dst <= i /\ i < w2n dst + type_memory_size tyv) ==>
    (i IN tf.t_mem <=> i IN tn.t_mem)) ==>
  stmt_state_rel H ctx func cenv cx
    (es with scopes :=
      (sc |+ (id,<|assignable := a; type := tyv; value := v; popped := []|>)) :: rest) t /\
  ghost_inv_at D lo d cenv cx
    (es with scopes :=
      (sc |+ (id,<|assignable := a; type := tyv; value := v; popped := []|>)) :: rest)
    Gf tf t
Proof
  strip_tac >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    (irule gas_marked_path_from_mem >>
     drule gas_origin_ptr_path_projections >> strip_tac >>
     drule gas_origin_path_erase >> simp[gas_marked_path_def]) >>
  `typed_copy_effect ctx func sa sb s t (w2n dst) (type_memory_size tyv)` by
    (fs[typed_copy_effect_def,typed_copy_state_frame_def,typed_copy_frame_def,
        venom_state_component_equality] >> metis_tac[]) >>
  conj_tac >- suspend "source" >>
  `ghost_inv_at D lo d cenv cx es Gf tf t` by suspend "frame" >>
  rewrite_tac[ghost_inv_at_def] >> conj_tac >- suspend "install" >>
  fs[ghost_inv_at_def]
QED

Resume body_full_annassign_memory_post[source]:
  `typed_copy_effect ctx func sa sb s t (w2n dst) cap` by
    (irule typed_copy_effect_enlarge >> goal_assum (drule_at Any) >> simp[]) >>
  irule stmt_state_rel_declare_copy_effect >>
  simp[] >> goal_assum (drule_at Any) >>
  qexists_tac `inst` >> fs[] >> metis_tac[]
QED

Resume body_full_annassign_memory_post[frame]:
  `local_ptrs_rel func cenv es.scopes s /\ alloca_inv s` by
    fs[stmt_state_rel_def,state_rel_def] >>
  `!name b n. local_region cenv es.scopes s name b n ==>
    regions_disjoint (w2n dst) cap b n` by
    (rpt strip_tac >> irule local_ptrs_rel_alloca_disjoint >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `!i. ~(w2n dst <= i /\ i < w2n dst + type_memory_size tyv) ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tf.t_mem <=> i IN tn.t_mem)` by
    (rpt strip_tac >>
     `i + 1 <= w2n dst \/ w2n dst + type_memory_size tyv <= i` by decide_tac >>
     fs[typed_copy_state_frame_def,typed_copy_frame_def] >> metis_tac[]) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (fs[typed_copy_state_frame_def,venom_state_component_equality,
        ghost_inv_at_def,allocas_from_def] >> metis_tac[]) >>
  irule body_full_memory_ghost_frame >> simp[] >>
  qexistsl_tac [`G`,`s`,`sa`,`tn`,
    `{i | w2n dst <= i /\ i < w2n dst + type_memory_size tyv}`] >>
  simp[] >> conj_tac >- suspend "footprint" >>
  `!i. i < lo /\ i IN tf.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >>
     `~(w2n dst <= i /\ i < w2n dst + type_memory_size tyv)` by decide_tac >>
     metis_tac[]) >>
  fs[typed_copy_state_frame_def,typed_copy_frame_def,
     venom_state_component_equality] >> metis_tac[ADD_CLAUSES]
QED

Resume body_full_annassign_memory_post[footprint]:
  rpt gen_tac >> strip_tac >>
  `lookup_scopes name es.scopes = SOME entry` by metis_tac[] >>
  drule_all local_ptrs_rel_value >> strip_tac >>
  gvs[eval_operand_def] >>
  `local_region cenv es.scopes s name (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `regions_disjoint (w2n dst) cap (w2n w) sz` by metis_tac[] >>
  `val_footprint entry.type entry.value <= type_memory_size entry.type` by
    metis_tac[exprSimPropsTheory.val_footprint_le] >>
  simp[] >> fs[regions_disjoint_def] >> rpt strip_tac >> decide_tac
QED

Resume body_full_annassign_memory_post[install]:
  rpt gen_tac >> strip_tac >> Cases_on `name = id`
  >- (gvs[lookup_scopes_def,FLOOKUP_UPDATE] >>
      irule ptr_covers_lookup_frame >> goal_assum (drule_at Any) >>
      metis_tac[]) >>
  `lookup_scopes name es.scopes = SOME entry` by
    (fs[lookup_scopes_def,FLOOKUP_UPDATE]) >>
  fs[ghost_inv_at_def] >> metis_tac[]
QED

Finalise body_full_annassign_memory_post
