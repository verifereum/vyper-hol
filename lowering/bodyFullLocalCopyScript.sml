(* Land a joint typed store in the source scope and its pointer ghost. *)
Theory bodyFullLocalCopy
Ancestors
  bodyFullMemoryFrames assignRelayoutFrame placeMemoryCopyEffect typedMemoryCopy
  fragGasOriginPtr fragGasOrigin fragGasMode bodyPtrDefs loweringStateRelDefs
  localPtrsProps compileEnv venomState venomMemDefs vyperLookup
  exprLoweringProps memSafeRun arithmetic
  codegenRel ptrDiscipline

Theorem body_full_local_copy_post:
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK t,Gf,tf) /\
  typed_copy_state_frame sa (w2n dst) (type_memory_size entry.type) s t /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  stmt_state_rel H ctx func cenv cx es s /\
  ghost_inv_at D lo d cenv cx es G tn s /\
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\
  lookup_var p s = SOME dst /\ local_ptrs_reserved cenv sa /\
  type_memory_size entry.type <= cap /\ lo <= w2n dst /\
  val_wf entry.type v /\ value_has_type entry.type v /\
  val_in_memory entry.type v (w2n dst) t.vs_memory /\
  (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
    val_in_memory entry.type v (w2n dst) mem) /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==>
    not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==>
    not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  (!i. ~(w2n dst <= i /\ i < w2n dst + type_memory_size entry.type) ==>
    (i IN tf.t_mem <=> i IN tn.t_mem)) ==>
  stmt_state_rel H ctx func cenv cx
    (es with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) t /\
  ghost_inv_at D lo d cenv cx
    (es with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest)
    Gf tf t
Proof
  strip_tac >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    (irule gas_marked_path_from_mem >>
     drule gas_origin_ptr_path_projections >> strip_tac >>
     drule gas_origin_path_erase >> simp[gas_marked_path_def]) >>
  `typed_copy_effect ctx func sa sb s t (w2n dst) (type_memory_size entry.type)` by
    (fs[typed_copy_effect_def,typed_copy_state_frame_def,typed_copy_frame_def,
        venom_state_component_equality] >> metis_tac[]) >>
  conj_tac
  >- (irule stmt_state_rel_write_local_copy_effect >>
      simp[] >> qexistsl_tac [`dst`,`s`,`sa`,`sb`] >> simp[]) >>
  `local_region cenv es.scopes s id (w2n dst) cap` by
    (simp[local_region_def] >> metis_tac[find_containing_scope_lookup]) >>
  `local_ptrs_rel func cenv es.scopes s` by fs[stmt_state_rel_def,state_rel_def] >>
  `stor_taint_ok_at D tf t /\ allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (fs[typed_copy_state_frame_def,venom_state_component_equality,
       ghost_inv_at_def,stor_taint_ok_at_def,allocas_from_def] >> metis_tac[]) >>
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (fs[typed_copy_state_frame_def,typed_copy_frame_def] >> metis_tac[ADD_CLAUSES]) >>
  `!i. i < lo /\ i IN tf.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >>
     `~(w2n dst <= i /\ i < w2n dst + type_memory_size entry.type)` by decide_tac >>
     metis_tac[]) >>
  `!i. ~(w2n dst <= i /\ i < w2n dst + type_memory_size entry.type) ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tf.t_mem <=> i IN tn.t_mem)` by
    (rpt strip_tac >>
     `i + 1 <= w2n dst \/ w2n dst + type_memory_size entry.type <= i` by decide_tac >>
     fs[typed_copy_state_frame_def,typed_copy_frame_def] >> metis_tac[]) >>
  irule (Q.INST [`sz` |-> `cap`,`dst` |-> `dst`,`G` |-> `G`,
    `p` |-> `p`,`s` |-> `s`,`sa` |-> `sa`,`tn` |-> `tn`,
    `n` |-> `type_memory_size entry.type`]
      (SPEC_ALL body_full_local_scope_ghost_post)) >>
  simp[] >> qexistsl_tac [`G`,`dst`,`func`,`s`,`sa`,`tn`] >>
  simp[] >> metis_tac[]
QED
