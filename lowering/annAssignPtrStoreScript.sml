(* Declaration scope extension is independent of the operation initializing
   its buffer. Word stores and memory copies share this ghost boundary. *)
Theory annAssignPtrStore
Ancestors
  bodyPtrDefs vyperState finite_map stmtSimDeclStore typedCopyPtr
  annAssignPtrSetup fragGasSeqPtr fragGasPathPtr fragExecPtr
  venomInst venomInstProofs venomExecSemantics venomState emitHelperProps
  representationCleanPtr valueEncodingProps valueEncoding list pred_set
  venomMemProofs valueEncodingProofs ptrSafeRun ptrDiscipline
  robustCopyTransportPtr localPtrsProps exprLoweringProps exprSimProps
  loweringPosts compileEnv venomMemDefs emitHelper arithmetic

Theorem annassign_ghost_scope_update_ptr:
 !d cenv cx es G tn s sc rest id entry p sz.
 es.scopes = sc :: rest /\
 ghost_inv d cenv cx es G tn s /\
 FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
 ptr_covers G tn p s sz /\
 (!w mem. lookup_var p s = SOME w /\
           mem_agree_outside tn.t_mem s.vs_memory mem ==>
           val_in_memory entry.type entry.value (w2n w) mem) ==>
 ghost_inv d cenv cx
   (es with scopes := (sc |+ (id,entry)) :: rest) G tn s
Proof
 rpt gen_tac >> strip_tac >> fs[ghost_inv_def] >>
 rpt gen_tac >> strip_tac >> Cases_on `name = id`
 >- gvs[lookup_scopes_def, FLOOKUP_UPDATE] >>
 `lookup_scopes name es.scopes = SOME entry'` by
   gvs[lookup_scopes_def, FLOOKUP_UPDATE] >>
 first_x_assum drule_all >> simp[]
QED

Theorem annassign_mstore_path_ptr:
 !D ctx func PG G tn s bb id p value a w.
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
 get_instruction bb s.vs_inst_idx =
   SOME (mk_inst id MSTORE [Var p; value] []) /\
 ptr_covers G tn p s 32 /\ op_taint tn value = {} /\
 lookup_var p s = SOME a /\ eval_operand value s = SOME w ==>
 gas_path_ptr D 0 ctx func PG G tn s 0
   (step_prov PG G (mk_inst id MSTORE [Var p; value] []) (mstore (w2n a) w s))
   (step_taint (mk_inst id MSTORE [Var p; value] []) s (mstore (w2n a) w s) tn)
   (OK ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
 rpt gen_tac >> strip_tac >>
 `step_inst_base (mk_inst id MSTORE [Var p; value] []) s =
    OK (mstore (w2n a) w s)` by
   (irule step_MSTORE >> simp[eval_operand_def]) >>
 `gas_path_ptr_edge D 0 ctx func PG G tn s 0
   (step_prov PG G (mk_inst id MSTORE [Var p; value] []) (mstore (w2n a) w s))
   (step_taint (mk_inst id MSTORE [Var p; value] []) s (mstore (w2n a) w s) tn)
   (OK ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx))` by
   (drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
    disch_then (irule o SRULE [instruction_accessors, is_terminator_def]) >>
    simp[] >> irule ptr_inst_ok_mstore >> simp[]) >>
 drule (cj 2 gas_path_ptr_rules) >> simp[mstore_def] >>
 disch_then irule >> irule (cj 1 gas_path_ptr_rules) >> simp[mstore_def]
QED

Theorem annassign_clean_store_observation_ptr:
 !off wd s tm mem base n.
 mem_agree_outside (tm DIFF {i | off <= i /\ i < off + 32})
   (mstore off wd s).vs_memory mem ==>
 mem_bytes_at base n (mstore off wd (s with vs_memory := mem)).vs_memory =
 mem_bytes_at base n mem
Proof
 rpt gen_tac >> strip_tac >>
 `!i. mem_bytes_at i 1 (mstore off wd (s with vs_memory := mem)).vs_memory =
      mem_bytes_at i 1 mem` by
   (gen_tac >> Cases_on `off <= i /\ i < off + 32`
    >- (`mem_bytes_at i 1 (mstore off wd s).vs_memory = mem_bytes_at i 1 mem` by
          (fs[mem_agree_outside_def] >> first_x_assum irule >> simp[]) >>
        `mem_bytes_at off 32 (mstore off wd (s with vs_memory := mem)).vs_memory =
         mem_bytes_at off 32 (mstore off wd s).vs_memory` by
          simp[mem_bytes_at_mstore_same] >>
        fs[] >> drule_all mem_bytes_at_eq_byte >> simp[]) >>
    `i + 1 <= off \/ off + 32 <= i` by decide_tac >>
    simp[mstore_mem_bytes_at_disjoint]) >>
 irule LIST_EQ >> simp[] >> rpt strip_tac >>
 rename1 `EL k (mem_bytes_at addr n mem)` >>
 first_x_assum (qspec_then `addr + k` mp_tac) >> simp[LIST_EQ_REWRITE, EL_mem_bytes_at]
QED

Theorem annassign_clean_store_layout_ptr:
 !ty v off wd s tm mem.
  val_wf ty v /\
  (!u. val_in_memory ty v off (mstore off wd u).vs_memory) /\
  mem_agree_outside (tm DIFF {i | off <= i /\ i < off + 32})
    (mstore off wd s).vs_memory mem ==>
  val_in_memory ty v off mem
Proof
 rpt gen_tac >> strip_tac >>
 irule val_in_memory_mem_agree >> conj_tac >- simp[] >>
 qexistsl [`type_memory_size ty`,
   `(mstore off wd (s with vs_memory := mem)).vs_memory`] >> simp[] >>
 irule annassign_clean_store_observation_ptr >> metis_tac[]
QED

Theorem annassign_ghost_kept_mem_subset_ptr:
 !cenv es sa G0 tn0 s0 G tn tm.
 ghost_kept cenv es sa G0 tn0 s0 G tn ==>
 ghost_kept cenv es sa G0 tn0 s0 G (tn with t_mem := tn.t_mem DIFF tm)
Proof
 rw[ghost_kept_def, op_taint_def] >> metis_tac[]
QED

Theorem annassign_mstore_disjoint_robust_ptr:
 !ty v b off wd s tm.
 val_wf ty v /\
 (b + val_footprint ty v <= off \/ off + 32 <= b) /\
 (!m. mem_agree_outside tm s.vs_memory m ==> val_in_memory ty v b m) ==>
 !m. mem_agree_outside (tm DIFF {i | off <= i /\ i < off + 32})
       (mstore off wd s).vs_memory m ==> val_in_memory ty v b m
Proof
 rpt gen_tac >> strip_tac >> (rpt gen_tac >> strip_tac >>
 irule robust_val_in_memory_exterior_frame >> conj_tac >- simp[] >>
 qexistsl [`s.vs_memory`, `(mstore off wd s).vs_memory`, `tm`,
           `tm DIFF {i | off <= i /\ i < off + 32}`,
           `{i | off <= i /\ i < off + 32}`] >> simp[] >>
 rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> fs[] >> decide_tac)
QED

Theorem annassign_alloca_mstore_ghost_ptr:
 !ctx func cenv cx es d G tn s p sz a inst wd.
 stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
 ghost_inv d cenv cx es G tn s /\ not_local_ptr cenv es.scopes p /\
 lookup_var p s = SOME a /\ MEM inst (fn_insts func) /\
 inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
 FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n a,sz) /\ 32 <= sz ==>
 ghost_inv d cenv cx es G
   (tn with t_mem := tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32})
   (mstore (w2n a) wd s)
Proof
 rpt gen_tac >> strip_tac >>
 `alloca_inv s /\ local_ptrs_rel func cenv es.scopes s` by
   fs[stmt_state_rel_def, state_rel_def] >>
 fs[ghost_inv_def] >>
 conj_tac >- (
   rpt gen_tac >> strip_tac >>
   qpat_assum `local_ptrs_rel _ _ _ _`
     (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
   qpat_x_assum `!name entry p sz. _ ==> ?w. _` drule_all >> strip_tac >>
   `local_region cenv es.scopes s name (w2n w) sz'` by
     (simp[local_region_def] >> metis_tac[]) >>
   `regions_disjoint (w2n a) sz (w2n w) sz'` by
     (drule_all local_ptrs_rel_alloca_disjoint >> simp[]) >>
   qpat_x_assum `!name entry p sz. _` drule_all >> strip_tac >>
   conj_tac >- fs[ptr_covers_def, op_taint_def, mstore_def, lookup_var_def] >>
   rpt gen_tac >> strip_tac >>
   gvs[] >> irule annassign_mstore_disjoint_robust_ptr >>
   conj_tac >- simp[] >>
   qexistsl [`w2n a`, `s`, `tn.t_mem`, `wd`] >> simp[] >>
   `val_footprint entry.type entry.value <= type_memory_size entry.type` by
     simp[val_footprint_le] >>
   fs[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
 fs[return_buf_ptr_def, ptr_covers_def, stor_taint_ok_def,
    op_taint_def, mstore_def, lookup_var_def] >>
 Cases_on `d` >- simp[return_buf_ptr_def] >>
 PairCases_on `x` >> gvs[return_buf_ptr_def, ptr_covers_def, op_taint_def,
                       lookup_var_def]
QED

Theorem annassign_store_ghost_normalize_ptr[local]:
 !PG G tn id p value s a wd.
 lookup_var p s = SOME a /\ eval_operand value s = SOME wd /\
 op_taint tn value = {} ==>
 step_prov PG G (mk_inst id MSTORE [Var p; value] []) (mstore (w2n a) wd s) = G /\
 step_taint (mk_inst id MSTORE [Var p; value] []) s (mstore (w2n a) wd s) tn =
   (tn with t_mem := tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32})
Proof
 rpt gen_tac >> strip_tac >> drule_all mstore_ghost_frame >> strip_tac >>
 simp[] >> simp[taint_component_equality] >>
 simp[step_taint_def, adopt_reset_def, step_writes_def,
      set_var_taint_def, instruction_accessors, store_taint_def, imm_taint_def]
QED

Theorem annassign_declare_store_ptr:
 !ctx func cenv cx es d PG G tn s st st' id p sz a inst value wd ty v sc rest assign sa G0 tn0 s0.
 emit_void MSTORE [Var p; value] st = ((),st') /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
 s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
 stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
 ghost_kept cenv es sa G0 tn0 s0 G tn /\
 es.scopes = sc::rest /\ lookup_scopes id es.scopes = NONE /\
 FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
 not_local_ptr cenv es.scopes p /\ ptr_covers G tn p s sz /\
 lookup_var p s = SOME a /\ eval_operand value s = SOME wd /\ op_taint tn value = {} /\
 MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
 FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n a,sz) /\
 32 <= sz /\ type_memory_size ty <= sz /\ val_wf ty v /\
 (!u. val_in_memory ty v (w2n a) (mstore (w2n a) wd u).vs_memory) /\
 (!u. memory_value_rel ty v (w2n a) (mstore (w2n a) wd u).vs_memory) ==>
 ?s' tn'.
 gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 G tn' (OK s') /\
 stmt_state_rel ctx func cenv cx
   (es with scopes := (sc |+ (id,<|assignable := assign; type := ty; value := v; popped := []|>))::rest) s' /\
 ghost_inv d cenv cx
   (es with scopes := (sc |+ (id,<|assignable := assign; type := ty; value := v; popped := []|>))::rest) G tn' s' /\
 ghost_kept cenv es sa G0 tn0 s0 G tn' /\
 tn' = (tn with t_mem := tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32}) /\
 s'.vs_memory = (mstore (w2n a) wd s).vs_memory /\
 (!x. lookup_var x s' = lookup_var x s) /\
 s'.vs_allocas = s.vs_allocas /\
 ~s'.vs_halted /\ s'.vs_current_bb = st'.cs_current_bb /\
 s'.vs_inst_idx = LENGTH st'.cs_current_insts
Proof
 rpt gen_tac >> strip_tac >>
 `emit_inst MSTORE [Var p; value] [] st = ((),st')` by fs[emit_void_def, emit_inst_def] >>
 drule_all annassign_emit_instruction_ptr >> strip_tac >>
 `ptr_covers G tn p s 32` by
   (fs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS, LESS_EQ_MONO_ADD_EQ]) >>
 `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst st.cs_next_id MSTORE [Var p; value] [])` by simp[] >>
 drule_all annassign_mstore_path_ptr >>
 disch_then (qspecl_then [`cx_dead cx`, `PG`] assume_tac) >>
 drule_all annassign_store_ghost_normalize_ptr >> strip_tac >>
 `st'.cs_current_bb = st.cs_current_bb /\
  LENGTH st'.cs_current_insts = SUC (LENGTH st.cs_current_insts)` by
   gvs[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
 qexistsl [`(mstore (w2n a) wd s) with vs_inst_idx := SUC s.vs_inst_idx`,
   `tn with t_mem := tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32}`] >>
 simp[stmt_state_rel_inst_idx, annassign_ghost_inst_idx_ptr] >>
 conj_tac >- metis_tac[] >>
 conj_tac >- (irule stmt_state_rel_declare_store >> simp[] >>
   conj_tac >- (qexists `inst` >> gvs[]) >>
   qpat_x_assum `!u. memory_value_rel _ _ _ _` (qspec_then `s` ACCEPT_TAC)) >>
 conj_tac >- (
   irule annassign_ghost_scope_update_ptr >> simp[] >>
   reverse conj_tac
   >- (irule annassign_alloca_mstore_ghost_ptr >> metis_tac[]) >>
   conj_tac >- (rpt strip_tac >> irule annassign_clean_store_layout_ptr >> metis_tac[]) >>
   gvs[ptr_covers_def, op_taint_def, mstore_def, lookup_var_def]) >>
 simp[annassign_ghost_kept_mem_subset_ptr, mstore_def, lookup_var_def]
QED
