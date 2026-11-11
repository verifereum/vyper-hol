(* Conditional constructor immutable replacement frame. *)
Theory immutableWordStoreFrame
Ancestors
  exprSimPopNestedImmutableDeploy localPtrsProps bodyDeclMemoryCore
  bodyDeclMemoryCounted allocaFootprint emitHelperProps emitHelper
  venomInst fragExec fragExecMem venomExecSemantics compileEnv
  fragGasMode venomState valueEncodingDefs loweringStateRelDefs exprLoweringProps
  finite_map alist

Theorem immutable_word_store_stmt_frame:
  cenv.ce_is_ctor /\ expr_sim_inv cenv cx env es /\
  stmt_state_rel ctx func cenv cx es s /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
  FLOOKUP (get_source_immutables cenv.ce_module imms) id = SOME (tv,a) /\
  k + 32 <= type_memory_size tv /\
  es' = es with immutables :=
    (cx.txn.target,set_source_immutables cenv.ce_module
      (get_source_immutables cenv.ce_module imms |+ (id,(tv,updated))) imms) ::
    ADELKEY cx.txn.target es.immutables /\
  immutable_value_admissible tv updated /\
  val_in_memory tv updated off (mstore (off+k) word s).vs_memory /\
  immutable_value_bytes_rel tv updated
    (mem_bytes_at off (type_memory_size tv) (mstore (off+k) word s).vs_memory) ==>
  stmt_state_rel ctx func cenv cx es' (mstore (off+k) word s)
Proof
  strip_tac >>
  `immutables_rel cenv cx.txn.target cenv.ce_module T es s` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  `immutables_rel cenv cx.txn.target cenv.ce_module T es'
     (mstore (off+k) word s)` by
    (irule immutables_rel_ctor_update >>
     qexistsl [`es`, `id`, `imms`, `off`, `s`, `tv`, `updated`] >>
     simp[] >> rpt strip_tac >>
     pure_once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
     irule immutable_store_other_bytes >> metis_tac[]) >>
  `local_ptrs_rel func cenv es.scopes s` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  `!name b sz. local_region cenv es.scopes s name b sz ==>
     mem_bytes_at b sz (mstore (off+k) word s).vs_memory =
     mem_bytes_at b sz s.vs_memory` by
    (rpt strip_tac >> irule immutable_store_frame_bytes >> metis_tac[]) >>
  `(mstore (off+k) word s).vs_vars = s.vs_vars /\
   (mstore (off+k) word s).vs_allocas = s.vs_allocas /\
   (mstore (off+k) word s).vs_alloca_next = s.vs_alloca_next` by
    simp[mstore_def, write_memory_with_expansion_def] >>
  `local_ptrs_rel func cenv es.scopes (mstore (off+k) word s)` by
    (irule local_ptrs_rel_mem_agree >> qexists `s` >>
     simp[lookup_var_def] >> conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
     rpt strip_tac >> gvs[]) >>
  irule immutable_replace_mstore_stmt_frame >>
  conj_tac >- gvs[] >> metis_tac[]
QED

(* Unlike a local binding store, an immutable destination may be literal. *)
Theorem immutable_word_store_path_mem:
  emit_void MSTORE [dst;op] sa = ((),sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand dst s = SOME w /\ eval_operand op s = SOME word /\
  w2n w + 32 <= s.vs_alloca_next /\ alloca_history func s /\ alloca_inv s ==>
  gas_marked_path T ctx func s 0
    (OK (mstore (w2n w) word s with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  alloca_history func
    (mstore (w2n w) word s with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  `run_inst_seq (emitted_insts sa sb) s = OK (mstore (w2n w) word s)` by
    (`step_inst_base (mk_inst sa.cs_next_id MSTORE [dst;op] []) s =
        OK (mstore (w2n w) word s)` by
       (irule step_MSTORE >> simp[]) >>
     simp[run_inst_seq_def]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    simp[mk_inst_def, is_terminator_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule emit_mstore_mem_ok >> metis_tac[]) >>
  conj_tac
  >- (simp[gas_marked_path_def] >>
      drule_at (Pat `run_inst_seq _ _ = _`) body_decl_zero_gas_path >> simp[]) >>
  irule body_store_memory_history >> simp[] >>
  qexistsl [`s`, `sa`] >> fs[listTheory.EVERY_MEM]
QED
