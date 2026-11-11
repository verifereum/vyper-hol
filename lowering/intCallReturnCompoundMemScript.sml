(* Widened compound return through the typed-store memory continuation. *)
Theory intCallReturnCompoundMem
Ancestors
  intCallReturnDirectBranchesMem stmtSimReturnWiden stmtSimReturn emptyScopeMemoryFrame
  typedStoreEndpoint typedNormalizeEntryBoundary externalNormalizePremises
  typedMemoryCopy memContinuation exprSimTypedAlloc exprSimStorageCopy
  fragExec fragExecMem abiEncoderExitPhi loweringPosts intCallReturnMem intCallReturn
  exprSimDefs exprSimProps exprLoweringProps stmtLowering emitHelper
  compileEnv context venomState venomExecSemantics venomInst
  list rich_list finite_map valueEncoding vyperState loweringStateRelDefs

Theorem typed_return_ret_entry[local]:
  compile_store_memory_typed ce dst dt src st sa = ((),sm) /\
  emit_inst RET [rpc] [] sm = ((),sb) /\ fn_has_code sm sb fn ==>
  (emitted_blocks sa sm <> [] ==>
    ?bb. lookup_block sm.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0)
Proof
  rpt strip_tac >>
  `phi_prefix_length sm.cs_current_insts = 0` by
    metis_tac[normalize_typed_changed_prefix_zero] >>
  qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
  simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
  Cases_on `sm.cs_current_insts` >>
  gvs[phi_prefix_length_def, mk_inst_def] >>
  Cases_on `h.inst_opcode = PHI` >> gvs[phi_prefix_length_def]
QED

Theorem compile_internal_return_compound_mem:
  !ctx func cenv cx es ty sty dtv stv v val_op rpc elem_types buf_op sa sb bw.
    sty <> ty /\ ~is_word_type ty /\ ~is_bytestring_type ty /\
    compile_internal_return cenv (SOME val_op) rpc 0 ty sty elem_types
      (SOME buf_op) sa = ((),sb) /\
    (!x. val_op = Var x ==> not_fresh_at sa x) /\
    (!x. buf_op = Var x ==> not_fresh_at sa x) /\
    (!x. rpc = Var x ==> not_fresh_at sa x) /\
    (!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
    type_widens_to (get_tenv cx) sty ty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\
    evaluate_type (get_tenv cx) ty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    (!name fields.
       FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname, fty, sz). !tv.
         evaluate_type (get_tenv cx) fty = SOME tv ==>
         sz = type_memory_size tv) fields) /\
    type_memory_bytes cenv ty = type_memory_size dtv /\
    w2n bw + type_memory_size dtv + 64 < dimword (:256) /\
    (cenv.ce_is_ctor ==> !name itv iv off.
       FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
         SOME (ImmutableLoc off) /\
       FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
         | SOME imms => get_source_immutables cenv.ce_module imms) name =
         SOME (itv,iv) ==>
       regions_disjoint off (type_memory_size itv) (w2n bw)
         (type_memory_size dtv)) ==>
    frag_exec_mem ctx sa sb
      (\s. stmt_state_rel ctx func cenv cx (es with scopes := []) s /\
           expr_val_rel cx sty v val_op s /\
           eval_operand buf_op s = SOME bw /\
           w2n bw + type_memory_size dtv <= s.vs_alloca_next /\
           expr_store_bound cx sty v val_op s /\
           (~is_word_type sty ==> !sw. eval_operand val_op s = SOME sw ==>
              type_memory_size stv = 0 \/
              w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
           (sty <> ty /\ ~is_word_type ty /\ ~is_bytestring_type ty ==>
            ?sw. eval_operand val_op s = SOME sw /\
                 w2n sw + type_memory_size stv < dimword (:256) /\
                 (w2n sw + type_memory_size stv <= w2n bw \/
                  w2n bw + type_memory_size dtv <= w2n sw)) /\
           ?pc. eval_operand rpc s = SOME pc)
      (\s. F)
      (intret_mem_q func cenv cx dtv bw v (es with scopes := []))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_internal_return _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_internal_return_def, comp_ignore_bind_def, comp_bind_def,
       compile_store_memory_def] >>
  Cases_on `compile_store_memory_typed cenv buf_op ty val_op sty sa` >>
  rename1 `compile_store_memory_typed _ _ _ _ _ _ = (u,sm)` >>
  Cases_on `u` >> simp[] >> strip_tac >>
  `cs_extends sa sm` by
    (drule typed_return_store_mono >> simp[ci_mono_def]) >>
  `cs_extends sm sb` by (irule cs_extends_emit_inst >> metis_tac[]) >>
  (* Use the whole suffix's code certificate, since the typed store may branch. *)
  rewrite_tac[frag_exec_mem_def] >> rpt strip_tac >>
  `fn_has_code sa sm fn /\ fn_has_code sm sb fn` by
    metis_tac[fn_has_code_split] >>
  `~is_word_type sty` by metis_tac[return_source_word_widens_eq] >>
  `0 < type_memory_size stv` by metis_tac[normalize_return_source_positive] >>
  gvs[] >>
  `val_in_memory stv v (w2n sw) s.vs_memory` by gvs[expr_val_rel_def] >>
  `w2n sw + type_memory_size stv <= s.vs_alloca_next` by decide_tac >>
  `w2n bw + type_memory_size dtv < dimword (:256)` by decide_tac >>
  `!x. buf_op = Var x \/ val_op = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  `emitted_blocks sa sm <> [] ==>
    ?bb. lookup_block sm.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[typed_return_ret_entry] >>
  `w2n sw + type_memory_size stv < dimword (:256) /\
   w2n bw + type_memory_size dtv <= s.vs_alloca_next` by decide_tac >>
  Q.SUBGOAL_THEN
    `w2n sw + type_memory_size stv <= w2n bw \/
     w2n bw + type_memory_size dtv <= w2n sw` assume_tac >- decide_tac >>
  drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`) typed_store_mem_cont >>
  disch_then (drule_at (Pat `sfields_tenv_consistent _ _`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  simp[] >>
  disch_then (qspec_then `ctx` mp_tac) >>
  (impl_tac >- metis_tac[]) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  suspend "frame_and_ret"
QED

Resume compile_internal_return_compound_mem[frame_and_ret]:
  markerLib.RESUME_TAC >>
  `copy_static t = copy_static s` by
    (qpat_x_assum `_ = s` mp_tac >>
     simp[copy_static_def, venom_state_component_equality] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx (es with scopes := []) t` by
    (irule empty_scope_memory_frame >>
     qexistsl_tac [`w2n bw`, `s`, `type_memory_size dtv`] >>
     simp[] >> metis_tac[]) >>
  `t.vs_labels = s.vs_labels` by
    (qpat_x_assum `_ = s` (mp_tac o AP_TERM ``\u:venom_state. u.vs_labels``) >> simp[]) >>
  `eval_operand rpc t = SOME pc` by
    (Cases_on `rpc` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `frag_exec_mem ctx sm sb (\u. u = t) (\u. F)
     (intret_mem_q func cenv cx dtv bw v (es with scopes := []))` by
    (irule emit_ret_pc_frag_mem >> qexists_tac `rpc` >> simp[] >>
     gvs[intret_mem_q_def, intret_q_def, result_rel_def,
         intret_vals_match_def, stmt_state_rel_def]) >>
  qpat_x_assum `frag_exec_mem _ _ _ _ _ _` mp_tac >>
  simp[frag_exec_mem_def] >>
  disch_then (qspec_then `fn` mp_tac) >> simp[] >>
  strip_tac >>
  qpat_x_assum `mem_cont_sim _ _ _ _` mp_tac >>
  simp[mem_cont_sim_def] >>
  disch_then (qspec_then `fuel` mp_tac) >>
  (impl_tac >- metis_tac[exit_result_def]) >>
  strip_tac >> qexists_tac `fuel'` >> gvs[]
QED

Finalise compile_internal_return_compound_mem
