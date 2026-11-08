(* Source-independent selector store and payload-address resources. *)
Theory reasonSelectorResourcesPtr
Ancestors
  reasonStoragePrefixPtr reasonPrefixPtr reasonPrefixResourcesPtr
  typedCopyPtr allocationPtr loweringPosts exprLoweringProps emitHelperProps
  emitHelper context compileEnv venomInst venomState venomExecSemantics
  venomInstProofs ptrDiscipline ptrSafeRun bodyPtrDefs loweringHalt
  fragExec fragExecPtr fragGasPathPtr instIdxIndep finite_map words arithmetic

Theorem reason_selector_store_resources:
  stmt_state_rel ctx func cenv cx es s /\
  lookup_var outer s = SOME (n2w b) /\ b+n < dimword(:256) /\ 32 <= n /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,n) /\
  (!name off len. local_region cenv es.scopes s name off len ==>
    regions_disjoint b n off len) ==>
  step_inst_base (mk_inst id MSTORE [Var outer; Lit 0x08c379a0w] []) s =
    OK (mstore b 0x08c379a0w s) /\
  stmt_state_rel ctx func cenv cx es (mstore b 0x08c379a0w s) /\
  (!PG G. step_prov PG G (mk_inst id MSTORE [Var outer; Lit 0x08c379a0w] [])
    (mstore b 0x08c379a0w s) = G) /\
  (!G tn old k. ptr_covers G tn old s k ==>
    ptr_covers G
      (step_taint (mk_inst id MSTORE [Var outer; Lit 0x08c379a0w] []) s
        (mstore b 0x08c379a0w s) tn) old (mstore b 0x08c379a0w s) k) /\
  (!tn old. op_taint
      (step_taint (mk_inst id MSTORE [Var outer; Lit 0x08c379a0w] []) s
        (mstore b 0x08c379a0w s) tn) (Var old) = op_taint tn (Var old)) /\
  (!ty tv a. ~cenv.ce_is_ctor /\ immutable_holds cenv cx ty tv a es s ==>
    immutable_holds cenv cx ty tv a es (mstore b 0x08c379a0w s))
Proof
  strip_tac >> `b < dimword(:256)` by decide_tac >>
  `w2n (n2w b : bytes32) = b` by simp[] >>
  conj_tac
  >- (qpat_assum `w2n (n2w b : bytes32) = b` (fn th => once_rewrite_tac[GSYM th]) >>
      irule step_MSTORE >> simp[eval_operand_def]) >>
  conj_tac
  >- (irule reason_storage_allocated_mstore_state_rel >>
      goal_assum (drule_at Any) >> qexistsl_tac [`b`, `inst`, `n`] >>
      asm_rewrite_tac[] >> decide_tac) >>
  conj_tac
  >- simp[step_prov_def, set_prov_def, out_prov_def, mk_inst_def,
          finite_mapTheory.DRESTRICT_UNIV] >>
  `eval_operand (Lit 0x08c379a0w) s = SOME 0x08c379a0w /\
   !tn. op_taint tn (Lit 0x08c379a0w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  conj_tac >- suspend "covers" >>
  conj_tac >- suspend "taint" >>
  rpt strip_tac >> gvs[immutable_holds_def, mstore_def, write_memory_with_expansion_def] >>
  metis_tac[]
QED

Resume reason_selector_store_resources[covers]:
  rpt strip_tac >>
  `op_taint tn (Lit 0x08c379a0w) = {}` by simp[op_taint_def] >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`ARB`, `G`, `id`] mp_tac) >>
  simp[] >> strip_tac >>
  gvs[ptr_covers_def, op_taint_def, lookup_var_def, mstore_def,
      write_memory_with_expansion_def]
QED
Resume reason_selector_store_resources[taint]:
  rpt gen_tac >>
  `op_taint tn (Lit 0x08c379a0w) = {}` by simp[op_taint_def] >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`ARB`, `ARB`, `id`] mp_tac) >> simp[op_taint_def]
QED
Finalise reason_selector_store_resources

Theorem reason_selector_payload_path_ptr:
  emit_void MSTORE [Var outer; Lit 0x08c379a0w] ca = ((),cb) /\
  emit_op ADD [Var outer; Lit 32w] cb = (Var payload,cd) /\
  fn_has_code ca cb func /\ fn_has_code cb cd func /\ ~ctx_has_dalloca ctx /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv ca /\
  s.vs_current_bb = ca.cs_current_bb /\
  s.vs_inst_idx = LENGTH ca.cs_current_insts /\ ~s.vs_halted /\
  lookup_var outer s = SOME (n2w b) /\ b+n < dimword(:256) /\ 32 <= n /\
  not_fresh_at ca outer /\ ptr_covers G tn outer s n /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,n) /\
  (!name off len. local_region cenv es.scopes s name off len ==>
    regions_disjoint b n off len) ==>
  ?Gf tnf t.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK t) /\
    t.vs_current_bb = cd.cs_current_bb /\
    t.vs_inst_idx = LENGTH cd.cs_current_insts /\ ~t.vs_halted /\
    stmt_state_rel ctx func cenv cx es t /\ local_ptrs_reserved cenv cd /\
    lookup_var outer t = SOME (n2w b) /\
    lookup_var payload t = SOME (n2w b+32w) /\
    ptr_covers Gf tnf outer t n /\ ptr_covers Gf tnf payload t (n-32) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_labels = s.vs_labels /\
    (!old. not_fresh_at ca old ==>
      lookup_var old t = lookup_var old s /\ FLOOKUP Gf old = FLOOKUP G old /\
      op_taint tnf (Var old) = op_taint tn (Var old)) /\
    (!old k. not_fresh_at ca old /\ ptr_covers G tn old s k ==>
      ptr_covers Gf tnf old t k) /\
    (!ty tv a. ~cenv.ce_is_ctor /\ immutable_holds cenv cx ty tv a es s ==>
      immutable_holds cenv cx ty tv a es t)
Proof
  strip_tac >> drule_all reason_selector_store_resources >>
  disch_then (qspec_then `ca.cs_next_id` strip_assume_tac) >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `emit_inst MSTORE [Var outer; Lit 0x08c379a0w] [] ca = ((),cb) /\
   emit_inst ADD [Var outer; Lit 32w] [payload]
     (cb with cs_next_var := cb.cs_next_var+1) = ((),cd)` by
    (gvs[emit_void_def, emit_op_def, comp_bind_def, fresh_var_def,
         comp_return_def, fresh_id_def, emit_inst_def, emit_def,
         comp_ignore_bind_def]) >>
  imp_res_tac emit_inst_extends >>
  `~not_fresh_at ca payload /\ payload <> outer` by
    (gvs[not_fresh_at_def] >> metis_tac[]) >>
  qabbrev_tac `u = mstore b 0x08c379a0w s` >>
  qabbrev_tac `tn1 = step_taint
    (mk_inst ca.cs_next_id MSTORE [Var outer; Lit 0x08c379a0w] []) s u tn` >>
  qabbrev_tac `v = update_var payload (n2w b+32w) u` >>
  qabbrev_tac `Gf = step_prov PG G
    (mk_inst cb.cs_next_id ADD [Var outer; Lit 32w] [payload]) v` >>
  qabbrev_tac `tnf = step_taint
    (mk_inst cb.cs_next_id ADD [Var outer; Lit 32w] [payload]) u v tn1` >>
  qexistsl_tac [`Gf`, `tnf`, `v with vs_inst_idx := LENGTH cd.cs_current_insts`] >>
  simp[lookup_var_def, stmt_state_rel_inst_idx] >> rpt conj_tac
  >- suspend "path" >- suspend "block" >- suspend "halted"
  >- suspend "state_rel" >- suspend "reserved"
  >- suspend "outer_value" >- suspend "payload_value"
  >- suspend "outer_cover" >- suspend "payload_cover"
  >- suspend "allocas" >- suspend "labels" >- suspend "metadata"
  >- suspend "old_cover" >> suspend "immutable"
QED

Resume reason_selector_payload_path_ptr[block]:
  simp[Abbr `v`, Abbr `u`, update_var_def, mstore_def]
QED
Resume reason_selector_payload_path_ptr[halted]:
  simp[Abbr `v`, Abbr `u`, update_var_def, mstore_def]
QED
Resume reason_selector_payload_path_ptr[allocas]:
  simp[Abbr `v`, Abbr `u`, update_var_def, mstore_def]
QED
Resume reason_selector_payload_path_ptr[labels]:
  simp[Abbr `v`, Abbr `u`, update_var_def, mstore_def]
QED
Resume reason_selector_payload_path_ptr[outer_value]:
  gvs[Abbr `v`, Abbr `u`, update_var_def, mstore_def, lookup_var_def,
      finite_mapTheory.FLOOKUP_UPDATE]
QED
Resume reason_selector_payload_path_ptr[payload_value]:
  simp[Abbr `v`, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED
Resume reason_selector_payload_path_ptr[reserved]:
  irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]
QED
Resume reason_selector_payload_path_ptr[state_rel]:
  simp[Abbr `v`] >> irule stmt_state_rel_update_var >>
  asm_rewrite_tac[] >>
  gvs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]
QED
Resume reason_selector_payload_path_ptr[immutable]:
  rpt strip_tac >> gvs[immutable_holds_def, Abbr `v`, update_var_def] >> metis_tac[]
QED
Resume reason_selector_payload_path_ptr[metadata]:
  rpt strip_tac >> `old <> payload` by metis_tac[] >>
  simp[Abbr `Gf`, Abbr `tnf`, Abbr `v`, Abbr `u`,
    copy_len_binop_ghost_frame, lookup_var_def, update_var_def, mstore_def,
    finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[]
QED
Resume reason_selector_payload_path_ptr[old_cover]:
  rpt strip_tac >> `old <> payload` by metis_tac[] >>
  `ptr_covers G tn1 old u k` by metis_tac[] >>
  gvs[ptr_covers_def, Abbr `Gf`, Abbr `tnf`, Abbr `v`,
      copy_len_binop_ghost_frame, lookup_var_def, update_var_def,
      finite_mapTheory.FLOOKUP_UPDATE]
QED
Resume reason_selector_payload_path_ptr[outer_cover]:
  `ptr_covers G tn1 outer u n` by metis_tac[] >>
  gvs[ptr_covers_def, Abbr `Gf`, Abbr `tnf`, Abbr `v`,
      copy_len_binop_ghost_frame, lookup_var_def, update_var_def,
      finite_mapTheory.FLOOKUP_UPDATE]
QED
Resume reason_selector_payload_path_ptr[payload_cover]:
  `ptr_covers G tn1 outer u n /\ lookup_var outer u = SOME (n2w b)` by
    (conj_tac >- metis_tac[] >>
     simp[Abbr `u`, lookup_var_def, mstore_def] >> gvs[lookup_var_def]) >>
  simp[Abbr `Gf`, Abbr `tnf`, Abbr `v`] >>
  irule reason_encoder_offset_covers >>
  goal_assum (drule_at Any) >> simp[] >> qexists_tac `n` >> asm_rewrite_tac[] >> decide_tac
QED
Resume reason_selector_payload_path_ptr[path]:
  `gas_path_ptr D 0 ctx func PG G tn s 0 G tn1
    (OK (u with vs_inst_idx := LENGTH cb.cs_current_insts))` by suspend "store_path" >>
  `gas_path_ptr D 0 ctx func PG G tn1
    (u with vs_inst_idx := LENGTH cb.cs_current_insts) 0 Gf tnf
    (OK (v with vs_inst_idx := LENGTH cd.cs_current_insts))` by suspend "add_path" >>
  drule_all gas_path_ptr_then >> simp[]
QED
Resume reason_selector_payload_path_ptr[store_path]:
  `ptr_covers G tn outer s 32` by
    (gvs[ptr_covers_def] >> goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  `ptr_inst_ok D 0 0 ctx func G tn
    (mk_inst ca.cs_next_id MSTORE [Var outer; Lit 0x08c379a0w] []) s` by
    (irule ptr_inst_ok_mstore >> simp[op_taint_def]) >>
  `MSTORE <> INVOKE /\ MSTORE <> GAS /\ ~is_terminator MSTORE` by
    simp[is_terminator_def] >>
  drule_at (Pat `ptr_inst_ok _ _ _ _ _ _ _ _ _`) reason_encoder_emit_path_ptr >>
  disch_then drule >>
  asm_rewrite_tac[] >> disch_then (qspecl_then [`u`, `PG`] mp_tac) >>
  simp[Abbr `tn1`, ADD1]
QED
Resume reason_selector_payload_path_ptr[add_path]:
  `op_taint tn1 (Var outer) = {}` by
    (gvs[Abbr `tn1`, ptr_covers_def] >> metis_tac[]) >>
  `ptr_inst_ok D 0 0 ctx func G tn1
    (mk_inst cb.cs_next_id ADD [Var outer; Lit 32w] [payload])
    (u with vs_inst_idx := LENGTH cb.cs_current_insts)` by
    (irule ptr_inst_ok_copy_len_binop >> simp[op_taint_def]) >>
  `lookup_var outer u = SOME (n2w b)` by
    gvs[Abbr `u`, lookup_var_def, mstore_def] >>
  `step_inst_base (mk_inst cb.cs_next_id ADD [Var outer; Lit 32w] [payload])
    (u with vs_inst_idx := LENGTH cb.cs_current_insts) =
    OK (v with vs_inst_idx := LENGTH cb.cs_current_insts)` by
    (`step_inst_base (mk_inst cb.cs_next_id ADD [Var outer; Lit 32w] [payload]) u = OK v` by
       (simp[Abbr `v`] >> irule step_ADD >> simp[eval_operand_def]) >>
     qpat_x_assum `step_inst_base _ u = OK v` mp_tac >>
     simp[step_inst_inst_idx_indep, exec_result_map_def, mk_inst_def, is_terminator_def]) >>
  `fn_has_code (cb with cs_next_var := cb.cs_next_var+1) cd func` by
    (qpat_x_assum `fn_has_code cb cd func` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[fn_has_code_def, emitted_blocks_def]) >>
  qpat_assum `emit_inst ADD _ _ _ = _`
    (mp_then Any mp_tac reason_encoder_emit_path_ptr) >>
  simp[NoAsms] >> disch_then (drule_at (Pat `ptr_inst_ok _ _ _ _ _ _ _ _ _`)) >>
  simp[Abbr `u`, mstore_def, is_terminator_def] >>
  disch_then (qspec_then `PG` mp_tac) >>
  simp[Abbr `Gf`, Abbr `tnf`, ADD1, mstore_def]
QED
Finalise reason_selector_payload_path_ptr
