(* Ordinary and ghost postconditions of the checked storage append suffix. *)
Theory appendStorageSuccessPostPtr
Ancestors
  appendStorageGhostPtr stmtAppendStoragePathPtr stmtSimAppendStorageCompose
  appendStorageRel stmtSimDefs stmtSimProps freshWrites stateFrame
  venomState venomExecSemantics vyperStorage vyperValue vyperState
  vyperInterpreter compileEnv bodyPtrDefs ptrDiscipline words arithmetic
  finite_map pred_set vyperScopePreservation

Theorem append_storage_word_success_post:
  !ctx func cenv cx es s u sb tr slot len w mid n tv cap v res es'.
  state_frame u = state_frame
    (if tr then tstore slot (n2w len+1w) (tstore (slot+1w+n2w len) w s)
     else sstore slot (n2w len+1w) (sstore (slot+1w+n2w len) w s)) /\
  (!x a. not_fresh_at sb x /\ lookup_var x s = SOME a ==>
         lookup_var x u = SOME a) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sb /\
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  type_slot_size tv = 1 /\
  len = w2n (lookup_storage slot (get_storage cx es tr)) /\ len < cap /\
  encode_value tv v = SOME [(0,w)] /\
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es =
    (res,es') ==>
  res = INL () /\ stmt_state_rel ctx func cenv cx es' u /\
  u.vs_current_bb = s.vs_current_bb /\ u.vs_halted = s.vs_halted /\
  u.vs_allocas = s.vs_allocas
Proof
  rpt gen_tac >> strip_tac >>
  `u.vs_current_bb = s.vs_current_bb /\ u.vs_halted = s.vs_halted /\
   u.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `state_frame u = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `tr` >> simp[state_frame_def, sstore_def, tstore_def,
       LET_THM, venom_state_component_equality]) >>
  qmatch_asmsub_abbrev_tac `state_frame u = state_frame su` >>
  drule_all stmt_state_rel_append_storage_word >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es' su` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ es' _` mp_tac >>
     simp_tac bool_ss [Abbr `su`, GSYM wordsTheory.word_add_n2w,
                      wordsTheory.WORD_ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
  simp[] >>
  irule stmt_state_rel_reserved_frame >> qexistsl_tac [`su`, `sb`] >>
  asm_simp_tac bool_ss [] >> rpt strip_tac >>
  qpat_x_assum `lookup_var _ su = SOME _` mp_tac >>
  Cases_on `tr` >>
  simp_tac (srw_ss()) [Abbr `su`, sstore_def, tstore_def, LET_THM,
                       lookup_var_def] >>
  strip_tac >>
  qpat_x_assum `!x a. _ ==> lookup_var x u = SOME a`
    (qspec_then `x` mp_tac) >> simp[lookup_var_def]
QED

Theorem append_storage_word_taint_post:
  stor_taint_ok cx tn s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  type_slot_size tv = 1 /\
  len = w2n (lookup_storage slot
    (if tr then contract_transient s else contract_storage s)) /\ len < cap /\
  state_frame u = state_frame
    (if tr then tstore slot (n2w len+1w) (tstore (slot+1w+n2w len) w s)
     else sstore slot (n2w len+1w) (sstore (slot+1w+n2w len) w s)) /\
  tn'.t_imm = tn.t_imm /\
  (if tr then
     tn'.t_trans = key_update (key_update tn.t_trans (slot+1w+n2w len) {}) slot {} /\
     tn'.t_stor = tn.t_stor
   else
     tn'.t_stor = key_update (key_update tn.t_stor (slot+1w+n2w len) {}) slot {} /\
     tn'.t_trans = tn.t_trans) ==>
  stor_taint_ok cx tn' u
Proof
  strip_tac >> drule_all append_clean_stores_taint_ok >>
  disch_then (qspec_then `w` mp_tac) >>
  qpat_x_assum `state_frame u = _` mp_tac >>
  Cases_on `tr` >>
  simp[stor_taint_ok_def, state_frame_def, venom_state_component_equality,
       GSYM word_add_n2w, WORD_ADD_ASSOC, ADD_COMM] >>
  rpt strip_tac >> gvs[]
QED

Theorem append_storage_word_ghost_post:
  ghost_inv d cenv cx es G tn s /\
  local_ptrs_reserved cenv sb /\ ret_pc_ok cenv sb s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sb x) /\
  s.vs_call_ctx.cc_address = cx.txn.target /\
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  type_slot_size tv = 1 /\
  len = w2n (lookup_storage slot
    (if tr then contract_transient s else contract_storage s)) /\ len < cap /\
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es =
    (res,es') /\
  state_frame u = state_frame
    (if tr then tstore slot (n2w len+1w) (tstore (slot+1w+n2w len) w s)
     else sstore slot (n2w len+1w) (sstore (slot+1w+n2w len) w s)) /\
  (!x. not_fresh_at sb x ==>
     FLOOKUP G' x = FLOOKUP G x /\
     op_taint tn' (Var x) = op_taint tn (Var x) /\
     lookup_var x u = lookup_var x s) /\
  tn'.t_mem = tn.t_mem /\ tn'.t_imm = tn.t_imm /\
  (if tr then
     tn'.t_trans = key_update (key_update tn.t_trans (slot+1w+n2w len) {}) slot {} /\
     tn'.t_stor = tn.t_stor
   else
     tn'.t_stor = key_update (key_update tn.t_stor (slot+1w+n2w len) {}) slot {} /\
     tn'.t_trans = tn.t_trans) ==>
  ghost_inv d cenv cx es' G' tn' u /\
  ghost_kept cenv es sb G tn s G' tn' /\
  (!es0 sa G0 tn0 s0.
     ghost_kept cenv es0 sa G0 tn0 s0 G tn /\
     sa.cs_next_var <= sb.cs_next_var ==>
     ghost_kept cenv es0 sa G0 tn0 s0 G' tn')
Proof
  strip_tac >>
  `stor_taint_ok cx tn s` by metis_tac[ghost_inv_def] >>
  drule_all append_storage_word_taint_post >> strip_tac >>
  `es'.scopes = es.scopes` by
    metis_tac[append_storage_place_scopes_immutables] >>
  `u.vs_memory = s.vs_memory` by
    (qpat_x_assum `state_frame u = _` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `tr` >>
     simp[state_frame_def, venom_state_component_equality,
          sstore_def, tstore_def, LET_THM]) >>
  conj_tac
  >- (drule_all ghost_inv_old_transport >> simp[]) >>
  conj_tac
  >- (irule ghost_kept_old_transport >> simp[] >> metis_tac[]) >>
  rpt strip_tac >> irule ghost_kept_suffix_compose >>
  goal_assum (drule_at Any) >> qexistsl_tac [`G`, `tn`] >> simp[] >> metis_tac[]
QED
