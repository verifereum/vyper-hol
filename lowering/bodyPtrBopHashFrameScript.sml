Theory bodyPtrBopHashFrame
Ancestors
  bodyPtrBopHashCompile bodyPtrBopHashSequence bodyPtrDefs
  loweringPosts compileEnv venomState venomExecSemantics
  finite_map exprLoweringProps ptrDiscipline

Theorem bop_hash_compile_run_frame:
  compile_bytestring_hash (Var p) sc = (op,sd) /\ not_fresh_at sc p /\
  lookup_var p s = SOME w /\
  run_inst_seq (emitted_insts sc sd) s = OK t ==>
  t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
  t.vs_fmp = s.vs_fmp /\
  (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule_all bop_hash_compile_emission >> strip_tac >>
  qpat_x_assum `emitted_insts _ _ = _` (fn th =>
    rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[run_inst_seq_def, AllCaseEqs()] >> strip_tac >>
  drule_all bop_hash_add_state >> strip_tac >> gvs[] >>
  `p <> q` by metis_tac[] >>
  `lookup_var p (update_var q (w + 32w) s) = SOME w` by
    fs[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  drule_all bop_hash_mload_state >> strip_tac >> gvs[] >>
  drule bop_hash_sha3_state_frame >> strip_tac >>
  gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem bop_ptr_val_readonly_frame:
  ptr_val_ok cx ty v (Var r) G tn s /\
  t.vs_memory = s.vs_memory /\ lookup_var r t = lookup_var r s /\
  tn'.t_mem = tn.t_mem /\ FLOOKUP G' r = FLOOKUP G r /\
  FLOOKUP tn'.t_var r = FLOOKUP tn.t_var r ==>
  ptr_val_ok cx ty v (Var r) G' tn' t
Proof
  simp[ptr_val_ok_def, ptr_mem_ok_def, op_taint_def, op_prov_def,
       eval_operand_def] >>
  metis_tac[]
QED

Theorem bop_ptr_val_readonly_frame_cursor:
  ptr_val_ok cx ty v (Var r) G tn s /\
  t.vs_memory = s.vs_memory /\ lookup_var r t = lookup_var r s /\
  tn'.t_mem = tn.t_mem /\ FLOOKUP G' r = FLOOKUP G r /\
  FLOOKUP tn'.t_var r = FLOOKUP tn.t_var r ==>
  ptr_val_ok cx ty v (Var r) G' tn' (t with vs_inst_idx := idx)
Proof
  strip_tac >> irule bop_ptr_val_readonly_frame >>
  qexistsl_tac [`G`, `s`, `tn`] >> fs[lookup_var_def]
QED

Theorem bop_local_region_readonly_frame:
  local_ptrs_reserved cenv sc /\
  (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x s) ==>
  (local_region cenv scopes t n b sz <=> local_region cenv scopes s n b sz)
Proof
  simp[local_region_def, local_ptrs_reserved_def] >>
  rpt strip_tac >> eq_tac >> strip_tac >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem bop_expr_val_readonly_frame:
  expr_val_at cenv cx ty sa sb es v (Var r) s /\
  local_ptrs_reserved cenv sc /\ not_fresh_at sc r /\
  t.vs_allocas = s.vs_allocas /\
  (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x s) ==>
  expr_val_at cenv cx ty sa sb es v (Var r) t
Proof
  strip_tac >>
  `!n b sz. local_region cenv es.scopes t n b sz <=>
             local_region cenv es.scopes s n b sz` by
    (rpt gen_tac >> irule bop_local_region_readonly_frame >>
     qexists_tac `sc` >> simp[]) >>
  fs[expr_val_at_def, eval_operand_def] >> metis_tac[]
QED

Theorem bop_expr_val_readonly_frame_cursor:
  expr_val_at cenv cx ty sa sb es v (Var r) s /\
  local_ptrs_reserved cenv sc /\ not_fresh_at sc r /\
  t.vs_allocas = s.vs_allocas /\
  (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x s) ==>
  expr_val_at cenv cx ty sa sb es v (Var r) (t with vs_inst_idx := idx)
Proof
  strip_tac >> irule bop_expr_val_readonly_frame >>
  qexistsl_tac [`s`, `sc`] >> fs[lookup_var_def]
QED
