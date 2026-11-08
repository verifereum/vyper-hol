(* Metadata transport across memory-changing argument reads.
   Semantic value preservation is supplied separately at the same endpoint. *)
Theory bodyIntCallHeldCopyFrame
Ancestors
  bodyIntCallHeldArgs bodyIntCallHeldFrame exprSimSubscriptArrayFrame
  loweringPosts compileEnv venomState context freshWrites list pair

Theorem intcall_held_args_holds_frame:
  intcall_held_args ce cx a sm es s H /\
  wb_frame ce es sm s t /\ local_ptrs_reserved ce sm /\
  local_ptrs_rel func ce es.scopes s /\ t.vs_labels = s.vs_labels /\
  contract_storage t = contract_storage s /\
  contract_transient t = contract_transient s /\
  sm.cs_next_id <= sn.cs_next_id /\ sm.cs_next_var <= sn.cs_next_var /\
  (!ty raw vv. MEM (ty,raw,vv) H ==> vv_holds ce cx ty raw vv es t) ==>
  intcall_held_args ce cx a sn es t H
Proof
  strip_tac >>
  `!n b sz. local_region ce es.scopes t n b sz <=>
             local_region ce es.scopes s n b sz` by
    (rpt gen_tac >> irule local_region_wb_frame >> metis_tac[]) >>
  simp[intcall_held_args_def, EVERY_MEM, FORALL_PROD] >>
  rpt gen_tac >> disch_tac >> rename1 `MEM (ty,raw,vv) H` >>
  drule_all intcall_held_args_member >> strip_tac >>
  `eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s` by
    (drule intcall_held_operand_defined >> strip_tac >>
     Cases_on `vv_operand vv` >> gvs[eval_operand_def, wb_frame_def] >>
     metis_tac[]) >>
  conj_tac >- (irule held_vv_at_alloc_frame >> gvs[wb_frame_def] >> metis_tac[]) >>
  conj_tac >- (irule intcall_vv_provenance_frame >> metis_tac[]) >>
  conj_tac >- (Cases_on `vv` >> gvs[vv_operand_def]) >>
  simp[] >> metis_tac[not_fresh_at_mono]
QED
