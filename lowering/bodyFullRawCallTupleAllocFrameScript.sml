(* The tuple allocation preserves the original constructor's ghost frame. *)
Theory bodyFullRawCallTupleAllocFrame
Ancestors
  bodyPtrIfExpAllocKept bodyPtrDefs exprSimProps loweringPosts
  stateRelProj externalReturnFootprint loweringHalt exprLoweringProps compileEnv
  ptrDiscipline venomState venomInst venomMemDefs freshWrites finite_map

Theorem raw_call_tuple_alloc_kept_at:
  stmt_state_rel (H:(bool # 256 word # type_value) list # num list)
    ctx func cenv cx es s /\
  wb_frame cenv es0 es sf s0 s /\
  ghost_kept_at lo cenv es0 sf G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sf /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  sf.cs_next_var <= sb.cs_next_var /\
  compile_alloc_buffer n sb = (buf,sc) /\ buf.buf_operand = Var out /\
  n < dimword (:256) /\ lo <= s.vs_alloca_next /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
  ghost_kept_at lo cenv es0 sf G0 tn0 s0
    (step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s u tn)
Proof
  strip_tac >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  `ghost_kept cenv es0 sf G0 tn0 s0 G tn` by
    (qhdtm_assum `ghost_kept_at` mp_tac >>
     rewrite_tac[ghost_kept_zero, ghost_kept_at_def]) >>
  `ghost_kept cenv es0 sf G0 tn0 s0
    (step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s u tn)`
    suffices_by rewrite_tac[ghost_kept_zero, ghost_kept_at_def] >>
  irule alloca_step_ghost_kept_bounded >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `local_region cenv es.scopes s name b sz` by
        (irule local_region_frame_fwd >> simp[] >>
         qexistsl_tac [`s0`, `sf`, `es0.scopes`] >> gvs[wb_frame_def]) >>
      metis_tac[return_local_region_frontier]) >>
  conj_tac
  >- (drule compile_alloc_buffer_parts >> strip_tac >> gvs[] >>
      metis_tac[not_fresh_at_mono]) >>
  rpt strip_tac >>
  `FLOOKUP s.vs_allocas aid = SOME (off,sz)` by gvs[wb_frame_def] >>
  gvs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]
QED
