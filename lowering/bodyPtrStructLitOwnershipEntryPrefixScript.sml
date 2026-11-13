Theory bodyPtrStructLitOwnershipEntryPrefix
Ancestors
  bodyPtrStructLitOwnershipInternalFrame bodyPtrStructLitOwnershipRetpc
  bodyPtrStructLitOwnershipFrame bodyPtrStructLitOwnershipShape
  bodyPtrStructLitOwnershipInternalEntry
  bodyPtrStructLitOwnershipImmutable bodyPtrStructLitOwnershipInternalShape
  bodyPtrStructLitOwnershipSteps bodyPtrStructLitOwnershipFreshness
  loweringShapeProps loweringShapeDefs loweringShapeRules
  moduleLowering compileEnv context emitHelper

(* The corresponding shape proof has a private keep-bb lemma; expose the
   capture boundary here because the RETPC ownership consumer also needs it. *)
Theorem structlit_internal_param_decls_keep_bb:
  !params idx st r st'.
    compile_internal_param_decls params idx st = (r,st') ==>
    st'.cs_current_bb = st.cs_current_bb
Proof
  Induct_on `params`
  >- simp[compile_internal_param_decls_def, comp_return_def] >>
  qx_gen_tac `h` >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_internal_param_decls_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule emit_op_facts >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem structlit_optional_return_param_keep_bb:
  (if has_ret_buf then
     do rb <- emit_op PARAM [Lit 0w]; return (SOME rb) od
   else return NONE) st = (r,st') ==>
  st'.cs_current_bb = st.cs_current_bb
Proof
  Cases_on `has_ret_buf` >>
  simp[comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  metis_tac[emit_op_facts]
QED

Theorem alloc_run_internal_param_capture_label_frame:
  shape_stable R ==>
  alloc_run (\st. shape_state st /\ R st /\ internal_label_ok st.cs_current_bb)
    (compile_internal_param_decls params idx)
    (\r st. shape_state st /\ R st /\ internal_label_ok st.cs_current_bb /\
      EVERY (\(name,is_stack,op). plain_operand st op) (FST r) /\
      fresh_outputs st)
Proof
  strip_tac >> drule alloc_run_internal_param_capture_frame >>
  simp[alloc_run_def] >> rpt strip_tac >>
  drule_all structlit_internal_param_decls_keep_bb >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem alloc_run_param_label_frame:
  shape_stable R ==>
  alloc_run (\st. shape_state st /\ R st /\ internal_label_ok st.cs_current_bb)
    (emit_op PARAM [Lit (n2w idx)])
    (\op st. shape_state st /\ R st /\ internal_label_ok st.cs_current_bb /\
      plain_operand st op /\ fresh_outputs st)
Proof
  strip_tac >>
  `alloc_run shape_state (emit_op PARAM [Lit (n2w idx)])
     (\op st. fresh_outputs st)` by
    (irule alloc_run_conseq >> irule_at Any alloc_run_emit_op_fresh >>
     simp[shape_state_def, shape_base_fresh_outputs]) >>
  `alloc_run (\st. shape_state st /\ R st)
     (emit_op PARAM [Lit (n2w idx)])
     (\op st. shape_state st /\ R st /\ plain_operand st op /\
       fresh_outputs st)` by
    (irule alloc_run_conseq >> irule_at Any alloc_run_shape_frame >>
     irule_at Any structlit_param_op_shape >>
     simp[SF ETA_ss] >> goal_assum (drule_at Any) >>
     qexists `R` >> simp[]) >>
  pop_assum mp_tac >> simp[alloc_run_def] >> rpt strip_tac >>
  drule emit_op_facts >> strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem alloc_run_optional_return_param_label_frame:
  shape_stable R ==>
  alloc_run (\st. shape_state st /\ R st /\ internal_label_ok st.cs_current_bb)
    (if has_ret_buf then
       do op <- emit_op PARAM [Lit 0w]; return (SOME op) od
     else return NONE)
    (\rb st. shape_state st /\ R st /\ internal_label_ok st.cs_current_bb /\
      (!op. rb = SOME op ==> plain_operand st op) /\ fresh_outputs st)
Proof
  strip_tac >> Cases_on `has_ret_buf` >> simp[]
  >- (irule alloc_run_bind >>
      qexists `\op st. shape_state st /\ R st /\
        internal_label_ok st.cs_current_bb /\ plain_operand st op /\
        fresh_outputs st` >>
      reverse conj_tac
      >- (mp_tac (Q.INST [`idx` |-> `0`] alloc_run_param_label_frame) >> simp[]) >>
      gen_tac >> simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl,
       shape_state_def, shape_base_fresh_outputs]
QED

Theorem alloc_run_internal_physical_prefix_frame:
  shape_stable R ==>
  alloc_run (\st. shape_state st /\ R st /\ internal_label_ok st.cs_current_bb)
    (do rb <- (if has_ret_buf then
                 do op <- emit_op PARAM [Lit 0w]; return (SOME op) od
               else return NONE);
        r <- compile_internal_param_decls params (if has_ret_buf then 1 else 0);
        pc <- emit_op RETPC_PARAM [Lit (n2w (SND r))];
        return (rb,FST r,pc)
     od)
    (\(rb,captured,pc) st. shape_state st /\ R st /\
      (!op. rb = SOME op ==> plain_operand st op) /\
      EVERY (\(name,is_stack,op). plain_operand st op) captured /\
      retpc_operand st pc /\ fresh_outputs st)
Proof
  strip_tac >> irule alloc_run_bind >>
  qexists `\rb st. shape_state st /\ R st /\
    internal_label_ok st.cs_current_bb /\
    (!op. rb = SOME op ==> plain_operand st op) /\ fresh_outputs st` >>
  reverse conj_tac >- simp[alloc_run_optional_return_param_label_frame] >>
  qx_gen_tac `rb` >> simp[] >> irule alloc_run_bind >>
  qexists `\r st. shape_state st /\ R st /\
    (!op. rb = SOME op ==> plain_operand st op) /\
    internal_label_ok st.cs_current_bb /\
    EVERY (\(name,is_stack,op). plain_operand st op) (FST r) /\
    fresh_outputs st` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >>
      irule_at Any alloc_run_internal_param_capture_label_frame >>
      qexists `\st. R st /\ (!op. rb = SOME op ==> plain_operand st op)` >>
      simp[shape_stable_conj, structlit_optional_plain_shape_stable] >>
      metis_tac[]) >>
  qx_gen_tac `r` >> simp[] >> irule alloc_run_bind >>
  qexists `\pc st. shape_state st /\ R st /\
    (!op. rb = SOME op ==> plain_operand st op) /\
    EVERY (\(name,is_stack,op). plain_operand st op) (FST r) /\
    retpc_operand st pc /\ fresh_outputs st` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_retpc_frame >>
      qexists `\st. R st /\ (!op. rb = SOME op ==> plain_operand st op) /\
        EVERY (\(name,is_stack,op). plain_operand st op) (FST r)` >>
      simp[shape_stable_conj, structlit_optional_plain_shape_stable,
           structlit_captured_params_shape_stable] >> metis_tac[]) >>
  gen_tac >> simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_internal_installed_suffix_frame:
  shape_stable R ==>
  alloc_run (\st. shape_state st /\ R st /\ cenv_shape_ok st ce /\
      EVERY (\(name,is_stack,op). plain_operand st op) captured)
    (do imm <- (if is_ctor /\ imm_len > 0 then
                  do r <- compile_fixed_region_with_id imm_len;
                     return (SOME (SND r).buf_operand) od
                else return NONE);
        ce' <- materialize_internal_params ce captured;
        return (ce',imm)
     od)
    (\(ce',imm) st. shape_state st /\ R st /\
      cenv_shape_ok st (ce' with <|ce_imm_alloca := imm; ce_alloca_locals := T|>) /\
      fresh_outputs st)
Proof
  strip_tac >> irule alloc_run_bind >>
  qexists `\imm st. shape_state st /\ R st /\ cenv_shape_ok st ce /\
    EVERY (\(name,is_stack,op). plain_operand st op) captured /\
    (!b. imm = SOME b ==> plain_operand st b) /\ fresh_outputs st` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >>
      irule_at Any alloc_run_internal_immutable_frame >>
      qexists `\st. R st /\ cenv_shape_ok st ce /\
        EVERY (\(name,is_stack,op). plain_operand st op) captured` >>
      simp[shape_stable_conj, cenv_shape_ok_stable,
           structlit_captured_params_shape_stable] >> metis_tac[]) >>
  qx_gen_tac `imm` >> simp[] >> irule alloc_run_bind >>
  qexists `\ce' st. shape_state st /\ R st /\
    (!b. imm = SOME b ==> plain_operand st b) /\ cenv_shape_ok st ce' /\
    ce'.ce_return_pc = ce.ce_return_pc /\ fresh_outputs st` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >>
      irule_at Any alloc_run_internal_param_materialization_frame >>
      qexists `\st. R st /\ (!b. imm = SOME b ==> plain_operand st b)` >>
      simp[shape_stable_conj, structlit_optional_plain_shape_stable] >>
      metis_tac[]) >>
  gen_tac >> simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
  metis_tac[structlit_internal_body_env_shape]
QED

Theorem alloc_run_internal_entry_prefix_frame:
  shape_stable R /\ cenv_static_ok ce ==>
  alloc_run (\st. shape_state st /\ R st /\ internal_label_ok st.cs_current_bb)
    (do entry <-
          (do rb <- (if has_ret_buf then
                       do op <- emit_op PARAM [Lit 0w]; return (SOME op) od
                     else return NONE);
              r <- compile_internal_param_decls params
                     (if has_ret_buf then 1 else 0);
              pc <- emit_op RETPC_PARAM [Lit (n2w (SND r))];
              return (rb,FST r,pc) od);
        (\(rb,captured,pc).
          do imm <- (if is_ctor /\ imm_len > 0 then
                       do r <- compile_fixed_region_with_id imm_len;
                          return (SOME (SND r).buf_operand) od
                     else return NONE);
             ce' <- materialize_internal_params
               (ce with <|ce_return_buf :=
                 (case (rb,ce.ce_return_buf) of
                    (SOME op,SOME (MemLoc off sz)) => SOME (PtrVar op sz)
                  | _ => ce.ce_return_buf);
                 ce_return_pc := SOME (PtrVar pc 0)|>) captured;
             return (ce',imm) od) entry
     od)
    (\(ce',imm) st. shape_state st /\ R st /\
      cenv_shape_ok st (ce' with <|ce_imm_alloca := imm; ce_alloca_locals := T|>) /\
      fresh_outputs st)
Proof
  strip_tac >> irule alloc_run_bind >>
  qexists `\(rb,captured,pc) st. shape_state st /\ R st /\
    (!op. rb = SOME op ==> plain_operand st op) /\
    EVERY (\(name,is_stack,op). plain_operand st op) captured /\
    retpc_operand st pc /\ fresh_outputs st` >>
  reverse conj_tac >- simp[alloc_run_internal_physical_prefix_frame] >>
  gen_tac >> PairCases_on `v` >> simp[] >>
  irule alloc_run_conseq >>
  irule_at Any alloc_run_internal_installed_suffix_frame >>
  qexists `R` >> simp[] >> rpt strip_tac >>
  irule (SRULE [] structlit_internal_cenv_install_shape) >>
  Cases_on `v0` >> simp[]
QED
