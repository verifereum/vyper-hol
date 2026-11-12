Theory bodyPtrStructLitOwnershipEntryPc
Ancestors
  bodyPtrStructLitOwnershipEntryPrefix bodyPtrStructLitOwnershipSteps
  bodyPtrStructLitOwnershipInternalShape bodyPtrStructLitOwnershipInternalEntry
  bodyPtrStructLitOwnershipFreshness loweringShapeProps loweringShapeDefs
  compileEnv context

Theorem entry_pair_map[local]:
  (do x <- (f : 'a compiler); y <- (g x : 'b compiler); return (y,x,z) od) =
  (do p <- (do x <- f; y <- g x; return (y,x) od);
      return (FST p,SND p,z) od)
Proof
  simp[FUN_EQ_THM, comp_bind_def, comp_return_def] >>
  gen_tac >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[]
QED

Theorem alloc_run_internal_entry_prefix_pc_frame:
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
             return (ce',imm,pc) od) entry
     od)
    (\(ce',imm,pc) st. shape_state st /\ R st /\
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
  CONV_TAC (ONCE_DEPTH_CONV (HO_REWR_CONV entry_pair_map)) >>
  irule alloc_run_bind >>
  qexists `\(ce',imm) st. shape_state st /\ R st /\
    cenv_shape_ok st (ce' with <|ce_imm_alloca := imm; ce_alloca_locals := T|>) /\
    fresh_outputs st` >> conj_tac
  >- (gen_tac >> PairCases_on `v` >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
  irule alloc_run_conseq >>
  irule_at Any alloc_run_internal_installed_suffix_frame >>
  qexists `R` >> simp[] >> rpt strip_tac >>
  irule (SRULE [] structlit_internal_cenv_install_shape) >>
  Cases_on `v0` >> simp[]
QED
