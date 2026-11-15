(* Endpoint producer audit.  These facts distinguish selected call sites
   from calls later in the same owner visit. *)
Theory readonlyInvokeCopyFwdProtectionProducers
Ancestors
  readonlyInvokeCopyFwdProtection readonlyInvokeCopyFwdPlan
  readonlyInvokeCopyFwdDefs invokeCopyFwdCommonDefs venomExecSemantics
  indexedLists list dfgDefs venomInst finite_map readonlyMemoryArgsProps

Theorem ricf_selected_source_operand_readonly:
  ~ricf_has_mutable_sibling ctx sites sv /\ MEM (callinst,p) sites /\
  icf_is_readonly_op ctx.icf_rma callinst p /\
  j < LENGTH callinst.inst_operands /\ j <> 0 /\
  icf_assign_root_op ctx.icf_dfg (EL j callinst.inst_operands) = Var sv ==>
  icf_is_readonly_op ctx.icf_rma callinst j
Proof
  simp[ricf_has_mutable_sibling_def, EXISTS_MEM, MEM_MAPi,
       pairTheory.EXISTS_PROD] >>
  rpt strip_tac >> CCONTR_TAC >>
  first_x_assum (qspecl_then [`callinst`,`p`] mp_tac) >> simp[] >>
  qexists_tac `j` >> simp[] >> metis_tac[]
QED

Theorem ricf_event_source_sibling_check:
  ricf_event_ok e bb /\ e.rfe_source = SOME sv ==>
  ~ricf_has_mutable_sibling e.rfe_ctx e.rfe_sites sv
Proof
  simp[ricf_event_ok_def, ricf_try_forward_def] >>
  strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem ricf_selected_call_source_readonly:
  ricf_event_ok e bb /\ e.rfe_source = SOME sv /\
  MEM (callinst,p) e.rfe_sites /\
  decode_invoke callinst = SOME (nm,ops) /\
  k < LENGTH ops /\
  icf_assign_root_op e.rfe_ctx.icf_dfg (EL k ops) = Var sv ==>
  rma_is_readonly e.rfe_ctx.icf_rma nm k
Proof
  rpt strip_tac >>
  drule_all ricf_event_source_sibling_check >> strip_tac >>
  drule_all ricf_event_sites_readonly >> strip_tac >>
  `callinst.inst_operands = Label nm :: ops` by
    (gvs[decode_invoke_def, AllCaseEqs()]) >>
  `icf_is_readonly_op e.rfe_ctx.icf_rma callinst (SUC k)` by
    (irule ricf_selected_source_operand_readonly >>
     simp[] >> metis_tac[]) >>
  gvs[icf_is_readonly_op_def, icf_get_callee_name_def]
QED

(* A later call is outside both the sibling check and the open interval
   checked by icf_has_src_clobber.  It must not inherit the old cross fact. *)
Definition ricf_late_call_block_def:
  ricf_late_call_block : basic_block =
    <| bb_label := "entry"; bb_instructions :=
      [mk_inst 1 ALLOCA [Lit 32w] ["src"];
       mk_inst 2 ALLOCA [Lit 32w] ["dst"];
       mk_inst 3 MCOPY [Var "dst";Var "src";Lit 32w] [];
       mk_inst 4 INVOKE [Label "reader";Var "dst"] [];
       mk_inst 5 INVOKE [Label "writer";Var "src"] [];
       mk_inst 6 STOP [] []] |>
End

Definition ricf_late_call_fn_def:
  ricf_late_call_fn = mk_raw_function "owner" [ricf_late_call_block]
End

Definition ricf_late_call_ctx_def:
  ricf_late_call_ctx = icf_build_ctx FEMPTY []
    (FEMPTY |+ ("reader",[T]) |+ ("writer",[F])) ricf_late_call_fn
End

Theorem ricf_late_call_dfg_fields[local]:
  (dfg_build_function ricf_late_call_fn).dfg_defs =
    FEMPTY |+ ("dst",mk_inst 2 ALLOCA [Lit 32w] ["dst"])
           |+ ("src",mk_inst 1 ALLOCA [Lit 32w] ["src"]) /\
  (dfg_build_function ricf_late_call_fn).dfg_uses =
    FEMPTY |+ ("src",[mk_inst 3 MCOPY [Var "dst";Var "src";Lit 32w] [];
                        mk_inst 5 INVOKE [Label "writer";Var "src"] []])
           |+ ("dst",[mk_inst 3 MCOPY [Var "dst";Var "src";Lit 32w] [];
                        mk_inst 4 INVOKE [Label "reader";Var "dst"] []])
Proof
  conj_tac >> EVAL_TAC >>
  simp[FLOOKUP_EXT, FUN_EQ_THM, FLOOKUP_UPDATE] >>
  gen_tac >> IF_CASES_TAC >> simp[] >> IF_CASES_TAC >> simp[]
QED

Theorem ricf_late_call_forward_accepted:
  ricf_try_forward ricf_late_call_ctx ricf_late_call_block 2 =
    SOME (SOME "src",[(mk_inst 4 INVOKE [Label "reader";Var "dst"] [],1)])
Proof
  `icf_collect_aliases (dfg_build_function ricf_late_call_fn) "dst" = {"dst"}` by
    (irule icf_collect_aliases_no_assign >>
     simp[dfg_get_uses_def, ricf_late_call_dfg_fields, FLOOKUP_UPDATE,
          mk_inst_def]) >>
  simp[ricf_try_forward_def, ricf_late_call_ctx_def,
       ricf_late_call_block_def, icf_build_ctx_def,
       icf_is_assign_output_use_def,
       invokeCopyFwdCommonDefsTheory.findi_def, INDEX_FIND_def,
       icf_assign_root_op_def, ricf_has_mutable_sibling_def,
       Once icf_assign_root_def, dfg_get_def_def, ricf_late_call_dfg_fields,
       FLOOKUP_UPDATE, mk_inst_def, icf_use_positions_def,
       dfg_get_uses_def, icf_is_readonly_op_def, icf_get_callee_name_def,
       readonlyMemoryArgsDefsTheory.rma_is_readonly_def,
       readonlyMemoryArgsDefsTheory.rma_get_readonly_idxs_def,
       icf_has_src_clobber_adjacent] >>
  simp[Once icf_assign_root_def, dfg_get_def_def,
       ricf_late_call_dfg_fields, FLOOKUP_UPDATE, mk_inst_def] >>
  simp[Once icf_assign_root_def, dfg_get_def_def,
       ricf_late_call_dfg_fields, FLOOKUP_UPDATE, mk_inst_def]
QED

Theorem ricf_late_call_is_mutable:
  decode_invoke (EL 4 ricf_late_call_block.bb_instructions) =
    SOME ("writer",[Var "src"]) /\
  ~rma_is_readonly ricf_late_call_ctx.icf_rma "writer" 0 /\
  ~icf_has_src_clobber ricf_late_call_ctx.icf_aliases
    ricf_late_call_ctx.icf_bp ricf_late_call_block.bb_instructions 2 [3]
    (bp_get_read_location ricf_late_call_ctx.icf_bp
      (EL 2 ricf_late_call_block.bb_instructions) AddrSp_Memory)
Proof
  simp[icf_has_src_clobber_adjacent, ricf_late_call_block_def,
       ricf_late_call_ctx_def, icf_build_ctx_def, mk_inst_def,
       decode_invoke_def, readonlyMemoryArgsDefsTheory.rma_is_readonly_def,
       readonlyMemoryArgsDefsTheory.rma_get_readonly_idxs_def, FLOOKUP_UPDATE]
QED
