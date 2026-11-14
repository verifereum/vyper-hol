Theory readonlyInvokeCopyFwdReadonlyContract
Ancestors
  readonlyInvokeCopyFwdReadonly readonlyProvenanceSupport
  readonlyMemoryArgsOrigin readonlyMemoryArgsDefs pointerConfinedDefs
  readonlyMemoryArgsParam venomWf venomInst venomExecSemantics
  memLocDefs o1PassContract unitShapeDefs list pred_set

(* The unqualified closure clause also covers malformed ASSIGN operands,
   whereas analysis origins deliberately do not trace those instructions. *)
Theorem ricf_analysis_origin_assign_shape_gap:
  !inst u. inst.inst_opcode = ASSIGN /\
    inst.inst_operands = [Var u; Lit 0w] ==>
    is_pointer_preserving_op inst.inst_opcode /\
    MEM (Var u) inst.inst_operands /\ root_from_inst_ops inst = []
Proof
  simp[is_pointer_preserving_op_def, root_from_inst_ops_def]
QED

Definition ricf_analysis_origins_def:
  ricf_analysis_origins C fn =
    {v | ?k. rma_is_readonly (readonly_mem_analyze C) fn.fn_name k /\
      rma_origin (dfg_build_function fn)
        (collect_param_info (icf_fn_meta_of C) fn).fpi_invoke_param_index v k}
End

Theorem ricf_analysis_readonly_origin_contract_fn:
  ALL_DISTINCT (MAP (\f. f.fn_name) C.ctx_functions) /\
  MEM fn C.ctx_functions /\ wf_ssa fn /\ ricf_param_order_ok fn /\
  fn_inst_wf fn ==>
  readonly_origin_contract (rma_is_readonly (readonly_mem_analyze C))
    (ricf_analysis_origins C) fn
Proof
  strip_tac >> rewrite_tac[readonly_origin_contract_def] >> rpt conj_tac
  >- (rpt strip_tac >>
      `inst.inst_outputs = [v]` by gvs[inst_output_def, AllCaseEqs()] >>
      simp[ricf_analysis_origins_def] >> qexists_tac `w2n idx` >>
      simp[] >> metis_tac[ricf_readonly_param_origin])
  >- (rpt strip_tac >>
      `inst_wf inst` by
        (gvs[fn_inst_wf_def, fn_insts_def, MEM_fn_insts_blocks_iff,
             MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
      gvs[ricf_analysis_origins_def] >> qexists_tac `k` >> simp[] >>
      irule rma_origin_pointer_preserving >>
      gvs[wf_ssa_def] >> metis_tac[])
  >- (rpt strip_tac >>
      gvs[ricf_analysis_origins_def] >>
      `inst.inst_opcode <> INVOKE` by
        (strip_tac >> gvs[mem_write_ops_def]) >>
      `?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions` by
        metis_tac[fn_insts_def, MEM_fn_insts_blocks_iff] >>
      metis_tac[ricf_readonly_origin_no_write])
  >> rpt strip_tac >>
  gvs[ricf_analysis_origins_def] >>
  `inst.inst_operands = Label nm :: args` by
    gvs[decode_invoke_def, AllCaseEqs()] >>
  `?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions` by
    metis_tac[fn_insts_def, MEM_fn_insts_blocks_iff] >>
  metis_tac[ricf_readonly_origin_call]
QED

Theorem ricf_analysis_readonly_origin_contract:
  o1_ctx_shape C /\
  ALL_DISTINCT (MAP (\f. f.fn_name) C.ctx_functions) /\
  EVERY wf_ssa C.ctx_functions /\
  EVERY ricf_param_order_ok C.ctx_functions ==>
  EVERY (readonly_origin_contract (rma_is_readonly (readonly_mem_analyze C))
    (ricf_analysis_origins C)) C.ctx_functions
Proof
  simp[EVERY_MEM] >> rpt strip_tac >>
  irule ricf_analysis_readonly_origin_contract_fn >>
  gvs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >> metis_tac[]
QED
