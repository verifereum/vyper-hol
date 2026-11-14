(* Original-context syntactic readonly soundness.  A runtime consumer must
   establish rma_origin for its address/argument variable using the original
   function's DFG and parameter-index map.  No claim about arbitrary runtime
   provenance maps is made here. *)
Theory readonlyInvokeCopyFwdReadonly
Ancestors
  readonlyMemoryArgsSound readonlyMemoryArgsOrigin readonlyMemoryArgsParam
  readonlyMemoryArgsProps
  invokeCopyFwdCommonDefs venomWf finite_map list pred_set

Theorem ricf_readonly_function_analysis:
  !C fn k.
    ALL_DISTINCT (MAP (\f. f.fn_name) C.ctx_functions) /\
    MEM fn C.ctx_functions /\
    rma_is_readonly (readonly_mem_analyze C) fn.fn_name k ==>
    k < LENGTH (rma_analyze_fn C.ctx_functions (readonly_mem_analyze C)
      (dfg_build_function fn) (collect_param_info (icf_fn_meta_of C) fn) fn) /\
    EL k (rma_analyze_fn C.ctx_functions (readonly_mem_analyze C)
      (dfg_build_function fn) (collect_param_info (icf_fn_meta_of C) fn) fn)
Proof
  rpt gen_tac >> rewrite_tac[readonly_mem_analyze_def] >> strip_tac >>
  drule_all rma_analyze_fn_equation >> strip_tac >>
  gvs[rma_is_readonly_iff]
QED

Theorem ricf_readonly_origin_no_write:
  !C fn k bb inst ops v.
    ALL_DISTINCT (MAP (\f. f.fn_name) C.ctx_functions) /\
    MEM fn C.ctx_functions /\
    rma_is_readonly (readonly_mem_analyze C) fn.fn_name k /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode <> INVOKE /\ mem_write_ops inst = SOME ops /\
    ops.iao_ofst = Var v ==>
    ~rma_origin (dfg_build_function fn)
      (collect_param_info (icf_fn_meta_of C) fn).fpi_invoke_param_index v k
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ricf_readonly_function_analysis >> strip_tac >>
  drule_all rma_analyze_fn_no_write >> strip_tac >>
  drule_all rma_analyze_fn_readonly >> strip_tac >>
  metis_tac[rma_origin_root_param_indices_op]
QED

Theorem ricf_readonly_origin_call:
  !C fn k bb inst name args j v.
    ALL_DISTINCT (MAP (\f. f.fn_name) C.ctx_functions) /\
    MEM fn C.ctx_functions /\
    rma_is_readonly (readonly_mem_analyze C) fn.fn_name k /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = INVOKE /\ inst.inst_operands = Label name :: args /\
    j < LENGTH args /\ EL j args = Var v /\
    rma_origin (dfg_build_function fn)
      (collect_param_info (icf_fn_meta_of C) fn).fpi_invoke_param_index v k ==>
    EXISTS (\callee. callee.fn_name = name) C.ctx_functions /\
    rma_is_readonly (readonly_mem_analyze C) name j
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ricf_readonly_function_analysis >> strip_tac >>
  drule_all rma_analyze_fn_readonly >> strip_tac >>
  drule_all rma_origin_root_param_indices_op >> strip_tac >>
  irule rma_analyze_fn_readonly_call >> gvs[] >> metis_tac[]
QED

(* Bridge an actual PARAM instruction to the syntactic origin relation.
   Readonly classification supplies the analysis's parameter-count bound. *)
Theorem ricf_readonly_param_origin:
  !C fn inst idx v.
    ALL_DISTINCT (MAP (\f. f.fn_name) C.ctx_functions) /\
    MEM fn C.ctx_functions /\ wf_ssa fn /\ ricf_param_order_ok fn /\
    rma_is_readonly (readonly_mem_analyze C) fn.fn_name (w2n idx) /\
    MEM inst (fn_insts fn) /\ inst.inst_opcode = PARAM /\
    inst.inst_operands = [Lit idx] /\ inst.inst_outputs = [v] ==>
    rma_origin (dfg_build_function fn)
      (collect_param_info (icf_fn_meta_of C) fn).fpi_invoke_param_index v (w2n idx)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ricf_readonly_function_analysis >> strip_tac >>
  drule_all rma_analyze_fn_readonly >> strip_tac >>
  irule (cj 1 rma_origin_rules) >>
  irule ricf_param_index_lookup >> metis_tac[]
QED
