(* TOP-LEVEL: source-state and live-local relations survive expression loads
   and instruction-index advancement. Live pointer lifetimes protect their
   bindings even when unrelated generated variables are overwritten. *)
Theory sourceValueFrames
Ancestors
  nameLoweringProps localPtrsProps valueLoadProps eventTopicExecProps
  compileEnv valueEncoding exprLoweringProps instIdxIndep abiFieldOperands
  venomState venomExecSemantics

Theorem state_rel_simple_inst_idx[simp]:
  !cenv cx es ss index.
    state_rel_simple cenv cx es (ss with vs_inst_idx := index) = state_rel_simple cenv cx es ss
Proof
  simp[state_rel_simple_def, vars_rel_def, storage_rel_def, transient_rel_def,
    immutables_rel_simple_def, logs_rel_def, call_ctx_rel_def,
    contract_storage_def, contract_transient_def]
QED

Theorem local_ptrs_rel_inst_idx[simp]:
  !func cenv scopes ss index.
    local_ptrs_rel func cenv scopes (ss with vs_inst_idx := index) = local_ptrs_rel func cenv scopes ss
Proof
  simp[local_ptrs_rel_def, local_backed_def, local_region_def, lookup_var_def]
QED

Theorem lowered_value_rel_inst_idx[simp]:
  !ty tv v op ss index.
    lowered_value_rel ty tv v op (ss with vs_inst_idx := index) = lowered_value_rel ty tv v op ss
Proof
  simp[lowered_value_rel_def, eval_op_inst_idx]
QED

Theorem fresh_vars_wrt_inst_idx[simp]:
  !cs ss index. fresh_vars_wrt cs (ss with vs_inst_idx := index) = fresh_vars_wrt cs ss
Proof
  simp[fresh_vars_wrt_def]
QED

Theorem local_pointer_operands_frame:
  !bound cenv scopes before after.
    (!name entry p region_size. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before bound (Var p)) /\
    (!arg_op. abi_operand_before bound arg_op ==> eval_operand arg_op after = eval_operand arg_op before) ==>
    !name entry p region_size. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> lookup_var p after = lookup_var p before
Proof
  rpt gen_tac >> strip_tac >> MAP_EVERY qx_gen_tac [`name`, `entry`, `p`, `region_size`] >> strip_tac >>
  `abi_operand_before bound (Var p)` by
    (qpat_x_assum `!name entry p region_size. _` (qspecl_then [`name`, `entry`, `p`, `region_size`] mp_tac) >> simp[]) >>
  qpat_x_assum `!arg_op. _` (qspec_then `Var p` mp_tac) >> simp[eval_operand_def]
QED

Theorem local_ptrs_rel_before_assignment_frame:
  !func cenv scopes bound before after.
    local_ptrs_rel func cenv scopes before /\ after with vs_vars := before.vs_vars = before /\
    (!name entry p region_size. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before bound (Var p)) /\
    (!arg_op. abi_operand_before bound arg_op ==> eval_operand arg_op after = eval_operand arg_op before) ==>
    local_ptrs_rel func cenv scopes after
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`bound`, `cenv`, `scopes`, `before`, `after`] local_pointer_operands_frame) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  `after.vs_allocas = before.vs_allocas /\ after.vs_alloca_next = before.vs_alloca_next /\
    after.vs_memory = before.vs_memory` by
    (qpat_x_assum `after with vs_vars := before.vs_vars = before`
       (mp_tac o AP_TERM ``\ss. (ss.vs_allocas,ss.vs_alloca_next,ss.vs_memory)``) >> simp[]) >>
  irule local_ptrs_rel_frame >> qexists_tac `before` >> rpt conj_tac >>
  FIRST [first_assum MATCH_ACCEPT_TAC, simp[] >> rpt strip_tac >> gvs[]]
QED

Theorem state_rel_simple_assignment_index_frame:
  !cenv cx es before after index.
    state_rel_simple cenv cx es before /\
    after with vs_vars := before.vs_vars = before with vs_inst_idx := index ==>
    state_rel_simple cenv cx es after
Proof
  rpt gen_tac >> strip_tac >> irule state_rel_simple_assignment_frame >>
  qexists_tac `before with vs_inst_idx := index` >> simp[]
QED

Theorem local_ptrs_rel_before_assignment_index_frame:
  !func cenv scopes bound before after index.
    local_ptrs_rel func cenv scopes before /\
    after with vs_vars := before.vs_vars = before with vs_inst_idx := index /\
    (!name entry p region_size. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before bound (Var p)) /\
    (!arg_op. abi_operand_before bound arg_op ==> eval_operand arg_op after = eval_operand arg_op before) ==>
    local_ptrs_rel func cenv scopes after
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`func`, `cenv`, `scopes`, `bound`, `before with vs_inst_idx := index`, `after`]
    local_ptrs_rel_before_assignment_frame) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, simp[eval_op_inst_idx]]) >> simp[]
QED
