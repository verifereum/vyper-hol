(* Syntactic parameter origins; no assertion about runtime provenance. *)
Theory readonlyMemoryArgsOrigin
Ancestors
  readonlyMemoryArgsSound readonlyMemoryArgsDefs list rich_list finite_map pred_set
  venomWf pointerConfinedDefs

Inductive rma_origin:
  (!dfg param_idx p k.
    FLOOKUP param_idx p = SOME k ==> rma_origin dfg param_idx p k) /\
  (!dfg param_idx v w inst k.
    FLOOKUP param_idx v = NONE /\
    dfg_get_def dfg v = SOME inst /\
    MEM w (root_from_inst_ops inst) /\ rma_origin dfg param_idx w k ==>
    rma_origin dfg param_idx v k)
End

Theorem rma_origin_path:
  !dfg param_idx v k. rma_origin dfg param_idx v k ==>
    ?path. path <> [] /\ HD path = v /\
      FLOOKUP param_idx (LAST path) = SOME k /\
      (!j. SUC j < LENGTH path ==>
        ?inst. dfg_get_def dfg (EL j path) = SOME inst /\
               MEM (EL (SUC j) path) (root_from_inst_ops inst) /\
               FLOOKUP param_idx (EL j path) = NONE)
Proof
  ho_match_mp_tac rma_origin_ind >> rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (qexists_tac `[v]` >> simp[]) >>
  qexists_tac `v::path` >> simp[] >> conj_tac
  >- (Cases_on `path` >> gvs[]) >>
  Cases >> simp[] >> metis_tac[]
QED

Theorem rma_origin_root_param_indices:
  !dfg param_idx v k n visited.
    rma_origin dfg param_idx v k /\ k < n ==>
    k IN root_param_indices dfg param_idx n visited v
Proof
  rpt strip_tac >> drule rma_origin_path >> strip_tac >>
  drule_all root_param_indices_path >> simp[]
QED

Theorem rma_origin_root_param_indices_op:
  !dfg param_idx v k n visited.
    rma_origin dfg param_idx v k /\ k < n ==>
    k IN root_param_indices_op dfg param_idx n visited (Var v)
Proof
  simp[root_param_indices_op_def, rma_origin_root_param_indices]
QED

Theorem root_from_inst_ops_assign:
  !inst v. inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var v] ==>
    MEM v (root_from_inst_ops inst)
Proof
  simp[root_from_inst_ops_def]
QED

Theorem root_from_inst_ops_phi_add:
  !inst v. (inst.inst_opcode = PHI \/ inst.inst_opcode = ADD) /\
    MEM (Var v) inst.inst_operands ==> MEM v (root_from_inst_ops inst)
Proof
  rpt strip_tac >> simp[root_from_inst_ops_def, MEM_FLAT, MEM_MAP] >>
  qexists_tac `[v]` >> simp[] >> qexists_tac `Var v` >> simp[]
QED

Theorem root_from_inst_ops_sub:
  !inst a b v. inst.inst_opcode = SUB /\ inst.inst_operands = [b;a] /\
    (a = Var v \/ b = Var v) ==> MEM v (root_from_inst_ops inst)
Proof
  rpt strip_tac >> gvs[root_from_inst_ops_def] >>
  Cases_on `a` >> Cases_on `b` >> simp[]
QED

Theorem root_from_inst_ops_pointer_preserving:
  !inst u. inst_wf inst /\ is_pointer_preserving_op inst.inst_opcode /\
    MEM (Var u) inst.inst_operands ==> MEM u (root_from_inst_ops inst)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_pointer_preserving_op_def, inst_wf_def] >>
  gvs[LENGTH_EQ_NUM_compute] >>
  gvs[root_from_inst_ops_def, MEM_FLAT, MEM_MAP] >>
  qexists_tac `[u]` >> simp[] >> qexists_tac `Var u` >> simp[]
QED
