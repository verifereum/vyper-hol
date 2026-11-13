Theory concretizeLayoutLocalPhi
Ancestors frameRelocationPhi frameRelocationTaintOrder frameRelocationEnvironment
  concretizeLayoutReaderContext venomExecProofs ptrDiscipline venomState
  finite_map pred_set list

(* Selections use the original masks, even when destinations alias inputs. *)
Theorem phis_taint_subset:
  !insts. (!v. op_taint un (Var v) SUBSET op_taint tn (Var v)) ==>
  !v. (case FLOOKUP (phis_taint prev un insts) v of NONE => {} | SOME m => m)
      SUBSET
      (case FLOOKUP (phis_taint prev tn insts) v of NONE => {} | SOME m => m)
Proof
  Induct >> simp[phis_taint_def] >> rpt strip_tac
  >- gvs[op_taint_def] >>
  Cases_on `h.inst_opcode = PHI` >> simp[]
  >- (irule set_var_taint_subset >> conj_tac
      >- (first_x_assum irule >> simp[]) >>
      Cases_on `prev` >> simp[phi_taint_def] >>
      Cases_on `resolve_phi x h.inst_operands` >> simp[] >>
      Cases_on `x'` >> gvs[op_taint_def]) >>
  gvs[op_taint_def]
QED

Theorem relocation_taint_le_phis:
  relocation_taint_le R tn un ==>
  relocation_taint_le R (tn with t_var := phis_taint prev tn insts)
    (un with t_var := phis_taint prev un insts)
Proof
  simp[relocation_taint_le_def, op_taint_def] >> strip_tac >>
  irule phis_taint_subset >> gvs[op_taint_def]
QED

Theorem concretize_parallel_phis_transport:
  local_rel (\u. F) (guarded_ptr (retpc_var fn) L rv)
    (guarded_bytes (retpc_var fn) rv tn) R
    (\s t. dead_result_rel D (Halt s) (Halt t)) s t /\
  relocation_taint_le R tn un /\ relocation_env s t /\
  relocation_reader_context s t /\ s.vs_prev_bb = t.vs_prev_bb /\
  EVERY (\inst. MEM inst (fn_insts fn)) insts /\
  eval_phis s insts = OK post ==>
  ?tpost. eval_phis t insts = OK tpost /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn) L (resolved_phis s.vs_prev_bb rv insts))
      (guarded_bytes (retpc_var fn) (resolved_phis s.vs_prev_bb rv insts)
        (tn with t_var := phis_taint s.vs_prev_bb tn insts)) R
      (\s t. dead_result_rel D (Halt s) (Halt t)) post tpost /\
    relocation_taint_le R
      (tn with t_var := phis_taint s.vs_prev_bb tn insts)
      (un with t_var := phis_taint t.vs_prev_bb un insts) /\
    relocation_env post tpost /\ relocation_reader_context post tpost /\
    phis_prov s.vs_prev_bb (SND o_f rv) insts =
      SND o_f (resolved_phis s.vs_prev_bb rv insts)
Proof
  strip_tac >>
  `s.vs_labels = t.vs_labels` by gvs[relocation_env_def] >>
  `!a b v x y. dead_result_rel D (Halt a) (Halt b) ==>
    dead_result_rel D (Halt (update_var v x a))
      (Halt (update_var v y b))` by
    simp[dead_result_rel_def, update_var_def] >>
  drule retpc_parallel_phis >>
  disch_then (qspecl_then [`post`, `insts`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `t'` >> simp[resolved_phis_erasure] >>
  conj_tac >- metis_tac[relocation_taint_le_phis] >>
  qpat_assum `eval_phis s insts = OK post`
    (mp_tac o MATCH_MP eval_phis_only_updates_vs_vars) >> strip_tac >>
  qpat_x_assum `eval_phis t insts = OK _`
    (mp_tac o MATCH_MP eval_phis_only_updates_vs_vars) >>
  strip_tac >>
  gvs[relocation_env_def, relocation_reader_context_def,
      venom_state_component_equality]
QED
