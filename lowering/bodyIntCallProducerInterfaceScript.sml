(* Provenance is attached to the success witness, never to a second run. *)
Theory bodyIntCallProducerInterface
Ancestors
  exprSimDefs exprSimMemorySource loweringPosts gasOutcome gasSummary
  bodyIntCallPathLayout finite_map vyperState venomState

Definition intcall_vv_provenance_def:
  intcall_vv_provenance cenv cx t sa sb es tv vv s <=>
    (!op.
       ((?t'. vv = StackValue t' op /\ ~is_word_type t) \/
        (?t' p. vv = LocatedValue t' p /\
                p.ptr_location = LocMemory /\ op = p.ptr_operand)) ==>
       !v tvt. read_result cx tv es = (INL v,es) /\
               evaluate_type (get_tenv cx) t = SOME tvt ==>
         ?w. eval_operand op s = SOME w /\
           ((?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
              sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
              b <= w2n w /\ w2n w + val_footprint tvt v <= b + sz /\
              (!n lb lsz. local_region cenv es.scopes s n lb lsz ==>
                          b + sz <= lb \/ lb + lsz <= b)) \/
            val_footprint tvt v = 0 \/
            (?n b sz. local_region cenv es.scopes s n b sz /\
              b <= w2n w /\ w2n w + val_footprint tvt v <= b + sz /\
              local_val_at cenv cx n (w2n w - b) tvt v /\ dynarray_free tvt) \/
            (?n b sz entry p base k.
              local_region cenv es.scopes s n b sz /\
              b <= w2n w /\ w2n w + val_footprint tvt v <= b + sz /\
              lookup_scopes n es.scopes = SOME entry /\
              FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz) /\
              lookup_var p s = SOME base /\ b = w2n base /\
              w2n w = w2n base + k /\
              value_has_type entry.type entry.value /\
              sub_layout entry.type entry.value k tvt v))) /\
    (!t' p w.
       vv = LocatedValue t' p /\ p.ptr_location = LocCode /\
       eval_operand p.ptr_operand s = SOME w ==>
       ?name off itv iv k tvt v.
         FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
           SOME (ImmutableLoc off) /\ w = n2w (off + k) /\
         off + type_memory_size itv < dimword (:256) /\
         FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
                    NONE => FEMPTY
                  | SOME imms => get_source_immutables cenv.ce_module imms)
                 name = SOME (itv,iv) /\
         evaluate_type (get_tenv cx) t = SOME tvt /\
         sub_layout itv iv k tvt v /\ value_has_type tvt v /\
         read_result cx tv es = (INL v,es))
End

Theorem gas_summary_at_strengthen_witness:
  gas_summary_at memory p marks source start Q R /\
  (!res ee r. gas_marked_exec memory p source start marks res ee r ==>
     !t. r = OK t /\ Q res (ee with gas_obs := []) t ==>
         P res (ee with gas_obs := []) t) ==>
  gas_summary_at memory p marks source start
    (\res ee t. Q res ee t /\ P res ee t) R
Proof
  PairCases_on `p` >> PairCases_on `start` >>
  simp[gas_summary_at_def] >> metis_tac[]
QED

Theorem gas_outcome_strengthen_witness:
  gas_outcome memory tops p source start Q R /\
  (!marks res ee r.
     gas_marked_exec memory p source start marks res ee r ==>
     !t. r = OK t /\ Q res (ee with gas_obs := []) t ==>
         P res (ee with gas_obs := []) t) ==>
  gas_outcome memory tops p source start
    (\res ee t. Q res ee t /\ P res ee t) R
Proof
  simp[gas_outcome_def] >> metis_tac[gas_summary_at_strengthen_witness]
QED

Theorem read_result_success_gas_obs_iff:
  read_result cx tv (es with gas_obs := gs) = (INL v,es with gas_obs := gs) <=>
  read_result cx tv es = (INL v,es)
Proof
  eq_tac >> strip_tac >> drule read_result_gas_obs
  >- (disch_then (qspec_then `es.gas_obs` mp_tac) >> simp[]) >>
  simp[]
QED

Theorem intcall_vv_provenance_gas_obs[simp]:
  intcall_vv_provenance cenv cx t sa sb (es with gas_obs := gs) tv vv s <=>
  intcall_vv_provenance cenv cx t sa sb es tv vv s
Proof
  simp[intcall_vv_provenance_def, read_result_success_gas_obs_iff]
QED

Theorem intcall_vv_success_projection:
  (?tv. res = INL tv /\
    vv_post ctx func cenv cx e es sa sb s0 ee tv vv s /\
    s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts /\
    intcall_vv_provenance cenv cx (expr_type e) sa sb ee tv vv s) ==>
  ?tv. res = INL tv /\
    vv_post ctx func cenv cx e es sa sb s0 ee tv vv s /\
    s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  metis_tac[]
QED

Theorem intcall_vv_provenance_word:
  is_word_type t ==>
  intcall_vv_provenance cenv cx t sa sb es tv (StackValue t' op) s
Proof
  simp[intcall_vv_provenance_def]
QED

Theorem intcall_vv_provenance_memory_operand:
  intcall_vv_provenance cenv cx t sa sb es tv vv s /\
  ((?t'. vv = StackValue t' op /\ ~is_word_type t) \/
   (?t' p. vv = LocatedValue t' p /\
           p.ptr_location = LocMemory /\ op = p.ptr_operand)) /\
  read_result cx tv es = (INL v,es) /\
  evaluate_type (get_tenv cx) t = SOME tvt ==>
  ?w. eval_operand op s = SOME w
Proof
  rewrite_tac[intcall_vv_provenance_def] >> metis_tac[]
QED
