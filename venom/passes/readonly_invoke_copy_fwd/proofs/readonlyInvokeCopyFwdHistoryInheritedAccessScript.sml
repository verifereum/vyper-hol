(* Current-map access consequences of paired inherited readonly histories.
   No transport of the current occurrence annotation is asserted here. *)
Theory readonlyInvokeCopyFwdHistoryInheritedAccess
Ancestors
  readonlyInvokeCopyFwdHistorySelected readonlyInvokeCopyFwdReadonlyReach
  occurrenceAccess occurrenceGeometry ptrDiscipline finite_map list

(* Reads of the inherited destination are protected slices, not dead reads.
   Reverting accesses are deliberately outside this boundary. *)
Theorem ricf_history_inherited_access:
  ricf_history_inherited vs C ctx0 log p stk PG G tn fn inst s /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  EVERY (readonly_origin_contract (rma_is_readonly ctx0.icf_rma) V)
    C.ctx_functions /\
  occurrence_natural_geometry lo a U B stk s /\
  occurrence_env_ok B owners H G /\
  FLOOKUP B p.rpe_dst = SOME (p.rpe_db,p.rpe_size) /\
  FLOOKUP B p.rpe_src = SOME (p.rpe_sb,p.rpe_size) /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s ==>
  (!off len k. MEM (off,len) (source_memory_write_ranges inst s) /\
     k < p.rpe_size ==>
     ~(off <= p.rpe_db+k /\ p.rpe_db+k < off+len) /\
     ~(off <= p.rpe_sb+k /\ p.rpe_sb+k < off+len)) /\
  (!ops off len. mem_read_ops inst = SOME ops /\
     op_prov G ops.iao_ofst = SOME (p.rpe_db,p.rpe_size) /\
     MEM (off,len) (source_memory_read_ranges inst s) ==>
     len = 0 \/ ?delta. off = p.rpe_db+delta /\ delta+len <= p.rpe_size)
Proof
  strip_tac >>
  reverse conj_tac >- metis_tac[occurrence_access_read_slice] >>
  `!ops. mem_write_ops inst = SOME ops ==>
     op_prov G ops.iao_ofst <> SOME (p.rpe_db,p.rpe_size) /\
     op_prov G ops.iao_ofst <> SOME (p.rpe_sb,p.rpe_size)` by
    (gvs[ricf_history_inherited_def] >>
     metis_tac[readonly_call_reachable_no_write]) >>
  rpt gen_tac >> strip_tac >> conj_tac >>
  metis_tac[occurrence_access_write_exclusion]
QED

(* Call positions remain readonly at both endpoints, independently of the
   range geometry and of whether the instruction is in revert-forward. *)
Theorem ricf_history_inherited_call_position:
  ricf_history_inherited vs C ctx0 log p stk PG G tn fn inst s /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  EVERY (readonly_origin_contract (rma_is_readonly ctx0.icf_rma) V)
    C.ctx_functions /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,args) /\
  k < LENGTH args /\
  (op_prov G (EL k args) = SOME (p.rpe_db,p.rpe_size) \/
   op_prov G (EL k args) = SOME (p.rpe_sb,p.rpe_size)) ==>
  rma_is_readonly ctx0.icf_rma nm k
Proof
  simp[ricf_history_inherited_def] >> rpt strip_tac >>
  metis_tac[readonly_call_reachable_call_position]
QED
