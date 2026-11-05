Theory deadStoreElimCertificate
Ancestors
  decoratedExecution deadStoreElimExecution deadStoreElimSafety
  deadStoreElimDefs basePtrDefs venomMemDefs venomExecSemantics venomState
  finite_map words

(* Concrete field-dependent decoration: caller safe_inv is used only in
   the initial construction, never asserted on transformed states. *)
Definition dse_occ_safe_def:
  dse_occ_safe fn inst s <=>
    alloca_inv s /\
    (!aid base sz. FLOOKUP s.vs_allocas aid = SOME (base, sz) ==>
                   base + sz < dimword (:256)) /\
    bp_ptr_sound (bp_analyze (cfg_analyze fn) fn) s /\
    bp_ptrs_bounded (bp_analyze (cfg_analyze fn) fn) fn s /\
    bp_accesses_in_own_alloca (bp_analyze (cfg_analyze fn) fn) inst s
End

Definition dse_run_certificate_def:
  dse_run_certificate fn fuel ctx s r <=>
    decorated_run (dse_occ_safe fn) fuel ctx fn s r
End

Theorem dse_certificate_initial:
  s.vs_inst_idx = 0 /\ safe_inv s /\
  (!bb s0 s1.
    lookup_block s0.vs_current_bb fn.fn_blocks = SOME bb /\
    s0.vs_inst_idx = 0 /\ safe_inv s0 /\
    eval_phis s0 bb.bb_instructions = OK s1 ==>
    safe_inv (s1 with vs_inst_idx := phi_prefix_length bb.bb_instructions)) /\
  (!bb inst fuel' s0 s1.
    lookup_block s0.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s0.vs_inst_idx = SOME inst /\ safe_inv s0 /\
    step_inst fuel' ctx inst s0 = OK s1 ==>
    safe_inv (if is_terminator inst.inst_opcode then s1
              else s1 with vs_inst_idx := SUC s0.vs_inst_idx)) /\
  (!s0. safe_inv s0 ==>
    alloca_inv s0 /\
    (!aid base sz. FLOOKUP s0.vs_allocas aid = SOME (base, sz) ==>
                   base + sz < dimword (:256)) /\
    bp_ptr_sound (bp_analyze (cfg_analyze fn) fn) s0 /\
    bp_ptrs_bounded (bp_analyze (cfg_analyze fn) fn) fn s0 /\
    (!bb inst. lookup_block s0.vs_current_bb fn.fn_blocks = SOME bb /\
       get_instruction bb s0.vs_inst_idx = SOME inst ==>
       bp_accesses_in_own_alloca (bp_analyze (cfg_analyze fn) fn) inst s0)) /\
  run_blocks fuel ctx fn s = r /\ ~(?e. r = Error e) ==>
  dse_run_certificate fn fuel ctx s r
Proof
  strip_tac >> gvs[dse_run_certificate_def] >>
  irule decorated_run_invariant >>
  reverse conj_tac >- metis_tac[] >> qexists_tac `safe_inv` >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (rpt gen_tac >> strip_tac >> simp[dse_occ_safe_def] >>
      first_x_assum drule >> strip_tac >> simp[] >> metis_tac[]) >>
  first_assum ACCEPT_TAC
QED
