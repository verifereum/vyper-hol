(* Consumer-facing universal transfer probes.  No finite-fuel claim yet. *)
Theory concretizeAnalysisBoundary
Ancestors concretizeMemLocDefs basePtrProofs basePtrConvergenceOrder basePtrDefs list pred_set combin venomInst
  venomExecSemantics venomState finite_map words

Definition bp_bases_def:
  bp_bases r v = set (MAP ptr_base (bp_get_ptrs r v))
End

Definition bp_base_covers_def:
  bp_base_covers r s <=> !v. bp_bases r v SUBSET bp_bases s v
End

Theorem bp_assign_base_transfer:
  inst_output inst = SOME out /\ inst.inst_opcode = ASSIGN /\
  inst.inst_operands = [Var src] ==>
  bp_bases (SND (bp_handle_inst r inst)) out = bp_bases r src
Proof
  rpt strip_tac >>
  simp[bp_bases_def, bp_handle_inst_def, bp_get_ptrs_update]
QED

Theorem bp_add_base_transfer:
  inst_output inst = SOME out /\ inst.inst_opcode = ADD /\
  inst.inst_operands = [Var x; Var y] /\
  bp_get_ptrs r x <> [] /\ bp_get_ptrs r y = [] ==>
  bp_bases (SND (bp_handle_inst r inst)) out = bp_bases r x
Proof
  rpt strip_tac >>
  simp[bp_bases_def, bp_handle_inst_def, bp_get_ptrs_update, MAP_MAP_o, o_DEF] >>
  AP_TERM_TAC >> irule MAP_CONG >> simp[] >> Cases >> rename1 `Ptr a off` >> Cases_on `off` >> simp[offset_by_def, ptr_base_def]
QED

(* ALLOCA caches sites within a frame; a loop does not create new instances. *)
Theorem exec_alloca_cached_site:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
  exec_alloca inst s n = OK (update_var out (n2w b) s)
Proof
  simp[venomExecSemanticsTheory.exec_alloca_def]
QED

Theorem exec_alloca_cached_frame:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  exec_alloca inst s n = OK s' ==>
  s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next
Proof
  rpt strip_tac >>
  gvs[venomExecSemanticsTheory.exec_alloca_def, venomStateTheory.update_var_def]
QED

Theorem setup_callee_empty_allocas:
  setup_callee fn args caller = SOME callee ==>
  callee.vs_allocas = FEMPTY
Proof
  rw[venomExecSemanticsTheory.setup_callee_def] >> gvs[]
QED

Theorem bp_sub_base_transfer:
  inst_output inst = SOME out /\ inst.inst_opcode = SUB /\
  inst.inst_operands = [Var x; Var y] /\
  bp_get_ptrs r x <> [] /\ bp_get_ptrs r y = [] ==>
  bp_bases (SND (bp_handle_inst r inst)) out = bp_bases r x
Proof
  rpt strip_tac >>
  simp[bp_bases_def, bp_handle_inst_def, bp_get_ptrs_update, MAP_MAP_o, o_DEF] >>
  AP_TERM_TAC >> irule MAP_CONG >> simp[] >> Cases >>
  rename1 `Ptr a off` >> Cases_on `off` >>
  simp[offset_by_def, ptr_base_def]
QED

Theorem bp_phi_base_transfer:
  inst_output inst = SOME out /\ inst.inst_opcode = PHI ==>
  bp_bases (SND (bp_handle_inst r inst)) out =
    bp_bases r out UNION
    BIGUNION (set (MAP (bp_bases r) (MAP SND (phi_pairs inst.inst_operands))))
Proof
  rpt strip_tac >>
  `bp_bases (SND (bp_handle_inst r inst)) out =
   set (MAP ptr_base (bp_normalize (bp_get_ptrs r out ++
     FLAT (MAP (bp_get_ptrs r) (MAP SND (phi_pairs inst.inst_operands))))))`
    by (simp[bp_handle_inst_def] >>
        Cases_on `bp_normalize (bp_get_ptrs r out ++
          FLAT (MAP (bp_get_ptrs r) (MAP SND (phi_pairs inst.inst_operands)))) = []`
        >- gvs[bp_normalize_eq_nil, bp_bases_def] >>
        simp[bp_bases_def, bp_get_ptrs_update]) >>
  asm_rewrite_tac[] >>
  simp[bp_normalize_base_set, bp_bases_def, MAP_APPEND, MAP_FLAT,
       MAP_MAP_o, o_DEF, LIST_TO_SET_APPEND, LIST_TO_SET_FLAT]
QED

(* A false flag preserves lookups, not necessarily the finite map's domain.
   Instruction and block versions are bp_handle_inst_stable_ptrs and
   bp_process_block_unchanged in basePtrProofsTheory. *)
Theorem bp_one_pass_aux_stable_ptrs:
  !order fn bp.
    FST (bp_one_pass_aux fn bp order) = F ==>
    !v. bp_get_ptrs (SND (bp_one_pass_aux fn bp order)) v = bp_get_ptrs bp v
Proof
  Induct >> simp[bp_one_pass_aux_def] >> rpt gen_tac >>
  Cases_on `FIND (\bb. bb.bb_label = h) fn.fn_blocks`
  >- (simp[] >> metis_tac[]) >>
  rename1 `_ = SOME bb` >>
  Cases_on `bp_process_block bp bb.bb_instructions` >>
  rename1 `_ = (c1,r1)` >>
  Cases_on `bp_one_pass_aux fn r1 order` >>
  rename1 `_ = (c2,r2)` >>
  simp[] >> strip_tac >>
  `FST (bp_process_block bp bb.bb_instructions) = F` by simp[] >>
  drule bp_process_block_unchanged >>
  simp[] >> strip_tac >>
  first_x_assum (qspecl_then [`fn`,`r1`] mp_tac) >> simp[]
QED

Theorem bp_one_pass_stable_ptrs:
  FST (bp_one_pass fn order bp) = F ==>
  !v. bp_get_ptrs (SND (bp_one_pass fn order bp)) v = bp_get_ptrs bp v
Proof
  simp[bp_one_pass_def, bp_one_pass_aux_stable_ptrs]
QED

Theorem bp_iterate_fuel_fixed:
  !n fn order bp.
    bp_one_pass fn order bp = (F,bp) ==>
    bp_iterate_fuel n fn order bp = bp
Proof
  Induct >> simp[bp_iterate_fuel_def]
QED

(* PARAM provenance is supplied by the caller's PG, not the local BP map. *)
Theorem bp_param_passthrough:
  inst.inst_opcode = PARAM ==> bp_handle_inst r inst = (F,r)
Proof
  strip_tac >> Cases_on `inst_output inst` >> simp[bp_handle_inst_def]
QED

(* Origin audit (interfaces, not a completeness theorem).
   Runtime sources are ptrDisciplineTheory.out_prov, phi_prov and
   frame_reachable rules call/ret; static sources are basePtrDefsTheory.

   instruction  runtime origin                   local BP / consumer
   ALLOCA       s'.vs_allocas[inst_id]            Allocation inst_id;
                                                  find_base_allocas
   DALLOCA      (output, new_fmp - output)        ignored; separate FMP region
   PARAM        PG[index]                        ignored; caller argument lives
   ASSIGN       first_prov G operands            copies source bases
   PHI          selected edge, pre-entry G       union of all incoming bases
   ADD/SUB      first_prov G operands            affine transfer of local bases
   call return  restored caller G, outputs cut   ignored (not a pointer seed)

   ptr_roots includes ALLOCA, DALLOCA and designated pointer PARAMs; it
   classifies legal pointer uses, not BP seeds. A call saves caller G,
   sets callee PG = MAP (op_prov G) args, and starts callee G at FEMPTY.
   Thus callee local BP must NOT represent caller allocation identities.

   concretizeMemLocDefsTheory.ml_liveat_inst adds both every operand's
   bases and callee mems_used at INVOKE. ml_used_inst adds them to forward
   demand too. ml_used_block merges live_pallocas at block entry, but
   context_mem_livesets supplies []: incoming pointer retention must be
   proved at the suspended caller's INVOKE, not by inventing callee seeds.
   callee_mems_used reads fn_mems_used; imported_mems_used collects it at
   calls; imported_liveset_info and compute_alloc_map_fuel_in_context keep
   imported intervals at their fixed positions. These computations do not
   themselves establish semantic completeness of the imported metadata.

   Proposed runtime invariant to validate next (not assumed here): equip
   each frame with an origin map from concrete (base,size) pairs to tagged
   origins. For every G[v] = site, either (1) site is a local ALLOCA origin
   a covered by bp_bases r v, (2) it is an incoming PG origin with a retained
   suspended-caller witness, or (3) it is a DALLOCA origin in the FMP region.
   Copy/PHI/affine steps propagate this disjunction. Call pushes the
   retention witness; return restores it and drops output provenance.
   Quantitative local BP coverage, caller retention throughout nested
   calls, callee summary coverage for local/transitive static allocations,
   and sufficient iteration fuel remain separate unproved obligations.
   Absence of PARAM entries alone is not a stage counterexample.
*)
