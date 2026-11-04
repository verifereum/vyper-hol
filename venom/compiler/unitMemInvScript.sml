(*
 * The unit memory invariant the compiler stages share (PLAN §5.8, #641).
 *
 * mem_inv M ctx vs packages one reachability witness with one per-state
 * memory fact M.  The reachability part is fixed: raw_reachable vs ctx is
 * the least packaged witness, so mem_inv M ctx vs says exactly that the
 * context entry resolves and M holds at every raw-reachable state
 * (mem_inv_raw_reachable).  Only the memory fact changes along the
 * pipeline:
 *
 *   raw_mem_ok              below the alloca frontier; S3's output
 *                           (raw_unit_memory_ok is mem_inv raw_mem_ok)
 *   static_mem_ok eom       below a static layout end; after ConcretizeMemLoc
 *   lowered_mem_ok eom fmp  static, or at or above the initial free-memory
 *                           pointer; after FmpLowering, what codegen consumes
 *
 * A pass transports mem_inv through a simulation of the raw-reachable
 * states (mem_inv_transport); a pass that leaves memory alone keeps M.
 * Codegen gets codegen_memory_obligations from lowered_mem_ok, the spill
 * regions inside the gap [eom, fmp), and the step write footprint
 * (mem_inv_codegen_obligations).
 *
 * TOP-LEVEL:
 *   inst_mem_ranges, mem_inv, raw_mem_ok, static_mem_ok, lowered_mem_ok,
 *   step_write_footprint                   - definitions
 *   raw_unit_memory_ok_mem_inv              - S3's statement is the raw phase
 *   mem_inv_raw_reachable                   - the witness is raw_reachable
 *   mem_inv_mono, static_mem_ok_lowered
 *   mem_inv_transport                       - transport along a simulation
 *   mem_inv_codegen_obligations             - what codegen consumes
 *)

Theory unitMemInv
Ancestors
  list pair words finite_map venomInst venomState venomMemDefs
  venomExecSemantics contextCodegenRel contextCodegenRelProps
  contextRawReachable unitTransformDefs stackPlanTypes

(* ===== Definitions ===== *)

Definition inst_mem_ranges_def:
  inst_mem_ranges inst s =
    source_memory_read_ranges inst s ++ source_memory_write_ranges inst s
End

(* The shared invariant: some packaged reachability invariant, every state
   of which satisfies the phase's memory fact M. *)
Definition mem_inv_def:
  mem_inv M ctx vs <=>
    ?Inv. codegen_reachability_package Inv ctx vs /\
          !fn inst s. Inv ctx fn inst s ==> M ctx fn inst s
End

(* Raw phase: the frontier fits a word and every access is below it, or
   part of a revert forwarding (inst_mem_ok_in_fn). *)
Definition raw_mem_ok_def:
  raw_mem_ok (ctx:venom_context) (fn:ir_function) inst s <=>
    s.vs_alloca_next < dimword (:256) /\ inst_mem_ok_in_fn fn inst s
End

(* Static phase: every access is below the static layout end, or part of
   a revert forwarding. *)
Definition static_mem_ok_def:
  static_mem_ok eom (ctx:venom_context) (fn:ir_function) inst s <=>
    in_revert_forward fn s \/
    EVERY (\(off,len). len = 0 \/ off + len <= eom) (inst_mem_ranges inst s)
End

(* Lowered phase: every access is static or dynamic, never in [eom, fmp),
   or part of a revert forwarding. *)
Definition lowered_mem_ok_def:
  lowered_mem_ok eom fmp (ctx:venom_context) (fn:ir_function) inst s <=>
    in_revert_forward fn s \/
    EVERY (\(off,len). len = 0 \/ off + len <= eom \/ fmp <= off)
      (inst_mem_ranges inst s)
End

(* A step from a reachable state outside a revert forwarding changes a
   byte only inside a write range of a reachable instruction outside one:
   its own, or for INVOKE one the callee runs (a callee that forwards a
   revert reverts, so the INVOKE does not step OK). *)
Definition step_write_footprint_def:
  step_write_footprint ctx vs <=>
    !fn inst s s' fuel i.
      raw_reachable vs ctx fn inst s /\ ~in_revert_forward fn s /\
      step_inst fuel ctx inst s = OK s' /\
      read_byte i s.vs_memory <> read_byte i s'.vs_memory ==>
      ?fn2 inst2 s2 off len.
        raw_reachable vs ctx fn2 inst2 s2 /\ ~in_revert_forward fn2 s2 /\
        MEM (off,len) (source_memory_write_ranges inst2 s2) /\
        off <= i /\ i < off + len
End

(* ===== The raw phase is S3's statement ===== *)

Theorem raw_unit_memory_ok_mem_inv:
  raw_unit_memory_ok ctx vs <=> mem_inv raw_mem_ok ctx vs
Proof
  simp[raw_unit_memory_ok_def, mem_inv_def, raw_mem_ok_def]
QED

(* ===== The witness is raw_reachable ===== *)

Theorem mem_inv_raw_reachable:
  mem_inv M ctx vs <=>
    (?name fn lbl.
       ctx.ctx_entry = SOME name /\
       lookup_function name ctx.ctx_functions = SOME fn /\
       fn_entry_label fn = SOME lbl) /\
    !fn inst s. raw_reachable vs ctx fn inst s ==> M ctx fn inst s
Proof
  rw[mem_inv_def] >> eq_tac >> rw[]
  >- (fs[codegen_reachability_package_def] >> metis_tac[])
  >- metis_tac[raw_reachable_least]
  >> qexists_tac `raw_reachable vs` >> simp[] >>
  metis_tac[raw_reachable_package]
QED

Theorem mem_inv_mono:
  (!fn inst s. M ctx fn inst s ==> M' ctx fn inst s) /\ mem_inv M ctx vs ==>
  mem_inv M' ctx vs
Proof
  rw[mem_inv_def] >> metis_tac[]
QED

Theorem static_mem_ok_lowered:
  static_mem_ok eom ctx fn inst s ==> lowered_mem_ok eom fmp ctx fn inst s
Proof
  rw[static_mem_ok_def, lowered_mem_ok_def, EVERY_MEM, FORALL_PROD] >>
  metis_tac[]
QED

(* ===== Transport along a simulation of reachable states ===== *)

(* R relates each raw-reachable state of the output context to a
   raw-reachable state of the input context, and carries the memory fact
   across.  Both runs start from the same initial state. *)
Theorem mem_inv_transport:
  (?name fn lbl.
     ctx'.ctx_entry = SOME name /\
     lookup_function name ctx'.ctx_functions = SOME fn /\
     fn_entry_label fn = SOME lbl) /\
  (!fn' inst' s'.
     raw_reachable vs ctx' fn' inst' s' ==>
     ?fn inst s. raw_reachable vs ctx fn inst s /\ R fn inst s fn' inst' s') /\
  (!fn inst s fn' inst' s'.
     R fn inst s fn' inst' s' /\ M ctx fn inst s ==> M' ctx' fn' inst' s') /\
  mem_inv M ctx vs ==>
  mem_inv M' ctx' vs
Proof
  rw[mem_inv_raw_reachable] >> metis_tac[]
QED

(* ===== What codegen consumes ===== *)

Theorem lowered_mem_ok_range[local]:
  lowered_mem_ok eom fmp ctx fn inst s /\ ~in_revert_forward fn s /\
  MEM (off,len) (inst_mem_ranges inst s) ==>
  len = 0 \/ off + len <= eom \/ fmp <= off
Proof
  rw[lowered_mem_ok_def, EVERY_MEM] >> res_tac >> fs[]
QED

Theorem lowered_reads_disjoint[local]:
  lowered_mem_ok eom fmp ctx fn inst s /\ ~in_revert_forward fn s /\
  (!r. MEM r cp.cp_regions ==> eom <= r.sr_spill_base /\ r.sr_spill_end <= fmp) ==>
  source_memory_reads_disjoint cp inst s
Proof
  rw[source_memory_reads_disjoint_def, source_memory_read_byte_def,
     context_spill_byte_def] >>
  CCONTR_TAC >> fs[] >>
  rename1 `byte_in_memory_range rng i` >> PairCases_on `rng` >>
  fs[byte_in_memory_range_def] >>
  `MEM (rng0,rng1) (inst_mem_ranges inst s)` by simp[inst_mem_ranges_def] >>
  drule_all lowered_mem_ok_range >> res_tac >> decide_tac
QED

Theorem lowered_writes_disjoint[local]:
  lowered_mem_ok eom fmp ctx fn inst s /\ ~in_revert_forward fn s /\
  (!r. MEM r cp.cp_regions ==> eom <= r.sr_spill_base /\ r.sr_spill_end <= fmp) ==>
  context_source_memory_writes_disjoint cp inst s
Proof
  rw[context_source_memory_writes_disjoint_def, EVERY_MEM, FORALL_PROD] >>
  rename1 `MEM (off,len) (source_memory_write_ranges inst s)` >>
  `MEM (off,len) (inst_mem_ranges inst s)` by simp[inst_mem_ranges_def] >>
  drule_all lowered_mem_ok_range >> strip_tac >> simp[] >>
  disj2_tac >> rpt strip_tac >> res_tac >> decide_tac
QED

Theorem lowered_spill_step_safe[local]:
  step_write_footprint ctx vs /\
  (!fn inst s. raw_reachable vs ctx fn inst s ==>
               lowered_mem_ok eom fmp ctx fn inst s) /\
  (!r. MEM r cp.cp_regions ==> eom <= r.sr_spill_base /\ r.sr_spill_end <= fmp) /\
  raw_reachable vs ctx fn inst s /\ ~in_revert_forward fn s /\
  step_inst fuel ctx inst s = OK s' ==>
  context_spill_step_safe cp s s'
Proof
  rw[context_spill_step_safe_def, context_spill_byte_def] >>
  CCONTR_TAC >>
  fs[step_write_footprint_def] >>
  first_x_assum (qspecl_then [`fn`,`inst`,`s`,`s'`,`fuel`,`i`] mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >>
  `MEM (off,len) (inst_mem_ranges inst2 s2)` by simp[inst_mem_ranges_def] >>
  `lowered_mem_ok eom fmp ctx fn2 inst2 s2` by res_tac >>
  drule_all lowered_mem_ok_range >> res_tac >> decide_tac
QED

(* TOP-LEVEL: the lowered phase, spill regions inside the gap [eom, fmp)
   and the step write footprint give codegen its two memory premises, with
   raw_reachable vs as the invariant. *)
Theorem mem_inv_codegen_obligations:
  mem_inv (lowered_mem_ok eom fmp) ctx vs /\
  (!r. MEM r cp.cp_regions ==> eom <= r.sr_spill_base /\ r.sr_spill_end <= fmp) /\
  step_write_footprint ctx vs ==>
  codegen_reachability_package (raw_reachable vs) ctx vs /\
  codegen_memory_obligations (raw_reachable vs) ctx cp
Proof
  strip_tac >>
  `(?name fn lbl.
      ctx.ctx_entry = SOME name /\
      lookup_function name ctx.ctx_functions = SOME fn /\
      fn_entry_label fn = SOME lbl) /\
   !fn inst s. raw_reachable vs ctx fn inst s ==>
               lowered_mem_ok eom fmp ctx fn inst s`
    by fs[mem_inv_raw_reachable] >>
  conj_tac >- metis_tac[raw_reachable_package] >>
  rw[codegen_memory_obligations_def] >>
  metis_tac[lowered_reads_disjoint, lowered_writes_disjoint,
            lowered_spill_step_safe]
QED
