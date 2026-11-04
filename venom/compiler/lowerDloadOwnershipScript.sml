(* Source ownership audit; annotation definitions are deliberately deferred.

   CONTRACT SCOPE (o1PassContractScript.sml:529-535): o1_src_inv explicitly
   excludes ctx_has_dalloca and requires fmp_free_ctx. Consequently looped
   DALLOCA, dynamic/static overlap and dynamic return-FMP adoption are NOT
   reachable branches for this frozen task. The more general local DALLOCA
   interfaces in lowerDloadLifetime remain valid, but must not drive the
   required source producer's design.

   frame_reachable transition table (ptrDisciplineScript.sml:445-500):
   init: PG=[], G=FEMPTY, tn=entry_taint; entry PHIs have no inherited G.
         Initial allocation map is empty by o1_initial_state_ok. Create no
         owners; retain the initial natural allocation frontier.
   next: retains stack/PG; computes step_prov PG G inst s'. ALLOCA creates
         an event owner exactly on a missing ID; a repeated ID reuses the
         active-frame selection and saved (base,size), ignoring new size.
         PARAM copies inherited indexed selection. ADD/SUB/ASSIGN select
         first pointer operand; other outputs lose provenance. Counter
         increases only for fresh allocation; never restore it on return.
   block: uses entry_prov fn s' G (pre-entry G), NOT step_prov. PHIs read
          old G in parallel (phis_prov reads phi_prov prev G inst while its
          recursive result is only the update destination). Their source
          selection maps must likewise be frozen before entry updates.
   call: saves caller PG/G/state/t_var. Child PG=MAP(op_prov G) actual ops;
         child G=FEMPTY even though enters_block has executed value PHIs.
         Retain caller owner entries; child static-ID selection map is
         empty, regardless of caller IDs. setup_callee inherits frontier
         and memory. No numeric search recovers an inherited owner.
   ret: restores saved PG and DRESTRICT saved G, deleting INVOKE outputs;
        it does NOT copy child provenance or return-value owners. Discard
        child-private selections, preserve caller/inherited selections and
        global event serial. bind_outputs changes values only. merge keeps
        child memory but restores caller allocation map/frontier. An IntRet
        FMP adoption affects only vs_fmp (adopt_return_fmp_allocas).

   Geometry obligations still to prove, not premises for annotation:
   - Each active/suspended frame's static site ends <= its saved frontier.
   - Each child starts at the caller frontier. Positive child sites are
     >= that frontier, while all retained caller sites end <= it.
   - Fresh static site is [next,next+w2n size); repeated site adds nothing.
     The fresh owner's base is next. Need monotone frame frontier and
     preservation for all nonallocating step_inst_base cases.
   - Return restores the saved frontier, so expired child intervals may
     overlap the next call. No return-value provenance survives this rule.
   - Positive interval uniqueness is only for surviving selections, not
     historical E entries. Zero-size selections may share all numeric data.
   - lo <= base comes from ptr_discipline's allocas_from for current frame;
     suspended-frame versions require carrying the fact from call time.

   Existing checked interfaces:
   lowerDloadReachability.ld_frame_reachable_raw:
     o1_ctx_shape C /\ frame_reachable vs C stk PG G tn fn inst s ==>
     raw_reachable vs C fn inst s.
   unitMemInv.mem_inv_raw_reachable: entry existence /\ per-raw-state fact.
   raw_mem_ok: vs_alloca_next < dimword(:256) /\ inst_mem_ok_in_fn.
   lowerDloadStackBound.ld_stack_dload_count_bound supplies stack scratch
     count capacity, NOT allocation interval geometry.
   lowerDloadAllocation.ld_alloc_account_frontier:
     account keys d0 A s t ==> t.next = s.next+d0+32*CARD A.
   lowerDloadLifetime.ld_alloca_successive_calls checks exact repeated-call
     ID/range reuse, inherited memory and fresh new_site_bytes coverage.

   Missing interfaces: source reachable static-site frontier preservation
   (including saved caller environments), nonallocating-step projections,
   annotation erasure/reconstruction and live-owner disjointness. Raw
   frontier no-wrap at an instruction does not by itself bound the final
   ALLOCA result if there is no successor observation; the induction must
   distinguish natural geometry from word-observable endpoint bounds.
   No dynamic no-wrap theorem is needed for this contract.
*)
Theory lowerDloadOwnership
Ancestors
  lowerDloadLifetime lowerDloadReachability o1PassContract
  ctxLookupAgreeHelpers unitMemInv contextCodegenRelProps list
  o1PassLift ptrDiscipline

Theorem ld_source_frame_raw_bound:
  o1_src_inv D C vs /\ o1_ctx_shape C /\
  frame_reachable vs C stk PG G tn fn inst s ==>
  s.vs_alloca_next < dimword (:256)
Proof
  strip_tac >> drule_all ld_frame_reachable_raw >>
  qpat_x_assum `o1_src_inv D C vs` mp_tac >>
  simp[o1_src_inv_def, mem_inv_raw_reachable] >> rpt strip_tac >>
  qpat_x_assum `!f i t. raw_reachable vs C f i t ==> raw_mem_ok C f i t`
    (drule_then mp_tac) >> simp[raw_mem_ok_def]
QED

Theorem ld_source_frame_no_dalloca:
  o1_src_inv D C vs /\ o1_ctx_shape C /\
  frame_reachable vs C stk PG G tn fn inst s ==>
  inst.inst_opcode <> DALLOCA
Proof
  strip_tac >> drule_all ld_frame_reachable_prefix >> strip_tac >>
  `MEM fn C.ctx_functions` by metis_tac[ld_stack_origin_member] >>
  `active_inst fn inst s` by metis_tac[frame_reach_active] >>
  `EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)` by
    (qpat_x_assum `o1_src_inv D C vs` mp_tac >>
     simp[o1_src_inv_def, ctx_has_dalloca_def, EXISTS_MEM, EVERY_MEM] >>
     metis_tac[]) >>
  drule_all EVERY_active_inst >> simp[]
QED
