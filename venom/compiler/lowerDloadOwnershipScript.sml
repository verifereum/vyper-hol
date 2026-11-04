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
  o1PassLift ptrDiscipline venomMemProps venomExecProofs
  venomExecSemantics venomState finite_map contextCodegenRel
  calleeTransport venomInstProofs1

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

(* Natural endpoint geometry: no word no-wrap premise is needed. *)
Theorem ld_exec_alloca_static_endpoints:
  exec_alloca i s w = OK s' /\
  (!id b n. FLOOKUP s.vs_allocas id = SOME (b,n) ==>
     b+n <= s.vs_alloca_next) ==>
  (!id b n. FLOOKUP s'.vs_allocas id = SOME (b,n) ==>
     b+n <= s'.vs_alloca_next)
Proof
  simp[exec_alloca_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[FLOOKUP_UPDATE, AllCaseEqs()] >>
  first_x_assum drule >> simp[]
QED

Theorem ld_step_nonallocation_fields:
  step_inst fuel C i s = OK s' /\
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> ALLOCA ==>
  s'.vs_allocas = s.vs_allocas /\
  s'.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `step_inst_base i s = OK s'` by gvs[step_inst_non_invoke] >>
  metis_tac[venomMemPropsTheory.step_inst_base_preserves_allocas,
            step_inst_base_preserves_alloca_next]
QED

Theorem ld_enters_block_allocation_fields:
  enters_block fn s s' ==>
  s'.vs_allocas = s.vs_allocas /\
  s'.vs_alloca_next = s.vs_alloca_next
Proof
  rw[enters_block_def] >>
  drule eval_phis_preserves_alloca_fields >> simp[]
QED

Theorem ld_bind_outputs_allocas:
  bind_outputs outs vals s = SOME s' ==> s'.vs_allocas = s.vs_allocas
Proof
  strip_tac >> irule bind_outputs_preserves >>
  simp[update_var_def] >> metis_tac[]
QED

(* Remaining projection interfaces are already exported; do not duplicate:
   - venomMemProps.exec_alloca_alloca_next_mono: natural monotonicity.
   - o1ContractLowerDloadTaint.exec_alloca_fresh_projections and
     exec_alloca_repeated_projections: fresh/repeated exact effects.
   - o1ContractLowerDloadTaint.setup_callee_allocas: empty child map.
   - calleeTransport.setup_callee_shared_fields: inherited frontier.
   - calleeTransport.merge_callee_local_fields: restored caller map/frontier.
   - venomExecSemantics.adopt_return_fmp_allocas: map/frontier unchanged.
   - calleeTransport.bind_outputs_shared_fields: frontier unchanged;
     ld_bind_outputs_allocas above supplies the missing map projection.
   The nonallocation boundary above is stronger than the requested static
   source interface: DALLOCA changes FMP, not the static allocation fields.
*)

(* Annotated static provenance. The owner is selected, never recovered by
   comparing numeric sites. PHIs always read the unchanged input map. *)
Definition ld_erase_def:
  ld_erase (AG:('a, (num # num) # (num # num)) fmap) = SND o_f AG
End

Definition ld_op_prov_def:
  ld_op_prov (AG:(string, (num # num) # (num # num)) fmap) op =
    case op of Var u => FLOOKUP AG u | _ => NONE
End

Definition ld_first_prov_def:
  ld_first_prov AG [] = NONE /\
  ld_first_prov AG (op::ops) =
    case ld_op_prov AG op of
      SOME site => SOME site
    | NONE => ld_first_prov AG ops
End

Definition ld_set_prov_def:
  ld_set_prov (AG:(string, (num # num) # (num # num)) fmap) outs p =
    case (outs,p) of
      ([out], SOME site) => AG |+ (out,site)
    | _ => DRESTRICT AG (COMPL (set outs))
End

Definition ld_out_prov_def:
  ld_out_prov AP AG (L:(num, (num # num) # (num # num)) fmap) inst =
    if inst.inst_opcode = ALLOCA then FLOOKUP L inst.inst_id
    else if inst.inst_opcode = PARAM then
      (case inst.inst_operands of
         [Lit idx] => if w2n idx < LENGTH AP then EL (w2n idx) AP else NONE
       | _ => NONE)
    else if inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/
            inst.inst_opcode = ASSIGN
    then ld_first_prov AG inst.inst_operands
    else NONE
End

Definition ld_step_prov_def:
  ld_step_prov AP AG L inst =
    ld_set_prov AG inst.inst_outputs (ld_out_prov AP AG L inst)
End

Definition ld_phi_prov_def:
  ld_phi_prov prev AG inst =
    case prev of
      NONE => NONE
    | SOME lbl =>
        case resolve_phi lbl inst.inst_operands of
          SOME op => ld_op_prov AG op
        | NONE => NONE
End

Definition ld_phis_prov_def:
  ld_phis_prov prev AG [] = AG /\
  ld_phis_prov prev AG (inst::rest) =
    if inst.inst_opcode <> PHI then AG
    else ld_set_prov (ld_phis_prov prev AG rest) inst.inst_outputs
                     (ld_phi_prov prev AG inst)
End

Definition ld_entry_prov_def:
  ld_entry_prov fn s AG =
    case lookup_block s.vs_current_bb fn.fn_blocks of
      SOME bb => ld_phis_prov s.vs_prev_bb AG bb.bb_instructions
    | NONE => AG
End

Theorem ld_erase_lookup[simp]:
  FLOOKUP (ld_erase AG) x = OPTION_MAP SND (FLOOKUP AG x)
Proof
  Cases_on `FLOOKUP AG x` >> simp[ld_erase_def, FLOOKUP_o_f]
QED

Theorem ld_erase_op_prov:
  OPTION_MAP SND (ld_op_prov AG op) = op_prov (ld_erase AG) op
Proof
  Cases_on `op` >> simp[ld_op_prov_def, op_prov_def]
QED

Theorem ld_erase_first_prov:
  !ops. OPTION_MAP SND (ld_first_prov AG ops) =
        first_prov (ld_erase AG) ops
Proof
  Induct >> simp[ld_first_prov_def, first_prov_def,
                 GSYM ld_erase_op_prov] >>
  Cases_on `ld_op_prov AG h` >> simp[]
QED

Theorem ld_erase_restrict:
  ld_erase (DRESTRICT AG keys) = DRESTRICT (ld_erase AG) keys
Proof
  simp[fmap_eq_flookup, FUN_EQ_THM, FLOOKUP_DRESTRICT] >>
  gen_tac >> Cases_on `x IN keys` >> simp[]
QED

Theorem ld_erase_update:
  ld_erase (AG |+ (x,site)) = ld_erase AG |+ (x,SND site)
Proof
  simp[ld_erase_def, o_f_FUPDATE]
QED

Theorem ld_erase_set_prov:
  ld_erase (ld_set_prov AG outs p) =
  set_prov (ld_erase AG) outs (OPTION_MAP SND p)
Proof
  simp[ld_set_prov_def, set_prov_def] >>
  Cases_on `outs` >- simp[ld_erase_restrict] >>
  Cases_on `t` >> Cases_on `p` >>
  simp[ld_erase_update, ld_erase_restrict]
QED

Theorem ld_erase_out_prov:
  i.inst_opcode <> DALLOCA /\ ld_erase L = s.vs_allocas ==>
  OPTION_MAP SND (ld_out_prov AP AG L i) =
  out_prov (MAP (OPTION_MAP SND) AP) (ld_erase AG) i s
Proof
  strip_tac >> Cases_on `i.inst_opcode = ALLOCA`
  >- (simp[ld_out_prov_def, out_prov_def] >>
      qpat_x_assum `ld_erase L = _` (fn th => rewrite_tac[GSYM th]) >>
      simp[]) >>
  Cases_on `i.inst_opcode = PARAM`
  >- (simp[ld_out_prov_def, out_prov_def] >>
      Cases_on `i.inst_operands` >- simp[] >>
      Cases_on `t` >> simp[] >> Cases_on `h` >> simp[] >>
      rename1 `Lit idx` >> Cases_on `w2n idx < LENGTH AP` >> simp[EL_MAP]) >>
  simp[ld_out_prov_def, out_prov_def, ld_erase_first_prov] >>
  Cases_on `i.inst_opcode = ADD \/ i.inst_opcode = SUB \/
            i.inst_opcode = ASSIGN` >> simp[ld_erase_first_prov]
QED

Theorem ld_erase_step_prov:
  i.inst_opcode <> DALLOCA /\ ld_erase L = s.vs_allocas ==>
  ld_erase (ld_step_prov AP AG L i) =
  step_prov (MAP (OPTION_MAP SND) AP) (ld_erase AG) i s
Proof
  strip_tac >> drule_all ld_erase_out_prov >>
  simp[ld_step_prov_def, step_prov_def, ld_erase_set_prov]
QED

Theorem ld_erase_phi_prov:
  OPTION_MAP SND (ld_phi_prov prev AG i) =
  phi_prov prev (ld_erase AG) i
Proof
  Cases_on `prev` >> simp[ld_phi_prov_def, phi_prov_def] >>
  Cases_on `resolve_phi x i.inst_operands` >> simp[ld_erase_op_prov]
QED

Theorem ld_erase_phis_prov:
  !is. ld_erase (ld_phis_prov prev AG is) =
       phis_prov prev (ld_erase AG) is
Proof
  Induct >> simp[ld_phis_prov_def, phis_prov_def,
                 ld_erase_set_prov, ld_erase_phi_prov] >>
  Cases_on `h.inst_opcode = PHI` >> simp[ld_erase_set_prov,
                                        ld_erase_phi_prov]
QED

Theorem ld_erase_entry_prov:
  ld_erase (ld_entry_prov fn s AG) = entry_prov fn s (ld_erase AG)
Proof
  simp[ld_entry_prov_def, entry_prov_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  simp[ld_erase_phis_prov]
QED

Theorem ld_op_prov_selected:
  ld_op_prov AG op = SOME site ==> ?v. FLOOKUP AG v = SOME site
Proof
  Cases_on `op` >> simp[ld_op_prov_def] >> metis_tac[]
QED

Theorem ld_phi_prov_selected:
  ld_phi_prov prev AG i = SOME site ==> ?v. FLOOKUP AG v = SOME site
Proof
  Cases_on `prev` >> simp[ld_phi_prov_def] >>
  Cases_on `resolve_phi x i.inst_operands` >> simp[] >>
  metis_tac[ld_op_prov_selected]
QED

Theorem ld_set_prov_selected:
  FLOOKUP (ld_set_prov AG outs p) v = SOME site ==>
  FLOOKUP AG v = SOME site \/ p = SOME site
Proof
  Cases_on `outs` >- simp[ld_set_prov_def, FLOOKUP_DRESTRICT] >>
  Cases_on `t` >> Cases_on `p` >>
  simp[ld_set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem ld_phis_prov_selected:
  !is v site. FLOOKUP (ld_phis_prov prev AG is) v = SOME site ==>
    ?u. FLOOKUP AG u = SOME site
Proof
  Induct >- (simp[ld_phis_prov_def] >> metis_tac[]) >>
  rpt gen_tac >> Cases_on `h.inst_opcode = PHI`
  >- (simp[ld_phis_prov_def] >> strip_tac >>
      drule ld_set_prov_selected >> strip_tac
      >- metis_tac[] >>
      metis_tac[ld_phi_prov_selected]) >>
  simp[ld_phis_prov_def] >> metis_tac[]
QED

Theorem ld_entry_prov_selected:
  FLOOKUP (ld_entry_prov fn s AG) v = SOME site ==>
  ?u. FLOOKUP AG u = SOME site
Proof
  simp[ld_entry_prov_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  simp[] >> metis_tac[ld_phis_prov_selected]
QED

Theorem ld_param_prov_selected:
  i.inst_opcode = PARAM /\ i.inst_operands = [Lit idx] ==>
  ld_out_prov AP AG L i =
    if w2n idx < LENGTH AP then EL (w2n idx) AP else NONE
Proof
  simp[ld_out_prov_def]
QED

(* A swap is the adversarial parallel-PHI test: the second source must
   not see the first output update. Distinct output names select the two
   old sites even when their source names are each other's destinations. *)
Theorem ld_two_phis_parallel:
  i.inst_opcode = PHI /\ j.inst_opcode = PHI /\
  i.inst_outputs = [x] /\ j.inst_outputs = [y] /\ x <> y /\
  ld_phi_prov prev AG i = SOME a /\ ld_phi_prov prev AG j = SOME b ==>
  FLOOKUP (ld_phis_prov prev AG [i;j]) x = SOME a /\
  FLOOKUP (ld_phis_prov prev AG [i;j]) y = SOME b
Proof
  simp[ld_phis_prov_def, ld_set_prov_def, FLOOKUP_UPDATE]
QED
