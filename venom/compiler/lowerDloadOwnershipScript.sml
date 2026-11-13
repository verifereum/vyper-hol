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

(* One event selection per fresh static ID of this active frame. *)
Definition ld_select_alloca_def:
  ld_select_alloca k (L:(num, (num # num) # (num # num)) fmap) i s =
    if i.inst_opcode = ALLOCA /\ FLOOKUP L i.inst_id = NONE then
      case FLOOKUP s.vs_allocas i.inst_id of
        SOME site => (SUC k, L |+ (i.inst_id,((0,k),site)))
      | NONE => (k,L)
    else (k,L)
End

Datatype:
  ld_saved_frame = <|
    lf_fn : ir_function;
    lf_inst : instruction;
    lf_state : venom_state;
    lf_params : ((num # num) # (num # num)) option list;
    lf_prov : (string, (num # num) # (num # num)) fmap;
    lf_tvar : (string, num set) fmap;
    lf_local : (num, (num # num) # (num # num)) fmap |>
End

Definition ld_erase_frame_def:
  ld_erase_frame f =
    <| cf_fn := f.lf_fn; cf_inst := f.lf_inst; cf_state := f.lf_state;
       cf_params := MAP (OPTION_MAP SND) f.lf_params;
       cf_prov := ld_erase f.lf_prov; cf_tvar := f.lf_tvar |>
End

Inductive ld_annotated_reachable:
[~entry:]
  (!vs0 ctx name fn lbl inst s1.
     ctx.ctx_entry = SOME name /\
     lookup_function name ctx.ctx_functions = SOME fn /\
     fn_entry_label fn = SOME lbl /\
     enters_block fn
       (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                    vs_inst_idx := 0 |>) s1 /\
     s1.vs_allocas = FEMPTY /\ active_inst fn inst s1 ==>
     ld_annotated_reachable vs0 ctx [] 0 FEMPTY [] FEMPTY
       entry_taint fn inst s1)
[~next:]
  (!vs0 ctx astk k L AP AG tn fn inst inst' s s' fuel k' L'.
     ld_annotated_reachable vs0 ctx astk k L AP AG tn fn inst s /\
     active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
     inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> DALLOCA /\
     step_inst fuel ctx inst s = OK s' /\
     ld_select_alloca k L inst s' = (k',L') /\
     ld_erase L' = s'.vs_allocas /\
     active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
     ld_annotated_reachable vs0 ctx astk k' L' AP
       (ld_step_prov AP AG L' inst) (step_taint inst s s' tn) fn inst'
       (s' with vs_inst_idx := SUC s.vs_inst_idx))
[~block:]
  (!vs0 ctx astk k L AP AG tn fn inst inst' s s' s1 fuel.
     ld_annotated_reachable vs0 ctx astk k L AP AG tn fn inst s /\
     active_inst fn inst s /\ is_terminator inst.inst_opcode /\
     step_inst fuel ctx inst s = OK s' /\ ~s'.vs_halted /\
     enters_block fn s' s1 /\ active_inst fn inst' s1 ==>
     ld_annotated_reachable vs0 ctx astk k L AP (ld_entry_prov fn s' AG)
       (entry_taint_vars fn s' tn) fn inst' s1)
[~call:]
  (!vs0 ctx astk k L AP AG tn caller inv s nm ops callee args cs s1 inst.
     ld_annotated_reachable vs0 ctx astk k L AP AG tn caller inv s /\
     active_inst caller inv s /\ inv.inst_opcode = INVOKE /\
     decode_invoke inv = SOME (nm,ops) /\
     lookup_function nm ctx.ctx_functions = SOME callee /\
     eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
     enters_block callee cs s1 /\ active_inst callee inst s1 ==>
     ld_annotated_reachable vs0 ctx
       (<| lf_fn := caller; lf_inst := inv; lf_state := s;
           lf_params := AP; lf_prov := AG; lf_tvar := tn.t_var;
           lf_local := L |> :: astk)
       k FEMPTY (MAP (ld_op_prov AG) ops) FEMPTY
       (tn with t_var := FEMPTY) callee inst s1)
[~ret:]
  (!vs0 ctx f astk k L AP AG tn fn rinst s ret s_end s' inst' fuel.
     ld_annotated_reachable vs0 ctx (f::astk) k L AP AG tn fn rinst s /\
     active_inst fn rinst s /\
     step_inst fuel ctx rinst s = IntRet ret s_end /\
     bind_outputs f.lf_inst.inst_outputs ret.iret_values
       (adopt_return_fmp ret (merge_callee_state f.lf_state s_end)) = SOME s' /\
     active_inst f.lf_fn inst'
       (s' with vs_inst_idx := SUC f.lf_state.vs_inst_idx) ==>
     ld_annotated_reachable vs0 ctx astk k f.lf_local f.lf_params
       (DRESTRICT f.lf_prov (COMPL (set f.lf_inst.inst_outputs)))
       (tn with t_var := DRESTRICT f.lf_tvar (COMPL (set f.lf_inst.inst_outputs)))
       f.lf_fn inst' (s' with vs_inst_idx := SUC f.lf_state.vs_inst_idx))
End

Theorem ld_annotated_erasure:
  !vs0 ctx astk k L AP AG tn fn inst s.
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn inst s ==>
  frame_reachable vs0 ctx (MAP ld_erase_frame astk)
    (MAP (OPTION_MAP SND) AP) (ld_erase AG) tn fn inst s
Proof
  ho_match_mp_tac ld_annotated_reachable_ind >> rpt conj_tac
  >- suspend "entry"
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume ld_annotated_erasure[entry]:
  rpt strip_tac >> simp[ld_erase_def, o_f_FEMPTY] >>
  irule frame_reachable_entry >> metis_tac[]
QED

Resume ld_annotated_erasure[next]:
  rpt strip_tac >>
  drule_all ld_erase_step_prov >> disch_then (fn th => simp[th]) >>
  irule frame_reachable_next >> metis_tac[]
QED

Resume ld_annotated_erasure[block]:
  rpt strip_tac >> simp[ld_erase_entry_prov] >>
  irule frame_reachable_block >> metis_tac[]
QED

Resume ld_annotated_erasure[call]:
  rpt strip_tac >>
  simp[MAP_MAP_o, combinTheory.o_DEF, ld_erase_op_prov,
       ld_erase_frame_def, ETA_THM] >>
  `ld_erase (FEMPTY:(string, (num # num) # (num # num)) fmap) = FEMPTY`
    by simp[ld_erase_def, o_f_FEMPTY] >>
  asm_rewrite_tac[] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule frame_reachable_call >> metis_tac[]
QED

Resume ld_annotated_erasure[ret]:
  rpt strip_tac >> simp[ld_erase_restrict] >>
  qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[ld_erase_frame_def] >> strip_tac >>
  drule frame_reachable_ret >> simp[ld_erase_frame_def] >>
  disch_then irule >> metis_tac[]
QED

Finalise ld_annotated_erasure

Theorem ld_select_alloca_erase:
  ld_erase L = s.vs_allocas /\ i.inst_opcode <> INVOKE /\
  step_inst fuel C i s = OK s' ==>
  ld_erase (SND (ld_select_alloca k L i s')) = s'.vs_allocas
Proof
  strip_tac >>
  `FLOOKUP s.vs_allocas i.inst_id =
   OPTION_MAP SND (FLOOKUP L i.inst_id)` by metis_tac[ld_erase_lookup] >>
  Cases_on `i.inst_opcode = ALLOCA`
  >- (gvs[step_inst_non_invoke] >>
      qpat_x_assum `step_inst_base i s = _` mp_tac >>
      simp[step_inst_base_def] >>
      strip_tac >> gvs[AllCaseEqs()] >>
      qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
      simp[exec_alloca_def, AllCaseEqs(), update_var_def] >>
      rpt strip_tac >> gvs[] >>
      simp[ld_select_alloca_def, FLOOKUP_UPDATE] >>
      Cases_on `FLOOKUP L i.inst_id` >>
      gvs[ld_erase_lookup, ld_erase_update]) >>
  drule_all ld_step_nonallocation_fields >> strip_tac >>
  simp[ld_select_alloca_def]
QED

Theorem ld_annotated_local_maps:
  !vs0 ctx astk k L AP AG tn fn inst s.
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn inst s ==>
  ld_erase L = s.vs_allocas /\
  EVERY (\f. ld_erase f.lf_local = f.lf_state.vs_allocas) astk
Proof
  ho_match_mp_tac ld_annotated_reachable_ind >> rpt conj_tac
  >- (simp[ld_erase_def, o_f_FEMPTY])
  >- (rpt strip_tac >> simp[])
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume ld_annotated_local_maps[block]:
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> ALLOCA` by
    (rpt strip_tac >> gvs[venomInstTheory.is_terminator_def]) >>
  drule_all ld_step_nonallocation_fields >> strip_tac >>
  drule ld_enters_block_allocation_fields >> simp[]
QED

Resume ld_annotated_local_maps[call]:
  rpt strip_tac >> simp[] >>
  drule setup_callee_shared_fields >> strip_tac >>
  drule ld_enters_block_allocation_fields >> strip_tac >>
  qpat_x_assum `setup_callee _ _ _ = _` mp_tac >>
  simp[setup_callee_def] >> strip_tac >>
  gvs[ld_erase_def, o_f_FEMPTY]
QED

Resume ld_annotated_local_maps[ret]:
  rpt strip_tac >> gvs[] >>
  drule ld_bind_outputs_allocas >>
  simp[adopt_return_fmp_allocas, merge_callee_local_fields]
QED

Finalise ld_annotated_local_maps

Theorem ld_annotated_active_lookup:
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn inst s ==>
  FLOOKUP s.vs_allocas id = OPTION_MAP SND (FLOOKUP L id)
Proof
  strip_tac >> drule ld_annotated_local_maps >>
  strip_tac >> metis_tac[ld_erase_lookup]
QED

Theorem ld_annotated_saved_lookup:
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn inst s /\ MEM f astk ==>
  FLOOKUP f.lf_state.vs_allocas id =
    OPTION_MAP SND (FLOOKUP f.lf_local id)
Proof
  strip_tac >> drule ld_annotated_local_maps >>
  simp[EVERY_MEM] >> strip_tac >>
  first_x_assum drule >> strip_tac >> metis_tac[ld_erase_lookup]
QED

Theorem ld_source_annotation:
  !vs0 ctx stk PG G tn fn inst s.
  frame_reachable vs0 ctx stk PG G tn fn inst s ==>
  !D. o1_src_inv D ctx vs0 /\ o1_ctx_shape ctx /\ o1_run_state_ok vs0 ==>
  ?astk k L AP AG.
    ld_annotated_reachable vs0 ctx astk k L AP AG tn fn inst s /\
    MAP ld_erase_frame astk = stk /\ MAP (OPTION_MAP SND) AP = PG /\
    ld_erase AG = G
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- suspend "entry"
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume ld_source_annotation[entry]:
  rpt strip_tac >>
  qexistsl [`[]`, `0`, `FEMPTY`, `[]`, `FEMPTY`] >>
  simp[ld_erase_def, o_f_FEMPTY] >>
  irule ld_annotated_reachable_entry >>
  `vs0.vs_allocas = FEMPTY` by
    gvs[o1_run_state_ok_def, unitTransformDefsTheory.o1_initial_state_ok_def] >>
  drule ld_enters_block_allocation_fields >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Resume ld_source_annotation[next]:
  rpt strip_tac >>
  first_x_assum (drule_then strip_assume_tac) >> gvs[] >>
  drule ld_annotated_erasure >> strip_tac >>
  `inst.inst_opcode <> DALLOCA` by metis_tac[ld_source_frame_no_dalloca] >>
  drule ld_annotated_local_maps >> strip_tac >>
  drule_all ld_select_alloca_erase >>
  disch_then (qspec_then `k` assume_tac) >>
  Cases_on `ld_select_alloca k L inst s'` >> gvs[] >>
  qexistsl [`astk`, `q`, `r`, `AP`, `ld_step_prov AP AG r inst`] >>
  simp[] >> conj_tac
  >- (irule ld_annotated_reachable_next >> metis_tac[]) >>
  irule ld_erase_step_prov >> simp[]
QED

Resume ld_source_annotation[block]:
  rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >> gvs[] >>
  qexistsl [`astk`, `k`, `L`, `AP`, `ld_entry_prov fn s' AG`] >>
  simp[ld_erase_entry_prov] >>
  irule ld_annotated_reachable_block >> metis_tac[]
QED

Resume ld_source_annotation[call]:
  rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >> gvs[] >>
  qexistsl [`<| lf_fn := fn; lf_inst := inst; lf_state := s;
                lf_params := AP; lf_prov := AG; lf_tvar := tn.t_var;
                lf_local := L |> :: astk`,
             `k`, `FEMPTY`, `MAP (ld_op_prov AG) ops`, `FEMPTY`] >>
  simp[ld_erase_frame_def, ld_erase_def, o_f_FEMPTY,
       MAP_MAP_o, combinTheory.o_DEF, ld_erase_op_prov] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[] >>
  irule ld_annotated_reachable_call >> metis_tac[]
QED

Resume ld_source_annotation[ret]:
  rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >> gvs[] >>
  Cases_on `astk` >> gvs[ld_erase_frame_def] >>
  qexistsl [`t`, `k`, `h.lf_local`, `h.lf_params`,
    `DRESTRICT h.lf_prov (COMPL (set h.lf_inst.inst_outputs))`] >>
  simp[ld_erase_restrict] >>
  irule ld_annotated_reachable_ret >> metis_tac[]
QED

Finalise ld_source_annotation

(* Sites retained by one frame, and by the simultaneously live call stack.
   Numeric equality of sites is deliberately not used to select an owner. *)
Definition ld_selected_def:
  ld_selected (L:(num, (num # num) # (num # num)) fmap) AP
              (AG:(string, (num # num) # (num # num)) fmap) site <=>
    (?id. FLOOKUP L id = SOME site) \/
    MEM (SOME site) AP \/ (?v. FLOOKUP AG v = SOME site)
End

Definition ld_live_def:
  ld_live astk L AP AG site <=>
    ld_selected L AP AG site \/
    ?f. MEM f astk /\ ld_selected f.lf_local f.lf_params f.lf_prov site
End

Theorem ld_first_prov_selected:
  !ops. ld_first_prov AG ops = SOME site ==>
    ?v. FLOOKUP AG v = SOME site
Proof
  Induct >> simp[ld_first_prov_def, AllCaseEqs()] >>
  metis_tac[ld_op_prov_selected]
QED

Theorem ld_out_prov_selected:
  ld_out_prov AP AG L i = SOME site ==> ld_selected L AP AG site
Proof
  simp[ld_out_prov_def] >>
  Cases_on `i.inst_opcode = ALLOCA`
  >- (simp[ld_selected_def] >> metis_tac[]) >>
  Cases_on `i.inst_opcode = PARAM`
  >- (simp[AllCaseEqs()] >> rpt strip_tac >>
      simp[ld_selected_def] >> metis_tac[MEM_EL]) >>
  simp[] >> rpt strip_tac >> gvs[AllCaseEqs()] >>
  drule ld_first_prov_selected >> simp[ld_selected_def] >> metis_tac[]
QED

Theorem ld_step_selected:
  ld_selected L AP (ld_step_prov AP AG L i) site ==>
  ld_selected L AP AG site
Proof
  simp[ld_selected_def, ld_step_prov_def] >> rpt strip_tac
  >- metis_tac[]
  >- metis_tac[] >>
  drule ld_set_prov_selected >> strip_tac
  >- metis_tac[] >>
  drule ld_out_prov_selected >> simp[ld_selected_def]
QED

Theorem ld_entry_selected:
  ld_selected L AP (ld_entry_prov fn s AG) site ==>
  ld_selected L AP AG site
Proof
  simp[ld_selected_def] >> rpt strip_tac >>
  metis_tac[ld_entry_prov_selected]
QED

Theorem ld_call_selected:
  ld_selected FEMPTY (MAP (ld_op_prov AG) ops) FEMPTY site ==>
  ld_selected L AP AG site
Proof
  simp[ld_selected_def, MEM_MAP] >> rpt strip_tac >>
  metis_tac[ld_op_prov_selected]
QED

Theorem ld_restrict_selected:
  ld_selected L AP (DRESTRICT AG keys) site ==> ld_selected L AP AG site
Proof
  simp[ld_selected_def, FLOOKUP_DRESTRICT, AllCaseEqs()] >> metis_tac[]
QED

Theorem ld_select_alloca_lookup:
  ld_select_alloca k L i s = (k',L') ==>
  k <= k' /\
  (!id site. FLOOKUP L' id = SOME site ==>
     FLOOKUP L id = SOME site \/ (FST site = (0,k) /\ k < k'))
Proof
  simp[ld_select_alloca_def] >> rpt strip_tac >>
  gvs[AllCaseEqs(), FLOOKUP_UPDATE] >> rpt strip_tac >>
  gvs[AllCaseEqs()]
QED

Theorem ld_selected_serial_mono:
  (k:num) <= k' /\
  (!site. ld_selected (L:(num, (num # num) # (num # num)) fmap) AP
                     (AG:(string, (num # num) # (num # num)) fmap) site ==>
    FST (FST site) = (0:num) /\ SND (FST site) < k) /\
  (!id site. FLOOKUP L' id = SOME site ==>
    FLOOKUP L id = SOME site \/ (FST site = (0,k) /\ k < k')) ==>
  !site. ld_selected L' AP AG site ==>
    FST (FST site) = (0:num) /\ SND (FST site) < k'
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> disch_tac >>
  `ld_selected L AP AG site \/ (FST site = (0,k) /\ k < k')` by
    (gvs[ld_selected_def] >> metis_tac[]) >>
  pop_assum strip_assume_tac
  >- (first_x_assum (drule_then strip_assume_tac) >>
      qpat_x_assum `!id site. _` kall_tac >>
      conj_tac >- simp[] >>
      irule arithmeticTheory.LESS_LESS_EQ_TRANS >> qexists_tac `k` >> simp[]) >>
  simp[]
QED

Theorem ld_annotated_serial:
  !vs0 ctx astk k L AP AG tn fn inst s.
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn inst s ==>
  !site. ld_live astk L AP AG site ==>
    FST (FST site) = (0:num) /\ SND (FST site) < k
Proof
  ho_match_mp_tac ld_annotated_reachable_ind >> rpt conj_tac
  >- simp[ld_live_def, ld_selected_def]
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume ld_annotated_serial[next]:
  rpt gen_tac >> strip_tac >> gen_tac >> disch_tac >> drule ld_select_alloca_lookup >> strip_tac >>
  `!site. ld_selected L AP AG site ==>
     FST (FST site) = (0:num) /\ SND (FST site) < k` by
    metis_tac[ld_live_def] >>
  `!site. ld_selected L' AP AG site ==>
     FST (FST site) = (0:num) /\ SND (FST site) < k'` by
    (gen_tac >> disch_tac >> irule ld_selected_serial_mono >>
     goal_assum (drule_at Any) >> qexistsl [`L`, `k`] >> simp[]) >>
  qpat_x_assum `ld_live _ _ _ _ _` mp_tac >>
  simp[ld_live_def] >> strip_tac
  >- metis_tac[ld_step_selected] >>
  `FST (FST site) = (0:num) /\ SND (FST site) < k` by
    (qpat_x_assum `!site. ld_live _ _ _ _ site ==> _`
       (qspec_then `site` mp_tac) >>
     simp[ld_live_def] >> metis_tac[]) >>
  gvs[]
QED

Resume ld_annotated_serial[block]:
  rpt strip_tac >> metis_tac[ld_live_def, ld_entry_selected]
QED

Resume ld_annotated_serial[call]:
  rpt strip_tac >> gvs[ld_live_def] >>
  metis_tac[ld_call_selected]
QED

Resume ld_annotated_serial[ret]:
  rpt strip_tac >> gvs[ld_live_def] >>
  metis_tac[ld_restrict_selected]
QED

Finalise ld_annotated_serial

(* Bounds are natural endpoints, independent of the word no-wrap bound. *)
Definition ld_frame_bound_def:
  ld_frame_bound n (L:(num, (num # num) # (num # num)) fmap) AP
                   (AG:(string, (num # num) # (num # num)) fmap) <=>
    !site. ld_selected L AP AG site ==>
      FST (SND site) + SND (SND site) <= n
End

Definition ld_stack_bound_def:
  ld_stack_bound n [] = T /\
  ld_stack_bound n (f::astk) =
    (f.lf_state.vs_alloca_next <= n /\
     ld_frame_bound f.lf_state.vs_alloca_next f.lf_local f.lf_params f.lf_prov /\
     ld_stack_bound f.lf_state.vs_alloca_next astk)
End

Theorem ld_frame_bound_mono:
  ld_frame_bound n L AP AG /\ n <= m ==> ld_frame_bound m L AP AG
Proof
  simp[ld_frame_bound_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem ld_stack_bound_mono:
  !astk n m. ld_stack_bound n astk /\ n <= m ==> ld_stack_bound m astk
Proof
  Cases >> simp[ld_stack_bound_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem ld_frame_bound_step:
  ld_frame_bound n L AP AG ==> ld_frame_bound n L AP (ld_step_prov AP AG L i)
Proof
  simp[ld_frame_bound_def] >> metis_tac[ld_step_selected]
QED

Theorem ld_frame_bound_entry:
  ld_frame_bound n L AP AG ==> ld_frame_bound n L AP (ld_entry_prov fn s AG)
Proof
  simp[ld_frame_bound_def] >> metis_tac[ld_entry_selected]
QED

Theorem ld_frame_bound_call:
  ld_frame_bound n L AP AG ==>
  ld_frame_bound n FEMPTY (MAP (ld_op_prov AG) ops) FEMPTY
Proof
  simp[ld_frame_bound_def] >> metis_tac[ld_call_selected]
QED

Theorem ld_frame_bound_restrict:
  ld_frame_bound n L AP AG ==> ld_frame_bound n L AP (DRESTRICT AG keys)
Proof
  simp[ld_frame_bound_def] >> metis_tac[ld_restrict_selected]
QED

Theorem ld_select_alloca_endpoints:
  ld_erase L = s.vs_allocas /\ i.inst_opcode <> INVOKE /\
  step_inst fuel C i s = OK s' /\ ld_select_alloca k L i s' = (k',L') ==>
  s.vs_alloca_next <= s'.vs_alloca_next /\
  (!id site. FLOOKUP L' id = SOME site ==>
    FLOOKUP L id = SOME site \/
    (FST (SND site) = s.vs_alloca_next /\
     FST (SND site) + SND (SND site) = s'.vs_alloca_next))
Proof
  strip_tac >>
  `FLOOKUP s.vs_allocas i.inst_id =
   OPTION_MAP SND (FLOOKUP L i.inst_id)` by metis_tac[ld_erase_lookup] >>
  Cases_on `i.inst_opcode = ALLOCA`
  >- (gvs[step_inst_non_invoke] >>
      qpat_x_assum `step_inst_base i s = _` mp_tac >>
      simp[step_inst_base_def] >>
      strip_tac >> gvs[AllCaseEqs()] >>
      qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
      simp[exec_alloca_def, AllCaseEqs(), update_var_def] >>
      rpt strip_tac >> gvs[] >>
      Cases_on `FLOOKUP L i.inst_id` >>
      gvs[ld_select_alloca_def, FLOOKUP_UPDATE, AllCaseEqs()] >>
      rpt strip_tac >> gvs[AllCaseEqs()]) >>
  drule_all ld_step_nonallocation_fields >> strip_tac >>
  gvs[ld_select_alloca_def]
QED

Theorem ld_frame_bound_alloca:
  ld_erase L = s.vs_allocas /\ i.inst_opcode <> INVOKE /\
  step_inst fuel C i s = OK s' /\ ld_select_alloca k L i s' = (k',L') /\
  ld_frame_bound s.vs_alloca_next L AP AG ==>
  ld_frame_bound s'.vs_alloca_next L' AP AG
Proof
  strip_tac >> drule_all ld_select_alloca_endpoints >> strip_tac >>
  simp[ld_frame_bound_def] >> gen_tac >> disch_tac >>
  `ld_selected L AP AG site \/
   FST (SND site) + SND (SND site) = s'.vs_alloca_next` by
    (gvs[ld_selected_def] >> metis_tac[]) >>
  pop_assum strip_assume_tac >- (
    qpat_x_assum `ld_frame_bound _ _ _ _` mp_tac >>
    simp[ld_frame_bound_def] >>
    disch_then (qspec_then `site` mp_tac) >> simp[]) >>
  simp[]
QED

Theorem ld_annotated_bounds:
  !vs0 ctx astk k L AP AG tn fn inst s.
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn inst s ==>
  ld_frame_bound s.vs_alloca_next L AP AG /\ ld_stack_bound s.vs_alloca_next astk
Proof
  ho_match_mp_tac ld_annotated_reachable_strongind >> rpt conj_tac
  >- simp[ld_frame_bound_def, ld_selected_def, ld_stack_bound_def]
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume ld_annotated_bounds[next]:
  rpt gen_tac >> strip_tac >>
  `ld_erase L = s.vs_allocas` by metis_tac[ld_annotated_local_maps] >>
  drule_all ld_select_alloca_endpoints >> strip_tac >>
  conj_tac
  >- (simp[] >> irule ld_frame_bound_step >>
      irule ld_frame_bound_alloca >> metis_tac[]) >>
  simp[] >> irule ld_stack_bound_mono >> metis_tac[]
QED

Resume ld_annotated_bounds[block]:
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> ALLOCA` by
    (rpt strip_tac >> gvs[venomInstTheory.is_terminator_def]) >>
  drule_all ld_step_nonallocation_fields >> strip_tac >>
  drule ld_enters_block_allocation_fields >> strip_tac >>
  gvs[] >> metis_tac[ld_frame_bound_entry]
QED

Resume ld_annotated_bounds[call]:
  rpt strip_tac >>
  drule setup_callee_shared_fields >> strip_tac >>
  drule ld_enters_block_allocation_fields >> strip_tac >>
  gvs[ld_stack_bound_def] >> metis_tac[ld_frame_bound_call]
QED

Theorem ld_adopt_return_alloca_next[simp]:
  (adopt_return_fmp ret s).vs_alloca_next = s.vs_alloca_next
Proof
  irule adopt_return_fmp_projection >> simp[]
QED

Resume ld_annotated_bounds[ret]:
  rpt strip_tac >> gvs[ld_stack_bound_def] >>
  drule bind_outputs_shared_fields >>
  simp[adopt_return_fmp_allocas, merge_callee_local_fields] >>
  strip_tac >> gvs[] >> metis_tac[ld_frame_bound_restrict]
QED

Finalise ld_annotated_bounds

Theorem ld_stack_bound_member:
  !astk n f. ld_stack_bound n astk /\ MEM f astk ==>
    f.lf_state.vs_alloca_next <= n /\
    ld_frame_bound f.lf_state.vs_alloca_next f.lf_local f.lf_params f.lf_prov
Proof
  Induct >> simp[ld_stack_bound_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem ld_annotated_live_endpoint:
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn inst s /\
  ld_live astk L AP AG site ==>
  FST (SND site) + SND (SND site) <= s.vs_alloca_next
Proof
  strip_tac >> drule ld_annotated_bounds >> strip_tac >>
  qpat_x_assum `ld_live _ _ _ _ _` mp_tac >> simp[ld_live_def] >> strip_tac
  >- gvs[ld_frame_bound_def] >>
  drule_all ld_stack_bound_member >> strip_tac >>
  qpat_x_assum `ld_frame_bound _ _ _ _` mp_tac >>
  simp[ld_frame_bound_def] >> disch_then (qspec_then `site` mp_tac) >> simp[]
QED

Definition ld_compatible_def:
  ld_compatible (a:(num # num) # (num # num)) b <=>
    if FST a = FST b then SND a = SND b
    else FST (SND a) + SND (SND a) <= FST (SND b) \/
         FST (SND b) + SND (SND b) <= FST (SND a)
End

Definition ld_coherent_def:
  ld_coherent astk L AP AG <=>
    !a b. ld_live astk L AP AG a /\ ld_live astk L AP AG b ==>
      ld_compatible a b
End

Theorem ld_compatible_refl[simp]:
  ld_compatible a a
Proof
  simp[ld_compatible_def]
QED

Theorem ld_compatible_sym:
  ld_compatible a b ==> ld_compatible b a
Proof
  simp[ld_compatible_def] >> metis_tac[]
QED

Theorem ld_coherent_mono:
  ld_coherent astk L AP AG /\
  (!site. ld_live astk' L' AP' AG' site ==> ld_live astk L AP AG site) ==>
  ld_coherent astk' L' AP' AG'
Proof
  simp[ld_coherent_def] >> metis_tac[]
QED

Theorem ld_coherent_step:
  ld_coherent astk L AP AG ==> ld_coherent astk L AP (ld_step_prov AP AG L i)
Proof
  strip_tac >> irule ld_coherent_mono >>
  goal_assum (drule_at Any) >> simp[ld_live_def] >>
  metis_tac[ld_step_selected]
QED

Theorem ld_coherent_entry:
  ld_coherent astk L AP AG ==> ld_coherent astk L AP (ld_entry_prov fn s AG)
Proof
  strip_tac >> irule ld_coherent_mono >>
  goal_assum (drule_at Any) >> simp[ld_live_def] >>
  metis_tac[ld_entry_selected]
QED

Theorem ld_coherent_call:
  ld_coherent astk L AP AG ==>
  ld_coherent
    (<| lf_fn := caller; lf_inst := ins; lf_state := s;
        lf_params := AP; lf_prov := AG; lf_tvar := tv; lf_local := L |> :: astk)
    FEMPTY (MAP (ld_op_prov AG) ops) FEMPTY
Proof
  strip_tac >> irule ld_coherent_mono >>
  goal_assum (drule_at Any) >> simp[ld_live_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[ld_call_selected]
QED

Theorem ld_coherent_ret:
  ld_coherent (f::astk) L AP AG ==>
  ld_coherent astk f.lf_local f.lf_params (DRESTRICT f.lf_prov keys)
Proof
  strip_tac >> irule ld_coherent_mono >>
  goal_assum (drule_at Any) >> simp[ld_live_def] >>
  metis_tac[ld_restrict_selected]
QED

Theorem ld_live_update:
  ld_live astk (L |+ (id,site)) AP AG a ==>
  ld_live astk L AP AG a \/ a = site
Proof
  simp[ld_live_def, ld_selected_def, FLOOKUP_UPDATE, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem ld_coherent_update:
  ld_coherent astk L AP AG /\
  (!a. ld_live astk L AP AG a ==> ld_compatible a site) ==>
  ld_coherent astk (L |+ (id,site)) AP AG
Proof
  simp[ld_coherent_def] >> rpt strip_tac >>
  drule ld_live_update >> strip_tac >> gvs[] >>
  metis_tac[ld_live_update, ld_compatible_sym, ld_compatible_refl]
QED

Theorem ld_select_alloca_cases:
  ld_select_alloca k L i s = (k',L') ==>
  L' = L \/
  ?p. L' = L |+ (i.inst_id,((0,k),p)) /\
      FLOOKUP L i.inst_id = NONE /\
      FLOOKUP s.vs_allocas i.inst_id = SOME p
Proof
  simp[ld_select_alloca_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem ld_annotated_coherent:
  !vs0 ctx astk k L AP AG tn fn inst s.
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn inst s ==>
  ld_coherent astk L AP AG
Proof
  ho_match_mp_tac ld_annotated_reachable_strongind >> rpt conj_tac
  >- simp[ld_coherent_def, ld_live_def, ld_selected_def]
  >- suspend "next"
  >- (rpt strip_tac >> metis_tac[ld_coherent_entry])
  >- (rpt strip_tac >> metis_tac[ld_coherent_call])
  >> (rpt strip_tac >> metis_tac[ld_coherent_ret])
QED

Resume ld_annotated_coherent[next]:
  rpt strip_tac >> irule ld_coherent_step >>
  drule ld_select_alloca_cases >> strip_tac >- gvs[] >>
  gvs[] >> irule ld_coherent_update >> simp[] >>
  gen_tac >> disch_tac >>
  `FST (FST a) = (0:num) /\ SND (FST a) < k` by
    metis_tac[ld_annotated_serial] >>
  `FST (SND a) + SND (SND a) <= s.vs_alloca_next` by
    metis_tac[ld_annotated_live_endpoint] >>
  `ld_erase L = s.vs_allocas` by metis_tac[ld_annotated_local_maps] >>
  drule_all ld_select_alloca_endpoints >> strip_tac >>
  qpat_x_assum `!id site. _`
    (qspecl_then [`inst.inst_id`, `((0,k),p)`] mp_tac) >>
  simp[FLOOKUP_UPDATE] >> strip_tac >>
  `FST a <> (0,k)` by (strip_tac >> gvs[]) >>
  simp[ld_compatible_def]
QED

Finalise ld_annotated_coherent

(* Lookup consumers use ld_selected_def for local/parameter/provenance
   selections, without unfolding any annotated propagation operation. *)
Theorem ld_annotated_saved_endpoint:
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn inst s /\ MEM f astk /\
  ld_selected f.lf_local f.lf_params f.lf_prov site ==>
  FST (SND site) + SND (SND site) <= f.lf_state.vs_alloca_next /\
  f.lf_state.vs_alloca_next <= s.vs_alloca_next
Proof
  strip_tac >> drule ld_annotated_bounds >> strip_tac >>
  drule_all ld_stack_bound_member >>
  simp[ld_frame_bound_def] >> metis_tac[]
QED

Theorem ld_annotated_owner_site:
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn inst s /\
  ld_live astk L AP AG a /\ ld_live astk L AP AG b /\ FST a = FST b ==>
  SND a = SND b
Proof
  strip_tac >> drule ld_annotated_coherent >>
  simp[ld_coherent_def] >>
  disch_then (qspecl_then [`a`, `b`] mp_tac) >> simp[ld_compatible_def]
QED

Theorem ld_annotated_owner_separation:
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn inst s /\
  ld_live astk L AP AG a /\ ld_live astk L AP AG b /\ FST a <> FST b ==>
  FST (SND a) + SND (SND a) <= FST (SND b) \/
  FST (SND b) + SND (SND b) <= FST (SND a)
Proof
  strip_tac >> drule ld_annotated_coherent >>
  simp[ld_coherent_def] >>
  disch_then (qspecl_then [`a`, `b`] mp_tac) >> simp[ld_compatible_def]
QED

Theorem ld_source_ownership:
  frame_reachable vs0 ctx stk PG G tn fn inst s /\
  o1_src_inv D ctx vs0 /\ o1_ctx_shape ctx /\ o1_run_state_ok vs0 ==>
  ?astk k L AP AG.
    ld_annotated_reachable vs0 ctx astk k L AP AG tn fn inst s /\
    MAP ld_erase_frame astk = stk /\ MAP (OPTION_MAP SND) AP = PG /\
    ld_erase AG = G /\
    ld_frame_bound s.vs_alloca_next L AP AG /\
    ld_stack_bound s.vs_alloca_next astk /\ ld_coherent astk L AP AG
Proof
  strip_tac >> drule_all ld_source_annotation >> strip_tac >>
  qexistsl [`astk`, `k`, `L`, `AP`, `AG`] >> simp[] >>
  metis_tac[ld_annotated_bounds, ld_annotated_coherent]
QED
