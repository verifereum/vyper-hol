Theory frameIncomingArgument
Ancestors
  frameAllocationOwnership frameOriginCacheReach frameOriginHistory
  frameOriginReachable frameOriginUpdates ptrDiscipline venomExecSemantics
  venomState venomInst venomWf contextCodegenRel removeUnusedSsaProofs finite_map list

Definition incoming_argument_def:
  incoming_argument stk oms site <=>
    ?k aid u nm ops. k < LENGTH stk /\ k < LENGTH oms /\
      (EL k stk).cf_inst.inst_opcode = INVOKE /\
      decode_invoke (EL k stk).cf_inst = SOME (nm,ops) /\
      active_inst (EL k stk).cf_fn (EL k stk).cf_inst (EL k stk).cf_state /\
      MEM (Var u) ops /\
      FLOOKUP (EL k oms) u = SOME (OriginLocal aid,site)
End

Definition argument_origins_def:
  argument_origins stk oms om <=>
    !v tag site. FLOOKUP om v = SOME (tag,site) ==>
      (?aid. tag = OriginLocal aid) \/
      (?p. tag = OriginParameter p /\ incoming_argument stk oms site)
End

Definition argument_frame_def:
  argument_frame stk oms PG om <=>
    param_sites (incoming_argument stk oms) PG /\
    argument_origins stk oms om
End

Definition argument_stack_def:
  (argument_stack [] oms <=> oms = []) /\
  (argument_stack (f::stk) oms <=>
    ?m ms. oms = m::ms /\ argument_frame stk ms f.cf_params m /\
      argument_stack stk ms)
End

Theorem incoming_argument_cons:
  incoming_argument stk oms site ==>
  incoming_argument (f::stk) (m::oms) site
Proof
  simp[incoming_argument_def] >> rpt strip_tac >>
  qexists_tac `SUC k` >> simp[] >> metis_tac[]
QED

Theorem argument_origins_restrict:
  argument_origins stk oms om ==>
  argument_origins stk oms (DRESTRICT om keys)
Proof
  simp[argument_origins_def, FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem argument_origins_out:
  argument_frame stk oms PG om /\ inst.inst_opcode <> DALLOCA /\
  origin_out PG om inst s = SOME (tag,site) ==>
  (?aid. tag = OriginLocal aid) \/
  (?p. tag = OriginParameter p /\ incoming_argument stk oms site)
Proof
  strip_tac >> Cases_on `inst.inst_opcode = ALLOCA`
  >- (gvs[origin_out_alloca] >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = PARAM`
  >- (gvs[origin_out_param, argument_frame_def, param_sites_def] >>
      metis_tac[MEM_EL]) >>
  drule_all origin_out_inherited >> strip_tac >>
  gvs[origin_op_some, argument_frame_def, argument_origins_def] >> metis_tac[]
QED

Theorem argument_frame_step:
  argument_frame stk oms PG om /\ inst.inst_opcode <> DALLOCA ==>
  argument_frame stk oms PG (origin_step PG om inst s)
Proof
  strip_tac >> fs[argument_frame_def] >> simp[argument_frame_def] >>
  simp[argument_origins_def] >> rpt strip_tac >>
  drule origin_step_lookup >> strip_tac
  >- metis_tac[argument_origins_def] >>
  metis_tac[argument_origins_out, argument_frame_def]
QED

Theorem argument_frame_entry:
  argument_frame stk oms PG om ==>
  argument_frame stk oms PG (origin_entry fn s om)
Proof
  simp[origin_entry_def] >> strip_tac >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  fs[argument_frame_def] >> simp[argument_frame_def, argument_origins_def] >>
  rpt strip_tac >> drule origin_phis_lookup >> strip_tac
  >- metis_tac[argument_origins_def] >>
  gvs[origin_phi_some, origin_op_some, argument_origins_def] >> metis_tac[]
QED

Theorem argument_frame_call:
  argument_frame stk oms PG om /\ origin_erase om = G /\
  callinst.inst_opcode = INVOKE /\ decode_invoke callinst = SOME (nm,ops) /\
  active_inst fn callinst s ==>
  argument_frame
    (<|cf_fn := fn; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tv |> :: stk)
    (om::oms) (MAP (op_prov G) ops) FEMPTY
Proof
  strip_tac >> simp[argument_frame_def, argument_origins_def,
                        param_sites_def, MEM_MAP] >>
  rpt strip_tac >>
  `?v tag. y = Var v /\ FLOOKUP om v = SOME (tag,site)` by
    (Cases_on `y` >> gvs[op_prov_def, origin_erase_lookup,
                          optionTheory.OPTION_MAP_EQ_SOME] >>
     metis_tac[pairTheory.PAIR]) >>
  gvs[] >>
  `(?aid. tag = OriginLocal aid) \/
   (?p. tag = OriginParameter p /\ incoming_argument stk oms site)` by
    metis_tac[argument_frame_def, argument_origins_def]
  >- (simp[incoming_argument_def] >> qexists_tac `0` >> simp[] >> metis_tac[]) >>
  metis_tac[incoming_argument_cons]
QED

Theorem origin_frame_argument_invariant:
  !vs0 ctx stk PG G tn fn inst s oms om.
  origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om ==>
  ~ctx_has_dalloca ctx ==>
  origin_erase om = G /\
  LIST_REL (\f m. origin_erase m = f.cf_prov) stk oms /\
  MEM fn ctx.ctx_functions /\
  EVERY (\f. MEM f.cf_fn ctx.ctx_functions) stk /\
  argument_frame stk oms PG om /\ argument_stack stk oms
Proof
  ho_match_mp_tac origin_frame_reachable_ind >> rpt conj_tac
  >- (rpt strip_tac >> simp[argument_frame_def, argument_origins_def,
          param_sites_def, argument_stack_def] >> metis_tac[lookup_function_MEM])
  >- suspend "next"
  >- (rpt strip_tac >> gvs[origin_entry_erase] >> metis_tac[argument_frame_entry])
  >- suspend "call"
  >> (rpt strip_tac >> gvs[argument_stack_def, argument_frame_def, origin_erase_restrict] >>
      metis_tac[argument_origins_restrict])
QED

Resume origin_frame_argument_invariant[next]:
  rpt strip_tac >> gvs[origin_step_erase] >>
  `inst.inst_opcode <> DALLOCA` by
    (gvs[ctx_has_dalloca_def, EXISTS_MEM] >>
     gvs[active_inst_def, fn_insts_def,
         removeUnusedSsaProofsTheory.fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[MEM_EL]) >>
  metis_tac[argument_frame_step]
QED

Resume origin_frame_argument_invariant[call]:
  rpt strip_tac >> simp[argument_stack_def] >>
  metis_tac[argument_frame_call, origin_frame_current_map, lookup_function_MEM]
QED

Finalise origin_frame_argument_invariant

Theorem joint_incoming_argument:
  joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h /\
  ~ctx_has_dalloca ctx /\
  FLOOKUP om v = SOME (OriginParameter p,site) ==>
  ?k aid u nm ops. k < LENGTH stk /\ k < LENGTH oms /\
    (EL k stk).cf_inst.inst_opcode = INVOKE /\
    decode_invoke (EL k stk).cf_inst = SOME (nm,ops) /\
    active_inst (EL k stk).cf_fn (EL k stk).cf_inst (EL k stk).cf_state /\
    MEM (Var u) ops /\ FLOOKUP (EL k oms) u = SOME (OriginLocal aid,site) /\
    FLOOKUP (EL k stk).cf_state.vs_allocas aid = SOME site
Proof
  strip_tac >> drule joint_origin_history_erasure >> strip_tac >>
  drule_all origin_frame_argument_invariant >>
  simp[argument_frame_def, argument_origins_def] >> strip_tac >>
  `incoming_argument stk oms site` by
    (first_x_assum drule >> simp[]) >>
  fs[incoming_argument_def] >> metis_tac[origin_frame_saved_cache]
QED
