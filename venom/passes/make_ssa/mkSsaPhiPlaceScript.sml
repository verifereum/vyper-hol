(*
 * SSA Construction: PHI Placement
 *
 * This theory defines PHI placement based on dominance frontiers and
 * simple worklist iteration with explicit fuel.
 *)

Theory mkSsaPhiPlace
Ancestors
  mkSsaDominance mkSsaCfg mkSsaDefs mkSsaTransform
  venomInst list finite_map pred_set

(* ===== Definition Sites ===== *)

(* TOP-LEVEL: Compute definition sites for each variable. *)
Definition compute_def_sites_def:
  compute_def_sites blocks =
    FOLDR (λbb acc.
      FOLDR (λinst acc'.
        FOLDR (λv acc''.
          let curr = case FLOOKUP acc'' v of SOME s => s | NONE => {} in
          acc'' |+ (v, bb.bb_label INSERT curr)
        ) acc' inst.inst_outputs
      ) acc bb.bb_instructions
    ) FEMPTY blocks
End

(* ===== Worklist PHI Placement ===== *)

Definition phi_worklist_fuel_def:
  phi_worklist_fuel 0 _ work placed _ = placed /\
  phi_worklist_fuel (SUC n) df work placed seen =
    if work = {} then placed
    else
      let bb = CHOICE work in
      let work' = work DELETE bb in
      let frontier = get_dom_frontier df bb in
      let new_sites = frontier DIFF placed in
      let work'' = work' UNION (new_sites DIFF seen) in
      phi_worklist_fuel n df work'' (placed UNION new_sites) (seen UNION new_sites)
End

Definition phi_sites_var_def:
  phi_sites_var df var def_sites =
    let init_work = case FLOOKUP def_sites var of SOME s => s | NONE => {} in
    let fuel = (CARD (FDOM df)) * (CARD (FDOM df)) in
    phi_worklist_fuel fuel df init_work {} init_work
End

(* Helper: Iterated dominance frontier via the same worklist/fuel. *)
Definition iterated_df_def:
  iterated_df df init =
    let fuel = (CARD (FDOM df)) * (CARD (FDOM df)) in
    phi_worklist_fuel fuel df init {} init
End

Definition compute_all_phi_sites_def:
  compute_all_phi_sites df def_sites =
    FUN_FMAP (λvar. phi_sites_var df var def_sites) (FDOM def_sites)
End

(* ===== Block Update Helpers ===== *)

Definition update_block_def:
  update_block fn bb =
    fn with fn_blocks :=
      MAP (λb. if b.bb_label = bb.bb_label then bb else b) fn.fn_blocks
End

(* ===== PHI Insertion ===== *)

Definition insert_phi_at_def:
  insert_phi_at preds var bb next_id =
    let pred_list = SET_TO_LIST preds in
    place_phi_at_block next_id var pred_list bb
End

Definition insert_phis_def:
  insert_phis phi_sites preds live_in fn next_id =
    FOLDL (λ(fn', id) var.
      let sites = case FLOOKUP phi_sites var of SOME s => s | NONE => {} in
      FOLDL (λ(fn'', id') site.
        if var IN live_in site then
          case lookup_block site fn''.fn_blocks of
            NONE => (fn'', id')
          | SOME bb =>
              let (bb', id'') =
                insert_phi_at (get_preds preds site) var bb id' in
              (update_block fn'' bb', id'')
        else (fn'', id')
      ) (fn', id) (SET_TO_LIST sites)
    ) (fn, next_id) (SET_TO_LIST (FDOM phi_sites))
End

(* ===== Basic Properties ===== *)

Theorem phi_sites_complete:
  !df def_sites var sites.
    sites = phi_sites_var df var def_sites ==>
    !b.
      b IN iterated_df df
        (case FLOOKUP def_sites var of SOME s => s | NONE => {}) ==>
      b IN sites
Proof
  rpt strip_tac >>
  simp[phi_sites_var_def, iterated_df_def]
QED

Theorem resolve_phi_mk_phi_operands:
  !preds var prev.
    MEM prev preds ==>
    resolve_phi prev (mk_phi_operands preds var) = SOME (Var var)
Proof
  Induct_on `preds` >> simp[mk_phi_operands_def, resolve_phi_def] >>
  rpt strip_tac >>
  Cases_on `h = prev` >> simp[resolve_phi_def]
QED

Theorem phi_operands_cover_predecessors:
  !preds var bb next_id bb' next_id' prev.
    insert_phi_at preds var bb next_id = (bb', next_id') /\
    FINITE preds /\
    prev IN preds ==>
    ?phi.
      HD bb'.bb_instructions = phi /\
      resolve_phi prev phi.inst_operands = SOME (Var var)
Proof
  rpt strip_tac >>
  qexists_tac `mk_phi_inst next_id var (SET_TO_LIST preds) var` >>
  qpat_x_assum `insert_phi_at preds var bb next_id = (bb', next_id')` mp_tac >>
  simp[insert_phi_at_def, place_phi_at_block_def] >>
  strip_tac >> gvs[] >>
  drule resolve_phi_mk_phi_operands >>
  simp[MEM_SET_TO_LIST]
QED

Theorem insert_phi_at_well_formed:
  !preds var bb next_id bb' next_id'.
    insert_phi_at preds var bb next_id = (bb', next_id') ==>
    ?phi.
      HD bb'.bb_instructions = phi /\
      phi.inst_opcode = PHI /\
      phi.inst_outputs = [var] /\
      phi_well_formed phi.inst_operands
Proof
  rpt strip_tac >>
  qexists_tac `mk_phi_inst next_id var (SET_TO_LIST preds) var` >>
  qpat_x_assum `insert_phi_at preds var bb next_id = (bb', next_id')` mp_tac >>
  simp[insert_phi_at_def, place_phi_at_block_def] >>
  strip_tac >> gvs[] >>
  simp[mk_phi_inst_def, mk_phi_operands_well_formed]
QED
