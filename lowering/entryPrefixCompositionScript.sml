(* First-cut prefix composition requires exclusion of the enclosing cut. *)
Theory entryPrefixComposition
Ancestors abiEncoderObserver venomState

Theorem abi_observer_step_change_cut:
  !ctx fn inner x y outer.
    abi_observer_step ctx fn inner x y /\
    (x.vs_current_bb,x.vs_inst_idx) <> outer ==>
    abi_observer_step ctx fn outer x y
Proof
  simp[abi_observer_step_def] >> metis_tac[]
QED

Theorem local_prefix_compose_invariant:
  !ctx fn inner s m.
    local_prefix ctx fn inner s m ==>
    !outer t P.
      local_prefix ctx fn outer m t /\ P s /\
      (!x y. P x /\ abi_observer_step ctx fn inner x y ==> P y) /\
      (!x. P x /\ (x.vs_current_bb,x.vs_inst_idx) <> inner ==>
        (x.vs_current_bb,x.vs_inst_idx) <> outer) ==>
      local_prefix ctx fn outer s t
Proof
  ho_match_mp_tac local_prefix_ind >> rpt strip_tac >>
  rename1 `abi_observer_step ctx fn inner s middle` >>
  irule (cj 2 local_prefix_rules) >>
  qexists_tac `middle` >> conj_tac
  >- (irule abi_observer_step_change_cut >> conj_tac
      >- (first_x_assum irule >> fs[abi_observer_step_def]) >>
      qexists_tac `inner` >> asm_rewrite_tac[]) >>
  qpat_x_assum `!outer t P. _` irule >>
  reverse conj_tac >- asm_rewrite_tac[] >>
  qexists_tac `P` >> asm_rewrite_tac[] >> metis_tac[]
QED

Theorem local_prefix_compose_region:
  !ctx fn inner s m outer t R.
    local_prefix ctx fn inner s m /\ local_prefix ctx fn outer m t /\
    R (s.vs_current_bb,s.vs_inst_idx) /\
    (!x y. R (x.vs_current_bb,x.vs_inst_idx) /\
      abi_observer_step ctx fn inner x y ==> R (y.vs_current_bb,y.vs_inst_idx)) /\
    (!pos. R pos /\ pos <> inner ==> pos <> outer) ==>
    local_prefix ctx fn outer s t
Proof
  rpt strip_tac >> irule local_prefix_compose_invariant >>
  qexistsl_tac [`\x. R (x.vs_current_bb,x.vs_inst_idx)`, `inner`, `m`] >>
  simp[] >> metis_tac[]
QED
