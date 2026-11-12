Theory dftGasInvFixedTrace
Ancestors
  dftGasInvExtraction dftGasInvFlexibleTrace dftGasInvCallExchange
  dftGasInvResidualTrace dftGasInvInversion dftGasOracleDefs
  dftRunRel dftScheduleOrder dftStructural dftSsaPreserve dftPermSim
  venomInst venomState list rich_list sorting pred_set

Theorem inv_ev_trace_append:
  !xs ys s t. inv_ev_trace orc p d fuel ctx (xs ++ ys) s t <=>
    ?u. inv_ev_trace orc p d fuel ctx xs s u /\
        inv_ev_trace orc p d fuel ctx ys u t
Proof
  Induct >> simp[inv_ev_trace_def] >> metis_tac[]
QED

Theorem inv_ev_trace_exchange:
  dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  inv_ev_trace orc p d fuel ctx (y::x::xs) s t ==>
  inv_ev_trace orc p d fuel ctx (x::y::xs) s t
Proof
  simp[inv_ev_trace_def] >> rpt strip_tac >>
  drule_all inv_ev_indexed_pair_ok >> strip_tac >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem inv_trace_pull:
  !pre s t.
  EVERY (\z. dft_gas_swap_pair x z /\ inst_wf x /\ inst_wf z) pre /\
  inv_ev_trace orc p d fuel ctx (pre ++ x::post) s t ==>
  inv_ev_trace orc p d fuel ctx (x::pre ++ post) s t
Proof
  Induct >> simp[] >> rpt strip_tac >>
  qpat_x_assum `inv_ev_trace _ _ _ _ _ _ _ _` mp_tac >>
  simp[Once inv_ev_trace_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  irule inv_ev_trace_exchange >> simp[] >>
  simp[Once inv_ev_trace_def] >> gvs[APPEND] >> metis_tac[]
QED

Theorem inv_trace_source_sort:
  !ordered executed s t.
  ALL_DISTINCT ordered /\ PERM executed ordered /\
  (!x z. id_before ordered x z /\ id_before executed z x ==>
     dft_gas_swap_pair x z /\ inst_wf x /\ inst_wf z) /\
  inv_ev_trace orc p d fuel ctx executed s t ==>
  inv_ev_trace orc p d fuel ctx ordered s t
Proof
  Induct >> simp[] >> rpt strip_tac >>
  `MEM h executed` by metis_tac[PERM_MEM_EQ, MEM] >>
  `?pre post. executed = pre ++ h::post` by metis_tac[MEM_SPLIT] >>
  `PERM (pre ++ post) ordered` by
    (irule perm_cons_delete >> qexists_tac `h` >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> metis_tac[]) >>
  `EVERY (\z. dft_gas_swap_pair h z /\ inst_wf h /\ inst_wf z) pre` by
    (simp[EVERY_MEM] >> gen_tac >> disch_tac >> first_x_assum irule >>
     simp[dftSsaPreserveTheory.id_before_cons,
          dftSsaPreserveTheory.id_before_append] >>
     metis_tac[PERM_MEM_EQ, MEM_APPEND]) >>
  `inv_ev_trace orc p d fuel ctx (h::pre ++ post) s t` by
    (irule inv_trace_pull >> goal_assum (drule_at Any) >> metis_tac[]) >>
  gvs[Once inv_ev_trace_def] >> simp[Once inv_ev_trace_def] >>
  first_x_assum irule >>
  goal_assum (drule_at Any) >> simp[] >>
  ntac 2 gen_tac >> strip_tac >> first_x_assum irule >>
  gvs[dftSsaPreserveTheory.id_before_cons,
      dftSsaPreserveTheory.id_before_append] >> metis_tac[]
QED

Theorem inv_trace_original_representatives:
  !scheduled s t.
  EVERY (from_block bi) scheduled /\ inv_ev_trace orc p d fuel ctx scheduled s t ==>
  ?originals. MAP (\i. i.inst_id) originals = MAP (\i. i.inst_id) scheduled /\
    EVERY (\i. MEM i bi /\ ~is_pseudo i.inst_opcode) originals /\
    inv_ev_trace orc p d fuel ctx originals s t
Proof
  Induct
  >- simp[inv_ev_trace_def] >>
  simp[inv_ev_trace_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `from_block _ _` mp_tac >> simp[from_block_def] >> strip_tac >>
  qexists_tac `j::originals` >> simp[] >>
  gvs[flip_operands_inst_id] >>
  simp[inv_ev_trace_def] >>
  metis_tac[inv_ev_flip_step, inv_ev_flip_nonterminator]
QED

Theorem inv_lookup_body_sort:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bb' /\
  bb.bb_instructions = pseudos ++ ordered ++ [term] /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ordered /\
  MAP (\i. i.inst_id) bb'.bb_instructions =
    MAP (\i. i.inst_id) pseudos ++ MAP (\i. i.inst_id) executed ++ [term.inst_id] /\
  ALL_DISTINCT ordered /\ PERM executed ordered /\
  inv_ev_trace orc p d fuel ctx executed s t ==>
  inv_ev_trace orc p d fuel ctx ordered s t
Proof
  strip_tac >> irule inv_trace_source_sort >> simp[] >>
  qexists_tac `executed` >> simp[] >> ntac 2 gen_tac >> strip_tac >>
  `MEM x ordered /\ MEM z ordered` by
    metis_tac[id_before_def, EL_MEM, arithmeticTheory.LESS_TRANS] >>
  `MEM x bb.bb_instructions /\ MEM z bb.bb_instructions /\
   ~is_pseudo x.inst_opcode /\ ~is_pseudo z.inst_opcode` by
    (asm_rewrite_tac[MEM_APPEND] >> fs[EVERY_MEM] >> metis_tac[]) >>
  `id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id z.inst_id /\
   id_before (MAP (\i. i.inst_id) bb'.bb_instructions) z.inst_id x.inst_id` by
    (`id_before (MAP (\i. i.inst_id) ordered) x.inst_id z.inst_id /\
      id_before (MAP (\i. i.inst_id) executed) z.inst_id x.inst_id` by
       metis_tac[dftSsaPreserveTheory.id_before_map] >>
     asm_rewrite_tac[MAP_APPEND] >>
     simp[dftSsaPreserveTheory.id_before_append] >> metis_tac[]) >>
  drule_all inv_lookup_inversion_swap >> simp[]
QED
