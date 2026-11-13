(* Shared array transition assembly and strong-result packaging. *)
Theory abiEncoderWindowArrayResultMem
Ancestors
  abiEncoderWindowArrayInvariant abiEncoderWindowArrayLoop abiEncoderWindowArrayRound
  abiEncoderWindowContract abiEncoderRegisteredEffect abiEncoderExtendSim
  freshWrites pred_set valueEncoding valueEncodingDefs valueEncodingProps

Theorem window_array_transition_assembly:
  window_array_transition ctx func st ids [(d,32)] s entry /\
  window_array_transition ctx func owner loop_ids [(d,n)] entry completed /\
  window_array_transition ctx func owner {site} [] completed t /\
  (!x. not_fresh_at st x ==> not_fresh_at owner x) /\
  loop_ids SUBSET ids /\ site IN ids /\ 32 <= n ==>
  window_array_transition ctx func st ids [(d,n)] s t
Proof
  strip_tac >>
  `window_array_transition ctx func st ids [(d,n)] entry completed` by
    (irule window_array_transition_owner_weaken >> qexists_tac `owner` >>
     asm_rewrite_tac[] >> irule window_array_transition_region >>
     qexistsl_tac [`loop_ids`, `[(d,n)]`] >> asm_rewrite_tac[] >> simp[]) >>
  `window_array_transition ctx func st ids [(d,n)] completed t` by
    (irule window_array_transition_owner_weaken >> qexists_tac `owner` >>
     asm_rewrite_tac[] >> irule window_array_transition_region >>
     qexistsl_tac [`{site}`, `[]`] >> asm_rewrite_tac[] >> simp[]) >>
  `window_array_transition ctx func st ids [(d,n)] s entry` by
    (irule window_array_transition_region >> qexistsl_tac [`ids`, `[(d,32)]`] >>
     asm_rewrite_tac[] >> simp[]) >>
  irule window_array_transition_trans >> qexists_tac `entry` >> asm_rewrite_tac[] >>
  irule window_array_transition_trans >> qexists_tac `completed` >> asm_rewrite_tac[]
QED

Theorem window_array_transition_strong_result:
  window_array_transition ctx func st (window_alloca_sites func (frag_ids st en))
    [(d,LENGTH (enc at av))] s t /\
  window_sizes32 (window_alloca_sites func (frag_ids st en)) s /\
  mem_bytes_at d (LENGTH (enc at av)) t.vs_memory = enc at av /\
  eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
  t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts ==>
  window_strong_result ctx func st en out at av d s t
Proof
  strip_tac >>
  `window_sizes32 (window_alloca_sites func (frag_ids st en)) t` by
    (qpat_x_assum `window_array_transition _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_array_transition_def] >>
     strip_tac >> first_x_assum irule >> asm_rewrite_tac[]) >>
  qpat_x_assum `window_array_transition _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [window_array_transition_def] >> strip_tac >>
  `abi_encoder_registered_effect (frag_ids st en)
    [(d,LENGTH (enc at av))] s t` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl_tac [`window_alloca_sites func (frag_ids st en)`,
       `[(d,LENGTH (enc at av))]`] >>
     asm_rewrite_tac[] >> irule window_alloca_sites_subset) >>
  simp_tac bool_ss [window_strong_result_def, abi_encoder_window_result_def] >>
  asm_rewrite_tac[] >>
  conj_tac >- metis_tac[abi_encoder_extend_sim_sim] >>
  qpat_x_assum `window_sizes32 _ t` mp_tac >>
  simp_tac bool_ss [window_sizes32_def] >> strip_tac >> asm_rewrite_tac[]
QED
