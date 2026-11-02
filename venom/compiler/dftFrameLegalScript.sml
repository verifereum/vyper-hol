(* Legal swaps retain the source-directed root ordering exclusion. *)
Theory dftFrameLegal
Ancestors
  dftFrameCertificate dftFrameCross dftFrameSwap dftFramePerm dftFrameNormalize
  dftRunRel dftScheduleOrder dftDefs dftWf venomWf venomInst unitShapeDefs
  relation sorting list

Definition dft_legal_cross_def:
  dft_legal_cross a b <=> dft_cross a b /\ ~dft_must_order a b
End

Definition dft_legal_swap_list_def:
  dft_legal_swap_list = adjacent_swap dft_legal_cross
End

Definition dft_legal_swap_fn_def:
  dft_legal_swap_fn f g <=>
    ?p bb q insts.
      f.fn_blocks = p ++ [bb] ++ q /\
      dft_legal_swap_list bb.bb_instructions insts /\
      g = f with fn_blocks := p ++ [bb with bb_instructions := insts] ++ q
End

Theorem dft_legal_cross_projection:
  dft_legal_cross a b ==> dft_cross a b
Proof
  simp[dft_legal_cross_def]
QED

Theorem dft_legal_swap_list_projection:
  dft_legal_swap_list l r ==> dft_swap_list l r
Proof
  simp[dft_legal_swap_list_def, dft_swap_list_def, adjacent_swap_def,
       dft_legal_cross_def] >> metis_tac[]
QED

Theorem dft_legal_swap_fn_projection:
  dft_legal_swap_fn f g ==> dft_swap_fn f g
Proof
  simp[dft_legal_swap_fn_def, dft_swap_fn_def] >>
  metis_tac[dft_legal_swap_list_projection]
QED

Theorem dft_legal_swap_RTC_projection:
  !f g. RTC dft_legal_swap_fn f g ==> RTC dft_swap_fn f g
Proof
  ho_match_mp_tac RTC_INDUCT >> simp[] >> rpt strip_tac >>
  metis_tac[dft_legal_swap_fn_projection, RTC_RULES]
QED

Theorem dft_block_legal_certificate:
  wf_function f /\ wf_ssa f /\ fn_inst_wf f /\ fn_pseudos_prefix f /\
  MEM bb f.fn_blocks /\ dft_block_rel bb bb' /\
  (!x y. MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
    ~abort_compatible x.inst_opcode y.inst_opcode /\
    id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id ==>
    id_before (MAP (\i. i.inst_id) bb'.bb_instructions) x.inst_id y.inst_id) ==>
  ?n. RTC dft_legal_swap_list bb.bb_instructions n /\
      dft_flip_block (bb with bb_instructions := n) bb'
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[wf_fn_block_inst_ids_distinct] >>
  `pseudos_prefix bb` by metis_tac[fn_pseudos_prefix_def] >>
  drule_all dft_block_normalize >> strip_tac >>
  qexists_tac `n` >> conj_tac
  >- (pure_rewrite_tac[dft_legal_swap_list_def] >>
      `ALL_DISTINCT bb.bb_instructions` by metis_tac[ALL_DISTINCT_MAP] >>
      irule adjacent_swap_extract >> simp[] >> rpt strip_tac >>
      `dft_cross a b` by
        (irule dft_normalized_inversion_cross >> metis_tac[]) >>
      simp[dft_legal_cross_def] >>
      irule normalized_inversion_unordered >> metis_tac[dft_cross_def]) >>
  simp[dft_flip_block_def] >> metis_tac[dft_block_rel_def]
QED

Theorem dft_legal_block_RTC_lift:
  !l r. RTC dft_legal_swap_list l r ==>
  !f p bb q. f.fn_blocks = p ++ [bb] ++ q /\ bb.bb_instructions = l ==>
    RTC dft_legal_swap_fn f
      (f with fn_blocks := p ++ [bb with bb_instructions := r] ++ q)
Proof
  ho_match_mp_tac RTC_INDUCT >> rpt strip_tac
  >- (gvs[] >>
      `bb with bb_instructions := bb.bb_instructions = bb` by
        (Cases_on `bb` >> simp[]) >>
      simp[] >>
      qpat_x_assum `f.fn_blocks = _` (fn th => rewrite_tac[GSYM th]) >>
      Cases_on `f` >> simp[]) >>
  irule RTC_TRANS >>
  qexists_tac `f with fn_blocks := p ++ [bb with bb_instructions := l'] ++ q` >>
  conj_tac
  >- (irule RTC_SINGLE >> simp[dft_legal_swap_fn_def] >>
      qexistsl [`p`, `bb`, `q`, `l'`] >> simp[]) >>
  first_x_assum (qspecl_then
    [`f with fn_blocks := p ++ [bb with bb_instructions := l'] ++ q`,
     `p`, `bb with bb_instructions := l'`, `q`] mp_tac) >> simp[]
QED

Theorem dft_legal_blocks_RTC_lift:
  !bs cs. LIST_REL (\b c. c.bb_label = b.bb_label /\
      RTC dft_legal_swap_list b.bb_instructions c.bb_instructions) bs cs ==>
    !f p q. RTC dft_legal_swap_fn (f with fn_blocks := p ++ bs ++ q)
                                (f with fn_blocks := p ++ cs ++ q)
Proof
  Induct >> Cases_on `cs` >> simp[] >> rpt strip_tac >>
  rename1 `RTC dft_legal_swap_list src.bb_instructions dst.bb_instructions` >>
  `src with bb_instructions := dst.bb_instructions = dst` by
    simp[basic_block_component_equality] >>
  irule RTC_TRANS >>
  qexists_tac `f with fn_blocks := p ++ dst::bs ++ q` >> conj_tac
  >- (drule dft_legal_block_RTC_lift >>
      disch_then (qspecl_then
        [`f with fn_blocks := p ++ src::bs ++ q`, `p`, `src`, `bs ++ q`] mp_tac) >>
      pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
  first_x_assum drule >>
  disch_then (qspecl_then [`f`, `p ++ [dst]`, `q`] mp_tac) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]
QED

Theorem dft_blocks_legal_certificate:
  !bs cs. LIST_REL dft_block_rel bs cs /\
    LIST_REL (\bb bb'. !x y.
      MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
      ~abort_compatible x.inst_opcode y.inst_opcode /\
      id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id ==>
      id_before (MAP (\i. i.inst_id) bb'.bb_instructions) x.inst_id y.inst_id) bs cs ==>
    !f. wf_function f /\ wf_ssa f /\ fn_inst_wf f /\ fn_pseudos_prefix f /\
      (!bb. MEM bb bs ==> MEM bb f.fn_blocks) ==>
    ?ns. LIST_REL (\b c. c.bb_label = b.bb_label /\
           RTC dft_legal_swap_list b.bb_instructions c.bb_instructions) bs ns /\
         LIST_REL dft_flip_block ns cs
Proof
  Induct >> Cases_on `cs` >> simp[] >> rpt strip_tac >>
  rename1 `dft_block_rel src dst` >>
  `MEM src f.fn_blocks` by metis_tac[] >>
  drule_all dft_block_legal_certificate >> strip_tac >>
  `?ns. LIST_REL (\b c. c.bb_label = b.bb_label /\
           RTC dft_legal_swap_list b.bb_instructions c.bb_instructions) bs ns /\
         LIST_REL dft_flip_block ns t` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  qexists_tac `(src with bb_instructions := n)::ns` >> simp[]
QED

Theorem dft_fn_legal_certificate:
  dft_fn_rel f f' /\ fn_shape_ok f /\ dft_labels_bound f L ==>
  ?g. RTC dft_legal_swap_fn f g /\ dft_flip_fn g f' /\ dft_swap_invariant L g
Proof
  simp[dft_fn_rel_def, dft_fallible_order_kept_def] >> strip_tac >>
  `dft_swap_invariant L f` by simp[dft_swap_invariant_def] >>
  drule dft_blocks_legal_certificate >>
  disch_then (qspec_then `f` mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `f with fn_blocks := ns` >>
  `RTC dft_legal_swap_fn f (f with fn_blocks := ns)` by
    (drule dft_legal_blocks_RTC_lift >>
     disch_then (qspecl_then [`f`, `[]`, `[]`] mp_tac) >> simp[] >>
     `f with fn_blocks := f.fn_blocks = f` by (Cases_on `f` >> simp[]) >>
     simp[]) >>
  simp[dft_flip_fn_def] >>
  drule dft_legal_swap_RTC_projection >>
  strip_tac >> drule_all dft_swap_RTC_invariant >> simp[]
QED

Theorem dft_legal_cross_excludes_assert_before_mload:
  ~dft_legal_cross (mk_inst 0 ASSERT [Lit 0w] [])
                   (mk_inst 1 MLOAD [Lit 0w] ["x"])
Proof
  EVAL_TAC >> simp[]
QED
