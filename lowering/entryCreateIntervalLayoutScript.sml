Theory entryCreateIntervalLayout
Ancestors
  entryCreateFocusSpec createSizeCutRegion compileEnv fragExec loweringShapeDefs
  venomInst list rich_list

(* This is a stream of occurrences, not the set of installed labels. *)
Definition create_layout_def:
  create_layout a b <=>
    ALL_DISTINCT (b.cs_current_bb :: MAP (\bb. bb.bb_label) (emitted_blocks a b))
End

Theorem create_emitted_blocks_shape[local]:
  cs_extends a b ==>
  b.cs_blocks = emitted_blocks a b ++ a.cs_blocks /\
  (if emitted_blocks a b = [] then
     b.cs_current_bb = a.cs_current_bb /\
     isPREFIX a.cs_current_insts b.cs_current_insts
   else
     (LAST (emitted_blocks a b)).bb_label = a.cs_current_bb /\
     isPREFIX a.cs_current_insts (LAST (emitted_blocks a b)).bb_instructions)
Proof
  simp_tac std_ss [cs_extends_def] >> strip_tac >>
  `emitted_blocks a b = new` by metis_tac[emitted_blocks_append] >>
  simp[]
QED

Theorem create_emitted_blocks_compose[local]:
  cs_extends a m /\ cs_extends m b ==>
  emitted_blocks a b = emitted_blocks m b ++ emitted_blocks a m
Proof
  strip_tac >> irule emitted_blocks_append >>
  imp_res_tac create_emitted_blocks_shape >> simp[APPEND_ASSOC]
QED

Theorem create_layout_left[local]:
  cs_extends a m /\ cs_extends m b /\ create_layout a b ==>
  create_layout a m
Proof
  strip_tac >> drule_all create_emitted_blocks_compose >> strip_tac >>
  drule_then mp_tac create_emitted_blocks_shape >>
  Cases_on `emitted_blocks m b = []`
  >- (fs[create_layout_def] >> metis_tac[]) >>
  simp[create_layout_def] >> strip_tac >>
  `MEM m.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks m b))` by
    (simp[MEM_MAP] >> qexists_tac `LAST (emitted_blocks m b)` >>
     simp[MEM_LAST_NOT_NIL]) >>
  fs[create_layout_def, ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem create_layout_right[local]:
  cs_extends a m /\ cs_extends m b /\ create_layout a b ==>
  create_layout m b
Proof
  strip_tac >> drule_all create_emitted_blocks_compose >> strip_tac >>
  fs[create_layout_def, ALL_DISTINCT_APPEND]
QED

Theorem create_layout_subinterval:
  cs_extends o' a /\ cs_extends a b /\ cs_extends b z /\ create_layout o' z ==>
  create_layout a b
Proof
  metis_tac[cs_extends_trans, create_layout_right, create_layout_left]
QED

Theorem create_layout_of_all_blocks:
  cs_extends a b /\ ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks b)) ==>
  create_layout a b
Proof
  strip_tac >> drule create_emitted_blocks_shape >> strip_tac >>
  fs[create_layout_def, all_blocks_def, MAP_REVERSE, ALL_DISTINCT_APPEND]
QED

Theorem create_layout_left_stop:
  cs_extends a m /\ cs_extends m b /\ create_layout a b /\
  create_cut_region a m u /\ ~create_operand_at m u ==>
  ~create_operand_at b u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all create_emitted_blocks_compose >> strip_tac >>
  qpat_assum `cs_extends m b` (mp_tac o MATCH_MP create_emitted_blocks_shape) >>
  Cases_on `emitted_blocks m b = []`
  >- (simp[] >> strip_tac >>
      `LENGTH m.cs_current_insts <= LENGTH b.cs_current_insts` by
        metis_tac[IS_PREFIX_LENGTH] >>
      fs[create_layout_def, create_cut_region_def, create_operand_at_def, MEM_MAP] >>
      metis_tac[MEM_LAST_NOT_NIL, MEM_FRONT_NOT_NIL, FRONT_DEF,
                DECIDE ``i:num <= j /\ j <= i ==> i = j``]) >>
  simp[] >> strip_tac >>
  fs[create_layout_def, create_cut_region_def, create_operand_at_def, MEM_MAP] >>
  metis_tac[MEM_LAST_NOT_NIL, MEM_FRONT_NOT_NIL, FRONT_DEF]
QED
