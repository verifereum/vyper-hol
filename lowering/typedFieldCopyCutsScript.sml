Theory typedFieldCopyCuts
Ancestors
  typedNormalizeFields typedNormalizeEntryBoundary typedNormalizeContinuation
  exprLoweringProps stmtLoweringMono compileEnv context emitHelper fragExec
  venomExecSemantics venomInst list rich_list

Theorem normalize_fields_compiler_cuts:
  !DT ST d0 s0 sa sb N.
  LENGTH DT = N /\ LENGTH ST = N /\
  compile_typed_copy_fields ce dst src DT ST d0 s0 sa = ((),sb) /\
  fn_has_code sa sb fn /\
  (emitted_blocks sa sb <> [] ==>
    ?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) ==>
  ?C DP A SP B.
    C 0 = sa /\ C N = sb /\
    !i. i < N ==>
      compile_with_byte_offset dst
        (d0 + SUM (MAP (type_memory_bytes ce) (TAKE i DT))) (C i) = (DP i,A i) /\
      compile_with_byte_offset src
        (s0 + SUM (MAP (type_memory_bytes ce) (TAKE i ST))) (A i) = (SP i,B i) /\
      compile_store_memory_typed ce (DP i) (EL i DT) (SP i) (EL i ST) (B i) =
        ((),C (SUC i)) /\
      cs_extends (C i) (C (SUC i)) /\ fn_has_code (C i) (C (SUC i)) fn /\
      (emitted_blocks (C i) (C (SUC i)) <> [] ==>
        ?bb. lookup_block (C (SUC i)).cs_current_bb fn.fn_blocks = SOME bb /\
          phi_prefix_length bb.bb_instructions = 0)
Proof
  Induct_on `DT`
  >- (rpt gen_tac >> simp[Once compile_store_memory_typed_def, comp_return_def] >>
      strip_tac >> gvs[] >> qexists_tac `\i. sa` >> simp[]) >>
  rpt gen_tac >> Cases_on `ST` >- (strip_tac >> gvs[]) >>
  strip_tac >> drule normalize_fields_cons_states >> strip_tac >>
  drule_all normalize_fields_suffix_code >> strip_tac >>
  `cs_extends sd se /\ cs_extends se sb` by
    metis_tac[ci_mono_typed_memory_family, ci_mono_def, pairTheory.SND] >>
  imp_res_tac normalize_byte_offset_straight >>
  `cs_extends sa se` by metis_tac[cs_extends_trans] >>
  `emitted_blocks sa se = emitted_blocks sd se` by simp[emitted_blocks_def] >>
  `(emitted_blocks sa se <> [] ==>
    ?bb. lookup_block se.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0)` by
    (strip_tac >> irule normalize_fields_conditional_suffix_entry >>
     goal_assum (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ se = _`)) >>
     qexists_tac `sa` >> simp[] >>
     metis_tac[normalize_typed_changed_prefix_zero]) >>
  `(emitted_blocks se sb <> [] ==>
    ?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0)` by
    (strip_tac >> first_x_assum irule >>
     qpat_assum `cs_extends sa se` mp_tac >>
     qpat_assum `cs_extends se sb` mp_tac >>
     qpat_x_assum `emitted_blocks se sb <> []` mp_tac >>
     simp_tac (srw_ss()) [cs_extends_def, emitted_blocks_def,
       LENGTH_APPEND, TAKE_LENGTH_APPEND] >> rpt strip_tac >>
     gvs[LENGTH_APPEND] >> decide_tac) >>
  `LENGTH t = LENGTH DT` by gvs[] >>
  qpat_x_assum `!ST d0 s0 sa sb N. _`
    (qspec_then `t` mp_tac) >> simp[] >>
  disch_then drule_all >> strip_tac >>
  qexistsl_tac [`\i. if i = 0 then sa else C (PRE i)`,
    `\i. if i = 0 then dp else DP (PRE i)`,
    `\i. if i = 0 then sc else A (PRE i)`,
    `\i. if i = 0 then sp else SP (PRE i)`,
    `\i. if i = 0 then sd else B (PRE i)`] >>
  `N = SUC (LENGTH DT)` by gvs[] >> simp[] >>
  gen_tac >> Cases_on `i` >- simp[] >>
  gvs[]
QED
