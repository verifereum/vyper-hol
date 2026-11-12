(*
 * From fragment fuel bounds to per-function fuel bounds of a packaged unit.
 *
 * A unit's generator emits the entry code from the initial state, then the
 * internal functions (compile_internal_fn_bodies), each from a new block
 * carrying its label.  extract_context_with_internals cuts the block stream
 * at those labels.  Each function's blocks are then exactly the blocks one
 * closed fragment emitted, so fuel_stable_of_frag applies to it.
 *
 * TOP-LEVEL:
 *   fuel_stable_of_segment      - one closed fragment, packaged as a function
 *   compile_internal_fn_bodies_fuel
 *   extract_context_fuel_stable - every function of the extracted context
 *)

Theory fragFuelPackage
Ancestors
  fragFuel fragExec loweringShapeProps loweringShapeDefs vyperCompiler compileEnv
  moduleLowering
  venomExecSemantics venomInst list rich_list

(* ===== Blocks ===== *)

Theorem lookup_block_distinct_MEM[local]:
  !bbs bb. ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\ MEM bb bbs ==>
           lookup_block bb.bb_label bbs = SOME bb
Proof
  Induct >> rw[lookup_block_def, FIND_thm] >> fs[lookup_block_def, MEM_MAP] >>
  metis_tac[]
QED

Theorem phi_prefix_length_no_phi[local]:
  !l. EVERY (\i. i.inst_opcode <> PHI) l ==> phi_prefix_length l = 0
Proof
  Cases >> simp[phi_prefix_length_def]
QED

Theorem cs_no_phi_all_blocks[local]:
  !st. cs_no_phi st ==>
       EVERY (\bb. EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions)
         (all_blocks st)
Proof
  simp[cs_no_phi_def, all_blocks_def, EVERY_REVERSE]
QED

Theorem no_phi_fn_of_blocks[local]:
  !fn bbs.
    (!bb. MEM bb fn.fn_blocks ==> MEM bb bbs) /\
    EVERY (\bb. EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions) bbs ==>
    no_phi_fn fn
Proof
  rw[no_phi_fn_def, EVERY_MEM] >> irule phi_prefix_length_no_phi >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem cs_no_phi_new_block[local]:
  !name st old s. new_block name st = (old, s) /\ cs_no_phi st ==> cs_no_phi s
Proof
  rw[new_block_def] >> fs[cs_no_phi_def]
QED

(* ===== One segment ===== *)

(* A closed fragment from st (at the start of an empty block) to st',
   whose blocks are exactly fn's: fn is fuel-stable from Kb + 1 blocks past
   its callees' bound. *)
Theorem fuel_stable_of_segment:
  !Wv st st' Kb G ctx fn.
    frag_fuel Wv {} {} st st' Kb /\ cs_extends st st' /\
    st.cs_current_insts = [] /\
    all_blocks st' = REVERSE st.cs_blocks ++ fn.fn_blocks /\
    ALL_DISTINCT (fn_labels fn) /\ no_phi_fn fn /\ callees_stable G ctx fn ==>
    fuel_stable (G + Kb + 1) ctx fn
Proof
  rpt strip_tac >>
  fs[cs_extends_def] >>
  qabbrev_tac `cur = <| bb_label := st'.cs_current_bb;
                        bb_instructions := st'.cs_current_insts |>` >>
  `fn.fn_blocks = REVERSE new ++ [cur]` by
    (qpat_x_assum `all_blocks _ = _` mp_tac >>
     simp[all_blocks_def, REVERSE_APPEND, Abbr `cur`] >>
     metis_tac[APPEND_11, APPEND_ASSOC]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by fs[fn_labels_def] >>
  `lookup_block st'.cs_current_bb fn.fn_blocks = SOME cur` by
    (`st'.cs_current_bb = cur.bb_label` by simp[Abbr `cur`] >>
     pop_assum SUBST1_TAC >> irule lookup_block_distinct_MEM >> simp[]) >>
  qspecl_then [`Wv`, `{}`, `st`, `st'`, `Kb`, `G`, `ctx`, `fn`] mp_tac
    fuel_stable_of_frag >>
  impl_tac >- (
    rpt conj_tac
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- (simp[fn_has_code_def, emitted_blocks_def, TAKE_LENGTH_APPEND] >>
        conj_tac
        >- (rpt strip_tac >> irule lookup_block_distinct_MEM >>
            qpat_x_assum `ALL_DISTINCT (MAP _ fn.fn_blocks)` mp_tac >>
            asm_rewrite_tac[] >> fs[])
        >> simp[Abbr `cur`])
    >- first_assum ACCEPT_TAC
    >- simp[]
    >- (qspec_then `new` strip_assume_tac SNOC_CASES >>
        gvs[REVERSE_SNOC, LAST_SNOC, Abbr `cur`])
    >- first_assum ACCEPT_TAC >>
    rpt strip_tac >> fs[at_point_def] >>
    `lookup_block st'.cs_current_bb (REVERSE new ++ [cur]) = SOME cur` by
      (qpat_x_assum `lookup_block _ fn.fn_blocks = _` mp_tac >>
       asm_rewrite_tac[]) >>
    fs[run_from_def] >>
    ONCE_REWRITE_TAC [exec_block_def] >>
    simp[get_instruction_def, Abbr `cur`]) >>
  simp[]
QED

(* ===== Internal functions ===== *)

Theorem compile_internal_fn_bodies_fuel:
  !fns P st r st'.
    compile_internal_fn_bodies fns st = (r, st') /\ shape_state st /\
    next_stable P /\ P st /\
    EVERY internal_fn_shape_ok fns /\
    EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors fns) /\
    EVERY (\(fn_lbl, cenv, params, has_ret_buf, is_nr, nkey, use_trans,
             is_view, is_ctor, imm_len, body, ret_type).
             ?Wv. fuel_okS P Wv {} {}
                    (compile_internal_function cenv params has_ret_buf is_nr
                       nkey use_trans is_view is_ctor imm_len body ret_type))
      fns /\
    cs_no_phi st ==>
    cs_no_phi st' /\
    ?segs. all_blocks st' = all_blocks st ++ FLAT segs /\
           LIST_REL internal_segment_ok (internal_fn_descriptors fns) segs /\
           EVERY (\seg. ?Kf. !G ctx fn.
                    fn.fn_blocks = seg /\ ALL_DISTINCT (fn_labels fn) /\
                    no_phi_fn fn /\ callees_stable G ctx fn ==>
                    fuel_stable (G + Kf) ctx fn) segs
Proof
  Induct_on `fns`
  >- (simp[compile_internal_fn_bodies_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `[]` >>
      simp[internal_fn_descriptors_def]) >>
  qx_gen_tac `h` >> PairCases_on `h` >>
  simp[Once compile_internal_fn_bodies_def, internal_fn_shape_ok_def,
       internal_fn_descriptors_def] >>
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `comp_ignore_bind (new_block name) m st` >>
  Cases_on `new_block name st` >>
  fs[comp_ignore_bind_def, comp_bind_def] >>
  rename1 `new_block name st = (old,s)` >>
  drule_all shape_state_new_block >> strip_tac >>
  drule_all cs_no_phi_new_block >> strip_tac >>
  `s.cs_current_bb = name /\ s.cs_current_insts = [] /\
   REVERSE s.cs_blocks = all_blocks st /\ s.cs_next_var = st.cs_next_var` by
    gvs[new_block_def, all_blocks_def] >>
  `P s` by metis_tac[next_stable_def, cs_extends_new_block, arithmeticTheory.LESS_EQ_REFL] >>
  fs[Abbr `m`, comp_bind_def] >>
  pairarg_tac >> fs[] >>
  rename1 `compile_internal_function _ _ _ _ _ _ _ _ _ _ _ s = (aa, t)` >>
  drule_all compile_internal_function_shape >>
  rewrite_tac[shape_step_def] >>
  disch_then drule >> simp[] >> strip_tac >>
  `cs_extends s t /\ s.cs_next_var <= t.cs_next_var /\ cs_no_phi t /\
   ?Kb. frag_fuel Wv {} {} s t Kb` by
    metis_tac[fuel_okS_def] >>
  `P t` by metis_tac[next_stable_def] >>
  gvs[comp_return_def] >>
  first_x_assum (qspecl_then [`P`, `t`, `st'`] mp_tac) >>
  impl_tac >- fs[] >> strip_tac >> simp[] >>
  drule_all internal_segment_new_block >>
  disch_then (qspecl_then [`h3`, `h1.ce_returns_count`] strip_assume_tac) >>
  qexists_tac `seg :: segs` >>
  simp[internal_fn_descriptors_def, APPEND_ASSOC] >>
  qexists_tac `Kb + 1` >> rpt strip_tac >>
  `G + (Kb + 1) = G + Kb + 1` by decide_tac >> pop_assum SUBST1_TAC >>
  irule fuel_stable_of_segment >> simp[] >>
  qexistsl_tac [`Wv`, `s`, `t`] >> simp[]
QED

(* ===== The extracted context ===== *)

Theorem extract_context_fuel_stable:
  !pre P0 P lbl ifns a mid r st1 ctx data Wv.
    pre (initial_compile_state lbl) = (a, mid) /\
    fuel_okS P0 Wv {} {} pre /\ P0 (initial_compile_state lbl) /\
    next_stable P /\ P mid /\
    shape_state mid /\ EVERY internal_fn_shape_ok ifns /\
    EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ifns) /\
    ALL_DISTINCT (MAP FST (internal_fn_descriptors ifns)) /\
    EVERY (\d. ~compiler_label (FST d) /\
               ~MEM (FST d) (MAP (\bb. bb.bb_label) (all_blocks mid)))
      (internal_fn_descriptors ifns) /\
    EVERY (\(fn_lbl, cenv, params, has_ret_buf, is_nr, nkey, use_trans,
             is_view, is_ctor, imm_len, body, ret_type).
             ?Wv. fuel_okS P Wv {} {}
                    (compile_internal_function cenv params has_ret_buf is_nr
                       nkey use_trans is_view is_ctor imm_len body ret_type))
      ifns /\
    compile_internal_fn_bodies ifns mid = (r, st1) /\
    extract_context_with_internals lbl ifns st1 = SOME (ctx, data) /\
    EVERY (\fn. ALL_DISTINCT (fn_labels fn)) ctx.ctx_functions ==>
    !fn. MEM fn ctx.ctx_functions ==>
         ?Kf. !G. callees_stable G ctx fn ==> fuel_stable (G + Kf) ctx fn
Proof
  rpt gen_tac >> strip_tac >>
  `cs_no_phi (initial_compile_state lbl)` by
    simp[cs_no_phi_def, initial_compile_state_def] >>
  `cs_extends (initial_compile_state lbl) mid /\ cs_no_phi mid /\
   ?Kb. frag_fuel Wv {} {} (initial_compile_state lbl) mid Kb` by
    metis_tac[fuel_okS_def] >>
  qspecl_then [`ifns`, `P`, `mid`, `r`, `st1`] mp_tac compile_internal_fn_bodies_fuel >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all package_internal_blocks_segments >> strip_tac >>
  qpat_x_assum `extract_context_with_internals _ _ _ = _` mp_tac >>
  simp[extract_context_with_internals_def, GSYM all_blocks_def] >>
  strip_tac >> gvs[] >>
  `EVERY (\fn. ALL_DISTINCT (fn_labels fn))
     (mk_venom_context
        (mk_raw_function lbl (all_blocks mid) ::
         MAP2 (\d seg. mk_internal_function (FST d) seg (FST (SND d))
                         (SND (SND d))) (internal_fn_descriptors ifns) segs)
        (SOME lbl)).ctx_functions` by
    fs[] >>
  drule cs_no_phi_all_blocks >> strip_tac >>
  rpt strip_tac >> fs[EVERY_MEM] >>
  first_x_assum drule >> strip_tac >>
  fs[mk_venom_context_def]
  >- (
    (* the entry function *)
    qexists_tac `Kb + 1` >> rpt strip_tac >>
    `G + (Kb + 1) = G + Kb + 1` by decide_tac >> pop_assum SUBST1_TAC >>
    qpat_x_assum `fn = _` SUBST_ALL_TAC >>
    `no_phi_fn (mk_raw_function lbl (all_blocks mid))` by (
      irule no_phi_fn_of_blocks >> qexists_tac `all_blocks st1` >>
      gvs[mk_raw_function_def, EVERY_MEM] >> metis_tac[MEM_APPEND]) >>
    `all_blocks mid = REVERSE (initial_compile_state lbl).cs_blocks ++
                      (mk_raw_function lbl (all_blocks mid)).fn_blocks /\
     (initial_compile_state lbl).cs_current_insts = []` by
      simp[initial_compile_state_def, mk_raw_function_def] >>
    irule fuel_stable_of_segment >> metis_tac[]) >>
  (* an internal function *)
  `LENGTH segs = LENGTH (internal_fn_descriptors ifns)` by
    metis_tac[LIST_REL_LENGTH] >>
  qpat_x_assum `MEM fn (MAP2 _ _ _)` mp_tac >>
  simp[MEM_EL, LENGTH_MAP2] >> strip_tac >>
  `fn.fn_blocks = EL n segs` by gvs[EL_MAP2, mk_internal_function_metadata] >>
  `MEM (EL n segs) segs` by metis_tac[MEM_EL] >>
  qpat_x_assum `!seg. MEM seg segs ==> _` drule >> strip_tac >>
  qexists_tac `Kf` >> rpt strip_tac >> first_x_assum irule >> fs[] >>
  irule no_phi_fn_of_blocks >> qexists_tac `all_blocks st1` >>
  gvs[EVERY_MEM, MEM_FLAT] >> metis_tac[MEM_EL]
QED
