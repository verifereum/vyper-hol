(* Restore, halt and forwarding slices at the same bounded FMP cursor. *)
Theory gasFocusFmpCutControlSegments
Ancestors
  gasFocusFmpCutRestorePrefix gasFocusFmpCutHaltPoint
  gasFocusFmpCutForwardLayout gasFocusFmpCutForwardRun
  fmpStageRel o1PassContract contextCodegenRel venomExecProofs
  venomExecSemantics venomWf venomInst finite_map pred_set list

Theorem focus_fmp_cut_control_segments:
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
    (o1_walk_view rpolicy 3) C C' /\
  o1_ctx_shape C /\ o1_ctx_shape C' /\ EVERY (o1_fn_row 3) C.ctx_functions /\
  lookup_function fn.fn_name C.ctx_functions = SOME fn /\
  ssa_form fn /\ fn.fn_fmp_signature = NONE /\ opaque_use_ok fn /\
  raw0 = w2n vs.vs_fmp /\
  (!fn inst s. raw_reachable vs C fn inst s /\ gas_cut n vs s ==>
               dalloca_no_wrap inst s) /\
  frame_reachable vs C stk PG G tn fn inst s /\ gas_cut n vs s /\
  active_inst fn inst s /\ ~s.vs_halted /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  ptr_use_static_ok P (fn_pv P fn) inst /\ FDOM G SUBSET fn_pv P fn /\
  taint_ok fn tn inst s /\ taint_within_upto D n C vs /\ access_ok eom G fn inst s ==>
  ?fn' bb bb' infos ctx runner i d u cut.
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    fmp_stage_lowered infos ctx runner fn fn' /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    t.vs_current_bb = s.vs_current_bb /\
    i = t.vs_inst_idx /\
    i = fmp_stage_tidx (fmp_stage_plan infos ctx fn)
          (fmp_stage_root infos ctx fn) s.vs_current_bb
          bb.bb_instructions s.vs_inst_idx /\
    i < LENGTH bb'.bb_instructions /\
    u.vs_current_bb = t.vs_current_bb /\ u.vs_inst_idx = i + d /\
    i + d <= LENGTH bb'.bb_instructions /\ cut <= lo /\
    (!fuel. fmp_target_run fuel C' fn.fn_name t d u) /\
    (case FLOOKUP (fmp_stage_plan infos ctx fn)
       (s.vs_current_bb,s.vs_inst_idx) of
       NONE => d = 0 /\ u = t /\ cut = lo
     | SOME target => d = 1 /\ ?id value.
         EL i bb'.bb_instructions = mk_inst id ASSIGN [Var target] [runner] /\
         lookup_var target t = SOME value /\
         u = (update_var runner value t) with vs_inst_idx := SUC i) /\
    fmp_stage_rel D C'
      (DRESTRICT sm {key | key IN FDOM sm /\ FST (sm ' key) < cut})
      fmp0 raw0 eom T stk PG G tn fn s cut u ts /\
    (MEM inst.inst_opcode [STOP; RETURN; REVERT; SINK; SELFDESTRUCT; INVALID] ==>
     active_inst fn' inst u /\
     !fuel r. step_inst fuel C inst s = r /\ terminates r ==>
       ?r'. step_inst fuel C' inst u = r' /\
         case r of
           OK s1 => s1.vs_halted /\
                    ?u1. r' = OK u1 /\ u1.vs_halted /\
                         dead_result_rel D (Halt s1) (Halt u1)
         | Halt s1 => dead_result_rel D r r'
         | Abort ab s1 => dead_result_rel D r r'
         | _ => F) /\
    (!j. revert_forward_pair bb s.vs_inst_idx j ==>
      d = 0 /\ u = t /\ cut = lo /\
      revert_forward_pair bb' i (i + (j - s.vs_inst_idx)) /\
      (!fuel h trace.
        h <= j - s.vs_inst_idx /\ trace 0 = s /\
        (!k. k < h ==>
             ?ii r. get_instruction bb (s.vs_inst_idx+k) = SOME ii /\
                    step_inst fuel C ii (trace k) = OK r /\
                    trace (SUC k) = r with vs_inst_idx := s.vs_inst_idx + SUC k) ==>
        ?U. U 0 = t /\
            (!k. k <= h ==> (U k).vs_current_bb = t.vs_current_bb /\
                 (U k).vs_inst_idx = i+k /\
                 ?ii. get_instruction bb (s.vs_inst_idx+k) = SOME ii /\
                      get_instruction bb' (U k).vs_inst_idx = SOME ii /\
                      (k = 0 ==> ii = inst) /\
                      (0 < k /\ k < j - s.vs_inst_idx ==> ii.inst_opcode = ASSIGN) /\
                      (k = j - s.vs_inst_idx ==> ii.inst_opcode = REVERT)) /\
            (!k. k < h ==>
                 ?ii r. get_instruction bb' (U k).vs_inst_idx = SOME ii /\
                        ~is_terminator ii.inst_opcode /\
                        step_inst fuel C' ii (U k) = OK r /\
                        U (SUC k) = r with vs_inst_idx := i + SUC k)) /\
      (!fuel reason se. exec_block fuel C bb s = Abort reason se ==>
           ?te. exec_block fuel C' bb' t = Abort reason te))
Proof
  strip_tac >>
  `wf_function fn /\ o1_fn_row 3 fn` by
    metis_tac[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM,
              venomInstTheory.lookup_function_MEM] >>
  `make_ssa_input_ok fn` by fs[o1_fn_row_def] >>
  `t.vs_current_bb = s.vs_current_bb` by fs[fmp_stage_rel_def, fmp_frame_rel_def] >>
  drule_all focus_fmp_cut_restore_prefix >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME inst` by
    (fs[active_inst_def] >>
     `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
       fs[wf_function_def, fn_labels_def] >>
     `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb''` by
       (irule MEM_lookup_block >> simp[]) >>
     gvs[get_instruction_def]) >>
  qexistsl [`fn'`, `bb`, `bb'`, `infos`, `ctx`, `runner`, `i`, `d`, `u`, `cut`] >>
  asm_rewrite_tac[] >> conj_tac >- simp[] >>
  conj_tac
  >- (disch_tac >> drule_all focus_fmp_cut_halt_point >> metis_tac[]) >>
  gen_tac >> disch_tac >>
  drule_all focus_fmp_cut_forward_layout >> simp[NoAsms] >> strip_tac >>
  `bb'' = bb'` by metis_tac[optionTheory.SOME_11] >>
  `FLOOKUP (fmp_stage_plan infos ctx fn) (s.vs_current_bb,s.vs_inst_idx) = NONE` by
    (qpat_assum `!h. _ ==> (_,_) NOTIN FDOM (fmp_stage_plan infos ctx fn) /\ _`
       (qspec_then `0` (assume_tac o CONJUNCT1 o SIMP_RULE (srw_ss()) [])) >>
     simp[FLOOKUP_DEF]) >>
  `d = 0 /\ u = t /\ cut = lo` by fs[] >>
  `?dst src sz. inst.inst_opcode = RETURNDATACOPY /\
                inst.inst_operands = [dst;src;sz]` by
    (qpat_assum `revert_forward_pair bb s.vs_inst_idx j`
       (strip_assume_tac o REWRITE_RULE [revert_forward_pair_def]) >>
     gvs[]) >>
  `fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
     s.vs_current_bb bb.bb_instructions s.vs_inst_idx = t.vs_inst_idx` by metis_tac[] >>
  `!k. k <= j - s.vs_inst_idx ==>
       get_instruction bb' (t.vs_inst_idx+k) = get_instruction bb (s.vs_inst_idx+k)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!h. _ ==> (_,_) NOTIN FDOM (fmp_stage_plan infos ctx fn) /\ _`
       (drule_then (mp_tac o CONJUNCT2 o CONJUNCT2)) >>
     asm_rewrite_tac[] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  drule_all focus_fmp_cut_forward_run >> asm_rewrite_tac[] >> simp[NoAsms] >>
  strip_tac >> conj_tac
  >- (qpat_x_assum `revert_forward_pair bb'' (fmp_stage_tidx _ _ _ _ _) _` mp_tac >>
      asm_rewrite_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> first_assum (qspecl_then [`fuel`,`C`,`h`,`trace`] ACCEPT_TAC)) >>
  rpt gen_tac >> first_assum (qspecl_then [`fuel`,`C`,`reason`,`se`] ACCEPT_TAC)
QED
