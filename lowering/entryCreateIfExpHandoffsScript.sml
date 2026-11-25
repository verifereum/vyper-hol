(* Administrative PCs and the native suffix after a selected branch. *)
Theory entryCreateIfExpHandoffs
Ancestors
  entryCreateIfExpAdmin entryCreateNativeFirstExit
  entryCreateFocusSpec fragGasOrigin createSizePrefixReplay createSizeCutRegion
  fragExec emitHelperProps venomExecProofs venomExecSemantics venomInst venomState
  dftGasFromListTraceDefs relation pair list

Triviality emit_pc_fetch:
  emit_inst opc ops outs x = ((),y) /\ fn_has_code x y f /\
  create_operand_at x s /\ ~create_operand_at b s /\
  x.cs_next_id IN frag_ids a b ==>
  create_operand_fetch a b f s (mk_inst x.cs_next_id opc ops outs)
Proof
  strip_tac >> drule emit_inst_extends >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >>
  fs[create_operand_at_def, create_operand_fetch_def, mk_inst_def] >> metis_tac[]
QED

Triviality ifexp_assign_native_endpoint:
  create_operand_fetch a b f s (mk_inst id ASSIGN [op] [rv]) /\
  create_operand_native_step a b E C f p (d,k,s,left) (d',k',v,right) ==>
  ?w. eval_operand op s = SOME w /\
      v = (update_var rv w s) with vs_inst_idx := SUC s.vs_inst_idx
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ASSIGN [op] [rv]) s =
     (case eval_operand op s of SOME w => OK (update_var rv w s)
                                | NONE => Error "undefined operand")` by
    simp[mk_inst_def, Once step_inst_base_def] >>
  fs[create_operand_native_step_def, LET_THM, create_operand_fetch_def,
     create_prefix_step_def, gas_origin_edge_def] >>
  gvs[step_inst_non_invoke, is_terminator_def, mk_inst_def] >>
  Cases_on `eval_operand op s` >> gvs[exit_result_def]
QED

Theorem ifexp_admin_pc_handoffs:
  (!a b sc sj sn se cop tl el sel f s.
     emit_inst JNZ [cop; Label tl; Label el] [] sj = ((),sn) /\
     fn_has_code sj sn f /\ sj.cs_current_bb = sc.cs_current_bb /\
     sj.cs_current_insts = sc.cs_current_insts /\ create_operand_at sc s /\
     ~create_operand_at b s /\ sj.cs_next_id IN frag_ids a b /\
     se.cs_current_bb = (if sel then tl else el) /\ se.cs_current_insts = [] ==>
     let i = mk_inst sj.cs_next_id JNZ [cop; Label tl; Label el] [] in
     let t = jump_to (if sel then tl else el) s in
       create_operand_fetch a b f s i /\ create_operand_at se t /\
       (eval_operand cop s = SOME (if sel then 1w else 0w) ==>
        step_inst_base i s = OK t /\
        (!E C. ~s.vs_halted ==> create_prefix_step a b E C f s [] t) /\
        ((!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) ==>
         !E C p d k left d' k' v right.
           create_operand_native_step a b E C f p (d,k,s,left) (d',k',v,right) ==>
           v = t))) /\
  (!a b sx sy op rv f s.
     emit_inst ASSIGN [op] [rv] sx = ((),sy) /\ fn_has_code sx sy f /\
     create_operand_at sx s /\ ~create_operand_at b s /\ sx.cs_next_id IN frag_ids a b ==>
       create_operand_fetch a b f s (mk_inst sx.cs_next_id ASSIGN [op] [rv]) /\
       (!w. eval_operand op s = SOME w ==>
        let t = (update_var rv w s) with vs_inst_idx := SUC s.vs_inst_idx in
          create_operand_at sy t /\
          (!E C. ~s.vs_halted ==> create_prefix_step a b E C f s [] t)) /\
       (!E C p d k left d' k' v right.
          create_operand_native_step a b E C f p (d,k,s,left) (d',k',v,right) ==>
          create_operand_at sy v /\
          ?w. eval_operand op s = SOME w /\
              v = (update_var rv w s) with vs_inst_idx := SUC s.vs_inst_idx)) /\
  (!a b sy sz z xl f s.
     emit_inst JMP [Label xl] [] sy = ((),sz) /\ fn_has_code sy sz f /\
     create_operand_at sy s /\ ~create_operand_at b s /\ sy.cs_next_id IN frag_ids a b /\
     z.cs_current_bb = xl /\ z.cs_current_insts = [] ==>
     let i = mk_inst sy.cs_next_id JMP [Label xl] [] in
     let t = jump_to xl s in
       create_operand_fetch a b f s i /\ create_operand_at z t /\
       step_inst_base i s = OK t /\
       (!E C. ~s.vs_halted ==> create_prefix_step a b E C f s [] t) /\
       ((!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) ==>
        !E C p d k left d' k' v right.
          create_operand_native_step a b E C f p (d,k,s,left) (d',k',v,right) ==>
          v = t))
Proof
  conj_tac
  >- (simp_tac bool_ss [LET_THM] >> rpt gen_tac >> strip_tac >>
      `create_operand_at sj s` by fs[create_operand_at_def] >>
      `create_operand_fetch a b f s (mk_inst sj.cs_next_id JNZ [cop; Label tl; Label el] [])`
        by metis_tac[emit_pc_fetch] >>
      `create_operand_at se (jump_to (if sel then tl else el) s)` by
        simp[create_operand_at_def, jump_to_def] >>
      simp[] >> strip_tac >>
      `step_inst_base (mk_inst sj.cs_next_id JNZ [cop; Label tl; Label el] []) s =
       OK (jump_to (if sel then tl else el) s)` by
        (drule venomExecProofsTheory.step_jnz_behavior >>
         disch_then (qspecl_then [`tl`,`el`,`sj.cs_next_id`] mp_tac) >>
         Cases_on `sel` >> simp[mk_inst_def]) >>
      `(mk_inst sj.cs_next_id JNZ [cop; Label tl; Label el] []).inst_opcode = JNZ`
        by simp[mk_inst_def] >>
      simp[] >> metis_tac[ifexp_jump_edge, ifexp_jump_native_endpoint]) >>
  conj_tac
  >- (simp_tac bool_ss [LET_THM] >> rpt gen_tac >> strip_tac >>
      `create_operand_fetch a b f s (mk_inst sx.cs_next_id ASSIGN [op] [rv])`
        by metis_tac[emit_pc_fetch] >>
      drule emit_inst_extends >> strip_tac >>
      `!w. create_operand_at sy ((update_var rv w s) with vs_inst_idx := SUC s.vs_inst_idx)`
        by fs[create_operand_at_def, update_var_def, arithmeticTheory.ADD1] >>
      simp[] >> metis_tac[ifexp_assign_edge, ifexp_assign_native_endpoint]) >>
  simp_tac bool_ss [LET_THM] >> rpt gen_tac >> strip_tac >>
  `create_operand_fetch a b f s (mk_inst sy.cs_next_id JMP [Label z.cs_current_bb] [])`
    by metis_tac[emit_pc_fetch] >>
  `create_operand_at z (jump_to z.cs_current_bb s)` by simp[create_operand_at_def, jump_to_def] >>
  `step_inst_base (mk_inst sy.cs_next_id JMP [Label z.cs_current_bb] []) s =
   OK (jump_to z.cs_current_bb s)` by simp[mk_inst_def, step_jmp_behavior] >>
  `(mk_inst sy.cs_next_id JMP [Label z.cs_current_bb] []).inst_opcode = JMP` by simp[mk_inst_def] >>
  simp[] >> metis_tac[ifexp_jump_edge, ifexp_jump_native_endpoint]
QED

(* The supplied continuation keeps its final fetch and the parent/child
   classification of the hit. Only the completed accumulator is rebased. *)
Theorem ifexp_selected_jump_tail:
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  create_cut_code {} se b /\ fn_has_code se b f /\
  create_operand_at se s /\
  RTC (create_operand_native_step a b E ctx f p) (d,k,s,front) (d',k',u,whole) /\
  create_operand_fetch a b f u i ==>
  ?tail. whole = front ++ tail /\
    RTC (create_operand_native_step se b E ctx f p) (d,k,s,[]) (d',k',u,tail) /\
    create_operand_fetch se b f u i /\
    !before hit after.
      create_trace_from p d k ctx f s = before ++ hit::after /\
      (before = tail /\ hit = ((p,d',i.inst_id),f,i,u) \/
       ?inside suffix. before = tail ++ ((p,d',i.inst_id),f,i,u)::inside /\
                       trace_step p d' k' ctx f i u = inside ++ hit::suffix) ==>
      create_interior_visit se b E ctx f (p,d,k) s (before,hit,after)
Proof
  strip_tac >>
  `?tail. whole = front ++ tail /\ create_cut_region se b u /\
      RTC (create_operand_native_step se b E ctx f p) (d,k,s,[]) (d',k',u,tail)` by
    metis_tac[create_native_closed_suffix_rebase] >>
  `create_operand_fetch se b f u i` by
    (fs[create_operand_fetch_def, create_operand_at_def] >>
     metis_tac[cj 2 create_cut_region_rules]) >>
  qexists_tac `tail` >> simp[create_interior_visit_def, LET_THM] >>
  rpt strip_tac >> qexistsl_tac [`d'`,`k'`,`u`,`tail`,`i`] >> simp[] >> metis_tac[]
QED
