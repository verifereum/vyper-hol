(* Relative layout and the actual control transfers at a selected IfExp. *)
Theory entryCreateIfExpLayout
Ancestors
  bodyFullIfExpShadow entryCreateIntervalLayout entryCreateIfExpHandoffs
  entryCreateIfExpFinishVisit entryCreateIfExpAdmin createSizeOperandCode createSizeExprBodyCode
  createSizeTypedCopyCode createSizeCutOpens createSizeCutRegion
  createSizeLocationCode createSizeCutCode exprLowering
  abiEncoderProps emitHelperProps externalEntryShape fragExec arithmetic pred_set list pair
  compileEnv entryCreateFocusSpec venomInst venomExecSemantics venomState

Triviality ifexp_arm_closed:
  compile_ifexp_arm ce rt aty av a = (op,b) ==> create_cut_code {} a b
Proof
  disch_then (SUBST1_TAC o SYM o SIMP_RULE std_ss [SND] o AP_TERM ``SND : operand # compile_state -> compile_state``) >>
  simp_tac std_ss [compile_ifexp_arm_def] >> IF_CASES_TAC
  >- simp[create_unwrap_cut_code] >>
  rpt (FIRST [match_mp_tac create_cut_code_bind >> conj_tac >> BETA_TAC,
              match_mp_tac create_cut_code_ignore_bind >> conj_tac >> BETA_TAC,
              CHANGED_TAC (simp[create_alloc_buffer_cut_code, create_unwrap_cut_code,
                                create_store_memory_cut_code])])
QED

Triviality cut_code_extends:
  create_cut_code A a b ==> cs_extends a b
Proof
  simp[create_cut_code_def]
QED

Triviality ifexp_emit_cut:
  emit_inst opc ops outs a = ((),b) /\
  (!l. MEM l (create_cut_targets opc ops) ==> l IN exits) ==>
  create_cut_code exits a b
Proof
  strip_tac >>
  `b = SND (emit_inst opc ops outs a)` by simp[] >>
  pop_assum SUBST1_TAC >> irule create_cut_code_emit_inst >> simp[]
QED

Triviality ifexp_else_suffix:
  create_cut_code {} a m /\ create_cut_code {} m x /\
  emit_inst ASSIGN [op] [rv] x = ((),y) /\
  emit_inst JMP [Label j] [] y = ((),h) /\ new_block j h = (r,z) ==>
  create_cut_code {} a z /\ create_cut_code {} m z /\ create_cut_code {} x z
Proof
  strip_tac >>
  `create_cut_code {j} x y /\ create_cut_code {j} y h` by
    (conj_tac >> irule ifexp_emit_cut
     >- (qexistsl_tac [`ASSIGN`,`[op]`,`[rv]`] >> simp[create_cut_targets_def]) >>
     qexistsl_tac [`JMP`,`[Label j]`,`[]`] >> simp[create_cut_targets_def]) >>
  `create_cut_code {j} h z` by metis_tac[create_cut_code_new_block, SND] >>
  `create_cut_code {j} a m /\ create_cut_code {j} m x` by
    metis_tac[create_cut_code_weaken, EMPTY_SUBSET] >>
  `create_cut_code {j} x h /\ create_cut_code {j} m h /\ create_cut_code {j} a h`
    by metis_tac[create_cut_code_join] >>
  `cs_extends x h /\ cs_extends m h /\ cs_extends a h /\ cs_extends h z`
    by metis_tac[cut_code_extends] >>
  `added_labels h z = [j]` by metis_tac[added_labels_new_block] >>
  rpt conj_tac >> irule create_cut_code_close >> qexists_tac `{j}` >>
  simp[] >> metis_tac[create_cut_code_join, added_labels_trans, MEM_APPEND, MEM]
QED

Triviality ifexp_branch_suffixes:
  create_cut_code {} st sc /\ create_cut_code {} sc sj /\
  emit_inst JNZ [cop; Label tl; Label el] [] sj = ((),sn) /\
  new_block tl sn = (r1,ta) /\ create_cut_code {} ta tm /\ create_cut_code {} tm tx /\
  emit_inst ASSIGN [top] [rv] tx = ((),ty) /\
  emit_inst JMP [Label xl] [] ty = ((),tz) /\
  new_block el tz = (r2,ea) /\ create_cut_code {} ea em /\ create_cut_code {} em ex /\
  emit_inst ASSIGN [eop] [rv] ex = ((),ey) /\
  emit_inst JMP [Label xl] [] ey = ((),ez) /\
  new_block xl ez = (r3,z) ==>
  create_cut_code {} sc z /\
  (if sel then create_cut_code {} ta z /\ create_cut_code {} tm z /\ create_cut_code {} tx z
          else create_cut_code {} ea z /\ create_cut_code {} em z /\ create_cut_code {} ex z)
Proof
  strip_tac >>
  `create_cut_code {} ta tx /\ create_cut_code {} ea ex`
    by metis_tac[create_cut_code_join] >>
  drule_all_then strip_assume_tac ifexp_selected_closed_suffixes >>
  conj_tac >- metis_tac[create_cut_code_join] >>
  Cases_on `sel` >> simp[]
  >- metis_tac[create_cut_code_join] >>
  irule ifexp_else_suffix >> metis_tac[]
QED

Triviality ifexp_interval_geometry:
  !st a m z f. cs_extends st a /\ cs_extends a m /\ cs_extends m z /\
  create_layout st z /\ fn_has_code st z f /\
  st.cs_next_id <= a.cs_next_id /\ m.cs_next_id <= z.cs_next_id ==>
  create_layout a m /\ fn_has_code a m f /\ fn_has_code a z f /\
  frag_ids a m SUBSET frag_ids st z /\ frag_ids a m SUBSET frag_ids a z /\
  (!u. create_cut_region a m u /\ ~create_operand_at m u ==> ~create_operand_at z u)
Proof
  rpt gen_tac >> strip_tac >>
  `cs_extends a z` by metis_tac[cs_extends_trans] >>
  `create_layout a z` by metis_tac[create_layout_subinterval, cs_extends_refl] >>
  conj_tac >- metis_tac[create_layout_subinterval] >>
  conj_tac >- metis_tac[fn_has_code_mid] >>
  conj_tac >- metis_tac[fn_has_code_mid, cs_extends_refl] >>
  conj_tac >- (simp[frag_ids_def, SUBSET_DEF] >> decide_tac) >>
  conj_tac >- (simp[frag_ids_def, SUBSET_DEF] >> decide_tac) >>
  metis_tac[create_layout_left_stop]
QED

Triviality ifexp_emit_geometry:
  !st a b z opc ops outs. cs_extends st a /\ cs_extends b z /\ create_layout st z /\
  st.cs_next_id <= a.cs_next_id /\ b.cs_next_id <= z.cs_next_id /\
  emit_inst opc ops outs a = ((),b) ==>
  a.cs_next_id IN frag_ids a z /\ a.cs_next_id IN frag_ids st z /\
  !u. create_operand_at a u ==> ~create_operand_at z u
Proof
  rpt gen_tac >> strip_tac >>
  `cs_extends a b` by metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends a z` by metis_tac[cs_extends_trans] >>
  `create_layout a z` by metis_tac[create_layout_subinterval, cs_extends_refl] >>
  drule_then strip_assume_tac emit_inst_extends >>
  conj_tac >- (simp[frag_ids_def] >> decide_tac) >>
  conj_tac >- (simp[frag_ids_def] >> decide_tac) >>
  rpt strip_tac >>
  `create_cut_region a b u /\ ~create_operand_at b u` by
    (fs[create_cut_region_def,create_operand_at_def] >> simp[]) >>
  metis_tac[create_layout_left_stop]
QED

Triviality ifexp_narrow_finish_admin:
  emit_inst ASSIGN [op] [rv] x = ((),y) /\
  emit_inst JMP [Label j] [] y = ((),h) /\
  fn_has_code x y f /\ fn_has_code y h f /\
  x.cs_next_id IN frag_ids x z /\ y.cs_next_id IN frag_ids x z /\
  z.cs_current_bb = j /\ z.cs_current_insts = [] /\
  (!u. create_operand_at x u ==> ~create_operand_at z u) /\
  (!u. create_operand_at y u ==> ~create_operand_at z u) /\
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) ==>
  (!u inst. create_operand_fetch x z f u inst ==>
    (create_operand_at x u ==> inst.inst_opcode = ASSIGN) /\
    (create_operand_at y u ==> inst.inst_opcode = JMP)) /\
  (!E C p d0 k0 u left d1 k1 v right.
    create_operand_native_step x z E C f p (d0,k0,u,left) (d1,k1,v,right) ==>
    (create_operand_at x u ==> create_operand_at y v) /\
    (create_operand_at y u ==> create_operand_at z v))
Proof
  strip_tac >>
  `!s. create_operand_at x s ==>
    create_operand_fetch x z f s (mk_inst x.cs_next_id ASSIGN [op] [rv]) /\
    (!E C p d k left d' k' v right.
      create_operand_native_step x z E C f p (d,k,s,left) (d',k',v,right) ==>
      create_operand_at y v)` by
    (gen_tac >> disch_tac >>
     `~create_operand_at z s` by metis_tac[] >>
     drule_all (CONJUNCT1 (CONJUNCT2 ifexp_admin_pc_handoffs)) >> metis_tac[]) >>
  `!s. create_operand_at y s ==>
    create_operand_fetch x z f s (mk_inst y.cs_next_id JMP [Label j] []) /\
    create_operand_at z (jump_to j s) /\
    (!E C p d k left d' k' v right.
      create_operand_native_step x z E C f p (d,k,s,left) (d',k',v,right) ==>
      v = jump_to j s)` by
    (gen_tac >> disch_tac >>
     `~create_operand_at z s` by metis_tac[] >>
     drule_all (CONJUNCT2 (CONJUNCT2 ifexp_admin_pc_handoffs)) >>
     simp[LET_THM] >> metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >> conj_tac >> disch_tac
      >- (`create_operand_fetch x z f u (mk_inst x.cs_next_id ASSIGN [op] [rv])` by metis_tac[] >>
          fs[create_operand_fetch_def] >> gvs[mk_inst_def]) >>
      `create_operand_fetch x z f u (mk_inst y.cs_next_id JMP [Label j] [])` by metis_tac[] >>
      fs[create_operand_fetch_def] >> gvs[mk_inst_def]) >>
  metis_tac[]
QED

Theorem ifexp_finish_visit_disjoint:
  emit_inst ASSIGN [op] [rv] x = ((),y) /\
  emit_inst JMP [Label j] [] y = ((),h) /\
  fn_has_code x y f /\ fn_has_code y h f /\
  x.cs_next_id IN frag_ids x z /\ y.cs_next_id IN frag_ids x z /\
  z.cs_current_bb = j /\ z.cs_current_insts = [] /\
  (!u. create_operand_at x u ==> ~create_operand_at z u) /\
  (!u. create_operand_at y u ==> ~create_operand_at z u) /\
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  create_interior_visit x z E C f (p,d,k) s (before,hit,after) ==>
  ?d' u inst. hit = ((p,d',inst.inst_id),f,inst,u) /\
              (inst.inst_opcode = ASSIGN \/ inst.inst_opcode = JMP)
Proof
  strip_tac >> drule_all_then strip_assume_tac ifexp_narrow_finish_admin >>
  drule_at (Pos last) ifexp_two_pc_finish_visit >>
  disch_then (qspec_then `y` mp_tac) >>
  (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> metis_tac[])) >>
  metis_tac[]
QED

Triviality ifexp_closed_open_label:
  cs_extends h z /\ h.cs_blocks <> z.cs_blocks /\ create_layout h z ==>
  h.cs_current_bb <> z.cs_current_bb
Proof
  strip_tac >> qpat_x_assum `cs_extends h z` mp_tac >>
  simp_tac std_ss [cs_extends_def] >> strip_tac >>
  `new <> []` by (strip_tac >> fs[]) >>
  `emitted_blocks h z = new` by metis_tac[emitted_blocks_append] >>
  fs[create_layout_def] >>
  `MEM (LAST new).bb_label (MAP (\bb. bb.bb_label) new)` by
    (simp[MEM_MAP] >> qexists_tac `LAST new` >> simp[rich_listTheory.MEM_LAST_NOT_NIL]) >>
  metis_tac[]
QED

(* The same compiler witnesses serve the outcome and native-visit clients. *)
Theorem ifexp_selected_cut_handoffs:
  compile_expr cenv ty (IfExp t c a b) st = (vv,z) /\
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr (IfExp t c a b)) shst = (vv,shz) /\
  gas_shadow_state st shst /\ fn_has_code st z f /\ fn_has_code shst shz shf /\
  local_ptrs_reserved cenv st /\
  (!ty' e. gas_shadow_compiles (compile_expr cenv ty' e)
             (compile_expr (gas_shadow_env T cenv) ty' (gas_shadow_expr e))) /\
  (!ty' e. gas_shadow_compiles (lower_value compile_expr cenv ty' e)
             (lower_value compile_expr (gas_shadow_env T cenv) ty' (gas_shadow_expr e))) /\
  (!rt at av. gas_shadow_compiles (compile_ifexp_arm cenv rt at av)
                (compile_ifexp_arm (gas_shadow_env T cenv) rt at av)) /\
  create_layout st z ==>
  ?cop sc shsc sj sn tl el xl rv se shse av m shm op x y h.
    lower_value compile_expr cenv (BaseT BoolT) c st = (cop,sc) /\
    lower_value compile_expr (gas_shadow_env T cenv) (BaseT BoolT) (gas_shadow_expr c)
      shst = (cop,shsc) /\ gas_shadow_state sc shsc /\
    emit_inst JNZ [cop; Label tl; Label el] [] sj = ((),sn) /\
    sj.cs_current_bb = sc.cs_current_bb /\ sj.cs_current_insts = sc.cs_current_insts /\
    compile_expr cenv ty (if sel then a else b) se = (av,m) /\
    compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr (if sel then a else b)) shse = (av,shm) /\
    gas_shadow_state se shse /\ gas_shadow_state m shm /\
    compile_ifexp_arm cenv t (lowered_value_type cenv (if sel then a else b)) av m = (op,x) /\
    emit_inst ASSIGN [op] [rv] x = ((),y) /\ emit_inst JMP [Label xl] [] y = ((),h) /\
    se.cs_current_bb = (if sel then tl else el) /\ se.cs_current_insts = [] /\
    z.cs_current_bb = xl /\ z.cs_current_insts = [] /\
    vv = (if is_word_type t then StackValue t (Var rv)
          else LocatedValue t (mk_ptr (Var rv) LocMemory)) /\
    fn_has_code shst shsc shf /\ fn_has_code shse shm shf /\
    local_ptrs_reserved cenv se /\ (!v. not_fresh_at st v ==> v <> rv) /\
    st.cs_next_var <= sc.cs_next_var /\ sc.cs_next_var <= se.cs_next_var /\
    se.cs_next_var <= m.cs_next_var /\
    create_cut_code {} st sc /\ create_cut_code {} se m /\ create_cut_code {} m x /\
    create_cut_code {} sc z /\ create_cut_code {} se z /\
    create_cut_code {} m z /\ create_cut_code {} x z /\
    fn_has_code st sc f /\ fn_has_code sc z f /\ fn_has_code se m f /\
    fn_has_code se z f /\ fn_has_code m x f /\ fn_has_code m z f /\ fn_has_code x z f /\
    fn_has_code sj sn f /\ fn_has_code x y f /\ fn_has_code y h f /\
    create_layout st sc /\ create_layout se m /\ create_layout m x /\
    frag_ids st sc SUBSET frag_ids st z /\
    frag_ids se m SUBSET frag_ids st z /\ frag_ids se m SUBSET frag_ids se z /\
    frag_ids m x SUBSET frag_ids st z /\ frag_ids m x SUBSET frag_ids m z /\
    (!u. create_cut_region st sc u /\ ~create_operand_at sc u ==> ~create_operand_at z u) /\
    (!u. create_cut_region se m u /\ ~create_operand_at m u ==> ~create_operand_at z u) /\
    (!u. create_cut_region m x u /\ ~create_operand_at x u ==> ~create_operand_at z u) /\
    (!u. create_operand_at sc u ==> ~create_operand_at z u) /\
    (!u. create_operand_at x u ==> ~create_operand_at z u) /\
    (!u. create_operand_at y u ==> ~create_operand_at z u) /\
    sj.cs_next_id IN frag_ids sc z /\ x.cs_next_id IN frag_ids x z /\
    y.cs_next_id IN frag_ids x z /\ h.cs_next_id <= z.cs_next_id /\
    x.cs_current_bb <> xl /\
    (!E C u w. create_operand_at x u /\ ~u.vs_halted /\ eval_operand op u = SOME w ==>
      create_operand_full_scope x z E C f u []
        (OK (jump_to xl ((update_var rv w u) with vs_inst_idx := LENGTH y.cs_current_insts)))) /\
    (!u. create_operand_at sc u ==>
      let i = mk_inst sj.cs_next_id JNZ [cop; Label tl; Label el] [] in
      let v = jump_to (if sel then tl else el) u in
      create_operand_fetch sc z f u i /\ create_operand_at se v /\
      (eval_operand cop u = SOME (if sel then 1w else 0w) ==>
        step_inst_base i u = OK v /\
        (!E C. ~u.vs_halted ==> create_prefix_step sc z E C f u [] v) /\
        ((!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) ==>
         !E C p d k left d' k' v' right.
           create_operand_native_step sc z E C f p (d,k,u,left) (d',k',v',right) ==>
           v' = v))) /\
    (!E C p d k s before hit after.
      (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
      create_interior_visit x z E C f (p,d,k) s (before,hit,after) ==>
      ?d' u inst. hit = ((p,d',inst.inst_id),f,inst,u) /\
                  (inst.inst_opcode = ASSIGN \/ inst.inst_opcode = JMP))
Proof
  strip_tac >> drule_all ifexp_shadow_code_layout_chain >>
  disch_then (qspec_then `sel` (qx_choosel_then
    [`cop`,`sc`,`shsc`,`sj`,`sn`,`tl`,`el`,`xl`,`rv`,`se`,`shse`,`av`,`m`,`shm`,`op`,`x`,`y`,`h`]
    strip_assume_tac)) >>
  qexistsl_tac [`cop`,`sc`,`shsc`,`sj`,`sn`,`tl`,`el`,`xl`,`rv`,`se`,`shse`,`av`,`m`,`shm`,`op`,`x`,`y`,`h`] >>
  simp_tac bool_ss [LET_THM] >>
  `create_cut_code {} st sc /\ create_cut_code {} se m /\ create_cut_code {} m x` by
    metis_tac[create_operand_cut_code, ifexp_arm_closed, SND] >>
  `create_cut_code {} sc z /\ create_cut_code {} se z /\ create_cut_code {} m z /\
   create_cut_code {} x z` by suspend "suffixes" >>
  suspend "handoffs"
QED

Resume ifexp_selected_cut_handoffs[suffixes]:
  `create_cut_code {} sc sj` by
    (`create_cut_code {} sc s2 /\ create_cut_code {} s2 s3 /\
      create_cut_code {} s3 s4 /\ create_cut_code {} s4 sj` by
        metis_tac[create_cut_code_fresh_var, create_cut_code_fresh_label, SND] >>
     metis_tac[create_cut_code_join]) >>
  `create_cut_code {} s7 s7a /\ create_cut_code {} s7a s8 /\
   create_cut_code {} s11 s11a /\ create_cut_code {} s11a s12` by
    metis_tac[create_operand_cut_code, ifexp_arm_closed, SND] >>
  drule_all ifexp_branch_suffixes >>
  disch_then (qspec_then `sel` mp_tac) >> Cases_on `sel` >> gvs[]
QED

Resume ifexp_selected_cut_handoffs[handoffs]:
  `cs_extends st sj /\ cs_extends st se /\ cs_extends st m /\
   cs_extends st x /\ cs_extends st y /\ cs_extends sn z /\ cs_extends y z /\
   cs_extends m z /\ cs_extends x z`
    by metis_tac[cs_extends_trans, cut_code_extends] >>
  `fn_has_code sc z f /\ fn_has_code x z f` by
    (rpt conj_tac >> irule fn_has_code_mid >> metis_tac[cs_extends_refl, cut_code_extends]) >>
  `cs_extends st st` by simp[cs_extends_refl] >>
  `st.cs_next_id <= se.cs_next_id /\ st.cs_next_id <= m.cs_next_id /\
   st.cs_next_id <= x.cs_next_id /\ st.cs_next_id <= y.cs_next_id /\
   m.cs_next_id <= z.cs_next_id /\ y.cs_next_id <= z.cs_next_id /\
   sn.cs_next_id <= z.cs_next_id /\ st.cs_next_id <= sj.cs_next_id` by decide_tac >>
  map_every (fn ends =>
    mp_tac (Q.SPECL ends ifexp_interval_geometry) >>
    (impl_tac >- (asm_rewrite_tac[] >> decide_tac)) >> strip_tac)
    [[`st`,`st`,`sc`,`z`,`f`], [`st`,`se`,`m`,`z`,`f`], [`st`,`m`,`x`,`z`,`f`]] >>
  map_every (fn ends =>
    mp_tac (Q.SPECL ends ifexp_emit_geometry) >>
    (impl_tac >- asm_rewrite_tac[]) >> strip_tac)
    [[`st`,`sj`,`sn`,`z`,`JNZ`,`[cop; Label tl; Label el]`,`[]`],
     [`st`,`x`,`y`,`z`,`ASSIGN`,`[op]`,`[rv]`],
     [`st`,`y`,`h`,`z`,`JMP`,`[Label xl]`,`[]`]] >>
  `sj.cs_next_id IN frag_ids sc z /\ y.cs_next_id IN frag_ids x z` by
    fs[frag_ids_def] >>
  `!u. create_operand_at sc u ==> ~create_operand_at z u` by
    (simp[create_operand_at_def] >> metis_tac[]) >>
  `~not_fresh_at st rv` by
    (qpat_assum `!v. not_fresh_at st v ==> v <> rv` (qspec_then `rv` mp_tac) >> simp[NoAsms]) >>
  `create_layout h z` by
    (irule create_layout_subinterval >> simp[] >> qexistsl_tac [`st`,`z`] >>
     simp[cs_extends_refl] >> metis_tac[cs_extends_trans]) >>
  `x.cs_current_bb <> xl` by
    (`h.cs_current_bb <> z.cs_current_bb` by metis_tac[ifexp_closed_open_label] >>
     qpat_assum `emit_inst ASSIGN _ _ x = _` (strip_assume_tac o MATCH_MP emit_inst_extends) >>
     qpat_assum `emit_inst JMP _ _ y = _` (strip_assume_tac o MATCH_MP emit_inst_extends) >>
     metis_tac[]) >>
  asm_rewrite_tac[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule ifexp_finish_scope >>
      metis_tac[]) >>
  conj_tac
  >- (gen_tac >> disch_tac >> `~create_operand_at z u` by metis_tac[] >>
      drule_all (CONJUNCT1 ifexp_admin_pc_handoffs) >> simp[LET_THM] >>
      metis_tac[]) >>
  rpt gen_tac >> strip_tac >> drule_all ifexp_finish_visit_disjoint >> metis_tac[]
QED

Finalise ifexp_selected_cut_handoffs
