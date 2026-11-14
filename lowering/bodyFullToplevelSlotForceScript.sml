(* Aggregate TopLevelName forcing at one framed joint endpoint. *)
Theory bodyFullToplevelSlotForce
Ancestors
  bodyFullToplevelSlotSingle bodyFullToplevelSlotEntry
  bodyFullToplevelSlotLoopFrame bodyFullToplevelSlotLoopPost
  bodyMemBopRestWordPath fragGasOriginPtr fragGasPathPtr
  exprPtrUnwrapRuntimeFrame exprPtrUnwrapLoopInvariant createSourceCallback

Theorem toplevel_slot_loop_path_history:
  compile_expr cenv ty (TopLevelName ann nsid) sa = (vv,sm) /\
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tnf) /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s ==>
  alloca_history func z /\ alloca_inv z
Proof
  strip_tac >> drule gas_origin_ptr_path_projections >> strip_tac >>
  drule gas_path_ptr_erase >> strip_tac >>
  drule rest_word_path_alloca >> simp[]
QED

Theorem toplevel_slot_loop_common_run:
  compile_expr cenv ty (TopLevelName ann nsid) ca = (place,sa) /\
  (loc = LocStorage \/ loc = LocTransient) /\ n <> 1 /\
  compile_ensure_in_memory src loc nb n ctor imm sa = (op,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel H ctx func cenv cx es s /\
  nb < dimword (:256) /\ n < 2**256 /\ 32*n <= nb /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ op_taint tn src = {} ==>
  ?root d a G0 tn0 mid buf u z Gf tnf lab.
    compile_alloc_buffer nb sa = (buf,mid) /\ op = Var root /\ buf.buf_operand = Var root /\
    compile_slot_to_memory src (Var root) n loc mid = (lab,sb) /\
    fn_has_code sa mid func /\ fn_has_code mid sb func /\
    u = update_var root d (buffer_allocation_fields s sa.cs_next_id nb) /\
    step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
    a = u with vs_inst_idx := SUC s.vs_inst_idx /\
    G0 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
    tn0 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
    d = n2w (buffer_allocation_base s sa.cs_next_id) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tnf)) /\
    z.vs_current_bb = slot_copy_exit mid /\ z.vs_inst_idx = 0 /\
    slot_copy_inv mid (if loc=LocStorage then SLOAD else TLOAD) a p d n [] n z /\
    slot_copy_ghost_inv mid (if loc=LocStorage then SLOAD else TLOAD) p d root n G0 tn0 n Gf tnf z /\
    slot_copy_runtime_frame mid d n a z /\ allocas_from lo z /\
    slot_copy_external mid src /\ slot_copy_external mid (Var root) /\
    eval_operand src a = SOME p /\ lookup_var root a = SOME d /\
    ptr_covers G0 tn0 root a nb /\
    a.vs_memory = s.vs_memory /\ a.vs_accounts = s.vs_accounts /\
    a.vs_transient = s.vs_transient /\ a.vs_call_ctx = s.vs_call_ctx /\
    a.vs_immutables = s.vs_immutables /\
    tn0.t_stor = tn.t_stor /\ tn0.t_trans = tn.t_trans /\ tn0.t_imm = tn.t_imm
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac strip_assume_tac)) >>
  `create_memory_snapshot [] s` by simp[create_memory_snapshot_def] >>
  `EVERY (\(off,bs). off+LENGTH bs <= LENGTH s.vs_memory /\
    (off+LENGTH bs <= w2n (n2w (buffer_allocation_base s sa.cs_next_id):bytes32) \/
     w2n (n2w (buffer_allocation_base s sa.cs_next_id):bytes32)+32*n <= off)) []` by simp[] >>
  mp_tac (Q.INST [`regions` |-> `[]`] (SPEC_ALL toplevel_slot_copy_entry_joint)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `slot_copy_runtime_frame sm d 0 a h` by
    metis_tac[slot_copy_runtime_frame_initial] >>
  `?t Gf tnf.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (h,Gh,tnh) [] (OK t,Gf,tnf)) /\
    t.vs_current_bb = slot_copy_exit sm /\ t.vs_inst_idx = 0 /\
    slot_copy_inv sm (if loc=LocStorage then SLOAD else TLOAD) a p d n [] n t /\
    slot_copy_ghost_inv sm (if loc=LocStorage then SLOAD else TLOAD) p d root n G0 tn0 n Gf tnf t /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    t.vs_alloca_next = h.vs_alloca_next /\ slot_copy_runtime_frame sm d n a t` by
    (irule toplevel_slot_copy_joint_finish_framed >>
     simp[SF SFY_ss] >>
     Cases_on `loc=LocStorage` >> gvs[] >>
     (conj_tac >- (qexists `src` >> simp[])) >>
     qexists `0:num` >> simp[]) >>
  qexistsl [`root`, `d`, `a`, `G0`, `tn0`, `sm`, `buf`, `u`, `t`, `Gf`, `tnf`, `lab`] >>
  simp[] >> rpt gen_tac >>
  qpat_x_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) _ _`
    (qspecl_then [`D`, `explicit`] mp_tac) >>
  disch_then (mp_then Any (qspecl_then [`a`, `G0`, `tn0`, `[]`] mp_tac) gas_origin_ptr_path_append) >>
  simp[] >> disch_then irule >>
  qpat_x_assum `!D explicit. gas_origin_ptr_path _ (a,G0,tn0) _ _`
    (qspecl_then [`D`, `explicit`] mp_tac) >>
  disch_then (mp_then Any (qspecl_then [`h`, `Gh`, `tnh`, `[]`] mp_tac) gas_origin_ptr_path_append) >>
  simp[] >> disch_then irule >> gvs[]
QED
