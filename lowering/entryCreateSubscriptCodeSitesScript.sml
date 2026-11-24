(* Guarded child sites for the installed runtime LocCode selector. *)
Theory entryCreateSubscriptCodeSites
Ancestors
  entryCreateSubscriptUncopied entryCreateIntervalLayout entryCreateFocusSpec
  entryCreateOperandReplay exprSimTopLevelProps s1PrefixDefs
  createSizeOperandCode entryCreateCompletedCut exprSimSubscriptArraySource
  fragGasOriginPtr vyperStorageTrace vyperState compileEnv exprSimArrayIndex
  entryCreateSubscriptArrayRun

Theorem code_selector_count[local]:
  compile_array_subscript bop iop
    (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0) ws sz signed load =
  compile_array_subscript bop iop
    (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic n => n) ws sz signed load
Proof
  Cases_on `bd` >> simp[compile_array_subscript_split]
QED

Theorem framed_code_guarded_child_sites:
  body_inv tops ctx ce cx /\
  ~copies_subscript_base ce obj idx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre ce cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\ place_type ce obj = ValPT (ArrayT et bd) /\
  (!ty' st. vv_location (FST (compile_expr ce ty' obj st)) = SOME LocCode) /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty (Subscript ann obj idx)
    es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) /\ create_layout sa sb /\
  (!sm shm bvv.
    expr_body_pre ce cx env obj es /\
    expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty obj
      es (st0,sa,sm,sha,shm,bvv,s0,G0,tn0) /\ create_layout sa sm ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
      (cx_tops cx) cx st0 sa sm (eval_expr cx obj) (es,s0,G0,tn0)
      (\H res ee G tn t. create_operand_vv_post (DF,lo,d,ctx,f) ce cx obj
        (es,sa,sm,s0,bvv,G0,tn0) H res ee G tn t /\
        t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts)
      (create_operand_exit_post ctx cx) /\
    create_operand_cut sa sm (gas_explicit_sites ctx shctx) ctx f tops cx st0
      (eval_expr cx obj) (es,s0)) /\
  (!gs raw mid s G1 tn1 sm shm st2 sh2 iop.
    eval_expr cx obj (es with gas_obs := gs) = (INL raw,mid) /\
    body_const_cells_agree [(NONE,tops)] cx env mid /\ expr_body_pre ce cx env idx mid /\
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty idx
      mid (st0,sm,st2,shm,sh2,iop,s,G1,tn1) /\ create_layout sm st2 ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
      (cx_tops cx) cx st0 sm st2 (bind (eval_expr cx idx) (read_result cx)) (mid,s,G1,tn1)
      (expr_sim_full_post (DF,lo,d,ctx,f) ce cx idx (mid,sm,st2,s,iop,G1,tn1))
      (create_operand_exit_post ctx cx) /\
    create_operand_cut sm st2 (gas_explicit_sites ctx shctx) ctx f tops cx st0
      (bind (eval_expr cx idx) (read_result cx)) (mid,s)) ==>
  ?bvv sm shm iop st2 sh2 dst.
    compile_expr ce ty obj sa = (bvv,sm) /\ vv_location bvv = SOME LocCode /\
    lower_value compile_expr ce ty idx sm = (iop,st2) /\
    compile_array_subscript (vv_operand bvv) iop
      (case bd of Fixed _ => F | Dynamic _ => T)
      (case bd of Fixed n => n | Dynamic n => n)
      (word_scale LocCode) (elem_size_in_location ce LocCode et)
      (is_signed_type (expr_type idx))
      (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca LocCode) st2 = (dst,sb) /\
    vv = LocatedValue ann (mk_ptr dst LocCode) /\
    compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr obj) sha = (bvv,shm) /\
    lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr idx) shm = (iop,sh2) /\
    cs_extends sa sm /\ cs_extends sm st2 /\ cs_extends st2 sb /\
    fn_has_code sa sm f /\ fn_has_code sm st2 f /\ fn_has_code st2 sb f /\
    create_layout sa sm /\ create_layout sm st2 /\ create_layout st2 sb /\
    create_cut_code {} sa sm /\ create_cut_code {} sm st2 /\
    expr_body_pre ce cx env obj es /\
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
      (cx_tops cx) cx st0 sa sm (eval_expr cx obj) (es,s0,G0,tn0)
      (\H res ee G tn t. create_operand_vv_post (DF,lo,d,ctx,f) ce cx obj
        (es,sa,sm,s0,bvv,G0,tn0) H res ee G tn t /\
        t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts)
      (create_operand_exit_post ctx cx) /\
    create_operand_cut sa sm (gas_explicit_sites ctx shctx) ctx f tops cx st0
      (eval_expr cx obj) (es,s0) /\
    (!gs raw mid s G1 tn1 marks.
      eval_expr cx obj (es with gas_obs := gs) = (INL raw,mid) /\
      storage_trace_domain cx st0 mid.storage_trace /\ ~s.vs_halted /\ create_operand_at sm s /\
      (!H. valid_horizon cx st0 H mid.storage_trace ==>
        create_operand_vv_post (DF,lo,d,ctx,f) ce cx obj
          (es,sa,sm,s0,bvv,G0,tn0) H (INL raw : eval_result + exception) mid G1 tn1 s /\
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
          (s0,G0,tn0) marks (OK s,G1,tn1)) ==>
      scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
        (cx_tops cx) cx st0 sm st2 (bind (eval_expr cx idx) (read_result cx)) (mid,s,G1,tn1)
        (expr_sim_full_post (DF,lo,d,ctx,f) ce cx idx (mid,sm,st2,s,iop,G1,tn1))
        (create_operand_exit_post ctx cx) /\
      create_operand_cut sm st2 (gas_explicit_sites ctx shctx) ctx f tops cx st0
        (bind (eval_expr cx idx) (read_result cx)) (mid,s) /\
      expr_body_pre ce cx env idx mid /\ body_const_cells_agree [(NONE,tops)] cx env mid)
Proof
  strip_tac >>
  qpat_assum `expr_vv_sim_full_pre _ _ _ _ (Subscript _ _ _) _ _`
    (strip_assume_tac o REWRITE_RULE [expr_vv_sim_full_pre_def]) >>
  drule_all_then (qx_choosel_then [`bvv`,`sm`,`shm`,`iop`,`st2`,`sh2`,`dst`,`loc`] strip_assume_tac)
    subscript_nocopy_selected_layout >>
  `vv_location bvv = SOME LocCode` by metis_tac[pairTheory.FST] >>
  `loc = LocCode` by fs[] >>
  qpat_x_assum `loc = (case _ of NONE => _ | SOME _ => _)` kall_tac >>
  qpat_x_assum `loc = LocCode` SUBST_ALL_TAC >>
  `cs_extends sa st2 /\ cs_extends sm sb` by metis_tac[cs_extends_trans] >>
  `create_layout sa sm /\ create_layout sm st2 /\ create_layout st2 sb` by
    metis_tac[create_layout_subinterval,cs_extends_refl] >>
  `~array_slot_base ce obj` by metis_tac[array_slot_base_compile_location,pairTheory.FST] >>
  drule_all_then strip_assume_tac subscript_nocopy_base_ready >>
  qpat_x_assum `~array_slot_base ce obj ==> _` (drule_then assume_tac) >>
  qpat_assum `!sm shm bvv. _ ==> _ /\ _` (qspecl_then [`sm`,`shm`,`bvv`] mp_tac) >>
  (impl_tac >- rpt (FIRST_ASSUM ACCEPT_TAC ORELSE conj_tac)) >> strip_tac >>
  `create_cut_code {} sa sm` by metis_tac[operand_vv_cut_code] >>
  `create_cut_code {} sm st2` by metis_tac[create_operand_cut_code,pairTheory.SND] >>
  qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [code_selector_count]) >>
  qexistsl_tac [`bvv`,`sm`,`shm`,`iop`,`st2`,`sh2`,`dst`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac subscript_nocopy_index_ready >>
  qpat_x_assum `!gs raw mid s G1 tn1 sm shm st2 sh2 iop. _ ==> _ /\ _`
    (qspecl_then [`gs`,`raw`,`mid`,`s`,`G1`,`tn1`,`sm`,`shm`,`st2`,`sh2`,`iop`] mp_tac) >>
  simp[]
QED

(* The common no-read rule transports the supplied visit.  Only its
   compiler-independent sequent is needed here; the installed LocCode suffix
   is discharged separately, without running either bounds branch. *)
Theorem framed_code_visit_cut_at:
  (!p ix dyn cnt ws sz signed ctor imm loc a dst b.
    compile_array_subscript p ix dyn cnt ws sz signed
      (compile_ptr_load ctor imm loc) a = (dst,b) ==> create_cut_code {} a b) /\
  (!DF lo d ctx E f PG tops ce cx st0 sa sm st2 sb ann obj idx es s0 G0 tn0 bvv.
    body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\ ~s0.vs_halted /\
    ~subscript_reads_base cx obj idx /\
    create_cut_code {} sa sm /\ create_cut_code {} sm st2 /\ create_cut_code {} st2 sb /\
    fn_has_code sa sm f /\ fn_has_code sm st2 f /\ fn_has_code st2 sb f /\
    scoped_operand_outcome (DF,lo,E,ctx,f,PG) (cx_tops cx) cx st0 sa sm
      (eval_expr cx obj) (es,s0,G0,tn0)
      (\H res ee G tn t. create_operand_vv_post (DF,lo,d,ctx,f) ce cx obj
        (es,sa,sm,s0,bvv,G0,tn0) H res ee G tn t /\
        t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts)
      (create_operand_exit_post ctx cx) /\
    create_operand_cut sa sm E ctx f tops cx st0 (eval_expr cx obj) (es,s0) /\
    (!gs raw mid s G1 tn1 marks.
      eval_expr cx obj (es with gas_obs := gs) = (INL raw,mid) /\
      storage_trace_domain cx st0 mid.storage_trace /\ ~s.vs_halted /\ create_operand_at sm s /\
      (!H. valid_horizon cx st0 H mid.storage_trace ==>
        create_operand_vv_post (DF,lo,d,ctx,f) ce cx obj
          (es,sa,sm,s0,bvv,G0,tn0) H (INL raw : eval_result + exception) mid G1 tn1 s /\
        gas_origin_ptr_path (DF H,lo,E,ctx,f,PG) (s0,G0,tn0) marks (OK s,G1,tn1)) ==>
      create_operand_cut sm st2 E ctx f tops cx st0
        (bind (eval_expr cx idx) (read_result cx)) (mid,s)) /\
    (!raw key fin it. create_operand_at st2 it ==>
      create_operand_cut st2 sb E ctx f tops cx st0
        (select_result cx (expr_type obj) raw (ValueSubscript key)) (fin,it)) ==>
    create_operand_cut sa sb E ctx f tops cx st0
      (eval_expr cx (Subscript ann obj idx)) (es,s0)) /\
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\ ~s0.vs_halted /\
  ~subscript_reads_base cx obj idx /\
  create_cut_code {} sa sm /\ create_cut_code {} sm st2 /\
  fn_has_code sa sm f /\ fn_has_code sm st2 f /\ fn_has_code st2 sb f /\
  compile_array_subscript (vv_operand bvv) iop dyn cnt (word_scale LocCode)
    sz (is_signed_type (expr_type idx)) (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca LocCode)
    st2 = (dst,sb) /\
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
    (cx_tops cx) cx st0 sa sm (eval_expr cx obj) (es,s0,G0,tn0)
    (\H res ee G tn t. create_operand_vv_post (DF,lo,d,ctx,f) ce cx obj
      (es,sa,sm,s0,bvv,G0,tn0) H res ee G tn t /\
      t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts)
    (create_operand_exit_post ctx cx) /\
  create_operand_cut sa sm (gas_explicit_sites ctx shctx) ctx f tops cx st0
    (eval_expr cx obj) (es,s0) /\
  (!gs raw mid s G1 tn1 marks.
    eval_expr cx obj (es with gas_obs := gs) = (INL raw,mid) /\
    storage_trace_domain cx st0 mid.storage_trace /\ ~s.vs_halted /\ create_operand_at sm s /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      create_operand_vv_post (DF,lo,d,ctx,f) ce cx obj
        (es,sa,sm,s0,bvv,G0,tn0) H (INL raw : eval_result + exception) mid G1 tn1 s /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
        (s0,G0,tn0) marks (OK s,G1,tn1)) ==>
    create_operand_cut sm st2 (gas_explicit_sites ctx shctx) ctx f tops cx st0
      (bind (eval_expr cx idx) (read_result cx)) (mid,s)) ==>
  create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx f tops cx st0
    (eval_expr cx (Subscript ann obj idx)) (es,s0)
Proof
  strip_tac >>
  `create_cut_code {} st2 sb` by
    (qpat_assum `!p ix dyn cnt ws sz signed ctor imm loc a dst b. _`
       (irule o SPEC_ALL) >>
     qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _` (irule_at Any)) >>
  `array_selector_code st2 sb` by
    (irule compile_array_selector_code >>
     qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
     metis_tac[array_length_selector_code]) >>
  qpat_x_assum `!DF lo d ctx E f PG tops ce cx st0 sa sm st2 sb ann obj idx es s0 G0 tn0 bvv. _`
    (irule o SPEC_ALL) >>
  qpat_assum `scoped_operand_outcome _ _ _ _ _ _ _ _ _ _` (irule_at Any) >> simp[] >>
  qexists_tac `st2` >> simp[] >>
  reverse conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >> irule array_selector_visit_inventory >> simp[]
QED
