(* Attribute the selected native visit through the paired bytestring hash stages. *)
Theory entryCreateBopBytestringNative
Ancestors
  entryCreateNativeFirstExit entryCreateReplayBind entryCreateBodyCut
  entryCreateFocusSpec entryCreateCompletedCut entryCreateOperandReplay
  exprBopSimProps exprLoweringProps bodySimFullMain
  createExprSizeExitDefs createSizePrefixReplay createMarkedPath
  createSizeCutCode fragExec fragGasOriginPtr vyperStorageTrace
  vyperInterpreter vyperState
  venomExecSemantics venomInst relation list pair arithmetic

Theorem bop_bytestring_selected_native_cut:
  body_inv tops ctx ce cx /\ MEM func ctx.ctx_functions /\
  create_cut_code {} sa sh1 /\ fn_has_code sa sh1 func /\
  create_cut_code {} sh1 sh2 /\ fn_has_code sh1 sh2 func /\
  create_cut_code {} sh2 sb /\ fn_has_code sh2 sb func /\
  fn_has_code sa sb func /\ ~s0.vs_halted /\
  create_operand_cut sa sh1 E ctx func (cx_tops cx) cx st0
    (bind (eval_expr cx e1) (read_result cx)) (es,s0) /\
  gas_completed_operand (DF,lo,E,ctx,func,PG) (cx_tops cx) cx st0 sa sh1
    (bind (eval_expr cx e1) (read_result cx)) (es,s0,G0,tn0) Q /\
  (!H r ee G tn t. Q H r ee G tn t ==> ?v. r = INL v) /\
  (!v. storage_trace_frame
    (bind (bind (eval_expr cx e2) (read_result cx))
      (\v2 s. (bop_result cx ann bop [expr_type e1;expr_type e2] v v2 s,s)))) /\
  (!H0 front v mid G tn t.
    valid_horizon cx st0 H0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (s0,G0,tn0)
        (create_cut_marks E front) (OK t,G,tn) /\
      Q H (INL v) (mid with gas_obs := []) G tn t) ==>
    create_operand_cut sh1 sb E ctx func (cx_tops cx) cx st0
      (bind (bind (eval_expr cx e2) (read_result cx))
        (\v2 s. (bop_result cx ann bop [expr_type e1;expr_type e2] v v2 s,s)))
      (mid with gas_obs := [],t)) ==>
  create_operand_cut sa sb E ctx func (cx_tops cx) cx st0
    (bind (bind (eval_expr cx e1) (read_result cx))
      (\v. bind (bind (eval_expr cx e2) (read_result cx))
        (\v2 s. (bop_result cx ann bop [expr_type e1;expr_type e2] v v2 s,s))))
    (es,s0)
Proof
  strip_tac >>
  pop_assum (mk_asm "callback") >>
  `create_cut_code {} sh1 sb` by metis_tac[create_cut_code_join] >>
  `cs_extends sa sh1 /\ cs_extends sh1 sb` by
    metis_tac[create_cut_code_def] >>
  `fn_has_code sa sh1 func /\ fn_has_code sh1 sb func` by
    (mp_tac (Q.INST [`st1` |-> `sa`, `st2` |-> `sh1`, `st3` |-> `sb`,
      `fn` |-> `func`] fn_has_code_split) >> simp[] >> metis_tac[]) >>
  `!p d k before hit after.
      create_interior_visit sa sb E ctx func (p,d,k) s0
        (before,hit,after) ==>
      create_interior_visit sa sh1 E ctx func (p,d,k) s0
        (before,hit,after) \/
      ?t d1 k1 front back. before = front ++ back /\
        create_operand_at sh1 t /\
        RTC (create_operand_native_step sa sh1 E ctx func p)
          (d,k,s0,[]) (d1,k1,t,front) /\
        create_expr_prefix sa sh1 E ctx func s0
          (create_cut_marks E front) t /\
        create_interior_visit sh1 sb E ctx func (p,d1,k1) t
          (back,hit,after)` by
    (rpt gen_tac >> disch_tac >>
     irule create_interior_visit_first_exit >> simp[] >> metis_tac[]) >>
  irule (Q.INST [`a` |-> `sa`, `m` |-> `sh1`, `b` |-> `sb`,
    `fnc` |-> `func`] create_operand_cut_bind_replay) >>
  first_assum (irule_at (Pat `create_operand_cut sa sh1 _ _ _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `gas_completed_operand _ _ _ _ sa sh1 _ _ _`)) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum drule >> simp[] >> metis_tac[]) >>
  conj_tac
  >- asm "callback" ACCEPT_TAC
  >- first_assum ACCEPT_TAC
QED
