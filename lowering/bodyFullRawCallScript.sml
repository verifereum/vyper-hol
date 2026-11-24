Theory bodyFullRawCall
Ancestors
  bodyFullShadowBodyInv
  bodyFullPreds bodySimFull bodyFullRawCallPrefix bodyFullRawCallFinishPost
  bodyFullRawCallRequestGas bodyFullOfVV exprSimRawCallCalldata
  extCallOracleStep oracleCallStepPtr fragGasEmitCtrl instMemFrontier
  venomExecSemantics venomInst venomState words bodyPtrDefs ptrDiscipline
  memLocDefs fragGasOriginPtr fragExec memSafeRun gasEvents gasCount
  contextCodegenRel codegenRel unitTransformDefs ptrSafeRun bodyFullRawCallCall
  exprSimRawCall exprSimHyps exprSimSource
  gasOutcomeFullCompose vyperStorageTrace bodyFullIntCallReturnHalt exprLoweringProps
  bodyFullHashKeccakFixed bodyFullWordArgs bodyFullRawCallAdapter
Libs
  monadsyntax

Theorem raw_call_empty_write_memory[local]:
  mem_bytes_at src len (write_memory_with_expansion dst [] s).vs_memory =
  mem_bytes_at src len s.vs_memory
Proof
  irule listTheory.LIST_EQ >>
  simp[valueEncodingProofsTheory.LENGTH_mem_bytes_at_proof] >>
  rpt strip_tac >>
  simp[valueEncodingProofsTheory.EL_mem_bytes_at,GSYM codegenRelTheory.read_byte_def,
       regularCallEmitSimTheory.read_byte_write_memory_with_expansion]
QED

(* Both early errors exit at the call itself, without executing the suffix. *)
Theorem raw_call_fetched_early_exit[local]:
  inst = mk_inst id (case call_ty of
           RegularCall => CALL | StaticCall => STATICCALL | DelegateCall => DELEGATECALL)
    (if call_ty = RegularCall then [gas;addr;value;dp;dl;op;Lit (n2w cap)]
     else [gas;addr;dp;dl;op;Lit (n2w cap)]) [out] /\
  eval_operand gas t = SOME gw /\ eval_operand addr t = SOME aw /\
  eval_operand value t = SOME vw /\ eval_operand dp t = SOME iw /\
  eval_operand dl t = SOME nw /\ eval_operand op t = SOME rw /\
  (t.vs_outcomes = [] \/ (call_ty = RegularCall /\ t.vs_call_ctx.cc_static /\ vw <> 0w)) /\
  (nw <> 0w ==> ?p. dp = Var p /\ ptr_covers G tn p t (w2n nw)) /\
  (n2w cap <> (0w:bytes32) ==>
     ?p. op = Var p /\ ptr_covers G tn p t (w2n (n2w cap:bytes32))) /\
  EVERY (\op. op_taint tn op = {}) inst.inst_operands /\
  (!j. w2n iw <= j /\ j < w2n iw + w2n nw ==> j NOTIN tn.t_mem) /\
  mem_safe_step 0 ctx inst t /\
  allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ ~t.vs_halted /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst ==>
  gas_origin_edge T explicit ctx func t []
    (Abort ExHalt_abort (halt_state (set_returndata [] t))) /\
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) []
    (Abort ExHalt_abort (halt_state (set_returndata [] t)),G,tn)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!fuel. step_inst fuel ctx inst t =
    Abort ExHalt_abort (halt_state (set_returndata [] t))` by
    (map_every (fn pattern => qpat_assum pattern mp_tac)
       [`inst = mk_inst _ _ _ _`, `eval_operand gas t = SOME gw`,
        `eval_operand addr t = SOME aw`, `eval_operand value t = SOME vw`,
        `eval_operand dp t = SOME iw`, `eval_operand dl t = SOME nw`,
        `eval_operand op t = SOME rw`, `t.vs_outcomes = [] \/ _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> ntac 8 disch_tac >>
     let
       fun is_call_clause th =
         let val opc = rhs (fst (dest_imp (snd (strip_forall (concl th)))))
         in aconv opc ``CALL`` orelse aconv opc ``STATICCALL`` orelse
              aconv opc ``DELEGATECALL`` end
       val clauses = List.filter is_call_clause (CONJUNCTS step_inst_base_opcode_eqs)
     in
       Cases_on `call_ty` >>
       gvs(clauses @ [mk_inst_def,step_inst_non_invoke,eval_operand_def])
     end >>
     gs[exec_ext_call_abort_iff, exec_delegatecall_abort_iff] >>
     Cases_on `t.vs_call_ctx.cc_static /\ vw <> 0w` >>
     gs[exec_ext_call_abort_iff, exec_delegatecall_abort_iff]) >>
  `source_memory_read_ranges inst t = [(w2n iw,w2n nw)] /\
   source_memory_write_ranges inst t = [(w2n rw,w2n (n2w cap:bytes32))]` by
    (Cases_on `call_ty` >>
     simp[mk_inst_def, source_memory_read_ranges_def, source_memory_write_ranges_def,
         mem_read_ops_def, mem_write_ops_def, memory_range_of_operands_def,
         eval_operand_def]) >>
  `w2n (n2w cap:bytes32) <> 0 ==>
   ?v b sz. op = Var v /\ FLOOKUP G v = SOME (b,sz) /\
            b <= w2n rw /\ w2n rw + w2n (n2w cap:bytes32) <= b + sz` by
    (PURE_REWRITE_TAC [w2n_eq_0] >> strip_tac >>
     qpat_x_assum `(n2w cap:bytes32) <> 0w ==> _` drule >>
     simp[ptr_covers_def] >> strip_tac >> gvs[eval_operand_def] >> metis_tac[]) >>
  `w2n nw <> 0 ==>
   ?v b sz. dp = Var v /\ FLOOKUP G v = SOME (b,sz) /\
            b <= w2n iw /\ w2n iw + w2n nw <= b + sz` by
    (PURE_REWRITE_TAC [w2n_eq_0] >> strip_tac >>
     qpat_x_assum `nw <> 0w ==> _` drule >>
     simp[ptr_covers_def] >> strip_tac >> gvs[eval_operand_def] >> metis_tac[]) >>
  qpat_x_assum `w2n (n2w cap:bytes32) <> 0 ==> _`
    (assume_tac o SRULE [w2n_n2w]) >>
  `access_ok lo G func inst t` by
    (Cases_on `call_ty` >>
     simp[access_ok_def, mk_inst_def, mem_read_ops_def, mem_write_ops_def] >>
     rpt strip_tac >> first_assum irule >> simp[]) >>
  `taint_ok func tn inst t` by
    (qpat_assum `EVERY _ inst.inst_operands` mp_tac >>
     qpat_assum `source_memory_read_ranges inst t = _` mp_tac >>
     qpat_assum `!j. w2n iw <= j /\ j < w2n iw + w2n nw ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[taint_ok_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `ptr_inst_ok D lo 0 ctx func G tn inst t` by simp[ptr_inst_ok_def] >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
   inst_dload_in_section inst t` by
    (Cases_on `call_ty` >> simp[mk_inst_def, inst_dload_in_section_def]) >>
  `gas_events_step 0 ctx func.fn_name inst t = [] /\
   gas_count_step 0 ctx inst t = 0` by
    (Cases_on `call_ty` >> simp[mk_inst_def, gas_events_step_def, gas_count_step_def]) >>
  qpat_x_assum `inst = mk_inst _ _ _ _` kall_tac >>
  conj_tac
  >- (simp[fragGasOriginTheory.gas_origin_edge_def,exit_result_def] >> qexists_tac `0` >> simp[] >> metis_tac[]) >>
  irule exit_inst_origin_ptr >> simp[exit_result_def]
QED

(* Anchor all inputs of the counted raw call rule before introducing its post. *)
local
  val rule = SPEC_ALL (INST_TYPE [alpha |-> ``:256``]
    bodyFullRawCallCallTheory.raw_call_actual_call_mem_safe_full)
  val inputs = strip_conj (fst (dest_imp (concl rule)))
  fun head name tm =
    case total dest_thy_const (#1 (strip_comb tm)) of
      SOME {Name,...} => name = Name | NONE => false
  fun find_atom name pred =
    case List.find pred inputs of
      SOME tm => tm | NONE => raise Fail ("counted CALL input: " ^ name)
  fun atom name = find_atom name (head name)
  fun eqn side name = find_atom name (fn tm => is_eq tm andalso head name (side tm))
  fun operand role = find_atom role (fn tm => is_eq tm andalso
    head "eval_operand" (lhs tm) andalso
    (case #2 (strip_comb (lhs tm)) of
       v::_ => is_var v andalso #1 (dest_var v) = role | [] => false))
  fun param name = List.find (fn v => #1 (dest_var v) = name) (free_vars (concl rule))
                   |> valOf
  val setup = pairSyntax.list_mk_pair
    ([eqn lhs "emit_op", eqn lhs "COND", eqn rhs "mk_inst"] @
     map operand ["gas_op", "to_op", "op", "val_op"] @ [param "explicit", param "PG"])
  val pattern = pairSyntax.list_mk_pair [atom "stmt_state_rel", atom "ghost_inv_at", setup]
in
  fun raw_call_at wrapper ghost finish goal ctxt =
    let
      fun select q =
        let val chosen = ref NONE
            val _ = qpat_assum q (fn th => (chosen := SOME th; all_tac)) goal ctxt
        in valOf (!chosen) end
      val rel = select wrapper
      val inv = select ghost
    in
      Q_TAC (fn actual =>
        let
          val state = pairSyntax.list_mk_pair [concl rel, concl inv, actual]
          val instantiation = match_term pattern state
            handle HOL_ERR _ => raise Fail "counted CALL typed input match"
          val instance = INST_TY_TERM instantiation rule
        in
          mp_tac instance >> (impl_tac >-
            (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
             FILTER_ASM_REWRITE_TAC (can (match_term ``w2n (n2w _ : bytes32) = _``))
               [EVAL ``dimword (:256)``] >>
             (first_assum ACCEPT_TAC ORELSE
               goal_term (fn tm => FAIL_TAC (term_to_string tm))))) >>
          disch_then (finish o BETA_RULE o REWRITE_RULE [LET_THM])
        end)
        `(emit_op (case call_ty of
           RegularCall => CALL | StaticCall => STATICCALL | DelegateCall => DELEGATECALL)
            (if call_ty = RegularCall then [gas;addr;vop;dp;len;op;Lit (n2w cap)]
             else [gas;addr;dp;len;op;Lit (n2w cap)]) s7 = (ok,sc),
          (if call_ty = DelegateCall then take_delegate_outcome else take_call_outcome)
            gas_cap target
            (read_memory (w2n (n2w ib : bytes32)) (w2n (n2w (LENGTH bs) : bytes32)) t7)
            value_opt esK = (INL (rq,outcome),es1),
          inst = mk_inst s7.cs_next_id (case call_ty of
           RegularCall => CALL | StaticCall => STATICCALL | DelegateCall => DELEGATECALL)
            (if call_ty = RegularCall then [gas;addr;vop;dp;len;op;Lit (n2w cap)]
             else [gas;addr;dp;len;op;Lit (n2w cap)])
            [STRING #"%" (toString s7.cs_next_var)],
          eval_operand gas t7 = SOME gw, eval_operand addr t7 = SOME (w2w target),
          eval_operand op t7 = SOME (n2w ro), eval_operand vop t7 = SOME (n2w amount),
          gas_explicit_sites ctx shadow_ctx, PG)` goal ctxt
    end
end

(* The post-call supplier can retain an observation about its chosen endpoint.
   Its physical state and ghosts are shared with the ordinary return post. *)
Definition raw_call_finish_rule_def:
  raw_call_finish_rule finish_ok <=>
  !to_op dp dl gas_op val_op call_ty n rev ov op sa result sb ok sc success s
   tn G func ctx lo H0 cenv cx es es0 sf s0 G0 tn0 e explicit PG dep ann.
  compile_raw_call_finish to_op dp dl gas_op val_op
    call_ty n rev ov op sa = (result,sb) /\
  (case call_ty of
    RegularCall => emit_op CALL [gas_op;to_op;val_op;dp;dl;op;Lit (n2w n)]
  | StaticCall => emit_op STATICCALL [gas_op;to_op;dp;dl;op;Lit (n2w n)]
  | DelegateCall => emit_op DELEGATECALL [gas_op;to_op;dp;dl;op;Lit (n2w n)]) sa = (ok,sc) /\
  eval_operand ok s = SOME (if success then 1w else 0w) /\
  op_taint tn ok = {} /\ op_prov G ok = NONE /\
  fn_has_code sc sb func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\ LENGTH (s.vs_returndata) < dimword (:256) /\
  stmt_state_rel (H0:(bool # 256 word # type_value) list # num list) ctx func cenv cx es s /\
  wb_frame cenv es0 es sf s0 s /\
  ghost_kept_at lo cenv es0 sf G0 tn0 s0 G tn /\
  (!a sz. cenv.ce_return_buf = SOME (PtrVar (Var a) sz) ==> not_fresh_at sf a) /\
  (!a sz. cenv.ce_return_pc = SOME (PtrVar (Var a) sz) ==> not_fresh_at sf a) /\
  expr_has_effect e /\ post_value_type cenv e = expr_type e /\
  lowered_value_type cenv e = expr_type e /\ expr_type e = (if n = 0 then (if rev then NoneT else BaseT
    BoolT) else if rev then BaseT (BytesT (Dynamic n)) else TupleT [BaseT BoolT;BaseT (BytesT (Dynamic n))]) /\
  (0 < n /\ (~rev \/ success) ==>
    ?x w alloc q pre (ro:bytes32) old_tn.
      ov = Var x /\ n < dimword (:256) /\ 32 + (32 + ((n + 31) DIV 32) * 32) < dimword (:256) /\
      MEM alloc (fn_insts func) /\ alloc.inst_opcode = ALLOCA /\
      alloc.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
      FLOOKUP s.vs_allocas alloc.inst_id = SOME (w2n w,(32 + ((n + 31) DIV 32) * 32)) /\
      local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sc /\
      sf.cs_next_var <= sc.cs_next_var /\ sf.cs_next_id <= alloc.inst_id /\
      alloc.inst_id < sc.cs_next_id /\ MAP FDOM es0.scopes = MAP FDOM es.scopes /\
      not_fresh_at sc x /\ lookup_var x s = SOME w /\ ptr_covers G tn x s (32 + ((n + 31) DIV 32) * 32) /\
      w2n ro = w2n w + 32 /\
      s.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE n (s.vs_returndata)) pre).vs_memory /\
      tn.t_mem = old_tn.t_mem DIFF
        {i | i | w2n ro <= i /\ i < w2n ro + LENGTH (TAKE n (s.vs_returndata))} /\
      (~rev ==> safe_operand sc ok /\ evaluate_type (get_tenv cx) (if n = 0 then (if rev then NoneT else
        BaseT BoolT) else if rev then BaseT (BytesT (Dynamic n)) else TupleT [BaseT BoolT;BaseT (BytesT
        (Dynamic n))]) =
        SOME (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))]))) ==>
  ?r Gf tnf.
    finish_ok sc sb explicit ctx func s r /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (r,Gf,tnf)) /\
    (if rev /\ ~success then
       ?u. r = Abort Revert_abort u /\ u.vs_returndata = s.vs_returndata /\
           expr_exit (INR (Error (RevertData s.vs_returndata)) : eval_result + vyperState$exception) r /\
           !H:(bool # 256 word # type_value) list # num list. halt_exit H cx es
             (INR (Error (RevertData s.vs_returndata)) : eval_result + vyperState$exception) r
     else
       ?u. r = OK u /\ ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func u /\
       ghost_kept_at lo cenv es0 sf G0 tn0 s0 Gf tnf /\
       (!D. ghost_inv_at D lo dep cenv cx es G tn s ==>
         ghost_inv_at D lo dep cenv cx es Gf tnf u) /\
       ptr_vv_ok cx (post_value_type cenv e) (Value (if n = 0 then (if rev then NoneV else BoolV success)
         else if rev then BytesV (TAKE n (s.vs_returndata)) else ArrayV (TupleV [BoolV success;BytesV (TAKE
         n (s.vs_returndata))]))) (if n = 0 then StackValue ann result else LocatedValue (if n = 0 then (if
         rev then NoneT else BaseT BoolT) else if rev then BaseT (BytesT (Dynamic n)) else TupleT [BaseT
         BoolT;BaseT (BytesT (Dynamic n))]) (mk_ptr result LocMemory)) es Gf tnf u /\
       (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e result Gf u) /\
       (!H:(bool # 256 word # type_value) list # num list.
         stmt_state_rel H ctx func cenv cx es s /\
            storage_well_formed_on cx es (FST H) ==>
         vv_post H ctx func cenv cx e es0 sf sb s0 es (Value (if n = 0 then (if rev then NoneV else BoolV
           success) else if rev then BytesV (TAKE n (s.vs_returndata)) else ArrayV (TupleV [BoolV success;
           BytesV (TAKE n (s.vs_returndata))]))) (if n = 0 then StackValue ann result else LocatedValue (if
           n = 0 then (if rev then NoneT else BaseT BoolT) else if rev then BaseT (BytesT (Dynamic n)) else
           TupleT [BaseT BoolT;BaseT (BytesT (Dynamic n))]) (mk_ptr result LocMemory)) u /\
         vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
           es (Value (if n = 0 then (if rev then NoneV else BoolV success) else if rev then BytesV (TAKE n
             (s.vs_returndata)) else ArrayV (TupleV [BoolV success;BytesV (TAKE n (s.vs_returndata))]))) (if
             n = 0 then StackValue ann result else LocatedValue (if n = 0 then (if rev then NoneT else
             BaseT BoolT) else if rev then BaseT (BytesT (Dynamic n)) else TupleT [BaseT BoolT;BaseT (BytesT
             (Dynamic n))]) (mk_ptr result LocMemory)) u /\
         vv_own cenv cx (post_value_type cenv e) sf sb es (Value (if n = 0 then (if rev then NoneV else
           BoolV success) else if rev then BytesV (TAKE n (s.vs_returndata)) else ArrayV (TupleV [BoolV
           success;BytesV (TAKE n (s.vs_returndata))]))) (if n = 0 then StackValue ann result else
           LocatedValue (if n = 0 then (if rev then NoneT else BaseT BoolT) else if rev then BaseT (BytesT
           (Dynamic n)) else TupleT [BaseT BoolT;BaseT (BytesT (Dynamic n))]) (mk_ptr result LocMemory)) u))
End

Theorem raw_call_finish_rule_plain[local]:
  raw_call_finish_rule (\sc sb E C f s r. T)
Proof
  simp_tac bool_ss [raw_call_finish_rule_def] >> rpt gen_tac >>
  rename1 `gas_origin_ptr_path (_,_,sites,_,_,_) _ _ _` >>
  disch_then (mp_tac o MATCH_MP (SIMP_RULE bool_ss []
    (Q.INST [`explicit` |-> `sites`] raw_call_finish_continuation_full))) >>
  Cases_on `rev /\ ~success` >> simp[exprSimDefsTheory.halt_exit_def] >>
  strip_tac >> qexistsl_tac [`r`,`Gf`,`tnf`] >> simp[] >>
  gvs[exprSimDefsTheory.expr_exit_def] >> metis_tac[]
QED

(* A no-GAS action either leaves the storage domain at once or retains an
   observation on exactly the result paired with its source run and ghosts. *)
Definition raw_call_observed_outcome_def:
  raw_call_observed_outcome accept (DF,lo,explicit,ctx,func,PG) cx st0
    source (es,s,G,tn) Q R <=>
  (~s.vs_halted /\ (!tail. ~storage_trace_domain cx st0
    (SND (source (es with gas_obs := tail))).storage_trace)) \/
  ?res ee r Gf tnf.
    accept r /\
    (!tail. source (es with gas_obs := tail) = (res,ee with gas_obs := tail)) /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (r,Gf,tnf) /\
       ((?t. r = OK t /\ Q H res (ee with gas_obs := []) Gf tnf t) \/
        (exit_result r /\ R H res (ee with gas_obs := []) (Gf,tnf) r)))
End

Theorem raw_call_observed_bad[local]:
  ~s.vs_halted /\
  (!tail. ~storage_trace_domain cx st0
          (SND (source (es with gas_obs := tail))).storage_trace) ==>
  raw_call_observed_outcome accept (DF,lo,E,C,f,PG) cx st0 source (es,s,G,tn) Q R
Proof
  simp[raw_call_observed_outcome_def]
QED

Theorem raw_call_observed_intro[local]:
  accept r /\
  (!tail. source (es with gas_obs := tail) = (res,ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G,tn) [] (r,Gf,tnf) /\
       ((?t. r = OK t /\ Q H res (ee with gas_obs := []) Gf tnf t) \/
        (exit_result r /\ R H res (ee with gas_obs := []) (Gf,tnf) r))) ==>
  raw_call_observed_outcome accept (DF,lo,E,C,f,PG) cx st0 source (es,s,G,tn) Q R
Proof
  simp[raw_call_observed_outcome_def] >> metis_tac[]
QED

Theorem raw_call_observed_exit[local]:
  ~s.vs_halted /\
  (!tail. source (es with gas_obs := tail) = (res,ee with gas_obs := tail)) /\
  exit_result r /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G,tn) [] (r,Gf,tnf) /\
       R H res (ee with gas_obs := []) (Gf,tnf) r /\ accept r) ==>
  raw_call_observed_outcome accept (DF,lo,E,C,f,PG) cx st0 source (es,s,G,tn) Q R
Proof
  strip_tac >> Cases_on `storage_trace_domain cx st0 ee.storage_trace`
  >- (irule raw_call_observed_intro >>
      qexistsl_tac [`Gf`,`ee`,`r`,`res`,`tnf`] >> simp[] >>
      fs[vyperStorageFootprintTheory.storage_trace_domain_def] >> metis_tac[]) >>
  irule raw_call_observed_bad >> simp[]
QED

Theorem raw_call_observed_plain:
  raw_call_observed_outcome accept (DF,lo,explicit,ctx,func,PG) cx st0
    source (es,s,G,tn) Q R ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source (es,s,G,tn) Q R
Proof
  simp[raw_call_observed_outcome_def] >> strip_tac
  >- (irule gas_outcome_full_bad_nil >> simp[]) >>
  irule gas_outcome_full_intro >>
  qexistsl_tac [`Gf`,`ee`,`[]`,`r`,`res`,`tnf`] >> simp[gasSummaryTheory.gas_explicit_def]
QED

(* After evaluating its input, either lowering uses the same call and result
   continuation. The input range can come from ALLOCA or DALLOCA. *)
Theorem raw_call_continuation_observed:
  expr_has_effect e /\ post_value_type cenv e = expr_type e /\
  lowered_value_type cenv e = expr_type e /\
  expr_type e = raw_call_return_type flags /\ type_alloc_ok cenv (expr_type e) /\
  ~(flags.rcf_is_delegate /\ flags.rcf_is_static) /\
  (flags.rcf_is_delegate ==> amount = 0) /\
  (flags.rcf_is_static ==> amount = 0) /\
  amount < dimword (:256) /\ flags.rcf_max_outsize < dimword (:256) /\
  expr_sim_inv cenv cx env esK /\ esK.gas_obs = [] /\
  storage_trace_domain cx st0 esK.storage_trace /\
  fn_has_code sa sb func /\ fn_has_code s6 sout func /\ fn_inst_ids_distinct func /\
  ci_mono sa s6 /\ ci_mono s6 s7 /\ ci_mono sout s7 /\ ci_mono sa s7 /\
  compile_raw_call_outbuf flags.rcf_max_outsize s6 = ((ov,op),sout) /\
  compile_raw_call_finish addr dp len gas
    (case ext_call_kwarg EKValue flags.rcf_kws xs of
      NONE => Lit 0w | SOME p => p)
    (if flags.rcf_is_delegate then DelegateCall
     else if flags.rcf_is_static then StaticCall else RegularCall)
    flags.rcf_max_outsize flags.rcf_revert_on_failure ov op s7 = (result,sb) /\
  vv = (if flags.rcf_max_outsize = 0
        then StackValue (raw_call_return_type flags) result
        else LocatedValue (raw_call_return_type flags) (mk_ptr result LocMemory)) /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H esK.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0) /\
  (!H. valid_horizon cx st0 H esK.storage_trace ==>
    stmt_state_rel H ctx func cenv cx esK t7 /\
    storage_well_formed_on cx esK (FST H) /\
    ghost_inv_at (DF H) lo dframe cenv cx esK G7 tn7 t7) /\
  return_buf_frame dframe cenv sa t7 /\
  wb_frame cenv es esK sa s0 t7 /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G7 tn7 /\
  ~t7.vs_halted /\ t7.vs_current_bb = s7.cs_current_bb /\
  t7.vs_inst_idx = LENGTH s7.cs_current_insts /\ alloca_history func t7 /\
  s0.vs_alloca_next <= t7.vs_alloca_next /\ lo <= t7.vs_alloca_next /\ allocas_from lo t7 /\
  eval_operand addr t7 = SOME (w2w target) /\
  eval_operand (case ext_call_kwarg EKValue flags.rcf_kws xs of
      NONE => Lit 0w | SOME p => p) t7 = SOME (n2w amount) /\
  eval_operand gas t7 = SOME gw /\
  (!g. OPTION_BIND (ext_call_kwarg EKGas flags.rcf_kws kvs) dest_NumV = SOME g ==>
       g = w2n gw) /\
  eval_operand dp t7 = SOME (n2w ib) /\ eval_operand len t7 = SOME (n2w (LENGTH bs)) /\
  ib < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  (LENGTH bs = 0 \/ ib + LENGTH bs <= t7.vs_alloca_next \/
   ctx_has_dalloca ctx /\
   w2n t7.vs_initial_fmp <= ib /\ ib + LENGTH bs <= w2n t7.vs_fmp) /\
  read_memory ib (LENGTH bs) t7 = bs /\
  (!j. ib <= j /\ j < ib + LENGTH bs ==> j NOTIN tn7.t_mem) /\
  (bs <> [] ==> ?p. dp = Var p /\ ptr_covers G7 tn7 p t7 (LENGTH bs)) /\
  eval_operand ov t7 = SOME (n2w ob) /\
  eval_operand op t7 = SOME (n2w (if flags.rcf_max_outsize = 0 then ob else ob + 32)) /\
  (flags.rcf_max_outsize = 0 ==> ov = op) /\
  ob + (if flags.rcf_max_outsize = 0 then 0
      else 32 * ((flags.rcf_max_outsize + 31) DIV 32) + 32) < dimword (:256) /\
  FLOOKUP t7.vs_allocas s6.cs_next_id = SOME (ob,(if flags.rcf_max_outsize = 0 then 0
      else 32 * ((flags.rcf_max_outsize + 31) DIV 32) + 32)) /\
  op_prov G7 ov = SOME (ob,(if flags.rcf_max_outsize = 0 then 0
      else 32 * ((flags.rcf_max_outsize + 31) DIV 32) + 32)) /\
  op_prov G7 op = SOME (ob,(if flags.rcf_max_outsize = 0 then 0
      else 32 * ((flags.rcf_max_outsize + 31) DIV 32) + 32)) /\
  op_taint tn7 ov = {} /\ op_taint tn7 op = {} /\
  (!name lb sz. local_region cenv esK.scopes t7 name lb sz ==>
    regions_disjoint ob (if flags.rcf_max_outsize = 0 then 0
      else 32 * ((flags.rcf_max_outsize + 31) DIV 32) + 32) lb sz) /\
  (cenv.ce_is_ctor ==> !name tv v off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP esK.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) ob (if flags.rcf_max_outsize = 0 then 0
      else 32 * ((flags.rcf_max_outsize + 31) DIV 32) + 32)) /\
  EVERY (\x. op_taint tn7 x = {})
    [addr;len;dp;gas;(case ext_call_kwarg EKValue flags.rcf_kws xs of
      NONE => Lit 0w | SOME p => p)] /\
  EVERY (safe_operand s7)
    [addr;len;dp;gas;(case ext_call_kwarg EKValue flags.rcf_kws xs of
      NONE => Lit 0w | SOME p => p);ov;op] /\
  (!x. MEM (Var x)
    [addr;len;dp;gas;(case ext_call_kwarg EKValue flags.rcf_kws xs of
      NONE => Lit 0w | SOME p => p);ov;op] ==> not_fresh_at s7 x) /\
  raw_call_finish_rule finish_ok /\
  (!r. exit_result r /\ gas_origin_edge T (gas_explicit_sites ctx shadow_ctx) ctx func t7 [] r ==>
       accept r) /\
  (!opc ops ok sc u r.
     emit_op opc ops s7 = (ok,sc) /\ MEM opc [CALL;STATICCALL;DELEGATECALL] /\
     fn_has_code s7 sc func /\ run_inst_seq (emitted_insts s7 sc) t7 = OK u /\
     finish_ok sc sb (gas_explicit_sites ctx shadow_ctx) ctx func
       (u with vs_inst_idx := LENGTH sc.cs_current_insts) r ==> accept r)
  ==>
  raw_call_observed_outcome accept (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0
    (eval_raw_call cx flags target bs amount (ext_call_kwarg EKGas flags.rcf_kws kvs))
    (esK,t7,G7,tn7)
        (\H res ee G tn t. ?tv. res = INL tv /\
          vv_post H ctx func cenv cx e es sa sb s0 ee tv vv t /\
          vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
            ee tv vv t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
          s0.vs_alloca_next <= t.vs_alloca_next /\
          ghost_inv_at (DF H) lo dframe cenv cx ee G tn t /\
          ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn t /\
          (!v. tv = Value v /\ ~is_word_type (post_value_type cenv e) /\
               ~is_bytestring_type (post_value_type cenv e) ==>
               vv_own cenv cx (post_value_type cenv e) sa sb ee (Value v) vv t /\
               (!t' p. vv = LocatedValue t' p ==>
                       p.ptr_location = LocMemory)) /\
          (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
           ?val. read_result cx tv ee = (INL val, ee) /\
                 !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) =
                          SOME rt /\
                        eval_operand (vv_operand vv) t = SOME w ==>
                        w2n w + type_memory_size rt <= lo /\
                        (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                               val_in_memory rt val (w2n w) mem)) /\
          (!t' op. vv = StackValue t' op /\
                   ~is_word_type (post_value_type cenv e) ==>
                   ptr_buf_ok cenv e op G t) /\
          (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
                  ptr_buf_ok cenv e p.ptr_operand G t) /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
        (\H res ee gt r.
          expr_exit res r /\ halt_exit H cx ee res r /\
          (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))

Proof
  simp_tac bool_ss [] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==>
      stmt_state_rel H ctx func cenv cx esK t7 /\ _`
    (qspec_then `storage_trace_horizon esK.storage_trace` mp_tac) >>
  impl_tac >-
    (qpat_assum `storage_trace_domain cx st0 esK.storage_trace` mp_tac >>
     simp[NoAsms,vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `stmt_state_rel (storage_trace_horizon esK.storage_trace) ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon cx st0 H esK.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0`
       (qspec_then `storage_trace_horizon esK.storage_trace` match_mp_tac) >>
     qpat_assum `storage_trace_domain cx st0 esK.storage_trace`
       (ACCEPT_TAC o REWRITE_RULE [vyperStorageFootprintTheory.storage_trace_domain_def])) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t7` by
    (qpat_assum `stmt_state_rel _ ctx func cenv cx esK t7`
       (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp)) >>
  `esK.outcomes = SOME t7.vs_outcomes` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ esK t7`
       (mp_tac o MATCH_MP stateRelProjTheory.stmt_state_rel_state_rel) >>
     simp[NoAsms,loweringStateRelDefsTheory.state_rel_def]) >>
  qabbrev_tac `vop = case ext_call_kwarg EKValue flags.rcf_kws xs of NONE => Lit 0w | SOME v => v` >>
  qabbrev_tac `stat = flags.rcf_is_static` >>
  qabbrev_tac `delegate = flags.rcf_is_delegate` >>
  qabbrev_tac `call_ty =
    if delegate then DelegateCall else if stat then StaticCall else RegularCall` >>
  `~(delegate /\ stat)` by simp[Abbr `delegate`, Abbr `stat`] >>
  `delegate ==> amount = 0` by simp[Abbr `delegate`] >>
  qabbrev_tac `cap = flags.rcf_max_outsize` >>
  qabbrev_tac `opc = case call_ty of RegularCall => CALL | StaticCall => STATICCALL | DelegateCall => DELEGATECALL` >>
  qabbrev_tac `ops = if call_ty = RegularCall then [gas;addr;vop;dp;len;op;Lit (n2w cap)]
                      else [gas;addr;dp;len;op;Lit (n2w cap)]` >>
  `?ok sc. emit_op opc ops s7 = (ok,sc) /\ cs_extends sc sb` by
    (drule raw_call_finish_prefix >>
     disch_then (qx_choose_then `ok` (qx_choose_then `sc` strip_assume_tac)) >>
     qexistsl [`ok`,`sc`] >> simp[Abbr `opc`, Abbr `ops`] >>
     qpat_assum `_ s7 = (ok,sc)` mp_tac >>
     Cases_on `call_ty` >> simp[NoAsms]) >>
  `fn_has_code s7 sc func` by
    (irule fn_has_code_mid >> conj_tac
     >- metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND] >>
     qexistsl [`sb`,`sa`] >> simp[] >>
     qpat_assum `ci_mono sa s7` (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [ci_mono_def])) >>
  qabbrev_tac `inst = mk_inst s7.cs_next_id opc ops
    [STRING #"%" (toString s7.cs_next_var)]` >>
  `?bb. lookup_block t7.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb t7.vs_inst_idx = SOME inst` by
    (drule_all bodyPtrMakeArrayEmissionTheory.emit_op_fetch_boundary >>
     simp[Abbr `inst`] >> metis_tac[]) >>
  `op_taint tn7 (Lit (n2w cap)) = {}` by simp[op_taint_def] >>
  `EVERY (\p. op_taint tn7 p = {}) inst.inst_operands` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`EVERY _ [addr;len;dp;gas;vop]`,`op_taint tn7 op = _`,
        `op_taint tn7 (Lit (n2w cap)) = _`] >>
     Cases_on `call_ty` >>
     simp[NoAsms, Abbr `inst`,Abbr `ops`,Abbr `opc`,mk_inst_def] >>
     tautLib.TAUT_TAC) >>
  qmatch_goalsub_abbrev_tac `raw_call_observed_outcome accept _ _ _ _ _ QS RS` >>
  qabbrev_tac `round = 32 * ((cap + 31) DIV 32)` >>
  qabbrev_tac `ro = if cap = 0 then ob else ob + 32` >>
  `cap <= round` by simp[Abbr `round`,spillSimTheory.n_le_round_up_32] >>
  `ro < dimword (:256)` by
    (qpat_assum `ob + (if cap = 0 then 0 else round + 32) < _` mp_tac >>
     qpat_assum `Abbrev (ro = _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `cap = 0` >> simp[markerTheory.Abbrev_def] >> decide_tac) >>
  `w2n (n2w ro : bytes32) = ro /\ w2n (n2w cap : bytes32) = cap /\
   w2n (n2w ib : bytes32) = ib /\
   w2n (n2w (LENGTH bs) : bytes32) = LENGTH bs /\
   w2n (n2w amount : bytes32) = amount` by simp[w2n_n2w] >>
  qpat_assum `stmt_state_rel _ _ _ _ _ esK t7`
    (mp_tac o MATCH_MP stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `(cap <> 0 ==> ro + cap <= t7.vs_alloca_next)` by
    (strip_tac >> simp[Abbr `ro`] >>
     `ob + (round + 32) <= t7.vs_alloca_next` by
       (irule allocaSiteResourceTheory.alloca_site_registered_below >>
        simp[] >> qexists `s6.cs_next_id` >> simp[]) >> decide_tac) >>
  `(cap <> 0 ==> ?p. op = Var p /\ ptr_covers G7 tn7 p t7 cap)` by
    (strip_tac >>
     `op_prov G7 op = SOME (ob,round + 32)` by simp[] >>
     `ob <= ro /\ ro + cap <= ob + (round + 32)` by
       (simp[Abbr `ro`] >> decide_tac) >>
     qpat_assum `op_prov G7 op = SOME (ob,round + 32)` mp_tac >>
     qpat_assum `eval_operand op t7 = _` mp_tac >>
     qpat_assum `op_taint tn7 op = _` mp_tac >>
     qpat_assum `w2n (n2w ro : bytes32) = _` mp_tac >>
     qpat_assum `ob <= ro` mp_tac >>
     qpat_assum `ro + cap <= _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `op` >> simp[op_prov_def,eval_operand_def,ptr_covers_def]) >>
  `mem_safe_step 0 ctx inst t7` by
    (`source_memory_read_ranges inst t7 = [(ib,LENGTH bs)] /\
      source_memory_write_ranges inst t7 = [(ro,cap)] /\
      inst_dload_in_section inst t7 /\ inst.inst_opcode <> INVOKE /\
      inst.inst_opcode <> DALLOCA` by
       (Cases_on `call_ty` >>
        simp[Abbr `inst`, Abbr `ops`, Abbr `opc`, mk_inst_def,
             source_memory_read_ranges_def, source_memory_write_ranges_def,
             mem_read_ops_def, mem_write_ops_def, memory_range_of_operands_def,
             eval_operand_def, inst_dload_in_section_def]) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`LENGTH bs = 0 \/ ib + _ <= _ \/ _`, `cap <> 0 ==> ro + cap <= _`,
        `source_memory_read_ranges inst t7 = _`, `source_memory_write_ranges inst t7 = _`,
        `inst_dload_in_section inst t7`, `inst.inst_opcode <> INVOKE`,
        `inst.inst_opcode <> DALLOCA`] >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[mem_safe_step_non_invoke, inst_mem_below_frontiers_def,
          inst_mem_below_frontier_def] >> tautLib.TAUT_TAC) >>
  `t7.vs_call_ctx.cc_static = cx.txn.is_static` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ esK t7`
       (mp_tac o MATCH_MP stateRelProjTheory.state_rel_call_ctx_rel o
        MATCH_MP stateRelProjTheory.stmt_state_rel_state_rel) >>
     simp[loweringStateRelDefsTheory.call_ctx_rel_def]) >>
  Cases_on `t7.vs_outcomes = [] \/ (cx.txn.is_static /\ amount <> 0)`
  >- (qabbrev_tac `err = if cx.txn.is_static /\ amount <> 0
                         then "write in static context" else "take_call_outcome"` >>
      `!tail. eval_raw_call cx flags target bs amount
         (ext_call_kwarg EKGas flags.rcf_kws kvs) (esK with gas_obs := tail) =
         (INR (Error (RuntimeError err)),esK with gas_obs := tail)` by
        (gen_tac >> Cases_on `cx.txn.is_static /\ amount <> 0`
         >- (simp[Abbr `err`] >> irule raw_call_static_value_abort >>
             qpat_assum `delegate ==> amount = 0` mp_tac >>
             qpat_assum `stat ==> amount = 0` mp_tac >>
             qpat_assum `cx.txn.is_static /\ amount <> 0` mp_tac >>
             simp_tac bool_ss [Abbr `stat`, Abbr `delegate`] >>
             POP_ASSUM_LIST (K ALL_TAC) >> tautLib.TAUT_TAC) >>
         simp[Abbr `err`] >>
         irule raw_call_oracle_empty >>
         qunabbrev_tac `delegate` >> qunabbrev_tac `stat` >>
         qpat_x_assum `~(cx.txn.is_static /\ amount <> 0)` mp_tac >>
         map_every (fn pat => qpat_assum pat mp_tac)
           [`~(flags.rcf_is_delegate /\ flags.rcf_is_static)`,
            `flags.rcf_is_delegate ==> amount = 0`,
            `flags.rcf_is_static ==> amount = 0`,
            `esK.outcomes = SOME t7.vs_outcomes`,
            `t7.vs_outcomes = [] \/ (cx.txn.is_static /\ amount <> 0)`] >>
         POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> tautLib.TAUT_TAC) >>
      Q.SUBGOAL_THEN `t7.vs_outcomes = [] \/
         (call_ty = RegularCall /\ t7.vs_call_ctx.cc_static /\ (n2w amount : bytes32) <> 0w)` ASSUME_TAC
       >- (simp[GSYM w2n_eq_0, Abbr `call_ty`] >>
           qpat_x_assum `delegate ==> amount = 0` mp_tac >>
           qpat_assum `stat ==> amount = 0` mp_tac >>
           qpat_assum `t7.vs_outcomes = [] \/ (cx.txn.is_static /\ amount <> 0)` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           Cases_on `delegate` >> Cases_on `stat` >> simp[] >> tautLib.TAUT_TAC) >>
      irule raw_call_observed_exit >> reverse conj_tac >- simp[] >>
      qexistsl_tac [`G7`,`esK`,`Abort ExHalt_abort (halt_state (set_returndata [] t7))`,
                    `INR (Error (RuntimeError err))`,`tn7`] >>
      simp[exit_result_def,Abbr `RS`,exprSimDefsTheory.expr_exit_def,
           exprSimDefsTheory.halt_exit_def] >>
      rpt (gen_tac ORELSE disch_tac) >>
      `inst = mk_inst s7.cs_next_id (case call_ty of
           RegularCall => CALL | StaticCall => STATICCALL | DelegateCall => DELEGATECALL)
         (if call_ty = RegularCall then [gas;addr;vop;dp;len;op;Lit (n2w cap)]
          else [gas;addr;dp;len;op;Lit (n2w cap)])
         [STRING #"%" (toString s7.cs_next_var)]` by
        simp[Abbr `inst`,Abbr `opc`,Abbr `ops`] >>
      qmatch_goalsub_abbrev_tac `gas_origin_ptr_path (deadH,_,_,_,_,_) _ _ _` >>
      mp_tac (Q.INST [`t` |-> `t7`, `G` |-> `G7`, `tn` |-> `tn7`,
          `D` |-> `deadH`, `explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
          `value` |-> `vop`, `dl` |-> `len`, `id` |-> `s7.cs_next_id`,
          `out` |-> `STRING #"%" (toString s7.cs_next_var)`, `vw` |-> `n2w amount`,
          `rw` |-> `n2w ro`, `nw` |-> `n2w (LENGTH (bs:word8 list))`, `iw` |-> `n2w ib`,
          `aw` |-> `w2w (target:160 word)`] raw_call_fetched_early_exit) >>
      impl_tac >-
        (FILTER_ASM_REWRITE_TAC
           (can (match_term ``w2n (n2w _ : bytes32) = _``)) [] >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         once_rewrite_tac[GSYM w2n_eq_0] >>
         FILTER_ASM_REWRITE_TAC
           (can (match_term ``w2n (n2w _ : bytes32) = _``)) [] >>
         simp_tac bool_ss [listTheory.LENGTH_NIL] >>
         TRY (first_assum ACCEPT_TAC) >>
         TRY (qpat_assum `!j. ib <= j /\ j < _ ==> _` ACCEPT_TAC) >>
         TRY (qpat_assum `(cap <> 0 ==> _)` ACCEPT_TAC)) >>
      strip_tac >> simp[] >>
      qpat_assum `!r. exit_result r /\ gas_origin_edge _ _ _ _ _ _ r ==> _`
        irule >> simp[exit_result_def]) >>
  `(cx.txn.is_static ==> amount = 0) /\ esK.outcomes <> SOME []` by
    (qpat_assum `~(t7.vs_outcomes = [] \/ _)` mp_tac >>
     qpat_assum `esK.outcomes = _` (fn th => rewrite_tac [th]) >>
     simp[] >> tautLib.TAUT_TAC) >>
  `outcomes_accounts_typed esK.outcomes /\ IS_SOME esK.outcomes /\
   accounts_runtime_well_typed esK.accounts` by
    (qpat_assum `expr_sim_inv cenv cx env esK`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [exprSimHypsDefsTheory.expr_sim_inv_def]) >>
     simp[NoAsms, vyperTypeExtCallCoreTheory.accounts_runtime_well_typed_accounts_well_typed] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`es` |-> `esK`, `bytes` |-> `bs`,
     `gas` |-> `ext_call_kwarg EKGas flags.rcf_kws kvs`] raw_call_kind_source_tail) >>
  (impl_tac >- (simp[Abbr `stat`, Abbr `delegate`] >> metis_tac[])) >>
  disch_then (DISJ_CASES_THEN2 (assume_tac o CONJUNCT1)
    (qx_choose_then `rq` (qx_choose_then `outcome` (qx_choose_then `es1`
      (qx_choose_then `es2` (map_every assume_tac o CONJUNCTS))))))
  >- (qpat_assum `esK.outcomes <> SOME []` mp_tac >>
      qpat_assum `esK.outcomes = SOME []` (fn th => rewrite_tac [th]) >> simp[]) >>
  qabbrev_tac `value_opt = if stat \/ cx.txn.is_static then NONE else SOME amount` >>
  qabbrev_tac `gas_cap = OPTION_BIND (ext_call_kwarg EKGas flags.rcf_kws kvs) dest_NumV` >>
  `(call_ty = DelegateCall) = flags.rcf_is_delegate` by
    (simp[Abbr `call_ty`, Abbr `delegate`] >>
     Cases_on `flags.rcf_is_delegate` >> Cases_on `stat` >> simp[]) >>
  `(if call_ty = DelegateCall then take_delegate_outcome else take_call_outcome)
     gas_cap target
     (read_memory (w2n (n2w ib : bytes32)) (w2n (n2w (LENGTH bs) : bytes32)) t7)
     value_opt esK = (INL (rq,outcome),es1)` by
    (qpat_assum `(if flags.rcf_is_delegate then _ else _) gas_cap target bs _ esK = _` mp_tac >>
     qpat_assum `(call_ty = DelegateCall) = flags.rcf_is_delegate` (fn kind =>
     qpat_assum `w2n (n2w ib:bytes32) = ib` (fn start =>
     qpat_assum `w2n (n2w (LENGTH bs):bytes32) = LENGTH bs` (fn size =>
     qpat_assum `read_memory ib (LENGTH bs) t7 = bs` (fn memory =>
       simp[NoAsms, kind, start, size, memory, Abbr `value_opt`, Abbr `stat`]))))) >>
  `(call_ty = StaticCall \/ cx.txn.is_static) = IS_NONE value_opt /\
   w2n (if call_ty = RegularCall then n2w amount else 0w : bytes32) =
     (case value_opt of NONE => 0 | SOME n => n)` by
    (map_every (fn pattern => qpat_assum pattern mp_tac)
       [`~(delegate /\ stat)`, `delegate ==> amount = 0`,
        `stat ==> amount = 0`, `cx.txn.is_static ==> amount = 0`,
        `w2n (n2w amount : bytes32) = amount`] >>
     simp[NoAsms, Abbr `value_opt`, Abbr `call_ty`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `delegate` >> Cases_on `stat` >> Cases_on `cx.txn.is_static` >> simp[]) >>
  `emit_op (case call_ty of
           RegularCall => CALL | StaticCall => STATICCALL | DelegateCall => DELEGATECALL)
    (if call_ty = RegularCall then [gas;addr;vop;dp;len;op;Lit (n2w cap)]
     else [gas;addr;dp;len;op;Lit (n2w cap)]) s7 = (ok,sc) /\
   inst = mk_inst s7.cs_next_id (case call_ty of
           RegularCall => CALL | StaticCall => STATICCALL | DelegateCall => DELEGATECALL)
    (if call_ty = RegularCall then [gas;addr;vop;dp;len;op;Lit (n2w cap)]
     else [gas;addr;dp;len;op;Lit (n2w cap)])
     [STRING #"%" (toString s7.cs_next_var)]` by simp[Abbr `inst`, Abbr `opc`, Abbr `ops`] >>
  `local_ptrs_reserved cenv s7 /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s7 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s7 x)` by
    (rpt conj_tac >> rpt strip_tac >>
     metis_tac[exprOperandVarTheory.compiler_ci_mono_reserved,
               exprOperandVarTheory.compiler_ci_mono_not_fresh]) >>
  Q.SUBGOAL_THEN `cap = 0 \/ lo <= ro` ASSUME_TAC
  >- (Cases_on `cap = 0` >> simp[Abbr `ro`] >>
      qpat_assum `allocas_from lo t7` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
      disch_then (qspec_then `s6.cs_next_id` mp_tac) >> simp[]) >>
  `!name lb sz. local_region cenv esK.scopes t7 name lb sz ==>
       regions_disjoint ro cap lb sz` by
    (rpt strip_tac >>
     qpat_assum `!name lb sz. local_region _ _ _ name lb sz ==> regions_disjoint ob _ lb sz`
       drule >>
     Cases_on `cap = 0` >> simp[Abbr `ro`, loweringStateRelDefsTheory.regions_disjoint_def] >>
     decide_tac) >>
  `cenv.ce_is_ctor ==> !name tv v off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP esK.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
     off + type_memory_size tv <= ro \/ ro + cap <= off` by
    (strip_tac >>
     qpat_assum `_ ==> !name tv v off. _ ==> regions_disjoint off _ ob _` drule >>
     disch_then (fn th => rpt gen_tac >> strip_tac >> drule_all th) >>
     Cases_on `cap = 0` >> simp[Abbr `ro`, loweringStateRelDefsTheory.regions_disjoint_def] >>
     decide_tac) >>
  `w2w (w2w target : bytes32) = target` by wordsLib.WORD_DECIDE_TAC >>
  `!g. gas_cap = SOME g ==> g = w2n gw` by simp[Abbr `gas_cap`] >>
  `((n2w (LENGTH bs) : bytes32) <> 0w ==>
      ?p. dp = Var p /\ ptr_covers G7 tn7 p t7 (LENGTH bs))` by
    (PURE_ONCE_REWRITE_TAC[GSYM w2n_eq_0] >>
     qpat_assum `w2n (n2w (LENGTH bs) : bytes32) = LENGTH bs`
       (fn th => rewrite_tac[th, listTheory.LENGTH_NIL]) >>
     first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H esK.storage_trace ==>
    ?u. run_inst_seq (emitted_insts s7 sc) t7 = OK u /\
      stmt_state_rel H ctx func cenv cx es2 u /\
      u.vs_memory = (write_memory_with_expansion ro
        (TAKE cap outcome.co_returnData) t7).vs_memory /\
      u.vs_returndata = outcome.co_returnData /\
      u.vs_allocas = t7.vs_allocas /\ u.vs_alloca_next = t7.vs_alloca_next /\
      u.vs_fmp = t7.vs_fmp /\
      (!p. safe_operand s7 p ==> eval_operand p u = eval_operand p t7) /\
      let Gq = step_prov PG G7 inst u;
          tnq = step_taint inst t7 u tn7;
          q = u with vs_inst_idx := LENGTH sc.cs_current_insts
      in gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
           (t7,G7,tn7) [] (OK q,Gq,tnq) /\
         ghost_inv_at (DF H) lo dframe cenv cx es2 Gq tnq q /\
         ghost_kept_at lo cenv esK s7 G7 tn7 t7 Gq tnq /\
         eval_operand ok q = SOME (bool_to_word outcome.co_success) /\
         op_taint tnq ok = {} /\ op_prov Gq ok = NONE /\
         tnq.t_mem = tn7.t_mem DIFF
           {j | ro <= j /\ j < ro + LENGTH (TAKE cap outcome.co_returnData)}` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H esK.storage_trace ==> _` drule >>
     strip_tac >>
     raw_call_at
       `stmt_state_rel H ctx func cenv cx esK t7`
       `ghost_inv_at (DF H) lo dframe cenv cx esK G7 tn7 t7`
       (qx_choose_then `u` (map_every assume_tac o CONJUNCTS)) >>
     qexists_tac `u` >>
     simp_tac bool_ss [LET_THM] >> BETA_TAC >>
     qpat_assum `adopt_call_outcome _ _ _ = _` (fn adopt =>
       qpat_assum `w2n (n2w ro : bytes32) = ro` (fn offset =>
         rpt conj_tac >>
         first_assum (ACCEPT_TAC o REWRITE_RULE [adopt,offset,pairTheory.SND])))) >>
  qpat_assum `!H. valid_horizon cx st0 H esK.storage_trace ==> ?u. _`
    (qspec_then `storage_trace_horizon esK.storage_trace` mp_tac) >>
  impl_tac >-
    (qpat_assum `storage_trace_domain cx st0 esK.storage_trace`
       (ACCEPT_TAC o REWRITE_RULE [vyperStorageFootprintTheory.storage_trace_domain_def])) >>
  disch_then (qx_choose_then `u` (map_every assume_tac o CONJUNCTS o BETA_RULE o
    REWRITE_RULE [LET_THM])) >>
  `!H. valid_horizon cx st0 H es2.storage_trace ==>
    valid_horizon cx st0 H esK.storage_trace /\ storage_well_formed_on cx es2 (FST H)` by
    (gen_tac >> strip_tac >>
     `valid_horizon cx st0 H esK.storage_trace` by
       (qpat_assum `eval_raw_call _ _ _ _ _ _ esK = _`
          (mp_then (Pat `_ _ = (_,_)`) mp_tac vyperStorageFootprintTheory.valid_horizon_frame) >>
        simp[storage_trace_frame_raw_call]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `!H. valid_horizon cx st0 H esK.storage_trace ==>
       stmt_state_rel H ctx func cenv cx esK t7 /\ _` drule >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `eval_raw_call _ _ _ _ _ _ esK = _`
       (mp_then (Pat `eval_raw_call _ _ _ _ _ _ _ = _`) mp_tac
          vyperFiniteStoragePreservationTheory.eval_raw_call_preserves_storage_well_formed_on) >>
     disch_then (qspec_then `H` mp_tac) >>
     impl_tac >-
       (qpat_assum `valid_horizon cx st0 H es2.storage_trace`
          (mp_tac o REWRITE_RULE [vyperStorageFootprintTheory.valid_horizon_def]) >>
        rpt strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  qabbrev_tac `q = u with vs_inst_idx := LENGTH sc.cs_current_insts` >>
  qabbrev_tac `Gq = step_prov PG G7 inst u` >>
  qabbrev_tac `tnq = step_taint inst t7 u tn7` >>
  `emitted_insts s7 sc = [inst] /\
    ok = Var (STRING #"%" (toString s7.cs_next_var)) /\
    sc.cs_next_var = s7.cs_next_var + 1 /\
    sc.cs_next_id = s7.cs_next_id + 1` by
    (qpat_assum `emit_op opc ops s7 = (ok,sc)`
       (mp_tac o MATCH_MP emitted_insts_emit_op_local) >>
     qunabbrev_tac `inst` >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts s7 sc)` by
    (qunabbrev_tac `inst` >> qunabbrev_tac `opc` >>
     qpat_assum `emitted_insts s7 sc = [mk_inst _ _ _ _]` SUBST1_TAC >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `call_ty` >> simp[mk_inst_def,is_terminator_def]) >>
  `~q.vs_halted /\ q.vs_current_bb = sc.cs_current_bb /\
   q.vs_inst_idx = LENGTH sc.cs_current_insts /\ alloca_history func q` by
    (qpat_assum `emit_op opc ops s7 = (ok,sc)`
       (strip_assume_tac o REWRITE_RULE [same_blocks_def] o MATCH_MP emit_op_extends) >>
     qpat_assum `run_inst_seq (emitted_insts s7 sc) t7 = OK u` (fn run =>
       qpat_assum `EVERY _ (emitted_insts s7 sc)` (fn safe =>
         let val premises = CONJ run safe in
           assume_tac (MATCH_MP run_inst_seq_preserves_halted premises) >>
           assume_tac (MATCH_MP bodyPtrHashBuiltinsCursorTheory.hash_run_inst_seq_current_bb premises)
         end)) >>
     conj_tac >-
       (simp[NoAsms,Abbr `q`] >> asm_rewrite_tac[]) >>
     conj_tac >-
       (simp[NoAsms,Abbr `q`] >> asm_rewrite_tac[]) >>
     conj_tac >- simp[NoAsms,Abbr `q`] >>
     qunabbrev_tac `q` >>
     mp_tac (Q.SPECL [`emitted_insts s7 sc`,`s7`,`sc`,`t7`,`u`]
       bodyFullUnwrapRunTheory.emitted_alloca_history) >>
     impl_tac
     >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         qpat_assum `EVERY _ (emitted_insts s7 sc)` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> simp[listTheory.EVERY_MEM]) >>
     disch_then ACCEPT_TAC) >>
  `es2.scopes = esK.scopes` by
    (qpat_assum `(if call_ty = DelegateCall then take_delegate_outcome else take_call_outcome)
     gas_cap target _ value_opt esK = _`
       (mp_tac o MATCH_MP raw_call_kind_take_adopt_fields) >>
     qpat_assum `adopt_call_outcome rq outcome es1 = _`
       (fn th => rewrite_tac[th,pairTheory.SND]) >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  `wb_frame cenv es es2 sa s0 t7` by
    (qpat_assum `wb_frame cenv es esK sa s0 t7` mp_tac >>
     pure_rewrite_tac[loweringPostsTheory.wb_frame_def,
       loweringPostsTheory.locals_kept_def,loweringPostsTheory.popped_kept_def] >>
     qpat_assum `es2.scopes = esK.scopes` (fn th => pure_rewrite_tac[th]) >>
     disch_then ACCEPT_TAC) >>
  `MAP FDOM es.scopes = MAP FDOM esK.scopes` by
    (qpat_assum `wb_frame cenv es esK sa s0 t7`
       (mp_tac o REWRITE_RULE [loweringPostsTheory.wb_frame_def,
                             loweringPostsTheory.locals_kept_def]) >>
     rpt strip_tac >> simp[]) >>
  `wb_frame cenv es es2 sa s0 q` by
    (simp[NoAsms,Abbr `q`,raw_call_wb_frame_inst_idx] >>
     mp_tac (Q.INST [`cenv` |-> `cenv`, `es` |-> `es`,
       `es'` |-> `es2`, `sa` |-> `sa`, `sm` |-> `s6`,
       `s0` |-> `s0`, `s` |-> `t7`, `t` |-> `u`,
       `scopes` |-> `esK.scopes`] exprSimHashTheory.wb_frame_allocating_tail) >>
     impl_tac >-
     (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (qpat_assum `ci_mono sa s6` (ACCEPT_TAC o cj 2 o REWRITE_RULE [ci_mono_def]))
     >- (qpat_assum `ci_mono sa s6` (ACCEPT_TAC o cj 3 o REWRITE_RULE [ci_mono_def]))
     >- (rpt strip_tac >>
         `safe_operand s7 (Var x)` by
           (simp[NoAsms,exprSafeOperandTheory.safe_operand_def] >>
            qpat_assum `ci_mono s6 s7`
              (mp_then Any irule exprOperandVarTheory.compiler_ci_mono_not_fresh) >>
            first_assum ACCEPT_TAC) >>
         qpat_assum `!p. safe_operand s7 p ==> _`
           (qspec_then `Var x` mp_tac) >>
         impl_tac >- first_assum ACCEPT_TAC >>
         simp_tac bool_ss [venomStateTheory.eval_operand_def])
     >- (qpat_assum `u.vs_allocas = t7.vs_allocas` (fn th => rewrite_tac[th]) >>
         rpt strip_tac >> first_assum ACCEPT_TAC)
     >- (rpt strip_tac >>
         rename1 `mem_bytes_at old_base old_size u.vs_memory = _` >>
         `aid <> s6.cs_next_id` by decide_tac >>
         qpat_assum `alloca_inv t7` (fn inv =>
           qpat_assum `aid <> s6.cs_next_id` (fn distinct =>
             qpat_assum `FLOOKUP t7.vs_allocas aid = SOME (old_base,old_size)` (fn old =>
               qpat_assum `FLOOKUP t7.vs_allocas s6.cs_next_id = SOME (ob,_)` (fn fresh =>
                 mp_tac (foldl (fn (premise,rule) => MATCH_MP rule premise)
                   (REWRITE_RULE [GSYM AND_IMP_INTRO]
                     allocaSiteResourceTheory.alloca_site_registered_disjoint)
                   [inv,distinct,old,fresh]))))) >>
         qpat_assum `u.vs_memory = _` (fn th => rewrite_tac[th]) >>
         disch_then (assume_tac o REWRITE_RULE [venomMemDefsTheory.regions_disjoint_def]) >>
         Cases_on `cap = 0`
         >- (qpat_assum `cap = 0`
               (fn th => simp[NoAsms,th,raw_call_empty_write_memory])) >>
         Cases_on `old_size = 0`
         >- (qpat_assum `old_size = 0`
               (fn th => simp[NoAsms,th,valueEncodingDefsTheory.mem_bytes_at_def])) >>
         irule exprSimHashTheory.hash_write_memory_disjoint >>
         qpat_x_assum `old_size = 0 \/ _ = 0 \/ old_base + old_size <= ob \/ _` mp_tac >>
         qpat_assum `cap <= round` mp_tac >>
         qpat_assum `~(old_size = 0)` (fn old_nonzero =>
           qpat_assum `~(cap = 0)` (fn cap_nonzero =>
             simp[NoAsms,old_nonzero,cap_nonzero,Abbr `ro`,
                  listTheory.LENGTH_TAKE_EQ,arithmeticTheory.MIN_DEF])) >>
         IF_CASES_TAC >> decide_tac)
     >- (rpt strip_tac >>
         qpat_assum `!name lb sz. local_region cenv esK.scopes t7 name lb sz ==> _`
           (drule_then strip_assume_tac) >>
         qpat_assum `u.vs_memory = _` (fn th => rewrite_tac[th]) >>
         irule exprSimHashTheory.hash_write_memory_disjoint >>
         qpat_assum `loweringStateRelDefs$regions_disjoint ro cap _ _`
           (mp_tac o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def]) >>
         POP_ASSUM_LIST (K ALL_TAC) >>
         simp[listTheory.LENGTH_TAKE_EQ,arithmeticTheory.MIN_DEF] >>
         IF_CASES_TAC >> decide_tac)) >>
     disch_then ACCEPT_TAC) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gq tnq` by
    (mp_tac (Q.SPECL [`lo`,`cenv`,`es`,`sa`,`G0`,`tn0`,`s0`,`G7`,`tn7`,
       `esK`,`s7`,`Gq`,`tnq`,`t7`,
       `storage_trace_horizon esK.storage_trace`,`ctx`,`func`,`cx`,`es2`]
       (INST_TYPE [alpha |-> ``:num # num``, beta |-> ``:256``]
         wordArgsPtrTheory.ghost_kept_at_wb_trans)) >>
     impl_tac
     >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         TRY (qpat_assum `ci_mono sa s7`
           (fn th => FIRST (map ACCEPT_TAC (CONJUNCTS (REWRITE_RULE [ci_mono_def] th))))) >>
         qpat_assum `ghost_kept_at lo cenv esK s7 G7 tn7 t7 _ _` mp_tac >>
         simp[NoAsms,Abbr `Gq`,Abbr `tnq`]) >>
     disch_then ACCEPT_TAC) >>
  qabbrev_tac `rev = flags.rcf_revert_on_failure` >>
  qabbrev_tac `payload = 32 + ((cap + 31) DIV 32) * 32` >>
  `payload = round + 32` by
    (simp_tac bool_ss [Abbr `payload`,Abbr `round`] >>
     CONV_TAC (RAND_CONV (LAND_CONV (REWR_CONV arithmeticTheory.MULT_COMM))) >>
     MATCH_ACCEPT_TAC arithmeticTheory.ADD_COMM) >>
  `ci_mono s7 sc` by
    (mp_tac (Q.SPECL [`opc`,`ops`,`s7`] ci_mono_emit_op) >>
     qpat_assum `emit_op opc ops s7 = (ok,sc)` (fn th => rewrite_tac[th,pairTheory.SND]) >>
     disch_then ACCEPT_TAC) >>
  `ci_mono sa sc` by
    (irule ci_mono_trans >> qexists_tac `s7` >> simp[]) >>
  `fn_has_code sc sb func` by
    (qpat_assum `fn_has_code sa sb func` mp_tac >>
     qpat_assum `cs_extends sc sb` mp_tac >>
     qpat_assum `ci_mono sa s6` mp_tac >>
     qpat_assum `ci_mono s6 s7` mp_tac >>
     qpat_assum `ci_mono s7 sc` mp_tac >>
     qpat_assum `ci_mono sa sc` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rewrite_tac[ci_mono_def] >>
     rpt (disch_then (map_every assume_tac o CONJUNCTS)) >>
     irule fn_has_code_mid >> simp[] >> qexistsl [`sb`,`sa`] >>
     simp[compileEnvTheory.cs_extends_refl]) >>
  `local_ptrs_reserved cenv s6 /\ local_ptrs_reserved cenv sc` by
    (qpat_assum `local_ptrs_reserved cenv sa` mp_tac >>
     qpat_assum `ci_mono sa s6` mp_tac >>
     qpat_assum `ci_mono sa sc` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[exprOperandVarTheory.compiler_ci_mono_reserved]) >>
  `compile_raw_call_finish addr dp len gas vop call_ty
      cap rev ov op s7 = (result,sb)` by
    simp[Abbr `call_ty`,Abbr `stat`,Abbr `delegate`,
         Abbr `cap`,Abbr `rev`,Abbr `vop`] >>
  `expr_type e =
      (if cap = 0 then if rev then NoneT else BaseT BoolT
       else if rev then BaseT (BytesT (Dynamic cap))
       else TupleT [BaseT BoolT;BaseT (BytesT (Dynamic cap))])` by
    (Cases_on `flags.rcf_max_outsize = 0` >> Cases_on `flags.rcf_revert_on_failure` >>
     simp[Abbr `cap`, Abbr `rev`, vyperTypeSystemTheory.raw_call_return_type_def]) >>
  `0 < cap ==> 32 + payload < dimword (:256)` by
    (simp[NoAsms,Abbr `payload`,Abbr `cap`] >> strip_tac >>
     `type_alloc_ok cenv (raw_call_return_type flags)` by
       (qpat_assum `expr_type e = raw_call_return_type flags`
           (fn th => rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
     qpat_assum `type_alloc_ok _ (raw_call_return_type flags)` mp_tac >>
     qpat_assum `0 < flags.rcf_max_outsize` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     Cases_on `flags.rcf_revert_on_failure` >>
     gvs[vyperTypeSystemTheory.raw_call_return_type_def,allocLimitsTheory.type_alloc_ok_def,compileEnvTheory.is_word_type_def,compileEnvTheory.type_memory_bytes_def] >>
     `2 ** 64 + 64 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
     decide_tac) >>
  `q.vs_returndata = outcome.co_returnData /\ q.vs_allocas = t7.vs_allocas /\
    q.vs_alloca_next = t7.vs_alloca_next` by
    (simp[NoAsms,Abbr `q`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `allocas_from lo q` by
    (qpat_assum `allocas_from lo t7` mp_tac >>
     qpat_assum `q.vs_allocas = t7.vs_allocas` (fn th => rewrite_tac[allocas_from_def,th]) >>
     simp[NoAsms,allocas_from_def]) >>
  `lo <= q.vs_alloca_next /\ s0.vs_alloca_next <= q.vs_alloca_next` by simp[] >>
  `LENGTH q.vs_returndata < dimword (:256)` by
    (qpat_assum `q.vs_returndata = outcome.co_returnData` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `eval_operand ok q = SOME (if outcome.co_success then 1w else 0w)` by
    (`bool_to_word outcome.co_success = (if outcome.co_success then 1w else 0w)` by
       (POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `outcome.co_success` >> simp[bool_to_word_def]) >>
     qpat_assum `eval_operand ok _ = SOME (bool_to_word outcome.co_success)` mp_tac >>
     qpat_assum `bool_to_word outcome.co_success = _` (fn th => rewrite_tac[th]) >>
     simp[NoAsms,Abbr `q`]) >>
  `op_taint tnq ok = {} /\ op_prov Gq ok = NONE` by
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     simp[NoAsms,Abbr `tnq`,Abbr `Gq`] >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel (storage_trace_horizon esK.storage_trace) ctx func cenv cx es2 q` by
    (simp[NoAsms,Abbr `q`,stmt_state_rel_inst_idx] >> first_assum ACCEPT_TAC) >>
  `0 < cap /\ (~rev \/ outcome.co_success) ==>
     ?x w alloc var pre (offset:bytes32) old_tn.
       ov = Var x /\ cap < dimword (:256) /\ 32 + payload < dimword (:256) /\
       MEM alloc (fn_insts func) /\ alloc.inst_opcode = ALLOCA /\
       alloc.inst_outputs = [var] /\ not_local_ptr cenv es2.scopes var /\
       FLOOKUP q.vs_allocas alloc.inst_id = SOME (w2n w,payload) /\
       local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sc /\
       sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= alloc.inst_id /\
       alloc.inst_id < sc.cs_next_id /\ MAP FDOM es.scopes = MAP FDOM es2.scopes /\
       not_fresh_at sc x /\ lookup_var x q = SOME w /\ ptr_covers Gq tnq x q payload /\
       w2n offset = w2n w + 32 /\
       q.vs_memory = (write_memory_with_expansion (w2n offset)
         (TAKE cap q.vs_returndata) pre).vs_memory /\
       tnq.t_mem = old_tn.t_mem DIFF
         {i | w2n offset <= i /\ i < w2n offset + LENGTH (TAKE cap q.vs_returndata)} /\
       (~rev ==> safe_operand sc ok /\ evaluate_type (get_tenv cx) (expr_type e) =
         SOME (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic cap))]))` by
    (strip_tac >>
     `cap <> 0` by decide_tac >>
     `FLOOKUP t7.vs_allocas s6.cs_next_id = SOME (ob,payload) /\
      op_prov G7 ov = SOME (ob,payload) /\ ob < dimword (:256)` by
       (qpat_assum `FLOOKUP t7.vs_allocas s6.cs_next_id = _` mp_tac >>
        qpat_assum `op_prov G7 ov = _` mp_tac >>
        qpat_assum `ob + _ < _` mp_tac >>
        qpat_assum `payload = round + 32` mp_tac >>
        qpat_assum `cap <> 0` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[wordsTheory.dimword_def] >> decide_tac) >>
     `?x. ov = Var x` by
       (qpat_assum `op_prov G7 ov = SOME (ob,payload)` mp_tac >>
        Cases_on `ov` >> simp[NoAsms,op_prov_def]) >>
     `safe_operand s7 ov` by
       (first_assum ACCEPT_TAC ORELSE
        (qpat_assum `EVERY (safe_operand s7) _` mp_tac >> simp[NoAsms])) >>
     `not_fresh_at s7 x` by
       (qpat_assum `safe_operand s7 ov` mp_tac >>
        qpat_assum `ov = Var x` (fn th => rewrite_tac[th]) >>
        simp[NoAsms,exprSafeOperandTheory.safe_operand_def]) >>
     `not_fresh_at sc x` by
       (qpat_assum `ci_mono s7 sc` mp_tac >>
        qpat_assum `not_fresh_at s7 x` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh]) >>
     `eval_operand ov u = SOME (n2w ob)` by
       (qpat_assum `!p. safe_operand s7 p ==> eval_operand p u = _`
          (qspec_then `ov` mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >>
        disch_then SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     `lookup_var x q = SOME (n2w ob)` by
       (qpat_assum `eval_operand ov u = SOME (n2w ob)` mp_tac >>
        qpat_assum `ov = Var x` (fn th => rewrite_tac[th]) >>
        simp[NoAsms,Abbr `q`,venomStateTheory.eval_operand_def,
             venomStateTheory.lookup_var_def]) >>
     `ptr_covers Gq tnq x q payload` by
       (qpat_assum `ghost_kept_at lo cenv esK s7 G7 tn7 t7 _ _`
          (mp_tac o cj 1 o REWRITE_RULE [ghost_kept_at_def]) >>
        disch_then (qspec_then `x` mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >>
        simp[NoAsms,Abbr `Gq`,Abbr `tnq`] >> strip_tac >>
        qpat_assum `op_prov G7 ov = SOME (ob,payload)` mp_tac >>
        qpat_assum `op_taint tn7 ov = {}` mp_tac >>
        qpat_assum `ov = Var x` (fn th => rewrite_tac[th]) >>
        simp[ptr_covers_def,op_prov_def,w2n_n2w]) >>
     `?alloc var. MEM alloc (fn_insts func) /\ alloc.inst_opcode = ALLOCA /\
       alloc.inst_outputs = [var] /\ alloc.inst_id = s6.cs_next_id /\
       not_local_ptr cenv es2.scopes var /\ s6.cs_next_id < s7.cs_next_id` by
       (qpat_assum `ci_mono sout s7` (assume_tac o cj 3 o REWRITE_RULE [ci_mono_def]) >>
        mp_tac (Q.INST [`sa` |-> `s6`,`sm` |-> `sout`,`scopes` |-> `es2.scopes`,
          `cap` |-> `cap`,`ov` |-> `ov`,`op` |-> `op`]
          exprSimRawCallTheory.raw_call_outbuf_allocation_site) >>
        impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
                     simp[NoAsms,Abbr `cap`] >> first_assum ACCEPT_TAC) >>
        qpat_assum `sout.cs_next_id <= s7.cs_next_id` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
     `32 + payload < dimword (:256)` by
       (qpat_assum `0 < cap ==> 32 + payload < dimword (:256)` drule >>
        disch_then ACCEPT_TAC) >>
     `FLOOKUP q.vs_allocas alloc.inst_id = SOME (w2n (n2w ob : bytes32),payload)` by
       (qpat_assum `alloc.inst_id = s6.cs_next_id` (fn th => rewrite_tac[th]) >>
        qpat_assum `q.vs_allocas = t7.vs_allocas` (fn th => rewrite_tac[th]) >>
        simp[w2n_n2w]) >>
     `w2n (n2w ro : bytes32) = w2n (n2w ob : bytes32) + 32` by
       (simp[Abbr `ro`,w2n_n2w]) >>
     `alloc.inst_id < sc.cs_next_id` by
       (qpat_assum `alloc.inst_id = s6.cs_next_id` (fn th => rewrite_tac[th]) >>
        qpat_assum `sc.cs_next_id = s7.cs_next_id + 1` (fn th => rewrite_tac[th]) >>
        qpat_assum `s6.cs_next_id < s7.cs_next_id` mp_tac >>
        decide_tac) >>
     `q.vs_memory = (write_memory_with_expansion (w2n (n2w ro : bytes32))
       (TAKE cap q.vs_returndata) t7).vs_memory` by
       (qpat_assum `w2n (n2w ro : bytes32) = ro` (fn th => rewrite_tac[th]) >>
        simp[NoAsms,Abbr `q`] >>
        qpat_assum `u.vs_returndata = outcome.co_returnData` (fn th => rewrite_tac[th]) >>
        first_assum ACCEPT_TAC) >>
     `tnq.t_mem = tn7.t_mem DIFF
       {i | w2n (n2w ro : bytes32) <= i /\
        i < w2n (n2w ro : bytes32) + LENGTH (TAKE cap q.vs_returndata)}` by
       (qpat_assum `w2n (n2w ro : bytes32) = ro` (fn th => rewrite_tac[th]) >>
        qpat_assum `q.vs_returndata = outcome.co_returnData` (fn th => rewrite_tac[th]) >>
        TRY (first_assum ACCEPT_TAC) >>
        simp[NoAsms,Abbr `tnq`] >> first_assum ACCEPT_TAC) >>
     `~rev ==> safe_operand sc ok /\ evaluate_type (get_tenv cx) (expr_type e) =
         SOME (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic cap))])` by
       (disch_tac >> conj_tac
        >- (qpat_assum `emit_op opc ops s7 = (ok,sc)`
             (ACCEPT_TAC o MATCH_MP exprSafeOperandTheory.emit_op_safe_operand)) >>
        qpat_assum `expr_type e = _` (fn th => rewrite_tac[th]) >>
        qpat_assum `cap <> 0` (fn th => rewrite_tac[th]) >>
        qpat_assum `~rev` (fn th => rewrite_tac[th]) >>
        qpat_assum `cap < dimword (:256)`
          (fn th => mp_tac th >>
            mp_tac (MATCH_MP vyperTypeExtCallSoundnessTheory.raw_call_bytes_slot_size_bound th)) >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[vyperValueTheory.evaluate_type_def]) >>
     `MAP FDOM es.scopes = MAP FDOM es2.scopes` by
       (qpat_assum `es2.scopes = esK.scopes` (fn th => rewrite_tac[th]) >>
        first_assum ACCEPT_TAC) >>
     `sa.cs_next_id <= alloc.inst_id` by
       (qpat_assum `alloc.inst_id = s6.cs_next_id` (fn th => rewrite_tac[th]) >>
        qpat_assum `ci_mono sa s6` (ACCEPT_TAC o cj 3 o REWRITE_RULE [ci_mono_def])) >>
     qexistsl_tac [`x`,`n2w ob`,`alloc`,`var`,`t7`,`n2w ro:bytes32`,`tn7`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     TRY (qpat_assum `ci_mono sa sc` (ACCEPT_TAC o cj 2 o REWRITE_RULE [ci_mono_def]))) >>
  `!H. valid_horizon cx st0 H es2.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t7,G7,tn7) [] (OK q,Gq,tnq) /\
    stmt_state_rel H ctx func cenv cx es2 q /\
    storage_well_formed_on cx es2 (FST H) /\
    ghost_inv_at (DF H) lo dframe cenv cx es2 Gq tnq q` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon cx st0 H es2.storage_trace ==> _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!H. valid_horizon cx st0 H esK.storage_trace ==> ?u. _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (qx_choose_then `v` (map_every assume_tac o CONJUNCTS o BETA_RULE o
       REWRITE_RULE [LET_THM])) >>
     `v = u` by
       (qpat_assum `run_inst_seq _ t7 = OK u` mp_tac >>
        qpat_assum `run_inst_seq _ t7 = OK v` (fn th => rewrite_tac[th]) >>
        simp[NoAsms]) >>
     simp[NoAsms,Abbr `q`,Abbr `Gq`,Abbr `tnq`,stmt_state_rel_inst_idx] >>
     rpt conj_tac >>
     TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `v = u` (fn th => rewrite_tac[GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp q /\
    q.vs_alloca_next + pending_alloca_size func q <= w2n q.vs_initial_fmp` by
    (strip_tac >>
     qpat_assum `stmt_state_rel (storage_trace_horizon esK.storage_trace) ctx func cenv cx es2 q`
       (fn rel => conj_tac
          >- (match_mp_tac (MATCH_MP stmt_state_rel_allocas_below_fmp rel) >>
              first_assum ACCEPT_TAC)
          >> mp_tac (MATCH_MP stateRelProjTheory.stmt_state_rel_fmp_room rel)) >>
     qpat_assum `ctx_has_dalloca ctx` (fn has =>
       simp[NoAsms,fmp_room_def,has]) >> decide_tac) >>
  qpat_assum `raw_call_finish_rule finish_ok` (fn finish =>
  mp_tac (SIMP_RULE bool_ss [LET_THM]
    (Q.INST [`n` |-> `cap`,`rev` |-> `rev`,`call_ty` |-> `call_ty`,
      `success` |-> `outcome.co_success`,`s` |-> `q`,
      `to_op` |-> `addr`,`dp` |-> `dp`,`dl` |-> `len`,`gas_op` |-> `gas`,
      `val_op` |-> `vop`,`ov` |-> `ov`,`op` |-> `op`,
      `sa` |-> `s7`,`sb` |-> `sb`,`sc` |-> `sc`,
      `H0` |-> `storage_trace_horizon esK.storage_trace`,
      `es` |-> `es2`,`es0` |-> `es`,`sf` |-> `sa`,
      `G` |-> `Gq`,`tn` |-> `tnq`,`dep` |-> `dframe`,
      `ann` |-> `raw_call_return_type flags`,
      `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
      (SPEC_ALL (REWRITE_RULE [raw_call_finish_rule_def] finish))))) >>
  impl_tac >-
    (qpat_assum `Abbrev (payload = _)`
       (fn th => rewrite_tac[GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (qpat_assum `emit_op _ _ s7 = (ok,sc)` mp_tac >>
         Cases_on `call_ty` >> simp[NoAsms]) >>
     qpat_assum `expr_type e = _` (fn ty =>
       qpat_assum `0 < cap /\ (~rev \/ outcome.co_success) ==>
                   ?x w alloc var pre (offset:bytes32) old_tn. _`
         (ACCEPT_TAC o SIMP_RULE bool_ss [ty]))) >>
  disch_then (qx_choose_then `r` (qx_choose_then `Gf`
    (qx_choose_then `tnf` (map_every assume_tac o CONJUNCTS)))) >>
  `es2.gas_obs = []` by
    (qpat_assum `es2.gas_obs = esK.gas_obs` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `es2 with gas_obs := [] = es2` by
    (qpat_assum `es2.gas_obs = []` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  Cases_on `~storage_trace_domain cx st0 es2.storage_trace`
  >- (irule raw_call_observed_bad >> rpt conj_tac >>
      TRY (first_assum ACCEPT_TAC) >>
      qx_gen_tac `tail` >>
      qpat_assum `!gs. eval_raw_call _ _ _ _ _ _ (esK with gas_obs := gs) = _`
        (qspec_then `tail` (fn th => rewrite_tac[th,pairTheory.SND])) >>
      simp[NoAsms] >> first_assum ACCEPT_TAC) >>
  `storage_trace_domain cx st0 es2.storage_trace` by
    (FIRST [first_assum ACCEPT_TAC,
      qpat_assum `~~storage_trace_domain cx st0 es2.storage_trace`
        (ACCEPT_TAC o REWRITE_RULE [NOT_CLAUSES])]) >>
  `accept r` by
    (qpat_assum `!opc ops ok sc u r. emit_op _ _ _ = _ /\ _ ==> _` irule >>
     qexistsl_tac [`ok`,`opc`,`ops`,`sc`,`u`] >>
     qpat_assum `Abbrev (q = _)` (fn th => simp[GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
     simp[Abbr `opc`] >>
     Cases_on `call_ty` >> simp[]) >>
  irule raw_call_observed_intro >>
  qexistsl_tac [`Gf`,`es2`,`r`,
    `FST (eval_raw_call cx flags target bs amount (ext_call_kwarg EKGas flags.rcf_kws kvs) esK)`,
    `tnf`] >>
  simp[NoAsms,gasSummaryTheory.gas_explicit_def] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon cx st0 H es2.storage_trace ==>
                    gas_origin_ptr_path (DF H,lo,_,ctx,func,PG) (t7,G7,tn7) [] _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (t7,G7,tn7) [] (r,Gf,tnf)` by
    (qpat_assum `gas_origin_ptr_path (DF H,lo,_,ctx,func,PG)
                  (t7,G7,tn7) [] (OK q,Gq,tnq)`
       (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
     disch_then (qspecl_then [`q`,`Gq`,`tnq`,`[]`,`r`,`Gf`,`tnf`] mp_tac) >>
     simp[NoAsms] >>
     disch_then irule >>
     qpat_assum `!D. gas_origin_ptr_path (D,lo,_,ctx,func,PG) (q,Gq,tnq) [] _`
       (qspec_then `DF H` ACCEPT_TAC)) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `es2 with gas_obs := [] = es2` (fn th => rewrite_tac[th]) >>
  qabbrev_tac `v = if cap = 0 then (if rev then NoneV else BoolV outcome.co_success)
    else if rev then BytesV (TAKE cap q.vs_returndata)
    else ArrayV (TupleV [BoolV outcome.co_success;BytesV (TAKE cap q.vs_returndata)])` >>
  `vv = if cap = 0 then StackValue (raw_call_return_type flags) result
        else LocatedValue
          (if rev then BaseT (BytesT (Dynamic cap))
           else TupleT [BaseT BoolT;BaseT (BytesT (Dynamic cap))])
          (mk_ptr result LocMemory)` by
    (`raw_call_return_type flags = expr_type e` by
       (qpat_assum `expr_type e = raw_call_return_type flags` (ACCEPT_TAC o SYM)) >>
     qpat_assum `expr_type e = if _ then _ else _`
       (fn ty => qpat_assum `raw_call_return_type flags = expr_type e`
         (fn rt => qpat_assum `vv = if _ then _ else _` mp_tac >>
           Cases_on `cap = 0` >>
           FILTER_ASM_REWRITE_TAC (fn tm => aconv tm ``cap = 0`` orelse
             aconv tm ``~(cap = 0)``) [ty,rt]))) >>
  qpat_assum `vv = if cap = 0 then _ else LocatedValue (if _ then _ else _) _`
    (fn vv_eq => qpat_assum `Abbrev (v = _)` (fn ab =>
      qpat_assum `expr_type e = if _ then _ else _` (fn ty =>
        qpat_assum `post_value_type cenv e = expr_type e` (fn post =>
          qpat_assum `lowered_value_type cenv e = expr_type e` (fn lowered =>
            qpat_assum `(if rev /\ ~outcome.co_success then _ else _)`
              (mp_tac o PURE_REWRITE_RULE [GSYM vv_eq,GSYM ty,post,lowered,
                GSYM (REWRITE_RULE [markerTheory.Abbrev_def] ab)])))))) >>
  Cases_on `rev /\ ~outcome.co_success` >-
    (FILTER_ASM_REWRITE_TAC (can (match_term ``rev /\ ~outcome.co_success``)) [] >>
     disch_then (qx_choose_then `z` (map_every assume_tac o CONJUNCTS)) >>
     disj2_tac >>
     qpat_assum `eval_raw_call _ _ _ _ _ _ esK = _` (fn th => rewrite_tac[th,pairTheory.FST]) >>
     `flags.rcf_revert_on_failure` by
       (qpat_assum `rev /\ ~outcome.co_success` mp_tac >> simp[NoAsms,Abbr `rev`]) >>
     qpat_assum `flags.rcf_revert_on_failure`
       (fn flag => qpat_assum `rev /\ ~outcome.co_success`
         (fn failed => rewrite_tac[flag,CONJUNCT1 failed,CONJUNCT2 failed])) >>
     qpat_assum `r = Abort Revert_abort z` (fn run =>
       simp[NoAsms,Abbr `RS`,exit_result_def,exprSimDefsTheory.expr_exit_def,
            exprSimDefsTheory.halt_exit_def,run])) >>
  FILTER_ASM_REWRITE_TAC (can (match_term ``~(rev /\ ~outcome.co_success)``)) [] >>
  disch_then (qx_choose_then `z` (map_every assume_tac o CONJUNCTS)) >>
  disj1_tac >>
  qexists_tac `z` >>
  qpat_assum `!H. stmt_state_rel H ctx func cenv cx es2 q /\ _ ==> _`
    (qspec_then `H` mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ghost_inv_at (DF H) lo dframe cenv cx es2 Gf tnf z` by
    (qpat_assum `!D. ghost_inv_at D lo dframe cenv cx es2 Gq tnq q ==> _`
       (qspec_then `DF H` mp_tac) >> disch_then irule >>
     first_assum ACCEPT_TAC) >>
  `s0.vs_alloca_next <= z.vs_alloca_next` by
    (qpat_assum `!D. gas_origin_ptr_path (D,lo,_,ctx,func,PG) (q,Gq,tnq) [] _`
       (qspec_then `DF H` mp_tac) >>
     qpat_assum `r = OK z` (fn th => rewrite_tac[th]) >>
     disch_then (mp_tac o MATCH_MP (SPEC_ALL gas_origin_ptr_path_projections)) >>
     disch_then (mp_tac o MATCH_MP (SPEC_ALL fragGasPathPtrTheory.gas_path_ptr_erase)
       o CONJUNCT2) >>
     disch_then (mp_tac o MATCH_MP (SPEC_ALL bodyMemBopRestWordPathTheory.rest_word_path_frontier)) >>
     disch_then (qspec_then `z` mp_tac) >>
     qpat_assum `s0.vs_alloca_next <= q.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> decide_tac) >>
  `FST (eval_raw_call cx flags target bs amount
      (ext_call_kwarg EKGas flags.rcf_kws kvs) esK) = INL (Value v)` by
    (qpat_assum `eval_raw_call _ _ _ _ _ _ esK = _`
       (fn th => rewrite_tac[th,pairTheory.FST]) >>
     qpat_assum `~(rev /\ ~outcome.co_success)` mp_tac >>
     qpat_assum `q.vs_returndata = outcome.co_returnData`
       (fn th => simp_tac bool_ss [Abbr `v`,Abbr `cap`,Abbr `rev`,th]) >>
     Cases_on `flags.rcf_max_outsize = 0` >>
     Cases_on `flags.rcf_revert_on_failure` >>
     simp[]) >>
  qpat_assum `FST (eval_raw_call _ _ _ _ _ _ esK) = INL (Value v)`
    (fn th => PURE_ONCE_REWRITE_TAC[th]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `Abbrev (QS = _)`
    (fn th => PURE_ONCE_REWRITE_TAC[REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
  BETA_TAC >>
  qpat_assum `vv = if cap = 0 then StackValue _ _ else LocatedValue (raw_call_return_type flags) _`
    (fn th => PURE_REWRITE_TAC[GSYM th]) >>
  qpat_assum `lowered_value_type cenv e = expr_type e` (fn th => PURE_REWRITE_TAC[th]) >>
  `cap <> 0 ==> ~is_word_type (expr_type e)` by
    (qpat_assum `expr_type e = if _ then _ else _` (fn th => rewrite_tac[th]) >>
     Cases_on `rev` >> simp[compileEnvTheory.is_word_type_def]) >>
  `!t' p. vv = LocatedValue t' p ==>
    p.ptr_location = LocMemory /\ p.ptr_operand = result /\ cap <> 0` by
    (qpat_assum `vv = if cap = 0 then StackValue _ _ else LocatedValue (raw_call_return_type flags) _`
       mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> disch_then (fn th => rewrite_tac[th]) >>
     Cases_on `cap = 0` >> simp[contextTheory.mk_ptr_def]) >>
  `!t' p. vv = StackValue t' p ==> p = result` by
    (qpat_assum `vv = if cap = 0 then StackValue _ _ else LocatedValue (raw_call_return_type flags) _`
       mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> disch_then (fn th => rewrite_tac[th]) >>
     Cases_on `cap = 0` >> simp[]) >>
  `vv_location vv <> SOME LocCode` by
    (qpat_assum `vv = if cap = 0 then StackValue _ _ else LocatedValue (raw_call_return_type flags) _`
       mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> disch_then (fn th => rewrite_tac[th]) >>
     Cases_on `cap = 0` >> simp[contextTheory.mk_ptr_def,contextTheory.vv_location_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    (qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ z`
       (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.vv_post_def]) >>
     first_assum (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp)) >>
  qexists_tac `Value v` >>
  qpat_assum `expr_type e = raw_call_return_type flags`
    (fn th => PURE_REWRITE_TAC[GSYM th]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (qpat_assum `vv_location vv <> SOME LocCode` (fn th => simp[NoAsms,th])) >>
  TRY (rpt gen_tac >> strip_tac >>
       qpat_assum `!t' p. vv = StackValue t' p ==> _`
         (drule_then (fn th => PURE_REWRITE_TAC[th])) >>
       qpat_assum `~is_word_type (expr_type e) ==> ptr_buf_ok cenv e result Gf z` irule >>
       first_assum ACCEPT_TAC) >>
  TRY (rpt gen_tac >> strip_tac >>
       qpat_assum `!t' p. vv = LocatedValue t' p ==> _` (drule_then strip_assume_tac) >>
       qpat_assum `_ .ptr_operand = result` (fn th => PURE_REWRITE_TAC[th]) >>
       qpat_assum `~is_word_type (expr_type e) ==> ptr_buf_ok cenv e result Gf z` irule >>
       qpat_assum `cap <> 0 ==> ~is_word_type (expr_type e)` irule >>
       first_assum ACCEPT_TAC) >>
  strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!t' p. vv = LocatedValue t' p ==> _`
    (drule_then (ACCEPT_TAC o CONJUNCT1))
QED

Theorem raw_call_continuation_full:
  expr_has_effect e /\ post_value_type cenv e = expr_type e /\
  lowered_value_type cenv e = expr_type e /\
  expr_type e = raw_call_return_type flags /\ type_alloc_ok cenv (expr_type e) /\
  ~(flags.rcf_is_delegate /\ flags.rcf_is_static) /\
  (flags.rcf_is_delegate ==> amount = 0) /\
  (flags.rcf_is_static ==> amount = 0) /\
  amount < dimword (:256) /\ flags.rcf_max_outsize < dimword (:256) /\
  expr_sim_inv cenv cx env esK /\ esK.gas_obs = [] /\
  storage_trace_domain cx st0 esK.storage_trace /\
  fn_has_code sa sb func /\ fn_has_code s6 sout func /\ fn_inst_ids_distinct func /\
  ci_mono sa s6 /\ ci_mono s6 s7 /\ ci_mono sout s7 /\ ci_mono sa s7 /\
  compile_raw_call_outbuf flags.rcf_max_outsize s6 = ((ov,op),sout) /\
  compile_raw_call_finish addr dp len gas
    (case ext_call_kwarg EKValue flags.rcf_kws xs of
      NONE => Lit 0w | SOME p => p)
    (if flags.rcf_is_delegate then DelegateCall
     else if flags.rcf_is_static then StaticCall else RegularCall)
    flags.rcf_max_outsize flags.rcf_revert_on_failure ov op s7 = (result,sb) /\
  vv = (if flags.rcf_max_outsize = 0
        then StackValue (raw_call_return_type flags) result
        else LocatedValue (raw_call_return_type flags) (mk_ptr result LocMemory)) /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H esK.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0) /\
  (!H. valid_horizon cx st0 H esK.storage_trace ==>
    stmt_state_rel H ctx func cenv cx esK t7 /\
    storage_well_formed_on cx esK (FST H) /\
    ghost_inv_at (DF H) lo dframe cenv cx esK G7 tn7 t7) /\
  return_buf_frame dframe cenv sa t7 /\
  wb_frame cenv es esK sa s0 t7 /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G7 tn7 /\
  ~t7.vs_halted /\ t7.vs_current_bb = s7.cs_current_bb /\
  t7.vs_inst_idx = LENGTH s7.cs_current_insts /\ alloca_history func t7 /\
  s0.vs_alloca_next <= t7.vs_alloca_next /\ lo <= t7.vs_alloca_next /\ allocas_from lo t7 /\
  eval_operand addr t7 = SOME (w2w target) /\
  eval_operand (case ext_call_kwarg EKValue flags.rcf_kws xs of
      NONE => Lit 0w | SOME p => p) t7 = SOME (n2w amount) /\
  eval_operand gas t7 = SOME gw /\
  (!g. OPTION_BIND (ext_call_kwarg EKGas flags.rcf_kws kvs) dest_NumV = SOME g ==>
       g = w2n gw) /\
  eval_operand dp t7 = SOME (n2w ib) /\ eval_operand len t7 = SOME (n2w (LENGTH bs)) /\
  ib < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  (LENGTH bs = 0 \/ ib + LENGTH bs <= t7.vs_alloca_next \/
   ctx_has_dalloca ctx /\
   w2n t7.vs_initial_fmp <= ib /\ ib + LENGTH bs <= w2n t7.vs_fmp) /\
  read_memory ib (LENGTH bs) t7 = bs /\
  (!j. ib <= j /\ j < ib + LENGTH bs ==> j NOTIN tn7.t_mem) /\
  (bs <> [] ==> ?p. dp = Var p /\ ptr_covers G7 tn7 p t7 (LENGTH bs)) /\
  eval_operand ov t7 = SOME (n2w ob) /\
  eval_operand op t7 = SOME (n2w (if flags.rcf_max_outsize = 0 then ob else ob + 32)) /\
  (flags.rcf_max_outsize = 0 ==> ov = op) /\
  ob + (if flags.rcf_max_outsize = 0 then 0
      else 32 * ((flags.rcf_max_outsize + 31) DIV 32) + 32) < dimword (:256) /\
  FLOOKUP t7.vs_allocas s6.cs_next_id = SOME (ob,(if flags.rcf_max_outsize = 0 then 0
      else 32 * ((flags.rcf_max_outsize + 31) DIV 32) + 32)) /\
  op_prov G7 ov = SOME (ob,(if flags.rcf_max_outsize = 0 then 0
      else 32 * ((flags.rcf_max_outsize + 31) DIV 32) + 32)) /\
  op_prov G7 op = SOME (ob,(if flags.rcf_max_outsize = 0 then 0
      else 32 * ((flags.rcf_max_outsize + 31) DIV 32) + 32)) /\
  op_taint tn7 ov = {} /\ op_taint tn7 op = {} /\
  (!name lb sz. local_region cenv esK.scopes t7 name lb sz ==>
    regions_disjoint ob (if flags.rcf_max_outsize = 0 then 0
      else 32 * ((flags.rcf_max_outsize + 31) DIV 32) + 32) lb sz) /\
  (cenv.ce_is_ctor ==> !name tv v off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP esK.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) ob (if flags.rcf_max_outsize = 0 then 0
      else 32 * ((flags.rcf_max_outsize + 31) DIV 32) + 32)) /\
  EVERY (\x. op_taint tn7 x = {})
    [addr;len;dp;gas;(case ext_call_kwarg EKValue flags.rcf_kws xs of
      NONE => Lit 0w | SOME p => p)] /\
  EVERY (safe_operand s7)
    [addr;len;dp;gas;(case ext_call_kwarg EKValue flags.rcf_kws xs of
      NONE => Lit 0w | SOME p => p);ov;op] /\
  (!x. MEM (Var x)
    [addr;len;dp;gas;(case ext_call_kwarg EKValue flags.rcf_kws xs of
      NONE => Lit 0w | SOME p => p);ov;op] ==> not_fresh_at s7 x)
  ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0
    (eval_raw_call cx flags target bs amount (ext_call_kwarg EKGas flags.rcf_kws kvs))
    (esK,t7,G7,tn7)
        (\H res ee G tn t. ?tv. res = INL tv /\
          vv_post H ctx func cenv cx e es sa sb s0 ee tv vv t /\
          vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
            ee tv vv t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
          s0.vs_alloca_next <= t.vs_alloca_next /\
          ghost_inv_at (DF H) lo dframe cenv cx ee G tn t /\
          ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn t /\
          (!v. tv = Value v /\ ~is_word_type (post_value_type cenv e) /\
               ~is_bytestring_type (post_value_type cenv e) ==>
               vv_own cenv cx (post_value_type cenv e) sa sb ee (Value v) vv t /\
               (!t' p. vv = LocatedValue t' p ==>
                       p.ptr_location = LocMemory)) /\
          (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
           ?val. read_result cx tv ee = (INL val, ee) /\
                 !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) =
                          SOME rt /\
                        eval_operand (vv_operand vv) t = SOME w ==>
                        w2n w + type_memory_size rt <= lo /\
                        (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                               val_in_memory rt val (w2n w) mem)) /\
          (!t' op. vv = StackValue t' op /\
                   ~is_word_type (post_value_type cenv e) ==>
                   ptr_buf_ok cenv e op G t) /\
          (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
                  ptr_buf_ok cenv e p.ptr_operand G t) /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
        (\H res ee gt r.
          expr_exit res r /\ halt_exit H cx ee res r /\
          (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule raw_call_observed_plain >> qexists_tac `\r. T` >>
  irule (BETA_RULE (Q.INST
    [`finish_ok` |-> `\sc sb E C f s r. T`, `accept` |-> `\r. T`]
    raw_call_continuation_observed)) >>
  simp_tac bool_ss [raw_call_finish_rule_plain] >> rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >>
  TRY (qpat_assum `~(_ /\ _)` (ACCEPT_TAC o REWRITE_RULE [DE_MORGAN_THM])) >>
  ((qexistsl_tac [`addr`,`dp`,`gas`,`gw`,`ib`,`len`,`ob`,`op`,`ov`,`result`,
                  `s6`,`s7`,`sout`,`xs`] >> rpt conj_tac >> first_assum ACCEPT_TAC)
   ORELSE (qexists_tac `env` >> rpt conj_tac >> first_assum ACCEPT_TAC))
QED

Theorem raw_call_expr_vv_by:
  body_exprs_full_ok cx args /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) args dflt) es /\
  raw_call_vv_pre (DF,lo,dframe,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Call ann (RawCallTarget flags) args dflt) es
    (st0,sa,sb,shadow_sa,shadow_sb,vv,s0,G0,tn0) /\
  raw_call_vv_answer_rules A ctx /\
  raw_call_vv_prefix_rule A (DF,lo,dframe,ctx,shadow_ctx,PG,func,shadow_func)
    (tops,cenv,env,cx,ty,ann,flags,es)
    (st0,sa,sb,shadow_sa,shadow_sb,vv,s0,G0,tn0) /\
  raw_call_vv_request_rule A (DF,lo,dframe,ctx,func)
    (cenv,env,cx,flags,st0) (es,sa,sb,s0,G0,tn0) ==>
  A sa (eval_expr cx (Call ann (RawCallTarget flags) args dflt)) (es,s0,G0,tn0)
    (raw_call_vv_answer_post (DF,lo,dframe,ctx,func) cenv cx
      (Call ann (RawCallTarget flags) args dflt) (es,sa,sb,s0,vv,G0,tn0))
    (raw_call_vv_answer_exit ctx cx)
Proof
  strip_tac >>
  drule raw_call_pre_operands >> strip_tac >>
  drule raw_call_pre_flags >> strip_tac >> gvs[] >>
  qpat_assum `raw_call_vv_pre _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [raw_call_vv_pre_def]) >>
  drule compile_expr_raw_call >> strip_tac >>
  drule raw_call_kwargs_types >> simp[] >> strip_tac >>
  drule_all raw_call_kwargs_word_args >> strip_tac >>
  irule raw_call_vv_answer_basic_exit >> conj_tac >- first_assum ACCEPT_TAC >>
  CONV_TAC (SIMP_CONV bool_ss [raw_call_eval_action]) >>
  qpat_x_assum `raw_call_vv_prefix_rule _ _ _ _`
    (irule o BETA_RULE o Q.ISPEC `\av dv kvs.
      do
        type_check (LENGTH (av::dv::kvs) = 2 + LENGTH flags.rcf_kws) "raw_call args";
        target <- lift_option_type (dest_AddressV av) "raw_call target";
        data <- lift_option_type (dest_BytesV dv) "raw_call data";
        amount <- lift_option_type (raw_call_value flags.rcf_kws kvs) "raw_call value";
        eval_raw_call cx flags target data amount (ext_call_kwarg EKGas flags.rcf_kws kvs)
      od` o Q.GEN `k` o SPEC_ALL o REWRITE_RULE [raw_call_vv_prefix_rule_def]) >>
  first_assum (irule_at (Pat `lower_value _ _ _ a _ = _`)) >>
  first_assum (irule_at (Pat `lower_value _ _ _ d _ = _`)) >>
  first_assum (irule_at (Pat `emit_op MLOAD _ _ = _`)) >>
  first_assum (irule_at (Pat `emit_op ADD _ _ = _`)) >>
  first_assum (irule_at (Pat `compile_ext_call_kwargs _ _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `lower_word_args _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `compile_raw_call_outbuf _ _ = _`)) >>
  first_assum (irule_at (Pat `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]
  >~ [`storage_trace_frame _`]
  >- (rpt gen_tac >> irule storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_checks] >>
      irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >> gen_tac >>
      irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >> gen_tac >>
      irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_lifts,storage_trace_frame_raw_call]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> _`
    (qspec_then `storage_trace_horizon esK.storage_trace` mp_tac) >>
  impl_tac >- fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t7` by
    (qpat_assum `stmt_state_rel _ ctx func cenv cx esK t7`
       (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp)) >>
  drule_all raw_call_prefix_source_ready >> strip_tac >>
  `!e. vyperState$assert T e = vyperState$return ()` by
    simp[FUN_EQ_THM, vyperStateTheory.assert_def, vyperStateTheory.return_def] >>
  simp[vyperStateTheory.type_check_def, vyperStateTheory.lift_option_type_def,
       vyperValueTheory.dest_BytesV_def, vyperStateTheory.bind_return,
       vyperStateTheory.ignore_bind_def] >>
  `ci_mono sa s6 /\ ci_mono s6 s7 /\ ci_mono sa s7` by
    (`ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\
      ci_mono s3 s4 /\ ci_mono s4 s5 /\ ci_mono s5 s6 /\ ci_mono s6 s7` by
       (rpt conj_tac
        >- metis_tac[ci_mono_lower_value_compile_expr,pairTheory.SND]
        >- metis_tac[ci_mono_lower_value_compile_expr,pairTheory.SND]
        >- metis_tac[ci_mono_emit_op,pairTheory.SND]
        >- metis_tac[ci_mono_emit_op,pairTheory.SND]
        >- metis_tac[ci_mono_lower_word_args]
        >- (qpat_assum `(case go of NONE => emit_op GAS [] s5 | SOME g => (g,s5)) = (gas,s6)` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> Cases_on `go` >> simp[] >> strip_tac >>
            metis_tac[ci_mono_emit_op,pairTheory.SND,ci_mono_refl]) >>
        metis_tac[ci_mono_compile_raw_call_outbuf,pairTheory.SND]) >>
     rpt (qhdtm_x_assum `ci_mono` mp_tac) >> POP_ASSUM_LIST (K all_tac) >>
     metis_tac[ci_mono_trans]) >>
  `expr_sim_inv cenv cx env es` by
    (qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` mp_tac >>
     simp[NoAsms, exprSimHypsDefsTheory.expr_body_pre_def]) >>
  `expr_body_pre cenv cx env a (es with gas_obs := gsA)` by
    (irule expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  `expr_sim_inv cenv cx env esA` by
    (irule (cj 1 exprSimHashTheory.expr_body_pre_base_result) >>
     goal_assum (drule_at Any) >> simp[ETA_THM] >>
     qexists_tac `INL av` >>
     qpat_assum `bind (eval_expr cx a) (read_result cx) _ = (INL av,esA)` mp_tac >>
     simp[NoAsms,vyperStateTheory.bind_def]) >>
  `expr_body_pre cenv cx env d (esA with gas_obs := gsD)` by
    (irule expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  `expr_sim_inv cenv cx env esD` by
    (irule (cj 1 exprSimHashTheory.expr_body_pre_base_result) >>
     goal_assum (drule_at Any) >> simp[ETA_THM] >>
     qexists_tac `INL (BytesV bs)` >>
     qpat_assum `bind (eval_expr cx d) (read_result cx) _ = (INL (BytesV bs),esD)` mp_tac >>
     simp[NoAsms,vyperStateTheory.bind_def]) >>
  `!p. ext_call_kwarg EKGas flags.rcf_kws xs = SOME p ==> gas = p` by
    (qpat_assum `go = ext_call_kwarg EKGas flags.rcf_kws xs`
       (fn th => rewrite_tac [GSYM th]) >>
     qpat_x_assum `(case go of NONE => emit_op GAS [] s5 | SOME g => (g,s5)) = _` mp_tac >>
     Cases_on `go` >> simp[]) >>
  `!g. OPTION_BIND (ext_call_kwarg EKGas flags.rcf_kws kvs) dest_NumV = SOME g ==>
       g = w2n gw` by
    (gen_tac >> disch_tac >>
     irule (INST_TYPE [alpha |-> ``:256``] raw_call_request_gas_at_entry) >>
     first_assum (irule_at (Pat `eval_exprs _ _ _ = _`)) >>
     qpat_assum `typed_args_post _ ctx func cenv cx esD s4 t4 esK kws xs kvs tk`
       (irule_at Any) >>
     qpat_assum `eval_operand gas t7 = SOME gw`
       (irule_at (Pat `eval_operand _ _ = _`)) >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `expr_has_effect (Call (raw_call_return_type flags) (RawCallTarget flags) (a::d::kws) NONE) /\
    post_value_type cenv (Call (raw_call_return_type flags) (RawCallTarget flags) (a::d::kws) NONE)
      = raw_call_return_type flags /\
    lowered_value_type cenv (Call (raw_call_return_type flags) (RawCallTarget flags) (a::d::kws) NONE)
      = raw_call_return_type flags /\
    type_alloc_ok cenv (raw_call_return_type flags)` by
    (simp[NoAsms,loweringPostsTheory.expr_has_effect_thm, loweringPostsTheory.post_value_type_def,
          exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def] >>
     qpat_assum `expr_body_pre _ _ _ (Call _ (RawCallTarget _) _ _) _` mp_tac >>
     simp[NoAsms,exprSimHypsDefsTheory.expr_body_pre_def,allocLimitsTheory.alloc_limits_expr_def]) >>
  `~(flags.rcf_is_delegate /\ flags.rcf_is_static) /\
    (flags.rcf_is_delegate ==> amount = 0)` by
    (conj_tac >-
      (qpat_assum `expr_body_pre _ _ _ (Call _ (RawCallTarget _) _ _) _` mp_tac >>
       simp[NoAsms,exprSimHypsDefsTheory.expr_body_pre_def,vyperTypeSystemTheory.well_typed_expr_def]) >>
     strip_tac >>
     `~MEM EKValue flags.rcf_kws` by
       (qpat_assum `raw_call_kws_ok flags kws`
          (strip_assume_tac o REWRITE_RULE [vyperTypeSystemTheory.raw_call_kws_ok_def]) >>
        qpat_assum `_ \/ _ ==> ~MEM EKValue flags.rcf_kws` irule >>
        disj1_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `~MEM EKValue flags.rcf_kws` (fn th =>
       qpat_assum `raw_call_value flags.rcf_kws kvs = SOME amount` mp_tac >>
       simp[NoAsms,vyperInterpreterTheory.raw_call_value_def,
            MATCH_MP (SPEC_ALL vyperTypeExtCallSoundnessTheory.ext_call_kwarg_not_mem) th] >>
       disch_then (ACCEPT_TAC o SYM))) >>
  `fn_has_code s6 s7 func` by
    (`cs_extends s7 sb` by metis_tac[ci_mono_compile_raw_call_finish,ci_mono_def,pairTheory.SND] >>
     irule fn_has_code_mid >> conj_tac >-
       qpat_assum `ci_mono s6 s7` (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [ci_mono_def]) >>
     qexistsl [`sb`,`sa`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `ci_mono sa s6` (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [ci_mono_def])) >>
  `!j. b + 32 <= j /\ j < b + 32 + LENGTH bs ==> j NOTIN tn7.t_mem` by
    (qpat_assum `!mem. mem_agree_outside tn7.t_mem t7.vs_memory mem ==> _`
       (mp_tac o MATCH_MP representationCleanPtrTheory.robust_mem_bytes_at_clean) >>
     simp[]) >>
  `bs <> [] ==> ?p. dp = Var p /\ ptr_covers G7 tn7 p t7 (LENGTH bs)` by
    (strip_tac >> qpat_assum `bs <> [] ==> _` drule >>
     qpat_assum `eval_operand dp t7 = _` mp_tac >>
     qpat_assum `op_taint tn7 dp = {}` mp_tac >>
     qpat_assum `b + 32 < _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `dp` >> simp[op_prov_def,eval_operand_def,ptr_covers_def,w2n_n2w] >>
     rpt strip_tac >> simp[] >> decide_tac) >>
  `read_memory (b + 32) (LENGTH bs) t7 = bs` by
    simp[memoryReadPropsTheory.read_memory_eq_mem_bytes_at] >>
  qpat_x_assum `vo = _` SUBST_ALL_TAC >>
  qpat_assum `raw_call_vv_answer_rules _ _`
    (irule o cj 1 o REWRITE_RULE [raw_call_vv_answer_rules_def]) >>
  qexistsl_tac [`raw_call_vv_answer_post (DF,lo,dframe,ctx,func) cenv cx
      (Call (raw_call_return_type flags) (RawCallTarget flags) (a::d::kws) NONE)
      (es,sa,sb,s0,(if flags.rcf_max_outsize = 0 then StackValue (raw_call_return_type flags) result
          else LocatedValue (raw_call_return_type flags) (mk_ptr result LocMemory)),G0,tn0)`,
    `raw_call_vv_answer_exit ctx cx`] >>
  simp[raw_call_vv_answer_exit_def,NoAsms] >>
  qpat_assum `raw_call_vv_request_rule _ _ _ _`
    (mp_tac o Q.INST [`e` |-> `Call (raw_call_return_type flags) (RawCallTarget flags) (a::d::kws) NONE`,
       `vv` |-> `if flags.rcf_max_outsize = 0 then StackValue (raw_call_return_type flags) result
         else LocatedValue (raw_call_return_type flags) (mk_ptr result LocMemory)`,
       `ib` |-> `b + 32`, `sout` |-> `s7`] o SPEC_ALL o
       REWRITE_RULE [raw_call_vv_request_rule_def]) >>
  (impl_tac >- suspend "continuation") >>
  simp[raw_call_vv_answer_exit_def]
QED

Resume raw_call_expr_vv_by[continuation]:
  simp[NoAsms,ci_mono_refl,loweringPostsTheory.expr_has_effect_thm,
       exprLoweringTheory.lowered_value_type_def,vyperASTTheory.expr_type_def] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (rpt strip_tac >>
       qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
         (drule_then (map_every assume_tac o CONJUNCTS)) >>
       rpt conj_tac >> first_assum ACCEPT_TAC) >>
  TRY (qpat_assum `~(flags.rcf_is_delegate /\ flags.rcf_is_static)`
         (ACCEPT_TAC o REWRITE_RULE [DE_MORGAN_THM])) >>
  TRY (qpat_assum `!g. OPTION_BIND (ext_call_kwarg EKGas _ _) _ = SOME g ==> _`
         (ACCEPT_TAC o SIMP_RULE (srw_ss()) [])) >>
  TRY (disj2_tac >> disj1_tac >> first_assum ACCEPT_TAC) >>
  TRY (qpat_assum `amount < dimword (:256)`
         (ACCEPT_TAC o SIMP_RULE (srw_ss()) [])) >>
  PURE_ONCE_REWRITE_TAC [Q.SPECL [`LENGTH bs`,`32`] arithmeticTheory.ADD_COMM] >>
  PURE_REWRITE_TAC [arithmeticTheory.ADD_ASSOC] >>
  first_assum ACCEPT_TAC
QED

Finalise raw_call_expr_vv_by

Theorem raw_call_vv_prefix_rule_full[local]:
  raw_call_vv_prefix_rule
    (\i source x Q R. gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 source x Q R)
    (DF,lo,dframe,ctx,shadow_ctx,PG,func,shadow_func) (tops,cenv,env,cx,ty,ann,flags,es)
    (st0,sa,sb,shadow_sa,shadow_sb,vv,s0,G0,tn0)
Proof
  simp_tac bool_ss [raw_call_vv_prefix_rule_def, raw_call_vv_pre_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule raw_call_prefix_prepared_full >>
  first_assum (irule_at (Pat `compile_expr _ _ (Call _ _ _ _) _ = _`)) >>
  first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >>
  first_assum (irule_at (Pat `lower_value _ _ _ a _ = _`)) >>
  first_assum (irule_at (Pat `lower_value _ _ _ d _ = _`)) >>
  first_assum (irule_at (Pat `emit_op MLOAD _ _ = _`)) >>
  first_assum (irule_at (Pat `emit_op ADD _ _ = _`)) >>
  first_assum (irule_at (Pat `compile_ext_call_kwargs _ _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `lower_word_args _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `compile_raw_call_outbuf _ _ = _`)) >>
  first_assum (irule_at (Pat `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `compile_expr _ _ (gas_shadow_expr _) _ = _`)) >>
  first_assum (irule_at (Pat `return_buf_frame _ _ _ _`)) >>
  first_assum (irule_at (Pat `body_inv _ _ _ _`)) >>
  first_assum (irule_at (Pat `gas_shadow_function _ _`)) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!H exc ee gt r. _ ==> R H (INR exc) ee gt r` irule >>
  metis_tac[stmtSimPropsTheory.expr_exit_INR_type,haltExitProjTheory.halt_exit_INR_type]
QED

Theorem raw_call_vv_request_rule_full[local]:
  raw_call_vv_request_rule
    (\i source x Q R. gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 source x Q R)
    (DF,lo,dframe,ctx,func) (cenv,env,cx,flags,st0) (es,sa,sb,s0,G0,tn0)
Proof
  simp_tac bool_ss [raw_call_vv_request_rule_def, raw_call_vv_answer_exit_fun] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qmatch_goalsub_abbrev_tac `raw_call_vv_answer_post _ _ _ _ (_,_,_,_,out,_,_)` >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ Q _` >>
  `Q = (\H res ee G tn t. raw_call_vv_answer_post (DF,lo,dframe,ctx,func) cenv cx e
                             (es,sa,sb,s0,out,G0,tn0) H res ee G tn t)` by
    simp[Abbr `Q`, FUN_EQ_THM] >>
  pop_assum SUBST1_TAC >>
  pure_rewrite_tac [raw_call_vv_answer_post_def, GSYM CONJ_ASSOC] >>
  irule (PURE_REWRITE_RULE [GSYM CONJ_ASSOC] raw_call_continuation_full) >>
  first_assum (irule_at (Pat `compile_raw_call_outbuf _ _ = _`)) >>
  first_assum (irule_at (Pat `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `eval_operand dp _ = _`)) >>
  first_assum (irule_at (Pat `eval_operand gas _ = _`)) >>
  first_assum (irule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  first_assum (irule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  qexistsl_tac [`ib`,`gw`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[Abbr `out`, DE_MORGAN_THM]
QED

Theorem raw_call_vv_answer_rules_full[local]:
  raw_call_vv_answer_rules
    (\i source x Q R. gas_outcome_full (DF,lo,E,ctx,func,PG) tops cx st0 source x Q R) ctx
Proof
  simp[raw_call_vv_answer_rules_def] >> conj_tac >>
  rpt gen_tac >> PairCases_on `x` >>
  metis_tac[gasOutcomeFullTheory.gas_outcome_full_post_mono,gas_outcome_full_halt_room]
QED

Theorem raw_call_expr_vv_full:
  body_exprs_full_ok cx args /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) args dflt) es ==>
  expr_vv_sim_full (DF,lo,dframe,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Call ann (RawCallTarget flags) args dflt) es
Proof
  rpt (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >> disch_tac >>
  simp_tac bool_ss [expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ Q R` >>
  `Q = raw_call_vv_answer_post (DF,lo,dframe,ctx,func) cenv cx
         (Call ann (RawCallTarget flags) args dflt) (es,sa,sb,s0,vv,G0,tn0)` by
    simp[Abbr `Q`, FUN_EQ_THM, raw_call_vv_answer_post_def] >>
  `R = raw_call_vv_answer_exit ctx cx` by
    simp[Abbr `R`, FUN_EQ_THM, raw_call_vv_answer_exit_def] >>
  simp[] >>
  irule (BETA_RULE (Q.ISPEC
    `\(i:compile_state)
       (source:evaluation_state -> (eval_result + vyperState$exception) # evaluation_state)
       x Q R.
       gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (cx_tops cx) cx st0 source x Q R` (Q.GEN `A` raw_call_expr_vv_by))) >>
  first_assum (irule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
  qexistsl_tac [`ty`,`tops`,`shadow_sb`,`shadow_sa`,`shadow_func`] >>
  simp[raw_call_vv_prefix_rule_full,raw_call_vv_request_rule_full,raw_call_vv_answer_rules_full,
       raw_call_vv_pre_def] >>
  first_assum ACCEPT_TAC
QED
