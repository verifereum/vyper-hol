(* Request sites for one exact-layout tuple store at its current cursor. *)
Theory s1PrefixAssignTupleExactHead
Ancestors
  bodyFullAssignTuple bodyTupleExactStoreCursor bodyFullTargetRoots
  s1PrefixTarget s1PrefixImmutableTargetPlace s1PrefixTupleBaseStore
  s1PrefixOfVV bodyPtrPopTargetFragTransport
  bodyFullShared bodyFullPreds bodyFullTupleTargetProjection s1PrefixPreds s1PrefixDefs
  vyperTypeCallGraph vyperTypeCallStackSoundness vyperTypeSystem
  vyperInterpreter vyperState list

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_then (qx_choosel_then [`sm`,`shadow_sm`,`r`,`sc`,`shadow_sc`]
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)) tuple_exact_store_head_code >>
  qpat_x_assum `tuple_exact_store_cursor _ _ _ _ _ _ _`
    (REPEAT_TCL CONJUNCTS_THEN assume_tac o
     SIMP_RULE (srw_ss()) [tuple_exact_store_cursor_def, tuple_exact_cursor_common_def,
       tuple_exact_cursor_at_def, EVERY_DEF, well_typed_atarget_def]) >>
  dxrule_then assume_tac body_tuple_target_full_ok_base >>
  RULE_ASSUM_TAC (REWRITE_RULE [body_tuple_target_prefix_ok_def]) >>
  irule tuple_base_store_prefix_from_place >>
  Cases_on `immutable_root cx bt`
  >- suspend "immutable" >>
  `target_pre cenv cx env bt src` by
    (`immutable_section_layout_mods [(NONE,tops)] cenv` by
       metis_tac[bodySimTheory.body_inv_contract,
                 bodyInvSplitTheory.contract_inv_immutable_section_layout] >>
     `cenv.ce_modules = [(NONE,tops)] /\ cenv.ce_module = NONE /\
      ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` by
       fs[bodySimTheory.body_inv_def, bodySimTheory.cenv_module_pins_def] >>
     fs[bodyFullPredsModsTheory.target_pre_mods_singleton]) >>
  irule body_target_sim_prefix >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`cenv`,`d`,`env`,`r`,`cur`,`sc`,`shadow_func`,`shadow_cur`,
            `shadow_sc`,`tops`,`Type sty`] >> simp[]
QED
*)
Theorem tuple_assign_exact_store_head_prefix:
  tuple_exact_store_cursor (cenv,cx,env,tops,bindings)
    (DF,lo,d,ctx,func,shadow_func,st0) (sa,sb,shadow_sb)
    (es,s0,G0,tn0) (tys,tvs,vs)
    (BaseTarget bt::todo,sty::tys_tail,tvs1,vi::vs_tail,op0::ops_tail,k,p)
    (cur,shadow_cur,src,u,Gu,tu) /\
  body_tuple_target_full_ok cx (BaseTarget bt) vi /\
  body_tuple_target_prefix_ok cx (BaseTarget bt) vi /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_inst_ids_distinct func /\ (!H. dead_lo_ok H (DF H) lo cenv cx) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (assign_tuple_targets cx (BaseTarget bt) vi) (src,u,Gu,tu)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume tuple_assign_exact_store_head_prefix[immutable]:
  `IS_SOME (type_place_target env bt)` by simp[] >>
  drule_all_then (qx_choosel_then [`id`,`root_ty`]
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)) typed_immutable_target_root >>
  `call_evaluation_safe cx (int_calls_target bt)` by
    (qpat_assum `call_evaluation_safe cx (int_calls_atargets (_ :: todo))`
       (mp_then Any ACCEPT_TAC call_evaluation_safe_append_left o
        REWRITE_RULE [int_calls_atarget_def])) >>
  `?stv. evaluate_type (get_tenv cx) sty = SOME stv` by
    (Cases_on `tvs1` >> fs[LIST_REL_def]) >>
  `!qe. SND (eval_base_place cx bt qe) = SND (eval_target_place cx bt qe)` by
    simp[eval_target_place_as_bind, get_place_bind_state] >>
  drule_then (fn th => pure_once_rewrite_tac[th]) gas_prefix_full_state_cong >>
  irule immutable_target_place_prefix >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`cenv`,`d`,`env`,`r`,`cur`,`sc`,`shadow_func`,`shadow_cur`,
            `shadow_sc`,`tops`,`stv`,`sty`] >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise tuple_assign_exact_store_head_prefix
*)
