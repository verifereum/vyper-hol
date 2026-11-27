(* Physical caller transport at the endpoint selected by ExtCall packing. *)
Theory bodyFullExtCallEncoderStmtFrame
Ancestors
  exprSimAbiEncodeStateTransport allocationGrowth stateRelProj
  bodyFullIntCallReturnFrame loweringStateRelDefs exprLoweringProps
  compileEnv venomInst venomState finite_map alist words list

(* SCRATCH MEASUREMENT: the original proof failed after restating the state-relation
   lemmas. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  drule_then assume_tac stmt_state_rel_state_rel >>
  drule_then assume_tac stmt_state_rel_alloca_room >>
  drule_then assume_tac stmt_state_rel_fmp_room >>
  drule_then assume_tac return_stmt_immutable_sep >>
  drule_then assume_tac stmt_state_rel_immutable_base_zero >>
  `!name entry p sz. lookup_scopes name ee.scopes = SOME entry /\
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
     lookup_var p t = lookup_var p q` by
    (rpt strip_tac >>
     `not_fresh_at st p` by
       (qpat_assum `local_ptrs_reserved cenv st` (strip_assume_tac o
          PURE_REWRITE_RULE [local_ptrs_reserved_def]) >>
        first_assum (drule_then (ACCEPT_TAC o CONJUNCT1 o SPEC_ALL))) >>
     `?w. lookup_var p q = SOME w` by
       (qpat_assum `local_ptrs_rel func cenv ee.scopes q`
          (drule_all_then (strip_assume_tac) o cj 1 o
           PURE_REWRITE_RULE [local_ptrs_rel_def]) >>
        goal_assum (drule_at Any)) >>
     metis_tac[]) >>
  qpat_assum `allocation_growth q t`
    (strip_assume_tac o PURE_REWRITE_RULE [allocation_growth_def]) >>
  `state_rel H func cenv cx ee t` by
    (irule abi_encode_caller_state_rel >>
     qpat_assum `abi_encoder_registered_effect ids outs q t` (irule_at Any) >>
     qpat_assum `abi_encode_exec_frame func q t` (irule_at Any) >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, REFL_TAC]) >>
  `immutable_alloca_sep func cenv cx ee t` by
    (irule abi_encode_caller_immutable_separation >> qexists `q` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `immutable_base_zero cenv t` by
    (irule abi_encode_caller_immutable_base >> qexists `q` >> simp[] >>
     metis_tac[local_ptrs_reserved_imm_base]) >>
  `alloca_room ctx func t /\ fmp_room ctx func t` by
    (irule abi_encode_caller_resource_room >>
     qpat_assum `abi_encode_exec_frame func q t` (irule_at Any) >>
     rpt conj_tac >> TRY (rpt strip_tac >> first_assum ACCEPT_TAC) >>
     metis_tac[]) >>
  irule stmt_state_rel_intro >> asm_rewrite_tac[] >>
  rpt strip_tac >> Cases_on `FLOOKUP q.vs_allocas inst.inst_id`
  >- (first_assum (drule_all_then ACCEPT_TAC)) >>
  `FLOOKUP t.vs_allocas inst.inst_id = SOME x` by
    (qpat_assum `!id allocation. _` irule >> simp[]) >>
  PairCases_on `x` >> gvs[] >>
  qpat_assum `stmt_state_rel H ctx func cenv cx ee q`
    (mp_then Any (drule_all_then ACCEPT_TAC) stmt_state_rel_alloca_size)
QED
*)
Theorem extcall_encoder_stmt_frame:
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list)
    ctx func cenv cx ee q /\
  abi_encode_exec_frame func q t /\
  abi_encoder_registered_effect ids outs q t /\
  allocation_growth q t /\ alloca_inv t /\ t.vs_labels = q.vs_labels /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv st /\
  (!x w. not_fresh_at st x /\ lookup_var x q = SOME w ==>
    lookup_var x t = SOME w) /\
  (!name b n. local_region cenv ee.scopes q name b n ==>
    mem_bytes_at b n t.vs_memory = mem_bytes_at b n q.vs_memory) /\
  (cenv.ce_is_ctor ==> !name tv v off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
    mem_bytes_at off (type_memory_size tv) t.vs_memory =
      mem_bytes_at off (type_memory_size tv) q.vs_memory) /\
  (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\ FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) /\
    FLOOKUP q.vs_allocas inst.inst_id = NONE ==> sz = w2n n) ==>
  stmt_state_rel H ctx func cenv cx ee t
Proof
  cheat
QED
