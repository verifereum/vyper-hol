(* Preserve local and protected windows across the ordinary Slice suffix. *)
Theory bodySliceWindowGhostMods
Ancestors
  bodyShaRegisteredFrameMods bodyPtrBytestringBuiltinsWindowGhost
  bodyFullShadowBodyInv bodyPtrDefs ptrDiscipline venomMemDefs
  valueEncodingDefs loweringStateRelDefs loweringPosts compileEnv venomState
  finite_map pred_set

Theorem slice_window_ghost_frame_mods:
  ghost_inv_at_mods D lo d cenv cx es G tn s /\
  immutable_frame_mods func cenv cx es s /\
  local_ptrs_rel func cenv es.scopes s /\ alloca_inv s /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
       lookup_var x target = lookup_var x s /\
       FLOOKUP G3 x = FLOOKUP G x /\
       op_taint tm (Var x) = op_taint tn (Var x)) /\
  target.vs_call_ctx = s.vs_call_ctx /\ target.vs_accounts = s.vs_accounts /\
  target.vs_transient = s.vs_transient /\ target.vs_immutables = s.vs_immutables /\
  tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
  (!name b len. local_region cenv es.scopes s name b len ==>
       mem_bytes_at b len target.vs_memory = mem_bytes_at b len s.vs_memory /\
       (!i. b <= i /\ i < b+len /\ i IN tm.t_mem ==> i IN tn.t_mem)) /\
  (!i. i < s.vs_alloca_next /\ i IN tm.t_mem ==> i IN tn.t_mem) /\
  target.vs_data_section = s.vs_data_section /\
  LENGTH s.vs_memory <= LENGTH target.vs_memory /\
  s.vs_alloca_next <= target.vs_alloca_next /\
  (!aid a sz. FLOOKUP target.vs_allocas aid = SOME (a,sz) ==>
       FLOOKUP s.vs_allocas aid = SOME (a,sz) \/ s.vs_alloca_next <= a) /\
  pure_frame cenv func es sa s target ==>
  ghost_inv_at_mods D lo d cenv cx es G3 tm target /\
  immutable_frame_mods func cenv cx es target /\
  ghost_kept_at lo cenv es sa G tn s G3 tm
Proof
  strip_tac >>
  `ghost_inv_at D 0 d cenv cx es G tn s /\ lo <= s.vs_alloca_next` by
    (qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE[ghost_inv_at_mods_def]) >>
     simp[ghost_inv_at_def, allocas_from_def] >> first_assum ACCEPT_TAC) >>
  `stor_taint_ok_at D tm target` by
    (qpat_assum `ghost_inv_at D 0 _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE[ghost_inv_at_def]) >>
     fs[stor_taint_ok_at_def]) >>
  `mem_bytes_at 0 0 target.vs_memory = mem_bytes_at 0 0 s.vs_memory` by
    simp[mem_bytes_at_def] >>
  `ghost_inv_at D 0 d cenv cx es G3 tm target` by
    (irule ghost_inv_at_local_window_transport >>
     simp[allocas_from_def] >>
     qexistsl_tac [`G`,`es`,`func`,`s`,`sa`,`tn`] >>
     asm_rewrite_tac[] >> conj_tac
     >- (rpt strip_tac >> qpat_assum `!x. not_fresh_at sa x ==> _`
           (drule_then strip_assume_tac) >> simp[]) >>
     rpt strip_tac >> qpat_assum `!x. not_fresh_at sa x ==> _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `!i. i < lo /\ i IN tm.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >> qpat_assum `!i. i < s.vs_alloca_next /\ _ ==> _` irule >>
     simp[] >> decide_tac) >>
  drule_all_then strip_assume_tac sha_registered_frame_mods >>
  asm_rewrite_tac[ghost_kept_at_def] >> conj_tac
  >- (rpt strip_tac >> qpat_assum `!x. not_fresh_at sa x ==> _`
        (drule_then strip_assume_tac) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      fs[alloca_inv_def, alloca_next_valid_def] >>
      qpat_assum `!aid b k. FLOOKUP s.vs_allocas aid = SOME (b,k) ==> _`
        (drule_then assume_tac) >>
      qpat_assum `!i. i < s.vs_alloca_next /\ _ ==> _` irule >>
      simp[] >> decide_tac) >>
  rpt strip_tac >> qpat_assum `!name b len. local_region _ _ _ _ _ _ ==> _`
    (drule_then strip_assume_tac) >> first_x_assum irule >> simp[]
QED
