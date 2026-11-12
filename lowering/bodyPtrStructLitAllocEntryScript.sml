Theory bodyPtrStructLitAllocEntry
Ancestors bodyPtrStructLitFreshGhost bodyPtrStructLitAlloc allocationPtr
  finite_map ptrDiscipline bodyPtrDefs venomState

Theorem structlit_reused_alloca_ghost_inv:
  ghost_inv d ce cx es G tn s /\
  FLOOKUP s.vs_allocas id = SOME (b,n) /\
  (!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
     FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p <> out) ==>
  ghost_inv d ce cx es
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out])
      (update_var out (n2w b) s))
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s
      (update_var out (n2w b) s) tn)
    (update_var out (n2w b) s with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> irule ghost_inv_update_var_pc >>
  drule reused_alloca_ghost >>
  disch_then (qspecl_then [`out`, `PG`, `G`, `tn`] strip_assume_tac) >>
  simp[op_taint_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem structlit_reused_alloca_entry:
  ghost_inv d ce cx es G tn s /\
  FLOOKUP s.vs_allocas id = SOME (b,n) /\ b + n < dimword (:256) /\
  (!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
     FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id ALLOCA [Lit (n2w n)] [out]) ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out])
      (update_var out (n2w b) s))
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s
      (update_var out (n2w b) s) tn)
    (OK (update_var out (n2w b) s with vs_inst_idx := SUC s.vs_inst_idx)) /\
  ghost_inv d ce cx es
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out])
      (update_var out (n2w b) s))
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s
      (update_var out (n2w b) s) tn)
    (update_var out (n2w b) s with vs_inst_idx := SUC s.vs_inst_idx) /\
  ptr_covers
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out])
      (update_var out (n2w b) s))
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s
      (update_var out (n2w b) s) tn) out
    (update_var out (n2w b) s with vs_inst_idx := SUC s.vs_inst_idx) n
Proof
  strip_tac >> conj_tac
  >- (irule structlit_alloca_counted_edge >> simp[] >>
      metis_tac[reused_alloca_step]) >>
  conj_tac
  >- (irule structlit_reused_alloca_ghost_inv >> metis_tac[]) >>
  drule_all reused_alloca_ptr_covers >>
  disch_then (qspecl_then [`out`, `PG`, `G`, `tn`] mp_tac) >>
  simp[ptr_covers_def, lookup_var_def]
QED

(* This is only the reused-site dynamic producer. The actual StructLit
   consumer must still discharge live-register freshness, code placement,
   allocation bounds, source/body relations and gas admissibility. Fresh-site
   t_mem growth and narrow-call declared capacity are separate obligations. *)
