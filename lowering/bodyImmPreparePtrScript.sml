(* Scalar preparation of the immutable element address. *)
Theory bodyImmPreparePtr
Ancestors
  bodyPtrBopScalarSeq whitelistForIterImmLoop forPtrScope
  ptrDiscipline venomState venomInst venomExecSemantics fragExec
  finite_map words list arithmetic pred_set

Theorem immutable_address_prefix_ptr:
  lookup_var idx s = SOME (n2w k) /\ ov <> tot /\
  ov NOTIN R /\ tot NOTIN R /\ ep NOTIN R /\
  FLOOKUP G idx = NONE /\ op_taint tn (Var idx) = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX
    ([mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]] ++
     (if dyn then [mk_inst j4 ADD [Lit 32w; Var ov] [tot]] else []) ++
     [mk_inst j5 ADD [Lit (n2w off); Var (if dyn then tot else ov)] [ep]])
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  let code =
    [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]] ++
    (if dyn then [mk_inst j4 ADD [Lit 32w; Var ov] [tot]] else []) ++
    [mk_inst j5 ADD [Lit (n2w off); Var (if dyn then tot else ov)] [ep]];
      u = update_var ep (n2w off + n2w ((if dyn then 32 else 0) + k * stride))
       (if dyn then update_var tot (n2w (32 + k * stride))
          (update_var ov (n2w (k * stride)) s)
        else update_var ov (n2w (k * stride)) s)
  in
  ?H tm.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm
      (OK (u with vs_inst_idx := s.vs_inst_idx + LENGTH code)) /\
    op_prov H (Var ep) = NONE /\ op_taint tm (Var ep) = {} /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. x IN R ==> FLOOKUP H x = FLOOKUP G x /\
      FLOOKUP tm.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >> simp[] >>
  qabbrev_tac `A = {Var idx; Lit (n2w stride); Lit 32w; Lit (n2w off)}` >>
  qabbrev_tac `B = Var ep INSERT
    (if dyn then Var tot INSERT (Var ov INSERT A) else Var ov INSERT A)` >>
  `bop_scalar_seq R A
    ([mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]] ++
     (if dyn then [mk_inst j4 ADD [Lit 32w; Var ov] [tot]] else []) ++
     [mk_inst j5 ADD [Lit (n2w off); Var (if dyn then tot else ov)] [ep]]) B` by
    (Cases_on `dyn` >> simp[Abbr `B`, Abbr `A`, bop_scalar_seq_def, mk_inst_def]) >>
  `!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[Abbr `A`] >> rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  `run_inst_seq
    ([mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov]] ++
     (if dyn then [mk_inst j4 ADD [Lit 32w; Var ov] [tot]] else []) ++
     [mk_inst j5 ADD [Lit (n2w off); Var (if dyn then tot else ov)] [ep]]) s =
    OK (update_var ep (n2w off + n2w ((if dyn then 32 else 0) + k * stride))
       (if dyn then update_var tot (n2w (32 + k * stride))
          (update_var ov (n2w (k * stride)) s)
        else update_var ov (n2w (k * stride)) s))` by
    (irule immutable_address_prefix_run >> simp[]) >>
  drule_all bop_scalar_seq_path >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexistsl [`G'`,`tn'`] >> simp[] >>
  `Var ep IN B` by simp[Abbr `B`] >>
  conj_tac >- (qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
    SIMP_TAC bool_ss [LENGTH_APPEND, LENGTH, ONE, ADD_CLAUSES, ADD_COMM]) >> metis_tac[]
QED
