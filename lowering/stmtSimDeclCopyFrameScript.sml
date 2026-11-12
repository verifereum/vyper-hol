(* Registering a newly stored aggregate under the typed-copy frame. *)
Theory stmtSimDeclCopyFrame
Ancestors
  stmtSimDeclMem stmtSimDeclStore exprSimStorageCopy localPtrsProps
  loweringPosts loweringStateRelDefs valueEncoding compileEnv
  exprLoweringProps loweringSlice
  finite_map venomState venomInst

Theorem stmt_state_rel_declare_copy_frame:
  !func cenv cx es s t sa id p sz w inst v tyv sc rest a ctx.
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ lookup_var p s = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    local_ptrs_reserved cenv sa /\ not_fresh_at sa p /\
    copy_static t = copy_static s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!b n. b + n <= w2n w \/ w2n w + type_memory_size tyv <= b ==>
           mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    type_memory_size tyv <= sz /\ val_wf tyv v /\
    val_in_memory tyv v (w2n w) t.vs_memory ==>
    stmt_state_rel ctx func cenv cx
      (es with scopes :=
        (sc |+ (id, <|assignable := a; type := tyv; value := v; popped := []|>)) :: rest) t
Proof
  rpt gen_tac >> strip_tac >>
  `!q. q = p \/ ~not_local_ptr cenv es.scopes q ==>
       lookup_var q t = lookup_var q s` by
    (rpt strip_tac >- simp[] >>
     `not_fresh_at sa q` by
       (gvs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]) >>
     simp[]) >>
  `!n b sz'. n <> id /\ local_region cenv es.scopes s n b sz' ==>
       mem_bytes_at b sz' s.vs_memory = mem_bytes_at b sz' t.vs_memory` by
    (rpt strip_tac >>
     `regions_disjoint (w2n w) sz b sz'` by
       (irule local_ptrs_rel_alloca_disjoint >>
        qexistsl_tac [`cenv`, `func`, `inst`, `n`, `p`, `es.scopes`, `s`] >>
        fs[stmt_state_rel_def, state_rel_def]) >>
     `b + sz' <= w2n w \/ w2n w + type_memory_size tyv <= b` by
       (fs[regions_disjoint_def] >> decide_tac) >>
     metis_tac[]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t` by
    (irule immutables_rel_mem_agree >> qexists_tac `s` >>
     fs[stmt_state_rel_def, state_rel_def] >>
     `t.vs_data_section = s.vs_data_section` by
       metis_tac[copy_static_fields] >>
     fs[immutable_alloca_sep_def] >> rpt strip_tac >>
     first_x_assum drule_all >> strip_tac >>
     `regions_disjoint off (type_memory_size tv) (w2n w) sz` by metis_tac[] >>
     `off + type_memory_size tv <= w2n w \/
      w2n w + type_memory_size tyv <= off` by
       (fs[regions_disjoint_def] >> decide_tac) >>
     qpat_x_assum `!b n. _ ==> mem_bytes_at b n t.vs_memory = _`
       (qspecl_then [`off`, `type_memory_size tv`] mp_tac) >> simp[]) >>
  irule stmt_state_rel_declare_memory >> simp[] >>
  qexistsl_tac [`inst`, `s`, `w`] >> gs[] >>
  qpat_x_assum `copy_static t = copy_static s` mp_tac >>
  simp[copy_static_def, venom_state_component_equality] >>
  strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
