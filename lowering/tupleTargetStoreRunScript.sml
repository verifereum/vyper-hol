(* Compiler head boundaries for mixed tuple destinations. *)
Theory tupleTargetStoreRun
Ancestors
  loweringPosts stmtSimDefs stmtSimProps
  tupleAssignParts
  tupleTargetStoreProps tupleLocalStoreRun stmtSimAssignStorage
  stmtSimAssignAttrStorage stmtLowering exprLowering exprLoweringProps
  storageStoreFrame  stmtSimDecl stmtSimDeclMem venomExecSemantics venomState vyperState
  exprSimBuffer fragExec venomInst ASCIInumbers string rich_list
  emitHelper emitHelperProps compileEnv list finite_map
  tupleMemoryFrame tupleMemoryLayout valueEncoding vyperTyping stmtLoweringMono
  vyperInterpreter freshWrites

Theorem tuple_store_word_step:
  !cenv ty tys bt gs op ops st sp sf dst loc vt.
    compile_tuple_store_all cenv (ty::tys) (BaseTarget bt::gs) (op::ops) st =
      ((), sf) /\
    compile_get_target_ptr compile_expr cenv bt st =
      ((dst, loc, SOME (ValPT vt)), sp) /\
    is_word_type ty /\ is_word_type vt ==>
    ?sm. compile_store_at_loc cenv.ce_imm_alloca dst op loc sp = ((), sm) /\
         compile_tuple_store_all cenv tys gs ops sm = ((), sf)
Proof
  cheat
QED

(* The storage part of either storage head, after its pointer is available. *)
Theorem tuple_storage_store_head_run:
  !ctx func cenv cx es es' s tr slot tv v op dst st st'.
    compile_store_at_loc cenv.ce_imm_alloca dst op
      (SOME (if tr then LocTransient else LocStorage)) st = ((), st') /\
    eval_operand dst s = SOME slot /\
    eval_operand op s = SOME (typed_val_to_w256 tv v) /\
    stmt_state_rel ctx func cenv cx es s /\
    (!u mem. storage_dead cx tr (update_storage slot u mem) =
             storage_dead cx tr mem) /\
    write_storage_slot cx tr slot tv v es = (INL (), es') /\
    encode_value tv v = SOME [(0, typed_val_to_w256 tv v)] /\
    fn_has_code st st' func /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?t. stmt_state_rel ctx func cenv cx es' t /\
        t.vs_memory = s.vs_memory /\
        ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
        t.vs_inst_idx = LENGTH st'.cs_current_insts /\
        (!x. lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s = r
Proof
  cheat
QED

(* Pointer ADDs preserve the unread tuple and all older loaded operands. *)
Theorem tuple_field_add_frame_frag:
  !ctx func cenv cx es s st st' dst slot off R.
    emit_op ADD [Lit slot; Lit (n2w off)] st = (dst, st') /\
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv st ==>
    frag_exec ctx st st' (\t. t = s)
      (\t. stmt_state_rel ctx func cenv cx es t /\
           eval_operand dst t = SOME (slot + n2w off) /\
           t.vs_labels = s.vs_labels /\
           t.vs_memory = s.vs_memory /\
           (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
           (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                    FLOOKUP t.vs_allocas aid = SOME b)) R
Proof
  cheat
QED

Theorem tuple_field_add_frame_run:
  !ctx func cenv cx es s st st' dst slot off.
    emit_op ADD [Lit slot; Lit (n2w off)] st = (dst, st') /\
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv st /\
    fn_has_code st st' func /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?t. stmt_state_rel ctx func cenv cx es t /\
        eval_operand dst t = SOME (slot + n2w off) /\
        t.vs_labels = s.vs_labels /\
        t.vs_memory = s.vs_memory /\
        ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
        t.vs_inst_idx = LENGTH st'.cs_current_insts /\
        (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s = r
Proof
  cheat
QED

Theorem tuple_field_storage_head_run:
  !ctx func cenv cx es es' s tr slot off tv v op dst st sp sf.
    emit_op ADD [Lit slot; Lit (n2w off)] st = (dst, sp) /\
    compile_store_at_loc cenv.ce_imm_alloca dst op
      (SOME (if tr then LocTransient else LocStorage)) sp = ((), sf) /\
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv st /\
    eval_operand op s = SOME (typed_val_to_w256 tv v) /\
    (!x. op = Var x ==> not_fresh_at st x) /\
    (!u mem. storage_dead cx tr (update_storage (slot + n2w off) u mem) =
             storage_dead cx tr mem) /\
    write_storage_slot cx tr (slot + n2w off) tv v es = (INL (), es') /\
    encode_value tv v = SOME [(0, typed_val_to_w256 tv v)] /\
    fn_has_code st sf func /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?t. stmt_state_rel ctx func cenv cx es' t /\
        t.vs_memory = s.vs_memory /\
        ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
        t.vs_inst_idx = LENGTH sf.cs_current_insts /\
        (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s = r
Proof
  cheat
QED

Theorem tuple_store_base_cons:
  !cenv ty tys bt gs op ops st sf.
    compile_tuple_store_all cenv (ty::tys) (BaseTarget bt::gs) (op::ops) st =
      ((),sf) ==>
    ?sm. compile_tuple_store_all cenv [ty] [BaseTarget bt] [op] st = ((),sm) /\
         compile_tuple_store_all cenv tys gs ops sm = ((),sf)
Proof
  cheat
QED

Theorem tuple_store_singleton_local_open[local]:
  !cenv id p sz ty op st sf.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME ty /\ 0 < type_memory_bytes cenv ty /\
    compile_tuple_store_all cenv [ty] [BaseTarget (NameTarget id)] [op] st =
      ((),sf) ==> ~block_is_terminated sf
Proof
  cheat
QED

Theorem tuple_store_singleton_storage_open[local]:
  !cenv bt ty op st sf dst sp tr.
    compile_get_target_ptr compile_expr cenv bt st =
      ((dst, SOME (if tr then LocTransient else LocStorage), SOME (ValPT ty)),sp) /\
    is_word_type ty /\
    compile_tuple_store_all cenv [ty] [BaseTarget bt] [op] st = ((),sf) ==>
    ~block_is_terminated sf
Proof
  cheat
QED

Theorem tuple_store_singleton_open:
  !cenv g ty op st sf.
    tuple_compiler_target cenv g ty /\
    compile_tuple_store_all cenv [ty] [g] [op] st = ((),sf) ==>
    ~block_is_terminated sf
Proof
  cheat
QED

Theorem tuple_stores_open:
  !gs cenv tys ops st sf.
    LIST_REL (tuple_compiler_target cenv) gs tys /\
    LENGTH ops = LENGTH tys /\
    compile_tuple_store_all cenv tys gs ops st = ((),sf) ==>
    (gs <> [] \/ ~block_is_terminated st ==> ~block_is_terminated sf)
Proof
  cheat
QED

Theorem tuple_store_local_singleton_code:
  !cenv id p sz ty op st sf.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME ty /\
    compile_tuple_store_all cenv [ty] [BaseTarget (NameTarget id)] [op] st =
      ((),sf) ==>
    (if is_word_type ty then emit_void MSTORE [Var p;op]
     else compile_store_memory cenv op (Var p) ty ty) st = ((),sf)
Proof
  cheat
QED

Theorem tuple_target_local_head_run:
  !ctx func cenv cx es es' s id ty tv v op st sf.
    compile_tuple_store_all cenv [ty] [BaseTarget (NameTarget id)] [op] st =
      ((),sf) /\
    assign_tuple_targets cx (BaseTarget (NameTarget id)) v es = (INL (),es') /\
    tuple_target_aligned cenv cx (BaseTarget (NameTarget id)) ty tv /\
    tuple_target_layout es.scopes (BaseTarget (NameTarget id)) ty tv v /\
    value_has_type tv v /\ val_wf tv v /\
    (if is_word_type ty then eval_operand op s = SOME (typed_val_to_w256 tv v)
     else ?w. eval_operand op s = SOME w /\
       val_in_memory tv v (w2n w) s.vs_memory /\
       type_memory_size tv + 64 < dimword(:256)) /\
    local_ptrs_reserved cenv st /\ (!x. op = Var x ==> not_fresh_at st x) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_has_code st sf func /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?t idp sz entry dw.
      stmt_state_rel ctx func cenv cx es' t /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      lookup_scopes id es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var idp) sz) /\
      lookup_var idp s = SOME dw /\
      (!a len. a + len <= w2n dw \/
         w2n dw + (if is_word_type ty then 32 else type_memory_size tv) <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                ?fuel'. run_from fuel' ctx func s = r)
Proof
  cheat
QED

Theorem tuple_target_nonlocal_head_run:
  !ctx func cenv cx es es' s g ty tv v op st sf.
    compile_tuple_store_all cenv [ty] [g] [op] st = ((),sf) /\
    assign_tuple_targets cx g v es = (INL (),es') /\
    tuple_target_aligned cenv cx g ty tv /\
    (!id. g <> BaseTarget (NameTarget id)) /\ value_has_type tv v /\
    eval_operand op s = SOME (typed_val_to_w256 tv v) /\
    local_ptrs_reserved cenv st /\ (!x. op = Var x ==> not_fresh_at st x) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_has_code st sf func /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?t. stmt_state_rel ctx func cenv cx es' t /\ t.vs_memory = s.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                ?fuel'. run_from fuel' ctx func s = r)
Proof
  cheat
QED



Theorem tuple_target_store_head_run:
  !ctx func cenv cx es es' s g ty tv v op st sf.
    compile_tuple_store_all cenv [ty] [g] [op] st = ((),sf) /\
    assign_tuple_targets cx g v es = (INL (),es') /\
    tuple_target_aligned cenv cx g ty tv /\
    tuple_target_layout es.scopes g ty tv v /\
    value_has_type tv v /\ val_wf tv v /\
    (if is_word_type ty then eval_operand op s = SOME (typed_val_to_w256 tv v)
     else ?w. eval_operand op s = SOME w /\
       val_in_memory tv v (w2n w) s.vs_memory /\
       type_memory_size tv + 64 < dimword(:256)) /\
    local_ptrs_reserved cenv st /\ (!x. op = Var x ==> not_fresh_at st x) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_has_code st sf func /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?t. stmt_state_rel ctx func cenv cx es' t /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      MAP FDOM es.scopes = MAP FDOM es'.scopes /\
      (!n. OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n es'.scopes) =
           OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n es.scopes)) /\
      (t.vs_memory = s.vs_memory \/ ?id p sz entry dw.
        g = BaseTarget (NameTarget id) /\
        lookup_scopes id es.scopes = SOME entry /\
        FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
        lookup_var p s = SOME dw /\
        (!a len. a + len <= w2n dw \/
           w2n dw + (if is_word_type ty then 32 else type_memory_size tv) <= a ==>
           mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)) /\
      (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                ?fuel'. run_from fuel' ctx func s = r)
Proof
  cheat
QED

Theorem tuple_target_store_memory_tail:
  !ctx func cenv cx es s t st scopes' g ty tv tvs v vs b sz addr.
    stmt_state_rel ctx func cenv cx es s /\
    tuple_target_layout es.scopes g ty tv v /\
    local_ptrs_reserved cenv st /\ MAP FDOM es.scopes = MAP FDOM scopes' /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
    (!aid bs. FLOOKUP s.vs_allocas aid = SOME bs ==> FLOOKUP t.vs_allocas aid = SOME bs) /\
    ((?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz)) \/
     (?name. local_region cenv es.scopes s name b sz)) /\
    b <= addr /\ addr + type_memory_size_list (tv::tvs) <= b + sz /\
    (is_word_type ty ==> type_memory_size tv = 32) /\
    tuple_in_memory (v::vs) (tv::tvs) addr s.vs_memory /\
    tuple_val_wf (v::vs) (tv::tvs) /\
    (t.vs_memory = s.vs_memory \/ ?id p dsz entry dw.
      g = BaseTarget (NameTarget id) /\
      lookup_scopes id es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) dsz) /\
      lookup_var p s = SOME dw /\
      (!a len. a + len <= w2n dw \/
         w2n dw + (if is_word_type ty then 32 else type_memory_size tv) <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)) ==>
    b <= addr + type_memory_size tv /\
    addr + type_memory_size tv + type_memory_size_list tvs <= b + sz /\
    ((?aid. FLOOKUP t.vs_allocas aid = SOME (b,sz)) \/
     (?name. local_region cenv scopes' t name b sz)) /\
    tuple_in_memory vs tvs (addr + type_memory_size tv) t.vs_memory /\
    tuple_val_wf vs tvs
Proof
  cheat
QED




Theorem tuple_store_targets_run:
  !gs m tys tvs vs ops addr b sz ctx func cenv cx es es' s st st'.
    compile_tuple_store_all cenv tys gs ops st = ((),st') /\
    assign_tuple_target_list cx gs vs es = (INL (),es') /\
    LENGTH gs = LENGTH tys /\ LENGTH tys = LENGTH tvs /\
    LENGTH tvs = LENGTH vs /\ LENGTH ops = LENGTH vs /\
    (~m ==> EVERY is_word_type tys) /\
    EVERY (\op. ?x. op = Var x) ops /\
    EVERY (\op. !x. op = Var x ==> not_fresh_at st x) ops /\
    local_ptrs_reserved cenv st /\ values_have_types tvs vs /\ tuple_val_wf vs tvs /\
    (!i. i < LENGTH gs ==>
       ?w. eval_operand (EL i ops) s = SOME w /\
         (if is_word_type (EL i tys) then
            w = typed_val_to_w256 (EL i tvs) (EL i vs)
          else w2n w = addr + SUM (MAP type_memory_size (TAKE i tvs)))) /\
    (!i. i < LENGTH gs ==>
       tuple_target_aligned cenv cx (EL i gs) (EL i tys) (EL i tvs) /\
       tuple_target_layout es.scopes (EL i gs) (EL i tys) (EL i tvs) (EL i vs)) /\
    (!i. i < LENGTH tys /\ ~is_word_type (EL i tys) ==>
       type_memory_size (EL i tvs) + 64 < dimword(:256)) /\
    (m ==> (!i. i < LENGTH tys ==>
          evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
          (is_word_type (EL i tys) ==> type_memory_size (EL i tvs) = 32)) /\
       b <= addr /\ addr + type_memory_size_list tvs <= b + sz /\
       ((?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz)) \/
        (?name. local_region cenv es.scopes s name b sz)) /\
       tuple_in_memory vs tvs addr s.vs_memory) /\
    fn_has_code st st' func /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\ stmt_state_rel ctx func cenv cx es s ==>
    (gs <> [] \/ ~block_is_terminated st ==> ~block_is_terminated st') /\
    ?t. stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
        t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
        (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
        (!aid bs. FLOOKUP s.vs_allocas aid = SOME bs ==> FLOOKUP t.vs_allocas aid = SOME bs) /\
        (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                  ?fuel'. run_from fuel' ctx func s = r)
Proof
  cheat
QED











