(* Fixed-endpoint certificates for the ordered stores of a linked StructLit. *)
Theory bodyStructFieldCutsMods
Ancestors
  bodyFullPostsMods bodyPtrMakeArrayMemoryFrame exprSimFullBundleProps
  typedMemoryCopy bodyPtrDefs loweringPosts loweringStateRelDefs
  compileEnv context exprSimProps vyperValue valueEncoding valueEncodingDefs
  venomInst venomState finite_map pred_set words list pair

(* frame: configuration; anchor: original expression entry;
   buffer: the one result allocation; at: current horizon and endpoint. *)
Definition struct_prefix_mods_def[nocompute]:
  struct_prefix_mods (ctx,func,ce,cx,lo,d,pure)
    (ees,fr,sf,Gf,tnf) (root,addr,capacity,aid)
    (H,D,ee,cs,G,tn,s) cells off <=>
    stmt_state_rel H ctx func ce cx ee s /\
    immutable_frame_mods func ce cx ee s /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods D lo d ce cx ee G tn s /\
    wb_frame ce ees ee fr sf s /\ ghost_kept_at lo ce ees fr Gf tnf sf G tn /\
    MAP FDOM ees.scopes = MAP FDOM ee.scopes /\
    ~s.vs_halted /\ expr_sim_full_endpoint func cs sf s /\
    not_fresh_at cs root /\ lookup_var root s = SOME (n2w addr) /\
    ptr_covers G tn root s capacity /\
    FLOOKUP s.vs_allocas aid = SOME (addr,capacity) /\
    MEM (mk_inst aid ALLOCA [Lit (n2w capacity)] [root]) (fn_insts func) /\
    lo <= addr /\ addr + capacity < dimword (:256) /\
    fr.cs_next_id <= aid /\ aid < cs.cs_next_id /\
    fr.cs_next_var <= cs.cs_next_var /\ off <= capacity /\
    (!name p k. local_region ce ee.scopes s name p k ==>
       addr + capacity <= p \/ p + k <= addr) /\
    (!name p k. local_region ce ees.scopes sf name p k ==>
       addr + capacity <= p \/ p + k <= addr) /\
    (!old p k. FLOOKUP sf.vs_allocas old = SOME (p,k) /\ old < fr.cs_next_id ==>
       addr + capacity <= p \/ p + k <= addr) /\
    EVERY (\(tv,v,p,k). addr <= p /\ p + k <= addr + off) cells /\
    literal_prefix_ok cells tn s /\
    (pure ==> pure_frame ce func ees fr sf s)
End

(* The word route takes a decoded word. A physical nonword of width zero
   needs an operand but not an allocated source region or a variable.
   The bytestring route has its own overlap-safe store; the other positive
   nonword route needs separation of the read footprint. *)
Definition struct_operand_mods_def[nocompute]:
  struct_operand_mods (ce,tenv,sty,dty,stv,dtv) (op,v) (dst,base) (sa,G,tn,s) <=>
    evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
    type_widens_to tenv sty dty /\ type_memory_bytes ce dty = type_memory_size dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    not_fresh_at sa dst /\ lookup_var dst s = SOME (n2w base) /\
    base + type_memory_size dtv < dimword (:256) /\
    base + type_memory_size dtv <= s.vs_alloca_next /\
    ptr_covers G tn dst s (type_memory_size dtv) /\ op_taint tn op = {} /\
    (if is_word_type dty then
       eval_operand op s = SOME (typed_val_to_w256 dtv v)
     else
       ?sw. eval_operand op s = SOME sw /\
         w2n sw + type_memory_size stv < dimword (:256) /\
         (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
              val_in_memory stv v (w2n sw) m) /\
         (0 < type_memory_size stv ==>
            w2n sw + type_memory_size stv <= s.vs_alloca_next /\
            (?src. op = Var src /\ not_fresh_at sa src /\
                   ptr_covers G tn src s (type_memory_size stv)) /\
            (~is_bytestring_type dty ==>
               (w2n sw + val_footprint stv v <= base \/
                base + type_memory_size dtv <= w2n sw))))
End

(* typed_copy_state_frame accounts for unchanged allocation and data
   fields, preserved old variables, and unchanged bytes outside the write.
   The path to this endpoint is a separate premise/conclusion. *)
Definition struct_store_effects_def[nocompute]:
  struct_store_effects func (sa,G,tn,s) (sb,G',tn',t) (base,tv,v) <=>
    val_wf tv v /\
    typed_copy_state_frame sa base (type_memory_size tv) s t /\
    ~t.vs_halted /\ expr_sim_full_endpoint func sb s t /\
    (!p. not_fresh_at sa p ==>
       FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p)) /\
    tn'.t_imm = tn.t_imm /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    (!i. ~(base <= i /\ i < base + type_memory_size tv) ==>
       (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    (!m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
         val_in_memory tv v base m)
End

Theorem struct_prefix_empty_intro:
  stmt_state_rel H ctx func ce cx es s /\
  immutable_frame_mods func ce cx es s /\
  storage_well_formed_on cx es (FST H) /\
  ghost_inv_at_mods D lo d ce cx es G tn s /\
  wb_frame ce es es fr sf s /\ ghost_kept_at lo ce es fr Gf tnf sf G tn /\
  ~s.vs_halted /\ expr_sim_full_endpoint func cs sf s /\
  not_fresh_at cs root /\ lookup_var root s = SOME (n2w addr) /\
  ptr_covers G tn root s capacity /\
  FLOOKUP s.vs_allocas fr.cs_next_id = SOME (addr,capacity) /\
  MEM (mk_inst fr.cs_next_id ALLOCA [Lit (n2w capacity)] [root]) (fn_insts func) /\
  lo <= addr /\ addr + capacity < dimword (:256) /\
  fr.cs_next_id < cs.cs_next_id /\ fr.cs_next_var <= cs.cs_next_var /\
  (!name p k. local_region ce es.scopes s name p k ==>
     addr + capacity <= p \/ p + k <= addr) /\
  (!name p k. local_region ce es.scopes sf name p k ==>
     addr + capacity <= p \/ p + k <= addr) /\
  (!old p k. FLOOKUP sf.vs_allocas old = SOME (p,k) /\ old < fr.cs_next_id ==>
     addr + capacity <= p \/ p + k <= addr) /\
  (pure ==> pure_frame ce func es fr sf s) ==>
  struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) (es,fr,sf,Gf,tnf)
    (root,addr,capacity,fr.cs_next_id) (H,D,es,cs,G,tn,s) [] 0
Proof
  strip_tac >> fs[struct_prefix_mods_def, literal_prefix_ok_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem struct_prefix_cell_lookup:
  struct_prefix_mods frame anchor (root,addr,capacity,aid)
    (H,D,ee,cs,G,tn,s) cells off /\ MEM (tv,v,p,k) cells ==>
  val_wf tv v /\ val_footprint tv v <= k /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v p m)
Proof
  PairCases_on `frame` >> PairCases_on `anchor` >>
  simp[struct_prefix_mods_def] >> strip_tac >>
  irule literal_prefix_lookup >> simp[] >>
  qexists_tac `cells` >> simp[]
QED
