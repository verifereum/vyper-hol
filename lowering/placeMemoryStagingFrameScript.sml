Theory placeMemoryStagingFrame
Ancestors
  placeMemoryCopyEffect fragGasMode compileEnv loweringStateRelDefs venomState freshWrites
  placeMemoryCopyFrames

Theorem staging_store_local_frame:
  gas_marked_path F ctx func s 0 (OK u) /\
  r.vs_memory = s.vs_memory /\
  (u with <|vs_vars := r.vs_vars; vs_memory := r.vs_memory;
    vs_prev_bb := r.vs_prev_bb; vs_current_bb := r.vs_current_bb;
    vs_inst_idx := r.vs_inst_idx|>) = r /\
  u.vs_allocas = r.vs_allocas /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP r.vs_allocas aid = SOME e) /\
  (!name b len. local_region cenv scopes s name b len ==>
     local_region cenv scopes r name b len) /\
  (!name b len. local_region cenv scopes r name b len ==>
     regions_disjoint tmp sz b len) /\
  (!a len. a+len <= tmp \/ tmp+sz <= a ==>
     mem_bytes_at a len u.vs_memory = mem_bytes_at a len s.vs_memory) /\
  LENGTH s.vs_memory <= LENGTH u.vs_memory /\
  sa.cs_next_var <= sn.cs_next_var /\
  typed_copy_effect ctx func sn sb u t d n ==>
  gas_marked_path F ctx func s 0 (OK t) /\
  (t with <|vs_vars := r.vs_vars; vs_memory := r.vs_memory;
    vs_prev_bb := r.vs_prev_bb; vs_current_bb := r.vs_current_bb;
    vs_inst_idx := r.vs_inst_idx|>) = r /\
  t.vs_allocas = r.vs_allocas /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP t.vs_allocas aid = SOME e) /\
  (!name b len. local_region cenv scopes s name b len ==>
     local_region cenv scopes r name b len) /\
  (!name b len a k. local_region cenv scopes r name b len /\
     b <= a /\ a+k <= b+len /\ (a+k <= d \/ d+n <= a) ==>
     mem_bytes_at a k t.vs_memory = mem_bytes_at a k r.vs_memory) /\
  LENGTH r.vs_memory <= LENGTH t.vs_memory /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  simp[typed_copy_effect_def] >> strip_tac >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  `(t with <|vs_vars := r.vs_vars; vs_memory := r.vs_memory;
    vs_prev_bb := r.vs_prev_bb; vs_current_bb := r.vs_current_bb;
    vs_inst_idx := r.vs_inst_idx|>) = r` by
    (qpat_x_assum `(t with <|vs_memory := _; vs_vars := _; vs_prev_bb := _;
        vs_current_bb := _; vs_inst_idx := _|>) = u`
      (mp_tac o Q.AP_TERM `\z. z with <|vs_vars := r.vs_vars;
        vs_memory := r.vs_memory; vs_prev_bb := r.vs_prev_bb;
        vs_current_bb := r.vs_current_bb; vs_inst_idx := r.vs_inst_idx|>`) >> simp[]) >>
  qpat_x_assum `(t with <|vs_vars := _; vs_memory := _; vs_prev_bb := _;
      vs_current_bb := _; vs_inst_idx := _|>) = r` mp_tac >>
  simp[] >> strip_tac >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sn x` by metis_tac[not_fresh_at_mono] >>
      metis_tac[]) >>
  rpt strip_tac >>
  `regions_disjoint tmp sz b len` by metis_tac[] >>
  `a+k <= tmp \/ tmp+sz <= a` by
    (gvs[regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at a k t.vs_memory = mem_bytes_at a k u.vs_memory` by
    (qpat_x_assum `!a len. a+len <= d \/ _ ==> _` irule >> simp[]) >>
  `mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory` by
    (qpat_x_assum `!a len. a+len <= tmp \/ _ ==> _` irule >> simp[]) >>
  simp[]
QED
