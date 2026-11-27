Theory bodyIntCallBufferHeadLandedSnocMods
Ancestors
  bodyIntCallStagePacketMods bodyIntCallStageSnocMods
  exprSimProps loweringStateRelDefs loweringPosts context
  vyperContext vyperTypeSystem valueEncoding valueEncodingDefs
  ptrDiscipline venomState venomInst finite_map words list arithmetic

(* Consume the landed store's value facts and the surviving allocation at
   its original site (ci), not at the cursor where the store started. *)
val _ = Parse.hide "base";

Theorem intcall_buffer_head_landed_snoc_mods:
  intcall_stage_ops_mods (lo,func) cenv cx sa (cs,mid,t,Gf,tf) pin
    (ops,ws,vals,ptys,pflags) /\
  buf.buf_operand = Var dst /\ not_fresh_at cs dst /\
  lookup_var dst t = SOME (n2w base) /\ op_taint tf (Var dst) = {} /\
  FLOOKUP Gf dst = SOME (base,cap) /\
  FLOOKUP t.vs_allocas ci.cs_next_id = SOME (base,cap) /\
  sa.cs_next_id <= ci.cs_next_id /\ ci.cs_next_id < cs.cs_next_id /\
  MEM (mk_inst ci.cs_next_id ALLOCA [Lit (n2w cap)] [dst]) (fn_insts func) /\
  32 <= cap /\ lo <= base /\ base + cap < dimword (:256) /\
  base + cap <= t.vs_alloca_next /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type dtv v /\
  val_wf dtv v /\ type_memory_size dtv <= cap /\
  (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
     val_in_memory dtv v base mem) /\
  (!n b k. local_region cenv mid.scopes t n b k ==>
     base + cap <= b \/ b + k <= base) /\
  (case pin of NONE => T | SOME (rb,b,k) => base + cap <= b \/ b + k <= base) /\
  (!i b k. i < LENGTH ops /\ ~EL i pflags /\
     op_prov Gf (EL i ops) = SOME (b,k) ==> regions_disjoint b k base cap) ==>
  intcall_stage_ops_mods (lo,func) cenv cx sa (cs,mid,t,Gf,tf) pin
    (ops ++ [buf.buf_operand], ws ++ [n2w base], vals ++ [v],
     ptys ++ [dty], pflags ++ [F])
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule intcall_stage_ops_snoc_mods >>
  conj_tac
  >- (simp[op_prov_def] >> rpt strip_tac >> gvs[] >>
      qpat_assum `!i b k. _ ==> regions_disjoint b k base cap` irule >>
      qexists `i` >> simp[op_prov_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `base < dimword (:256)` by decide_tac >>
  `w2n (n2w base : 256 word) = base` by simp[LESS_MOD] >>
  drule_then assume_tac val_footprint_le >>
  simp[intcall_stage_ops_mods_def,eval_operands_def,eval_operand_def,
       op_prov_def,LESS_MOD] >>
  conj_tac
  >- (qexists `ci.cs_next_id` >> simp[] >>
      qexists `mk_inst ci.cs_next_id ALLOCA [Lit (n2w cap)] [dst]` >>
      simp[mk_inst_def]) >>
  qexists `ci.cs_next_id` >> simp[] >> first_assum ACCEPT_TAC
QED
