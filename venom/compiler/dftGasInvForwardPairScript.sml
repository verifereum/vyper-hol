Theory dftGasInvForwardPair
Ancestors
  dftGasInvAliasTransport dftGasInvForwardOutput dftGasInvForwardOrigins
  dftGasInvAliasNormal dftGasInvScheduledAliases contextCodegenRel
  venomInst venomWf dftRunRel list rich_list arithmetic

Theorem inv_forward_drop_copy[local]:
  !pre copy rest. DROP (SUC (LENGTH pre)) (pre ++ copy::rest) = rest
Proof
  Induct >> pure_asm_rewrite_tac[ONE, LENGTH, APPEND, ADD_CLAUSES, DROP] >>
  rewrite_tac[]
QED

Theorem inv_forward_pair_from_origins:
  bb.bb_instructions = pre ++ [copy] ++ mid ++ [rev] ++ post /\
  copy.inst_opcode = RETURNDATACOPY /\ copy.inst_outputs = [] /\
  copy.inst_operands = [p;src;n] /\ rev.inst_opcode = REVERT /\
  rev.inst_operands = [q;m] /\
  EVERY (\a. a.inst_opcode = ASSIGN) mid /\
  inv_alias_prefix (REVERSE (pre ++ [copy] ++ mid)) /\
  resolve_block_assigns (REVERSE pre) src = Lit 0w /\
  resolve_block_assigns (REVERSE pre) p =
    resolve_block_assigns (REVERSE (pre ++ [copy] ++ mid)) q /\
  resolve_block_assigns (REVERSE pre) n =
    resolve_block_assigns (REVERSE (pre ++ [copy] ++ mid)) m ==>
  revert_forward_pair bb (LENGTH pre) (LENGTH pre + SUC (LENGTH mid))
Proof
  strip_tac >>
  `inv_alias_prefix (REVERSE pre)` by
    (irule inv_alias_prefix_suffix >>
     qexists `REVERSE mid ++ [copy]` >>
     qpat_x_assum `inv_alias_prefix (REVERSE (pre ++ [copy] ++ mid))` mp_tac >>
     pure_rewrite_tac[REVERSE_APPEND, REVERSE_DEF, GSYM APPEND_ASSOC, APPEND] >>
     simp[]) >>
  `!a. resolve_block_assigns (REVERSE (pre ++ [copy] ++ mid)) a =
    resolve_block_assigns (REVERSE pre)
      (resolve_block_assigns (REVERSE mid) a)` by
    (gen_tac >>
     `resolve_block_assigns (REVERSE mid ++ REVERSE (pre ++ [copy])) a =
      resolve_block_assigns (REVERSE (pre ++ [copy]))
        (resolve_block_assigns (REVERSE mid) a)` by
       (irule inv_alias_resolve_append >> simp[GSYM REVERSE_APPEND]) >>
     Cases_on `resolve_block_assigns (REVERSE mid) a` >>
     gvs[REVERSE_APPEND, resolve_block_assigns_def]) >>
  `same_after_assigns (REVERSE pre) src (Lit 0w) /\
   same_after_assigns (REVERSE pre) p (resolve_block_assigns (REVERSE mid) q) /\
   same_after_assigns (REVERSE pre) n (resolve_block_assigns (REVERSE mid) m)` by
    (simp[inv_alias_prefix_normal] >>
     simp[resolve_block_assigns_def] >> metis_tac[]) >>
  rewrite_tac[revert_forward_pair_def] >>
  conj_tac >- simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `k < LENGTH bb.bb_instructions` by gvs[get_instruction_def, AllCaseEqs()] >>
      `LENGTH pre <= k /\ k - LENGTH pre = SUC (k - SUC (LENGTH pre)) /\
       k - SUC (LENGTH pre) < LENGTH mid` by decide_tac >>
      `inst = EL (k - SUC (LENGTH pre)) mid` by
        gvs[get_instruction_def, EL_APPEND2, EL_APPEND1, ADD1] >>
      gvs[EVERY_EL]) >>
  qexistsl [`copy`, `rev`, `p`, `src`, `n`, `q`, `m`] >>
  simp[get_instruction_def, EL_APPEND2, EL_APPEND1,
       TAKE_APPEND1, DROP_APPEND2, ADD1] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  pure_rewrite_tac[GSYM ADD1, inv_forward_drop_copy] >>
  simp[TAKE_APPEND1]
QED

Theorem inv_forward_block_pair:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  revert_forward_pair bb i j /\
  get_instruction bb i = SOME copy /\ get_instruction bb j = SOME rev ==>
  ?k l. revert_forward_pair (dft_block [] bb) k l /\
    get_instruction (dft_block [] bb) k = SOME copy /\
    get_instruction (dft_block [] bb) l = SOME rev
Proof
  strip_tac >>
  drule_all inv_forward_block_output >> strip_tac >>
  `copy.inst_opcode = RETURNDATACOPY /\ rev.inst_opcode = REVERT /\
   ?p src n q m. copy.inst_operands = [p;src;n] /\ rev.inst_operands = [q;m]` by
    gvs[revert_forward_pair_def] >>
  `EVERY inst_wf bb.bb_instructions` by
    (gvs[dftRunRelTheory.dft_fn_rel_def, venomWfTheory.fn_inst_wf_def, EVERY_MEM] >>
     metis_tac[]) >>
  `MEM copy bb.bb_instructions` by
    (gvs[get_instruction_def, AllCaseEqs()] >> irule EL_MEM >> simp[]) >>
  `inst_wf copy` by metis_tac[EVERY_MEM] >>
  `copy.inst_outputs = []` by gvs[inst_wf_def] >>
  `inv_alias_prefix (REVERSE (pre ++ [copy] ++ mid))` by
    (irule inv_alias_prefix_suffix >> qexists `REVERSE ([rev] ++ post)` >>
     rewrite_tac[GSYM REVERSE_APPEND] >>
     `inv_alias_prefix (REVERSE (dft_block [] bb).bb_instructions)` by
       metis_tac[inv_scheduled_alias_prefix] >>
     gvs[APPEND_ASSOC]) >>
  drule_all inv_forward_scheduled_origins >> strip_tac >>
  qexistsl [`LENGTH pre`, `LENGTH pre + SUC (LENGTH mid)`] >>
  conj_tac
  >- (irule inv_forward_pair_from_origins >> metis_tac[]) >>
  simp[get_instruction_def, EL_APPEND1, EL_APPEND2, ADD1]
QED
