Theory bodyFullBuiltinECArithPayloadShape
Ancestors compileEnv emitHelper venomInst

Theorem ecadd_payload_point_cuts:
  (do xp <- emit_op ADD [p1; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p1; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib; Lit 32w];
      emit_void MSTORE [dst1; y];
      xp2 <- emit_op ADD [p2; Lit 0w];
      x2 <- emit_op MLOAD [xp2];
      dst2 <- emit_op ADD [ib; Lit 64w];
      emit_void MSTORE [dst2; x2];
      yp2 <- emit_op ADD [p2; Lit 32w];
      y2 <- emit_op MLOAD [yp2];
      dst3 <- emit_op ADD [ib; Lit 96w];
      emit_void MSTORE [dst3; y2] od) ca = ((),cp) ==>
  ?cm.
    (do xp <- emit_op ADD [p1; Lit 0w];
        x <- emit_op MLOAD [xp];
        dst0 <- emit_op ADD [ib; Lit 0w];
        emit_void MSTORE [dst0; x];
        yp <- emit_op ADD [p1; Lit 32w];
        y <- emit_op MLOAD [yp];
        dst1 <- emit_op ADD [ib; Lit 32w];
        emit_void MSTORE [dst1; y] od) ca = ((),cm) /\
    (do xp2 <- emit_op ADD [p2; Lit 0w];
        x2 <- emit_op MLOAD [xp2];
        dst2 <- emit_op ADD [ib; Lit 64w];
        emit_void MSTORE [dst2; x2];
        yp2 <- emit_op ADD [p2; Lit 32w];
        y2 <- emit_op MLOAD [yp2];
        dst3 <- emit_op ADD [ib; Lit 96w];
        emit_void MSTORE [dst3; y2] od) cm = ((),cp)
Proof
  strip_tac >>
  qpat_abbrev_tac `first = (do
    xp <- emit_op ADD [p1; Lit 0w]; x <- emit_op MLOAD [xp];
    dst0 <- emit_op ADD [ib; Lit 0w]; emit_void MSTORE [dst0; x];
    yp <- emit_op ADD [p1; Lit 32w]; y <- emit_op MLOAD [yp];
    dst1 <- emit_op ADD [ib; Lit 32w]; emit_void MSTORE [dst1; y] od)` >>
  qpat_abbrev_tac `second = (do
    xp2 <- emit_op ADD [p2; Lit 0w]; x2 <- emit_op MLOAD [xp2];
    dst2 <- emit_op ADD [ib; Lit 64w]; emit_void MSTORE [dst2; x2];
    yp2 <- emit_op ADD [p2; Lit 32w]; y2 <- emit_op MLOAD [yp2];
    dst3 <- emit_op ADD [ib; Lit 96w]; emit_void MSTORE [dst3; y2] od)` >>
  `comp_ignore_bind first second ca = ((),cp)` by
    fs[Abbr `first`, Abbr `second`, comp_ignore_bind_def, comp_bind_assoc] >>
  Cases_on `first ca` >> Cases_on `q` >>
  gvs[comp_ignore_bind_def, comp_bind_def] >> metis_tac[]
QED

Theorem ecmul_payload_point_cut:
  (do xp <- emit_op ADD [p; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib; Lit 32w];
      emit_void MSTORE [dst1; y];
      dst2 <- emit_op ADD [ib; Lit 64w];
      emit_void MSTORE [dst2; scalar] od) ca = ((),cp) ==>
  ?cm.
    (do xp <- emit_op ADD [p; Lit 0w];
        x <- emit_op MLOAD [xp];
        dst0 <- emit_op ADD [ib; Lit 0w];
        emit_void MSTORE [dst0; x];
        yp <- emit_op ADD [p; Lit 32w];
        y <- emit_op MLOAD [yp];
        dst1 <- emit_op ADD [ib; Lit 32w];
        emit_void MSTORE [dst1; y] od) ca = ((),cm) /\
    (do dst2 <- emit_op ADD [ib; Lit 64w];
        emit_void MSTORE [dst2; scalar] od) cm = ((),cp)
Proof
  strip_tac >>
  qpat_abbrev_tac `first = (do
    xp <- emit_op ADD [p; Lit 0w]; x <- emit_op MLOAD [xp];
    dst0 <- emit_op ADD [ib; Lit 0w]; emit_void MSTORE [dst0; x];
    yp <- emit_op ADD [p; Lit 32w]; y <- emit_op MLOAD [yp];
    dst1 <- emit_op ADD [ib; Lit 32w]; emit_void MSTORE [dst1; y] od)` >>
  qpat_abbrev_tac `second = (do
    dst2 <- emit_op ADD [ib; Lit 64w]; emit_void MSTORE [dst2; scalar] od)` >>
  `comp_ignore_bind first second ca = ((),cp)` by
    fs[Abbr `first`, Abbr `second`, comp_ignore_bind_def, comp_bind_assoc] >>
  Cases_on `first ca` >> Cases_on `q` >>
  gvs[comp_ignore_bind_def, comp_bind_def] >> metis_tac[]
QED
