- in `ssralg.v`, the following constants and abbreviations have been removed
  from the `GRing` module in favor of `nmodule.v`, but they are still reexported
  from the `GRing.Theory` module:
  + Lemmas `addrA`, `addrC`, `add0r`, `addr0`, `addrCA`, `addrAC`, `addrACA`,
    `mulr0n`, `mulr1n`, `mulr2n`, `mulrS`, `mulrSr`, `mulrb`, `mul0rn`,
    `mulrnDl`, `mulrnDr`, `mulrnA`, `mulrnAC`, `iter_addr`, `iter_addr_0`,
    `sumrMnl`, `sumrMnr`, `sumr_const`, `sumr_const_nat`, `addNr`, `addrN`,
    `subrr`, `addKr`, `addNKr`, `addrK`, `addrNK`, `subrK`, `subrKC`, `subKr`,
    `addrI`, `addIr`, `subrI`, `subIr`, `opprK`, `oppr_inj`, `oppr0`,
    `oppr_eq0`, `subr0`, `sub0r`, `opprB`, `opprD`, `addrKA`, `subrKA`,
    `addr0_eq`, `subr0_eq`, `addr_eq0`, `eqr_opp`, `eqr_oppLR`, `mulNrn`,
    `mulrnBl`, `mulrnBr`, `sumrN`, `sumrB`, `telescope_sumr`,
    `telescope_sumr_eq`, `zmod_closedN`, `rpred0D`, `zmodClosedP`
  + Definitions `oppr_closed`, `zmod_closed`, `addrClosed`, `opprClosed`
    ([#1433](https://github.com/math-comp/math-comp/pull/1433),
    fixes [#1478](https://github.com/math-comp/math-comp/issues/1478)).
