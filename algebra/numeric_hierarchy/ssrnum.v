Attributes deprecated(since="mathcomp 2.7.0",
  note="Use orderedzmod.v, numdomain.v, and numfield.v instead.").

From mathcomp Require Export orderedzmod numdomain numfield.

Module Num.
Export orderedzmod.Num.
Export numdomain.Num.
Export numfield.Num.

Module Theory.
Export Num.Theory.
End Theory.

Module Def.
Export Num.Def.
End Def.

Module ExtraDef.
#[deprecated(since="mathcomp 2.5.0", use=Num.Def.sqrtr)]
Notation sqrtr := numfield.Num.Def.sqrtr.
End ExtraDef.

End Num.
