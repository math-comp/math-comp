From mathcomp Require Export orderedzmod numdomain numfield.

Attributes deprecated(since="mathcomp 2.6.0",
  note="'ssrnum' has been renamed 'numeric_hierarchy'.").

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
