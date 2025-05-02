From mathcomp Require Export orderedzmod.
From mathcomp Require Export numdomain.
From mathcomp Require Export numfield.

Module Num.
Export orderedzmod.Num.
Export numdomain.Num.
Export numfield.Num.

Module Theory.
Export orderedzmod.Num.Theory.
Export numdomain.Num.Theory.
Export numfield.Num.Theory.
End Theory.

Module Def.
Export orderedzmod.Num.Def.
Export numdomain.Num.Def.
Export numfield.Num.Def.
End Def.

Module ExtraDef.
#[deprecated(since="mathcomp 2.5.0", note="Use Num.Def.sqrtr instead.")]
Notation sqrtr := numfield.Num.Def.sqrtr.
End ExtraDef.

End Num.
