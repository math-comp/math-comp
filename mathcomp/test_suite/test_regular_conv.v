From mathcomp Require Import all_ssreflect all_algebra all_field.

Section regular.

Import GRing.

Let eq_ringType_of_regular_lalgType (R : ringType) :=
  erefl : regular_lalgType R = Ring.Pack (Ring.class R) :> ringType.

Let eq_ringType_of_regular_algType (R : comRingType) :=
  erefl : regular_algType R = Ring.Pack (Ring.class R) :> ringType.

Let eq_comRingType_of_regular_comAlgType (R : comRingType) :=
  erefl : regular_comAlgType R = ComRing.Pack (ComRing.class R) :> ringType.

Let eq_unitRingType_of_regular_unitAlgType (R : comUnitRingType) :=
  erefl : regular_unitAlgType R =
          UnitRing.Pack (UnitRing.class R) :> unitRingType.

Let eq_comUnitRingType_of_regular_comUnitAlgType (R : comUnitRingType) :=
  erefl : regular_comUnitAlgType R =
          ComUnitRing.Pack (ComUnitRing.class R) :> comUnitRingType.

Let eq_unitRingType_of_regular_FalgType (R : comUnitRingType) :=
  erefl : regular_FalgType R = UnitRing.Pack (UnitRing.class R) :> unitRingType.

Let eq_fieldType_of_regular_fieldExtType (K : fieldType) :=
  erefl : regular_fieldExtType K = Field.Pack (Field.class K) :> fieldType.

End regular.
